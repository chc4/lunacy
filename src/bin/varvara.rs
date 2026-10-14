//! The Lua Varvara emulator (varvara/app.lua, bundled to bytecode) in a window:
//! lunacy runs the program, which draws through `ui`, a library of natives over
//! Dear ImGui, and reads the ROM it emulates from the global `rom`.
//!
//!     varvara <app.bin> <rom>
//!
//! `ui.open(title, width, height)` opens the window, a userdata, once. Its
//! methods: `frame()`, which shows the frame drawn since the last call and
//! starts the next, false once the window is closed; `texture(width, height)`,
//! a new texture, a userdata; `begin(title)` and `finish()` around a window's
//! widgets, `begin` true if the window is open (`begin(title, x, y, width,
//! height)` places it, the first time it's shown); `text(s)`; `button(label)`, true
//! if clicked; `checkbox(label, value)`, the value after a click; `slider(label,
//! value, min, max)`, an integer; `same_line()` and `separator()`; `key(name)`,
//! whether a key is down (`up`, `down`, `left`, `right`, `home`, `ctrl`, `alt`,
//! `shift`); `typed()`, the bytes typed since the last frame (Enter, Backspace,
//! Tab and Escape as their ASCII codes); and `mouse()`, the mouse's buttons
//! (left 1, middle 2, right 4) and its wheel's vertical move this frame. A
//! texture's: `update(width, height, fg, bg, palette)`, its pixels from two
//! layers of palette indexes (tables from 0, the first drawn over the second
//! where it isn't 0) and a palette (red, green, blue of each index from 1);
//! `image(scale)`, drawn as a widget; and `pointer()`, the mouse's position in
//! its pixels as last drawn.
//!
//! With `VARVARA_FRAMES=n`, `frame()` is false after n frames; with
//! `VARVARA_SCREENSHOT=path` too, the window's last frame is written to `path`
//! as a binary PPM image.

use std::cell::{Cell, RefCell};
use std::error::Error;
use std::ffi::CString;
use std::rc::Rc;

use glow::HasContext;
use imgui::sys;
use imgui_glow_renderer::AutoRenderer;
use imgui_sdl2_support::SdlPlatform;
use qcell::{LCell, LCellOwner};
use sdl2::event::Event;
use sdl2::keyboard::Keycode;

use lunacy::gc::Gc;
use lunacy::vm::{self, LBoxed, LValue, Table, Tc, Userdata};
use lunacy::{Owner, Vm, chunk};

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

thread_local! {
    // The window's and textures' metatables, as their bits: a native captures
    // nothing. The `ui` table holds them too, which keeps them alive.
    static WINDOW_METATABLE: Cell<u64> = const { Cell::new(0) };
    static TEXTURE_METATABLE: Cell<u64> = const { Cell::new(0) };
}

/// The window: SDL's, its GL context, and Dear ImGui's.
struct Host {
    _sdl: sdl2::Sdl,
    window: sdl2::video::Window,
    _gl: sdl2::video::GLContext,
    events: sdl2::EventPump,
    imgui: imgui::Context,
    platform: SdlPlatform,
    renderer: AutoRenderer,
    /// Whether a frame has begun, which the next `frame` shows.
    drawing: bool,
    /// The bytes typed since the last frame.
    typed: Vec<u8>,
    frames: usize,
    /// `VARVARA_FRAMES` and `VARVARA_SCREENSHOT`.
    last_frame: Option<usize>,
    screenshot: Option<String>,
}

/// A GL texture, in its window's GL context, and where it was last drawn: its
/// top left corner on the screen, and its scale.
struct Texture {
    context: Rc<glow::Context>,
    gl: glow::NativeTexture,
    size: Cell<(u32, u32)>,
    drawn: Cell<([f32; 2], f32)>,
}

fn error<'s, 'i>(message: impl AsRef<str>) -> LBoxed<'s, 'i> {
    LBoxed::box_lvalue(LValue::OwnedString(Gc::string(message.as_ref().as_bytes())))
}

fn string<'s, 'i>(bytes: &[u8]) -> LBoxed<'s, 'i> {
    LBoxed::box_lvalue(LValue::OwnedString(Gc::string(bytes)))
}

/// A native from `$body`, which takes its arguments (a slice) and the owner and
/// gives its results, or an error message. See Note [Library natives]: the results fill the caller's result slots, nil past them, and
/// there are only as many slots as the call's function and arguments.
macro_rules! native {
    ($name:ident, |$args:ident, $owner:ident| $body:expr) => {
        fn $name<'id, 'a, 's, 'i>(mut seq: LCellOwner<'id>, args: &'a LCell<'id, [LBoxed<'s, 'i>]>, returns: &'a LCell<'id, [LBoxed<'s, 'i>]>, $owner: &mut Owner) -> Result<usize, LBoxed<'s, 'i>> {
            let $args: Vec<LBoxed<'s, 'i>> = args.ro(&seq).to_vec();
            let results = (|| -> Result<Vec<LBoxed<'s, 'i>>, String> { $body })();
            let results = results.map_err(error)?;
            let slots = returns.rw(&mut seq);
            if results.len() > slots.len() {
                return Err(error(format!("{}: {} results, but only {} slots for them", stringify!($name), results.len(), slots.len())));
            }
            for (i, slot) in slots.iter_mut().enumerate() {
                *slot = results.get(i).copied().unwrap_or(LBoxed::NIL);
            }
            Ok(results.len())
        }
    };
}

fn arg<'s, 'i>(args: &[LBoxed<'s, 'i>], i: usize) -> LBoxed<'s, 'i> {
    args.get(i).copied().unwrap_or(LBoxed::NIL)
}

fn number(args: &[LBoxed], i: usize, what: &str) -> Result<f64, String> {
    arg(args, i).as_number().ok_or_else(|| format!("{what}: a number expected"))
}

fn text(args: &[LBoxed], i: usize, owner: &Owner, what: &str) -> Result<CString, String> {
    let v = arg(args, i).unbox();
    match v {
        LValue::InternedString(_) | LValue::OwnedString(_) => CString::new(v.string_bytes(owner)).map_err(|_| format!("{what}: a string with no zero byte expected")),
        _ => Err(format!("{what}: a string expected")),
    }
}

fn table<'s, 'i>(args: &[LBoxed<'s, 'i>], i: usize, what: &str) -> Result<Tc<Table<'s, 'i>>, String> {
    arg(args, i).as_table().ok_or_else(|| format!("{what}: a table expected"))
}

/// The userdata argument `i`'s data, if it's a userdata with data of type `T`.
fn data<'o, 's: 'o, 'i: 'o, T: 'static>(args: &[LBoxed<'s, 'i>], i: usize, owner: &'o Owner, what: &str) -> Result<&'o T, String> {
    match arg(args, i).unbox() {
        // Safety: the argument keeps the userdata alive while the native runs.
        LValue::Userdata(u) => unsafe { &*(u.ro(owner) as *const Userdata<'s, 'i>) }.data::<T>().ok_or_else(|| format!("{what}: not the userdata expected")),
        _ => Err(format!("{what}: a userdata expected")),
    }
}

fn host<'o, 's: 'o, 'i: 'o>(args: &[LBoxed<'s, 'i>], owner: &'o Owner, what: &str) -> Result<std::cell::RefMut<'o, Host>, String> {
    data::<RefCell<Host>>(args, 0, owner, what)?.try_borrow_mut().map_err(|_| format!("{what}: the window is busy"))
}

/// Requires a frame to have begun, as every widget does.
fn drawing(host: &Host, what: &str) -> Result<(), String> {
    if host.drawing { Ok(()) } else { Err(format!("{what}: no frame has begun (call frame() first)")) }
}

fn userdata<'s, 'i, T: 'static>(metatable: &'static std::thread::LocalKey<Cell<u64>>, data: T) -> LBoxed<'s, 'i> {
    // Safety: the `ui` table keeps the metatable alive.
    let metatable = unsafe { LBoxed::from_bits(metatable.with(|bits| bits.get())) }.as_table();
    LBoxed::box_lvalue(LValue::Userdata(Tc::new(Userdata::with_data(metatable, data))))
}

native!(ui_open, |args, owner| {
    let title = text(&args, 0, owner, "ui.open")?;
    let width = number(&args, 1, "ui.open")? as u32;
    let height = number(&args, 2, "ui.open")? as u32;
    open(title.to_str().unwrap_or("varvara"), width, height).map(|host| vec![userdata(&WINDOW_METATABLE, RefCell::new(host))])
});

fn open(title: &str, width: u32, height: u32) -> Result<Host, String> {
    let sdl = sdl2::init()?;
    let video = sdl.video()?;
    let attributes = video.gl_attr();
    attributes.set_context_version(3, 3);
    attributes.set_context_profile(sdl2::video::GLProfile::Core);
    let window = video.window(title, width, height).opengl().position_centered().resizable().build().map_err(|e| e.to_string())?;
    let gl_context = window.gl_create_context()?;
    window.gl_make_current(&gl_context)?;
    // Without vsync (as on a virtual display) frames come as fast as they're drawn.
    let _ = video.gl_set_swap_interval(1);
    let gl = unsafe { glow::Context::from_loader_function(|s| video.gl_get_proc_address(s) as _) };
    let mut imgui = imgui::Context::create();
    imgui.set_ini_filename(None);
    imgui.set_log_filename(None);
    imgui.fonts().add_font(&[imgui::FontSource::DefaultFontData { config: None }]);
    let platform = SdlPlatform::new(&mut imgui);
    let renderer = AutoRenderer::new(gl, &mut imgui).map_err(|e| e.to_string())?;
    let events = sdl.event_pump()?;
    let env = |name| std::env::var(name).ok();
    Ok(Host {
        _sdl: sdl, window, _gl: gl_context, events, imgui, platform, renderer,
        drawing: false, typed: Vec::new(), frames: 0,
        last_frame: env("VARVARA_FRAMES").map(|n| n.parse().expect("VARVARA_FRAMES: a number of frames")),
        screenshot: env("VARVARA_SCREENSHOT"),
    })
}

native!(window_frame, |args, owner| {
    let mut host = host(&args, owner, "frame")?;
    let host = &mut *host;
    if host.drawing {
        let draw_data = host.imgui.render();
        unsafe {
            let gl = host.renderer.gl_context();
            gl.clear_color(0.12, 0.12, 0.14, 1.0);
            gl.clear(glow::COLOR_BUFFER_BIT);
        }
        host.renderer.render(draw_data).map_err(|e| e.to_string())?;
        host.frames += 1;
        if host.last_frame == Some(host.frames) && let Some(path) = &host.screenshot {
            screenshot(host, path)?;
        }
        host.window.gl_swap_window();
        host.drawing = false;
    }
    if host.last_frame.is_some_and(|last| host.frames >= last) {
        return Ok(vec![LBoxed::from_bool(false)]);
    }
    host.typed.clear();
    for event in host.events.poll_iter() {
        host.platform.handle_event(&mut host.imgui, &event);
        match event {
            Event::Quit { .. } => return Ok(vec![LBoxed::from_bool(false)]),
            Event::TextInput { text, .. } => host.typed.extend_from_slice(text.as_bytes()),
            Event::KeyDown { keycode: Some(key), .. } => match key {
                Keycode::Return | Keycode::KpEnter => host.typed.push(0x0d),
                Keycode::Backspace => host.typed.push(0x08),
                Keycode::Tab => host.typed.push(0x09),
                Keycode::Escape => host.typed.push(0x1b),
                _ => (),
            },
            _ => (),
        }
    }
    host.platform.prepare_frame(&mut host.imgui, &host.window, &host.events);
    host.imgui.new_frame();
    host.drawing = true;
    Ok(vec![LBoxed::from_bool(true)])
});

/// The window's back buffer, written to `path` as a binary PPM image.
fn screenshot(host: &Host, path: &str) -> Result<(), String> {
    let (width, height) = host.window.drawable_size();
    let mut pixels = vec![0u8; width as usize * height as usize * 3];
    unsafe {
        let gl = host.renderer.gl_context();
        gl.pixel_store_i32(glow::PACK_ALIGNMENT, 1);
        gl.read_pixels(0, 0, width as i32, height as i32, glow::RGB, glow::UNSIGNED_BYTE, glow::PixelPackData::Slice(&mut pixels));
    }
    // GL's rows go from the bottom.
    let mut out = format!("P6\n{width} {height}\n255\n").into_bytes();
    for row in pixels.chunks(width as usize * 3).rev() {
        out.extend_from_slice(row);
    }
    std::fs::write(path, out).map_err(|e| format!("{path}: {e}"))
}

native!(window_texture, |args, owner| {
    let host = host(&args, owner, "texture")?;
    let width = number(&args, 1, "texture")? as u32;
    let height = number(&args, 2, "texture")? as u32;
    let gl = host.renderer.gl_context();
    let texture = unsafe {
        let texture = gl.create_texture()?;
        gl.bind_texture(glow::TEXTURE_2D, Some(texture));
        gl.tex_parameter_i32(glow::TEXTURE_2D, glow::TEXTURE_MIN_FILTER, glow::NEAREST as i32);
        gl.tex_parameter_i32(glow::TEXTURE_2D, glow::TEXTURE_MAG_FILTER, glow::NEAREST as i32);
        gl.tex_image_2d(glow::TEXTURE_2D, 0, glow::RGBA as i32, width as i32, height as i32, 0, glow::RGBA, glow::UNSIGNED_BYTE, None);
        texture
    };
    Ok(vec![userdata(&TEXTURE_METATABLE, Texture { context: gl.clone(), gl: texture, size: Cell::new((width, height)), drawn: Cell::new(([0.0; 2], 1.0)) })])
});

native!(window_begin, |args, owner| {
    let host = host(&args, owner, "begin")?;
    drawing(&host, "begin")?;
    let title = text(&args, 1, owner, "begin")?;
    if args.len() >= 6 {
        let at = |i| number(&args, i, "begin").map(|n| n as f32);
        unsafe {
            sys::igSetNextWindowPos(sys::ImVec2 { x: at(2)?, y: at(3)? }, sys::ImGuiCond_FirstUseEver as i32, sys::ImVec2 { x: 0.0, y: 0.0 });
            sys::igSetNextWindowSize(sys::ImVec2 { x: at(4)?, y: at(5)? }, sys::ImGuiCond_FirstUseEver as i32);
        }
    }
    let open = unsafe { sys::igBegin(title.as_ptr(), std::ptr::null_mut(), 0) };
    Ok(vec![LBoxed::from_bool(open)])
});

native!(window_finish, |args, owner| {
    let host = host(&args, owner, "finish")?;
    drawing(&host, "finish")?;
    unsafe { sys::igEnd() };
    Ok(vec![])
});

native!(window_text, |args, owner| {
    let host = host(&args, owner, "text")?;
    drawing(&host, "text")?;
    let s = text(&args, 1, owner, "text")?;
    unsafe { sys::igTextUnformatted(s.as_ptr(), std::ptr::null()) };
    Ok(vec![])
});

native!(window_button, |args, owner| {
    let host = host(&args, owner, "button")?;
    drawing(&host, "button")?;
    let label = text(&args, 1, owner, "button")?;
    let clicked = unsafe { sys::igButton(label.as_ptr(), sys::ImVec2 { x: 0.0, y: 0.0 }) };
    Ok(vec![LBoxed::from_bool(clicked)])
});

native!(window_checkbox, |args, owner| {
    let host = host(&args, owner, "checkbox")?;
    drawing(&host, "checkbox")?;
    let label = text(&args, 1, owner, "checkbox")?;
    let mut value = arg(&args, 2).truthy();
    unsafe { sys::igCheckbox(label.as_ptr(), &mut value) };
    Ok(vec![LBoxed::from_bool(value)])
});

native!(window_slider, |args, owner| {
    let host = host(&args, owner, "slider")?;
    drawing(&host, "slider")?;
    let label = text(&args, 1, owner, "slider")?;
    let mut value = number(&args, 2, "slider")? as i32;
    let (min, max) = (number(&args, 3, "slider")? as i32, number(&args, 4, "slider")? as i32);
    unsafe { sys::igSliderInt(label.as_ptr(), &mut value, min, max, c"%d".as_ptr(), 0) };
    Ok(vec![LBoxed::from_int(value)])
});

native!(window_same_line, |args, owner| {
    let host = host(&args, owner, "same_line")?;
    drawing(&host, "same_line")?;
    unsafe { sys::igSameLine(0.0, -1.0) };
    Ok(vec![])
});

native!(window_separator, |args, owner| {
    let host = host(&args, owner, "separator")?;
    drawing(&host, "separator")?;
    unsafe { sys::igSeparator() };
    Ok(vec![])
});

native!(window_key, |args, owner| {
    let host = host(&args, owner, "key")?;
    drawing(&host, "key")?;
    let name = text(&args, 1, owner, "key")?;
    let keys: &[sys::ImGuiKey] = match name.to_bytes() {
        b"up" => &[sys::ImGuiKey_UpArrow],
        b"down" => &[sys::ImGuiKey_DownArrow],
        b"left" => &[sys::ImGuiKey_LeftArrow],
        b"right" => &[sys::ImGuiKey_RightArrow],
        b"home" => &[sys::ImGuiKey_Home],
        b"ctrl" => &[sys::ImGuiKey_LeftCtrl, sys::ImGuiKey_RightCtrl],
        b"alt" => &[sys::ImGuiKey_LeftAlt, sys::ImGuiKey_RightAlt],
        b"shift" => &[sys::ImGuiKey_LeftShift, sys::ImGuiKey_RightShift],
        other => return Err(format!("key: no key {:?}", String::from_utf8_lossy(other))),
    };
    let down = keys.iter().any(|&k| unsafe { sys::igIsKeyDown(k) });
    Ok(vec![LBoxed::from_bool(down)])
});

native!(window_typed, |args, owner| {
    let host = host(&args, owner, "typed")?;
    Ok(vec![string(&host.typed)])
});

native!(window_mouse, |args, owner| {
    let host = host(&args, owner, "mouse")?;
    let io = host.imgui.io();
    // Left, right and middle in Dear ImGui's order; Varvara's is left, middle, right.
    let buttons = [(0, 1), (2, 2), (1, 4)].iter().filter(|(i, _)| io.mouse_down[*i]).map(|(_, bit)| bit).sum::<i32>();
    Ok(vec![LBoxed::from_int(buttons), LBoxed::from_double(io.mouse_wheel as f64)])
});

native!(texture_update, |args, owner| {
    let texture = data::<Texture>(&args, 0, owner, "update")?;
    let width = number(&args, 1, "update")? as u32;
    let height = number(&args, 2, "update")? as u32;
    let fg = table(&args, 3, "update")?;
    let bg = table(&args, 4, "update")?;
    let palette = table(&args, 5, "update")?;
    let colors: Vec<[u8; 4]> = (0..4).map(|c| {
        let channel = |i: usize| palette.get_number(owner, (3 * c + i) as f64).as_number().unwrap_or(0.0) as u8;
        [channel(1), channel(2), channel(3), 255]
    }).collect();
    let mut pixels = Vec::with_capacity(width as usize * height as usize * 4);
    for i in 0..(width * height) as usize {
        let index = |layer: &Tc<Table>| layer.get_number(owner, i as f64).as_number().unwrap_or(0.0) as usize & 3;
        let c = match index(&fg) { 0 => index(&bg), c => c };
        pixels.extend_from_slice(&colors[c]);
    }
    let gl = &texture.context;
    unsafe {
        gl.bind_texture(glow::TEXTURE_2D, Some(texture.gl));
        gl.pixel_store_i32(glow::UNPACK_ALIGNMENT, 1);
        if texture.size.get() != (width, height) {
            gl.tex_image_2d(glow::TEXTURE_2D, 0, glow::RGBA as i32, width as i32, height as i32, 0, glow::RGBA, glow::UNSIGNED_BYTE, Some(&pixels));
            texture.size.set((width, height));
        } else {
            gl.tex_sub_image_2d(glow::TEXTURE_2D, 0, 0, 0, width as i32, height as i32, glow::RGBA, glow::UNSIGNED_BYTE, glow::PixelUnpackData::Slice(&pixels));
        }
    }
    Ok(vec![])
});

native!(texture_image, |args, owner| {
    let texture = data::<Texture>(&args, 0, owner, "image")?;
    let scale = number(&args, 1, "image")? as f32;
    let (width, height) = texture.size.get();
    unsafe {
        let mut at = sys::ImVec2 { x: 0.0, y: 0.0 };
        sys::igGetCursorScreenPos(&mut at);
        texture.drawn.set(([at.x, at.y], scale));
        sys::igImage(
            texture.gl.0.get() as usize as sys::ImTextureID,
            sys::ImVec2 { x: width as f32 * scale, y: height as f32 * scale },
            sys::ImVec2 { x: 0.0, y: 0.0 }, sys::ImVec2 { x: 1.0, y: 1.0 },
            sys::ImVec4 { x: 1.0, y: 1.0, z: 1.0, w: 1.0 }, sys::ImVec4 { x: 0.0, y: 0.0, z: 0.0, w: 0.0 },
        );
    }
    Ok(vec![])
});

native!(texture_pointer, |args, owner| {
    let texture = data::<Texture>(&args, 0, owner, "pointer")?;
    let ([x, y], scale) = texture.drawn.get();
    let mut mouse = sys::ImVec2 { x: 0.0, y: 0.0 };
    unsafe { sys::igGetMousePos(&mut mouse) };
    let at = |m: f32, origin: f32| LBoxed::from_int(((m - origin) / scale).floor() as i32);
    Ok(vec![at(mouse.x, x), at(mouse.y, y)])
});

fn main() -> Result<(), Box<dyn Error>> {
    env_logger::builder().format_timestamp(None).format_source_path(true).init();
    let mut args = std::env::args().skip(1);
    let usage = "usage: varvara <app.bin> <rom>";
    let program = args.next().ok_or(usage)?;
    let rom = std::fs::read(args.next().ok_or(usage)?)?;
    let bytecode = std::fs::read(program)?;
    let (_, header) = chunk::header(&bytecode[..]).map_err(|e| format!("not Lua 5.1 bytecode: {e:?}"))?;
    let intern_strings = internment::Arena::new();
    let header = header.globally_intern(&intern_strings);
    let mut owner = Owner::new();
    let vm = Vm::new(&header.top_level as *const _);
    vm.scope(&intern_strings, &mut owner, |s, owner| -> Result<(), Box<dyn Error>> {
        let mut g = s.global_env(owner);
        let key = |name: &str| vm::LBoxed::box_lvalue(vm::InternString::intern(s.intern(), name));
        let methods = |entries: &[(&str, vm::NativeFunc)]| {
            let mut index = Table::new(0, entries.len());
            for &(name, native) in entries {
                index.insert_lvalue(vm::InternString::intern(s.intern(), name), LValue::NClosure(vm::NClosure::new(native)));
            }
            let mut metatable = Table::new(0, 1);
            metatable.insert_lvalue(vm::InternString::intern(s.intern(), "__index"), LValue::Table(Tc::new(index)));
            LBoxed::box_lvalue(LValue::Table(Tc::new(metatable)))
        };
        let window = methods(&[
            ("frame", window_frame), ("texture", window_texture), ("begin", window_begin), ("finish", window_finish),
            ("text", window_text), ("button", window_button), ("checkbox", window_checkbox), ("slider", window_slider),
            ("same_line", window_same_line), ("separator", window_separator), ("key", window_key), ("typed", window_typed),
            ("mouse", window_mouse),
        ]);
        let texture = methods(&[("update", texture_update), ("image", texture_image), ("pointer", texture_pointer)]);
        WINDOW_METATABLE.with(|bits| bits.set(window.bits()));
        TEXTURE_METATABLE.with(|bits| bits.set(texture.bits()));
        let mut ui = Table::new(0, 3);
        ui.insert_lvalue(vm::InternString::intern(s.intern(), "open"), LValue::NClosure(vm::NClosure::new(ui_open)));
        ui.insert_lvalue(vm::InternString::intern(s.intern(), "window_metatable"), window.unbox());
        ui.insert_lvalue(vm::InternString::intern(s.intern(), "texture_metatable"), texture.unbox());
        g.set(owner, key("ui"), LBoxed::box_lvalue(LValue::Table(Tc::new(ui))), s.intern());
        g.set(owner, key("rom"), string(&rom), s.intern());
        let clos = vm::Tc::new(vm::LClosure::new(s.vm().top_level));
        s.run(owner, g.clone(), clos, vec![].into())?;
        Ok(())
    })?;
    Ok(())
}
