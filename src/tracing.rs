use std::fs::File;
use std::io::{BufWriter, Write};
use std::time::Instant;
use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::OnceLock;

pub struct Tracer {
    writer: BufWriter<File>,
    start_time: Instant,
    string_table: HashMap<String, u16>,
    next_string_index: u16,
    pid: u32,
}

impl Tracer {
    pub fn new(path: &str) -> Self {
        let file = File::create(path).expect("Failed to create trace file");
        let mut tracer = Self {
            writer: BufWriter::new(file),
            start_time: Instant::now(),
            string_table: HashMap::new(),
            next_string_index: 1, // index 0 is empty string
            pid: std::process::id(),
        };

        // 1. Magic Number Record: Type 0 (Metadata), Size 1, Metadata Type 4 (Trace Info), Magic 0x16547846
        tracer.write_word((1u64 << 4) | (4u64 << 16) | (0x16547846u64 << 24));

        // 2. Initialization Record: 1 tick = 1 microsecond
        // Type 1, Size 2. This is what zjit uses.
        tracer.write_word(1u64 | (2u64 << 4));
        tracer.write_word(1_000_000u64);

        // 3. Register thread at index 1: (process_koid=pid, thread_koid=1)
        // Record Type 3 (Thread Record), Size 3, Thread Index 1
        tracer.write_word(3u64 | (3u64 << 4) | (1u64 << 16));
        tracer.write_word(tracer.pid as u64);
        tracer.write_word(1u64); // TID 1

        tracer
    }

    fn write_word(&mut self, val: u64) {
        let _ = self.writer.write_all(&val.to_le_bytes()).unwrap();
    }

    fn write_padded_bytes(&mut self, bytes: &[u8]) {
        let _ = self.writer.write_all(bytes).unwrap();
        let remainder = bytes.len() % 8;
        if remainder != 0 {
            let _ = self.writer.write_all(&[0u8; 7][..8 - remainder]).unwrap();
        }
    }

    fn intern_string(&mut self, s: &str) -> u16 {
        if s.is_empty() { return 0; }
        if let Some(&idx) = self.string_table.get(s) {
            return idx;
        }
        if self.next_string_index >= 0x8000 { return 0; }

        let idx = self.next_string_index;
        let bytes = s.as_bytes();
        let len = bytes.len().min(0x7FFF);
        let words = (len + 7) / 8;
        let size = 1 + words;

        // Record Type 2: String Record
        // [0:3] Type=2, [4:15] Size, [16:30] Index, [32:46] Length
        let header = 2u64 | ((size as u64) << 4) | ((idx as u64) << 16) | ((len as u64) << 32);
        self.write_word(header);
        self.write_padded_bytes(&bytes[..len]);

        self.string_table.insert(s.to_string(), idx);
        self.next_string_index += 1;
        idx
    }

    pub fn write_event(&mut self, ev_type: u64, category: &str, name: &str, args: &[(&str, TraceValue)]) {
        let cat_ref = self.intern_string(category) as u64;
        let name_ref = self.intern_string(name) as u64;
        let ts = self.start_time.elapsed().as_micros() as u64;

        let n_args = args.len().min(15) as u64;
        let mut frame_refs = Vec::with_capacity(n_args as usize);
        for (arg_name, arg_val) in args.iter().take(15) {
            let name_ref = self.intern_string(arg_name) as u64;
            match arg_val {
                TraceValue::String(s) => {
                    let val_ref = self.intern_string(s) as u64;
                    frame_refs.push((name_ref, Some(val_ref), None));
                }
                TraceValue::Uint64(n) => {
                    frame_refs.push((name_ref, None, Some(*n)));
                }
            }
        }

        let mut arg_words = 0;
        for (_, val_ref, _) in &frame_refs {
            if val_ref.is_some() {
                arg_words += 1;
            } else {
                arg_words += 2;
            }
        }
        let size = 2 + arg_words;

        // Record Type 4: Event Record
        // [0:3] Type=4, [4:15] Size, [16:19] Event Type, [20:23] Arg Count
        // [24:31] Thread Ref (Type 1 (bit 0), Index 1 (bits 1-7) -> 3)
        let thread_ref = 3u64;
        let header = 4u64 | (size << 4) | (ev_type << 16) | (n_args << 20) | (thread_ref << 24) | (cat_ref << 32) | (name_ref << 48);
        self.write_word(header);
        self.write_word(ts);

        for (name_ref, val_ref, u64_val) in frame_refs {
            if let Some(vr) = val_ref {
                // Argument Type 6: String, Size 1
                let arg_header = 6u64 | (1 << 4) | (name_ref << 16) | (vr << 32);
                self.write_word(arg_header);
            } else if let Some(uv) = u64_val {
                // Argument Type 3: Uint64, Size 2
                let arg_header = 3u64 | (2 << 4) | (name_ref << 16);
                self.write_word(arg_header);
                self.write_word(uv);
            }
        }
    }
}

pub enum TraceValue<'a> {
    String(&'a str),
    Uint64(u64),
}

impl<'a> From<&'a str> for TraceValue<'a> {
    fn from(s: &'a str) -> Self {
        TraceValue::String(s)
    }
}

impl From<u64> for TraceValue<'static> {
    fn from(n: u64) -> Self {
        TraceValue::Uint64(n)
    }
}

impl From<usize> for TraceValue<'static> {
    fn from(n: usize) -> Self {
        TraceValue::Uint64(n as u64)
    }
}

static TRACER: OnceLock<Mutex<Tracer>> = OnceLock::new();

pub fn init(path: &str) {
    let tracer = Tracer::new(path);
    let _ = TRACER.set(Mutex::new(tracer));
}

pub fn instant(category: &str, name: &str, args: &[(&str, TraceValue)]) {
    if let Some(tracer) = TRACER.get() {
        if let Ok(mut tracer) = tracer.lock() {
            tracer.write_event(0, category, name, args);
        }
    }
}

pub fn begin(category: &str, name: &str, args: &[(&str, TraceValue)]) {
    if let Some(tracer) = TRACER.get() {
        if let Ok(mut tracer) = tracer.lock() {
            tracer.write_event(2, category, name, args);
        }
    }
}

pub fn end(category: &str, name: &str, args: &[(&str, TraceValue)]) {
    if let Some(tracer) = TRACER.get() {
        if let Ok(mut tracer) = tracer.lock() {
            tracer.write_event(3, category, name, args);
        }
    }
}

pub fn flush() {
    if let Some(tracer) = TRACER.get() {
        if let Ok(mut tracer) = tracer.lock() {
            let _ = tracer.writer.flush();
        }
    }
}
