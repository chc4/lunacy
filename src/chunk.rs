use nom::{
  bytes::complete::{tag, take_while_m_n, take},
  number::{complete::{le_u8, le_u32, le_u64, f64}, Endianness},
  branch::alt,
  combinator::{map, map_res, verify, opt},
  sequence::tuple,
  IResult,
  Parser, error::ParseError, InputLength, InputIter, Slice,
};
use core::fmt::{Formatter, Debug};
use std::{ops::RangeFrom, fmt::Display};
use bitfield::bitfield;
use crate::vm::{Opcode, Number};

fn lua_number(input: &[u8]) -> IResult<&[u8], Number> {
    map(f64(Endianness::Little), |f| Number(f))(input)
}

#[derive(Clone)]
pub struct PackedString<'a> {
    len: usize,
    pub data: &'a [u8],
}

impl<'a> Debug for PackedString<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.len == 0 {
            return write!(f, "\"\"")
        }
        if let Ok(s) = std::ffi::CStr::from_bytes_with_nul(self.data) {
            write!(f, "{:?}", s)
        } else {
            write!(f, "<invalid utf>")
        }
    }
}

pub fn packed_string(input: &[u8]) -> IResult<&[u8], PackedString<'_>> {
    let (input, len) = map_res(le_u64, |i| usize::try_from(i))(input)?;
    let (input, data) = take(len)(input)?;
    Ok((input, PackedString { len, data }))
}

pub struct PackedList<T> {
    count: u32,
    pub items: Vec<T>,
}

impl<T> Debug for PackedList<T> where T: Debug {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.items)
    }
}

fn packed_list<I, O, E, F>(f: F) -> impl FnMut(I) -> IResult<I, PackedList<O>, E>
where
    I: Clone + PartialEq + InputLength + InputIter<Item=u8> + Slice<RangeFrom<usize>>,
    F: Parser<I, O, E> + Copy,
    E: ParseError<I>
{
    move |input: I| {
        let (input, list_count) = le_u32(input)?;
        let (input, items) = nom::multi::count(f, list_count as usize)(input)?;
        Ok((input, PackedList { count: list_count, items }))
    }
}

bitfield! {
    pub struct InstBits(u32);
    impl Debug;
    pub u8, into Opcode, Opcode, _: 6, 0;
    pub A, _: 14, 6;
    pub C, _: 23, 14;
    pub B, _: 31, 23;

    pub Bx, _: 31, 14;

    pub sBx, _: 31, 14;
}

impl Clone for InstBits {
    fn clone(&self) -> Self {
        InstBits(self.0)
    }
}

impl Copy for InstBits {
}

pub struct Instruction(pub InstBits);

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:08x}", self.0.0)
    }
}

fn instruction(input: &[u8]) -> IResult<&[u8], Instruction> {
    map(le_u32, |i| Instruction(InstBits(i)))(input)
}

#[derive(Clone)]
pub enum Constant<'src> {
    Nil,
    Bool(bool),
    Number(Number),
    String(PackedString<'src>)
}

impl<'a> Debug for Constant<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Nil => write!(f, "nil"),
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Number(i) => write!(f, "{}", i.0),
            Constant::String(s) => write!(f, "{:?}", s),
        }
    }
}

fn constant(input: &[u8]) -> IResult<&[u8], Constant<'_>> {
    let (input, ctype) = le_u8(input)?;
    match ctype {
        0 => Ok((input, Constant::Nil)),
        1 => {
            let (input, bval) = alt((tag("\x00"), tag("\x01")))(input)?;
            let bval = match bval[0] {
                0 => false,
                1 => true,
                _ => unreachable!()
            };
            Ok((input, Constant::Bool(bval)))
        },
        3 => {
            map(lua_number, |i| Constant::Number(i))(input)
        },
        4 => {
            map(packed_string, |s| {
                Constant::String(s)
            })(input)
        },
        _ => unreachable!()
    }
}

#[derive(Debug)]
struct LocalInfo<'a> {
    name: PackedString<'a>,
    start_pc: u32,
    end_pc: u32,
}

fn local_info(input: &[u8]) -> IResult<&[u8], LocalInfo<'_>> {
    map(tuple((packed_string, le_u32, le_u32)), |(name, start_pc, end_pc)| {
        LocalInfo { name: name, start_pc, end_pc }
    })(input)
}

#[derive(Debug)]
pub struct Header<'a> {
    pub top_level: FunctionBlock<'a>
}

#[derive(Debug)]
pub struct FunctionBlock<'a> {
    pub source: PackedString<'a>,
    pub upval_count: u8,
    pub param_count: u8,
    pub is_vararg: u8,
    pub max_stack: u8,
    pub instructions: PackedList<Instruction>,
    pub constants: PackedList<Constant<'a>>,
    pub line_info: PackedList<u32>, // Empty list if stripped
    pub local_info: PackedList<LocalInfo<'a>>, // Empty list if stripped
    pub upvalues: PackedList<PackedString<'a>>,
    pub prototypes: PackedList<FunctionBlock<'a>>,
}

pub fn function_block(input: &[u8]) -> IResult<&[u8], FunctionBlock> {
    let (input, (source, line_defined, last_line, upval_count, param_count, is_vararg, max_stack)) =
        tuple((packed_string, le_u32, le_u32, le_u8, le_u8, le_u8, le_u8))(input)?;
    dbg!(&source);
    let (input, instructions) = packed_list(instruction)(input)?;
    dbg!(&instructions.items.iter().map(|inst| inst.0.Opcode()).collect::<Vec<_>>());
    let (input, constants) = packed_list(constant)(input)?;
    dbg!(&constants);
    let (input, prototypes) = packed_list(function_block)(input)?;
    dbg!(&prototypes);
    let (input, line_info) = packed_list(le_u32)(input)?;
    dbg!(&line_info);
    let (input, local_info) = packed_list(local_info)(input)?;
    dbg!(&local_info);
    let (input, upvalues) = packed_list(packed_string)(input)?;
    dbg!(&upvalues);
    Ok((input, FunctionBlock {
        source,
        // lines,
        upval_count,
        param_count,
        is_vararg,
        max_stack,
        instructions,
        constants,
        prototypes,
        line_info,
        local_info,
        upvalues,
    }))
}

pub fn header(input: &[u8]) -> IResult<&[u8], Header> {
    let (input, _) = tag("\x1bLua")(input)?;
    let (input, (version, format, endianness, int_size, sizet_size, inst_size, number_size, integral)) =
        tuple((le_u8, le_u8, le_u8, le_u8, le_u8, le_u8, le_u8, le_u8))(input)?;
    assert_eq!(int_size, 4);
    assert_eq!(endianness, 1);
    assert_eq!(sizet_size, 8);
    let (input, top_level) = function_block(input)?;
    Ok((input, Header {
        top_level
    }))
}
