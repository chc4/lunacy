#![allow(non_snake_case)]
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

use internment::Arena;

use log::debug;

fn lua_number(input: &[u8]) -> IResult<&[u8], Number> {
    map(f64(Endianness::Little), |f| Number(f))(input)
}

#[derive(Clone, PartialEq, Eq, PartialOrd)]
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
    pub u8, into Opcode, Opcode, _: 5, 0;
    pub A, _: 13, 6;
    pub C, _: 22, 14;
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

#[derive(Copy, Clone)]
pub struct Instruction(pub InstBits);

impl Debug for Instruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:08x}", self.0.0)
    }
}

fn instruction(input: &[u8]) -> IResult<&[u8], Instruction> {
    map(le_u32, |i| Instruction(InstBits(i)))(input)
}

#[derive(Clone, Eq, PartialEq)]
pub enum Constant<S: PartialEq + Eq> {
    Nil,
    Bool(bool),
    Number(Number),
    String(S)
}

impl<S: Debug + PartialEq + Eq> Debug for Constant<S> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Constant::Nil => write!(f, "nil"),
            Constant::Bool(b) => write!(f, "{}", b),
            Constant::Number(i) => write!(f, "{}", i.0),
            Constant::String(s) => write!(f, "{:?}", s),
        }
    }
}

fn constant(input: &[u8]) -> IResult<&[u8], Constant<PackedString<'_>>> {
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
pub struct Header<'a, C> {
    pub top_level: FunctionBlock<'a, C>
}

#[derive(Debug)]
pub struct FunctionBlock<'a, C> {
    pub source: PackedString<'a>,
    pub upval_count: u8,
    pub param_count: u8,
    pub is_vararg: u8,
    pub max_stack: u8,
    pub instructions: PackedList<Instruction>,
    pub constants: PackedList<C>,
    pub line_info: PackedList<u32>, // Empty list if stripped
    pub local_info: PackedList<LocalInfo<'a>>, // Empty list if stripped
    pub upvalues: PackedList<PackedString<'a>>,
    pub prototypes: PackedList<FunctionBlock<'a, C>>,
}

pub fn function_block(input: &[u8]) -> IResult<&[u8], FunctionBlock<Constant<PackedString<'_>>>> {
    let (input, (source, line_defined, last_line, upval_count, param_count, is_vararg, max_stack)) =
        tuple((packed_string, le_u32, le_u32, le_u8, le_u8, le_u8, le_u8))(input)?;
    debug!("source {:?}", &source);
    let (input, instructions) = packed_list(instruction)(input)?;
    debug!("instructions {:?}", &instructions.items.iter().map(|inst| inst.0.Opcode()).collect::<Vec<_>>());
    let (input, constants) = packed_list(constant)(input)?;
    debug!("constants {:?}", &constants);
    let (input, prototypes) = packed_list(function_block)(input)?;
    debug!("prototypes {:?}", &prototypes);
    let (input, line_info) = packed_list(le_u32)(input)?;
    debug!("line_info {:?}", &line_info);
    let (input, local_info) = packed_list(local_info)(input)?;
    debug!("local_info {:?}", &local_info);
    let (input, upvalues) = packed_list(packed_string)(input)?;
    debug!("upvalues {:?}", &upvalues);
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

pub fn header(input: &[u8]) -> IResult<&[u8], Header<Constant<PackedString<'_>>>> {
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

impl<'src> Constant<PackedString<'src>> {
    pub fn globally_intern<'intern>(self, intern: &'intern Arena<&'src [u8]>)
        -> Constant<internment::ArenaIntern<'intern, &'src [u8]>>
    {
        match self {
            Constant::Nil => Constant::Nil,
            Constant::Bool(b) => Constant::Bool(b),
            Constant::Number(n) => Constant::Number(n),
            Constant::String(s) => Constant::String(intern.intern(s.data)),
            _ => unimplemented!()
        }
    }
}

impl<'src> FunctionBlock<'src, Constant<PackedString<'src>>> {
    pub fn globally_intern<'intern>(self, intern: &'intern Arena<&'src [u8]>)
        -> FunctionBlock<'src, Constant<internment::ArenaIntern<'intern, &'src [u8]>>>
    {
        let FunctionBlock {
            source,
            upval_count,
            param_count,
            is_vararg,
            max_stack,
            instructions,
            constants,
            prototypes,
            line_info,
            local_info,
            upvalues
        } = self;
        // intern all the constants
        let PackedList::<_> { count: const_count, items: mut const_items } = constants;
        let const_items = const_items.drain(..).map(|con| con.globally_intern(intern)).collect();
        // intern all the nested prototypes
        let PackedList::<Self> { count: proto_count, items: mut proto_items } = prototypes;
        let proto_items = proto_items.drain(..).map(|proto| proto.globally_intern(intern)).collect();
        let new_self = FunctionBlock::<'src, Constant<internment::ArenaIntern<'intern, &'src [u8]>>> {
            source,
            upval_count,
            param_count,
            is_vararg,
            max_stack,
            instructions,
            constants: PackedList { count: const_count, items: const_items },
            prototypes: PackedList { count: proto_count, items: proto_items },
            line_info,
            local_info,
            upvalues
        };

        new_self
    }
}

impl<'src> Header<'src, Constant<PackedString<'src>>> {
    pub fn globally_intern<'intern>(self, intern: &'intern Arena<&'src [u8]>)
        -> Header<'src, Constant<internment::ArenaIntern<'intern, &'src [u8]>>>
        where 'src: 'intern
    {
        Header::<'src, _> {
            top_level: self.top_level.globally_intern(intern),
        }
    }
}
