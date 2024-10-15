#![feature(trait_alias)]
use typewit::{MakeTypeWitness, TypeEq, HasTypeWitness};

typewit::simple_type_witness! {
    enum LValue<'a> {
        U32 = u32,
        F64 = f64,
        STR = &'a str,
    }
}

#[derive(Debug, Clone)]
enum RValue<'a> {
    Int(u32),
    Float(f64),
    Str(&'a str),
}

trait LUnknown<'a> = Clone + std::fmt::Debug + HasTypeWitness<LValue<'a, Self>>;

fn increment<'a, V: LUnknown<'a>>(val: V) -> V {
    match V::WITNESS {
        LValue::U32(te) => {
            println!("int {:?}", te.to_right(val.clone()));
            return te.to_left(te.to_right(val) + 1);
        },
        LValue::F64(te) => {
            println!("float {:?}", te.to_right(val.clone()));
            return te.to_left(te.to_right(val) + 1.0);
        },
        LValue::STR(te) => {
            panic!()
        },
    }
}

fn add_0<'a, 'b, 'c>(left: RValue<'a>, right: RValue<'b>) -> RValue<'c> {
    match left {
        RValue::Int(i) => {
            return add_1(i, right)
        },
        _ => unimplemented!(),
    }
}


fn add_1<'a, 'b, 'c, L: LUnknown<'a>>(left: L, right: RValue<'b>) -> RValue<'c> {
    match right {
        RValue::Int(i) => {
            return add(left, i)
        },
        _ => unimplemented!(),
    }
}

fn add<'a, 'b, 'c, L: LUnknown<'a>, R: LUnknown<'b>>(left: L, right: R) -> RValue<'c> {
    match (L::WITNESS, R::WITNESS) {
        (LValue::U32(l_te), LValue::U32(r_te)) => {
            RValue::Int(l_te.to_right(left) + r_te.to_right(right))
        },
        _ => unimplemented!(),
    }
}

fn increment_r<'a>(rval: RValue<'a>) -> RValue<'a> {
    match rval {
        RValue::Int(i) => RValue::Int(increment(i)),
        RValue::Float(f) => RValue::Float(increment(f)),
        RValue::Str(s) => panic!(),
    }
}

fn main() {
    dbg!(add_0(RValue::Int(1), RValue::Int(2)));

    println!("sandbox");
}
