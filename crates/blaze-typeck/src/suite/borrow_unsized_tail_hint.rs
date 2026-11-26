//! The pointee of an expected `&U` is only a hint for `&`'s operand when the operand is not a
//! place and `U`'s STRUCT TAIL is unsized (rules/op.rs `expr_borrow`).
//!
//! The site is e9 everything-auth src/mcp_oauth.rs:241: `from_row(&entry?)` with
//! `fn from_row(raw: &RawValue)`, `entry: Option<Box<RawValue>>` and serde_json's
//! `struct RawValue { json: str }`. blaze gave "found `Box<RawValue>`, expected `RawValue`
//! (E0308 IncompatibleArms)" at the `?`: its operand was checked with `HasType(RawValue)`, so
//! the desugared match's arms coerced to it.
//!
//! The rule: rustc_hir_typeck expr.rs `check_expr_addr_of` takes `expected.only_has_type()`;
//! for `&T`/`*T` a syntactic place operand gets `ExpectHasType(T)`, any other operand
//! `Expectation::rvalue_hint(T)`, which is `ExpectRvalueLikeUnsized` when `T`'s struct tail is
//! `str`, a slice or `dyn` (expectation.rs). A match's coercion target is then a fresh variable
//! (`coercion_target_type`), and the argument deref-coerces `&Box<RawValue>` after.
//!
//! ```text
//! #[lang = "sized"] trait Sized {}  #[lang = "deref"] trait Deref { type Target: ?Sized; }
//! struct W { s: str }  struct B<T: ?Sized>;  impl<T: ?Sized> Deref for B<T> { type Target = T; }
//! fn take(w: &W) -> u8;
//! fn a(p: B<W>) -> u8 { take(&match p { x => x }) }   // clean (the e9 shape)
//! fn c(p: B<W>) -> u8 { take(&p) }                    // control: a place, clean either way
//! ```
//!
//! CONTROL (rule 23): with the operand's hint `HasType(W)` whatever it is, `a` is E0308 again
//! and the first test fails. `c` is clean either way.

use std::vec::Vec;

use super::check_body;
use crate::fixture::{Bb, Fx};
use crate::ids::{ExprId, LangItem, Mutbl};
use crate::infer::InferPlant;
use crate::machine::Plant;
use crate::portable::PNode;

fn world() -> Fx {
    let mut world = Fx::new();
    let fx = &mut world;
    let sized = fx.tr("Sized", 1, Vec::new(), &[]);
    fx.lang(LangItem::Sized, sized);
    let deref = fx.tr("Deref", 1, Vec::new(), &["Target"]);
    fx.lang(LangItem::Deref, deref);
    let (p0, u8_) = (fx.param(0), fx.u8());
    let str_ = fx.ty(PNode::Str);

    let w_k = fx.strukt("W", 0, &[("s", str_)]);
    let w = fx.adt(w_k, &[]);
    let b_k = fx.strukt("B", 1, &[]);
    let b_t = fx.adt(b_k, &[p0]);
    let imp = fx.imp("impl<T: ?Sized> Deref for B<T>", 1, b_t, Some((deref, &[])), &[("Target", p0)], Vec::new());
    fx.unsized_param(imp, 0);
    let b_w = fx.adt(b_k, &[w]);
    let ref_w = fx.r(Mutbl::Not, w);

    fx.func("take", 0, &[ref_w], u8_, Vec::new());
    fx.func("a", 0, &[b_w], u8_, Vec::new());
    fx.func("c", 0, &[b_w], u8_, Vec::new());
    fx.finish();
    world
}

/// `take(&<operand>)`, the operand made from the parameter `p` by `make`.
fn codes(fx: &Fx, owner: &str, make: impl FnOnce(&mut Bb, ExprId) -> ExprId) -> Vec<&'static str> {
    let mut b = Bb::new();
    let p = b.param("p");
    let take = b.path(&["take"]);
    let p_use = b.local(p);
    let operand = make(&mut b, p_use);
    let r = b.borrow(Mutbl::Not, operand);
    let call = b.call(take, &[r]);
    let root = b.block(&[], Some(call));
    let checked = check_body(fx, &b, fx.key_of(owner), root, Plant::None, InferPlant::None);
    checked.diags.iter().map(|d| d.code.code()).collect()
}

/// The e9 shape. Prints nothing; fails with "a: [\"E0308\"]" before the fix.
#[test]
fn a_borrowed_rvalue_takes_an_unsized_tail_pointee_as_a_hint() {
    let fx = world();
    let got = codes(&fx, "a", |b, p| {
        let x = b.bind("x");
        let x_use = b.local(x);
        b.match_(p, &[(x, x_use)])
    });
    assert!(got.is_empty(), "a: {got:?}");
}

/// A place operand: clean before and after.
#[test]
fn control_a_borrowed_place_deref_coerces() {
    let fx = world();
    let got = codes(&fx, "c", |_, p| p);
    assert!(got.is_empty(), "c: {got:?}");
}
