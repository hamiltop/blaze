//! A struct's ctor registers the struct's where-clauses at its arguments (rules/lit_path.rs
//! `value_def_ty`, `Def::Ctor`; rules/adt.rs `expr_struct` for a literal).
//!
//! The site is e9 everything-edge src/request_span.rs:89: `let mut unrun = Unrun(Some(finish),
//! PhantomData);` for `struct Unrun<O, F: FnOnce(Option<O>)>(Option<F>, PhantomData<fn(O)>)`
//! in `fn finish_after<E, O, F: FnOnce(Option<O>)>`. Only the struct's bound decides `O`.
//! blaze gave "found `{unknown}` (E0282 AnnotationsNeeded) undecided: generic argument #0 of
//! Unrun ... no goal is pending on it".
//!
//! The rule: rustc `predicates_of(ctor)` is its parent ADT's, and `instantiate_value_path`
//! registers them (`add_required_obligations_for_hir`), as a fn path's. With `F` the caller's
//! parameter, `F: Tr<?O>` is met by the caller's `F: Tr<O>` alone, which decides `?O = O`.
//!
//! ```text
//! #[lang = "sized"] trait Sized {}  trait Tr<O> {}
//! struct P<O, F: Tr<O>>(F);
//! fn a<O, F: Tr<O>>(f: F) { let _u = P(f); }   // clean (the e9 shape)
//! struct Q<O, F>(F);
//! fn b<O, F: Tr<O>>(f: F) { let _u = Q(f); }   // the twin: no clause, `O` undecided (E0282)
//! ```
//!
//! CONTROL (rule 23): with the ctor's `register_predicates` removed, `a` is E0282 again and
//! the first test fails. `b` is never clean.

use std::vec::Vec;

use super::check_body;
use crate::fixture::{Bb, Fx};
use crate::ids::LangItem;
use crate::infer::InferPlant;
use crate::machine::Plant;
use crate::world::{CtorKind, Def};

fn world() -> Fx {
    let mut world = Fx::new();
    let fx = &mut world;
    let sized = fx.tr("Sized", 1, Vec::new(), &[]);
    fx.lang(LangItem::Sized, sized);
    let tr = fx.tr("Tr", 2, Vec::new(), &[]);
    let (p0, p1) = (fx.param(0), fx.param(1));
    let unit = fx.unit();

    let p_k = fx.tuple_strukt("P", 2, &[p1]);
    let f_tr_o = fx.bound(tr, &[p1, p0]);
    fx.set_adt_clauses(p_k, Vec::from([f_tr_o]));
    fx.use_path("P", Def::Ctor { adt: p_k, variant: 0, kind: CtorKind::Tuple });
    let q_k = fx.tuple_strukt("Q", 2, &[p1]);
    fx.use_path("Q", Def::Ctor { adt: q_k, variant: 0, kind: CtorKind::Tuple });

    let f_tr_o = fx.bound(tr, &[p1, p0]);
    fx.func("a", 2, &[p1], unit, Vec::from([f_tr_o]));
    let f_tr_o = fx.bound(tr, &[p1, p0]);
    fx.func("b", 2, &[p1], unit, Vec::from([f_tr_o]));
    fx.finish();
    world
}

/// `{ let _u = <ctor>(f); }` in `owner`.
fn codes(fx: &Fx, owner: &str, ctor: &str) -> Vec<&'static str> {
    let mut b = Bb::new();
    let f = b.param("f");
    let callee = b.path(&[ctor]);
    let f_use = b.local(f);
    let call = b.call(callee, &[f_use]);
    let u = b.bind("_u");
    let s = b.let_(u, None, call);
    let root = b.block(&[s], None);
    let checked = check_body(fx, &b, fx.key_of(owner), root, Plant::None, InferPlant::None);
    checked.diags.iter().map(|d| d.code.code()).collect()
}

/// The e9 shape. Prints nothing; fails with "a: [\"E0282\"]" before the fix.
#[test]
fn a_ctor_registers_its_structs_where_clauses() {
    let fx = world();
    let got = codes(&fx, "a", "P");
    assert!(got.is_empty(), "a: {got:?}");
}

/// No clause on the struct: nothing decides `O`.
#[test]
fn control_a_struct_with_no_clause_leaves_the_parameter_undecided() {
    let fx = world();
    let got = codes(&fx, "b", "Q");
    assert_eq!(got, Vec::from(["E0282"]), "b");
}
