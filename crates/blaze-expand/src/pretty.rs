//! A proc macro's `TokenStream::to_string`, written as rustc writes it: `rustc_ast_pretty`'s
//! `tts_to_string`, the spacing of `print_tts` (`space_between`) and the line breaking of its
//! Oppen printer (`pp.rs`, a 78-column margin). Macros hash this text (a schema lock's
//! fingerprint is the hash of `quote!(#item).to_string()`), so it is matched byte for byte,
//! newlines and indentation included, not only token for token.
//!
//! The tokens are the bridge's, made by the macro: an identifier, a literal and a group are
//! `Alone` to rustc (`ToInternal`), a punct as the macro set it. Two puncts rustc glues into one
//! token (`..`, a lifetime's `'` and its name) are read as that one token where `space_between`
//! asks about it.

use blaze_own::Vec;
use core::alloc::Allocator;

use crate::tokens::Delim;

/// One token of the stream to print, in order, groups as their two delimiters.
#[derive(Clone, Copy, Debug)]
pub enum PrettyTok<'s> {
    Open(Delim),
    Close(Delim),
    Ident { text: &'s str, raw: bool },
    Punct { ch: char, joint: bool },
    /// The literal as written (`-1`, `"a\n"`, `1u8`).
    Literal { text: &'s str },
}

/// `pp.rs`'s `MARGIN` and `MIN_SPACE`, and `INDENT_UNIT`.
const MARGIN: isize = 78;
const MIN_SPACE: isize = 60;
const INDENT_UNIT: isize = 4;

/// The printer's tokens: every break is `space()`'s one blank.
#[derive(Clone, Copy)]
enum Pp<'s> {
    Str(&'s str),
    Break { offset: isize },
    Begin { offset: isize, consistent: bool },
    End,
}

/// What `space_between` reads of a tree.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Tree {
    /// `dot`: a `.` that is a token of its own, not glued into `..`.
    Punct { ch: char, dot: bool },
    /// `call`: no space before a parenthesis (not reserved, or `fn`, `Self`, `pub`, raw).
    Ident { call: bool },
    Lifetime,
    /// `negative`: rustc's tokens are a `-` and the literal.
    Literal { negative: bool },
    Group(Delim),
}

/// Words rustc's `is_reserved` holds, but `fn`, `Self` and `pub`, which `space_between` lets a
/// parenthesis follow unspaced.
const RESERVED: &[&str] = &[
    "_", "$crate", "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false",
    "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut", "ref", "return",
    "self", "static", "struct", "super", "trait", "true", "type", "unsafe", "use", "where",
    "while", "async", "await", "dyn", "abstract", "become", "box", "do", "final", "macro",
    "override", "priv", "typeof", "unsized", "virtual", "yield", "try", "gen",
];

/// rustc's `space_between(prev, next)`, both `Alone`.
fn space_between(prev: Tree, next: Tree) -> bool {
    let prev_punct = matches!(prev, Tree::Punct { .. });
    let next_punct = matches!(next, Tree::Punct { .. } | Tree::Literal { negative: true });
    match (prev, next) {
        (Tree::Punct { dot: true, .. }, _) if !next_punct => false,
        (Tree::Punct { ch: '$', .. }, Tree::Ident { .. }) => false,
        (_, Tree::Punct { ch: ',' | ';', .. } | Tree::Punct { dot: true, .. }) if !prev_punct => false,
        (Tree::Ident { call: true }, Tree::Group(Delim::Paren)) => false,
        (Tree::Punct { ch: '#', .. }, Tree::Group(Delim::Bracket)) => false,
        _ => true,
    }
}

fn open_text(delim: Delim) -> &'static str {
    match delim {
        Delim::Paren => "(",
        Delim::Brace => "{",
        Delim::Bracket => "[",
        Delim::Invisible => "",
    }
}

fn close_text(delim: Delim) -> &'static str {
    match delim {
        Delim::Paren => ")",
        Delim::Brace => "}",
        Delim::Bracket => "]",
        Delim::Invisible => "",
    }
}

/// The tree token `at` starts, as `space_between` reads it.
fn tree_at(toks: &[PrettyTok<'_>], at: usize) -> Tree {
    let joint_punct = |at: Option<usize>, want: char| {
        matches!(at.and_then(|at| toks.get(at)), Some(PrettyTok::Punct { ch, joint: true }) if *ch == want)
    };
    match toks[at] {
        PrettyTok::Open(delim) | PrettyTok::Close(delim) => Tree::Group(delim),
        PrettyTok::Ident { text, raw } => {
            if joint_punct(at.checked_sub(1), '\'') {
                Tree::Lifetime
            } else {
                Tree::Ident { call: raw || !RESERVED.contains(&text) }
            }
        }
        PrettyTok::Punct { ch: '\'', joint: true } if matches!(toks.get(at + 1), Some(PrettyTok::Ident { .. })) => {
            Tree::Lifetime
        }
        PrettyTok::Punct { ch, joint } => {
            let glued_before = joint_punct(at.checked_sub(1), '.');
            let glued_after = joint && matches!(toks.get(at + 1), Some(PrettyTok::Punct { ch: '.' | '=', .. }));
            Tree::Punct { ch, dot: ch == '.' && !glued_before && !glued_after }
        }
        PrettyTok::Literal { text } => Tree::Literal { negative: text.starts_with('-') },
    }
}

/// `toks` as rustc's `TokenStream::to_string` writes them, handed to `out` piece by piece.
/// `toks` is balanced (the bridge's streams are).
pub fn pretty_print<A: Allocator + Clone>(toks: &[PrettyTok<'_>], alloc: A, out: &mut impl FnMut(&str)) {
    // `print_tts` and `print_mac_common`, the printer's tokens laid out.
    let mut pp: Vec<Pp<'_>, A> = Vec::new_in(alloc.clone());
    // Per open level: the tree before (and whether it is `Alone`), and whether the group is empty.
    let mut levels: Vec<(Option<(Tree, bool)>, bool), A> = Vec::new_in(alloc.clone());
    levels.push((None, false));
    for (at, tok) in toks.iter().enumerate() {
        if let PrettyTok::Close(delim) = *tok {
            let Some((_, empty)) = levels.pop() else { break };
            if delim == Delim::Brace {
                pp.push(Pp::End);
                // `bclose`: `break_offset_if_not_bol(1, -INDENT_UNIT)`, never at a line's start
                // here (an `End` was the last token).
                if !empty {
                    pp.push(Pp::Break { offset: -INDENT_UNIT });
                }
                pp.push(Pp::Str("}"));
                pp.push(Pp::End);
            } else {
                pp.push(Pp::End);
                pp.push(Pp::Str(close_text(delim)));
            }
            if let Some(level) = levels.last_mut() {
                level.0 = Some((Tree::Group(delim), true));
            }
            continue;
        }
        let tree = tree_at(toks, at);
        if let Some(&(Some((prev, true)), _)) = levels.last()
            && space_between(prev, tree)
        {
            pp.push(Pp::Break { offset: 0 });
        }
        let alone = match *tok {
            PrettyTok::Open(delim) => {
                let empty = matches!(toks.get(at + 1), Some(PrettyTok::Close(_)));
                if delim == Delim::Brace {
                    pp.push(Pp::Begin { offset: INDENT_UNIT, consistent: true });
                    pp.push(Pp::Str("{"));
                    if !empty {
                        pp.push(Pp::Break { offset: 0 });
                    }
                } else {
                    pp.push(Pp::Str(open_text(delim)));
                }
                pp.push(Pp::Begin { offset: 0, consistent: false });
                if let Some(level) = levels.last_mut() {
                    level.0 = None;
                }
                levels.push((None, empty));
                continue;
            }
            PrettyTok::Ident { text, raw } => {
                if raw {
                    pp.push(Pp::Str("r#"));
                }
                pp.push(Pp::Str(text));
                true
            }
            PrettyTok::Punct { ch, joint } => {
                pp.push(Pp::Str(punct_text(ch)));
                !joint
            }
            PrettyTok::Literal { text } => {
                pp.push(Pp::Str(text));
                true
            }
            PrettyTok::Close(_) => unreachable!("a close is laid out above"),
        };
        if let Some(level) = levels.last_mut() {
            level.0 = Some((tree, alone));
        }
    }

    // `scan_*` and `check_stack`: a begin's size runs to the first break after its end at its
    // own depth or above, a break's to the next break at its depth or above (or the end).
    let mut size: Vec<isize, A> = Vec::from_elem_in(0, pp.len(), alloc.clone());
    let mut stack: Vec<usize, A> = Vec::new_in(alloc.clone());
    let mut right: isize = 0;
    let check = |stack: &mut Vec<usize, A>, size: &mut Vec<isize, A>, pp: &[Pp<'_>], right: isize| {
        let mut depth = 0usize;
        while let Some(&at) = stack.last() {
            match pp[at] {
                Pp::Begin { .. } => {
                    if depth == 0 {
                        break;
                    }
                    stack.pop();
                    size[at] += right;
                    depth -= 1;
                }
                Pp::End => {
                    stack.pop();
                    size[at] = 1;
                    depth += 1;
                }
                _ => {
                    stack.pop();
                    size[at] += right;
                    if depth == 0 {
                        break;
                    }
                }
            }
        }
    };
    for at in 0..pp.len() {
        match pp[at] {
            Pp::Begin { .. } => {
                size[at] = -right;
                stack.push(at);
            }
            Pp::End => stack.push(at),
            Pp::Break { .. } => {
                check(&mut stack, &mut size, &pp, right);
                size[at] = -right;
                stack.push(at);
                right += 1;
            }
            Pp::Str(text) => right += text.len() as isize,
        }
    }
    check(&mut stack, &mut size, &pp, right);
    while let Some(at) = stack.pop() {
        if !matches!(pp[at], Pp::End) {
            size[at] += right;
        }
    }

    // `print_begin`, `print_end`, `print_break`, `print_string`.
    #[derive(Clone, Copy)]
    enum Frame {
        Fits,
        Broken { indent: isize, consistent: bool },
    }
    let mut frames: Vec<Frame, A> = Vec::new_in(alloc);
    let mut space = MARGIN;
    let mut indent: isize = 0;
    let mut pending: isize = 0;
    const SPACES: &str = "                                                                ";
    for (at, entry) in pp.iter().enumerate() {
        match *entry {
            Pp::Begin { offset, consistent } => {
                if size[at] > space {
                    frames.push(Frame::Broken { indent, consistent });
                    indent += offset;
                } else {
                    frames.push(Frame::Fits);
                }
            }
            Pp::End => {
                if let Some(Frame::Broken { indent: before, .. }) = frames.pop() {
                    indent = before;
                }
            }
            Pp::Break { offset } => {
                let fits = match frames.last() {
                    Some(Frame::Fits) => true,
                    Some(Frame::Broken { consistent: true, .. }) => false,
                    Some(Frame::Broken { consistent: false, .. }) | None => size[at] <= space,
                };
                if fits {
                    pending += 1;
                    space -= 1;
                } else {
                    out("\n");
                    let to = (indent + offset).max(0);
                    pending = to;
                    space = (MARGIN - to).max(MIN_SPACE);
                }
            }
            Pp::Str(text) => {
                while pending > 0 {
                    let take = (pending as usize).min(SPACES.len());
                    out(&SPACES[..take]);
                    pending -= take as isize;
                }
                out(text);
                space -= text.len() as isize;
            }
        }
    }
}

/// A punct's one character as text (the bridge's puncts are ASCII).
fn punct_text(ch: char) -> &'static str {
    const PUNCTS: &str = "!#$%&'*+,-./:;<=>?@^|~";
    match PUNCTS.find(ch) {
        Some(at) => &PUNCTS[at..at + 1],
        None => "?",
    }
}

#[cfg(test)]
mod tests {
    extern crate std;
    use std::string::String;

    use super::*;

    fn print(toks: &[PrettyTok<'_>]) -> String {
        let mut out = String::new();
        pretty_print(toks, std::alloc::Global, &mut |s| out.push_str(s));
        out
    }

    fn id(text: &str) -> PrettyTok<'_> {
        PrettyTok::Ident { text, raw: false }
    }

    fn p(ch: char) -> PrettyTok<'static> {
        PrettyTok::Punct { ch, joint: false }
    }

    /// What rustc 1.97 prints for `quote!(#item).to_string()` of
    /// `#[derive(Default, Clone, Serialize, Deserialize)] pub struct Tally { total: i64, }`:
    /// the line is past the margin, so the break before the brace group is taken.
    #[test]
    fn a_long_struct_breaks_before_its_body() {
        use PrettyTok::{Close, Open};
        let toks = [
            p('#'),
            Open(Delim::Bracket),
            id("derive"),
            Open(Delim::Paren),
            id("Default"),
            p(','),
            id("Clone"),
            p(','),
            id("Serialize"),
            p(','),
            id("Deserialize"),
            Close(Delim::Paren),
            Close(Delim::Bracket),
            id("pub"),
            id("struct"),
            id("Tally"),
            Open(Delim::Brace),
            id("total"),
            p(':'),
            id("i64"),
            p(','),
            Close(Delim::Brace),
        ];
        assert_eq!(print(&toks), "#[derive(Default, Clone, Serialize, Deserialize)] pub struct Tally\n{ total : i64, }");
        // The same without two derives fits on one line.
        let short: std::vec::Vec<_> = toks[..4].iter().chain(&toks[8..]).copied().collect();
        assert_eq!(print(&short), "#[derive(Serialize, Deserialize)] pub struct Tally { total : i64, }");
    }

    #[test]
    fn spacing_follows_space_between() {
        use PrettyTok::{Close, Open};
        let joint = |ch| PrettyTok::Punct { ch, joint: true };
        let toks = [
            id("f"),
            Open(Delim::Paren),
            id("x"),
            p('.'),
            id("y"),
            Close(Delim::Paren),
            p(';'),
            id("let"),
            Open(Delim::Paren),
            Close(Delim::Paren),
            joint(':'),
            p(':'),
            id("a"),
            joint('.'),
            p('.'),
            id("b"),
            p('&'),
            joint('\''),
            id("a"),
            Open(Delim::Brace),
            Close(Delim::Brace),
        ];
        assert_eq!(print(&toks), "f(x.y); let () :: a .. b & 'a {}");
    }
}
