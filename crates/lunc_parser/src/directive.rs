//! Parsing of lun's directives.

use crate::item::Item;

use super::*;

/// Directive in an item
#[derive(Debug, Clone)]
pub enum ItemDirective {
    /// "#" "mod" ident ";"
    Mod { name: String, loc: Span },
}

pub fn parse_mod_directive(parser: &mut Parser) -> Result<Item, Diagnostic> {
    let (_, lo) =
        expect_token!(parser => [Punct(Punctuation::Hashtag), ()], Punct(Punctuation::Hashtag));

    match parser.peek_tt() {
        Some(Ident(id)) if id.as_str() == "mod" => {
            parser.pop();
        }
        Some(_) => {
            let t = parser.peek_tok().unwrap().clone();

            return Err(ExpectedToken::new(["mod"], t.tt, Some("directive"), t.loc).into_diag());
        }
        _ => return Err(parser.eof_diag()),
    }

    let (name, _) = expect_token!(parser => [Ident(s), s.clone()], "integer literal");

    let (_, hi) =
        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));

    Ok(Item::Directive(ItemDirective::Mod {
        name,
        loc: Span::from_ends(lo, hi),
    }))
}
