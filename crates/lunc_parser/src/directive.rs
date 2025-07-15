//! Parsing of lun's directives.

use crate::item::Item;

use super::*;

/// Directive in an item
#[derive(Debug, Clone)]
pub enum ItemDirective {
    /// "#" "mod" ident ";"
    Mod { name: String, loc: Span },
    /// "#" "use" path [ "as" ident ] ";"
    Use {
        path: EffectivePath,
        alias: Option<String>,
        loc: Span,
    },
}

pub fn parse_mod_directive(parser: &mut Parser) -> Result<Item, Diagnostic> {
    let (_, lo) =
        expect_token!(parser => [Punct(Punctuation::Hashtag), ()], Punct(Punctuation::Hashtag));

    expect_token!(parser => [Ident(id), id.clone(), if id.as_str() == "mod"], Ident(String::new()));

    let (name, _) = expect_token!(parser => [Ident(s), s.clone()], "integer literal");

    let (_, hi) =
        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));

    Ok(Item::Directive(ItemDirective::Mod {
        name,
        loc: Span::from_ends(lo, hi),
    }))
}

pub fn parse_use_directive(parser: &mut Parser) -> Result<Item, Diagnostic> {
    let (_, lo) =
        expect_token!(parser => [Punct(Punctuation::Hashtag), ()], Punct(Punctuation::Hashtag));

    expect_token!(parser => [Ident(id), id.clone(), if id.as_str() == "use"], Ident(String::new()));

    let path = parse!(parser => EffectivePath);

    let alias = if let Some(Kw(Keyword::As)) = parser.peek_tt() {
        parser.pop();
        let alias = expect_token!(noloc: parser => [Ident(id), id.clone()], Ident(String::new()));

        Some(alias)
    } else {
        None
    };

    let (_, hi) =
        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));

    Ok(Item::Directive(ItemDirective::Use {
        path,
        alias,
        loc: Span::from_ends(lo, hi),
    }))
}

/// ident { "." ident }
#[derive(Debug, Clone)]
pub struct EffectivePath {
    pub path: Vec<String>,
    pub loc: Span,
}

impl AstNode for EffectivePath {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut path = Vec::new();
        let (id, lo) = expect_token!(parser => [Ident(id), id.clone(); Kw(Keyword::Orb), String::from("orb")], Ident(String::new()));
        path.push(id);

        let mut hi = lo.clone();
        while let Some(Punct(Punctuation::Dot)) = parser.peek_tt() {
            parser.pop();

            let (id, h) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));
            hi = h;
            path.push(id);
        }

        Ok(EffectivePath {
            path,
            loc: Span::from_ends(lo, hi),
        })
    }
}
