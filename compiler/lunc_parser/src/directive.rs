//! Parsing of lun's directives.

use lunc_ast::symbol::EffectivePath;

use crate::item::Item;

use super::*;

/// Directive in an item
#[derive(Debug, Clone)]
pub enum Directive {
    /// `"#" "mod" ident ";"`
    Mod { name: String, loc: Span },
    /// `"#" "import" path [ "as" ident ] ";"`
    Import {
        path: SpannedPath,
        alias: Option<String>,
        loc: Span,
    },
}

impl Directive {
    /// Name of the [`Directive::Mod`].
    pub const MOD_NAME: &str = "mod";

    /// Name of the [`Directive::Import`].
    pub const IMPORT_NAME: &str = "import";

    /// List of every supported directives name.
    pub const DIRECTIVES: &[&str] = &[
        // all the directives V
        Directive::MOD_NAME,
        Directive::IMPORT_NAME,
    ];
}

pub fn parse_mod_directive(parser: &mut Parser) -> Result<Item, Diagnostic> {
    // TEST: n/a
    let (_, lo) =
        expect_token!(parser => [Punct(Punctuation::Hashtag), ()], Punct(Punctuation::Hashtag));

    // TEST: n/a
    expect_token!(parser => [Ident(id), id.clone(), if id.as_str() == Directive::MOD_NAME], Ident(String::new()));

    // TEST: no. 1
    let (name, _) = expect_token!(parser => [Ident(s), s.clone()], Ident(String::new()));

    // TEST: no. 2
    let (_, hi) =
        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));

    Ok(Item::Directive(Directive::Mod {
        name,
        loc: Span::from_ends(lo, hi),
    }))
}

pub fn parse_import_directive(parser: &mut Parser) -> Result<Item, Diagnostic> {
    // TEST: n/a
    let (_, lo) =
        expect_token!(parser => [Punct(Punctuation::Hashtag), ()], Punct(Punctuation::Hashtag));

    // TEST: n/a
    expect_token!(parser => [Ident(id), id.clone(), if id.as_str() == Directive::IMPORT_NAME], Ident(String::new()));

    let path = parse!(parser => SpannedPath);

    let alias = if let Some(Kw(Keyword::As)) = parser.peek_tt() {
        parser.pop();
        // TEST: no. 1
        let alias = expect_token!(noloc: parser => [Ident(id), id.clone()], Ident(String::new()));

        Some(alias)
    } else {
        None
    };

    // TEST: no. 2
    let (_, hi) =
        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punct(Punctuation::Semicolon));

    Ok(Item::Directive(Directive::Import {
        path,
        alias,
        loc: Span::from_ends(lo, hi),
    }))
}

/// Spanned [EffectivePath].
#[derive(Debug, Clone)]
pub struct SpannedPath {
    pub path: EffectivePath,
    pub loc: Span,
}

impl AstNode for SpannedPath {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut path = Vec::new();
        // TEST: no. 1
        let (id, lo) = expect_token!(parser => [Ident(id), id.clone(); Kw(Keyword::Orb), String::from("orb")], Ident(String::new()));
        path.push(id);

        let mut hi = lo.clone();
        while let Some(Punct(Punctuation::Dot)) = parser.peek_tt() {
            parser.pop();

            // TEST: no. 2
            let (id, h) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));
            hi = h;
            path.push(id);
        }

        Ok(SpannedPath {
            path: EffectivePath::from_vec(path),
            loc: Span::from_ends(lo, hi),
        })
    }
}
