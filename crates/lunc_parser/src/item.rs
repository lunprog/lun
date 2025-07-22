//! Parsing of lun's definitions.

use lunc_diag::FileId;

use crate::{
    directive::{ItemDirective, parse_mod_directive, parse_use_directive},
    expr::parse_typexpr,
};

use super::*;

/// Visibility
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Vis {
    #[default]
    Private,
    Public,
}

/// Lun program.
#[derive(Debug, Clone)]
pub struct Module {
    pub items: Vec<Item>,
    pub fid: FileId,
}

impl AstNode for Module {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut defs = Vec::new();

        loop {
            if let None | Some(TokenType::EOF) = parser.peek_tt() {
                break;
            }

            defs.push(parse!(parser => Item));
        }

        Ok(Module {
            items: defs,
            fid: parser.fid,
        })
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    /// Global constant.
    ///
    /// ident ":" expression? ":" exprWithBlock
    /// ident ":" expression? ":" exprWithoutBlock ";"
    GlobalConst {
        name: String,
        name_loc: Span,
        typexpr: Option<Expression>,
        value: Expression,
        loc: Span,
    },
    /// Global variable.
    ///
    /// ident ":" expression? "=" expr ";"
    GlobalVar {
        name: String,
        name_loc: Span,
        typexpr: Option<Expression>,
        value: Expression,
        loc: Span,
    },
    /// A directive, always starts with #
    Directive(ItemDirective),
}

impl AstNode for Item {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        match parser.peek_tt() {
            Some(Ident(_)) => parse_global_item(parser),
            Some(Punct(Punctuation::Hashtag)) => parse_directive_item(parser),
            Some(_) => {
                let t = parser.peek_tok().unwrap().clone();
                Err(ExpectedToken::new("item", t.tt, None::<String>, t.loc).into_diag())
            }
            None => Err(parser.eof_diag()),
        }
    }
}

pub fn parse_global_item(parser: &mut Parser) -> Result<Item, Diagnostic> {
    let (name, lo) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    expect_token!(parser => [Punct(Punctuation::Colon), ()], Punctuation::Colon);

    let typexpr = match parser.peek_tt() {
        Some(Punct(Punctuation::Colon | Punctuation::Equal)) => None,
        _ => Some(parse!(@fn parser => parse_typexpr)),
    };

    let (is_const, _) = expect_token!(
        parser => [
            Punct(Punctuation::Colon), true;
            Punct(Punctuation::Equal), false;
        ],
        [Punctuation::Colon, Punctuation::Equal]
    );

    let value = parse!(parser => Expression);

    let hi = if !value.is_expr_with_block() || !is_const {
        expect_token!(parser => [Punct(Punctuation::Semicolon), ()], Punctuation::Semicolon).1
    } else {
        value.loc.clone()
    };

    let loc = Span::from_ends(lo.clone(), hi);

    if is_const {
        Ok(Item::GlobalConst {
            name,
            name_loc: lo,
            typexpr,
            value,
            loc,
        })
    } else {
        Ok(Item::GlobalVar {
            name,
            name_loc: lo,
            typexpr,
            value,
            loc,
        })
    }
}

pub fn parse_directive_item(parser: &mut Parser) -> Result<Item, Diagnostic> {
    match parser.nth_tt(1) {
        Some(Ident(id)) => match id.as_str() {
            "mod" => parse_mod_directive(parser),
            "use" => parse_use_directive(parser),
            _ => {
                let t = parser.nth_tok(1).unwrap().clone();
                Err(ExpectedToken::new(["mod"], t.tt, Some("directive"), t.loc).into_diag())
            }
        },
        _ => {
            let t = parser.nth_tok(1).unwrap().clone();
            Err(ExpectedToken::new(["mod"], t.tt, Some("directive"), t.loc).into_diag())
        }
    }
}
