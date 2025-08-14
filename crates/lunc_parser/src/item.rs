//! Parsing of lun's definitions.

use std::str::FromStr;

use lunc_diag::FileId;

use crate::{
    directive::{Directive, parse_import_directive, parse_mod_directive},
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
        let mut items = Vec::new();

        loop {
            if let None | Some(TokenType::EOF) = parser.peek_tt() {
                break;
            }

            items.push(parse!(parser => Item));
        }

        Ok(Module {
            items,
            fid: parser.fid,
        })
    }
}

/// ABI names usable in an extern block
#[derive(Debug, Clone, Default)]
pub enum Abi {
    /// `C`
    #[default]
    C,
}

impl FromStr for Abi {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "C" => Ok(Abi::C),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    /// Global constant.
    ///
    /// `ident ":" expression? ":" exprWithBlock`
    /// `ident ":" expression? ":" exprWithoutBlock ";"`
    GlobalConst {
        name: String,
        name_loc: Span,
        typexpr: Option<Expression>,
        value: Expression,
        loc: Span,
    },
    /// Global variable.
    ///
    /// `ident ":" expression? "=" exprWithBlock`
    /// `ident ":" expression? "=" exprWithoutBlock ";"`
    GlobalVar {
        name: String,
        name_loc: Span,
        typexpr: Option<Expression>,
        value: Expression,
        loc: Span,
    },
    /// Extern block.
    ///
    /// `"extern" ident "{" ( item )* "}"`
    ExternBlock {
        abi: Abi,
        items: Vec<Item>,
        loc: Span,
    },
    /// A directive, always starts with `#`
    Directive(Directive),
}

impl AstNode for Item {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        match parser.peek_tt() {
            Some(Ident(_)) => parse_global_item(parser),
            Some(Punct(Punctuation::Hashtag)) => parse_directive_item(parser),
            Some(Kw(Keyword::Extern)) => parse_extern_block_item(parser),
            Some(_) => {
                let t = parser.peek_tok().unwrap().clone();
                // TEST: no. 1
                Err(ExpectedToken::new("item", t.tt, None::<String>, t.loc).into_diag())
            }
            None => Err(parser.eof_diag()),
        }
    }
}

pub fn parse_global_item(parser: &mut Parser) -> Result<Item, Diagnostic> {
    // TEST: n/a
    let (name, lo) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    // TEST: no. 1
    expect_token!(parser => [Punct(Punctuation::Colon), ()], Punctuation::Colon);

    let typexpr = match parser.peek_tt() {
        Some(Punct(Punctuation::Colon | Punctuation::Equal)) => None,
        _ => Some(parse!(@fn parser => parse_typexpr)),
    };

    // TEST: no. 2
    let (is_const, _) = expect_token!(
        parser => [
            Punct(Punctuation::Colon), true;
            Punct(Punctuation::Equal), false;
        ],
        [Punctuation::Colon, Punctuation::Equal]
    );

    let value = parse!(parser => Expression);

    let hi = if !value.is_expr_with_block() {
        // TEST: no. 3
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
            Directive::MOD_NAME => parse_mod_directive(parser),
            Directive::IMPORT_NAME => parse_import_directive(parser),
            _ => {
                let t = parser.nth_tok(1).unwrap().clone();
                Err(UnknownDirective {
                    name: id.clone(),
                    loc: t.loc,
                }
                .into_diag())
            }
        },
        _ => {
            let t = parser.nth_tok(1).unwrap().clone();
            // TEST: no. 2
            Err(
                ExpectedToken::new(TokenType::Ident(String::new()), t.tt, None::<String>, t.loc)
                    .into_diag(),
            )
        }
    }
}

pub fn parse_extern_block_item(parser: &mut Parser) -> Result<Item, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Extern), ()], Kw(Keyword::Extern));

    // TEST: no. 1
    let (abi_str, abi_loc) = expect_token!(parser => [StringLit(s), s.clone()], "string literal");
    let abi = match Abi::from_str(&abi_str) {
        Ok(abi) => abi,
        Err(()) => {
            parser.sink.emit(UnknownAbi {
                abi: abi_str,
                loc: abi_loc,
            });

            Abi::default()
        }
    };

    // TEST: no. 2
    expect_token!(parser => [Punct(Punctuation::LBrace), ()], Punct(Punctuation::LBrace));

    let mut items = Vec::new();

    loop {
        if let Some(Punct(Punctuation::RBrace)) = parser.peek_tt() {
            break;
        }

        let item = parse!(parser => Item);

        items.push(item);

        if let Some(Punct(Punctuation::RBrace)) = parser.peek_tt() {
            break;
        }
    }

    // TEST: n/a
    let (_, hi) =
        expect_token!(parser => [Punct(Punctuation::RBrace), ()], Punct(Punctuation::RBrace));

    Ok(Item::ExternBlock {
        abi,
        items,
        loc: Span::from_ends(lo, hi),
    })
}
