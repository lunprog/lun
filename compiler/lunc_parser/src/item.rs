//! Parsing of Lun's item.

use std::str::FromStr;

use lunc_diag::FileId;
use lunc_token::{Lit, LitKind, LitVal};
use lunc_utils::opt_unreachable;

use crate::directive::Directive;

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
#[derive(Debug, Clone, Default, PartialEq, Eq)]
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

/// Lun item.
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
    /// Global uninitialized
    ///
    /// `ident ":" expression ";"`
    GlobalUninit {
        name: String,
        name_loc: Span,
        typexpr: Expression,
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
            Some(Pound) => parse_directive_item(parser),
            Some(KwExtern) => parse_extern_block_item(parser),
            Some(_) => {
                let t = parser.peek_tok().unwrap().clone();
                // TEST: no. 1
                Err(OldExpectedToken::new("item", t.tt, None::<String>, t.loc).into_diag())
            }
            None => Err(parser.eof_diag()),
        }
    }
}

pub fn parse_global_item(parser: &mut Parser) -> Result<Item, Diagnostic> {
    // TEST: n/a
    let (name, lo) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    // TEST: no. 1
    expect_token!(parser => [Colon, ()], Colon);

    let typexpr = match parser.peek_tt() {
        Some(Colon | Eq) => None,
        _ => Some(parse!(@fn parser => Parser::parse_typexpr)),
    };

    let is_const = match parser.peek_tt() {
        Some(Colon) => {
            // const global def
            true
        }
        Some(Eq) => {
            // var global def
            false
        }
        _ => {
            // uninit global def
            let Some(typexpr) = typexpr else {
                // SAFETY: we always parse a typexpr if the token after :
                // isn't : or =
                opt_unreachable!()
            };

            // TEST: no. 2
            let hi = expect_token!(parser => [Semi, ()], Semi).1;

            return Ok(Item::GlobalUninit {
                name,
                name_loc: lo.clone(),
                typexpr,
                loc: Span::from_ends(lo, hi),
            });
        }
    };

    parser.pop();

    let value = parse!(parser => Expression);

    let hi = if value.is_expr_with_block() {
        if let Some(Semi) = parser.peek_tt() {
            parser.pop();
        }

        value.loc.clone()
    } else {
        // TEST: no. 3
        expect_token!(parser => [Semi, ()], Semi).1
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

pub fn parse_directive_item(parser: &mut Parser) -> IResult<Item> {
    // NOTE: already rewritten.
    let directive_name = parser.look_ahead(1, look_tok);

    match &directive_name.tt {
        Ident(id) => match id.as_str() {
            Directive::MOD_NAME => parser.parse_mod_directive().map(Item::Directive),
            Directive::IMPORT_NAME => parser.parse_import_directive().map(Item::Directive),
            _ => Err(UnknownDirective {
                name: id.clone(),
                loc: directive_name.loc.clone(),
            }
            .into_diag()),
        },
        _ => {
            // TEST: no. 2
            Err(parser.recover_directive().unwrap_err())
        }
    }
}

pub fn parse_extern_block_item(parser: &mut Parser) -> Result<Item, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [KwExtern, ()], KwExtern);

    // TEST: no. 1
    let (LitVal::Str(abi_str), abi_loc) = expect_token!(parser => [Lit(Lit { kind: LitKind::Str, value, .. }), value.clone()], "string literal")
    else {
        // SAFETY: literal is guaranteed to contain a string value, if kind is str.
        opt_unreachable!()
    };
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
    expect_token!(parser => [LCurly, ()], LCurly);

    let mut items = Vec::new();

    loop {
        if let Some(RCurly) = parser.peek_tt() {
            break;
        }

        let item = parse!(parser => Item);

        items.push(item);

        if let Some(RCurly) = parser.peek_tt() {
            break;
        }
    }

    // TEST: n/a
    let (_, hi) = expect_token!(parser => [RCurly, ()], RCurly);

    Ok(Item::ExternBlock {
        abi,
        items,
        loc: Span::from_ends(lo, hi),
    })
}
