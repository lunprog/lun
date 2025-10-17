//! Parsing of Lun's item.

use std::str::FromStr;

use lunc_ast::Abi;
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

/// Parsing for Lun items
impl Parser {
    /// Parses a Lun Module.
    pub fn parse_module(&mut self) -> IResult<Module> {
        let mut items = Vec::new();

        loop {
            if self.token.tt == EOF {
                break;
            }

            items.push(self.parse_item()?);
        }

        Ok(Module {
            items,
            fid: self.fid,
        })
    }

    /// Parses a Lun Item.
    pub fn parse_item(&mut self) -> IResult<Item> {
        match self.token.tt {
            Ident(_) => self.parse_global_item(),
            Pound => self.parse_directive_item(),
            KwExtern => self.parse_extern_block_item(),
            _ => {
                // TEST: no. 1
                Err(ExpectedToken::new(["item"], self.token.clone()).into_diag())
            }
        }
    }

    /// Parses a global const / var
    pub fn parse_global_item(&mut self) -> IResult<Item> {
        // TEST: n/a
        let lo = self.expect(ExpToken::Ident)?;
        let name = self.as_ident();

        // TEST: no. 1
        self.expect(ExpToken::Colon)?;

        let typexpr = match self.token.tt {
            Colon | Eq => None,
            _ => Some(self.parse_typexpr()?),
        };

        let is_const = if self.eat_no_expect(ExpToken::Colon) {
            // const global def
            true
        } else if self.eat_no_expect(ExpToken::Eq) {
            // var global def
            false
        } else {
            // uninit global def
            let Some(typexpr) = typexpr else {
                // SAFETY: we always parse a typexpr if the token after :
                // isn't : or =
                opt_unreachable!()
            };

            // TEST: no. 2
            let hi = self.expect(ExpToken::Semi)?;

            return Ok(Item::GlobalUninit {
                name,
                name_loc: lo.clone(),
                typexpr,
                loc: Span::from_ends(lo, hi),
            });
        };

        let value = self.parse_expr()?;

        let hi = if value.is_expr_with_block() {
            self.eat_no_expect(ExpToken::Semi);

            value.loc.clone()
        } else {
            // TEST: no. 3
            self.expect(ExpToken::Semi)?
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

    /// Parses item directive.
    pub fn parse_directive_item(&mut self) -> IResult<Item> {
        let directive_name = self.look_ahead(1, look_tok);

        match &directive_name.tt {
            Ident(id) => match id.as_str() {
                Directive::MOD_NAME => self.parse_mod_directive().map(Item::Directive),
                Directive::IMPORT_NAME => self.parse_import_directive().map(Item::Directive),
                _ => Err(UnknownDirective {
                    name: id.clone(),
                    loc: directive_name.loc.clone(),
                }
                .into_diag()),
            },
            _ => {
                // TEST: no. 2
                Err(self.recover_directive().unwrap_err())
            }
        }
    }

    /// Parses extern block item
    pub fn parse_extern_block_item(&mut self) -> IResult<Item> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwExtern)?;

        // TEST: no. 1
        let (abi_str, abi_loc) = if let Some(Lit {
            kind: LitKind::Str,
            value: LitVal::Str(str),
            ..
        }) = self.eat_lit()
        {
            (str, self.token_loc())
        } else {
            // self.bump();

            return Err(
                ExpectedToken::new(["string literal"], self.prev_token.clone()).into_diag(),
            );
        };

        let abi = match Abi::from_str(&abi_str) {
            Ok(abi) => abi,
            Err(()) => {
                self.sink.emit(UnknownAbi {
                    abi: abi_str,
                    loc: abi_loc,
                });

                Abi::default()
            }
        };

        // TEST: no. 2
        self.expect(ExpToken::LCurly)?;

        let mut items = Vec::new();

        loop {
            if self.eat_no_expect(ExpToken::RCurly) {
                break;
            }

            items.push(self.parse_item()?);

            if self.eat_no_expect(ExpToken::RCurly) {
                break;
            }
        }

        let hi = self.token_loc();

        Ok(Item::ExternBlock {
            abi,
            items,
            loc: Span::from_ends(lo, hi),
        })
    }
}
