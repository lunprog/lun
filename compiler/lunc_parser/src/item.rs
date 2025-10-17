//! Parsing of Lun's item.

use std::str::FromStr;

use lunc_ast::{Abi, ItemContainer};
use lunc_diag::{FileId, Recovered, ResultExt};
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
    /// `ident ":" typexpr? ":" exprWithBlock`
    /// `ident ":" typexpr? ":" exprWithoutBlock ";"`
    GlobalConst {
        name: String,
        name_loc: Span,
        typexpr: Option<Expression>,
        value: Expression,
        loc: Span,
    },
    /// Global variable.
    ///
    /// `ident ":" typexpr? "=" exprWithBlock`
    /// `ident ":" typexpr? "=" exprWithoutBlock ";"`
    GlobalVar {
        name: String,
        name_loc: Span,
        typexpr: Option<Expression>,
        value: Expression,
        loc: Span,
    },
    /// Global uninitialized
    ///
    /// `ident ":" typexpr ";"`
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

            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(recovered) => {
                    if let Recovered::Unable(d) = recovered {
                        self.sink.emit(d);
                    }

                    if let Some(item) = self.recover_item_in_container(ItemContainer::Module) {
                        items.push(item);
                    }
                }
            }
        }

        Ok(Module {
            items,
            fid: self.fid,
        })
    }

    /// Tries to recover the parsing of an item in a module.
    ///
    /// Bumps the parser until it is able to correctly parse an [`Item`] if so
    /// returns `Some(..)`, otherwise it returns `None`.
    ///
    /// If `container` == [`ItemContainer::ExternBlock`], this function will
    /// early return if it sees the matching `}` to the first `{`:
    ///
    /// ```lun
    /// extern "C" {
    ///
    /// // ...
    /// {}
    /// // ...
    ///
    /// } // the parser will recover until here even tho there was a } before
    ///   // but it was preceded by a {
    /// ```
    ///
    /// Please note that this is the last thing that can help in case of a
    /// diagnostic.
    pub(crate) fn recover_item_in_container(&mut self, container: ItemContainer) -> Option<Item> {
        let mut res = None;

        // number of } remaining until the } of the matching {
        let mut remaining_rcurly = 0;

        while res.is_none() {
            self.bump();
            if self.check(ExpToken::EOF) {
                break;
            }

            if container == ItemContainer::ExternBlock {
                if self.check_no_expect(ExpToken::LCurly) {
                    remaining_rcurly += 1;
                } else if self.check_no_expect(ExpToken::RCurly) {
                    if remaining_rcurly == 0 {
                        // eat the }
                        self.bump();

                        break;
                    } else {
                        remaining_rcurly -= 1;
                    }
                }
            }

            match self.parse_item() {
                Ok(item) => {
                    res = Some(item);
                }
                Err(recovered) => {
                    if let Recovered::Unable(d) = recovered {
                        self.sink.emit(d);
                    }
                }
            }
        }

        res
    }

    /// Parses a Lun Item.
    pub fn parse_item(&mut self) -> IResult<Item> {
        match self.token.tt {
            Ident(_) => self.parse_global_item(),
            Pound => self.parse_directive_item(),
            KwExtern => self.parse_extern_block_item(),
            _ => {
                // TEST: no. 1
                Err(ExpectedToken::new(["item"], self.token.clone()).into())
            }
        }
    }

    /// Parses a global const / var
    pub fn parse_global_item(&mut self) -> IResult<Item> {
        // TEST: n/a
        let lo = self.expect(ExpToken::Ident)?;
        let name = self.as_ident();

        // TEST: no. 1
        self.expect(ExpToken::Colon).emit_wdef(self.x());

        let typexpr = match self.token.tt {
            Colon | Eq => None,
            _ => self.parse_typexpr().emit_opt(self.x()),
        };

        let is_const = if self.eat(ExpToken::Colon) {
            // const global def
            true
        } else if self.eat(ExpToken::Eq) {
            // var global def
            false
        } else if !self.in_recovery() {
            // TEST: no. 2
            let hi = self.expect(ExpToken::Semi)?;

            // uninit global def
            let Some(typexpr) = typexpr else {
                // SAFETY: we always parse a typexpr if the token after :
                // isn't : or =
                opt_unreachable!()
            };

            return Ok(Item::GlobalUninit {
                name,
                name_loc: lo.clone(),
                typexpr,
                loc: Span::from_ends(lo, hi),
            });
        } else {
            return Err(Recovered::Yes);
        };

        let value = self.parse_expr()?;

        let hi = if value.is_expr_with_block() {
            self.eat_no_expect(ExpToken::Semi);

            value.loc.clone()
        } else {
            // TEST: no. 3
            self.expect(ExpToken::Semi).emit_wdef(self.x())
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
        let directive_name = self.look_ahead(1, look_tok).clone();

        match &directive_name.tt {
            Ident(id) => match id.as_str() {
                Directive::MOD_NAME => self.parse_mod_directive().map(Item::Directive),
                Directive::IMPORT_NAME => self.parse_import_directive().map(Item::Directive),
                _ => {
                    let Ok(()) = self.recover_directive() else {
                        // SAFETY: recover_directive always returns an Ok(()) in
                        // this case.
                        opt_unreachable!()
                    };

                    Err(UnknownDirective {
                        name: id.clone(),
                        loc: directive_name.loc.clone(),
                    }
                    .into())
                }
            },
            _ => {
                // TEST: no. 2
                let Err(recovered) = self.recover_directive() else {
                    // SAFETY: recover_directive always returns an Err(..) in
                    // this case.
                    opt_unreachable!()
                };
                Err(recovered)
            }
        }
    }

    /// Parses extern block item
    pub fn parse_extern_block_item(&mut self) -> IResult<Item> {
        // TEST: n/a
        let lo = self.expect(ExpToken::KwExtern)?;

        // TEST: no. 1
        let abi = if let Some(Lit {
            kind: LitKind::Str,
            value: LitVal::Str(str),
            ..
        }) = self.eat_lit()
        {
            match Abi::from_str(&str) {
                Ok(abi) => abi,
                Err(()) => {
                    self.sink.emit(UnknownAbi {
                        abi: str,
                        loc: self.token_loc(),
                    });

                    Abi::default()
                }
            }
        } else {
            self.sink.emit(ExpectedToken::new(
                ["string literal"],
                self.prev_token.clone(),
            ));

            Abi::default()
        };

        // TEST: no. 2
        self.expect_nae(ExpToken::LCurly).emit_wdef(self.x());

        let mut items = Vec::new();

        loop {
            if self.eat_no_expect(ExpToken::RCurly) {
                break;
            } else if self.check(ExpToken::EOF) {
                self.expected_token_exps.insert(ExpToken::RCurly);

                let diag = self.expected_diag();
                self.sink.emit(diag);

                self.bump();
                break;
            }

            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(recovered) => {
                    if let Recovered::Unable(d) = recovered {
                        self.sink.emit(d);
                    }

                    if let Some(item) = self.recover_item_in_container(ItemContainer::ExternBlock) {
                        items.push(item);
                    }
                }
            }

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
