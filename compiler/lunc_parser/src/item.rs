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
            if self.token.tt == Eof {
                break;
            }

            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(recovered) => {
                    if let Recovered::Unable(d) = recovered {
                        self.sink.emit(d);
                    }

                    self.recover_item_in_container(ItemContainer::Module);
                    continue;
                }
            }
        }

        Ok(Module {
            items,
            fid: self.fid,
        })
    }

    /// Tries to recover the parsing of an Item in `container`.
    ///
    /// The parser is bump until `self.token` is `token.can_begin_item() ==
    /// true`. If `container == ItemContainer::ExternBlock` it also returns when
    /// `self.token` is a `RCurly` that matches the first `LCurly`:
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
    pub fn recover_item_in_container(&mut self, container: ItemContainer) {
        // amount of } remaining until the one that will break the loop
        let mut remaining_rcurly = 0;

        while !self.token.can_begin_item() && !self.check_no_expect(ExpToken::Eof) {
            if container == ItemContainer::ExternBlock {
                if self.check_no_expect(ExpToken::LCurly) {
                    remaining_rcurly += 1;
                } else if self.check_no_expect(ExpToken::RCurly) {
                    if remaining_rcurly == 0 {
                        break;
                    } else {
                        remaining_rcurly -= 1;
                    }
                }
            }

            self.bump();
        }
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
        self.expect(ExpToken::Colon).emit(self.x());

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
            self.expect_nae(ExpToken::Semi).emit(self.x());

            // if semi was there it's his correct location,
            // if semi was not here it's a dummy location.
            self.prev_token.loc.clone()
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

            // NOTE: here we are not recovering from this error because it's too
            // messy if we do so.
            self.recover_item_in_container(ItemContainer::ExternBlock);

            // bump (without it, it complains about the RCurly be unexpected for
            // an item)
            self.bump();

            return Err(Recovered::Yes);
        };

        // TEST: no. 2
        self.expect(ExpToken::LCurly).emit(self.x());

        let mut items = Vec::new();

        loop {
            if self.eat_no_expect(ExpToken::RCurly) {
                break;
            } else if self.check(ExpToken::Eof) {
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

                    self.recover_item_in_container(ItemContainer::ExternBlock);
                    continue;
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
