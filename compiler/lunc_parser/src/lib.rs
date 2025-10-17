//! Parser of the lun language.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{borrow::Cow, fmt::Debug, mem};

use diags::*;
use expr::Expression;
use item::Module;

use lunc_ast::{Mutability, Spanned};
use lunc_diag::{DiagnosticSink, FileId, IResult, Recovered, ToDiagnostic};
use lunc_token::{
    ExpToken, ExpTokenSet, Lit, Token, TokenStream,
    TokenType::{self, *},
};
use lunc_utils::{Recovery, Span, opt_unreachable};

pub mod diags;
pub mod directive;
pub mod expr;
pub mod item;
pub mod pretty;
pub mod stmt;

/// Parser of Lun, turns Tokens into an Ast.
#[derive(Debug, Clone)]
pub struct Parser {
    /// Token stream
    pub tokstream: TokenStream,
    /// Token index
    ti: usize,
    /// Sink of diags
    pub sink: DiagnosticSink,
    /// File id of the file we are currently parsing
    pub fid: FileId,
    /// The current token
    pub token: Token,
    /// The previous token
    pub prev_token: Token,
    /// The expected token reprs.
    pub expected_token_exps: ExpTokenSet,
    /// is the parser in recovery mode?
    pub recovery: Recovery,
}

impl Parser {
    /// Create a new parser with the given token stream.
    pub fn new(tokstream: TokenStream, sink: DiagnosticSink, fid: FileId) -> Parser {
        let token = tokstream.get(0).clone();

        Parser {
            tokstream,
            ti: 0,
            sink,
            fid,
            token,
            prev_token: Token::dummy(),
            expected_token_exps: ExpTokenSet::new(),
            recovery: Recovery::No,
        }
    }

    /// Methods used to shorten the length of [`ResultExt`] methods like:
    /// `RES.emit_wdef(self.x());`.
    ///
    /// [`ResultExt`]: lunc_diag::ResultExt
    pub fn x(&mut self) -> lunc_diag::X<'_> {
        (&mut self.sink, &mut self.recovery)
    }

    /// Is the parser currently in recovery mode?
    #[inline(always)]
    pub fn in_recovery(&mut self) -> bool {
        self.recovery == Recovery::Yes
    }

    /// Advances the parser by one token.
    pub fn bump(&mut self) {
        // get the next token
        self.ti += 1;
        let next = self.tokstream.get(self.ti).clone();

        // update the current and previous token
        self.prev_token = mem::replace(&mut self.token, next);

        // diagnostic.
        self.expected_token_exps.clear();
    }

    /// Checks if the next token is `exp.tok`, if so returns `true`.
    ///
    /// This method add `exp` to the `Parser::expected_token_exps` set if `exp`
    /// is not encountered.
    pub fn check(&mut self, exp: ExpToken) -> bool {
        let is_present = self.token.tt == exp;

        if !is_present {
            self.expected_token_exps.insert(exp);
        }

        is_present
    }

    /// [`Parser::check`] but do not add `exp` to
    /// [`Parser::expected_token_exps`].
    #[inline(always)]
    pub fn check_no_expect(&self, exp: ExpToken) -> bool {
        self.token.tt == exp
    }

    /// Consumes the `exp.tok` if it exists. Returns `true` if it existed or
    /// `false` if it did not.
    pub fn eat(&mut self, exp: ExpToken) -> bool {
        let is_present = self.check(exp);

        if is_present {
            self.bump();
        }

        is_present
    }

    /// Consumes one of the `edible` if it exists, and return true, or check if
    /// it's in `inedible` and return true. In other cases return false.
    ///
    /// # Note
    ///
    /// This function adds neither `exp`s from `edible` or `inedible` into
    /// [`Parser::expected_token_exps`]
    pub fn eat_one_of(
        &mut self,
        edible: impl IntoIterator<Item = ExpToken>,
        inedible: impl IntoIterator<Item = ExpToken>,
    ) -> bool {
        if edible.into_iter().any(|exp| self.check_no_expect(exp)) {
            self.bump();
            true
        } else {
            inedible.into_iter().any(|exp| self.check_no_expect(exp))
        }
    }

    /// [`Parser::eat`] but do not add `exp` to
    /// [`Parser::expected_token_exps`].
    pub fn eat_no_expect(&mut self, exp: ExpToken) -> bool {
        let is_present = self.check_no_expect(exp);

        if is_present {
            self.bump();
        }

        is_present
    }

    /// Consumes the next token if it is a [`TokenType::Lit`]. Returns
    /// `Some(lit)` if it existed or `None` if it did not.
    pub fn eat_lit(&mut self) -> Option<Lit> {
        match &self.token.tt {
            TokenType::Lit(lit) => {
                let lit = lit.clone();
                self.bump();

                Some(lit)
            }
            _ => None,
        }
    }

    /// Expects and consumes the token `exp`, or something else if it's not
    /// `exp`. Signals an error is the next token isn't `exp`. Returns the span
    /// of the consumed token if it was the correct one.
    #[inline(never)]
    pub fn expect(&mut self, exp: ExpToken) -> IResult<Span> {
        self._expect_advance(exp, true)?;
        Ok(self.token_loc())
    }

    /// Expects and consumes the token `exp` if it exists. Signals an error if
    /// the next token isn't `exp`.
    ///
    /// *`expect_nae` for `EXPECT Not Always Eat`*
    #[inline(never)]
    pub fn expect_nae(&mut self, exp: ExpToken) -> IResult<()> {
        self._expect_advance(exp, false)?;
        Ok(())
    }

    #[inline(always)]
    fn _expect_advance(&mut self, exp: ExpToken, eat_unexpected: bool) -> IResult<()> {
        if !self.eat(exp) {
            // token was not present
            let diag = self.expected_diag().into_diag();

            if eat_unexpected {
                self.bump();
            }

            return Err(Recovered::Unable(diag));
        }

        Ok(())
    }

    /// Create a new expected diag with the current token and the
    /// [`Parser::expected_token_exps`].
    ///
    /// # Note
    ///
    /// This function also resets the [`Parser::expected_token_exps`].
    pub fn expected_diag(&mut self) -> ExpectedToken {
        let res = ExpectedToken::new(ExpectedToken::EMPTY, self.token.clone())
            .add_expects(self.expected_token_exps);

        self.expected_token_exps.clear();

        res
    }

    /// Look-ahead `dist` tokens away from [`Parser::token`], when `dist == 0`,
    /// it is equivalent to accessing [`Parser::token`].
    pub fn look_ahead<'a, R: 'a>(&'a self, dist: usize, looker: impl FnOnce(&'a Token) -> R) -> R {
        if dist == 0 {
            looker(&self.token)
        } else {
            looker(self.tokstream.get(self.ti + dist))
        }
    }

    /// Look many (`N`) tokens ahead of `dist` tokens from the current one. If
    /// the number of token to look exceeds the number of tokens in the token
    /// stream it will return enough of the EOF token to make it `N` long.
    pub fn look_many_ahead<R, const N: usize>(
        &self,
        dist: usize,
        looker: impl FnOnce([&Token; N]) -> R,
    ) -> R {
        const {
            if N == 0 {
                panic!("cannot use look_many_ahead with N = 0.")
            } else if N == 1 {
                panic!("use look_ahead")
            }
        }

        let dist_abs = dist + self.ti;
        let cow: Cow<'_, [Token]> = self.tokstream.get_slice(dist_abs..dist_abs + N);
        debug_assert_eq!(cow.len(), N);

        let slice: &[Token] = cow.as_ref();

        if cfg!(debug_assertions) && cow.is_empty() && N != 0 {
            panic!("failed to compute the length of the array to output")
        }

        let Ok(arr1): Result<&[Token; N], _> = slice.try_into() else {
            // SAFETY: guaranteed by TokenStream::get_slice.
            opt_unreachable!()
        };

        let arr = arr1.each_ref();

        looker(arr)
    }

    /// Like [`Parser::look_many_ahead`] but gives access to the [`TokenType`]
    /// instead of the [`Token`].
    #[inline(always)]
    pub fn look_many_tt<R, const N: usize>(
        &self,
        dist: usize,
        looker: impl FnOnce([&TokenType; N]) -> R,
    ) -> R {
        self.look_many_ahead(dist, |t: [&Token; N]| {
            let tts = t.map(|t| &t.tt);
            looker(tts)
        })
    }

    /// Return the literal contained in the previously parsed token,
    /// [`Parser::prev_token`].
    ///
    /// # Safety
    ///
    /// Calling this function if [`Parser::prev_token`] isn't a
    /// [`TokenType::Lit`], it's a UB.
    pub fn as_lit(&self) -> Lit {
        let Lit(lit) = &self.prev_token.tt else {
            // SAFETY: upheld by caller
            opt_unreachable!();
        };

        lit.clone()
    }

    /// Return the identifier (the string) contained in the previously parsed
    /// token, [`Parser::prev_token`].
    ///
    /// # Safety
    ///
    /// Calling this function if [`Parser::prev_token`] isn't a
    /// [`TokenType::Ident`], it's a UB.
    pub fn as_ident(&self) -> String {
        let Ident(id) = &self.prev_token.tt else {
            // SAFETY: upheld by caller
            opt_unreachable!();
        };

        id.clone()
    }

    /// Clones the location of the previous token, [`Parser::prev_token`].
    #[inline(always)]
    pub fn token_loc(&self) -> Span {
        self.prev_token.loc.clone()
    }

    /// Returns the current expected token diagnostic and then bump the parser.
    pub fn etd_and_bump<T>(&mut self) -> IResult<T> {
        let diag = self.expected_diag().into_diag();

        self.bump();

        Err(Recovered::Unable(diag))
    }

    /// Parse mutability, either `mut` / *nothing*.
    pub fn parse_mutability(&mut self) -> Mutability {
        if self.eat_no_expect(ExpToken::KwMut) {
            Mutability::Mut
        } else {
            Mutability::Not
        }
    }

    /// Parses and produce a module.
    pub fn produce(&mut self) -> Option<Module> {
        let module = match self.parse_module() {
            Ok(ast) => ast,
            Err(recovered) => {
                if let Recovered::Unable(d) = recovered {
                    self.sink.emit(d);
                }
                return None;
            }
        };

        if self.sink.failed() {
            return None;
        }

        Some(module)
    }
}

/// Look token used in [`Parser::look_ahead`]
pub fn look_tok(tok: &Token) -> &Token {
    tok
}

/// Look token type used in [`Parser::look_ahead`]
pub fn look_tt(tok: &Token) -> &TokenType {
    &tok.tt
}
