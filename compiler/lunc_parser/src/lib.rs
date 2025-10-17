//! Parser of the lun language.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]
// TODO: remove me
#![allow(deprecated)]

use std::{borrow::Cow, fmt::Debug, mem};

use diags::*;
use expr::Expression;
use item::Module;

use lunc_ast::{Mutability, Spanned};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, IResult, ReachedEOF, ToDiagnostic};
use lunc_token::{
    ExpToken, ExpTokenSet, Lit, Token, TokenStream,
    TokenType::{self, *},
};
use lunc_utils::{Span, opt_unreachable, pretty::PrettyDump};

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
        }
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

    /// Expects and consumes the token `exp.tok`, or something else if it's no
    /// `exp.tok`. Signals an error is the next token isn't `exp.tok`. Returns
    /// the span of the consumed token if it was the correct one.
    pub fn expect(&mut self, exp: ExpToken) -> IResult<Span> {
        if !self.eat(exp) {
            // token was not present
            let diag = self.expected_diag().into_diag();

            self.bump();

            return Err(diag);
        }

        Ok(self.token_loc())
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
    pub fn etd_and_bump(&mut self) -> Diagnostic {
        let diag = self.expected_diag().into_diag();

        self.bump();

        diag
    }

    /// Parse mutability, either `mut` / *nothing*.
    pub fn parse_mutability(&mut self) -> Mutability {
        if self.eat_no_expect(ExpToken::KwMut) {
            Mutability::Mut
        } else {
            Mutability::Not
        }
    }

    // TODO: deprecate and then remove when no longer used the following methods

    /// Pops a tokens of the stream
    ///
    /// If there is no more tokens in the stream, it will not increment the
    /// `ti` field.
    #[inline]
    #[deprecated(note = "use `self.bump()` and `self.prev_token`")]
    pub fn pop(&mut self) -> Option<Token> {
        self.bump();
        Some(self.prev_token.clone())
    }

    /// Get the `nth` token ahead of the next to be popped
    #[inline]
    #[deprecated(note = "use `self.look_ahead(idx, look_tok)`")]
    pub fn nth_tok(&self, idx: usize) -> Option<&Token> {
        Some(self.look_ahead(idx, look_tok))
    }

    /// Get the `nth` token type ahead of the next to be popped
    #[inline]
    #[deprecated(note = "use `self.look_ahead(idx, look_tt)`")]
    pub fn nth_tt(&self, idx: usize) -> Option<&TokenType> {
        Some(self.look_ahead(idx, look_tt))
    }

    /// Get the token that will be popped if you call `pop` after this call.
    #[inline]
    #[deprecated(note = "use `self.token`")]
    pub fn peek_tok(&self) -> Option<&Token> {
        Some(&self.token)
    }

    /// Get the token type that will be popped if you call `pop` after this call.
    #[inline]
    #[deprecated(note = "use `self.token.tt`")]
    pub fn peek_tt(&self) -> Option<&TokenType> {
        Some(&self.token.tt)
    }

    /// Returns true if the next token the end of a statement or chunk.
    #[deprecated(note = "use `self.token.is_stmt_end()`")]
    pub fn is_stmt_end(&self) -> bool {
        matches!(self.peek_tt(), Some(KwElse | Semi | RCurly))
    }

    #[deprecated]
    pub fn parse_node<T: AstNode>(&mut self) -> Result<T, Diagnostic> {
        T::parse(&mut *self)
    }

    #[deprecated(note = "it's useless.")]
    pub(crate) fn eof_diag(&self) -> Diagnostic {
        let eof = self.tokstream.get_eof();
        ReachedEOF {
            loc: eof.loc.clone(),
        }
        .into_diag()
    }

    // until here.

    /// Parses and produce a module.
    pub fn produce(&mut self) -> Option<Module> {
        let module = match self.parse_module() {
            Ok(ast) => ast,
            Err(diag) => {
                self.sink.emit(diag);
                return None;
            }
        };

        if self.sink.failed() {
            return None;
        }

        Some(module)
    }
}

/// A node of the AST that can be parsed.
#[deprecated]
pub trait AstNode: Debug + PrettyDump {
    /// parse the node with the given parser and returns the node.
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic>
    where
        Self: Sized;
}

/// Look token used in [`Parser::look_ahead`]
pub fn look_tok(tok: &Token) -> &Token {
    tok
}

/// Look token type used in [`Parser::look_ahead`]
pub fn look_tt(tok: &Token) -> &TokenType {
    &tok.tt
}

/// This macro is used to expect a token from the parser, one of the most
/// useful macro in the parser
///
/// # Note
///
/// If you use a value contained in the token, like the content of a string
/// literal, an integer literal, or an identifier, remember to either
/// dereference it, if it implements [`Copy`] or [clone][`Clone`] it if it
/// doesn't.
#[deprecated]
#[macro_export]
macro_rules! expect_token {
    ($parser:expr => [ $($token:pat, $result:expr $(,in $between:stmt)?);* ] else $unexpected:block) => (
        match $parser.peek_tok() {
            $(
                Some(::lunc_token::Token { tt: $token, .. }) => {
                    $(
                        $between
                    )?
                    // we allow unreachable code because the $between type may be `!`
                    #[allow(unreachable_code)]
                    ($result, $parser.pop().unwrap().loc)
                }
            )*
            _ => $unexpected
        }
    );

    ($parser:expr => [ $($token:pat, $result:expr $(, if $cond:expr )? $(,in $between:stmt)?);* $( ; )?], $expected:expr $(, in $node:expr)?) => (
        match $parser.peek_tok() {
            $(
                // we allow unused variable in case of a $between that terminates.
                #[allow(unused_variables)]
                Some(::lunc_token::Token {
                    tt: $token,
                    ..
                }) $( if $cond )? => {
                    $(
                        $between
                    )?
                    // we allow unreachable code because the $between type may
                    // be `!` and we can use unwraps and we already know that
                    // there is a tokens with a location so it is sure we wont
                    // panic
                    #[allow(unreachable_code)]
                    ($result, $parser.pop().unwrap().loc)
                }
            )*
            Some(::lunc_token::Token { tt, loc }) => {
                let node = None::<String>;
                $(
                    node = Some($node);
                )?

                return Err($crate::diags::OldExpectedToken::new($expected, tt.clone(), node, loc.clone()).into_diag());
            }
            _ => return Err($parser.eof_diag())
        }
    );

    (noloc: $( $tt:tt )*) => (
        expect_token!( $( $tt )* ).0
    )
}

#[deprecated]
#[macro_export]
macro_rules! parse {
    (box: $($tt:tt)*) => {
        Box::new(parse!( $( $tt )* ))
    };
    ($parser:expr => $node:ty) => {
        parse!(@fn $parser => <$node as $crate::AstNode>::parse)
    };
    (@fn $parser:expr => $parsing_fn:expr $(, $arg:expr)*) => (
        $parsing_fn($parser $(, $arg)*)?
    );
}
