//! Parser of the lun language.

use std::fmt::Debug;

use diags::*;
use expr::Expression;
use lun_diag::{Diagnostic, DiagnosticSink, StageResult, ToDiagnostic};
use stmt::Chunk;

use lun_utils::{
    Span,
    token::{
        Keyword, Punctuation, Token, TokenTree,
        TokenType::{self, *},
    },
};

pub mod diags;
pub mod expr;
pub mod stmt;

#[derive(Debug, Clone)]
pub struct Parser {
    /// token tree
    tt: TokenTree,
    /// token index
    ti: usize,
    /// sink of diags
    sink: DiagnosticSink,
}

impl Parser {
    /// Create a new parser with the given token tree.
    pub fn new(tt: TokenTree, sink: DiagnosticSink) -> Parser {
        Parser { tt, ti: 0, sink }
    }

    /// Pops a tokens of the stream
    ///
    /// If there is no more tokens in the stream, it will not increment the
    /// `ti` field.
    #[inline]
    pub fn pop(&mut self) -> Option<Token> {
        let tok = self.peek_tok()?.clone();
        self.ti += 1;
        Some(tok)
    }

    /// Get the `nth` token ahead of the next to be popped
    #[inline]
    pub fn nth_tok(&self, idx: usize) -> Option<&Token> {
        self.tt.get(self.ti + idx)
    }

    /// Get the `nth` token type ahead of the next to be popped
    #[inline]
    pub fn nth_tt(&self, idx: usize) -> Option<&TokenType> {
        self.nth_tok(idx).map(|t| &t.tt)
    }

    /// Get the token that will be popped if you call `pop` after this call.
    #[inline]
    pub fn peek_tok(&self) -> Option<&Token> {
        self.nth_tok(0)
    }

    /// Get the token type that will be popped if you call `pop` after this call.
    #[inline]
    pub fn peek_tt(&self) -> Option<&TokenType> {
        self.peek_tok().map(|t| &t.tt)
    }

    /// Returns true if the next token the end of a statement or chunk.
    pub fn is_stmt_end(&self) -> bool {
        matches!(
            self.peek_tt(),
            Some(Kw(Keyword::End | Keyword::Else) | Punct(Punctuation::SemiColon))
        )
    }

    pub fn produce(&mut self) -> StageResult<Chunk> {
        let ast = match Chunk::parse(self) {
            Ok(ast) => ast,
            Err(diag) => {
                self.sink.push(diag);
                return StageResult::Fail(self.sink.clone());
            }
        };

        if self.sink.failed() {
            return StageResult::Fail(self.sink.clone());
        }

        StageResult::Good(ast)
    }

    pub fn parse_node<T: AstNode>(&mut self) -> Result<T, Diagnostic> {
        T::parse(&mut *self)
    }

    pub(crate) fn eof_diag(&self) -> Diagnostic {
        // it's ok to unwrap there is at least the EOF token
        let eof = self.tt.last().unwrap();
        ReachedEOF {
            loc: eof.loc.clone(),
        }
        .into_diag()
    }
}

/// A node of the AST that can be parsed.
pub trait AstNode: Debug {
    /// parse the node with the given parser and returns the node.
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic>
    where
        Self: Sized;
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
#[macro_export]
macro_rules! expect_token {
    ($parser:expr => [ $($token:pat, $result:expr $(,in $between:stmt)?);* ] else $unexpected:block) => (
        match $parser.peek_tok() {
            $(
                Some(::lun_utils::token::Token { tt: $token, .. }) => {
                    $(
                        $between
                    )?
                    // we allow unreacheable code because the $between type may be `!`
                    #[allow(unreachable_code)]
                    ($result, $parser.pop().unwrap().loc)
                }
            )*
            _ => $unexpected
        }
    );

    ($parser:expr => [ $($token:pat, $result:expr $(,in $between:stmt)?);* $( ; )?], $expected:expr $(, in $node:expr)?) => (
        match $parser.peek_tok() {
            $(
                // we allow unused variable in case of a $between that terminates.
                #[allow(unused_variables)]
                Some(::lun_utils::token::Token {
                    tt: $token,
                    ..
                }) => {
                    $(
                        $between
                    )?
                    // we allow unreacheable code because the $between type may
                    // be `!` and we can use unwraps and we already know that
                    // there is a tokens with a location so it is sure we wont
                    // panic
                    #[allow(unreachable_code)]
                    ($result, $parser.pop().unwrap().loc)
                }
            )*
            Some(::lun_utils::token::Token { tt, loc }) => {
                let node = None::<String>;
                $(
                    node = Some($node);
                )?

                return Err($crate::diags::ExpectedToken::new($expected, tt.clone(), node, loc.clone()).into_diag());
            }
            _ => return Err($parser.eof_diag())
        }
    );

    (@noloc $parser:expr => [ $($token:pat, $result:expr $(,in $between:stmt)?);* $( ; )?], $expected:expr) => (
        match $parser.peek_tok() {
            $(
                // we allow unused variable in case of a $between that terminates.
                #[allow(unused_variables)]
                Some(::lun_utils::token::Token {
                    tt: $token,
                    ..
                }) => {
                    $(
                        $between
                    )?
                    // we allow unreacheable code because the $between type may
                    // be of type `!` and we can use unwraps and we already
                    // know that there is a tokens with a location so it is
                    // sure we wont panic
                    #[allow(unreachable_code)]
                    {
                        $parser.pop();
                        $result
                    }
                }
            )*
            Some(::lun_utils::token::Token { tt, loc: loc }) => {
                return Err(ParsingError::new_expected($expected, tt, loc.clone()));
            }
            _ => return Err(ParsingError::ReachedEOF)
        }
    )
}

#[macro_export]
macro_rules! parse {
    ($parser:expr => $node:ty) => {
        parse!(@fn $parser => <$node as $crate::AstNode>::parse)
    };
    (@fn $parser:expr => $parsing_fn:expr $(, $arg:expr)*) => (
        $parsing_fn($parser $(, $arg)*)?
    )
}
