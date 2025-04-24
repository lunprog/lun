//! Parser of the l2 language.

use std::fmt::Debug;

use expr::Expression;
use stmt::Chunk;
use thiserror::Error;

use l2_utils::{
    Span,
    token::{
        Keyword, Punctuation, Token, TokenTree,
        TokenType::{self, *},
    },
};

pub mod expr;
pub mod stmt;

#[derive(Debug, Clone, Error)]
pub enum ParsingError {
    #[error("{loc:?}: expected {expected:?}, but found {found:?}")]
    Expected {
        expected: String,
        found: String,
        loc: Span,
    },
    #[error("reached eof.")]
    ReachedEOF,
}

impl ParsingError {
    pub fn new_expected(expected: impl ToString, found: impl ToString, loc: Span) -> ParsingError {
        ParsingError::Expected {
            expected: expected.to_string(),
            found: found.to_string(),
            loc,
        }
    }
}

/// Parsing result
type PResult<T, E = ParsingError> = Result<T, E>;

#[derive(Debug, Clone)]
pub struct Parser {
    /// token tree
    tt: TokenTree,
    /// token index
    ti: usize,
}

impl Parser {
    /// Create a new parser with the given token tree.
    pub fn new(tt: TokenTree) -> Parser {
        Parser { tt, ti: 0 }
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

    pub fn parse(&mut self) -> PResult<Chunk> {
        <Chunk as AstNode>::parse(self)
    }

    pub fn parse_node<T: AstNode>(&mut self) -> PResult<T> {
        T::parse(&mut *self)
    }
}

/// A node of the AST that can be parsed.
pub trait AstNode: Debug {
    /// parse the node with the given parser and returns the node.
    fn parse(parser: &mut Parser) -> PResult<Self>
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
                Some(::l2_utils::token::Token { tt: $token, .. }) => {
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

    ($parser:expr => [ $($token:pat, $result:expr $(,in $between:stmt)?);* $( ; )?], $expected:expr) => (
        match $parser.peek_tok() {
            $(
                // we allow unused variable in case of a $between that terminates.
                #[allow(unused_variables)]
                Some(::l2_utils::token::Token {
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
            Some(::l2_utils::token::Token { tt, loc }) => {
                return Err(ParsingError::new_expected($expected, tt, loc.clone()));
            }
            _ => return Err(ParsingError::ReachedEOF)
        }
    );

    (@noloc $parser:expr => [ $($token:pat, $result:expr $(,in $between:stmt)?);* $( ; )?], $expected:expr) => (
        match $parser.peek_tok() {
            $(
                // we allow unused variable in case of a $between that terminates.
                #[allow(unused_variables)]
                Some(::l2_utils::token::Token {
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
            Some(::l2_utils::token::Token { tt, loc: loc }) => {
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
