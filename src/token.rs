//! Token, TokenTree, everything related to tokens.

use std::fmt::Debug;

use crate::Span;

#[derive(Clone)]
pub struct TokenTree {
    toks: Vec<Token>,
}

impl TokenTree {
    pub fn new() -> TokenTree {
        TokenTree { toks: Vec::new() }
    }

    /// Pushes the TokenType with its start and end offsets and return `true`
    /// if the token is End Of File
    pub fn push(&mut self, tt: TokenType, start: usize, end: usize) -> bool {
        dbg!(&tt);
        let is_eof = tt == TokenType::EOF;

        self.toks.push(Token {
            tt,
            loc: Span { start, end },
        });

        is_eof
    }
}

impl Debug for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(&self.toks).finish()
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    tt: TokenType,
    loc: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenType {
    /// keyword
    KW(Keyword),
    /// identifier
    Ident(String),
    /// integer literal
    Int(u64),
    /// string literal
    String(String),
    /// punctuation and operators
    Punct(Punctuation),
    /// End Of File
    EOF,
}

// /!\ If an identifier is added change the `lex_identifer` method of the Lexer
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Keyword {
    /// class
    Class,
    /// do
    Do,
    /// end
    End,
    /// false
    False,
    /// for
    For,
    /// fun
    Fun,
    /// impl
    Impl,
    /// local
    Local,
    /// return
    Return,
    /// self
    Zelf,
    /// trait
    Trait,
    /// true
    True,
    /// while
    While,
}

impl Keyword {
    /// `class` keyword.
    pub const CLASS: &str = "class";
    /// `do` keyword.
    pub const DO: &str = "do";
    /// `end` keyword.
    pub const END: &str = "end";
    /// `false` keyword.
    pub const FALSE: &str = "false";
    /// `for` keyword.
    pub const FOR: &str = "for";
    /// `fun` keyword.
    pub const FUN: &str = "fun";
    /// `impl` keyword.
    pub const IMPL: &str = "impl";
    /// `local` keyword.
    pub const LOCAL: &str = "local";
    /// `return` keyword.
    pub const RETURN: &str = "return";
    /// `self` keyword.
    pub const SELF: &str = "self";
    /// `trait` keyword.
    pub const TRAIT: &str = "trait";
    /// `true` keyword.
    pub const TRUE: &str = "true";
    /// `while` keyword.
    pub const WHILE: &str = "while";
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Punctuation {
    /// (
    LParen,
    /// )
    RParen,
    /// [
    LBracket,
    /// ]
    RBracket,
    /// {
    LBrace,
    /// }
    RBrace,
    /// +
    Plus,
    /// -
    Minus,
    /// *
    Star,
    /// /
    Slash,
    /// :
    Colon,
    /// ,
    Comma,
}
