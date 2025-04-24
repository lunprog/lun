//! Token, TokenTree, everything related to tokens.

use std::fmt::{Debug, Display};

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
        let is_eof = tt == TokenType::EOF;

        self.toks.push(Token {
            tt,
            loc: Span { start, end },
        });

        is_eof
    }

    pub fn get(&self, idx: usize) -> Option<&Token> {
        self.toks.get(idx)
    }
}

impl Debug for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(&self.toks).finish()
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tt: TokenType,
    pub loc: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenType {
    /// keyword
    KW(Keyword),
    /// identifier
    Ident(String),
    /// integer literal
    IntLit(u64),
    /// string literal
    StringLit(String),
    /// punctuation and operators
    Punct(Punctuation),
    /// End Of File
    EOF,
}

impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

// /!\ If an identifier is added change the `lex_identifer` method of the Lexer
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Keyword {
    /// break
    Break,
    /// class
    Class,
    /// continue
    Continue,
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
    /// not
    Not,
    /// return
    Return,
    /// self
    ///
    /// Note: here the name of this keyword is `Zelf` because we can't name it
    /// Self because it's a keyword and neither `r#Self`.
    Zelf,
    /// then
    Then,
    /// trait
    Trait,
    /// true
    True,
    /// while
    While,
}

impl Keyword {
    /// `break` keyword.
    pub const BREAK: &str = "break";

    /// `class` keyword.
    pub const CLASS: &str = "class";

    /// `continue` keyword.
    pub const CONTINUE: &str = "continue";

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

    /// `not` keyword.
    pub const NOT: &str = "not";

    /// `return` keyword.
    pub const RETURN: &str = "return";

    /// `self` keyword.
    pub const SELF: &str = "self";

    /// `then` keyword.
    pub const THEN: &str = "then";

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
    /// =
    Equal,
    /// ==
    Equal2,
    /// !=
    BangEqual,
    /// <=
    LArrow,
    /// <
    LArrowEqual,
    /// >
    RArrow,
    /// >=
    RArrowEqual,
}

impl Display for Punctuation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
