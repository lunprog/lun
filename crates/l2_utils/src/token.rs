//! Token, TokenTree, everything related to tokens.

use std::fmt::{self, Debug, Display};

use crate::Span;

// TODO(UREGENT+): ensure we have an eof token at the end and that we can't
// modify the tokens after finished it, add a `finished` field and while it's
// false we can mutate the TokenTree but can't get the tokens and as soon
// as `finished` is true, we can get tokens but can't push new ones. In the
// `finish()` method assert the presence of a EOF token.

/// A list of Tokens, and always ending with a `end of file` token (not ensured
/// tho, maybe in the future)
#[derive(Clone, Default)]
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

    pub fn last(&self) -> Option<&Token> {
        self.toks.last()
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
    Kw(Keyword),
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TokenType::*;
        match self {
            Kw(kw) => write!(f, "keyword `{}`", kw),
            Ident(_) => write!(f, "identifier"),
            IntLit(_) => write!(f, "integer literal"),
            StringLit(_) => write!(f, "string literal"),
            Punct(p) => Display::fmt(p, f),
            EOF => write!(f, "end of file"),
        }
    }
}

// TODO: add keyword `nil` and implement the nil expression
//
// /!\ If a keyword is added change the `lex_identifer` method of the Lexer
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
    /// else
    Else,
    /// end
    End,
    /// false
    False,
    /// for
    For,
    /// fun
    Fun,
    /// if
    If,
    /// impl
    Impl,
    /// in
    In,
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

    /// `else` keyword.
    pub const ELSE: &str = "else";

    /// `end` keyword.
    pub const END: &str = "end";

    /// `false` keyword.
    pub const FALSE: &str = "false";

    /// `for` keyword.
    pub const FOR: &str = "for";

    /// `fun` keyword.
    pub const FUN: &str = "fun";

    /// `if` keyword.
    pub const IF: &str = "if";

    /// `impl` keyword.
    pub const IMPL: &str = "impl";

    /// `in` keyword.
    pub const IN: &str = "in";

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

impl Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Keyword::Break => f.write_str(Keyword::BREAK),
            Keyword::Class => f.write_str(Keyword::CLASS),
            Keyword::Continue => f.write_str(Keyword::CONTINUE),
            Keyword::Do => f.write_str(Keyword::DO),
            Keyword::Else => f.write_str(Keyword::ELSE),
            Keyword::End => f.write_str(Keyword::END),
            Keyword::False => f.write_str(Keyword::FALSE),
            Keyword::For => f.write_str(Keyword::FOR),
            Keyword::Fun => f.write_str(Keyword::FUN),
            Keyword::If => f.write_str(Keyword::IF),
            Keyword::Impl => f.write_str(Keyword::IMPL),
            Keyword::In => f.write_str(Keyword::IN),
            Keyword::Local => f.write_str(Keyword::LOCAL),
            Keyword::Not => f.write_str(Keyword::NOT),
            Keyword::Return => f.write_str(Keyword::RETURN),
            Keyword::Zelf => f.write_str(Keyword::SELF),
            Keyword::Then => f.write_str(Keyword::THEN),
            Keyword::Trait => f.write_str(Keyword::TRAIT),
            Keyword::True => f.write_str(Keyword::TRUE),
            Keyword::While => f.write_str(Keyword::WHILE),
        }
    }
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
    /// ;
    SemiColon,
}

impl Display for Punctuation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Punctuation::*;
        match self {
            LParen => f.write_str("("),
            RParen => f.write_str(")"),
            LBracket => f.write_str("["),
            RBracket => f.write_str("]"),
            LBrace => f.write_str("{"),
            RBrace => f.write_str("}"),
            Plus => f.write_str("+"),
            Minus => f.write_str("-"),
            Star => f.write_str("*"),
            Slash => f.write_str("/"),
            Colon => f.write_str(":"),
            Comma => f.write_str(","),
            Equal => f.write_str("="),
            Equal2 => f.write_str("=="),
            BangEqual => f.write_str("!="),
            LArrow => f.write_str("<="),
            LArrowEqual => f.write_str("<"),
            RArrow => f.write_str(">"),
            RArrowEqual => f.write_str(">="),
            SemiColon => f.write_str(";"),
        }
    }
}
