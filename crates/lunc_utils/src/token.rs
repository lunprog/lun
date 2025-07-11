//! Token, TokenStream, everything related to tokens.

use std::{
    fmt::{self, Debug, Display},
    io::{self, Write},
};

use crate::{FileId, Span};

/// A list of Tokens, and always ending with a `end of file` token
#[derive(Clone, Default)]
pub struct TokenStream {
    toks: Vec<Token>,
    finished: bool,
}

impl TokenStream {
    /// Create a new empty TokenStream.
    pub fn new() -> TokenStream {
        TokenStream {
            toks: Vec::new(),
            finished: false,
        }
    }

    /// Finish a TokenStream, will ensure the last token is an end of file token
    /// so if it's not this function will **panic**.
    #[track_caller]
    pub fn finish(&mut self) {
        assert!(!self.finished, "token stream already finished");
        assert_eq!(
            self.toks.last().map(|t| &t.tt),
            Some(&TokenType::EOF),
            "the last token of a token stream must be the end of file token."
        );

        self.finished = true;
    }

    /// Pushes the TokenType with its start and end offsets and return `true`
    /// if the token is End Of File
    #[track_caller]
    pub fn push(&mut self, tt: TokenType, (lo, hi): (usize, usize), fid: FileId) -> bool {
        assert!(
            !self.finished,
            "can't push a token to the token stream if it's already finished"
        );
        assert_ne!(tt, TokenType::__NotAToken__);

        let is_eof = tt == TokenType::EOF;

        self.toks.push(Token {
            tt,
            loc: Span { lo, hi, fid },
        });

        is_eof
    }

    /// Get the token a the index `idx` returns None if the token isn't found
    ///
    /// # Panic
    ///
    /// This function will panic if you call it on a non-finished token stream
    #[track_caller]
    pub fn get(&self, idx: usize) -> Option<&Token> {
        assert!(
            self.finished,
            "can't access tokens while the token stream isn't finished."
        );
        self.toks.get(idx)
    }

    /// Get the last token of a finished token stream will always be the EOF token
    ///
    /// # Panic
    ///
    /// This function will panic if you call it on a non-finished token stream
    #[track_caller]
    pub fn last(&self) -> Option<&Token> {
        assert!(
            self.finished,
            "can't access tokens while the token stream isn't finished."
        );
        self.toks.last()
    }

    pub fn fmt(&self, out: &mut impl Write, src: &str) -> io::Result<()> {
        writeln!(out, "{{")?;

        for token in &self.toks {
            token.fmt(out, src)?;
        }

        writeln!(out, "}}")?;
        Ok(())
    }
}

impl Debug for TokenStream {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(&self.toks).finish()
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub tt: TokenType,
    pub loc: Span,
}

impl Token {
    pub fn fmt<W: Write>(&self, out: &mut W, src: &str) -> io::Result<()> {
        let print_common = |out: &mut W| -> io::Result<()> {
            writeln!(out, "    loc: {};", self.loc)?;
            writeln!(out, "    lexeme: `{}`;", self.loc.slice_str(src))?;
            Ok(())
        };

        match &self.tt {
            TokenType::Kw(kw) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: keyword '{kw}';")?;
                print_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::Ident(id) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: ident '{id}';")?;
                print_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::IntLit(i) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: integer '{i}';")?;
                print_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::StringLit(s) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: string {:?};", s)?;
                print_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::CharLit(c) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: character {c:?};")?;
                print_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::FloatLit(f) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: float {f:?};")?;
                print_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::Punct(p) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: punctuation {p:?};")?;
                print_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::EOF => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: end of file;")?;
                writeln!(out, "    loc: {};", self.loc)?;
                writeln!(out, "    lexeme: N/A;")?;
                writeln!(out, "  }},")?;
            }
            TokenType::__NotAToken__ => unreachable!(),
        }

        Ok(())
    }
}

// NOTE: when adding a new token, a correspond test should be added into
// `tests/lexer/` that should test everything about this new token
#[derive(Debug, Clone, PartialEq)]
pub enum TokenType {
    /// keyword
    Kw(Keyword),
    /// identifier
    Ident(String),
    /// integer literal
    IntLit(u128),
    /// string literal
    StringLit(String),
    /// char literal
    CharLit(char),
    /// float literal
    FloatLit(f64),
    /// punctuation and operators
    Punct(Punctuation),
    /// End Of File
    EOF,
    /// this is not a token, it is used when encountering a comment or a
    /// whitespace it can't be pushed into a token stream.
    #[doc(hidden)]
    __NotAToken__,
}

impl Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TokenType::*;
        match self {
            Kw(kw) => write!(f, "keyword `{}`", kw),
            Ident(_) => write!(f, "identifier"),
            IntLit(_) => write!(f, "integer literal"),
            StringLit(_) => write!(f, "string literal"),
            CharLit(_) => write!(f, "character literal"),
            FloatLit(_) => write!(f, "float literal"),
            Punct(p) => write!(f, "`{p}`"),
            EOF => write!(f, "\"<eof>\""),
            __NotAToken__ => write!(f, "not a token"),
        }
    }
}

// WARN: /!\ If a keyword is added change the `lex_identifer` method of the Lexer
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Keyword {
    /// and
    And,
    /// break
    Break,
    /// comptime
    Comptime,
    /// continue
    Continue,
    /// else
    Else,
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
    /// let
    Let,
    /// mut
    Mut,
    /// null
    Null,
    /// Or
    Or,
    /// pub
    Pub,
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
    /// `and` keyword.
    pub const AND: &str = "and";

    /// `break` keyword.
    pub const BREAK: &str = "break";

    /// `comptime` keyword.
    pub const COMPTIME: &str = "comptime";

    /// `continue` keyword.
    pub const CONTINUE: &str = "continue";

    /// `else` keyword.
    pub const ELSE: &str = "else";

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

    /// `let` keyword.
    pub const LET: &str = "let";

    /// `mut` keyword
    pub const MUT: &str = "mut";

    /// `null` keyword.
    pub const NULL: &str = "null";

    /// `or` keyword.
    pub const OR: &str = "or";

    /// `pub` keyword.
    pub const PUB: &str = "pub";

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
            Keyword::And => f.write_str(Keyword::AND),
            Keyword::Break => f.write_str(Keyword::BREAK),
            Keyword::Comptime => f.write_str(Keyword::COMPTIME),
            Keyword::Continue => f.write_str(Keyword::CONTINUE),
            Keyword::Else => f.write_str(Keyword::ELSE),
            Keyword::False => f.write_str(Keyword::FALSE),
            Keyword::For => f.write_str(Keyword::FOR),
            Keyword::Fun => f.write_str(Keyword::FUN),
            Keyword::If => f.write_str(Keyword::IF),
            Keyword::Impl => f.write_str(Keyword::IMPL),
            Keyword::In => f.write_str(Keyword::IN),
            Keyword::Let => f.write_str(Keyword::LET),
            Keyword::Mut => f.write_str(Keyword::MUT),
            Keyword::Null => f.write_str(Keyword::NULL),
            Keyword::Or => f.write_str(Keyword::OR),
            Keyword::Pub => f.write_str(Keyword::PUB),
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
    /// !
    Bang,
    /// <=
    LtEqual,
    /// <
    Lt,
    /// <<
    Lt2,
    /// >
    Gt,
    /// >>
    Gt2,
    /// >=
    GtEqual,
    /// ;
    Semicolon,
    /// ->
    MinusGt,
    /// ^
    Carret,
    /// &
    Ampsand,
    /// |
    Pipe,
    /// %
    Percent,
    /// .
    Dot,
    /// .*
    DotStar,
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
            Bang => f.write_str("!"),
            LtEqual => f.write_str("<="),
            Lt => f.write_str("<"),
            Lt2 => f.write_str("<<"),
            Gt => f.write_str(">"),
            Gt2 => f.write_str(">>"),
            GtEqual => f.write_str(">="),
            Semicolon => f.write_str(";"),
            MinusGt => f.write_str("->"),
            Carret => f.write_str("^"),
            Ampsand => f.write_str("&"),
            Pipe => f.write_str("|"),
            Percent => f.write_str("%"),
            Dot => f.write_str("."),
            DotStar => f.write_str(".*"),
        }
    }
}
