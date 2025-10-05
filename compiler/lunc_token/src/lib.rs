//! Token related to tokens shared between lunc_lexer and lunc_parser.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{
    fmt::{self, Debug, Display},
    io::{self, Write},
};

use lunc_utils::{FileId, Span};

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
        assert_ne!(tt, TokenType::Dummy);

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
        let p_common = |out: &mut W| -> io::Result<()> {
            writeln!(out, "    loc: {};", self.loc)?;
            writeln!(out, "    lexeme: `{}`;", self.loc.slice_str(src))?;
            Ok(())
        };

        let p_kw = |out: &mut W, kw: &'static str| -> io::Result<()> {
            writeln!(out, "  {{")?;
            writeln!(out, "    tt: keyword '{}';", kw)?;
            p_common(out)?;
            writeln!(out, "  }},")?;
            Ok(())
        };

        let p_punct = |out: &mut W, p: &TokenType| -> io::Result<()> {
            writeln!(out, "  {{")?;
            writeln!(out, "    tt: punct {p:?};")?;
            p_common(out)?;
            writeln!(out, "  }},")?;
            Ok(())
        };

        let tt = &self.tt;
        match tt {
            TokenType::LParen
            | TokenType::RParen
            | TokenType::LBracket
            | TokenType::RBracket
            | TokenType::LCurly
            | TokenType::RCurly
            | TokenType::Plus
            | TokenType::Minus
            | TokenType::Star
            | TokenType::Slash
            | TokenType::Colon
            | TokenType::Comma
            | TokenType::Eq
            | TokenType::EqEq
            | TokenType::BangEq
            | TokenType::Bang
            | TokenType::LtEq
            | TokenType::Lt
            | TokenType::LtLt
            | TokenType::Gt
            | TokenType::GtGt
            | TokenType::GtEq
            | TokenType::Semi
            | TokenType::MinusGt
            | TokenType::Caret
            | TokenType::And
            | TokenType::AndAnd
            | TokenType::Or
            | TokenType::OrOr
            | TokenType::Percent
            | TokenType::Dot
            | TokenType::DotStar
            | TokenType::Pound => {
                p_punct(out, tt)?;
            }
            TokenType::KwAs => {
                p_kw(out, TokenType::KW_AS)?;
            }
            TokenType::KwBreak => {
                p_kw(out, TokenType::KW_BREAK)?;
            }
            TokenType::KwComptime => {
                p_kw(out, TokenType::KW_COMPTIME)?;
            }
            TokenType::KwContinue => {
                p_kw(out, TokenType::KW_CONTINUE)?;
            }
            TokenType::KwDefer => {
                p_kw(out, TokenType::KW_DEFER)?;
            }
            TokenType::KwElse => {
                p_kw(out, TokenType::KW_ELSE)?;
            }
            TokenType::KwExtern => {
                p_kw(out, TokenType::KW_EXTERN)?;
            }
            TokenType::KwFalse => {
                p_kw(out, TokenType::KW_FALSE)?;
            }
            TokenType::KwFor => {
                p_kw(out, TokenType::KW_FOR)?;
            }
            TokenType::KwFun => {
                p_kw(out, TokenType::KW_FUN)?;
            }
            TokenType::KwIf => {
                p_kw(out, TokenType::KW_IF)?;
            }
            TokenType::KwImpl => {
                p_kw(out, TokenType::KW_IMPL)?;
            }
            TokenType::KwIn => {
                p_kw(out, TokenType::KW_IN)?;
            }
            TokenType::KwLet => {
                p_kw(out, TokenType::KW_LET)?;
            }
            TokenType::KwLoop => {
                p_kw(out, TokenType::KW_LOOP)?;
            }
            TokenType::KwMut => {
                p_kw(out, TokenType::KW_MUT)?;
            }
            TokenType::KwNull => {
                p_kw(out, TokenType::KW_NULL)?;
            }
            TokenType::KwOrb => {
                p_kw(out, TokenType::KW_ORB)?;
            }
            TokenType::KwPub => {
                p_kw(out, TokenType::KW_PUB)?;
            }
            TokenType::KwReturn => {
                p_kw(out, TokenType::KW_RETURN)?;
            }
            TokenType::KwSelfVal => {
                p_kw(out, TokenType::KW_SELF)?;
            }
            TokenType::KwThen => {
                p_kw(out, TokenType::KW_THEN)?;
            }
            TokenType::KwTrait => {
                p_kw(out, TokenType::KW_TRAIT)?;
            }
            TokenType::KwTrue => {
                p_kw(out, TokenType::KW_TRUE)?;
            }
            TokenType::KwWhile => {
                p_kw(out, TokenType::KW_WHILE)?;
            }
            TokenType::Ident(id) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: ident '{id}';")?;
                p_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::Lit(Literal { kind, value, tag }) => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: {kind} {value};")?;

                if let Some(tag) = tag {
                    writeln!(out, "    tag: {tag:?};")?;
                }

                p_common(out)?;
                writeln!(out, "  }},")?;
            }
            TokenType::EOF => {
                writeln!(out, "  {{")?;
                writeln!(out, "    tt: end of file;")?;
                writeln!(out, "    loc: {};", self.loc)?;
                writeln!(out, "    lexeme: N/A;")?;
                writeln!(out, "  }},")?;
            }
            TokenType::Dummy => unreachable!(),
        }

        Ok(())
    }
}

// NOTE: when adding a new token, a correspond test should be added into
// `tests/lexer/` that should test everything about this new token
// WARN: /!\ If a keyword is added change the `lex_identifier` method of the
// Lexer and add it to the list of all keywords.
#[derive(Debug, Clone, PartialEq)]
pub enum TokenType {
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `{`
    LCurly,
    /// `}`
    RCurly,
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Star,
    /// `/`
    Slash,
    /// `:`
    Colon,
    /// `,`
    Comma,
    /// `=`
    Eq,
    /// `==`
    EqEq,
    /// `!=`
    BangEq,
    /// `!`
    Bang,
    /// `<=`
    LtEq,
    /// `<`
    Lt,
    /// `<<`
    LtLt,
    /// `>`
    Gt,
    /// `>>`
    GtGt,
    /// `>=`
    GtEq,
    /// `;`
    Semi,
    /// `->`
    MinusGt,
    /// `^`
    Caret,
    /// `&`
    And,
    /// `&&`
    AndAnd,
    /// `|`
    Or,
    /// `||`
    OrOr,
    /// `%`
    Percent,
    /// `.`
    Dot,
    /// `.*`
    DotStar,
    /// `#`
    Pound,
    /// keyword `as`
    KwAs,
    /// keyword `break`
    KwBreak,
    /// keyword `comptime`
    KwComptime,
    /// keyword `continue`
    KwContinue,
    /// keyword `defer`
    KwDefer,
    /// keyword `else`
    KwElse,
    /// keyword `extern`
    KwExtern,
    /// keyword `false`
    KwFalse,
    /// keyword `for`
    KwFor,
    /// keyword `fun`
    KwFun,
    /// keyword `if`
    KwIf,
    /// keyword `impl`
    KwImpl,
    /// keyword `in`
    KwIn,
    /// keyword `let`
    KwLet,
    /// keyword `loop`
    KwLoop,
    /// keyword `mut`
    KwMut,
    /// keyword `null`
    KwNull,
    /// keyword `orb`
    KwOrb,
    /// keyword `pub`
    KwPub,
    /// keyword `return`
    KwReturn,
    /// keyword `self`
    KwSelfVal,
    /// keyword `then`
    KwThen,
    /// keyword `trait`
    KwTrait,
    /// keyword `true`
    KwTrue,
    /// keyword `while`
    KwWhile,
    /// identifier
    Ident(String),
    /// literal
    Lit(Literal),
    /// End Of File
    EOF,
    /// this is a dummy token, it is used when encountering a comment or a
    /// whitespace it can't be pushed into a token stream.
    Dummy,
}

impl TokenType {
    /// `as` keyword.
    pub const KW_AS: &str = "as";

    /// `break` keyword.
    pub const KW_BREAK: &str = "break";

    /// `comptime` keyword.
    pub const KW_COMPTIME: &str = "comptime";

    /// `continue` keyword.
    pub const KW_CONTINUE: &str = "continue";

    /// `defer` keyword.
    pub const KW_DEFER: &str = "defer";

    /// `else` keyword.
    pub const KW_ELSE: &str = "else";

    /// `extern` keyword.
    pub const KW_EXTERN: &str = "extern";

    /// `false` keyword.
    pub const KW_FALSE: &str = "false";

    /// `for` keyword.
    pub const KW_FOR: &str = "for";

    /// `fun` keyword.
    pub const KW_FUN: &str = "fun";

    /// `if` keyword.
    pub const KW_IF: &str = "if";

    /// `impl` keyword.
    pub const KW_IMPL: &str = "impl";

    /// `in` keyword.
    pub const KW_IN: &str = "in";

    /// `let` keyword.
    pub const KW_LET: &str = "let";

    /// `loop` keyword.
    pub const KW_LOOP: &str = "loop";

    /// `mut` keyword
    pub const KW_MUT: &str = "mut";

    /// `null` keyword.
    pub const KW_NULL: &str = "null";

    /// `orb` keyword.
    pub const KW_ORB: &str = "orb";

    /// `pub` keyword.
    pub const KW_PUB: &str = "pub";

    /// `return` keyword.
    pub const KW_RETURN: &str = "return";

    /// `self` keyword.
    pub const KW_SELF: &str = "self";

    /// `then` keyword.
    pub const KW_THEN: &str = "then";

    /// `trait` keyword.
    pub const KW_TRAIT: &str = "trait";

    /// `true` keyword.
    pub const KW_TRUE: &str = "true";

    /// `while` keyword.
    pub const KW_WHILE: &str = "while";

    /// List of all of the keywords
    pub const ALL_KEYWORDS: [&str; 25] = [
        TokenType::KW_AS,
        TokenType::KW_BREAK,
        TokenType::KW_COMPTIME,
        TokenType::KW_CONTINUE,
        TokenType::KW_DEFER,
        TokenType::KW_ELSE,
        TokenType::KW_EXTERN,
        TokenType::KW_FALSE,
        TokenType::KW_FOR,
        TokenType::KW_FUN,
        TokenType::KW_IF,
        TokenType::KW_IMPL,
        TokenType::KW_IN,
        TokenType::KW_LET,
        TokenType::KW_LOOP,
        TokenType::KW_MUT,
        TokenType::KW_NULL,
        TokenType::KW_ORB,
        TokenType::KW_PUB,
        TokenType::KW_RETURN,
        TokenType::KW_SELF,
        TokenType::KW_THEN,
        TokenType::KW_TRAIT,
        TokenType::KW_TRUE,
        TokenType::KW_WHILE,
    ];
}

impl Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TokenType as Tt;

        match self {
            Tt::LParen => write!(f, "`(`"),
            Tt::RParen => write!(f, "`)`"),
            Tt::LBracket => write!(f, "`[`"),
            Tt::RBracket => write!(f, "`]`"),
            Tt::LCurly => write!(f, "`{{`"),
            Tt::RCurly => write!(f, "`}}`"),
            Tt::Plus => write!(f, "`+`"),
            Tt::Minus => write!(f, "`-`"),
            Tt::Star => write!(f, "`*`"),
            Tt::Slash => write!(f, "`/`"),
            Tt::Colon => write!(f, "`:`"),
            Tt::Comma => write!(f, "`,`"),
            Tt::Eq => write!(f, "`=`"),
            Tt::EqEq => write!(f, "`==`"),
            Tt::BangEq => write!(f, "`!=`"),
            Tt::Bang => write!(f, "`!`"),
            Tt::LtEq => write!(f, "`<=`"),
            Tt::Lt => write!(f, "`<`"),
            Tt::LtLt => write!(f, "`<<`"),
            Tt::Gt => write!(f, "`>`"),
            Tt::GtGt => write!(f, "`>>`"),
            Tt::GtEq => write!(f, "`>=`"),
            Tt::Semi => write!(f, "`;`"),
            Tt::MinusGt => write!(f, "`->`"),
            Tt::Caret => write!(f, "`^`"),
            Tt::And => write!(f, "`&`"),
            Tt::AndAnd => write!(f, "`&&`"),
            Tt::Or => write!(f, "`|`"),
            Tt::OrOr => write!(f, "`||`"),
            Tt::Percent => write!(f, "`%`"),
            Tt::Dot => write!(f, "`.`"),
            Tt::DotStar => write!(f, "`.*`"),
            Tt::Pound => write!(f, "`#`"),
            Tt::KwAs => write!(f, "keyword `as`"),
            Tt::KwBreak => write!(f, "keyword `break`"),
            Tt::KwComptime => write!(f, "keyword `comptime`"),
            Tt::KwContinue => write!(f, "keyword `continue`"),
            Tt::KwDefer => write!(f, "keyword `defer`"),
            Tt::KwElse => write!(f, "keyword `else`"),
            Tt::KwExtern => write!(f, "keyword `extern`"),
            Tt::KwFalse => write!(f, "keyword `false`"),
            Tt::KwFor => write!(f, "keyword `for`"),
            Tt::KwFun => write!(f, "keyword `fun`"),
            Tt::KwIf => write!(f, "keyword `if`"),
            Tt::KwImpl => write!(f, "keyword `impl`"),
            Tt::KwIn => write!(f, "keyword `in`"),
            Tt::KwLet => write!(f, "keyword `let`"),
            Tt::KwLoop => write!(f, "keyword `loop`"),
            Tt::KwMut => write!(f, "keyword `mut`"),
            Tt::KwNull => write!(f, "keyword `null`"),
            Tt::KwOrb => write!(f, "keyword `orb`"),
            Tt::KwPub => write!(f, "keyword `pub`"),
            Tt::KwReturn => write!(f, "keyword `return`"),
            Tt::KwSelfVal => write!(f, "keyword `self`"),
            Tt::KwThen => write!(f, "keyword `then`"),
            Tt::KwTrait => write!(f, "keyword `trait`"),
            Tt::KwTrue => write!(f, "keyword `true`"),
            Tt::KwWhile => write!(f, "keyword `while`"),
            Tt::Ident(_) => write!(f, "identifier"),
            Tt::Lit(Literal { kind, .. }) => write!(f, "{kind} literal"),
            Tt::EOF => write!(f, "<eof>"),
            Tt::Dummy => write!(f, "not a token"),
        }
    }
}

/// Is this string identifier compatible?
pub fn is_identifier(id: &str) -> bool {
    // identifiers only support ascii for now
    if !id.is_ascii() {
        return false;
    }

    // identifiers cannot have a whitespace
    if id.contains(char::is_whitespace) {
        return false;
    }

    // identifiers always start with a letter
    if !id.chars().next().unwrap().is_alphabetic() {
        return false;
    }

    // identifier cannot be a keyword
    if TokenType::ALL_KEYWORDS.contains(&id) {
        return false;
    }

    true
}

/// A literal token
///
/// # Note
///
/// The `kind` and `value` must match, a literal with kind [`LitKind::Float`] and
/// value [`LitVal::Int(12)`] is invalid, and **can lead to UB**.
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Literal {
    pub kind: LitKind,
    pub value: LitVal,
    pub tag: Option<String>,
}

impl Literal {
    /// Create a new character literal
    pub const fn char(val: char) -> Literal {
        Literal {
            kind: LitKind::Char,
            value: LitVal::Char(val),
            tag: None,
        }
    }

    /// Create a new integer literal
    pub const fn int(val: u128) -> Literal {
        Literal {
            kind: LitKind::Integer,
            value: LitVal::Int(val),
            tag: None,
        }
    }

    /// Create a new float literal
    pub const fn float(val: f64) -> Literal {
        Literal {
            kind: LitKind::Float,
            value: LitVal::Float(val),
            tag: None,
        }
    }

    /// Create a new string literal
    pub fn string(val: String) -> Literal {
        Literal {
            kind: LitKind::Str,
            value: LitVal::Str(val),
            tag: None,
        }
    }

    /// Create a new c string literal
    pub fn c_string(val: String) -> Literal {
        Literal {
            kind: LitKind::CStr,
            value: LitVal::Str(val),
            tag: None,
        }
    }
}

/// A kind of literal token
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum LitKind {
    Char,
    Integer,
    Float,
    Str,
    CStr,
}

impl Display for LitKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Char => write!(f, "char"),
            Self::Integer => write!(f, "integer"),
            Self::Float => write!(f, "float"),
            Self::Str => write!(f, "string"),
            Self::CStr => write!(f, "c_string"),
        }
    }
}

/// The value of a literal.
#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub enum LitVal {
    Char(char),
    Int(u128),
    Float(f64),
    Str(String),
}

impl Display for LitVal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Char(val) => write!(f, "{val:?}"),
            Self::Int(val) => write!(f, "{val:?}"),
            Self::Float(val) => write!(f, "{val:?}"),
            Self::Str(val) => write!(f, "{val:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifiers_checks_test() {
        assert!(is_identifier("hello"));
        assert!(!is_identifier("ça"));
        assert!(!is_identifier("Hello, World!"));
        assert!(!is_identifier("orb"));
    }
}
