//! Token related to tokens shared between lunc_lexer and lunc_parser.
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/src/assets/logo_no_bg_black.png"
)]

use std::{
    fmt::{self, Debug, Display},
    hash::{DefaultHasher, Hash, Hasher},
    io::{self, Write},
    mem,
};

use lunc_utils::{FileId, Span, opt_unreachable};

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

    /// Get the token a the index `idx`, always returns the EOF token if `idx`
    /// is out of bounds of the stream.
    ///
    /// # Panic
    ///
    /// This function will panic if you call it on a non-finished token stream
    #[track_caller]
    pub fn get(&self, idx: usize) -> &Token {
        assert!(
            self.finished,
            "can't access tokens while the token stream isn't finished."
        );
        self.toks.get(idx).unwrap_or_else(|| self.get_eof())
    }

    /// Get the last token of a finished token stream, it will always be the
    /// EOF token
    ///
    /// # Panic
    ///
    /// This function will panic if you call it on a non-finished token stream
    #[track_caller]
    pub fn get_eof(&self) -> &Token {
        assert!(
            self.finished,
            "can't access tokens while the token stream isn't finished."
        );

        let Some(eof) = self.toks.last() else {
            // SAFETY: a token stream is ensured to contain an eof token
            opt_unreachable!();
        };

        eof
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
            TokenType::Lit(Lit { kind, value, tag }) => {
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

    /// Create a new dummy token.
    pub const fn dummy() -> Token {
        Token {
            tt: TokenType::Dummy,
            loc: Span::ZERO,
        }
    }
}

impl PartialEq<TokenType> for Token {
    fn eq(&self, other: &TokenType) -> bool {
        self.tt == *other
    }
}

// WARN: when adding a new token, a correspond test should be added into
// `tests/lexer/` that should test everything about this new token
// WARN: /!\ If a keyword is added change the `lex_identifier` method of the
// Lexer and add it to the list of all keywords.
/// Token type.
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
    Lit(Lit),
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
            Tt::Lit(Lit { kind, .. }) => write!(f, "{kind} literal"),
            Tt::EOF => write!(f, "<eof>"),
            Tt::Dummy => write!(f, "not a token"),
        }
    }
}

impl PartialEq<ExpToken> for TokenType {
    fn eq(&self, other: &ExpToken) -> bool {
        let mut state = DefaultHasher::new();
        mem::discriminant(self).hash(&mut state);
        let self_hash = state.finish();

        state = DefaultHasher::new();
        other.hash(&mut state);
        let other_hash = state.finish();

        self_hash == other_hash
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
pub struct Lit {
    pub kind: LitKind,
    pub value: LitVal,
    pub tag: Option<String>,
}

impl Lit {
    /// Create a new character literal
    pub const fn char(val: char) -> Lit {
        Lit {
            kind: LitKind::Char,
            value: LitVal::Char(val),
            tag: None,
        }
    }

    /// Create a new integer literal
    pub const fn int(val: u128) -> Lit {
        Lit {
            kind: LitKind::Integer,
            value: LitVal::Int(val),
            tag: None,
        }
    }

    /// Create a new float literal
    pub const fn float(val: f64) -> Lit {
        Lit {
            kind: LitKind::Float,
            value: LitVal::Float(val),
            tag: None,
        }
    }

    /// Create a new string literal
    pub fn string(val: String) -> Lit {
        Lit {
            kind: LitKind::Str,
            value: LitVal::Str(val),
            tag: None,
        }
    }

    /// Create a new c string literal
    pub fn c_string(val: String) -> Lit {
        Lit {
            kind: LitKind::CStr,
            value: LitVal::Str(val),
            tag: None,
        }
    }
}

impl Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.kind, self.value)
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

/// Expected token.
///
/// This is used by `E006`, `ExpectedToken`, diagnostics to avoid
/// creating empty tokens when a TokenType expects a value, so [`ExpToken`]
/// don't expect a value.
///
/// This is also used by `check` and `expect` methods of the parser.
///
/// *This is inspired by [rustc's TokenType].*
///
/// [rustc's TokenType]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_parse/parser/token_type/enum.TokenType.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExpToken {
    LParen,
    RParen,
    LBracket,
    RBracket,
    LCurly,
    RCurly,
    Plus,
    Minus,
    Star,
    Slash,
    Colon,
    Comma,
    Eq,
    EqEq,
    BangEq,
    Bang,
    LtEq,
    Lt,
    LtLt,
    Gt,
    GtGt,
    GtEq,
    Semi,
    MinusGt,
    Caret,
    And,
    AndAnd,
    Or,
    OrOr,
    Percent,
    Dot,
    DotStar,
    Pound,
    KwAs,
    KwBreak,
    KwComptime,
    KwContinue,
    KwDefer,
    KwElse,
    KwExtern,
    KwFalse,
    KwFor,
    KwFun,
    KwIf,
    KwImpl,
    KwIn,
    KwLet,
    KwLoop,
    KwMut,
    KwNull,
    KwOrb,
    KwPub,
    KwReturn,
    KwSelfVal,
    KwThen,
    KwTrait,
    KwTrue,
    KwWhile,
    Ident,
    Lit,
    EOF,
    Dummy,
}

impl Display for ExpToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExpToken as Et;

        match self {
            Et::LParen => write!(f, "`(`"),
            Et::RParen => write!(f, "`)`"),
            Et::LBracket => write!(f, "`[`"),
            Et::RBracket => write!(f, "`]`"),
            Et::LCurly => write!(f, "`{{`"),
            Et::RCurly => write!(f, "`}}`"),
            Et::Plus => write!(f, "`+`"),
            Et::Minus => write!(f, "`-`"),
            Et::Star => write!(f, "`*`"),
            Et::Slash => write!(f, "`/`"),
            Et::Colon => write!(f, "`:`"),
            Et::Comma => write!(f, "`,`"),
            Et::Eq => write!(f, "`=`"),
            Et::EqEq => write!(f, "`==`"),
            Et::BangEq => write!(f, "`!=`"),
            Et::Bang => write!(f, "`!`"),
            Et::LtEq => write!(f, "`<=`"),
            Et::Lt => write!(f, "`<`"),
            Et::LtLt => write!(f, "`<<`"),
            Et::Gt => write!(f, "`>`"),
            Et::GtGt => write!(f, "`>>`"),
            Et::GtEq => write!(f, "`>=`"),
            Et::Semi => write!(f, "`;`"),
            Et::MinusGt => write!(f, "`->`"),
            Et::Caret => write!(f, "`^`"),
            Et::And => write!(f, "`&`"),
            Et::AndAnd => write!(f, "`&&`"),
            Et::Or => write!(f, "`|`"),
            Et::OrOr => write!(f, "`||`"),
            Et::Percent => write!(f, "`%`"),
            Et::Dot => write!(f, "`.`"),
            Et::DotStar => write!(f, "`.*`"),
            Et::Pound => write!(f, "`#`"),
            Et::KwAs => write!(f, "keyword `as`"),
            Et::KwBreak => write!(f, "keyword `break`"),
            Et::KwComptime => write!(f, "keyword `comptime`"),
            Et::KwContinue => write!(f, "keyword `continue`"),
            Et::KwDefer => write!(f, "keyword `defer`"),
            Et::KwElse => write!(f, "keyword `else`"),
            Et::KwExtern => write!(f, "keyword `extern`"),
            Et::KwFalse => write!(f, "keyword `false`"),
            Et::KwFor => write!(f, "keyword `for`"),
            Et::KwFun => write!(f, "keyword `fun`"),
            Et::KwIf => write!(f, "keyword `if`"),
            Et::KwImpl => write!(f, "keyword `impl`"),
            Et::KwIn => write!(f, "keyword `in`"),
            Et::KwLet => write!(f, "keyword `let`"),
            Et::KwLoop => write!(f, "keyword `loop`"),
            Et::KwMut => write!(f, "keyword `mut`"),
            Et::KwNull => write!(f, "keyword `null`"),
            Et::KwOrb => write!(f, "keyword `orb`"),
            Et::KwPub => write!(f, "keyword `pub`"),
            Et::KwReturn => write!(f, "keyword `return`"),
            Et::KwSelfVal => write!(f, "keyword `self`"),
            Et::KwThen => write!(f, "keyword `then`"),
            Et::KwTrait => write!(f, "keyword `trait`"),
            Et::KwTrue => write!(f, "keyword `true`"),
            Et::KwWhile => write!(f, "keyword `while`"),
            Et::Ident => write!(f, "identifier"),
            Et::Lit => write!(f, "literal"),
            Et::EOF => write!(f, "end of file"),
            Et::Dummy => unreachable!(),
        }
    }
}

impl PartialEq<TokenType> for ExpToken {
    fn eq(&self, other: &TokenType) -> bool {
        other.eq(self)
    }
}

/// A bitset used by `Parser::check`, `Parser::eat` and `Parser::expect`
///
/// *This is inspired by [rustc's TokenTypeSet].*
///
/// [rustc's TokenTypeSet]: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_parse/parser/token_type/struct.TokenTypeSet.html
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ExpTokenSet(u64);

impl ExpTokenSet {
    /// Create a new ExpToken Set.
    pub fn new() -> ExpTokenSet {
        ExpTokenSet(0)
    }

    /// Insert an ExpToken inside the set.
    pub fn insert(&mut self, exp: ExpToken) {
        self.0 |= 1u64 << exp as u64;
    }

    /// Does this ExpTokenSet contains `exp`?
    pub fn contains(&self, exp: ExpToken) -> bool {
        self.0 & (1u64 << exp as u64) != 0
    }

    /// Clear the set.
    pub fn clear(&mut self) {
        self.0 = 0;
    }

    /// Create an iterator of [`ExpToken`].
    pub fn iter(&self) -> ExpTokenSetIter {
        ExpTokenSetIter(*self)
    }
}

impl Default for ExpTokenSet {
    fn default() -> Self {
        ExpTokenSet::new()
    }
}

/// Iterator of [`ExpToken`] in a [`ExpTokenSet`].
pub struct ExpTokenSetIter(ExpTokenSet);

impl Iterator for ExpTokenSetIter {
    type Item = ExpToken;

    fn next(&mut self) -> Option<Self::Item> {
        let num_bits = (size_of_val(&self.0.0) * 8) as u64;
        debug_assert_eq!(num_bits, 64);

        let zeros = self.0.0.trailing_zeros() as u64;

        if zeros == num_bits {
            None
        } else {
            self.0.0 &= !(1 << zeros);

            if !(0..=62).contains(&zeros) {
                panic!("invalid token repr {zeros}")
            }

            Some(unsafe { mem::transmute::<u8, ExpToken>(zeros as u8) })
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

    macro_rules! eq_test {
        ($name:ident) => {
            assert!(TokenType::$name.eq(&ExpToken::$name));
            assert!(ExpToken::$name.eq(&TokenType::$name));
        };
        (@val $tt:expr, $exp:expr) => {
            assert!($tt.eq(&$exp));
            assert!($exp.eq(&$tt));
        };
    }

    #[test]
    fn exp_token_and_token_type_equality() {
        eq_test!(LParen);
        eq_test!(RParen);
        eq_test!(LBracket);
        eq_test!(RBracket);
        eq_test!(LCurly);
        eq_test!(RCurly);
        eq_test!(Plus);
        eq_test!(Minus);
        eq_test!(Star);
        eq_test!(Slash);
        eq_test!(Colon);
        eq_test!(Comma);
        eq_test!(Eq);
        eq_test!(EqEq);
        eq_test!(BangEq);
        eq_test!(Bang);
        eq_test!(LtEq);
        eq_test!(Lt);
        eq_test!(LtLt);
        eq_test!(Gt);
        eq_test!(GtGt);
        eq_test!(GtEq);
        eq_test!(Semi);
        eq_test!(MinusGt);
        eq_test!(Caret);
        eq_test!(And);
        eq_test!(AndAnd);
        eq_test!(Or);
        eq_test!(OrOr);
        eq_test!(Percent);
        eq_test!(Dot);
        eq_test!(DotStar);
        eq_test!(Pound);
        eq_test!(KwAs);
        eq_test!(KwBreak);
        eq_test!(KwComptime);
        eq_test!(KwContinue);
        eq_test!(KwDefer);
        eq_test!(KwElse);
        eq_test!(KwExtern);
        eq_test!(KwFalse);
        eq_test!(KwFor);
        eq_test!(KwFun);
        eq_test!(KwIf);
        eq_test!(KwImpl);
        eq_test!(KwIn);
        eq_test!(KwLet);
        eq_test!(KwLoop);
        eq_test!(KwMut);
        eq_test!(KwNull);
        eq_test!(KwOrb);
        eq_test!(KwPub);
        eq_test!(KwReturn);
        eq_test!(KwSelfVal);
        eq_test!(KwThen);
        eq_test!(KwTrait);
        eq_test!(KwTrue);
        eq_test!(KwWhile);
        eq_test!(@val TokenType::Ident(String::from("Hello")), ExpToken::Ident);
        eq_test!(@val TokenType::Ident(String::new()), ExpToken::Ident);
        eq_test!(@val TokenType::Ident(String::from("..")), ExpToken::Ident);
        eq_test!(@val TokenType::Ident(String::from("Très bien!")), ExpToken::Ident);
        eq_test!(@val TokenType::Lit(Lit::int(123)), ExpToken::Lit);
        eq_test!(@val TokenType::Lit(Lit::char('L')), ExpToken::Lit);
        eq_test!(@val TokenType::Lit(Lit::float(6.9)), ExpToken::Lit);
        eq_test!(@val TokenType::Lit(Lit::string("Hello, world".to_string())), ExpToken::Lit);
        eq_test!(EOF);
        eq_test!(Dummy);
    }
}
