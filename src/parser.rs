//! Parser of the l2 language.

use std::fmt::Debug;

use thiserror::Error;

use l2_utils::{
    Span,
    token::{
        Keyword, Punctuation, Token, TokenTree,
        TokenType::{self, *},
    },
};

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
        parse!(@fn $parser => <$node as $crate::parser::AstNode>::parse)
    };
    (@fn $parser:expr => $parsing_fn:expr $(, $arg:expr)*) => (
        $parsing_fn($parser $(, $arg)*)?
    )
}

/// Every source file is a Chunk, a Chunk is a sequence of Statements
#[derive(Debug, Clone)]
pub struct Chunk {
    pub stmts: Vec<Statement>,
    pub loc: Span,
}

impl AstNode for Chunk {
    fn parse(parser: &mut Parser) -> PResult<Self> {
        todo!("chunk parsing :D")
    }
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub stmt: StmtKind,
    pub loc: Span,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    Assignement { variable: String, value: Expression },
}

/// The associativity, is used to parse the binary operations
#[derive(Clone, Debug, PartialEq)]
pub enum Associativity {
    LeftToRight,
    RightToLeft,
    None,
}

/// The precedence table of the Gatti Programming Language
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    // `None` is a special precedence value, it is used to exit out of the loop
    // when a non expression token is after an expression. It is not the
    // `HIGHEST_PRECEDENCE` for the same reason.
    #[doc(hidden)]
    __First__,
    // /!\ Attention /!\
    //
    // If you change the highest precedence in this enumeration change the
    // HIGHEST_PRECEDENCE constant
    //
    /// `or`
    Or,
    /// `and`
    And,
    /// `==  !=`
    Equality,
    /// `<  >  <=  >= `
    Comparison,
    /// `+ -`
    Term,
    /// `* /`
    Factor,
    /// `op expression`
    Unary,
    /// `expression ( expression,* )`
    Call,
    /// `intlit true false charlit strlit parenthesis )`
    Primary,
    // Like `__First__` it is a special variant of `Precedence` that should
    // never be used.
    #[doc(hidden)]
    __Last__,
}

impl Precedence {
    /// Returns the [`Precedence`] following the one passed as arg.
    pub fn next(self) -> Precedence {
        match self {
            Self::__First__ => Self::Or,
            Self::Or => Self::And,
            Self::And => Self::Equality,
            Self::Equality => Self::Comparison,
            Self::Comparison => Self::Term,
            Self::Term => Self::Factor,
            Self::Factor => Self::Unary,
            Self::Unary => Self::Call,
            Self::Call => Self::Primary,
            Self::Primary => Self::__Last__,
            Self::__Last__ => unreachable!(),
        }
    }

    pub fn associativity(&self) -> Associativity {
        match self {
            Self::Or => Associativity::LeftToRight,
            Self::And => Associativity::LeftToRight,
            Self::Equality => Associativity::LeftToRight,
            Self::Comparison => Associativity::LeftToRight,
            Self::Term => Associativity::LeftToRight,
            Self::Factor => Associativity::LeftToRight,
            Self::Unary => Associativity::RightToLeft,
            Self::Call => Associativity::LeftToRight,
            Self::Primary => Associativity::LeftToRight,
            Self::__Last__ | Self::__First__ => unreachable!(),
        }
    }
}

impl From<TokenType> for Precedence {
    fn from(value: TokenType) -> Self {
        use TokenType::Punct;
        match value {
            Punct(Punctuation::Equal2 | Punctuation::BangEqual) => Precedence::Equality,
            Punct(
                Punctuation::LArrow
                | Punctuation::RArrow
                | Punctuation::LArrowEqual
                | Punctuation::RArrowEqual,
            ) => Precedence::Comparison,
            Punct(Punctuation::Plus | Punctuation::Minus) => Precedence::Term,
            Punct(Punctuation::Star | Punctuation::Slash) => Precedence::Factor,
            Punct(Punctuation::LParen) => Precedence::Call,
            _ => panic!("unknown precedence of token {value:?}"),
        }
    }
}

/// The higest precedence of [`Precedence`]
pub const HIGHEST_PRECEDENCE: Precedence = Precedence::Or;

#[derive(Debug, Clone)]
pub struct Expression {
    pub expr: Expr,
    pub loc: Span,
}

impl AstNode for Expression {
    #[inline]
    #[track_caller]
    fn parse(parser: &mut Parser) -> PResult<Self> {
        parse_expr_precedence(parser, HIGHEST_PRECEDENCE)
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    /// Integer literal expression
    IntLit(u64),
    /// Boolean literal expression
    BoolLit(bool),
    /// String literal expression
    StringLit(String),
    /// Grouping expression (just parenthesis)
    Grouping(Box<Expression>),
    /// An identifier expression
    Ident(String),
    /// Binary operation
    Binary {
        lhs: Box<Expression>,
        op: BinOp,
        rhs: Box<Expression>,
    },
    Unary {
        op: UnaryOp,
        expr: Box<Expression>,
    },
}

#[derive(Debug, Clone)]
pub enum BinOp {
    /// addition
    Add,
    /// substraction
    Sub,
    /// multiplication
    Mul,
    /// division
    Div,
    /// less than
    CompLT,
    /// less than or equal
    CompLE,
    /// greater than
    CompGT,
    /// greater than or equal
    CompGE,
    /// equal
    CompEq,
    /// not equal
    CompNe,
}

impl BinOp {
    pub fn from_punct(punct: Punctuation) -> Option<BinOp> {
        use BinOp as BOp;
        use Punctuation as Punct;
        Some(match punct {
            Punct::Star => BOp::Mul,
            Punct::Slash => BOp::Div,
            Punct::Plus => BOp::Add,
            Punct::Minus => BOp::Sub,
            Punct::LArrow => BOp::CompLT,
            Punct::RArrow => BOp::CompGT,
            Punct::LArrowEqual => BOp::CompLE,
            Punct::RArrowEqual => BOp::CompGE,
            Punct::Equal2 => BOp::CompEq,
            Punct::BangEqual => BOp::CompNe,
            _ => return None,
        })
    }

    pub fn from_tt(tt: TokenType) -> Option<BinOp> {
        match tt {
            Punct(p) => Self::from_punct(p),
            _ => None,
        }
    }
}

/// Parses an expression given the following precedence.
pub fn parse_expr_precedence(parser: &mut Parser, precedence: Precedence) -> PResult<Expression> {
    let mut lhs = match parser.peek_tt() {
        Some(IntLit(_)) => parse!(@fn parser => parse_intlit_expr),
        Some(KW(Keyword::True | Keyword::False)) => parse!(@fn parser => parse_boollit_expr),
        // Some(Char(_)) => parse!(@fn parser => parse_charlit_expr),
        Some(StringLit(_)) => parse!(@fn parser => parse_strlit_expr),
        Some(Punct(Punctuation::LParen)) => parse!(@fn parser => parse_grouping_expr),
        Some(Ident(_)) => parse!(@fn parser => parse_ident_expr),
        Some(tt) if UnaryOp::from_tt(tt.clone()).is_some() => {
            parse!(@fn parser => parse_unary_expr)
        }
        Some(_) => {
            // unwrap is safe because we already know the next has a token type
            let t = parser.peek_tok().unwrap().clone();
            return Err(ParsingError::new_expected("expression", t.tt, t.loc));
        }
        None => return Err(ParsingError::ReachedEOF),
    };

    loop {
        let Some(tt) = parser.peek_tt().cloned() else {
            break;
        };
        if precedence > Precedence::from(tt) {
            break;
        }

        // we match a token here, because, in the future there will be
        // binary operators that are Keyword, like Logical And.
        lhs = match parser.peek_tt() {
            // Some(Punct(Punctuation::LParen)) => {
            //     parse!(@fn parser => parse_call_expr, Box::new(lhs))
            // }
            Some(maybe_bin_op) if BinOp::from_tt(maybe_bin_op.clone()).is_some() => {
                parse!(@fn parser => parse_binary_expr, lhs)
            }
            _ => break,
        }
    }

    Ok(lhs)
}

/// Parse an integer literal expression
pub fn parse_intlit_expr(parser: &mut Parser) -> PResult<Expression> {
    let (i, loc) = expect_token!(parser => [IntLit(i), *i], "integer literal");

    Ok(Expression {
        expr: Expr::IntLit(i),
        loc,
    })
}

/// Parse a boolean literal expression
pub fn parse_boollit_expr(parser: &mut Parser) -> PResult<Expression> {
    let (b, loc) = expect_token!(parser => [KW(Keyword::True), true; KW(Keyword::False), false], "bool literal");

    Ok(Expression {
        expr: Expr::BoolLit(b),
        loc,
    })
}

/// Parse a string literal expression
pub fn parse_strlit_expr(parser: &mut Parser) -> PResult<Expression> {
    let (str, loc) = expect_token!(parser => [StringLit(s), s.clone()], "integer literal");

    Ok(Expression {
        expr: Expr::StringLit(str),
        loc,
    })
}

/// Parse a grouping expression
pub fn parse_grouping_expr(parser: &mut Parser) -> PResult<Expression> {
    let ((), start) =
        expect_token!(parser => [Punct(Punctuation::LParen), ()], Punctuation::LParen);
    let expr = Box::new(parse!(parser => Expression));
    let ((), end) = expect_token!(parser => [Punct(Punctuation::RParen), ()], Punctuation::RParen);

    Ok(Expression {
        expr: Expr::Grouping(expr),
        loc: Span::from_ends(start, end),
    })
}

/// Parse an identifier expression
pub fn parse_ident_expr(parser: &mut Parser) -> PResult<Expression> {
    let (id, loc) = expect_token!(parser => [Ident(s), s.clone()], "integer literal");

    Ok(Expression {
        expr: Expr::Ident(id),
        loc,
    })
}

/// Parse binary expression, `expression op expression`
pub fn parse_binary_expr(parser: &mut Parser, lhs: Expression) -> PResult<Expression> {
    let (op, tok) = match parser.peek_tok() {
        // TODO: here we compute twice the binary op its a little dumb, find a solution to that problem.
        Some(Token { tt: op, .. }) if BinOp::from_tt(op.clone()).is_some() => {
            let op = op.clone();
            parser.pop();
            (BinOp::from_tt(op.clone()).unwrap(), op)
        }
        Some(tok) => {
            let t = tok.clone();
            return Err(ParsingError::new_expected("binary operator", t.tt, t.loc));
        }
        None => return Err(ParsingError::ReachedEOF),
    };
    let mut pr = Precedence::from(tok.clone());

    if pr.associativity() == Associativity::LeftToRight {
        pr = pr.next();
    }

    let rhs = parse!(@fn parser => parse_expr_precedence, pr);
    let loc = Span::from_ends(lhs.loc.clone(), rhs.loc.clone());

    Ok(Expression {
        expr: Expr::Binary {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        },
        loc,
    })
}

/// Unary Operators
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    // LEFT UNARY OPERATOR
    /// `"-" expression`
    Negation,
    /// `not expression`
    Not,
}

impl UnaryOp {
    pub fn from_tt(tt: TokenType) -> Option<UnaryOp> {
        match tt {
            Punct(Punctuation::Minus) => Some(UnaryOp::Negation),
            KW(Keyword::Not) => Some(UnaryOp::Not),
            _ => None,
        }
    }
}

/// Parse unary expression, `op expression`
pub fn parse_unary_expr(parser: &mut Parser) -> PResult<Expression> {
    let (op, start) = expect_token!(parser => [
        Punct(Punctuation::Minus), UnaryOp::Negation;
        KW(Keyword::Not), UnaryOp::Not;
    ], "minus operator or keyword not");

    let expr = Box::new(parse!(@fn parser => parse_expr_precedence, Precedence::Unary));

    Ok(Expression {
        loc: Span::from_ends(start, expr.loc.clone()),
        expr: Expr::Unary { op, expr },
    })
}
