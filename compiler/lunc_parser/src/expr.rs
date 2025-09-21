//! Parsing of lun's expressions.

use std::fmt::Display;

use lunc_utils::opt_unreachable;

use crate::stmt::Block;

use super::*;

/// The associativity, is used to parse the binary operations
#[derive(Clone, Debug, PartialEq)]
pub enum Associativity {
    LeftToRight,
    RightToLeft,
    None,
}

/// Expression in lun.
#[derive(Debug, Clone)]
pub struct Expression {
    pub expr: Expr,
    pub loc: Span,
}

impl Expression {
    /// Is the expression `ExpressionWithBlock`?
    pub fn is_expr_with_block(&self) -> bool {
        matches!(
            self.expr,
            Expr::If(_)
                | Expr::Block(_)
                | Expr::BlockWithLabel { .. }
                | Expr::PredicateLoop { .. }
                | Expr::IteratorLoop { .. }
                | Expr::FunDefinition { .. }
                | Expr::InfiniteLoop { .. }
        )
    }
}

/// parses a type expression with a precedence of logical or and cannot be a
/// labelled expression.
///
/// # Why?
///
/// - We parse only to the precedence equal to logical or, because in binding
///   definition like `a : u32 = 12;` gets parsed as `a : (u32 = 12);` (instead
///   of `a : (u32) = 12;`) if we dont lower the precedence.
///
/// - We don't allow labelled expression because a binding definition like `a
///   : u32 : loop {};` gets parsed as `a : (u32: loop {});` (instead of `a :
///   (u32) : loop {};`) so it is disallowed.
///
/// **BUT** those expression can still be written if wrapped in parenthesis:
/// - `a : (a = u32) = 12;` and
/// - `a : (a: loop {}) : 12;`
pub fn parse_typexpr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    parse_expr_precedence(parser, Precedence::LogicalOr, true)
}

impl AstNode for Expression {
    #[inline]
    #[track_caller]
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        parse_expr_precedence(parser, HIGHEST_PRECEDENCE, false)
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    /// integer literal expression
    ///
    /// `integer`
    IntLit(u128),
    /// boolean literal expression
    ///
    /// `"true" | "false"`
    BoolLit(bool),
    /// string literal expression
    ///
    /// `string`
    StringLit(String),
    /// C string literal expression
    ///
    /// *specialized string, with prefix 'c'*
    CStrLit(String),
    /// character literal expression
    ///
    /// `char`
    CharLit(char),
    /// float literal expression
    ///
    /// `float`
    FloatLit(f64),
    /// grouping expression (just parenthesis)
    ///
    /// `"(" expr ")"`
    Grouping(Box<Expression>),
    /// an identifier expression
    ///
    /// `ident`
    Ident(String),
    /// binary operation
    ///
    /// `expr op expr`
    Binary {
        lhs: Box<Expression>,
        op: BinOp,
        rhs: Box<Expression>,
    },
    /// unary operation
    ///
    /// `op expr`
    Unary { op: UnaryOp, expr: Box<Expression> },
    /// Borrow operator
    ///
    /// `"&" "mut"? expression`
    Borrow {
        mutable: bool,
        expr: Box<Expression>,
    },
    /// function call expression
    ///
    /// `expr "(" ( expr ),* ")"`
    FunCall {
        callee: Box<Expression>,
        args: Vec<Expression>,
    },
    /// if else expression
    ///
    /// `"if" expression block [ "else" (if-expr | block-expr) ]`
    If(IfExpression),
    /// if then else expression
    ///
    /// `"if" expression "then" expression "else" expression`
    IfThenElse {
        cond: Box<Expression>,
        true_val: Box<Expression>,
        false_val: Box<Expression>,
    },
    /// block expression
    // TODO: make the grammar for block expr
    Block(Block),
    /// block with label
    BlockWithLabel { label: (String, Span), block: Block },
    /// predicate loop expression
    ///
    /// `"while" expression block`
    PredicateLoop {
        label: Option<(String, Span)>,
        cond: Box<Expression>,
        body: Block,
    },
    /// iterator loop expression
    ///
    /// `"for" ident "in" expression block`
    IteratorLoop {
        label: Option<(String, Span)>,
        variable: String,
        iterator: Box<Expression>,
        body: Block,
        // NOTE: this is used to emit the diagnostic `feature_todo`.
        loc: Span,
    },
    /// infinite loop
    ///
    /// `"loop" block`
    InfiniteLoop {
        label: Option<(String, Span)>,
        body: Block,
    },
    /// return expression
    ///
    /// `"return" expression?`
    Return { expr: Option<Box<Expression>> },
    /// break expression
    ///
    /// `"break" [ ":" ident ] expression?`
    Break {
        label: Option<String>,
        expr: Option<Box<Expression>>,
    },
    /// continue expression
    ///
    /// `"continue"`
    Continue { label: Option<String> },
    /// null expression
    ///
    /// `"null"`
    Null,
    /// member access expression
    ///
    /// `expr "." ident`
    MemberAccess {
        expr: Box<Expression>,
        member: String,
    },
    /// orb expression
    ///
    /// `"orb"`
    Orb,
    //
    // definitions
    //
    /// function definition expression
    ///
    /// `"fun" "(" ( ident ":" expr ),* ")" [ "->" expr ] block`
    FunDefinition {
        args: Vec<Arg>,
        rettypexpr: Option<Box<Expression>>,
        body: Block,
    },
    /// function declaration expression
    ///
    /// `"fun" "(" ( expr ),* ")" [ "->" expr ]`
    FunDeclaration {
        args: Vec<Expression>,
        rettypexpr: Option<Box<Expression>>,
    },
    //
    // type expression
    //
    /// pointer type expression
    ///
    /// `"*" "mut"? expression`
    PointerType {
        mutable: bool,
        typexpr: Box<Expression>,
    },
    /// function pointer type
    ///
    /// `"*" "fun" "(" ( expr ),* ")" [ "->" expr ]`
    FunPtrType {
        args: Vec<Expression>,
        ret: Option<Box<Expression>>,
    },
}

#[derive(Debug, Clone)]
pub struct IfExpression {
    pub cond: Box<Expression>,
    pub body: Box<Block>,
    pub else_br: Option<Box<Else>>,
    pub loc: Span,
}

#[derive(Debug, Clone)]
pub enum Else {
    IfExpr(IfExpression),
    Block(Block),
}

#[derive(Debug, Clone)]
pub struct Arg {
    pub name: String,
    pub name_loc: Span,
    pub typexpr: Expression,
    pub loc: Span,
}

/// Parses an expression given the following precedence.
///
/// `typexpr` when set to true, it will parse with some constraints described in
/// [`parse_typexpr`].
pub fn parse_expr_precedence(
    parser: &mut Parser,
    precedence: Precedence,
    typexpr: bool,
) -> Result<Expression, Diagnostic> {
    // TODO: parsing of range expressions, `expr..<expr` and `expr..=expr`, and
    // maybe `..<expr`, `..=expr` and maybe `expr..`
    let mut lhs = match parser.peek_tt() {
        Some(IntLit(_)) => parse!(@fn parser => parse_intlit_expr),
        Some(Kw(Keyword::True | Keyword::False)) => parse!(@fn parser => parse_boollit_expr),
        Some(StringLit(_)) => parse!(@fn parser => parse_strlit_expr),
        Some(SpecializedStringLit {
            specialization,
            str: _,
        }) if specialization == "c" => parse!(@fn parser => parse_cstrlit_expr),
        Some(CharLit(_)) => parse!(@fn parser => parse_charlit_expr),
        Some(FloatLit(_)) => parse!(@fn parser => parse_floatlit_expr),
        Some(Punct(Punctuation::LParen)) => parse!(@fn parser => parse_grouping_expr),
        Some(Punct(Punctuation::Ampsand)) => parse!(@fn parser => parse_borrow_expr),
        Some(Ident(_)) if !typexpr && parser.is_labeled_expr() => match parser.nth_tt(2) {
            Some(Kw(Keyword::Loop)) => parse!(@fn parser => parse_infinite_loop_expr),
            Some(Kw(Keyword::While)) => parse!(@fn parser => parse_predicate_loop_expr),
            Some(Kw(Keyword::For)) => parse!(@fn parser => parse_iterator_loop_expr),
            Some(Punct(Punctuation::LBrace)) => parse!(@fn parser => parse_block_expr),
            // SAFETY: we checked in the if of the match arm that it can only
            // be a keyword and one of loop, while or for
            _ => opt_unreachable!(),
        },
        Some(Ident(_)) => parse!(@fn parser => parse_ident_expr),
        Some(Kw(Keyword::Fun)) => parse!(@fn parser => parse_funkw_expr),
        Some(Kw(Keyword::If)) => parse!(@fn parser => parse_if_else_expr, false),
        Some(Kw(Keyword::While)) => parse!(@fn parser => parse_predicate_loop_expr),
        Some(Kw(Keyword::For)) => parse!(@fn parser => parse_iterator_loop_expr),
        Some(Kw(Keyword::Loop)) => parse!(@fn parser => parse_infinite_loop_expr),
        Some(Kw(Keyword::Return)) => parse!(@fn parser => parse_return_expr),
        Some(Kw(Keyword::Break)) => parse!(@fn parser => parse_break_expr),
        Some(Kw(Keyword::Continue)) => parse!(@fn parser => parse_continue_expr),
        Some(Kw(Keyword::Null)) => parse!(@fn parser => parse_null_expr),
        Some(Kw(Keyword::Orb)) => parse!(@fn parser => parse_orb_expr),
        Some(Punct(Punctuation::LBrace)) => parse!(@fn parser => parse_block_expr),
        Some(Punct(Punctuation::Star))
            if parser.nth_tt(1) == Some(&TokenType::Kw(Keyword::Fun)) =>
        {
            parse!(@fn parser => parse_funptr_type_expr)
        }
        Some(Punct(Punctuation::Star)) => parse!(@fn parser => parse_pointer_type_expr),
        Some(tt) if UnaryOp::left_from_token(tt.clone()).is_some() => {
            parse!(@fn parser => parse_unary_left_expr)
        }
        Some(_) => {
            // unwrap is safe because we already know the next has a token type
            let t = parser.peek_tok().unwrap().clone();
            // TODO: make the parser retry if he failed to parse lhs with a
            // loop, see parsing of statements also.

            // TEST: no. 1
            return Err(ExpectedToken::new("expression", t.tt, None::<String>, t.loc).into_diag());
        }
        None => {
            return Err(parser.eof_diag());
        }
    };

    loop {
        let Some(tt) = parser.peek_tt().cloned() else {
            break;
        };

        let Some(pr) = Precedence::from(tt) else {
            // the next token isn't part of a post expression
            break;
        };

        if precedence > pr {
            break;
        }

        lhs = match parser.peek_tt() {
            Some(Punct(Punctuation::LParen)) => {
                parse!(@fn parser => parse_funcall_expr, Box::new(lhs))
            }
            Some(Punct(Punctuation::Dot)) => {
                parse!(@fn parser => parse_member_access_expr, lhs)
            }
            Some(maybe_bin_op) if BinOp::from_tt(maybe_bin_op.clone()).is_some() => {
                parse!(@fn parser => parse_binary_expr, lhs)
            }
            Some(maybe_right_op) if UnaryOp::right_from_token(maybe_right_op.clone()).is_some() => {
                parse!(@fn parser => parse_unary_right_expr, lhs)
            }
            _ => break,
        };
    }

    Ok(lhs)
}

impl Parser {
    pub fn is_labeled_expr(&self) -> bool {
        matches!(self.nth_tt(1), Some(Punct(Punctuation::Colon)))
            && matches!(
                self.nth_tt(2),
                Some(
                    Kw(Keyword::While | Keyword::For | Keyword::Loop) | Punct(Punctuation::LBrace)
                )
            )
    }
}

/// Parse an integer literal expression
pub fn parse_intlit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (i, loc) = expect_token!(parser => [IntLit(i), *i], "integer literal");

    Ok(Expression {
        expr: Expr::IntLit(i),
        loc,
    })
}

/// Parse a boolean literal expression
pub fn parse_boollit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (b, loc) = expect_token!(parser => [Kw(Keyword::True), true; Kw(Keyword::False), false], "bool literal");

    Ok(Expression {
        expr: Expr::BoolLit(b),
        loc,
    })
}

/// Parse a string literal expression
pub fn parse_strlit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (str, loc) = expect_token!(parser => [StringLit(s), s.clone()], "string literal");

    Ok(Expression {
        expr: Expr::StringLit(str),
        loc,
    })
}

/// Parse a C string literal expression
pub fn parse_cstrlit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (str, loc) = expect_token!(parser =>
        [
            SpecializedStringLit { specialization, str},
            str.clone(),
            if specialization == "c"
        ], "c string literal");

    Ok(Expression {
        expr: Expr::CStrLit(str),
        loc,
    })
}

/// Parses a character literal expression
pub fn parse_charlit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (char, loc) = expect_token!(parser => [CharLit(c), *c], "character literal");

    Ok(Expression {
        expr: Expr::CharLit(char),
        loc,
    })
}

/// Parses a float literal expression
pub fn parse_floatlit_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (float, loc) = expect_token!(parser => [FloatLit(f), *f], "float literal");

    Ok(Expression {
        expr: Expr::FloatLit(float),
        loc,
    })
}

/// Parse a grouping expression
pub fn parse_grouping_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let ((), lo) = expect_token!(parser => [Punct(Punctuation::LParen), ()], [Punctuation::LParen]);
    let expr = parse!(box: parser => Expression);
    // TEST: yes
    let ((), hi) = expect_token!(parser => [Punct(Punctuation::RParen), ()], [Punctuation::RParen]);

    Ok(Expression {
        expr: Expr::Grouping(expr),
        loc: Span::from_ends(lo, hi),
    })
}

/// Parse an identifier expression
pub fn parse_ident_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (id, loc) = expect_token!(parser => [Ident(s), s.clone()], Ident(String::new()));

    Ok(Expression {
        expr: Expr::Ident(id),
        loc,
    })
}

/// The precedence table of Lun
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
    /// `a = b`
    Assignment,
    /// `a or b`
    LogicalOr,
    /// `a and b`
    LogicalAnd,
    /// `a < b ; a > b ; a <= b ; a >= b`
    Comparison,
    /// `a == b ; a != b`
    Equality,
    /// `a | b`
    BitwiseOr,
    /// `a ^ b`
    BitwiseXor,
    /// `a & b`
    BitwiseAnd,
    /// `a >> b ; a << b`
    Shift,
    /// `a + b ; a - b`
    Term,
    /// `a * b ; a / b ; a % b`
    Factor,
    /// `op expression`
    Unary,
    /// `expression "(" expression,* ")"`
    Call,
    /// `expression "." ident`
    MemberAccess,
    /// `intlit "true" "false" charlit strlit group`
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
            Self::__First__ => Self::Assignment,
            Self::Assignment => Self::LogicalOr,
            Self::LogicalOr => Self::LogicalAnd,
            Self::LogicalAnd => Self::Comparison,
            Self::Comparison => Self::Equality,
            Self::Equality => Self::BitwiseOr,
            Self::BitwiseOr => Self::BitwiseXor,
            Self::BitwiseXor => Self::BitwiseAnd,
            Self::BitwiseAnd => Self::Shift,
            Self::Shift => Self::Term,
            Self::Term => Self::Factor,
            Self::Factor => Self::Unary,
            Self::Unary => Self::Call,
            Self::Call => Self::MemberAccess,
            Self::MemberAccess => Self::Primary,
            Self::Primary => Self::__Last__,
            Self::__Last__ => unreachable!(),
        }
    }

    pub fn associativity(&self) -> Associativity {
        match self {
            Self::Assignment => Associativity::RightToLeft,
            Self::LogicalOr => Associativity::LeftToRight,
            Self::LogicalAnd => Associativity::LeftToRight,
            Self::Comparison => Associativity::LeftToRight,
            Self::Equality => Associativity::LeftToRight,
            Self::BitwiseOr => Associativity::LeftToRight,
            Self::BitwiseXor => Associativity::LeftToRight,
            Self::BitwiseAnd => Associativity::LeftToRight,
            Self::Shift => Associativity::LeftToRight,
            Self::Term => Associativity::LeftToRight,
            Self::Factor => Associativity::LeftToRight,
            Self::Unary => Associativity::RightToLeft,
            Self::Call => Associativity::LeftToRight,
            Self::MemberAccess => Associativity::LeftToRight,
            Self::Primary => Associativity::LeftToRight,
            Self::__Last__ | Self::__First__ => unreachable!(),
        }
    }
}

impl Precedence {
    fn from(value: TokenType) -> Option<Precedence> {
        use TokenType::Punct;
        match value {
            Punct(Punctuation::Equal) => Some(Precedence::Assignment),
            Kw(Keyword::Or) => Some(Precedence::LogicalOr),
            Kw(Keyword::And) => Some(Precedence::LogicalAnd),
            Punct(
                Punctuation::Lt | Punctuation::Gt | Punctuation::LtEqual | Punctuation::GtEqual,
            ) => Some(Precedence::Comparison),
            Punct(Punctuation::Equal2 | Punctuation::BangEqual) => Some(Precedence::Equality),
            Punct(Punctuation::Pipe) => Some(Precedence::BitwiseOr),
            Punct(Punctuation::Caret) => Some(Precedence::BitwiseXor),
            Punct(Punctuation::Ampsand) => Some(Precedence::BitwiseAnd),
            Punct(Punctuation::Lt2 | Punctuation::Gt2) => Some(Precedence::Shift),
            Punct(Punctuation::Plus | Punctuation::Minus) => Some(Precedence::Term),
            Punct(Punctuation::Star | Punctuation::Slash | Punctuation::Percent) => {
                Some(Precedence::Factor)
            }
            Punct(Punctuation::LParen) => Some(Precedence::Call),
            Punct(Punctuation::Dot) => Some(Precedence::MemberAccess),
            Punct(Punctuation::DotStar) => Some(Precedence::Primary),
            _ => None,
        }
    }
}

/// The highest precedence of [`Precedence`]
pub const HIGHEST_PRECEDENCE: Precedence = Precedence::Assignment;

#[derive(Debug, Clone)]
pub enum BinOp {
    /// addition
    Add,
    /// subtraction
    Sub,
    /// multiplication
    Mul,
    /// division
    Div,
    /// remainder
    Rem,
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
    /// assignment
    Assignment,
    /// and
    LogicalAnd,
    /// or
    LogicalOr,
    /// &
    BitwiseAnd,
    /// ^
    BitwiseXor,
    /// |
    BitwiseOr,
    /// shift right, >>
    Shr,
    /// shift left, <<
    Shl,
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
            Self::CompLT => "<",
            Self::CompLE => "<=",
            Self::CompGT => ">",
            Self::CompGE => ">=",
            Self::CompEq => "==",
            Self::CompNe => "!=",
            Self::Assignment => "=",
            Self::LogicalAnd => "and",
            Self::LogicalOr => "or",
            Self::BitwiseAnd => "&",
            Self::BitwiseXor => "^",
            Self::BitwiseOr => "|",
            Self::Shr => ">>",
            Self::Shl => "<<",
        };

        f.write_str(str)
    }
}

impl BinOp {
    pub fn from_punct(punct: Punctuation) -> Option<BinOp> {
        use BinOp as BOp;
        use Punctuation as Punct;

        Some(match punct {
            Punct::Equal => BOp::Assignment,
            Punct::Star => BOp::Mul,
            Punct::Slash => BOp::Div,
            Punct::Percent => BOp::Rem,
            Punct::Plus => BOp::Add,
            Punct::Minus => BOp::Sub,
            Punct::Lt => BOp::CompLT,
            Punct::Gt => BOp::CompGT,
            Punct::LtEqual => BOp::CompLE,
            Punct::GtEqual => BOp::CompGE,
            Punct::Equal2 => BOp::CompEq,
            Punct::BangEqual => BOp::CompNe,
            Punct::Ampsand => BOp::BitwiseAnd,
            Punct::Caret => BOp::BitwiseXor,
            Punct::Pipe => BOp::BitwiseOr,
            Punct::Lt2 => BOp::Shl,
            Punct::Gt2 => BOp::Shr,
            _ => return None,
        })
    }

    pub fn from_tt(tt: TokenType) -> Option<BinOp> {
        match tt {
            Punct(p) => Self::from_punct(p),
            Kw(Keyword::And) => Some(BinOp::LogicalAnd),
            Kw(Keyword::Or) => Some(BinOp::LogicalOr),
            _ => None,
        }
    }

    /// Is the binary operation rational? < <= > >= == !=
    pub fn is_relational(&self) -> bool {
        matches!(
            self,
            BinOp::CompLT
                | BinOp::CompLE
                | BinOp::CompGT
                | BinOp::CompGE
                | BinOp::CompEq
                | BinOp::CompNe
        )
    }

    pub fn is_logical(&self) -> bool {
        // TODO: implement logical operators like `"not" expr`, `expr "and"
        // expr`, `expr "or" expr`, `expr "xor" expr`
        matches!(self, Self::LogicalAnd | Self::LogicalOr)
    }
}

/// Parse binary expression, `expression op expression`
pub fn parse_binary_expr(parser: &mut Parser, lhs: Expression) -> Result<Expression, Diagnostic> {
    let (op, tok) = match parser.peek_tok() {
        // TODO: here we compute twice the binary op its a little dumb, find a solution to that problem.
        Some(Token { tt: op, .. }) if BinOp::from_tt(op.clone()).is_some() => {
            let op = op.clone();
            parser.pop();
            (BinOp::from_tt(op.clone()).unwrap(), op)
        }
        Some(tok) => {
            let t = tok.clone();
            // TEST: n/a
            return Err(
                ExpectedToken::new("binary operator", t.tt, Some("expression"), t.loc).into_diag(),
            );
        }
        None => return Err(parser.eof_diag()),
    };

    let Some(mut pr) = Precedence::from(tok.clone()) else {
        // we can't reach here because we already checked that our token is a
        // binary operator like those we want in this function
        unreachable!()
    };

    if pr.associativity() == Associativity::LeftToRight {
        pr = pr.next();
    }

    let rhs = parse!(@fn parser => parse_expr_precedence, pr, false);
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
    // left unary operator
    /// `- expression`
    Negation,
    /// `! expression`
    Not,
    // right unary operator
    /// `expression.*`
    Dereference,
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let str = match self {
            Self::Negation => "-",
            Self::Not => "!",
            Self::Dereference => ".*",
        };

        f.write_str(str)
    }
}

impl UnaryOp {
    /// get the unary operation for left side unary operation
    ///
    /// eg:
    /// `-a` `!a` `&a`
    pub fn left_from_token(tt: TokenType) -> Option<UnaryOp> {
        match tt {
            Punct(Punctuation::Minus) => Some(UnaryOp::Negation),
            Punct(Punctuation::Bang) => Some(UnaryOp::Not),
            _ => None,
        }
    }

    /// get the unary operation for right side unary operation
    ///
    /// eg:
    /// `a.*`
    pub fn right_from_token(tt: TokenType) -> Option<UnaryOp> {
        match tt {
            Punct(Punctuation::DotStar) => Some(UnaryOp::Dereference),
            _ => None,
        }
    }
}

/// Parse unary expression, `op expression`
pub fn parse_unary_left_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let (op, lo) = if let Some(Token { tt, loc }) = parser.peek_tok() {
        if let Some(op) = UnaryOp::left_from_token(tt.clone()) {
            let loc = loc.clone();
            parser.pop();
            (op, loc)
        } else {
            let t = parser.peek_tok().unwrap().clone();
            // TEST: n/a
            return Err(
                ExpectedToken::new("unary operator", t.tt, Some("expression"), t.loc).into_diag(),
            );
        }
    } else {
        return Err(parser.eof_diag());
    };

    let expr = parse!(box: @fn parser => parse_expr_precedence, Precedence::Unary, false);

    Ok(Expression {
        loc: Span::from_ends(lo, expr.loc.clone()),
        expr: Expr::Unary { op, expr },
    })
}

/// parses the call expression
pub fn parse_funcall_expr(
    parser: &mut Parser,
    called: Box<Expression>,
) -> Result<Expression, Diagnostic> {
    let lo = called.loc.clone();
    // TEST: n/a
    expect_token!(parser => [Punct(Punctuation::LParen), ()], Punctuation::LParen);

    let mut args = Vec::new();

    loop {
        if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
            break;
        }

        args.push(parse!(parser => Expression));

        // TEST: yes
        expect_token!(parser => [Punct(Punctuation::Comma), (); Punct(Punctuation::RParen), (), in break], [Punctuation::Comma, Punctuation::RParen]);
    }

    // TEST: n/a
    let ((), hi) = expect_token!(parser => [Punct(Punctuation::RParen), ()], Punctuation::RParen);

    Ok(Expression {
        expr: Expr::FunCall {
            callee: called,
            args,
        },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses the function definition / declaration expression
pub fn parse_funkw_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Fun), ()], Kw(Keyword::Fun));

    // TEST: no. 1
    expect_token!(parser => [Punct(Punctuation::LParen), ()], Punctuation::LParen);

    match (parser.peek_tt(), parser.nth_tt(1)) {
        (Some(Ident(_)), Some(Punct(Punctuation::Colon))) => {
            // function definition

            let mut args = Vec::new();

            loop {
                if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
                    break;
                }

                // TEST: n/a
                let (name, lo_arg) =
                    expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

                // TEST: n/a
                expect_token!(parser => [Punct(Punctuation::Colon), ()], Punct(Punctuation::Colon));

                let typexpr = parse!(@fn parser => parse_typexpr);

                args.push(Arg {
                    name,
                    name_loc: lo_arg.clone(),
                    typexpr: typexpr.clone(),
                    loc: Span::from_ends(lo_arg, typexpr.loc),
                });

                // TEST: no. 2
                expect_token!(parser => [Punct(Punctuation::Comma), (); Punct(Punctuation::RParen), (), in break], Punct(Punctuation::Comma));
            }
            // TEST: no. 3
            expect_token!(parser => [Punct(Punctuation::RParen), ()], Punct(Punctuation::RParen));

            let rettypexpr = if let Some(Punct(Punctuation::MinusGt)) = parser.peek_tt() {
                parser.pop();
                Some(parse!(box: @fn parser => parse_typexpr))
            } else {
                None
            };

            let body = parse!(parser => Block);
            let hi = body.loc.clone();

            Ok(Expression {
                expr: Expr::FunDefinition {
                    args,
                    rettypexpr,
                    body,
                },
                loc: Span::from_ends(lo, hi),
            })
        }
        (Some(Punct(Punctuation::RParen)), _) => {
            // ambiguous

            // TEST: n/a
            let ((), hi_paren) = expect_token!(parser => [Punct(Punctuation::RParen), ()], Punct(Punctuation::RParen));

            let rettypexpr = if let Some(Punct(Punctuation::MinusGt)) = parser.peek_tt() {
                parser.pop();
                Some(parse!(box: @fn parser => parse_typexpr))
            } else {
                None
            };

            if parser.is_stmt_end() {
                // function declaration

                let hi = rettypexpr
                    .as_ref()
                    .map(|typexpr| typexpr.loc.clone())
                    .unwrap_or(hi_paren);

                Ok(Expression {
                    expr: Expr::FunDeclaration {
                        args: Vec::new(),
                        rettypexpr,
                    },
                    loc: Span::from_ends(lo, hi),
                })
            } else {
                // function definition

                let body = parse!(parser => Block);
                let hi = body.loc.clone();

                Ok(Expression {
                    expr: Expr::FunDefinition {
                        args: Vec::new(),
                        rettypexpr,
                        body,
                    },
                    loc: Span::from_ends(lo, hi),
                })
            }
        }
        _ => {
            // function declaration

            let mut args = Vec::new();

            loop {
                if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
                    break;
                }

                let typexpr = parse!(@fn parser => parse_typexpr);

                args.push(typexpr);

                // TEST: no. 4
                expect_token!(parser => [Punct(Punctuation::Comma), (); Punct(Punctuation::RParen), (), in break], [Punct(Punctuation::Comma), Punct(Punctuation::RParen)]);
            }
            // TEST: n/a
            let ((), hi_paren) = expect_token!(parser => [Punct(Punctuation::RParen), ()], Punct(Punctuation::RParen));

            let rettypexpr = if let Some(Punct(Punctuation::MinusGt)) = parser.peek_tt() {
                parser.pop();
                Some(parse!(box: @fn parser => parse_typexpr))
            } else {
                None
            };

            let hi = rettypexpr
                .as_ref()
                .map(|typexpr| typexpr.loc.clone())
                .unwrap_or(hi_paren);

            Ok(Expression {
                expr: Expr::FunDeclaration { args, rettypexpr },
                loc: Span::from_ends(lo, hi),
            })
        }
    }
}

/// parses the if-else expression
pub fn parse_if_else_expr(parser: &mut Parser, only_block: bool) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Kw(Keyword::If), ()], Kw(Keyword::If));

    let cond = parse!(box: parser => Expression);

    if let Some(TokenType::Punct(Punctuation::LBrace)) = parser.peek_tt() {
        // if expr
        // "if" expression block [ "else" (if-expr | block-expr) ]
        let body = parse!(box: parser => Block);

        let mut hi = body.loc.clone();

        let else_br = if let Some(Kw(Keyword::Else)) = parser.peek_tt() {
            parser.pop();

            let else_branch = match parser.peek_tt() {
                Some(Kw(Keyword::If)) => {
                    let Expression {
                        expr: Expr::If(if_expr),
                        loc: _,
                    } = parse!(@fn parser => parse_if_else_expr, true)
                    else {
                        unreachable!();
                    };
                    hi = if_expr.loc.clone();

                    Else::IfExpr(if_expr)
                }
                Some(Punct(Punctuation::LBrace)) => {
                    // block
                    let block = parse!(parser => Block);

                    hi = block.loc.clone();

                    Else::Block(block)
                }
                Some(_) => {
                    let t = parser.peek_tok().unwrap();

                    // TEST: no. 2
                    return Err(ExpectedToken::new(
                        [Punct(Punctuation::LBrace), Kw(Keyword::If)],
                        t.tt.clone(),
                        Some("if expression"),
                        t.loc.clone(),
                    )
                    .into_diag());
                }
                None => return Err(parser.eof_diag()),
            };

            Some(Box::new(else_branch))
        } else {
            None
        };

        let loc = Span::from_ends(lo, hi);

        Ok(Expression {
            expr: Expr::If(IfExpression {
                cond,
                body,
                else_br,
                loc: loc.clone(),
            }),
            loc,
        })
    } else if !only_block {
        // if then else expr
        // "if" expression then expression "else" expression

        // TEST: n/a
        expect_token!(parser => [Kw(Keyword::Then), ()], Kw(Keyword::Then));
        let true_val = parse!(box: parser => Expression);
        // TEST: no. 1
        expect_token!(parser => [Kw(Keyword::Else), ()], Kw(Keyword::Else));
        let false_val = parse!(box: parser => Expression);

        let hi = false_val.loc.clone();

        Ok(Expression {
            expr: Expr::IfThenElse {
                cond,
                true_val,
                false_val,
            },
            loc: Span::from_ends(lo, hi),
        })
    } else {
        let t = parser.peek_tok().unwrap();

        // TEST: no. 3
        Err(ExpectedToken::new(
            [Punct(Punctuation::LBrace)],
            t.tt.clone(),
            Some("if expression"),
            t.loc.clone(),
        )
        .into_diag())
    }
}

/// parses block expression
pub fn parse_block_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    if let Some(Ident(id)) = parser.peek_tt() {
        let id = id.clone();

        let Some(Token { tt: _, loc: lo }) = parser.pop() else {
            opt_unreachable!()
        };

        let label = (id, lo.clone());

        // TEST: n/a
        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punct(Punctuation::Colon));

        let block = parse!(parser => Block);
        let hi = block.loc.clone();

        return Ok(Expression {
            expr: Expr::BlockWithLabel { label, block },
            loc: Span::from_ends(lo, hi),
        });
    }

    let block = parse!(parser => Block);
    let loc = block.loc.clone();

    Ok(Expression {
        expr: Expr::Block(block),
        loc,
    })
}

/// parses predicate loop expression
pub fn parse_predicate_loop_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let label = if let Some(Ident(id)) = parser.peek_tt() {
        let label = id.clone();
        let Some(Token { tt: _, loc }) = parser.pop() else {
            opt_unreachable!()
        };

        // TEST: n/a
        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punct(Punctuation::Colon));

        Some((label, loc))
    } else {
        None
    };

    // TEST: n/a
    let (_, lo_while) = expect_token!(parser => [Kw(Keyword::While), ()], Kw(Keyword::While));
    let lo = label.as_ref().map(|l| l.1.clone()).unwrap_or(lo_while);

    let cond = parse!(box: parser => Expression);
    let body = parse!(parser => Block);

    let hi = body.loc.clone();

    Ok(Expression {
        expr: Expr::PredicateLoop { label, cond, body },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses iterator loop expression
pub fn parse_iterator_loop_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let label = if let Some(Ident(id)) = parser.peek_tt() {
        let label = id.clone();
        let Some(Token { tt: _, loc }) = parser.pop() else {
            opt_unreachable!()
        };

        // TEST: n/a
        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punct(Punctuation::Colon));

        Some((label, loc))
    } else {
        None
    };

    // TEST: n/a
    let (_, lo_for) = expect_token!(parser => [Kw(Keyword::For), ()], Kw(Keyword::For));
    let lo = label.as_ref().map(|l| l.1.clone()).unwrap_or(lo_for);

    // TEST: no. 1
    let (variable, _) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    // TEST: no. 2
    expect_token!(parser => [Kw(Keyword::In), ()], Kw(Keyword::In));

    let iterator = parse!(box: parser => Expression);

    let body = parse!(parser => Block);

    let hi = body.loc.clone();

    let loc = Span::from_ends(lo, hi);

    Ok(Expression {
        expr: Expr::IteratorLoop {
            label,
            variable,
            iterator,
            body,
            loc: loc.clone(),
        },
        loc,
    })
}

/// parses infinite loop expression
pub fn parse_infinite_loop_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    let label = if let Some(Ident(id)) = parser.peek_tt() {
        let label = id.clone();
        let Some(Token { tt: _, loc }) = parser.pop() else {
            opt_unreachable!()
        };

        // TEST: n/a
        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punct(Punctuation::Colon));

        Some((label, loc))
    } else {
        None
    };

    // TEST: n/a
    let (_, lo_loop) = expect_token!(parser => [Kw(Keyword::Loop), ()], Kw(Keyword::Loop));
    let lo = label.as_ref().map(|l| l.1.clone()).unwrap_or(lo_loop);

    let block = parse!(parser => Block);

    let hi = block.loc.clone();

    Ok(Expression {
        expr: Expr::InfiniteLoop { label, body: block },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses return expression
pub fn parse_return_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Return), ()], Kw(Keyword::Return));
    let mut hi = lo.clone();

    let val = if parser.is_stmt_end() {
        None
    } else {
        let expr = parse!(box: parser => Expression);
        hi = expr.loc.clone();

        Some(expr)
    };

    Ok(Expression {
        expr: Expr::Return { expr: val },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses break expression
pub fn parse_break_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Break), ()], Kw(Keyword::Break));

    let mut hi = lo.clone();

    let label = if let Some(Punct(Punctuation::Colon)) = parser.peek_tt() {
        let Some(_) = parser.pop() else {
            // SAFETY: we already checked that the next token is here.
            opt_unreachable!()
        };

        // TEST: no. 1
        let (label, loc) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

        hi = loc;

        Some(label)
    } else {
        None
    };

    let expr = if parser.is_stmt_end() {
        None
    } else {
        let expr = parse!(box: parser => Expression);
        hi = expr.loc.clone();

        Some(expr)
    };

    Ok(Expression {
        expr: Expr::Break { label, expr },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses continue expression
pub fn parse_continue_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Kw(Keyword::Continue), ()], Kw(Keyword::Continue));
    let mut hi = lo.clone();

    let label = if let Some(Punct(Punctuation::Colon)) = parser.peek_tt() {
        let Some(_) = parser.pop() else {
            // SAFETY: we already checked that the next token is here.
            opt_unreachable!()
        };

        // TEST: no. 1
        let (label, loc) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));
        hi = loc;

        Some(label)
    } else {
        None
    };

    Ok(Expression {
        expr: Expr::Continue { label },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses null expression
pub fn parse_null_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, loc) = expect_token!(parser => [Kw(Keyword::Null), ()], Kw(Keyword::Null));

    Ok(Expression {
        expr: Expr::Null,
        loc,
    })
}

/// parses orb expression
pub fn parse_orb_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, loc) = expect_token!(parser => [Kw(Keyword::Orb), ()], Kw(Keyword::Orb));

    Ok(Expression {
        expr: Expr::Orb,
        loc,
    })
}

/// parses function pointer type
pub fn parse_funptr_type_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Punct(Punctuation::Star), ()], Punctuation::Star);

    // TEST: n/a
    expect_token!(parser => [Kw(Keyword::Fun), ()], Kw(Keyword::Fun));

    // TEST: no. 1
    expect_token!(parser => [Punct(Punctuation::LParen), ()], Punctuation::LParen);

    let mut args = Vec::new();

    loop {
        if let Some(Punct(Punctuation::RParen)) = parser.peek_tt() {
            break;
        }

        args.push(parse!(@fn parser => parse_typexpr));

        // TEST: no. 2
        expect_token!(parser => [Punct(Punctuation::Comma), (); Punct(Punctuation::RParen), (), in break], [Punctuation::Comma, Punctuation::RParen]);
    }

    // TEST: n/a
    let ((), hi_paren) =
        expect_token!(parser => [Punct(Punctuation::RParen), ()], Punctuation::RParen);

    let (hi, ret) = if let Some(Punct(Punctuation::MinusGt)) = parser.peek_tt() {
        parser.pop();

        let t = parse!(box: @fn parser => parse_typexpr);

        (t.loc.clone(), Some(t))
    } else {
        (hi_paren, None)
    };

    Ok(Expression {
        expr: Expr::FunPtrType { args, ret },
        loc: Span::from_ends(lo, hi),
    })
}

/// parses pointer type expression
pub fn parse_pointer_type_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Punct(Punctuation::Star), ()], Punctuation::Star);

    let mutable = if let Some(Kw(Keyword::Mut)) = parser.peek_tt() {
        parser.pop();
        true
    } else {
        false
    };

    let typexpr = parse!(box: @fn parser => parse_typexpr);
    let hi = typexpr.loc.clone();

    Ok(Expression {
        expr: Expr::PointerType { mutable, typexpr },
        loc: Span::from_ends(lo, hi),
    })
}

pub fn parse_unary_right_expr(
    parser: &mut Parser,
    lhs: Expression,
) -> Result<Expression, Diagnostic> {
    let lo = lhs.loc.clone();

    let (op, hi) = if let Some(Token { tt, loc }) = parser.peek_tok() {
        if let Some(op) = UnaryOp::right_from_token(tt.clone()) {
            let loc = loc.clone();
            parser.pop();
            (op, loc)
        } else {
            let t = parser.peek_tok().unwrap().clone();

            // TEST: n/a
            return Err(
                ExpectedToken::new("unary operator", t.tt, Some("expression"), t.loc).into_diag(),
            );
        }
    } else {
        return Err(parser.eof_diag());
    };

    Ok(Expression {
        expr: Expr::Unary {
            op,
            expr: Box::new(lhs),
        },
        loc: Span::from_ends(lo, hi),
    })
}

pub fn parse_borrow_expr(parser: &mut Parser) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    let (_, lo) = expect_token!(parser => [Punct(Punctuation::Ampsand), ()], Punctuation::Ampsand);

    let mutable = if let Some(Kw(Keyword::Mut)) = parser.peek_tt() {
        parser.pop();
        true
    } else {
        false
    };

    let val = parse!(box: parser => Expression);

    let hi = val.loc.clone();

    Ok(Expression {
        expr: Expr::Borrow { mutable, expr: val },
        loc: Span::from_ends(lo, hi),
    })
}

pub fn parse_member_access_expr(
    parser: &mut Parser,
    expr: Expression,
) -> Result<Expression, Diagnostic> {
    // TEST: n/a
    expect_token!(parser => [Punct(Punctuation::Dot), ()], Punctuation::Dot);

    // TEST: no. 1
    let (member, hi) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

    let loc = Span::from_ends(expr.loc.clone(), hi);

    Ok(Expression {
        expr: Expr::MemberAccess {
            expr: Box::new(expr),
            member,
        },
        loc,
    })
}
