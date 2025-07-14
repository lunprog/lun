//! Parsing of lun's definitions.

use crate::expr::parse_type_expression;

use super::*;

/// Visibility
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum Vis {
    #[default]
    Private,
    Public,
}

/// Lun program.
#[derive(Debug, Clone)]
pub struct Program {
    pub defs: Vec<Item>,
}

impl AstNode for Program {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let mut defs = Vec::new();

        loop {
            if let None | Some(TokenType::EOF) = parser.peek_tt() {
                break;
            }

            defs.push(parse!(parser => Item));
        }

        Ok(Program { defs })
    }
}

#[derive(Debug, Clone)]
pub enum Item {
    /// Global constant.
    ///
    /// ident ":" expression? ":" expr
    GlobalConst {
        name: String,
        name_loc: Span,
        typ: Option<Expression>,
        value: Expression,
        loc: Span,
    },
}

impl AstNode for Item {
    fn parse(parser: &mut Parser) -> Result<Self, Diagnostic> {
        let (name, lo) = expect_token!(parser => [Ident(id), id.clone()], Ident(String::new()));

        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punctuation::Colon);

        let typ = if let Some(Punct(Punctuation::Colon)) = parser.peek_tt() {
            None
        } else {
            Some(parse!(@fn parser => parse_type_expression))
        };

        expect_token!(parser => [Punct(Punctuation::Colon), ()], Punctuation::Colon);

        let value = parse!(parser => Expression);

        let hi = value.loc.clone();

        Ok(Item::GlobalConst {
            name,
            name_loc: lo.clone(),
            typ,
            value,
            loc: Span::from_ends(lo, hi),
        })
    }
}
