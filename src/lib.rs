use std::fmt::Display;

pub mod lexer;
pub mod token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[inline(always)]
pub fn span(start: impl Into<usize>, end: impl Into<usize>) -> Span {
    Span {
        start: start.into(),
        end: end.into(),
    }
}

impl Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}
