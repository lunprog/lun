//! Lexer of l2

use thiserror::Error;

use crate::{
    Span, span,
    token::{Keyword, TokenTree, TokenType},
};

// TODO: handle errors with `miette` and be able to report multiple errors at
// each stage of the compilation
#[derive(Debug, Clone, Error)]
pub enum LexingError {
    /// used to communicate between make_token and lex, it's not an actual error,
    /// there is just a comment or a whitespace where we tried to lex so there
    /// is no token to produce
    #[error("this is actually not an error and shouldn't be displayed as one.")]
    WsOrComment,
    #[error("{loc}: unknown start of token {c:?} ")]
    UnknownToken { c: char, loc: Span },
    #[error(transparent)]
    IntParseError(#[from] ParseUIntError),
    #[error("{0}: unterminated string literal")]
    UnterminatedStringLiteral(Span),
    #[error("{loc}: unknown escape sequence {es:?} ")]
    UnknownEscapeSequence { es: char, loc: Span },
}

#[derive(Debug, Clone)]
pub struct Lexer {
    /// the list of characters, our source code but character by character
    chars: Vec<char>,
    /// the current position of the lexing head
    cur: usize,
    /// the position of the previous token's end
    prev: usize,
}

impl Lexer {
    pub fn new(source_code: String) -> Lexer {
        Lexer {
            chars: source_code.chars().collect(),
            cur: 0,
            prev: 0,
        }
    }

    pub fn lex(&mut self) -> Result<TokenTree, LexingError> {
        let mut tt = TokenTree::new();

        loop {
            self.prev = self.cur;
            let t = match self.make_token() {
                Ok(t) => t,
                Err(LexingError::WsOrComment) => continue,
                Err(e) => Err(e)?,
            };

            if tt.push(t, self.prev, self.cur) {
                break;
            }
        }

        Ok(tt)
    }

    pub fn peek(&self) -> Option<char> {
        self.chars.get(self.cur).cloned()
    }

    pub fn pop(&mut self) -> Option<char> {
        let c = self.peek();
        self.cur += 1;
        c
    }

    pub fn expect(&mut self, expected: char) {
        let popped = self.pop().unwrap();
        if popped != expected {
            panic!("during lexing expected a character to be {expected:?} but found {popped:?}")
        }
    }

    pub fn lex_until(&mut self, stopper: char) -> String {
        // TODO: instead of reconstructing the String character by character we
        // could find where the closest character that is a stopper is and
        // slice the source code, and clone the string
        //
        // same for make_word and make_int
        let mut content = String::new();

        loop {
            match self.peek() {
                Some(c) if c == stopper => break content,
                Some(c) => {
                    content.push(c);
                    self.pop();
                }
                None => break content,
            }
        }
    }

    pub fn make_token(&mut self) -> Result<TokenType, LexingError> {
        use crate::token::{Punctuation::*, TokenType::*};

        let t = match self.peek() {
            Some('(') => Punct(LParen),
            Some(')') => Punct(RParen),
            Some('[') => Punct(LBracket),
            Some(']') => Punct(RBracket),
            Some('{') => Punct(LBrace),
            Some('}') => Punct(RBrace),
            Some('+') => Punct(Plus),
            Some('-') => Punct(Minus),
            Some('*') => Punct(Star),
            Some(':') => Punct(Colon),
            Some(',') => Punct(Comma),
            Some('/') => {
                self.pop();
                match self.peek() {
                    Some('/') => {
                        // start of a line comment
                        self.pop();
                        self.lex_until('\n');
                        return Err(LexingError::WsOrComment);
                    }
                    _ => return Ok(Punct(Slash)),
                }
            }
            Some('"') => return self.lex_string(),
            Some('a'..='z' | 'A'..='Z' | '_') => return Ok(self.lex_identifier()),
            Some('0'..='9') => return self.lex_number(),
            Some(w) if w.is_whitespace() => {
                self.cur += 1;
                return Err(LexingError::WsOrComment);
            }
            Some(c) => {
                self.pop();
                return Err(LexingError::UnknownToken {
                    c,
                    loc: span(self.prev, self.cur),
                });
            }
            None => EOF,
        };

        self.pop();

        Ok(t)
    }

    pub fn lex_identifier(&mut self) -> TokenType {
        let word = self.make_word();

        use TokenType::KW;

        match word.as_str() {
            Keyword::BREAK => KW(Keyword::Break),
            Keyword::CLASS => KW(Keyword::Class),
            Keyword::CONTINUE => KW(Keyword::Continue),
            Keyword::DO => KW(Keyword::Do),
            Keyword::END => KW(Keyword::End),
            Keyword::FALSE => KW(Keyword::False),
            Keyword::FOR => KW(Keyword::For),
            Keyword::FUN => KW(Keyword::Fun),
            Keyword::IMPL => KW(Keyword::Impl),
            Keyword::LOCAL => KW(Keyword::Local),
            Keyword::RETURN => KW(Keyword::Return),
            Keyword::SELF => KW(Keyword::Zelf),
            Keyword::THEN => KW(Keyword::Then),
            Keyword::TRAIT => KW(Keyword::Trait),
            Keyword::TRUE => KW(Keyword::True),
            Keyword::WHILE => KW(Keyword::While),
            _ => TokenType::Ident(word),
        }
    }

    /// Lexes the input while the content is alphanumeric with underscore(s) returns the content and if the
    /// string is numeric, in a tuple.
    pub fn make_word(&mut self) -> String {
        let mut word = String::new();

        loop {
            match self.peek() {
                Some(c @ ('A'..='Z' | 'a'..='z' | '_' | '0'..='9')) => {
                    word.push(c);
                }
                _ => break,
            }
            self.pop();
        }
        word
    }

    pub fn make_int(&mut self) -> String {
        let mut int = String::new();

        loop {
            match self.peek() {
                Some(c @ ('_' | '0'..='9')) => {
                    int.push(c);
                }
                _ => break,
            }
            self.pop();
        }

        int
    }

    pub fn lex_number(&mut self) -> Result<TokenType, LexingError> {
        // TODO: add support for floats.
        // TODO: add support for radix like `0x...`, `0o...`, `0b...`
        let int = self.make_int();

        Ok(TokenType::Int(parse_u64(&int, 10)?))
    }

    pub fn lex_string(&mut self) -> Result<TokenType, LexingError> {
        let mut str = String::new();

        // pop the first "
        self.pop();

        loop {
            match self.peek() {
                Some('"') => {
                    self.expect('"');
                    break;
                }
                Some('\\') => {
                    self.expect('\\');

                    let es = match self.pop() {
                        Some(es) => es,
                        None => continue,
                    };

                    if es == '"' {
                        str.push(es);
                        continue;
                    }

                    str.push(self.make_escape_sequence(es)?);
                }
                Some(c) => {
                    str.push(c);
                    self.pop();
                }
                _ => {
                    return Err(LexingError::UnterminatedStringLiteral(span(
                        self.prev, self.cur,
                    )));
                }
            }
        }

        Ok(TokenType::String(str))
    }

    pub fn make_escape_sequence(&mut self, es: char) -> Result<char, LexingError> {
        Ok(match es {
            '0' => '\0',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            'x' => self.make_hex_es()?,
            'u' => {
                // TODO: implement the lexing of unicode es
                // in the for of \U+FFFF ig
                todo!("support unicode escape sequences")
            }
            _ => {
                return Err(LexingError::UnknownEscapeSequence {
                    es,
                    loc: span(self.prev, self.cur),
                });
            }
        })
    }

    pub fn make_hex_es(&mut self) -> Result<char, LexingError> {
        let mut str = String::with_capacity(2);
        for _ in 0..2 {
            str.push(match self.pop() {
                Some(c) => c,
                None => {
                    return Err(LexingError::UnterminatedStringLiteral(span(
                        self.prev, self.cur,
                    )));
                }
            })
        }

        Ok(parse_u64(&str, 16)? as u8 as char)
    }
}

#[derive(Debug, Clone, PartialEq, Error)]
pub enum ParseUIntError {
    #[error("radix must be between 2 and 36 inclusive")]
    InvalidRadix,
    #[error("invalid character in integer")]
    InvalidCharacter(Span),
    #[error("digit in number is greater than the radix")]
    DigitOutOfRange(Span),
    #[error("too big integer literal too fit in 64 bits")]
    IntegerOverflow,
}

/// Parse a number passed as input into a u64 using the radix.
///
/// # Note
///
/// The radix is 'inclusive' if you want to parse a number as a decimal, then
/// `radix = 10` and if you want to parse a number as hexadecimal `radix = 16`
/// etc etc...
pub fn parse_u64(input: &str, radix: u8) -> Result<u64, ParseUIntError> {
    if !(2..=36).contains(&radix) {
        return Err(ParseUIntError::InvalidRadix);
    }

    let mut result: u64 = 0;

    for (i, c) in input.char_indices().peekable() {
        let digit = match c {
            '0'..='9' => (c as u8 - b'0') as u32,
            'a'..='z' => (c as u8 - b'a' + 10) as u32,
            'A'..='Z' => (c as u8 - b'A' + 10) as u32,
            '_' => continue,
            _ => {
                return Err(ParseUIntError::InvalidCharacter(span(i, i + 1)));
            }
        };

        if digit >= radix.into() {
            return Err(ParseUIntError::DigitOutOfRange(span(i, i + 1)));
        }

        result = match result
            .checked_mul(radix as u64)
            .and_then(|r| r.checked_add(digit as u64))
        {
            Some(val) => val,
            None => return Err(ParseUIntError::IntegerOverflow),
        };
    }

    Ok(result)
}
