//! Lexer of lun

use diags::{
    InvalidDigitInNumber, TooLargeIntegerLiteral, UnknownCharacterEscape, UnknownToken,
    UnterminatedStringLiteral,
};
use lun_diag::{Diagnostic, DiagnosticSink, StageResult};

use lun_utils::{
    Span, span,
    token::{Keyword, TokenTree, TokenType},
};

pub mod diags;

#[derive(Debug, Clone)]
pub struct Lexer {
    /// the list of characters, our source code but character by character
    chars: Vec<char>,
    /// the current position of the lexing head
    cur: usize,
    /// the position of the previous token's end
    prev: usize,
    /// sink of diags
    sink: DiagnosticSink,
}

impl Lexer {
    pub fn new(sink: DiagnosticSink, source_code: String) -> Lexer {
        Lexer {
            chars: source_code.chars().collect(),
            cur: 0,
            prev: 0,
            sink,
        }
    }

    /// Lex the whole source code and return a **finished** TokenTree.
    pub fn produce(&mut self) -> StageResult<TokenTree> {
        let mut tt = TokenTree::new();

        loop {
            self.prev = self.cur;
            let t = match self.make_token() {
                Some(Ok(t)) => t,
                Some(Err(diag)) => {
                    // irrecoverable error diagnostic
                    self.sink.push(diag);
                    break;
                }
                None => continue,
            };

            if tt.push(t, self.prev, self.cur) {
                break;
            }
        }

        if self.sink.failed() {
            return StageResult::Part(tt, self.sink.clone());
        }

        tt.finish();

        StageResult::Good(tt)
    }

    pub fn peek(&self) -> Option<char> {
        self.chars.get(self.cur).cloned()
    }

    pub fn pop(&mut self) -> Option<char> {
        let c = self.peek();
        self.cur += 1;
        c
    }

    pub fn loc(&self) -> Span {
        span(self.prev, self.cur)
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

    pub fn make_token(&mut self) -> Option<Result<TokenType, Diagnostic>> {
        // TODO: find a less ugly type than that shitty Option<Result<..>>
        // maybe skip the whitespaces until there is something else than a ws
        //
        // OR (and better) create a special `__NoneToken__`(or sth else) token
        // that has the same utility than the old `WsOrComment` error and be
        // used when there was a recoverable error.
        use lun_utils::token::{Punctuation::*, TokenType::*};

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
            Some(';') => Punct(SemiColon),
            Some('=') => {
                self.pop();
                match self.peek() {
                    Some('=') => {
                        self.pop();
                        return Some(Ok(Punct(Equal2)));
                    }
                    _ => return Some(Ok(Punct(Equal))),
                }
            }
            Some('!') => {
                self.pop();
                self.expect('=');
                return Some(Ok(Punct(BangEqual)));
            }
            Some('<') => {
                self.pop();
                match self.peek() {
                    Some('=') => {
                        self.pop();
                        return Some(Ok(Punct(LArrowEqual)));
                    }
                    _ => return Some(Ok(Punct(LArrow))),
                }
            }
            Some('>') => {
                self.pop();
                match self.peek() {
                    Some('=') => {
                        self.pop();
                        return Some(Ok(Punct(RArrowEqual)));
                    }
                    _ => return Some(Ok(Punct(RArrow))),
                }
            }
            Some('/') => {
                self.pop();
                match self.peek() {
                    Some('/') => {
                        // start of a line comment
                        self.pop();
                        self.lex_until('\n');
                        return None;
                    }
                    _ => return Some(Ok(Punct(Slash))),
                }
            }
            Some('"') => return Some(self.lex_string()),
            Some('a'..='z' | 'A'..='Z' | '_') => return Some(Ok(self.lex_identifier())),
            Some('0'..='9') => return Some(self.lex_number()),
            Some(w) if w.is_whitespace() => {
                self.cur += 1;
                return None;
            }
            Some(c) => {
                self.pop();
                self.sink.push(UnknownToken { c, loc: self.loc() });
                return None;
            }
            None => EOF,
        };

        self.pop();

        Some(Ok(t))
    }

    pub fn lex_identifier(&mut self) -> TokenType {
        let word = self.make_word();

        use TokenType::Kw;

        match word.as_str() {
            Keyword::BREAK => Kw(Keyword::Break),
            Keyword::CLASS => Kw(Keyword::Class),
            Keyword::CONTINUE => Kw(Keyword::Continue),
            Keyword::DO => Kw(Keyword::Do),
            Keyword::ELSE => Kw(Keyword::Else),
            Keyword::END => Kw(Keyword::End),
            Keyword::FALSE => Kw(Keyword::False),
            Keyword::FOR => Kw(Keyword::For),
            Keyword::FUN => Kw(Keyword::Fun),
            Keyword::IF => Kw(Keyword::If),
            Keyword::IMPL => Kw(Keyword::Impl),
            Keyword::IN => Kw(Keyword::In),
            Keyword::LOCAL => Kw(Keyword::Local),
            Keyword::NOT => Kw(Keyword::Not),
            Keyword::RETURN => Kw(Keyword::Return),
            Keyword::SELF => Kw(Keyword::Zelf),
            Keyword::THEN => Kw(Keyword::Then),
            Keyword::TRAIT => Kw(Keyword::Trait),
            Keyword::TRUE => Kw(Keyword::True),
            Keyword::WHILE => Kw(Keyword::While),
            _ => TokenType::Ident(word),
        }
    }

    /// Lexes the input while the content is alphanumeric with underscore(s) returns the content and if the
    /// string is numeric, in a tuple.
    pub fn make_word(&mut self) -> String {
        // TODO: maybe add support for a wider amount of characters in unicode.
        // https://www.unicode.org/reports/tr31/ look at that maybe
        let mut word = String::new();

        while let Some(c @ ('A'..='Z' | 'a'..='z' | '_' | '0'..='9')) = self.peek() {
            word.push(c);
            self.pop();
        }
        word
    }

    pub fn lex_number(&mut self) -> Result<TokenType, Diagnostic> {
        // TODO: add support for floats.
        // TODO: add support for radix like `0x...`, `0o...`, `0b...`
        let int = self.make_word();

        Ok(TokenType::IntLit(self.parse_u64(&int, 10)?))
    }

    pub fn lex_string(&mut self) -> Result<TokenType, Diagnostic> {
        let mut str = String::new();

        // pop the first "
        self.pop();

        loop {
            match self.peek() {
                Some('"') => {
                    self.pop();
                    break;
                }
                Some('\\') => {
                    self.pop();

                    let es = match self.pop() {
                        Some(es) => es,
                        None => continue,
                    };

                    if es == '"' {
                        str.push(es);
                        continue;
                    }

                    // here we change the offset of the previous token to make
                    // the diagnostic point to the correct digit in the \xXX if
                    // there was an error, it's kinda a hack but you know lmao
                    let old_prev = self.prev;
                    self.prev = self.cur;

                    match self.make_escape_sequence(es) {
                        Ok(c) => {
                            str.push(c);
                        }
                        Err(d) => {
                            self.sink.push(d);
                        }
                    }

                    self.prev = old_prev;
                }
                Some(c) => {
                    str.push(c);
                    self.pop();
                }
                _ => {
                    self.sink
                        .push(UnterminatedStringLiteral { loc: self.loc() });
                    break;
                }
            }
        }

        Ok(TokenType::StringLit(str))
    }

    pub fn make_escape_sequence(&mut self, es: char) -> Result<char, Diagnostic> {
        Ok(match es {
            '0' => '\0',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '\\' => '\\',
            'x' => self.make_hex_es()?,
            'u' | 'U' => {
                // TODO: implement the lexing of unicode es
                // in the for of \U+FFFF ig
                self.sink.push(UnknownCharacterEscape {
                    es,
                    loc: span(self.cur - 1, self.cur),
                    is_unicode: true,
                });
                '\0'
            }
            _ => {
                self.sink.push(UnknownCharacterEscape {
                    es,
                    loc: span(self.cur - 1, self.cur),
                    is_unicode: false,
                });

                '\0'
            }
        })
    }

    pub fn make_hex_es(&mut self) -> Result<char, Diagnostic> {
        let mut str = String::with_capacity(2);
        for _ in 0..2 {
            str.push(match self.pop() {
                Some(c) => c,
                None => {
                    self.sink
                        .push(UnterminatedStringLiteral { loc: self.loc() });
                    // it's the poisoned value.
                    str.push_str("00");
                    break;
                }
            })
        }

        Ok(self.parse_u64(&str, 16)? as u8 as char)
    }

    /// Parse a number passed as input into a u64 using the radix.
    ///
    /// # Note
    ///
    /// The radix is 'inclusive' if you want to parse a number as a decimal, then
    /// `radix = 10` and if you want to parse a number as hexadecimal `radix = 16`
    /// etc etc...
    pub fn parse_u64(&mut self, input: &str, radix: u8) -> Result<u64, Diagnostic> {
        if !(2..=36).contains(&radix) {
            panic!("invalid radix provided, {radix}, it must be between 2 and 36 included.")
        }

        let mut result: u64 = 0;
        // did the literal is too big too fit in a u64
        let mut overflowed = false;
        // don't emit the integer too large if there was an overflow, deal one
        // thing at a time
        let mut had_invalid_digit = false;

        for (i, c) in input.char_indices().peekable() {
            let digit = match c {
                '0'..='9' => (c as u8 - b'0') as u32,
                'a'..='z' => (c as u8 - b'a' + 10) as u32,
                'A'..='Z' => (c as u8 - b'A' + 10) as u32,
                '_' => continue,
                _ => {
                    had_invalid_digit = true;
                    let pos = self.prev + i;
                    self.sink.push(InvalidDigitInNumber {
                        c,
                        loc_c: span(pos, pos + 1),
                        loc_i: self.loc(),
                    });

                    // the poisoned value
                    0
                }
            };

            if digit >= radix.into() {
                had_invalid_digit = true;
                let pos = self.prev + i;
                self.sink.push(InvalidDigitInNumber {
                    c,
                    loc_c: span(pos, pos + 1),
                    loc_i: self.loc(),
                });
            }

            let prev_result = result;
            result = match result
                .checked_mul(radix as u64)
                .and_then(|r| r.checked_add(digit as u64))
            {
                Some(val) => val,
                None => {
                    overflowed = true;
                    prev_result
                }
            };
        }

        if overflowed && !had_invalid_digit {
            self.sink.push(TooLargeIntegerLiteral { loc: self.loc() })
        }

        Ok(result)
    }
}
