//! Lexer of lun

use diags::{
    InvalidDigitInNumber, TooLargeIntegerLiteral, UnknownCharacterEscape, UnknownToken,
    UnterminatedStringLiteral,
};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, ReachedEOF, feature_todo};

use lunc_utils::{
    Span, span,
    token::{Keyword, TokenStream, TokenType},
};

pub mod diags;
mod head;

pub use head::*;

#[derive(Debug, Clone)]
pub struct Lexer {
    /// the list of characters, our source code but character by character
    chars: Vec<char>,
    /// lexing head
    head: LexHead,
    /// sink of diags
    sink: DiagnosticSink,
    /// file id of the file we are lexing
    fid: FileId,
}

impl Lexer {
    pub fn new(sink: DiagnosticSink, source_code: String, fid: FileId) -> Lexer {
        Lexer {
            chars: source_code.chars().collect(),
            head: LexHead::new(),
            sink,
            fid,
        }
    }

    /// Lex the whole source code and return a **finished** token stream.
    pub fn produce(&mut self) -> Option<TokenStream> {
        let mut tt = TokenStream::new();

        loop {
            self.head.reset();
            let t = match self.make_token() {
                Ok(TokenType::__NotAToken__) => continue,
                Ok(t) => t,
                Err(diag) => {
                    // irrecoverable error diagnostic
                    self.sink.push(diag);
                    break;
                }
            };

            if tt.push(t, self.head.bytes_pos(), self.fid) {
                break;
            }
        }

        tt.finish();

        if self.sink.failed() {
            return None;
        }

        Some(tt)
    }

    /// return the char that is n-chars offseted
    pub fn peek_nth(&self, offset: isize) -> Option<char> {
        self.chars
            .get((self.head.cur_chars() as isize + offset) as usize)
            .cloned()
    }

    /// return the character a the current position
    pub fn peek(&self) -> Option<char> {
        self.chars.get(self.head.cur_chars()).cloned()
    }

    pub fn pop(&mut self) -> Option<char> {
        let c = self.peek();
        self.head.increment(c.unwrap_or_default());
        c
    }

    pub fn loc(&self) -> Span {
        let (lo, hi) = self.head.bytes_pos();
        span(lo, hi, self.fid)
    }

    #[track_caller]
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

    pub fn make_token(&mut self) -> Result<TokenType, Diagnostic> {
        use lunc_utils::token::{Punctuation::*, TokenType::*};

        let t = match self.peek() {
            Some('(') => Punct(LParen),
            Some(')') => Punct(RParen),
            Some('[') => Punct(LBracket),
            Some(']') => Punct(RBracket),
            Some('{') => Punct(LBrace),
            Some('}') => Punct(RBrace),
            Some('+') => Punct(Plus),
            Some('-') => {
                self.pop();
                match self.peek() {
                    Some('>') => {
                        self.pop();
                        return Ok(Punct(MinusGt));
                    }
                    _ => return Ok(Punct(Minus)),
                }
            }
            Some('*') => Punct(Star),
            Some(':') => Punct(Colon),
            Some(',') => Punct(Comma),
            Some(';') => Punct(Semicolon),
            Some('^') => Punct(Carret),
            Some('&') => Punct(Ampsand),
            Some('|') => Punct(Pipe),
            Some('%') => Punct(Percent),
            Some('=') => {
                self.pop();
                match self.peek() {
                    Some('=') => {
                        self.pop();
                        return Ok(Punct(Equal2));
                    }
                    _ => return Ok(Punct(Equal)),
                }
            }
            Some('!') => {
                self.pop();

                return match self.peek() {
                    Some('=') => {
                        self.pop();
                        Ok(Punct(BangEqual))
                    }
                    _ => Ok(Punct(Bang)),
                };
            }
            Some('<') => {
                self.pop();
                match self.peek() {
                    Some('=') => {
                        self.pop();
                        return Ok(Punct(LtEqual));
                    }
                    Some('<') => {
                        self.pop();
                        return Ok(Punct(Lt2));
                    }
                    _ => return Ok(Punct(Lt)),
                }
            }
            Some('>') => {
                self.pop();
                match self.peek() {
                    Some('=') => {
                        self.pop();
                        return Ok(Punct(GtEqual));
                    }
                    Some('>') => {
                        self.pop();
                        return Ok(Punct(Gt2));
                    }
                    _ => return Ok(Punct(Gt)),
                }
            }
            Some('/') => {
                self.pop();
                match self.peek() {
                    Some('/') => {
                        // start of a line comment
                        self.pop();
                        self.lex_until('\n');
                        return Ok(TokenType::__NotAToken__);
                    }
                    Some('*') => {
                        // start of multiline comment
                        self.pop();

                        loop {
                            match (self.peek(), self.peek_nth(1)) {
                                (Some('*'), Some('/')) => break,
                                (Some(_), _) => {
                                    self.pop();
                                }
                                (None, _) => break,
                            }
                        }

                        self.pop(); // pop *
                        self.pop(); // pop /

                        return Ok(TokenType::__NotAToken__);
                    }
                    _ => return Ok(Punct(Slash)),
                }
            }
            Some('.') => {
                self.pop();
                match self.peek() {
                    Some('*') => {
                        self.pop();
                        return Ok(Punct(DotStar));
                    }
                    _ => return Ok(Punct(Dot)),
                }
            }
            Some('\'') => return self.lex_char(),
            Some('"') => return self.lex_string(),
            Some('a'..='z' | 'A'..='Z' | '_') => return Ok(self.lex_identifier()),
            Some('0'..='9') => return self.lex_number(),
            Some(w) if w.is_whitespace() => {
                self.pop();
                return Ok(TokenType::__NotAToken__);
            }
            Some(c) => {
                self.pop();
                self.sink.push(UnknownToken { c, loc: self.loc() });
                return Ok(TokenType::__NotAToken__);
            }
            None => EOF,
        };

        self.pop();

        Ok(t)
    }

    pub fn lex_identifier(&mut self) -> TokenType {
        let word = self.make_word();

        use TokenType::Kw;

        match word.as_str() {
            Keyword::AND => Kw(Keyword::And),
            Keyword::BREAK => Kw(Keyword::Break),
            Keyword::COMPTIME => Kw(Keyword::Comptime),
            Keyword::CONTINUE => Kw(Keyword::Continue),
            Keyword::ELSE => Kw(Keyword::Else),
            Keyword::FALSE => Kw(Keyword::False),
            Keyword::FOR => Kw(Keyword::For),
            Keyword::FUN => Kw(Keyword::Fun),
            Keyword::IF => Kw(Keyword::If),
            Keyword::IMPL => Kw(Keyword::Impl),
            Keyword::IN => Kw(Keyword::In),
            Keyword::LET => Kw(Keyword::Let),
            Keyword::MUT => Kw(Keyword::Mut),
            Keyword::NULL => Kw(Keyword::Null),
            Keyword::OR => Kw(Keyword::Or),
            Keyword::PUB => Kw(Keyword::Pub),
            Keyword::RETURN => Kw(Keyword::Return),
            Keyword::SELF => Kw(Keyword::Zelf),
            Keyword::THEN => Kw(Keyword::Then),
            Keyword::TRAIT => Kw(Keyword::Trait),
            Keyword::TRUE => Kw(Keyword::True),
            Keyword::WHILE => Kw(Keyword::While),
            _ => TokenType::Ident(word),
        }
    }

    /// Lexes the input while the content is alphanumeric with underscore(s)
    /// returns the content and if the string is numeric, in a tuple.
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

    /// Lexes the input while the content is decimal digits or underscore,
    /// returns the content.
    pub fn make_decimal(&mut self) -> String {
        // TODO: maybe add support for a wider amount of characters in unicode.
        // https://www.unicode.org/reports/tr31/ look at that maybe
        let mut decimal = String::new();

        while let Some(c @ ('_' | '0'..='9')) = self.peek() {
            decimal.push(c);
            self.pop();
        }

        decimal
    }

    pub fn lex_number(&mut self) -> Result<TokenType, Diagnostic> {
        // Integer literal grammar:
        //
        // int_lit = decimal_lit | binary_lit | octal_lit | hexadecimal_lit ;
        // decimal_lit = "0" | decimal_digits ;
        // binary_lit = ("0b" | "0B") binary_digits ;
        // octal_lit = ("0o" | "0O") octal_digits ;
        // hex_lit = ("0x" | "0X") hex_digits ;
        // decimal_digits = { ["_"] decimal_digit } ;
        // binary_digits = { ["_"] binary_digit } ;
        // octal_digits = { ["_"] octal_digit } ;
        // hex_digits = { ["_"] hex_digit } ;
        let radix = match self.peek_nth(1) {
            Some('B' | 'b') if self.peek() == Some('0') => {
                self.pop(); // 0
                self.pop(); // B / b
                2
            }
            Some('O' | 'o') if self.peek() == Some('0') => {
                self.pop(); // 0
                self.pop(); // O / o
                8
            }
            Some('X' | 'x') if self.peek() == Some('0') => {
                // self.pop(); // 0
                // self.pop(); // X / x
                // 16
                // hexadecimal floating point number grammar:
                //
                // hex_float_lit = ("0x" | "0X") hex_mantissa hex_exponent ;
                // hex_mantissa = ["_"] hex_digits "." [hex_digits]
                //   | ["_"] hex_digits
                //   | "." hex_digits ;
                // hex_exponent = ("p" | "P") ["+" | "-"] decimal_digits ;

                todo!("HEXADECIMAL NUMBER AMBIGUITY");
            }
            _ => 10,
        };
        let int = self.make_word();

        let int_part = self.parse_u128(&int, radix)?;

        match self.peek() {
            Some('.') if radix == 10 => {
                // Decimal floating point number grammar:
                //
                // float_lit = decimal_float_lit | hex_float_lit ;
                // decimal_float_lit = decimal_digits "." [decimal_digits] [ decimal_exponent ]
                //   | decimal_digits decimal_exponent
                //   | "." decimal_digits [decimal_exponent] ;
                // decimal_exponent = ("e" | "E") ["+" | "-"] decimal_digits ;
                self.pop();

                let (frac_part, frac_divisor) = match self.peek() {
                    Some('0'..='9') => {
                        let frac_str = self.make_decimal();

                        match self.parse_u128_advanced(&frac_str, 10) {
                            Ok((f, n)) => (f, n as i32),
                            Err(d) => {
                                // NOTE: we are not using ? to propagate the diag, we just use
                                // a poisoned value
                                self.sink.push(d);
                                (0, 0)
                            }
                        }
                    }
                    _ => (0, 0),
                };

                let exp_value = match self.peek() {
                    Some('e' | 'E') => {
                        self.pop();
                        let sign = match self.peek() {
                            Some('-') => {
                                self.pop();
                                -1i32
                            }
                            Some('+') => {
                                self.pop();
                                1
                            }
                            Some('_' | '0'..='9') => 1,
                            Some(c) => {
                                self.sink.push(InvalidDigitInNumber {
                                    c,
                                    loc_c: {
                                        let (_, cur) = self.head.bytes_pos();
                                        span(cur, cur + 1, self.fid)
                                    },
                                    loc_i: self.loc(),
                                });
                                1
                            }
                            _ => {
                                self.sink.push(ReachedEOF { loc: self.loc() });
                                1
                            }
                        };

                        let exp_str = self.make_decimal();

                        let exp = match self.parse_u128(&exp_str, 10) {
                            Ok(e) => e as i32,
                            Err(d) => {
                                self.sink.push(d);
                                0
                            }
                        };

                        sign * exp
                    }
                    _ => 0,
                };

                let int_f64 = int_part as f64;
                let frac_f64 = frac_part as f64 * 10f64.powi(-frac_divisor);

                let base = int_f64 + frac_f64;

                let float = base * 10.0f64.powi(exp_value);

                Ok(TokenType::FloatLit(float))
            }
            Some('.') if radix == 16 => {
                todo!()
            }
            _ => Ok(TokenType::IntLit(int_part)),
        }
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

                    match self.make_escape_sequence(es) {
                        Ok(c) => {
                            str.push(c);
                        }
                        Err(d) => {
                            self.sink.push(d);
                        }
                    }
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

    pub fn lex_char(&mut self) -> Result<TokenType, Diagnostic> {
        self.expect('\'');

        let c = match self.peek() {
            Some('\\') => {
                self.pop();

                let es = match self.pop() {
                    Some(es) => es,
                    None => {
                        self.sink.push(ReachedEOF { loc: self.loc() });
                        char::default()
                    }
                };

                if es == '\'' {
                    es
                } else {
                    match self.make_escape_sequence(es) {
                        Ok(es) => es,
                        Err(d) => {
                            self.sink.push(d);
                            char::default()
                        }
                    }
                }
            }
            Some(c) => {
                self.pop();
                c
            }
            None => {
                self.sink.push(ReachedEOF { loc: self.loc() });
                char::default()
            }
        };

        self.expect('\'');

        Ok(TokenType::CharLit(c))
    }

    /// makes an escape sequence return a tuple of the character that corresponds
    /// to the escape and the increments to make to the head
    pub fn make_escape_sequence(&mut self, es: char) -> Result<char, Diagnostic> {
        #[inline(always)]
        fn char(i: u8) -> char {
            i as char
        }

        let es = match es {
            '0' => char(0x00),
            'n' => char(0x0A),
            'r' => char(0x0D),
            'f' => char(0x0C),
            't' => char(0x09),
            'v' => char(0x0B),
            'a' => char(0x07),
            'b' => char(0x08),
            'e' => char(0x1B),
            '\\' => char(0x5C), // character \
            'x' => self.make_hex_es()?,
            'u' | 'U' => {
                // TODO: implement the lexing of unicode es
                // in the for of \U+FFFF ig
                self.sink.push(feature_todo! {
                    feature: "unicode escape sequence",
                    label: "unicode escape isn't yet implemented.",
                    loc: self.loc(),
                });
                char::default()
            }
            _ => {
                self.sink.push(UnknownCharacterEscape {
                    es,
                    loc: self.loc(),
                });
                char::default()
            }
        };

        Ok(es)
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

        Ok(self.parse_u128(&str, 16)? as u8 as char)
    }

    /// Parse a number passed as input into a u128 using the radix.
    ///
    /// # Note
    ///
    /// The radix is 'inclusive' if you want to parse a number as a decimal, then
    /// `radix = 10` and if you want to parse a number as hexadecimal `radix = 16`
    /// etc etc...
    pub fn parse_u128(&mut self, input: &str, radix: u8) -> Result<u128, Diagnostic> {
        self.parse_u128_advanced(input, radix).map(|(int, _)| int)
    }

    /// returns a tuple of the parsed integer and how many digits has been parsed, leading zero count.
    pub fn parse_u128_advanced(
        &mut self,
        input: &str,
        radix: u8,
    ) -> Result<(u128, u32), Diagnostic> {
        if !(2..=36).contains(&radix) {
            panic!("invalid radix provided, {radix}, it must be between 2 and 36 included.")
        }

        let mut result: u128 = 0;
        // did the literal is too big too fit in a u128
        let mut overflowed = false;
        // don't emit the integer too large if there was an overflow, deal one
        // thing at a time
        let mut had_invalid_digit = false;

        // count of how many digits of the radix we parsed
        let mut digit_count = 0;

        for (i, c) in input.char_indices().peekable() {
            let digit = match c {
                '0'..='9' => (c as u8 - b'0') as u32,
                'a'..='z' => (c as u8 - b'a' + 10) as u32,
                'A'..='Z' => (c as u8 - b'A' + 10) as u32,
                '_' => continue,
                _ => {
                    had_invalid_digit = true;
                    let pos = self.head.prev_chars() + i;
                    self.sink.push(InvalidDigitInNumber {
                        c,
                        loc_c: span(pos, pos + 1, self.fid),
                        loc_i: self.loc(),
                    });

                    // the poisoned value
                    0
                }
            };

            if digit >= radix.into() {
                had_invalid_digit = true;
                let pos = self.head.prev_chars() + i;
                self.sink.push(InvalidDigitInNumber {
                    c,
                    loc_c: span(pos, pos + 1, self.fid),
                    loc_i: self.loc(),
                });
            } else {
                digit_count += 1
            }

            let prev_result = result;
            result = match result
                .checked_mul(radix as u128)
                .and_then(|r| r.checked_add(digit as u128))
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

        Ok((result, digit_count))
    }
}
