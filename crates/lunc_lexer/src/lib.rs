//! Lexer of lun
#![doc(
    html_logo_url = "https://raw.githubusercontent.com/lunprog/lun/main/logo/logo_no_bg_black.png"
)]

use diags::{
    EmptyCharLiteral, ExpectedExponentPart, InvalidDigitInNumber, InvalidUnicodeEscape,
    InvalidUnicodeNote, NoDigitsInANonDecimal, NotEnoughHexDigits, TooLargeIntegerLiteral,
    TooManyCodepointsInCharLiteral, UnknownCharacterEscape, UnknownToken,
    UnterminatedStringLiteral,
};
use lunc_diag::{Diagnostic, DiagnosticSink, FileId, ReachedEOF};

use lunc_utils::{
    Span, span,
    token::{Keyword, TokenStream, TokenType},
};

pub mod diags;
mod head;

pub use head::*;

/// Lexer, takes a source code of Lun and turns it into a token stream.
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
    // TODO: we don't need to retrieve the source code from argument, it already
    // is in the sink
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
            let t = match self.lex_token() {
                Ok(TokenType::__NotAToken__) => continue,
                Ok(t) => t,
                Err(diag) => {
                    // irrecoverable error diagnostic
                    self.sink.emit(diag);
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

    /// return the char that is n-chars offsetted
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

    pub fn loc_current_char(&self) -> Span {
        let cur = self.head.cur_bytes();
        span(cur, cur + 1, self.fid)
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

    pub fn lex_token(&mut self) -> Result<TokenType, Diagnostic> {
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
            Some('^') => Punct(Caret),
            Some('&') => Punct(Ampsand),
            Some('|') => Punct(Pipe),
            Some('%') => Punct(Percent),
            Some('#') => Punct(Hashtag),
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
                self.sink.emit(UnknownToken { c, loc: self.loc() });
                return Ok(TokenType::__NotAToken__);
            }
            None => EOF,
        };

        self.pop();

        Ok(t)
    }

    pub fn lex_identifier(&mut self) -> TokenType {
        let word = self.lex_word();

        match self.peek() {
            Some('\"') => {
                let str = match self.lex_string_with_options(false) {
                    Ok(TokenType::StringLit(s)) => s,
                    Ok(_) => unreachable!(),
                    Err(d) => {
                        self.sink.emit(d);
                        String::default()
                    }
                };

                TokenType::SpecializedStringLit {
                    specialization: word,
                    str,
                }
            }
            Some('\'') => {
                let char = match self.lex_char() {
                    Ok(TokenType::CharLit(c)) => c,
                    Ok(_) => unreachable!(),
                    Err(d) => {
                        self.sink.emit(d);
                        char::default()
                    }
                };

                TokenType::SpecializedCharLit {
                    specialization: word,
                    char,
                }
            }
            _ => {
                use TokenType::Kw;

                match word.as_str() {
                    Keyword::AND => Kw(Keyword::And),
                    Keyword::AS => Kw(Keyword::As),
                    Keyword::BREAK => Kw(Keyword::Break),
                    Keyword::COMPTIME => Kw(Keyword::Comptime),
                    Keyword::CONTINUE => Kw(Keyword::Continue),
                    Keyword::DEFER => Kw(Keyword::Defer),
                    Keyword::ELSE => Kw(Keyword::Else),
                    Keyword::EXTERN => Kw(Keyword::Extern),
                    Keyword::FALSE => Kw(Keyword::False),
                    Keyword::FOR => Kw(Keyword::For),
                    Keyword::FUN => Kw(Keyword::Fun),
                    Keyword::IF => Kw(Keyword::If),
                    Keyword::IMPL => Kw(Keyword::Impl),
                    Keyword::IN => Kw(Keyword::In),
                    Keyword::LET => Kw(Keyword::Let),
                    Keyword::LOOP => Kw(Keyword::Loop),
                    Keyword::MUT => Kw(Keyword::Mut),
                    Keyword::NULL => Kw(Keyword::Null),
                    Keyword::OR => Kw(Keyword::Or),
                    Keyword::ORB => Kw(Keyword::Orb),
                    Keyword::PUB => Kw(Keyword::Pub),
                    Keyword::RETURN => Kw(Keyword::Return),
                    Keyword::SELF => Kw(Keyword::SelfVal),
                    Keyword::THEN => Kw(Keyword::Then),
                    Keyword::TRAIT => Kw(Keyword::Trait),
                    Keyword::TRUE => Kw(Keyword::True),
                    Keyword::WHILE => Kw(Keyword::While),
                    _ => TokenType::Ident(word),
                }
            }
        }
    }

    /// Lexes the input while the content is alphanumeric with underscore(s)
    /// returns the content and if the string is numeric, in a tuple.
    pub fn lex_word(&mut self) -> String {
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
    pub fn lex_decimal(&mut self) -> String {
        // TODO: maybe add support for a wider amount of characters in unicode.
        // https://www.unicode.org/reports/tr31/ look at that maybe
        let mut decimal = String::new();

        while let Some(c @ ('_' | '0'..='9')) = self.peek() {
            decimal.push(c);
            self.pop();
        }

        decimal
    }

    /// Lexes the input while the content is hexadecimal digits or underscore,
    /// returns the content.
    pub fn lex_hexadecimal(&mut self) -> String {
        // TODO: maybe add support for a wider amount of characters in unicode.
        // https://www.unicode.org/reports/tr31/ look at that maybe
        let mut hex = String::new();

        while let Some(c @ ('_' | '0'..='9' | 'A'..='F' | 'a'..='f')) = self.peek() {
            hex.push(c);
            self.pop();
        }

        hex
    }

    pub fn lex_number(&mut self) -> Result<TokenType, Diagnostic> {
        let number = self.lex_number_internal()?;

        match self.peek() {
            Some('\'') => {
                self.pop();
                let specialization = self.lex_word();

                match number {
                    TokenType::IntLit(int) => Ok(TokenType::SpecializedIntLit {
                        specialization,
                        int,
                    }),
                    TokenType::FloatLit(float) => Ok(TokenType::SpecializedFloatLit {
                        specialization,
                        float,
                    }),
                    _ => unreachable!(),
                }
            }
            _ => Ok(number),
        }
    }

    /// function to lex a number BUT does not support specialization, call
    /// [`lex_number`] instead
    fn lex_number_internal(&mut self) -> Result<TokenType, Diagnostic> {
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
                // hexadecimal floating point number grammar:
                //
                // hex_float_lit = ("0x" | "0X") hex_mantissa hex_exponent ;
                // hex_mantissa = ["_"] hex_digits "." [hex_digits]
                //   | ["_"] hex_digits
                //   | "." hex_digits ;
                // hex_exponent = ("p" | "P") ["+" | "-"] decimal_digits ;

                self.pop(); // 0
                self.pop(); // X / x
                let int_str = self.lex_hexadecimal();
                let int_part = match self.parse_u128(&int_str, 16) {
                    Ok(h) => h,
                    Err(d) => {
                        self.sink.emit(d);
                        0
                    }
                };

                match self.peek() {
                    Some('.') => {
                        self.pop();

                        let (frac_part, frac_divisor) = match self.peek() {
                            Some('0'..='9' | 'a'..='f' | 'A'..='F' | '_') => {
                                let frac_str = self.lex_hexadecimal();

                                match self.parse_u128_with_digit_count(&frac_str, 16) {
                                    Ok((f, n)) => (f, n as i32),
                                    Err(d) => {
                                        self.sink.emit(d);
                                        (0, 0)
                                    }
                                }
                            }
                            _ => (0, 0),
                        };

                        let exp_value = match self.peek() {
                            Some('p' | 'P') => {
                                self.pop();
                                let sign = match self.peek() {
                                    Some('-') => {
                                        self.pop();
                                        -1i32
                                    }
                                    Some('+') => {
                                        self.pop();
                                        1i32
                                    }

                                    Some('_' | '0'..='9') => 1,
                                    Some(c) => {
                                        self.sink.emit(InvalidDigitInNumber {
                                            c,
                                            loc_c: self.loc_current_char(),
                                            loc_i: self.loc(),
                                        });
                                        1
                                    }
                                    _ => {
                                        self.sink.emit(ReachedEOF { loc: self.loc() });
                                        1
                                    }
                                };

                                let exp_str = self.lex_decimal();

                                let exp = match self.parse_u128(&exp_str, 10) {
                                    Ok(e) => e as i32,
                                    Err(d) => {
                                        self.sink.emit(d);
                                        0
                                    }
                                };

                                sign * exp
                            }
                            Some(found) => {
                                self.sink.emit(ExpectedExponentPart {
                                    found,
                                    loc_c: self.loc_current_char(),
                                    loc_float: self.loc(),
                                });
                                0
                            }
                            None => {
                                self.sink.emit(ReachedEOF { loc: self.loc() });
                                0
                            }
                        };

                        let int_f64 = int_part as f64;
                        let frac_f64 = frac_part as f64 * 16f64.powi(-frac_divisor);

                        let base = int_f64 + frac_f64;

                        let float = base * 2.0f64.powi(exp_value);

                        return Ok(TokenType::FloatLit(float));
                    }
                    Some('p' | 'P') => {
                        self.pop();
                        let sign = match self.peek() {
                            Some('-') => {
                                self.pop();
                                -1i32
                            }
                            Some('+') => {
                                self.pop();
                                1i32
                            }

                            Some('_' | '0'..='9') => 1,
                            Some(c) => {
                                self.sink.emit(InvalidDigitInNumber {
                                    c,
                                    loc_c: self.loc_current_char(),
                                    loc_i: self.loc(),
                                });
                                1
                            }
                            _ => {
                                self.sink.emit(ReachedEOF { loc: self.loc() });
                                1
                            }
                        };

                        let exp_str = self.lex_decimal();

                        let exp_value = sign
                            * match self.parse_u128(&exp_str, 10) {
                                Ok(e) => e as i32,
                                Err(d) => {
                                    self.sink.emit(d);
                                    0
                                }
                            };

                        let int_f64 = int_part as f64;
                        let float = int_f64 * 2.0f64.powi(exp_value);

                        return Ok(TokenType::FloatLit(float));
                    }
                    _ => {
                        if int_str.is_empty() {
                            self.sink.emit(NoDigitsInANonDecimal { loc: self.loc() });
                        }
                        return Ok(TokenType::IntLit(int_part));
                    }
                }
            }
            _ => 10,
        };
        let int_str = self.lex_word();

        if int_str.is_empty() {
            self.sink.emit(NoDigitsInANonDecimal { loc: self.loc() });
        }

        let int_part = self.parse_u128(&int_str, radix)?;

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
                        let frac_str = self.lex_decimal();

                        match self.parse_u128_with_digit_count(&frac_str, 10) {
                            Ok((f, n)) => (f, n as i32),
                            Err(d) => {
                                // NOTE: we are not using ? to propagate the diag, we just use
                                // a poisoned value
                                self.sink.emit(d);
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
                                self.sink.emit(InvalidDigitInNumber {
                                    c,
                                    loc_c: self.loc_current_char(),
                                    loc_i: self.loc(),
                                });
                                1
                            }
                            _ => {
                                self.sink.emit(ReachedEOF { loc: self.loc() });
                                1
                            }
                        };

                        let exp_str = self.lex_decimal();

                        let exp = match self.parse_u128(&exp_str, 10) {
                            Ok(e) => e as i32,
                            Err(d) => {
                                self.sink.emit(d);
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
            _ => Ok(TokenType::IntLit(int_part)),
        }
    }

    pub fn lex_string(&mut self) -> Result<TokenType, Diagnostic> {
        self.lex_string_with_options(true)
    }

    pub fn lex_string_with_options(
        &mut self,
        support_escape: bool,
    ) -> Result<TokenType, Diagnostic> {
        let mut str = String::new();

        // pop the first "
        self.pop();

        loop {
            match self.peek() {
                Some('"') => {
                    self.pop();
                    break;
                }
                Some('\\') if support_escape => {
                    self.pop();

                    let es = match self.pop() {
                        Some(es) => es,
                        None => continue,
                    };

                    if es == '"' {
                        str.push(es);
                        continue;
                    }

                    match self.lex_escape_sequence(es, true) {
                        Ok(c) => {
                            str.push(c);
                        }
                        Err(d) => {
                            self.sink.emit(d);
                        }
                    }
                }
                Some(c) => {
                    str.push(c);
                    self.pop();
                }
                _ => {
                    self.sink
                        .emit(UnterminatedStringLiteral { loc: self.loc() });
                    break;
                }
            }
        }

        Ok(TokenType::StringLit(str))
    }

    pub fn lex_char(&mut self) -> Result<TokenType, Diagnostic> {
        self.expect('\'');

        let mut empty_char = false;
        let c = match self.peek() {
            Some('\\') => {
                self.pop();

                let es = match self.pop() {
                    Some(es) => es,
                    None => {
                        self.sink.emit(ReachedEOF { loc: self.loc() });
                        char::default()
                    }
                };

                if es == '\'' {
                    es
                } else {
                    match self.lex_escape_sequence(es, false) {
                        Ok(es) => es,
                        Err(d) => {
                            self.sink.emit(d);
                            char::default()
                        }
                    }
                }
            }
            Some('\'') => {
                self.pop();
                self.sink.emit(EmptyCharLiteral { loc: self.loc() });
                empty_char = true;
                char::default()
            }
            Some(c) => {
                self.pop();
                c
            }
            None => {
                self.sink.emit(ReachedEOF { loc: self.loc() });
                char::default()
            }
        };

        if !empty_char {
            match self.peek() {
                Some('\'') => {
                    self.pop();
                }
                Some(_) => {
                    self.lex_until('\'');
                    self.pop(); // '
                    self.sink
                        .emit(TooManyCodepointsInCharLiteral { loc: self.loc() });
                }
                None => {
                    self.sink.emit(ReachedEOF { loc: self.loc() });
                }
            }
        }

        Ok(TokenType::CharLit(c))
    }

    /// makes an escape sequence return a tuple of the character that corresponds
    /// to the escape and the increments to make to the head
    pub fn lex_escape_sequence(&mut self, es: char, string: bool) -> Result<char, Diagnostic> {
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
            '\\' => char(0x5C), // \
            'x' => self.lex_hex_escape(string)?,
            'u' => {
                match self.peek() {
                    Some('{') => {
                        self.pop();
                    }
                    _ => self.sink.emit(InvalidUnicodeEscape {
                        note: InvalidUnicodeNote::ExpectedOpeningBrace,
                        loc: self.loc_current_char(),
                    }),
                }
                let hex_str = self.lex_hexadecimal();

                if hex_str.is_empty() {
                    self.sink.emit(InvalidUnicodeEscape {
                        note: InvalidUnicodeNote::EmptyUnicode,
                        loc: self.loc() + self.loc_current_char(),
                    });
                }

                let hex: u32 = match self.parse_u128(&hex_str, 16)?.try_into() {
                    Ok(h) => h,
                    Err(_) => {
                        self.sink.emit(InvalidUnicodeEscape {
                            note: InvalidUnicodeNote::TooBig,
                            loc: self.loc(),
                        });

                        0x00
                    }
                };

                match self.peek() {
                    Some('}') => {
                        self.pop();
                    }
                    _ => self.sink.emit(InvalidUnicodeEscape {
                        note: InvalidUnicodeNote::ExpectedClosingBrace,
                        loc: self.loc_current_char(),
                    }),
                }

                if let Some(c) = char::from_u32(hex) {
                    c
                } else {
                    self.sink.emit(InvalidUnicodeEscape {
                        note: InvalidUnicodeNote::MustNotBeASurrogate,
                        loc: self.loc(),
                    });

                    char::default()
                }
            }
            _ => {
                self.sink.emit(UnknownCharacterEscape {
                    es,
                    loc: self.loc(),
                });
                char::default()
            }
        };

        Ok(es)
    }

    /// set string to true if the escape sequence is part of a string, false if
    /// it is part of a char literal
    pub fn lex_hex_escape(&mut self, string: bool) -> Result<char, Diagnostic> {
        let mut str = String::with_capacity(2);
        for _ in 0..2 {
            str.push(match self.peek() {
                Some('\'') if !string => {
                    self.sink.emit(NotEnoughHexDigits {
                        loc: span(self.head.prev_bytes(), self.head.cur_bytes() + 1, self.fid),
                    });
                    break;
                }
                Some('"') if string => {
                    self.sink.emit(NotEnoughHexDigits {
                        loc: span(self.head.prev_bytes(), self.head.cur_bytes() + 1, self.fid),
                    });
                    break;
                }
                Some(_) => self.pop().unwrap(),
                None => {
                    self.pop();
                    self.sink
                        .emit(UnterminatedStringLiteral { loc: self.loc() });
                    // it's the poisoned value.
                    str.push_str("00");
                    break;
                }
            })
        }

        Ok(self.parse_u128_with_options(
            &str,
            16,
            ParseOptions {
                base_bytes: self.head.cur_bytes() - 2,
                int_loc: {
                    let cur_bytes = self.head.cur_bytes();

                    Some(span(cur_bytes - 2, cur_bytes, self.fid))
                },
            },
        )? as u8 as char)
    }

    /// Parse a string slice into a `u128` integer using the specified radix.
    ///
    /// This function is a convenience wrapper that parses the input string and
    /// returns only the parsed integer. If the input is malformed or the number
    /// is too large, a diagnostic error is returned.
    ///
    /// # Note
    ///
    /// The radix is 'inclusive' if you want to parse a number as a decimal,
    /// then `radix = 10` and if you want to parse a number as hexadecimal
    /// `radix = 16` etc etc...
    ///
    /// # Arguments
    ///
    /// * `input` - The string slice to parse.
    /// * `radix` - The base to use (between 2 and 36).
    ///
    /// # Errors
    ///
    /// Returns a [`Diagnostic`] if the input is invalid or too large.
    pub fn parse_u128(&mut self, input: &str, radix: u8) -> Result<u128, Diagnostic> {
        self.parse_u128_with_digit_count(input, radix)
            .map(|(int, _)| int)
    }

    /// Parse a string slice into a `u128` integer using the specified radix and
    /// custom options.
    ///
    /// Allows fine-grained control over how the number is parsed by passing
    /// additional options like the base byte offset for error location
    /// reporting.
    ///
    /// # Arguments
    ///
    /// * `input` - The string slice to parse.
    /// * `radix` - The base to use (between 2 and 36).
    /// * `options` - Parsing configuration such as base byte offset.
    ///
    /// # Errors
    ///
    /// Returns a [`Diagnostic`] on overflow or invalid input.
    pub fn parse_u128_with_options(
        &mut self,
        input: &str,
        radix: u8,
        options: ParseOptions,
    ) -> Result<u128, Diagnostic> {
        self.parse_u128_advanced(input, radix, options)
            .map(|(int, _)| int)
    }

    /// Parse a string slice into a `u128` and return how many digits were
    /// parsed.
    ///
    /// This is useful when you need to know how many characters in the input
    /// were part of a valid number. It uses the specified radix.
    ///
    /// # Arguments
    ///
    /// * `input` - The string to parse.
    /// * `radix` - The numeric base (between 2 and 36).
    ///
    /// # Returns
    ///
    /// Returns a tuple `(value, digit_count)`:
    /// * `value` - The parsed `u128` integer.
    /// * `digit_count` - The number of valid digits parsed.
    ///
    /// # Errors
    ///
    /// Returns a [`Diagnostic`] if the input is invalid or overflows.
    pub fn parse_u128_with_digit_count(
        &mut self,
        input: &str,
        radix: u8,
    ) -> Result<(u128, u32), Diagnostic> {
        self.parse_u128_advanced(
            input,
            radix,
            ParseOptions {
                base_bytes: self.head.prev_bytes(),
                int_loc: None,
            },
        )
    }

    /// Low-level parser for a `u128` with full error reporting and
    /// customization.
    ///
    /// This function gives the most control over parsing, including byte
    /// offset for accurate diagnostics. It reports invalid digits and handles
    /// underscores as digit separators (like Rust's numeric syntax).
    ///
    /// # Arguments
    ///
    /// * `input` - The string to parse.
    /// * `radix` - The numeric base (2–36 inclusive).
    /// * `options` - Parsing options (e.g. base offset for spans).
    ///
    /// # Returns
    ///
    /// Returns a tuple `(value, digit_count)`:
    /// * `value` - The parsed `u128` integer.
    /// * `digit_count` - Number of valid digits parsed (excluding underscores).
    ///
    /// # Panics
    ///
    /// Panics if `radix` is not between 2 and 36.
    ///
    /// # Errors
    ///
    /// Returns a [`Diagnostic`] if an invalid character is encountered or the
    /// value overflows.
    pub fn parse_u128_advanced(
        &mut self,
        input: &str,
        radix: u8,
        options: ParseOptions,
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
                    let pos = options.base_bytes + i;
                    self.sink.emit(InvalidDigitInNumber {
                        c,
                        loc_c: span(pos, pos + 1, self.fid),
                        loc_i: options.int_loc.clone().unwrap_or_else(|| self.loc()),
                    });

                    // the poisoned value
                    0
                }
            };

            if digit >= radix.into() {
                had_invalid_digit = true;
                let pos = options.base_bytes + i;
                self.sink.emit(InvalidDigitInNumber {
                    c,
                    loc_c: span(pos, pos + 1, self.fid),
                    loc_i: options.int_loc.clone().unwrap_or_else(|| self.loc()),
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
            self.sink.emit(TooLargeIntegerLiteral { loc: self.loc() })
        }

        Ok((result, digit_count))
    }
}

/// Configuration options for number parsing.
///
/// This struct is used to customize how parsing diagnostics are reported,
/// particularly where the input string began in the source, and more.
///
/// # Fields
///
/// * `base_bytes`
///   The byte offset of the start of the number in the source input. Used for
///   generating accurate error spans.
#[derive(Debug, Clone)]
pub struct ParseOptions {
    /// the base position where the parsing of the integer starts
    base_bytes: usize,
    /// location of the integer that is currently parsed
    int_loc: Option<Span>,
}
