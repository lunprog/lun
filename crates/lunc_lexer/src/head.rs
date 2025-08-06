/// Lexing head
#[derive(Debug, Clone)]
pub struct LexHead {
    /// the current position of the lexing head, in the `chars` field
    cur_chars: usize,
    /// the position of the previous token's end, in the `chars` field
    prev_chars: usize,
    /// the current position of the lexing head, index byte of the currently lexed file
    cur_bytes: usize,
    /// the position of the previous token's end, index byte of the currently lexed file
    prev_bytes: usize,
}

impl LexHead {
    /// Create a new lexer head
    pub fn new() -> LexHead {
        LexHead {
            cur_chars: 0,
            prev_chars: 0,
            cur_bytes: 0,
            prev_bytes: 0,
        }
    }

    /// Resets the head, to allow a new token to be lexed
    pub fn reset(&mut self) {
        self.prev_bytes = self.cur_bytes;
        self.prev_chars = self.cur_chars;
    }

    /// Return the byte position
    pub fn bytes_pos(&self) -> (usize, usize) {
        (self.prev_bytes, self.cur_bytes)
    }

    /// Return the current position in the char array
    pub fn cur_chars(&self) -> usize {
        self.cur_chars
    }

    /// Return the previous position in the char array
    pub fn prev_chars(&self) -> usize {
        self.prev_chars
    }

    /// Return the current position, index byte of the currently lexed file
    pub fn cur_bytes(&self) -> usize {
        self.cur_bytes
    }

    /// Return the previous position, index byte of the currently lexed file
    pub fn prev_bytes(&self) -> usize {
        self.prev_bytes
    }

    /// Increment the head with the corresponding character
    pub fn increment(&mut self, c: char) {
        self.cur_chars += 1;
        self.cur_bytes += c.len_utf8();
    }
}

impl Default for LexHead {
    fn default() -> Self {
        LexHead::new()
    }
}
