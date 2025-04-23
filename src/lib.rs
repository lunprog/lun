//! L2 is a simple, staticaly typed programming language that aims to replace Lua,
//!
//! # Hello world example
//!
//! ```l2
//! println("Hello world!")
//! ```
//!
//! # Fibonacci example
//!
//! ```l2
//! fun fib(n: int) -> int
//!     if n < 2 then return n end
//!     return fib(n - 1) + fib(n + 1)
//! end
//! ```
use std::fmt::Display;

pub mod blob;
pub mod lexer;
pub mod parser;
pub mod token;
pub mod vm;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span {
    // TODO: maybe rename `start` to `lo` and `end` to `hi`.
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub const fn from_ends(start: Span, end: Span) -> Span {
        Span {
            start: start.start,
            end: end.end,
        }
    }
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

/// Write a u64 in little endian format at the end of the Vec, and returns the
/// offset where it was written
pub fn write_qword(bytes: &mut Vec<u8>, qword: u64) -> usize {
    let offset = bytes.len();

    let qword_bytes = qword.to_le_bytes();
    bytes.extend_from_slice(&qword_bytes);

    offset
}

/// Write a u32 in little endian format at the end of the Vec, and returns the
/// offset where it was written
pub fn write_dword(bytes: &mut Vec<u8>, dword: u32) -> usize {
    let offset = bytes.len();

    let dword_bytes = dword.to_le_bytes();
    bytes.extend_from_slice(&dword_bytes);

    offset
}

/// Write a u16 in little endian format at the end of the Vec, and returns the
/// offset where it was written
pub fn write_word(bytes: &mut Vec<u8>, word: u16) -> usize {
    let offset = bytes.len();

    let word_bytes = word.to_le_bytes();
    bytes.extend_from_slice(&word_bytes);

    offset
}

/// Reads a 64 bit little-endian u64 from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full u64.
pub fn read_qword(bytes: &[u8], offset: usize) -> u64 {
    let end = offset + 8;
    let qword = &bytes[offset..end];
    u64::from_le_bytes(qword.try_into().expect("Slice should be 8 bytes long"))
}

/// Reads a 32 bit little-endian u32 from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full u32.
pub fn read_dword(bytes: &[u8], offset: usize) -> u32 {
    let end = offset + 4;
    let dword = &bytes[offset..end];
    u32::from_le_bytes(dword.try_into().expect("Slice should be 4 bytes long"))
}

/// Reads a 16 bit little-endian u16 from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full u16.
pub fn read_word(bytes: &[u8], offset: usize) -> u16 {
    let end = offset + 2;
    let word = &bytes[offset..end];
    u16::from_le_bytes(word.try_into().expect("Slice should be 2 bytes long"))
}

/// Reads a 64 bit little-endian u64 from the Slice at the given offset.
/// Panics if there are not enough bytes to read a full u64.
pub fn read_many(bytes: &[u8], offset: usize, size: usize) -> &[u8] {
    let end = offset + size;
    &bytes[offset..end]
}
