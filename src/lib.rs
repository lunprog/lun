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

pub mod blob;
pub mod parser;
pub mod vm;
