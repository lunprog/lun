<div align="center">
  <picture>
    <!-- white logo for dark mode -->
    <source
      srcset="https://raw.githubusercontent.com/thi8v/lun/main/logo/logo_no_bg_white.png"
      media="(prefers-color-scheme: dark)"
    >
    <!-- black logo for light mode (fallback) -->
    <img
      src="https://raw.githubusercontent.com/thi8v/lun/main/logo/logo_no_bg_black.png"
      alt="The Lun Programming Language"
      style="width: 50%;"
    >
  </picture>
</div>

# The Lun Programming Language

> [!WARNING]
> The compiler, `lunc` and the programming language are both experimental, and
> **may not** work. It is not recommended to use Lun in production.

Lun is a general-purpose programming language, that compile AOT to machine code,
used to create **maintanable**, **reusable** and **optimized** software.

## Installation

### Build from source on Linux

```bash
# 1. clone the repo
$ git clone git@github.com:thi8v/lun.git

# 2. build the lunc compiler
$ cargo build --bin lunc --release

# 3. use the lunc compiler
$ ./target/release/lunc
```

## Example

Checkout the examples in the [examples folder].

### Hello world

Unfortunately there is no function currently to print to stdout, so we can't do
hello world.

[examples folder]: examples/

## License

Licensed under either of
 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Feel free to contribute. For the moment there is no documentation but it will come.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you shall be dual licensed as above, without any
additional terms or conditions.
