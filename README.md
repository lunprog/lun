# l2

Language heavily inspired by Lua so its name come from it kinda:
`Lua v2` -> `l2`.

- To create the tree sitter take inspiration from:
  https://github.com/tjdevries/tree-sitter-lua
- Name resolution -> https://www3.nd.edu/~dthain/compilerbook/chapter7.pdf
  and generally -> https://www3.nd.edu/~dthain/compilerbook/
- Use https://github.com/brendanzab/codespan for diagnostics or
  https://github.com/zesterer/ariadne, or `miette`, create a Diagnotic Collector
  `DiagnosticSink`, that we store in the lexer, parser etc and we return it if,
  we encoutered errors in the current phase.
- Reimplement with `salsa` to enable incremental compilation and some crazy
  things

TODO: implement a tests suit in `tests/` that check every stage of `l2` and
source code files have the following format to expect errors or a result:
```l2
local fun = 0
//    ^ err: E0006
```
to expect an error or
```l2
local a = 2 * 4 + 3 // ok: a = 11
```
to expect a value in a variable or elsewhere

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
