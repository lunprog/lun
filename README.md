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
