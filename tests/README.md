# Tests of the compiler

This directory contains the various tests performed on the various stages of
compilation.

## Test types

There is 3 types of tests in the compiler, `"positive"`, `"negative"` and
`"resilience"`. Each have a purpose and a naming convention.

Every test name should be in `snake_case` and the name MUST finish with `.lun`.

### `"positive"`

Positive tests, are testing and ensuring something is working and that it
doesn't make the compiler output any diagnostic or exit with a non zero status
code.

#### Naming convention

A simple name that describes the test.

### `"negative"`

Negative tests, ensure that the compiler is outputting a diagnostic(s) and the
correct diagnostic(s) and should always have a compiler exit code of `255`.

#### Naming convention

Start with the error code, followed by a short description like positive tests
if necessary.

*e.g:* `E006_expr_1.lun`, `E041.lun`

In the testing file a comment at the top of the file must be present and with
the following form:

```lun
// ENNN: error testing - ErrorName
```

with `ENNN` be the number of the test and `ErrorName` be the `UpperCamelCase`
name of the error in `lunc_diag::ErrorCode`.

*e.g:*
```lun
// EO41: error testing - MainUndefined

...
```

### `"resilience"`

Resilience tests, ensure that the compiler correctly recover from errors in
a way that should not change. It's primarily used by the parser for parsing
recovery.


#### Naming convention

Starts with the error code, followed by a short description like positive tests
if necessary and finish with `resilience_NNN` and a `NNN` when multiple tests
are needed.

*e.g:* `E006_extern_block_resilience_1.lun`

In the testing file a comment MUST be present with the following form:

```lun
// ENNN: error resilience testing - ErrorName
```

with `ENNN` be the number of the test and `ErrorName` be the `UpperCamelCase`
name of the error in `lunc_diag::ErrorCode`.

*e.g:*
```lun
// E006: error resilience testing - ExpectedToken

// ..
```

## Directories

Explanation of the directories:

- `behavior/` is testing the correct behavior of the compiler assembly, like a
  `logic_and` correctly performs the and operation and that it short circuits.
- `desugaring/` is testing the `DSIR` stage of the compiler, where we combine
  modules in one tree, we desugar some Lun syntax to be easier, and we resolve names.
- `lexer/` is testing the lexer.
- `multifile` is a special tests that deeply test the desugaring stage with more
  complex name resolution to ensure that it is working. And more generally it is
  here to ensure that the compiler works as expected on multiple files.
- `parser/` is testing the parser.
- `scir/` is testing the semantic checker.
