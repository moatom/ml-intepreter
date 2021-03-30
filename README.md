# README #
This is an interpreter for a concise ML-like language which has pattern-matching, a type system based on TAPL Ch 22 (type reconstruction), and a tunable evaluation strategy between call-by-value and call-by-name.


## How to Use ##
Invoke `make` in an environment where OCaml is installed, the you can use this interpreter in REPL or file input mode:
- `./interpreter`
- `./interpreter <filename>` like `./interpreter tests/parser/test1`

You can toggle evaluation strategies by the line 6 and 7 in interpreter.ml.