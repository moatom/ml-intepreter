SOURCES = syntax.ml types.ml lexer.mll parser.mly interpreter.ml
RESULT  = interpreter
OCAMLFLAGS = -w +27

YFLAGS = -v 

all: native-code native-code-library

clean::
	rm -f parser.output

-include OCamlMakefile
