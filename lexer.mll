{
  open Parser
}

let digit = ['0'-'9']
let space = ' ' | '\t' | '\r' | '\n'
let alpha = ['a'-'z' 'A'-'Z' '_' ] 
let ident = alpha (alpha | digit | '\'')* 

rule token = parse
| space+      { token lexbuf }

| "let"       { LET }
| "rec"       { REC }
| "and"       { AND }
| "in"        { IN }

| "match"     { MATCH }
| "with"      { WITH }
| "end"       { END }

| "if"        { IF }
| "then"      { THEN }
| "else"      { ELSE }

| "fun"       { FUN }
| "->"        { RARROW }

| '='         { EQ }
| '<'         { LT }

| '+'         { PLUS }
| '-'         { MINUS }
| '*'         { TIMES }
| '/'         { DIVIDE }

| ";;"        { SEMISEMI }
| '|'         { BAR }

| '('         { LPAR }
| ')'         { RPAR }

| "[]"        { BRACKETS }
| ','         { COMMA }
| "::"        { COLONCOLON }
| "true"      { TRUE }
| "false"     { FALSE }
| digit+ as n { INT (int_of_string n) }
| ident  as n { ID n }

| eof         { EOF  }
| _           { failwith ("Unknown Token: " ^ Lexing.lexeme lexbuf)}
