%{
  open Syntax
  let fold_extra_args : Syntax.name list -> Syntax.expr -> Syntax.expr =
    fun args e ->
      List.fold_left (fun z x ->
        EFun(x,z)
      ) e args

  let to_etuple extra_exprs e1 e2 =
    match extra_exprs with
    | [] -> ETuple([e1;e2])
    | xs -> ETuple(xs @ [e1;e2])

  let to_ptuple extra_patts e1 e2 =
    match extra_patts with
    | [] -> PTuple([e1;e2])
    | xs -> PTuple(xs @ [e1;e2])

%}


%token <int>    INT
%token <string> ID
%token TRUE FALSE
%token BRACKETS COLONCOLON

%token LET REC AND IN
%token MATCH WITH END
%token IF THEN ELSE
%token FUN RARROW

%token PLUS MINUS TIMES DIVIDE
%token EQ LT

%token LPAR RPAR
%token COMMA
%token SEMISEMI
%token BAR
%token EOF


// https://github.com/ocaml/ocaml/blob/trunk/parsing/parser.mly#L793
// https://caml.inria.fr/pub/docs/manual-ocaml/language.html
%nonassoc IN
%nonassoc LET
%nonassoc WITH
%nonassoc AND
%nonassoc THEN
%nonassoc ELSE
%left BAR
%left COMMA
%right RARROW
%left EQ LT
%right COLONCOLON
%left PLUS MINUS
%left TIMES DIVIDE
%nonassoc INT ID TRUE FALSE LPAR RPAR


// Process a file
%start main
%type <Syntax.expr> main
// REPL
%start repl
%type <Syntax.command> repl
%% 

main: 
expr EOF {$1}
;

repl: 
  | expr SEMISEMI           { CExp($1) }
  | LET ID EQ expr SEMISEMI { CLet($2,$4) }
;

expr:
  | LET ID EQ expr IN expr                    { ELet($2,$4,$6) }
  | LET REC ID EQ expr IN expr                { ERLetV($3,$5,$7) } // only works in CBN
  | LET REC ID ID extra_args EQ expr IN expr  { ERLet($3,$4,fold_extra_args $5 $7,$9) }
  | LET REC ID ID extra_args EQ expr
    and_seped_letrecs IN expr                 { ERAndLet(($3,$4,fold_extra_args $5 $7)::$8, $10) }
  | MATCH expr WITH patt_and_exprs END        { EMatch($2, List.rev $4) }
  | IF expr THEN expr ELSE expr               { EIfThenElse($2,$4,$6) }
  | FUN ID extra_args RARROW expr             { EFun($2, fold_extra_args $3 $5) }
  | arith_expr                                { $1 }
;

and_seped_letrecs:
  | AND ID ID extra_args EQ expr and_seped_letrecs { [$2,$3, fold_extra_args $4 $6] @ $7 }
  |                                                { [] }
;

arith_expr:
  | arith_expr PLUS       arith_expr { EBin(OpAdd,$1,$3) }
  | arith_expr MINUS      arith_expr { EBin(OpSub,$1,$3) }
  | arith_expr TIMES      arith_expr { EBin(OpMul,$1,$3) }
  | arith_expr DIVIDE     arith_expr { EBin(OpDiv,$1,$3) }
  | arith_expr EQ         arith_expr { EBin(OpEq,$1,$3) }
  | arith_expr LT         arith_expr { EBin(OpLt,$1,$3) }
  | arith_expr COLONCOLON arith_expr { ECons($1,$3) }
  | app_expr                         { $1 }
;

app_expr:
  | app_expr atomic_expr { EApp($1,$2) }
  | atomic_expr          { $1 }
;

atomic_expr:
  | const          { $1 }
  | ID             { EVar($1) }
  | LPAR expr commma_seped_exprs RPAR         { ETuple([$2] @ $3) }
  | LPAR expr RPAR { $2 }
;

commma_seped_exprs:
  | COMMA expr commma_seped_exprs { [$2] @ $3 }
  |                               { [] }
;

const:
  | INT      { EConst(VInt($1)) }
  | TRUE     { EConst(VBool(true)) }
  | FALSE    { EConst(VBool(false)) }
  | BRACKETS { EConst(VNil) }
;

extra_args:
  | extra_args ID  { $2::$1 }
  |                { [] }
;

patt_and_exprs:
  | patt_and_exprs BAR patt RARROW expr { ($3,$5)::$1 }
  | patt RARROW expr                    { [($1,$3)] }
  | BAR patt RARROW expr                { [($2,$4)] }
;

patt:
  | INT                       { PConstInt($1) }
  | BRACKETS                  { PNil }
  | patt COLONCOLON patt      { PCons($1, $3) }
  | LPAR patt
    commma_seped_patts RPAR   { PTuple([$2] @ $3) }
  | ID                        { PVar($1) }
  | TRUE                      { PConstBool(true) }
  | FALSE                     { PConstBool(false) }
  | LPAR patt RPAR            { $2 }
;

commma_seped_patts:
  | COMMA patt commma_seped_patts { [$2] @ $3 }
  |                               { [] }
;
