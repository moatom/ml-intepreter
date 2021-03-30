open Syntax
open Types
open Parser
open Lexer

(* open CallByValue *)
open CallByName

let main () =
  let open Format in
  let ppf = std_formatter in
  match Sys.argv with
  | [| _; fname |] -> (
    (* file *)
    let ch = open_in fname in
    let lexbuf = Lexing.from_channel ch in
    try
      let result = Parser.main Lexer.token lexbuf in
      let typ, _ = infer_expr [] result in
      print_expr ppf result;
      pp_print_newline ppf ();
      pp_print_newline ppf ();
      print_string "- : ";
      (* type *)
      print_type ppf typ;
      print_string " = ";
      print_value ppf (eval [] result);
      pp_print_newline ppf ()
    with
    | Parsing.Parse_error ->
      print_endline "Parse Error!";
      close_in ch)
  | _ ->
    (* repl *)
    let lexbuf = Lexing.from_channel stdin in
    let rec aux env tenv : unit =
      try
        let t = Parser.repl Lexer.token lexbuf in
        let typ, tenv' = infer_cmd tenv t in
        match t with
        | CExp result ->
          print_string "- : ";
          (* type *)
          print_type ppf typ;
          print_string " = ";
          print_value ppf (eval env result);
          print_newline ();
          aux env tenv'
        | CLet (name, result) ->
          let t' = eval env result in
          print_string "val ";
          print_name ppf name;
          print_string " : ";
          (* type *)
          print_type ppf typ;
          print_string " = ";
          print_value ppf t';
          print_newline ();
          aux ((name, t') :: env) tenv'
      with
      | Parsing.Parse_error ->
        print_endline "Parse Error!";
        Lexing.flush_input lexbuf;
        aux env tenv
      | Types.Unify_error
      | Types.Unbound_error ->
        print_endline "Type Error!";
        Lexing.flush_input lexbuf;
        aux env tenv
    in
    aux [] []

;;
if !Sys.interactive then
  ()
else
  main ()
