open Format

let val_or_exception : (unit -> 'b) -> 'a option -> 'a =
 fun k optv ->
  match optv with
  | Some x -> x
  | None -> k ()

type name = string

type binOp =
  | OpAdd
  | OpSub
  | OpMul
  | OpDiv
  | OpEq
  | OpLt
  | OpLAnd
  | OpLOr

type value =
  | VInt of int
  | VBool of bool
  | VNil
  | VCons of value * value
  | VTuple of value list
  | VVal of name * expr * env
  | VFun of name * expr * env
  | VRFun of name * name * expr * env
  | VRAndFun of int * (name * name * expr) list * env
  | Thunk of expr * env

and env = (name * value) list

and patt =
  | PConstInt of int
  | PConstBool of bool
  | PNil
  | PCons of patt * patt
  | PTuple of patt list
  | PVar of name

and expr =
  | EConst of value
  | ECons of expr * expr
  | ETuple of expr list
  | EVar of name
  | EBin of binOp * expr * expr
  | EIfThenElse of expr * expr * expr
  | ELet of name * expr * expr
  | ERLetV of name * expr * expr
  | ERLet of name * name * expr * expr
  | ERAndLet of (name * name * expr) list * expr
  | EMatch of expr * (patt * expr) list
  | EFun of name * expr
  | EApp of expr * expr

and command =
  | CExp of expr
  | CLet of name * expr

exception Eval_error

let get_int : value -> int = function
  | VInt x -> x
  | _ -> raise Eval_error
let get_bool : value -> bool = function
  | VBool x -> x
  | _ -> raise Eval_error

let get_tuple : value -> value list = function
  | VTuple x -> x
  | _ -> raise Eval_error

module CallByValue = struct
  let rec find_match : patt -> value -> env option =
   fun pt v ->
    match pt with
    | PConstInt i ->
      if i = get_int v then
        Some []
      else
        None
    | PConstBool b ->
      if b = get_bool v then
        Some []
      else
        None
    | PVar x -> Some [ (x, v) ]
    | PNil ->
      if v = VNil then
        Some []
      else
        None
    | PCons (x, xs) -> (
      match v with
      | VCons (y, ys) -> (
        let hd = find_match x y in
        let tl = find_match xs ys in
        match (hd, tl) with
        | Some x, Some y -> Some (x @ y)
        | _ -> None)
      | _ -> None)
    | PTuple [] ->
      if v = VTuple [] then
        Some []
      else
        None
    | PTuple (x :: xs) -> (
      let tp = get_tuple v in
      let hd = find_match x (List.hd tp) in
      let tl = find_match (PTuple xs) (VTuple (List.tl tp)) in
      match (hd, tl) with
      | Some x, Some y -> Some (x @ y)
      | _ -> None)

  let rec eval : env -> expr -> value =
   fun env -> function
    | EConst x -> x
    | ECons (x, xs) ->
      let v = eval env x in
      let vs = eval env xs in
      VCons (v, vs)
    | ETuple xs -> VTuple (xs |> List.map (fun e -> eval env e))
    | EVar x ->
      List.assoc_opt x env |> val_or_exception (fun () -> raise Eval_error)
    | EBin (OpAdd, x, y) ->
      VInt ((get_int @@ eval env x) + (get_int @@ eval env y))
    | EBin (OpSub, x, y) ->
      VInt ((get_int @@ eval env x) - (get_int @@ eval env y))
    | EBin (OpMul, x, y) ->
      VInt ((get_int @@ eval env x) * (get_int @@ eval env y))
    | EBin (OpDiv, x, y) ->
      VInt ((get_int @@ eval env x) / (get_int @@ eval env y))
    | EBin (OpEq, x, y) ->
      VBool (get_int @@ eval env x = get_int @@ eval env y)
    | EBin (OpLt, x, y) ->
      VBool (get_int @@ eval env x < get_int @@ eval env y)
    | EBin (OpLAnd, x, y) ->
      VBool ((get_bool @@ eval env x) && (get_bool @@ eval env y))
    | EBin (OpLOr, x, y) ->
      VBool ((get_bool @@ eval env x) || (get_bool @@ eval env y))
    | EIfThenElse (cond, et, ef) -> (
      match eval env cond with
      | VBool x ->
        if x then
          eval env et
        else
          eval env ef
      | _ -> raise Eval_error)
    | ELet (name, e1, e2) -> eval ((name, eval env e1) :: env) e2
    | ERLetV _ -> raise Eval_error
    | ERLet (fname, name, e1, e2) ->
      eval ((fname, VRFun (fname, name, e1, env)) :: env) e2
    | ERAndLet (fns, e2) ->
      let fns_env =
        fns |> List.mapi (fun i (f, _, _) -> (f, VRAndFun (i, fns, env)))
      in
      eval (fns_env @ env) e2
    | EMatch (e1, tuples) -> (
      let v = eval env e1 in
      let matched =
        tuples
        |> List.find_map (fun (pat, e2) ->
               find_match pat v |> Option.map (fun env' -> (pat, e2, env')))
      in
      match matched with
      | Some (_, e2, env') -> eval (env' @ env) e2
      | None -> raise Eval_error)
    | EFun (name, e) -> VFun (name, e, env)
    | EApp (e1, e2) -> (
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      match v1 with
      | VFun (x, e, env') -> eval ((x, v2) :: env') e
      | VRFun (f, x, e, env') ->
        eval ((x, v2) :: (f, VRFun (f, x, e, env')) :: env') e
      | VRAndFun (i, fns, env') ->
        let fns_env =
          fns |> List.mapi (fun i (f, _, _) -> (f, VRAndFun (i, fns, env')))
        in
        let _, x, e = List.nth fns i in
        eval ((x, v2) :: fns_env @ env') e
      | _ -> raise Eval_error)
end

module CallByName = struct
  let rec find_match_lazy : env -> patt -> expr -> env option =
   fun env pt e ->
    match pt with
    | PConstInt i ->
      let v = eval env e in
      (* call-by-need would share v if e is thunk *)
      if i = get_int v then
        Some []
      else
        None
    | PConstBool b ->
      let v = eval env e in
      if b = get_bool v then
        Some []
      else
        None
    | PVar x -> Some [ (x, Thunk (e, env)) ]
    | PNil ->
      let v = eval env e in
      if v = VNil then
        Some []
      else
        None
    | PCons (x, xs) -> (
      let v = eval env e in
      match v with
      | VCons (y, ys) -> (
        let hd = find_match_lazy env x (EConst y) in
        let tl = find_match_lazy env xs (EConst ys) in
        match (hd, tl) with
        | Some x, Some y -> Some (x @ y)
        | _ -> None)
      | _ -> None)
    | PTuple [] ->
      let v = eval env e in
      if v = VTuple [] then
        Some []
      else
        None
    | PTuple (x :: xs) -> (
      let v = eval env e in
      let tp = get_tuple v in
      let hd = find_match_lazy env x (EConst (List.hd tp)) in
      let tl =
        find_match_lazy env (PTuple xs)
          (ETuple (List.tl tp |> List.map (fun e -> EConst e)))
      in
      match (hd, tl) with
      | Some x, Some y -> Some (x @ y)
      | _ -> None)

  (* tak works too slowly... *)
  and eval : env -> expr -> value =
   fun env -> function
    | EConst (Thunk (e, env')) -> eval env' e
    | EConst (VCons (x, xs)) ->
      let v = eval env (EConst x) in
      let vs = eval env (EConst xs) in
      VCons (v, vs)
    | EConst (VTuple xs) ->
      VTuple (xs |> List.map (fun e -> eval env (EConst e)))
    | EConst x -> x
    | ECons (x, xs) -> VCons (Thunk (x, env), Thunk (xs, env))
    | ETuple xs -> VTuple (xs |> List.map (fun e -> Thunk (e, env)))
    | EVar x -> (
      let x' =
        List.assoc_opt x env |> val_or_exception (fun () -> raise Eval_error)
      in
      match x' with
      (* Support recursive value *)
      | VVal (x, e, env') -> eval ((x, VVal (x, e, env')) :: env') e
      | Thunk (e, env') -> eval env' e
      | y -> y)
    | EBin (OpAdd, x, y) ->
      VInt ((get_int @@ eval env x) + (get_int @@ eval env y))
    | EBin (OpSub, x, y) ->
      VInt ((get_int @@ eval env x) - (get_int @@ eval env y))
    | EBin (OpMul, x, y) ->
      VInt ((get_int @@ eval env x) * (get_int @@ eval env y))
    | EBin (OpDiv, x, y) ->
      VInt ((get_int @@ eval env x) / (get_int @@ eval env y))
    | EBin (OpEq, x, y) ->
      VBool (get_int @@ eval env x = get_int @@ eval env y)
    | EBin (OpLt, x, y) ->
      VBool (get_int @@ eval env x < get_int @@ eval env y)
    | EBin (OpLAnd, x, y) ->
      VBool ((get_bool @@ eval env x) && (get_bool @@ eval env y))
    | EBin (OpLOr, x, y) ->
      VBool ((get_bool @@ eval env x) || (get_bool @@ eval env y))
    | EIfThenElse (cond, et, ef) ->
      eval env cond |> get_bool |> fun x ->
      if x then
        eval env et
      else
        eval env ef
    | ELet (x, e1, e2) -> eval ((x, Thunk (e1, env)) :: env) e2
    | ERLetV (x, e1, e2) -> eval ((x, VVal (x, e1, env)) :: env) e2
    | ERLet (f, x, e1, e2) -> eval ((f, VRFun (f, x, e1, env)) :: env) e2
    | ERAndLet (fns, e2) ->
      let fns_env =
        fns |> List.mapi (fun i (f, _, _) -> (f, VRAndFun (i, fns, env)))
      in
      eval (fns_env @ env) e2
    | EMatch (e1, tuples) -> (
      let matched =
        tuples
        |> List.find_map (fun (pat, e2) ->
               find_match_lazy env pat e1
               |> Option.map (fun env' -> (pat, e2, env')))
      in
      match matched with
      | Some (_, e2, env') -> eval (env' @ env) e2
      | None -> raise Eval_error)
    | EFun (name, e) -> VFun (name, e, env)
    | EApp (e1, e2) -> (
      let v1 = eval env e1 in
      match v1 with
      | VFun (x, e, env') -> eval ((x, Thunk (e2, env)) :: env') e
      | VRFun (f, x, e, env') ->
        eval ((x, Thunk (e2, env)) :: (f, v1) :: env') e
      | VRAndFun (i, fns, env') ->
        let fns_env = fns |> List.map (fun (f, _, _) -> (f, v1)) in
        let _, x, e = List.nth fns i in
        eval ((x, Thunk (e2, env)) :: fns_env @ env') e
      | _ -> raise Eval_error)
end

let rec print_name ppf = pp_print_string ppf

and print_value ppf value =
  let rec aux k ppf = function
    | VInt i -> pp_print_int ppf i
    | VBool b -> pp_print_string ppf @@ string_of_bool b
    | VNil ->
      if k then
        pp_print_string ppf "[]"
      else
        pp_print_string ppf "..."
    | VCons (x, xs) -> fprintf ppf "@[(%a :: %a)@]" (aux k) x (aux k) xs
    | VTuple xs ->
      fprintf ppf "@[(%a)@]"
        (pp_print_list
           ~pp_sep:(fun ppf () -> pp_print_string ppf ", ")
           (aux k))
        xs
    | VVal (x, (ECons (_, _) as e), env) as thunk -> (
      let rec mk_plist nil_term = function
        | [] -> PNil
        | [ x ] when nil_term -> PCons (PVar x, PNil)
        | [ x ] -> PVar x
        | x :: xs -> PCons (PVar x, mk_plist nil_term xs)
      in
      let rec mk_elist nil_term = function
        | [] -> EConst VNil
        | [ x ] when nil_term -> ECons (EVar x, EConst VNil)
        | [ x ] -> EVar x
        | x :: xs -> ECons (EVar x, mk_elist nil_term xs)
      in
      try
        let vars = [ "x1"; "x2"; "x3"; "x4"; "x5" ] in
        let vars_res = [ "x1"; "x2"; "x3"; "x4" ] in
        let see4' =
          CallByName.eval ((x, thunk) :: env)
            (EMatch (e, [ (mk_plist false vars, mk_elist true vars_res) ]))
        in
        let see4 = CallByName.eval [] (EConst see4') in
        aux false ppf see4
      with
      | Eval_error -> print_expr ppf e)
    | VVal (_, e, _) -> print_expr ppf e
    | VFun (name, e, _) ->
      (* XXX env *)
      pp_print_string ppf "fun ";
      print_name ppf name;
      pp_print_string ppf " -> ";
      print_expr ppf e
    | VRFun (fname, name, e, _) ->
      (* XXX env *)
      pp_print_string ppf "fun ";
      print_name ppf fname;
      pp_print_string ppf " ";
      print_name ppf name;
      pp_print_string ppf " -> ";
      print_expr ppf e
    | VRAndFun (i, fns, env) ->
      let f, x, e = List.nth fns i in
      (aux k) ppf (VRFun (f, x, e, env))
    | Thunk (EVar x, env) ->
      let x' = List.assoc x env in
      (aux k) ppf x'
    | Thunk (e, env) -> (
      try
        let v = CallByName.eval env e in
        (aux k) ppf v
      with
      | Eval_error -> print_expr ppf e)
  in
  aux true ppf value

and print_bin ppf (op, x, y) =
  print_expr ppf x;
  (match op with
  | OpAdd -> pp_print_string ppf " + "
  | OpSub -> pp_print_string ppf " - "
  | OpMul -> pp_print_string ppf " * "
  | OpDiv -> pp_print_string ppf " / "
  | OpEq -> pp_print_string ppf " = "
  | OpLt -> pp_print_string ppf " < "
  | OpLAnd -> pp_print_string ppf " && "
  | OpLOr -> pp_print_string ppf " || ");
  print_expr ppf y

and print_patt ppf = function
  | PConstInt i -> print_expr ppf (EConst (VInt i))
  | PConstBool b -> print_expr ppf (EConst (VBool b))
  | PNil -> pp_print_string ppf "[]"
  | PCons (x, xs) -> fprintf ppf "@[%a :: %a@]" print_patt x print_patt xs
  | PTuple xs ->
    fprintf ppf "@[(%a)@]"
      (pp_print_list
         ~pp_sep:(fun ppf () -> pp_print_string ppf ", ")
         print_patt)
      xs
  | PVar x -> print_expr ppf (EVar x)

and print_expr ppf = function
  | EConst v -> print_value ppf v
  | ECons (x, xs) -> fprintf ppf "@[(%a :: %a)@]" print_expr x print_expr xs
  | ETuple xs ->
    fprintf ppf "@[(%a)@]"
      (pp_print_list
         ~pp_sep:(fun ppf () -> pp_print_string ppf ", ")
         print_expr)
      xs
  | EVar x -> print_name ppf x
  | EBin (op, x, y) -> print_bin ppf (op, x, y)
  | EIfThenElse (cond, e1, e2) ->
    pp_print_string ppf "if ";
    print_expr ppf cond;
    pp_print_string ppf " then ";
    print_expr ppf e1;
    pp_print_string ppf "\n else ";
    print_expr ppf e2
  | ELet (name, e1, e2) ->
    pp_print_string ppf "let ";
    print_name ppf name;
    pp_print_string ppf " = ";
    print_expr ppf e1;
    pp_print_string ppf " in ";
    print_expr ppf e2
  | ERLetV (name, e1, e2) ->
    pp_print_string ppf "let rec ";
    print_name ppf name;
    pp_print_string ppf " = ";
    print_expr ppf e1;
    pp_print_string ppf " in ";
    print_expr ppf e2
  | ERLet (fname, name, e1, e2) ->
    pp_print_string ppf "let rec ";
    print_name ppf fname;
    pp_print_string ppf " ";
    print_name ppf name;
    pp_print_string ppf " = ";
    print_expr ppf e1;
    pp_print_string ppf " in ";
    print_expr ppf e2
  | ERAndLet (fns, e2) ->
    pp_print_string ppf "let rec ";
    pp_print_list
      ~pp_sep:(fun ppf () -> fprintf ppf "@.%s" " and ")
      (fun ppf (f, x, e1) ->
        print_name ppf f;
        pp_print_string ppf " ";
        print_name ppf x;
        pp_print_string ppf " = ";
        print_expr ppf e1)
      ppf fns;
    pp_print_string ppf " in ";
    print_expr ppf e2
  | EMatch (e, tuples) ->
    let rec aux = function
      | [] -> ()
      | (pt, e2) :: xs ->
        pp_print_string ppf "\n| ";
        print_patt ppf pt;
        pp_print_string ppf " -> ";
        print_expr ppf e2;
        aux xs
    in
    pp_print_string ppf "(match ";
    print_expr ppf e;
    pp_print_string ppf " with";
    aux tuples;
    pp_print_string ppf "\nend)\n"
  | EFun (name, e) ->
    pp_print_string ppf "fun ";
    print_name ppf name;
    pp_print_string ppf " -> ";
    print_expr ppf e
  | EApp (fn, x) ->
    pp_print_string ppf "(";
    print_expr ppf fn;
    pp_print_string ppf ") (";
    print_expr ppf x;
    pp_print_string ppf ")"
