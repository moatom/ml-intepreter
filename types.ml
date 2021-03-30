type type_name = string

type ty =
  | TInt
  | TBool
  | TList of ty
  | TTuple of ty list
  | TFun of (ty * ty)
  | TVar of type_name

type ty_subst = (type_name * ty) list
type ty_constraints = (ty * ty) list

type ty_env = (Syntax.name * ty) list

exception Unify_error
exception Unbound_error

let rec print_type ppf =
  let open Format in
  function
  | TInt -> pp_print_string ppf "int"
  | TBool -> pp_print_string ppf "bool"
  | TList t -> fprintf ppf "%a list" print_type t
  | TTuple xs ->
    fprintf ppf "@[(%a)@]"
      (pp_print_list
         ~pp_sep:(fun ppf () -> pp_print_string ppf " * ")
         print_type)
      xs
  | TFun (x, e) -> fprintf ppf "(%a) -> %a" print_type x print_type e
  | TVar id -> pp_print_string ppf id

let rec print_ty_subst ppf subst =
  let open Format in
  pp_print_list
    ~pp_sep:(fun ppf () -> pp_print_string ppf "; ")
    (fun ppf (n, ty) ->
      fprintf ppf "(%a, %a)" pp_print_string n print_type ty)
    ppf subst

let rec print_ty_constraints ppf cons =
  let open Format in
  pp_print_list
    ~pp_sep:(fun ppf () -> pp_print_string ppf "; ")
    (fun ppf (ty1, ty2) ->
      fprintf ppf "(%a, %a)" print_type ty1 print_type ty2)
    ppf cons

(*
In order to preserve the expression
    apply_ty_subst (compose_ty_subst s1 s2) ty
  = apply_ty_subst s1 (apply_ty_subst s2 ty),
I refers to TAPL, sec. 22.
*)
let rec apply_ty_subst : ty_subst -> ty -> ty =
 fun subst typ ->
  match typ with
  | TInt -> typ
  | TBool -> typ
  | TList x -> TList (apply_ty_subst subst x)
  | TTuple xs -> TTuple (xs |> List.map (fun x -> apply_ty_subst subst x))
  | TFun (x, e) -> TFun (apply_ty_subst subst x, apply_ty_subst subst e)
  | TVar id -> (
    match List.assoc_opt id subst with
    | Some t -> t
    | None -> typ)

let rec apply_ty_subst_constrains :
    ty_subst -> ty_constraints -> ty_constraints =
 fun subst const ->
  const
  |> List.map (fun (tau1, tau2) ->
         (apply_ty_subst subst tau1, apply_ty_subst subst tau2))

let rec apply_ty_subst_env : ty_subst -> ty_env -> ty_env =
 fun subst tenv ->
  tenv |> List.map (fun (vname, tau) -> (vname, apply_ty_subst subst tau))

let compose_ty_subst : ty_subst -> ty_subst -> ty_subst =
 fun subst1 subst2 ->
  let l1 =
    subst2 |> List.map (fun (id, typ) -> (id, apply_ty_subst subst1 typ))
  in
  let l2 =
    subst1
    |> List.filter_map (fun (id, typ) ->
           if not (List.mem_assoc id subst2) then
             Some (id, typ)
           else
             None)
  in
  l1 @ l2

let rec ftv : ty -> type_name list = function
  | TInt -> []
  | TBool -> []
  | TList x -> ftv x
  | TTuple xs -> xs |> List.concat_map (fun x -> ftv x)
  | TFun (tau1, tau2) -> ftv tau1 @ ftv tau2
  | TVar t -> [ t ]

let rec ty_unify : ty_constraints -> ty_subst = function
  | [] -> []
  | x :: xs -> (
    match x with
    | tau1, tau2 when tau1 = tau2 -> ty_unify xs
    | TList tau1, TList tau2 -> ty_unify ((tau1, tau2) :: xs)
    | TTuple tau1, TTuple tau2 -> ty_unify (List.combine tau1 tau2 @ xs)
    | TFun (tau1, tau1'), TFun (tau2, tau2') ->
      ty_unify ((tau1, tau2) :: (tau1', tau2') :: xs)
    | TVar t, tau
    | tau, TVar t ->
      (* occur check *)
      if List.mem t (ftv tau) then raise Unify_error;
      compose_ty_subst
        (ty_unify @@ apply_ty_subst_constrains [ (t, tau) ] xs)
        [ (t, tau) ]
    | _ -> raise Unify_error)

let global_cnt = ref 0
let new_ty_var : unit -> ty =
 fun () ->
  let cnt = !global_cnt in
  incr global_cnt;
  let id = Printf.sprintf "_t_%d" cnt in
  TVar id

let rec gather_ty_constraints : ty_env -> Syntax.expr -> ty * ty_constraints
    =
 fun env -> function
  | EConst (VInt _) -> (TInt, [])
  | EConst (VBool _) -> (TBool, [])
  | EConst VNil ->
    let a = new_ty_var () in
    (TList a, [])
  | EConst (VCons (car, cdr)) ->
    gather_ty_constraints env (ECons (EConst car, EConst cdr))
  | EConst (VTuple xs) ->
    gather_ty_constraints env
      (ETuple (xs |> List.map (fun e -> Syntax.EConst e)))
  | EConst (VVal (x, _, _))
  | EConst (VFun (x, _, _))
  | EConst (VRFun (x, _, _, _)) -> (
    match List.assoc_opt x env with
    | Some t -> (t, [])
    | None -> raise Unbound_error)
  | EConst (VRAndFun (i, fns, _)) -> (
    let fi = List.nth fns i |> fun (fi, _, _) -> fi in
    match List.assoc_opt fi env with
    | Some t -> (t, [])
    | None -> raise Unbound_error)
  | EConst (Thunk (e, _)) -> gather_ty_constraints env e
  | ECons (car, cdr) ->
    let t1, c1 = gather_ty_constraints env car in
    let t2, c2 = gather_ty_constraints env cdr in
    (t2, (TList t1, t2) :: c1 @ c2)
  | ETuple xs ->
    let tys, ty_css =
      xs |> List.map (fun e -> gather_ty_constraints env e) |> List.split
    in
    (TTuple tys, List.concat ty_css)
  | EVar x -> (
    match List.assoc_opt x env with
    | Some t -> (t, [])
    | None -> raise Unbound_error)
  | EBin (op, x, y) -> (
    let t1, c1 = gather_ty_constraints env x in
    let t2, c2 = gather_ty_constraints env y in
    match op with
    | OpAdd
    | OpSub
    | OpMul
    | OpDiv ->
      (TInt, (t1, TInt) :: (t2, TInt) :: c1 @ c2)
    | OpEq
    | OpLt ->
      (TBool, (t1, TInt) :: (t2, TInt) :: c1 @ c2)
    | OpLAnd
    | OpLOr ->
      (TBool, (t1, TBool) :: (t2, TBool) :: c1 @ c2))
  | EIfThenElse (cnd, et, ef) ->
    let t1, c1 = gather_ty_constraints env cnd in
    let t2, c2 = gather_ty_constraints env et in
    let t3, c3 = gather_ty_constraints env ef in
    (t2, (t1, TBool) :: (t2, t3) :: c1 @ c2 @ c3)
  | ELet (x, e1, e2) ->
    let t1, c1 = gather_ty_constraints env e1 in
    let env' = (x, t1) :: env in
    let t2, c2 = gather_ty_constraints env' e2 in
    (t2, c1 @ c2)
  | ERLetV (x, e1, e2) ->
    (* Support recursive value *)
    let a = new_ty_var () in
    let env' = (x, a) :: env in
    let t1, c1 = gather_ty_constraints env' e1 in
    let t2, c2 = gather_ty_constraints env' e2 in
    (t2, (t1, a) :: c1 @ c2)
  | ERLet (f, x, e1, e2) ->
    let a = new_ty_var () in
    let b = new_ty_var () in
    let env' = (f, TFun (a, b)) :: env in
    let env1 = (x, a) :: env' in
    let t1, c1 = gather_ty_constraints env1 e1 in
    let t2, c2 = gather_ty_constraints env' e2 in
    (t2, (t1, b) :: c1 @ c2)
  | ERAndLet (fns, e) ->
    let fns' =
      fns
      |> List.map (fun e ->
             let a = new_ty_var () in
             let b = new_ty_var () in
             (e, (a, b)))
    in
    let env' =
      fns'
      |> List.fold_left
           (fun z ((fi, _, _), (a, b)) -> (fi, TFun (a, b)) :: z)
           env
    in
    let c_last =
      fns'
      |> List.fold_left
           (fun z ((_, xi, ei), (a, b)) ->
             let envi = (xi, a) :: env' in
             let ti, ci = gather_ty_constraints envi ei in
             (ti, b) :: ci @ z)
           []
    in
    let t, c = gather_ty_constraints env' e in
    (t, c_last @ c)
  | EMatch (e, tuples) ->
    let a = new_ty_var () in
    let t, c = gather_ty_constraints env e in
    let cs =
      tuples
      |> List.fold_left
           (fun zc (patt, expr) ->
             let tp, ep, cp = gather_ty_constraints_pattern patt in
             let te, ce = gather_ty_constraints (ep @ env) expr in
             (a, te) :: (t, tp) :: cp @ ce @ zc)
           c
    in
    (a, cs)
  | EFun (x, e) ->
    let a = new_ty_var () in
    let env' = (x, a) :: env in
    let t, c = gather_ty_constraints env' e in
    (TFun (a, t), c)
  | EApp (e1, e2) ->
    let t1, c1 = gather_ty_constraints env e1 in
    let t2, c2 = gather_ty_constraints env e2 in
    let a = new_ty_var () in
    (a, (t1, TFun (t2, a)) :: c1 @ c2)

and gather_ty_constraints_pattern :
    Syntax.patt -> ty * ty_env * ty_constraints = function
  | PConstInt _ -> (TInt, [], [])
  | PConstBool _ -> (TBool, [], [])
  | PNil ->
    let a = new_ty_var () in
    (TList a, [], [])
  | PCons (car, cdr) ->
    let t1, e1, c1 = gather_ty_constraints_pattern car in
    let t2, e2, c2 = gather_ty_constraints_pattern cdr in
    (t2, e1 @ e2, (TList t1, t2) :: c1 @ c2)
  | PTuple xs ->
    xs
    |> List.map (fun x ->
           let ti, ei, ci = gather_ty_constraints_pattern x in
           ((ti, ei), ci))
    |> List.split
    |> fun (l12, l3) ->
    l12 |> List.split |> fun (l1, l2) ->
    (TTuple l1, l2 |> List.concat, l3 |> List.concat)
  | PVar x ->
    let a = new_ty_var () in
    (a, [ (x, a) ], [])

let infer_expr : ty_env -> Syntax.expr -> ty * ty_env =
 fun tenv expr ->
  let t, c = gather_ty_constraints tenv expr in
  let s = ty_unify c in
  (apply_ty_subst s t, apply_ty_subst_env s tenv)

let infer_cmd : ty_env -> Syntax.command -> ty * ty_env =
 fun tenv -> function
  | CExp expr -> infer_expr tenv expr
  | CLet (name, expr) -> (
    match infer_expr tenv expr with
    | e1, e2 -> (e1, (name, e1) :: e2))
