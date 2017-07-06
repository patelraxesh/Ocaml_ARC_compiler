open Types
open Instruction
open Expr
open Pretty
open Printf


let purity_env (prog : 'a aprogram) : (string, bool) Hashtbl.t =
  let ans : (string, bool) Hashtbl.t = Hashtbl.create 0 in
  let rec helpA (aexp : 'a aexpr) : bool =
    match aexp with
    | ALet(id, value, body, _) -> let pureval = (helpC value) in
      (Hashtbl.add ans id pureval);
      pureval && helpA body
(* if the value is pure and int/bool, add to a list, use in the body. else leave as-is and go to body *)
    | ALetRec(bindlist, body, tag) -> false
    | ASeq(first, body, tag) -> false
    | ACExpr(expr) -> (helpC expr)
  (* is the given expression pure or not?
  Also, update ans with any bindings you encounter. *)
  and helpC (cexp : 'a cexpr) : bool =
    match cexp with
    | CIf(cnd, thn, els, _) ->
      (helpI cnd) && (helpA thn) && (helpA els)
    | CPrim1(prim, imm, _) -> (
      match prim with
      | Print -> false
      | PrintStack -> false
      | _ -> helpI imm)
    | CPrim2(prim2, lef, rig, _) ->
      (helpI lef) && (helpI rig)
    | CImmExpr(i) -> helpI i
    | CApp(fnval, args, _) -> false (* fixme *)
    | CLambda(arg_ids, abody, _) -> false (* fixme *)
    | CTuple(items, _) -> false
    | CGetItem(_, _, _) -> false
    | CSetItem(_,_,_,_) -> false

  and helpI (imm : 'a immexpr) : bool = (
    match imm with
    | ImmNum(_, _) -> true
    | ImmBool(_, _) -> true
    | ImmId(valu, _) -> (Hashtbl.mem ans valu))
  in
  ignore(helpA prog);
ans

(* Define a function
   let purity = purity_env prog in
   ...
   that detects whether any definitions are not subsequently used, and eliminates them.
   This interacts with purity as well; if a defining expression is impure, then the ALet
   should be turned into an ASeq instead of completely discarding the expression.
*)
let contains_identifier (id : string) (prog : 'a aprogram) : bool =
  let rec helpA (id : string) (prog : 'a aexpr) : bool =
    match prog with
    | ALet(i, value, body, tag) -> (
        id = i || (helpC id value) || (helpA id body))
    (* if the value is pure and int/bool, add to a list, use in the body. else leave as-is and go to body *)
    | ALetRec(bindlist, body, tag) -> (helpA id body) (* Don't check the bindlist—it's a redefinition, not a usage. *)
    | ASeq(first, body, tag) -> (helpC id first) || (helpA id body)
    | ACExpr(expr) -> (helpC id expr)
  and helpC (id : string) (e : 'a cexpr) : bool =
    match e with
    | CIf(cnd, thn, els, _) ->
      (helpI id cnd) || (helpA id thn) || (helpA id els)
    | CPrim1(prim, imm, _) -> (helpI id imm)
    | CPrim2(prim2, lef, rig, _) -> (helpI id lef) || helpI id rig
    | CImmExpr(i) -> helpI id i
    | CApp(fnval, args, _) -> helpI id fnval || (List.exists (fun a ->  helpI id a) args)
    | CLambda(arg_ids, abody, _) -> (List.mem id arg_ids) || helpA id abody
    | CTuple(items, _) -> (List.exists (fun a ->  helpI id a) items)
    | CGetItem(tup, idx, _) -> helpI id tup || helpI id idx
    | CSetItem(tup, idx, nu, _) -> helpI id tup || helpI id idx || helpI id nu
  and helpI (id : string) (e : 'a immexpr) : bool =
    match e with
    | ImmId(i, _) -> i = id
    | _ -> false in

helpA id prog

let rec cse (prog : tag aprogram) : unit aprogram =
  let purity = purity_env prog in
  let equiv_exprs : (simple_expr, simple_expr) Hashtbl.t = Hashtbl.create 0 in
  let purehuh (id : string) : bool =
    (Hashtbl.mem purity id) in
  let rec simple_to_cexpr simple =
    let rec s_to_imm s =
      match s with
      | Id n -> ImmId(n, ())
      | Num n -> ImmNum(n, ())
      | Bool b -> ImmBool(b, ())
      | _ -> failwith "Impossible"
    in
    match simple with
    | Prim1(op, arg) -> CPrim1(op, s_to_imm arg, ())
    | Prim2(op, left, right) -> CPrim2(op, s_to_imm left, s_to_imm right, ())
    | App(f, args) -> CApp(s_to_imm f, List.map s_to_imm args, ())
    | _ -> CImmExpr (s_to_imm simple)
  in
  let imm_to_simple i =
    match i with
    | ImmId(n, _) -> Id n
    | ImmNum(n, _) -> Num n
    | ImmBool(b, _) -> Bool b
  in
  let cexpr_to_simple_opt cexp =
    match cexp with
    | CPrim1(op, arg, _) -> Some (Prim1(op, imm_to_simple arg))
    | CPrim2(op, left, right, _) -> Some (Prim2(op, imm_to_simple left, imm_to_simple right))
    | CApp(f, args, _) -> Some (App(imm_to_simple f, List.map imm_to_simple args))
    | CImmExpr i -> Some (imm_to_simple i)
    | _ -> None
  in
  let canonical_version (e : simple_expr) : simple_expr =
    let find_kind (tab : ('a, 'a) Hashtbl.t) (input : 'a) : 'a =
      if (Hashtbl.mem equiv_exprs input) then (Hashtbl.find equiv_exprs input) else input in
    match e with
    | Id(s) -> (find_kind equiv_exprs e)
    | Prim1(prim, sexpr) -> (find_kind equiv_exprs (Prim1(prim, (find_kind equiv_exprs sexpr))))
    | Prim2(prim, sexpr, sexpr2) -> (find_kind equiv_exprs (Prim2(prim, (find_kind equiv_exprs sexpr), (find_kind equiv_exprs sexpr2))))
    | App(sexpr, sexprlist) -> (find_kind equiv_exprs (App((find_kind equiv_exprs sexpr), (List.map (fun f ->  (find_kind equiv_exprs f)) sexprlist))))
    | _ -> e in
  let rec helpA (prog : tag aprogram) : unit aprogram =
    match prog with
    | ALet(ide, valu, body, _) -> (
        let rhs_option = cexpr_to_simple_opt valu in
        let p = (purehuh ide) in
        let swappable = (p && (Option.is_some rhs_option)) in
        let replacement_valu = if swappable then Some(canonical_version (Option.get rhs_option)) else rhs_option in
        let value_to_place = if (Option.is_some replacement_valu) then simple_to_cexpr (Option.get replacement_valu) else untagC valu in
        if swappable then Hashtbl.add equiv_exprs (Option.get replacement_valu) (Id ide);
        ALet(ide, value_to_place, (helpA body), ()));
    | ALetRec(cfn_binds, body, _) ->  ALetRec((List.map
                                                 (fun (str, ce) -> (str, (helpC ce)))
                                                 cfn_binds),
                                              helpA body,
                                              ())
    | ASeq(c, a, _) -> ASeq(helpC c, helpA a, ())
    | ACExpr(c) -> ACExpr(helpC c)
  and helpC (e : tag cexpr) : unit cexpr =
    match e with
    | CIf(ifc, athn, aels, _) -> CIf(iuntag ifc, (helpA athn), (helpA aels), ())
    | CLambda(args, aexp, _) -> CLambda(args, (helpA aexp), ())
    | _ -> (untagC e) in
  (helpA prog)

let rec dae (prog : tag aprogram) : unit aprogram =
  let purity = purity_env prog in
  let purehuh (id : string) : bool =
    (Hashtbl.mem purity id) in
  let rec helpA (prog : tag aprogram) : unit aprogram =
  match prog with
  | ALet(id, valu, body, _) -> (
    let p = (purehuh id) in
    let used = (contains_identifier id body) in
    let new_body = (helpA body) in
    let new_val = (helpC valu) in
    if used then ALet(id, new_val, new_body, ()) else (if p then new_body else (ASeq(new_val, new_body, ()))))
  | ALetRec(cfn_binds, body, _) -> let used_bindings = (List.filter (fun (str, lambda) -> contains_identifier str prog) cfn_binds) in
                                    ALetRec((List.map (fun (str, lambda) -> (str, untagC lambda)) used_bindings), (dae body), ())
  | ASeq(c, a, _) -> ASeq(helpC c, helpA a, ())
  | ACExpr(c) -> ACExpr(helpC c)
  and helpC (e : 'a cexpr) : unit cexpr =
    match e with
    | CIf(ifc, athn, aels, _) -> CIf(iuntag ifc, (helpA athn), (helpA aels), ())
    | CLambda(args, aexp, _) -> CLambda(args, (helpA aexp), ())
    | _ -> (untagC e) in
  (helpA prog)

let rec const_fold (prog : tag aprogram) : unit aprogram =
  let pure = (purity_env prog) in
  let not_id (e : 'a immexpr) : bool =
    match e with
    | ImmNum(i, _) -> true
    | ImmBool(i, _) -> true
    | ImmId(i, _) -> false in
  let rec force_num (e : unit immexpr) : int =
    match e with
    | ImmNum(i, _) -> i
    | _ -> failwith "Error: expected a number, but found something else" in
  let rec force_bool (e : unit immexpr) : bool =
    match e with
    | ImmBool(v, _) -> v
    | _ -> failwith "Error: expected a number, but found something else" in
  let prop_raw (e : tag immexpr) (pure_imm_vals : unit immexpr envt) : unit immexpr =
    match e with
  | ImmNum(i, _) -> ImmNum(i, ())
  | ImmBool(b, _) -> ImmBool(b, ())
  | ImmId(id, _) -> if (List.mem_assoc id pure_imm_vals) then (List.assoc id pure_imm_vals) else ImmId(id, ()) in
  let rec helpE (e : tag immexpr) (pure_imm_vals : unit immexpr envt) : unit immexpr option =
    match e with
    | ImmNum(i, _) -> Some(ImmNum(i, ()))
    | ImmBool(b, _) -> Some(ImmBool(b, ()))
    | ImmId(id, _) -> if (List.mem_assoc id pure_imm_vals) then Some((List.assoc id pure_imm_vals)) else None
  and helpC (e : tag cexpr) (env : unit immexpr envt) : unit cexpr =
    match e with
    | CPrim1(primitive, immexpr, tag) -> (
      let mayb_const = (helpE immexpr env) in
      if (Option.is_none mayb_const) then CPrim1(primitive, (iuntag immexpr), ())
      else let const = (Option.get mayb_const) in (
        match primitive with
        | Print -> CPrim1(Print, (iuntag immexpr), ())
        | PrintStack -> CPrim1(primitive, (iuntag immexpr), ())
        | _ ->
        CImmExpr(match primitive with
        | Add1 -> ImmNum((force_num const) + 1, ())
        | Sub1 -> ImmNum((force_num const) - 1, ())
        | IsNum -> (match const with
            | ImmNum(_, _) -> ImmBool(true, ())
            | ImmBool(_, _) -> ImmBool(false, ())
            | _ -> failwith "Impossible"
          )
        | IsBool -> (match const with
            | ImmNum(_, _) -> ImmBool(false, ())
            | ImmBool(_, _) -> ImmBool(true, ())
            | _ -> failwith "Impossible"
          )
        | IsTuple -> ImmBool(false, ())
        | Not -> if (force_bool const) then ImmBool(false, ()) else ImmBool(true, ())
        | _ -> failwith "Impossible!")))
    | CIf(if_e, athen, aelse, tag) -> CIf((prop_raw if_e env),
                                          (helpA athen env),
                                          (helpA aelse env), ())
    | CTuple(items, tag) -> CTuple((List.map (fun (a) -> (prop_raw a env)) items), ())
    | CGetItem(tupleimm, idximm, tag) -> CGetItem(iuntag tupleimm, prop_raw idximm env, ())
    | CSetItem(tupleimm, idximm, newval, tag) -> CSetItem(iuntag tupleimm, prop_raw idximm env, prop_raw newval env, ())
    | CLambda(argnames, afnbody, tag) -> CLambda(argnames, (helpA afnbody env), ())
    | CImmExpr(immexpr) -> CImmExpr(prop_raw immexpr env)
    | CApp(funimm, args, tag) -> CApp(iuntag funimm, (List.map (fun (a) -> (prop_raw a env)) args), ())
    | CPrim2(prim2, immleft, immright, tag) ->
      let left_side = (prop_raw immleft env) in
      let right_side = (prop_raw immright env) in
      let simplifiable = (not_id left_side) && (not_id right_side) in
      if (simplifiable) then
        match prim2 with
        | Plus -> CImmExpr(ImmNum((force_num left_side) + (force_num right_side), ()))
        | Minus -> CImmExpr(ImmNum((force_num left_side) - (force_num right_side), ()))
        | Times -> CImmExpr(ImmNum((force_num left_side) * (force_num right_side), ()))
        | Less -> CImmExpr(ImmBool((force_num left_side) < (force_num right_side), ()))
        | Greater -> CImmExpr(ImmBool((force_num left_side) > (force_num right_side), ()))
        | LessEq -> CImmExpr(ImmBool((force_num left_side) <= (force_num right_side), ()))
        | GreaterEq -> CImmExpr(ImmBool((force_num left_side) >= (force_num right_side), ()))
        | Eq -> CImmExpr(ImmBool((force_num left_side) <= (force_num right_side), ()))
        | And -> CImmExpr(ImmBool((force_bool left_side) && (force_bool right_side), ()))
        | Or -> CImmExpr(ImmBool((force_bool left_side) || (force_bool right_side), ()))
      else (if ((not_id left_side) || (not_id right_side)) then (let (simple_side, id_side) = if (not_id left_side) then (left_side, right_side) else (right_side, left_side) in
        match (prim2, simple_side) with
        | And, ImmBool(true, _) -> CImmExpr(id_side)
        | Or, ImmBool(false, _) ->  CImmExpr(id_side)
        | Plus, ImmNum(0, _) -> CImmExpr(id_side)
        | Minus, ImmNum(0, _) -> CImmExpr(id_side)
        | Times, ImmNum(1, _) -> CImmExpr(id_side)
      (* Here be dragons! We cannot use the approach below without checking for the purity
        of the ellided expression. Therefore, they're commented out for now. *)
        (* | And, ImmBool(false, _) -> CImmExpr(ImmBool(false, ()))
        | Or, ImmBool(true, _) ->  CImmExpr(ImmBool(true, ()))
        | Times, ImmNum(0, _) ->  CImmExpr(ImmNum(0, ())) *)
        | _, _ -> CPrim2(prim2, left_side, right_side, ()))
            else CPrim2(prim2, left_side, right_side, ()))
  and helpA (prog : tag aexpr) (env : unit immexpr envt) : unit aprogram =
    let is_imm (expr : 'a cexpr) : bool =
      match expr with
      | CImmExpr(_) -> true
      | _ -> false in
    let imm_unwrap (expr : 'a cexpr) : unit immexpr =
      match expr with
      | CImmExpr(a) -> a
      | _ -> failwith "Impossible!" in
  match prog with
  | ALet(id, value, body, tag) -> (
      let valu = (helpC value env) in
      let new_env : unit immexpr envt = (if (Hashtbl.mem pure id) && (is_imm valu) then (id, (imm_unwrap valu))::env else env) in
      let body_val = (helpA body new_env) in
      ALet(id, valu, body_val, ()))
  (* if the value is pure and int/bool, add to a list, use in the body. else leave as-is and go to body *)
  | ALetRec(bindlist, body, tag) -> let new_binds = List.map (fun (str, cex) -> (str, (helpC cex env))) bindlist in
    ALetRec(new_binds, (helpA body env), ())
  | ASeq(first, body, tag) -> ASeq(helpC first env, helpA body env, ())
  | ACExpr(expr) -> ACExpr(helpC expr env)
  in
  helpA prog []

let optimize (prog : tag aprogram) (verbose : bool) : unit aprogram =
  let const_prog = (const_fold prog) in
  let cse_prog = atag (cse (atag const_prog)) in
  let dae_prog = (dae (atag cse_prog)) in
  (if verbose
    then begin
      printf "Const/tagged:\n%s\n" (string_of_aprogram const_prog);
      printf "CSE/tagged:\n%s\n" (string_of_aprogram (atag cse_prog));
      printf "DAE/tagged:\n%s\n" (string_of_aprogram (atag dae_prog));
     end
   else ());
  dae_prog
  (* const_prog *)


let free_vars (e : 'a aexpr) : string list =
  let rec helpA (bound : string list) (e : 'a aexpr) : string list =
     match e with
     | ASeq(fst, rest, _) ->
        helpC bound fst @ helpA bound rest
     | ALet(name, binding, body, _) ->
       (helpC bound binding) (* all the free variables in the binding, plus *)
       (* all the free variables in the body, except the name itself *)
       @ (helpA (name :: bound) body)
     | ALetRec(bindings, body, _) ->
        let names = List.map fst bindings in
        let new_bound = (names @ bound) in
        (helpA new_bound body) @ List.flatten (List.map (fun binding -> helpC new_bound (snd binding)) bindings)
     | ACExpr c -> helpC bound c
  and helpC (bound : string list) (e : 'a cexpr) : string list =
    match e with
    | CLambda(args, body, _) ->
      helpA (args @ bound) body
    | CIf(cond, thn, els, _) ->
      helpI bound cond @ helpA bound thn @ helpA bound els
    | CPrim1(_, arg, _) -> helpI bound arg
    | CPrim2(_, left, right, _) -> helpI bound left @ helpI bound right
    | CApp(fn, args, _) ->
      (helpI bound fn) @ (List.flatten (List.map (fun arg -> helpI bound arg) args))
    | CTuple(vals, _) -> List.flatten (List.map (fun v -> helpI bound v) vals)
    | CGetItem(tup, idx, _) -> helpI bound tup @ helpI bound idx
    | CSetItem(tup, idx, rhs, _) -> helpI bound tup @ helpI bound idx @ helpI bound rhs
    | CImmExpr i -> helpI bound i
  and helpI (bound : string list) (e : 'a immexpr) : string list =
    match e with
    | ImmId(name, _) ->
      (* a name is free if it is not bound *)
      if List.mem name bound then [] else [name]
    | _ -> []
  in List.sort_uniq String.compare (helpA [] e)
;;
