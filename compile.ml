open Types
open Printf
open Instruction
open Expr
open Pretty
open Optimize

(* Add or change these constants as needed *)
let err_COMP_NOT_NUM   = 1
let err_ARITH_NOT_NUM  = 2
let err_LOGIC_NOT_BOOL = 3
let err_IF_NOT_BOOL    = 4
let err_OVERFLOW       = 5
let err_GET_NOT_TUPLE  = 6
let err_GET_LOW_INDEX  = 7
let err_GET_HIGH_INDEX = 8
let err_INDEX_NOT_NUM  = 9


let const_true = HexConst (0xFFFFFFFF)
let const_false = HexConst(0x7FFFFFFF)
let bool_mask = HexConst(0x80000000)
let tag_as_bool = HexConst(0x00000001)

let rec replicate x i =
  if i = 0 then []
  else x :: (replicate x (i - 1))

(* Zip two lists that are of the same length *)
let rec zip (ays : 'a list) (bees : 'b list) : ('a * 'b) list =
  match ays,bees with
  | (a::ax),(b::bx) -> (a,b)::(zip ax bx)
  | [],[] -> []
  | _ -> failwith "Someone didn't read the documentation for this function, and gave it unequal lists."

(* Unzip one association list into two lists of the same length *)
let unzip (ab : ('a * 'b) list) : ('a list) * ('b list) =
  ((List.map fst ab),(List.map snd ab))

let andmap (items : 'a list) (predicate : ('a -> bool)) : bool =
  (List.fold_left (&&) (true) (List.map predicate items))

let ormap (items : 'a list) (predicate : ('a -> bool)) : bool =
  (List.fold_left (||) (false) (List.map predicate items))

(* FINISH THIS FUNCTION WITH THE WELL-FORMEDNESS FROM FER-DE-LANCE *)
let well_formed (p : (Lexing.position * Lexing.position) program) builtins : exn list =
  let rec wf_E e (env : sourcespan envt) =
    match e with
    | EBool _ -> []
    | ENumber(n, loc) ->
       if n > 1073741823 || n < -1073741824 then [Overflow(n, loc)] else []
    | EId (x, loc) ->
       (try ignore (List.assoc x env); []
        with Not_found ->
             [UnboundId(x, loc)])
    | EPrim1(_, e, _) -> wf_E e env
    | EPrim2(_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf(c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ETuple(vals, _) -> List.concat (List.map (fun e -> wf_E e env) vals)
    | EGetItem(tup, idx, _) -> wf_E tup env @ wf_E idx env
    | ESetItem(tup, idx, rhs, _) -> wf_E tup env @ wf_E idx env @ wf_E rhs env
    | ESeq(stmts, _) -> List.flatten (List.map (fun s -> wf_E s env) stmts)
    | ELet(binds, body, _) ->
       let rec dupe x binds =
         match binds with
         | [] -> None
         | (y, _, loc)::_ when x = y -> Some loc
         | _::rest -> dupe x rest in
       let rec process_binds rem_binds env =
         match rem_binds with
         | [] -> (env, [])
         | (x, e, loc)::rest ->
            let shadow =
              match dupe x rest with
              | Some where -> [DuplicateId(x, where, loc)]
              | None ->
                 try
                   let existing = List.assoc x env in [ShadowId(x, loc, existing)]
                 with Not_found -> [] in
            let errs_e = wf_E e env in
            let new_env = (x, loc)::env in
            let (newer_env, errs) = process_binds rest new_env in
            (newer_env, (shadow @ errs_e @ errs)) in
       let (env2, errs) = process_binds binds env in
       errs @ wf_E body env2
    | ELetRec(binds, body, _) ->
      let rec dupe x binds =
        match binds with
        | [] -> None
        | (y, _, loc)::_ when x = y -> Some loc
        | _::rest -> dupe x rest in
      let rec process_binds rem_binds env =
        match rem_binds with
        | [] -> (env, [])
        | (x, e, loc)::rest ->
          let lambdaerror = match e with
            | ELambda(_, _, _) -> []
            | _ -> [LetRecNonFunction(x, loc)] in
            let shadow =
              match dupe x rest with
              | Some where -> [DuplicateId(x, where, loc)]
              | None ->
                try
                  let existing = List.assoc x env in [ShadowId(x, loc, existing)]
                with Not_found -> [] in
          let errs_e = wf_E e ((List.map (fun (x, e, loc) -> (x, loc)) rem_binds ) @ env) in
          let new_env = (x, loc)::env in
          let (newer_env, errs) = process_binds rest new_env in
          (newer_env, (lambdaerror @ shadow @ errs_e @ errs)) in
      let (env2, errs) = process_binds binds env in
      errs @ wf_E body env2
    | ELambda(args, body, _) ->
    wf_E body (args @ env)
    | EApp(func, args, loc) ->
       (wf_E func env) @ List.concat (List.map (fun e -> wf_E e env) args)
  in
  wf_E p builtins
;;


type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let next = ref 0 in
  let rec let_inner_tag () =
    next := !next + 1;
    !next in
  let rec helpP (p : tag program) : unit aprogram = helpA p
  and helpC (e : tag expr) : (unit cexpr * unit anf_bind list) =
    match e with
    | EPrim1(op, arg, _) ->
       let (arg_imm, arg_setup) = helpI arg in
       (CPrim1(op, arg_imm, ()), arg_setup)
    | EPrim2(op, left, right, _) ->
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (CPrim2(op, left_imm, right_imm, ()), left_setup @ right_setup)
    | EIf(cond, _then, _else, _) ->
       let (cond_imm, cond_setup) = helpI cond in
       (CIf(cond_imm, helpA _then, helpA _else, ()), cond_setup)
    | ESeq([], _) -> failwith "Impossible by syntax"
    | ESeq([stmt], _) -> helpC stmt
    | ESeq(fst :: rest, tag) ->
       let (fst_ans, fst_setup) = helpC fst in
       let (rest_ans, rest_setup) = helpC (ESeq(rest, tag)) in
       (rest_ans, fst_setup @ [BSeq fst_ans] @ rest_setup)
    | ELet([], body, _) -> helpC body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpC (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet (bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, _) ->
       let (names, new_binds_setup) = List.split (List.map (fun (name, rhs, _) -> (name, helpC rhs)) binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (body_ans, (BLetRec (List.combine names new_binds)) :: body_setup)
    | ELambda(args, body, _) ->
       (CLambda(List.map fst args, helpA body, ()), [])
    | EApp(func, args, _) ->
       let (new_func, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CApp(new_func, new_args, ()), func_setup @ List.concat new_setup)
    | ETuple(args, _) ->
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (CTuple(new_args, ()), List.concat new_setup)
    | EGetItem(tup, idx, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (CGetItem(tup_imm, idx_imm, ()), tup_setup @ idx_setup)
    | ESetItem(tup, idx, rhs, _) ->
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (rhs_imm, rhs_setup) = helpI rhs in
       (CSetItem(tup_imm, idx_imm, rhs_imm, ()), tup_setup @ idx_setup @ rhs_setup)
    | _ -> let (imm, setup) = helpI e in (CImmExpr imm, setup)

  and helpI (e : tag expr) : (unit immexpr * unit anf_bind list) =
    match e with
    | ENumber(n, _) -> (ImmNum(n, ()), [])
    | EBool(b, _) -> (ImmBool(b, ()), [])
    | EId(name, _) -> (ImmId(name, ()), [])

    | EPrim1(op, arg, tag) ->
       let tmp = sprintf "unary_%d" tag in
       let (arg_imm, arg_setup) = helpI arg in
       (ImmId(tmp, ()), arg_setup @ [BLet(tmp, CPrim1(op, arg_imm, ()))])
    | EPrim2(op, left, right, tag) ->
       let tmp = sprintf "binop_%d" tag in
       let (left_imm, left_setup) = helpI left in
       let (right_imm, right_setup) = helpI right in
       (ImmId(tmp, ()), left_setup @ right_setup @ [BLet(tmp, CPrim2(op, left_imm, right_imm, ()))])
    | EIf(cond, _then, _else, tag) ->
       let tmp = sprintf "if_%d" tag in
       let (cond_imm, cond_setup) = helpI cond in
       (ImmId(tmp, ()), cond_setup @ [BLet(tmp, CIf(cond_imm, helpA _then, helpA _else, ()))])
    | EApp(func, args, tag) ->
       let tmp = sprintf "app_%d" tag in
       let (new_func, func_setup) = helpI func in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (func_setup @ List.concat new_setup) @ [BLet(tmp, CApp(new_func, new_args, ()))])
    | ESeq([], _) -> failwith "Impossible by syntax"
    | ESeq([stmt], _) -> helpI stmt
    | ESeq(fst :: rest, tag) ->
       let (fst_ans, fst_setup) = helpC fst in
       let (rest_ans, rest_setup) = helpI (ESeq(rest, tag)) in
       (rest_ans, fst_setup @ [BSeq fst_ans] @ rest_setup)
    | ELet([], body, _) -> helpI body
    | ELet((bind, exp, _)::rest, body, pos) ->
       let (exp_ans, exp_setup) = helpC exp in
       let (body_ans, body_setup) = helpI (ELet(rest, body, pos)) in
       (body_ans, exp_setup @ [BLet(bind, exp_ans)] @ body_setup)
    | ELetRec(binds, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       let (names, new_binds_setup) = List.split (List.map (fun (name, rhs, _) -> (name, helpC rhs)) binds) in
       let (new_binds, new_setup) = List.split new_binds_setup in
       let (body_ans, body_setup) = helpC body in
       (ImmId(tmp, ()), (List.concat new_setup)
                        @ [BLetRec (List.combine names new_binds)]
                        @ body_setup
                        @ [BLet(tmp, body_ans)])
    | ELambda(args, body, tag) ->
       let tmp = sprintf "lam_%d" tag in
       (ImmId(tmp, ()), [BLet(tmp, CLambda(List.map fst args, helpA body, ()))])
    | ETuple(args, tag) ->
       let tmp = sprintf "tup_%d" tag in
       let (new_args, new_setup) = List.split (List.map helpI args) in
       (ImmId(tmp, ()), (List.concat new_setup) @ [BLet(tmp, CTuple(new_args, ()))])
    | EGetItem(tup, idx, tag) ->
       let tmp = sprintf "get_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ [BLet(tmp, CGetItem(tup_imm, idx_imm, ()))])
    | ESetItem(tup, idx, rhs, tag) ->
       let tmp = sprintf "set_%d" tag in
       let (tup_imm, tup_setup) = helpI tup in
       let (idx_imm, idx_setup) = helpI idx in
       let (rhs_imm, rhs_setup) = helpI rhs in
       (ImmId(tmp, ()), tup_setup @ idx_setup @ rhs_setup @ [BLet(tmp, CSetItem(tup_imm, idx_imm, rhs_imm, ()))])
  and helpA e : unit aexpr =
    (* cexpr / unit anf_bind list *)
    let (ans, ans_setup) = helpC e in
    let valu = (sprintf "inner_let_%d" (let_inner_tag())) in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq(exp) -> ASeq(exp, body, ())
        | BLet(name, exp) -> ALet(name, exp, body, ())
        | BLetRec(names) -> ALetRec(names, body, ()))
      ans_setup (ALet(valu, ans, (ACExpr(CImmExpr(ImmId(valu, ())))), ()))
  in
  helpP p
;;

let reserve size tag =
  [
    IPush(Const(size)); (* bytes_needed in C *)
    ICall("allocate");
    IAdd(Reg(STACK_TOP_R), Const(4)); (* clean up after call *)
    IMov(Reg(HEAP_POINTER_R), Reg(EAX));
  ];;

let decrement pointer =
  [
    ILineComment("Here we decrement stuff");
    IMov(Reg(EBX), Reg(EAX)); (* Store EAX value temporarily in EBX *)
    IPush(Sized(DWORD_PTR, pointer)); (* bytes_needed in C *)
    ICall("decrement_pointer");
    IAdd(Reg(STACK_TOP_R), Const(4)); (* clean up after call *)
    IMov(Reg(EAX), Reg(EBX)); (* Restore EAX value back from EBX *)
  ];;

let let_increment (id : string) (env : arg envt) : instruction list =
  let pointer = (List.assoc id env) in
  [IMov(Reg(EBX), Reg(EAX)); (* Store EAX value temporarily in EBX *)
   IPush(Sized(DWORD_PTR, pointer));
   ICall("increment_pointer");
   (* IAdd(Reg(STACK_TOP_R), Const(4)); *)
   IMov(Reg(EAX), Reg(EBX)); (* Restore EAX value back from EBX *)

  ]

let tup_increment (id : Instruction.arg) : instruction list =
  let pointer = id in
  [IMov(Reg(EBX), Reg(EAX)); (* Store EAX value temporarily in EBX *)
   IPush(Sized(DWORD_PTR, pointer));
   ICall("increment_pointer");
   (* IAdd(Reg(STACK_TOP_R), Const(4)); *)
   IMov(Reg(EAX), Reg(EBX)); (* Restore EAX value back from EBX *)

  ]

let deallocate pointer tag =
  [
    IPush(Const(pointer)); (* bytes_needed in C *)
    ICall("dereference_pointer");
    IAdd(Reg(STACK_TOP_R), Const(4)); (* clean up after call *)
    IMov(Reg(HEAP_POINTER_R), Reg(EAX));
  ];;

let rec find (ls : 'a envt) (x : string) : 'a =
  match ls with
  | [] -> failwith (sprintf "Name %s not found" x)
  | (y,v)::rest ->
    if y = x then v else find rest x


let rec max_l (l : int list) : int =
  match l with
  | [i] -> i
  | i::j -> (max i (max_l j))
  | [] -> failwith "empty"

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT -- THE ONLY NEW CODE IS CSetItem and ALet *)
let count_vars e =
  let rec helpA e =
    match e with
    | ALet(_, bind, body, _) -> 1 + (max (helpC bind) (helpA body))
    | ACExpr e -> helpC e
    | ALetRec(bind, body, _) -> 1 + (max_l (List.map (fun (id, bin) -> (helpC bin)) bind @ [(helpA body)]))
    | ASeq(body, last, _) -> 1 + (max (helpC body) (helpA last))
  and helpC e =
    match e with
    | CIf(_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in helpA e

let rec compile_fun fun_name args e (closed_vars : string list) : (instruction list * instruction list * instruction list * instruction list) =
  let args_env = List.mapi (fun i a -> (a, RegOffset(word_size * (i + 3), STACK_FRAME_LOC_R))) args in
  (* this next line is wrong, as is the one on 364—I'm missing a step here in placing these on the stack *)
  (* I can get some tests to pass by increasing the number added to i, but this is not a good idea and obviously fucks things up *)
  let closed_env = List.mapi (fun i a -> a, RegOffset(word_size* ~-1 *(i+1), STACK_FRAME_LOC_R)) closed_vars in
  let compiled = (compile_aexpr e 1 (closed_env @ args_env) (List.length args + List.length closed_vars)) in
  let count_local_vars = count_vars e in
  (* let pop_args =  *)
  (([
      ILabel(fun_name);
      ILineComment("Function prologue");
      IPush(Reg(STACK_FRAME_LOC_R));
      IMov(Reg(STACK_FRAME_LOC_R), Reg(STACK_TOP_R));
      (* IMov(Reg(EAX), RegOffset(12, STACK_FRAME_LOC_R)); *)
    ] @ (List.flatten (List.mapi (fun i _ -> [IMov(Reg(ECX), RegOffset(4*(i+1)+3, EAX));
                                              IMov((find closed_env (List.nth closed_vars i)), Reg(ECX))]) closed_vars))
      (* @ List.flatten (List.mapi (fun _ i -> [IMov(Reg(ECX), RegOffset(4*i+3, EAX));
                              IMov(RegOffset(-4*i-8, STACK_FRAME_LOC_R), Reg(ECX))]) closed_vars) *)

      (* IMov(Reg(ECX), RegOffset(3, EAX));
         IMov(RegOffset(-8, STACK_FRAME_LOC_R), Reg(ECX));
         IMov(Reg(ECX), RegOffset(7, EAX));
         IMov(RegOffset(-12, STACK_FRAME_LOC_R), Reg(ECX)); *)
    ),
   (replicate (IPush(Sized(DWORD_PTR, HexConst(0xDEADBEEF)))) count_local_vars),
   ([ ILineComment("Function body") ]
    @ compiled),
   [
     ILineComment("Function epilogue");
     IMov(Reg(STACK_TOP_R), Reg(STACK_FRAME_LOC_R));
     IPop(Reg(STACK_FRAME_LOC_R));
     IInstrComment(IRet, sprintf "End of %s" fun_name)
   ])
and mov_if_needed dest src =
  if dest = src then []
  else [ IMov(dest, src) ]
and check_num err arg =
  [
    ITest(Sized(DWORD_PTR, arg), HexConst(0x00000001));
    IJnz(err)
  ]
and check_nums err left right = check_num err left @ check_num err right
and check_number err scratch arg =
  (mov_if_needed scratch arg) @
  [
    ITest(scratch, HexConst(0x00000001));
    IJnz(err)
  ]
and check_tuple err scratch arg =
  (mov_if_needed scratch arg) @
  [ IAnd(scratch, HexConst(0x00000007));
    ICmp(scratch, HexConst(0x00000001));
    IJne(err)
  ]
and check_tuple_index scratch tuple idx =
  [
    IMov(scratch, Const(0));
    ICmp(scratch, idx);
    IJg("err_get_low_index");
  ] @ (mov_if_needed (Reg ECX) tuple) @
  [
    ISub(Reg(ECX), Const(1));
    IMov(scratch, RegOffset(0, ECX));
    IAdd(Reg(ECX), Const(1));
    ISub(scratch, Const(1));
    IMul(scratch, Const(2));
    ICmp(scratch, idx);
    IJl("err_get_high_index");
  ]
(* (mov_if_needed scratch Address(HexConst(tuple-1)) ????? *)
and check_bool err scratch arg =
  (mov_if_needed scratch arg) @
  [
    IAnd(scratch, HexConst(0x00000007));
    ICmp(scratch, HexConst(0x00000007));
    IJne(err)
  ]
and check_bools err scratch left right = check_bool err scratch left @ check_bool err scratch right
and check_overflow err =
  [
    IJo(err);
  ]
and let_helper (id, (e : tag cexpr), body) (si : int) (env : arg envt) (num_args : int) (allocated : arg envt) : instruction list =
  let prelude = compile_cexpr e (si + 1) env num_args in
  let new_env = ((id, RegOffset(~-word_size * si, STACK_FRAME_LOC_R))::env) in
  let new_body = match body with
    | ALet(i, e, b, _) -> (let_helper (i, e, b) (si + 1) new_env num_args ([(id, RegOffset(~-word_size * si, STACK_FRAME_LOC_R))] @ allocated))
    | ACExpr(p) -> (match p with
        | CImmExpr(ImmId(z, _)) -> (compile_cexpr p (si + 1) new_env num_args) @
                                     (let p = (List.remove_assoc z allocated) in
                                     (List.flatten (List.map (fun (eyedee, location) -> (decrement location)) p)))
        | _ -> failwith "Immediates with IDs only")
    | ASeq(c, aex, _) ->
      (compile_cexpr c (si+1) new_env num_args) @
      (* (decrement (Reg(EAX))) @ *)
      (compile_aexpr aex (si+1) new_env num_args)
    | _ -> failwith "letrec not supported yet" in
  let let_content = prelude
                    @ [ IMov(RegOffset(~-word_size * si, STACK_FRAME_LOC_R), Reg(EAX)) ]
                    @ (let_increment id new_env)
                    @ new_body in
  let_content
      (* ^Depending on which of these, we either add to the list of releases at the end or remove from it *)

and compile_aexpr (e : tag aexpr) (si : int) (env : arg envt) (num_args : int) : instruction list =
  match e with
  | ALet(id, e, body, _) ->
    (let_helper (id, e, body) si env num_args [])
  | ACExpr e -> (compile_cexpr e si env num_args)
  | ALetRec(binds, body, loc)  ->
    (match binds with
    | [(id, e)] ->
      let prelude = compile_cexpr e (si + 1) ((id, RegOffset(~-word_size * si, STACK_FRAME_LOC_R))::env) num_args in
      let body = compile_aexpr body (si + 1) ((id, RegOffset(~-word_size * si, STACK_FRAME_LOC_R))::env) num_args in
      prelude
      @ [ IMov(RegOffset(~-word_size * si, STACK_FRAME_LOC_R), Reg(EAX)) ]
      @ body
    | _ -> failwith("single recursion only plz"))
  | ASeq(body, last, _) ->
    let prelude = compile_cexpr body (si + 1) env num_args in
    let body = compile_aexpr last (si + 1) env num_args in
    prelude
    @ [ IMov(RegOffset(~-word_size * si, STACK_FRAME_LOC_R), Reg(EAX)) ]
    @ body
and compile_cexpr (e : tag cexpr) si (env : arg envt) num_args : instruction list =
  match e with
  | CPrim1(op, e, tag) ->
    let e_reg = compile_imm e env in
    begin match op with
      | Print ->
        (mov_if_needed (Reg EAX) e_reg) @
        [ IPush(Reg(EAX));
          ICall("print");
          IPop(Reg(EAX));
        ]
      | Add1 ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_num "err_arith_not_num" (Reg EAX))
        @ [ IAdd(Reg(EAX), Const(2)) ]
        @ (check_overflow "err_overflow")
      | Sub1 ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_num "err_arith_not_num" (Reg EAX))
        @ [ IAdd(Reg(EAX), Const(~-2)) ]
        @ (check_overflow "err_overflow")
      | IsBool ->
        (mov_if_needed (Reg EAX) e_reg) @
        [
          IShl(Reg(EAX), Const(29));
          ICmp(Reg(EAX), HexConst(0x20000000));
          IJe(sprintf "Bool_false_%d" tag);
        ]
        @ (mov_if_needed (Reg EAX) e_reg) @
        [
          IShl(Reg(EAX), Const(31));
          IOr(Reg(EAX), const_false);
          ICmp(Reg(EAX), const_true);
          IJe(sprintf "Bool_done_%d" tag)
        ]
        @ [
          ILabel(sprintf "Bool_false_%d" tag);
          IMov(Reg(EAX), const_false);
          ILabel(sprintf "Bool_done_%d" tag);
        ]
      | IsNum -> (mov_if_needed (Reg EAX) e_reg) @
                 [
                   IShl(Reg(EAX), Const(31));
                   IXor(Reg(EAX), const_true)
                 ]
      | IsTuple -> (mov_if_needed (Reg EAX) e_reg) @
                   [
                     IShl(Reg(EAX), Const(29));
                     ICmp(Reg(EAX), HexConst(0x20000000));
                     IJe(sprintf "Tuple_true_%d" tag);
                     IMov(Reg(EAX), const_false);
                     IJmp(sprintf "Tuple_done_%d" tag);
                     ILabel(sprintf "Tuple_true_%d" tag);
                     IMov(Reg(EAX), const_true);
                     ILabel(sprintf "Tuple_done_%d" tag)
                   ]
      | Not ->
        (mov_if_needed (Reg EAX) e_reg)
        @ (check_bool "err_logic_not_bool" (Reg EDX) (Reg EAX))
        @ [ IXor(Reg(EAX), bool_mask) ]
      | PrintStack ->
        (mov_if_needed (Reg EAX) e_reg)
        @ call "print_stack"
          [Sized(DWORD_PTR, Reg(EAX));
           Sized(DWORD_PTR, Reg(STACK_TOP_R));
           Sized(DWORD_PTR, Reg(STACK_FRAME_LOC_R));
           Sized(DWORD_PTR, Const(num_args))]
    end
  | CPrim2(op, left, right, tag) ->
    let left_reg = compile_imm left env in
    let right_reg = compile_imm right env in
    let arith_op op =
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ check_nums "err_arith_not_num" (Reg EAX) (Reg EDX)
      @ [ op (Reg(EAX), Reg(EDX)) ]
      @ check_overflow "err_overflow" in
    let comp_op op =
      let true_label = sprintf "true_%d" tag in
      let done_label = sprintf "done_%d" tag in
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ (check_nums "err_comp_not_num" (Reg EAX) (Reg EDX))
      @ [
        IMov(Reg(EAX), left_reg);
        ICmp(Reg(EAX), right_reg);
        IMov(Reg(EAX), const_false);
        op done_label;
        ILabel(true_label);
        IMov(Reg(EAX), const_true);
        ILabel(done_label);
      ] in
    let logic_op op =
      (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
      @ (check_bools "err_arith_not_num" (Reg ECX) (Reg EAX) (Reg EDX))
      @ [
        IMov(Reg(EAX), left_reg);
        op (Reg(EAX), right_reg)
      ]  in
    begin match op with
      | Plus -> arith_op (fun (dest, src) -> IAdd(dest, src))
      | Minus -> arith_op (fun (dest, src) -> ISub(dest, src))
      | Times ->
        (mov_if_needed (Reg EAX) left_reg) @ (mov_if_needed (Reg EDX) right_reg)
        @ check_nums "err_arith_not_num" (Reg EAX) (Reg EDX)
        @ [ ISar(Reg(EAX), Const(1)); IMul(Reg(EAX), Reg(EDX)) ]
        @ check_overflow "err_overflow"
      | Less ->
        (* comp_op (fun dest -> IJge dest) *)
        (* You're encouraged to try generating better code for these comparisons.
              The following code should work for lessthan; generate similar code for the others *)
        [
          IMov(Reg(EAX), left_reg);
          ISar(Reg(EAX), Const(1));
          IMov(Reg(ECX), right_reg);
          ISar(Reg(ECX), Const(1));
          ISub(Reg(EAX), Reg(ECX));
          IAnd(Reg(EAX), bool_mask);
          IOr(Reg(EAX), const_false)
        ]
      | Greater -> comp_op (fun dest -> IJle dest)
      | LessEq -> comp_op (fun dest -> IJg dest)
      | GreaterEq -> comp_op (fun dest -> IJl dest)
      | Eq ->
        let true_label = sprintf "true_%d" tag in
        let done_label = sprintf "done_%d" tag in
        (mov_if_needed (Reg EAX) left_reg) @
        [
          ICmp(Reg(EAX), right_reg);
          IMov(Reg(EAX), const_false);
          IJne(done_label);
          ILabel(true_label);
          IMov(Reg(EAX), const_true);
          ILabel(done_label)
        ]
      | And -> logic_op (fun (dest, src) -> IAnd(dest, src))
      | Or -> logic_op (fun (dest, src) -> IOr(dest, src))
    end
  | CIf(cond, thn, els, tag) ->
    let cond_reg = compile_imm cond env in
    let else_label = sprintf "else_%d" tag in
    let end_label = sprintf "end_%d" tag in
    (mov_if_needed (Reg EAX) cond_reg)
    @ (check_bool "err_if_not_bool" (Reg ECX) (Reg EAX))
    @ [
      ICmp(Reg(EAX), const_true);
      IJne(else_label)
    ]
    @ (compile_aexpr thn si env num_args)
    @ [ IJmp(end_label); ILabel(else_label) ]
    @ (compile_aexpr els si env num_args)
    @ [ ILabel(end_label) ]
  | CImmExpr i -> [ IMov(Reg(EAX), compile_imm i env) ]
  | CApp(f, args, _) ->
    let func_ref = (compile_imm f env) in
    let pushargs = List.rev (List.map (fun a -> IPush (Sized(DWORD_PTR, compile_imm a env))) args) in
    pushargs
    @ [ IMov(Reg(EDX), func_ref); IPush(Reg(EDX)); IAdd(Reg(EDX), Const(3)); IFCall(Reg(EDX))]
  | CLambda(bindings, body, tag) ->
    (* | arity | ref_count | code ptr | var1 | var2 | ... | varn | (maybe padding) | *)
    let arity = ((List.length bindings)) in
    let free_vs = (List.filter (fun i -> not (List.mem i bindings)) (free_vars body)) in
    let free_v_count = (List.length free_vs) in
    let heap_offset = 4*(if free_v_count mod 2 == 0 then free_v_count+4 else (free_v_count+3)) in
    let code_name = sprintf "lambda_%d" tag in
    let (prologue, heap_push, comp_body, epilogue) = (compile_fun code_name bindings body free_vs) in
    let after_name = sprintf "after_%d" tag in
    [IJmp(after_name)] @
    prologue @ comp_body @ epilogue @
    [ILabel(after_name);
    ] @ (reserve heap_offset tag) @
    [
     IMov(RegOffset(0, HEAP_POINTER_R), Sized(DWORD_PTR, Const(arity)));
     IMov(RegOffset(4, HEAP_POINTER_R), Sized(DWORD_PTR, Const(0)));
     IMov(RegOffset(8, HEAP_POINTER_R), Sized(DWORD_PTR, Label(code_name)))] @
    List.flatten (List.mapi (fun i v_name -> [IMov(Reg(ECX), Sized(DWORD_PTR, (find env v_name)));
                                 IMov(RegOffset(4*(i+3), HEAP_POINTER_R), Reg(ECX))]) free_vs)  @
    [
     IMov(Reg(EAX), Reg(HEAP_POINTER_R));
     IAdd(Reg(HEAP_POINTER_R), Const(heap_offset));
     IAdd(Reg(EAX), Const(5))
    ]
  | CTuple(elts, tag) ->
    (* Tuples now have the following layout:
    Number of elements; reference count; items *)
    let len = (List.length elts) in
    (* let p = e : arg *)
    let heap_offset = 4*(if len mod 2 == 0 then len+2 else (len+3)) in
    (reserve heap_offset tag) @
    [ IMov(RegOffset(0, HEAP_POINTER_R), Sized(DWORD_PTR, Const(len))) ] @
    (* Initialize the reference count at zero *)
    [ IMov(RegOffset(4, HEAP_POINTER_R), Sized(DWORD_PTR, Const(0))) ] @
    List.flatten (List.mapi (fun i e -> [IMov(Reg(ECX), Sized(DWORD_PTR,(compile_imm e env)));IMov(RegOffset((i+2)*4, HEAP_POINTER_R), Reg(ECX))]) elts) @
    [ IMov(Reg(EAX), Reg(HEAP_POINTER_R));
      IAdd(Reg(HEAP_POINTER_R), Const(heap_offset));
      IAdd(Reg(EAX), Const(1))
    ]
    @ List.flatten (List.map (fun f -> (tup_increment (compile_imm f env))) elts)
  | CSetItem(tup, index, rhs, _) ->
    let tuple = (compile_imm tup env) in
    let idx = (compile_imm index env) in
    let rhs_val = (compile_imm rhs env) in
    (check_tuple "err_get_not_tuple" (Reg EDX) tuple) @
    (check_number "err_index_not_num" (Reg EDX) idx) @
    (check_tuple_index (Reg EDX) tuple idx) @
    [
      ISub(Reg(EAX), Const(1));] @
      decrement (RegOffsetReg(EAX, ECX, 2, 8)) @
  [
      IMov(Reg(ECX), idx);
      IMov(Reg(EDX), rhs_val);
      IMov(RegOffsetReg(EAX, ECX, 2, 8), Reg(EDX))] @
    (tup_increment (RegOffsetReg(EAX, ECX, 2, 8))) @ [
      IAdd(Reg(EAX), Const(1));
    ]
  | CGetItem(coll, index, _) ->
    let tuple = (compile_imm coll env) in
    let idx = (compile_imm index env) in
    (check_tuple "err_get_not_tuple" (Reg EDX) tuple) @
    (check_number "err_index_not_num" (Reg EDX) idx) @
    (check_tuple_index (Reg EDX) tuple idx) @
    [
      ISub(Reg(EAX), Const(1));
      IMov(Reg(ECX), idx);
      IMov(Reg(EAX), RegOffsetReg(EAX, ECX, 2, 8));
    ]
and compile_imm (e : tag immexpr) (env : arg envt) : Instruction.arg =
  match e with
  | ImmNum(n, _) -> Const((n lsl 1))
  | ImmBool(true, _) -> const_true
  | ImmBool(false, _) -> const_false
  | ImmId(x, _) -> (find env x)
(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED *)
and call (label : string) args =
  (let setup = List.rev_map (fun arg ->
                  match arg with
                  | Sized _ -> IPush(arg)
                  | _ -> IPush(Sized(DWORD_PTR, arg))) args in
  let teardown =
    (let len = List.length args in
    if len = 0 then []
    else [ IInstrComment(IAdd(Reg(STACK_TOP_R), Const(4 * len)), sprintf "Popping %d arguments" len) ]) in
  setup @ [ ICall(label) ] @ teardown)

let compile_prog anfed =
  let prelude =
    "section .text
extern error
extern print
extern equal
extern allocate
extern dereference_pointer
extern decrement_pointer
extern increment_pointer
extern HEAP_END
extern STACK_BOTTOM
global our_code_starts_here" in
  let suffix = sprintf "
err_comp_not_num:%s
err_arith_not_num:%s
err_logic_not_bool:%s
err_if_not_bool:%s
err_overflow:%s
err_get_not_tuple:%s
err_get_low_index:%s
err_get_high_index:%s
err_index_not_num:%s"
                       (* If you modified `call` above, then fix these up, too *)
                       (to_asm (call "error" [Const(err_COMP_NOT_NUM)]))
                       (to_asm (call "error" [Const(err_ARITH_NOT_NUM)]))
                       (to_asm (call "error" [Const(err_LOGIC_NOT_BOOL)]))
                       (to_asm (call "error" [Const(err_IF_NOT_BOOL)]))
                       (to_asm (call "error" [Const(err_OVERFLOW)]))
                       (to_asm (call "error" [Const(err_GET_NOT_TUPLE)]))
                       (to_asm (call "error" [Const(err_GET_LOW_INDEX)]))
                       (to_asm (call "error" [Const(err_GET_HIGH_INDEX)]))
                       (to_asm (call "error" [Const(err_INDEX_NOT_NUM)]))
  in
  (* $heap is a mock parameter name, just so that compile_fun knows our_code_starts_here takes in 1 parameter *)
  let (prologue, heap_push, comp_main, epilogue) = compile_fun "our_code_starts_here" ["$heap"] anfed [] in
     let heap_start = [
         IInstrComment(IMov(LabelContents("STACK_BOTTOM"), Reg(STACK_FRAME_LOC_R)), "This is the bottom of our Garter stack");
         ILineComment("heap start");
         IInstrComment(IMov(Reg(HEAP_POINTER_R), RegOffset(8, STACK_FRAME_LOC_R)), "Load HEAP_POINTER_R with our argument, the heap pointer");
         IInstrComment(IAdd(Reg(HEAP_POINTER_R), Const(7)), "Align it to the nearest multiple of 8");
         IInstrComment(IAnd(Reg(HEAP_POINTER_R), HexConst(0xFFFFFFF8)), "by adding no more than 7 to it")
       ] in
     let main = (prologue @ heap_start @ heap_push @ comp_main @ epilogue) in
     sprintf "%s%s%s\n" prelude (to_asm main) suffix


let compile_to_string prog : (exn list, string) either =
  let env = [ (* DBuiltin("equal", 2) *) ] in
  let errors = well_formed prog env in
  match errors with
  | [] ->
     let tagged : tag program = tag prog in
     let anfed : tag aprogram = atag (anf tagged) in
     (* let opted : tag aprogram = atag (optimize anfed false) in *)
     (* printf "Prog:\n%s\n" (ast_of_prog prog); *)
     (* printf "Tagged:\n%s\n" (format_prog tagged string_of_int); *)
     (* printf "ANFed/tagged:\n%s\n" (string_of_aprogram anfed); *)
     Right(compile_prog anfed)
  | _ -> Left(errors)
