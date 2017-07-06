open Compile
open Runner
open Printf
open OUnit2
open ExtLib
open Types
open Expr
open Pretty
open Optimize

let t name program expected = name>::test_run [] program name expected;;
let tvg name program expected = name>::test_run_valgrind [] program name expected;;
let terr name program expected = name>::test_err [] program name expected;;

let tfvs name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let vars = free_vars anfed in
    let c = Pervasives.compare in
    let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in
    assert_equal (List.sort ~cmp:c vars) (List.sort ~cmp:c expected) ~printer:str_list_print)
;;

let test_fold name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let opt = (const_fold (atag anfed)) in
    (* Printf.printf "prog: %s\n" (string_of_aprogram opt);
    Printf.printf "expe: %s\n" expected; *)
    assert_equal (string_of_aprogram opt) expected);
;;

let test_anf name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    Printf.printf "prog: %s\n" (string_of_aprogram anfed);
    Printf.printf "expe: %s\n" expected;
    assert_equal (string_of_aprogram anfed) expected);
;;

let test_optimize name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let opt = (optimize (atag anfed) false) in
    (* Printf.printf "prog: %s\n" (string_of_aprogram opt);
    Printf.printf "expe: %s\n" expected; *)
    assert_equal (string_of_aprogram opt) expected);
;;

let test_dae name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let opt = (dae (atag anfed)) in
    (* Printf.printf "prog: %s\n" (string_of_aprogram opt);
    Printf.printf "expe: %s\n" expected; *)
    assert_equal (string_of_aprogram opt) expected);
;;

let test_cse name program expected = name>::
  (fun _ ->
    let ast = parse_string name program in
    let anfed = anf (tag ast) in
    let opt = (cse (atag anfed)) in
    (* Printf.printf "prog: %s\n" (string_of_aprogram opt);
    Printf.printf "expe: %s\n" expected; *)
    assert_equal (string_of_aprogram opt) expected);
;;


let reg_tests = [
  (* Optimization tests have been broken by the new rule that all let-bindings will end with an immediate *)
  (* test_fold "basics" "5 + 5" "10";
  test_fold "basics2" "5 + print(5) + 5" "(alet unary_4 = print(5) in (alet binop_3 = (5 + unary_4) in (binop_3 + 5)))";
  test_fold "n" "let x = 5 in add1(x)" "(alet x = 5 in 6)";
  test_fold "n2" "let x = 5 in 6+add1(x)" "(alet x = 5 in (alet unary_3 = 6 in 12))";
  test_fold "impure" "let z = print(5) in z" "(alet z = print(5) in z)";
  test_fold "bools" "let z = isnum(5 + 4) in (true && z)" "(alet binop_7 = 9 in (alet z = true in true))";
  test_fold "fn" "let z = (lambda x: 5 + 5 * x) in z(3)" "(alet z = (lambda(x): (alet binop_9 = 10 in (binop_9 * x))) in (z(3)))";

  test_optimize "doubleoptz2" "5+5+5" "15";
  test_optimize "doubleoptz3" "let p = 5+5+5 in add1(let x = print(false) in p)" "16";

  test_dae "doubleoptz4" "let q = 4 in let r = print((4,3)) in r" "(alet tup_6 = (4, 3) in (alet r = print(tup_6) in r))";
  test_dae "many_facets" "let x = add1(print(99)) in
                              let y = x in
                              let a = x + 2 in
                              let b = !(y < 2) in
                              a + 1" "(alet unary_21 = print(99) in (alet x = add1(unary_21) in (alet y = x in (alet a = (x + 2) in (alet binop_10 = (y < 2) in (!(binop_10); (a + 1)))))))";

  test_cse "basic_cse" "let x = 5 in
                        let y = x in
                        let a = x + 2 in
                        let b = y + 2 in
                      33"
    "(alet x = 5 in (alet y = x in (alet a = (y + 2) in (alet b = a in 33))))";

  test_cse "complex_cse" "let x = 5 in
                          let y = x in
                          let a = x + 2 + 3 in
                          let b = y + 2 in
                          let z = y + 2  + x + 2 + 3 in
                        33"
    "(alet x = 5 in (alet y = x in (alet binop_24 = (y + 2) in (alet a = (binop_24 + 3) in (alet b = binop_24 in (alet binop_14 = binop_24 in (alet binop_12 = (binop_14 + y) in (alet binop_10 = (binop_12 + 2) in (alet z = (binop_10 + 3) in 33)))))))))";

  test_optimize "many_facet" "let x = 11 in
                        let y = x in
                        let a = x + 2 in
                        let b = y + 2 in
                        b + 1" "14"; *)

  t "basics" "1 + 1" "2";
  t "40" "let x = 40 in x" "40";
  t "fals" "let x = false in x" "false";
  t "basics-1"  "let x = true in x" "true";
	t "basics-2"  "let x = add1(40) in x" "41";
  (* terr "basics-3" "let x = add1(true) in x" "Compile error: Error: expected a number, but found something else";
  terr "basics-4" "let x = sub1(true) in x" "Compile error: Error: expected a number, but found something else"; *)

	t "isbool-1"  "let x = add1(40) in isbool(add1(x))" "false";
	t "isbool-2" "isbool(true)" "true";
  t "isbool-3" "isbool(isbool(5))" "true";

	t "isnum-1"  "let x = add1(40) in isnum(add1(x))" "true";
	t "isnum-2" "isnum(true)" "false";
  t "isnum3" "isbool(isnum(5))" "true";

  t "not1" "!(false)" "true";
  t "not2" "!(!(false))" "false";
  t "not3" "let x = !(isbool(5)) in !(x)" "false";
  (* terr "not4" "let x = 5 in !(x)" "Compile error: Error: expected a number, but found something else"; *)

  t "addtest" "5 + 5" "10";
  t "addtest2" "let z = 44 + 12 in sub1(z + 2)" "57";
  t "subtest" "8 - 2" "6";
  t "subtest2" "let z = 44 - 12 in add1(z - 2)" "31";
  t "multest" "8 * 3" "24";
  t "multest2" "let z = 4 * 12 in add1(z * 2)" "97";

  t "andtest" "true && true" "true";
  t "andtest2" "true && false" "false";
  t "andtest3" "true && (let x = isbool(4) in !(x))" "true";
  t "ortest" "true || false" "true";
  t "ortest2" "false || false" "false";
  t "ortest3" "false || (let x = isbool(4) in !(x))" "true";


  t "lt_test" "5 < 3" "false";
  t "lt_test2" "5 < 5" "false";
  t "lte_test" "3 <= 5" "true";
  t "lte_test2" "5 <= 5" "true";
  t "gt_test" "let x = (5 > 2) in !(x)" "false";
  t "gt_test3" "5 > 3" "true";

  terr "iftest0" "if 54: true else: false" "Error 4: if expected a boolean";
  t "iftest" "let x = 5 in (if (x > 2): 7 else: 3)" "7";
  t "comprehensive" "let x = 4 in if (isnum(x)): (x >= 2) else: 5" "true";

  (* terr "overflow" "((add1(12345*67890))*12345)" "Error 5: Integer overflow"; *)
  (* NB: The above test has been disabled because the behavior of overflowing integers is no longer defined. *)
  terr "multifail" "58549589485949 + badbinding" "The number literal 58549589485949, used at <multifail, 1:0-1:14>, is not supported in this language
The identifier badbinding, used at <multifail, 1:17-1:27>, is not in scope";

  t "functionsrgood" "let add3 = (lambda x, y, z: x + y + z) in add3(5, 7, 9)" "21";
  terr "functions_are_bad" "let f = (lambda x, x: x + z) in
  f(1, 2, 3)" "The identifier z, used at <functions_are_bad, 1:26-1:27>, is not in scope";

  t "fadd2" "let f = (lambda x, y: x + y + x + x) in
  f(5, 1)" "16";

  t "doublecall" "let f = (lambda x, y: x + 73) in f(5) + f(6)" "157";
  t "twicecall"  "let f = (lambda x, y: x + 73) in f(f(5))" "151";
  t "unary" "let f = (lambda x: x+777) in f(55555)" "56332";
  t "functions_are_good3" "let f = (lambda x, y: add1(x * y)) in
  f(5, 7)" "36";

  terr "letrecscope" "let rec f = (lambda x: z) in f(1)" "The identifier z, used at <letrecscope, 1:23-1:24>, is not in scope";

  t "closing_over" "let z = 5 in
  let f = (lambda k: add1(z)) in f(4)" "6";

  t "closing_over2" "let n = 5 in
  let f = (lambda k: 1 + n + k) in f(7)" "13";

  t "closing_over3" "let n = 5 in
  let z = 1 in
  let f = (lambda k: z + n) in f(3)" "6";

  terr "tuple_expected" "6[33]" "Error 6: get expected tuple";
  terr "tuple_small" "(6,5,4)[-1]" "Error 7: index too small to get";
  terr "tuple_big" "(1,4,6,7,8)[5]" "Error 8: index too large to get";
  terr "tuple_big2" "(1,4,6,7)[4]" "Error 8: index too large to get";
  terr "tuple_big3" "(1,4,6)[3]" "Error 8: index too large to get";
  terr "tuple_big4" "(1,4,6)[13]" "Error 8: index too large to get";


  t "tuple_access" "(6,5,4)[0]" "6";
  t "tuple_access2" "(true,false,78)[0]" "true";
  t "tuple_if" "if false: 100 else: (44, 55, 66)[2]" "66";
  t "tuple_index0" "let t = (44, 55, 66, 2, 5) in t[0]" "44";
  t "tuple_index" "(44, 55, 66)[2]" "66";
  t "tuple_index2" "let t = (44, 55, 66, 2) in t[2]" "66";
  t "tuple_index3" "let t = (44, 55, 66, 2) in t[3]" "2";
  t "tuple_index4" "let t = (44, 55, 66, 2, 5) in t[3]" "2";
  t "tuple_index5" "let t = (44, 55, 66, 2, 5) in t[4]" "5";
  t "tuple_index6" "let t = (44, 55, 66, 2, 5, 6) in t[5]" "6";
  t "is_tuple_true" "istuple((2,3,4))" "true";
  t "is_tuple_false" "istuple(true)" "false";

  t "tuple_ex" "(5+3, 5+2, 22)[1]" "7";
  t "tuple_ex_1" "let x = 5 in (5, 5, 22)[1]" "5";
  t "tuple_ex_2" "(4 + 4 + 4 + 4)" "16";
  t "isbooltup" "isbool((3, 6))" "false" ;
  t "isnumtup" "isnum((3, 6))" "false" ;

  (* failing tests *)
  t "recursive_test" "let rec f = (lambda x, adds_another:
  if (adds_another): f(x + 1, false) else: x + 1) in
  f(4, true)" "6";

  t "functions_are_rec2" "let rec f = (lambda x:
  if (x == 0): 1 else: (x + f(x - 1))) in
  f(4)" "11";

  t "closing_over4" "let n = 5 in
  let p = 22 in
  let z = 1 in
  let f = (lambda k: (2*p) + (3*z) + n + k) in f(3)" "55";

  t "closing_over5" "
  let n = 5 in
  let p = 22 in
  let z = 1 in
  let f = (lambda k: 2*p + 3*z + n + k) in f(3)+n" "60";

  t "closing_over6" "
  let n = 5 in
  let p = 22 in
  let z = 1 in
  let f = (lambda k: 2*p + 3*z + n + k) in f(3)+p" "77";

  t "closing_over7" "
  let tophat = 123 in
  let n = 5 in
  let p = 22 in
  let z = 5 in
  let f = (lambda k: 2*p + 3*z + n*11 + 8*k) in f(19)+p+f(tophat)+tophat" "1487";

  t "decrementing" "let x = (5, 4) in let q = (lambda k: (4, k)) in q(1)" "(4, 1)";
  t "decrementing2" "let x = (5, 4) in let q = (lambda k: (4, k)) in q((1, 4))" "(4, (1, 4))";

]

let pair_tests = [
  t "tup1" "let t = (4, (5, 6)) in
            begin
              t[0] := 7;
              t
            end" "(7, (5, 6))";
  t "tup2" "let t = (4, (5, 6)) in
            begin
              t[1] := 7;
              t
            end" "(4, 7)";
  t "tup3" "let t = (4, (5, 6)) in
            begin
              t[1] := t;
              t
            end" "(4, <cyclic tuple 1>)";
  t "tup4" "let t = (4, 6) in
            (t, t)"
           "((4, 6), (4, 6))";
  t "tup5" "let t = (4, (5, 6, 7, 9), (3, 2)) in
            begin
              t[0] := 7;
              t
            end" "(7, (5, 6, 7, 9), (3, 2))";
  t "tup6" "let t = (4, (5, 6, 9), (3, 2)) in
            begin
              t[0] := 7;
              t
            end" "(7, (5, 6, 9), (3, 2))";
  t "alloc_example" "begin
                      let p = (4,3) in print(p);
                      33
                     end" "(4, 3)\n33";
  t "tup999" "let t = (4, 5, 6) in
                let p = (1, 2, t) in
                  begin
                    p[2] := p[2];
                    p
                  end" "foo"
]



let suite =
"suite">:::
reg_tests @ pair_tests



let () =
  run_test_tt_main suite
;;
