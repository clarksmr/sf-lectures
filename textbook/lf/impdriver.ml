open Imp

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let test s =
  print_newline();
  print_endline ("Propgram: " ^ s);
  let parse_res = parse (explode s) in
  (match parse_res with
    NoneE _ -> print_endline ("Syntax error");
  | SomeE c ->
      let fuel = 1000 in
      match (ceval_step empty_st c fuel) with
        None ->
          print_endline
            ("Still running after " ^ string_of_int fuel ^ " steps")
      | Some res ->
          print_endline (
              "Result: ["
            ^ string_of_int (res ['w']) ^ " " 
            ^ string_of_int (res ['x']) ^ " " 
            ^ string_of_int (res ['y']) ^ " " 
            ^ string_of_int (res ['z']) ^ " ...]"))
;;

test "x:=1 ; y:=2";;

test "true";;  (* syntax error *)
test "skip";;
test "skip;skip";;
test "while true do skip end";;
test "x:=3";;
test "x:=3; while 0<=x do skip end";;
test "x:=3; while 1<=x do y:=y+1; x:=x-1 end";;
