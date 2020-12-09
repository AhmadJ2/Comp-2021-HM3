
let rec ormap f s =
  match s with
  | [] -> false
  | car :: cdr -> (f car) || (ormap f cdr);;

let rec andmap f s =
  match s with
  | [] -> true
  | car :: cdr -> (f car) && (andmap f cdr);;	  

let lowercase_ascii  =
  let delta = int_of_char 'A' - int_of_char 'a' in
  fun ch ->
  if ('A' <= ch && ch <= 'Z')
  then char_of_int ((int_of_char ch) - delta)
  else ch;;

let string_to_list str =
  let rec loop i limit =
    if i = limit then []
    else (String.get str i) :: (loop (i + 1) limit)
  in
  loop 0 (String.length str);;

let list_to_string s =
  String.concat "" (List.map (fun ch -> String.make 1 ch) s);;

module PC = struct

(* the parsing combinators defined here *)
  
exception X_not_yet_implemented;;

exception X_no_match;;

let const pred =
  function 
  | [] -> raise X_no_match
  | e :: s ->
     if (pred e) then (e, s)
     else raise X_no_match;;

let caten nt1 nt2 s =
  let (e1, s) = (nt1 s) in
  let (e2, s) = (nt2 s) in
  ((e1, e2), s);;

let pack nt f s =
  let (e, s) = (nt s) in
  ((f e), s);;

let nt_epsilon s = ([], s);;

let caten_list nts =
  List.fold_right
    (fun nt1 nt2 ->
     pack (caten nt1 nt2)
	  (fun (e, es) -> (e :: es)))
    nts
    nt_epsilon;;

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_no_match -> (nt2 s);;

let nt_none _ = raise X_no_match;;
  
let disj_list nts = List.fold_right disj nts nt_none;;

let delayed thunk s =
  thunk() s;;

let nt_end_of_input = function
  | []  -> ([], [])
  | _ -> raise X_no_match;;

let rec star nt s =
  try let (e, s) = (nt s) in
      let (es, s) = (star nt s) in
      (e :: es, s)
  with X_no_match -> ([], s);;

let plus nt =
  pack (caten nt (star nt))
       (fun (e, es) -> (e :: es));;

let guard nt pred s =
  let ((e, _) as result) = (nt s) in
  if (pred e) then result
  else raise X_no_match;;
  
let diff nt1 nt2 s =
  match (let result = nt1 s in
	 try let _ = nt2 s in
	     None
	 with X_no_match -> Some(result)) with
  | None -> raise X_no_match
  | Some(result) -> result;;

let not_followed_by nt1 nt2 s =
  match (let ((_, s) as result) = (nt1 s) in
	 try let _ = (nt2 s) in
	     None
	 with X_no_match -> (Some(result))) with
  | None -> raise X_no_match
  | Some(result) -> result;;
	  
let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

(* useful general parsers for working with text *)

let make_char equal ch1 = const (fun ch2 -> equal ch1 ch2);;

let char = make_char (fun ch1 ch2 -> ch1 = ch2);;

let char_ci =
  make_char (fun ch1 ch2 ->
	     (lowercase_ascii ch1) =
	       (lowercase_ascii ch2));;

let make_word char str = 
  List.fold_right
    (fun nt1 nt2 -> pack (caten nt1 nt2) (fun (a, b) -> a :: b))
    (List.map char (string_to_list str))
    nt_epsilon;;

let word = make_word char;;

let word_ci = make_word char_ci;;

let make_one_of char str =
  List.fold_right
    disj
    (List.map char (string_to_list str))
    nt_none;;

let one_of = make_one_of char;;

let one_of_ci = make_one_of char_ci;;

let nt_whitespace = const (fun ch -> ch <= ' ');;

let make_range leq ch1 ch2 (s : char list) =
  const (fun ch -> (leq ch1 ch) && (leq ch ch2)) s;;

let range = make_range (fun ch1 ch2 -> ch1 <= ch2);;

let range_ci =
  make_range (fun ch1 ch2 ->
	      (lowercase_ascii ch1) <=
		(lowercase_ascii ch2));;

let nt_any (s : char list) = const (fun ch -> true) s;;

let trace_pc desc nt s =
  try let ((e, s') as args) = (nt s)
      in
      (Printf.printf ";;; %s matched the head of \"%s\", and the remaining string is \"%s\"\n"
		     desc
		     (list_to_string s)
		     (list_to_string s') ;
       args)
  with X_no_match ->
    (Printf.printf ";;; %s failed on \"%s\"\n"
		   desc
		   (list_to_string s) ;
     raise X_no_match);;

(* testing the parsers *)

let test_string nt str =
  let (e, s) = (nt (string_to_list str)) in
  (e, (Printf.sprintf "->[%s]" (list_to_string s)));;

end;; (* end of struct PC *)

(* end-of-input *)

(* #use "pc.ml";; *)
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
exception X_comment;;  
exception M_no_match;;  


type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  |_ -> raise X_no_match;;
  
module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;
  
(*   
  let read_sexprs string = raise X_comment;;
  end;; *)
let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
    nt;;
   
let nt_whitespaces = star (char ' ');;

let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;

let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

let digit = range '0' '9';;

let maybe nt s =
  try let (e, s) = (nt s) in
      (Some(e), s)
  with X_no_match -> (None, s);;

let get_option some_val =
  match some_val with
    | Some a -> a
    | None -> None;;

let string_metachar
  = caten (char ('\\')) (const (fun ch -> ch='f'||ch='n'||ch='\\'||ch='t'||ch='r'||ch='"'));;

let list_to_string_ci s =
    String.concat "" (List.map (fun ch -> String.make 1 (lowercase_ascii ch)) s);;

let replace_metachar s = 
  match s with
    | ('\\','f') -> '\012'
    | ('\\','n') -> '\n'
    | ('\\','t') -> '\t'
    | ('\\','r') -> '\r'
    | ('\\','\\') -> '\\'
    | ('\\', '\"') -> '\"'
    | (s, r) -> raise X_no_match;;

let stringLiteralChar =  (const (fun ch -> ch!='\"' && ch!= '\\'));;

let strignChar
  = disj (pack string_metachar replace_metachar) stringLiteralChar;;

let rec gcd a b =
  if b = 0 then a else gcd b (a mod b);;

let do_gcd a b = 
  let x = gcd a b in
  if x>0 then
    (a/x, b/x)
    else (a/(-1*x), b/(-1*x));;

let tenEx num ex = 
  let rec pow a = function
    | 0 -> 1.
    | 1 -> a
    | n -> 
      let b = pow a (n / 2) in
      b *. b *. (if n mod 2 = 0 then 1. else a) in
  let times = pow 10. ex in
  num *. times;;

let nt_boolt = make_spaced (word_ci "#t");;

let nt_boolf = make_spaced (word_ci "#f");;

let tok_lparen = make_spaced ( char '(');;

let tok_rparen = make_spaced ( char ')');;

let tok_addop = make_spaced ( char '+');;

let tok_mulop = make_spaced ( char '*');;

let tok_semicolon = char ';';;

let nt_rightquotation = 
  make_paired (nt_epsilon) (nt_whitespaces) (char '"');;

let nt_leftquotation =
  make_paired (nt_whitespaces) (nt_epsilon) (char '"');;

let disj_l l nt =
  List.fold_right
    (fun x acc -> disj (nt x) (acc)) 
    l 
    nt_none;;

let nt_disj_nt_list l= 
  List.fold_right
    (fun x acc -> disj (x) (acc))
    l
    nt_none;;

let nt_specialchar = disj_l ['!';'$';'^';'*';'-';'_';'+';'=';'<';'>';'?';'/';':'] char;;
let symNums = range '0' '9';;
let symLetters = range_ci 'a' 'z';;
let symbolCharNoDot = disj (disj symNums symLetters) nt_specialchar;;
let dot =  char '.';;
let symChar = disj symbolCharNoDot dot;;

let natural =
  let digits =  plus digit in
  pack digits (fun (ds) -> ds);;

let sign = maybe (fun s -> 
  match s with
  | []-> raise X_no_match
  | car::cdr ->  if (car = '+') || (car = '-') 
      then (car, cdr) 
        else raise X_no_match);;

let integer = pack (caten sign natural) (fun s ->
  match s with
  |(Some a, num) -> a::num
  |((None, num)) -> num
  );;

let fraction = caten (caten integer (char '/')) natural;;

let floats = caten (caten integer dot) natural;;

let exponent_float (((domi, symb), nomi), expo) = match symb with
      |'.' -> (match expo with |'e'::rest -> Number(Float(float_of_string (list_to_string (domi@symb::nomi@expo))))
                               |_ -> raise X_no_match)
      |'_' -> (match expo with  | 'e'::rest -> Number(Float(float_of_string (list_to_string (domi@expo))))
                                |_ -> raise X_no_match)
      |_-> raise X_no_match
                                
let number s = 
    let (((domi, symb), nomi), rest) = 
      try (fraction s)
      with PC.X_no_match -> (
        try (floats s)
        with PC.X_no_match -> pack integer (fun x -> ((x, '_'), ['1'])) s
      ) 
      in
      let (scientific, rest) = maybe (char_ci 'e') rest in
      let (exponent, rest) = match scientific with
      |Some(e) -> let  (expo, rest) = integer rest in (['e']@expo, rest)
      |None -> (['_'], rest) in
      let (sexp) = 
      disj exponent_float (fun (((domi, symb), nomi), exponent) -> match symb with
      | '.' -> Number(Float(float_of_string (list_to_string (domi@symb::nomi))))
      | '_' -> (Number(Fraction((int_of_string (list_to_string domi)), (int_of_string (list_to_string nomi)))))
      | '/' -> let(domi, nomi) = do_gcd (int_of_string (list_to_string domi)) (int_of_string (list_to_string nomi)) in (Number(Fraction(domi, nomi)))
      | _ -> raise X_no_match) (((domi, symb), nomi), exponent) in
      (sexp, rest);;

let charPrefix s = word "#\\" s;;

let visiblesimplechar s = const (fun ch -> ch >' ') s;;

let nt_namedChar s = 
  let (e,s) = disj_l ["newline"; "nul"; "page"; "return"; "space"; "tab"] word_ci s in
  let e = (list_to_string_ci e) in
  match e with
    |"newline" -> ('\n', s)
    |"nul" -> ('\000', s)
    |"page" -> ('\012',s)
    |"return" -> ('\013',s)
    |"space" -> (' ',s)
    |"tab" ->('\t', s)
    |e -> raise X_no_match;;

let nt_regular_char s = match s with  
          | car::cdr -> (car, cdr)
          | _ -> raise X_no_match;;


let rec pairs lst = match lst with
    | [] -> Nil
    |first:: rst -> Pair(first, pairs rst);;
let rec nt_expr s =
  let nt_nestedexp = pack (caten (caten tok_lparen nt_expr) tok_rparen)
      (fun ((l, e), r) -> e) in
  (disj nt_number nt_nestedexp) s
and nt_string s = 
  let st = (pack (caten (caten nt_leftquotation (star  strignChar)) nt_rightquotation)
                (fun ((l, e), r) -> String(list_to_string e))) in st s
and nt_bool = disj (pack nt_boolt (fun _-> Bool(true))) 
  (pack nt_boolf (fun _-> Bool(false)))
and nt_char = pack (caten (caten charPrefix (disj nt_namedChar nt_regular_char)) nt_whitespaces) 
    (fun ((pre, vis), spaces) -> Char(vis))


and nt_number =  not_followed_by number (disj symLetters nt_specialchar)
and nt_symbol =  disj (fun x ->
  let ((sym,slst), rest) = caten symChar (plus symChar) x in
  (Symbol(list_to_string_ci (sym::slst)), rest)) 
  (fun s -> let (sym,rest) = symbolCharNoDot s in (Symbol(list_to_string_ci [sym]), rest))

and nt_list s = let p = pack 
    (caten (caten tok_lparen (star (nt_sexpr))) tok_rparen) 
      (fun ((l,exps), r) -> (List.fold_right(
                (fun x acc  -> Pair(x ,acc)))) exps Nil)
                 in p s

and nt_dotted_list s = let dotted = pack 
      (
        caten (caten tok_lparen (plus nt_sexpr)) (caten (caten (make_spaced dot) nt_sexpr) tok_rparen)
      )
              (fun ((l, exps),((d,exp), r)) -> (List.fold_right((fun x acc -> Pair(x, acc)))) exps exp 
              )
              in dotted s
and nt_all_quotes s = let (quete,sexp) = match s with
      | '\''::rest -> ("quote",rest)
      | '`'::rest -> ("quasiquote",rest)
      | ','::rest -> (match rest with 
                        | '@'::rest_2 -> ("unquote-splicing",rest_2)
                        |_ -> ("unquote",rest)
                      )
      |_ -> raise X_no_match 
      in let (s,r) = nt_sexpr sexp in 
      (Pair(Symbol(quete), Pair(s, Nil)), r)

and nt_sexpr s =  let nt_l = [
  nt_number; nt_char;nt_string; nt_bool;nt_symbol;nt_list;nt_dotted_list;nt_all_quotes] in
  (make_spaced(nt_disj_nt_list nt_l)) s;;

let rec remove_last_nil s lst = match s with 
  | Nil::[] -> lst
  | car::[] -> (lst@[car])
  | car::rest -> remove_last_nil rest (lst@[car])
  | _ -> raise X_no_match;;
 

let rec remove_all_comments s new_s = match s with
        | '#'::';'::rest -> remove_sexprcomment rest new_s 
        | ';'::rest -> remove_all_comments (remove_comment s) new_s
        | chr::[] -> new_s@[chr]
        | chr::rest -> remove_all_comments rest (new_s@[chr])
        | _ -> new_s
  
and remove_comment cmnt = let(_, s) = (star (const (fun ch -> ch!='\n'))) cmnt in 
    match s with 
    | '\n'::rest -> rest
    | _ -> []

and remove_sexprcomment cmnt new_s = let to_remove = remove_all_comments cmnt [] in 
      let (_, rest) =  nt_sexpr to_remove in new_s@rest;;

let read_sexprs string = let chars = remove_all_comments (string_to_list string) [] in
  let (sexp, lst) = star nt_sexpr chars in        
        match lst with | [] -> sexp | _ -> raise X_no_match ;;
 (* struct Reader *)
end;;

(* #use "reader.ml";; *)
open Reader;;
type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;
exception X_Reserve_Word;;
exception X_empty_lambda_body;;
exception X_not_supported_forum;;
exception X_invalid_let;;
exception X_invalid_let_star;;
exception X_invalid_let_rec;;
exception M_no_match;;
exception X_invalid_MIT_define;;
exception X_invalid_quatisquote;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
 (* signature TAG_PARSER *)
end
module Tag_Parser : TAG_PARSER = struct



let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;

let nt_disj_nt_list l= 
 List.fold_right
  (fun x acc -> disj (x) (acc))
  l
  nt_none;;

let frac_to_const e = match e with
    | Number(Fraction(nomi, domi)) -> Const(Sexpr(e))
    | _ -> raise X_no_match;;

let float_to_const e = match e with
    | Number(Float(num)) -> Const(Sexpr(e))
    | _ -> raise X_no_match;;
    
let number_to_const e = disj frac_to_const float_to_const e;;

let reserve_word e = ormap (fun acc -> e = acc) reserved_word_list;;

let check_var s = if (reserve_word s) then raise X_Reserve_Word else Var(s);;

let quote_body body = match body with  (* forum *)
      | Pair(exp, Nil) -> Const(Sexpr(exp))
      | _-> raise X_no_match;;
      
let if_body body = match body with
        | Pair(test, Pair(dit, rest))-> (match rest with
                  | Pair(dut, Nil) -> (test, dit, dut)
                  | Nil -> (test, dit, Nil)
                  |_ -> raise X_no_match)
        | _ -> raise X_no_match;;

let rec proper_list lst = match lst with  
          | Nil-> true
          | Pair(_ , cdr) -> proper_list cdr
          | _ -> false;;


let rec simple_lambda_args_helper args lst = match args with         
        | Pair(Symbol(s), rest) -> simple_lambda_args_helper rest (lst@[s])
        | Nil -> lst 
        | _-> raise X_no_match;;

let simple_lambda_args args = simple_lambda_args_helper args [];;

let rec opt_lambda_args_helper args lst = match args with         
        | Pair(Symbol(s), rest) -> opt_lambda_args_helper rest (lst@[s])
        | Symbol(after_dot) -> (lst, after_dot)
        |_-> raise X_no_match;;

let rec inside_pair_helper args lst = match args with         
      | Pair(s, rest) -> inside_pair_helper rest (lst@[s])
      | Nil -> lst
      | _ -> (lst@[args]);;

let inside_pair args = inside_pair_helper args [];;

let lambda_opt_args args = opt_lambda_args_helper args [];;

let parse_set body = match body with
          | Pair(var, Pair(value, Nil)) -> (var, value)
          | _-> raise X_no_match;;

let rec let_vars vexps vars = match vexps with 
          | Pair(Pair(Symbol(s), body), rest) -> let_vars rest (vars@[s])
          | Nil -> vars
          | _-> raise X_invalid_let;;
let rec mit_vars exp acc= match exp with 
          | Pair(Symbol(s),rest) -> mit_vars rest (acc@[s])
          | Nil -> acc
          | _ -> raise X_invalid_MIT_define
;;

let rec let_exps vexps exps = match vexps with 
          | Pair(Pair(s, Pair(body, Nil)), rest) -> let_exps rest (exps@[body])
          | Nil -> exps
          | _ -> raise X_invalid_let;;
let rec flip lst = match lst with 
          | first::rest -> (flip rest)@[first]
          | [] -> []

let rec whatever_rec exps = match exps with
          | Pair(Pair(s, exp), rest) -> Pair(Pair(s, Pair(String("whatever"), Nil)), whatever_rec rest)
          | Nil -> Nil
          | _ -> raise X_invalid_let_rec;;
          
let rec whatever_set exps body = match exps with 
          | Pair(Pair(s, exp), rest) -> Pair(Pair(Symbol("set!"), Pair(s, exp)), (whatever_set rest body))
          | Nil -> Pair(Pair(Symbol("let"), Pair(Nil, body)), Nil)
          | _ -> raise X_invalid_let_rec;;

let rec tag_parse e = match e with
      | Number(num) -> number_to_const e
      | Bool(b) -> Const(Sexpr(e))
      | Char(c) -> Const(Sexpr(e))
      | String(s) -> Const(Sexpr(e))
      | Symbol(s) -> check_var s
      | Pair(Symbol("quote"), body) -> quote_body body (* forum *)
      | Pair(Symbol("define"),Pair(Pair(Symbol(s),lst), rest)) -> expand_define (Pair(Pair(Symbol(s),lst), rest))
      | Pair(Symbol("define"), body) -> parse_define body
      | Pair(Symbol("if"), body) -> parse_if body                 
      | Pair(Symbol("lambda"), Pair(args, exps)) -> parse_lambda args exps
      | Pair(Symbol("and"), rest) -> parse_and rest
      | Pair(Symbol("or"), rest) -> Or(List.map tag_parse (inside_pair rest))
      | Pair(Symbol("set!"), rest) -> let (var, value) = parse_set rest in Set(tag_parse var, tag_parse value)
      | Pair(Symbol("begin"), rest) -> parse_begin_sequence rest
      | Pair(Symbol("pset!"), rest) -> expand_pset rest 
      | Pair(Symbol("let"), rest) -> expand_let rest
      | Pair(Symbol("let*"), rest) -> expand_let_star rest
      | Pair(Symbol("letrec"), rest) -> expand_let_rec rest
      | Pair(Symbol("cond"), rest) -> expand_cond rest 
      | Pair(Symbol("quasiquote"),Pair(exp,Nil)) -> expand_quasiquote exp
      | Pair(car, cdr) -> Applic(tag_parse(car), List.map tag_parse (inside_pair cdr))
      | Nil -> Const(Void)


and parse_if body = let (test, dit, dut) = if_body body in
              (match dut with
              | Nil -> If(tag_parse(test), tag_parse(dit), Const(Void))
              | _-> If(tag_parse(test), tag_parse(dit), tag_parse(dut))
              )
              
and parse_lambda args exps = let body = match exps with | Pair(b, q) -> exps | _ -> raise X_empty_lambda_body in (* body not empty, check -> improper body list *)
                        let seq = Seq(List.map tag_parse (inside_pair body)) in
                            if (proper_list args) 
                                    then 
                                    (let (args) = simple_lambda_args args in LambdaSimple(args, seq)) 
                                    else 
                                    (let (args, last) = lambda_opt_args args in LambdaOpt(args, last, seq))
  
and parse_and rest = match rest with (* forum *)
                | Nil -> Const(Sexpr(Bool(true)))
                | Pair(exp, Nil)-> tag_parse exp
                | Pair(exp, rest) -> If(tag_parse exp, tag_parse (Pair(Symbol("and"), rest)), Const(Sexpr(Bool(false))))
                |_-> raise X_no_match 
       
and parse_define body =  match body with
                | Pair(var, vl) -> let value = (match vl with 
                                        | Pair(vl, Nil) -> vl
                                        |_-> raise X_syntax_error)
                in Def(tag_parse var, tag_parse value)
                | _ -> raise X_no_match

and parse_begin_sequence body = match body with
        | Nil -> Const(Void)
        | Pair(s, Nil) -> tag_parse s
        | Pair(s, rest) -> Seq(no_base_begin body [])
        |_ -> raise X_not_supported_forum

and no_base_begin body seq = match body with
        | Nil -> seq
        | Pair(Pair(Symbol("begin") ,rest), rest2) -> no_base_begin rest2 (no_base_begin rest seq) 
        | Pair(exp ,rest) -> no_base_begin rest (seq@[tag_parse exp])
        | _ -> seq@[tag_parse body]

and expand_let exps_body = match exps_body with
          | Pair(exps, body) -> (let body = inside_pair body in
                                let vars = (let_vars exps []) in
                                let exps = (let_exps exps []) in
                                Applic(LambdaSimple(vars, Seq(List.map tag_parse body)), List.map tag_parse exps)
                                )
          | _ -> raise X_invalid_let

and expand_let_star exps_body = match exps_body with
            | Pair(Nil, body) -> expand_let exps_body
            | Pair(Pair(s, Nil), body) -> expand_let exps_body
            | Pair(Pair(exp, rest), body) -> expand_let (Pair(Pair(exp, Nil), Pair(Pair(Symbol("let*"), Pair(rest, Pair(body, Nil))), Nil)))
            | _ -> raise X_invalid_let_star

and expand_let_rec exps_body = match exps_body with
          | Pair(exps, body) -> let whatever = whatever_rec exps in
                                let whatever_set = whatever_set exps body in
                                tag_parse (Pair(Symbol("let"), Pair(whatever, whatever_set)))
          | _ -> raise X_invalid_let_rec
                                        
and zip paired_lists =
      match paired_lists with
      | [], [] -> []
      | h1::t1, h2::t2 -> (h1, h2)::(zip (t1, t2))
      | _ -> raise X_not_supported_forum

and expand_pset lst = 
                    let cdrE =  let_exps lst [] in
                    let carE =  let_vars lst [] in
                    Seq(expand_pset_rec ((zip (carE, cdrE))) [])

and expand_pset_rec lst ret = match lst with 
                | (car, cdr)::rest -> expand_pset_rec rest ret@[Set(Var(car), tag_parse cdr)]
                | [] -> ret
                    
and expand_cond lst = match lst with 
                | Nil -> Const(Void)
                | Pair(Pair(exp, Pair(Symbol("=>"), Pair(func, Nil))), rest) ->
                  
                let theValue = Pair(Symbol("value"),Pair(exp,Nil)) in 
                let func = Pair(Symbol("f"),Pair(Pair(Symbol("lambda"),Pair(Nil, Pair(func,Nil))),Nil)) in             
                      let res =  Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"),Pair(Nil, (Pair(Pair(Symbol("cond"), rest),Nil)))),Nil)) in
                      let body = (Pair (Symbol "if",
                        Pair (Symbol "value",
                        Pair (Pair (Pair (Symbol "f", Nil), Pair (Symbol "value", Nil)),
                          Pair (Pair (Symbol "rest", Nil), Nil))))) in
                        let let_args = Pair(theValue,Pair(func, Pair(res, Nil))) in
                        let let_expr = Pair(Symbol("let"), Pair(let_args, Pair(body,Nil))) in
                        tag_parse let_expr
                | Pair (Pair(Symbol("else"), seq),_ ) -> tag_parse(Pair(Symbol("begin"),seq))
                | Pair(Pair(exp, seq), rest) -> let test = tag_parse(exp) in
                                  let thenn = tag_parse (Pair(Symbol("begin"),seq)) in 
                                  let elsee = tag_parse (Pair(Symbol("cond"), rest))  in 
                                  If(test, thenn, elsee)
                | _ -> raise X_no_match

and expand_define exp = match exp with
  | Pair(Pair(Symbol(s),lst), rest) ->
          let body_of_lambda = tag_parse rest in
          let vars = mit_vars lst [] in
          Def(tag_parse (Symbol(s)), LambdaSimple(vars, body_of_lambda))
  | _ -> raise X_invalid_MIT_define


and expand_quasiquote exp = match exp with
  | Pair(Symbol("unquote"), Pair(exp,Nil)) -> tag_parse exp
  | Pair(Symbol("unquote-splicing"),Pair(exp,Nil)) -> raise X_invalid_quatisquote
  | Pair(Pair(Symbol("unquote"),Pair(exp,Nil)),rest) -> Applic(Var("cons"), [(tag_parse exp); (expand_quasiquote rest)])
  | Pair(Pair(Symbol("unquote-splicing"),Pair(exp,Nil)),rest) -> Applic(Var("append"), [(tag_parse exp); (expand_quasiquote rest)])
  | Nil -> Const(Sexpr(Nil))
  | Pair(exp,rest) -> Applic(Var("cons"),[Const(Sexpr(exp)); (expand_quasiquote rest)])


  | _ -> Const(Sexpr(exp));;


let tag_parse_expressions e = List.map tag_parse e;;             
end;;



(* #use "tag-parser.ml";; *)

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
  
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e = raise X_not_yet_implemented;;

let annotate_tail_calls e = raise X_not_yet_implemented;;

let box_set e = raise X_not_yet_implemented;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;;
 (* struct Semantics *)

 (* let annotate_lexical_addresses e =  *)
 let tags e = (Tag_Parser.tag_parse_expressions (Reader.read_sexprs e));;

 (* let annotate_lexical_addresses e = let exps = tags e in *)