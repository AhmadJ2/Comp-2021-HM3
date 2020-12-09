#use "pc.ml";;
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
