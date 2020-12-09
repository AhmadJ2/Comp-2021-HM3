
#use "reader.ml";;
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


