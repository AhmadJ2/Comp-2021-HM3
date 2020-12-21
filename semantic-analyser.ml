#use "tag-parser.ml";;
open Tag_Parser;;
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
                       
exception X_invalid_expr;;
exception Var_Not_Here_Param;;
exception Var_Not_Here_Bound;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val bx : string -> expr' list
  val tl : string -> expr' list
end;;

module Semantics : SEMANTICS = struct

 (* struct Semantics *)
(* end;; *)

let rec lex env expr =  match expr with
      | Const(x)-> Const'(x)
      | Or(lst) -> Or'(List.map (lex env) lst )
      | If(test, thn , alt) -> If'(lex env test, lex env thn , lex env alt)
      | Seq(lst) -> Seq'(List.map (lex env) lst)
      | LambdaSimple(slst, expr) -> LambdaSimple'(slst, lex (slst::env) expr) 
      | LambdaOpt(slst ,s, expr) -> LambdaOpt'(slst, s, lex (slst::env) expr)
      | Def(Var(s), vl) -> Def'(VarFree(s), lex env vl)
      | Set(Var(vr),vl) -> Set'(check_vars env vr, lex env vl)
      | Var(v) -> Var'(check_vars env v)
      | Applic(expr, lst_expr) -> Applic'(lex env expr, (List.map (lex env) lst_expr))
      | _-> raise X_invalid_expr


and search_lst line_env vr n = 
    match line_env with
      | v::rest -> (if v=vr then n else search_lst rest vr (n+1))
      | [] -> raise Var_Not_Here_Param

and search_bound env vr minor = match env with
      | env::rest -> (try(let major = (search_lst env vr 0) in (minor, major)) 
              with Var_Not_Here_Param -> search_bound rest vr (minor+1))
      | [] -> raise Var_Not_Here_Bound


and check_vars env vr = match env with
      | [] -> VarFree(vr)
      | env::rest -> try VarParam(vr, search_lst env vr 0) 
            with Var_Not_Here_Param -> (try(let (minor, major) = search_bound rest vr 0 
                in VarBound(vr,minor, major))
                  with Var_Not_Here_Bound -> VarFree(vr))                
;;
let annotate_lexical_addresses e = lex [] e ;;


let rec tails b e = 
        if b != 0 then check_if_lambda e 
        else
        match e with
      | If'(test, thn, alt) -> If'(test, check_if_app b thn, check_if_app b alt)
      | Seq'(lst) -> (if (List.length lst) = 1 then check_if_app b (List.nth lst 0) 
                        else let(lst, last) = pari_last lst [] in 
                            Seq'(lst@[check_if_app b last]))
      | Applic'(e, exps) ->  Applic'(e, List.map (tails 1) exps)
      | LambdaSimple'(vars, body) -> LambdaSimple'(vars, check_if_app 0 body)
      | LambdaOpt'(vars,s, body) -> LambdaOpt'(vars, s, check_if_app 0 body)
      | Or'(lst) -> let(lst, last) = pari_last lst [] in Or'(lst@[check_if_app b last])
      | _ -> e

and pari_last lst_exp lst = 
            if (List.length lst_exp) = 1 then 
                  (lst, List.nth lst_exp 0) 
                else match lst_exp with
                  | f::rest -> pari_last rest (lst@[check_if_lambda f])
                  | _ -> raise X_invalid_expr

and check_if_app b expr = match expr with
      | Applic'(x, w) -> ApplicTP'(x, List.map (tails 1) w)
      | _ -> tails b expr
      
and check_if_lambda expr = match expr with
    | LambdaSimple'(e, body) -> LambdaSimple'(e, check_if_app 0 body)
    | LambdaOpt'(e, s, body) -> LambdaOpt'(e, s, check_if_app 0 body)
    | Applic'(e, exps) ->  Applic'(e, List.map (tails 1) exps)
    | Seq'(exps) -> Seq'(List.map (tails 1) exps)
    | _-> expr
      ;;


let annotate_tail_calls e = match e with
      | Applic'(e, exps) -> ApplicTP'(e, List.map (tails 1) exps)
      | _ -> tails 0 e;;


let rec boxes exprs = match exprs with
    | LambdaSimple'(vars, seq) -> LambdaSimple'(vars, chech_if_vars_need_to_box vars 0 (boxes seq) )
    | LambdaOpt'(vars,s, seq) -> LambdaOpt'(vars, s, chech_if_vars_need_to_box (vars@[s]) 0 (boxes seq) )
    | If'(test, thn, alt) -> If'(boxes test, boxes thn, boxes alt)
    | Or'(seq) -> Or'(List.map boxes seq)
    | Set'(var, vl) -> Set'(var, boxes vl)
    | Seq'(seq) -> Seq'(List.map boxes seq)
    | Def'(var, vl) -> Def'(var, boxes vl)
    | Applic'(op, seq) -> Applic'(boxes op, List.map boxes seq)
    | ApplicTP'(op, seq) -> ApplicTP'(boxes op, List.map boxes seq)
    | _ -> exprs

and chech_if_vars_need_to_box vars minor seq = 
    match vars with
        | v::rest -> (let change = levels v 0 seq in 
              if change = 1 then 
              (let new_seq = change_to_box v minor seq in 
                    chech_if_vars_need_to_box rest (minor + 1) new_seq) 
              else 
                    chech_if_vars_need_to_box rest (minor + 1) seq
              )
        | [] -> seq

(* on the stack *)
and levels var f seq = match seq with
      | Var'(VarParam(v, _)) -> 0
      | Var'(VarBound(v, _, _)) -> 0
      | Set'(v, expr) -> levels var f expr
      | Seq'(seq) -> check_seq var f seq 
      | LambdaOpt'( _) -> 0
      | LambdaSimple'( _) -> 0
      | If'(test ,thn, alt) -> let test = levels var f test in
                                let thn = levels var f thn in
                                let alt = levels var f alt in
                                    if test=1 || thn=1 || alt=1 then 1 else 0
      | Or'(seq) -> let seq1 = check_seq_app var 1 seq in
                    let seq2 = check_seq var 1 seq in
                      if seq2 = 1 || seq1=1 then 1 else 0
      | Applic'(op, seq) -> let op = levels var f op in
                              let seq1 = check_seq_app var 1 seq in
                              let seq2 = check_seq var 1 seq in
                                if seq2 = 1 || seq1=1 || op = 1 then 1 else 0
      | ApplicTP'(op, seq) -> let op = levels var f op in
                              let seq1 = check_seq_app var 1 seq in
                              let seq2 = check_seq var 1 seq in
                                if seq1 = 1 || seq2=1 || op = 1 then 1 else 0                              
      | _ -> 0

and check_lower_levels var f exp = match exp with 
      | Var'(VarParam(v, _)) -> (f,0)
      | Set'(VarParam(v, _), exp) -> if v=var then (let (read, write) = check_lower_levels var f exp in (read, if f>write then f else write)) else check_lower_levels var f exp
      | Var'(VarBound(v, _, _)) -> if v=var then (1, 0) else (0,0)
      | Set'(VarBound(v, _, _), exp) -> let (read, write) = check_lower_levels var f exp in (read, if v=var then 1 else write)
      | LambdaSimple'(vars, seq) -> if (check_if_in_there vars var) then (0,0) else (match seq with | Seq'(seq) -> do_inner_job var f seq | _ -> check_lower_levels var f seq)
      | LambdaOpt'(vars, s, seq) -> if ((check_if_in_there vars var)|| s=var) then (0,0) else (match seq with | Seq'(seq) -> do_inner_job var f seq | _ -> check_lower_levels var f seq)
      | Applic'(op, seq) -> do_inner_job var f (op::seq)
      | ApplicTP'(op, seq) -> do_inner_job var f (op::seq)
      | Or'(seq) -> do_inner_job var f seq

      | _-> (0,0)

and do_inner_job var f seq = let (lst) = List.map (check_lower_levels var f) seq in
            List.fold_right (fun (r, w) (r_acc, w_acc) -> let r = if r_acc = 1 || r = 1 then 1 else 0 in
                                                          let w =  if w_acc = 1 || w = 1 then 1 else 0 in (r, w)) 
                                                          lst (0, 0)

and do_the_job (acc_read, acc_write) seq = match seq with
              | (read, write):: rest -> if ((read=1 && acc_write>0) || write=1 && acc_read>0) then 1 else (do_the_job (read+acc_read, write+acc_write) rest)
              | [] -> 0

and check_seq var f seq = let(seq_read_write) = List.map (check_lower_levels var f) seq in do_the_job (0,0) seq_read_write

and check_seq_app var f seq = let(seq_read_write) = List.map (levels var f) seq in if (List.exists (fun x-> x=1) seq_read_write) then 1 else 0

and change_to_box var minor seq = let seq = match seq with | Seq'(seq) -> [Set'(VarParam(var, minor), Box'(VarParam(var, minor)))]@seq | _ -> [Set'(VarParam(var, minor), Box'(VarParam(var, minor)))]@[seq] in 
            Seq'(List.map (change_to_box_helper var) seq)

and check_if_in_there vars var = List.exists (fun x-> x=var) vars

and change_to_box_helper var exp  = match exp with
      | Set'(VarParam(v, pos), exp) -> BoxSet'(VarParam(v, pos), change_to_box_helper var exp)
      | Set'(VarBound(v, min, maj), exp) -> BoxSet'(VarBound(v, min, maj), change_to_box_helper var exp)
      | Var'(v) ->  (match v with | VarParam(vr, m) -> if vr=var then BoxGet'(v) else exp
                                  | VarBound(vr, min, maj) -> if vr=var then BoxGet'(v) else exp
                                  |_ -> exp)
      | Applic'(op, seq) -> Applic'(change_to_box_helper var op, List.map (change_to_box_helper var) seq)
      | ApplicTP'(op, seq) -> ApplicTP'(change_to_box_helper var op, List.map (change_to_box_helper var) seq)
      | If'(test, thn, alt) -> If'(change_to_box_helper var test, change_to_box_helper var thn, change_to_box_helper var alt)
      | Or'(seq) -> Or'(List.map (change_to_box_helper var) seq)
      | Seq'(seq) -> Seq'(List.map (change_to_box_helper var) seq)
      | LambdaSimple'(vars, seq) -> if check_if_in_there vars var then exp else LambdaSimple'(vars, change_to_box_helper var seq)
      | LambdaOpt'(vars, s, seq) -> if (check_if_in_there vars var) || s=var then exp else LambdaOpt'(vars, s, change_to_box_helper var seq)
      | _ -> exp;;

let box_set e = boxes e;;



let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;


let tags e = (Tag_Parser.tag_parse_expressions (Reader.read_sexprs e));;
let lx e = List.map annotate_lexical_addresses (tags e);;
let tl e = List.map annotate_tail_calls (lx e);;
let bx e = List.map box_set (tl e);;

end;;