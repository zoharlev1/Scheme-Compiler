(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)
#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;

type env = Env of string list;;

let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct
let rec place_at lst element indx =
  match lst with
  | [] -> -1
  | car::cdr ->
    if (car = element) then indx
    else place_at cdr element (indx + 1);;

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;
(*------------------------------------------------lexical address----------------------------------------------------*)
  (* run this first! *)
  let annotate_lexical_addresses pe = 
   let rec run pe params env =
      match pe with 
      |ScmConst(var)-> ScmConst'(var)
      |ScmVar(var)-> ScmVar'(tag_lexical_address_for_var var params env)
      |ScmIf(tst,thn,els) -> ScmIf'((run tst params env),(run thn params env),(run els params env))
      |ScmSeq(exprlist) -> ScmSeq'(map_list exprlist params env)
      |ScmSet(ScmVar(var),exp) -> 
        ScmSet'((tag_lexical_address_for_var var params env), (run exp params env))
      |ScmDef(ScmVar(var),exp) -> ScmDef'((tag_lexical_address_for_var var params env), (run exp params env))
      |ScmOr(exprlist) -> ScmOr'(map_list exprlist params env)
      |ScmLambdaSimple(arguments, body) -> ScmLambdaSimple'(arguments,(run body arguments (params::env)))
      |ScmLambdaOpt(arguments,opt_arguments,body) -> ScmLambdaOpt'(arguments,opt_arguments,(run body (arguments@[opt_arguments]) (params::env)))
      |ScmApplic(expr,exprlist) -> ScmApplic'((run expr params env),(map_list exprlist params env))
      |_ -> raise X_this_should_not_happen

    and map_list list params env =
    (List.map (fun x -> (run x params env)) list)
   in 
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  (*--------------------------------------------------------------- tail ------------------------------------------------*)
  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail =
  match pe, in_tail with 
    | ScmSeq'(s),_ -> ScmSeq'(List.mapi (fun i e -> if (i != ((List.length s) -1)) then run e false else run e in_tail) s)
    | ScmOr'(list) ,_ -> ScmOr'(List.mapi (fun i e -> if (i != ((List.length list) -1)) then run e false else run e in_tail) list)
    | ScmIf'(test, dit,dif), _ -> ScmIf'(run test false, run dit in_tail, run dif in_tail)
    | ScmSet'(var, expr), _ -> ScmSet' (var, run expr false)
    | ScmDef'(var, expr),_ -> ScmDef'(var, run expr false)
    | ScmLambdaSimple'(args,body),_-> ScmLambdaSimple'(args,run body true)
    | ScmLambdaOpt'(args,optionalargs,body),_-> ScmLambdaOpt'(args,optionalargs,(run body true))
    | ScmApplic'(exp,list),true -> ScmApplicTP'(run exp false,(applic_map list))
    | ScmApplic'(exp,list),false -> ScmApplic'(run exp false,(applic_map list))
    | ScmApplicTP'(exp,list),_ -> ScmApplicTP'(run exp false ,(applic_map list))
    |_,_ -> pe
    
    and applic_map list = 
    (List.map(fun a -> run a false) list)

   in 
   run pe false ;;

  (* boxing------------------------------------------------------------------------------------ *)
let find_reads name enclosing_lambda expr = raise X_not_yet_implemented
let rec run depth env exp params =
  match exp with
  | ScmConst'(x) -> ([],[])
  | ScmDef'(var1,val1) -> let (r1, w1) = (run depth env val1 params) in
                          (r1 ,List.append (write_var depth env params var1) w1 )
  | ScmSet'(var1,val1) -> let (r1, w1) = (run depth env val1 params) in
                          (r1 ,List.append (write_var depth env params var1) w1 )
  | ScmIf'(test, dit, dif) ->  write_append (write_append (run depth env test params) (run depth env dit params)) (run depth env dif params)
  | ScmVar'(expr) -> (write_scmvar depth env params expr)
  | ScmSeq'(exprs) ->  List.fold_left (fun acc exp -> write_append acc (run depth env exp params)) ([],[]) exprs
  | ScmOr'(exprs) -> List.fold_left (fun acc exp -> write_append acc (run depth env exp params)) ([],[]) exprs
  | ScmLambdaSimple'(args,body) -> (run (depth +1) (params::env) body (Env args)) 
  | ScmLambdaOpt'(args, opt, body) -> run (depth +1) (params::env) body (Env((List.append args [opt])))
  | ScmApplic'(op, args) -> (write_append (run depth env op params) (List.fold_left (fun acc exp -> write_append acc (run depth env exp params)) ([],[]) args))
  | ScmApplicTP'(op, args) -> (write_append (run depth env op params) (List.fold_left (fun acc exp -> write_append acc (run depth env exp params)) ([],[]) args))
  | ScmBoxSet'(var,val1) -> (run depth env val1 params)
  | ScmBoxGet'(var) -> ([],[])
  | ScmBox'(var) -> ([],[])

  and write_scmvar depth env params expr =
  match expr with 
  | VarFree(var) -> ([],[])
  | VarParam(var,minor) -> if (depth == 0) then ([var, params::env],[]) else ([],[])
  | VarBound(var,major,minor) -> if (depth -1 == major) then ([var, params::env],[]) else ([],[])

  and write_var depth env params expr =
  match expr with
  | VarFree(var) -> []
  | VarParam(var,minor) -> if (depth == 0) then [var, params::env] else []
  | VarBound(var,major,minor) -> if (depth - 1 == major) then [var, params::env] else []

  and write_append (read1,write1) (read2,write2) =
  let lst1 = List.append read1 read2 in
  let lst2 = List.append write1 write2 in
  (lst1, lst2)

(* box var ------------------------------------------------------------------------------ --------*)
let rec var_box name expr1 =
  match expr1 with
  | ScmDef'(var1,val1) -> ScmDef'(var1, var_box name val1)
  | ScmIf'(test, dit, dif) -> ScmIf'(var_box name test, var_box name dit, var_box name dif)
  | ScmBoxSet'(var1, val1) -> ScmBoxSet'(var1, var_box name val1)
  | ScmVar'(expr) -> (box_scm_var expr name)
  | ScmSeq'(expr) -> ScmSeq'(List.map (fun x -> var_box name x) expr) 
  | ScmOr'(expr) -> ScmOr'(List.map (fun x -> var_box name x) expr) 
  | ScmSet'(var1,ScmBox'(var2)) -> ScmSet'(var1,ScmBox'(var2))
  | ScmSet'(var1,val1) -> if ((get_name (ScmVar'(var1))) = name) then ScmBoxSet'(var1,var_box name val1) else ScmSet'(var1,var_box name val1)
  | ScmLambdaSimple'(args, body) -> if (List.mem name args) then expr1 else ScmLambdaSimple'(args, var_box name body)
  | ScmLambdaOpt'(args, opt, body) -> if (List.mem name (List.append args [opt])) then expr1 else ScmLambdaOpt'(args, opt, var_box name body)
  | ScmApplic'(op, args) -> ScmApplic'(var_box name op, List.map (fun x -> var_box name x) args)
  | ScmApplicTP'(op, args) -> ScmApplicTP'(var_box name op, List.map (fun x -> var_box name x) args)
  | _ -> expr1

  and  get_name expr =
  match expr with
  | ScmVar'(VarFree(var1)) -> var1
  | ScmVar'(VarParam(var1,_)) -> var1
  | ScmVar'(VarBound(var1,_,_)) -> var1
  | _ -> raise X_this_should_not_happen 

  and box_scm_var var name =
  match var with
  | VarFree(var1) -> ScmVar'(VarFree(var1))
  | VarParam(var1,minor) -> if (var1 = name) then ScmBoxGet'(VarParam(var1,minor)) else ScmVar'(VarParam(var1,minor))
  | VarBound(var1, major, minor) -> if (var1 = name) then ScmBoxGet'(VarBound(var1,major,minor)) else ScmVar'(VarBound(var1,major,minor))


  (*box set --------------------------------------------------------------------------------------------------------------------------------- *)
  let rec box_set expr =
   match expr with
    | ScmConst'(var1) -> ScmConst'(var1)
    | ScmVar'(var1) -> ScmVar'(var1)
    | ScmIf'(test,dit,dif) -> ScmIf'((box_set test),(box_set dit),(box_set dif))
    | ScmOr'(exprs) -> ScmOr'(List.map box_set exprs)
    | ScmSeq'(exprs) -> ScmSeq'(List.map box_set exprs)
    | ScmSet'(var1, val1) -> ScmSet'(var1 , (box_set val1))
    | ScmDef'(var1, val1) -> ScmDef'(var1 , (box_set val1))
    | ScmBox'(var1) -> ScmBox'(var1)
    | ScmBoxGet'(var1) -> ScmBoxGet'(var1)
    | ScmBoxSet'(var1, val1) -> ScmBoxSet'(var1 , (box_set val1))
    | ScmApplic'(op, args) -> ScmApplic'((box_set op), (List.map box_set args))
    | ScmApplicTP'(op, args) -> ScmApplicTP'((box_set op), (List.map box_set args))
    | ScmLambdaSimple'(args, body) -> (lambda_boxing(ScmLambdaSimple'(args, box_set body)))
    | ScmLambdaOpt'(args, opt, body) -> (lambda_boxing(ScmLambdaOpt'(args, opt, box_set body))) 


    and  lambda_boxing expr =
    let (args,body) = match expr with
                      | ScmLambdaSimple'(args,body) -> (args,body)
                      | ScmLambdaOpt'(args, opt, body) -> (args@[opt],body)
                      | _ -> raise X_this_should_not_happen  in
    match args with 
    | [] -> expr
    | _ -> let (r1, w1) = (run 0 [] body (Env(args))) in
           let lst = (List.fold_left (fun acc (v1, e1) -> if (List.exists (fun (v2, e2) -> matching_vars v1 v2 e1 e2) w1) then v1::acc else acc ) [] r1) in
           let lst = (List.fold_right (fun x acc -> if (List.mem x lst) then x::acc else acc) args []) in
           if (lst == []) then expr else 
                let set = List.map (fun name -> ScmSet'(VarParam(name, place_at args name 0),ScmBox'(VarParam(name, place_at args name 0)))) lst in
                let changed_body = change_body body set in
                let changed_body = List.fold_left (fun acc var -> var_box var acc) changed_body lst in
                match expr with
                | ScmLambdaSimple'(args,_) -> ScmLambdaSimple'(args, changed_body)
                | ScmLambdaOpt'(args, opt, _) -> ScmLambdaOpt'(args, opt, changed_body)
                | _ -> raise X_this_should_not_happen

    and change_body body set =
    match body with
    | ScmSeq'(exprs) -> ScmSeq'(List.append set exprs)
    | exp -> ScmSeq'(List.append set [exp]) 

    and matching_vars var1 var2 env1 env2 =
      let rec check_rib (env1:env list) (env2:env list) =
        match env1,env2 with
        | [] , [] -> true
        | [] , hd::rest -> false
        | hd::rest , [] -> false
        | hd1::rest1 , hd2::rest2 -> let pred1 = (hd1 == hd2) in
                                     match pred1 with
                                     | true -> check_rib rest1 rest2 
                                     | false -> false in
                                     let pred2 = (var1 = var2) && (not (check_var_in_env var1 env1 env2)) && (not (check_rib env1 env2)) in
                                     pred2

    and check_var_in_env var (env1:env list) (env2:env list) =
    match env1 with
      | [] -> false
      | hd::rest -> if ((List.exists (fun x -> x == hd) env2) && (not (List.mem var (get_env hd)))) then true else (check_var_in_env var rest env2)

    and get_env (env:env) =
    let Env(e) = env in
    e

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)