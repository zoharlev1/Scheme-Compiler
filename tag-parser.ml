#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;



let rec simpletostring args  = 
  match args with
| ScmPair(ScmSymbol(head),tail) -> ((head)::(simpletostring tail))
| ScmNil -> []
| _ -> raise (X_syntax_error(args,"error in simple to string"))


let rec improper_list_to_args_without_final args=
  match args with 
 | ScmPair(ScmSymbol(head),ScmSymbol(rest)) -> [head]
 | ScmPair(ScmSymbol(head), tail)-> ((head)::(improper_list_to_args_without_final tail))
 | ScmSymbol(final)->[]
 | _ -> raise (X_syntax_error(args,"error in improper list to args with out final"))


let rec final_arg_in_improper args = 
  match args with 
| ScmPair(ScmSymbol(head),ScmSymbol(final))-> final
| ScmPair(ScmSymbol(head), tail)-> (final_arg_in_improper tail)
| ScmSymbol(final)-> final
| _ -> raise (X_syntax_error(args,"error in final arg in improper"))

    let rec list_to_proper_list = function
    | [] -> ScmNil
    | hd::[] -> ScmPair (hd, ScmNil)
    | hd::tl -> ScmPair (hd, list_to_proper_list tl);;
    
    let rec list_to_improper_list = function
    | [] -> raise X_proper_list_error
    | hd::[] -> hd
    | hd::tl -> ScmPair (hd, list_to_improper_list tl);;
    
    let rec scm_append scm_list sexpr =
    match scm_list with
    | ScmNil -> sexpr
    | ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
    | _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))
    
    let rec scm_map f sexpr =
    match sexpr with
    | ScmNil -> ScmNil
    | ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
    | _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;
    
    let rec scm_zip f sexpr1 sexpr2 =
    match sexpr1, sexpr2 with
    | ScmNil, ScmNil -> ScmNil
    | ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
    | _, _ ->
        let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
        raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;
    
    let rec scm_list_to_list = function
    | ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
    | ScmNil -> []
    | sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;
    
    let rec scm_is_list = function
    | ScmPair (hd, tl) -> scm_is_list tl
    | ScmNil -> true
    | _ -> false
    
    let rec scm_list_length = function
    | ScmPair (hd, tl) -> 1 + (scm_list_length tl)
    | ScmNil -> 0
    | sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;
    
    let rec untag expr =
    let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
    let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in
    
    let untag_lambda_opt vars var body =
    let vars = match vars with
    | [] -> ScmSymbol var
    | _ -> list_to_improper_list (untag_vars (vars@[var])) in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in
    
    match expr with
    | (ScmConst (ScmSymbol(_) as sexpr)
        | ScmConst (ScmNil as sexpr)
        | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
    | ScmConst s -> s
    | ScmVar (name) -> ScmSymbol(name)
    | ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
    | ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
    | ScmSeq(exprs) -> untag_tagged_list "begin" exprs
    | ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
    | ScmDef (var, value) -> untag_tagged_list "define" [var; value]
    | ScmOr (exprs) -> untag_tagged_list "or" exprs
    | ScmLambdaSimple (vars, ScmSeq(body)) ->
        let vars = list_to_proper_list (untag_vars vars) in
        let body = List.map untag body in
        list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
    | ScmLambdaSimple (vars, body) ->
        let vars = list_to_proper_list (untag_vars vars) in
        list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
    | ScmLambdaOpt (vars, var, ScmSeq(body)) ->
        let body = List.map untag body in
        untag_lambda_opt vars var body
    | ScmLambdaOpt (vars, var, body) ->
        let body = [untag body] in
        untag_lambda_opt vars var body
    | ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;
    
    
    let rec string_of_expr expr =
    string_of_sexpr (untag expr)
    
    let scm_number_eq n1 n2 =
    match n1, n2 with
    | ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
            numerator1 = numerator2 && denominator1 = denominator2
    | ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
    | _, _ -> false
    
    let rec sexpr_eq s1 s2 =
    match s1, s2 with
    | (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
    | ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
    | ScmChar(char1), ScmChar(char2) -> char1 = char2
    | ScmString(string1), ScmString(string2) -> String.equal string1 string2
    | ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
    | ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
    | ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
    | ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
    | _, _ -> false
    
    let rec expr_eq e1 e2 =
      match e1, e2 with
      | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
      | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
      | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                                (expr_eq dit1 dit2) &&
                                                  (expr_eq dif1 dif2)
      | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
            List.for_all2 expr_eq exprs1 exprs2
      | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
            (expr_eq var1 var2) && (expr_eq val1 val2)
      | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
         (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
      | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
         (String.equal var1 var2) &&
           (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
      | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
         (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
      | _ -> false;;
    
    module type TAG_PARSER = sig
      val tag_parse_expression : sexpr -> expr
    end;; 
    
    module Tag_Parser : TAG_PARSER = struct
    
    let reserved_word_list =
      ["and"; "begin"; "cond"; "define"; "else";
       "if"; "lambda"; "let"; "let*"; "letrec"; "or";
       "quasiquote"; "quote"; "set!"; "unquote";
       "unquote-splicing"];;
    
  let rec tag_parse_expression sexpr =
    let sexpr = macro_expand sexpr in
    match sexpr with 
    | ScmNil -> ScmConst(ScmNil) 
    | ScmBoolean(var) -> ScmConst(ScmBoolean(var))
    | ScmNumber(var) -> ScmConst(ScmNumber(var))
    | ScmChar(var) -> ScmConst(ScmChar(var))
    | ScmString(var) -> ScmConst(ScmString(var)) 
    | ScmSymbol(var) -> if (List.mem var reserved_word_list) then raise (X_reserved_word(var)) else ScmVar(var)
    | ScmPair(ScmSymbol("quote"), (ScmPair(var, ScmNil))) -> ScmConst(var)
    | ScmPair(ScmSymbol("if"),ScmPair(test,ScmPair(a,ScmPair(b,ScmNil)))) -> ScmIf (tag_parse_expression test , tag_parse_expression a , tag_parse_expression b) 
    | ScmPair(ScmSymbol("if"),ScmPair(test,ScmPair(a,ScmNil))) -> ScmIf (tag_parse_expression test, tag_parse_expression a , ScmConst(ScmVoid)) 
    | ScmPair(ScmSymbol("or"), sexprs) -> tag_parse_or sexprs  
    | ScmPair(ScmSymbol("lambda"), ScmPair(args, body)) -> tag_parse_lambda (args) (body)
    | ScmPair(ScmSymbol("define"), sexprs) -> tag_parse_define sexprs 
    | ScmPair(ScmSymbol("begin"), sexprs) -> tag_parse_seq sexprs
    |ScmPair(ScmSymbol("set!"),ScmPair(name,ScmPair(value,ScmNil)))-> tage_parse_set name value
    | ScmPair(operand, operands) -> ScmApplic((tag_parse_expression operand), List.map tag_parse_expression (scm_list_to_list operands))
    | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

  and tage_parse_set name value =
    match name with
    |ScmSymbol(a) -> ScmSet( ScmVar(a), tag_parse_expression value)
    |_ -> raise (X_syntax_error (ScmNil, "Expected variable on LHS of set!"))

  and tag_parse_define sexprs =
    match sexprs with 
    | ScmPair(ScmSymbol(var), ScmPair(vals, ScmNil)) -> ScmDef(ScmVar(var), tag_parse_expression vals)
    | ScmPair(ScmPair(var, args), ScmPair(body, ScmNil)) -> tag_parse_expression (ScmPair(ScmSymbol("define"), ScmPair(var, ScmPair((ScmPair(ScmSymbol("lambda"), ScmPair(args, ScmPair(body, ScmNil)))), ScmNil))))
    | _ -> raise X_not_implemented
    
  and tag_parse_seq sexprs =
    match sexprs with
    | ScmNil -> ScmConst(ScmVoid)
    | ScmPair(sexpr, ScmNil) -> tag_parse_expression sexpr
    | ScmPair(sexpr, sexprs1) -> ScmSeq (List.map (fun exp -> tag_parse_expression exp)(scm_list_to_list sexprs))
    | _ -> raise (X_syntax_error(sexprs, ("wrong syntax for sequence")))

    
  and tag_parse_lambda args body =
    let flag = scm_is_list args in
    let body_seq = tag_parse_seq body in 
    match flag with
      |true -> let args_new = List.map (fun x -> tag_parse_expression x) (scm_list_to_list args) in
               let args_new = List.map (fun x -> 
                                        match x with
                                        | ScmVar(name) -> name
                                        | _ -> raise X_proper_list_error) args_new in
               ScmLambdaSimple(args_new, body_seq)
      |false -> ScmLambdaOpt((improper_list_to_args_without_final args),(final_arg_in_improper args),body_seq) 


  and tag_parse_or sexprs =
    let list_sexprs = scm_list_to_list sexprs in
    match list_sexprs with 
    | [] -> ScmConst(ScmBoolean(false))
    | hd :: [] -> tag_parse_expression hd 
    | lst -> ScmOr(List.map tag_parse_expression lst)


  and extract_let_args args =
   (List.map (fun arg ->
    match arg with 
    |(ScmPair(var,value)) -> var
    | _ ->raise (X_syntax_error(arg,"wrong arguments of let")))
    (scm_list_to_list args))
  
  and extract_let_values values =
    (List.map (fun val1 ->
    match val1 with 
    |(ScmPair(var,ScmPair(value,ScmNil))) -> value
    | _ ->raise (X_syntax_error(val1,"wrong values of let")))
    (scm_list_to_list values))
    
  
  and parse_let_tag ribs body =
    let args = extract_let_args ribs in 
    let values = extract_let_values ribs in
    if ((scm_list_length body) =0) then 
      raise (X_syntax_error(body,"wrong body of let"))
    else
    ScmPair(ScmPair(ScmSymbol("lambda"),ScmPair((list_to_proper_list args),body)),( list_to_proper_list values))
      
  and first_arg args = 
     ScmPair((List.hd (scm_list_to_list args)),ScmNil)

  and tail_arg args =
    (list_to_proper_list (List.tl (scm_list_to_list args)))

  and let_katen_body ribs body = 
        (macro_expand(ScmPair(ScmSymbol("let*"),ScmPair((tail_arg ribs),body))))

  and make_let_katen ribs body =
        let lenthL = List.length (scm_list_to_list ribs) in
        match lenthL with 
        | 1 -> (ScmPair(ScmSymbol("let"), ScmPair(ribs,body)))
        | _ -> (ScmPair(ScmSymbol("let"),ScmPair((first_arg ribs),ScmPair((let_katen_body ribs body),ScmNil))))

  and tag_parse_and sexprs =
    match sexprs with 
    | ScmNil -> ScmBoolean(true)
    | ScmPair(single, ScmNil) -> single
    | ScmPair(first, rest) -> ScmPair(ScmSymbol("if"), ScmPair(first, ScmPair((tag_parse_and rest), ScmPair(ScmBoolean(false), ScmNil))))
    | _ -> raise(X_syntax_error(sexprs, "illegal and sexpr"))

  and tag_parse_cond ribs = 
     match ribs with
     | ScmNil -> ScmVoid
     | ScmPair(ScmPair(ScmSymbol("else"), exprs), ribs) -> macro_expand (tag_parse_else_rib exprs)
     | ScmPair(ScmPair(exprs1, ScmPair(ScmSymbol("=>"), exprsf)), rest) -> tag_parse_arrow_rib exprs1 exprsf rest
     | ScmPair(ScmPair(test, dit), rest) -> tag_simple_rib test dit rest 
     | _ -> raise (X_syntax_error (ribs, ("syntax error with ribs")))
     
  and tag_simple_rib test dit rest =
     match rest with
     | ScmNil -> ScmPair(ScmSymbol("if"), ScmPair((macro_expand test), ScmPair((tag_parse_else_rib(macro_expand dit)) ,ScmNil))) 
     | _ -> ScmPair(ScmSymbol("if"), ScmPair((macro_expand test), ScmPair((tag_parse_else_rib(macro_expand dit)) ,ScmPair((tag_parse_cond rest), ScmNil)))) 
     
  and tag_parse_else_rib exprs =
     match exprs with 
     | ScmPair(_ , _) -> ScmPair(ScmSymbol("begin"), exprs)
       | _ -> exprs
     
  and tag_parse_arrow_rib exprs1 exprsf rest =
     match rest with 
     | ScmNil -> ScmPair(ScmSymbol("let"), ScmPair(ScmPair(ScmPair(ScmSymbol("value"), exprs1), ScmPair(ScmPair(ScmSymbol("f"), cond_lambda exprsf), ScmPair(ScmSymbol("rest"), ScmPair(cond_lambda rest, ScmNil)))), (ScmPair(ScmSymbol("if"), ScmPair(exprs1, 
       ScmPair(ScmPair(exprsf, ScmNil), ScmPair(exprs1, ScmPair(rest, ScmNil))))))))
     | _ ->  macro_expand (parse_cond_let exprs1 exprsf rest)
     
  and parse_cond_let exprs1 exprsf rest =
     let value = ScmPair(ScmSymbol("value"), ScmPair(exprs1, ScmNil)) in
     let fbody = ScmPair(ScmSymbol("f"), ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, exprsf)), ScmNil)) in
     let ribs = tag_parse_cond rest in
     let rest = ScmPair(ScmSymbol("rest"), ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, ScmPair(ribs, ScmNil))), ScmNil)) in
     let if_expr = ScmPair(ScmPair(ScmSymbol("if"), ScmPair(ScmSymbol("value"), ScmPair(ScmPair(ScmPair(ScmSymbol("f"), ScmNil), ScmPair(ScmSymbol("value"), ScmNil)), ScmPair(ScmPair(ScmSymbol("rest"), ScmNil), ScmNil)))),ScmNil) in
     let first = ScmPair(value, ScmPair(fbody, ScmPair(rest, ScmNil))) in
     macro_expand (ScmPair(ScmSymbol("let"), ScmPair(first, if_expr)))
     
     and cond_lambda body = 
     ScmPair(ScmSymbol("lambda"), ScmPair(ScmNil, ScmPair(body, ScmNil)))
    

  and extract_letrec_args ribs =
    match ribs with
  | ScmPair(ScmPair(ribs, ScmPair(whatever, ScmNil)),ScmNil) -> 
    ScmPair(ScmPair(ribs, ScmPair(ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol "whatever", ScmNil)), ScmNil)), ScmNil)
  | ScmPair(ScmPair(ribs, ScmPair(whatever, ScmNil)),tail) ->
    ScmPair(ScmPair(ribs, ScmPair(ScmPair(ScmSymbol "quote", ScmPair(ScmSymbol "whatever", ScmNil)), ScmNil)), (extract_letrec_args tail))
  | _ -> raise (X_syntax_error(ribs,"syntax error in letrec args"))

  and extract_letrec_vals ribs body =
    match ribs with
  | ScmPair(ScmPair(arg, ScmPair(value, ScmNil)),ScmNil) -> 
    ScmPair(ScmPair(ScmSymbol "set!", ScmPair(arg, ScmPair(value, ScmNil))), body)
  | ScmPair(ScmPair(arg, ScmPair(value, ScmNil)),rest) -> 
    ScmPair(ScmPair(ScmSymbol "set!", ScmPair(arg, ScmPair(value, ScmNil))), (extract_letrec_vals rest body))
  | _ -> raise (X_syntax_error(ribs,"syntax error in letrec vals"))

  and parse_qq_tag body = 
    match body with
  | ScmNil -> (ScmPair(ScmSymbol("quote"), ScmPair(body, ScmNil))) 
  | ScmSymbol(var) -> (ScmPair(ScmSymbol("quote"), ScmPair(body, ScmNil)))
  | ScmPair(ScmSymbol("unquote"), ScmPair(var, ScmNil)) -> var
  | ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexpr,ScmNil)) -> ScmPair(ScmSymbol("quote"),ScmPair(body,ScmNil))
  | ScmVector(var) -> let arg = (parse_qq_tag (list_to_proper_list var)) in
                               ScmPair(ScmSymbol("list->vector"), ScmPair(arg,ScmNil)) 
  | ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexp, ScmNil)), whatever) -> ScmPair(ScmSymbol "append", ScmPair(sexp, ScmPair((parse_qq_tag whatever), ScmNil)))
  | ScmPair(whatever , ScmPair(ScmSymbol("unquote-splicing"), ScmPair(sexp, ScmNil))) -> ScmPair(ScmSymbol("cons"),ScmPair((parse_qq_tag whatever),ScmPair(sexp,ScmNil)))
  | ScmPair(first, second) ->ScmPair(ScmSymbol "cons", ScmPair((parse_qq_tag first), ScmPair((parse_qq_tag second), ScmNil)))
  | _ -> (body)

  and macro_expand_let ribs sexpr = 
    let ribs = scm_list_to_list ribs in
    let args = ( List.map ( fun x -> ( match x with 
                                                  | ScmPair( v , _ ) -> v 
                                                  | _ -> raise X_proper_list_error)) ribs) in 
    let params =  (List.map (fun x -> ( match x with 
                                              | ScmPair( _ , ScmPair( v , ScmNil )) -> v 
                                              | _ -> raise X_proper_list_error)) ribs) in 
    ScmPair ( ScmPair (ScmSymbol "lambda" , ScmPair(list_to_proper_list args , sexpr )), list_to_proper_list params)

  and macro_expand_let_star ribs sexpr = 
   match ribs with 
   | ScmNil -> ScmPair(ScmSymbol "let", ScmPair(ribs, sexpr))
   | ScmPair( x , ScmNil) -> ScmPair( ScmSymbol "let" , ScmPair ( ribs , sexpr ))
   | ScmPair ( first , rest ) -> let changed_sexpr = ScmPair( ScmSymbol "let*" , ScmPair( rest, sexpr )) in 
                                 ScmPair(ScmSymbol "let" , ScmPair( ScmPair( first, ScmNil ), ScmPair( changed_sexpr, ScmNil ))) 
   | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized - let*"))

  and macro_expand_let_rec ribs sexpr = 
    let ribs = scm_list_to_list ribs in
    let changed_sexpr = List.fold_right ( fun x y -> ScmPair( ScmPair (ScmSymbol ("set!"), x), y)) ribs sexpr in
    let changed_ribs = list_to_proper_list ( List.map (fun x -> (match x with 
                                                              | ScmPair( ScmSymbol v, _ ) -> ScmPair (ScmSymbol v , ScmPair (ScmPair ( ScmSymbol "quote" , ScmPair( ScmSymbol ("whatever"), ScmNil)),ScmNil))
                                                              | _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized - letrec "))))ribs) in 
    ScmPair(ScmSymbol "let", ScmPair(changed_ribs, changed_sexpr))
  
  and macro_expand sexpr =
      match sexpr with
  | ScmPair(ScmSymbol("cond"), ribs) -> (macro_expand(tag_parse_cond ribs))
  | ScmPair(ScmSymbol("and"), sexprs1) -> (macro_expand(tag_parse_and sexprs1))
  | ScmPair(ScmSymbol("let"), ScmPair(ribs, sexpr)) -> macro_expand_let ribs sexpr
  | ScmPair(ScmSymbol("let*"), ScmPair(ribs, sexpr)) -> macro_expand(macro_expand_let_star ribs sexpr)
  | ScmPair(ScmSymbol("letrec"), ScmPair(ribs, sexpr)) -> macro_expand(macro_expand_let_rec ribs sexpr)
  |ScmPair(ScmSymbol("quasiquote"), ScmPair(body, ScmNil)) -> (macro_expand (parse_qq_tag body))
  | _ -> sexpr
end;; 

