#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
  (* val test : expr' list -> string *)
end;;

module Code_Gen : CODE_GEN = struct
  let movax = "\nmov rax"
  let fadress = "cmp rax, SOB_FALSE_ADDRESS\n"
  let vaddress =", SOB_VOID_ADDRESS\n"
  let naddress = " SOB_NIL_ADDRESS"
  let label_index = ref 0;;
  let counter = (fun () -> 
  label_index := (!label_index +1); ((string_of_int !label_index)))

  let remove_dup list =
  (List.fold_left (fun first rest -> if(List.mem rest first) then first else first@[rest]) [] list)

  let rec find_str_offset expr1 table =
      match table with
      | [] -> raise X_this_should_not_happen
      | first::rest -> begin
          let ((const),(off,asm)) = first in
            let a = (sexpr_eq const expr1) in
            match a with 
            | true -> off
            | false -> (find_str_offset expr1 rest)
            end


let free_var_proc = [
               (* Type queries  *)
    "boolean?"; "flonum?"; "rational?";
    "pair?"; "null?"; "char?"; "string?";
    "procedure?"; "symbol?";
    (* String procedures *)
    "string-length"; "string-ref"; "string-set!";
    "make-string"; "symbol->string";
    (* Type conversions *)
    "char->integer"; "integer->char"; "exact->inexact";
    (* Identity test *)
    "eq?";
    (* Arithmetic ops *)
    "+"; "*"; "/"; "="; "<";
    (* Additional rational numebr ops *)
    "numerator"; "denominator"; "gcd";
    (* List ops *)
    "car"; "cdr"; "cons"; "apply"; "set-car!"; "set-cdr!"
  ]
  let rec collect_sexprs asts = 
    match asts with 
  | ScmConst'(sexPr) -> [sexPr]
  | ScmVar'(var1) -> []
  | ScmBox'(var1) -> []
  | ScmBoxGet'(var1) -> []
  | ScmBoxSet'(var1,expr1) -> collect_sexprs expr1
  | ScmIf'(tst,thn,els) -> (collect_sexprs tst)@(collect_sexprs thn)@(collect_sexprs els)
  | ScmSeq'(list) -> collect_or_seq_app list
  | ScmSet'(var1,expr1) -> collect_sexprs expr1
  | ScmDef'(var1,expr1) -> collect_sexprs expr1
  | ScmOr'(list)-> collect_or_seq_app list
  | ScmLambdaSimple' (args,body) -> collect_sexprs body
  | ScmLambdaOpt'(args,optargs,body) -> collect_sexprs body
  | ScmApplic'(exp, list) -> collect_or_seq_app ([exp]@list)
  | ScmApplicTP'(exp, list) -> collect_or_seq_app ([exp]@list)

  and collect_or_seq_app list =
  List.flatten (List.map collect_sexprs list)


  let rec make_consts_tbl asts = 
  let table = List.flatten (List.map collect_sexprs asts) in
  let table = [ScmVoid; ScmNil; ScmBoolean(false);ScmBoolean(true)] @ table in 
  let table = remove_dup table in
  let new_table = List.flatten(List.map expanding_table table) in 
  let new_table1 = remove_dup new_table in 
  make_compile_table [] 0 new_table1


  and expanding_table expr1 =
  match expr1 with 
  | ScmSymbol(name) -> [ScmString(name); expr1]
  | ScmPair(first,rest) -> (expanding_table (first))@(expanding_table((rest)))@[(first);(rest);expr1]
  | ScmVector(list1) -> (List.fold_left (fun acc curr -> acc @(expanding_table (curr))) [] list1)@[expr1] 
  | _ -> [expr1]

  and make_compile_table finaltable pos constable = 
    match constable with 
    | [] -> finaltable
    | first::rest ->
      match first with 
        | ScmVoid -> make_compile_table (finaltable@ [(first,(pos,"db T_VOID"))]) (pos+1) rest
        | ScmNil -> make_compile_table (finaltable@ [(first,(pos,"db T_NIL"))]) (pos+1) rest
        | ScmBoolean(false) -> (make_compile_table (finaltable @ [(first,(pos,"db T_BOOL, 0"))]) (pos+2) rest) 
        | ScmBoolean(true) -> (make_compile_table (finaltable @ [(first,(pos,"db T_BOOL, 1"))]) (pos+2) rest)
        | ScmChar(c) -> (make_compile_table (finaltable @ [(first,(pos,"MAKE_LITERAL_CHAR("^(string_of_int(int_of_char c))^")"))]) (pos+2) rest)
        | ScmString(str) -> (make_compile_table (finaltable @ [(first,(pos,"MAKE_LITERAL_STRING {\""^str^"\"}"))]) (pos+9+(String.length str)) rest)
        | ScmSymbol(s) -> (make_compile_table (finaltable @ [(first,(pos,"MAKE_LITERAL_SYMBOL(const_tbl+" ^ (string_of_int (find_str_offset (ScmString(s)) finaltable))^ ")"))]) (pos+9) rest) 
        | ScmNumber(ScmReal(a)) -> (make_compile_table (finaltable @ [(first,(pos,"MAKE_LITERAL_FLOAT(" ^ (string_of_float (a)) ^ ")"))]) (pos+9) rest)
        | ScmNumber(ScmRational(a,b)) -> (make_compile_table (finaltable @ [(first,(pos,"MAKE_LITERAL_RATIONAL("^(string_of_int a) ^ "," ^ (string_of_int b)^")"))]) (pos+17) rest)
        | ScmPair(car,cdr) -> 
        (make_compile_table (finaltable @ [(first,(pos,"MAKE_LITERAL_PAIR(const_tbl+" ^ 
        (string_of_int (find_str_offset (car) finaltable)) ^ ", const_tbl+" ^ (string_of_int (find_str_offset (cdr) finaltable)) ^ ")"))]) (pos+17) rest)   
        | ScmVector(list) -> 
         let length = (List.length list) in
            match length with 
            | 0 -> (make_compile_table (finaltable @ [(first,(pos,("db T_VECTOR\ndq 0")))]) (pos+(9+8*length)) rest) 
            | _ -> (make_compile_table (finaltable @ [(first,(pos,(vector_const_tbl list finaltable)))]) (pos+(9+8*length)) rest) 

  and vector_const_tbl list finaltable =
    let firstvector = "MAKE_LITERAL_VECTOR const_tbl+"^(string_of_int (find_str_offset (List.hd list) finaltable)) in
    (List.fold_left (fun acc curr -> acc ^ ", const_tbl+" ^ (string_of_int (find_str_offset (curr) finaltable))) firstvector (List.tl list))

(*--------------------------------------------------------------------- free vars table---------------------------------------------------- *)
  let rec make_fvars_tbl asts = 
  let table = (List.flatten (List.map collect_free_vars asts)) in
  let table = (free_var_proc @ table) in 
  let table = (remove_dup table) in
  let final_table = (table_indexer table 0) in 
    final_table

  and collect_free_vars asts =
  match asts with 
  | ScmConst'(sexPr) -> []
  | ScmVar'(var1) -> (check_var var1)
  | ScmBox'(var1) -> []
  | ScmBoxGet'(var1) -> []
  | ScmBoxSet'(var1,expr1) -> []
  | ScmIf'(tst,thn,els) -> (collect_free_vars tst)@(collect_free_vars thn)@(collect_free_vars els)
  | ScmSeq'(list) -> (collect_helper list)
  | ScmOr'(list)-> (collect_helper list)
  | ScmSet'(var1,expr1) -> (check_var var1)@(collect_free_vars expr1)
  | ScmDef'(var1,expr1) ->  (check_var var1)@(collect_free_vars expr1)
  | ScmLambdaSimple' (args,body) -> (collect_free_vars body)
  | ScmLambdaOpt'(args,optargs,body) -> (collect_free_vars body)
  | ScmApplic'(exp, list) -> (collect_helper ([exp]@list))
  | ScmApplicTP'(exp, list) ->  (collect_helper ([exp]@list))

  and collect_helper list =
    List.flatten(List.map collect_free_vars list)

  and check_var var =
       match var with 
      | VarFree(v) -> [v]
      | _ -> [] 

  and table_indexer table index =
  match table with 
  | first::rest -> [(first,index)] @(table_indexer rest (index+8))
  | _ -> []


(*----------------------------------------- generate ----------------------------------------------------------- *)

  let generate consts fvars e = 
   let rec run consts fvars e index = 
    match e with
  | ScmConst'(expr1) -> (generate_const expr1 consts)
  | ScmVar'(VarParam(_, minor)) -> (generate_varparam (string_of_int (minor)))
  | ScmVar'(VarFree(v)) -> (generate_varfree v fvars)
  | ScmVar'(VarBound(_, major, minor)) -> (generate_varbound (string_of_int(major)) (string_of_int(minor)))
  | ScmSet'(VarBound(_,major, minor), ex) ->  (generate_setbound consts fvars ex index (string_of_int major) (string_of_int minor))
  | ScmSet'(VarParam(_, minor), ex) -> (generate_setparam consts fvars ex index (string_of_int minor))
  | ScmSet'(VarFree(v), ex) -> (generate_setfree consts fvars v ex index)
  | ScmSeq'(lst) -> (generate_seq consts fvars index lst)
  | ScmOr'(lst) -> let label_ex = counter () in (generate_or consts fvars index label_ex lst)
  | ScmIf'(test,dit,dif)->
      let label_els = counter() in
      let label_ext = counter() in (generate_if consts fvars test dit dif index label_els label_ext)
  | ScmBoxGet'(var1) -> (generate_boxget consts fvars ( ScmVar'(var1)) index)
  | ScmBoxSet'(var1,value1) -> (generate_boxset consts fvars value1 index (ScmVar'(var1)))
  | ScmBox'(VarParam(x, minor)) -> (generate_box (string_of_int (minor))) 
  | ScmDef'(VarFree(var1),value1) -> (generate_def consts fvars value1 index var1)

  | ScmLambdaSimple'(args,body) ->         
      let l_code = "Lcode" ^ (counter()) in
      let l_cont = "Lcont" ^ (counter()) in
        begin match index with 
        |0 -> (generate_lambdasimplezero consts fvars body index l_code l_cont)
        |_->  (generate_lambdasimple consts fvars body index l_code l_cont) end

  |ScmLambdaOpt'(args,opt,body) ->
      let l_code = "Lcode" ^ (counter()) in
      let l_cont = "Lcont" ^ (counter()) in
      let args_num = ((List.length args)+1) in
      (generate_lambdaOPt consts fvars body index l_code l_cont args_num)

  | ScmApplic'(expr,exprs) -> 
       let exprs_num = (List.length exprs) in
       let args_applic = (List.fold_right (fun curr acc -> acc ^ (run consts fvars curr index) ^ "push rax\n")  exprs "" )in
       args_applic ^ (generate_applic consts fvars expr index exprs_num)

  |ScmApplicTP'(expr,exprs) -> 
      let exprs_num =  (List.length exprs) in
      let args_applic = (List.fold_right (fun curr acc -> acc ^ (run consts fvars curr index) ^ "push rax\n")  exprs "") in
       args_applic ^ (generate_applicTP consts fvars expr exprs index exprs_num )
  |_-> ""

  and fvar_index fvars v = 
  match fvars with
  | (name, index) ::rest -> if v = name then index else fvar_index rest v
  | [] -> raise X_this_should_not_happen

  and generate_const expr1 consts =
  movax^", const_tbl+"^(string_of_int(find_str_offset expr1 consts))^"\n" 


  and generate_varfree v fvars = 
  movax^", qword [fvar_tbl +"^(string_of_int (fvar_index fvars v))^"]\n"

  and generate_varparam theminor =
  movax^", qword [rbp + 8*(4 + "^theminor^")]\n"


  and generate_varbound themajor theminor = 
  movax^", qword [rbp + 8*2]"^movax^", qword [rax + 8*" ^themajor^"]"^movax^", qword [rax + 8*"^theminor^"]\n"

  and generate_setbound consts fvars ex index themajor theminor =
  "\n"^(run consts fvars ex index)^
  "\nmov rbx, qword [rbp + 8*2]\nmov rbx, qword [rbx + 8*"^
  themajor^"]\nmov qword [rbx + 8*"^
  theminor^"], rax"^movax^vaddress

  and generate_setparam consts fvars ex index theminor =
  "\n"^(run consts fvars ex index)^
  "\nmov qword [rbp + 8*(4 +"^
  theminor^")],rax"^movax^vaddress

  and generate_box theminor =
  movax^", qword[rbp + 8 * (4 + " ^theminor ^ ")]\n" ^
  "push"^ naddress ^"\npush rax\npush 2\npush" ^ naddress ^"\ncall cons\nadd rsp,8*1\npush rcx\npop rcx\npop rbx\nshl rbx,3\nadd rsp,rbx\nmov qword[rbp + 8 * (4 + " ^ 
  theminor ^ ")],rax\n"

  and generate_setfree consts fvars v ex index =
  (run consts fvars ex index)^
  "\nmov qword [fvar_tbl+"^(string_of_int (fvar_index fvars v))^"], rax"^movax^vaddress

  and generate_or consts fvars index label_ex lst =
      (List.fold_left (fun asm ex -> asm ^ (run consts fvars ex index)^
      fadress^ "jne Lexit"^label_ex^" \n") "" lst  ) ^"Lexit"^label_ex^":\n"

  and generate_if consts fvars test dit dif index label_els label_ext =
  (run consts fvars test index) ^ 
  fadress ^"je Lelse"^label_els^"\n"^(run consts fvars dit index) ^ "jmp Lexit"^label_ext^"\n"^"Lelse"^label_els^":\n"^ (run consts fvars dif index)^"Lexit"^label_ext^":\n"

  and generate_boxget consts fvars var1 index =
  "\n"^(run consts fvars var1 index)^movax^", qword [rax]\n"

  and generate_boxset consts fvars value1 index var1 =
  "\n"^(run consts fvars value1 index) ^ 
  "\npush rax\n"^ (run consts fvars var1 index)^
  "\npop qword [rax]"^movax^vaddress

  and generate_def consts fvars value1 index var1 =
  (run consts fvars value1 index)^ 
   "mov qword [fvar_tbl+"^
   (string_of_int (fvar_index fvars var1))^
   "],rax"^movax^vaddress

  and generate_seq consts fvars index list =
  (List.fold_left(fun asm ex -> asm^(run consts fvars ex index)) "\n" list) ^ "\n"

  and generate_lambdasimplezero consts fvars body index l_code l_cont =
      "MAKE_CLOSURE(rax,"^naddress^"," ^ l_code ^ ")" ^ "\n" ^ 
      "jmp " ^ l_cont ^ "\n" ^l_code^":\n"^"push rbp\nmov rbp, rsp\n" ^(run consts fvars body (index+1))^"\nleave\nret\n"^l_cont^":\n"

  and generate_lambdasimple consts fvars body index l_code l_cont =
  let nindex = (string_of_int index) in
      "push rcx\npush rdx\npop rdx\npop rcx\n"^"ENV_EXT " ^ nindex^"\nmov rbx, rax\nMAKE_CLOSURE(rax, rbx, "^ l_code ^ ")\njmp " ^l_cont^"\n" ^
      l_code ^":\npush rbp\nmov rbp, rsp\n"^(run consts fvars body (index + 1)) ^"leave\nret\n"^l_cont ^ ":\n" 


  and generate_lambdaOPt consts fvars body index l_code l_cont args_num=
  let nindex = (string_of_int index) in
     "ENV_EXT " ^ nindex^"\nmov rbx, rax\nMAKE_CLOSURE(rax, rbx, "^ l_code ^ ")\njmp " ^l_cont ^"\n" ^l_code ^ ":\n" ^
      "FIX_LAMBDAOPT " ^ (string_of_int args_num) ^"\npush rbp\nmov rbp, rsp\n" ^(run consts fvars body (index+1)) ^"leave\nret\n"^l_cont ^ ":\n"

  and generate_applic consts fvars expr index exprs_num =
      "push " ^ (string_of_int exprs_num) ^ "\n" ^(run consts fvars expr (index+1)) ^"CLOSURE_ENV rbx, rax\npush rbx\nCLOSURE_CODE rbx, rax\ncall rbx\nadd rsp,8*1 \n" ^
      "pop rbx\nshl rbx,3\npush rcx\npop rcx\npush rcx\npop rcx\nadd rsp,rbx \n"
    
  and generate_applicTP consts fvars expr exprs index exprs_num  =
      "push " ^(string_of_int(exprs_num)) ^ "\n" ^(run consts fvars expr (index+1)) ^"CLOSURE_ENV rbx, rax\npush rbx\n"^"push qword[rbp  + 8 * 1] \n" ^
      "FIX_APPLICTP " ^ (string_of_int (3 +  (List.length exprs))) ^ "\nCLOSURE_CODE rbx, rax\npush rcx\npush rdx\npop rdx\npop rcx\njmp rbx\n"
      
  in
  run consts fvars e 0
end;;