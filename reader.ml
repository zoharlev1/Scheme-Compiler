(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

 #use "pc.ml";;
 open PC

 let rec gcd a b =
   match (a, b) with
   | (0, b) -> b
   | (a, 0) -> a
   | (a, b) -> gcd b (a mod b);;

 type scm_number =
   | ScmRational of (int * int)
   | ScmReal of float;;
   
 type sexpr =
   | ScmVoid
   | ScmNil
   | ScmBoolean of bool
   | ScmChar of char
   | ScmString of string
   | ScmSymbol of string
   | ScmNumber of scm_number
   | ScmVector of (sexpr list)
   | ScmPair of (sexpr * sexpr);;
   (*Lior solution*)
   let rec list_to_proper_list = function
   | [] -> ScmNil
   | hd::tl -> ScmPair (hd, list_to_proper_list tl);;
   
 module type READER = sig
     val nt_sexpr : sexpr PC.parser
 end;; (* end of READER signature *)
 
 module Reader : READER = struct
 open PC;;
 
 let unitify nt = pack nt (fun _ -> ());;
 
 let rec nt_whitespace str =
   const (fun ch -> ch <= ' ') str

 and nt_end_of_line_or_file str =
   let nt1 = unitify (char '\n') in
   let nt2 = unitify nt_end_of_input in
   let nt1 = disj nt1 nt2 in
   nt1 str
    (*Mayer solution*)
   and nt_line_comment str = 
   let nt_end = disj (unitify (char '\n')) (unitify nt_end_of_input) in
   let nt1 = char ';' in 
   let nt2 = diff nt_any nt_end in
   let nt2 = star nt2 in
   let nt1 = caten nt1 (caten nt2 nt_end) in
   let nt1 = unitify nt1 in
  nt1 str

  (* Mayer solution in shaaot kabala + unitify*)
  and nt_paired_comment str =
  let nt1 = char '{' in
  let nt2 = disj_list [unitify nt_char; unitify nt_string; nt_comment] in
  let nt3 = disj nt2 (unitify (one_of "{}")) in
  let nt3 = diff nt_any nt3 in
  let nt3 = disj (unitify nt3) nt2 in
  let nt2 = star nt3 in
  let nt3 = char '}' in
  let nt1 = unitify (caten nt1 (caten nt2 nt3)) in
  nt1 str

and nt_sexpr_comment str = 
  let nt1 = unitify(caten (word "#;") nt_sexpr) in
  nt1 str

  and nt_comment str =
  disj_list
     [nt_paired_comment;
      nt_sexpr_comment;
      nt_line_comment] str
      
 and nt_skip_star str =
   let nt1 = disj (unitify nt_whitespace) nt_comment in
   let nt1 = unitify (star nt1) in
   nt1 str

 and make_skipped_star (nt : 'a parser) =
   let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
   let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
   nt1

   and nt_natural str= (*took from ps 3*) (*digits from 0 to 9 natural numbers*) 
   let nt1 =  pack (plus (range '0' '9')) (fun (ds) -> (list_to_string ds)) in
   nt1 str
   (*mustttttt return all the list, not just one number *)

   and nt_int str = 
     let nt_sign = disj (pack (char '-') (fun _ -> "-")) (pack (char '+') (fun _ -> "")) in
     let nt_sign = pack  (maybe nt_sign)
      (fun sign-> match sign with
      | None -> ""
      | Some (a) -> a) in
      let nt_n = pack (caten nt_sign nt_natural) (fun (a,b) -> int_of_string(a^b)) in
      nt_n str
      (*------------------------------------------------------------------------------------------*)
(*should do div to zero !!!! do not forget*)
 and nt_frac str =  
   let frac = caten (caten nt_int (char '/')) (only_if nt_int (fun c-> if c!=0 then true else false ))  in
   let frac = pack frac (fun ((a,b),c) -> ScmRational( (a/(gcd a c), c/(gcd a c))))in
   frac str

   (*not to implement, accendntly implements in floatA,B,C, but works good*)
(* and nt_integer_part str = raise X_not_yet_implemented
 and nt_mantissa str = raise X_not_yet_implemented*)

 and nt_exponent str = 
    let nt_exponent_tokens = disj_list [word "e"; word "E"; word "*10^"; word "*10**"] in
    let nt_exponent_tokens = pack nt_exponent_tokens (fun _ -> "e") in 
    let nt_sign = disj (pack (char '-') (fun _ -> "-")) (pack (char '+') (fun _ -> "")) in
    let nt_sign = pack  (maybe nt_sign)
     (fun sign-> match sign with
     | None -> ""
     | Some (a) -> a) in
    let nt2 = pack (plus (range '0' '9')) (fun (ds) -> (list_to_string ds)) in
    let nt2 = caten nt_sign nt2 in 
    let nt2 = pack nt2 (fun (a,b)->a^b) in
    let nt4 = caten nt_exponent_tokens  nt2 in
    let nt4 = pack nt4 (fun (a,b)-> a^b) in
    nt4 str

    and nt_floatA str = 
      let nt3 = pack (plus (range '0' '9')) (fun (ds) -> (list_to_string ds)) in
      let nekuda = word_ci "." in 
      let nekuda = pack nekuda (fun a -> list_to_string a) in
      let nt1 = caten nt3 nekuda in 
      let nt1 = pack nt1 (fun (a,b)-> a^b) in
      let maybemantisaa =  pack (maybe nt3)
       (fun x-> match x with
       | None -> "0"
       | Some (a) -> a) in
       let nt1 = caten nt1 maybemantisaa in
       let nt1 = pack nt1 (fun (a,b)->a^b) in
      let maybeexp =  pack (maybe nt_exponent)
       (fun sign-> match sign with
       | None -> "e0"
       | Some (a) -> a) in
       let nt1 = caten nt1 maybeexp in 
       let nt1 = pack nt1 (fun (a,b)->a^b) in 
        nt1 str
      (*-----------------------------------------------------------------------------------------*)
      and nt_floatB str =
        let signn = word_ci "." in
        let signn = pack signn (fun a -> list_to_string a) in
        let nt1= pack (plus (range '0' '9')) (fun (ds) -> (list_to_string ds)) in
        let nt1 = caten signn nt1 in
        let nt2 = pack nt1 (fun (a,b) -> a^b) in
        let nt3 =  pack (maybe nt_exponent)
       (fun x-> match x with
       | None -> "e0"
       | Some (a) -> a) in
        let nt2 = caten nt2 nt3 in
        let nt2 = pack nt2 (fun (a,b)-> a^b) in
        nt2 str
    (*------------------------------------------------------------------------------------------------*)
   and nt_floatC str = 
      let nt1 = pack (plus (range '0' '9')) (fun (ds) -> (list_to_string ds)) in
      let nt2 = caten nt1 nt_exponent in
      let nt1 = pack nt2 (fun (a,b)->a^b) in
      nt1 str
  (*-------------------------------------------------------------------*)
    and nt_float str =
      let nt_sign = disj (pack (char '-') (fun _ -> "-")) (pack (char '+') (fun _ -> "")) in
      let nt_sign = pack  (maybe nt_sign)
       (fun sign-> match sign with
       | None -> ""
       | Some (a) -> a) in
    let nt_finalFloat = caten (nt_sign) (disj_list[nt_floatA; nt_floatB;nt_floatC]) in
    let nt_finalFloat = pack nt_finalFloat (fun (a,b)->a^b) in
    let nt_finalFloat = pack nt_finalFloat (fun a -> ScmReal( float_of_string a)) in
    nt_finalFloat str
    (*---------------------------------*)
   and nt_number str =
   let nt1 = nt_float in
   let nt2 = nt_frac in
   let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
   let nt1 = disj nt1 (disj nt2 nt3) in
   let nt1 = pack nt1 (fun r -> ScmNumber r) in
   let nt1 = not_followed_by nt1 nt_symbol_char in
   nt1 str
  (* Mayer solution *)
   and nt_boolean str = 
   let nt1 = word_ci "#f" in
   let nt1 = pack nt1 (fun _ -> false) in
   let nt2 = word_ci "#t" in
   let nt2 = pack nt2 ( fun _ -> true) in
   let nt1 = disj nt1 nt2 in
   let nt1 = pack nt1 ( fun b -> ScmBoolean b ) in
   nt1 str

 and nt_char_simple str = 
 let nt1 = pack (range '!' '~') (fun c ->  c) in 
 let nt1 = not_followed_by nt1 nt_symbol_char in
 nt1 str

 and make_named_char char_name ch  = 
 let nt1 = word_ci char_name in 
  let nt1 = pack nt1 (fun _ -> ch) in 
   nt1 

 and nt_char_named str =
   let nt1 =
     disj_list [(make_named_char "newline" '\n');
                (make_named_char "page" '\012');
                (make_named_char "return" '\r');
                (make_named_char "space" ' ');
                (make_named_char "tab" '\t')] in
   nt1 str
   
   and nt_char_hex str = 
   let _digits = disj (range '0' '9')(range_ci 'a' 'f') in
   _digits str

 and nt_charHex str = 
   let nt1 = char 'x' in
   let nt1 = caten nt1 (plus nt_char_hex) in
  let nt1 = pack nt1 (fun (a,b)-> char_of_int(int_of_string("0x"^ list_to_string (b)))) in
   nt1 str 

   and nt_char str = 
     let nt1 = word_ci "#\\" in
     let nt2 = disj_list [nt_charHex;nt_char_named ;nt_char_simple] in
     let nt1 = caten nt1 nt2 in
     let nt1 = pack nt1 (fun (a,b)-> ScmChar b) in
     nt1 str

 and nt_symbol_char str = 
    let nt1 = disj_list [char '!'; char '$'; char '^'; char '*';char '-';char '_';char '=';char '+';char '<';char '>';char '?';char '/';char ':'] in 
    let nt_digit = range '0' '9' in
    let nt_smallletter = range 'a' 'z' in
    let nt_bigletter = range 'A' 'Z' in
    let nt1 = disj_list [ nt1 ; nt_digit ; nt_smallletter ; nt_bigletter] in
    nt1 str

 and nt_symbol str =
   let nt1 = plus nt_symbol_char in
   let nt1 = pack nt1 list_to_string in
   let nt1 = pack nt1 (fun name -> ScmSymbol name) in
   let nt1 = diff nt1 nt_number in
   nt1 str
   
   and nt_StringInterpolated str =
    let nt1 = word "~{" in
    let nt1 = caten nt1 nt_sexpr in
    let nt1 = caten nt1 (word "}") in
    let nt1 = pack nt1 (fun ((a,b), c) -> ScmPair(ScmSymbol("format"), ScmPair(ScmString("~a"), ScmPair(b, ScmNil)))) in
    nt1 str
 
   and nt_StringHexChar str = 
    let nt1 = word_ci "\\x" in 
    let nt2 = plus (nt_char_hex) in
    let nt2 = caten nt1 nt2 in 
    let nt2 = pack nt2 (fun (a,b) -> (int_of_string("0x"^ list_to_string(b)^";"))) in 
    let nt2 = pack nt2 (fun x -> char_of_int x) in 
    nt2 str
    
    and nt_StringMetaChar str =
    let nt1 = 
      disj_list[(make_named_char "\\n" '\n');
                (make_named_char "\\f" '\012');
                (make_named_char "\\r" '\r');
                (make_named_char "\\\"" '\"');
                (make_named_char "\\t" '\t');
                (make_named_char "~~" '~')] in
    nt1 str
    
    and nt_StringLiteralChar str = 
    let nt1 = disj_list [char '\\'; char '"'; char '~'] in
    let nt1 = diff nt_any nt1 in
    nt1 str

    
    and nt_stringchar str = 
    let nt1 = disj_list [nt_StringLiteralChar;nt_StringMetaChar; nt_StringHexChar] in 
    let nt1 = plus nt1 in 
    nt1 str
    
    
  (*Lior solution*)
  and nt_string str =
 let nt_Rperfix = word "\"" in
 let nt_Lperfix = word "\"" in
 let nt1 = pack nt_stringchar (fun a -> ScmString(list_to_string a)) in
  let nt3 = star (disj nt1 nt_StringInterpolated ) in
  let nt2 = caten nt_Rperfix nt3 in 
  let nt2 = caten nt2 nt_Lperfix in
  let nt1 = pack nt2 (fun ((a,str_elements),c) -> match str_elements with
    | [] -> ScmString ""
    | hd::[] -> hd
    |_ -> ScmPair(ScmSymbol("string-append") ,list_to_proper_list (str_elements))) in
    nt1 str

  and nt_vector str =
   let nt1 = word "#(" in
   let nt2 = caten nt_skip_star (char ')') in
   let nt2 = pack nt2 (fun _ -> ScmVector []) in
   let nt3 = plus nt_sexpr in
   let nt4 = char ')' in
   let nt3 = caten nt3 nt4 in
   let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
   let nt2 = disj nt2 nt3 in
   let nt1 = caten nt1 nt2 in
   let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
   nt1 str

   and nt_Proper_list str =
   let nt1 = char '(' in
   let nt1 = caten nt1 nt_skip_star in
   let nt2 = caten (star nt_sexpr) nt_skip_star in
   let nt3 = char ')' in
   let nt3 = caten nt2 nt3 in (* nt2 is caten too *)
   let nt3 = caten nt1 nt3 in 
   let nt3 = pack nt3 (fun ((a,b),((c,d),e))-> c) in
   let nt3 = pack nt3 (fun c -> List.fold_right (fun a b -> ScmPair(a,b)) c ScmNil) in
   nt3 str

   and nt_Improper_list str =
   let nt1 = caten (char '(') nt_skip_star in
   let nt2 = caten (plus nt_sexpr) nt_skip_star in
   let nt3 = caten (char '.') nt_skip_star in
   let nt4 = caten nt_sexpr (char ')') in
   let nt5 = caten nt1 nt2 in
   let nt6 = caten nt3 nt4 in
   let nt7 = caten nt5 nt6 in
   let nt7 = pack nt7 (fun ( ((a,b),(c,d)),((e,f),(g,h)) ) -> List.fold_right (fun x y -> ScmPair(x,y)) c g ) in
   nt7 str

   and nt_list str = 
   let nt1 = disj nt_Proper_list nt_Improper_list in
      nt1 str 
      
 and nt_Quoted str =
  let nt1 = word_ci "'" in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = pack nt1 (fun (a,b) -> ScmPair((ScmSymbol("quote"),ScmPair(b,ScmNil)))) in
  nt1 str

and nt_QuasiQuoted str = 
  let nt1 = word_ci "`" in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = pack nt1 (fun (a,b) -> ScmPair((ScmSymbol("quasiquote"),ScmPair(b,ScmNil)))) in
  nt1 str

and nt_Unquoted str = 
  let nt1 = word_ci "," in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = pack nt1 (fun (a,b) -> ScmPair((ScmSymbol("unquote"),ScmPair(b,ScmNil)))) in
  nt1 str

and nt_UnquoteAndSpliced str = 
  let nt1 = word_ci ",@" in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = pack nt1 (fun (a,b) -> ScmPair((ScmSymbol("unquote-splicing"),ScmPair(b,ScmNil)))) in
  nt1 str

and nt_quoted_forms str =
let nt1 = disj_list[nt_Quoted;nt_QuasiQuoted;nt_Unquoted;nt_UnquoteAndSpliced] in 
  nt1 str

 and nt_sexpr str =
   let nt1 =
     disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
                nt_string; nt_vector; nt_list;nt_quoted_forms] in
   let nt1 = make_skipped_star nt1 in
   nt1 str;;
 
 end;; (* end of struct Reader *)
 
 let rec string_of_sexpr = function
   | ScmVoid -> "#<void>"
   | ScmNil -> "()"
   | ScmBoolean(false) -> "#f"
   | ScmBoolean(true) -> "#t"
   | ScmChar('\n') -> "#\\newline"
   | ScmChar('\r') -> "#\\return"
   | ScmChar('\012') -> "#\\page"
   | ScmChar('\t') -> "#\\tab"
   | ScmChar(' ') -> "#\\space"
   | ScmChar(ch) ->
      if (ch < ' ')
      then let n = int_of_char ch in
           Printf.sprintf "#\\x%x" n
      else Printf.sprintf "#\\%c" ch
   | ScmString(str) ->
      Printf.sprintf "\"%s\""
        (String.concat ""
           (List.map
              (function
               | '\n' -> "\\n"
               | '\012' -> "\\f"
               | '\r' -> "\\r"
               | '\t' -> "\\t"
               | ch ->
                  if (ch < ' ')
                  then Printf.sprintf "\\x%x;" (int_of_char ch)
                  else Printf.sprintf "%c" ch)
              (string_to_list str)))
   | ScmSymbol(sym) -> sym
   | ScmNumber(ScmRational(0, _)) -> "0"
   | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
   | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
   | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
   | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
   | ScmVector(sexprs) ->
      let strings = List.map string_of_sexpr sexprs in
      let inner_string = String.concat " " strings in
      Printf.sprintf "#(%s)" inner_string
   | ScmPair(ScmSymbol "quote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "'%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "quasiquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf "`%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",%s" (string_of_sexpr sexpr)
   | ScmPair(ScmSymbol "unquote-splicing",
             ScmPair(sexpr, ScmNil)) ->
      Printf.sprintf ",@%s" (string_of_sexpr sexpr)
   | ScmPair(car, cdr) ->
      string_of_sexpr' (string_of_sexpr car) cdr
 and string_of_sexpr' car_string = function
   | ScmNil -> Printf.sprintf "(%s)" car_string
   | ScmPair(cadr, cddr) ->
      let new_car_string =
        Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
      string_of_sexpr' new_car_string cddr
   | cdr ->
      let cdr_string = (string_of_sexpr cdr) in
      Printf.sprintf "(%s . %s)" car_string cdr_string;;