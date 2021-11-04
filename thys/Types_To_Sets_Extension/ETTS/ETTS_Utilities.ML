(* Title: ETTS/ETTS_Utilities.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

A collection of unrelated utilities for the ETTS.
*)

signature ETTS_UTILITIES =
sig
val term_name_of_type_name : string -> string
val string_of_token_src_list : Token.src list -> string
end;


structure ETTS_Utilities : ETTS_UTILITIES =
struct

fun term_name_of_type_name c =
  let val s = substring (c, 1, size c - 1)
  in
    if s |> String.explode |> map Char.isAlpha |> List.all I
    then String.map Char.toUpper s
    else "A"
  end;

fun string_of_token_src_list ts = 
  let
    val lhs_cs = map (Token.name_of_src #> fst) ts
    val rhs_cs = ts
      |> map (Token.args_of_src #> map Token.print #> String.concatWith " ") 
    val cs = 
      let
        fun condc (lhs_c, rhs_c) = 
          if rhs_c = "" then lhs_c else lhs_c ^ " " ^ rhs_c 
      in map condc (lhs_cs ~~ rhs_cs) end
  in ML_Syntax.print_list I cs end;

end;

open ETTS_Utilities;