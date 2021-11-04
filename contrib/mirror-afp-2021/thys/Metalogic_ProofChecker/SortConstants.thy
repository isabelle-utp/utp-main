
text\<open>Constants for encoding class/sort constraints in term language\<close>

(* Mostly from ML code again *)

theory SortConstants
  imports Sorts
begin

(* pattern matching on strings not posigible *)
fun dest_type :: "term \<Rightarrow> typ option" where
  "dest_type (Ct nc (Ty nt [ty])) = 
    (if nc = STR ''Pure.type'' \<and> nt = STR ''Pure.type'' then Some ty else None)"
| "dest_type t = None"

definition "type_map f t = map_option (\<lambda>ty. mk_type (f ty)) (dest_type t)"

(** type classes **)

(* i have implementations for those somewhere, find them, currently not used *)
consts unsuffix :: "name \<Rightarrow> name \<Rightarrow> name option"

abbreviation "class_of_const c \<equiv> (unsuffix classN c)"

(* class/sort membership *)

fun dest_of_class :: "term \<Rightarrow> (typ * class) option" where 
  "dest_of_class (Ct c_class _ $ ty) = lift2_option Pair (dest_type ty) (class_of_const c_class)"
| "dest_of_class _ = None"

definition "mk_of_sort ty S == map (\<lambda>c . mk_of_class ty c) S"


end