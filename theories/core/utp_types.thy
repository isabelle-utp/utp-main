(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_types.thy                                                        *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Value Types *}

theory utp_types
imports "../utp_common" utp_sorts
begin

class UTP_TYPE

subsection {* Integer Type *}

class INT_TYPE = UTP_TYPE +
  fixes IntType :: "'a"

subsection {* Boolean Type *}

class BOOL_TYPE = UTP_TYPE +
  fixes BoolType :: "'a"

subsection {* Character Type *}

class CHAR_TYPE = UTP_TYPE +
  fixes CharType :: "'a"

subsection {* String Type *}

class STRING_TYPE = UTP_TYPE +
  fixes StrType :: "'a"

subsection {* Real Type *}

class REAL_TYPE = UTP_TYPE +
  fixes RealType :: "'a"

subsection {* Pair Type *}

class PAIR_TYPE = UTP_TYPE +
  fixes PairType :: "('a \<times> 'a) \<Rightarrow> 'a"

subsection {* Set Type *}

class SET_TYPE = UTP_TYPE +
  fixes SetType :: "'a \<Rightarrow> 'a"

subsection {* List Type *}

class LIST_TYPE = UTP_TYPE +
  fixes ListType :: "'a \<Rightarrow> 'a"
end