(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: UNIV_TYPE.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 27 March 2014 *)

section \<open>Type Universe\<close>

theory UNIV_TYPE
imports Main
begin

definition UNIV_TYPE :: "'a itself \<Rightarrow> 'a set" where
"UNIV_TYPE (t :: 'a itself) = (UNIV :: 'a set)"

(* declare UNIV_TYPE_def [simp] *)

syntax
  "_UNIV_TYPE" :: "type => logic"  ("(1UNIV'_T/(1'(_')))")

translations
  "UNIV_T('t)" \<rightleftharpoons> "(CONST UNIV_TYPE) TYPE('t)"

theorem "0 \<in> UNIV_T(int)"
apply (simp add: UNIV_TYPE_def)
done

theorem "\<forall>x. x \<in> UNIV_T('a)"
apply (simp add: UNIV_TYPE_def)
done

theorem "UNIV_T('a) = UNIV"
apply (simp add: UNIV_TYPE_def)
done
end
