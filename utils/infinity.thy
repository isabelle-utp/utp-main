(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: infinity.thy                                                         *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 4 September 2014 *)

header {* Infinity Supplement *}

theory infinity
imports Main Real Infinite_Set "~~/src/HOL/Cardinals/Cardinals"
begin

text {*
  This theory introduces a type class @{text infinite} for infinite types. It
  also provides useful theorems to prove infinity of the universe for various
  constructions using common HOL types.
*}

subsection {* Type class @{text infinite} *}

text {*
  This type class captures that the universe (carrier) of a type is infinite.
*}

class infinite =
  assumes infinite_UNIV [simp] : "infinite (UNIV :: 'a set)"

subsection {* Infinity Theorems *}

text {* Useful theorems to prove that a type's @{const UNIV} is infinite. *}

theorem infinite_UNIV_real [simp] :
"infinite (UNIV :: real set)"
  by (rule infinite_UNIV_char_0)

theorem infinite_UNIV_fun1 [simp] :
"infinite (UNIV :: 'a set) \<Longrightarrow>
 card (UNIV :: 'b set) \<noteq> Suc 0 \<Longrightarrow>
 infinite (UNIV :: ('a \<Rightarrow> 'b) set)"
apply (erule contrapos_nn)
apply (erule finite_fun_UNIVD1)
apply (assumption)
done

theorem infinite_UNIV_fun2 [simp] :
"infinite (UNIV :: 'b set) \<Longrightarrow>
 infinite (UNIV :: ('a \<Rightarrow> 'b) set)"
apply (erule contrapos_nn)
apply (erule finite_fun_UNIVD2)
done

theorem infinite_UNIV_set [simp] :
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: 'a set set)"
apply (erule contrapos_nn)
apply (simp add: Finite_Set.finite_set)
done

theorem infinite_UNIV_prod1 [simp] :
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: ('a \<times> 'b) set)"
apply (erule contrapos_nn)
apply (simp add: finite_prod)
done

theorem infinite_UNIV_prod2 [simp] :
"infinite (UNIV :: 'b set) \<Longrightarrow>
 infinite (UNIV :: ('a \<times> 'b) set)"
apply (erule contrapos_nn)
apply (simp add: finite_prod)
done

theorem infinite_UNIV_sum1 [simp] :
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: ('a + 'b) set)"
apply (erule contrapos_nn)
apply (simp)
done

theorem infinite_UNIV_sum2 [simp] :
"infinite (UNIV :: 'b set) \<Longrightarrow>
 infinite (UNIV :: ('a + 'b) set)"
apply (erule contrapos_nn)
apply (simp)
done

theorem infinite_UNIV_list [simp] :
"infinite (UNIV :: 'a list set)"
apply (rule infinite_UNIV_listI)
done

theorem infinite_UNIV_option [simp] :
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: 'a option set)"
apply (erule contrapos_nn)
apply (simp)
done

theorem infinite_image [intro] :
"infinite A \<Longrightarrow> inj_on f A \<Longrightarrow> infinite (f ` A)"
apply (metis finite_imageD)
done

subsection {* Instantiations *}

text {*
  The instantiations for product and union types have stronger caveats than
  principally needed. This is a necessary downside of using classes and also
  perhaps the reason why HOL does not include an infinity class by default.
*}

instance nat :: infinite by (intro_classes, simp)
instance int :: infinite by (intro_classes, metis infinite_UNIV_int)
instance real :: infinite by (intro_classes, auto)
instance "fun" :: (type, infinite) infinite by (intro_classes, simp)
instance set :: (infinite) infinite by (intro_classes, simp)
instance prod :: (infinite, infinite) infinite by (intro_classes, simp)
instance sum :: (infinite, infinite) infinite by (intro_classes, simp)
instance list :: (type) infinite by (intro_classes, simp)
instance option :: (infinite) infinite by (intro_classes, simp)
end
