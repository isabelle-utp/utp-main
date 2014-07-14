(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: infinity.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Infinity Theorems *}

theory infinity
imports Main Real "~~/src/HOL/Cardinals/Cardinals"
begin

subsection {* Infinity of @{const UNIV} *}

declare nat_infinite [simp del]
declare int_infinite [simp del]

theorem infinite_UNIV_nat [simp] :
"infinite (UNIV :: nat set)"
apply (rule nat_infinite)
done

theorem infinite_UNIV_int [simp] :
"infinite (UNIV :: int set)"
apply (rule int_infinite)
done

theorem infinite_UNIV_real [simp] :
"infinite (UNIV :: real set)"
apply (rule infinite_UNIV_char_0)
done

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

theorem infinite_UNIV_option [simp] :
"infinite (UNIV :: 'a set) \<Longrightarrow>
 infinite (UNIV :: 'a option set)"
apply (erule contrapos_nn)
apply (simp)
done

subsection {* Class Infinite *}

class infinite =
  assumes infinite_UNIV [simp] : "infinite (UNIV :: 'a set)"

subsection {* Instantiations *}

text {*
  The instantiations for product and union types have stronger caveats on the
  types than principally needed. This is a necessary downside of using classes
  and perhaps the reason why HOL does not include an infinity class by default.
*}

instance nat :: infinite by (intro_classes, simp)
instance int :: infinite by (intro_classes, simp)
instance "fun" :: (type, infinite) infinite by (intro_classes, simp)
instance set :: (infinite) infinite by (intro_classes, simp)
instance prod :: (infinite, infinite) infinite by (intro_classes, simp)
instance sum :: (infinite, infinite) infinite by (intro_classes, simp)
instance option :: (infinite) infinite by (intro_classes, simp)

subsection {* Theorems *}

theorem infinite_image :
"infinite A \<Longrightarrow> inj_on f A \<Longrightarrow> infinite (f ` A)"
apply (metis finite_imageD)
done
end
