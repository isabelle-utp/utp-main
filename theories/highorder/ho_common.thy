(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ho_common.thy                                                        *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 26 August 2014 *)

header {* Higher-Order Common *}

theory ho_common
imports
  "../utp_common"
  "../utils/cardinals"
  "../utils/type_injection"
(* "../utils/fset" *)
  "../utils/maxset"
begin

default_sort type

text {* We are going to use the colon for type membership in UTP models. *}

no_notation
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50)

text {* Undeclare notation from theory @{theory McCarthy_Logic}. *}

no_notation Some ("\<lfloor>_\<rfloor>")

subsection {* Syntax and Printing *}

translations
  (type) "'a \<rightharpoonup> 'b" \<leftharpoondown> (type) "'a \<Rightarrow> 'b option"

subsection {* Sum Types *}

notation Sum_Type.Projl ("Projl")
notation Sum_Type.Projr ("Projr")

primrec IsInl :: "'a + 'b \<Rightarrow> bool" where
"IsInl (Inl x) = True" |
"IsInl (Inr x) = False"

primrec IsInr :: "'a + 'b \<Rightarrow> bool" where
"IsInr (Inl x) = False" |
"IsInr (Inr x) = True"

theorem not_IsInl [simp] :
"\<not> IsInl x \<longleftrightarrow> IsInr x"
apply (case_tac x)
apply (simp_all)
done

theorem not_IsInr [simp] :
"\<not> IsInr x \<longleftrightarrow> IsInl x"
apply (case_tac x)
apply (simp_all)
done

theorem IsInl_range [simp] :
"IsInl x \<Longrightarrow> x \<in> range Inl"
apply (case_tac x)
apply (simp_all)
done

theorem IsInr_range [simp] :
"IsInr x \<Longrightarrow> x \<in> range Inr"
apply (case_tac x)
apply (simp_all)
done

subsection {* Partial Functions *}

subsubsection {* Mapping over Ranges *}

definition map_ran ::
  "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'c)" where
"map_ran f g = (Option.map f) \<circ> g"

theorem dom_map_ran [simp] :
"dom (map_ran f g) = dom g"
apply (unfold map_ran_def)
apply (safe)
apply (metis comp_apply option_map_eq_Some)
apply (metis comp_apply option_map_eq_Some)
done

theorem ran_map_ran [simp] :
"ran (map_ran f g) = f ` (ran g)"
apply (unfold map_ran_def ran_def)
apply (simp add: set_eq_iff image_iff)
apply (safe)
apply (metis)
apply (metis)
done

theorem inj_on_map_ran :
"inj_on f S \<Longrightarrow>
 inj_on (map_ran f) {g . ran g \<subseteq> S}"
apply (rule inj_onI)
apply (unfold map_ran_def)
apply (drule CollectD)+
apply (simp only: fun_eq_iff)
apply (clarsimp)
apply (rename_tac g h x)
apply (drule_tac x = "x" in spec)
apply (case_tac "g x", case_tac[!] "h x")
apply (simp_all) [4]
apply (rename_tac g h x a b)
apply (erule inj_onD)
apply (assumption)
apply (metis in_mono ranI)+
done

theorem inj_on_map_ranI :
"inj_on f S \<Longrightarrow> (\<And> g . g \<in> T \<Longrightarrow> ran g \<subseteq> S) \<Longrightarrow>
 inj_on (map_ran f) T"
apply (drule inj_on_map_ran)
apply (subgoal_tac "T \<subseteq>  {g. ran g \<subseteq> S}")
apply (erule subset_inj_on)
apply (assumption)
apply (clarsimp)
apply (drule_tac x = "x" in meta_spec)
apply (auto)
done

theorem map_ran_inject :
"inj_on f (ran A \<union> ran B) \<Longrightarrow>
 (map_ran f A) = (map_ran f B) = (A = B)"
apply (unfold map_ran_def)
apply (unfold comp_def)
apply (simp add: fun_eq_iff)
apply (safe)
-- {* Subgoal 1 *}
apply (drule_tac x = "x" in spec)
apply (case_tac "A x")
apply (simp_all) [2]
apply (case_tac "B x")
apply (simp_all) [2]
apply (case_tac "B x")
apply (simp_all) [2]
apply (metis UnI1 UnI2 inj_onD ranI)
-- {* Subgoal 2 *}
apply (simp)
done

subsubsection {* General Theorems *}

theorem ranE :
"\<lbrakk>y \<in> ran f; \<And> x . \<lbrakk>x \<in> dom f; f x = Some y\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (unfold ran_def)
apply (unfold dom_def)
apply (clarsimp)
done

theorem ran_comp_subset :
"ran (f \<circ> g) \<subseteq> ran f"
apply (unfold ran_def)
apply (simp add: set_eq_iff)
apply (safe)
apply (metis)
done

theorem ran_comp_subsetI :
"ran f \<subseteq> S \<Longrightarrow> ran (f \<circ> g) \<subseteq> S"
apply (metis ran_comp_subset subset_trans)
done

subsection {* Injectivity Theorems *}

theorem inj_on_prod_fun :
"inj_on f (fst ` S) \<Longrightarrow>
 inj_on g (snd ` S) \<Longrightarrow>
 inj_on (\<lambda> (a, b) . (f a, g b)) S"
apply (rule inj_onI)
apply (case_tac x)
apply (case_tac y)
apply (clarsimp)
apply (rename_tac a b x y)
apply (rule conjI)
-- {* Subgoal 1 *}
apply (erule inj_onD)
apply (assumption)
apply (metis fst_conv rev_image_eqI)
apply (metis fst_conv rev_image_eqI)
-- {* Subgoal 2 *}
apply (erule inj_onD)
apply (assumption)
apply (metis snd_conv rev_image_eqI)
apply (metis snd_conv rev_image_eqI)
done

theorem inj_on_if :
"inj_on f {x \<in> S . P x} \<Longrightarrow>
 inj_on g {x \<in> S . \<not> P x} \<Longrightarrow>
 f ` {x \<in> S . P x} \<inter> g ` {x \<in> S . \<not> P x} = {} \<Longrightarrow>
 inj_on (\<lambda> x . if P x then f x else g x) S"
apply (rule inj_onI)
apply (case_tac "P x", case_tac[!] "P y")
apply (simp_all)
apply (metis (lifting) mem_Collect_eq the_inv_into_f_f)
apply (auto) [1]
apply (auto) [1]
apply (metis (lifting) mem_Collect_eq the_inv_into_f_f)
done

theorem inj_on_image :
"inj_on f (\<Union> S) \<Longrightarrow> inj_on ((op `) f) S"
apply (drule inj_on_image_Pow)
apply (erule subset_inj_on)
apply (rule subset_Pow_Union)
done

theorem inj_on_Inl :
"inj_on f S \<Longrightarrow> inj_on (Inl \<circ> f) S"
apply (erule comp_inj_on)
apply (rule inj_Inl)
done

theorem inj_on_Inr :
"inj_on f S \<Longrightarrow> inj_on (Inr \<circ> f) S"
apply (erule comp_inj_on)
apply (rule inj_Inr)
done

theorem inj_on_Projl :
"S \<subseteq> range Inl \<Longrightarrow> inj_on Projl S"
apply (rule inj_onI)
apply (atomize (full))
apply (rule allI)+
apply (rule impI)
apply (induct_tac x, induct_tac[!] y)
apply (auto)
done

theorem inj_on_Projr :
"S \<subseteq> range Inr \<Longrightarrow> inj_on Projr S"
apply (rule inj_onI)
apply (atomize (full))
apply (rule allI)+
apply (rule impI)
apply (induct_tac x, induct_tac[!] y)
apply (auto)
done

subsection {* Type Definitions and Injections *}

theorem leq_card_type_injection :
"(A :: 'a set) \<preceq>\<^sub>c (B :: 'b set) \<Longrightarrow>
 \<exists> (Abs :: 'a \<Rightarrow> 'b) (Rep :: 'b \<Rightarrow> 'a) . type_injection Abs Rep A (Abs ` A)"
apply (unfold leq_card_def)
apply (clarsimp)
apply (rule_tac x = "f" in exI)
apply (erule inj_on_Abs_imp_type_injection)
done

theorem equal_card_type_injection :
"(A :: 'a set) \<equiv>\<^sub>c (B :: 'b set) \<Longrightarrow>
 \<exists> (Abs :: 'a \<Rightarrow> 'b) (Rep :: 'b \<Rightarrow> 'a) . type_injection Abs Rep A B"
apply (simp add: equal_card_bij_betw)
apply (clarsimp)
apply (rule_tac x = "f" in exI)
apply (erule bij_betw_Abs_imp_type_injection)
done

theorem equal_card_type_definition :
"(A :: 'a set) \<equiv>\<^sub>c UNIV_T('b) \<Longrightarrow>
 \<exists> (Abs :: 'a \<Rightarrow> 'b) (Rep :: 'b \<Rightarrow> 'a) . type_definition Rep Abs A"
apply (fold type_injection_iff_type_definition)
apply (simp add: UNIV_TYPE_def)
apply (erule equal_card_type_injection)
done
end
