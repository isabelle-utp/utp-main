(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: typedef_extra.thy                                                    *)
(* Authors: Simon Foster & Frank Zeyda, University of York (UK)               *)
(******************************************************************************)
(* LAST REVIEWED: 3 September 2014 *)

header {* Typedef Extra *}

theory typedef_extra
imports Main Countable_Set
begin

text {* This theory provides a few  extra theorems and lemmas for typedefs. *}

subsection {* Locale Theorems *}

text {*
  Unfortunately, the theorems below are not automatically inherited into the
  namespace of a new type definition. Perhaps mention this to the developers
  as a possible improvement to @{text "typedef.ML"}.
*}

context type_definition
begin
theorem Rep_inject_sym [intro] :
"(x = y) \<longleftrightarrow> (Rep x = Rep y)"
apply (rule sym)
apply (rule Rep_inject)
done

theorem Rep_inj [simp] :
"inj Rep"
apply (rule inj_onI)
apply (simp only: Rep_inject)
done

theorem Abs_inj_on [simp] :
"inj_on Abs A"
apply (rule inj_onI)
apply (simp only: Abs_inject)
done

theorem Rep_bij_betw [simp] :
"bij_betw Rep UNIV A"
apply (unfold bij_betw_def)
apply (simp add: Rep_range)
done

theorem Abs_bij_betw [simp] :
"bij_betw Abs A UNIV"
apply (unfold bij_betw_def)
apply (simp add: Abs_image)
done

declare Abs_image [simp]
declare Rep_range [simp]

theorem Abs_imageD :
"\<lbrakk>Abs ` X = Y; X \<subseteq> A\<rbrakk> \<Longrightarrow> Rep ` Y = X"
apply (clarsimp)
apply (simp add: image_def)
apply (safe)
apply (metis Abs_inverse set_rev_mp)
apply (metis Abs_inverse set_rev_mp)
done

text {* \fixme{Should the following be a default simplification?} *}

theorem Rep_image [simp] :
"Rep ` Y \<subseteq> A"
apply (metis Rep image_subsetI)
done
end

subsection {* Interpretation Lemmas *}

text {* The below facilitate non-axiomatic type definitions via bijections. *}

lemma type_definition_inv_into :
"bij_betw Abs A UNIV \<Longrightarrow> type_definition (inv_into A Abs) Abs A"
apply (simp add: type_definition_def)
apply (simp add: bij_betw_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule inv_into_into)
apply (simp)
-- {* Subgoal 2 *}
apply (simp add: f_inv_into_f)
done

lemma type_definition_the_inv_into :
"bij_betw Abs A UNIV \<Longrightarrow> type_definition (the_inv_into A Abs) Abs A"
apply (simp add: type_definition_def)
apply (simp add: bij_betw_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule the_inv_into_into)
apply (simp_all) [3]
-- {* Subgoal 2 *}
apply (simp add: f_the_inv_into_f)
-- {* Subgoal 3 *}
apply (simp add: the_inv_into_f_f)
done

subsection {* Countability Theorems *}

text {* The next are useful to instantiate typedefs as @{class countable}. *}

theorem type_definition_countable :
"type_definition Rep (Abs :: 'a::countable \<Rightarrow> 'b) A \<Longrightarrow>
 countable (UNIV :: 'b set)"
apply (rule_tac f = "Rep" in countableI')
apply (rule injI)
apply (simp add: type_definition.Rep_inject)
done

theorem type_definition_exists_to_nat :
"type_definition Rep (Abs :: 'a::countable \<Rightarrow> 'b) A \<Longrightarrow>
 \<exists> to_nat :: 'b \<Rightarrow> nat . inj to_nat"
apply (fold countable_def)
apply (erule type_definition_countable)
done
end
