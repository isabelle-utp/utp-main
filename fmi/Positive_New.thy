(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Positive_New.thy                                                     *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Sept 2017 *)

section {* Positive Subtypes *}

theory Positive_New
imports Two Continuum
  "../axiomatic/theories/utils/Infinity"
  "~~/src/HOL/Library/Countable"
begin

text {* Move this instantiation to a more suitable place in the hierarchy. *}

subclass (in infinite) two
apply (intro_classes)
apply (rule disjI1)
apply (rule local.infinite_UNIV)
done

subsection {* Type Definition *}

typedef (overloaded) 'a::"{zero, linorder}" pos = "{x::'a. x \<ge> 0}"
apply (rule_tac x = "0" in exI)
apply (clarsimp)
done

setup_lifting type_definition_pos

subsection {* Instantiations *}

instantiation pos :: ("{zero, linorder}") zero
begin
lift_definition zero_pos :: "'a pos"
is "0 :: 'a" ..
instance ..
end

instantiation pos :: ("{zero, linorder}") linorder
begin
lift_definition less_eq_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> bool"
is "op \<le> :: 'a \<Rightarrow> 'a \<Rightarrow> bool" .
lift_definition less_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> bool"
is "op < :: 'a \<Rightarrow> 'a \<Rightarrow> bool" .
instance
apply (intro_classes; transfer)
apply (auto)
done
end

instance pos :: ("{zero, linorder, no_top}") no_top
apply (intro_classes)
apply (transfer)
apply (clarsimp)
apply (meson gt_ex less_imp_le order.strict_trans1)
done

instance pos :: ("{zero, linorder, no_top}") infinite
apply (intro_classes)
apply (rule notI)
apply (subgoal_tac "\<forall>x::'a pos. x \<le> Max UNIV")
using gt_ex leD apply (blast)
apply (simp)
done

(*<*)
(* Removed as clashing with the instantiation of @{class continuum}. *)

(*
instance pos :: ("{zero, linorder, countable}") countable
apply (intro_classes)
apply (rule_tac x = "to_nat o Rep_pos" in exI)
apply (rule inj_comp)
apply (clarsimp)
apply (rule injI)
apply (simp add: Rep_pos_inject)
done
*)
(*>*)

instantiation pos :: (linordered_semidom) linordered_semidom
begin
lift_definition one_pos :: "'a pos"
is "1 :: 'a" by (simp)
lift_definition plus_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
is "op +" by (simp)
lift_definition minus_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
is "\<lambda>x y. if y \<le> x then x - y else 0"
  by (simp add: add_le_imp_le_diff)
lift_definition times_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
is "op *" by (simp)
instance
apply (intro_classes; transfer; simp?)
apply (simp add: add.assoc)
apply (simp add: add.commute)
apply (safe; clarsimp?) [1]
apply (simp add: diff_diff_add)
apply (metis add_left_mono le_add_diff_inverse)
apply (simp add: add.commute add_le_imp_le_diff)
apply (metis add_increasing2 antisym linear)
apply (simp add: mult.assoc)
apply (simp add: mult.commute)
apply (simp add: comm_semiring_class.distrib)
apply (simp add: mult_strict_left_mono)
apply (safe; clarsimp?) [1]
apply (simp add: right_diff_distrib')
apply (simp add: mult_left_mono)
using mult_left_le_imp_le apply (fastforce)
apply (simp add: distrib_left)
done
end

instantiation pos :: ("linordered_field") semidom_divide
begin
lift_definition divide_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
is "op div" by (simp)
instance
apply (intro_classes; transfer)
apply (simp_all)
done
end

subsection {* Continuum Closure *}

lemma ge_num_infinite_if_no_top:
"infinite {x::'a::{linorder, no_top}. n \<le> x}"
apply (clarsimp)
-- {* From the assumption that the set is finite. *}
apply (subgoal_tac "\<exists>y::'a. Max {x. n \<le> x} < y")
apply (clarsimp)
apply (metis Max_ge leD mem_Collect_eq order.strict_implies_order order_refl order_trans)
using gt_ex apply (blast)
done

lemma less_zero_ordLeq_ge_zero:
"|{x::'a::{ordered_ab_group_add}. x < 0}| \<le>o |{x::'a. 0 \<le> x}|"
apply (rule_tac f = "uminus" in surj_imp_ordLeq)
apply (simp add: image_def)
apply (clarsimp)
apply (rule_tac x = "- x" in exI)
apply (simp)
done

instance pos :: ("{zero, linorder, no_top}") two ..

text {* The next theorem is not entirely trivial to prove! *}

instance pos :: ("{linordered_ab_group_add, no_top, continuum}") continuum
apply (intro_classes)
apply (case_tac "countable (UNIV :: 'a set)")
-- {* Subgoal 1 (Easy Case) *}
apply (rule disjI1)
apply (subgoal_tac "\<exists>to_nat::'a \<Rightarrow> nat. inj to_nat")
-- {* Subgoal 1.1 *}
apply (clarsimp)
apply (thin_tac "countable UNIV")
apply (rule_tac x = "to_nat o Rep_pos" in exI)
apply (rule inj_comp)
apply (assumption)
apply (meson Positive_New.pos.Rep_pos_inject injI)
-- {* Subgoal 1.2 *}
apply (blast)
-- {* Subgoal 2 (Difficult Case) *}
apply (rule disjI2)
apply (subst sym [OF equal_card_bij_betw])
apply (rule equal_card_intro)
apply (subgoal_tac "|UNIV::'a pos set| =o |{x::'a. 0 \<le> x}|")
-- {* Subgoal 2.1 *}
apply (erule ordIso_transitive)
apply (rule ordIso_symmetric)
apply (subgoal_tac "|UNIV::nat set set| =o |UNIV::'a set|")
-- {* Subgoal 2.1.1 *}
apply (erule ordIso_transitive)
apply (subgoal_tac "(UNIV::'a set) = {x.0 \<le> x} \<union> {x. x < 0}")
-- {* Subgoal 2.1.1.1 *}
apply (erule ssubst)
apply (rule card_of_Un_infinite_simps(1))
apply (rule ge_num_infinite_if_no_top)
apply (rule less_zero_ordLeq_ge_zero)
-- {* Subgoal 2.1.1.2 *}
apply (auto)
-- {* Subgoal 2.1.2 *}
apply (rule_tac f = "from_nat_set" in card_of_ordIsoI)
apply (rule_tac bij_betwI'; clarsimp?)
-- {* This is the only place where @{term "countable UNIV"} is needed. *}
apply (metis bij_betw_imp_surj from_nat_set_def surj_f_inv_f to_nat_set_bij)
apply (rule_tac x = "to_nat_set y" in exI)
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (rule_tac f = "Rep_pos" in card_of_ordIsoI)
apply (rule_tac bij_betwI'; clarsimp?)
apply (simp add: Positive_New.pos.Rep_pos_inject)
using Positive_New.pos.Rep_pos apply (blast)
apply (rule_tac x = "Abs_pos y" in exI)
apply (simp add: Positive_New.pos.Abs_pos_inverse)
done
end