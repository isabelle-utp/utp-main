  (******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Positive_New.thy                                                     *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Sept 2017 *)

section {* Positive Subtypes *}

theory Positive
imports 
  Infinity 
  "Library_extra/Monoid_extra"
  "~~/src/HOL/Library/Countable"
begin

text {* Move this instantiation to a more suitable place in the hierarchy. *}


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
            apply (metis add_le_cancel_left le_add_diff_inverse)
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

lemma pos_positive [simp]: "0 \<le> (x::'a::{zero,linorder} pos)"
  by (transfer, simp)

text {* Positives form a trace algebra *}
    
instance pos :: (linordered_semidom) trace
proof (intro_classes, simp_all)
  fix a b c d :: "'a pos"
  show "a + b = 0 \<Longrightarrow> a = 0"
    by (transfer, simp add: add_nonneg_eq_0_iff)
  show "a + b = c + d \<Longrightarrow> \<exists>e. a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
    apply (cases "c \<le> a")
    apply (metis (no_types, lifting) cancel_semigroup_add_class.add_left_imp_eq le_add_diff_inverse semiring_normalization_rules(25))
    apply (metis (no_types, lifting) cancel_semigroup_add_class.add_left_imp_eq less_imp_le linordered_semidom_class.add_diff_inverse semiring_normalization_rules(21))
  done
  show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    by auto    
  show le_def: "\<And> a b :: 'a pos. (a \<le> b) = (a \<le>\<^sub>m b)"    
    by (auto simp add: monoid_le_def, metis le_add_diff_inverse)  
  show "a - b = a -\<^sub>m b"
    apply (auto simp add: monoid_subtract_def le_def[THEN sym])
     apply (rule sym)
     apply (rule the_equality)
      apply (simp_all)
      apply (transfer, simp)
  done
qed
    
type_synonym preal = "real pos"

end