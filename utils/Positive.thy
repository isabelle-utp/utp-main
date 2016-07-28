section {* Positive numbers *}

theory Positive
imports Real
begin

typedef (overloaded) 'a::"{zero,order}" pos = "{x::'a. x \<ge> 0}"
  by (auto)

setup_lifting type_definition_pos

instantiation pos :: ("{zero,order}") zero
begin

lift_definition zero_pos :: "'a pos" is 0 by auto

instance ..
end

instantiation pos :: ("{zero,order}") order
begin

lift_definition less_eq_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> bool" is "op \<le> :: 'a \<Rightarrow> 'a \<Rightarrow> bool" .
lift_definition less_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> bool" is "op < :: 'a \<Rightarrow> 'a \<Rightarrow> bool" .

instance
  by (intro_classes, (transfer, auto)+)
end

instantiation pos :: ("{ordered_ab_semigroup_add,monoid_add}") ordered_ab_semigroup_add
begin

lift_definition plus_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos" is plus
  by (metis add.right_neutral add_mono)

instance 
  apply (intro_classes)
  apply (transfer, simp add: add.assoc)
  apply (transfer, metis add.commute)
  apply (transfer, metis add_left_mono)
done

end

instance pos :: ("{ordered_ab_semigroup_add,monoid_add}") monoid_add
  by (intro_classes, transfer, metis add.left_neutral, transfer, metis add.right_neutral)

instance pos :: ("{ordered_ab_semigroup_add,comm_monoid_add}") comm_monoid_add
  by (intro_classes, metis add.left_neutral)

instance real :: ordered_ab_semigroup_add ..

instantiation pos :: (linordered_semidom) linordered_semidom
begin

lift_definition one_pos :: "'a pos" is 1
  by (metis zero_le_one)

lift_definition times_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos" is times
  by (metis mult_nonneg_nonneg)

lift_definition minus_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos" 
is "\<lambda> x y. if (y \<le> x) then x - y else 0"
  by (auto, metis add.left_neutral add_le_imp_le_diff)

instance
  apply (intro_classes)
  apply (transfer, auto, metis add_increasing2 dual_order.refl)
  apply (transfer, auto)
  apply (metis diff_diff_add)
  apply (metis add_mono_thms_linordered_semiring(2) le_add_diff_inverse)
  apply (metis add.commute add_le_imp_le_diff)
  apply (metis add.right_neutral add_le_cancel_left dual_order.trans)
  apply (transfer, auto)
  apply (transfer, metis mult.assoc)
  apply (transfer, metis mult.commute)
  apply (transfer, metis distrib_left mult.commute)
  apply (transfer, metis mult_zero_left)
  apply (transfer, metis mult_zero_right)
  apply (transfer, metis mult_strict_left_mono)
  apply (transfer, metis mult.left_neutral)
  apply (transfer, metis zero_neq_one)
  apply (transfer, metis (mono_tags, lifting) antisym_conv2 mult_left_le_imp_le mult_not_zero ordered_comm_semiring_class.comm_mult_left_mono right_diff_distrib')
  apply (transfer, metis distrib_left)
  apply (transfer, metis divisors_zero)
  apply (transfer, metis zero_less_one)
  apply (transfer, metis (full_types) le_add_diff_inverse2)
done
end

type_synonym preal = "real pos"

end