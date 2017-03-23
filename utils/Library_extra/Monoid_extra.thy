section {* Monoid variants and extra properties *}

theory Monoid_extra
  imports List_extra "~~/src/HOL/Library/Prefix_Order"
begin

class ordered_semigroup = semigroup_add + order +
  assumes add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
  and add_right_mono: "a \<le> b \<Longrightarrow> a + c \<le> b + c"
begin

lemma add_mono:
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d"
  using local.add_left_mono local.add_right_mono local.order.trans by blast

end

thm cancel_semigroup_add_axioms

class left_cancel_monoid = monoid_add +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"

class right_cancel_monoid = monoid_add +
  assumes add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"

class monoid_sum_0 = monoid_add +
  assumes zero_sum_left: "a + b = 0 \<Longrightarrow> a = 0"
begin

lemma zero_sum_right: "a + b = 0 \<Longrightarrow> b = 0"
  by (metis local.add_0_left local.zero_sum_left)

lemma zero_sum: "a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (metis local.add_0_right zero_sum_right)

end

context monoid_add
begin

definition monoid_le (infix "\<le>\<^sub>m" 50)
where "a \<le>\<^sub>m b \<longleftrightarrow> (\<exists>c. b = a + c)"

definition monoid_subtract (infixl "-\<^sub>m" 65)
where "a -\<^sub>m b = (if (b \<le>\<^sub>m a) then THE c. a = b + c else 0)"

end

class cancel_monoid = left_cancel_monoid + right_cancel_monoid + monoid_sum_0
begin

lemma monoid_le_least_zero: "0 \<le>\<^sub>m a"
  by (simp add: monoid_le_def)

lemma monoid_le_refl: "a \<le>\<^sub>m a"
  by (simp add: monoid_le_def, metis add.right_neutral)

lemma monoid_le_trans: "\<lbrakk> a \<le>\<^sub>m b; b \<le>\<^sub>m c \<rbrakk> \<Longrightarrow> a \<le>\<^sub>m c"
  by (metis add.assoc monoid_le_def)

lemma monoid_le_antisym:
  assumes "a \<le>\<^sub>m b" "b \<le>\<^sub>m a"
  shows "a = b"
proof -
  obtain a' where a': "b = a + a'"
    using assms(1) monoid_le_def by auto

  obtain b' where b': "a = b + b'"
    using assms(2) monoid_le_def by auto

  have "b' = (b' + a' + b')"
    by (metis a' add_assoc b' local.add_left_imp_eq)

  hence "a' + b' = 0"
    by (metis add_assoc local.add_0_right local.add_left_imp_eq)

  hence "a' = 0" "b' = 0"
    by (simp add: zero_sum)+

  with a' b' show ?thesis
    by simp
qed

lemma monoid_le_add: "a \<le>\<^sub>m a + b"
  by (auto simp add: monoid_le_def)

lemma monoid_le_add_left_mono: "a \<le>\<^sub>m b \<Longrightarrow> c + a \<le>\<^sub>m c + b"
  using add_assoc by (auto simp add: monoid_le_def)

lemma add_monoid_diff_cancel_left [simp]: "(a + b) -\<^sub>m a = b"
  apply (simp add: monoid_subtract_def monoid_le_add)
  apply (rule the_equality)
  apply (simp)
  using local.add_left_imp_eq apply blast
done

end

class ordered_cancel_monoid_diff = cancel_monoid + ord + minus +
  assumes le_is_monoid_le: "a \<le> b \<longleftrightarrow> (a \<le>\<^sub>m b)"
  and less_iff: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)"
  and minus_def: "a - b = a -\<^sub>m b"

instance ordered_cancel_monoid_diff \<subseteq> order
  apply (intro_classes)
  apply (simp_all add: less_iff le_is_monoid_le monoid_le_refl)
  using monoid_le_trans apply blast
  apply (simp add: monoid_le_antisym)
done

context ordered_cancel_monoid_diff
begin

  lemma le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists> c. b = a + c)"
    by (simp add: local.le_is_monoid_le local.monoid_le_def)

  lemma least_zero [simp]: "0 \<le> a"
    by (simp add: local.le_is_monoid_le local.monoid_le_least_zero)

  lemma le_add [simp]: "a \<le> a + b"
    by (simp add: le_is_monoid_le local.monoid_le_add)

  lemma not_le_minus [simp]:  "\<not> (a \<le> b) \<Longrightarrow> b - a = 0"
    by (simp add: le_is_monoid_le local.minus_def local.monoid_subtract_def)

  lemma add_diff_cancel_left [simp]: "(a + b) - a = b"
    by (simp add: minus_def)

  lemma diff_zero [simp]: "a - 0 = a"
    by (metis local.add_0_left local.add_diff_cancel_left)

  lemma diff_cancel [simp]: "a - a = 0"
    by (metis local.add_0_right local.add_diff_cancel_left)

  lemma add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by (simp add: local.le_is_monoid_le local.monoid_le_add_left_mono)

  lemma add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"
    by (auto simp add: le_iff_add, metis add_assoc local.add_diff_cancel_left)

  lemma add_diff_cancel_left' [simp]:  "(c + a) - (c + b) = a - b"
  proof (cases "b \<le> a")
    case True thus ?thesis
      by (metis add_assoc local.add_diff_cancel_left local.le_iff_add local.monoid_le_def)
  next
    case False thus ?thesis
      using local.add_le_imp_le_left not_le_minus by blast
  qed

  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = 0 \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add local.monoid_le_def by auto

  lemma diff_add_cancel_left': "a \<le> b \<Longrightarrow> a + (b - a) = b"
    using local.le_iff_add local.monoid_le_def by auto

end

instantiation list :: (type) monoid_add
begin

  definition zero_list :: "'a list" where "zero_list = []"
  definition plus_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where "plus_list = op @"

instance
  by (intro_classes, simp_all add: zero_list_def plus_list_def)

end

lemma monoid_le_list:
  "(xs :: 'a list) \<le>\<^sub>m ys \<longleftrightarrow> xs \<le> ys"
  apply (simp add: monoid_le_def plus_list_def)
  using Prefix_Order.prefixE Prefix_Order.prefixI apply blast
done

lemma monoid_subtract_list:
  "(xs :: 'a list) -\<^sub>m ys = xs - ys"
  apply (auto simp add: monoid_subtract_def monoid_le_list minus_list_def less_eq_list_def)
  apply (rule the_equality)
  apply (simp_all add: zero_list_def plus_list_def prefix_drop)
done

instance list :: (type) ordered_cancel_monoid_diff
  apply (intro_classes, simp_all add: zero_list_def plus_list_def monoid_le_def monoid_subtract_list)
  using Prefix_Order.prefixE Prefix_Order.prefixI apply blast
  apply (simp add: less_list_def)
done

lemma monoid_le_nat:
  "(x :: nat) \<le>\<^sub>m y \<longleftrightarrow> x \<le> y"
  by (simp add: monoid_le_def nat_le_iff_add)

lemma monoid_subtract_nat:
  "(x :: nat) -\<^sub>m y = x - y"
  by (auto simp add: monoid_subtract_def monoid_le_nat)

instance nat :: ordered_cancel_monoid_diff
  apply (intro_classes, simp_all add: monoid_subtract_nat)
  apply (simp add: nat_le_iff_add monoid_le_def)
  apply linarith
done
end