section {* Extra monoid variants for traces *}

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

class cancel_monoid_add = monoid_add + minus +
  assumes add_diff_cancel_left [simp]: "(c + a) - (c + b) = a - b"
  and diff_zero [simp]: "a - 0 = a"
begin

  lemma add_diff_cancel_left' [simp]: "(a + b) - a = b"
    by (metis local.add_0_right local.add_diff_cancel_left local.diff_zero)

  lemma diff_cancel [simp]: "a - a = 0"
    by (metis local.add_0_right local.add_diff_cancel_left')

  lemma add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
      by (metis local.add_diff_cancel_left')

end

class ordered_cancel_monoid_diff = cancel_monoid_add + order +
  assumes le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)"
begin

  lemma add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    using local.add_assoc local.le_iff_add by auto

  lemma add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"
    by (auto simp add: le_iff_add, metis local.add_assoc local.add_diff_cancel_left')

  lemma zero_least [simp]: "0 \<le> a"
    by (simp add: le_iff_add)

  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = 0 \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add by auto

  lemma diff_add_cancel_left': "a \<le> b \<Longrightarrow> a + (b - a) = b"
    using local.le_iff_add by auto

end

instantiation list :: (type) ordered_cancel_monoid_diff
begin

  definition zero_list :: "'a list" where "zero_list = []"
  definition plus_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where "plus_list = op @"

instance
  apply (intro_classes)
  apply (simp_all add: zero_list_def plus_list_def)
  apply (simp add: list_concat_minus_list_concat)
  using strict_prefixE strict_prefixI apply blast
done

end

instance nat :: ordered_cancel_monoid_diff
  by (intro_classes, simp_all, presburger)

end