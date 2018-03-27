(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Trace_Algebra_Hierarchy.thy                                          *)
(* Authors: Pedro Ribeiro                                                     *)
(* Emails: pedro.ribeiro@york.ac.uk                                           *)
(******************************************************************************)

theory Trace_Algebra_Hierarchy
  imports
    Trace_Algebra
    Trace_Algebra_Preorder
begin

section \<open> Hierarchy \<close>

subsection \<open> Trace Algebra and preorder variant \<close>

class fzero_is_0_sum_zero = fzero_is_0 + fzero_sum_zero

instance fzero_is_0_sum_zero \<subseteq> monoid_sum_0
  apply intro_classes
  apply (metis add_fzero_left fzero_is_0)
  apply (metis add_fzero_right fzero_is_0)
  by (metis fzero_is_0 fzero_sum)

text \<open> A semigroup trace with a fixed zero (@{term fzero_is_0}) 
       is a monoid. \<close>

class fzero_trace_0 = fzero_trace + fzero_is_0

instance fzero_trace_0 \<subseteq> monoid_add
proof
  fix a :: "'a::fzero_trace_0"
  show add_fzero_left: 
    "0 + a = a"
    by (metis add_fzero_right fzero_is_0 fzero_pre_trace_class.sum_eq_sum_conv semigroup_add_left_cancel_class.add_left_imp_eq)
  show add_zero_right: 
    "a + 0 = a"
    by (metis add_fzero_right fzero_is_0)
qed

text \<open> A semigroup trace with a fixed zero (@{term fzero_is_0}) 
       is a monoid trace. \<close>

instance fzero_trace_0 \<subseteq> trace 
proof
  fix a b c d :: "'a::fzero_trace_0"
  show left_cancellative: 
    "a + b = a + c \<Longrightarrow> b = c"
    using semigroup_add_left_cancel_class.add_left_imp_eq by blast
  show sum_left_zero:
    "a + b = 0 \<Longrightarrow> a = 0"
    by (metis add.right_neutral add_fzero_right fzero_sum_left semigroup_add_left_cancel_class.add_left_imp_eq)
  show sum_eq_conv:
    "a + b = c + d \<Longrightarrow> \<exists>e. a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
    by (simp add: fzero_pre_trace_class.sum_eq_sum_conv)
  show monoid_le:
    "(a \<le> b) = (a \<le>\<^sub>m b)"
    by (simp add: monoid_le_def semigroup_add_left_cancel_minus_ord_class.le_iff_add)
  show less:
    "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    by (simp add: fzero_add_fzero_ord_minus_class.less_iff)
  show minus:
    "a - b = a -\<^sub>m b"
    by (metis fzero_add_fzero_ord_minus_class.minus_def fzero_is_0 fzero_subtract_def le_is_fzero_le monoid_le_def monoid_subtract_def semigroup_add_left_cancel_minus_ord_class.le_iff_add)
qed

text \<open> Similarly, a trace which has a fixed @{term f\<^sub>0} is a semigroup satisfying the 
       mirror properties of a monoid. \<close>

class trace_fzero_0 = trace + fzero_is_0

instance trace_fzero_0 \<subseteq> fzero_add_zero
proof
  fix a b :: "'a::trace_fzero_0"
  show "f\<^sub>0(f\<^sub>0(a)) = f\<^sub>0(a)"
    by (simp add: fzero_is_0)
  show "f\<^sub>0(a) + a = a"
    by (simp add: fzero_is_0)
  show "a + f\<^sub>0(a) = a"
    by (simp add: fzero_is_0)
qed

text \<open> Hence such a trace is also a semigroup trace. \<close>

instance trace_fzero_0 \<subseteq> fzero_trace
proof
  fix a b c d :: "'a::trace_fzero_0"
  show "(a \<le> b) = (a \<le>\<^sub>u\<^sub>s b)"
    by (simp add: fzero_le_def trace_class.le_iff_add)
  show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    by (simp add: trace_class.less_iff)
  show "a - b = a -\<^sub>u\<^sub>s b"
    by (metis fzero_is_0 fzero_le_def fzero_subtract_def le_is_monoid_le monoid_subtract_def trace_class.le_iff_add trace_class.minus_def)
  show "a + b = a + c \<Longrightarrow> b = c"
    using left_cancel_monoid_class.add_left_imp_eq by blast
  show "a + b = c + d \<Longrightarrow> \<exists>e. a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
    by (simp add: pre_trace_class.sum_eq_sum_conv)
  show "a + b = f\<^sub>0(b) \<Longrightarrow> b = f\<^sub>0(b)"
    by (simp add: fzero_is_0 zero_sum_right)
qed

text \<open> Therefore, a semigroup trace with a fixed @{term f\<^sub>0} is exactly the same as the
       monoid trace. This is convenient as any type instantiated with the class @{class trace}
       can also be instantiated with the class @{class fzero_trace} by defining an appropriate
       @{term f\<^sub>0}. \<close>

section \<open> Models \<close>

subsection \<open> Lists \<close>

instantiation list :: (type) fzero_is_0
begin
  definition fzero_list :: "'a list \<Rightarrow> 'a list" where "fzero_list a = []"

  instance by (intro_classes, simp add:fzero_list_def zero_list_def)
end
    
instantiation list :: (type) fzero_add_zero
begin
 
  instance by (intro_classes, simp_all add:fzero_list_def plus_list_def)
end
    
lemma fzero_le_list:
  "(xs :: 'a list) \<le>\<^sub>u\<^sub>s ys \<longleftrightarrow> xs \<le> ys"
  apply (simp add: fzero_le_def plus_list_def)
  using Prefix_Order.prefixE Prefix_Order.prefixI by blast
    
lemma fzero_subtract_list:
  "(xs :: 'a list) -\<^sub>u\<^sub>s ys = xs - ys"
  proof (cases "ys \<le> xs")
    case True
    then show ?thesis 
      apply (auto simp add: fzero_subtract_def fzero_le_list minus_list_def less_eq_list_def)
      apply (rule the_equality)
      by (simp_all add: fzero_list_def plus_list_def prefix_drop)
  next
    case False then show ?thesis
      by (simp add: fzero_is_0 fzero_le_list fzero_subtract_def)
  qed

instance list :: (type) trace_fzero_0
  by intro_classes

subsection \<open> Naturals \<close>

instantiation nat :: fzero_is_0
begin
  
  definition fzero_nat :: "nat \<Rightarrow> nat" where "fzero_nat a = 0"
 
  instance
    by (intro_classes, auto simp add:fzero_nat_def)
end
  
instantiation nat :: fzero_add_zero
begin
  instance by (intro_classes, simp_all add:fzero_nat_def)
end
  
lemma fzero_le_nat:
  "(x :: nat) \<le>\<^sub>u\<^sub>s y \<longleftrightarrow> x \<le> y"
  by (simp add: fzero_le_def trace_class.le_iff_add)
  
lemma fzero_subtract_nat:
  "(x :: nat) -\<^sub>u\<^sub>s y = x - y"
  by (auto simp add:fzero_subtract_def fzero_le_nat fzero_nat_def) 

instance nat :: trace_fzero_0
  by intro_classes

instance nat :: fzero_trace
  by intro_classes

subsection \<open> Positives \<close>

instantiation pos :: (linordered_semidom) trace_fzero_0
begin
  definition fzero_pos :: "'a\<^sup>+ \<Rightarrow> 'a\<^sup>+" where "fzero_pos a = 0"

  instance by (intro_classes, auto simp add:fzero_pos_def)
end

instance pos :: (linordered_semidom) fzero_trace
  by intro_classes

end