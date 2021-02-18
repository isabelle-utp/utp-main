section \<open> Trace Algebras \<close>

theory Trace_Algebra
  imports 
    "Z_Toolkit.List_Extra"
    "Z_Toolkit.Positive"
begin

text \<open> Trace algebras provide a useful way in the UTP of characterising different notions of trace
  history. They can characterise notions as diverse as discrete event sequences and piecewise 
  continuous functions, as employed by hybrid systems. For more information, please see our
  journal publication~\cite{Foster17b}. \<close>

subsection \<open> Ordered Semigroups \<close>

class ordered_semigroup = semigroup_add + order +
  assumes add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
  and add_right_mono: "a \<le> b \<Longrightarrow> a + c \<le> b + c"
begin

lemma add_mono:
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d"
  using local.add_left_mono local.add_right_mono local.order.trans by blast

end

subsection \<open> Monoid Subclasses \<close>

class left_cancel_monoid = monoid_add +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"

class right_cancel_monoid = monoid_add +
  assumes add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"

text \<open> Positive Monoids \<close>

class monoid_pos = monoid_add +
  assumes zero_sum_left: "a + b = 0 \<Longrightarrow> a = 0"
begin

lemma zero_sum_right: "a + b = 0 \<Longrightarrow> b = 0"
  by (metis local.add_0_left local.zero_sum_left)

lemma zero_sum: "a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (metis local.add_0_right zero_sum_right)

end

context monoid_add
begin

text \<open> An additive monoid gives rise to natural notions of order, which we here define. \<close>

definition monoid_le (infix "\<le>\<^sub>m" 50)
where "a \<le>\<^sub>m b \<longleftrightarrow> (\<exists>c. b = a + c)"

text \<open> We can also define a subtraction operator that remove a prefix from a monoid, if possible. \<close>

definition monoid_subtract (infixl "-\<^sub>m" 65)
where "a -\<^sub>m b = (if (b \<le>\<^sub>m a) then THE c. a = b + c else 0)"

text \<open> We derive some basic properties of the preorder \<close>

lemma monoid_le_least_zero: "0 \<le>\<^sub>m a"
  by (simp add: monoid_le_def)

lemma monoid_le_add: "a \<le>\<^sub>m a + b"
  by (auto simp add: monoid_le_def)

lemma monoid_le_refl: "a \<le>\<^sub>m a"
  by (simp add: monoid_le_def, metis add.right_neutral)

lemma monoid_le_trans: "\<lbrakk> a \<le>\<^sub>m b; b \<le>\<^sub>m c \<rbrakk> \<Longrightarrow> a \<le>\<^sub>m c"
  by (metis add.assoc monoid_le_def)

lemma monoid_le_add_left_mono: "a \<le>\<^sub>m b \<Longrightarrow> c + a \<le>\<^sub>m c + b"
  using add_assoc by (auto simp add: monoid_le_def)

end 

class ordered_monoid_pos = monoid_pos + ord +
  assumes le_is_monoid_le: "a \<le> b \<longleftrightarrow> (a \<le>\<^sub>m b)"
  and less_iff: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)"
begin

  subclass preorder
  proof
    fix x y z :: "'a"
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      by (simp add: local.less_iff)
    show "x \<le> x"
      by (simp add: local.le_is_monoid_le local.monoid_le_refl)
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      using local.le_is_monoid_le local.monoid_le_trans by blast
  qed

end

subsection \<open> Trace Algebras \<close>

text \<open> A pre-trace algebra is based on a left-cancellative monoid with the additional property that
  plus has no additive inverse. The latter is required to ensure that there are no ``negative 
  traces''. A pre-trace algebra has all the trace algebra axioms, but does not export the definitions
  of @{term "(\<le>)"} and @{term "(-)"}. \<close>


class pre_trace = left_cancel_monoid + monoid_pos
begin

text \<open> From our axiom set, we can derive a variety of properties of the monoid order \<close>
  
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


text \<open> The monoid minus operator is also the inverse of plus in this context, as expected. \<close>

lemma add_monoid_diff_cancel_left [simp]: "(a + b) -\<^sub>m a = b"
  apply (simp add: monoid_subtract_def monoid_le_add)
  apply (rule the_equality)
   apply (simp)
  using local.add_left_imp_eq apply blast
  done

text \<open> Iterating a trace \<close>

fun tr_iter :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" where
tr_iter_0: "tr_iter 0 t = 0" |
tr_iter_Suc: "tr_iter (Suc n) t = tr_iter n t + t"

lemma tr_iter_empty [simp]: "tr_iter m 0 = 0"
  by (induct m, simp_all)

end

text \<open> We now construct the trace algebra by also exporting the order and minus operators. \<close>

class trace = pre_trace + ord + minus +
  assumes le_is_monoid_le: "a \<le> b \<longleftrightarrow> (a \<le>\<^sub>m b)"
  and less_iff: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)"
  and minus_def: "a - b = a -\<^sub>m b"
begin

text \<open> Next we prove all the trace algebra lemmas. \<close>

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
      by (metis add_assoc local.add_diff_cancel_left local.le_iff_add)
  next
    case False thus ?thesis
      using local.add_le_imp_le_left not_le_minus by blast
  qed

  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = 0 \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add local.monoid_le_def by auto

  lemma diff_add_cancel_left': "a \<le> b \<Longrightarrow> a + (b - a) = b"
    using local.le_iff_add local.monoid_le_def by auto

  lemma add_left_strict_mono: "\<lbrakk> a + b < a + c \<rbrakk> \<Longrightarrow> b < c"
    using local.add_le_imp_le_left local.add_left_mono local.less_iff by blast
      
  lemma sum_minus_left: "c \<le> a \<Longrightarrow> (a + b) - c = (a - c) + b"
    by (metis add_assoc diff_add_cancel_left' local.add_monoid_diff_cancel_left local.minus_def)      
      
  lemma neq_zero_impl_greater:
    "x \<noteq> 0 \<Longrightarrow> 0 < x"
    using le_is_monoid_le less_iff monoid_le_antisym monoid_le_least_zero by auto
 
  lemma minus_cancel_le:
    "\<lbrakk> x \<le> y; y \<le> z \<rbrakk> \<Longrightarrow> y - x \<le> z - x"
    using add_assoc le_iff_add by auto

  lemma sum_minus_right: "c \<ge> a \<Longrightarrow> a + b - c = b - (c - a)"
    by (metis diff_add_cancel_left' local.add_diff_cancel_left')

  lemma minus_gr_zero_iff [simp]:
    "0 < x - y \<longleftrightarrow> y < x"
    by (metis diff_cancel le_is_monoid_le least_zero less_iff minus_zero_eq monoid_le_antisym not_le_minus)

  lemma le_zero_iff [simp]: "x \<le> 0 \<longleftrightarrow> x = 0"
    using local.le_iff_add local.zero_sum by auto
            
  lemma minus_assoc [simp]: "x - y - z = x - (y + z)"
    by (metis diff_add_cancel_left' le_add local.add_0_right local.add_diff_cancel_left' local.zero_sum minus_cancel_le not_le_minus)
      
end

class trace_split = trace +
  assumes
  sum_eq_sum_conv: "(a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
  \<comment> \<open> @{thm sum_eq_sum_conv} shows how two equal traces that are each composed of two subtraces,
       can be expressed in terms of each other. \<close>
begin

  text \<open> The set subtraces of a common trace $c$ is totally ordered. \<close>

  lemma le_common_total: "\<lbrakk> a \<le> c; b \<le> c \<rbrakk> \<Longrightarrow> a \<le> b \<or> b \<le> a"
    by (metis diff_add_cancel_left' le_add local.sum_eq_sum_conv)  

  lemma le_sum_cases: "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a"
    by (simp add: le_common_total)
            
  lemma le_sum_cases':
    "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    by (auto, metis le_sum_cases, metis minus_def le_is_monoid_le add_monoid_diff_cancel_left monoid_le_def sum_eq_sum_conv)

  lemma le_sum_iff: "a \<le> b + c \<longleftrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    by (metis le_sum_cases' add_monoid_diff_cancel_left le_is_monoid_le minus_def monoid_le_add_left_mono monoid_le_def monoid_le_trans)

end



text \<open> Trace algebra give rise to a partial order on traces. \<close>

instance trace \<subseteq> order
  apply (intro_classes)
     apply (simp_all add: less_iff le_is_monoid_le monoid_le_refl)
  using monoid_le_trans apply blast
  apply (simp add: monoid_le_antisym)
  done

subsection \<open> Models \<close>

text \<open> Lists form a trace algebra. \<close>

instantiation list :: (type) monoid_add
begin

  definition zero_list :: "'a list" where "zero_list = []"
  definition plus_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where "plus_list = (@)"

instance
  by (intro_classes, simp_all add: zero_list_def plus_list_def)

end

lemma monoid_le_list:
  "(xs :: 'a list) \<le>\<^sub>m ys \<longleftrightarrow> xs \<le> ys"
  apply (simp add: monoid_le_def plus_list_def)
  apply (meson Prefix_Order.prefixE Prefix_Order.prefixI)
  done

lemma monoid_subtract_list:
  "(xs :: 'a list) -\<^sub>m ys = xs - ys"
  apply (auto simp add: monoid_subtract_def monoid_le_list minus_list_def less_eq_list_def)
   apply (rule the_equality)
    apply (simp_all add: zero_list_def plus_list_def prefix_drop)
  done

instance list :: (type) trace_split
  apply (intro_classes, simp_all add: zero_list_def plus_list_def monoid_le_def monoid_subtract_list)
  using Prefix_Order.prefixE apply blast
   apply (simp add: less_list_def)
  apply (simp add: append_eq_append_conv2)
  done

lemma monoid_le_nat:
  "(x :: nat) \<le>\<^sub>m y \<longleftrightarrow> x \<le> y"
  by (simp add: monoid_le_def nat_le_iff_add)

lemma monoid_subtract_nat:
  "(x :: nat) -\<^sub>m y = x - y"
  by (auto simp add: monoid_subtract_def monoid_le_nat)

instance nat :: trace_split
  apply (intro_classes, simp_all add: monoid_subtract_nat)
   apply (simp add: nat_le_iff_add monoid_le_def)
   apply linarith+
  apply (metis Nat.diff_add_assoc Nat.diff_add_assoc2 add_diff_cancel_right' add_le_cancel_left add_le_cancel_right add_less_mono cancel_ab_semigroup_add_class.add_diff_cancel_left' less_irrefl not_le)
  done

text \<open> Positives form a trace algebra. \<close>
    
instance pos :: (linordered_semidom) trace_split
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

end
