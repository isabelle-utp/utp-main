section \<open>\<open>Extra_Ordered_Fields\<close> -- Additional facts about ordered fields\<close>

theory Extra_Ordered_Fields
  imports Complex_Main 
    Jordan_Normal_Form.Conjugate (* Defines ordering for complex. We have to use theirs, otherwise there will be conflicts *)
begin


subsection\<open>Ordered Fields\<close>
text \<open>In this section we introduce some type classes for ordered rings/fields/etc.
that are weakenings of existing classes. Most theorems in this section are 
copies of the eponymous theorems from Isabelle/HOL, except that they are now proven 
requiring weaker type classes (usually the need for a total order is removed).

Since the lemmas are identical to the originals except for weaker type constraints, 
we use the same names as for the original lemmas. (In fact, the new lemmas could replace
the original ones in Isabelle/HOL with at most minor incompatibilities.\<close>

subsection \<open>Missing from Orderings.thy\<close>

text \<open>This class is analogous to \<^class>\<open>unbounded_dense_linorder\<close>, except that it does not require a total order\<close>

class unbounded_dense_order = dense_order + no_top + no_bot

instance unbounded_dense_linorder \<subseteq> unbounded_dense_order ..

subsection \<open>Missing from Rings.thy\<close>

text \<open>The existing class \<^class>\<open>abs_if\<close> requires \<^term>\<open>\<bar>a\<bar> = (if a < 0 then - a else a)\<close>.
However, if \<^term>\<open>(<)\<close> is not a total order, this condition is too strong when \<^term>\<open>a\<close> 
is incomparable with \<^term>\<open>0\<close>. (Namely, it requires the absolute value to be
the identity on such elements. E.g., the absolute value for complex numbers does not 
satisfy this.) The following class \<open>partial_abs_if\<close> is analogous to \<^class>\<open>abs_if\<close>
but does not require anything if \<^term>\<open>a\<close> is incomparable with \<^term>\<open>0\<close>.\<close>


class partial_abs_if = minus + uminus + ord + zero + abs +
  assumes abs_neg: "a \<le> 0 \<Longrightarrow> abs a = -a"
  assumes abs_pos: "a \<ge> 0 \<Longrightarrow> abs a = a"

class ordered_semiring_1 = ordered_semiring + semiring_1
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_semiring_1\<close> without requiring a total order\<close>
begin

lemma convex_bound_le:
  assumes "x \<le> a" and "y \<le> a" and "0 \<le> u" and "0 \<le> v" and "u + v = 1"
  shows "u * x + v * y \<le> a"
proof-
  from assms have "u * x + v * y \<le> u * a + v * a"
    by (simp add: add_mono mult_left_mono)
  with assms show ?thesis
    unfolding distrib_right[symmetric] by simp
qed

end

subclass (in linordered_semiring_1) ordered_semiring_1 ..

class ordered_semiring_strict = semiring + comm_monoid_add + ordered_cancel_ab_semigroup_add +
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_semiring_strict\<close> without requiring a total order\<close>
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin

subclass semiring_0_cancel ..

subclass ordered_semiring
proof
  fix a b c :: 'a
  assume t1: "a \<le> b" and t2: "0 \<le> c"
  thus "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
  from t2 show "a * c \<le> b * c"
    unfolding le_less
    by (metis local.antisym_conv2 local.mult_not_zero local.mult_strict_right_mono t1)    
qed

lemma mult_pos_pos[simp]: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a * b"
  using mult_strict_left_mono [of 0 b a] by simp

lemma mult_pos_neg: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> a * b < 0"
  using mult_strict_left_mono [of b 0 a] by simp

lemma mult_neg_pos: "a < 0 \<Longrightarrow> 0 < b \<Longrightarrow> a * b < 0"
  using mult_strict_right_mono [of a 0 b] by simp

text \<open>Strict monotonicity in both arguments\<close>
lemma mult_strict_mono:
  assumes t1: "a < b" and t2: "c < d" and t3: "0 < b" and t4: "0 \<le> c"
  shows "a * c < b * d"
proof-
  have "a * c < b * d"
    by (metis local.dual_order.order_iff_strict local.dual_order.strict_trans2 
        local.mult_strict_left_mono local.mult_strict_right_mono local.mult_zero_right t1 t2 t3 t4)        
  thus ?thesis
    using assms by blast
qed


text \<open>This weaker variant has more natural premises\<close>
lemma mult_strict_mono':
  assumes "a < b" and "c < d" and "0 \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
  by (rule mult_strict_mono) (insert assms, auto)

lemma mult_less_le_imp_less:
  assumes t1: "a < b" and t2: "c \<le> d" and t3: "0 \<le> a" and t4: "0 < c"
  shows "a * c < b * d"
  using local.mult_strict_mono' local.mult_strict_right_mono local.order.order_iff_strict 
    t1 t2 t3 t4 by auto

lemma mult_le_less_imp_less:
  assumes "a \<le> b" and "c < d" and "0 < a" and "0 \<le> c"
  shows "a * c < b * d"
  by (metis assms(1) assms(2) assms(3) assms(4) local.antisym_conv2 local.dual_order.strict_trans1 
      local.mult_strict_left_mono local.mult_strict_mono)

end

subclass (in linordered_semiring_strict) ordered_semiring_strict 
proof
  show "c * a < c * b"
    if "a < b"
      and "0 < c"
    for a :: 'a
      and b 
      and c 
    using that
    by (simp add: local.mult_strict_left_mono) 
  show "a * c < b * c"
    if "a < b"
      and "0 < c"
    for a :: 'a
      and b 
      and c 
    using that
    by (simp add: local.mult_strict_right_mono) 
qed

class ordered_semiring_1_strict = ordered_semiring_strict + semiring_1
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_semiring_1_strict\<close> without requiring 
  a total order\<close>
begin

subclass ordered_semiring_1 ..

lemma convex_bound_lt:
  assumes "x < a" and "y < a" and "0 \<le> u" and "0 \<le> v" and "u + v = 1"
  shows "u * x + v * y < a"
proof -
  from assms have "u * x + v * y < u * a + v * a"
    by (cases "u = 0") (auto intro!: add_less_le_mono mult_strict_left_mono mult_left_mono)
  with assms show ?thesis
    unfolding distrib_right[symmetric] by simp
qed

end

subclass (in linordered_semiring_1_strict) ordered_semiring_1_strict .. 

class ordered_comm_semiring_strict = comm_semiring_0 + ordered_cancel_ab_semigroup_add +
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_comm_semiring_strict\<close> without requiring a total order\<close>
  assumes comm_mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
begin

subclass ordered_semiring_strict
proof
  fix a b c :: 'a
  assume "a < b" and "0 < c"
  thus "c * a < c * b"
    by (rule comm_mult_strict_left_mono)
  thus "a * c < b * c"
    by (simp only: mult.commute)
qed

subclass ordered_cancel_comm_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" and "0 \<le> c"
  thus "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
qed

end

subclass (in linordered_comm_semiring_strict) ordered_comm_semiring_strict 
  apply standard
  by (simp add: local.mult_strict_left_mono)

class ordered_ring_strict = ring + ordered_semiring_strict
  + ordered_ab_group_add + partial_abs_if
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_ring_strict\<close> without requiring a total order\<close>
begin

subclass ordered_ring ..

lemma mult_strict_left_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> c * a < c * b"
  using mult_strict_left_mono [of b a "- c"] by simp

lemma mult_strict_right_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> a * c < b * c"
  using mult_strict_right_mono [of b a "- c"] by simp

lemma mult_neg_neg: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> 0 < a * b"
  using mult_strict_right_mono_neg [of a 0 b] by simp

end

lemmas mult_sign_intros =
  mult_nonneg_nonneg mult_nonneg_nonpos
  mult_nonpos_nonneg mult_nonpos_nonpos
  mult_pos_pos mult_pos_neg
  mult_neg_pos mult_neg_neg


subsection \<open>Ordered fields\<close>

class ordered_field = field + order + ordered_comm_semiring_strict + ordered_ab_group_add 
  + partial_abs_if 
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_field\<close> without requiring a total order\<close>
begin

lemma frac_less_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y < w / z \<longleftrightarrow> (x * z - w * y) / (y * z) < 0"
  by (subst less_iff_diff_less_0) (simp add: diff_frac_eq )

lemma frac_le_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y \<le> w / z \<longleftrightarrow> (x * z - w * y) / (y * z) \<le> 0"
  by (subst le_iff_diff_le_0) (simp add: diff_frac_eq )

lemmas sign_simps = algebra_simps zero_less_mult_iff mult_less_0_iff

lemmas (in -) sign_simps = algebra_simps zero_less_mult_iff mult_less_0_iff

text\<open>Simplify expressions equated with 1\<close>

lemma zero_eq_1_divide_iff [simp]: "0 = 1 / a \<longleftrightarrow> a = 0"
  by (cases "a = 0") (auto simp: field_simps)

lemma one_divide_eq_0_iff [simp]: "1 / a = 0 \<longleftrightarrow> a = 0"
  using zero_eq_1_divide_iff[of a] by simp

text\<open>Simplify expressions such as \<open>0 < 1/x\<close> to \<open>0 < x\<close>\<close>

text\<open>Simplify quotients that are compared with the value 1.\<close>

text \<open>Conditional Simplification Rules: No Case Splits\<close>

lemma eq_divide_eq_1 [simp]:
  "(1 = b/a) = ((a \<noteq> 0 & a = b))"
  by (auto simp add: eq_divide_eq)

lemma divide_eq_eq_1 [simp]:
  "(b/a = 1) = ((a \<noteq> 0 & a = b))"
  by (auto simp add: divide_eq_eq)

end (* class ordered_field *)


text \<open>The following type class intends to capture some important properties 
  that are common both to the real and the complex numbers. The purpose is
  to be able to state and prove lemmas that apply both to the real and the complex 
  numbers without needing to state the lemma twice.
\<close>

class nice_ordered_field = ordered_field + zero_less_one + idom_abs_sgn +
  assumes positive_imp_inverse_positive: "0 < a \<Longrightarrow> 0 < inverse a"
    and inverse_le_imp_le: "inverse a \<le> inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> a"
    and dense_le: "(\<And>x. x < y \<Longrightarrow> x \<le> z) \<Longrightarrow> y \<le> z"
    and nn_comparable: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a \<le> b \<or> b \<le> a"
    and abs_nn: "\<bar>x\<bar> \<ge> 0"
begin

subclass (in linordered_field) nice_ordered_field
proof
  show "\<bar>a\<bar> = - a"
    if "a \<le> 0"
    for a :: 'a
    using that
    by simp 
  show "\<bar>a\<bar> = a"
    if "0 \<le> a"
    for a :: 'a
    using that
    by simp 
  show "0 < inverse a"
    if "0 < a"
    for a :: 'a
    using that
    by simp 
  show "b \<le> a"
    if "inverse a \<le> inverse b"
      and "0 < a"
    for a :: 'a
      and b
    using that
    using local.inverse_le_imp_le by blast 
  show "y \<le> z"
    if "\<And>x::'a. x < y \<Longrightarrow> x \<le> z"
    for y
      and z
    using that
    using local.dense_le by blast 
  show "a \<le> b \<or> b \<le> a"
    if "0 \<le> a"
      and "0 \<le> b"
    for a :: 'a
      and b
    using that
    by auto 
  show "0 \<le> \<bar>x\<bar>"
    for x :: 'a
    by simp    
qed

lemma comparable:
  assumes h1: "a \<le> c \<or> a \<ge> c"
    and h2: "b \<le> c \<or> b \<ge> c"
  shows "a \<le> b \<or> b \<le> a"
proof-
  have "a \<le> b"
    if t1: "\<not> b \<le> a" and t2: "a \<le> c" and t3: "b \<le> c"
  proof-
    have "0 \<le> c-a"
      by (simp add: t2)      
    moreover have "0 \<le> c-b"
      by (simp add: t3)      
    ultimately have "c-a \<le> c-b \<or> c-a \<ge> c-b" by (rule nn_comparable)
    hence "-a \<le> -b \<or> -a \<ge> -b"
      using local.add_le_imp_le_right local.uminus_add_conv_diff by presburger
    thus ?thesis
      by (simp add: t1)
  qed
  moreover have "a \<le> b"
    if t1: "\<not> b \<le> a" and t2: "c \<le> a" and t3: "b \<le> c"
  proof-
    have "b \<le> a"       
      using local.dual_order.trans t2 t3 by blast 
    thus ?thesis
      using t1 by auto
  qed
  moreover have "a \<le> b"
    if t1: "\<not> b \<le> a" and t2: "c \<le> a" and t3: "c \<le> b"
  proof-
    have "0 \<le> a-c"
      by (simp add: t2)        
    moreover have "0 \<le> b-c"
      by (simp add: t3)      
    ultimately have "a-c \<le> b-c \<or> a-c \<ge> b-c" by (rule nn_comparable)
    hence "a \<le> b \<or> a \<ge> b"
      by (simp add: local.le_diff_eq)
    thus ?thesis
      by (simp add: t1)
  qed
  ultimately show ?thesis using assms by auto
qed

lemma negative_imp_inverse_negative:
  "a < 0 \<Longrightarrow> inverse a < 0"
  by (insert positive_imp_inverse_positive [of "-a"],
      simp add: nonzero_inverse_minus_eq less_imp_not_eq)

lemma inverse_positive_imp_positive:
  assumes inv_gt_0: "0 < inverse a" and nz: "a \<noteq> 0"
  shows "0 < a"
proof -
  have "0 < inverse (inverse a)"
    using inv_gt_0 by (rule positive_imp_inverse_positive)
  thus "0 < a"
    using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_negative_imp_negative:
  assumes inv_less_0: "inverse a < 0" and nz: "a \<noteq> 0"
  shows "a < 0"
proof-
  have "inverse (inverse a) < 0"
    using inv_less_0 by (rule negative_imp_inverse_negative)
  thus "a < 0" using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma linordered_field_no_lb:
  "\<forall>x. \<exists>y. y < x"
proof
  fix x::'a
  have m1: "- (1::'a) < 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "(- 1) + x < x" by simp
  thus "\<exists>y. y < x" by blast
qed

lemma linordered_field_no_ub:
  "\<forall>x. \<exists>y. y > x"
proof
  fix x::'a
  have m1: " (1::'a) > 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "1 + x > x" by simp
  thus "\<exists>y. y > x" by blast
qed

lemma less_imp_inverse_less:
  assumes less: "a < b" and apos:  "0 < a"
  shows "inverse b < inverse a"
  using assms by (metis local.dual_order.strict_iff_order 
      local.inverse_inverse_eq local.inverse_le_imp_le local.positive_imp_inverse_positive)

lemma inverse_less_imp_less:
  "inverse a < inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b < a"
  using local.inverse_le_imp_le local.order.strict_iff_order by blast

text\<open>Both premises are essential. Consider -1 and 1.\<close>
lemma inverse_less_iff_less [simp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  by (blast intro: less_imp_inverse_less dest: inverse_less_imp_less)

lemma le_imp_inverse_le:
  "a \<le> b \<Longrightarrow> 0 < a \<Longrightarrow> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less)

lemma inverse_le_iff_le [simp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le dest: inverse_le_imp_le)


text\<open>These results refer to both operands being negative.  The opposite-sign
case is trivial, since inverse preserves signs.\<close>
lemma inverse_le_imp_le_neg:
  "inverse a \<le> inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b \<le> a"
  by (metis local.inverse_le_imp_le local.inverse_minus_eq local.neg_0_less_iff_less 
      local.neg_le_iff_le)

lemma inverse_less_imp_less_neg:
  "inverse a < inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b < a"
  using local.dual_order.strict_iff_order local.inverse_le_imp_le_neg by blast

lemma inverse_less_iff_less_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  by (metis local.antisym_conv2 local.inverse_less_imp_less_neg local.negative_imp_inverse_negative 
      local.nonzero_inverse_inverse_eq local.order.strict_implies_order)

lemma le_imp_inverse_le_neg:
  "a \<le> b \<Longrightarrow> b < 0 \<Longrightarrow> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less_neg)

lemma inverse_le_iff_le_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le_neg dest: inverse_le_imp_le_neg)

lemma one_less_inverse:
  "0 < a \<Longrightarrow> a < 1 \<Longrightarrow> 1 < inverse a"
  using less_imp_inverse_less [of a 1, unfolded inverse_1] .

lemma one_le_inverse:
  "0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> 1 \<le> inverse a"
  using le_imp_inverse_le [of a 1, unfolded inverse_1] .

lemma pos_le_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a \<le> b / c \<longleftrightarrow> a * c \<le> b"
  using assms by (metis local.divide_eq_imp local.divide_inverse_commute 
      local.dual_order.order_iff_strict local.dual_order.strict_iff_order 
      local.mult_right_mono local.mult_strict_left_mono local.nonzero_divide_eq_eq 
      local.order.strict_implies_order local.positive_imp_inverse_positive)

lemma pos_less_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a < b / c \<longleftrightarrow> a * c < b"
  using assms local.dual_order.strict_iff_order local.nonzero_divide_eq_eq local.pos_le_divide_eq 
  by auto

lemma neg_less_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a < b / c \<longleftrightarrow> b < a * c"
  by (metis assms local.minus_divide_divide local.mult_minus_right local.neg_0_less_iff_less 
      local.neg_less_iff_less local.pos_less_divide_eq)

lemma neg_le_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a \<le> b / c \<longleftrightarrow> b \<le> a * c"
  by (metis assms local.dual_order.order_iff_strict local.dual_order.strict_iff_order 
      local.neg_less_divide_eq local.nonzero_divide_eq_eq)

lemma pos_divide_le_eq [field_simps]:
  assumes "0 < c"
  shows "b / c \<le> a \<longleftrightarrow> b \<le> a * c"
  by (metis assms local.dual_order.strict_iff_order local.nonzero_eq_divide_eq 
      local.pos_le_divide_eq)

lemma pos_divide_less_eq [field_simps]:
  assumes "0 < c"
  shows "b / c < a \<longleftrightarrow> b < a * c"
  by (metis assms local.minus_divide_left local.mult_minus_left local.neg_less_iff_less 
      local.pos_less_divide_eq)

lemma neg_divide_le_eq [field_simps]:
  assumes "c < 0"
  shows "b / c \<le> a \<longleftrightarrow> a * c \<le> b"
  by (metis assms local.minus_divide_left local.mult_minus_left local.neg_le_divide_eq 
      local.neg_le_iff_le)

lemma neg_divide_less_eq [field_simps]:
  assumes "c < 0"
  shows "b / c < a \<longleftrightarrow> a * c < b"
  using assms local.dual_order.strict_iff_order local.neg_divide_le_eq by auto

text\<open>The following \<open>field_simps\<close> rules are necessary, as minus is always moved atop of
division but we want to get rid of division.\<close>

lemma pos_le_minus_divide_eq [field_simps]: "0 < c \<Longrightarrow> a \<le> - (b / c) \<longleftrightarrow> a * c \<le> - b"
  unfolding minus_divide_left by (rule pos_le_divide_eq)

lemma neg_le_minus_divide_eq [field_simps]: "c < 0 \<Longrightarrow> a \<le> - (b / c) \<longleftrightarrow> - b \<le> a * c"
  unfolding minus_divide_left by (rule neg_le_divide_eq)

lemma pos_less_minus_divide_eq [field_simps]: "0 < c \<Longrightarrow> a < - (b / c) \<longleftrightarrow> a * c < - b"
  unfolding minus_divide_left by (rule pos_less_divide_eq)

lemma neg_less_minus_divide_eq [field_simps]: "c < 0 \<Longrightarrow> a < - (b / c) \<longleftrightarrow> - b < a * c"
  unfolding minus_divide_left by (rule neg_less_divide_eq)

lemma pos_minus_divide_less_eq [field_simps]: "0 < c \<Longrightarrow> - (b / c) < a \<longleftrightarrow> - b < a * c"
  unfolding minus_divide_left by (rule pos_divide_less_eq)

lemma neg_minus_divide_less_eq [field_simps]: "c < 0 \<Longrightarrow> - (b / c) < a \<longleftrightarrow> a * c < - b"
  unfolding minus_divide_left by (rule neg_divide_less_eq)

lemma pos_minus_divide_le_eq [field_simps]: "0 < c \<Longrightarrow> - (b / c) \<le> a \<longleftrightarrow> - b \<le> a * c"
  unfolding minus_divide_left by (rule pos_divide_le_eq)

lemma neg_minus_divide_le_eq [field_simps]: "c < 0 \<Longrightarrow> - (b / c) \<le> a \<longleftrightarrow> a * c \<le> - b"
  unfolding minus_divide_left by (rule neg_divide_le_eq)

lemma frac_less_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y < w / z \<longleftrightarrow> (x * z - w * y) / (y * z) < 0"
  by (subst less_iff_diff_less_0) (simp add: diff_frac_eq )

lemma frac_le_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y \<le> w / z \<longleftrightarrow> (x * z - w * y) / (y * z) \<le> 0"
  by (subst le_iff_diff_le_0) (simp add: diff_frac_eq )


text\<open>Lemmas \<open>sign_simps\<close> is a first attempt to automate proofs
of positivity/negativity needed for \<open>field_simps\<close>. Have not added \<open>sign_simps\<close> to \<open>field_simps\<close> 
  because the former can lead to case explosions.\<close>

lemma divide_pos_pos[simp]:
  "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> 0 < x / y"
  by(simp add:field_simps)

lemma divide_nonneg_pos:
  "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> 0 \<le> x / y"
  by(simp add:field_simps)

lemma divide_neg_pos:
  "x < 0 \<Longrightarrow> 0 < y \<Longrightarrow> x / y < 0"
  by(simp add:field_simps)

lemma divide_nonpos_pos:
  "x \<le> 0 \<Longrightarrow> 0 < y \<Longrightarrow> x / y \<le> 0"
  by(simp add:field_simps)

lemma divide_pos_neg:
  "0 < x \<Longrightarrow> y < 0 \<Longrightarrow> x / y < 0"
  by(simp add:field_simps)

lemma divide_nonneg_neg:
  "0 \<le> x \<Longrightarrow> y < 0 \<Longrightarrow> x / y \<le> 0"
  by(simp add:field_simps)

lemma divide_neg_neg:
  "x < 0 \<Longrightarrow> y < 0 \<Longrightarrow> 0 < x / y"
  by(simp add:field_simps)

lemma divide_nonpos_neg:
  "x \<le> 0 \<Longrightarrow> y < 0 \<Longrightarrow> 0 \<le> x / y"
  by(simp add:field_simps)

lemma divide_strict_right_mono:
  "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a / c < b / c"
  by (simp add: less_imp_not_eq2 divide_inverse mult_strict_right_mono
      positive_imp_inverse_positive)


lemma divide_strict_right_mono_neg:
  "b < a \<Longrightarrow> c < 0 \<Longrightarrow> a / c < b / c"
  by (simp add: local.neg_less_divide_eq)

text\<open>The last premise ensures that \<^term>\<open>a\<close> and \<^term>\<open>b\<close>
      have the same sign\<close>
lemma divide_strict_left_mono:
  "b < a \<Longrightarrow> 0 < c \<Longrightarrow> 0 < a*b \<Longrightarrow> c / a < c / b"
  by (metis local.divide_neg_pos local.dual_order.strict_iff_order local.frac_less_eq local.less_iff_diff_less_0 local.mult_not_zero local.mult_strict_left_mono)

lemma divide_left_mono:
  "b \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> 0 < a*b \<Longrightarrow> c / a \<le> c / b"
  using local.divide_cancel_left local.divide_strict_left_mono local.dual_order.order_iff_strict by auto

lemma divide_strict_left_mono_neg:
  "a < b \<Longrightarrow> c < 0 \<Longrightarrow> 0 < a*b \<Longrightarrow> c / a < c / b"
  by (metis local.divide_strict_left_mono local.minus_divide_left local.neg_0_less_iff_less local.neg_less_iff_less mult_commute)

lemma mult_imp_div_pos_le: "0 < y \<Longrightarrow> x \<le> z * y \<Longrightarrow> x / y \<le> z"
  by (subst pos_divide_le_eq, assumption+)

lemma mult_imp_le_div_pos: "0 < y \<Longrightarrow> z * y \<le> x \<Longrightarrow> z \<le> x / y"
  by(simp add:field_simps)

lemma mult_imp_div_pos_less: "0 < y \<Longrightarrow> x < z * y \<Longrightarrow> x / y < z"
  by(simp add:field_simps)

lemma mult_imp_less_div_pos: "0 < y \<Longrightarrow> z * y < x \<Longrightarrow> z < x / y"
  by(simp add:field_simps)

lemma frac_le: "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> 0 < w \<Longrightarrow> w \<le> z  \<Longrightarrow> x / z \<le> y / w"
  using local.mult_imp_div_pos_le local.mult_imp_le_div_pos local.mult_mono by auto

lemma frac_less: "0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> 0 < w \<Longrightarrow> w \<le> z \<Longrightarrow> x / z < y / w"
proof-
  assume a1: "w \<le> z"
  assume a2: "0 < w"
  assume a3: "0 \<le> x"
  assume a4: "x < y"
  have f5: "a = 0 \<or> (b = c / a) = (b * a = c)"
    for a b c::'a
    by (meson local.nonzero_eq_divide_eq)
  have f6: "0 < z"
    using a2 a1 by (meson local.order.ordering_axioms ordering.strict_trans2)
  have "z \<noteq> 0"
    using a2 a1 by (meson local.leD)
  moreover have "x / z \<noteq> y / w"
    using a1 a2 a3 a4 local.frac_eq_eq local.mult_less_le_imp_less by fastforce
  ultimately have "x / z \<noteq> y / w"
    using f5 by (metis (no_types))
  thus ?thesis
    using a4 a3 a2 a1 by (meson local.frac_le local.order.not_eq_order_implies_strict 
        local.order.strict_implies_order)
qed


lemma frac_less2: "0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> 0 < w \<Longrightarrow> w < z  \<Longrightarrow> x / z < y / w"
  by (metis local.antisym_conv2 local.divide_cancel_left local.dual_order.strict_implies_order 
      local.frac_le local.frac_less)

lemma less_half_sum: "a < b \<Longrightarrow> a < (a+b) / (1+1)"
  by (metis local.add_pos_pos local.add_strict_left_mono local.mult_imp_less_div_pos local.semiring_normalization_rules(4) local.zero_less_one mult_commute)

lemma gt_half_sum: "a < b \<Longrightarrow> (a+b)/(1+1) < b"
  by (metis local.add_pos_pos local.add_strict_left_mono local.mult_imp_div_pos_less local.semiring_normalization_rules(24) local.semiring_normalization_rules(4) local.zero_less_one mult_commute)

subclass unbounded_dense_order
proof
  fix x y :: 'a
  have less_add_one: "a < a + 1" for a::'a by auto
  from less_add_one show "\<exists>y. x < y"
    by blast 

  from less_add_one have "x + (- 1) < (x + 1) + (- 1)"
    by (rule add_strict_right_mono)
  hence "x - 1 < x + 1 - 1" by simp
  hence "x - 1 < x" by (simp add: algebra_simps)
  thus "\<exists>y. y < x" ..
  show "x < y \<Longrightarrow> \<exists>z>x. z < y" by (blast intro!: less_half_sum gt_half_sum)
qed


lemma dense_le_bounded:
  fixes x y z :: 'a
  assumes "x < y"
    and *: "\<And>w. \<lbrakk> x < w ; w < y \<rbrakk> \<Longrightarrow> w \<le> z"
  shows "y \<le> z"
proof (rule dense_le)
  fix w assume "w < y"
  from dense[OF \<open>x < y\<close>] obtain u where "x < u" "u < y" by safe
  have "u \<le> w \<or> w \<le> u"
    using \<open>u < y\<close> \<open>w < y\<close> comparable local.order.strict_implies_order by blast
  thus "w \<le> z"
    using "*" \<open>u < y\<close> \<open>w < y\<close> \<open>x < u\<close> local.dual_order.trans local.order.strict_trans2 by blast
qed

subclass field_abs_sgn ..


lemma nonzero_abs_inverse:
  "a \<noteq> 0 \<Longrightarrow> \<bar>inverse a\<bar> = inverse \<bar>a\<bar>"
  by (rule abs_inverse)

lemma nonzero_abs_divide:
  "b \<noteq> 0 \<Longrightarrow> \<bar>a / b\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
  by (rule abs_divide)

lemma field_le_epsilon:
  assumes e: "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof (rule dense_le)
  fix t assume "t < x"
  hence "0 < x - t" by (simp add: less_diff_eq)
  from e [OF this] have "x + 0 \<le> x + (y - t)" by (simp add: algebra_simps)
  hence "0 \<le> y - t" by (simp only: add_le_cancel_left)
  thus "t \<le> y" by (simp add: algebra_simps)
qed

lemma inverse_positive_iff_positive [simp]:
  "(0 < inverse a) = (0 < a)"
  using local.positive_imp_inverse_positive by fastforce

lemma inverse_negative_iff_negative [simp]:
  "(inverse a < 0) = (a < 0)"
  using local.negative_imp_inverse_negative by fastforce

lemma inverse_nonnegative_iff_nonnegative [simp]:
  "0 \<le> inverse a \<longleftrightarrow> 0 \<le> a"
  by (simp add: local.dual_order.order_iff_strict)

lemma inverse_nonpositive_iff_nonpositive [simp]:
  "inverse a \<le> 0 \<longleftrightarrow> a \<le> 0"
  using local.inverse_nonnegative_iff_nonnegative local.neg_0_le_iff_le by fastforce

lemma one_less_inverse_iff: "1 < inverse x \<longleftrightarrow> 0 < x \<and> x < 1"
  using less_trans[of 1 x 0 for x]
  by (metis local.dual_order.strict_trans local.inverse_1 local.inverse_less_imp_less local.inverse_positive_iff_positive local.one_less_inverse local.zero_less_one)

lemma one_le_inverse_iff: "1 \<le> inverse x \<longleftrightarrow> 0 < x \<and> x \<le> 1"
  by (metis local.dual_order.strict_trans1 local.inverse_1 local.inverse_le_imp_le local.inverse_positive_iff_positive local.one_le_inverse local.zero_less_one)

lemma inverse_less_1_iff: "inverse x < 1 \<longleftrightarrow> x \<le> 0 \<or> 1 < x"
proof (rule)
  assume invx1: "inverse x < 1"
  have "inverse x \<le> 0 \<or> inverse x \<ge> 0"
    using comparable invx1 local.order.strict_implies_order local.zero_less_one by blast
  then consider (leq0) "inverse x \<le> 0" | (pos) "inverse x > 0" | (zero) "inverse x = 0"
    using local.antisym_conv1 by blast
  thus "x \<le> 0 \<or> 1 < x"
    by (metis invx1 local.eq_iff local.inverse_1 local.inverse_less_imp_less 
        local.inverse_nonpositive_iff_nonpositive local.inverse_positive_imp_positive)
next
  assume "x \<le> 0 \<or> 1 < x"
  then consider (neg) "x \<le> 0" | (g1) "1 < x" by auto
  thus "inverse x < 1"
    by (metis local.dual_order.not_eq_order_implies_strict local.dual_order.strict_trans
        local.inverse_1 local.inverse_negative_iff_negative local.inverse_zero 
        local.less_imp_inverse_less local.zero_less_one)  
qed

lemma inverse_le_1_iff: "inverse x \<le> 1 \<longleftrightarrow> x \<le> 0 \<or> 1 \<le> x"
  by (metis local.dual_order.order_iff_strict local.inverse_1 local.inverse_le_iff_le 
      local.inverse_less_1_iff local.one_le_inverse_iff)

text\<open>Simplify expressions such as \<open>0 < 1/x\<close> to \<open>0 < x\<close>\<close>

lemma zero_le_divide_1_iff [simp]:
  "0 \<le> 1 / a \<longleftrightarrow> 0 \<le> a"
  using local.dual_order.order_iff_strict local.inverse_eq_divide 
    local.inverse_positive_iff_positive by auto

lemma zero_less_divide_1_iff [simp]:
  "0 < 1 / a \<longleftrightarrow> 0 < a"
  by (simp add: local.dual_order.strict_iff_order)

lemma divide_le_0_1_iff [simp]:
  "1 / a \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (smt local.abs_0 local.abs_1 local.abs_divide local.abs_neg local.abs_nn 
      local.divide_cancel_left local.le_minus_iff local.minus_divide_right local.zero_neq_one)

lemma divide_less_0_1_iff [simp]:
  "1 / a < 0 \<longleftrightarrow> a < 0"
  using local.dual_order.strict_iff_order by auto

lemma divide_right_mono:
  "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a/c \<le> b/c"
  using local.divide_cancel_right local.divide_strict_right_mono local.dual_order.order_iff_strict by blast

lemma divide_right_mono_neg: "a \<le> b
    \<Longrightarrow> c \<le> 0 \<Longrightarrow> b / c \<le> a / c"
  by (metis local.divide_cancel_right local.divide_strict_right_mono_neg local.dual_order.strict_implies_order local.eq_refl local.le_imp_less_or_eq)

lemma divide_left_mono_neg: "a \<le> b
    \<Longrightarrow> c \<le> 0 \<Longrightarrow> 0 < a * b \<Longrightarrow> c / a \<le> c / b"  
  by (metis local.divide_left_mono local.minus_divide_left local.neg_0_le_iff_le local.neg_le_iff_le mult_commute)

lemma divide_nonneg_nonneg [simp]:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x / y"
  using local.divide_eq_0_iff local.divide_nonneg_pos local.dual_order.order_iff_strict by blast

lemma divide_nonpos_nonpos:
  "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> 0 \<le> x / y"
  using local.divide_nonpos_neg local.dual_order.order_iff_strict by auto

lemma divide_nonneg_nonpos:
  "0 \<le> x \<Longrightarrow> y \<le> 0 \<Longrightarrow> x / y \<le> 0"
  by (metis local.divide_eq_0_iff local.divide_nonneg_neg local.dual_order.order_iff_strict)

lemma divide_nonpos_nonneg:
  "x \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> x / y \<le> 0"
  using local.divide_nonpos_pos local.dual_order.order_iff_strict by auto

text \<open>Conditional Simplification Rules: No Case Splits\<close>

lemma le_divide_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (1 \<le> b/a) = (a \<le> b)"
  by (simp add: local.pos_le_divide_eq)

lemma le_divide_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (1 \<le> b/a) = (b \<le> a)"
  by (metis local.le_divide_eq_1_pos local.minus_divide_divide local.neg_0_less_iff_less local.neg_le_iff_le)

lemma divide_le_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (b/a \<le> 1) = (b \<le> a)"
  using local.pos_divide_le_eq by auto

lemma divide_le_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (b/a \<le> 1) = (a \<le> b)"
  by (metis local.divide_le_eq_1_pos local.minus_divide_divide local.neg_0_less_iff_less 
      local.neg_le_iff_le)

lemma less_divide_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (1 < b/a) = (a < b)"
  by (simp add: local.dual_order.strict_iff_order)

lemma less_divide_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (1 < b/a) = (b < a)"
  using local.dual_order.strict_iff_order by auto

lemma divide_less_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (b/a < 1) = (b < a)"
  using local.divide_le_eq_1_pos local.dual_order.strict_iff_order by auto

lemma divide_less_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> b/a < 1 \<longleftrightarrow> a < b"
  using local.dual_order.strict_iff_order by auto

lemma abs_div_pos: "0 < y \<Longrightarrow>
    \<bar>x\<bar> / y = \<bar>x / y\<bar>"
  by (simp add: local.abs_pos)

lemma zero_le_divide_abs_iff [simp]: "(0 \<le> a / \<bar>b\<bar>) = (0 \<le> a | b = 0)"
proof 
  assume assm: "0 \<le> a / \<bar>b\<bar>"
  have absb: "abs b \<ge> 0" by (fact abs_nn)
  thus "0 \<le> a \<or> b = 0"
    using absb assm local.abs_eq_0_iff local.mult_nonneg_nonneg by fastforce
next
  assume "0 \<le> a \<or> b = 0"
  then consider (a) "0 \<le> a" | (b) "b = 0" by atomize_elim auto
  thus "0 \<le> a / \<bar>b\<bar>"
    by (metis local.abs_eq_0_iff local.abs_nn local.divide_eq_0_iff local.divide_nonneg_nonneg)
qed


lemma divide_le_0_abs_iff [simp]: "(a / \<bar>b\<bar> \<le> 0) = (a \<le> 0 | b = 0)"
  by (metis local.minus_divide_left local.neg_0_le_iff_le local.zero_le_divide_abs_iff)

text\<open>For creating values between \<^term>\<open>u\<close> and \<^term>\<open>v\<close>.\<close>
lemma scaling_mono:
  assumes "u \<le> v" and "0 \<le> r" and "r \<le> s"
  shows "u + r * (v - u) / s \<le> v"
proof -
  have "r/s \<le> 1" using assms
    by (metis local.divide_le_eq_1_pos local.division_ring_divide_zero 
        local.dual_order.order_iff_strict local.dual_order.trans local.zero_less_one)
  hence "(r/s) * (v - u) \<le> 1 * (v - u)"
    using assms(1) local.diff_ge_0_iff_ge local.mult_right_mono by blast
  thus ?thesis
    by (simp add: field_simps)
qed

end (* class nice_ordered_field *)


code_identifier
  code_module Ordered_Fields \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

subsection\<open>Ordered Complex\<close>

declare Conjugate.less_eq_complex_def[simp del]
declare Conjugate.less_complex_def[simp del]

subsection \<open>Ordering on complex numbers\<close>

instantiation complex :: nice_ordered_field begin
instance
proof intro_classes
  note defs = less_eq_complex_def less_complex_def abs_complex_def
  fix x y z a b c :: complex
  show "a \<le> 0 \<Longrightarrow> \<bar>a\<bar> = - a" unfolding defs
    by (simp add: cmod_eq_Re complex_is_Real_iff)
  show "0 \<le> a \<Longrightarrow> \<bar>a\<bar> = a"
    unfolding defs
    by (metis abs_of_nonneg cmod_eq_Re comp_apply complex.exhaust_sel complex_of_real_def zero_complex.simps(1) zero_complex.simps(2))
  show "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b" unfolding defs by auto
  show "0 < (1::complex)" unfolding defs by simp
  show "0 < a \<Longrightarrow> 0 < inverse a" unfolding defs by auto
  define ra ia rb ib rc ic where "ra = Re a" "ia = Im a" "rb = Re b" "ib = Im b" "rc = Re c" "ic = Im c"
  note ri = this[symmetric]
  hence "a = Complex ra ia" "b = Complex rb ib" "c = Complex rc ic" by auto
  note ri = this ri
  have "rb \<le> ra"
    if "1 / ra \<le> (if rb = 0 then 0 else 1 / rb)" 
      and "ia = 0" and "0 < ra" and "ib = 0"
  proof(cases "rb = 0")
    case True
    thus ?thesis
      using that(3) by auto 
  next
    case False
    thus ?thesis
      by (smt nice_ordered_field_class.frac_less2 that(1) that(3)) 
  qed
  thus "inverse a \<le> inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> a" unfolding defs ri
    by (auto simp: power2_eq_square) 
  show "(\<And>a. a < b \<Longrightarrow> a \<le> c) \<Longrightarrow> b \<le> c" unfolding defs ri
    by (metis complex.sel(1) complex.sel(2) dense less_le_not_le 
        nice_ordered_field_class.linordered_field_no_lb not_le_imp_less)    
  show "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a \<le> b \<or> b \<le> a" unfolding defs by auto
  show "0 \<le> \<bar>x\<bar>" unfolding defs by auto
qed
end

lemma less_eq_complexI: "Re x \<le> Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x\<le>y" unfolding less_eq_complex_def 
  by simp
lemma less_complexI: "Re x < Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x<y" unfolding less_complex_def 
  by simp

lemma complex_of_real_mono:
  "x \<le> y \<Longrightarrow> complex_of_real x \<le> complex_of_real y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_mono_iff[simp]:
  "complex_of_real x \<le> complex_of_real y \<longleftrightarrow> x \<le> y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_strict_mono_iff[simp]:
  "complex_of_real x < complex_of_real y \<longleftrightarrow> x < y"
  unfolding less_complex_def by auto

lemma complex_of_real_nn_iff[simp]:
  "0 \<le> complex_of_real y \<longleftrightarrow> 0 \<le> y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_pos_iff[simp]:
  "0 < complex_of_real y \<longleftrightarrow> 0 < y"
  unfolding less_complex_def by auto

lemma Re_mono: "x \<le> y \<Longrightarrow> Re x \<le> Re y"
  unfolding less_eq_complex_def by simp

lemma comp_Im_same: "x \<le> y \<Longrightarrow> Im x = Im y"
  unfolding less_eq_complex_def by simp

lemma Re_strict_mono: "x < y \<Longrightarrow> Re x < Re y"
  unfolding less_complex_def by simp

lemma complex_of_real_cmod: assumes "x \<ge> 0" shows "complex_of_real (cmod x) = x"
  by (metis Reals_cases abs_of_nonneg assms comp_Im_same complex_is_Real_iff complex_of_real_nn_iff norm_of_real zero_complex.simps(2))


end
