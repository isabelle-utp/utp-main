\<^marker>\<open>creator "Albert Rizaldi" "Fabian Immler\<close>

section \<open>Safe Distance\<close>

theory Safe_Distance
imports
  "HOL-Analysis.Multivariate_Analysis"
  "HOL-Decision_Procs.Approximation"
  Sturm_Sequences.Sturm
begin

text \<open>
This theory is about formalising the safe distance rule. The safe distance rule is obtained
from Vienna Convention which basically states the following thing.

  ``The car at all times must maintain a safe distance towards the vehicle in front of it,
    such that whenever the vehicle in front and the ego vehicle apply maximum deceleration,
    there will not be a collision.''

To formalise this safe distance rule we have to define first what is a safe distance.
To define this safe distance, we have to model the physics of the movement of the vehicle.
The following model is sufficient.

  \<open>s = s\<^sub>0 + v\<^sub>0 * t + 1 / 2 * a\<^sub>0 * t\<^sup>2\<close>

Assumptions in this model are :
  \<^item> Both vehicles are assumed to be point mass. The exact location of the ego vehicle
    is the front-most occupancy of the ego vehicle. Similarly for the other vehicle,
    its exact location is the rearmost occupancy of the other vehicle.

  \<^item> Both cars can never drive backward.
\<close>

lemmas [simp del] = div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4

subsection \<open>Quadratic Equations\<close>

lemma discriminant: "a * x\<^sup>2 + b * x + c = (0::real) \<Longrightarrow> 0 \<le> b\<^sup>2 - 4 * a * c" 
  by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [2*a*x + b]^2))))")

lemma quadratic_eq_factoring:
  assumes D : "D = b\<^sup>2 - 4 * a * c"
  assumes nn: "0 \<le> D"
  assumes x1: "x\<^sub>1 = (-b + sqrt D) / (2 * a)"
  assumes x2: "x\<^sub>2 = (-b - sqrt D) / (2 * a)"
  assumes a : "a \<noteq> 0"
  shows "a * x\<^sup>2 + b * x + c = a * (x - x\<^sub>1) * (x - x\<^sub>2)"
  using nn
  by (simp add: D x1 x2)
     (simp add: assms power2_eq_square power3_eq_cube field_split_simps)

lemma quadratic_eq_zeroes_iff:
  assumes D : "D = b\<^sup>2 - 4 * a * c"
  assumes x1: "x\<^sub>1 = (-b + sqrt D) / (2 * a)"
  assumes x2: "x\<^sub>2 = (-b - sqrt D) / (2 * a)"
  assumes a : "a \<noteq> 0"
  shows "a * x\<^sup>2 + b * x + c = 0 \<longleftrightarrow> (D \<ge> 0 \<and> (x = x\<^sub>1 \<or> x = x\<^sub>2))" (is "?z \<longleftrightarrow> _")
  using quadratic_eq_factoring[OF D _ x1 x2 a, of x] discriminant[of a x b c] a
  by (auto simp: D)

subsection \<open>Convexity Condition\<close>

lemma p_convex:
  fixes a b c x y z :: real
  assumes p_def: "p = (\<lambda>x. a * x\<^sup>2 + b * x + c)"
  assumes less : "x < y" "y < z" 
      and ge   : "p x > p y" "p y \<le> p z"
  shows "a > 0"
  using less ge unfolding p_def
  by (sos "((((A<0 * (A<1 * A<2)) * R<1) + (((A<2 * R<1) * (R<1/4 * [y + ~1*z]^2)) +
    (((A<=1 * R<1) * (R<1 * [x + ~1*y]^2)) + (((A<=1 * (A<0 * (A<1 * R<1))) * (R<1/4 * [1]^2)) +
    (((A<=0 * R<1) * (R<1/4 * [~1*y^2 + x*y + ~1*x*z + y*z]^2)) +
    ((A<=0 * (A<0 * (A<1 * R<1))) * (R<1 * [x + ~1/2*y + ~1/2*z]^2))))))))")
  
definition root_in :: "real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> bool" where
  "root_in m M f = (\<exists>x\<in>{m .. M}. f x = 0)"

definition quadroot_in :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "quadroot_in m M a b c = root_in m M (\<lambda>x. a * x^2 + b * x + c)"

lemma card_iff_exists: "0 < card X \<longleftrightarrow> finite X \<and> (\<exists>x. x \<in> X)"
  by (auto simp: card_gt_0_iff)
  
lemma quadroot_in_sturm[code]:
  "quadroot_in m M a b c \<longleftrightarrow> (a = 0 \<and> b = 0 \<and> c = 0 \<and> m \<le> M) \<or>
    (m \<le> M \<and> poly [:c, b, a:] m = 0) \<or>
    count_roots_between [:c, b, a:] m M > 0"
  apply (cases "a = 0 \<and> b = 0 \<and> c = 0 \<and> m \<le> M")
   apply (force simp: quadroot_in_def root_in_def)
  apply (cases "m \<le> M \<and> poly [:c, b, a:] m = 0")
   apply (force simp: quadroot_in_def root_in_def algebra_simps power2_eq_square count_roots_between_correct card_iff_exists)
proof -
  assume H: "\<not> (a = 0 \<and> b = 0 \<and> c = 0 \<and> m \<le> M)" "\<not> (m \<le> M \<and> poly [:c, b, a:] m = 0)"
  hence "poly [:c, b, a:] m \<noteq> 0 \<or> m > M"
    by auto
  then have "quadroot_in m M a b c \<longleftrightarrow> 0 < count_roots_between [:c, b, a:] m M"
  proof (rule disjE)
    assume pnz: "poly [:c, b, a:] m \<noteq> 0"
    then have nz: "[:c, b, a:] \<noteq> 0" by auto
    show ?thesis
      unfolding count_roots_between_correct card_iff_exists
      apply safe
        apply (rule finite_subset[where B="{x. poly [:c, b, a:] x = 0}"])
         apply force
        apply (rule poly_roots_finite)
        apply (rule nz)
      using pnz
       apply (auto simp add: count_roots_between_correct quadroot_in_def root_in_def card_iff_exists
          algebra_simps power2_eq_square)
      apply (case_tac "x = m")
       apply (force simp: algebra_simps)
      apply force
      done
  qed (auto simp: quadroot_in_def count_roots_between_correct root_in_def card_eq_0_iff)
  then show "quadroot_in m M a b c = (a = 0 \<and> b = 0 \<and> c = 0 \<and> m \<le> M \<or>
     m \<le> M \<and> poly [:c, b, a:] m = 0 \<or>
     0 < count_roots_between [:c, b, a:] m M)"
    using H by metis
qed

lemma check_quadroot_linear:
  fixes a b c :: real
  assumes "a = 0"
  shows "\<not> quadroot_in m M a b c \<longleftrightarrow>
    ((b = 0 \<and> c = 0 \<and> M < m) \<or> (b = 0 \<and> c \<noteq> 0) \<or>
     (b \<noteq> 0 \<and> (let x = - c / b in m > x \<or> x > M)))"
proof -
  have "quadroot_in m M a b c \<longleftrightarrow> (b = 0 \<longrightarrow> quadroot_in m M a b c) \<and> (b \<noteq> 0 \<longrightarrow> quadroot_in m M a b c)"
    by auto
  also have "(b = 0 \<longrightarrow> quadroot_in m M a b c) \<longleftrightarrow>
    ((b = 0 \<longrightarrow> c = 0 \<longrightarrow> m \<le> M) \<and> (b \<noteq> 0 \<or> c = 0))"
    by (auto simp: quadroot_in_def Let_def root_in_def assms field_split_simps
      intro!: bexI[where x="-c / b"])
  also have "(b \<noteq> 0 \<longrightarrow> quadroot_in m M a b c) \<longleftrightarrow> (b = 0 \<or> (let x = -c / b in m \<le> x \<and> x \<le> M))"
    apply (auto simp: quadroot_in_def Let_def root_in_def assms field_split_simps
        intro!: bexI[where x="-c / b"])
    by (metis mult.commute mult_le_cancel_left_neg add_eq_0_iff mult_le_cancel_iff2)+
  finally show ?thesis
    by (simp add: Let_def not_less not_le)
qed 

lemma check_quadroot_nonlinear:
  assumes "a \<noteq> 0"
  shows "quadroot_in m M a b c =
    (let D = b^2 - 4 * a * c in D \<ge> 0 \<and>
      ((let x = (-b + sqrt D)/(2*a) in m \<le> x \<and> x \<le> M) \<or>
      (let x = (-b - sqrt D)/(2*a) in m \<le> x \<and> x \<le> M)))"
  by (auto simp: quadroot_in_def Let_def root_in_def quadratic_eq_zeroes_iff[OF refl refl refl assms])

lemma ncheck_quadroot:
  shows "\<not>quadroot_in m M a b c \<longleftrightarrow>
    (a = 0 \<longrightarrow>\<not>quadroot_in m M a b c) \<and>
    (a = 0 \<or> \<not>quadroot_in m M a b c)"
  by auto

subsection \<open>Movement\<close>

locale movement = 
  fixes a v s0 :: real
begin

text \<open>
  Function to compute the distance using the equation

    \<open>s(t) = s\<^sub>0 + v\<^sub>0 * t + 1 / 2 * a\<^sub>0 * t\<^sup>2\<close>
  
  Input parameters: 
   \<^item> \<open>s\<^sub>0\<close>: initial distance
   \<^item> \<open>v\<^sub>0\<close>: initial velocity (positive means forward direction and the converse is true)
   \<^item> \<open>a\<close>: acceleration (positive for increasing and negative for decreasing)
   \<^item> \<open>t\<close>: time 

  For the time \<open>t < 0\<close>, we assume the output of the function is \<open>s\<^sub>0\<close>. Otherwise, the output
  is calculated according to the equation above.
\<close>

subsubsection \<open>Continuous Dynamics\<close>

definition p :: "real \<Rightarrow> real" where
  "p t = s0 + v * t + 1/2 * a * t\<^sup>2"

lemma p_all_zeroes:
  assumes D: "D = v\<^sup>2 - 2 * a * s0"
  shows "p t = 0 \<longleftrightarrow> ((a \<noteq> 0 \<and> 0 \<le> D \<and> ((t = (- v + sqrt D) / a) \<or> t = (- v - sqrt D) / a)) \<or>
    (a = 0 \<and> v = 0 \<and> s0 = 0) \<or> (a = 0 \<and> v \<noteq> 0 \<and> t = (- s0 / v)))"
  using quadratic_eq_zeroes_iff[OF refl refl refl, of "a / 2" t v s0]
  by (auto simp: movement.p_def D power2_eq_square field_split_simps)

lemma p_zero[simp]: "p 0 = s0"
  by (simp add: p_def)

lemma p_continuous[continuous_intros]: "continuous_on T p"
  unfolding p_def by (auto intro!: continuous_intros)

lemma isCont_p[continuous_intros]: "isCont p x"
  using p_continuous[of UNIV]
  by (auto simp: continuous_on_eq_continuous_at)

definition p' :: "real \<Rightarrow> real" where
  "p' t = v + a * t"

lemma p'_zero: "p' 0 = v"
  by (simp add: p'_def)

lemma p_has_vector_derivative[derivative_intros]: "(p has_vector_derivative p' t) (at t within s)"
  by (auto simp: p_def[abs_def] p'_def has_vector_derivative_def algebra_simps
    intro!: derivative_eq_intros)

lemma p_has_real_derivative[derivative_intros]: "(p has_real_derivative p' t) (at t within s)"
  using p_has_vector_derivative
  by (simp add: has_field_derivative_iff_has_vector_derivative)

definition p'' :: "real \<Rightarrow> real" where 
  "p'' t = a"

lemma p'_has_vector_derivative[derivative_intros]: "(p' has_vector_derivative p'' t) (at t within s)"
  by (auto simp: p'_def[abs_def] p''_def has_vector_derivative_def algebra_simps
    intro!: derivative_eq_intros)

lemma p'_has_real_derivative[derivative_intros]: "(p' has_real_derivative p'' t) (at t within s)"
  using p'_has_vector_derivative
  by (simp add: has_field_derivative_iff_has_vector_derivative)

definition t_stop :: real where 
  "t_stop = - v / a"

lemma p'_stop_zero: "p' t_stop = (if a = 0 then v else 0)" by (auto simp: p'_def t_stop_def)

lemma p'_pos_iff: "p' x > 0 \<longleftrightarrow> (if a > 0 then x > -v / a else if a < 0 then x < -v / a else v > 0)"
  by (auto simp: p'_def field_split_simps)

lemma le_t_stop_iff: "a \<noteq> 0 \<Longrightarrow> x \<le> t_stop \<longleftrightarrow> (if a < 0 then p' x \<ge> 0 else p' x \<le> 0)"
  by (auto simp: p'_def field_split_simps t_stop_def)

lemma p'_continuous[continuous_intros]: "continuous_on T p'"
  unfolding p'_def by (auto intro: continuous_intros)

lemma isCont_p'[continuous_intros]: "isCont p' x"
  using p'_continuous[of UNIV] by (auto simp: continuous_on_eq_continuous_at)

definition p_max :: real where 
  "p_max = p t_stop"

lemmas p_t_stop = p_max_def[symmetric]

lemma p_max_eq: "p_max = s0 - v\<^sup>2 / a / 2"
  by (auto simp: p_max_def p_def t_stop_def field_split_simps power2_eq_square)

subsubsection \<open>Hybrid Dynamics\<close>

definition s :: "real \<Rightarrow> real" where
  "s t = (     if t \<le> 0      then s0
          else if t \<le> t_stop then p t
          else                p_max)"

definition q :: "real \<Rightarrow> real" where
  "q t = s0 + v * t"

definition q' :: "real \<Rightarrow> real" where
  "q' t = v"

lemma init_q: "q 0 = s0" unfolding q_def by auto

lemma q_continuous[continuous_intros]: "continuous_on T q"
  unfolding q_def by (auto intro: continuous_intros)

lemma isCont_q[continuous_intros]: "isCont q x"
  using q_continuous[of UNIV]
  by (auto simp:continuous_on_eq_continuous_at)

lemma q_has_vector_derivative[derivative_intros]: "(q has_vector_derivative q' t) (at t within u)"
  by (auto simp: q_def[abs_def] q'_def has_vector_derivative_def algebra_simps
          intro!: derivative_eq_intros)

lemma q_has_real_derivative[derivative_intros]: "(q has_real_derivative q' t) (at t within u)"
  using q_has_vector_derivative
  by (simp add:has_field_derivative_iff_has_vector_derivative)

lemma s_cond_def:
  "t \<le> 0 \<Longrightarrow> s t = s0"
  "0 \<le> t \<Longrightarrow> t \<le> t_stop \<Longrightarrow> s t = p t"
  by (simp_all add: s_def)
  
end

locale braking_movement = movement +
  assumes decel: "a < 0"
  assumes nonneg_vel: "v \<ge> 0"
begin

lemma t_stop_nonneg: "0 \<le> t_stop"
  using decel nonneg_vel
  by (auto simp: t_stop_def divide_simps)

lemma t_stop_pos:
  assumes "v \<noteq> 0"
  shows "0 < t_stop"
  using decel nonneg_vel assms
  by (auto simp: t_stop_def divide_simps)

lemma t_stop_zero:
  assumes "t_stop = 0"
  shows "v = 0"
  using assms decel
  by (auto simp: t_stop_def)

lemma t_stop_zero_not_moving: "t_stop = 0 \<Longrightarrow> q t = s0" 
  unfolding q_def using t_stop_zero by auto

abbreviation "s_stop \<equiv> s t_stop"

lemma s_t_stop: "s_stop = p_max"
  using t_stop_nonneg
  by (auto simp: s_def t_stop_def p_max_def p_def)

lemma s0_le_s_stop: "s0 \<le> s_stop" 
proof (rule subst[where t="s_stop" and s="p_max"])
  show "p_max = s_stop" by (rule sym[OF s_t_stop])
next
  show "s0 \<le> p_max" 
  proof (rule subst[where t="p_max" and s="s0 - v\<^sup>2 / a / 2"]) 
    show " s0 - v\<^sup>2 / a / 2 = p_max" using p_max_eq by auto
  next
    have "0 \<le> - v\<^sup>2 / a / 2" using decel zero_le_square[of v]
    proof -
      have f1: "a \<le> 0"
        using \<open>a < 0\<close> by linarith
      have "(- 1 * v\<^sup>2 \<le> 0) = (0 \<le> v\<^sup>2)"
        by auto
      then have "0 \<le> - 1 * v\<^sup>2 / a"
        using f1 by (meson zero_le_divide_iff zero_le_power2)
      then show ?thesis
        by force
    qed
    thus "s0 \<le> s0 - v\<^sup>2 / a / 2" by auto
  qed
qed

lemma p_mono: "x \<le> y \<Longrightarrow> y \<le> t_stop \<Longrightarrow> p x \<le> p y"
  using decel
proof -
  assume "x \<le> y" and "y \<le> t_stop" and "a < 0"
  hence "x + y \<le> - 2 * v / a"
    unfolding t_stop_def by auto
  hence "-1 / 2 * a * (x + y) \<le> v" (is "?lhs0 \<le> ?rhs0")
    using \<open>a < 0\<close> by (auto simp add: field_simps)
  hence "?lhs0 * (x- y) \<ge> ?rhs0 * (x - y)"
    using \<open>x \<le> y\<close> by sos
  hence "v * x + 1 / 2 * a * x\<^sup>2 \<le> v * y + 1 / 2 * a * y\<^sup>2"
    by (auto simp add: field_simps power_def)
  thus " p x \<le> p y"
    unfolding p_max_def p_def t_stop_def by auto
qed

lemma p_antimono: "x \<le> y \<Longrightarrow> t_stop \<le> x \<Longrightarrow> p y \<le> p x"
  using decel
proof -
  assume "x \<le> y" and "t_stop \<le> x" and "a < 0"
  hence "- 2 * v / a \<le> x + y"
    unfolding t_stop_def by auto
  hence "v \<le> - 1/ 2 * a * (x + y)"
    using \<open>a < 0\<close> by (auto simp add: field_simps)
  hence "v * (x - y) \<ge> -1/2 * a * (x\<^sup>2 - y\<^sup>2) "
    using \<open>x \<le> y\<close> by sos
  hence "v * y + 1/2 * a * y\<^sup>2 \<le> v * x + 1/2 * a * x\<^sup>2"
    by (auto simp add: field_simps)
  thus "p y \<le> p x"
    unfolding p_max_def p_def t_stop_def by auto
qed

lemma p_strict_mono: "x < y \<Longrightarrow> y \<le> t_stop \<Longrightarrow> p x < p y"
  using decel
proof -
  assume "x < y" and "y \<le> t_stop" and "a < 0"
  hence "x + y < - 2 * v / a"
    unfolding t_stop_def by auto
  hence "-1 / 2 * a * (x + y) < v" (is "?lhs0 < ?rhs0")
    using \<open>a < 0\<close> by (auto simp add: field_simps)
  hence "?lhs0 * (x- y) > ?rhs0 * (x - y)"
    using \<open>x < y\<close> by sos
  hence "v * x + 1 / 2 * a * x\<^sup>2 < v * y + 1 / 2 * a * y\<^sup>2"
    by (auto simp add: field_simps power_def)
  thus " p x < p y"
    unfolding p_max_def p_def t_stop_def by auto
qed

lemma p_strict_antimono: "x < y \<Longrightarrow> t_stop \<le> x\<Longrightarrow> p y < p x"
  using decel
proof -
  assume "x < y" and "t_stop \<le> x" and "a < 0"
  hence "- 2 * v / a < x + y"
    unfolding t_stop_def by auto
  hence "v < - 1/ 2 * a * (x + y)"
    using \<open>a < 0\<close> by (auto simp add: field_simps)
  hence "v * (x - y) > -1/2 * a * (x\<^sup>2 - y\<^sup>2) "
    using \<open>x < y\<close> by sos
  hence "v * y + 1/2 * a * y\<^sup>2 < v * x + 1/2 * a * x\<^sup>2"
    by (auto simp add: field_simps)
  thus "p y < p x"
    unfolding p_max_def p_def t_stop_def by auto
qed

lemma p_max: "p x \<le> p_max"
  unfolding p_max_def
  by (cases "x \<le> t_stop") (auto intro: p_mono p_antimono)

lemma continuous_on_s[continuous_intros]: "continuous_on T s"
  unfolding s_def[abs_def]
  using t_stop_nonneg
  by (intro continuous_on_subset[where t=T and s = "{.. 0}\<union>({0 .. t_stop} \<union> {t_stop ..})"] continuous_on_If)
     (auto simp: p_continuous p_max_def antisym_conv[where x=0])

lemma isCont_s[continuous_intros]: "isCont s x"
  using continuous_on_s[of UNIV]
  by (auto simp: continuous_on_eq_continuous_at)

definition s' :: "real \<Rightarrow> real" where
  "s' t = (if t \<le> t_stop then p' t else 0)"

lemma s_has_real_derivative:
  assumes "t \<ge> 0" "v / a \<le> 0" "a \<noteq> 0"
  shows "(s has_real_derivative s' t) (at t within {0..})"
proof -
  from assms have *: "t \<le> t_stop \<longleftrightarrow> t \<in> {0 .. t_stop}" by simp
  from assms have "0 \<le> t_stop" by (auto simp: t_stop_def)
  have "((\<lambda>t. if t \<in> {0 .. t_stop} then p t else p_max) has_real_derivative
    (if t \<in> {0..t_stop} then p' t else 0)) (at t within {0..})"
    unfolding s_def[abs_def] s'_def 
      has_field_derivative_iff_has_vector_derivative
    apply (rule has_vector_derivative_If_within_closures[where T = "{t_stop ..}"])
    using \<open>0 \<le> t_stop\<close> \<open>a \<noteq> 0\<close>
    by (auto simp: assms p'_stop_zero p_t_stop max_def insert_absorb
      intro!: p_has_vector_derivative)
  from _ _ this show ?thesis
    unfolding has_vector_derivative_def has_field_derivative_iff_has_vector_derivative
      s'_def s_def[abs_def] *
    by (rule has_derivative_transform)
      (auto simp: assms s_def p_max_def t_stop_def)
qed

lemma s_has_vector_derivative[derivative_intros]:
  assumes "t \<ge> 0" "v / a \<le> 0" "a \<noteq> 0"
  shows  "(s has_vector_derivative s' t) (at t within {0..})"
  using s_has_real_derivative[OF assms]
  by (simp add: has_field_derivative_iff_has_vector_derivative)
   
lemma s_has_field_derivative[derivative_intros]:
  assumes "t \<ge> 0" "v / a \<le> 0" "a \<noteq> 0"
  shows "(s has_field_derivative s' t) (at t within {0..})"
  using s_has_vector_derivative[OF assms]
  by(simp add: has_field_derivative_iff_has_vector_derivative)
  
lemma s_has_real_derivative_at:
  assumes "0 < x" "0 \<le> v" "a < 0"
  shows "(s has_real_derivative s' x) (at x)"
proof -
  from assms have "(s has_real_derivative s' x) (at x within {0 ..})"
    by (intro s_has_real_derivative) (auto intro!: divide_nonneg_nonpos)
  then have "(s has_real_derivative s' x) (at x within {0<..})"
    by (rule DERIV_subset) auto
  then show "(s has_real_derivative s' x) (at x)" using assms
    by (subst (asm) at_within_open) auto
qed
                   
lemma s_delayed_has_field_derivative[derivative_intros]:
  assumes "\<delta> < t" "0 \<le> v" "a < 0"
  shows "((\<lambda>x. s (x - \<delta>)) has_field_derivative s' (t - \<delta>)) (at t within {\<delta><..})"
proof -
  from assms have "((\<lambda>x. s (x + - \<delta>)) has_real_derivative s' (t - \<delta>)) (at t)"
  using DERIV_shift[of "s" "(s' (t - \<delta>))" t "-\<delta>"] s_has_real_derivative_at 
  by auto  
  
  thus "((\<lambda>x. s (x - \<delta>)) has_field_derivative s' (t - \<delta>)) (at t within {\<delta><..})"
  using has_field_derivative_at_within by auto
qed  

lemma s_delayed_has_vector_derivative[derivative_intros]:
  assumes "\<delta> < t" "0 \<le> v" "a < 0"
  shows  "((\<lambda>x. s (x - \<delta>)) has_vector_derivative s' (t - \<delta>)) (at t within {\<delta><..})"
  using s_delayed_has_field_derivative[OF assms]  
  by(simp add:has_field_derivative_iff_has_vector_derivative)

lemma s'_nonneg: "0 \<le> v \<Longrightarrow> a \<le> 0 \<Longrightarrow> 0 \<le> s' x"
  by (auto simp: s'_def p'_def t_stop_def field_split_simps) 

lemma s'_pos: "0 \<le> x \<Longrightarrow> x < t_stop \<Longrightarrow> 0 \<le> v \<Longrightarrow> a \<le> 0 \<Longrightarrow> 0 < s' x"
  by (intro le_neq_trans s'_nonneg)
    (auto simp: s'_def p'_def t_stop_def field_split_simps)

subsubsection \<open>Monotonicity of Movement\<close>

lemma s_mono:
  assumes "t \<ge> u" "u \<ge> 0"
  shows "s t \<ge> s u"
  using p_mono[of u t] assms p_max[of u] by (auto simp: s_def)

lemma s_strict_mono:
  assumes "u < t" "t \<le> t_stop" "u \<ge> 0"
  shows "s u < s t"
  using p_strict_mono[of u t] assms p_max[of u] by (auto simp: s_def)

lemma s_antimono:
  assumes "x \<le> y"
  assumes "t_stop \<le> x"
  shows "s y \<le> s x"
proof -
  from assms have "t_stop \<le> y" by auto  
  hence "s y \<le> p_max" unfolding s_def p_max_eq
    using p_max_def p_max_eq s0_le_s_stop s_t_stop by auto
  also have "... \<le> s x" 
    using \<open>t_stop \<le> x\<close> s_mono s_t_stop t_stop_nonneg by fastforce
  ultimately show "s y \<le> s x" by auto
qed

lemma init_s : "t \<le> 0 \<Longrightarrow> s t = s0"
  using decel nonneg_vel by (simp add: divide_simps s_def)

lemma q_min: "0 \<le> t \<Longrightarrow> s0 \<le> q t"
  unfolding q_def using nonneg_vel by auto

lemma q_mono: "x \<le> y \<Longrightarrow> q x \<le> q y"
  unfolding q_def using nonneg_vel by (auto simp: mult_left_mono)

subsubsection \<open>Maximum at Stopping Time\<close>

lemma s_max: "s x \<le> s_stop"
  using p_max[of x] p_max[of 0] unfolding s_t_stop by (auto simp: s_def)

lemma s_eq_s_stop: "NO_MATCH t_stop x \<Longrightarrow> x \<ge> t_stop \<Longrightarrow> s x = s_stop"
  using t_stop_nonneg by (auto simp: s_def p_max_def)

end

subsection \<open>Safe Distance\<close>

locale safe_distance =
  fixes a\<^sub>e v\<^sub>e s\<^sub>e :: real
  fixes a\<^sub>o v\<^sub>o s\<^sub>o :: real
  assumes nonneg_vel_ego   : "0 \<le> v\<^sub>e"
  assumes nonneg_vel_other : "0 \<le> v\<^sub>o"
  assumes decelerate_ego   : "a\<^sub>e < 0"
  assumes decelerate_other : "a\<^sub>o < 0"
  assumes in_front         : "s\<^sub>e < s\<^sub>o"
begin

lemmas hyps =
  nonneg_vel_ego   
  nonneg_vel_other 
  decelerate_ego   
  decelerate_other 
  in_front

sublocale ego: braking_movement a\<^sub>e v\<^sub>e s\<^sub>e by (unfold_locales; rule hyps)
sublocale other: braking_movement a\<^sub>o v\<^sub>o s\<^sub>o by (unfold_locales; rule hyps)
sublocale ego_other: movement "a\<^sub>o - a\<^sub>e" "v\<^sub>o - v\<^sub>e" "s\<^sub>o - s\<^sub>e" by unfold_locales

subsubsection \<open>Collision\<close>

definition collision :: "real set \<Rightarrow> bool" where
  "collision time_set \<equiv> (\<exists>t \<in> time_set. ego.s t = other.s t )"

abbreviation no_collision :: "real set \<Rightarrow> bool" where
  "no_collision time_set \<equiv> \<not> collision time_set"

lemma no_collision_initially : "no_collision {.. 0}"
  using decelerate_ego nonneg_vel_ego
  using decelerate_other nonneg_vel_other in_front
  by (auto simp: divide_simps collision_def ego.s_def other.s_def)

lemma no_collisionI:
  "(\<And>t. t \<in> S \<Longrightarrow> ego.s t \<noteq> other.s t) \<Longrightarrow> no_collision S"
  unfolding collision_def by blast

theorem cond_1: "ego.s_stop < s\<^sub>o \<Longrightarrow> no_collision {0..}"
proof (rule no_collisionI, simp)
  fix t::real
  assume "t \<ge> 0"
  have "ego.s t \<le> ego.s_stop"
    by (rule ego.s_max)
  also assume "\<dots> < s\<^sub>o"
  also have "\<dots> = other.s 0"
    by (simp add: other.init_s)
  also have "\<dots> \<le> other.s t"
    using \<open>0 \<le> t\<close> hyps
    by (intro other.s_mono) auto
  finally show "ego.s t \<noteq> other.s t"
    by simp
qed

lemma ego_other_strict_ivt:
  assumes "ego.s t > other.s t"
  shows "collision {0 ..< t}"
proof cases
  have [simp]: "s\<^sub>e < s\<^sub>o \<Longrightarrow> ego.s 0 \<le> other.s 0" 
    by (simp add: movement.s_def)
  assume "0 \<le> t"
  with assms in_front
  have "\<exists>x\<ge>0. x \<le> t \<and> other.s x - ego.s x = 0"
    by (intro IVT2, auto simp: continuous_diff other.isCont_s ego.isCont_s)
  then show ?thesis
    using assms
    by (auto simp add: algebra_simps collision_def Bex_def order.order_iff_strict)
qed (insert assms hyps, auto simp: collision_def ego.init_s other.init_s intro!: bexI[where x=0])

lemma collision_subset: "collision s \<Longrightarrow> s \<subseteq> t \<Longrightarrow> collision t"
  by (auto simp: collision_def)

lemma ego_other_ivt:
  assumes "ego.s t \<ge> other.s t"
  shows "collision {0 .. t}"
proof cases
  assume "ego.s t > other.s t"
  from ego_other_strict_ivt[OF this]
  show ?thesis
    by (rule collision_subset) auto
qed (insert hyps assms; cases "t \<ge> 0"; force simp: collision_def ego.init_s other.init_s)

theorem cond_2:
  assumes "ego.s_stop \<ge> other.s_stop"
  shows "collision {0 ..}"
  using assms
  apply (intro collision_subset[where t="{0 ..}" and s = "{0 .. max ego.t_stop other.t_stop}"])
   apply (intro ego_other_ivt[where t = "max ego.t_stop other.t_stop"])
   apply (auto simp: ego.s_eq_s_stop other.s_eq_s_stop)
  done

abbreviation D2 :: "real" where
  "D2 \<equiv> (v\<^sub>o - v\<^sub>e)^2 - 2 * (a\<^sub>o - a\<^sub>e) * (s\<^sub>o - s\<^sub>e)"

abbreviation t\<^sub>D' :: "real" where
  "t\<^sub>D' \<equiv> sqrt (2 * (ego.s_stop - other.s_stop) / a\<^sub>o)"

lemma pos_via_half_dist:
  "dist a b < b / 2 \<Longrightarrow> b > 0 \<Longrightarrow> a > 0"
  by (auto simp: dist_real_def abs_real_def split: if_splits)

lemma collision_within_p:
  assumes "s\<^sub>o \<le> ego.s_stop" "ego.s_stop < other.s_stop"
  shows "collision {0..} \<longleftrightarrow> (\<exists>t\<ge>0. ego.p t = other.p t \<and> t < ego.t_stop \<and> t < other.t_stop)"
proof (auto simp: collision_def, goal_cases)
  case (2 t)
  then show ?case
    by (intro bexI[where x = t]) (auto simp: ego.s_def other.s_def)
next
  case (1 t)
  then show ?case using assms hyps ego.t_stop_nonneg other.t_stop_nonneg
    apply (auto simp: ego.s_def other.s_def ego.s_t_stop other.s_t_stop ego.p_t_stop other.p_t_stop not_le
        split: if_splits)
    defer
  proof goal_cases
    case 1
    from 1 have le: "ego.t_stop \<le> other.t_stop" by auto
    from 1 have "ego.t_stop < t" by simp
    from other.s_strict_mono[OF this] 1
    have "other.s ego.t_stop < other.s t"
      by auto
    also have "\<dots> = ego.s ego.t_stop"
      using ego.s_t_stop ego.t_stop_nonneg 1 other.s_def by auto
    finally have "other.s ego.t_stop < ego.s ego.t_stop" .
    from ego_other_strict_ivt[OF this] le in_front
    show ?case
      by (auto simp add: collision_def) (auto simp: movement.s_def split: if_splits)
  next
    case 2
    from 2 have "other.p_max = ego.p t" by simp
    also have "\<dots> \<le> ego.p ego.t_stop"
      using 2
      by (intro ego.p_mono) auto
    also have "\<dots> = ego.p_max"
      by (simp add: ego.p_t_stop)
    also note \<open>\<dots> < other.p_max\<close>
    finally show ?case by arith
  next
    case 3
    thus "\<exists>t\<ge>0. ego.p t = other.p t \<and> t < ego.t_stop \<and> t < other.t_stop" 
      apply (cases "t = other.t_stop")
       apply (simp add: other.p_t_stop )
       apply (metis (no_types) ego.p_max not_le)
      apply (cases "t = ego.t_stop")
       apply (simp add: ego.p_t_stop)
       defer
       apply force
    proof goal_cases
      case (1)
      let ?d = "\<lambda>t. other.p' t - ego.p' t"
      define d' where "d' = ?d ego.t_stop / 2"
      have d_cont: "isCont ?d ego.t_stop"
        unfolding ego.t_stop_def other.p'_def ego.p'_def by simp
      have "?d ego.t_stop > 0"
        using 1
        by (simp add: ego.p'_stop_zero other.p'_pos_iff) (simp add: ego.t_stop_def other.t_stop_def)
      then have "d' > 0" by (auto simp: d'_def)
      from d_cont[unfolded continuous_at_eps_delta, THEN spec, rule_format, OF \<open>d' > 0\<close>]
      obtain e where e: "e > 0" "\<And>x. dist x ego.t_stop < e \<Longrightarrow> ?d x > 0"
        unfolding d'_def
        using \<open>?d ego.t_stop > 0\<close> pos_via_half_dist
        by force
      define t' where "t' = ego.t_stop - min (ego.t_stop / 2) (e / 2)"
      have "0 < ego.t_stop" using 1 by auto
      have "other.p t' - ego.p t' < other.p ego.t_stop - ego.p ego.t_stop"
        apply (rule DERIV_pos_imp_increasing[of t'])
         apply (force simp: t'_def e min_def \<open>0 < ego.t_stop\<close>)
        apply (auto intro!: exI[where x = "?d x" for x] intro!: derivative_intros e)
        using \<open>e > 0\<close>
        apply (auto simp: t'_def dist_real_def algebra_simps)
        done
      also have "\<dots> = 0" using 1 by (simp add: ego.p_t_stop)
      finally have less: "other.p t' < ego.p t'" by simp
      have "t' > 0"
        using 1 by (auto simp: t'_def algebra_simps min_def)
      have "t' < ego.t_stop" by (auto simp: t'_def \<open>e > 0\<close> \<open>ego.t_stop > 0\<close>)
      from less_le_trans[OF \<open>t' < ego.t_stop\<close> \<open>ego.t_stop \<le> other.t_stop\<close>]
      have "t' < other.t_stop" .
      from ego_other_strict_ivt[of t'] less
      have "collision {0..<t'}"
        using \<open>t' > 0\<close> \<open>t' < ego.t_stop\<close> \<open>t' < other.t_stop\<close>
        by (auto simp: other.s_def ego.s_def split: if_splits)
      thus ?case
        using \<open>t' > 0\<close> \<open>t' < ego.t_stop\<close> \<open>t' < other.t_stop\<close>
        apply (auto simp: collision_def ego.s_def other.s_def movement.p_def
            split: if_splits)
        apply (rule_tac x = t in exI) 
        apply (auto simp: movement.p_def)[]
        done
    qed
  qed
qed

lemma collision_within_eq:
  assumes "s\<^sub>o \<le> ego.s_stop" "ego.s_stop < other.s_stop"
  shows "collision {0..} \<longleftrightarrow> collision {0 ..< min ego.t_stop other.t_stop}"
  unfolding collision_within_p[OF assms]
  unfolding collision_def
  by (safe; force
    simp: ego.s_def other.s_def movement.p_def ego.t_stop_def other.t_stop_def
    split: if_splits)

lemma collision_excluded: "(\<And>t. t \<in> T \<Longrightarrow> ego.s t \<noteq> other.s t) \<Longrightarrow> collision S \<longleftrightarrow> collision (S - T)"
  by (auto simp: collision_def)

lemma collision_within_less:
  assumes "s\<^sub>o \<le> ego.s_stop" "ego.s_stop < other.s_stop"
  shows "collision {0..} \<longleftrightarrow> collision {0 <..< min ego.t_stop other.t_stop}"
proof -
  note collision_within_eq[OF assms]
  also have "collision {0 ..< min ego.t_stop other.t_stop} \<longleftrightarrow>
    collision ({0 ..< min ego.t_stop other.t_stop} - {0})"
    using hyps assms
    by (intro collision_excluded) (auto simp: ego.s_def other.s_def)
  also have "{0 ..< min ego.t_stop other.t_stop} - {0} = {0 <..< min ego.t_stop other.t_stop}"
    by auto
  finally show ?thesis 
    unfolding collision_def
    by (safe;
      force
        simp: ego.s_def other.s_def movement.p_def ego.t_stop_def other.t_stop_def
        split: if_splits)
qed

theorem cond_3:
  assumes "s\<^sub>o \<le> ego.s_stop" "ego.s_stop < other.s_stop"
  shows "collision {0..} \<longleftrightarrow> (a\<^sub>o > a\<^sub>e \<and> v\<^sub>o < v\<^sub>e \<and> 0 \<le> D2 \<and> sqrt D2 > v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o)"
proof -
  have "v\<^sub>o \<noteq> 0"
    using assms(1) assms(2) movement.s_def movement.t_stop_def by auto
  with hyps have "v\<^sub>o > 0" by auto
  note hyps = hyps this
  define t1 where "t1 = (- (v\<^sub>o - v\<^sub>e) + sqrt D2) / (a\<^sub>o - a\<^sub>e)"
  define t2 where "t2 = (- (v\<^sub>o - v\<^sub>e) - sqrt D2) / (a\<^sub>o - a\<^sub>e)"
  define bounded where "bounded \<equiv> \<lambda>t. (0 \<le> t \<and> t \<le> ego.t_stop \<and> t \<le> other.t_stop)"
  have ego_other_conv:
    "\<And>t. bounded t \<Longrightarrow> ego.p t = other.p t \<longleftrightarrow> ego_other.p t = 0"
    by (auto simp: movement.p_def field_split_simps)
  let ?r = "{0 <..< min ego.t_stop other.t_stop}"
  have D2: "D2 = (v\<^sub>o - v\<^sub>e)\<^sup>2 - 4 * ((a\<^sub>o - a\<^sub>e) / 2) * (s\<^sub>o - s\<^sub>e)" by simp
  define D where "D = D2"
  note D = D_def[symmetric]
  define x1 where "x1 \<equiv> (- (v\<^sub>o - v\<^sub>e) + sqrt D2) / (2 * ((a\<^sub>o - a\<^sub>e) / 2))"
  define x2 where "x2 \<equiv> (- (v\<^sub>o - v\<^sub>e) - sqrt D2) / (2 * ((a\<^sub>o - a\<^sub>e) / 2))"
  have x2: "x2 =(- (v\<^sub>o - v\<^sub>e) - sqrt D2) / (a\<^sub>o - a\<^sub>e)"
    by (simp add: x2_def field_split_simps)
  have x1: "x1 =(- (v\<^sub>o - v\<^sub>e) + sqrt D2) / (a\<^sub>o - a\<^sub>e)"
    by (simp add: x1_def field_split_simps)
  from collision_within_less[OF assms]
  have coll_eq: "collision {0..} = collision ?r"
    by (auto simp add: bounded_def)
  also have "\<dots> \<longleftrightarrow> (a\<^sub>o > a\<^sub>e \<and> v\<^sub>o < v\<^sub>e \<and> 0 \<le> D2 \<and> sqrt D2 > v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o)"
  proof safe
    assume H: "a\<^sub>e < a\<^sub>o" "v\<^sub>o < v\<^sub>e" "0 \<le> D2"
    assume sqrt: "sqrt D2 > v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o"
    have nz: "(a\<^sub>o - a\<^sub>e) / 2 \<noteq> 0" using \<open>a\<^sub>e < a\<^sub>o\<close> by simp
    note sol = quadratic_eq_zeroes_iff[OF D2 x1_def[THEN meta_eq_to_obj_eq] x2_def[THEN meta_eq_to_obj_eq] nz]
    from sol[of x2] \<open>0 \<le> D2\<close>
    have "other.p x2 = ego.p x2"
      by (auto simp: ego.p_def other.p_def field_split_simps)
    moreover
    have "x2 > 0"
    proof (rule ccontr)
      assume "\<not> 0 < x2"
      then have "ego_other.p x2 \<ge> ego_other.p 0"
        using H hyps
        by (intro DERIV_nonpos_imp_nonincreasing[of x2]) 
          (auto intro!: exI[where x="ego_other.p' x" for x] derivative_eq_intros
            simp: ego_other.p'_def add_nonpos_nonpos mult_nonneg_nonpos)
      also have "ego_other.p 0 > 0" using hyps by (simp add: ego_other.p_def)
      finally (xtrans) show False using \<open>other.p x2 = ego.p x2\<close>
        by (simp add: movement.p_def field_split_simps power2_eq_square)
    qed
    moreover
    have "x2 < other.t_stop"
      using sqrt H hyps
      by (auto simp: x2 other.t_stop_def field_split_simps power2_eq_square)

    ultimately
    show "collision {0<..<min ego.t_stop other.t_stop}"
    proof (cases "x2 < ego.t_stop", goal_cases)
      case 2
      then have "other.s x2 = other.p x2"
        by (auto simp: other.s_def)
      also from 2 have "\<dots> \<le> ego.p ego.t_stop"
        by (auto intro!: ego.p_antimono)
      also have "\<dots> = ego.s x2"
        using 2 by (auto simp: ego.s_def ego.p_t_stop)
      finally have "other.s x2 \<le> ego.s x2" .
      from ego_other_ivt[OF this]
      show ?thesis
        unfolding coll_eq[symmetric]
        by (rule collision_subset) auto
    qed (auto simp: collision_def ego.s_def other.s_def not_le intro!: bexI[where x=x2])
  next
    let ?max = "max ego.t_stop other.t_stop"
    let ?min = "min ego.t_stop other.t_stop"
    assume "collision ?r"
    then obtain t where t: "ego.p t = other.p t" "0 < t" "t < ?min"
      by (auto simp: collision_def ego.s_def other.s_def)
    then have "t < - (v\<^sub>e / a\<^sub>e)" "t < - (v\<^sub>o / a\<^sub>o)" "t < other.t_stop"
      by (simp_all add: ego.t_stop_def other.t_stop_def)
    from t have "ego_other.p t = 0"
      by (auto simp: movement.p_def field_split_simps)
    from t have "t < ?max" by auto
    from hyps assms have "0 < ego_other.p 0"
      by simp
    from ego_other.p_def[abs_def, THEN meta_eq_to_obj_eq]
    have eop_eq: "ego_other.p = (\<lambda>t. 1 / 2 * (a\<^sub>o - a\<^sub>e) * t\<^sup>2 + (v\<^sub>o - v\<^sub>e) * t + (s\<^sub>o - s\<^sub>e))"
      by (simp add: algebra_simps)
    show "a\<^sub>o > a\<^sub>e"
    proof -
      have "ego.p other.t_stop \<le> ego.p_max"
        by (rule ego.p_max)
      also have "... \<le> other.p other.t_stop" using hyps assms
        by (auto simp:other.s_def ego.s_def ego.p_t_stop split:if_splits)
      finally have "0 \<le> ego_other.p other.t_stop"
        by (auto simp add:movement.p_def field_simps)
      from p_convex[OF eop_eq, of 0 t other.t_stop, simplified \<open>ego_other.p t = 0\<close>,
        OF \<open>0 < t\<close> \<open>t < other.t_stop\<close> \<open>0 < ego_other.p 0\<close> \<open>0 \<le> ego_other.p other.t_stop\<close>]
      show "a\<^sub>o > a\<^sub>e" by (simp add: algebra_simps)
    qed
    have rewr: "4 * ((a\<^sub>o - a\<^sub>e) / 2) = 2 * (a\<^sub>o - a\<^sub>e)" by simp
    from \<open>a\<^sub>o > a\<^sub>e\<close> \<open>ego_other.p t = 0\<close> ego_other.p_all_zeroes[OF D2[symmetric], of t]
    have "0 \<le> D2" and disj: "(t = (- (v\<^sub>o - v\<^sub>e) + sqrt D2) / (a\<^sub>o - a\<^sub>e) \<or> t = (- (v\<^sub>o - v\<^sub>e) - sqrt D2) / (a\<^sub>o - a\<^sub>e))"
      using hyps assms
      unfolding rewr by simp_all
    show "0 \<le> D2" by fact
    from add_strict_mono[OF \<open>t < - (v\<^sub>e / a\<^sub>e)\<close> \<open>t < - (v\<^sub>o / a\<^sub>o)\<close>] \<open>0 < t\<close> \<open>a\<^sub>o > a\<^sub>e\<close>
    have "0 < - (v\<^sub>e / a\<^sub>e) + - (v\<^sub>o / a\<^sub>o)" by (simp add: divide_simps)
    then have "0 > v\<^sub>e * a\<^sub>o + a\<^sub>e * v\<^sub>o" using hyps
      by (simp add: field_split_simps split: if_splits)
    show "v\<^sub>o < v\<^sub>e"
      using \<open>a\<^sub>e < a\<^sub>o\<close> \<open>movement.p (a\<^sub>o - a\<^sub>e) (v\<^sub>o - v\<^sub>e) (s\<^sub>o - s\<^sub>e) t = 0\<close> in_front  t(2)
      apply (auto simp: movement.p_def divide_less_0_iff algebra_simps power2_eq_square)
      by (smt divide_less_0_iff mult_le_cancel_right mult_mono mult_nonneg_nonneg nonneg_vel_ego)
    from disj have "x2 < ?min"
    proof rule
      assume "t = (- (v\<^sub>o - v\<^sub>e) - sqrt D2) / (a\<^sub>o - a\<^sub>e)"
      then show ?thesis
        using \<open>t < ?min\<close>
        by (simp add: x2)
    next
      assume "t = (- (v\<^sub>o - v\<^sub>e) + sqrt D2) / (a\<^sub>o - a\<^sub>e)"
      also have "\<dots> \<ge> x2"
        unfolding x2
        apply (rule divide_right_mono)
         apply (subst (2) diff_conv_add_uminus)
         apply (rule add_left_mono)
        using \<open>a\<^sub>o > a\<^sub>e\<close> \<open>D2 \<ge> 0\<close>
        by auto
      also (xtrans) note \<open>t < ?min\<close>
      finally show ?thesis .
    qed
    then show "sqrt D2 > v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o"
      using hyps \<open>a\<^sub>o > a\<^sub>e\<close>
      by (auto simp: x2 field_split_simps other.t_stop_def)
  qed
  finally show ?thesis .
qed

subsubsection \<open>Formalising Safe Distance\<close>

text \<open>First definition for Safe Distance based on \<open>cond_1\<close>.\<close>
definition absolute_safe_distance :: real where
  "absolute_safe_distance = - v\<^sub>e\<^sup>2 / (2 * a\<^sub>e)"

lemma absolute_safe_distance:
  assumes "s\<^sub>o - s\<^sub>e > absolute_safe_distance"
  shows "no_collision {0..}"
  proof -
  from assms hyps absolute_safe_distance_def have "ego.s_stop < s\<^sub>o" 
    by (auto simp add:ego.s_def ego.p_def ego.t_stop_def power_def)
  thus ?thesis by (rule cond_1)
  qed

text \<open>First Fallback for Safe Distance.\<close>
definition fst_safe_distance :: real where
  "fst_safe_distance = v\<^sub>o\<^sup>2 / (2 * a\<^sub>o) - v\<^sub>e\<^sup>2 / (2 * a\<^sub>e)"

definition distance_leq_d2 :: real where
  "distance_leq_d2 = (a\<^sub>e + a\<^sub>o) / (2 * a\<^sub>o\<^sup>2) * v\<^sub>o\<^sup>2 - v\<^sub>o * v\<^sub>e / a\<^sub>o"

lemma snd_leq_fst_exp: "distance_leq_d2 \<le> fst_safe_distance"
proof -
  have "0 \<le> (other.t_stop - ego.t_stop)\<^sup>2" by auto
  hence "- ego.t_stop\<^sup>2 \<le> other.t_stop\<^sup>2 - 2 * other.t_stop * ego.t_stop" by (simp add:power_def algebra_simps) 
  with hyps(3) have "- ego.t_stop\<^sup>2 * (a\<^sub>e / 2) \<ge> (other.t_stop\<^sup>2 - 2 * other.t_stop * ego.t_stop) * (a\<^sub>e / 2)"
    by (smt half_gt_zero_iff mult_le_cancel_right)
  with ego.t_stop_def other.t_stop_def hyps 
  have "- v\<^sub>e\<^sup>2 / (2 * a\<^sub>e) \<ge> a\<^sub>e * v\<^sub>o\<^sup>2 / (2 * a\<^sub>o\<^sup>2) - v\<^sub>o * v\<^sub>e / a\<^sub>o" by (simp add:power_def algebra_simps)
  with fst_safe_distance_def distance_leq_d2_def
  have 1: "fst_safe_distance \<ge>  a\<^sub>e * v\<^sub>o\<^sup>2 / (2 * a\<^sub>o\<^sup>2) - v\<^sub>o * v\<^sub>e / a\<^sub>o + v\<^sub>o\<^sup>2 / (2 * a\<^sub>o)" by (auto simp add:algebra_simps)
  have "a\<^sub>e * v\<^sub>o\<^sup>2 / (2 * a\<^sub>o\<^sup>2) - v\<^sub>o * v\<^sub>e / a\<^sub>o + v\<^sub>o\<^sup>2 / (2 * a\<^sub>o) = distance_leq_d2" (is "?LHS = _")
  proof -
    have "?LHS = a\<^sub>e * v\<^sub>o\<^sup>2 / (2 * a\<^sub>o\<^sup>2) - v\<^sub>o * v\<^sub>e / a\<^sub>o + a\<^sub>o * v\<^sub>o\<^sup>2 / (2 * a\<^sub>o\<^sup>2)"  
      by (auto simp add: algebra_simps power_def)
    also have "...  = distance_leq_d2" 
      by (auto simp add: power_def field_split_simps distance_leq_d2_def)
    finally show ?thesis by auto    
  qed
  with 1 show ?thesis by auto
qed  

lemma sqrt_D2_leq_stop_time_diff:
  assumes "a\<^sub>e < a\<^sub>o"
  assumes "0 \<le> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o "
  assumes "s\<^sub>o - s\<^sub>e \<ge> distance_leq_d2"
  shows "sqrt D2 \<le> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o"
proof -
  from assms have "- 2 * (a\<^sub>o - a\<^sub>e) * (s\<^sub>o - s\<^sub>e) \<le> - 2 * (a\<^sub>o - a\<^sub>e) * distance_leq_d2" (is "?L \<le> ?R") 
  by simp
  hence "D2 \<le> (v\<^sub>o - v\<^sub>e)\<^sup>2 - 2 * (a\<^sub>o - a\<^sub>e) * distance_leq_d2" by (simp add: algebra_simps)
  also have "... = (v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o)\<^sup>2"
  proof -
    from distance_leq_d2_def
    have 1: "(v\<^sub>o - v\<^sub>e)\<^sup>2 - 2 * (a\<^sub>o - a\<^sub>e) * distance_leq_d2 = 
             (v\<^sub>o - v\<^sub>e)\<^sup>2 - (a\<^sub>o - a\<^sub>e) * (a\<^sub>e + a\<^sub>o) / a\<^sub>o\<^sup>2 * v\<^sub>o\<^sup>2 + 2 * (a\<^sub>o - a\<^sub>e) * v\<^sub>o * v\<^sub>e / a\<^sub>o"
      by (auto simp add: field_split_simps)
    with hyps(4) have "... = (v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o)\<^sup>2"
      by (auto simp add: power_def field_split_simps)
    with 1 show ?thesis by auto
  qed
  finally show ?thesis  by (smt assms(2) real_le_lsqrt real_sqrt_le_0_iff)
qed

lemma cond2_imp_pos_vo:
  assumes "s\<^sub>o \<le> ego.s_stop" "ego.s_stop < other.s_stop"
  shows "v\<^sub>o \<noteq> 0"
proof (rule ccontr)
  assume "\<not> v\<^sub>o \<noteq> 0"
  with other.s_def other.t_stop_def have "other.s_stop = s\<^sub>o" by auto
  with assms(2) have "ego.s_stop < s\<^sub>o" by auto
  with assms(1) show "False" by auto
qed

lemma cond2_imp_gt_fst_sd:
  assumes "s\<^sub>o \<le> ego.s_stop" "ego.s_stop < other.s_stop"
  shows "fst_safe_distance < s\<^sub>o - s\<^sub>e"
proof (cases "v\<^sub>e \<noteq> 0")
  case True
  from fst_safe_distance_def assms ego.s_def ego.t_stop_pos[OF \<open>v\<^sub>e \<noteq> 0\<close>] ego.p_def ego.t_stop_def
       other.s_def other.t_stop_pos[OF cond2_imp_pos_vo[OF assms]] other.p_def other.t_stop_def hyps
  show ?thesis by (simp add: power_def algebra_simps)
next
  case False
  with fst_safe_distance_def  have "fst_safe_distance = v\<^sub>o\<^sup>2 / (2 * a\<^sub>o)" by auto
  also have "... \<le> 0"  by (simp add: divide_nonneg_neg hyps)
  also have "... < s\<^sub>o - s\<^sub>e" by (simp add: algebra_simps hyps)
  finally show ?thesis by auto
qed

text \<open>Second Fallback for Safe Distance.\<close>
definition snd_safe_distance :: real where
  "snd_safe_distance = (v\<^sub>o - v\<^sub>e)\<^sup>2 / (2 * (a\<^sub>o - a\<^sub>e))"

lemma fst_leq_snd_safe_distance:
  assumes "a\<^sub>e < a\<^sub>o"
  shows"fst_safe_distance \<le> snd_safe_distance"
proof -
  have "0 \<le> (v\<^sub>o / a\<^sub>o - v\<^sub>e / a\<^sub>e)\<^sup>2" by auto
  hence 1: "0 \<le> (v\<^sub>o / a\<^sub>o)\<^sup>2 - 2 * v\<^sub>o * v\<^sub>e / (a\<^sub>o * a\<^sub>e) + (v\<^sub>e / a\<^sub>e)\<^sup>2" by (auto simp add: power_def algebra_simps)
  from hyps have "0 \<le> a\<^sub>o * a\<^sub>e"  by (simp add: mult_nonpos_nonpos)  
  from mult_right_mono[OF 1 this] hyps
  have "0 \<le> v\<^sub>o\<^sup>2 * a\<^sub>e / a\<^sub>o - 2 * v\<^sub>o * v\<^sub>e  + v\<^sub>e\<^sup>2 * a\<^sub>o / a\<^sub>e" by (auto simp add: power_def algebra_simps)
  with hyps have 2: "(v\<^sub>o\<^sup>2 / (2 * a\<^sub>o) - v\<^sub>e\<^sup>2 / (2 * a\<^sub>e)) * (2 * (a\<^sub>o - a\<^sub>e)) \<le> (v\<^sub>o - v\<^sub>e)\<^sup>2"
    by (auto simp add: power_def field_split_simps)
  from assms have "0 \<le> 2 * (a\<^sub>o - a\<^sub>e)" by auto
  from divide_right_mono[OF 2 this] assms fst_safe_distance_def snd_safe_distance_def
  show ?thesis by auto
qed

lemma snd_safe_distance_iff_nonneg_D2: 
  assumes "a\<^sub>e < a\<^sub>o"
  shows "s\<^sub>o - s\<^sub>e \<le> snd_safe_distance \<longleftrightarrow> 0 \<le> D2"
proof -
  from snd_safe_distance_def assms pos_le_divide_eq[of "2 * (a\<^sub>o - a\<^sub>e)"]
  have "s\<^sub>o - s\<^sub>e \<le> snd_safe_distance \<longleftrightarrow> (s\<^sub>o - s\<^sub>e) * (2 * (a\<^sub>o - a\<^sub>e)) \<le> (v\<^sub>o - v\<^sub>e)\<^sup>2" by auto
  also have "... \<longleftrightarrow> 0 \<le> D2" by (auto simp add: algebra_simps)
  finally show ?thesis by auto
qed

lemma t_stop_diff_neg_means_leq_D2:
  assumes "s\<^sub>o \<le> ego.s_stop" "ego.s_stop < other.s_stop" "a\<^sub>e < a\<^sub>o" "0 \<le> D2"
  shows "v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < 0 \<longleftrightarrow> sqrt D2 > v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o"
proof
  assume only_if: "v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < 0"
  from assms have "... \<le> sqrt D2" by auto
  with only_if show "v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < sqrt D2" by linarith
next
  assume if_part: "v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < sqrt D2"
  from cond2_imp_gt_fst_sd[OF assms(1) assms(2)] snd_leq_fst_exp have "distance_leq_d2 \<le> s\<^sub>o - s\<^sub>e" by auto
  from if_part and sqrt_D2_leq_stop_time_diff [OF \<open>a\<^sub>e < a\<^sub>o\<close> _ \<open>distance_leq_d2 \<le> s\<^sub>o - s\<^sub>e\<close>]
  show " v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < 0"  by linarith
qed

theorem cond_3':
  assumes "s\<^sub>o \<le> ego.s_stop" "ego.s_stop < other.s_stop"
  shows "collision {0..} \<longleftrightarrow> (a\<^sub>o > a\<^sub>e \<and> v\<^sub>o < v\<^sub>e \<and> s\<^sub>o - s\<^sub>e \<le> snd_safe_distance \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < 0)"
proof (cases "a\<^sub>o \<le> a\<^sub>e \<or> v\<^sub>o \<ge> v\<^sub>e")
  case True
  with cond_3[OF assms] show ?thesis by auto
next
  case False
  from \<open>\<not> (a\<^sub>o \<le> a\<^sub>e \<or> v\<^sub>e \<le> v\<^sub>o)\<close> have "a\<^sub>o > a\<^sub>e" by auto
  from \<open>\<not> (a\<^sub>o \<le> a\<^sub>e \<or> v\<^sub>e \<le> v\<^sub>o)\<close> have "v\<^sub>o < v\<^sub>e" by auto
  show ?thesis 
  proof -
    from snd_safe_distance_iff_nonneg_D2 [OF \<open>a\<^sub>o > a\<^sub>e\<close>]
    have 1: "(a\<^sub>e < a\<^sub>o \<and> v\<^sub>o < v\<^sub>e \<and> s\<^sub>o - s\<^sub>e \<le> snd_safe_distance \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < 0) \<longleftrightarrow>
          (a\<^sub>e < a\<^sub>o \<and> v\<^sub>o < v\<^sub>e \<and> 0 \<le> D2 \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < 0)" by auto

    from t_stop_diff_neg_means_leq_D2[OF assms \<open>a\<^sub>e < a\<^sub>o\<close>]
    have "... = (a\<^sub>e < a\<^sub>o \<and> v\<^sub>o < v\<^sub>e \<and> 0 \<le> D2 \<and> sqrt D2 > v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o)" by auto

    with 1 cond_3[OF assms] show ?thesis by blast
  qed
qed

definition d :: "real \<Rightarrow> real" where
  "d t = (
    if t \<le> 0 then s\<^sub>o - s\<^sub>e
    else if t \<le> ego.t_stop \<and> t \<le> other.t_stop then ego_other.p t
    else if ego.t_stop \<le> t \<and> t \<le> other.t_stop then other.p t - ego.s_stop
    else if other.t_stop \<le> t \<and> t \<le> ego.t_stop then other.s_stop - ego.p t
    else other.s_stop - ego.s_stop
  )"

lemma d_diff: "d t = other.s t - ego.s t"
  by (auto simp: d_def ego.s_eq_s_stop other.s_eq_s_stop ego.s_cond_def other.s_cond_def
    movement.p_def field_split_simps)

lemma collision_d: "collision S \<longleftrightarrow> (\<exists>t\<in>S. d t = 0)"
  by (force simp: d_diff collision_def )

lemma collision_restrict: "collision {0..} \<longleftrightarrow> collision {0..max ego.t_stop other.t_stop}"  
  by (auto simp: max.coboundedI1 ego.t_stop_nonneg min_def
    ego.s_eq_s_stop other.s_eq_s_stop collision_def
    intro!: bexI[where x = "min t (max (movement.t_stop a\<^sub>e v\<^sub>e) (movement.t_stop a\<^sub>o v\<^sub>o))" for t])

lemma collision_union: "collision (A \<union> B) \<longleftrightarrow> collision A \<or> collision B"
  by (auto simp: collision_def)

lemma symbolic_checker:
  "collision {0..} \<longleftrightarrow>
    (quadroot_in 0 (min ego.t_stop other.t_stop) (1/2 * (a\<^sub>o - a\<^sub>e)) (v\<^sub>o - v\<^sub>e) (s\<^sub>o - s\<^sub>e)) \<or>
    (quadroot_in ego.t_stop other.t_stop (1/2 * a\<^sub>o) v\<^sub>o (s\<^sub>o - ego.s_stop)) \<or>
    (quadroot_in other.t_stop ego.t_stop (1/2 * a\<^sub>e) v\<^sub>e (s\<^sub>e - other.s_stop))"
 (is "_ \<longleftrightarrow> ?q1 \<or> ?q2 \<or> ?q3")
proof -
  have *: "{0..max ego.t_stop other.t_stop} =
    {0 .. min ego.t_stop other.t_stop} \<union> {ego.t_stop .. other.t_stop} \<union> {other.t_stop .. ego.t_stop}"
    using ego.t_stop_nonneg other.t_stop_nonneg
    by auto
  have "collision {0..min (movement.t_stop a\<^sub>e v\<^sub>e) (movement.t_stop a\<^sub>o v\<^sub>o)} = ?q1"
    by (force simp: collision_def quadroot_in_def root_in_def d_def
      power2_eq_square field_split_simps movement.p_def movement.s_cond_def)
  moreover
  have "collision {ego.t_stop .. other.t_stop} = ?q2"
    using ego.t_stop_nonneg
    by (force simp: collision_def quadroot_in_def root_in_def d_def
      ego.s_eq_s_stop movement.s_cond_def movement.p_def)
  moreover
  have "collision {other.t_stop .. ego.t_stop} = ?q3"
    using other.t_stop_nonneg
    by (force simp: collision_def quadroot_in_def root_in_def d_def
      other.s_eq_s_stop movement.s_cond_def movement.p_def)
  ultimately
  show ?thesis
    unfolding collision_restrict * collision_union
    by auto
qed

end

subsection \<open>Checker Design\<close>

definition rel_dist_to_stop :: "real \<Rightarrow> real \<Rightarrow> real" where
  "rel_dist_to_stop v a \<equiv> - v\<^sup>2 / (2 * a)"

context includes floatarith_notation begin
definition rel_dist_to_stop_expr :: "nat \<Rightarrow> nat \<Rightarrow> floatarith" where
  "rel_dist_to_stop_expr v a = Mult (Minus (Power (Var v) 2)) (Inverse (Mult (Num 2) (Var a)))"

definition rel_dist_to_stop' :: "nat \<Rightarrow> float interval option \<Rightarrow> float interval option \<Rightarrow> float interval option" where
  "rel_dist_to_stop' p v a = approx p (rel_dist_to_stop_expr 0 1) [v, a]"

lemma rel_dist_to_stop': "interpret_floatarith (rel_dist_to_stop_expr 0 1) [v, a] = rel_dist_to_stop v a"
  by (simp add: rel_dist_to_stop_def rel_dist_to_stop_expr_def inverse_eq_divide)

definition first_safe_dist :: "real \<Rightarrow> real \<Rightarrow> real" where
  "first_safe_dist v\<^sub>e a\<^sub>e \<equiv> rel_dist_to_stop v\<^sub>e a\<^sub>e"

definition second_safe_dist :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "second_safe_dist v\<^sub>e a\<^sub>e v\<^sub>o a\<^sub>o \<equiv> rel_dist_to_stop v\<^sub>e a\<^sub>e - rel_dist_to_stop v\<^sub>o a\<^sub>o"

definition second_safe_dist_expr :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> floatarith" where
  "second_safe_dist_expr ve ae vo ao = Add (rel_dist_to_stop_expr ve ae) (Minus (rel_dist_to_stop_expr vo ao))"

definition second_safe_dist' :: "nat \<Rightarrow> float interval option \<Rightarrow> float interval option
    \<Rightarrow> float interval option \<Rightarrow> float interval option \<Rightarrow> float interval option" where
  "second_safe_dist' p v\<^sub>e a\<^sub>e v\<^sub>o a\<^sub>o = approx p (second_safe_dist_expr 0 1 2 3) [v\<^sub>e, a\<^sub>e, v\<^sub>o, a\<^sub>o]"

lemma second_safe_dist':
  "interpret_floatarith (second_safe_dist_expr 0 1 2 3) [v, a, v', a'] = second_safe_dist v a v' a'"
  by (simp add: second_safe_dist_def second_safe_dist_expr_def rel_dist_to_stop_def rel_dist_to_stop_expr_def inverse_eq_divide)

definition t_stop :: "real \<Rightarrow> real \<Rightarrow> real" where
  "t_stop v a \<equiv> - v / a"

definition t_stop_expr :: "nat \<Rightarrow> nat \<Rightarrow> floatarith" where
  "t_stop_expr v a = Minus (Mult (Var v) (Inverse (Var a)))"
end

definition s_stop :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "s_stop s v a \<equiv> s + rel_dist_to_stop v a"

definition discriminant :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "discriminant s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<equiv> (v\<^sub>o - v\<^sub>e)\<^sup>2 - 2 * (a\<^sub>o - a\<^sub>e) * (s\<^sub>o - s\<^sub>e)"

definition suff_cond_safe_dist2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "suff_cond_safe_dist2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<equiv> 
    let D2 = discriminant s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o 
    in \<not> (a\<^sub>e < a\<^sub>o \<and> v\<^sub>o < v\<^sub>e \<and> 0 \<le> D2 \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < sqrt D2
  )"

lemma less_sqrt_iff: "y \<ge> 0 \<Longrightarrow> x < sqrt y \<longleftrightarrow> (x \<ge> 0 \<longrightarrow> x\<^sup>2 < y)"
  by (smt real_le_lsqrt real_less_rsqrt real_sqrt_ge_zero)

lemma suff_cond_safe_dist2_code[code]:
  "suff_cond_safe_dist2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o =
    (let D2 = discriminant s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o in
      (a\<^sub>e < a\<^sub>o \<longrightarrow> v\<^sub>o < v\<^sub>e \<longrightarrow> 0 \<le> D2 \<longrightarrow> (v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o \<ge> 0 \<and> (v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o)\<^sup>2 \<ge> D2)))"
  using real_sqrt_ge_zero real_less_rsqrt less_sqrt_iff
  by (auto simp: suff_cond_safe_dist2_def Let_def)
  
text \<open>
  There are two expressions for safe distance. The first safe distance \<open>first_safe_dist\<close> is always valid.
  Whenever the distance is bigger than \<open>first_safe_dist\<close>, it is guarantee to be collision free.
  The second one is \<open>second_safe_dist\<close>. If the sufficient condition \<open>suff_cond_safe_dist2\<close> is satisfied and
  the distance is bigger than \<open>second_safe_dist\<close>, it is guaranteed to be collision free.
\<close>

definition check_precond :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where 
  "check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<longleftrightarrow> s\<^sub>o > s\<^sub>e \<and> 0 \<le> v\<^sub>e \<and> 0 \<le> v\<^sub>o \<and> a\<^sub>e < 0 \<and> a\<^sub>o < 0 "

lemma check_precond_safe_distance: 
  "check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o = safe_distance a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o"
proof
  assume "safe_distance a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o"
  then interpret safe_distance a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o .
  show "check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o"
    by (auto simp: check_precond_def in_front nonneg_vel_ego other.nonneg_vel ego.decel other.decel)
qed (unfold_locales; auto simp: check_precond_def)

subsubsection \<open>Prescriptive Checker\<close>
  
definition checker :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<equiv>
    let distance   = s\<^sub>o - s\<^sub>e;
        precond    = check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o;
        safe_dist1 = first_safe_dist v\<^sub>e a\<^sub>e; 
        safe_dist2 = second_safe_dist v\<^sub>e a\<^sub>e v\<^sub>o a\<^sub>o;
        cond2      = suff_cond_safe_dist2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o 
    in precond \<and> (safe_dist1 < distance \<or> (safe_dist2 < distance \<and> distance \<le> safe_dist1 \<and> cond2))"

lemma aux_logic:
  assumes "a \<Longrightarrow> b"
  assumes "b \<Longrightarrow> a \<longleftrightarrow> c"
  shows "a \<longleftrightarrow> b \<and> c"
  using assms by blast

theorem soundness_correctness:
  "checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<longleftrightarrow> check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<and> safe_distance.no_collision a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o {0..}"
proof (rule aux_logic, simp add: checker_def Let_def)
  assume cp: "check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o"
  then have in_front': "s\<^sub>o > s\<^sub>e"
    and nonneg_vel_ego: "0 \<le> v\<^sub>e"
    and nonneg_vel_other: "0 \<le> v\<^sub>o"
    and decelerate_ego: "a\<^sub>e < 0"
    and decelerate_other: "a\<^sub>o < 0"
    by (auto simp: check_precond_def)

  from in_front' have in_front: "0 < s\<^sub>o - s\<^sub>e" by arith

  interpret safe_distance a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o by (unfold_locales; fact)
  interpret ego: braking_movement a\<^sub>e v\<^sub>e s\<^sub>e by (unfold_locales; fact)
  interpret other: braking_movement a\<^sub>o v\<^sub>o s\<^sub>o by (unfold_locales; fact)

  have "ego.p_max < s\<^sub>o \<or> other.p_max \<le> ego.p_max \<or> s\<^sub>o \<le> ego.p_max \<and> ego.p_max < other.p_max"
    by arith
  then show "checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o = safe_distance.no_collision a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o {0..}"
  proof (elim disjE)
    assume "ego.p_max < s\<^sub>o"
    then have "checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o"
      using \<open>a\<^sub>e < 0\<close> cp
      by (simp add: checker_def Let_def first_safe_dist_def rel_dist_to_stop_def ego.p_max_def
        ego.p_def ego.t_stop_def algebra_simps power2_eq_square)
    moreover
    have "no_collision {0..}"
      using \<open>ego.p_max < s\<^sub>o\<close>
      by (intro cond_1) (auto simp: ego.s_t_stop)
    ultimately show ?thesis by auto
  next
    assume "other.p_max \<le> ego.p_max"
    then have "\<not> checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o"
      using \<open>a\<^sub>e < 0\<close> \<open>a\<^sub>o < 0\<close> other.nonneg_vel
      by (auto simp add: checker_def Let_def first_safe_dist_def second_safe_dist_def
        rel_dist_to_stop_def movement.p_max_def
        movement.p_def movement.t_stop_def algebra_simps power2_eq_square)
         (smt divide_nonneg_neg mult_nonneg_nonneg)
    moreover have "collision {0..}"
      using \<open>other.p_max \<le> ego.p_max\<close>
      by (intro cond_2) (auto simp: other.s_t_stop ego.s_t_stop)
    ultimately show ?thesis by auto
  next
    assume H: "s\<^sub>o \<le> ego.p_max \<and> ego.p_max < other.p_max"
    then have "checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o = (\<not> (a\<^sub>e < a\<^sub>o \<and> v\<^sub>o < v\<^sub>e \<and> 0 \<le> D2 \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < sqrt D2))"
      using \<open>a\<^sub>e < 0\<close> \<open>a\<^sub>o < 0\<close> cp
      by (simp add: checker_def Let_def first_safe_dist_def rel_dist_to_stop_def ego.p_max_def
        ego.p_def ego.t_stop_def algebra_simps power2_eq_square second_safe_dist_def
        suff_cond_safe_dist2_def discriminant_def not_less other.p_max_def other.p_def other.t_stop_def)
    also have "\<dots> = no_collision {0..}"
      using H
      unfolding Not_eq_iff
      by (intro cond_3[symmetric]) (auto simp: ego.s_t_stop other.s_t_stop)
    finally show ?thesis by auto
  qed
qed

definition checker2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "checker2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<equiv> 
    let distance   = s\<^sub>o - s\<^sub>e;
        precond    = check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o;
        safe_dist1 = first_safe_dist v\<^sub>e a\<^sub>e; 
        safe_dist2 = second_safe_dist v\<^sub>e a\<^sub>e v\<^sub>o a\<^sub>o;
        safe_dist3 = - rel_dist_to_stop (v\<^sub>o - v\<^sub>e) (a\<^sub>o - a\<^sub>e) 
    in
      if \<not> precond then False 
      else if distance > safe_dist1 then True 
      else if a\<^sub>o > a\<^sub>e \<and> v\<^sub>o < v\<^sub>e \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < 0 then distance > safe_dist3
      else distance > safe_dist2"

theorem checker_eq_checker2: "checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<longleftrightarrow> checker2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o"
proof (cases "check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o")
  case False
  with checker_def checker2_def
  show ?thesis by auto
next
  case True
  with check_precond_def safe_distance_def 
  have "safe_distance a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o"  by (simp add: check_precond_safe_distance)
  
  from this interpret safe_distance a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o by auto
  interpret ego: braking_movement a\<^sub>e v\<^sub>e s\<^sub>e by (unfold_locales; fact)
  interpret other: braking_movement a\<^sub>o v\<^sub>o s\<^sub>o by (unfold_locales; fact)

  from \<open>check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o\<close>  cond_3 cond_3'[symmetric] fst_leq_snd_safe_distance
  ego.s_t_stop ego.p_max_def ego.p_def ego.t_stop_def hyps other.s_t_stop other.p_max_def other.p_def 
  other.t_stop_def checker2_def checker_def suff_cond_safe_dist2_def fst_safe_distance_def 
  first_safe_dist_def snd_safe_distance_def second_safe_dist_def rel_dist_to_stop_def discriminant_def 
  show ?thesis
    by (auto simp add:power_def Let_def split: if_splits)
qed

definition checker3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "checker3 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<equiv> 
    let distance = s\<^sub>o - s\<^sub>e;
        precond  = check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o;
        s_stop_e = s\<^sub>e + rel_dist_to_stop v\<^sub>e a\<^sub>e;
        s_stop_o = s\<^sub>o + rel_dist_to_stop v\<^sub>o a\<^sub>o 
    in precond \<and> (s_stop_e < s\<^sub>o 
               \<or> (s\<^sub>o \<le> s_stop_e \<and> s_stop_e < s_stop_o \<and>
                 (\<not>(a\<^sub>o > a\<^sub>e \<and> v\<^sub>o < v\<^sub>e \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o < 0 \<and> distance * (a\<^sub>o - a\<^sub>e) \<le> (v\<^sub>o - v\<^sub>e)\<^sup>2 / 2))))"

theorem checker2_eq_checker3:
  "checker2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<longleftrightarrow> checker3 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o"
  apply (auto simp: checker2_def checker3_def Let_def first_safe_dist_def not_less
    suff_cond_safe_dist2_def second_safe_dist_def rel_dist_to_stop_def check_precond_def)
proof goal_cases
  case 1
  then interpret safe_distance
    by unfold_locales auto
  from fst_leq_snd_safe_distance 1
  show ?case
    by (auto simp: fst_safe_distance_def snd_safe_distance_def)
next
  case 2
  then interpret safe_distance
    by unfold_locales auto
  from fst_leq_snd_safe_distance 2
  show ?case
    by (auto simp: fst_safe_distance_def snd_safe_distance_def field_split_simps)
next
  case 3
  then interpret safe_distance
    by unfold_locales auto
  from fst_leq_snd_safe_distance 3
  show ?case
    by (auto simp: fst_safe_distance_def snd_safe_distance_def field_split_simps)
qed

subsubsection \<open>Approximate Checker\<close>

lemma checker2_def': "checker2 a b c d e f = (
  let distance   = d - a;
      precond    = check_precond a b c d e f;
      safe_dist1 = first_safe_dist b c;
      safe_dist2 = second_safe_dist b c e f;
      C          = c < f \<and> e < b \<and> b * f > c * e;
      P1         = (e - b)\<^sup>2 < 2 * distance * (f - c);
      P2         = - b\<^sup>2 / c + e\<^sup>2 / f < 2 * distance
  in precond \<and> (safe_dist1 < distance \<or>
                safe_dist1 \<ge> distance \<and> (C \<and> P1 \<or> \<not>C \<and> P2)))"
  unfolding checker2_def
  by (auto simp: Let_def field_split_simps check_precond_def second_safe_dist_def
    rel_dist_to_stop_def)

lemma power2_less_sqrt_iff: "(x::real)\<^sup>2 < y \<longleftrightarrow> (y \<ge> 0 \<and> abs x < sqrt y)"
  apply (auto simp: real_less_rsqrt abs_real_def less_sqrt_iff)
   apply (meson le_less le_less_trans not_less power2_less_0)+
  done

schematic_goal checker_form: "interpret_form ?x ?y \<Longrightarrow> checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o"
  unfolding checker_eq_checker2 checker2_eq_checker3 checker3_def check_precond_def first_safe_dist_def second_safe_dist_def
    suff_cond_safe_dist2_def Let_def t_stop_def s_stop_def
    rel_dist_to_stop_def
    discriminant_def
    not_le not_less
    de_Morgan_conj
    de_Morgan_disj
    power2_less_sqrt_iff
  apply (tactic \<open>(Reification.tac @{context} @{thms interpret_form.simps interpret_floatarith.simps interpret_floatarith_divide interpret_floatarith_diff}) NONE 1\<close>)
  apply assumption
  done

context includes floatarith_notation begin                                            
definition "checker' p s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o = approx_form p
           (Conj (Conj (Less (Var (Suc (Suc 0))) (Var (Suc (Suc (Suc 0)))))
                   (Conj (LessEqual (Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) (Var (Suc (Suc (Suc (Suc (Suc 0)))))))
                     (Conj (LessEqual (Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) (Var (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))
                       (Conj (Less (Var 0) (Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))
                         (Less (Var (Suc 0)) (Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))
             (Disj (Less (Add (Var (Suc (Suc 0)))
                           (Mult (Minus (Power (Var (Suc (Suc (Suc (Suc (Suc 0)))))) 2)) (Inverse (Mult (Var (Suc (Suc (Suc (Suc 0))))) (Var 0)))))
                     (Var (Suc (Suc (Suc 0)))))
               (Conj (LessEqual (Var (Suc (Suc (Suc 0))))
                       (Add (Var (Suc (Suc 0)))
                         (Mult (Minus (Power (Var (Suc (Suc (Suc (Suc (Suc 0)))))) 2)) (Inverse (Mult (Var (Suc (Suc (Suc (Suc 0))))) (Var 0))))))
                 (Conj (Less (Add (Var (Suc (Suc 0)))
                               (Mult (Minus (Power (Var (Suc (Suc (Suc (Suc (Suc 0)))))) 2)) (Inverse (Mult (Var (Suc (Suc (Suc (Suc 0))))) (Var 0)))))
                         (Add (Var (Suc (Suc (Suc 0))))
                           (Mult (Minus (Power (Var (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) 2))
                             (Inverse (Mult (Var (Suc (Suc (Suc (Suc 0))))) (Var (Suc 0)))))))
                   (Disj (LessEqual (Var (Suc 0)) (Var 0))
                     (Disj (LessEqual (Var (Suc (Suc (Suc (Suc (Suc 0)))))) (Var (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))
                       (Disj (LessEqual (Var (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))
                               (Add (Var (Suc (Suc (Suc (Suc (Suc 0))))))
                                 (Minus (Mult (Mult (Var 0) (Inverse (Var (Suc 0)))) (Var (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))
                         (Less (Mult (Power (Add (Var (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) (Minus (Var (Suc (Suc (Suc (Suc (Suc 0)))))))) 2)
                                 (Inverse (Var (Suc (Suc (Suc (Suc 0)))))))
                           (Mult (Add (Var (Suc (Suc (Suc 0)))) (Minus (Var (Suc (Suc 0))))) (Add (Var (Suc 0)) (Minus (Var 0))))))))))))
  ([a\<^sub>e, a\<^sub>o, s\<^sub>e, s\<^sub>o, Interval' (Float 2 0) (Float 2 0), v\<^sub>e, v\<^sub>o, Interval' (Float 0 1) (Float 0 1)]) (replicate 8 0)"

lemma less_Suc_iff_disj: "i < Suc x \<longleftrightarrow> i = x \<or> i < x"
  by auto

lemma checker'_soundness_correctness:
  assumes "a \<in> {real_of_float al .. real_of_float au}"
  assumes "b \<in> {real_of_float bl .. real_of_float bu}"
  assumes "c \<in> {real_of_float cl .. real_of_float cu}"
  assumes "d \<in> {real_of_float dl .. real_of_float du}"
  assumes "e \<in> {real_of_float el .. real_of_float eu}"
  assumes "f \<in> {real_of_float fl .. real_of_float fu}"
  assumes chk: "checker' p (Interval' al au) (Interval' bl bu) (Interval' cl cu) (Interval' dl du) (Interval' el eu) (Interval' fl fu)"
  shows "checker a b c d e f"
  apply (rule checker_form)
  apply (rule approx_form_aux)
   apply (rule chk[unfolded checker'_def])
  using assms(1-6)
  unfolding bounded_by_def
proof (auto split: option.splits)
  fix i x2
  assume *: "[Interval' cl cu, Interval' fl fu, Interval' al au, Interval' dl du, 
           Interval' (Float 2 0) (Float 2 0), Interval' bl bu, Interval' el eu, Interval' 0 0] ! i = Some x2"
  assume " i < Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
  then consider "i = 0" | "i = 1" | "i = 2" | "i = 3" | "i = 4" | "i = 5" | "i = 6" | "i = 7"
    by linarith
  thus " [c, f, a, d, 2, b, e, 0] ! i \<in>\<^sub>r x2"
    apply cases using assms(1-6) *
    by (auto intro!: in_real_intervalI dest!: Interval'_eq_Some)
qed
    
lemma approximate_soundness_correctness:
  assumes "a \<in> {real_of_float al .. real_of_float au}"
  assumes "b \<in> {real_of_float bl .. real_of_float bu}"
  assumes "c \<in> {real_of_float cl .. real_of_float cu}"
  assumes "d \<in> {real_of_float dl .. real_of_float du}"
  assumes "e \<in> {real_of_float el .. real_of_float eu}"
  assumes "f \<in> {real_of_float fl .. real_of_float fu}"
  assumes chk: "checker' p (Interval' al au) (Interval' bl bu) (Interval' cl cu) (Interval' dl du) (Interval' el eu) (Interval' fl fu)"
  shows checker'_precond: "check_precond a b c d e f"
    and checker'_no_collision: "safe_distance.no_collision c b a f e d  {0..}"
  unfolding atomize_conj
  apply (subst soundness_correctness[symmetric])
  using checker'_soundness_correctness[OF assms]
  by (auto simp: checker_def Let_def)

subsubsection \<open>Symbolic Checker\<close>

definition symbolic_checker :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "symbolic_checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<equiv>
    let e_stop = - v\<^sub>e / a\<^sub>e;
        o_stop = - v\<^sub>o / a\<^sub>o
    in check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<and>
       (\<not>quadroot_in 0 (min e_stop o_stop) (1/2 * (a\<^sub>o - a\<^sub>e)) (v\<^sub>o - v\<^sub>e) (s\<^sub>o - s\<^sub>e) \<and>
       \<not>quadroot_in e_stop o_stop (1/2 * a\<^sub>o) v\<^sub>o (s\<^sub>o - movement.p a\<^sub>e v\<^sub>e s\<^sub>e e_stop) \<and>
       \<not>quadroot_in o_stop e_stop (1/2 * a\<^sub>e) v\<^sub>e (s\<^sub>e - movement.p a\<^sub>o v\<^sub>o s\<^sub>o o_stop))"

theorem symbolic_soundness_correctness:
  "symbolic_checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<longleftrightarrow> check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<and> safe_distance.no_collision a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o {0..}"
proof -
  {
    assume c: "check_precond s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o"
    then interpret safe_distance a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o
      by (simp add: check_precond_safe_distance)
    have "symbolic_checker s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o = no_collision {0..}"
      using c
      unfolding symbolic_checker symbolic_checker_def ego.s_t_stop other.s_t_stop ego.p_max_def other.p_max_def
      by (auto simp: Let_def movement.t_stop_def)
  }
  then show ?thesis
    by (auto simp: symbolic_checker_def Let_def)
qed
end

end