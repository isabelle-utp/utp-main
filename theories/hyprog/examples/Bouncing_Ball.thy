section \<open> Bouncing Ball \<close>

theory Bouncing_Ball
  imports "UTP-dL.utp_hyprog"
begin

text \<open> The goal of this theory is to show that a bouncing ball, in normal circumstances, rebounds
  no higher than its initial height. \<close>

utp_lit_vars

text \<open> The state space has two continuous variables, and so we use a two-place vector to model it. \<close>

type_synonym state = "real vec[2]"

text \<open> Each continuous variable is modelled as a projection from the state space. \<close>

abbreviation h :: "real \<Longrightarrow> state" where "h \<equiv> mat_lens 0 0"
abbreviation v :: "real \<Longrightarrow> state" where "v \<equiv> mat_lens 0 1"

text \<open> The following locale creates a context for the hybrid system, which fixes a number of
  constants and provides assumptions. \<close>

locale Ball =
  fixes g :: real \<comment> \<open> Gravitational constant \<close>
  and H :: real \<comment> \<open> The initial or maximum height of the ball \<close>
  and c :: real \<comment> \<open> The damping coefficient applied upon rebound \<close>
  assumes g_pos: "g > 0" \<comment> \<open> The gravitational contant should be strictly positive (e.g. 9.81) \<close>
  and c_pos: "c > 0" \<comment> \<open> The damping coefficient is greater than 0... \<close>
  and c_le_one: "c \<le> 1" \<comment> \<open> ... and no greater than 1, otherwise it increases its bounce. \<close>
  and H_pos: "H \<ge> 0"
begin

text \<open> The dynamics encodes the simple first order system of ODEs. It specifies the derivative
  for each continuous variable, and a evolution domain $h \ge 0$. \<close>

abbreviation Dynamics :: "(state, unit) hyrel" where
"Dynamics \<equiv> ode [h \<mapsto>\<^sub>s v, v \<mapsto>\<^sub>s -g] U(&\<^bold>c:h \<ge> 0)"

text \<open> The ``controller'' implements a rebound when $h = 0$. \<close>

definition Control :: "(state, unit) hyrel" where
"Control \<equiv> if (&\<^bold>c:h = 0) then \<^bold>c:v := -c * &\<^bold>c:v fi"

text \<open> The entire system iterative executes the dynamics follows by the controller. \<close>

abbreviation "BBall \<equiv> (Dynamics ;; Control)\<^sup>\<star>"

text \<open> Here is the invariant we wish to prove: it is sufficient to show that always $h \le H$. \<close>

abbreviation "Inv \<equiv> U(&\<^bold>c:h \<ge> 0 \<and> &\<^bold>c:v\<^sup>2 \<le> 2*g*(H - &\<^bold>c:h))"

text \<open> We first prove that it is an invariant of the dynamics using Hoare logic. \<close>

lemma l1 [hoare_safe]: "\<^bold>{Inv\<^bold>}Dynamics\<^bold>{Inv\<^bold>}"
  apply (rule dCut_split) \<comment> \<open> Differential cut rule \<close>
   apply (rule dWeakening) \<comment> \<open> Differential weakening (invariant first conjunct) \<close>
  apply (simp)
  apply (dInduct, rel_auto) \<comment> \<open> Differential induction (invariant second conjunct) \<close>
  done

text \<open> Next, we prove its also an invariant of the controller. This requires a call to sledgehammer. \<close>

lemma l2 [hoare_safe]: "\<^bold>{Inv\<^bold>}Control\<^bold>{Inv\<^bold>}"
  unfolding Control_def
  apply (hoare_auto)
  by (smt c_le_one c_pos mult_left_le_one_le power2_eq_square power_mult_distrib zero_le_square)

text \<open> As a consequence, it is an invariant of the whole system. \<close>

lemma l3: "\<^bold>{Inv\<^bold>}BBall\<^bold>{Inv\<^bold>}"
  by (hoare_auto)

text \<open> We can now show the safety property we desire using the consequence rule and sledgehammer. \<close>

lemma safety_property_1:
  "\<^bold>{0 \<le> &\<^bold>c:h \<and> &\<^bold>c:v\<^sup>2 \<le> 2*g*(H - &\<^bold>c:h)\<^bold>}BBall\<^bold>{0 \<le> &\<^bold>c:h \<and> &\<^bold>c:h \<le> H\<^bold>}"
  apply (rule hoare_r_conseq[OF l3]) \<comment> \<open> Consequence rule \<close>
  apply (simp)
  apply (rel_simp)
  apply (smt g_pos power2_less_0 zero_le_mult_iff)
  done

text \<open> A more specific version -- the ball starts stationary and at height $h$. \<close>

lemma safety_property_2:
  "\<^bold>{&\<^bold>c:h = H \<and> &\<^bold>c:v = 0\<^bold>}BBall\<^bold>{0 \<le> &\<^bold>c:h \<and> &\<^bold>c:h \<le> H\<^bold>}"
  apply (rule hoare_r_conseq[OF safety_property_1])
  apply (rel_simp)
  using H_pos apply blast
  apply (rel_simp)
  done

end

end