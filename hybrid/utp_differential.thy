section {* Differential Equations and their solutions *}

theory utp_differential
  imports utp_hyrel
begin

type_synonym 'c ODE = "real \<Rightarrow> 'c \<Rightarrow> 'c"

text {* An ordinary differential equation, @{typ "'c ODE"} is Isabelle is specified as a function
  from a real number, denoting the present time, and the continuous state @{typ "'c"} to the
  continuous state. Intuitively, the input @{typ "'c"} is the present value of the continuous
  variables, and that output @{typ "'c"} gives the derivative, that is the rate at which
  the continuous state is changing. For example, the ODE $\dot{x} = 5 \cdot x$, which states
  that $x$ is changing at a rate of $5 \cdot x$, is written in Isabelle as
  @{term "\<lambda> (t::real) (x::real). 5 * x"}. Of course we can only quantify this for certain kinds of
  type @{typ "'c"} and so we will usually require that @{typ "'c"} is a vector of real numbers,
  or some isomorphic structure. For more information on ODEs in Isabelle, please see~\cite{Immler2012}
  for a paper on an Isabelle analysis library for ODEs that this work depends on.
  *}

abbreviation hasDerivAt ::
  "((real \<Rightarrow> 'c :: real_normed_vector), '\<alpha>) uexpr \<Rightarrow>
   ('c ODE, '\<alpha>) uexpr \<Rightarrow>
   (real, '\<alpha>) uexpr \<Rightarrow>
   (real, '\<alpha>) uexpr \<Rightarrow> '\<alpha> upred" ("_ has-deriv _ at _ < _" [90, 0, 0, 91] 90)
where "hasDerivAt \<F> \<F>' \<tau> l \<equiv>
       qtop (\<lambda> \<F> \<F>' \<tau> l. (\<F> has_vector_derivative \<F>' \<tau> (\<F> \<tau>)) (at \<tau> within {0..l})) \<F> \<F>' \<tau> l"

text {* We introduce the notation @{term "\<F> has-deriv \<F>' at t < \<tau>"} to mean that the derivative
  of a function @{term "\<F>"} is given by the ODE @{term "\<F>'"} at a point $t$ in the time domain
  $[0,\tau]$. Note, that unlike for our hybrid relational calculus we deal with ODEs over closed
  intervals; the final value at $\tau$ will correspond to the after value of the continuous
  state and justify that our timed trace is piecewise convergent. *}

definition hODE ::
  "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow>
   ('a ODE, 'c) uexpr \<Rightarrow> ('d, 'c) hyrel" where
[urel_defs]: "hODE x \<F>' = (\<^bold>\<exists> \<F>, l \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> \<^bold>\<lceil> \<guillemotleft>\<F>\<guillemotright> has-deriv \<F>' at \<guillemotleft>\<tau>\<guillemotright> < \<guillemotleft>l\<guillemotright> \<and> &x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u \<^bold>\<rceil>\<^sub>H)"

syntax
  "_hODE" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ \<bullet> _\<rangle>\<^sub>H")

translations
  "_hODE a P" == "CONST hODE a P"

text {* We next introduce the construct @{term "\<langle>x \<bullet> \<F>'\<rangle>\<^sub>H"}, which states that continuous state lens
  $x$ evolves according the ODE described by @{term "\<F>'"}. The lens $x$ identifies a portion of
  the continuous state; that is it is not necessary that this construct define evolution for
  all continuous variables, only those specified. The others will evolve arbitrarily. The definition states that there is a function
  @{term "\<F>"} and evolution length @{term "l"}, such that at each instant $\tau$ in the time
  domain, @{term "\<F>'"} is the derivative @{term "\<F>"} and the continuous state $x$ is given by
  @{term "\<F>"}. Function @{term "\<F>"} is thus the solution of the ODE, and the definition states
  that such a solution exists. This actually may not always be the case, and if not such solution
  exists then the predicate will have the value @{term "false"}, the miraculous program. Note
  that since we use the hybrid interval operator here, the ODE will automatically pick up its
  initial value from the before value of $x$; thus an initial value problem is posed by this
  construct. Moreover, the final value of $x$ will be the value that the ODE tends toward at
  the limit, which is always defined as per our previous definition. *}

abbreviation hODE_IVP ("\<langle>_ := _ \<bullet> _\<rangle>\<^sub>H") where
"\<langle>x := x\<^sub>0 \<bullet> \<F>'\<rangle>\<^sub>H \<equiv> (\<^bold>c:x := x\<^sub>0 ;; \<langle>x \<bullet> \<F>'\<rangle>\<^sub>H)"

text {* We also set up notation that explicitly sets up the initial value for the continuous state,
  @{term "\<langle>x := x\<^sub>0 \<bullet> \<F>'\<rangle>\<^sub>H"}, which states that the initial value of @{term "x"} in the ODE
  @{term "\<F>'"} takes its value from @{term "x\<^sub>0"}. We next prove some important theorems about
  solutions to ODEs. *}

lemma at_left_from_zero:
  "n > 0 \<Longrightarrow> at_left n = at n within {0::real ..< n}"
  by (rule at_within_nhd[of _ "{0<..<n+1}"], auto)

lemma at_has_deriv [simp]:
  "(f has-deriv f' at \<tau> < l) @\<^sub>u t = (f @\<^sub>u t) has-deriv (f' @\<^sub>u t) at (\<tau> @\<^sub>u t) < (l @\<^sub>u t)"
  by (simp add: at_def usubst alpha)

lemma ivp_solution_refine:
  "\<lbrakk> vwb_lens x;
     continuous_on UNIV get\<^bsub>x\<^esub>;
     \<forall> l > 0. (\<F> usolves_ode \<F>' from 0) {0..l} UNIV;
     \<F>(0) = x\<^sub>0 \<rbrakk>
   \<Longrightarrow> \<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H \<sqsubseteq> (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H)"
proof (rel_auto)
  fix x :: "'a \<Longrightarrow> 'b" and \<F>' \<F> tr b tr' v
  assume assms:
    "vwb_lens x" "continuous_on UNIV get\<^bsub>x\<^esub>" "\<forall>l>0. (\<F> usolves_ode \<F>' from 0) {0..l} UNIV"
    "tr < tr'" "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = \<F> t"
    "put\<^bsub>x\<^esub> b v = \<langle>tr'\<rangle>\<^sub>t(end\<^sub>t tr)"

  let ?l = "end\<^sub>t (tr' - tr)"

  have etr_nz: "?l > 0"
    by (metis assms less_le minus_zero_eq tt_end_0_iff tt_end_ge_0)

  have tr_f: "\<forall>t. 0 \<le> t \<and> t < ?l \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr' - tr\<rangle>\<^sub>t) t = \<F> t"
    by (simp add: assms less_imp_le)

  from assms(1,5,6) etr_nz show F_0: "put\<^bsub>x\<^esub> b (\<F> 0) = \<langle>tr'\<rangle>\<^sub>t (end\<^sub>t tr)"
    apply (drule_tac x="0" in spec)
    apply (simp)
    apply (drule_tac sym)
    apply (simp)
  done

  obtain L where L:"(\<langle>tr' - tr\<rangle>\<^sub>t \<longlongrightarrow> L) (at ?l within {0..<?l})"
    using at_left_from_zero etr_nz ttrace_convergent_end by fastforce

  hence "((get\<^bsub>x\<^esub> \<circ> \<langle>tr' - tr\<rangle>\<^sub>t) \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at ?l within {0..<?l})"
    apply (simp add: comp_def)
    apply (rule continuous_on_tendsto_compose[of UNIV "get\<^bsub>x\<^esub>"])
    apply (simp_all add: assms)
  done

  moreover have "((get\<^bsub>x\<^esub> \<circ> \<langle>tr' - tr\<rangle>\<^sub>t) \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at ?l within {0..<?l})
                 \<longleftrightarrow>
                 (\<F> \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at ?l within {0..<?l})"
    using tr_f by (rule_tac Lim_cong_within, auto)

  moreover have "(\<F> \<longlongrightarrow> \<F> (end\<^sub>t (tr' - tr))) (at ?l within {0..<?l})"
  proof -
    have "continuous_on {0..end\<^sub>t(tr'-tr)} \<F>"
    proof -
      have 1:"(\<F> solves_ode \<F>') {0..?l} UNIV"
        using assms(3) etr_nz usolves_odeD(1) by blast
      show ?thesis
        by (rule solves_ode_continuous_on[OF 1])
    qed
    thus ?thesis
      by (simp add: etr_nz at_left_from_zero, meson atLeastAtMost_iff atLeastLessThan_subseteq_atLeastAtMost_iff continuous_on etr_nz less_le order_refl tendsto_within_subset)
  qed

  ultimately have "get\<^bsub>x\<^esub> L = \<F> (end\<^sub>t (tr' - tr))"
    by (metis at_left_from_zero etr_nz tendsto_Lim trivial_limit_at_left_real)

  have sol: "(\<F> usolves_ode \<F>' from 0) {0..end\<^sub>t (tr' - tr)} UNIV"
    using assms etr_nz by blast

  with etr_nz assms show
    "\<exists> f. \<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow>
            (f has_vector_derivative \<F>' t (f t)) (at t within {0..?l}) \<and> \<F> t = f t"
  proof (rule_tac x="\<F>" in exI, safe)
    fix t
    assume t: "0 \<le> t" "t < end\<^sub>t (tr' - tr)"

    show "(\<F> has_vector_derivative \<F>' t (\<F> t)) (at t within {0..?l})"
      using sol t
      by (auto simp add: usolves_ode_from_def solves_ode_def has_vderiv_on_def)
  qed
qed

text {* Theorem @{thm [source] ivp_solution_refine} how the specification of an ODE with given initial
  condition @{term "\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H"} can be refined to its solution. We require that the
  continuous state in @{term x} is a very well-behaved lens, and
  moreover that its get function is continuous. The latter assumption is necessary to ensure
  continuity between the entire continuous state and the portion described by $x$. Usually
  this will be the case since $x$ should identify a subset of the continuous variables in the
  real vector, and such a projective mapping is always continuous. The theorem also requires
  that the there exists a function @{term "\<F>"} that solves the ODE on any non-empty right closed
  interval $[0..l]$. This is specified by the notation @{term "(\<F> usolves_ode \<F>' from 0) {0..l} UNIV"}
  that is due to Immler~\cite{Immler2012,Immler2014}. Finally the theorem also requires that the value
  of the solution at time 0 corresponds to $x_0$. The continuous state $x$ is existentially
  quantified in the solution on the right hand side since the solution is closed and cannot
  be modified by changing the initial value. *}

lemma usolves_ode_subset:
  "\<lbrakk> (f usolves_ode f' from t\<^sub>0) T A; S \<subseteq> T; t\<^sub>0 \<in> S; is_interval S \<rbrakk> \<Longrightarrow> (f usolves_ode f' from t\<^sub>0) S A"
  apply (auto simp add: usolves_ode_from_def solves_ode_def has_vderiv_on_def)
  apply (meson has_vector_derivative_within_subset subset_iff)
  apply (meson dual_order.trans)
done

lemma ivp_uniq_solution_refine:
  "\<lbrakk> vwb_lens x; \<forall> l > 0. (\<F> usolves_ode \<F>' from 0) {0..l} UNIV; \<F>(0) = x\<^sub>0 \<rbrakk>
   \<Longrightarrow> (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H) \<sqsubseteq> (\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H)"
proof (rel_auto)
  fix x :: "'a \<Longrightarrow> 'b" and \<F>' \<F> tr b tr' \<G> t
  assume assms:
    "vwb_lens x" "\<forall>l>0. (\<F> usolves_ode \<F>' from 0) {0..l} UNIV"
    "tr < tr'"
    "put\<^bsub>x\<^esub> b (\<F> 0) = \<langle>tr'\<rangle>\<^sub>t (end\<^sub>t tr)"
    "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow>
         (\<G> has_vector_derivative \<F>' t (\<G> t)) (at t within {0..end\<^sub>t (tr' - tr)}) \<and>
         get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t (t + end\<^sub>t tr)) = \<G> t"
    "0 \<le> t" "t < end\<^sub>t (tr' - tr)"

  let ?l = "end\<^sub>t (tr' - tr)"

  have etr_nz: "?l > 0"
    by (metis assms less_le minus_zero_eq tt_end_0_iff tt_end_ge_0)

  have F_sol: "(\<F> usolves_ode \<F>' from 0) {0..?l} UNIV"
    using assms(2) etr_nz by (force)
      thm solution_in_cylinder.usolves_ode_on_subset
  with etr_nz have F_sol': "(\<F> usolves_ode \<F>' from 0) {0..<?l} UNIV"
    by (rule_tac usolves_ode_subset[OF F_sol], auto)

  have G_sol: "(\<G> solves_ode \<F>') {0..<?l} UNIV"
  proof (rule solves_odeI, simp_all)
    from assms(5) show "(\<G> has_vderiv_on (\<lambda>x. \<F>' x (\<G> x))) {0..<end\<^sub>t (tr' - tr)}"
      apply (auto intro: has_vector_derivative_within_subset simp add: has_vderiv_on_def)
      apply (drule_tac x="x" in spec)
      apply (auto intro: has_vector_derivative_within_subset)
    done
  qed

  from assms(1,5) etr_nz have F_G_0: "\<F>(0) = \<G>(0)"
    by (drule_tac x="0" in spec, simp_all add:assms(4)[THEN sym])

  with etr_nz show "\<G> t = \<F> t"
    by (rule_tac usolves_odeD(4)[OF F_sol', of "{0..<end\<^sub>t (tr' - tr)}"], auto simp add: G_sol assms(6,7))
qed

text {* The next theorem, @{thm [source] "ivp_uniq_solution_refine"}, shows the refinement in the
  opposite direction, that is when an ODE refines its solution. Similar assumptions are required.
  Proving the theorem in this direction effectively shows that we have a unique solution, which
  the Picard-Lindel\"{o}f theorem guarantees~\cite{Immler2012} for differential equations which
  are Lipschitz continuous. *}

theorem ivp_to_solution:
  fixes \<F> :: "real \<Rightarrow> 'a::ordered_euclidean_space"
  assumes
    "vwb_lens x"
    "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall> l > 0. (\<F> usolves_ode \<F>' from 0) {0..l} UNIV"
    "\<F>(0) = x\<^sub>0"
  shows "(\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H) = (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H)"
proof (rule antisym)
  from assms show "(\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H) \<sqsubseteq> (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H)"
    by (blast intro: ivp_solution_refine)
next
  from assms show "(\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H) \<sqsubseteq> (\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H)"
    by (rule_tac ivp_uniq_solution_refine, simp_all)
qed

text {* Finally @{thm [source] ivp_to_solution} combines the previous two theorems to produce a
  statement of equality. If we have a unique solution to a differential equation then its
  specification can be rewritten to the solution evolution. *}

theorem ivp_to_solution':
  fixes \<F> :: "real \<Rightarrow> 'a::ordered_euclidean_space"
  assumes
    "vwb_lens x"
    "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall> l > 0. (\<F> usolves_ode \<F>' from 0) {0..l} UNIV"
    "\<F>(0) = x\<^sub>0"
  shows "(\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H) = (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>(\<tau>)\<guillemotright>\<^bold>\<rceil>\<^sub>H)"
proof -
  have "(\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H) = (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>(\<tau>)\<guillemotright>\<^bold>\<rceil>\<^sub>H)"
    by (rel_auto)
  thus ?thesis
    by (subst ivp_to_solution, simp_all add: assms)
qed

lemma uos_impl_uniq_sol:
  assumes "unique_on_strip t0 T f' L" "is_interval T"
  and "(f solves_ode f') T UNIV"
shows "(f usolves_ode f' from t0) T UNIV"
proof -
  interpret uos: unique_on_strip t0 T f' L
    by (simp add: assms)
  thm uos.solution_usolves_ode
  have "\<forall> t \<in> T. f t = uos.solution (f t0) t"
  proof (auto)
    fix t
    assume "t \<in> T"
    thus "f t = uos.solution (f t0) t"
      using usolves_odeD(4)[where T'="T" and z="f" and t="t", OF uos.solution_usolves_ode[of "f t0"]]
      by (simp add: assms)
  qed
  thus ?thesis
    using assms(3) uos.solution_usolves_ode usolves_ode_solves_odeI by blast
qed

text {* We next show an example of solving an ODE. *}

term "\<langle>x := \<guillemotleft>(v\<^sub>0, h\<^sub>0)\<guillemotright> \<bullet> \<guillemotleft>(\<lambda> t (v, h). (- g, v))\<guillemotright>\<rangle>\<^sub>H"

lemma gravity_ode_example:
  assumes "vwb_lens x" "continuous_on UNIV get\<^bsub>x\<^esub>"
  shows "(\<langle>x := \<guillemotleft>(v\<^sub>0, h\<^sub>0)\<guillemotright> \<bullet> \<guillemotleft>(\<lambda> t (v, h). (- g, v))\<guillemotright>\<rangle>\<^sub>H) =
         (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil> &x =\<^sub>u \<guillemotleft>(v\<^sub>0 - g * \<tau>, v\<^sub>0*\<tau> - g*(\<tau>*\<tau>) / 2 + h\<^sub>0)\<guillemotright> \<^bold>\<rceil>\<^sub>H)"
proof (rule ivp_to_solution', simp_all add: assms)
  have 1:"\<forall>l>0. unique_on_strip 0 {0..l} (\<lambda> t (v, h). (- g, v)) 1"
    by (auto, unfold_locales, auto intro!: continuous_on_Pair continuous_on_const Topological_Spaces.continuous_on_fst continuous_on_snd simp add: lipschitz_def dist_Pair_Pair prod.case_eq_if)
  have 2:"\<forall>l>0. ((\<lambda>\<tau>. (v\<^sub>0 - g * \<tau>, v\<^sub>0 * \<tau> - g * (\<tau> * \<tau>) / 2 + h\<^sub>0))
                 solves_ode (\<lambda> t (v, h). (- g, v))) {0..l} UNIV"
    apply (auto, rule solves_odeI, auto simp add: has_vderiv_on_def)
    apply (rule has_vector_derivative_eq_rhs)
    apply (rule derivative_intros)+
    apply (auto intro!: derivative_intros)
  done

  from 1 2 show "\<forall>l>0. ((\<lambda>\<tau>. (v\<^sub>0 - g * \<tau>, v\<^sub>0 * \<tau> - g * (\<tau> * \<tau>) / 2 + h\<^sub>0))
                  usolves_ode (\<lambda> t (v, h). (- g, v)) from 0) {0..l} UNIV"
    by (auto, rule_tac uos_impl_uniq_sol[where L=1], simp_all)
qed
end