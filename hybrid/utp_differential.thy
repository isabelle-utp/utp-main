subsection {* Differential Equations and their solutions *}

theory utp_differential
  imports utp_hyrel
begin
  
type_synonym 'c ODE = "real \<Rightarrow> 'c \<Rightarrow> 'c"

abbreviation hasDerivAt :: 
  "((real \<Rightarrow> 'c :: real_normed_vector), '\<alpha>) uexpr \<Rightarrow> 
   ('c ODE, '\<alpha>) uexpr \<Rightarrow> 
   (real, '\<alpha>) uexpr \<Rightarrow> 
   (real, '\<alpha>) uexpr \<Rightarrow> '\<alpha> upred" ("_ has-deriv _ at _ < _" [90, 0, 0, 91] 90)
where "hasDerivAt \<F> \<F>' \<tau> l \<equiv>
       qtop (\<lambda> \<F> \<F>' \<tau> l. (\<F> has_vector_derivative \<F>' \<tau> (\<F> \<tau>)) (at \<tau> within {0..l})) \<F> \<F>' \<tau> l"
    
definition hODE :: "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a ODE, 'c) uexpr \<Rightarrow> ('d, 'c) hyrel" ("\<langle>_ \<bullet> _\<rangle>\<^sub>H") where
[urel_defs]: "\<langle>x \<bullet> \<F>'\<rangle>\<^sub>H = (\<^bold>\<exists> \<F>, l \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> \<^bold>\<lceil> \<guillemotleft>\<F>\<guillemotright> has-deriv \<F>' at \<guillemotleft>\<tau>\<guillemotright> < \<guillemotleft>l\<guillemotright> \<and> &x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u \<^bold>\<rceil>\<^sub>H)"

abbreviation hODE_IVP ("\<langle>_ := _ \<bullet> _\<rangle>\<^sub>H") where
"\<langle>x := x\<^sub>0 \<bullet> \<F>'\<rangle>\<^sub>H \<equiv> (\<^bold>c:x := x\<^sub>0 ;; \<langle>x \<bullet> \<F>'\<rangle>\<^sub>H)"

lemma at_left_from_zero:
  "n > 0 \<Longrightarrow> at_left n = at n within {0::real ..< n}"
  by (rule at_within_nhd[of _ "{0<..<n+1}"], auto)
   
lemma ivp_solution_refine:
  "\<lbrakk> vwb_lens x; continuous_on UNIV get\<^bsub>x\<^esub>; \<forall> l > 0. (\<F> usolves_ode \<F>' from 0) {0..l} UNIV; \<F>(0) = x\<^sub>0 \<rbrakk> 
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

lemma "(\<^bold>\<lceil>P(\<tau>)\<^bold>\<rceil>\<^sub>H ;; \<^bold>\<lceil>P(\<tau>)\<^bold>\<rceil>\<^sub>H) = \<^bold>\<lceil>P(\<tau>)\<^bold>\<rceil>\<^sub>H"
  apply (rel_auto)
oops

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

(* Example of solving an ODE *)

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