section \<open> Bouncing Ball \<close>

theory utp_bouncing_ball
  imports "UTP1-Hybrid.utp_hybrid"
begin
  
subsection \<open> State-space \<close>
  
text \<open> We first setup the state-space and prove this is a topological (T2) space \<close>
  
alphabet bball =
  height :: real
  velocity :: real

setup_lifting type_definition_bball_ext

instantiation bball_ext :: (t2_space) t2_space
begin
  lift_definition open_bball_ext :: "'a bball_scheme set \<Rightarrow> bool" is "open" .
  instance by (intro_classes, (transfer, auto simp add: separation_t2)+)
end

subsection \<open> Constants \<close>
  
text \<open> Next we define some constants; the ODE (ordinary differential equation) and its solution \<close>
  
abbreviation grav :: real where
"grav \<equiv> -9.81"

subsection \<open> Differential Equations and Solutions \<close>

text \<open> The ODE specifies two continuous variables, for velocity and height respectively. It
  does not depend on time which makes it an autonomous ODE. \<close>

abbreviation grav_ode :: "(real \<times> real) ODE" where
"grav_ode \<equiv> (\<lambda> t (v, h). (- grav, v))"

text \<open> We also present the following solution to the ODE, which is a function from initial values
  of the continuous variables to a continuous function that shows how the variables change with time. \<close>

abbreviation grav_sol :: "real \<times> real \<Rightarrow> real \<Rightarrow> real \<times> real" where
"grav_sol \<equiv> \<lambda> (v\<^sub>0, h\<^sub>0) \<tau>. (v\<^sub>0 - grav * \<tau>, v\<^sub>0 * \<tau> - grav * (\<tau> * \<tau>) / 2 + h\<^sub>0)"
  
lemma grav_ode_sol:
  "(\<langle>{&velocity,&height} \<bullet> grav_ode(ti)\<rangle>\<^sub>h) = {&velocity,&height} \<leftarrow>\<^sub>h \<guillemotleft>grav_sol\<guillemotright>($velocity, $height)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a"
proof -
  have 1:"\<forall>l>0. unique_on_strip 0 {0..l} grav_ode 1"
    by (auto, unfold_locales, auto intro!: continuous_on_Pair continuous_on_const continuous_on_fst continuous_on_snd simp add: lipschitz_on_def dist_Pair_Pair prod.case_eq_if)
  have 2:"\<forall> v\<^sub>0 h\<^sub>0. \<forall>l>0. ((grav_sol (v\<^sub>0, h\<^sub>0)) solves_ode grav_ode) {0..l} UNIV"
    by (clarify, ode_cert)
  from 1 2 have sol:"\<forall> v\<^sub>0 h\<^sub>0. \<forall>l>0. ((grav_sol (v\<^sub>0, h\<^sub>0)) usolves_ode grav_ode from 0) {0..l} UNIV"
    by (auto, rule_tac uos_impl_uniq_sol[where L=1], simp_all)
  show ?thesis
    apply (subst ode_solution[where \<F>="grav_sol"])
    apply (simp_all add: lens_indep_sym)
    using sol apply (simp)
    apply (rel_auto)
  done
qed

subsection \<open> System Definition \<close>

definition bouncing_ball :: "(unit, bball) hyrel" where
  "bouncing_ball =
     (\<^bold>c:velocity, \<^bold>c:height) :=\<^sub>r (0, 2.0) ;;
      (\<langle>{&velocity,&height} \<bullet> grav_ode(ti)\<rangle>\<^sub>h until\<^sub>h ($height\<acute> \<le>\<^sub>u 0) ;;
       \<^bold>c:velocity :=\<^sub>r (- 0.8 * &\<^bold>c:velocity))\<^sup>\<star>"
  
subsection \<open> Example Properties \<close>
  
lemma "\<lceil>$height\<acute> \<ge>\<^sub>u 0\<rceil>\<^sub>h \<sqsubseteq> bouncing_ball"
  apply (simp add: bouncing_ball_def)
  apply (rule ustar_inductr)
  apply (rel_simp)
oops
  
end
