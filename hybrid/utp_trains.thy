theory utp_trains
  imports utp_hybrid
begin

alphabet cst_train =
  accel :: real
  vel   :: real
  pos   :: real

setup_lifting type_definition_cst_train_ext

instantiation cst_train_ext :: (t2_space) t2_space
begin
  lift_definition open_cst_train_ext :: "'a cst_train_scheme set \<Rightarrow> bool" is "open" .
  instance
    apply (intro_classes)
    apply (transfer, simp)
    apply (transfer, auto)
    apply (transfer, auto)
    apply (transfer, meson hausdorff)
  done
end

abbreviation train_ode :: "real \<Rightarrow> real \<times> real \<times> real \<Rightarrow> real \<times> real \<times> real" where
"train_ode \<equiv> (\<lambda> t (a, v, p). (0, a, v))"
  
abbreviation train_sol :: "(real \<times> real \<times> real) \<Rightarrow> real \<Rightarrow> real \<times> real \<times> real" where
"train_sol \<equiv> (\<lambda> (a\<^sub>0, v\<^sub>0, p\<^sub>0) t. (a\<^sub>0, v\<^sub>0 + a\<^sub>0*t, p\<^sub>0 + v\<^sub>0*t + (a\<^sub>0*t\<^sup>2) / 2))"

lemma train_ode_sol:
  "l > 0 \<Longrightarrow> (train_sol (a\<^sub>0, v\<^sub>0, p\<^sub>0) solves_ode train_ode) {0..l} UNIV"
  by ode_cert
    
lemma train_ode_uniq_sol:
  assumes "l > 0"
  shows "(train_sol (a\<^sub>0, v\<^sub>0, p\<^sub>0) usolves_ode train_ode from 0) {0..l} UNIV"
proof -
  from assms have 1:"unique_on_strip 0 {0..l} train_ode 1"
    by (unfold_locales, auto intro!: continuous_on_Pair continuous_on_const Topological_Spaces.continuous_on_fst Topological_Spaces.continuous_on_snd continuous_on_snd simp add: lipschitz_def dist_Pair_Pair prod.case_eq_if)
  from assms have 2:"((train_sol (a\<^sub>0, v\<^sub>0, p\<^sub>0)) solves_ode train_ode) {0..l} UNIV"
    by (fact train_ode_sol)
  from 1 2 show sol:"((train_sol (a\<^sub>0, v\<^sub>0, p\<^sub>0)) usolves_ode train_ode from 0) {0..l} UNIV"
    by (auto, rule_tac uos_impl_uniq_sol[where L=1], simp_all)
qed

lemma 
  "\<lceil>$pos\<acute> \<le>\<^sub>u 1000\<rceil>\<^sub>h \<sqsubseteq> (\<^bold>c:accel := (-10);; \<^bold>c:pos := 0;; \<^bold>c:vel := 120;; \<langle>{&accel,&vel,&pos} \<bullet> \<guillemotleft>train_ode\<guillemotright>\<rangle>\<^sub>h)"
proof -
  have "\<langle>{&accel,&vel,&pos} \<bullet> \<guillemotleft>train_ode\<guillemotright>\<rangle>\<^sub>h = {&accel,&vel,&pos} \<leftarrow>\<^sub>h \<guillemotleft>train_sol\<guillemotright>\<lparr>(&accel,&vel,&pos)\<^sub>u\<rparr>\<^sub>u\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u"
    apply (subst ode_solution[where \<F>="train_sol"])
       apply (simp add: lens_indep_sym plus_vwb_lens)
    apply (rule allI)
    apply (rule allI)
    apply (rule impI)
      
    apply (rename_tac a\<^sub>0 v\<^sub>0 p\<^sub>0 l)
    
      
abbreviation train_vel_ode :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> real)" where
"train_vel_ode v\<^sub>s a d \<equiv> (\<lambda> t v. (if (v < v\<^sub>s) then a else if (v > v\<^sub>s) then d else 0))"

abbreviation train_vel_sol :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "train_vel_sol v\<^sub>s a d \<equiv> (\<lambda> v\<^sub>0 \<tau>. (if (v\<^sub>0 < v\<^sub>s) then min (v\<^sub>0 + a*\<tau>) v\<^sub>s else
                                    if (v\<^sub>0 > v\<^sub>s) then max (v\<^sub>0 + d*\<tau>) v\<^sub>s else v\<^sub>s))"
  

  
lemma "\<lbrakk> l > 0; v\<^sub>s > 0; a > 0; d < 0 \<rbrakk> 
  \<Longrightarrow> (train_vel_sol v\<^sub>s a d v\<^sub>0 solves_ode train_vel_ode v\<^sub>s a d) {0..l} UNIV"
  apply (rule solves_odeI)
  apply (auto simp add: has_vderiv_on_def)
  apply (rule_tac y="(v\<^sub>s - v\<^sub>0)/d" and f="\<lambda>\<tau>. v\<^sub>0 + d * \<tau>" in has_vector_derivative_left_point)     
  apply (rule has_vector_derivative_eq_rhs)
  apply (rule derivative_intros)
  apply (rule derivative_intros)
  apply (rule derivative_intros)
  apply (rule derivative_intros)
  apply (rule derivative_intros)
  apply (auto simp add: pos_divide_less_eq neg_less_divide_eq mult.commute)
oops

end