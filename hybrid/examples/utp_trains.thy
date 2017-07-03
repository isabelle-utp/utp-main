section {* Train Hybrid System *}

theory utp_trains
  imports 
    "../utp_hybrid"
    "~~/src/HOL/Decision_Procs/Approximation"
begin recall_syntax

subsection {* Constants *}
  
abbreviation "max_speed :: real \<equiv> 4.16"
abbreviation "normal_accel :: real \<equiv> 0.25"
abbreviation "normal_deceleration :: real \<equiv> -1.4"
  
abbreviation "track1_length \<equiv> 100"
  
subsection {* State-space *}
  
alphabet cst_train =
  accel :: real -- {* Acceleration *}
  vel   :: real -- {* Velocity *}
  pos   :: real -- {* Position *}
    
setup_lifting type_definition_cst_train_ext
  
text {* Proof that the state-space is a T2 topological space. *}
  
instantiation cst_train_ext :: (t2_space) t2_space
begin
  lift_definition open_cst_train_ext :: "'a cst_train_scheme set \<Rightarrow> bool" is "open" .
  instance by (intro_classes, (transfer, auto simp add: separation_t2)+)
end

lemma continuous_Rep_cst_train_ext [continuous_intros]:
  "continuous_on UNIV Rep_cst_train_ext"
  by (metis continuous_on_open_vimage image_vimage_eq open_Int open_UNIV open_cst_train_ext.rep_eq)

text {* All three variable lenses are continuous *}
    
lemma continuous_get_accel [continuous_intros]: "continuous_on UNIV get\<^bsub>accel\<^esub>"
  by (simp add: lens_defs cst_train.select_defs iso_tuple_fst_def tuple_iso_tuple_def 
      cst_train_ext_Tuple_Iso_def Topological_Spaces.continuous_on_fst continuous_Rep_cst_train_ext)

lemma continuous_get_vel [continuous_intros]: "continuous_on UNIV get\<^bsub>vel\<^esub>"
  by (simp add: lens_defs cst_train.select_defs iso_tuple_fst_def iso_tuple_snd_def tuple_iso_tuple_def 
      cst_train_ext_Tuple_Iso_def Topological_Spaces.continuous_on_snd Topological_Spaces.continuous_on_fst continuous_Rep_cst_train_ext)

lemma continuous_get_pos [continuous_intros]: "continuous_on UNIV get\<^bsub>pos\<^esub>"
  by (simp add: lens_defs cst_train.select_defs iso_tuple_fst_def iso_tuple_snd_def tuple_iso_tuple_def 
      cst_train_ext_Tuple_Iso_def Topological_Spaces.continuous_on_snd Topological_Spaces.continuous_on_fst continuous_Rep_cst_train_ext)
  
subsection {* Differential Equations and Solutions *}
  
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
  
lemma train_sol: 
  "\<langle>{&accel,&vel,&pos} \<bullet> \<guillemotleft>train_ode\<guillemotright>\<rangle>\<^sub>h = 
    {&accel,&vel,&pos} \<leftarrow>\<^sub>h \<guillemotleft>train_sol\<guillemotright>((&accel,&vel,&pos)\<^sub>u)\<^sub>a(\<guillemotleft>time\<guillemotright>)\<^sub>a"
    apply (subst ode_solution[where \<F>="train_sol"])
    apply (simp add: lens_indep_sym plus_vwb_lens)
    apply (rule allI)
    apply (rule allI)
    apply (rule impI)
    apply (rename_tac x l)
    apply (case_tac x)
    apply (simp only:)
    apply (rule train_ode_uniq_sol, simp)
    apply (simp)
    apply (rel_auto)
done
            
subsection {* Braking train scenario *}
  
definition 
"BrakingTrain = 
   \<^bold>c:accel, \<^bold>c:vel, \<^bold>c:pos := \<guillemotleft>normal_deceleration\<guillemotright>, \<guillemotleft>max_speed\<guillemotright>, \<guillemotleft>0\<guillemotright> ;; 
   \<langle>{&accel,&vel,&pos} \<bullet> \<guillemotleft>train_ode\<guillemotright>\<rangle>\<^sub>h until\<^sub>h ($vel\<acute> \<le>\<^sub>u 0) ;; \<^bold>c:accel := 0"
  
theorem braking_train_pos_le:
 "($\<^bold>c:accel\<acute> =\<^sub>u 0 \<and> \<lceil>$pos\<acute> <\<^sub>u 44\<rceil>\<^sub>h) \<sqsubseteq> BrakingTrain" (is "?lhs \<sqsubseteq> ?rhs")
proof -
  -- {* Solve ODE, replacing it with an explicit solution: @{term train_sol}. *}
  have "?rhs =
    \<^bold>c:accel, \<^bold>c:vel, \<^bold>c:pos := \<guillemotleft>-1.4\<guillemotright>, \<guillemotleft>4.16\<guillemotright>, \<guillemotleft>0\<guillemotright> ;; 
    {&accel,&vel,&pos} \<leftarrow>\<^sub>h \<guillemotleft>train_sol\<guillemotright>(&accel,&vel,&pos)\<^sub>a(\<guillemotleft>time\<guillemotright>)\<^sub>a until\<^sub>h ($vel\<acute> \<le>\<^sub>u 0) ;; 
    \<^bold>c:accel := 0"
  by (simp only: BrakingTrain_def train_sol)
  -- {* Set up initial values for the ODE solution using assigned variables. *}
  also have "... = 
    {&accel,&vel,&pos} \<leftarrow>\<^sub>h \<guillemotleft>train_sol(-1.4,4.16,0)(time)\<guillemotright> until\<^sub>h ($vel\<acute> \<le>\<^sub>u 0) ;; \<^bold>c:accel := 0"
  by (simp add: assigns_r_comp usubst unrest alpha, literalise, simp)
  also have "... =
    (({&accel,&vel,&pos} \<leftarrow>\<^sub>h(\<guillemotleft>416/140\<guillemotright>) \<guillemotleft>train_sol(-1.4,4.16,0)(time)\<guillemotright>)) ;; \<^bold>c:accel := 0"
    apply (literalise)
    apply (subst hUntil_solve[of _ "416/140"])
    apply (simp_all add: usubst unrest)
    apply (force intro: continuous_intros)
    apply (force intro: continuous_intros)
    apply (pred_auto)
  done
  also have "?lhs \<sqsubseteq> ..."
  proof (rel_simp)
    fix tr tr' :: "'a cst_train_scheme ttrace" and t::real
    assume "end\<^sub>t (tr' - tr) * 35 = 104" "0 \<le> t" "t < end\<^sub>t (tr' - tr)"
    hence "t \<in> {0..416/140}"
      by auto
    thus "104 * t / 25 - 7 * t\<^sup>2 / 10 < 44"
      by (approximation 4)
  qed
  finally show ?thesis .
qed
      
end