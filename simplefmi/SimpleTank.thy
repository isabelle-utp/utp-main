theory SimpleTank
  imports 
    VDMRT
    SimpleFMI
    "../hybrid/utp_hybrid"
begin recall_syntax
  
alphabet tank_st =
  valve   :: bool
  level   :: real
  
setup_lifting type_definition_tank_st_ext
  
text {* Proof that the state-space is a T2 topological space. *}
  
instantiation tank_st_ext :: (t2_space) t2_space
begin
  lift_definition open_tank_st_ext :: "'a tank_st_scheme set \<Rightarrow> bool" is "open" .
  instance by (intro_classes, (transfer, auto simp add: separation_t2)+)
end
  
alphabet ctr_st = vrt_st +
  valveOn     :: bool
  levelSensor :: real
  
alphabet wt_st =
  tank  :: tank_st
  ctr   :: "ctr_st vrt_st_scheme"
    
definition
  "Init = [ tank:valve      \<mapsto>\<^sub>s true
          , tank:level      \<mapsto>\<^sub>s 0
          , ctr:valveOn     \<mapsto>\<^sub>s false
          , ctr:levelSensor \<mapsto>\<^sub>s 0 ]"
  
definition 
  "Wiring = [ tank:valve      \<mapsto>\<^sub>s &ctr:valveOn
            , ctr:levelSensor \<mapsto>\<^sub>s &tank:level ]"

abbreviation (input) tank_ode_1 :: "real \<Rightarrow> real \<Rightarrow> real" where
"tank_ode_1 \<equiv> (\<lambda> t l. 1)"

abbreviation (input) tank_ode_2 :: "real \<Rightarrow> real \<Rightarrow> real" where
"tank_ode_2 \<equiv> (\<lambda> t l. -1)"

abbreviation (input) tank_sol_1 :: "real \<Rightarrow> real \<Rightarrow> real" where
"tank_sol_1 \<equiv> (\<lambda> l\<^sub>0 t. l\<^sub>0 + t)"

abbreviation (input) tank_sol_2 :: "real \<Rightarrow> real \<Rightarrow> real" where
"tank_sol_2 \<equiv> (\<lambda> l\<^sub>0 t. l\<^sub>0 - t)"

method linear_ode = 
  (rule_tac uos_impl_uniq_sol[where L=1], (unfold_locales, auto intro!: continuous_on_Pair continuous_on_const Topological_Spaces.continuous_on_fst Topological_Spaces.continuous_on_snd continuous_on_snd simp add: lipschitz_def dist_Pair_Pair prod.case_eq_if)[1], (auto)[1], ode_cert)  
  
lemma tank_ode_usol_1:
  "l > 0 \<Longrightarrow> (tank_sol_1 l\<^sub>0 usolves_ode tank_ode_1 from 0) {0..l} UNIV"
  by (linear_ode)

lemma tank_ode_usol_2:
  "l > 0 \<Longrightarrow> (tank_sol_2 l\<^sub>0 usolves_ode tank_ode_2 from 0) {0..l} UNIV"
  by (linear_ode)
    
definition Tank  :: "real \<Rightarrow> tank_st trel" where 
  "Tank area = H2T((\<langle>{&level} \<bullet> tank_ode_1(ti)\<rangle>\<^sub>h \<and> level \<leftarrow>\<^sub>h $level) 
                     \<triangleleft> &valve \<triangleright>\<^sub>h 
                   (\<langle>{&level} \<bullet> tank_ode_2(ti)\<rangle>\<^sub>h \<and> level \<leftarrow>\<^sub>h $level))"

definition Ctr :: "real \<Rightarrow> real \<Rightarrow> ctr_st vrel" where
"Ctr minLevel maxLevel = 
  Periodic 0.001 (valveOn := true \<triangleleft> &levelSensor \<le>\<^sub>u \<guillemotleft>minLevel\<guillemotright> \<triangleright>\<^sub>r 
                  valveOn := false \<triangleleft> &levelSensor \<ge>\<^sub>u \<guillemotleft>maxLevel\<guillemotright> \<triangleright>\<^sub>r II)"
  
definition
  "WaterTank minLevel maxLevel area = 
     FMI Init [FMU[ctr, Ctr minLevel maxLevel], FMU[tank, Tank area]] ArbStep Wiring"

lift_definition var_all_res :: "'\<alpha> upred \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred" is
"\<lambda> P x b. \<forall> b'. P (b' \<oplus>\<^sub>L b on x)" .

syntax
  "_uvar_all_res" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\<restriction>\<^sub>\<forall>" 90)
    
translations
  "_uvar_all_res P x b" == "CONST var_all_res P x b"
  
definition pred_ares :: "'\<alpha> upred \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> upred" 
  where [upred_defs]: "pred_ares P a = (P \<restriction>\<^sub>v a) \<restriction>\<^sub>p a"
    

update_uexpr_rep_eq_thms
    
syntax
  "_pred_ares" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\<restriction>\<^sub>q" 90)

translations
  "_pred_ares P a" == "CONST pred_ares P a"
  
thm "des_vars.defs"
    
lemma fmu_hoare_rp [hoare_safe]:
  "\<lbrakk> x \<natural> p; \<lbrace>p\<restriction>\<^sub>qx\<rbrace>Q\<lbrace>p\<restriction>\<^sub>qx\<rbrace>\<^sub>r \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>FMU[x, Q]\<lbrace>p\<rbrace>\<^sub>r"
  apply (rel_simp, auto simp add: des_vars.defs rp_vars.defs)
  apply (rename_tac ok wait tr st ok' wait' tr' st')
  apply (drule_tac x="ok" in spec)
  apply (drule_tac x="wait" in spec)
  apply (drule_tac x="tr" in spec)
  apply (drule_tac x="get\<^bsub>x\<^esub> st" in spec)
  apply (drule_tac x="ok'" in spec)
  apply (drule_tac x="wait'" in spec)
  apply (drule_tac x="tr'" in spec)
  apply (drule_tac x="get\<^bsub>x\<^esub> st'" in spec)
  apply (auto)
done
        
method ode_solve 
  for sol :: "'a::ordered_euclidean_space \<Rightarrow> real \<Rightarrow> 'a" 
  = (rule_tac trans, rule_tac ode_solution'[where \<F> = "sol"], simp_all, linear_ode, rel_auto)
    
lemma tank_ode_1_evolve:
  "\<langle>&level \<bullet> tank_ode_1(ti)\<rangle>\<^sub>h = level \<leftarrow>\<^sub>h ($level + \<guillemotleft>ti\<guillemotright>)"
  by (ode_solve tank_sol_1)

lemma tank_ode_2_evolve:
  "\<langle>&level \<bullet> tank_ode_2(ti)\<rangle>\<^sub>h = level \<leftarrow>\<^sub>h ($level - \<guillemotleft>ti\<guillemotright>)"
  by (ode_solve tank_sol_2)
    
definition hFrame :: "('a \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('d, 'c) hyrel \<Rightarrow> ('d, 'c) hyrel" where
[upred_defs]: "hFrame x P = (P \<and> \<lceil>x:[true]\<rceil>\<^sub>h)"
  
syntax
  "_hFrame" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>h" [99,0] 100)

translations
  "_hFrame a P" == "CONST hFrame a P"
  
abbreviation hODE_frame ::
  "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow>
   'a ODE \<Rightarrow> ('d, 'c) hyrel" where
"hODE_frame x \<F>' \<equiv> hFrame x (hODE x \<F>')"
        
syntax
  "_hODE_frame" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ : _\<rangle>\<^sub>h")

translations
  "_hODE_frame a P" => "CONST hODE_frame a (\<lambda> _time_var. P)"
  "_hODE_frame a P" <= "CONST hODE_frame a (\<lambda> t. P)"    
  
definition hEvolves :: "(real \<Rightarrow> 'c::t2_space usubst) \<Rightarrow> ('d, 'c) hyrel" where
[upred_defs]: "hEvolves s = (\<lceil>\<langle>s(ti)\<rangle>\<^sub>a\<rceil>\<^sub>h \<and> \<^bold>l >\<^sub>u 0)"
    
syntax
  "_hEvolves" :: "logic \<Rightarrow> logic" ("{_}\<^sub>h")

translations
  "_hEvolves s" => "CONST hEvolves (\<lambda> _time_var. s)"
  "_hEvolves s" <= "CONST hEvolves (\<lambda> t. s)"
  
lemma hEvolves_id: 
  "{id}\<^sub>h = \<^bold>v \<leftarrow>\<^sub>h $\<^bold>v"
  by (rel_auto)

thm ode_solution
      
theorem ode_frame_solution:
  assumes 
    "vwb_lens x" "\<forall> x. \<forall> l > 0. (\<F>(x) usolves_ode \<F>' from 0) {0..l} UNIV" "\<forall> x. \<F>(x)(0) = x"
  shows "\<langle>x : \<F>'(ti)\<rangle>\<^sub>h = {[x \<mapsto>\<^sub>s \<guillemotleft>\<F>\<guillemotright>(&x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]}\<^sub>h"
proof -
  have "\<langle>x : \<F>'(ti)\<rangle>\<^sub>h = x:[x \<leftarrow>\<^sub>h \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]\<^sub>h"
    by (simp add: ode_solution[where \<F>=\<F>] assms)
  also from assms(1) have "... = (\<lceil>$x\<acute> =\<^sub>u \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a \<and> x:[true]\<rceil>\<^sub>h \<and> 0 <\<^sub>u \<^bold>l)"
    by (rel_auto)
  also from assms(1) have "... = (\<lceil>x:[$x\<acute> =\<^sub>u \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]\<rceil>\<^sub>h \<and> 0 <\<^sub>u \<^bold>l)"      
    by (simp add: antiframe_conj_true unrest)
  also have "... = (\<lceil>x:[$x\<acute> =\<^sub>u \<lceil>\<guillemotleft>\<F>\<guillemotright>(&x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a\<rceil>\<^sub><]\<rceil>\<^sub>h \<and> 0 <\<^sub>u \<^bold>l)"
    by (rel_auto)
  also from assms(1) have "... = {[x \<mapsto>\<^sub>s \<guillemotleft>\<F>\<guillemotright>(&x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a]}\<^sub>h"
    by (simp add: antiframe_assign hEvolves_def, rel_auto)
  finally show ?thesis .
qed
  
lemma hyrel2trel_hEvolves:
  fixes x :: "'a::t2_space \<Longrightarrow> 'c::t2_space"
  assumes "continuous_lens x" "continuous_on {0..} f"
  shows "H2T({[x \<mapsto>\<^sub>s \<guillemotleft>f(ti)\<guillemotright>]}\<^sub>h) = 
         (\<Sqinter> t | \<guillemotleft>t\<guillemotright> >\<^sub>u 0 \<bullet> wait\<^sub>r(\<guillemotleft>t\<guillemotright>) ;; x :=\<^sub>r \<guillemotleft>f(real_of_pos t)\<guillemotright>)" (is "?lhs = ?rhs")
proof -
  from assms(1) 
  have "?lhs = R1 (\<^bold>\<exists> l \<bullet> ({[x \<mapsto>\<^sub>s \<guillemotleft>f ti\<guillemotright>]}\<^sub>h \<and> end\<^sub>u(&tt) =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d :: (unit,'c) hyrel)  \<restriction>\<^sub>r &st:\<^bold>c \<oplus>\<^sub>r st \<and> &tt =\<^sub>u \<guillemotleft>mk_pos l\<guillemotright>)"
    by (simp add: hyrel2trel_def)
  also have "... = R1(\<^bold>\<exists> l \<bullet> ((x := \<guillemotleft>f(l)\<guillemotright>) \<oplus>\<^sub>r st) \<and> \<guillemotleft>l\<guillemotright> >\<^sub>u 0 \<and> &tt =\<^sub>u \<guillemotleft>mk_pos l\<guillemotright>)" (is "?P = ?Q")
  proof (rule antisym)
    show "?P \<sqsubseteq> ?Q"
      apply (rel_simp)
      apply (rename_tac tr st tr' n)
      apply (rule_tac x="n" in exI)
      apply (auto)
      apply (rule_tac x="0" in exI)
      apply (rule_tac x="tt_mk n (\<lambda> t. put\<^bsub>x\<^esub> st (f t))" in exI)
      apply (subgoal_tac "continuous_on {0..n} (put\<^bsub>x\<^esub> st \<circ> f)")
       apply (auto simp add: assms Limit_solve at_left_from_zero)[1]
       apply (rule continuous_on_compose)
       apply (meson Icc_subset_Ici_iff assms continuous_on_subset order_refl)
        apply (rule continuous_lens.put_continuous_v[OF assms(1)])
    done
    show "?Q \<sqsubseteq> ?P"
      apply (rel_simp)
      apply (rename_tac tr tr' tr'' tr''')
      apply (rule_tac x="end\<^sub>t (tr''' - tr'')" in exI)
      apply (auto)
       apply (subst Limit_solve_at_left)
          apply (auto)
       apply (subgoal_tac "continuous_on {0..end\<^sub>t (tr''' - tr'')} (put\<^bsub>x\<^esub> tr \<circ> f)")
        apply (simp)
       apply (rule continuous_on_compose)
       apply (meson Icc_subset_Ici_iff assms continuous_on_subset order_refl)
       apply (rule continuous_lens.put_continuous_v[OF assms(1)])
    done
  qed
  also have "... = ?rhs"
    apply (rel_auto)
    apply (metis le_add_diff_inverse less_eq_real_def mk_pos_less mk_pos_zero real_of_pos)
    apply (metis (full_types) approximation_preproc_push_neg(3) least_zero mk_pos.abs_eq mk_pos_real_of_pos not_le zero_pos.abs_eq)
  done
  finally show ?thesis .
qed

      
    
term "[$level \<mapsto>\<^sub>s $x]"
    
    
lemma "(\<Sigma> :: tank_st \<Longrightarrow> tank_st) \<approx>\<^sub>L level +\<^sub>L valve"
    
    
lemma "H2T(\<langle>&level \<bullet> \<lambda>lev. 1\<rangle>\<^sub>h \<triangleleft> &valve \<triangleright>\<^sub>h \<langle>&level \<bullet> \<lambda>lev. - 1\<rangle>\<^sub>h) = undefined"
  apply (simp add: hyrel2trl_cond hyrel2trel_hEvolve tank_ode_1_evolve tank_ode_2_evolve)
  thm hyrel2trel_hEvolve
    
lemma "\<lbrace>true\<rbrace>WaterTank 0 10 10\<lbrace>&tank:level <\<^sub>u 10 \<and> &ctr:levelSensor <\<^sub>u 10\<rbrace>\<^sub>r"
  apply (simp add: conj_comm conj_assoc)
  apply (simp add: WaterTank_def Ctr_def Tank_def FMI_def)
  apply (rule hoare_safe)
   apply (rule hoare_safe)
   apply (simp add: Init_def)
   apply (rel_auto)
  apply (rule hoare_safe)
  apply (rule hoare_safe)
  apply (rule hoare_safe)
    apply (rule hoare_safe)
     apply (simp add: unrest)
    apply (simp add: Periodic_def PeriodicBody_def)
    apply (rule hoare_safe)
     apply (rule hoare_safe)
     apply (rel_auto)
        apply (rel_auto)
    apply (
     apply (rule unrest)
  apply (simp add: unrest)
(*
  apply (rule hoare)
   apply (rule hoare_safe)
   apply (simp add: Init_def)
   apply (rel_auto)
oops
*)

end