section {* Hybrid Reactive Designs *}

theory utp_hrd
  imports
    utp_rea_designs
    utp_differential
begin

text {* Lenses for discrete and continous state variables *}
  
definition svar_disc :: "('a \<Longrightarrow> 'd) \<Rightarrow> ('a \<Longrightarrow> 'd \<times> 'c)" where
[upred_defs]: "svar_disc x = x ;\<^sub>L fst\<^sub>L"

definition svar_cont :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'd \<times> 'c)" where
[upred_defs]: "svar_cont x = x ;\<^sub>L snd\<^sub>L"
  
syntax
  "_svardisc" :: "svid \<Rightarrow> svid" ("d-_" [999] 999)
  "_svarcont" :: "svid \<Rightarrow> svid" ("c-_" [999] 999)

translations
  "_svardisc x" == "CONST svar_disc x"
  "_svarcont x" == "CONST svar_cont x"

definition hrdEvolve :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real \<Rightarrow> ('a, 'c) uexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs, rdes_def]: "hrdEvolve x f = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> x \<leftarrow>\<^sub>h f(time) \<diamondop> false)"

text {* Evolve according to a continuous function for a definite time length. Currently this
  duplicates the state where t = l as the pre-emption operator does as well. *}

definition hrdEvolveTil :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real, 'd \<times> 'c) uexpr \<Rightarrow> (real \<Rightarrow> ('a, 'c) uexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hrdEvolveTil x t f = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (x \<leftarrow>\<^sub>h\<le>(t) f(time)) \<diamondop> ((x \<leftarrow>\<^sub>h(t) f(time)) \<triangleleft> t >\<^sub>u 0 \<triangleright>\<^sub>R II\<^sub>r))"

syntax
  "_hrdEvolve"    :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>H _" [90,91] 90)
  "_hrdEvolveTil" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>H'(_') _" [90,0,91] 90)  
  
translations
  "_hrdEvolve a f" => "CONST hrdEvolve a (\<lambda> _time_var. f)"
  "_hrdEvolve a f" <= "CONST hrdEvolve a (\<lambda> time. f)"
  "_hrdEvolveTil a t f" => "CONST hrdEvolveTil a t (\<lambda> _time_var. f)"
  "_hrdEvolveTil a t f" <= "CONST hrdEvolveTil a t (\<lambda> time. f)"

definition hrdODE ::
  "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow>
   ('a ODE, 'c \<times> 'c) uexpr \<Rightarrow> ('d, 'c) hyrel" where
[upred_defs]: "hrdODE x \<F>' = \<^bold>R\<^sub>s(true \<turnstile> \<langle>x \<bullet> \<F>'\<rangle>\<^sub>h \<diamondop> false)"

syntax
  "_hrdODE" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ \<bullet> _\<rangle>\<^sub>H")

translations
  "_hrdODE a P" == "CONST hODE a P"

text {* Should the until construct include in the pericondition the state where the condition
  has been satisfied at the limit? Currently it does, but this means that that particular evolution
  is present both as an intermediate and also a final state. *}
  
definition hrdUntil :: "('d, 'c::t2_space) hyrel \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow> ('d,'c) hyrel"
  where [upred_defs]: 
"hrdUntil P b = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (peri\<^sub>R(P) \<and> \<lceil>\<not>b(time)\<rceil>\<^sub>h) \<diamondop> (post\<^sub>R(P) \<or> peri\<^sub>R(P) \<and> \<lceil>\<not>b(time)\<rceil>\<^sub>h \<and> rl(&\<^bold>v) \<and> $tr <\<^sub>u $tr\<acute> \<and> (\<^bold>\<exists> l \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> \<lceil>b(l)\<rceil>\<^sub>C) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d))"

definition hrdPreempt_nz ::
    "('d, 'c::t2_space) hyrel \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hrdPreempt_nz P b Q = (hrdUntil P b) ;; Q"

definition hrdPreempt ::
    "('d, 'c::t2_space) hyrel \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" ("_ [_]\<^sub>H _" [64,0,65] 64) where
[upred_defs]: "hrdPreempt P b Q = (Q \<triangleleft> (\<^bold>\<exists> l \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> \<lceil>b(l)\<lbrakk>$\<^bold>v/$\<^bold>v\<acute>\<rbrakk>\<rceil>\<^sub>C) \<triangleright> (hrdPreempt_nz P b Q))"

syntax
  "_hrdUntil"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ until\<^sub>H _" [74,75] 74)
  "_hrdPreempt_nz" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ [_]\<^sub>H\<^sup>+ _" [64,0,65] 64)
  "_hrdPreempt"    :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ [_]\<^sub>H _" [64,0,65] 64)
  
translations
  "_hrdUntil P b" => "CONST hrdUntil P (\<lambda> _time_var. b)"
  "_hrdUntil P b" <= "CONST hrdUntil P (\<lambda> t. b)"
  "_hrdPreempt_nz P b Q" => "CONST hrdPreempt_nz P (\<lambda> _time_var. b) Q"
  "_hrdPreempt_nz P b Q" <= "CONST hrdPreempt_nz P (\<lambda> t. b) Q"
  "_hrdPreempt P b Q" => "CONST hrdPreempt P (\<lambda> _time_var. b) Q"
  "_hrdPreempt P b Q" <= "CONST hrdPreempt P (\<lambda> t. b) Q"

lemma preR_hrdEvolve [rdes]: "pre\<^sub>R(x \<leftarrow>\<^sub>H f(time)) = true\<^sub>r"
  by (rel_auto)
    
lemma periR_hrdEvolve [rdes]: "peri\<^sub>R(x \<leftarrow>\<^sub>H f(time)) = (x \<leftarrow>\<^sub>h f(time))"
  by (rel_auto)

lemma postR_hrdEvolve [rdes]: "post\<^sub>R(x \<leftarrow>\<^sub>H f(time)) = false"
  by (rel_auto)
    
lemma hrdEvolve_SRD [closure]: "x \<leftarrow>\<^sub>H f(time) is SRD"
  by (simp add: hrdEvolve_def init_cont_def closure unrest)
    
lemma hrdEvolve_NSRD [closure]: "x \<leftarrow>\<^sub>H f(time) is NSRD"
  by (rule NSRD_intro, simp_all add: init_cont_def rdes closure unrest)
    
lemma preR_hrdEvolveTil [rdes]: "pre\<^sub>R(x \<leftarrow>\<^sub>H(t) f(time)) = true\<^sub>r"
  by (rel_auto)
    
lemma periR_hrdEvolveTil [rdes]: "peri\<^sub>R(x \<leftarrow>\<^sub>H(t) f(time)) = (x \<leftarrow>\<^sub>h\<le>(t) f(time)) "
  by (rel_auto)

declare minus_zero_eq [dest]
    
lemma postR_hrdEvolveTil [rdes]: 
  "post\<^sub>R(x \<leftarrow>\<^sub>H(t) f(time)) = ((x \<leftarrow>\<^sub>h(t) f(time)) \<triangleleft> t >\<^sub>u 0 \<triangleright>\<^sub>R II\<^sub>r)"
  by (rel_auto)
    
lemma hrdEvolveTil_SRD [closure]: "x \<leftarrow>\<^sub>H(t) f(time) is SRD"
  by (simp add: hrdEvolveTil_def init_cont_def final_cont_def closure unrest)
    
lemma hrdEvolveTil_NSRD [closure]: "x \<leftarrow>\<^sub>H(t) f(time) is NSRD"
  by (rule NSRD_intro, simp_all add: init_cont_def final_cont_def rdes closure unrest)    
    
lemma preR_hrdUntil [rdes]: 
  "P is SRD \<Longrightarrow> pre\<^sub>R(P until\<^sub>H b(time)) = pre\<^sub>R(P)"
  by (simp add: hrdUntil_def rea_pre_RHS_design unrest usubst R1_R2c_is_R2 preR_R2 Healthy_if)

lemma periR_hrdUntil [rdes]: 
  "P is NSRD \<Longrightarrow> peri\<^sub>R(P until\<^sub>H b) = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R(P) \<and> \<lceil>\<not>b\<rceil>\<^sub>h)"
  by (simp add: hrdUntil_def rea_peri_RHS_design unrest usubst impl_alt_def
      NSRD_is_SRD R1_disj R1_extend_conj' R1_hInt  R2c_and R2c_disj 
      R2c_not R2c_peri_SRD R2s_hInt  R1_rea_impl R2c_preR R2c_rea_impl)

lemma postR_hrdUntil [rdes]:
  "P is NSRD \<Longrightarrow> post\<^sub>R(P until\<^sub>H b) = (pre\<^sub>R P \<Rightarrow>\<^sub>r (post\<^sub>R(P) \<or> peri\<^sub>R(P) \<and> \<lceil>\<not>b\<rceil>\<^sub>h \<and> rl(&\<^bold>v) \<and> $tr <\<^sub>u $tr\<acute> \<and> \<lceil>b\<rceil>\<^sub>C \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d))"
  apply (simp add: hrdUntil_def rea_post_RHS_design unrest usubst impl_alt_def
      NSRD_is_SRD R1_disj R1_extend_conj R1_hInt R2c_and R2c_disj 
      R2c_not R1_post_SRD R1_peri_SRD R2c_peri_SRD R2c_post_SRD R2s_hInt R2c_init_cont R2c_final_cont
      R1_rea_impl R2c_rea_impl R2c_preR)
  apply (rel_auto)
done
    
lemma hrdUntil_SRD [closure]: "P is SRD \<Longrightarrow> P until\<^sub>H b is SRD"
  by (simp add: hrdUntil_def closure unrest)
    
lemma hrdUntil_NSRD [closure]: "P is NSRD \<Longrightarrow> P until\<^sub>H b is NSRD"
  by (rule NSRD_intro, simp_all add: closure rdes unrest NSRD_neg_pre_unit)
        
lemma hrdUntil_false: 
  assumes "P is SRD"
  shows "P until\<^sub>H false = P"
proof -
  have "(peri\<^sub>R P \<and> \<lceil>true\<rceil>\<^sub>h) = peri\<^sub>R P"
    by (metis R1_extend_conj' R1_peri_SRD assms hInt_true utp_pred_laws.inf_top_right)
  thus ?thesis 
    by (simp add: hrdUntil_def alpha SRD_reactive_tri_design assms)
qed

lemma hrdUntil_true: 
  assumes "P is SRD"
  shows "P until\<^sub>H true = \<^bold>R\<^sub>s(pre\<^sub>R P \<turnstile> (peri\<^sub>R P \<and> $tr\<acute> =\<^sub>u $tr) \<diamondop> (post\<^sub>R P))"
  by (simp add: hrdUntil_def hInt_false alpha, rel_auto)

lemma hrdPreempt_true:
  "P is SRD \<Longrightarrow> P [true]\<^sub>H Q = Q"
  by (simp add: hrdPreempt_def alpha usubst, rel_auto)
        
lemma hrdIntF_zero: "x \<leftarrow>\<^sub>H(0) f(time) = II\<^sub>R"
  by (simp add: hrdEvolveTil_def alpha, rel_auto)

lemma in_var_unrest_wpR [unrest]: "\<lbrakk> $x \<sharp> P; tr \<bowtie> x \<rbrakk> \<Longrightarrow> $x \<sharp> (P wp\<^sub>R Q)"
  by (simp add: wpR_def unrest R1_def rea_not_def)

lemma out_var_unrest_wpR [unrest]: "\<lbrakk> $x\<acute> \<sharp> Q; tr \<bowtie> x \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> (P wp\<^sub>R Q)"
  by (simp add: wpR_def unrest R1_def rea_not_def)
    
lemma "(x::real) > 0 \<Longrightarrow> at_left x = at x within {0 ..< x}"
  by (simp add: at_left_from_zero)
    
lemma Limit_continuous: 
  assumes "x > 0" "continuous_on {0..x::real} f"
  shows "Lim (at x within {0..<x}) f = f(x)"
proof -
  have "(f \<longlongrightarrow> f x) (at x within {0..<x})"
    by (smt assms atLeastAtMost_iff atLeastLessThan_subseteq_atLeastAtMost_iff continuous_on tendsto_within_subset)
  with assms(1) show ?thesis
    apply (rule_tac tendsto_Lim)     
    apply (auto)
    using at_left_from_zero apply force
  done
qed
    
lemma Limit_solve:
  assumes "x > 0" "continuous_on {0..x::real} g" "\<forall> x\<in>{0..<x}. f x = g x"
  shows "Lim (at x within {0..<x}) f = g(x)"
proof -
  from assms have "Lim (at x within {0..<x}) f = Lim (at x within {0..<x}) g"
    apply (simp add: Topological_Spaces.Lim_def)
    apply (rule cong[of The], auto simp add:)
    apply (clarsimp simp add: fun_eq_iff)
    apply (rule Lim_cong_within)
    apply (auto)
  done
  also have "... = g(x)"
    using Limit_continuous assms(1) assms(2) by blast  
  finally show ?thesis .
qed

lemma hrdUntil_solve:
  assumes 
    "vwb_lens x" "k > 0" "continuous_on {0..k} f" "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall> t \<in> {0..<k}. c\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = false" "c\<lbrakk>\<guillemotleft>f(k)\<guillemotright>/$x\<acute>\<rbrakk> = true"
  shows "(x \<leftarrow>\<^sub>H \<guillemotleft>f(time)\<guillemotright>) until\<^sub>H c = x \<leftarrow>\<^sub>H(\<guillemotleft>k\<guillemotright>) \<guillemotleft>f(time)\<guillemotright>"
proof (rule SRD_eq_intro, simp_all add: closure assms rdes rpred)
  from assms(5,6) show 1:"(x \<leftarrow>\<^sub>h \<guillemotleft>f time\<guillemotright> \<and> \<lceil>\<not> c\<rceil>\<^sub>h) = x \<leftarrow>\<^sub>h\<le>(\<guillemotleft>k\<guillemotright>) \<guillemotleft>f time\<guillemotright>"
    apply (fast_uexpr_transfer)
    apply (rel_simp)
    apply (safe, simp_all)
     apply (rule hUntil_lemma2[of x k _ _ c f], simp_all add: assms)
    apply (rename_tac tr b tr' t)
    apply (drule_tac x="t" in bspec)
     apply (simp_all add: assms)
    apply (metis assms(1) vwb_lens.put_eq)
  done
  from assms(2,5,6) show
    "(x \<leftarrow>\<^sub>h \<guillemotleft>f time\<guillemotright> \<and> \<lceil>\<not> c\<rceil>\<^sub>h \<and> rl(&\<^bold>v) \<and> $tr <\<^sub>u $tr\<acute> \<and> \<lceil>c\<rceil>\<^sub>C \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) = x \<leftarrow>\<^sub>h(\<guillemotleft>k\<guillemotright>) \<guillemotleft>f time\<guillemotright> \<triangleleft> 0 <\<^sub>u \<guillemotleft>k\<guillemotright> \<triangleright>\<^sub>R II\<^sub>r"
    apply (fast_uexpr_transfer)
    apply (rel_simp)
    apply (safe, simp_all)
    apply (rule hUntil_lemma3[of x], auto simp add: assms)
    apply (rename_tac tr b tr' t)
    apply (drule_tac x="t" in bspec)
     apply (simp_all add: assms)
    apply (metis assms(1) vwb_lens.put_eq)
    apply (rule hUntil_lemma4[of x k f _])
    using assms apply (simp_all)
  done
qed
  
subsection {* Stepping a Hybrid Reactive Design *}

definition hrdStepRel :: "real \<Rightarrow> ('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel" ("Step[_]\<^sub>H") where
[upred_defs]: "Step[t]\<^sub>H P = HyStep[t](peri\<^sub>R(P))"

lemma hrdStep_hrdEvolve:
  assumes "n > 0" "continuous_on {0..n} f"
  shows "Step[n]\<^sub>H(&\<^bold>v \<leftarrow>\<^sub>H \<guillemotleft>f(time)\<guillemotright>) = (\<^bold>v := \<guillemotleft>f n\<guillemotright>)"
  by (simp add: hrdStepRel_def rdes assms HyStep_hEvolve)
  
lemma tt_eq_iff_end_same:
  "\<lbrakk> s \<le> t; end\<^sub>t(s) = end\<^sub>t(t) \<rbrakk> \<Longrightarrow> s = t"
  using tt_end_minus by fastforce

lemma hrdStep_hrdEvolveAt_le:
  fixes P :: "('d, 'c::t2_space) hyrel"
  assumes "n > 0" "l \<ge> n" "continuous_on {0..n} f" "P is NSRD" "pre\<^sub>R(P) = true\<^sub>r"
  shows "Step[n]\<^sub>H(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(time)\<guillemotright> ;; P) = (\<^bold>v := \<guillemotleft>f n\<guillemotright>)"
proof -
  from assms(1,2) 
  have 1:"peri\<^sub>R(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(time)\<guillemotright> ;; P) = (&\<^bold>v \<leftarrow>\<^sub>h\<le>(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright> \<or> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright> ;; RR(peri\<^sub>R P))"
    (is "?lhs = ?rhs")
    by (simp add: hrdStepRel_def hStepRel_def rdes closure assms rpred wp Healthy_if, rel_auto)
  from assms(1,2) have "(?lhs \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> rl(&\<^bold>v) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) = (&\<^bold>v \<leftarrow>\<^sub>h\<le>(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright> \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> rl(&\<^bold>v) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"
    by (simp add: 1, rel_auto, simp add: tt_end_minus, metis eq_iff tt_eq_iff_end_same tt_sub_end)
  also from assms(1,2) have "... = &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>n\<guillemotright>) \<guillemotleft>f time\<guillemotright>"
    by (rel_auto)
  finally have "HyStep[n](?lhs) = HyStep[n](&\<^bold>v \<leftarrow>\<^sub>h \<guillemotleft>f time\<guillemotright> :: ('d, 'c) hyrel)"
    using assms(1,2) by (simp add: hStepRel_def, rel_auto)
  thus ?thesis
    by (simp add: hrdStepRel_def HyStep_hEvolve assms)
qed 
  
lemma time_length_conj_seq:
  assumes "m < n" "P is R1" "Q is R1"
  shows  "((\<^bold>l =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> P) ;; Q \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright>) = ((\<^bold>l =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> P) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-m\<guillemotright> \<and> Q))"
proof -
  from assms(1) have "((\<^bold>l =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> R1(P)) ;; R1(Q) \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright>) = ((\<^bold>l =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> R1(P)) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-m\<guillemotright> \<and> R1(Q)))"
    apply (rel_auto, simp_all add: tt_end_minus)
    using tt_end_minus apply blast+
  done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
  
lemma lim_tt_minus:
  "g < f \<Longrightarrow> lim\<^sub>t(f - g) = lim\<^sub>t f"
  by (metis diff_add_cancel_left' less_imp_le lim_tt_cat tt_end_gr_zero_iff)
  
lemma final_cont_seq_right:
  assumes "P is RR" "Q is RR"
  shows "(P ;; ($tr <\<^sub>u $tr\<acute> \<and> Q) \<and> rl(&\<^bold>v)) = P ;; ($tr <\<^sub>u $tr\<acute> \<and> Q \<and> rl(&\<^bold>v))" (is "?lhs = ?rhs")
proof -
  have "(RR(P) ;; ($tr <\<^sub>u $tr\<acute> \<and> RR(Q)) \<and> rl(&\<^bold>v)) = RR(P) ;; ($tr <\<^sub>u $tr\<acute> \<and> RR(Q) \<and> rl(&\<^bold>v))" 
    apply (rel_auto)
    apply (metis lim_tt_minus)
    apply blast
    apply (simp_all add: lim_tt_minus)
    apply (metis less_iff minus_gr_zero_iff minus_zero_eq neq_zero_impl_greater)
    apply blast 
    apply (metis le_zero_iff minus_cancel_le minus_gr_zero_iff minus_zero_eq neq_zero_impl_greater)
  done
  thus ?thesis
    by (simp add: Healthy_if assms) 
qed

lemma final_cont_seq_right_length_eq:
  assumes "P is RR" "Q is RR" "n > 0"
  shows "(P ;; (\<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> Q) \<and> rl(&\<^bold>v)) = P ;; (\<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> Q \<and> rl(&\<^bold>v))" (is "?lhs = ?rhs")
proof -
  from assms(3) have "(RR(P) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> RR(Q)) \<and> rl(&\<^bold>v)) = RR(P) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> RR(Q) \<and> rl(&\<^bold>v))" 
    apply (rel_auto)
    apply (metis lim_tt_minus)
    apply blast
    apply (simp add: lim_tt_minus)
    apply blast
    apply (simp add: lim_tt_minus)
    apply (metis less_iff minus_gr_zero_iff minus_zero_eq neq_zero_impl_greater)
    apply blast
    apply (metis le_zero_iff minus_cancel_le minus_gr_zero_iff minus_zero_eq neq_zero_impl_greater)
    apply (metis (no_types, hide_lams))
    apply (metis (mono_tags, lifting) diff_add_cancel_left' le_sum_iff less_iff)
  done
  thus ?thesis
    by (simp add: Healthy_if assms) 
qed
        
lemma hrdStep_hrdEvolveAt_lemma1:
  assumes "0 < l" "l < n"  
  shows "(\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> rl(&\<^bold>v)) = (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a))"
  using assms
  apply (rel_auto)
  using tt_end_gr_zero_iff by fastforce+
  
lemma hrdStep_hrdEvolveAt_greater:
  fixes P :: "('d, 'c::t2_space) hyrel"
  assumes "0 < l" "l < n" "continuous_on {0..n} f" "P is NSRD" "pre\<^sub>R(P) = true\<^sub>r"
  shows "Step[n]\<^sub>H(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(time)\<guillemotright> ;; P) = (\<^bold>v := \<guillemotleft>f n\<guillemotright> ;; Step[n-l]\<^sub>H(P))"
proof -
  from assms(1,2)
  have 1:"peri\<^sub>R(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(time)\<guillemotright> ;; P) = (&\<^bold>v \<leftarrow>\<^sub>h\<le>(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright> \<or> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright> ;; RR(peri\<^sub>R P))"
    (is "?lhs = ?rhs")
    by (simp add: hrdStepRel_def hStepRel_def rdes closure assms rpred wp Healthy_if, rel_auto)
  from assms(1,2) 
  have "(?lhs \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> rl(&\<^bold>v) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) = 
        (((\<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright>) ;; RR(peri\<^sub>R P) \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright>) \<and> rl(&\<^bold>v) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"
    by (simp add: 1, rel_auto)
  also from assms(1,2) 
  have "... = ((\<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> RR(peri\<^sub>R P)) \<and> rl(&\<^bold>v) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"
    by (subst time_length_conj_seq, simp_all add: assms closure) 
  also
  have "... = (((\<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> RR(peri\<^sub>R P)) \<and> rl(&\<^bold>v)) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"
    by (simp add: conj_assoc)
  also from assms(1-2)
  have "... = ((\<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> rl(&\<^bold>v)) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"
    by (subst final_cont_seq_right_length_eq, (rel_auto)+)
  also
  have "... = ((&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright>) ;; ((\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> rl(&\<^bold>v)) \<and> RR(peri\<^sub>R P) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d))"
    by (rel_auto)
  also
  have "... = ((&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright>) ;; ((\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a)) \<and> RR(peri\<^sub>R P) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d))"
    by (simp add: hrdStep_hrdEvolveAt_lemma1 assms)  
  also
  have "... = ((&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d))"
    by (rel_auto)
  finally 
  have "Step[n]\<^sub>H(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(time)\<guillemotright> ;; P) = 
        \<lfloor>((&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n - l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)) \<restriction>\<^sub>v (&\<^bold>c \<times> &\<^bold>c)\<rfloor>\<^sub>C"
    using assms(1-2)
    by (simp add: hrdStepRel_def hStepRel_def 1 Healthy_if closure assms, rel_auto)
  also have "... = (\<lfloor>(&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f time\<guillemotright> :: ('d, 'c::t2_space) hyrel) \<restriction>\<^sub>v (&\<^bold>c \<times> &\<^bold>c)\<rfloor>\<^sub>C) ;;\<^sub>h \<lfloor>(\<^bold>l =\<^sub>u \<guillemotleft>n - l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(\<^bold>t(\<guillemotleft>t\<guillemotright>)\<^sub>a) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) \<restriction>\<^sub>v (&\<^bold>c \<times> &\<^bold>c)\<rfloor>\<^sub>C"
    apply (rel_auto)
    apply (rename_tac tr tr' tr'' d tr''')
    apply (rule_tac x="tr" in exI)
    apply (rule_tac x="d" in exI)
    apply (rule_tac x="tr'' + (tr''' - tr')" in exI)
    apply (rule_tac x="d" in exI)    
    apply (rule_tac x="tr''" in exI)
    apply (auto)
  done
  also have "... = \<^bold>v := \<guillemotleft>f n\<guillemotright> ;;\<^sub>h \<lfloor>(\<^bold>l =\<^sub>u \<guillemotleft>n - l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> rl(&\<^bold>v) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) \<restriction>\<^sub>v (&\<^bold>c \<times> &\<^bold>c)\<rfloor>\<^sub>C"
oops
  
end