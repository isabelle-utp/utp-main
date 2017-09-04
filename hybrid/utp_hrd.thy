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
  "_svardisc" :: "svid \<Rightarrow> svid" ("c-_" [999] 999)
  "_svarcont" :: "svid \<Rightarrow> svid" ("d-_" [999] 999)

translations
  "_svardisc x" == "CONST svar_disc x"
  "_svarcont x" == "CONST svar_cont x"

definition hrdEvolve :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real \<Rightarrow> ('a, 'c) uexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hrdEvolve x f = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> x \<leftarrow>\<^sub>h f(time) \<diamondop> false)"

text {* Evolve according to a continuous function for a definite time length. Currently this
  duplicates the state where t = l as the pre-emption operator does as well. *}

definition hrdEvolveTil :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real, 'd \<times> 'c) uexpr \<Rightarrow> (real \<Rightarrow> ('a, 'c) uexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hrdEvolveTil x t f = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (0 <\<^sub>u \<^bold>l \<and> x \<leftarrow>\<^sub>h f(time) \<and> \<^bold>l \<le>\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub><) 
                                    \<diamondop> ((x \<leftarrow>\<^sub>h f(time) \<and> \<^bold>l =\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> rl(&\<Sigma>) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) 
                                        \<triangleleft> t >\<^sub>u 0 \<triangleright>\<^sub>R 
                                       ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)))"

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
  
definition hrdUntil :: "('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel \<Rightarrow> ('d,'c) hyrel" (infixl "until\<^sub>H" 85)
  where [upred_defs]: 
"P until\<^sub>H b = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (peri\<^sub>R(P) \<and> \<lceil>\<not>b\<rceil>\<^sub>h) \<diamondop> (post\<^sub>R(P) \<or> peri\<^sub>R(P) \<and> \<lceil>\<not>b\<rceil>\<^sub>h \<and> rl(&\<Sigma>) \<and> \<lceil>b\<rceil>\<^sub>C \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d))"
  
definition hrdPreempt_nz ::
    "('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" ("_ [_]\<^sub>H\<^sup>+ _" [64,0,65] 64) where
[upred_defs]: "hrdPreempt_nz P b Q = (P until\<^sub>H b) ;; Q"

definition hrdPreempt ::
    "('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" ("_ [_]\<^sub>H _" [64,0,65] 64) where
[upred_defs]: "P [b]\<^sub>H Q = (Q \<triangleleft> \<lceil>b\<lbrakk>$\<Sigma>/$\<Sigma>\<acute>\<rbrakk>\<rceil>\<^sub>C \<triangleright> (P [b]\<^sub>H\<^sup>+ Q))"

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
    
lemma periR_hrdEvolveTil [rdes]: "peri\<^sub>R(x \<leftarrow>\<^sub>H(t) f(time)) = (0 <\<^sub>u \<^bold>l \<and> x \<leftarrow>\<^sub>h f(time) \<and> \<^bold>l \<le>\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub><) "
  by (rel_auto)

declare minus_zero_eq [dest]
    
lemma postR_hrdEvolveTil [rdes]: "post\<^sub>R(x \<leftarrow>\<^sub>H(t) f(time)) =
                             ((x \<leftarrow>\<^sub>h f(time) \<and> \<^bold>l =\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> rl(&\<Sigma>) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) 
                                        \<triangleleft> t >\<^sub>u 0 \<triangleright>\<^sub>R 
                                       ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st))"
  by (rel_auto)
    
lemma hrdEvolveTil_SRD [closure]: "x \<leftarrow>\<^sub>H(t) f(time) is SRD"
  by (simp add: hrdEvolveTil_def init_cont_def final_cont_def closure unrest)
    
lemma hrdEvolveTil_NSRD [closure]: "x \<leftarrow>\<^sub>H(t) f(time) is NSRD"
  by (rule NSRD_intro, simp_all add: init_cont_def final_cont_def rdes closure unrest)    
    
lemma preR_hrdUntil [rdes]: 
  "P is SRD \<Longrightarrow> pre\<^sub>R(P until\<^sub>H b) = pre\<^sub>R(P)"
  by (simp add: hrdUntil_def rea_pre_RHS_design unrest usubst R1_R2c_is_R2 preR_R2 Healthy_if)

lemma periR_hrdUntil [rdes]: 
  "P is NSRD \<Longrightarrow> peri\<^sub>R(P until\<^sub>H b) = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R(P) \<and> \<lceil>\<not>b\<rceil>\<^sub>h)"
  by (simp add: hrdUntil_def rea_peri_RHS_design unrest usubst impl_alt_def
      NSRD_is_SRD R1_disj R1_extend_conj' R1_hInt  R2c_and R2c_disj 
      R2c_not R2c_peri_SRD R2s_hInt  R1_rea_impl R2c_preR R2c_rea_impl)

lemma postR_hrdUntil [rdes]:
  "P is NSRD \<Longrightarrow> post\<^sub>R(P until\<^sub>H b) = (pre\<^sub>R P \<Rightarrow>\<^sub>r (post\<^sub>R(P) \<or> peri\<^sub>R(P) \<and> \<lceil>\<not>b\<rceil>\<^sub>h \<and> rl(&\<Sigma>) \<and> \<lceil>b\<rceil>\<^sub>C \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d))"
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
  by (simp add: hrdPreempt_def alpha usubst)
        
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

(*
lemma hrdUntil_solve:
  assumes 
    "k > 0" "continuous_on {0..k} f"
    "\<forall> t \<in> {0..<k}. b\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/&\<Sigma>\<rbrakk> = false" "b\<lbrakk>\<guillemotleft>f(k)\<guillemotright>/&\<Sigma>\<rbrakk> = true"
  shows "x \<leftarrow>\<^sub>H f(time)\<guillemotright> until\<^sub>H b = x \<leftarrow>\<^sub>H(\<guillemotleft>k\<guillemotright>) f(time)"
proof -
  from assms have 1:"((0 <\<^sub>u \<^bold>l \<and> \<lceil>&\<Sigma> =\<^sub>u \<guillemotleft>f time\<guillemotright>\<rceil>\<^sub>h) \<and> \<lceil>\<not> b\<rceil>\<^sub>h) = (0 <\<^sub>u \<^bold>l \<and> \<lceil>&\<Sigma> =\<^sub>u \<guillemotleft>f time\<guillemotright>\<rceil>\<^sub>h \<and> \<guillemotleft>k\<guillemotright> \<ge>\<^sub>u end\<^sub>u(\<^bold>t))"
    by (fast_uexpr_transfer)
       (rel_auto, meson approximation_preproc_push_neg(2) less_eq_real_def)
  from assms have 2: "((end\<^sub>u(\<^bold>t) >\<^sub>u 0 \<and> \<lceil>&\<Sigma> =\<^sub>u \<guillemotleft>f time\<guillemotright>\<rceil>\<^sub>h) \<and> \<lceil>\<not> b\<rceil>\<^sub>h \<and> rl \<and> \<lceil>b\<rceil>\<^sub>C\<^sub>> \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) =
                       (\<lceil>&\<Sigma> =\<^sub>u \<guillemotleft>f time\<guillemotright>\<rceil>\<^sub>h \<and> end\<^sub>u(\<^bold>t) =\<^sub>u \<guillemotleft>k\<guillemotright> \<and> rl \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) \<triangleleft> \<guillemotleft>k\<guillemotright> >\<^sub>u 0 \<triangleright>\<^sub>R ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)"
    apply (fast_uexpr_transfer)
    apply (rel_auto)
    apply (rename_tac t t')
    apply (rule_tac x="end\<^sub>t(t' - t)" and y="k" in linorder_cases)
    apply (simp only: at_left_from_zero Limit_solve[of _ f])
    apply (subst (asm) Limit_solve [of _ f])
    apply (auto)
    apply (rule continuous_on_subset[of "{0..k}"], auto)
    apply (simp add: Limit_solve at_left_from_zero)
  done

  from 1 2 show ?thesis
    by (rule_tac SRD_eq_intro, simp_all add: closure rdes alpha wp)
qed
*)
  
end