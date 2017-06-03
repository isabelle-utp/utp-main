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

definition hrdInt :: "(real \<Rightarrow> 'c::t2_space upred) \<Rightarrow> ('d, 'c) hyrel" where
[urel_defs]: "hrdInt P = \<^bold>R\<^sub>s(true \<turnstile> (ll \<and> \<lceil>P(\<tau>)\<rceil>\<^sub>h) \<diamondop> false)" 

text {* Evolve according to a continuous invariant for a definite time length. *}
  
definition hrdIntF :: 
  "(real \<Rightarrow> 'c::t2_space upred) \<Rightarrow> (real, 'd \<times> 'c) uexpr \<Rightarrow> ('d, 'c) hyrel" where
[urel_defs]: "hrdIntF P t = \<^bold>R\<^sub>s(true \<turnstile> (ll \<and> \<lceil>P(\<tau>)\<rceil>\<^sub>h \<and> \<^bold>l <\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub><) 
                                    \<diamondop> ((ll \<and> \<lceil>P(\<tau>)\<rceil>\<^sub>h \<and> \<^bold>l =\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> rl \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) 
                                        \<triangleleft> t >\<^sub>u 0 \<triangleright>\<^sub>R 
                                       ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st)))" 

syntax
  "_hrdInt"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>H'(_')")
  "_hrdIntF" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>H") 
  
translations
  "\<lceil>P\<rceil>\<^sub>H"    => "CONST hrdInt (\<lambda> _time_var. P)"
  "\<lceil>P\<rceil>\<^sub>H"    <= "CONST hrdInt (\<lambda> x. P)"
  "\<lceil>P\<rceil>\<^sub>H(t)" => "CONST hrdIntF (\<lambda> _time_var. P) t"
  "\<lceil>P\<rceil>\<^sub>H(t)" <= "CONST hrdIntF (\<lambda> x. P) t"

definition hrdODE ::
  "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow>
   ('a ODE, 'c) uexpr \<Rightarrow> ('d, 'c) hyrel" where
[urel_defs]: "hrdODE x \<F>' = \<^bold>R\<^sub>s(true \<turnstile> \<langle>x \<bullet> \<F>'\<rangle>\<^sub>h \<diamondop> false)"

syntax
  "_hrdODE" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ \<bullet> _\<rangle>\<^sub>H")

translations
  "_hrdODE a P" == "CONST hODE a P"

definition hrdPreempt ::
    "('d, 'c::t2_space) hyrel \<Rightarrow> 'c upred \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" ("_ [_]\<^sub>H _" [64,0,65] 64) where
"hrdPreempt P b Q =
  Q \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright>
    \<^bold>R\<^sub>s((pre\<^sub>R(P) \<and> (post\<^sub>R(P) \<and> rl \<and> \<lceil>b\<rceil>\<^sub>C\<^sub>>) wp\<^sub>R pre\<^sub>R(Q))
       \<turnstile> (peri\<^sub>R(P) \<or> (peri\<^sub>R(P) \<and> rl \<and> \<lceil>b\<rceil>\<^sub>C\<^sub>> \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) ;; peri\<^sub>R(Q))
       \<diamondop> (post\<^sub>R(P) \<or> (peri\<^sub>R(P) \<and> rl \<and> \<lceil>b\<rceil>\<^sub>C\<^sub>> \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) ;; post\<^sub>R(Q)))"

lemma preR_hrdInt [rdes]: "pre\<^sub>R(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = true"
  by (rel_auto)
    
lemma periR_hrdInt [rdes]: "peri\<^sub>R(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = (ll \<and> \<lceil>P(\<tau>)\<rceil>\<^sub>h)"
  by (rel_auto)

lemma postR_hrdInt [rdes]: "post\<^sub>R(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = false"
  by (rel_auto)
    
lemma hrdInt_SRD [closure]: "\<lceil>P(\<tau>)\<rceil>\<^sub>H is SRD"
  by (simp add: hrdInt_def closure unrest)
    
lemma hrdInt_NSRD [closure]: "\<lceil>P(\<tau>)\<rceil>\<^sub>H is NSRD"
  by (rule NSRD_intro, simp_all add: rdes closure unrest)
    
lemma preR_hrdIntF [rdes]: "pre\<^sub>R(\<lceil>P(\<tau>)\<rceil>\<^sub>H(n)) = true"
  by (rel_auto)
    
lemma periR_hrdIntF [rdes]: "peri\<^sub>R(\<lceil>P(\<tau>)\<rceil>\<^sub>H(t)) = (ll \<and> \<lceil>P(\<tau>)\<rceil>\<^sub>h \<and> \<^bold>l <\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub><)"
  by (rel_auto)

lemma postR_hrdIntF [rdes]: "post\<^sub>R(\<lceil>P(\<tau>)\<rceil>\<^sub>H(t)) =
                             ((ll \<and> \<lceil>P(\<tau>)\<rceil>\<^sub>h \<and> \<^bold>l =\<^sub>u \<lceil>t\<rceil>\<^sub>S\<^sub>< \<and> rl \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d) 
                                        \<triangleleft> t >\<^sub>u 0 \<triangleright>\<^sub>R 
                                       ($tr\<acute> =\<^sub>u $tr \<and> $st\<acute> =\<^sub>u $st))"
  apply (rel_auto) using minus_zero_eq by blast

lemma hrdIntF_SRD [closure]: "\<lceil>P(\<tau>)\<rceil>\<^sub>H(t) is SRD"
  by (simp add: hrdIntF_def closure unrest)
    
lemma hrdIntF_NSRD [closure]: "\<lceil>P(\<tau>)\<rceil>\<^sub>H(t) is NSRD"
  by (rule NSRD_intro, simp_all add: rdes closure unrest)    
    
    
lemma hrdPreempt_true:
  "P is SRD \<Longrightarrow> P [true]\<^sub>H Q = Q"
  by (simp add: hrdPreempt_def alpha)

lemma hrdPreempt_false:
  "P is SRD \<Longrightarrow> P [false]\<^sub>H Q = P"
  by (simp add: hrdPreempt_def alpha wp SRD_reactive_tri_design)

lemma hrdPreempt_term:
  "II\<^sub>R [b]\<^sub>H P = P \<triangleleft> \<lceil>b\<rceil>\<^sub>C\<^sub>< \<triangleright> II\<^sub>R"
  apply (simp add: hrdPreempt_def rdes, rel_auto) using minus_zero_eq by auto
   
lemma hrdIntF_zero: "\<lceil>P(\<tau>)\<rceil>\<^sub>H(0) = II\<^sub>R"
  apply (simp add: hrdIntF_def alpha, rel_auto)
  using minus_zero_eq apply blast
  using approximation_preproc_push_neg(1) tt_end_ge_0 apply blast
  using minus_zero_eq apply auto
done
  
(*
lemma 
  assumes "P is NSRD" "Q is NSRD" "R is NSRD"
  shows "P ;; (Q [b]\<^sub>H R) = (P ;; Q) [b]\<^sub>H R"
  apply (rule SRD_eq_intro)
  apply (simp_all add: closure assms rdes)
  
lemma 
  assumes "k > 0" "\<forall> t \<in> {0..<k}. b\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/&\<Sigma>\<rbrakk> = false" "b\<lbrakk>\<guillemotleft>f(k)\<guillemotright>/&\<Sigma>\<rbrakk> = true"
  shows "\<lceil>&\<Sigma> =\<^sub>u \<guillemotleft>f(\<tau>)\<guillemotright>\<rceil>\<^sub>H [b]\<^sub>H Q = \<lceil>&\<Sigma> =\<^sub>u \<guillemotleft>f(\<tau>)\<guillemotright>\<rceil>\<^sub>H(\<guillemotleft>k\<guillemotright>) ;; Q"
  apply (simp add: hrdPreempt_def rdes wp)
*)  

end