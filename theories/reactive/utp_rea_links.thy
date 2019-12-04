section \<open> Linking Reactive Relations \<close>

theory utp_rea_links
  imports "utp_rea_prog"
begin

subsection \<open> Observation Lenses \<close>

text \<open> The following lens describes the variables of the state space that are relevant for a 
  reactive relation. Usually, these are @{const tr}, @{const st}, and other semantic variables
  under @{term "\<Sigma>\<^sub>S"}" The goal is to use this lens to abstract an @{const RR} equivalent
  heterogeneous relation. The parameter @{term X} is used to represent the variables used to
  encode additional semantic information use as refusals. \<close>

definition rea_obs :: 
  "('r \<Longrightarrow> ('s, 't::trace, '\<alpha>) rsp) 
   \<Rightarrow> ('s \<times> 'r) \<times> ('s \<times> 't \<times> 'r) \<Longrightarrow> ('s, 't, '\<alpha>) rsp \<times> ('s, 't, '\<alpha>) rsp" where
[lens_defs]: "rea_obs X = {$st, $X}\<^sub>\<alpha> +\<^sub>L {$st\<acute>, $tr\<acute>, $X\<acute>}\<^sub>\<alpha>"

text \<open> The next constant describes the variables that are unrestricted in a reactive relation,
  typically @{const ok} and @{const wait}. \<close>

definition rea_frees ::
  "(bool \<times> bool \<times> 't::trace) \<times> (bool \<times> bool) \<Longrightarrow> ('t, '\<alpha>) rp \<times> ('t, '\<alpha>) rp" where
[lens_defs]: "rea_frees = {$ok, $wait, $tr}\<^sub>\<alpha> +\<^sub>L {$ok\<acute>, $wait\<acute>}\<^sub>\<alpha>"

text \<open> We can show that both @{const rea_obs} and @{const rea_frees} are very well-behaved lenses. \<close>

lemma rea_obs_vwb [simp]: 
  "\<lbrakk> vwb_lens X; st \<bowtie> X ; tr \<bowtie> X \<rbrakk> \<Longrightarrow> vwb_lens (rea_obs X)"
  by (simp add: rea_obs_def)

lemma rea_frees_vwb [simp]: "vwb_lens rea_frees"
  by (simp add: rea_frees_def)

lemma rea_obs_unrests [simp]:
  assumes "tr \<bowtie> X"
  shows "($tr)\<^sub>v \<bowtie> rea_obs X" "rea_obs X \<bowtie> ($tr)\<^sub>v"
  using assms by (simp_all add: rea_obs_def lens_indep_sym)

lemma rea_obs_cong: 
  assumes "vwb_lens X" "st \<bowtie> X" "tr \<bowtie> X" "X \<approx>\<^sub>L Y"
  shows "rea_obs X \<approx>\<^sub>L rea_obs Y"
unfolding rea_obs_def proof (rule lens_plus_cong, simp_all add: assms)
  show "($st)\<^sub>v +\<^sub>L ($X)\<^sub>v \<approx>\<^sub>L ($st)\<^sub>v +\<^sub>L ($Y)\<^sub>v"
    by (rule lens_plus_cong, simp_all add: assms lens_equiv_refl in_var_def lens_comp_cong_1)
  show "($st\<acute>)\<^sub>v +\<^sub>L ($tr\<acute>)\<^sub>v +\<^sub>L ($X\<acute>)\<^sub>v \<approx>\<^sub>L ($st\<acute>)\<^sub>v +\<^sub>L ($tr\<acute>)\<^sub>v +\<^sub>L ($Y\<acute>)\<^sub>v"
    by (rule lens_plus_cong, simp_all add: assms out_var_def lens_equiv_refl lens_comp_cong_1 lens_plus_eq_right)
qed

lemma rea_obs_unrest_indep_all [simp]: "rea_obs \<Sigma>\<^sub>S \<bowtie> rea_frees"
  by (simp add: rea_obs_def rea_frees_def)

text \<open> The reactive observation variables and unrestricted variables are independent of each other. \<close>

lemma rea_obs_unrest_indep: 
  assumes "X \<approx>\<^sub>L \<Sigma>\<^sub>S"
  shows "rea_obs X \<bowtie> rea_frees"
proof -
  from assms have "vwb_lens X"
    by (metis lens_equiv_def rsp_vars.more\<^sub>L_vwb_lens sublens_pres_vwb)
  moreover have "st \<bowtie> X" "tr \<bowtie> X"
    by (metis assms lens_equiv_def rp_vars.indeps rsp_vars.indeps sublens_pres_indep')+
  ultimately have "rea_obs X \<approx>\<^sub>L rea_obs \<Sigma>\<^sub>S"
    by (metis assms rea_obs_cong)
  thus ?thesis
    by (metis lens_equiv_def rea_obs_unrest_indep_all sublens_pres_indep)
qed

lemma rea_obs_plus_unrest_vwb [simp]: 
  "vwb_lens (rea_obs \<Sigma>\<^sub>S +\<^sub>L rea_frees)"
  by (rule plus_vwb_lens, simp_all)

text \<open> The summation of the observation variables and unrestricted variables is bijective,
  meaning their combination covers the entire state space. \<close>

lemma rea_obs_plus_unrest_bij [simp]: 
  "bij_lens (rea_obs \<Sigma>\<^sub>S +\<^sub>L rea_frees)"
  by (rule bij_lens.intro, auto simp add: bij_lens_axioms_def, simp add: lens_defs)

subsection \<open> Abstracting Reactive Relations \<close>

text \<open> We define a function that converts a reactive relation into a heterogeneous relation of
  type @{typ "('s \<times> '\<beta>, 's \<times> 't \<times> '\<beta>) urel"}, where @{typ 's} is the state space, @{typ "'t"}
  is the trace type and @{typ "'\<beta>"} is additional semantic information. This is the minimal
  representation of a healthy reactive relation. \<close>

definition rea_to_urel :: 
  "('\<beta> \<Longrightarrow> ('s, 't::trace, '\<alpha>) rsp) \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp \<Rightarrow> ('s \<times> '\<beta>, 's \<times> 't \<times> '\<beta>) urel" where
"rea_to_urel X P = P\<lbrakk>0/$tr\<rbrakk> \<restriction>\<^sub>e (rea_obs X)" \<comment> \<open> We substitute the empty trace for @{term "$tr"},
                                                and then restrict the alphabet to be only those
                                                variables in @{term "rea_obs X"}. \<close>

text \<open> We also define a function that translates in the opposite direction. \<close>

definition urel_to_rea :: 
  "('\<beta> \<Longrightarrow> ('s, 't::trace, '\<alpha>) rsp) \<Rightarrow> ('s \<times> '\<beta>, 's \<times> 't \<times> '\<beta>) urel \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" where
[upred_defs]: "urel_to_rea X P = R2(P \<oplus>\<^sub>p rea_obs X)"

text \<open> The latter function always constructs a healthy reactive relation. \<close>

lemma urel_to_rea_is_RR [closure]:
  assumes "X \<approx>\<^sub>L \<Sigma>\<^sub>S"
  shows "urel_to_rea X P is RR"
proof -
  have "X \<bowtie> ok" "X \<bowtie> wait" "X \<bowtie> st" "X \<bowtie> tr"
    using assms des_vars.indeps(2) lens_equiv_pres_indep rp_vars.indeps(2,6,4,11) rsp_vars.indeps(2,6) by blast+
  thus ?thesis
    by (rule_tac RR_intro, simp_all add: urel_to_rea_def R2_def rea_obs_def unrest, rel_auto+)
qed  

text \<open> Moreover, we can always invert the second function. \<close>

lemma urel_to_rea_inverse:
  assumes "X \<approx>\<^sub>L \<Sigma>\<^sub>S"
  shows "rea_to_urel X (urel_to_rea X P) = P"
proof -
  have indeps: "X \<bowtie> ok" "X \<bowtie> wait" "X \<bowtie> st" "X \<bowtie> tr"
    using assms des_vars.indeps(2) lens_equiv_pres_indep rp_vars.indeps(2,6,4,11) rsp_vars.indeps(2,6) by blast+
  hence indeps': "st \<bowtie> X" "tr \<bowtie> X"
    by (metis lens_indep_sym)+
  have "vwb_lens X"
    using assms lens_equiv_def rsp_vars.more\<^sub>L_vwb_lens sublens_pres_vwb by blast
  thus ?thesis
    by (simp add: rea_to_urel_def urel_to_rea_def usubst alpha unrest R2_def R1_def R2s_def prod_mwb_lens indeps indeps', rel_auto)
qed

text \<open> We can invert the first function provided that we apply it to a healthy reactive relation. \<close>

lemma rea_to_urel_inverse:
  assumes "X \<approx>\<^sub>L \<Sigma>\<^sub>S" "P is RR"
  shows "urel_to_rea X (rea_to_urel X P) = P"
proof -
  have indeps: "X \<bowtie> ok" "X \<bowtie> wait" "X \<bowtie> st" "X \<bowtie> tr"
    using assms des_vars.indeps(2) lens_equiv_pres_indep rp_vars.indeps(2,6,4,11) rsp_vars.indeps(2,6) by blast+
  hence indeps': "st \<bowtie> X" "tr \<bowtie> X"
    by (metis lens_indep_sym)+
  have vwb_X: "vwb_lens X"
    using assms lens_equiv_def rsp_vars.more\<^sub>L_vwb_lens sublens_pres_vwb by blast
  hence "urel_to_rea X (rea_to_urel X (RR P)) = RR P"
    apply (simp add: rea_to_urel_def urel_to_rea_def usubst alpha unrest R2_def R1_def R2s_def prod_mwb_lens indeps indeps')
    apply (subst aext_arestr[of _ rea_frees])
    apply (simp_all add: assms indeps' rea_obs_unrest_indep)
    apply (metis (no_types, hide_lams) vwb_X assms(1) bij_lens_cong indeps'(1) indeps'(2) lens_plus_eq_left rea_obs_cong rea_obs_plus_unrest_bij rea_obs_unrest_indep)
     apply (rel_simp')
    apply (rel_simp')
    done
  thus ?thesis
    by (metis Healthy_if assms(2))
qed


end