section \<open> Reactive Design Triples \<close>

theory utp_rdes_triples
  imports utp_rdes_designs
begin

subsection \<open> Diamond notation\<close>

definition wait'_cond ::
  "('t::trace,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp \<Rightarrow> ('t,'\<alpha>,'\<beta>) rel_rp" (infixr "\<diamondop>" 60) where
[upred_defs]: "P \<diamondop> Q = (P \<triangleleft> $wait\<acute> \<triangleright> Q)"

utp_const wait'_cond

lemma wait'_cond_unrest [unrest]:
  "\<lbrakk> out_var wait \<bowtie> x; x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<diamondop> Q)"
  by (simp add: wait'_cond_def unrest)

lemma wait'_cond_subst [usubst]:
  "$wait\<acute> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P \<diamondop> Q) = (\<sigma> \<dagger> P) \<diamondop> (\<sigma> \<dagger> Q)"
  by (simp add: wait'_cond_def usubst unrest usubst_apply_unrest)

lemma wait'_cond_left_false: "false \<diamondop> P = (\<not> $wait\<acute> \<and> P)"
  by (rel_auto)

lemma wait'_cond_seq: "((P \<diamondop> Q) ;; R) = ((P ;; ($wait \<and> R)) \<or> (Q ;; (\<not>$wait \<and> R)))"
  by (simp add: wait'_cond_def cond_def seqr_or_distl, rel_blast)

lemma wait'_cond_true: "(P \<diamondop> Q \<and> $wait\<acute>) = (P \<and> $wait\<acute>)"
  by (rel_auto)

lemma wait'_cond_false: "(P \<diamondop> Q \<and> (\<not>$wait\<acute>)) = (Q \<and> (\<not>$wait\<acute>))"
  by (rel_auto)

lemma wait'_cond_idem: "P \<diamondop> P = P"
  by (rel_auto)

lemma wait'_cond_conj_exchange:
  "((P \<diamondop> Q) \<and> (R \<diamondop> S)) = (P \<and> R) \<diamondop> (Q \<and> S)"
  by (rel_auto)

lemma subst_wait'_cond_true [usubst]: "(P \<diamondop> Q)\<lbrakk>true/$wait\<acute>\<rbrakk> = P\<lbrakk>true/$wait\<acute>\<rbrakk>"
  by (rel_auto)

lemma subst_wait'_cond_false [usubst]: "(P \<diamondop> Q)\<lbrakk>false/$wait\<acute>\<rbrakk> = Q\<lbrakk>false/$wait\<acute>\<rbrakk>"
  by (rel_auto)

lemma subst_wait'_left_subst: "(P\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> Q) = (P \<diamondop> Q)"
  by (rel_auto)

lemma subst_wait'_right_subst: "(P \<diamondop> Q\<lbrakk>false/$wait\<acute>\<rbrakk>) = (P \<diamondop> Q)"
  by (rel_auto)

lemma wait'_cond_split: "P\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<lbrakk>false/$wait\<acute>\<rbrakk> = P"
  by (simp add: wait'_cond_def cond_var_split)

lemma wait_cond'_assoc [simp]: "P \<diamondop> Q \<diamondop> R = P \<diamondop> R"
  by (rel_auto)

lemma wait_cond'_shadow: "(P \<diamondop> Q) \<diamondop> R = P \<diamondop> Q \<diamondop> R"
  by (rel_auto)

lemma wait_cond'_conj [simp]: "P \<diamondop> (Q \<and> (R \<diamondop> S)) = P \<diamondop> (Q \<and> S)"
  by (rel_auto)

lemma R1_wait'_cond: "R1(P \<diamondop> Q) = R1(P) \<diamondop> R1(Q)"
  by (rel_auto)

lemma R2s_wait'_cond: "R2s(P \<diamondop> Q) = R2s(P) \<diamondop> R2s(Q)"
  by (simp add: wait'_cond_def R2s_def R2s_def usubst)

lemma R2_wait'_cond: "R2(P \<diamondop> Q) = R2(P) \<diamondop> R2(Q)"
  by (simp add: R2_def R2s_wait'_cond R1_wait'_cond)
    
lemma wait'_cond_R1_closed [closure]: 
  "\<lbrakk> P is R1; Q is R1 \<rbrakk> \<Longrightarrow> P \<diamondop> Q is R1"
  by (simp add: Healthy_def R1_wait'_cond)

lemma wait'_cond_R2c_closed [closure]: "\<lbrakk> P is R2c; Q is R2c \<rbrakk> \<Longrightarrow> P \<diamondop> Q is R2c"
  by (simp add: R2c_condr wait'_cond_def Healthy_def, rel_auto)

subsection \<open> Export laws \<close>

lemma RH_design_peri_R1: "\<^bold>R(P \<turnstile> R1(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_idem R1_wait'_cond RH_design_export_R1)

lemma RH_design_post_R1: "\<^bold>R(P \<turnstile> Q \<diamondop> R1(R)) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_wait'_cond RH_design_export_R1 RH_design_peri_R1)

lemma RH_design_peri_R2s: "\<^bold>R(P \<turnstile> R2s(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RH_design_export_R2s)

lemma RH_design_post_R2s: "\<^bold>R(P \<turnstile> Q \<diamondop> R2s(R)) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RH_design_export_R2s)

lemma RH_design_peri_R2c: "\<^bold>R(P \<turnstile> R2c(Q) \<diamondop> R) = \<^bold>R(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_R2s_R2c RH_design_peri_R1 RH_design_peri_R2s)

lemma RHS_design_peri_R1: "\<^bold>R\<^sub>s(P \<turnstile> R1(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R1_idem R1_wait'_cond RHS_design_export_R1)

lemma RHS_design_post_R1: "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R1(R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_wait'_cond RHS_design_export_R1 RHS_design_peri_R1)

lemma RHS_design_peri_R2s: "\<^bold>R\<^sub>s(P \<turnstile> R2s(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis (no_types, lifting) R2s_idem R2s_wait'_cond RHS_design_export_R2s)

lemma RHS_design_post_R2s: "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R2s(R)) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R2s_wait'_cond RHS_design_export_R2s RHS_design_peri_R2s)

lemma RHS_design_peri_R2c: "\<^bold>R\<^sub>s(P \<turnstile> R2c(Q) \<diamondop> R) = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)"
  by (metis R1_R2s_R2c RHS_design_peri_R1 RHS_design_peri_R2s)

lemma RH_design_lemma1:
  "RH(P \<turnstile> (R1(R2c(Q)) \<or> R) \<diamondop> S) = RH(P \<turnstile> (Q \<or> R) \<diamondop> S)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R1_R2s_R2c R2_R1_form R2_disj R2c_idem RH_design_peri_R1 RH_design_peri_R2s)

lemma RHS_design_lemma1:
  "RHS(P \<turnstile> (R1(R2c(Q)) \<or> R) \<diamondop> S) = RHS(P \<turnstile> (Q \<or> R) \<diamondop> S)"
  by (metis (no_types, lifting) R1_R2c_is_R2 R1_R2s_R2c R2_R1_form R2_disj R2c_idem RHS_design_peri_R1 RHS_design_peri_R2s)

subsection \<open> Pre-, peri-, and postconditions \<close>

subsubsection \<open> Definitions \<close>

abbreviation "pre\<^sub>s  \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s false, $wait \<mapsto>\<^sub>s false]"
abbreviation "cmt\<^sub>s  \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false]"
abbreviation "peri\<^sub>s \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s true]"
abbreviation "post\<^sub>s \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s false]"

abbreviation "npre\<^sub>R(P) \<equiv> pre\<^sub>s \<dagger> P"

definition [upred_defs]: "pre\<^sub>R(P)  = (\<not>\<^sub>r npre\<^sub>R(P))"
definition [upred_defs]: "cmt\<^sub>R(P)  = R1(cmt\<^sub>s \<dagger> P)"
definition [upred_defs]: "peri\<^sub>R(P) = R1(peri\<^sub>s \<dagger> P)"
definition [upred_defs]: "post\<^sub>R(P) = R1(post\<^sub>s \<dagger> P)"

no_utp_lift pre\<^sub>R cmt\<^sub>R peri\<^sub>R post\<^sub>R npre\<^sub>R

subsubsection \<open> Unrestriction laws \<close>

lemma ok_pre_unrest [unrest]: "$ok \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma ok_peri_unrest [unrest]: "$ok \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma ok_post_unrest [unrest]: "$ok \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma ok_cmt_unrest [unrest]: "$ok \<sharp> cmt\<^sub>R P"
  by (simp add: cmt\<^sub>R_def unrest usubst)

lemma ok'_pre_unrest [unrest]: "$ok\<acute> \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma ok'_peri_unrest [unrest]: "$ok\<acute> \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma ok'_post_unrest [unrest]: "$ok\<acute> \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma ok'_cmt_unrest [unrest]: "$ok\<acute> \<sharp> cmt\<^sub>R P"
  by (simp add: cmt\<^sub>R_def unrest usubst)

lemma wait_pre_unrest [unrest]: "$wait \<sharp> pre\<^sub>R P"
  by (simp add: pre\<^sub>R_def unrest usubst)

lemma wait_peri_unrest [unrest]: "$wait \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma wait_post_unrest [unrest]: "$wait \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

lemma wait_cmt_unrest [unrest]: "$wait \<sharp> cmt\<^sub>R P"
  by (simp add: cmt\<^sub>R_def unrest usubst)

lemma wait'_peri_unrest [unrest]: "$wait\<acute> \<sharp> peri\<^sub>R P"
  by (simp add: peri\<^sub>R_def unrest usubst)

lemma wait'_post_unrest [unrest]: "$wait\<acute> \<sharp> post\<^sub>R P"
  by (simp add: post\<^sub>R_def unrest usubst)

subsubsection \<open> Substitution laws \<close>

lemma pre\<^sub>s_design: "pre\<^sub>s \<dagger> (P \<turnstile> Q) = (\<not> pre\<^sub>s \<dagger> P)"
  by (simp add: design_def pre\<^sub>R_def usubst)

lemma peri\<^sub>s_design: "peri\<^sub>s \<dagger> (P \<turnstile> Q \<diamondop> R) = peri\<^sub>s \<dagger> (P \<Rightarrow> Q)"
  by (simp add: design_def usubst wait'_cond_def)

lemma post\<^sub>s_design: "post\<^sub>s \<dagger> (P \<turnstile> Q \<diamondop> R) = post\<^sub>s \<dagger> (P \<Rightarrow> R)"
  by (simp add: design_def usubst wait'_cond_def)

lemma cmt\<^sub>s_design: "cmt\<^sub>s \<dagger> (P \<turnstile> Q) = cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)"
  by (simp add: design_def usubst wait'_cond_def)

lemma pre\<^sub>s_R1 [usubst]: "pre\<^sub>s \<dagger> R1(P) = R1(pre\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma pre\<^sub>s_R2c [usubst]: "pre\<^sub>s \<dagger> R2c(P) = R2c(pre\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma peri\<^sub>s_R1 [usubst]: "peri\<^sub>s \<dagger> R1(P) = R1(peri\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma peri\<^sub>s_R2c [usubst]: "peri\<^sub>s \<dagger> R2c(P) = R2c(peri\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma post\<^sub>s_R1 [usubst]: "post\<^sub>s \<dagger> R1(P) = R1(post\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma post\<^sub>s_R2c [usubst]: "post\<^sub>s \<dagger> R2c(P) = R2c(post\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma cmt\<^sub>s_R1 [usubst]: "cmt\<^sub>s \<dagger> R1(P) = R1(cmt\<^sub>s \<dagger> P)"
  by (simp add: R1_def usubst)

lemma cmt\<^sub>s_R2c [usubst]: "cmt\<^sub>s \<dagger> R2c(P) = R2c(cmt\<^sub>s \<dagger> P)"
  by (simp add: R2c_def R2s_def usubst)

lemma pre_wait_false:
  "pre\<^sub>R(P\<lbrakk>false/$wait\<rbrakk>) = pre\<^sub>R(P)"
  by (rel_auto)

lemma cmt_wait_false:
  "cmt\<^sub>R(P\<lbrakk>false/$wait\<rbrakk>) = cmt\<^sub>R(P)"
  by (rel_auto)

lemma rea_pre_RH_design: "pre\<^sub>R(\<^bold>R(P \<turnstile> Q)) = R1(R2c(pre\<^sub>s \<dagger> P))"
  by (simp add: RH_def usubst R3c_def pre\<^sub>R_def pre\<^sub>s_design R1_negate_R1 R2c_not rea_not_def)

lemma rea_pre_RHS_design: "pre\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q)) = R1(R2c(pre\<^sub>s \<dagger> P))"
  by (simp add: RHS_def usubst R3h_def pre\<^sub>R_def pre\<^sub>s_design R1_negate_R1 R2c_not rea_not_def)

lemma rea_cmt_RH_design: "cmt\<^sub>R(\<^bold>R(P \<turnstile> Q)) = R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)))"
  by (simp add: RH_def usubst R3c_def cmt\<^sub>R_def cmt\<^sub>s_design R1_idem)

lemma rea_cmt_RHS_design: "cmt\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q)) = R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)))"
  by (simp add: RHS_def usubst R3h_def cmt\<^sub>R_def cmt\<^sub>s_design R1_idem)

lemma rea_peri_RH_design: "peri\<^sub>R(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = R1(R2c(peri\<^sub>s \<dagger> (P \<Rightarrow>\<^sub>r Q)))"
  by rel_auto

lemma rea_peri_RHS_design: "peri\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = R1(R2c(peri\<^sub>s \<dagger> (P \<Rightarrow>\<^sub>r Q)))"
  by (simp add:RHS_def usubst peri\<^sub>R_def R3h_def peri\<^sub>s_design, rel_auto)

lemma rea_post_RH_design: "post\<^sub>R(\<^bold>R(P \<turnstile> Q \<diamondop> R)) = R1(R2c(post\<^sub>s \<dagger> (P \<Rightarrow>\<^sub>r R)))"
  by rel_auto

lemma rea_post_RHS_design: "post\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = R1(R2c(post\<^sub>s \<dagger> (P \<Rightarrow>\<^sub>r R)))"
  by (simp add:RHS_def usubst post\<^sub>R_def R3h_def post\<^sub>s_design, rel_auto)

lemma peri_cmt_def: "peri\<^sub>R(P) = (cmt\<^sub>R(P))\<lbrakk>true/$wait\<acute>\<rbrakk>"
  by (rel_auto)

lemma post_cmt_def: "post\<^sub>R(P) = (cmt\<^sub>R(P))\<lbrakk>false/$wait\<acute>\<rbrakk>"
  by (rel_auto)

lemma rdes_export_cmt: "\<^bold>R\<^sub>s(P \<turnstile> cmt\<^sub>s \<dagger> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

lemma rdes_export_pre: "\<^bold>R\<^sub>s((P\<lbrakk>true,false/$ok,$wait\<rbrakk>) \<turnstile> Q) = \<^bold>R\<^sub>s(P \<turnstile> Q)"
  by (rel_auto)

subsubsection \<open> Healthiness laws \<close>

lemma wait'_unrest_pre_SRD [unrest]:
  "$wait\<acute> \<sharp> pre\<^sub>R(P) \<Longrightarrow>  $wait\<acute> \<sharp> pre\<^sub>R (SRD P)"
  apply (rel_auto)
  using least_zero apply blast+
done

lemma R1_R2s_cmt_SRD:
  assumes "P is SRD"
  shows "R1(R2s(cmt\<^sub>R(P))) = cmt\<^sub>R(P)"
  by (metis (no_types, lifting) R1_R2c_commute R1_R2s_R2c R1_idem R2c_idem SRD_reactive_design assms rea_cmt_RHS_design)

lemma R1_R2s_peri_SRD:
  assumes "P is SRD"
  shows "R1(R2s(peri\<^sub>R(P))) = peri\<^sub>R(P)"
  by (metis (no_types, hide_lams) Healthy_def R1_R2s_R2c R2_def R2_idem RHS_def SRD_RH_design_form assms R1_idem peri\<^sub>R_def peri\<^sub>s_R1 peri\<^sub>s_R2c)

lemma R1_peri_SRD:
  assumes "P is SRD"
  shows "R1(peri\<^sub>R(P)) = peri\<^sub>R(P)"
proof -
  have "R1(peri\<^sub>R(P)) = R1(R1(R2s(peri\<^sub>R(P))))"
    by (simp add: R1_R2s_peri_SRD assms)
  also have "... = peri\<^sub>R(P)"
    by (simp add: R1_idem, simp add: R1_R2s_peri_SRD assms)
  finally show ?thesis .
qed

lemma periR_SRD_R1 [closure]: "P is SRD \<Longrightarrow> peri\<^sub>R(P) is R1"
  by (simp add: Healthy_def' R1_peri_SRD)

lemma R1_R2c_peri_RHS:
  assumes "P is SRD"
  shows "R1(R2c(peri\<^sub>R(P))) = peri\<^sub>R(P)"
  by (metis R1_R2s_R2c R1_R2s_peri_SRD assms)

lemma R1_R2s_post_SRD:
  assumes "P is SRD"
  shows "R1(R2s(post\<^sub>R(P))) = post\<^sub>R(P)"
  by (metis (no_types, hide_lams) Healthy_def R1_R2s_R2c R1_idem R2_def R2_idem RHS_def SRD_RH_design_form assms post\<^sub>R_def post\<^sub>s_R1 post\<^sub>s_R2c)

lemma R2c_peri_SRD:
  assumes "P is SRD"
  shows "R2c(peri\<^sub>R(P)) = peri\<^sub>R(P)"
  by (metis R1_R2c_commute R1_R2c_peri_RHS R1_peri_SRD assms)

lemma R1_post_SRD:
  assumes "P is SRD"
  shows "R1(post\<^sub>R(P)) = post\<^sub>R(P)"
proof -
  have "R1(post\<^sub>R(P)) = R1(R1(R2s(post\<^sub>R(P))))"
    by (simp add: R1_R2s_post_SRD assms)
  also have "... = post\<^sub>R(P)"
    by (simp add: R1_idem, simp add: R1_R2s_post_SRD assms)
  finally show ?thesis .
qed

lemma R2c_post_SRD:
  assumes "P is SRD"
  shows "R2c(post\<^sub>R(P)) = post\<^sub>R(P)"
  by (metis R1_R2c_commute R1_R2s_R2c R1_R2s_post_SRD R1_post_SRD assms)

lemma postR_SRD_R1 [closure]: "P is SRD \<Longrightarrow> post\<^sub>R(P) is R1"
  by (simp add: Healthy_def' R1_post_SRD)

lemma R1_R2c_post_RHS:
  assumes "P is SRD"
  shows "R1(R2c(post\<^sub>R(P))) = post\<^sub>R(P)"
  by (metis R1_R2s_R2c R1_R2s_post_SRD assms)

lemma R2_cmt_conj_wait':
  "P is SRD \<Longrightarrow> R2(cmt\<^sub>R P \<and> \<not> $wait\<acute>) = (cmt\<^sub>R P \<and> \<not> $wait\<acute>)"
  by (simp add: R2_def R2s_conj R2s_not R2s_wait' R1_extend_conj R1_R2s_cmt_SRD)

lemma R2c_preR:
  "P is SRD \<Longrightarrow> R2c(pre\<^sub>R(P)) = pre\<^sub>R(P)"
  by (metis (no_types, lifting) R1_R2c_commute R2c_idem SRD_reactive_design rea_pre_RHS_design)

lemma preR_R2c_closed [closure]: "P is SRD \<Longrightarrow> pre\<^sub>R(P) is R2c"
  by (simp add: Healthy_def' R2c_preR)

lemma R2c_periR:
  "P is SRD \<Longrightarrow> R2c(peri\<^sub>R(P)) = peri\<^sub>R(P)"
  by (metis (no_types, lifting) R1_R2c_commute R1_R2s_R2c R1_R2s_peri_SRD R2c_idem)

lemma periR_R2c_closed [closure]: "P is SRD \<Longrightarrow> peri\<^sub>R(P) is R2c"
  by (simp add: Healthy_def R2c_peri_SRD)

lemma R2c_postR:
  "P is SRD \<Longrightarrow> R2c(post\<^sub>R(P)) = post\<^sub>R(P)"
  by (metis (no_types, hide_lams) R1_R2c_commute R1_R2c_is_R2 R1_R2s_post_SRD R2_def R2s_idem)

lemma postR_R2c_closed [closure]: "P is SRD \<Longrightarrow> post\<^sub>R(P) is R2c"
  by (simp add: Healthy_def R2c_post_SRD)

lemma periR_RR [closure]: "P is SRD \<Longrightarrow> peri\<^sub>R(P) is RR"
  by (rule RR_intro, simp_all add: closure unrest)
  
lemma postR_RR [closure]: "P is SRD \<Longrightarrow> post\<^sub>R(P) is RR"
  by (rule RR_intro, simp_all add: closure unrest)

lemma wpR_trace_ident_pre [wp]:
  "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R) wp\<^sub>r pre\<^sub>R P = pre\<^sub>R P"
  by (rel_auto)
    
lemma R1_preR [closure]:
  "pre\<^sub>R(P) is R1"
  by (rel_auto)

lemma trace_ident_left_periR:
  "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R) ;; peri\<^sub>R(P) = peri\<^sub>R(P)"
  by (rel_auto)

lemma trace_ident_left_postR:
  "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R) ;; post\<^sub>R(P) = post\<^sub>R(P)"
  by (rel_auto)

lemma trace_ident_right_postR:
  "post\<^sub>R(P) ;; ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R) = post\<^sub>R(P)"
  by (rel_auto)

lemma preR_R2_closed [closure]: "P is SRD \<Longrightarrow> pre\<^sub>R(P) is R2"
  by (simp add: R2_comp_def Healthy_comp closure)

lemma periR_R2_closed [closure]: "P is SRD \<Longrightarrow> peri\<^sub>R(P) is R2"
  by (simp add: Healthy_def' R1_R2c_peri_RHS R2_R2c_def)
    
lemma postR_R2_closed [closure]: "P is SRD \<Longrightarrow> post\<^sub>R(P) is R2"
  by (simp add: Healthy_def' R1_R2c_post_RHS R2_R2c_def)

subsubsection \<open> Calculation laws \<close>

lemma wait'_cond_peri_post_cmt [rdes]:
  "cmt\<^sub>R P = peri\<^sub>R P \<diamondop> post\<^sub>R P"
  by (rel_auto)

lemma preR_rdes [rdes]: 
  assumes "P is RR"
  shows "pre\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = P"
  by (simp add: rea_pre_RHS_design unrest usubst assms Healthy_if RR_implies_R2c RR_implies_R1)

lemma periR_rdes [rdes]: 
  assumes "P is RR" "Q is RR"
  shows "peri\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = (P \<Rightarrow>\<^sub>r Q)"
  by (simp add: rea_peri_RHS_design unrest usubst assms Healthy_if RR_implies_R2c closure)

lemma postR_rdes [rdes]: 
  assumes "P is RR" "R is RR"
  shows "post\<^sub>R(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = (P \<Rightarrow>\<^sub>r R)"
  by (simp add: rea_post_RHS_design unrest usubst assms Healthy_if RR_implies_R2c closure)
    
lemma preR_Chaos [rdes]: "pre\<^sub>R(Chaos) = false"
  by (simp add: Chaos_def, rel_simp)

lemma periR_Chaos [rdes]: "peri\<^sub>R(Chaos) = true\<^sub>r"
  by (simp add: Chaos_def, rel_simp)

lemma postR_Chaos [rdes]: "post\<^sub>R(Chaos) = true\<^sub>r"
  by (simp add: Chaos_def, rel_simp)

lemma preR_Miracle [rdes]: "pre\<^sub>R(Miracle) = true\<^sub>r"
  by (simp add: Miracle_def, rel_auto)

lemma periR_Miracle [rdes]: "peri\<^sub>R(Miracle) = false"
  by (simp add: Miracle_def, rel_auto)

lemma postR_Miracle [rdes]: "post\<^sub>R(Miracle) = false"
  by (simp add: Miracle_def, rel_auto)

lemma preR_srdes_skip [rdes]: "pre\<^sub>R(II\<^sub>R) = true\<^sub>r"
  by (rel_auto)

lemma periR_srdes_skip [rdes]: "peri\<^sub>R(II\<^sub>R) = false"
  by (rel_auto)

lemma postR_srdes_skip [rdes]: "post\<^sub>R(II\<^sub>R) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R)"
  by (rel_auto)

lemma preR_INF [rdes]: "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(\<Sqinter> A) = (\<And> P\<in>A \<bullet> pre\<^sub>R(P))"
  by (rel_auto)

lemma periR_INF [rdes]: "peri\<^sub>R(\<Sqinter> A) = (\<Or> P\<in>A \<bullet> peri\<^sub>R(P))"
  by (rel_auto)

lemma postR_INF [rdes]: "post\<^sub>R(\<Sqinter> A) = (\<Or> P\<in>A \<bullet> post\<^sub>R(P))"
  by (rel_auto)

lemma preR_UINF [rdes]: "pre\<^sub>R(\<Sqinter> i \<bullet> P(i)) = (\<Squnion> i \<bullet> pre\<^sub>R(P(i)))"
  by (rel_auto)

lemma periR_UINF [rdes]: "peri\<^sub>R(\<Sqinter> i \<bullet> P(i)) = (\<Sqinter> i \<bullet> peri\<^sub>R(P(i)))"
  by (rel_auto)

lemma postR_UINF [rdes]: "post\<^sub>R(\<Sqinter> i \<bullet> P(i)) = (\<Sqinter> i \<bullet> post\<^sub>R(P(i)))"
  by (rel_auto)

lemma preR_UINF_member [rdes]: "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(\<Sqinter> i\<in>A \<bullet> P(i)) = (\<Squnion> i\<in>A \<bullet> pre\<^sub>R(P(i)))"
  by (rel_auto)
    
lemma preR_UINF_member_2 [rdes]: "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(\<Sqinter> (i,j)\<in>A \<bullet> P i j) = (\<Squnion> (i,j)\<in>A \<bullet> pre\<^sub>R(P i j))"
  by (rel_auto)

lemma preR_UINF_member_3 [rdes]: "A \<noteq> {} \<Longrightarrow> pre\<^sub>R(\<Sqinter> (i,j,k)\<in>A \<bullet> P i j k) = (\<Squnion> (i,j,k)\<in>A \<bullet> pre\<^sub>R(P i j k))"
  by (rel_auto)

lemma periR_UINF_member [rdes]: "peri\<^sub>R(\<Sqinter> i\<in>A \<bullet> P(i)) = (\<Sqinter> i\<in>A \<bullet> peri\<^sub>R(P(i)))"
  by (rel_auto)
    
lemma periR_UINF_member_2 [rdes]: "peri\<^sub>R(\<Sqinter> (i,j)\<in>A \<bullet> P i j) = (\<Sqinter> (i,j)\<in>A \<bullet> peri\<^sub>R(P i j))"
  by (rel_auto)

lemma periR_UINF_member_3 [rdes]: "peri\<^sub>R(\<Sqinter> (i,j,k)\<in>A \<bullet> P i j k) = (\<Sqinter> (i,j,k)\<in>A \<bullet> peri\<^sub>R(P i j k))"
  by (rel_auto)

lemma postR_UINF_member [rdes]: "post\<^sub>R(\<Sqinter> i\<in>A \<bullet> P(i)) = (\<Sqinter> i\<in>A \<bullet> post\<^sub>R(P(i)))"
  by (rel_auto)

lemma postR_UINF_member_2 [rdes]: "post\<^sub>R(\<Sqinter> (i,j)\<in>A \<bullet> P i j) = (\<Sqinter> (i,j)\<in>A \<bullet> post\<^sub>R(P i j))"
  by (rel_auto)
    
lemma postR_UINF_member_3 [rdes]: "post\<^sub>R(\<Sqinter> (i,j,k)\<in>A \<bullet> P i j k) = (\<Sqinter> (i,j,k)\<in>A \<bullet> post\<^sub>R(P i j k))"
  by (rel_auto)    
    
lemma preR_inf [rdes]: "pre\<^sub>R(P \<sqinter> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q))"
  by (rel_auto)

lemma periR_inf [rdes]: "peri\<^sub>R(P \<sqinter> Q) = (peri\<^sub>R(P) \<or> peri\<^sub>R(Q))"
  by (rel_auto)

lemma postR_inf [rdes]: "post\<^sub>R(P \<sqinter> Q) = (post\<^sub>R(P) \<or> post\<^sub>R(Q))"
  by (rel_auto)

lemma preR_SUP [rdes]: "pre\<^sub>R(\<Squnion> A) = (\<Or> P\<in>A \<bullet> pre\<^sub>R(P))"
  by (rel_auto)

lemma periR_SUP [rdes]: "A \<noteq> {} \<Longrightarrow> peri\<^sub>R(\<Squnion> A) = (\<And> P\<in>A \<bullet> peri\<^sub>R(P))"
  by (rel_auto)

lemma postR_SUP [rdes]: "A \<noteq> {} \<Longrightarrow> post\<^sub>R(\<Squnion> A) = (\<And> P\<in>A \<bullet> post\<^sub>R(P))"
  by (rel_auto)

subsection \<open> Formation laws \<close>

subsubsection \<open> Regular \<close>

lemma rdes_skip_tri_design [rdes_def]: "II\<^sub>C = \<^bold>R(true\<^sub>r \<turnstile> false \<diamondop> II\<^sub>r)"
  apply (simp add: skip_rea_def, rel_auto)
  using minus_zero_eq apply blast+
  done

lemma RH_tri_design_form:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = (II\<^sub>C \<triangleleft> $wait \<triangleright> (($ok \<and> P\<^sub>1) \<Rightarrow>\<^sub>r ($ok\<acute> \<and> (P\<^sub>2 \<diamondop> P\<^sub>3))))"
proof -
  have "\<^bold>R(RR(P\<^sub>1) \<turnstile> RR(P\<^sub>2) \<diamondop> RR(P\<^sub>3)) = (II\<^sub>C \<triangleleft> $wait \<triangleright> (($ok \<and> RR(P\<^sub>1)) \<Rightarrow>\<^sub>r ($ok\<acute> \<and> (RR(P\<^sub>2) \<diamondop> RR(P\<^sub>3)))))"
    apply (rel_auto) using minus_zero_eq by blast
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma RH_design_pre_post_form:
  "\<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
proof -
  have "\<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R((\<not> P\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk> \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: design_subst_ok)
  also have "... = \<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: pre\<^sub>R_def cmt\<^sub>R_def usubst, rel_auto)
  finally show ?thesis .
qed

lemma RD_as_reactive_design:
  "RD(P) = \<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
  by (simp add: RH_design_pre_post_form RD_RH_design_form)

lemma RD_reactive_design_alt:
  assumes "P is RD"
  shows "\<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = P"
proof -
  have "\<^bold>R(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: RH_design_pre_post_form)
  thus ?thesis
    by (simp add: RD_reactive_design assms)
qed

lemma RD_reactive_tri_design_lemma:
  "RD(P) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (simp add: RD_RH_design_form wait'_cond_split)

lemma RD_as_reactive_tri_design:
  "RD(P) = \<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
proof -
  have "RD(P) = \<^bold>R((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>)"
    by (simp add: RD_RH_design_form wait'_cond_split)
  also have "... = \<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma RD_reactive_tri_design:
  assumes "P is RD"
  shows "\<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
  by (metis Healthy_if RD_as_reactive_tri_design assms)
    
lemma RD_elimination [RD_elim]: "\<lbrakk> P is RD; Q(\<^bold>R(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))  \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: RD_reactive_tri_design)
    
lemma RH_tri_design_is_RD [closure]:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R"
  shows "\<^bold>R(P \<turnstile> Q \<diamondop> R) is RD"
  by (rule RH_design_is_RD, simp_all add: unrest assms)

lemma RD_rdes_intro [closure]:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "\<^bold>R(P \<turnstile> Q \<diamondop> R) is RD"
  by (rule RH_tri_design_is_RD, simp_all add: unrest closure assms)

subsubsection \<open> Stateful \<close>

lemma srdes_skip_tri_design [rdes_def]: "II\<^sub>R = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> II\<^sub>r)"
  by (simp add: srdes_skip_def, rel_auto)

lemma Chaos_tri_def [rdes_def]: "Chaos = \<^bold>R\<^sub>s(false \<turnstile> false \<diamondop> false)"
  by (simp add: Chaos_def design_false_pre)

lemma Miracle_tri_def [rdes_def]: "Miracle = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> false)"
  by (simp add: Miracle_def R1_design_R1_pre wait'_cond_idem)

lemma RHS_tri_design_form:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = (II\<^sub>R \<triangleleft> $wait \<triangleright> (($ok \<and> P\<^sub>1) \<Rightarrow>\<^sub>r ($ok\<acute> \<and> (P\<^sub>2 \<diamondop> P\<^sub>3))))"
proof -
  have "\<^bold>R\<^sub>s(RR(P\<^sub>1) \<turnstile> RR(P\<^sub>2) \<diamondop> RR(P\<^sub>3)) = (II\<^sub>R \<triangleleft> $wait \<triangleright> (($ok \<and> RR(P\<^sub>1)) \<Rightarrow>\<^sub>r ($ok\<acute> \<and> (RR(P\<^sub>2) \<diamondop> RR(P\<^sub>3)))))"
    apply (rel_auto) using minus_zero_eq by blast
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma RHS_design_pre_post_form:
  "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
proof -
  have "\<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk> \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: design_subst_ok)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: pre\<^sub>R_def cmt\<^sub>R_def usubst, rel_auto)
  finally show ?thesis .
qed

lemma SRD_as_reactive_design:
  "SRD(P) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
  by (simp add: RHS_design_pre_post_form SRD_RH_design_form)

lemma SRD_reactive_design_alt:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = P"
proof -
  have "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: RHS_design_pre_post_form)
  thus ?thesis
    by (simp add: SRD_reactive_design assms)
qed

lemma SRD_reactive_tri_design_lemma:
  "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (simp add: SRD_RH_design_form wait'_cond_split)

lemma SRD_as_reactive_tri_design:
  "SRD(P) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
proof -
  have "SRD(P) = \<^bold>R\<^sub>s((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>)"
    by (simp add: SRD_RH_design_form wait'_cond_split)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    apply (simp add: usubst)
    apply (subst design_subst_ok_ok'[THEN sym])
    apply (simp add: pre\<^sub>R_def peri\<^sub>R_def post\<^sub>R_def usubst unrest)
    apply (rel_auto)
  done
  finally show ?thesis .
qed

lemma SRD_reactive_tri_design:
  assumes "P is SRD"
  shows "\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) = P"
  by (metis Healthy_if SRD_as_reactive_tri_design assms)
    
lemma SRD_elim [RD_elim]: "\<lbrakk> P is SRD; Q(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))  \<rbrakk> \<Longrightarrow> Q(P)"
  by (simp add: SRD_reactive_tri_design)
    
lemma RHS_tri_design_is_SRD [closure]:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is SRD"
  by (rule RHS_design_is_SRD, simp_all add: unrest assms)

lemma SRD_rdes_intro [closure]:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) is SRD"
  by (rule RHS_tri_design_is_SRD, simp_all add: unrest closure assms)
        
lemma USUP_R1_R2s_cmt_SRD:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<Squnion> P \<in> A \<bullet> R1 (R2s (cmt\<^sub>R P))) = (\<Squnion> P \<in> A \<bullet> cmt\<^sub>R P)"
  by (rule USUP_cong[of A], metis (mono_tags, lifting) Ball_Collect R1_R2s_cmt_SRD assms)

lemma UINF_R1_R2s_cmt_SRD:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<Sqinter> P \<in> A \<bullet> R1 (R2s (cmt\<^sub>R P))) = (\<Sqinter> P \<in> A \<bullet> cmt\<^sub>R P)"
  by (rule UINF_cong[of A], metis (mono_tags, lifting) Ball_Collect R1_R2s_cmt_SRD assms)

subsubsection \<open> Order laws \<close>

lemma preR_antitone: "P \<sqsubseteq> Q \<Longrightarrow> pre\<^sub>R(Q) \<sqsubseteq> pre\<^sub>R(P)"
  by (rel_auto)

lemma periR_monotone: "P \<sqsubseteq> Q \<Longrightarrow> peri\<^sub>R(P) \<sqsubseteq> peri\<^sub>R(Q)"
  by (rel_auto)

lemma postR_monotone: "P \<sqsubseteq> Q \<Longrightarrow> post\<^sub>R(P) \<sqsubseteq> post\<^sub>R(Q)"
  by (rel_auto)

subsection \<open> Composition laws \<close>

theorem R1_design_composition_RR:
  assumes "P is RR" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  apply (subst R1_design_composition)
  apply (simp_all add: assms unrest wp_rea_def Healthy_if closure)
  apply (rel_auto)
done

theorem R1_design_composition_RC:
  assumes "P is RC" "Q is RR" "R is RR" "S is RR"
  shows
  "(R1(P \<turnstile> Q) ;; R1(R \<turnstile> S)) = R1((P \<and> Q wp\<^sub>r R) \<turnstile> (Q ;; S))"
  by (simp add: R1_design_composition_RR assms unrest Healthy_if closure wp)

subsubsection \<open> Regular \<close>

theorem RH_tri_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) =
       \<^bold>R((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1(R2s Q\<^sub>2) ;; R1 (\<not> R2s R))) \<turnstile>
                       ((Q\<^sub>1 \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> ((R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) =
        (\<not> ((R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)))"
    by (metis (no_types, hide_lams) R1_extend_conj R2s_conj R2s_not R2s_wait' wait'_cond_false)
  have 2: "(R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 (((R1 (R2s Q\<^sub>1)) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
  proof -
    have "(R1 (R2s Q\<^sub>1) ;; ($wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                       = (((R1 (R2s Q\<^sub>1)) \<and> $wait\<acute>))"
    proof -
      have "(R1 (R2s Q\<^sub>1) ;; ($wait \<and> ((\<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
           = (R1 (R2s Q\<^sub>1) ;; ($wait \<and> (\<lceil>II\<rceil>\<^sub>D)))"
        by (rel_auto)
      also have "... = ((R1 (R2s Q\<^sub>1) ;; \<lceil>II\<rceil>\<^sub>D) \<and> $wait\<acute>)"
        by (rel_auto)
      also from assms(2) have "... = ((R1 (R2s Q\<^sub>1)) \<and> $wait\<acute>)"
        by (rel_auto, blast)
      finally show ?thesis .
    qed

    moreover have "(R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> ((\<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                  = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
    proof -
      have "(R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
            = (R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))"
        by (metis (no_types, lifting) cond_def conj_disj_not_abs utp_pred_laws.double_compl utp_pred_laws.inf.left_idem utp_pred_laws.sup_assoc utp_pred_laws.sup_inf_absorb)

      also have "... = ((R1 (R2s Q\<^sub>2))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))\<lbrakk>false/$wait\<rbrakk>)"
        by (metis false_alt_def seqr_right_one_point upred_eq_false wait_vwb_lens)

      also have "... = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest assms)

      finally show ?thesis .
    qed

    moreover
    have "((R1 (R2s Q\<^sub>1) \<and> $wait\<acute>) \<or> ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
          = (R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
      by (simp add: wait'_cond_def cond_seq_right_distr cond_and_T_integrate unrest)

    ultimately show ?thesis
      by (simp add: R2s_wait'_cond R1_wait'_cond wait'_cond_seq ex_conj_contr_right unrest)  
  qed

  from assms(7,8) have 3: "(R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R) = R1 (R2s Q\<^sub>2) ;; R1 (\<not> R2s R)"
    by (rel_auto, meson)

  show ?thesis
    by (simp add: RH_design_composition unrest assms 1 2 3, simp add: R1_R2s_R2c RH_design_lemma1)
qed

theorem RH_tri_design_composition_wp:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
          "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
          "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
  shows "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> ((Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R ((\<not> R1 (\<not> P) ;; R1 true \<and> \<not> Q\<^sub>2 ;; R1 (\<not> R)) \<turnstile> (Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: RH_tri_design_composition assms Healthy_if R2c_healthy_R2s disj_upred_def)
       (metis (no_types, hide_lams) R1_negate_R1 R2c_healthy_R2s assms(11,16))
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed

theorem RH_tri_design_composition_RR_wp:
  assumes "P is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR"
          "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> ((Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))" (is "?lhs = ?rhs")
  by (simp add: RH_tri_design_composition_wp add: closure assms unrest RR_implies_R2c)

lemma RH_tri_normal_design_composition:
  assumes
    "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
    "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
    "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
    "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
    "R1 (\<not> P) ;; R1(true) = R1(\<not> P)"
  shows "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
        \<^bold>R((R1 (\<not> P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp_all add: RH_tri_design_composition_wp rea_not_def assms unrest)
  also have "... = \<^bold>R((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: assms wp_rea_def ex_unrest, rel_auto)
  finally show ?thesis .
qed
  
lemma RH_tri_normal_design_composition' [rdes_def]:
  assumes "P is RC" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "R1 (\<not> P) ;; R1 true = R1(\<not> P)"
    using RC_implies_RC1[OF assms(1)]
    by (simp add: Healthy_def RC1_def rea_not_def)
       (metis R1_negate_R1 R1_seqr utp_pred_laws.double_compl)
  thus ?thesis
    by (simp add: RH_tri_normal_design_composition assms closure unrest RR_implies_R2c)
qed

lemma RH_tri_design_right_unit_lemma:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait\<acute> \<sharp> R"
  shows "\<^bold>R(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>C = \<^bold>R((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> (Q \<diamondop> R))"
proof -
  have "\<^bold>R(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>C = \<^bold>R(P \<turnstile> Q \<diamondop> R) ;; \<^bold>R(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))"
    by (simp add: rdes_skip_tri_design, rel_auto)
  also have "... = \<^bold>R ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> Q \<diamondop> (R1 (R2s R) ;; R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))))"
    by (simp_all add: RH_tri_design_composition assms unrest R2s_true R1_false R2s_false)
  also have "... = \<^bold>R ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> Q \<diamondop> R1 (R2s R))"
  proof -
    from assms(3,4) have "(R1 (R2s R) ;; R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))) = R1 (R2s R)"
      by (rel_auto, metis (no_types, lifting) minus_zero_eq, meson order_refl trace_class.diff_cancel)
    thus ?thesis
      by simp
  qed
  also have "... = \<^bold>R((\<not> (\<not> P) ;; R1 true) \<turnstile> (Q \<diamondop> R))"
    by (metis (no_types, lifting) R1_R2s_R1_true_lemma R1_R2s_R2c R2c_not RH_design_R2c_pre RH_design_neg_R1_pre RH_design_post_R1 RH_design_post_R2s)
  also have "... = \<^bold>R((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> Q \<diamondop> R)"
    by (rel_auto)
  finally show ?thesis .
qed

subsubsection \<open> Stateful \<close>

theorem RHS_tri_design_composition:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) =
       \<^bold>R\<^sub>s((\<not> (R1 (\<not> R2s P) ;; R1 true) \<and> \<not> (R1(R2s Q\<^sub>2) ;; R1 (\<not> R2s R))) \<turnstile>
                       (((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> ((R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R))) =
        (\<not> ((R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R)))"
    by (metis (no_types, hide_lams) R1_extend_conj R2s_conj R2s_not R2s_wait' wait'_cond_false)
  have 2: "(R1 (R2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 (((\<exists> $st\<acute> \<bullet> R1 (R2s Q\<^sub>1)) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
  proof -
    have "(R1 (R2s Q\<^sub>1) ;; ($wait \<and> ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                       = (\<exists> $st\<acute> \<bullet> ((R1 (R2s Q\<^sub>1)) \<and> $wait\<acute>))"
    proof -
      have "(R1 (R2s Q\<^sub>1) ;; ($wait \<and> ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
           = (R1 (R2s Q\<^sub>1) ;; ($wait \<and> (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)))"
        by (rel_auto, blast+)
      also have "... = ((R1 (R2s Q\<^sub>1) ;; (\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D)) \<and> $wait\<acute>)"
        by (rel_auto)
      also from assms(2) have "... = (\<exists> $st\<acute> \<bullet> ((R1 (R2s Q\<^sub>1)) \<and> $wait\<acute>))"
        by (rel_auto, blast)
      finally show ?thesis .
    qed

    moreover have "(R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
                  = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
    proof -
      have "(R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
            = (R1 (R2s Q\<^sub>2) ;; (\<not> $wait \<and> (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))"
        by (metis (no_types, lifting) cond_def conj_disj_not_abs utp_pred_laws.double_compl utp_pred_laws.inf.left_idem utp_pred_laws.sup_assoc utp_pred_laws.sup_inf_absorb)

      also have "... = ((R1 (R2s Q\<^sub>2))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))\<lbrakk>false/$wait\<rbrakk>)"
        by (metis false_alt_def seqr_right_one_point upred_eq_false wait_vwb_lens)

      also have "... = ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest assms)

      finally show ?thesis .
    qed

    moreover
    have "((R1 (R2s Q\<^sub>1) \<and> $wait\<acute>) \<or> ((R1 (R2s Q\<^sub>2)) ;; (R1 (R2s S\<^sub>1) \<diamondop> R1 (R2s S\<^sub>2))))
          = (R1 (R2s Q\<^sub>1) \<or> (R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>1))) \<diamondop> ((R1 (R2s Q\<^sub>2) ;; R1 (R2s S\<^sub>2)))"
      by (simp add: wait'_cond_def cond_seq_right_distr cond_and_T_integrate unrest)

    ultimately show ?thesis
      by (simp add: R2s_wait'_cond R1_wait'_cond wait'_cond_seq ex_conj_contr_right unrest)
         (simp add: cond_and_T_integrate cond_seq_right_distr unrest_var wait'_cond_def)
  qed

  from assms(7,8) have 3: "(R1 (R2s Q\<^sub>2) \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s R) = R1 (R2s Q\<^sub>2) ;; R1 (\<not> R2s R)"
    by (rel_auto, blast, meson)

  show ?thesis
    apply (subst RHS_design_composition)
    apply (simp_all add: assms)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: 1 2 3)
    apply (simp add: R1_R2s_R2c RHS_design_lemma1)
    apply (metis R1_R2c_ex_st RHS_design_lemma1)
  done
qed
 
theorem RHS_tri_design_composition_wp:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
          "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
          "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R\<^sub>s(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R\<^sub>s ((\<not> R1 (\<not> P) ;; R1 true \<and> \<not> Q\<^sub>2 ;; R1 (\<not> R)) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: RHS_tri_design_composition assms Healthy_if R2c_healthy_R2s disj_upred_def)
       (metis (no_types, hide_lams) R1_negate_R1 R2c_healthy_R2s assms(11,16))
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed

theorem RHS_tri_design_composition_RR_wp:
  assumes "P is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR"
          "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
          \<^bold>R\<^sub>s(((\<not>\<^sub>r P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2)))" (is "?lhs = ?rhs")
  by (simp add: RHS_tri_design_composition_wp add: closure assms unrest RR_implies_R2c)

lemma RHS_tri_normal_design_composition:
  assumes
    "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
    "$wait \<sharp> R" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
    "P is R2c" "Q\<^sub>1 is R1" "Q\<^sub>1 is R2c" "Q\<^sub>2 is R1" "Q\<^sub>2 is R2c"
    "R is R2c" "S\<^sub>1 is R1" "S\<^sub>1 is R2c" "S\<^sub>2 is R1" "S\<^sub>2 is R2c"
    "R1 (\<not> P) ;; R1(true) = R1(\<not> P)" "$st\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
        \<^bold>R\<^sub>s ((R1 (\<not> P) wp\<^sub>r false \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q\<^sub>1) \<sqinter> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp_all add: RHS_tri_design_composition_wp rea_not_def assms unrest)
  also have "... = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
    by (simp add: assms wp_rea_def ex_unrest, rel_auto)
  finally show ?thesis .
qed
  
lemma RHS_tri_normal_design_composition' [rdes_def]:
  assumes "P is RC" "Q\<^sub>1 is RR" "$st\<acute> \<sharp> Q\<^sub>1" "Q\<^sub>2 is RR" "R is RR" "S\<^sub>1 is RR" "S\<^sub>2 is RR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)
         = \<^bold>R\<^sub>s((P \<and> Q\<^sub>2 wp\<^sub>r R) \<turnstile> (Q\<^sub>1 \<or> (Q\<^sub>2 ;; S\<^sub>1)) \<diamondop> (Q\<^sub>2 ;; S\<^sub>2))"
proof -
  have "R1 (\<not> P) ;; R1 true = R1(\<not> P)"
    using RC_implies_RC1[OF assms(1)]
    by (simp add: Healthy_def RC1_def rea_not_def)
       (metis R1_negate_R1 R1_seqr utp_pred_laws.double_compl)
  thus ?thesis
    by (simp add: RHS_tri_normal_design_composition assms closure unrest RR_implies_R2c)
qed

lemma RHS_tri_design_right_unit_lemma:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok\<acute> \<sharp> R" "$wait\<acute> \<sharp> R"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>R = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q) \<diamondop> R))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; II\<^sub>R = \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) ;; \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))"
    by (simp add: srdes_skip_tri_design, rel_auto)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> (\<exists> $st\<acute> \<bullet> Q) \<diamondop> (R1 (R2s R) ;; R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))))"
    by (simp_all add: RHS_tri_design_composition assms unrest R2s_true R1_false R2s_false)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 (\<not> R2s P) ;; R1 true) \<turnstile> (\<exists> $st\<acute> \<bullet> Q) \<diamondop> R1 (R2s R))"
  proof -
    from assms(3,4) have "(R1 (R2s R) ;; R1 (R2s ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R))) = R1 (R2s R)"
      by (rel_auto, metis (no_types, lifting) minus_zero_eq, meson order_refl trace_class.diff_cancel)
    thus ?thesis
      by simp
  qed
  also have "... = \<^bold>R\<^sub>s((\<not> (\<not> P) ;; R1 true) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q) \<diamondop> R))"
    by (metis (no_types, lifting) R1_R2s_R1_true_lemma R1_R2s_R2c R2c_not RHS_design_R2c_pre RHS_design_neg_R1_pre RHS_design_post_R1 RHS_design_post_R2s)
  also have "... = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r P) ;; true\<^sub>r) \<turnstile> ((\<exists> $st\<acute> \<bullet> Q) \<diamondop> R))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma SRD_composition_wp:
  assumes "P is SRD" "Q is SRD"
  shows "(P ;; Q) = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile>
                       ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
  (is "?lhs = ?rhs")
proof -
  have "(P ;; Q) = (\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q)))"
    by (simp add: SRD_reactive_tri_design assms(1) assms(2))
  also from assms
  have "... = ?rhs"
    by (simp add: RHS_tri_design_composition_wp disj_upred_def unrest assms closure)
  finally show ?thesis .
qed

subsection \<open> Refinement introduction laws \<close>

subsubsection \<open> Regular \<close>

lemma RH_tri_design_refine:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> P\<^sub>2` \<and> `P\<^sub>1 \<and> Q\<^sub>3 \<Rightarrow> P\<^sub>3`"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3 \<Rightarrow> P\<^sub>2 \<diamondop> P\<^sub>3`"
    by (simp add: RH_design_refine assms closure RR_implies_R2c unrest ex_unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `(P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<Rightarrow> P\<^sub>2 \<diamondop> P\<^sub>3`"
    by (rel_auto)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `((P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<Rightarrow> P\<^sub>2 \<diamondop> P\<^sub>3)\<lbrakk>true/$wait\<acute>\<rbrakk>` \<and> `((P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<Rightarrow> P\<^sub>2 \<diamondop> P\<^sub>3)\<lbrakk>false/$wait\<acute>\<rbrakk>`"
    by (rel_auto, metis)
  also have "... \<longleftrightarrow> ?rhs"
    by (simp add: usubst unrest assms)
  finally show ?thesis .
qed

lemma RH_tri_design_refine':
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> (Q\<^sub>1 \<sqsubseteq> P\<^sub>1) \<and> (P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)) \<and> (P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>3))"
  by (simp add: RH_tri_design_refine assms, rel_auto)

lemma rdes_tri_refine_intro:
  assumes "`P\<^sub>1 \<Rightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> Q\<^sub>1`" "`P\<^sub>1 \<and> R\<^sub>2 \<Rightarrow> R\<^sub>1`"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<sqsubseteq> \<^bold>R(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2)"
  using assms
  by (rule_tac rdes_refine_intro, simp_all, rel_auto)  
    
lemma rdes_tri_refine_intro':
  assumes "P\<^sub>2 \<sqsubseteq> P\<^sub>1" "Q\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)" "R\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> R\<^sub>2)"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<sqsubseteq> \<^bold>R(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2)"
  using assms
  by (rule_tac rdes_tri_refine_intro, simp_all add: refBy_order)

subsubsection \<open> Stateful \<close>

lemma RHS_tri_design_refine:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> P\<^sub>2` \<and> `P\<^sub>1 \<and> Q\<^sub>3 \<Rightarrow> P\<^sub>3`"
  (is "?lhs = ?rhs")
proof -
  have "?lhs \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `P\<^sub>1 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3 \<Rightarrow> P\<^sub>2 \<diamondop> P\<^sub>3`"
    by (simp add: RHS_design_refine assms closure RR_implies_R2c unrest ex_unrest)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `(P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<Rightarrow> P\<^sub>2 \<diamondop> P\<^sub>3`"
    by (rel_auto)
  also have "... \<longleftrightarrow> `P\<^sub>1 \<Rightarrow> Q\<^sub>1` \<and> `((P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<Rightarrow> P\<^sub>2 \<diamondop> P\<^sub>3)\<lbrakk>true/$wait\<acute>\<rbrakk>` \<and> `((P\<^sub>1 \<and> Q\<^sub>2) \<diamondop> (P\<^sub>1 \<and> Q\<^sub>3) \<Rightarrow> P\<^sub>2 \<diamondop> P\<^sub>3)\<lbrakk>false/$wait\<acute>\<rbrakk>`"
    by (rel_auto, metis)
  also have "... \<longleftrightarrow> ?rhs"
    by (simp add: usubst unrest assms)
  finally show ?thesis .
qed

lemma RHS_tri_design_refine':
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> (Q\<^sub>1 \<sqsubseteq> P\<^sub>1) \<and> (P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)) \<and> (P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>3))"
  by (simp add: RHS_tri_design_refine assms, rel_auto)

lemma srdes_tri_refine_intro:
  assumes "`P\<^sub>1 \<Rightarrow> P\<^sub>2`" "`P\<^sub>1 \<and> Q\<^sub>2 \<Rightarrow> Q\<^sub>1`" "`P\<^sub>1 \<and> R\<^sub>2 \<Rightarrow> R\<^sub>1`"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2)"
  using assms
  by (rule_tac srdes_refine_intro, simp_all, rel_auto)  
    
lemma srdes_tri_refine_intro':
  assumes "P\<^sub>2 \<sqsubseteq> P\<^sub>1" "Q\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)" "R\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> R\<^sub>2)"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> Q\<^sub>1 \<diamondop> R\<^sub>1) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>2 \<turnstile> Q\<^sub>2 \<diamondop> R\<^sub>2)"
  using assms
  by (rule_tac srdes_tri_refine_intro, simp_all add: refBy_order)

lemma SRD_peri_under_pre:
  assumes "P is SRD" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "(pre\<^sub>R(P) \<Rightarrow>\<^sub>r peri\<^sub>R(P)) = peri\<^sub>R(P)"
proof -
  have "peri\<^sub>R(P) =
        peri\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: SRD_reactive_tri_design assms)
  also have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)"
    by (simp add: rea_pre_RHS_design rea_peri_RHS_design assms 
        unrest usubst R1_peri_SRD R2c_preR R1_rea_impl R2c_rea_impl R2c_periR)
  finally show ?thesis ..
qed

lemma SRD_post_under_pre:
  assumes "P is SRD" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "(pre\<^sub>R(P) \<Rightarrow>\<^sub>r post\<^sub>R(P)) = post\<^sub>R(P)"
proof -
  have "post\<^sub>R(P) =
        post\<^sub>R(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)))"
    by (simp add: SRD_reactive_tri_design assms)
  also have "... = (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)"
    by (simp add: rea_pre_RHS_design rea_post_RHS_design assms 
        unrest usubst R1_post_SRD R2c_preR R1_rea_impl R2c_rea_impl R2c_postR)
  finally show ?thesis ..
qed

lemma SRD_refine_intro:
  assumes
    "P is SRD" "Q is SRD"
    "`pre\<^sub>R(P) \<Rightarrow> pre\<^sub>R(Q)`" "`pre\<^sub>R(P) \<and> peri\<^sub>R(Q) \<Rightarrow> peri\<^sub>R(P)`" "`pre\<^sub>R(P) \<and> post\<^sub>R(Q) \<Rightarrow> post\<^sub>R(P)`"
  shows "P \<sqsubseteq> Q"
  by (metis SRD_reactive_tri_design assms(1) assms(2) assms(3) assms(4) assms(5) srdes_tri_refine_intro)

lemma SRD_refine_intro':
  assumes
    "P is SRD" "Q is SRD"
    "`pre\<^sub>R(P) \<Rightarrow> pre\<^sub>R(Q)`" "peri\<^sub>R(P) \<sqsubseteq> (pre\<^sub>R(P) \<and> peri\<^sub>R(Q))" "post\<^sub>R(P) \<sqsubseteq> (pre\<^sub>R(P) \<and> post\<^sub>R(Q))"
  shows "P \<sqsubseteq> Q"
  using assms by (rule_tac SRD_refine_intro, simp_all add: refBy_order)
 
lemma SRD_eq_intro:
  assumes
    "P is SRD" "Q is SRD" "pre\<^sub>R(P) = pre\<^sub>R(Q)" "peri\<^sub>R(P) = peri\<^sub>R(Q)" "post\<^sub>R(P) = post\<^sub>R(Q)"
  shows "P = Q"
  by (metis SRD_reactive_tri_design assms)

lemma srdes_tri_eq_iff:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> (P\<^sub>1 = Q\<^sub>1 \<and> (P\<^sub>1 \<and> Q\<^sub>2) = (Q\<^sub>1 \<and> P\<^sub>2) \<and> (P\<^sub>1 \<and> Q\<^sub>3) = (Q\<^sub>1 \<and> P\<^sub>3))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<longleftrightarrow> 
        (\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<and> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<sqsubseteq> \<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3))"
    by fastforce
  also have "... = (Q\<^sub>1 \<sqsubseteq> P\<^sub>1 \<and> P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2) \<and> P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>3) \<and> P\<^sub>1 \<sqsubseteq> Q\<^sub>1 \<and> Q\<^sub>2 \<sqsubseteq> (Q\<^sub>1 \<and> P\<^sub>2) \<and> Q\<^sub>3 \<sqsubseteq> (Q\<^sub>1 \<and> P\<^sub>3))"
    by (simp add: RHS_tri_design_refine' assms)
  also have "... = (P\<^sub>1 = Q\<^sub>1 \<and> P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2) \<and> P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>3) \<and> Q\<^sub>2 \<sqsubseteq> (Q\<^sub>1 \<and> P\<^sub>2) \<and> Q\<^sub>3 \<sqsubseteq> (Q\<^sub>1 \<and> P\<^sub>3))"
    by fastforce
  also have "... = (P\<^sub>1 = Q\<^sub>1 \<and> (P\<^sub>1 \<and> Q\<^sub>2) = (Q\<^sub>1 \<and> P\<^sub>2) \<and> (P\<^sub>1 \<and> Q\<^sub>3) = (Q\<^sub>1 \<and> P\<^sub>3))"
    apply (safe, simp_all)
    apply (meson eq_iff utp_pred_laws.inf_greatest utp_pred_laws.inf_le1)+
     apply (metis utp_pred_laws.inf_le2)+
    done
  finally show ?thesis .
qed

lemma rdes_tri_eq_intro:
  assumes "P\<^sub>1 = Q\<^sub>1" "(P\<^sub>1 \<and> Q\<^sub>2) = (Q\<^sub>1 \<and> P\<^sub>2)" "(P\<^sub>1 \<and> Q\<^sub>3) = (Q\<^sub>1 \<and> P\<^sub>3)"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)

lemma srdes_tri_eq_intro:
  assumes "P\<^sub>1 = Q\<^sub>1" "(P\<^sub>1 \<and> Q\<^sub>2) = (Q\<^sub>1 \<and> P\<^sub>2)" "(P\<^sub>1 \<and> Q\<^sub>3) = (Q\<^sub>1 \<and> P\<^sub>3)"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) design_export_pre wait'_cond_conj_exchange wait'_cond_idem)

lemma rdes_tri_eq_intro':
  assumes "P\<^sub>1 = Q\<^sub>1" "P\<^sub>2 = Q\<^sub>2" "P\<^sub>3 = Q\<^sub>3"
  shows "\<^bold>R(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  using assms by (simp)

lemma srdes_tri_eq_intro':
  assumes "P\<^sub>1 = Q\<^sub>1" "P\<^sub>2 = Q\<^sub>2" "P\<^sub>3 = Q\<^sub>3"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) = \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)"
  using assms by (simp)

subsection \<open> Closure laws \<close>

lemma SRD_srdes_skip [closure]: "II\<^sub>R is SRD"
  by (simp add: srdes_skip_def RHS_design_is_SRD unrest)

lemma SRD_seqr_closure [closure]:
  assumes "P is SRD" "Q is SRD"
  shows "(P ;; Q) is SRD"
proof -
  have "(P ;; Q) = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile> 
                       ((\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<or> (post\<^sub>R P ;; peri\<^sub>R Q)) \<diamondop> (post\<^sub>R P ;; post\<^sub>R Q))"
    by (simp add: SRD_composition_wp assms(1) assms(2))
  also have "... is SRD"
    by (rule RHS_design_is_SRD, simp_all add: wp_rea_def unrest)
  finally show ?thesis .
qed

lemma SRD_power_Suc [closure]: "P is SRD \<Longrightarrow> P\<^bold>^(Suc n) is SRD"
proof (induct n)
  case 0
  then show ?case
    by (simp)
next
  case (Suc n)
  then show ?case
    using SRD_seqr_closure by (simp add: SRD_seqr_closure upred_semiring.power_Suc) 
qed

lemma SRD_power_comp [closure]: "P is SRD \<Longrightarrow> P ;; P\<^bold>^n is SRD"
  by (metis SRD_power_Suc upred_semiring.power_Suc)

lemma uplus_SRD_closed [closure]: "P is SRD \<Longrightarrow> P\<^sup>+ is SRD"
  by (simp add: uplus_power_def closure)

lemma SRD_Sup_closure [closure]:
  assumes "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H" "A \<noteq> {}"
  shows "(\<Sqinter> A) is SRD"
proof -
  have "SRD (\<Sqinter> A) = (\<Sqinter> (SRD `A))"
    by (simp add: ContinuousD SRD_Continuous assms(2))
  also have "... = (\<Sqinter> A)"
    by (simp only: Healthy_carrier_image assms)
  finally show ?thesis by (simp add: Healthy_def)
qed

subsection \<open> Distribution laws \<close>

lemma RHS_tri_design_choice [rdes_def]: 
  "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqinter> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<or> Q\<^sub>2) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3))"
  apply (simp add: RHS_design_choice)
  apply (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"])
   apply (simp)
  apply (rel_auto)
  done

lemma RHS_tri_design_disj [rdes_def]: 
  "(\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<or> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)) = \<^bold>R\<^sub>s((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<or> Q\<^sub>2) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3))"
  by (simp add: RHS_tri_design_choice disj_upred_def)

lemma RHS_tri_design_sup [rdes_def]: 
  "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<squnion> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = \<^bold>R\<^sub>s((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2)) \<diamondop> ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<and> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)))"
  by (simp add: RHS_design_sup, rel_auto)

lemma RHS_tri_design_conj [rdes_def]: 
  "(\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<and> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)) = \<^bold>R\<^sub>s((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2)) \<diamondop> ((P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) \<and> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3)))"
  by (simp add: RHS_tri_design_sup conj_upred_def)

lemma SRD_UINF [rdes_def]:
  assumes "A \<noteq> {}" "A \<subseteq> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "\<Sqinter> A = \<^bold>R\<^sub>s((\<And> P\<in>A \<bullet> pre\<^sub>R(P)) \<turnstile> (\<Or> P\<in>A \<bullet> peri\<^sub>R(P)) \<diamondop> (\<Or> P\<in>A \<bullet> post\<^sub>R(P)))"
proof -
  have "\<Sqinter> A = \<^bold>R\<^sub>s(pre\<^sub>R(\<Sqinter> A) \<turnstile> peri\<^sub>R(\<Sqinter> A) \<diamondop> post\<^sub>R(\<Sqinter> A))"
    by (metis SRD_as_reactive_tri_design assms srdes_theory.healthy_inf srdes_theory.healthy_inf_def)
  also have "... = \<^bold>R\<^sub>s((\<And> P\<in>A \<bullet> pre\<^sub>R(P)) \<turnstile> (\<Or> P\<in>A \<bullet> peri\<^sub>R(P)) \<diamondop> (\<Or> P\<in>A \<bullet> post\<^sub>R(P)))"
    by (simp add: preR_INF periR_INF postR_INF assms)
  finally show ?thesis .
qed

lemma RHS_tri_design_USUP [rdes_def]:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i) \<diamondop> R(i))) = \<^bold>R\<^sub>s((\<Squnion> i \<in> A \<bullet> P(i)) \<turnstile> (\<Sqinter> i \<in> A \<bullet> Q(i)) \<diamondop> (\<Sqinter> i \<in> A \<bullet> R(i)))"
  by (subst RHS_INF[OF assms, THEN sym], simp add: design_UINF_mem assms, rel_auto)

lemma SRD_UINF_mem:
  assumes "A \<noteq> {}" "\<And> i. P i is SRD"
  shows "(\<Sqinter> i\<in>A \<bullet> P i) = \<^bold>R\<^sub>s((\<And> i\<in>A \<bullet> pre\<^sub>R(P i)) \<turnstile> (\<Or> i\<in>A \<bullet> peri\<^sub>R(P i)) \<diamondop> (\<Or> i\<in>A \<bullet> post\<^sub>R(P i)))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sqinter> (P ` A))"
    by (rel_auto) 
  also have " ... =  \<^bold>R\<^sub>s ((\<Squnion> Pa \<in> P ` A \<bullet> pre\<^sub>R Pa) \<turnstile> (\<Sqinter> Pa \<in> P ` A \<bullet> peri\<^sub>R Pa) \<diamondop> (\<Sqinter> Pa \<in> P ` A \<bullet> post\<^sub>R Pa))"
    by (subst rdes_def, simp_all add: assms image_subsetI)
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed

lemma RHS_tri_design_UINF_ind [rdes_def]:
  "(\<Sqinter> i \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) = \<^bold>R\<^sub>s((\<And> i \<bullet> P\<^sub>1 i) \<turnstile> (\<Or> i \<bullet> P\<^sub>2(i)) \<diamondop> (\<Or> i \<bullet> P\<^sub>3(i)))"
  by (rel_auto)

lemma cond_srea_form [rdes_def]:
  "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) =
   \<^bold>R\<^sub>s((P \<triangleleft> b \<triangleright>\<^sub>R R) \<turnstile> (Q\<^sub>1 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>1) \<diamondop> (Q\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>2))"
proof -
  have "\<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) = \<^bold>R\<^sub>s(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<triangleleft> R2c(\<lceil>b\<rceil>\<^sub>S\<^sub><) \<triangleright> \<^bold>R\<^sub>s(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)"
    by (pred_auto)
  also have "... = \<^bold>R\<^sub>s (P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>R R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)"
    by (simp add: RHS_cond lift_cond_srea_def)
  also have "... = \<^bold>R\<^sub>s ((P \<triangleleft> b \<triangleright>\<^sub>R R) \<turnstile> (Q\<^sub>1 \<diamondop> Q\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>1 \<diamondop> S\<^sub>2))"
    by (simp add: design_condr lift_cond_srea_def)
  also have "... = \<^bold>R\<^sub>s((P \<triangleleft> b \<triangleright>\<^sub>R R) \<turnstile> (Q\<^sub>1 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>1) \<diamondop> (Q\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>R S\<^sub>2))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma SRD_cond_srea [closure]:
  assumes "P is SRD" "Q is SRD"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is SRD"
proof -
  have "P \<triangleleft> b \<triangleright>\<^sub>R Q = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    by (simp add: SRD_reactive_tri_design assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R peri\<^sub>R Q) \<diamondop> (post\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R post\<^sub>R Q))"
    by (simp add: cond_srea_form)
  also have "... is SRD"
    by (simp add: RHS_tri_design_is_SRD lift_cond_srea_def unrest)
  finally show ?thesis .
qed

subsection \<open> Algebraic laws \<close>

lemma SRD_left_unit:
  assumes "P is SRD"
  shows "II\<^sub>R ;; P = P"
  by (simp add: SRD_composition_wp closure rdes wp C1 R1_negate_R1 R1_false 
      rpred trace_ident_left_periR trace_ident_left_postR SRD_reactive_tri_design assms)

lemma skip_srea_self_unit [simp]:
  "II\<^sub>R ;; II\<^sub>R = II\<^sub>R"
  by (simp add: SRD_left_unit closure)

lemma SRD_right_unit_tri_lemma:
  assumes "P is SRD"
  shows "P ;; II\<^sub>R = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> post\<^sub>R P)"
  by (simp add: SRD_composition_wp closure rdes wp rpred trace_ident_right_postR assms)

lemma Miracle_left_zero:
  assumes "P is SRD"
  shows "Miracle ;; P = Miracle"
proof -
  have "Miracle ;; P = \<^bold>R\<^sub>s(true \<turnstile> false) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: Miracle_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s(true \<turnstile> false)"
    by (simp add: RHS_design_composition unrest R1_false R2s_false R2s_true)
  also have "... = Miracle"
    by (simp add: Miracle_def)
  finally show ?thesis .
qed

lemma Chaos_left_zero:
  assumes "P is SRD"
  shows "(Chaos ;; P) = Chaos"
proof -
  have "Chaos ;; P = \<^bold>R\<^sub>s(false \<turnstile> true) ;; \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P))"
    by (simp add: Chaos_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s ((\<not> R1 true \<and> \<not> (R1 true \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s (pre\<^sub>R P))) \<turnstile>
                       R1 true ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s (cmt\<^sub>R P))))"
    by (simp add: RHS_design_composition unrest R2s_false R2s_true R1_false)
  also have "... = \<^bold>R\<^sub>s ((false \<and> \<not> (R1 true \<and> \<not> $wait\<acute>) ;; R1 (\<not> R2s (pre\<^sub>R P))) \<turnstile>
                       R1 true ;; ((\<exists> $st \<bullet> \<lceil>II\<rceil>\<^sub>D) \<triangleleft> $wait \<triangleright> R1 (R2s (cmt\<^sub>R P))))"
    by (simp add: RHS_design_conj_neg_R1_pre)
  also have "... = \<^bold>R\<^sub>s(true)"
    by (simp add: design_false_pre)
  also have "... = \<^bold>R\<^sub>s(false \<turnstile> true)"
    by (simp add: design_def)
  also have "... = Chaos"
    by (simp add: Chaos_def)
  finally show ?thesis .
qed

lemma SRD_right_Chaos_tri_lemma:
  assumes "P is SRD"
  shows "P ;; Chaos = \<^bold>R\<^sub>s (((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<and> post\<^sub>R P wp\<^sub>r false) \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> false)"
  by (simp add: SRD_composition_wp closure rdes assms wp, rel_auto)

lemma SRD_right_Miracle_tri_lemma:
  assumes "P is SRD"
  shows "P ;; Miracle = \<^bold>R\<^sub>s ((\<not>\<^sub>r pre\<^sub>R P) wp\<^sub>r false \<turnstile> (\<exists> $st\<acute> \<bullet> peri\<^sub>R P) \<diamondop> false)"
  by (simp add: SRD_composition_wp closure rdes assms wp, rel_auto)

text \<open> Stateful reactive designs are left unital \<close>

interpretation srdes_left_unital: utp_theory_left_unital "SRD" "II\<^sub>R"
  by (unfold_locales, simp_all add: closure SRD_left_unit)

subsection \<open> Recursion laws \<close>

lemma mono_srd_iter:
  assumes "mono F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "mono (\<lambda>X. \<^bold>R\<^sub>s(pre\<^sub>R(F X) \<turnstile> peri\<^sub>R(F X) \<diamondop> post\<^sub>R (F X)))"
  apply (rule monoI)
  apply (rule srdes_tri_refine_intro')
  apply (meson assms(1) monoE preR_antitone utp_pred_laws.le_infI2)
  apply (meson assms(1) monoE periR_monotone utp_pred_laws.le_infI2)
  apply (meson assms(1) monoE postR_monotone utp_pred_laws.le_infI2)
done

lemma mu_srd_SRD:
  assumes "mono F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<mu> X \<bullet> \<^bold>R\<^sub>s (pre\<^sub>R (F X) \<turnstile> peri\<^sub>R (F X) \<diamondop> post\<^sub>R (F X))) is SRD"
  apply (subst gfp_unfold)
  apply (simp add: mono_srd_iter assms)
  apply (rule RHS_tri_design_is_SRD)
  apply (simp_all add: unrest)
done

lemma mu_srd_iter:
  assumes "mono F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "(\<mu> X \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(F(X)) \<turnstile> peri\<^sub>R(F(X)) \<diamondop> post\<^sub>R(F(X)))) = F(\<mu> X \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(F(X)) \<turnstile> peri\<^sub>R(F(X)) \<diamondop> post\<^sub>R(F(X))))"
  apply (subst gfp_unfold)
   apply (simp add: mono_srd_iter assms)
  apply (subst SRD_as_reactive_tri_design[THEN sym])
  apply (simp add: Healthy_apply_closed SRD_as_reactive_design SRD_reactive_design_alt assms(1) assms(2) mu_srd_SRD)
  done

lemma mu_srd_form:
  assumes "mono F" "F \<in> \<lbrakk>SRD\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>SRD\<rbrakk>\<^sub>H"
  shows "\<mu>\<^sub>R F = (\<mu> X \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(F(X)) \<turnstile> peri\<^sub>R(F(X)) \<diamondop> post\<^sub>R(F(X))))"
proof -
  have 1: "F (\<mu> X \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R (F X) \<turnstile> peri\<^sub>R(F X) \<diamondop> post\<^sub>R (F X))) is SRD"
    by (simp add: Healthy_apply_closed assms(1) assms(2) mu_srd_SRD)
  have 2:"Mono\<^bsub>utp_order SRD\<^esub> F"
    by (simp add: assms(1) mono_Monotone_utp_order)
  hence 3:"\<mu>\<^sub>R F = F (\<mu>\<^sub>R F)"
    by (simp add: srdes_theory.LFP_unfold[THEN sym] assms)
  hence "\<^bold>R\<^sub>s(pre\<^sub>R (F (F (\<mu>\<^sub>R F))) \<turnstile> peri\<^sub>R (F (F (\<mu>\<^sub>R F))) \<diamondop> post\<^sub>R (F (F (\<mu>\<^sub>R F)))) = \<mu>\<^sub>R F"
    using SRD_reactive_tri_design by force
  hence "(\<mu> X \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R (F X) \<turnstile> peri\<^sub>R(F X) \<diamondop> post\<^sub>R (F X))) \<sqsubseteq> F (\<mu>\<^sub>R F)"
    by (simp add: 2 srdes_theory.weak.LFP_lemma3 gfp_upperbound assms)
  thus ?thesis
    using assms 1 3 srdes_theory.weak.LFP_lowerbound eq_iff mu_srd_iter
    by (metis (mono_tags, lifting))
qed

lemma Monotonic_SRD_comp [closure]: "Monotonic ((;;) P \<circ> SRD)"
  by (simp add: mono_def R1_R2c_is_R2 R2_mono R3h_mono RD1_mono RD2_mono RHS_def SRD_def seqr_mono)

end