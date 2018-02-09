theory utp_rdes_prog
  imports utp_rdes_normal
begin

definition assigns_srd :: "'s usubst \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp" ("\<langle>_\<rangle>\<^sub>R") where
[upred_defs]: "assigns_srd \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S))"

syntax
  "_assign_srd" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') :=\<^sub>R '(_')")  
  "_assign_srd" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>R" 90)

translations
  "_assign_srd xs vs" => "CONST assigns_srd (_mk_usubst (CONST id) xs vs)"
  "_assign_srd x v" <= "CONST assigns_srd (CONST subst_upd (CONST id) x v)"
  "_assign_srd x v" <= "_assign_srd (_spvar x) v"
  "x,y :=\<^sub>R u,v" <= "CONST assigns_srd (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

definition choose_srd :: "('s,'t::trace,'\<alpha>) hrel_rsp" ("choose\<^sub>R") where
[upred_defs, rdes_def]: "choose\<^sub>R = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> true\<^sub>r)"
  
definition state_srea ::
  "'s itself \<Rightarrow> ('s,'t::trace,'\<alpha>,'\<beta>) rel_rsp \<Rightarrow> (unit,'t,'\<alpha>,'\<beta>) rel_rsp" where
[upred_defs]: "state_srea t P = \<langle>\<exists> {$st,$st\<acute>} \<bullet> P\<rangle>\<^sub>S"

syntax
  "_state_srea" :: "type \<Rightarrow> logic \<Rightarrow> logic" ("state _ \<bullet> _" [0,200] 200)

translations
  "state 'a \<bullet> P" == "CONST state_srea TYPE('a) P"

lemma assigns_srd_RHS_tri_des [rdes_def]:
  "\<langle>\<sigma>\<rangle>\<^sub>R = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> \<langle>\<sigma>\<rangle>\<^sub>r)"
  by (rel_auto)

lemma preR_assigns_srd [rdes]: "pre\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = true\<^sub>r"
  by (simp add: assigns_srd_def rea_pre_RHS_design usubst R2c_true)
    
lemma periR_assigns_srd [rdes]: "peri\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = false"
  by (simp add: assigns_srd_RHS_tri_des rea_peri_RHS_design usubst R2c_false R1_false)

lemma postR_assigns_srd [rdes]: "post\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S)"
  apply (rel_auto) using minus_zero_eq by blast

lemma R1_state_srea: "R1(state 'a \<bullet> P) = (state 'a \<bullet> R1(P))"
  by (rel_auto)

lemma R2c_state_srea: "R2c(state 'a \<bullet> P) = (state 'a \<bullet> R2c(P))"
  by (rel_auto)

lemma R3h_state_srea: "R3h(state 'a \<bullet> P) = (state 'a \<bullet> R3h(P))"
  by (rel_auto)
   
lemma RD1_state_srea: "RD1(state 'a \<bullet> P) = (state 'a \<bullet> RD1(P))"
  by (rel_auto)    

lemma RD2_state_srea: "RD2(state 'a \<bullet> P) = (state 'a \<bullet> RD2(P))"
  by (rel_auto)    

lemma RD3_state_srea: "RD3(state 'a \<bullet> P) = (state 'a \<bullet> RD3(P))"
  by (rel_auto, blast+)    
 
lemma SRD_state_srea [closure]: "P is SRD \<Longrightarrow> state 'a \<bullet> P is SRD"
  by (simp add: Healthy_def R1_state_srea R2c_state_srea R3h_state_srea RD1_state_srea RD2_state_srea RHS_def SRD_def)
    
lemma preR_state_srea [rdes]: "pre\<^sub>R(state 'a \<bullet> P) = \<langle>\<forall> {$st,$st\<acute>} \<bullet> pre\<^sub>R(P)\<rangle>\<^sub>S"
  by (simp add: state_srea_def, rel_auto)

lemma periR_state_srea [rdes]: "peri\<^sub>R(state 'a \<bullet> P) = state 'a \<bullet> peri\<^sub>R(P)"
  by (rel_auto)

lemma postR_state_srea [rdes]: "post\<^sub>R(state 'a \<bullet> P) = state 'a \<bullet> post\<^sub>R(P)"
  by (rel_auto)

lemma preR_choose [rdes]: "pre\<^sub>R(choose\<^sub>R) = true\<^sub>r"
  by (rel_auto)

lemma periR_choose [rdes]: "peri\<^sub>R(choose\<^sub>R) = false"
  by (rel_auto)

lemma postR_choose [rdes]: "post\<^sub>R(choose\<^sub>R) = true\<^sub>r"
  by (rel_auto)
    
lemma choose_srd_SRD [closure]: "choose\<^sub>R is SRD"
  by (simp add: choose_srd_def closure unrest)

lemma preR_cond_srea [rdes]:
  "pre\<^sub>R(P \<triangleleft> b \<triangleright>\<^sub>R Q) = ([b]\<^sub>S\<^sub>< \<and> pre\<^sub>R(P) \<or> [\<not>b]\<^sub>S\<^sub>< \<and> pre\<^sub>R(Q))"
  by (rel_auto)

lemma periR_cond_srea [rdes]:
  assumes "P is SRD" "Q is SRD"
  shows "peri\<^sub>R(P \<triangleleft> b \<triangleright>\<^sub>R Q) = ([b]\<^sub>S\<^sub>< \<and> peri\<^sub>R(P) \<or> [\<not>b]\<^sub>S\<^sub>< \<and> peri\<^sub>R(Q))"
proof -
  have "peri\<^sub>R(P \<triangleleft> b \<triangleright>\<^sub>R Q) = peri\<^sub>R(R1(P) \<triangleleft> b \<triangleright>\<^sub>R R1(Q))"
    by (simp add: Healthy_if SRD_healths assms)
  thus ?thesis
    by (rel_auto)
qed

lemma postR_cond_srea [rdes]:
  assumes "P is SRD" "Q is SRD"
  shows "post\<^sub>R(P \<triangleleft> b \<triangleright>\<^sub>R Q) = ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R(P) \<or> [\<not>b]\<^sub>S\<^sub>< \<and> post\<^sub>R(Q))"
proof -
  have "post\<^sub>R(P \<triangleleft> b \<triangleright>\<^sub>R Q) = post\<^sub>R(R1(P) \<triangleleft> b \<triangleright>\<^sub>R R1(Q))"
    by (simp add: Healthy_if SRD_healths assms)
  thus ?thesis
    by (rel_auto)
qed

end