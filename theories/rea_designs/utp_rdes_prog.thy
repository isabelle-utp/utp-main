section \<open> Reactive Design Programs \<close>

theory utp_rdes_prog
  imports 
    utp_rdes_normal
    utp_rdes_tactics
    utp_rdes_parallel
begin

subsection \<open> State substitution \<close>

lemma srd_subst_RHS_tri_design [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) = \<^bold>R\<^sub>s((\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P) \<turnstile> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> Q) \<diamondop> (\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> R))"
  by (rel_auto)

lemma srd_subst_SRD_closed [closure]: 
  assumes "P is SRD"
  shows "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P is SRD"
proof -
  have "SRD(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> (SRD P)) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> (SRD P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed

lemma preR_srd_subst [rdes]:
  "pre\<^sub>R(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> pre\<^sub>R(P)"
  by (rel_auto)

lemma periR_srd_subst [rdes]:
  "peri\<^sub>R(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> peri\<^sub>R(P)"
  by (rel_auto)

lemma postR_srd_subst [rdes]:
  "post\<^sub>R(\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> post\<^sub>R(P)"
  by (rel_auto)

lemma srd_subst_NSRD_closed [closure]: 
  assumes "P is NSRD"
  shows "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P is NSRD"
  by (rule NSRD_RC_intro, simp_all add: closure rdes assms unrest)

subsection \<open> Assignment \<close>

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

lemma assigns_srd_RHS_tri_des [rdes_def]:
  "\<langle>\<sigma>\<rangle>\<^sub>R = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> \<langle>\<sigma>\<rangle>\<^sub>r)"
  by (rel_auto)

lemma assigns_srd_NSRD_closed [closure]: "\<langle>\<sigma>\<rangle>\<^sub>R is NSRD"
  by (simp add: rdes_def closure unrest)

lemma preR_assigns_srd [rdes]: "pre\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = true\<^sub>r"
  by (simp add: rdes_def rdes closure)
    
lemma periR_assigns_srd [rdes]: "peri\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = false"
  by (simp add: rdes_def rdes closure)

lemma postR_assigns_srd [rdes]: "post\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>R) = \<langle>\<sigma>\<rangle>\<^sub>r"
  by (simp add: rdes_def rdes closure rpred)

subsection \<open> Conditional \<close>

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

lemma NSRD_cond_srea [closure]:
  assumes "P is NSRD" "Q is NSRD"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is NSRD"
proof (rule NSRD_RC_intro)
  show "P \<triangleleft> b \<triangleright>\<^sub>R Q is SRD"
    by (simp add: closure assms)
  show "pre\<^sub>R (P \<triangleleft> b \<triangleright>\<^sub>R Q) is RC"
  proof -
    have 1:"(\<lceil>\<not> b\<rceil>\<^sub>S\<^sub>< \<or> \<not>\<^sub>r pre\<^sub>R P) ;; R1(true) = (\<lceil>\<not> b\<rceil>\<^sub>S\<^sub>< \<or> \<not>\<^sub>r pre\<^sub>R P)"
      by (metis (no_types, lifting) NSRD_neg_pre_unit aext_not assms(1) seqr_or_distl st_lift_R1_true_right)
    have 2:"(\<lceil>b\<rceil>\<^sub>S\<^sub>< \<or> \<not>\<^sub>r pre\<^sub>R Q) ;; R1(true) = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<or> \<not>\<^sub>r pre\<^sub>R Q)"
      by (simp add: NSRD_neg_pre_unit assms seqr_or_distl st_lift_R1_true_right)
    show ?thesis
      by (simp add: rdes closure assms)
  qed
  show "$st\<acute> \<sharp> peri\<^sub>R (P \<triangleleft> b \<triangleright>\<^sub>R Q)"
   by (simp add: rdes assms closure unrest)
qed

subsection \<open> Alternation \<close>
  
definition AlternateR 
  :: "'a set \<Rightarrow> ('a \<Rightarrow> 's upred) \<Rightarrow> ('a \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp) \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" where
[upred_defs]:
"AlternateR A g P = \<^bold>R\<^sub>s(((\<Or> i\<in>A \<bullet> [g(i)]\<^sub>S\<^sub><) \<and> (\<And> i\<in>A \<bullet> [g(i)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R(P i))) 
                       \<turnstile> (\<Or> i\<in>A \<bullet> [g(i)]\<^sub>S\<^sub>< \<and> peri\<^sub>R(P i)) 
                       \<diamondop> (\<Or> i\<in>A \<bullet> [g(i)]\<^sub>S\<^sub>< \<and> post\<^sub>R(P i)))"

syntax
  "_altind_srd" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if\<^sub>R _\<in>_ \<bullet> _ \<rightarrow> _ fi")
  
translations
  "_altind_srd x A g P" => "CONST AlternateR A (\<lambda> x. g) (\<lambda> x. P)"
  "_altind_srd x A g P" <= "CONST AlternateR A (\<lambda> x. g) (\<lambda> x'. P)"
  
lemma AlternateR_NSRD_closed: 
  assumes "\<And> i. P(i) is NSRD"
  shows "AlternateR A g P is NSRD"
proof (cases "A = {}")
  case True
  then show ?thesis 
    by (simp add: AlternateR_def closure unrest) 
next
  case False
  then show ?thesis
    by (simp add: AlternateR_def closure unrest assms)
qed
  
lemma AlternateR_rdes_def [rdes_def]: 
  assumes "\<And> i. P\<^sub>1(i) is RR" "\<And> i. P\<^sub>2(i) is RR" "\<And> i. P\<^sub>3(i) is RR"
  shows
  "if\<^sub>R i \<in> A \<bullet> g(i) \<rightarrow> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) fi = 
    \<^bold>R\<^sub>s(((\<Or> i\<in>A \<bullet> [g(i)]\<^sub>S\<^sub><) \<and> (\<And> i\<in>A \<bullet> [g(i)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P\<^sub>1 i)) 
        \<turnstile> (\<Or> i\<in>A \<bullet> [g(i)]\<^sub>S\<^sub>< \<and> P\<^sub>2 i) 
        \<diamondop> (\<Or> i\<in>A \<bullet> [g(i)]\<^sub>S\<^sub>< \<and> P\<^sub>3 i))"
  by (simp add: AlternateR_def rdes closure assms, rel_auto)

subsection \<open> Choose \<close>

definition choose_srd :: "('s,'t::trace,'\<alpha>) hrel_rsp" ("choose\<^sub>R") where
[upred_defs, rdes_def]: "choose\<^sub>R = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> true\<^sub>r)"
  
lemma preR_choose [rdes]: "pre\<^sub>R(choose\<^sub>R) = true\<^sub>r"
  by (rel_auto)

lemma periR_choose [rdes]: "peri\<^sub>R(choose\<^sub>R) = false"
  by (rel_auto)

lemma postR_choose [rdes]: "post\<^sub>R(choose\<^sub>R) = true\<^sub>r"
  by (rel_auto)
    
lemma choose_srd_SRD [closure]: "choose\<^sub>R is SRD"
  by (simp add: choose_srd_def closure unrest)

lemma NSRD_choose_srd [closure]: "choose\<^sub>R is NSRD"
  by (rule NSRD_intro, simp_all add: closure unrest rdes)

subsection \<open> State Abstraction \<close>

definition state_srea ::
  "'s itself \<Rightarrow> ('s,'t::trace,'\<alpha>,'\<beta>) rel_rsp \<Rightarrow> (unit,'t,'\<alpha>,'\<beta>) rel_rsp" where
[upred_defs]: "state_srea t P = \<langle>\<exists> {$st,$st\<acute>} \<bullet> P\<rangle>\<^sub>S"

syntax
  "_state_srea" :: "type \<Rightarrow> logic \<Rightarrow> logic" ("state _ \<bullet> _" [0,200] 200)

translations
  "state 'a \<bullet> P" == "CONST state_srea TYPE('a) P"

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

lemma NSRD_state_srea [closure]: "P is NSRD \<Longrightarrow> state 'a \<bullet> P is NSRD"
  by (metis Healthy_def NSRD_is_RD3 NSRD_is_SRD RD3_state_srea SRD_RD3_implies_NSRD SRD_state_srea)

lemma preR_state_srea [rdes]: "pre\<^sub>R(state 'a \<bullet> P) = \<langle>\<forall> {$st,$st\<acute>} \<bullet> pre\<^sub>R(P)\<rangle>\<^sub>S"
  by (simp add: state_srea_def, rel_auto)

lemma periR_state_srea [rdes]: "peri\<^sub>R(state 'a \<bullet> P) = state 'a \<bullet> peri\<^sub>R(P)"
  by (rel_auto)

lemma postR_state_srea [rdes]: "post\<^sub>R(state 'a \<bullet> P) = state 'a \<bullet> post\<^sub>R(P)"
  by (rel_auto)

subsection \<open> Iteration Construction \<close>
  
definition IterateR
  :: "'a set \<Rightarrow> ('a \<Rightarrow> 's upred) \<Rightarrow> ('a \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp) \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp"
where "IterateR A g P = (\<mu>\<^sub>R X \<bullet> (if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> P(i) fi ;; X) \<triangleleft> (\<Or> i\<in>A \<bullet> g(i)) \<triangleright>\<^sub>R II\<^sub>R)"
   
syntax
  "_iter_srd" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("do\<^sub>R _\<in>_ \<bullet> _ \<rightarrow> _ fi")
  
translations
  "_iter_srd x A g P" => "CONST IterateR A (\<lambda> x. g) (\<lambda> x. P)"
  "_iter_srd x A g P" <= "CONST IterateR A (\<lambda> x. g) (\<lambda> x'. P)"
  
lemma IterateR_empty: 
  "do\<^sub>R i\<in>{} \<bullet> g(i) \<rightarrow> P(i) fi = II\<^sub>R"
  by (simp add: IterateR_def srd_mu_equiv closure rpred gfp_const)

subsection \<open> Substitution Laws \<close>
  
lemma srd_subst_Chaos [usubst]:
  "\<sigma> \<dagger>\<^sub>S Chaos = Chaos"
  by (rdes_simp)

lemma srd_subst_Miracle [usubst]:
  "\<sigma> \<dagger>\<^sub>S Miracle = Miracle"
  by (rdes_simp)

lemma srd_subst_skip [usubst]:
  "\<sigma> \<dagger>\<^sub>S II\<^sub>R = \<langle>\<sigma>\<rangle>\<^sub>R"
  by (rdes_eq)
    
lemma srd_subst_assigns [usubst]:
  "\<sigma> \<dagger>\<^sub>S \<langle>\<rho>\<rangle>\<^sub>R = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>R"
  by (rdes_eq)

subsection \<open> Algebraic Laws \<close>

theorem assigns_srd_id: "\<langle>id\<rangle>\<^sub>R = II\<^sub>R"
  by (rdes_eq)

theorem assigns_srd_comp: "\<langle>\<sigma>\<rangle>\<^sub>R ;; \<langle>\<rho>\<rangle>\<^sub>R = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>R"
  by (rdes_eq)

theorem assigns_srd_Miracle: "\<langle>\<sigma>\<rangle>\<^sub>R ;; Miracle = Miracle"
  by (rdes_eq)

theorem assigns_srd_Chaos: "\<langle>\<sigma>\<rangle>\<^sub>R ;; Chaos = Chaos"
  by (rdes_eq)

theorem assigns_srd_cond : "\<langle>\<sigma>\<rangle>\<^sub>R \<triangleleft> b \<triangleright>\<^sub>R \<langle>\<rho>\<rangle>\<^sub>R = \<langle>\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>\<rangle>\<^sub>R"
  by (rdes_eq)

theorem assigns_srd_left_seq:
  assumes "P is NSRD"
  shows "\<langle>\<sigma>\<rangle>\<^sub>R ;; P = \<sigma> \<dagger>\<^sub>S P"
  by (rdes_simp cls: assms)

lemma AlternateR_empty: 
  "if\<^sub>R i\<in>{} \<bullet> g(i) \<rightarrow> P(i) fi = Chaos"
  by (simp add: AlternateR_def Chaos_def, rel_auto)

lemma AlternateR_Chaos: 
  "if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> Chaos fi = Chaos"
  by (simp add: AlternateR_def Chaos_def, rel_auto)

lemma choose_srd_par:
  "choose\<^sub>R \<parallel>\<^sub>R choose\<^sub>R = choose\<^sub>R"
  by (rdes_eq)

subsection \<open> Lifting designs to reactive designs \<close>

definition des_rea_lift :: "'s hrel_des \<Rightarrow> ('s,'t::trace,'\<alpha>) hrel_rsp" ("\<^bold>R\<^sub>D") where
[upred_defs]: "\<^bold>R\<^sub>D(P) = \<^bold>R\<^sub>s(\<lceil>pre\<^sub>D(P)\<rceil>\<^sub>S \<turnstile> (false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>post\<^sub>D(P)\<rceil>\<^sub>S)))"

definition des_rea_drop :: "('s,'t::trace,'\<alpha>) hrel_rsp \<Rightarrow> 's hrel_des" ("\<^bold>D\<^sub>R") where
[upred_defs]: "\<^bold>D\<^sub>R(P) = \<lfloor>(pre\<^sub>R(P))\<lbrakk>$tr/$tr\<acute>\<rbrakk> \<restriction>\<^sub>v $st\<rfloor>\<^sub>S\<^sub><
                     \<turnstile>\<^sub>n \<lfloor>(post\<^sub>R(P))\<lbrakk>$tr/$tr\<acute>\<rbrakk> \<restriction>\<^sub>v {$st,$st\<acute>}\<rfloor>\<^sub>S"

lemma ndesign_rea_lift_inverse: "\<^bold>D\<^sub>R(\<^bold>R\<^sub>D(p \<turnstile>\<^sub>n Q)) = p \<turnstile>\<^sub>n Q"
  apply (simp add: des_rea_lift_def des_rea_drop_def rea_pre_RHS_design rea_post_RHS_design)
  apply (simp add: R1_def R2c_def R2s_def usubst unrest)
  apply (rel_auto)
  done

lemma ndesign_rea_lift_injective:
  assumes "P is \<^bold>N" "Q is \<^bold>N" "\<^bold>R\<^sub>D P = \<^bold>R\<^sub>D Q" (is "?RP(P) = ?RQ(Q)")
  shows "P = Q"
proof -
  have "?RP(\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) = ?RQ(\<lfloor>pre\<^sub>D(Q)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(Q))"
    by (simp add: ndesign_form assms)
  hence "\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P) = \<lfloor>pre\<^sub>D(Q)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(Q)"
    by (metis ndesign_rea_lift_inverse)
  thus ?thesis
    by (simp add: ndesign_form assms)
qed
        
lemma des_rea_lift_closure [closure]: "\<^bold>R\<^sub>D(P) is SRD"
  by (simp add: des_rea_lift_def RHS_design_is_SRD unrest)

lemma preR_des_rea_lift [rdes]:
  "pre\<^sub>R(\<^bold>R\<^sub>D(P)) = R1(\<lceil>pre\<^sub>D(P)\<rceil>\<^sub>S)"
  by (rel_auto)

lemma periR_des_rea_lift [rdes]:
  "peri\<^sub>R(\<^bold>R\<^sub>D(P)) = (false \<triangleleft> \<lceil>pre\<^sub>D(P)\<rceil>\<^sub>S \<triangleright> ($tr \<le>\<^sub>u $tr\<acute>))"
  by (rel_auto)

lemma postR_des_rea_lift [rdes]:
  "post\<^sub>R(\<^bold>R\<^sub>D(P)) = ((true \<triangleleft> \<lceil>pre\<^sub>D(P)\<rceil>\<^sub>S \<triangleright> (\<not> $tr \<le>\<^sub>u $tr\<acute>)) \<Rightarrow> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>post\<^sub>D(P)\<rceil>\<^sub>S))"
  apply (rel_auto) using minus_zero_eq by blast

lemma ndes_rea_lift_closure [closure]:
  assumes "P is \<^bold>N"
  shows "\<^bold>R\<^sub>D(P) is NSRD"
proof -
  obtain p Q where P: "P = (p \<turnstile>\<^sub>n Q)"
    by (metis H1_H3_commute H1_H3_is_normal_design H1_idem Healthy_def assms)
  show ?thesis
    apply (rule NSRD_intro)
      apply (simp_all add: closure rdes unrest P)
    apply (rel_auto)
    done
qed

lemma R_D_mono:
  assumes "P is \<^bold>H" "Q is \<^bold>H" "P \<sqsubseteq> Q"
  shows "\<^bold>R\<^sub>D(P) \<sqsubseteq> \<^bold>R\<^sub>D(Q)"
  apply (simp add: des_rea_lift_def)
  apply (rule srdes_tri_refine_intro')
    apply (auto intro: H1_H2_refines assms aext_mono)
   apply (rel_auto)
  apply (metis (no_types, hide_lams) aext_mono assms(3) design_post_choice
      semilattice_sup_class.sup.orderE utp_pred_laws.inf.coboundedI1 utp_pred_laws.inf.commute utp_pred_laws.sup.order_iff)
  done

text {* Homomorphism laws *}

lemma R_D_Miracle:
  "\<^bold>R\<^sub>D(\<top>\<^sub>D) = Miracle"
  by (simp add: Miracle_def, rel_auto)

lemma R_D_Chaos:
  "\<^bold>R\<^sub>D(\<bottom>\<^sub>D) = Chaos"
proof -
  have "\<^bold>R\<^sub>D(\<bottom>\<^sub>D) = \<^bold>R\<^sub>D(false \<turnstile>\<^sub>r true)"
    by (rel_auto)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr))"
    by (simp add: Chaos_def des_rea_lift_def alpha)
  also have "... = \<^bold>R\<^sub>s (true)"
    by (rel_auto)
  also have "... = Chaos"
    by (simp add: Chaos_def design_false_pre)
  finally show ?thesis .
qed

lemma R_D_inf:
  "\<^bold>R\<^sub>D(P \<sqinter> Q) = \<^bold>R\<^sub>D(P) \<sqinter> \<^bold>R\<^sub>D(Q)"
  by (rule antisym, rel_auto+)

lemma R_D_cond:
  "\<^bold>R\<^sub>D(P \<triangleleft> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> Q) = \<^bold>R\<^sub>D(P) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>D(Q)"
  by (rule antisym, rel_auto+)
   
lemma R_D_seq_ndesign:
  "\<^bold>R\<^sub>D(p\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>1) ;; \<^bold>R\<^sub>D(p\<^sub>2 \<turnstile>\<^sub>n Q\<^sub>2) = \<^bold>R\<^sub>D((p\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>1) ;; (p\<^sub>2 \<turnstile>\<^sub>n Q\<^sub>2))"
  apply (rule antisym)
   apply (rule SRD_refine_intro)
       apply (simp_all add: closure rdes ndesign_composition_wp)
  using dual_order.trans apply (rel_blast)
  using dual_order.trans apply (rel_blast)
   apply (rel_auto)
  apply (rule SRD_refine_intro)
      apply (simp_all add: closure rdes ndesign_composition_wp)
    apply (rel_auto)
   apply (rel_auto)
  apply (rel_auto)
  done

lemma R_D_seq:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "\<^bold>R\<^sub>D(P) ;; \<^bold>R\<^sub>D(Q) = \<^bold>R\<^sub>D(P ;; Q)"
  by (metis R_D_seq_ndesign assms ndesign_form)

text {* Thes laws are applicable only when there is no further alphabet extension *}

lemma R_D_skip:
  "\<^bold>R\<^sub>D(II\<^sub>D) = (II\<^sub>R :: ('s,'t::trace,unit) hrel_rsp)"
  apply (rel_auto) using minus_zero_eq by blast+
  
lemma R_D_assigns:
  "\<^bold>R\<^sub>D(\<langle>\<sigma>\<rangle>\<^sub>D) = (\<langle>\<sigma>\<rangle>\<^sub>R :: ('s,'t::trace,unit) hrel_rsp)"
  by (simp add: assigns_d_def des_rea_lift_def alpha assigns_srd_RHS_tri_des, rel_auto)

end