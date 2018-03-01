section \<open> Circus and CSP Actions\<close>

theory utp_circus_actions
  imports 
    utp_circus_extchoice
begin

subsection \<open> Conditionals \<close>

lemma NCSP_cond_srea [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is NCSP"
  by (rule NCSP_NSRD_intro, simp_all add: closure rdes assms unrest)

subsection \<open> Guarded commands \<close>

lemma GuardedCommR_NCSP_closed [closure]: 
  assumes "P is NCSP"
  shows "g \<rightarrow>\<^sub>R P is NCSP"
  by (simp add: gcmd_def closure assms)

subsection \<open> Alternation \<close>

lemma AlternateR_NCSP_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P(i) is NCSP" "Q is NCSP"
  shows "(if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> P(i) else Q fi) is NCSP"
proof (cases "A = {}")
  case True
  then show ?thesis
    by (simp add: assms)
next
  case False
  then show ?thesis
    by (simp add: AlternateR_def closure assms)
qed

subsection \<open> Assignment \<close>

definition AssignsCSP :: "'\<sigma> usubst \<Rightarrow> ('\<sigma>, '\<phi>) action" ("\<langle>_\<rangle>\<^sub>C") where
[upred_defs]: "AssignsCSP \<sigma> = \<^bold>R\<^sub>s(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S))"

syntax
  "_assigns_csp" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') :=\<^sub>C '(_')")  
  "_assigns_csp" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>C" 90)

translations
  "_assigns_csp xs vs" => "CONST AssignsCSP (_mk_usubst (CONST id) xs vs)"
  "_assigns_csp x v" <= "CONST AssignsCSP (CONST subst_upd (CONST id) x v)"
  "_assigns_csp x v" <= "_assigns_csp (_spvar x) v"
  "x,y :=\<^sub>C u,v" <= "CONST AssignsCSP (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

lemma preR_AssignsCSP [rdes]: "pre\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = true\<^sub>r"
  by (rel_auto)

lemma periR_AssignsCSP [rdes]: "peri\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = false"
  by (rel_auto)

lemma postR_AssignsCSP [rdes]: "post\<^sub>R(\<langle>\<sigma>\<rangle>\<^sub>C) = \<Phi>(true,\<sigma>,\<langle>\<rangle>)"
  by (rel_auto)

lemma AssignsCSP_rdes_def [rdes_def] : "\<langle>\<sigma>\<rangle>\<^sub>C = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> \<Phi>(true,\<sigma>,\<langle>\<rangle>))"
  by (rel_auto)

lemma AssignsCSP_CSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP"
  by (simp add: AssignsCSP_def RHS_tri_design_is_SRD unrest)

lemma AssignsCSP_CSP3 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP3"
  by (rule CSP3_intro, simp add: closure, rel_auto)

lemma AssignsCSP_CSP4 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CSP4"
  by (rule CSP4_intro, simp add: closure, rel_auto+)

lemma AssignsCSP_NCSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is NCSP"
  by (simp add: AssignsCSP_CSP AssignsCSP_CSP3 AssignsCSP_CSP4 NCSP_intro)

lemma AssignsCSP_ICSP [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is ICSP"
  apply (rule ICSP_intro, simp add: closure, simp add: rdes_def)
  apply (rule ISRD1_rdes_intro)
  apply (simp_all add: closure)
  apply (rel_auto)
done

subsection \<open> Assignment with update \<close>

text \<open> There are different collections that we would like to assign to, but they all have different
  types and perhaps more importantly different conditions on the update being well defined. For example,
  for a list well-definedness equates to the index being less than the length etc. Thus we here set
  up a polymorphic constant for CSP assignment updates that can be specialised to different types. \<close>
    
definition AssignCSP_update :: 
  "('f \<Rightarrow> 'k set) \<Rightarrow> ('f \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 'f) \<Rightarrow> ('f \<Longrightarrow> '\<sigma>) \<Rightarrow> 
   ('k, '\<sigma>) uexpr \<Rightarrow> ('v, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs,rdes_def]: "AssignCSP_update domf updatef x k v = 
  \<^bold>R\<^sub>s([k \<in>\<^sub>u uop domf (&x)]\<^sub>S\<^sub>< \<turnstile> false \<diamondop> \<Phi>(true,[x \<mapsto>\<^sub>s trop updatef (&x) k v], \<langle>\<rangle>))"

text \<open> All different assignment updates have the same syntax; the type resolves which implementation
  to use. \<close>
  
syntax
  "_csp_assign_upd" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_[_] :=\<^sub>C _" [0,0,72] 72)

translations
  "x[k] :=\<^sub>C v" == "CONST AssignCSP_update (CONST udom) (CONST uupd) x k v"

lemma AssignCSP_update_CSP [closure]:
  "AssignCSP_update domf updatef x k v is CSP"
  by (simp add: AssignCSP_update_def RHS_tri_design_is_SRD unrest)
    
lemma preR_AssignCSP_update [rdes]: 
  "pre\<^sub>R(AssignCSP_update domf updatef x k v) = [k \<in>\<^sub>u uop domf (&x)]\<^sub>S\<^sub><"
  by (rel_auto)

lemma periR_AssignCSP_update [rdes]:
  "peri\<^sub>R(AssignCSP_update domf updatef x k v) = [k \<notin>\<^sub>u uop domf (&x)]\<^sub>S\<^sub><"
  by (rel_simp)

lemma post_AssignCSP_update [rdes]:
  "post\<^sub>R(AssignCSP_update domf updatef x k v) = 
    (\<Phi>(true,[x \<mapsto>\<^sub>s trop updatef (&x) k v],\<langle>\<rangle>) \<triangleleft> k \<in>\<^sub>u uop domf (&x) \<triangleright>\<^sub>R R1(true))"
  by (rel_auto) 

lemma AssignCSP_update_NCSP [closure]:
  "(AssignCSP_update domf updatef x k v) is NCSP"
proof (rule NCSP_intro)
  show "(AssignCSP_update domf updatef x k v) is CSP"
    by (simp add: closure)
  show "(AssignCSP_update domf updatef x k v) is CSP3"
    by (rule CSP3_SRD_intro, simp_all add: csp_do_def closure rdes unrest)
  show "(AssignCSP_update domf updatef x k v) is CSP4"
    by (rule CSP4_tri_intro, simp_all add: csp_do_def closure rdes unrest, rel_auto)
qed

subsection \<open> State abstraction \<close>

lemma ref_unrest_abs_st [unrest]:
  "$ref \<sharp> P \<Longrightarrow> $ref \<sharp> \<langle>P\<rangle>\<^sub>S"
  "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> \<langle>P\<rangle>\<^sub>S"
  by (rel_simp)+
  
lemma NCSP_state_srea [closure]: "P is NCSP \<Longrightarrow> state 'a \<bullet> P is NCSP"
  apply (rule NCSP_NSRD_intro)
  apply (simp_all add: closure rdes)
  apply (simp_all add: state_srea_def unrest closure)
done

subsection \<open> Assumptions \<close>

definition AssumeCircus ("{_}\<^sub>C") where
[rdes_def]: "{b}\<^sub>C = \<^bold>R\<^sub>s(\<I>(b,\<langle>\<rangle>) \<turnstile> (false \<diamondop> \<Phi>(true,id,\<langle>\<rangle>)))"

subsection \<open> Guards \<close>

definition GuardCSP ::
  "'\<sigma> cond \<Rightarrow>
   ('\<sigma>, '\<phi>) action \<Rightarrow>
   ('\<sigma>, '\<phi>) action" (infixr "&\<^sub>u" 70) where
[upred_defs]: "g &\<^sub>u A = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R(A)) \<turnstile> ((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R(A)) \<or> (\<lceil>\<not> g\<rceil>\<^sub>S\<^sub><) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

lemma Guard_tri_design:
  "g &\<^sub>u P = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P)))"
proof -
  have "(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R P \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) = (peri\<^sub>R(P) \<triangleleft> \<lceil>g\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R(P))"
    by (rel_auto)
  thus ?thesis by (simp add: GuardCSP_def)
qed
    
lemma Guard_rdes_def [rdes_def]:
  assumes "P is RR" "Q is RR" "R is RR"
  shows "g &\<^sub>u \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) = \<^bold>R\<^sub>s(([g]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (Q \<triangleleft> g \<triangleright>\<^sub>R ($tr\<acute> =\<^sub>u $tr)) \<diamondop> ([g]\<^sub>S\<^sub>< \<and> R))"
  by (simp add: Guard_tri_design rdes assms, rel_auto)

lemma Guard_rdes_def':
  assumes "$ok\<acute> \<sharp> P"
  shows "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
proof -
  have "g &\<^sub>u (\<^bold>R\<^sub>s(P \<turnstile> Q)) = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> cmt\<^sub>R (\<^bold>R\<^sub>s (P \<turnstile> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: GuardCSP_def)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or>  \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> R1(R2c(cmt\<^sub>s \<dagger> (P \<Rightarrow> Q))) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> R1(R2c(\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"
     by (simp add: R1_R2c_commute R1_disj R1_extend_conj' R1_idem R2c_and R2c_disj R2c_idem)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (cmt\<^sub>s \<dagger> (P \<Rightarrow> Q)) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> cmt\<^sub>s \<dagger> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: usubst)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r R1(R2c(pre\<^sub>s \<dagger> P))) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_cmt)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r (pre\<^sub>s \<dagger> P)) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rel_auto)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>s \<dagger> P)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rel_auto)
   also from assms have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> (P \<Rightarrow> Q) \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (simp add: rdes_export_pre)
   also have "... = \<^bold>R\<^sub>s((\<lceil>g\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> (\<lceil>g\<rceil>\<^sub>S\<^sub>< \<and> Q \<or> \<lceil>\<not>g\<rceil>\<^sub>S\<^sub>< \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
     by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
   finally show ?thesis .
qed

lemma CSP_Guard [closure]: "b &\<^sub>u P is CSP"
  by (simp add: GuardCSP_def, rule RHS_design_is_SRD, simp_all add: unrest)

lemma preR_Guard [rdes]: "P is CSP \<Longrightarrow> pre\<^sub>R(b &\<^sub>u P) = ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)"
  by (simp add: Guard_tri_design rea_pre_RHS_design usubst unrest R2c_preR R2c_lift_state_pre
      R2c_rea_impl R1_rea_impl R1_preR Healthy_if, rel_auto)

lemma periR_Guard [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(b &\<^sub>u P) = (peri\<^sub>R P \<triangleleft> b \<triangleright>\<^sub>R \<E>(true,\<langle>\<rangle>,{}\<^sub>u))"
proof -
  have "peri\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<Rightarrow>\<^sub>r (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)))"
    by (simp add: assms Guard_tri_design rea_peri_RHS_design usubst unrest R1_rea_impl R2c_rea_not 
        R2c_rea_impl R2c_preR R2c_periR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr closure
        Healthy_if R1_cond R1_tr'_eq_tr)
  also have "... = ((pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr))"
    by (rel_auto)
  also have "... = (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr))"      
    by (simp add: SRD_peri_under_pre add: unrest closure assms)
  finally show ?thesis
    by rel_auto
qed
      
lemma postR_Guard [rdes]:
  assumes "P is NCSP"
  shows "post\<^sub>R(b &\<^sub>u P) = ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
proof -
  have "post\<^sub>R(b &\<^sub>u P) = ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<Rightarrow>\<^sub>r (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P))"
    by (simp add: Guard_tri_design rea_post_RHS_design usubst unrest R2c_rea_not R2c_and R2c_rea_impl
        R2c_preR R2c_postR R2c_tr'_minus_tr R2c_lift_state_pre R2c_condr R1_rea_impl R1_extend_conj'
        R1_post_SRD closure assms)
  also have "... = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P))"
    by (rel_auto)
  also have "... = (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
    by (simp add: SRD_post_under_pre add: unrest closure assms)
  also have "... = ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
    by (metis CSP_Guard R1_extend_conj R1_post_SRD calculation rea_st_cond_def)      
  finally show ?thesis .
qed
        
lemma CSP3_Guard [closure]:
  assumes "P is CSP" "P is CSP3"
  shows "b &\<^sub>u P is CSP3"
proof -
  from assms have 1:"$ref \<sharp> P\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: CSP_Guard CSP3_iff)
  hence "$ref \<sharp> pre\<^sub>R (P\<lbrakk>0/$tr\<rbrakk>)" "$ref \<sharp> pre\<^sub>R P" "$ref \<sharp> cmt\<^sub>R P"
    by (pred_blast)+
  hence "$ref \<sharp> (b &\<^sub>u P)\<lbrakk>false/$wait\<rbrakk>"
    by (simp add: CSP3_iff GuardCSP_def RHS_def R1_def R2c_def R2s_def R3h_def design_def unrest usubst)
  thus ?thesis
    by (metis CSP3_intro CSP_Guard)
qed

lemma CSP4_Guard [closure]:
  assumes "P is NCSP"
  shows "b &\<^sub>u P is CSP4"
proof (rule CSP4_tri_intro[OF CSP_Guard])
  show "(\<not>\<^sub>r pre\<^sub>R (b &\<^sub>u P)) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R (b &\<^sub>u P))"
  proof -
    have a:"(\<not>\<^sub>r pre\<^sub>R P) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R P)"
      by (simp add: CSP4_neg_pre_unit assms closure)
    have "(\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) ;; R1 true = (\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P))"
    proof -
      have 1:"(\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) = ([b]\<^sub>S\<^sub>< \<and> (\<not>\<^sub>r pre\<^sub>R P))"
        by (rel_auto)
      also have 2:"... = ([b]\<^sub>S\<^sub>< \<and> ((\<not>\<^sub>r pre\<^sub>R P) ;; R1 true))"
        by (simp add: a)
      also have 3:"... = (\<not>\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P)) ;; R1 true"
        by (rel_auto)
      finally show ?thesis ..
    qed
    thus ?thesis
      by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro closure assms unrest)
  qed
  show "$st\<acute> \<sharp> peri\<^sub>R (b &\<^sub>u P)"
    by (simp add: preR_Guard periR_Guard NSRD_CSP4_intro closure assms unrest)
  show "$ref\<acute> \<sharp> post\<^sub>R (b &\<^sub>u P)"
    by (simp add: preR_Guard postR_Guard NSRD_CSP4_intro closure assms unrest)
qed

lemma NCSP_Guard [closure]:
  assumes "P is NCSP"
  shows "b &\<^sub>u P is NCSP"
proof -
  have "P is CSP"
    using NCSP_implies_CSP assms by blast
  then show ?thesis
    by (metis (no_types) CSP3_Guard CSP3_commutes_CSP4 CSP4_Guard CSP4_Idempotent CSP_Guard Healthy_Idempotent Healthy_def NCSP_def assms comp_apply)
qed

lemma Productive_Guard [closure]:
  assumes "P is CSP" "P is Productive" "$wait\<acute> \<sharp> pre\<^sub>R(P)"
  shows "b &\<^sub>u P is Productive"
proof -
  have "b &\<^sub>u P = b &\<^sub>u \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> (post\<^sub>R(P) \<and> $tr <\<^sub>u $tr\<acute>))"
    by (metis Healthy_def Productive_form assms(1) assms(2))
  also have "... =
        \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile>
          ((pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> (\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P \<and> $tr\<acute> >\<^sub>u $tr)))"
    by (simp add: Guard_tri_design rea_pre_RHS_design rea_peri_RHS_design rea_post_RHS_design unrest assms
        usubst R1_preR Healthy_if R1_rea_impl R1_peri_SRD R1_extend_conj' R2c_preR R2c_not R2c_rea_impl 
        R2c_periR R2c_postR R2c_and R2c_tr_less_tr' R1_tr_less_tr')             
  also have "... = \<^bold>R\<^sub>s ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r pre\<^sub>R P) \<turnstile> (peri\<^sub>R P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<triangleright> ($tr\<acute> =\<^sub>u $tr)) \<diamondop> ((\<lceil>b\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R P) \<and> $tr\<acute> >\<^sub>u $tr))"
    by (rel_auto)
  also have "... = Productive(b &\<^sub>u P)"
    by (simp add: Productive_def Guard_tri_design RHS_tri_design_par unrest)
  finally show ?thesis
    by (simp add: Healthy_def')
qed

subsection \<open> Basic events\<close>

definition do\<^sub>u ::
  "('\<phi>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[upred_defs]: "do\<^sub>u e = (($tr\<acute> =\<^sub>u $tr \<and> \<lceil>e\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>e\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st))"

definition DoCSP :: "('\<phi>, '\<sigma>) uexpr \<Rightarrow> ('\<sigma>, '\<phi>) action" ("do\<^sub>C") where
[upred_defs]: "DoCSP a = \<^bold>R\<^sub>s(true \<turnstile> do\<^sub>u a)"

lemma R1_DoAct: "R1(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (rel_auto)

lemma R2c_DoAct: "R2c(do\<^sub>u(a)) = do\<^sub>u(a)"
  by (rel_auto)

lemma DoCSP_alt_def: "do\<^sub>C(a) = R3h(CSP1($ok\<acute> \<and> do\<^sub>u(a)))"
  apply (simp add: DoCSP_def RHS_def design_def impl_alt_def  R1_R3h_commute R2c_R3h_commute R2c_disj
                   R2c_not R2c_ok R2c_ok' R2c_and R2c_DoAct R1_disj R1_extend_conj' R1_DoAct)
  apply (rel_auto)
done

lemma DoAct_unrests [unrest]:
  "$ok \<sharp> do\<^sub>u(a)" "$wait \<sharp> do\<^sub>u(a)"
  by (pred_auto)+

lemma DoCSP_RHS_tri [rdes_def]:
  "do\<^sub>C(a) = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<diamondop> \<Phi>(true,id,\<langle>a\<rangle>)))"
  by (simp add: DoCSP_def do\<^sub>u_def wait'_cond_def, rel_auto)

lemma CSP_DoCSP [closure]: "do\<^sub>C(a) is CSP"
  by (simp add: DoCSP_def do\<^sub>u_def RHS_design_is_SRD unrest)

lemma preR_DoCSP [rdes]: "pre\<^sub>R(do\<^sub>C(a)) = true\<^sub>r"
  by (simp add: DoCSP_def rea_pre_RHS_design unrest usubst R2c_true)

lemma periR_DoCSP [rdes]: "peri\<^sub>R(do\<^sub>C(a)) = \<E>(true,\<langle>\<rangle>,{a}\<^sub>u)"
  by (rel_auto) 

lemma postR_DoCSP [rdes]: "post\<^sub>R(do\<^sub>C(a)) = \<Phi>(true,id,\<langle>a\<rangle>)"
  by (rel_auto)

lemma CSP3_DoCSP [closure]: "do\<^sub>C(a) is CSP3"
  by (rule CSP3_intro[OF CSP_DoCSP])
     (simp add: DoCSP_def do\<^sub>u_def RHS_def design_def R1_def R2c_def R2s_def R3h_def unrest usubst)

lemma CSP4_DoCSP [closure]: "do\<^sub>C(a) is CSP4"
  by (rule CSP4_tri_intro[OF CSP_DoCSP], simp_all add: preR_DoCSP periR_DoCSP postR_DoCSP unrest)

lemma NCSP_DoCSP [closure]: "do\<^sub>C(a) is NCSP"
  by (metis CSP3_DoCSP CSP4_DoCSP CSP_DoCSP Healthy_def NCSP_def comp_apply)

lemma Productive_DoCSP [closure]:
  "(do\<^sub>C a :: ('\<sigma>, '\<psi>) action) is Productive"
proof -
  have "((\<Phi>(true,id,\<langle>a\<rangle>) \<and> $tr\<acute> >\<^sub>u $tr) :: ('\<sigma>, '\<psi>) action)
        = (\<Phi>(true,id,\<langle>a\<rangle>))"
    by (rel_auto, simp add: Prefix_Order.strict_prefixI')
  hence "Productive(do\<^sub>C a) = do\<^sub>C a"
    by (simp add: Productive_RHS_design_form DoCSP_RHS_tri unrest)
  thus ?thesis
    by (simp add: Healthy_def)
qed

lemma PCSP_DoCSP [closure]:
  "(do\<^sub>C a :: ('\<sigma>, '\<psi>) action) is PCSP"
  by (simp add: Healthy_comp NCSP_DoCSP Productive_DoCSP)

lemma wp_rea_DoCSP_lemma:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = (\<exists> $ref \<bullet> P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  using assms
  by (rel_auto, meson)

lemma wp_rea_DoCSP:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>r pre\<^sub>R P = 
         (\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  by (simp add: wp_rea_def wp_rea_DoCSP_lemma unrest usubst ex_unrest assms closure)    
    
lemma wp_rea_DoCSP_alt:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) wp\<^sub>r pre\<^sub>R P = 
         ($tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<Rightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"  
  by (simp add: wp_rea_DoCSP assms rea_not_def R1_def usubst unrest, rel_auto)

subsection \<open> Event prefix \<close>

definition PrefixCSP ::
  "('\<phi>, '\<sigma>) uexpr \<Rightarrow>
  ('\<sigma>, '\<phi>) action \<Rightarrow>
  ('\<sigma>, '\<phi>) action" ("_ \<rightarrow>\<^sub>C _" [81, 80] 80) where
[upred_defs]: "PrefixCSP a P = (do\<^sub>C(a) ;; CSP(P))"

abbreviation "OutputCSP c v P \<equiv> PrefixCSP (c\<cdot>v)\<^sub>u P"

lemma CSP_PrefixCSP [closure]: "PrefixCSP a P is CSP"
  by (simp add: PrefixCSP_def closure)

lemma CSP3_PrefixCSP [closure]:
  "PrefixCSP a P is CSP3"
  by (metis (no_types, hide_lams) CSP3_DoCSP CSP3_def Healthy_def PrefixCSP_def seqr_assoc)

lemma CSP4_PrefixCSP [closure]:
  assumes "P is CSP" "P is CSP4"
  shows "PrefixCSP a P is CSP4"
  by (metis (no_types, hide_lams) CSP4_def Healthy_def PrefixCSP_def assms(1) assms(2) seqr_assoc)

lemma NCSP_PrefixCSP [closure]:
  assumes "P is NCSP"
  shows "PrefixCSP a P is NCSP"
  by (metis (no_types, hide_lams) CSP3_PrefixCSP CSP3_commutes_CSP4 CSP4_Idempotent CSP4_PrefixCSP
            CSP_PrefixCSP Healthy_Idempotent Healthy_def NCSP_def NCSP_implies_CSP assms comp_apply)

lemma Productive_PrefixCSP [closure]: "P is NCSP \<Longrightarrow> PrefixCSP a P is Productive"
  by (simp add: Healthy_if NCSP_DoCSP NCSP_implies_NSRD NSRD_is_SRD PrefixCSP_def Productive_DoCSP Productive_seq_1)

lemma PCSP_PrefixCSP [closure]: "P is NCSP \<Longrightarrow> PrefixCSP a P is PCSP"
  by (simp add: Healthy_comp NCSP_PrefixCSP Productive_PrefixCSP)
  
lemma PrefixCSP_Guarded [closure]: "Guarded (PrefixCSP a)"
proof -
  have "PrefixCSP a = (\<lambda> X. do\<^sub>C(a) ;; CSP(X))"
    by (simp add: fun_eq_iff PrefixCSP_def)
  thus ?thesis
    using Guarded_if_Productive NCSP_DoCSP NCSP_implies_NSRD Productive_DoCSP by auto
qed

lemma PrefixCSP_type [closure]: "PrefixCSP a \<in> \<lbrakk>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  using CSP_PrefixCSP by blast

lemma PrefixCSP_Continuous [closure]: "Continuous (PrefixCSP a)"
  by (simp add: Continuous_def PrefixCSP_def ContinuousD[OF SRD_Continuous] seq_Sup_distl)

lemma PrefixCSP_RHS_tri_lemma1:
  "R1 (R2s ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>II\<rceil>\<^sub>R)) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>II\<rceil>\<^sub>R)"
  by (rel_auto)

lemma PrefixCSP_RHS_tri_lemma2:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "(($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) \<and> \<not> $wait\<acute>) ;; P = (\<exists> $ref \<bullet> P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>)"
  using assms
  by (rel_auto, meson, fastforce)

lemma tr_extend_seqr:
  fixes P :: "('\<sigma>, '\<phi>) action"
  assumes "$ok \<sharp> P" "$wait \<sharp> P" "$ref \<sharp> P"
  shows "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle> \<and> $st\<acute> =\<^sub>u $st) ;; P = P\<lbrakk>$tr ^\<^sub>u \<langle>\<lceil>a\<rceil>\<^sub>S\<^sub><\<rangle>/$tr\<rbrakk>"
  using assms by (simp add: wp_rea_DoCSP_lemma assms unrest ex_unrest)
          
lemma trace_ext_R1_closed [closure]: "P is R1 \<Longrightarrow> P\<lbrakk>$tr ^\<^sub>u e/$tr\<rbrakk> is R1"
  by (rel_blast)
    
lemma preR_PrefixCSP_NCSP [rdes]:
  assumes "P is NCSP"
  shows "pre\<^sub>R(PrefixCSP a P) = (\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  by (simp add: PrefixCSP_def assms closure rdes rpred Healthy_if wp usubst unrest)
  
lemma periR_PrefixCSP [rdes]:
  assumes "P is NCSP"
  shows "peri\<^sub>R(PrefixCSP a P) = (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<or> (peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
proof -
  have "peri\<^sub>R(PrefixCSP a P) =  peri\<^sub>R (do\<^sub>C a ;; P)"
    by (simp add: PrefixCSP_def closure assms Healthy_if)
  also have "... = ((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r pre\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<Rightarrow>\<^sub>r $tr\<acute> =\<^sub>u $tr \<and> \<lceil>a\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute> \<or> peri\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (simp add: assms NSRD_CSP4_intro csp_enable_tr_empty closure rdes unrest ex_unrest usubst rpred wp)
  also have "... = (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<or> ((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r pre\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<Rightarrow>\<^sub>r peri\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t))"
    by (rel_auto)
  also have "... = (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<or> ((pre\<^sub>R(P) \<Rightarrow>\<^sub>r peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t))"
    by (rel_auto)
  also have "... = (\<E>(true,\<langle>\<rangle>,{a}\<^sub>u) \<or> (peri\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"      
    by (simp add: SRD_peri_under_pre assms closure unrest)
  finally show ?thesis .
qed
  
lemma postR_PrefixCSP [rdes]:
  assumes "P is NCSP"
  shows "post\<^sub>R(PrefixCSP a P) = (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t"
proof -
  have "post\<^sub>R(PrefixCSP a P) = ((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r (pre\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<Rightarrow>\<^sub>r (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (simp add: PrefixCSP_def assms Healthy_if) 
       (simp add: assms Healthy_if wp closure rdes rpred wp_rea_DoCSP_lemma unrest  ex_unrest usubst)
  also have "... = (\<I>(true,\<langle>a\<rangle>) \<and> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
    by (rel_auto)
  also have "... = (\<I>(true,\<langle>a\<rangle>) \<and> (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"      
    by (simp add: SRD_post_under_pre assms closure unrest)
  also have "... = (post\<^sub>R P)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t"
    by (rel_auto)
  finally show ?thesis .
qed
      
lemma PrefixCSP_RHS_tri:
  assumes "P is NCSP"
  shows "PrefixCSP a P = \<^bold>R\<^sub>s ((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r pre\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<turnstile> (\<E>(true,\<langle>\<rangle>, {a}\<^sub>u) \<or> peri\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<diamondop> post\<^sub>R P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  by (simp add: PrefixCSP_def Healthy_if unrest assms closure NSRD_composition_wp rdes rpred usubst wp)

text \<open> For prefix, we can chose whether to propagate the assumptions or not, hence there
  are two laws. \<close>
    
lemma PrefixCSP_rdes_def_1 [rdes_def]:
  assumes "P is CRC" "Q is CRR" "R is CRR"
          "$st\<acute> \<sharp> Q" "$ref\<acute> \<sharp> R"
  shows "PrefixCSP a (\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<turnstile> (\<E>(true,\<langle>\<rangle>, {a}\<^sub>u) \<or> Q\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<diamondop> R\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  apply (subst PrefixCSP_RHS_tri)
   apply (rule NCSP_rdes_intro)
       apply (simp_all add: assms rdes closure)
  apply (rel_auto)
  done

lemma PrefixCSP_rdes_def_2:
  assumes "P is CRC" "Q is CRR" "R is CRR"
          "$st\<acute> \<sharp> Q" "$ref\<acute> \<sharp> R"
  shows "PrefixCSP a (\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R)) = \<^bold>R\<^sub>s((\<I>(true,\<langle>a\<rangle>) \<Rightarrow>\<^sub>r P\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<turnstile> (\<E>(true,\<langle>\<rangle>, {a}\<^sub>u) \<or> (P\<and>Q)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t) \<diamondop> (P\<and>R)\<lbrakk>\<langle>a\<rangle>\<rbrakk>\<^sub>t)"
  apply (subst PrefixCSP_RHS_tri)
   apply (rule NCSP_rdes_intro)
       apply (simp_all add: assms rdes closure)
  apply (rel_auto)
  done

subsection \<open> Guarded external choice \<close>

abbreviation GuardedChoiceCSP :: "'\<theta> set \<Rightarrow> ('\<theta> \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow> ('\<sigma>, '\<theta>) action" where
"GuardedChoiceCSP A P \<equiv> (\<box> x\<in>A \<bullet> PrefixCSP \<guillemotleft>x\<guillemotright> (P(x)))"

syntax
  "_GuardedChoiceCSP" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box> _ \<in> _ \<^bold>\<rightarrow> _" [0,0,85] 86)

translations
  "\<box> x\<in>A \<^bold>\<rightarrow> P" == "CONST GuardedChoiceCSP A (\<lambda> x. P)"

lemma GuardedChoiceCSP [rdes_def]:
  assumes "\<And> x. P(x) is NCSP" "A \<noteq> {}"
  shows "(\<box> x\<in>A \<^bold>\<rightarrow> P(x)) =
             \<^bold>R\<^sub>s ((\<Squnion> x \<in> A \<bullet> \<I>(true,\<langle>\<guillemotleft>x\<guillemotright>\<rangle>) \<Rightarrow>\<^sub>r pre\<^sub>R (P x)\<lbrakk>\<langle>\<guillemotleft>x\<guillemotright>\<rangle>\<rbrakk>\<^sub>t) \<turnstile>
                 ((\<Squnion> x \<in> A \<bullet> \<E>(true,\<langle>\<rangle>, {\<guillemotleft>x\<guillemotright>}\<^sub>u)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> x \<in> A \<bullet> peri\<^sub>R (P x)\<lbrakk>\<langle>\<guillemotleft>x\<guillemotright>\<rangle>\<rbrakk>\<^sub>t)) \<diamondop>
                  (\<Sqinter> x \<in> A \<bullet> post\<^sub>R (P x)\<lbrakk>\<langle>\<guillemotleft>x\<guillemotright>\<rangle>\<rbrakk>\<^sub>t))"
  by (simp add: PrefixCSP_RHS_tri assms ExtChoice_tri_rdes closure unrest, rel_auto)

subsection \<open> Input prefix \<close>

definition InputCSP ::
  "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> upred) \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow> ('\<sigma>, '\<theta>) action" where
[upred_defs]: "InputCSP c A P = (\<box> x\<in>UNIV \<bullet> A(x) &\<^sub>u PrefixCSP (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u (P x))"

definition InputVarCSP :: "('a, '\<theta>) chan \<Rightarrow> ('a \<Rightarrow> '\<sigma> upred) \<Rightarrow> ('a \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<sigma>, '\<theta>) action \<Rightarrow> ('\<sigma>, '\<theta>) action" where
"InputVarCSP c A x P = InputCSP c A (\<lambda> v. \<langle>[x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>]\<rangle>\<^sub>C) ;; CSP(P)"

definition do\<^sub>I :: "
  ('a, '\<theta>) chan \<Rightarrow>
  ('a \<Longrightarrow> ('\<sigma>, '\<theta>) st_csp) \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow>
  ('\<sigma>, '\<theta>) action" where
"do\<^sub>I c x P = (
  ($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>$x\<acute>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>)))"

lemma InputCSP_CSP [closure]: "InputCSP c A P is CSP"
  by (simp add: CSP_ExtChoice InputCSP_def)

lemma InputCSP_NCSP [closure]: "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> InputCSP c A P is NCSP"
  apply (simp add: InputCSP_def)
  apply (rule NCSP_ExtChoice)
  apply (simp add: NCSP_Guard NCSP_PrefixCSP image_Collect_subsetI top_set_def)
  done

lemma Productive_InputCSP [closure]:
  "\<lbrakk> \<And> v. P(v) is NCSP \<rbrakk> \<Longrightarrow> InputCSP x A P is Productive"
  by (auto simp add: InputCSP_def unrest closure intro: Productive_ExtChoice)

lemma preR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "pre\<^sub>R(InputCSP a A P) = (\<Squnion> v \<bullet> [A(v)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r (pre\<^sub>R (P(v)))\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
  by (simp add: InputCSP_def rdes closure assms alpha usubst unrest)
    
lemma periR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "peri\<^sub>R(InputCSP a A P) =
           ((\<Squnion> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<E>(true, \<langle>\<rangle>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u))) 
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
            (\<Sqinter> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<and> (peri\<^sub>R (P x))\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)" 
  by (simp add: InputCSP_def rdes closure assms, rel_auto)

lemma postR_InputCSP [rdes]:
  assumes "\<And> v. P(v) is NCSP"
  shows "post\<^sub>R(InputCSP a A P) =
          (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> post\<^sub>R (P x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
  using assms by (simp add: InputCSP_def rdes closure assms usubst unrest)

lemma InputCSP_rdes_def [rdes_def]:
  assumes "\<And> v. P(v) is CRC" "\<And> v. Q(v) is CRR" "\<And> v. R(v) is CRR"
          "\<And> v. $st\<acute> \<sharp> Q(v)" "\<And> v. $ref\<acute> \<sharp> R(v)"
  shows "InputCSP a A (\<lambda> v. \<^bold>R\<^sub>s(P(v) \<turnstile> Q(v) \<diamondop> R(v))) = 
         \<^bold>R\<^sub>s( (\<Squnion> v \<bullet> ([A(v)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r (P v)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))
           \<turnstile> (((\<Squnion> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<E>(true, \<langle>\<rangle>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u))) 
               \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright>
               (\<Sqinter> x \<bullet> [A(x)]\<^sub>S\<^sub>< \<and> (P x \<and> Q x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))
           \<diamondop> (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<and> R x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t))" (is "?lhs = ?rhs")
proof -
  have 1:"pre\<^sub>R(?lhs) = (\<Squnion> v \<bullet> [A v]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<I>(true,\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r P v\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)" (is "_ = ?A")
    by (simp add: rdes NCSP_rdes_intro assms conj_comm closure)
  have 2:"peri\<^sub>R(?lhs) = (\<Squnion> x \<bullet> [A x]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r \<E>(true,\<langle>\<rangle>, {(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<Rightarrow>\<^sub>r Q x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
    (is "_ = ?B")
    by (simp add: rdes NCSP_rdes_intro assms closure)
  have 3:"post\<^sub>R(?lhs) = (\<Sqinter> x \<bullet> [A x]\<^sub>S\<^sub>< \<and> (P x \<Rightarrow>\<^sub>r R x)\<lbrakk>\<langle>(a\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>\<rbrakk>\<^sub>t)"
    (is "_ = ?C")
    by (simp add: rdes NCSP_rdes_intro assms closure)
  have "?lhs = \<^bold>R\<^sub>s(?A \<turnstile> ?B \<diamondop> ?C)"
    by (subst SRD_reactive_tri_design[THEN sym], simp_all add: closure 1 2 3)
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed

subsection \<open> Algebraic laws \<close>

lemma AssignCSP_conditional:
  assumes "vwb_lens x"
  shows "x :=\<^sub>C e \<triangleleft> b \<triangleright>\<^sub>R x :=\<^sub>C f = x :=\<^sub>C (e \<triangleleft> b \<triangleright> f)" 
  by (rdes_eq cls: assms)

lemma AssignsCSP_id: "\<langle>id\<rangle>\<^sub>C = Skip"
  by (rel_auto)

lemma Guard_comp:
  "g &\<^sub>u h &\<^sub>u P = (g \<and> h) &\<^sub>u P"
  by (rule antisym, rel_blast, rel_blast)

lemma Guard_false [simp]: "false &\<^sub>u P = Stop"
  by (simp add: GuardCSP_def Stop_def rpred closure alpha R1_design_R1_pre)

lemma Guard_true [simp]:
  "P is CSP \<Longrightarrow> true &\<^sub>u P = P"
  by (simp add: GuardCSP_def alpha SRD_reactive_design_alt closure rpred)

lemma Guard_conditional:
  assumes "P is NCSP"
  shows "b &\<^sub>u P = P \<triangleleft> b \<triangleright>\<^sub>R Stop"  
  by (rdes_eq cls: assms)

lemma Guard_expansion:
  assumes "P is NCSP"
  shows "(g\<^sub>1 \<or> g\<^sub>2) &\<^sub>u P = (g\<^sub>1 &\<^sub>u P) \<box> (g\<^sub>2 &\<^sub>u P)"
  by (rdes_eq cls: assms)

lemma Conditional_as_Guard:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q = b &\<^sub>u P \<box> (\<not> b) &\<^sub>u Q"  
  by (rdes_eq cls: assms)

lemma PrefixCSP_dist:
  "PrefixCSP a (P \<sqinter> Q) = (PrefixCSP a P) \<sqinter> (PrefixCSP a Q)"
  using Continuous_Disjunctous Disjunctuous_def PrefixCSP_Continuous by auto

lemma DoCSP_is_Prefix:
  "do\<^sub>C(a) = PrefixCSP a Skip"
  by (simp add: PrefixCSP_def Healthy_if closure, metis CSP4_DoCSP CSP4_def Healthy_def)

lemma PrefixCSP_seq:
  assumes "P is CSP" "Q is CSP"
  shows "(PrefixCSP a P) ;; Q = (PrefixCSP a (P ;; Q))"
  by (simp add: PrefixCSP_def seqr_assoc Healthy_if assms closure)

lemma PrefixCSP_extChoice_dist:
  assumes "P is NCSP" "Q is NCSP" "R is NCSP"
  shows "((a \<rightarrow>\<^sub>C P) \<box> (b \<rightarrow>\<^sub>C Q)) ;; R  = (a \<rightarrow>\<^sub>C P ;; R) \<box> (b \<rightarrow>\<^sub>C Q ;; R)"
  by (simp add: PCSP_PrefixCSP assms(1) assms(2) assms(3) extChoice_seq_distr)

lemma GuardedChoiceCSP_dist: 
  assumes "\<And> i. i\<in>A \<Longrightarrow> P(i) is NCSP" "Q is NCSP"
  shows "\<box> x\<in>A \<^bold>\<rightarrow> P(x) ;; Q = \<box> x\<in>A \<^bold>\<rightarrow> (P(x) ;; Q)"
  by (simp add: ExtChoice_seq_distr PrefixCSP_seq closure assms cong: ExtChoice_cong)

text \<open> Alternation can be re-expressed as an external choice when the guards are disjoint \<close>

lemma AlternateR_as_ExtChoice:
  assumes 
    "\<And> i. i \<in> A \<Longrightarrow> P(i) is NCSP" "Q is NCSP"
    "\<And> i j. \<lbrakk> i \<in> A; j \<in> A; i \<noteq> j \<rbrakk> \<Longrightarrow> (g i \<and> g j) = false" 
  shows "(if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> P(i) else Q fi) = 
         (\<box> i\<in>A \<bullet> g(i) &\<^sub>u P(i)) \<box> (\<And> i\<in>A \<bullet> \<not> g(i)) &\<^sub>u Q"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: ExtChoice_empty extChoice_Stop closure assms)
next
  case False
  show ?thesis
  proof -
    have 1:"(\<Sqinter> i \<in> A \<bullet> g i \<rightarrow>\<^sub>R P i) = (\<Sqinter> i \<in> A \<bullet> g i \<rightarrow>\<^sub>R \<^bold>R\<^sub>s(pre\<^sub>R(P i) \<turnstile> peri\<^sub>R(P i) \<diamondop> post\<^sub>R(P i)))"
      by (rule UINF_cong, simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(1))
    have 2:"(\<box> i\<in>A \<bullet> g(i) &\<^sub>u P(i)) = (\<box> i\<in>A \<bullet> g(i) &\<^sub>u \<^bold>R\<^sub>s(pre\<^sub>R(P i) \<turnstile> peri\<^sub>R(P i) \<diamondop> post\<^sub>R(P i)))"
      by (rule ExtChoice_cong, simp add: NCSP_implies_NSRD NSRD_is_SRD SRD_reactive_tri_design assms(1))
    from assms(3) show ?thesis
      by (simp add: AlternateR_def 1 2)
         (rdes_eq cls: assms(1-2) simps: False cong: UINF_cong ExtChoice_cong)
  qed
qed

end