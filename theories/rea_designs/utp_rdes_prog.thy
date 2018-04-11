section \<open> Reactive Design Programs \<close>

theory utp_rdes_prog
  imports 
    utp_rdes_normal
    utp_rdes_tactics
    utp_rdes_parallel
    utp_rdes_guarded
    "UTP-KAT.utp_kleene"
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

subsection \<open> Assumptions \<close>

definition AssumeR :: "'s cond \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp" ("[_]\<^sup>\<top>\<^sub>R") where
[upred_defs]: "AssumeR b = II\<^sub>R \<triangleleft> b \<triangleright>\<^sub>R Miracle"

lemma AssumeR_rdes_def [rdes_def]: 
  "[b]\<^sup>\<top>\<^sub>R = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> [b]\<^sup>\<top>\<^sub>r)"
  unfolding AssumeR_def by (rdes_eq)

lemma AssumeR_NSRD [closure]: "[b]\<^sup>\<top>\<^sub>R is NSRD"
  by (simp add: AssumeR_def closure)

lemma AssumeR_false: "[false]\<^sup>\<top>\<^sub>R = Miracle"
  by (rel_auto)

lemma AssumeR_true: "[true]\<^sup>\<top>\<^sub>R = II\<^sub>R"
  by (rel_auto)

lemma AssumeR_comp: "[b]\<^sup>\<top>\<^sub>R ;; [c]\<^sup>\<top>\<^sub>R = [b \<and> c]\<^sup>\<top>\<^sub>R"
  by (rdes_simp)

lemma AssumeR_choice: "[b]\<^sup>\<top>\<^sub>R \<sqinter> [c]\<^sup>\<top>\<^sub>R = [b \<or> c]\<^sup>\<top>\<^sub>R"
  by (rdes_eq)

lemma AssumeR_refine_skip: "II\<^sub>R \<sqsubseteq> [b]\<^sup>\<top>\<^sub>R"
  by (rdes_refine)

lemma AssumeR_test [closure]: "test\<^sub>R [b]\<^sup>\<top>\<^sub>R"
  by (simp add: AssumeR_refine_skip nsrd_thy.utest_intro)

lemma Star_AssumeR: "[b]\<^sup>\<top>\<^sub>R\<^sup>\<star>\<^sup>R = II\<^sub>R"
  by (simp add: AssumeR_NSRD AssumeR_test nsrd_thy.Star_test)

lemma AssumeR_choice_skip: "II\<^sub>R \<sqinter> [b]\<^sup>\<top>\<^sub>R = II\<^sub>R"
  by (rdes_eq)

lemma cond_srea_AssumeR_form:
  assumes "P is NSRD" "Q is NSRD"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q = ([b]\<^sup>\<top>\<^sub>R ;; P \<sqinter> [\<not>b]\<^sup>\<top>\<^sub>R ;; Q)"
  by (rdes_eq cls: assms)

lemma cond_srea_insert_assume:
  assumes "P is NSRD" "Q is NSRD"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q = ([b]\<^sup>\<top>\<^sub>R ;; P \<triangleleft> b \<triangleright>\<^sub>R [\<not>b]\<^sup>\<top>\<^sub>R ;; Q)"
  by (simp add: AssumeR_NSRD AssumeR_comp NSRD_seqr_closure RA1 assms cond_srea_AssumeR_form)

lemma AssumeR_cond_left:
  assumes "P is NSRD" "Q is NSRD"
  shows "[b]\<^sup>\<top>\<^sub>R ;; (P \<triangleleft> b \<triangleright>\<^sub>R Q) = ([b]\<^sup>\<top>\<^sub>R ;; P)"
  by (rdes_eq cls: assms)

lemma AssumeR_cond_right:
  assumes "P is NSRD" "Q is NSRD"
  shows "[\<not>b]\<^sup>\<top>\<^sub>R ;; (P \<triangleleft> b \<triangleright>\<^sub>R Q) = ([\<not>b]\<^sup>\<top>\<^sub>R ;; Q)"
  by (rdes_eq cls: assms)

subsection \<open> Guarded commands \<close>

definition GuardedCommR :: "'s cond \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" ("_ \<rightarrow>\<^sub>R _" [85, 86] 85) where
gcmd_def[rdes_def]: "GuardedCommR g A = A \<triangleleft> g \<triangleright>\<^sub>R Miracle"

lemma gcmd_false[simp]: "(false \<rightarrow>\<^sub>R A) = Miracle"
  unfolding gcmd_def by (pred_auto)

lemma gcmd_true[simp]: "(true \<rightarrow>\<^sub>R A) = A"
  unfolding gcmd_def by (pred_auto)

lemma gcmd_SRD: 
  assumes "A is SRD"
  shows "(g \<rightarrow>\<^sub>R A) is SRD"
  by (simp add: gcmd_def SRD_cond_srea assms srdes_theory_continuous.weak.top_closed)

lemma gcmd_NSRD [closure]: 
  assumes "A is NSRD"
  shows "(g \<rightarrow>\<^sub>R A) is NSRD"
  by (simp add: gcmd_def NSRD_cond_srea assms NSRD_Miracle)

lemma gcmd_Productive [closure]:
  assumes "A is NSRD" "A is Productive"
  shows "(g \<rightarrow>\<^sub>R A) is Productive"
  by (simp add: gcmd_def closure assms)

lemma gcmd_seq_distr: 
  assumes "B is NSRD"
  shows "(g \<rightarrow>\<^sub>R A) ;; B = (g \<rightarrow>\<^sub>R (A ;; B))"
  by (simp add: Miracle_left_zero NSRD_is_SRD assms cond_st_distr gcmd_def)

lemma gcmd_nondet_distr:
  assumes "A is NSRD" "B is NSRD"
  shows "(g \<rightarrow>\<^sub>R (A \<sqinter> B)) = (g \<rightarrow>\<^sub>R A) \<sqinter> (g \<rightarrow>\<^sub>R B)"
  by (rdes_eq cls: assms)

lemma AssumeR_as_gcmd:
  "[b]\<^sup>\<top>\<^sub>R = b \<rightarrow>\<^sub>R II\<^sub>R"
  by (rdes_eq)

section {* Generalised Alternation *}

definition AlternateR 
  :: "'a set \<Rightarrow> ('a \<Rightarrow> 's upred) \<Rightarrow> ('a \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp) \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" where
[upred_defs, rdes_def]: "AlternateR I g A B = (\<Sqinter> i \<in> I \<bullet> ((g i) \<rightarrow>\<^sub>R (A i))) \<sqinter> ((\<not> (\<Or> i \<in> I \<bullet> g i)) \<rightarrow>\<^sub>R B)"

definition AlternateR_list 
  :: "('s upred \<times> ('s, 't::trace, '\<alpha>) hrel_rsp) list \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" where 
[upred_defs, ndes_simp]:
  "AlternateR_list xs P = AlternateR {0..<length xs} (\<lambda> i. map fst xs ! i) (\<lambda> i. map snd xs ! i) P"

syntax
  "_altindR_els"   :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if\<^sub>R _\<in>_ \<bullet> _ \<rightarrow> _ else _ fi")
  "_altindR"       :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if\<^sub>R _\<in>_ \<bullet> _ \<rightarrow> _ fi")
  (* We reuse part of the parsing infrastructure for design alternation over a (finite) list of branches *)
  "_altgcommR_els" :: "gcomms \<Rightarrow> logic \<Rightarrow> logic" ("if\<^sub>R/ _ else _ /fi")
  "_altgcommR"     :: "gcomms \<Rightarrow> logic" ("if\<^sub>R/ _ /fi")

translations
  "if\<^sub>R i\<in>I \<bullet> g \<rightarrow> A else B fi"  \<rightharpoonup> "CONST AlternateR I (\<lambda>i. g) (\<lambda>i. A) B"
  "if\<^sub>R i\<in>I \<bullet> g \<rightarrow> A fi"  \<rightharpoonup> "CONST AlternateR I (\<lambda>i. g) (\<lambda>i. A) (CONST Chaos)"
  "if\<^sub>R i\<in>I \<bullet> (g i) \<rightarrow> A else B fi"  \<leftharpoondown> "CONST AlternateR I g (\<lambda>i. A) B"
  "_altgcommR cs" \<rightharpoonup> "CONST AlternateR_list cs (CONST Chaos)"
  "_altgcommR (_gcomm_show cs)" \<leftharpoondown> "CONST AlternateR_list cs (CONST Chaos)"
  "_altgcommR_els cs P" \<rightharpoonup> "CONST AlternateR_list cs P"
  "_altgcommR_els (_gcomm_show cs) P" \<leftharpoondown> "CONST AlternateR_list cs P"

lemma AlternateR_NSRD_closed [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> A i is NSRD" "B is NSRD"
  shows "(if\<^sub>R i\<in>I \<bullet> g i \<rightarrow> A i else B fi) is NSRD"
proof (cases "I = {}")
  case True
  then show ?thesis by (simp add: AlternateR_def assms)
next
  case False
  then show ?thesis by (simp add: AlternateR_def closure assms)
qed

lemma AlternateR_empty [simp]:
  "(if\<^sub>R i \<in> {} \<bullet> g i \<rightarrow> A i else B fi) = B"
  by (rdes_simp)

lemma AlternateR_Productive [closure]:
  assumes 
    "\<And> i. i \<in> I \<Longrightarrow> A i is NSRD" "B is NSRD" 
    "\<And> i. i \<in> I \<Longrightarrow> A i is Productive" "B is Productive"
  shows "(if\<^sub>R i\<in>I \<bullet> g i \<rightarrow> A i else B fi) is Productive"
proof (cases "I = {}")
  case True
  then show ?thesis
    by (simp add: assms(4)) 
next
  case False
  then show ?thesis
    by (simp add: AlternateR_def closure assms)
qed

lemma AlternateR_singleton:
  assumes "A k is NSRD" "B is NSRD"
  shows "(if\<^sub>R i \<in> {k} \<bullet> g i \<rightarrow> A i else B fi) = (A(k) \<triangleleft> g(k) \<triangleright>\<^sub>R B)"
  by (simp add: AlternateR_def, rdes_eq cls: assms)

text \<open> Convert an alternation over disjoint guards into a cascading if-then-else \<close>

lemma AlternateR_insert_cascade:
  assumes 
    "\<And> i. i \<in> I \<Longrightarrow> A i is NSRD"
    "A k is NSRD" "B is NSRD" 
    "(g(k) \<and> (\<Or> i\<in>I \<bullet> g(i))) = false"
  shows "(if\<^sub>R i \<in> insert k I \<bullet> g i \<rightarrow> A i else B fi) = (A(k) \<triangleleft> g(k) \<triangleright>\<^sub>R (if\<^sub>R i\<in>I \<bullet> g(i) \<rightarrow> A(i) else B fi))"
proof (cases "I = {}")
  case True
  then show ?thesis by (simp add: AlternateR_singleton assms)
next
  case False
  have 1: "(\<Sqinter> i \<in> I \<bullet> g i \<rightarrow>\<^sub>R A i) = (\<Sqinter> i \<in> I \<bullet> g i \<rightarrow>\<^sub>R \<^bold>R\<^sub>s(pre\<^sub>R(A i) \<turnstile> peri\<^sub>R(A i) \<diamondop> post\<^sub>R(A i)))"
    by (simp add: NSRD_is_SRD SRD_reactive_tri_design assms(1) cong: UINF_cong)
  from assms(4) show ?thesis
    by (simp add: AlternateR_def 1 False)
       (rdes_eq cls: assms(1-3) False cong: UINF_cong)
qed

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

subsection \<open> While Loop \<close>

definition WhileR :: "'s upred \<Rightarrow> ('s, 't::size_trace, '\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" ("while\<^sub>R _ do _ od") where
"WhileR b P = (\<mu>\<^sub>R X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"

lemma Sup_power_false:
  fixes F :: "'\<alpha> upred \<Rightarrow> '\<alpha> upred"
  shows "(\<Sqinter>i. (F ^^ i) false) = (\<Sqinter>i. (F ^^ (i+1)) false)"
proof -
  have "(\<Sqinter>i. (F ^^ i) false) = (F ^^ 0) false \<sqinter> (\<Sqinter>i. (F ^^ (i+1)) false)"
    by (subst Sup_power_expand, simp)
  also have "... = (\<Sqinter>i. (F ^^ (i+1)) false)"
    by (simp)
  finally show ?thesis .
qed
 
theorem WhileR_iter_expand:
  assumes "P is NSRD" "P is Productive"
  shows "while\<^sub>R b do P od = (\<Sqinter>i \<bullet> (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ i ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R))" (is "?lhs = ?rhs")
proof -
  have 1:"Continuous (\<lambda>X. P ;; SRD X)"
    using SRD_Continuous
    by (clarsimp simp add: Continuous_def seq_SUP_distl[THEN sym], drule_tac x="A" in spec, simp)
  have 2: "Continuous (\<lambda>X. P ;; SRD X \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: 1 closure assms)
  have "?lhs = (\<mu>\<^sub>R X \<bullet> P ;; X \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: WhileR_def)
  also have "... = (\<mu> X \<bullet> P ;; SRD(X) \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (auto simp add: srd_mu_equiv closure assms)
  also have "... = (\<nu> X \<bullet> P ;; SRD(X) \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (auto simp add: guarded_fp_uniq Guarded_if_Productive[OF assms] funcsetI closure assms)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; SRD X \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) ^^ i) false)"
    by (simp add: sup_continuous_lfp 2 sup_continuous_Continuous false_upred_def)
  also have "... = (\<Sqinter>i. ((\<lambda>X. P ;; SRD X \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) ^^ (i+1)) false)"
    by (simp add: Sup_power_false)
  also have "... = (\<Sqinter>i. (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)\<^bold>^i ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R))"
  proof (rule SUP_cong, simp)
    fix i
    show "((\<lambda>X. P ;; SRD X \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) ^^ (i + 1)) false = (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ i ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    proof (induct i)
      case 0
      thm if_eq_cancel
      then show ?case
        by (simp, metis srdes_hcond_def srdes_theory_continuous.healthy_top) 
    next
      case (Suc i)
      show ?case
      proof -
        have "((\<lambda>X. P ;; SRD X \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) ^^ (Suc i + 1)) false = 
              P ;; SRD (((\<lambda>X. P ;; SRD X \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) ^^ (i + 1)) false) \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R"
          by simp
        also have "... = P ;; SRD ((P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ i ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)) \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R"
          using Suc.hyps by auto
        also have "... = P ;; ((P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ i ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)) \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R"
          by (metis (no_types, lifting) Healthy_if NSRD_cond_srea NSRD_is_SRD NSRD_power_Suc NSRD_srd_skip SRD_cond_srea SRD_seqr_closure assms(1) power.power_eq_if seqr_left_unit srdes_theory_continuous.top_closed)
        also have "... = (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ Suc i ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
        proof (induct i)
          case 0
          then show ?case
            by (simp add: NSRD_is_SRD SRD_cond_srea SRD_left_unit SRD_seqr_closure SRD_srdes_skip assms(1) cond_L6 cond_st_distr srdes_theory_continuous.top_closed)
        next
          case (Suc i)
          have 1: "II\<^sub>R ;; ((P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) ;; (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ i) = ((P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) ;; (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ i)"
            by (simp add: NSRD_is_SRD RA1 SRD_cond_srea SRD_left_unit SRD_srdes_skip assms(1))
          then show ?case
          proof -
            have "\<And>u. (u ;; (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ Suc i) ;; (P ;; (Miracle) \<triangleleft> b \<triangleright>\<^sub>R (II\<^sub>R)) \<triangleleft> b \<triangleright>\<^sub>R (II\<^sub>R) = 
                      ((u \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) ;; (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ Suc i) ;; (P ;; (Miracle) \<triangleleft> b \<triangleright>\<^sub>R (II\<^sub>R))"
              by (metis (no_types) Suc.hyps 1 cond_L6 cond_st_distr power.power.power_Suc)
            then show ?thesis
              by (simp add: RA1 upred_semiring.power_Suc)
          qed
        qed
        finally show ?thesis .
      qed
    qed
  qed
  also have "... = (\<Sqinter>i \<bullet> (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)\<^bold>^i ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R))"
    by (simp add: UINF_as_Sup_collect')
  finally show ?thesis .
qed

theorem WhileR_star_expand:
  assumes "P is NSRD" "P is Productive"
  shows "while\<^sub>R b do P od = (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)\<^sup>\<star>\<^sup>R ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sqinter>i \<bullet> (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) \<^bold>^ i) ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: WhileR_iter_expand seq_UINF_distr' assms)
  also have "... = (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)\<^sup>\<star> ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: ustar_def)
  also have "... = ((P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)\<^sup>\<star> ;; II\<^sub>R) ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: seqr_assoc SRD_left_unit closure assms)
  also have "... = (P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)\<^sup>\<star>\<^sup>R ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: nsrd_thy.Star_def)
  finally show ?thesis .
qed

lemma WhileR_NSRD_closed [closure]:
  assumes "P is NSRD" "P is Productive"
  shows "while\<^sub>R b do P od is NSRD"
  by (simp add: WhileR_star_expand assms closure)

theorem WhileR_iter_form_lemma:
  assumes "P is NSRD"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)\<^sup>\<star>\<^sup>R ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) = ([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [\<not> b]\<^sup>\<top>\<^sub>R"
proof -
  have "(P \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)\<^sup>\<star>\<^sup>R ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R) = ([b]\<^sup>\<top>\<^sub>R ;; P \<sqinter> [\<not>b]\<^sup>\<top>\<^sub>R)\<^sup>\<star>\<^sup>R ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: AssumeR_NSRD NSRD_right_unit NSRD_srd_skip assms(1) cond_srea_AssumeR_form)
  also have "... = (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [\<not> b]\<^sup>\<top>\<^sub>R\<^sup>\<star>\<^sup>R)\<^sup>\<star>\<^sup>R ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: AssumeR_NSRD NSRD_seqr_closure nsrd_thy.Star_denest assms(1))
  also have "... = (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R)\<^sup>\<star>\<^sup>R ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (metis (no_types, hide_lams) RD3_def RD3_idem Star_AssumeR nsrd_thy.Star_def)
  also have "... = (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R) ;; (P ;; Miracle \<triangleleft> b \<triangleright>\<^sub>R II\<^sub>R)"
    by (simp add: AssumeR_NSRD NSRD_seqr_closure nsrd_thy.Star_invol assms(1))
  also have "... = (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R) ;; ([b]\<^sup>\<top>\<^sub>R ;; P ;; Miracle \<sqinter> [\<not>b]\<^sup>\<top>\<^sub>R)"
    by (simp add: AssumeR_NSRD NSRD_Miracle NSRD_right_unit NSRD_seqr_closure NSRD_srd_skip assms(1) cond_srea_AssumeR_form)
  also have "... = (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R) ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; Miracle \<sqinter> (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R) ;; [\<not>b]\<^sup>\<top>\<^sub>R"
    by (simp add: upred_semiring.distrib_left)
  also have "... = ([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [\<not> b]\<^sup>\<top>\<^sub>R"
  proof -
    have "(([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R) ;; [\<not>b]\<^sup>\<top>\<^sub>R = (II\<^sub>R \<sqinter> ([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P) ;; [\<not> b]\<^sup>\<top>\<^sub>R"
      by (simp add: AssumeR_NSRD NSRD_seqr_closure nsrd_thy.Star_unfoldr_eq assms(1))
    also have "... = [\<not> b]\<^sup>\<top>\<^sub>R \<sqinter> (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P) ;; [\<not> b]\<^sup>\<top>\<^sub>R"
      by (metis (no_types, lifting) AssumeR_NSRD AssumeR_as_gcmd NSRD_srd_skip Star_AssumeR nsrd_thy.Star_slide gcmd_seq_distr skip_srea_self_unit urel_dioid.distrib_right')
    also have "... = [\<not> b]\<^sup>\<top>\<^sub>R \<sqinter> (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; [b \<or> \<not> b]\<^sup>\<top>\<^sub>R) ;; [\<not> b]\<^sup>\<top>\<^sub>R"
      by (simp add: AssumeR_true NSRD_right_unit assms(1))
    also have "... = [\<not> b]\<^sup>\<top>\<^sub>R \<sqinter> (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; [b]\<^sup>\<top>\<^sub>R) ;; [\<not> b]\<^sup>\<top>\<^sub>R
                             \<sqinter> (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; [\<not> b]\<^sup>\<top>\<^sub>R) ;; [\<not> b]\<^sup>\<top>\<^sub>R"
      by (metis (no_types, hide_lams) AssumeR_choice upred_semiring.add_assoc upred_semiring.distrib_left upred_semiring.distrib_right)
    also have "... = [\<not> b]\<^sup>\<top>\<^sub>R \<sqinter> ([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; ([b]\<^sup>\<top>\<^sub>R ;; [\<not> b]\<^sup>\<top>\<^sub>R)
                             \<sqinter> ([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; ([\<not> b]\<^sup>\<top>\<^sub>R ;; [\<not> b]\<^sup>\<top>\<^sub>R)"
      by (simp add: RA1)
    also have "... = [\<not> b]\<^sup>\<top>\<^sub>R \<sqinter> (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; Miracle)
                             \<sqinter> (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; [\<not> b]\<^sup>\<top>\<^sub>R)"
      by (simp add: AssumeR_comp AssumeR_false)
    finally have "([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [\<not> b]\<^sup>\<top>\<^sub>R \<sqsubseteq> (([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R) ;; [b]\<^sup>\<top>\<^sub>R ;; P ;; Miracle"
      by (simp add: semilattice_sup_class.le_supI1)
    thus ?thesis
      by (simp add: semilattice_sup_class.le_iff_sup)
  qed
  finally show ?thesis .
qed
      
theorem WhileR_iter_form:
  assumes "P is NSRD" "P is Productive"
  shows "while\<^sub>R b do P od = ([b]\<^sup>\<top>\<^sub>R ;; P)\<^sup>\<star>\<^sup>R ;; [\<not> b]\<^sup>\<top>\<^sub>R"
  by (simp add: WhileR_iter_form_lemma WhileR_star_expand assms)

theorem WhileR_false:
  assumes "P is NSRD"
  shows "while\<^sub>R false do P od = II\<^sub>R"
  by (simp add: WhileR_def rpred closure srdes_theory_continuous.LFP_const)

theorem WhileR_true:
  assumes "P is NSRD" "P is Productive"
  shows "while\<^sub>R true do P od = P\<^sup>\<star>\<^sup>R ;; Miracle"
  by (simp add: WhileR_iter_form AssumeR_true AssumeR_false SRD_left_unit assms closure)

lemma WhileR_insert_assume:
  assumes "P is NSRD" "P is Productive"
  shows "while\<^sub>R b do ([b]\<^sup>\<top>\<^sub>R ;; P) od = while\<^sub>R b do P od"
  by (simp add: AssumeR_NSRD AssumeR_comp NSRD_seqr_closure Productive_seq_2 RA1 WhileR_iter_form assms)

theorem WhileR_rdes_def [rdes_def]:
  assumes "P is RC" "Q is RR" "R is RR" "$st\<acute> \<sharp> Q" "R is R4"
  shows "while\<^sub>R b do \<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) od = 
         \<^bold>R\<^sub>s (([b]\<^sup>\<top>\<^sub>r ;; R)\<^sup>\<star>\<^sup>r wp\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P) \<turnstile> ([b]\<^sup>\<top>\<^sub>r ;; R)\<^sup>\<star>\<^sup>r ;; [b]\<^sup>\<top>\<^sub>r ;; Q \<diamondop> ([b]\<^sup>\<top>\<^sub>r ;; R)\<^sup>\<star>\<^sup>r ;; [\<not> b]\<^sup>\<top>\<^sub>r)" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = ([b]\<^sup>\<top>\<^sub>R ;; \<^bold>R\<^sub>s (P \<turnstile> Q \<diamondop> R))\<^sup>\<star>\<^sup>R ;; [\<not> b]\<^sup>\<top>\<^sub>R"
    by (simp add: WhileR_iter_form Productive_rdes_RR_intro assms closure)
  also have "... = ?rhs"
    by (simp add: rdes_def assms closure unrest rpred wp del: rea_star_wp)
  finally show ?thesis .
qed

text \<open> Refinement introduction law for reactive while loops \<close>

theorem WhileR_refine_intro:
  assumes 
    -- {* Closure conditions *}
    "Q\<^sub>1 is RC" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR" "$st\<acute> \<sharp> Q\<^sub>2" "Q\<^sub>3 is R4"
    -- {* Refinement conditions *}
    "([b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>3)\<^sup>\<star>\<^sup>r wp\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r Q\<^sub>1) \<sqsubseteq> P\<^sub>1"
    "P\<^sub>2 \<sqsubseteq> [b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>2"
    "P\<^sub>2 \<sqsubseteq> [b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>3 ;; P\<^sub>2"
    "P\<^sub>3 \<sqsubseteq> [\<not>b]\<^sup>\<top>\<^sub>r"
    "P\<^sub>3 \<sqsubseteq> [b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>3 ;; P\<^sub>3"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<sqsubseteq> while\<^sub>R b do \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) od"
proof (simp add: rdes_def assms, rule srdes_tri_refine_intro')
  show "([b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>3)\<^sup>\<star>\<^sup>r wp\<^sub>r ([b]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r Q\<^sub>1) \<sqsubseteq> P\<^sub>1"
    by (simp add: assms)
  show "P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> ([b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>3)\<^sup>\<star>\<^sup>r ;; [b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>2)"
  proof -
    have "P\<^sub>2 \<sqsubseteq> ([b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>3)\<^sup>\<star>\<^sup>r ;; [b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>2"
      by (simp add: assms rea_assume_RR rrel_thy.Star_inductl seq_RR_closed seqr_assoc)
    thus ?thesis
      by (simp add: utp_pred_laws.le_infI2)
  qed
  show "P\<^sub>3 \<sqsubseteq> (P\<^sub>1 \<and> ([b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>3)\<^sup>\<star>\<^sup>r ;; [\<not> b]\<^sup>\<top>\<^sub>r)"
  proof -
    have "P\<^sub>3 \<sqsubseteq> ([b]\<^sup>\<top>\<^sub>r ;; Q\<^sub>3)\<^sup>\<star>\<^sup>r ;; [\<not> b]\<^sup>\<top>\<^sub>r"
      by (simp add: assms rea_assume_RR rrel_thy.Star_inductl seqr_assoc)
    thus ?thesis
      by (simp add: utp_pred_laws.le_infI2)
  qed
qed

subsection \<open> Iteration Construction \<close>

definition IterateR
  :: "'a set \<Rightarrow> ('a \<Rightarrow> 's upred) \<Rightarrow> ('a \<Rightarrow> ('s, 't::size_trace, '\<alpha>) hrel_rsp) \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp"
where "IterateR A g P = while\<^sub>R (\<Or> i\<in>A \<bullet> g(i)) do (if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> P(i) fi) od"

definition IterateR_list 
  :: "('s upred \<times> ('s, 't::size_trace, '\<alpha>) hrel_rsp) list \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" where 
[upred_defs, ndes_simp]:
  "IterateR_list xs = IterateR {0..<length xs} (\<lambda> i. map fst xs ! i) (\<lambda> i. map snd xs ! i)"

syntax
  "_iter_srd"    :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("do\<^sub>R _\<in>_ \<bullet> _ \<rightarrow> _ fi")
  "_iter_gcommR" :: "gcomms \<Rightarrow> logic" ("do\<^sub>R/ _ /od")

translations
  "_iter_srd x A g P" => "CONST IterateR A (\<lambda> x. g) (\<lambda> x. P)"
  "_iter_srd x A g P" <= "CONST IterateR A (\<lambda> x. g) (\<lambda> x'. P)"
  "_iter_gcommR cs" \<rightharpoonup> "CONST IterateR_list cs"
  "_iter_gcommR (_gcomm_show cs)" \<leftharpoondown> "CONST IterateR_list cs"

lemma IterateR_NSRD_closed [closure]:
  assumes 
    "\<And> i. i \<in> I \<Longrightarrow> P(i) is NSRD" 
    "\<And> i. i \<in> I \<Longrightarrow> P(i) is Productive"
  shows "do\<^sub>R i\<in>I \<bullet> g(i) \<rightarrow> P(i) fi is NSRD"
  by (simp add: IterateR_def closure assms)

lemma IterateR_empty: 
  "do\<^sub>R i\<in>{} \<bullet> g(i) \<rightarrow> P(i) fi = II\<^sub>R"
  by (simp add: IterateR_def srd_mu_equiv closure rpred gfp_const WhileR_false)

lemma IterateR_singleton: 
  assumes "P k is NSRD" "P k is Productive"
  shows "do\<^sub>R i\<in>{k} \<bullet> g(i) \<rightarrow> P(i) fi = while\<^sub>R g(k) do P(k) od" (is "?lhs = ?rhs")
proof -
  have "?lhs = while\<^sub>R g k do P k \<triangleleft> g k \<triangleright>\<^sub>R Chaos od"
    by (simp add: IterateR_def AlternateR_singleton assms closure)
  also have "... = while\<^sub>R g k do [g k]\<^sup>\<top>\<^sub>R ;; (P k \<triangleleft> g k \<triangleright>\<^sub>R Chaos) od"
    by (simp add: WhileR_insert_assume closure assms)
  also have "... = while\<^sub>R g k do P k od"
    by (simp add: AssumeR_cond_left NSRD_Chaos WhileR_insert_assume assms)
  finally show ?thesis .
qed

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

lemma AlternateR_seq_distr:
  assumes "\<And> i. A i is NSRD" "B is NSRD" "C is NSRD"
  shows "(if\<^sub>R i \<in> I \<bullet> g i \<rightarrow> A i else B fi) ;; C = (if\<^sub>R i \<in> I \<bullet> g i \<rightarrow> A i ;; C else B ;; C fi)"
proof (cases "I = {}")
  case True
  then show ?thesis by (simp)
next
  case False
  then show ?thesis
    by (simp add: AlternateR_def upred_semiring.distrib_right seq_UINF_distr gcmd_seq_distr assms(3))
qed

lemma AlternateR_is_cond_srea:
  assumes "A is NSRD" "B is NSRD"
  shows "(if\<^sub>R i \<in> {a} \<bullet> g \<rightarrow> A else B fi) = (A \<triangleleft> g \<triangleright>\<^sub>R B)"
  by (rdes_eq cls: assms)

lemma AlternateR_Chaos: 
  "if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> Chaos fi = Chaos"
  by (cases "A = {}", simp, rdes_eq)

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