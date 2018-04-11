section {* Imperative Programming in Designs *}

theory utp_des_prog
  imports utp_des_tactics
begin

subsection {* Assignment *}

definition assigns_d :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel_des" ("\<langle>_\<rangle>\<^sub>D") where 
[upred_defs]: "assigns_d \<sigma> = (true \<turnstile>\<^sub>r assigns_r \<sigma>)"

syntax
  "_assignmentd" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>D" 72)

translations
  "_assignmentd xs vs" => "CONST assigns_d (_mk_usubst (CONST id) xs vs)"
  "_assignmentd x v" <= "CONST assigns_d (CONST subst_upd (CONST id) x v)"
  "_assignmentd x v" <= "_assignmentd (_spvar x) v"
  "x,y :=\<^sub>D u,v" <= "CONST assigns_d (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

lemma assigns_d_is_H1_H2 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>D is \<^bold>H"
  by (simp add: assigns_d_def rdesign_is_H1_H2)

lemma assigns_d_H1_H3 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>D is \<^bold>N"
  by (metis H1_rdesign H3_ndesign Healthy_def' aext_true assigns_d_def ndesign_def)

text {* Designs are closed under substitutions on state variables only (via lifting) *}

lemma state_subst_H1_H2_closed [closure]: 
  "P is \<^bold>H \<Longrightarrow> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> P is \<^bold>H"
  by (metis H1_H2_eq_rdesign Healthy_if rdesign_is_H1_H2 state_subst_design)

lemma assigns_d_ndes_def [ndes_simp]:
  "\<langle>\<sigma>\<rangle>\<^sub>D = (true \<turnstile>\<^sub>n \<langle>\<sigma>\<rangle>\<^sub>a)"
  by (rel_auto)
    
lemma assigns_d_id [simp]: "\<langle>id\<rangle>\<^sub>D = II\<^sub>D"
  by (rel_auto)

lemma assign_d_left_comp:
  "(\<langle>f\<rangle>\<^sub>D ;; (P \<turnstile>\<^sub>r Q)) = (\<lceil>f\<rceil>\<^sub>s \<dagger> P \<turnstile>\<^sub>r \<lceil>f\<rceil>\<^sub>s \<dagger> Q)"
  by (simp add: assigns_d_def rdesign_composition assigns_r_comp subst_not)

lemma assign_d_right_comp:
  "((P \<turnstile>\<^sub>r Q) ;; \<langle>f\<rangle>\<^sub>D) = ((\<not> ((\<not> P) ;; true)) \<turnstile>\<^sub>r (Q ;; \<langle>f\<rangle>\<^sub>a))"
  by (simp add: assigns_d_def rdesign_composition)

lemma assigns_d_comp:
  "(\<langle>f\<rangle>\<^sub>D ;; \<langle>g\<rangle>\<^sub>D) = \<langle>g \<circ> f\<rangle>\<^sub>D"
  by (simp add: assigns_d_def rdesign_composition assigns_comp)

lemma assigns_d_comp_ext:
  fixes P :: "'\<alpha> hrel_des"
  assumes "P is \<^bold>H"
  shows "(\<langle>\<sigma>\<rangle>\<^sub>D ;; P) = \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> P"
proof -
  have "\<langle>\<sigma>\<rangle>\<^sub>D ;; P = \<langle>\<sigma>\<rangle>\<^sub>D ;; (pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P))"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def' assms)
  also have "... = \<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> pre\<^sub>D(P) \<turnstile>\<^sub>r \<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> post\<^sub>D(P)"
    by (simp add: assign_d_left_comp)
  also have "... = \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> (pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P))"
    by (rel_auto)
  also have "... = \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> P"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def' assms)
  finally show ?thesis .
qed

text {* Normal designs are closed under substitutions on state variables only *}

lemma state_subst_H1_H3_closed [closure]: 
  "P is \<^bold>N \<Longrightarrow> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> P is \<^bold>N"
  by (metis H1_H2_eq_rdesign H1_H3_impl_H2 Healthy_if assign_d_left_comp assigns_d_H1_H3 seq_r_H1_H3_closed state_subst_design)

lemma H4_assigns_d: "\<langle>\<sigma>\<rangle>\<^sub>D is H4"
proof -
  have "(\<langle>\<sigma>\<rangle>\<^sub>D ;; (false \<turnstile>\<^sub>r true\<^sub>h)) = (false \<turnstile>\<^sub>r true)"
    by (simp add: assigns_d_def rdesign_composition assigns_r_feasible)
  moreover have "... = true"
    by (rel_auto)
  ultimately show ?thesis
    using is_H4_alt_def by auto
qed

subsection {* Guarded Commands *}

definition GrdCommD :: "'\<alpha> upred \<Rightarrow> ('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("_ \<rightarrow>\<^sub>D _" [85, 86] 85) where
[upred_defs]: "b \<rightarrow>\<^sub>D P = P \<triangleleft> b \<triangleright>\<^sub>D \<top>\<^sub>D"

lemma GrdCommD_ndes_simp [ndes_simp]:
  "b \<rightarrow>\<^sub>D (p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) = ((b \<Rightarrow> p\<^sub>1) \<turnstile>\<^sub>n (\<lceil>b\<rceil>\<^sub>< \<and> P\<^sub>2))"
  by (rel_auto)

lemma GrdCommD_H1_H3_closed [closure]: "P is \<^bold>N \<Longrightarrow> b \<rightarrow>\<^sub>D P is \<^bold>N"
  by (simp add: GrdCommD_def closure)

lemma GrdCommD_true [simp]: "true \<rightarrow>\<^sub>D P = P"
  by (rel_auto)
    
lemma GrdCommD_false [simp]: "false \<rightarrow>\<^sub>D P = \<top>\<^sub>D"
  by (rel_auto)
  
lemma GrdCommD_abort [simp]: "b \<rightarrow>\<^sub>D true = ((\<not> b) \<turnstile>\<^sub>n false)"
  by (rel_auto)

subsection {* Alternation *}
  
consts
  ualtern       :: "'a set \<Rightarrow> ('a \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> 'r) \<Rightarrow> 'r \<Rightarrow> 'r"
  ualtern_list  :: "('a \<times> 'r) list \<Rightarrow> 'r \<Rightarrow> 'r"
  
definition AlternateD :: "'a set \<Rightarrow> ('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> ('\<alpha>, '\<beta>) rel_des) \<Rightarrow> ('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" where
[upred_defs, ndes_simp]:
"AlternateD A g P Q = (\<Sqinter> i\<in>A \<bullet> g(i) \<rightarrow>\<^sub>D P(i)) \<sqinter> (\<And> i\<in>A \<bullet> \<not> g(i)) \<rightarrow>\<^sub>D Q"

text {* This lemma shows that our generalised alternation is the same operator as Marcel Oliveira's
  definition of alternation when the else branch is abort. *}

lemma AlternateD_abort_alternate:
  assumes "\<And> i. P(i) is \<^bold>N"
  shows
  "AlternateD A g P \<bottom>\<^sub>D = 
  ((\<Or> i\<in>A \<bullet> g(i)) \<and> (\<And> i\<in>A \<bullet> g(i) \<Rightarrow> \<lfloor>pre\<^sub>D(P i)\<rfloor>\<^sub><)) \<turnstile>\<^sub>n (\<Or> i\<in>A \<bullet> \<lceil>g(i)\<rceil>\<^sub>< \<and> post\<^sub>D(P i))"
proof (cases "A = {}")
  case False
  have "AlternateD A g P \<bottom>\<^sub>D = 
        (\<Sqinter> i\<in>A \<bullet> g(i) \<rightarrow>\<^sub>D (\<lfloor>pre\<^sub>D(P i)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P i))) \<sqinter> (\<And> i\<in>A \<bullet> \<not> g(i)) \<rightarrow>\<^sub>D (false \<turnstile>\<^sub>n true)"
    by (simp add: AlternateD_def ndesign_form bot_d_ndes_def assms)
  also have "... = ((\<Or> i\<in>A \<bullet> g(i)) \<and> (\<And> i\<in>A \<bullet> g(i) \<Rightarrow> \<lfloor>pre\<^sub>D(P i)\<rfloor>\<^sub><)) \<turnstile>\<^sub>n (\<Or> i\<in>A \<bullet> \<lceil>g(i)\<rceil>\<^sub>< \<and> post\<^sub>D(P i))"
    by (simp add: ndes_simp False, rel_auto)
  finally show ?thesis by simp
next
  case True
  thus ?thesis
    by (simp add: AlternateD_def, rel_auto)
qed
     
definition AlternateD_list :: "('\<alpha> upred \<times> ('\<alpha>, '\<beta>) rel_des) list \<Rightarrow> ('\<alpha>, '\<beta>) rel_des  \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" where 
[upred_defs, ndes_simp]:
"AlternateD_list xs P = 
  AlternateD {0..<length xs} (\<lambda> i. map fst xs ! i) (\<lambda> i. map snd xs ! i) P"

adhoc_overloading
  ualtern AlternateD and
  ualtern_list AlternateD_list

nonterminal gcomm and gcomms
  
syntax
  "_altind_els"   :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if _\<in>_ \<bullet> _ \<rightarrow> _ else _ fi")
  "_altind"       :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("if _\<in>_ \<bullet> _ \<rightarrow> _ fi")
  "_gcomm"        :: "logic \<Rightarrow> logic \<Rightarrow> gcomm" ("_ \<rightarrow> _" [65, 66] 65)
  "_gcomm_nil"    :: "gcomm \<Rightarrow> gcomms" ("_")
  "_gcomm_cons"   :: "gcomm \<Rightarrow> gcomms \<Rightarrow> gcomms" ("_ |/ _" [60, 61] 61)
  "_gcomm_show"   :: "logic \<Rightarrow> logic"
  "_altgcomm_els" :: "gcomms \<Rightarrow> logic \<Rightarrow> logic" ("if/ _ /else _ /fi")
  "_altgcomm"     :: "gcomms \<Rightarrow> logic" ("if/ _ /fi")

translations
  "_altind_els x A g P Q" => "CONST ualtern A (\<lambda> x. g) (\<lambda> x. P) Q"
  "_altind_els x A g P Q" <= "CONST ualtern A (\<lambda> x. g) (\<lambda> x'. P) Q"
  "_altind x A g P" => "CONST ualtern A (\<lambda> x. g) (\<lambda> x. P) (CONST Orderings.top)"
  "_altind x A g P" <= "CONST ualtern A (\<lambda> x. g) (\<lambda> x'. P) (CONST Orderings.top)"
  "_altgcomm cs" => "CONST ualtern_list cs (CONST Orderings.top)"
  "_altgcomm (_gcomm_show cs)" <= "CONST ualtern_list cs (CONST Orderings.top)"
  "_altgcomm_els cs P" => "CONST ualtern_list cs P"
  "_altgcomm_els (_gcomm_show cs) P" <= "CONST ualtern_list cs P"

  "_gcomm g P" => "(g, P)"
  "_gcomm g P" <= "_gcomm_show (g, P)"
  "_gcomm_cons c cs" => "c # cs"
  "_gcomm_cons (_gcomm_show c) (_gcomm_show (d # cs))" <= "_gcomm_show (c # d # cs)"
  "_gcomm_nil c" => "[c]"
  "_gcomm_nil (_gcomm_show c)" <= "_gcomm_show [c]"

lemma AlternateD_H1_H3_closed [closure]: 
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is \<^bold>N" "Q is \<^bold>N"
  shows "if i\<in>A \<bullet> g(i) \<rightarrow> P(i) else Q fi is \<^bold>N"
proof (cases "A = {}")
  case True
  then show ?thesis
    by (simp add: AlternateD_def closure false_upred_def assms)
next
  case False
  then show ?thesis
    by (simp add: AlternateD_def closure assms)
qed
    
lemma AltD_ndes_simp [ndes_simp]: 
  "if i\<in>A \<bullet> g(i) \<rightarrow> (P\<^sub>1(i) \<turnstile>\<^sub>n P\<^sub>2(i)) else Q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2 fi 
   = ((\<And> i \<in> A \<bullet> g i \<Rightarrow> P\<^sub>1 i) \<and> ((\<And> i \<in> A \<bullet> \<not> g i) \<Rightarrow> Q\<^sub>1)) \<turnstile>\<^sub>n
     ((\<Or> i \<in> A \<bullet> \<lceil>g i\<rceil>\<^sub>< \<and> P\<^sub>2 i) \<or> (\<And> i \<in> A \<bullet> \<not> \<lceil>g i\<rceil>\<^sub><) \<and> Q\<^sub>2)"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: AlternateD_def)
next
  case False
  then show ?thesis
    by (simp add: ndes_simp, rel_auto)
qed

declare UINF_upto_expand_first [ndes_simp]
declare UINF_Suc_shift [ndes_simp]
declare USUP_upto_expand_first [ndes_simp]
declare USUP_Suc_shift [ndes_simp]
declare true_upred_def [THEN sym, ndes_simp]
  
lemma AlternateD_mono_refine:
  assumes "\<And> i. P i \<sqsubseteq> Q i" "R \<sqsubseteq> S"
  shows "(if i\<in>A \<bullet> g(i) \<rightarrow> P(i) else R fi) \<sqsubseteq> (if i\<in>A \<bullet> g(i) \<rightarrow> Q(i) else S fi)"
  using assms by (rel_auto, meson)
  
lemma Monotonic_AlternateD [closure]:
  "\<lbrakk> \<And> i. Monotonic (F i); Monotonic G \<rbrakk> \<Longrightarrow> Monotonic (\<lambda> X. if i\<in>A \<bullet> g(i) \<rightarrow> F i X else G(X) fi)" 
  by (rel_auto, meson)

lemma AlternateD_eq:
  assumes "A = B" "\<And> i. i\<in>A \<Longrightarrow> g(i) = h(i)" "\<And> i. i\<in>A \<Longrightarrow> P(i) = Q(i)" "R = S"
  shows "if i\<in>A \<bullet> g(i) \<rightarrow> P(i) else R fi = if i\<in>B \<bullet> h(i) \<rightarrow> Q(i) else S fi"
  by (insert assms, rel_blast)

lemma AlternateD_empty:
  "if i\<in>{} \<bullet> g(i) \<rightarrow> P(i) else Q fi = Q"
  by (rel_auto)
    
lemma AlternateD_true_singleton:
  assumes "P is \<^bold>N"
  shows "if true \<rightarrow> P fi = P"
  by (ndes_eq cls: assms)

lemma AlernateD_no_ind:
  assumes "A \<noteq> {}" "P is \<^bold>N" "Q is \<^bold>N"
  shows "if i\<in>A \<bullet> b \<rightarrow> P else Q fi = if b \<rightarrow> P else Q fi"
  by (ndes_eq cls: assms)

lemma AlernateD_singleton:
  assumes "P k is \<^bold>N" "Q is \<^bold>N"
  shows "if i\<in>{k} \<bullet> b(i) \<rightarrow> P(i) else Q fi = if b(k) \<rightarrow> P(k) else Q fi" (is "?lhs = ?rhs")
proof -
  have "?lhs = if i\<in>{k} \<bullet> b(k) \<rightarrow> P(k) else Q fi"
    by (auto intro: AlternateD_eq simp add: assms ndesign_form)
  also have "... = ?rhs"
    by (simp add: AlernateD_no_ind assms closure)
  finally show ?thesis .
qed

lemma AlternateD_commute:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "if g\<^sub>1 \<rightarrow> P | g\<^sub>2 \<rightarrow> Q fi = if g\<^sub>2 \<rightarrow> Q | g\<^sub>1 \<rightarrow> P fi"
  by (ndes_eq cls:assms)

lemma AlternateD_dcond:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "if g \<rightarrow> P else Q fi = P \<triangleleft> g \<triangleright>\<^sub>D Q"
  by (ndes_eq cls:assms)

lemma AlternateD_cover:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "if g \<rightarrow> P else Q fi = if g \<rightarrow> P | (\<not> g) \<rightarrow> Q fi"
  by (ndes_eq cls: assms)

lemma UINF_ndes_expand:
  assumes "\<And> i. i\<in>A \<Longrightarrow> P(i) is \<^bold>N"
  shows "(\<Sqinter> i \<in> A \<bullet> \<lfloor>pre\<^sub>D(P(i))\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P(i))) = (\<Sqinter> i \<in> A \<bullet> P(i))"
  by (rule UINF_cong, simp add: assms ndesign_form)

lemma USUP_ndes_expand:
  assumes "\<And> i. i\<in>A \<Longrightarrow> P(i) is \<^bold>N"
  shows "(\<Squnion> i \<in> A \<bullet> \<lfloor>pre\<^sub>D(P(i))\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P(i))) = (\<Squnion> i \<in> A \<bullet> P(i))"
  by (rule USUP_cong, simp add: assms ndesign_form)
    
lemma AlternateD_ndes_expand:
  assumes "\<And> i. i\<in>A \<Longrightarrow> P(i) is \<^bold>N" "Q is \<^bold>N"
  shows "if i\<in>A \<bullet> g(i) \<rightarrow> P(i) else Q fi =
         if i\<in>A \<bullet> g(i) \<rightarrow> (\<lfloor>pre\<^sub>D(P(i))\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P(i))) else \<lfloor>pre\<^sub>D(Q)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(Q) fi"
  apply (simp add: AlternateD_def)
  apply (subst UINF_ndes_expand[THEN sym])
   apply (simp add: assms closure)
  apply (ndes_simp cls: assms)
  apply (rel_auto)
  done

lemma AlternateD_ndes_expand':
  assumes "\<And> i. i\<in>A \<Longrightarrow> P(i) is \<^bold>N"
  shows "if i\<in>A \<bullet> g(i) \<rightarrow> P(i) fi = if i\<in>A \<bullet> g(i) \<rightarrow> (\<lfloor>pre\<^sub>D(P(i))\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P(i))) fi"
  apply (simp add: AlternateD_def)
  apply (subst UINF_ndes_expand[THEN sym])
   apply (simp add: assms closure)
  apply (ndes_simp cls: assms)
  apply (rel_auto)
  done

lemma ndesign_ind_form:
  assumes "\<And> i. P(i) is \<^bold>N"
  shows "(\<lambda> i. \<lfloor>pre\<^sub>D(P(i))\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P(i))) = P"
  by (simp add: assms ndesign_form)
    
lemma AlternateD_insert:
  assumes "\<And> i. i\<in>(insert x A) \<Longrightarrow> P(i) is \<^bold>N" "Q is \<^bold>N"
  shows "if i\<in>(insert x A) \<bullet> g(i) \<rightarrow> P(i) else Q fi = 
         if g(x) \<rightarrow> P(x) | 
            (\<Or> i\<in>A \<bullet> g(i)) \<rightarrow> if i\<in>A \<bullet> g(i) \<rightarrow> P(i) fi 
            else Q 
         fi" (is "?lhs = ?rhs")
proof -
  have "?lhs = if i\<in>(insert x A) \<bullet> g(i) \<rightarrow> (\<lfloor>pre\<^sub>D(P(i))\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P(i))) else (\<lfloor>pre\<^sub>D(Q)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(Q)) fi"
    using AlternateD_ndes_expand assms(1) assms(2) by blast
  also 
  have "... =
         if g(x) \<rightarrow> (\<lfloor>pre\<^sub>D(P(x))\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P(x))) | 
            (\<Or> i\<in>A \<bullet> g(i)) \<rightarrow> if i\<in>A \<bullet> g(i) \<rightarrow> \<lfloor>pre\<^sub>D(P(i))\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P(i)) fi 
            else \<lfloor>pre\<^sub>D(Q)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(Q)
         fi"
    by (ndes_simp cls:assms, rel_auto)
  also have "... = ?rhs"
    by (simp add: AlternateD_ndes_expand' ndesign_form assms)
  finally show ?thesis .
qed
   
subsection {* Iteration *}

theorem ndesign_iteration_wp [ndes_simp]:
  "(p \<turnstile>\<^sub>n Q) ;; (p \<turnstile>\<^sub>n Q) \<^bold>^ n = ((\<And> i\<in>{0..n} \<bullet> (Q \<^bold>^ i) wp p) \<turnstile>\<^sub>n Q \<^bold>^ Suc n)"
proof (induct n)
  case 0
  then show ?case by (rel_auto)
next
  case (Suc n) note hyp = this
  have "(p \<turnstile>\<^sub>n Q) ;; (p \<turnstile>\<^sub>n Q) \<^bold>^ Suc n = (p \<turnstile>\<^sub>n Q) ;; (p \<turnstile>\<^sub>n Q) ;; (p \<turnstile>\<^sub>n Q) \<^bold>^ n"
    by (simp add: upred_semiring.power_Suc)
  also have "... = (p \<turnstile>\<^sub>n Q) ;; ((\<Squnion> i \<in> {0..n} \<bullet> Q \<^bold>^ i wp p) \<turnstile>\<^sub>n Q \<^bold>^ Suc n)"
    by (simp add: hyp)
  also have "... = (p \<and> Q wp (\<Squnion> i \<in> {0..n} \<bullet> Q \<^bold>^ i wp p)) \<turnstile>\<^sub>n (Q ;; Q) ;; Q \<^bold>^ n"
    by (simp add: upred_semiring.power_Suc ndesign_composition_wp seqr_assoc)
  also have "... = (p \<and> (\<Squnion> i \<in> {0..n} \<bullet> Q \<^bold>^ Suc i wp p)) \<turnstile>\<^sub>n (Q ;; Q) ;; Q \<^bold>^ n"
    by (simp add: upred_semiring.power_Suc wp)
  also have "... = (p \<and> (\<Squnion> i \<in> {0..n}. Q \<^bold>^ Suc i wp p)) \<turnstile>\<^sub>n (Q ;; Q) ;; Q \<^bold>^ n"
    by (simp add: USUP_as_Inf_image)
  also have "... = (p \<and> (\<Squnion> i \<in> {1..Suc n}. Q \<^bold>^ i wp p)) \<turnstile>\<^sub>n (Q ;; Q) ;; Q \<^bold>^ n"
    by (metis (no_types, lifting) One_nat_def image_Suc_atLeastAtMost image_cong image_image)  
  also have "... = (Q \<^bold>^ 0 wp p \<and> (\<Squnion> i \<in> {1..Suc n}. Q \<^bold>^ i wp p)) \<turnstile>\<^sub>n (Q ;; Q) ;; Q \<^bold>^ n"
    by (simp add: wp)
  also have "... = ((\<Squnion> i \<in> {0..Suc n}. Q \<^bold>^ i wp p)) \<turnstile>\<^sub>n (Q ;; Q) ;; Q \<^bold>^ n"
    by (simp add: Iic_Suc_eq_insert_0 atLeast0AtMost conj_upred_def image_Suc_atMost)      
  also have "... = (\<Squnion> i \<in> {0..Suc n} \<bullet> Q \<^bold>^ i wp p) \<turnstile>\<^sub>n Q \<^bold>^ Suc (Suc n)"
    by (simp add: upred_semiring.power_Suc USUP_as_Inf_image upred_semiring.mult_assoc)
  finally show ?case .
qed

text {* Overloadable Syntax *}
  
consts
  uiterate       :: "'a set \<Rightarrow> ('a \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> 'r) \<Rightarrow> 'r"
  uiterate_list  :: "('a \<times> 'r) list \<Rightarrow> 'r"

syntax
  "_iterind"       :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("do _\<in>_ \<bullet> _ \<rightarrow> _ od")
  "_itergcomm"     :: "gcomms \<Rightarrow> logic" ("do _ od")
  
translations
  "_iterind x A g P" => "CONST uiterate A (\<lambda> x. g) (\<lambda> x. P)"
  "_iterind x A g P" <= "CONST uiterate A (\<lambda> x. g) (\<lambda> x'. P)"
  "_itergcomm cs" => "CONST uiterate_list cs"
  "_itergcomm (_gcomm_show cs)" <= "CONST uiterate_list cs"
  
definition IterateD :: "'a set \<Rightarrow> ('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> '\<alpha> hrel_des) \<Rightarrow> '\<alpha> hrel_des" where
[upred_defs, ndes_simp]:
"IterateD A g P = (\<^bold>\<mu>\<^bsub>NDES\<^esub> X \<bullet> if i\<in>A \<bullet> g(i) \<rightarrow> P(i) ;; X else II\<^sub>D fi)"

definition IterateD_list :: "('\<alpha> upred \<times> '\<alpha> hrel_des) list \<Rightarrow> '\<alpha> hrel_des" where 
[upred_defs, ndes_simp]:
"IterateD_list xs = IterateD {0..<length xs} (\<lambda> i. fst (nth xs i)) (\<lambda> i. snd (nth xs i))"

adhoc_overloading
  uiterate IterateD and
  uiterate_list IterateD_list
  
lemma IterateD_H1_H3_closed [closure]: 
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is \<^bold>N"
  shows "do i\<in>A \<bullet> g(i) \<rightarrow> P(i) od is \<^bold>N"
proof (cases "A = {}")
  case True
  then show ?thesis
    by (simp add: IterateD_def closure assms)
next
  case False
  then show ?thesis
    by (simp add: IterateD_def closure assms)
qed

lemma IterateD_empty:
  "do i\<in>{} \<bullet> g(i) \<rightarrow> P(i) od = II\<^sub>D"
  by (simp add: IterateD_def AlternateD_empty normal_design_theory_continuous.LFP_const skip_d_is_H1_H3)

lemma IterateD_list_single_expand:
  "do b \<rightarrow> P od = (\<^bold>\<mu>\<^bsub>NDES\<^esub> X \<bullet> if b \<rightarrow> P ;; X else II\<^sub>D fi)"
oops
    
lemma IterateD_singleton:
  assumes "P is \<^bold>N"
  shows "do b \<rightarrow> P od = do i\<in>{0} \<bullet> b \<rightarrow> P od"
  apply (simp add: IterateD_list_def IterateD_def AlernateD_singleton assms)
  apply (subst AlernateD_singleton)
  apply (simp)
  apply (rel_auto)
oops

lemma IterateD_mono_refine:
  assumes 
    "\<And> i. P i is \<^bold>N" "\<And> i. Q i is \<^bold>N"
    "\<And> i. P i \<sqsubseteq> Q i"
  shows "(do i\<in>A \<bullet> g(i) \<rightarrow> P(i) od) \<sqsubseteq> (do i\<in>A \<bullet> g(i) \<rightarrow> Q(i) od)"
  apply (simp add: IterateD_def normal_design_theory_continuous.utp_lfp_def)
  apply (subst normal_design_theory_continuous.utp_lfp_def)
  apply (simp_all add: closure assms)
  apply (subst normal_design_theory_continuous.utp_lfp_def)
  apply (simp_all add: closure assms)
  apply (simp add: ndes_hcond_def)
  apply (rule gfp_mono)
  apply (rule AlternateD_mono_refine)
  apply (simp_all add: closure seqr_mono assms)
done

lemma IterateD_single_refine:
  assumes 
    "P is \<^bold>N" "Q is \<^bold>N" "P \<sqsubseteq> Q"
  shows "(do g \<rightarrow> P od) \<sqsubseteq> (do g \<rightarrow> Q od)"
oops
  
lemma IterateD_refine_intro:
  fixes V :: "(nat, 'a) uexpr"
  assumes "vwb_lens w"
  shows
  "I \<turnstile>\<^sub>n (w:[\<lceil>I \<and> \<not> (\<Or> i\<in>A \<bullet> g(i))\<rceil>\<^sub>>]) \<sqsubseteq> 
   do i\<in>A \<bullet> g(i) \<rightarrow> (I \<and> g(i)) \<turnstile>\<^sub>n (w:[\<lceil>I\<rceil>\<^sub>> \<and> \<lceil>V\<rceil>\<^sub>> <\<^sub>u \<lceil>V\<rceil>\<^sub><]) od"
proof (cases "A = {}")
  case True
  with assms show ?thesis
    by (simp add: IterateD_empty, rel_auto)
next
  case False
  then show ?thesis
  using assms
    apply (simp add: IterateD_def)
    apply (rule ndesign_mu_wf_refine_intro[where e=V and R="{(x, y). x < y}"])
    apply (simp_all add: wf closure)
    apply (simp add: ndes_simp unrest)
    apply (rule ndesign_refine_intro)
    apply (rel_auto)
    apply (rel_auto)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
qed
  
lemma IterateD_single_refine_intro:
  fixes V :: "(nat, 'a) uexpr"
  assumes "vwb_lens w"
  shows
  "I \<turnstile>\<^sub>n (w:[\<lceil>I \<and> \<not> g\<rceil>\<^sub>>]) \<sqsubseteq> 
   do g \<rightarrow> ((I \<and> g) \<turnstile>\<^sub>n (w:[\<lceil>I\<rceil>\<^sub>> \<and> \<lceil>V\<rceil>\<^sub>> <\<^sub>u \<lceil>V\<rceil>\<^sub><])) od"
  apply (rule order_trans)
  defer
   apply (rule IterateD_refine_intro[of w "{0}" "\<lambda> i. g" I V, simplified, OF assms(1)])
  oops

subsection {* Let and Local Variables *}
  
definition LetD :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a \<Rightarrow> '\<alpha> hrel_des) \<Rightarrow> '\<alpha> hrel_des" where
[upred_defs]: "LetD v P = (P x)\<lbrakk>x \<rightarrow> \<lceil>v\<rceil>\<^sub>D\<^sub><\<rbrakk>"

syntax
  "_LetD"       :: "[letbinds, 'a] \<Rightarrow> 'a"                ("(let\<^sub>D (_)/ in (_))" [0, 10] 10)

translations
  "_LetD (_binds b bs) e"  \<rightleftharpoons> "_LetD b (_LetD bs e)"
  "let\<^sub>D x = a in e"        \<rightleftharpoons> "CONST LetD a (\<lambda>x. e)"

lemma LetD_ndes_simp [ndes_simp]: 
  "LetD v (\<lambda> x. p(x) \<turnstile>\<^sub>n Q(x)) = (p(x)\<lbrakk>x \<rightarrow> v\<rbrakk>) \<turnstile>\<^sub>n (Q(x)\<lbrakk>x \<rightarrow> \<lceil>v\<rceil>\<^sub><\<rbrakk>)"
  by (rel_auto)
    
lemma LetD_H1_H3_closed [closure]:
  "\<lbrakk> \<And> x. P(x) is \<^bold>N \<rbrakk> \<Longrightarrow> LetD v P is \<^bold>N"
  by (rel_auto)

subsection {* Deep Local Variables *}

definition des_local_state :: 
  "'a::countable itself \<Rightarrow> ((nat, 's) local_scheme des, 's, nat, 'a::countable) local_prim" where
  "des_local_state t = \<lparr> sstate = \<Sigma>\<^sub>D, sassigns = assigns_d, inj_local = nat_inj_univ \<rparr>"
  
syntax
  "_des_local_state_type" :: "type \<Rightarrow> logic" ("\<L>\<^sub>D[_]")
  "_des_var_scope_type" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var\<^sub>D _ :: _ \<bullet> _" [0, 0, 10] 10)
  
translations
  "\<L>\<^sub>D['a]" == "CONST des_local_state TYPE('a)"
  "_des_var_scope_type x t P" => "_var_scope_type (_des_local_state_type t) x t P"
  "var\<^sub>D x :: 'a \<bullet> P" <= "var[\<L>\<^sub>D['a]] x \<bullet> P"
  
lemma get_rel_local [lens_defs]:
  "get\<^bsub>\<^bold>s\<^bsub>\<L>\<^sub>D['a::countable]\<^esub>\<^esub> = get\<^bsub>\<Sigma>\<^sub>D\<^esub>"
  by (simp add: des_local_state_def)
    
lemma des_local_state [simp]: "utp_local_state \<L>\<^sub>D['a::countable]"
  by (unfold_locales, simp_all add: upred_defs assigns_comp des_local_state_def, rel_auto)
     (metis local.cases_scheme)
     
lemma sassigns_des_state [simp]: "\<^bold>\<langle>\<sigma>\<^bold>\<rangle>\<^bsub>\<L>\<^sub>D['a::countable]\<^esub> = \<langle>\<sigma>\<rangle>\<^sub>D"
  by (simp add: des_local_state_def)

lemma des_var_open_H1_H3_closed [closure]:
  "open[\<L>\<^sub>D['a::countable]] is \<^bold>N"
  by (simp add: utp_local_state.var_open_def closure)

lemma des_var_close_H1_H3_closed [closure]:
  "close[\<L>\<^sub>D['a::countable]] is \<^bold>N"
  by (simp add: utp_local_state.var_close_def closure)  
   
lemma unrest_ok_vtop_des [unrest]: "ok \<sharp> top[\<L>\<^sub>D['a::countable]]"
  by (simp add: utp_local_state.top_var_def, simp add: des_local_state_def  unrest)
    
lemma msubst_H1_H3_closed [closure]:
  "\<lbrakk> $ok \<sharp> v; out\<alpha> \<sharp> v; (\<And>x. P x is \<^bold>N) \<rbrakk> \<Longrightarrow> (P(x)\<lbrakk>x\<rightarrow>v\<rbrakk>) is \<^bold>N"
  by (rel_auto, metis+)
  
lemma var_block_H1_H3_closed [closure]:
  "(\<And>x. P x is \<^bold>N) \<Longrightarrow> \<V>[\<L>\<^sub>D['a::countable], P] is \<^bold>N"
  by (simp add: utp_local_state.var_scope_def closure unrest)

lemma inj_local_rel [simp]: "inj_local R\<^sub>l = \<U>\<^sub>\<nat>"
  by (simp add: rel_local_state_def)
    
lemma sstate_rel [simp]: "\<^bold>s\<^bsub>R\<^sub>l\<^esub> = 1\<^sub>L"
  by (simp add: rel_local_state_def)

lemma inj_local_des [simp]: 
  "inj_local \<L>\<^sub>D['a::countable] = \<U>\<^sub>\<nat>"
  by (simp add: des_local_state_def)
  
lemma sstate_des [simp]: "\<^bold>s\<^bsub>\<L>\<^sub>D['a::countable]\<^esub> = \<Sigma>\<^sub>D"
  by (simp add: des_local_state_def)
      
lemma ndesign_msubst_top [usubst]:
  "(p x \<turnstile>\<^sub>n Q x)\<lbrakk>x\<rightarrow>\<lceil>top[\<L>\<^sub>D['a::countable]]\<rceil>\<^sub><\<rbrakk> = ((p x)\<lbrakk>x\<rightarrow>top[R\<^sub>l['a]]\<rbrakk> \<turnstile>\<^sub>n (Q x)\<lbrakk>x\<rightarrow>\<lceil>top[R\<^sub>l['a]]\<rceil>\<^sub><\<rbrakk>)"
  by (rel_auto')
          
text {* First attempt at a law for expanding design variable blocks. Far from adequate at the
  moment though. *}
    
lemma ndesign_local_expand_1 [ndes_simp]:
  "(var\<^sub>D x :: 'a :: countable \<bullet> p(x) \<turnstile>\<^sub>n Q(x)) =
       (\<Squnion> v \<bullet> (p x)\<lbrakk>x\<rightarrow>top[R\<^sub>l]\<rbrakk>\<lbrakk>&store ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>/store\<rbrakk>) \<turnstile>\<^sub>n
       (\<Sqinter> v \<bullet> store := &store ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle> ;; (Q x)\<lbrakk>x\<rightarrow>\<lceil>top[R\<^sub>l]\<rceil>\<^sub><\<rbrakk> ;; store := (front\<^sub>u(&store) \<triangleleft> 0 <\<^sub>u #\<^sub>u(&store) \<triangleright> &store))"
  apply (simp add: utp_local_state.var_scope_def utp_local_state.var_open_def utp_local_state.var_close_def seq_UINF_distr' usubst)
  apply (simp add: ndes_simp wp unrest)
  apply (rel_auto')
  done

end