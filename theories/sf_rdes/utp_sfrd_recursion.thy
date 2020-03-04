section \<open> Recursion in Stateful-Failures \<close>

theory utp_sfrd_recursion
  imports utp_sfrd_contracts utp_sfrd_prog
begin

subsection \<open> Fixed-points \<close>

text \<open> The CSP weakest fixed-point is obtained simply by precomposing the body with the CSP
  healthiness condition. \<close>

abbreviation mu_CSP :: "(('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action) \<Rightarrow> ('\<sigma>, '\<phi>) action" ("\<mu>\<^sub>C") where
"\<mu>\<^sub>C F \<equiv> \<mu> (F \<circ> CSP)"

syntax
  "_mu_CSP" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>C _ \<bullet> _" [0, 10] 10)

translations
  "\<mu>\<^sub>C X \<bullet> P" == "CONST mu_CSP (\<lambda> X. P)"

lemma mu_CSP_equiv:
  assumes "Monotonic F" "F \<in> \<lbrakk>CSP\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>CSP\<rbrakk>\<^sub>H"
  shows "(\<mu>\<^sub>R F) = (\<mu>\<^sub>C F)"
  by (simp add: srd_mu_equiv assms comp_def)
    
lemma mu_CSP_unfold:
  "P is CSP \<Longrightarrow> (\<mu>\<^sub>C X \<bullet> P ;; X) = P ;; (\<mu>\<^sub>C X \<bullet> P ;; X)"
  apply (subst gfp_unfold)
  apply (simp_all add: closure Healthy_if)
  done

lemma mu_csp_expand [rdes]: "(\<mu>\<^sub>C ((;;) Q)) = (\<mu> X \<bullet> Q ;; CSP X)"
  by (simp add: comp_def)
    
lemma mu_csp_basic_refine:
  assumes 
    "P is CSP" "Q is NCSP" "Q is Productive" "pre\<^sub>R(P) = true\<^sub>r" "pre\<^sub>R(Q) = true\<^sub>r"
    "peri\<^sub>R P \<sqsubseteq> peri\<^sub>R Q"
    "peri\<^sub>R P \<sqsubseteq> post\<^sub>R Q ;; peri\<^sub>R P"
  shows "P \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> Q ;; X)"
proof (rule SRD_refine_intro', simp_all add: closure usubst alpha rpred rdes unrest wp seq_UINF_distr assms)
  show "peri\<^sub>R P \<sqsubseteq> (\<Sqinter> i \<bullet> post\<^sub>R Q \<^bold>^ i ;; peri\<^sub>R Q)"
  proof (rule UINF_refines')
    fix i
    show "peri\<^sub>R P \<sqsubseteq> post\<^sub>R Q \<^bold>^ i ;; peri\<^sub>R Q"
    proof (induct i)
      case 0
      then show ?case by (simp add: assms)
    next
      case (Suc i)
      then show ?case
        by (meson assms(6) assms(7) semilattice_sup_class.le_sup_iff upower_inductl)
    qed
  qed
qed
  
lemma CRD_mu_basic_refine:
  fixes P :: "'e list \<Rightarrow> 'e set \<Rightarrow> 's upred"
  assumes
    "Q is NCSP" "Q is Productive" "pre\<^sub>R(Q) = true\<^sub>r"
    "[P t r]\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(&tt, $ref\<acute>)\<^sub>u\<rbrakk> \<sqsubseteq> peri\<^sub>R Q"
    "[P t r]\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(&tt, $ref\<acute>)\<^sub>u\<rbrakk> \<sqsubseteq> post\<^sub>R Q ;;\<^sub>h [P t r]\<^sub>S\<^sub><\<lbrakk>(t, r)\<rightarrow>(&tt, $ref\<acute>)\<^sub>u\<rbrakk>"
  shows "[true \<turnstile> P trace refs | R]\<^sub>C \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> Q ;; X)"
proof (rule mu_csp_basic_refine, simp_all add: msubst_pair assms closure alpha rdes rpred Healthy_if R1_false)
  show "[P trace refs]\<^sub>S\<^sub><\<lbrakk>trace\<rightarrow>&tt\<rbrakk>\<lbrakk>refs\<rightarrow>$ref\<acute>\<rbrakk> \<sqsubseteq> peri\<^sub>R Q"
    using assms by (simp add: msubst_pair)
  show "[P trace refs]\<^sub>S\<^sub><\<lbrakk>trace\<rightarrow>&tt\<rbrakk>\<lbrakk>refs\<rightarrow>$ref\<acute>\<rbrakk> \<sqsubseteq> post\<^sub>R Q ;; [P trace refs]\<^sub>S\<^sub><\<lbrakk>trace\<rightarrow>&tt\<rbrakk>\<lbrakk>refs\<rightarrow>$ref\<acute>\<rbrakk>"
    using assms by (simp add: msubst_pair)
qed

subsection \<open> Example action expansion \<close>

lemma mu_example1: "(\<mu> X \<bullet> \<guillemotleft>a\<guillemotright> \<rightarrow>\<^sub>C X) = (\<Sqinter>i \<bullet> do\<^sub>C(\<guillemotleft>a\<guillemotright>) \<^bold>^ (i+1)) ;; Miracle"
  by (simp add: PrefixCSP_def mu_csp_form_1 closure)
    
lemma preR_mu_example1 [rdes]: "pre\<^sub>R(\<mu> X \<bullet> \<guillemotleft>a\<guillemotright> \<rightarrow>\<^sub>C X) = true\<^sub>r"
  by (simp add: mu_example1 rdes closure unrest wp)

lemma periR_mu_example1 [rdes]:
  "peri\<^sub>R(\<mu> X \<bullet> \<guillemotleft>a\<guillemotright> \<rightarrow>\<^sub>C X) = (\<Sqinter> i \<bullet> \<E>(true,iter[i](U([\<guillemotleft>a\<guillemotright>])), {\<guillemotleft>a\<guillemotright>}\<^sub>u))"
  by (simp add: mu_example1 rdes rpred closure unrest wp seq_UINF_distr alpha usubst)

lemma postR_mu_example1 [rdes]:
  "post\<^sub>R(\<mu> X \<bullet> \<guillemotleft>a\<guillemotright> \<rightarrow>\<^sub>C X) = false"
  by (simp add: mu_example1 rdes closure unrest wp)

end