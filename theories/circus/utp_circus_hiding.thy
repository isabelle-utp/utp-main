section \<open> Hiding \<close>

theory utp_circus_hiding
imports utp_circus_parallel
begin

subsection \<open> Hiding in peri- and postconditions \<close>

definition hide_rea ("hide\<^sub>r") where
[upred_defs]: "hide\<^sub>r P E = (\<^bold>\<exists> s \<bullet> (P\<lbrakk>$tr^\<^sub>u\<guillemotleft>s\<guillemotright>,(\<guillemotleft>E\<guillemotright>\<union>\<^sub>u$ref\<acute>)/$tr\<acute>,$ref\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr^\<^sub>u(\<guillemotleft>s\<guillemotright>\<restriction>\<^sub>u\<guillemotleft>-E\<guillemotright>)))"

lemma hide_rea_CRR_closed [closure]: 
  assumes "P is CRR"
  shows "hide\<^sub>r P E is CRR"
proof -
  have "CRR(hide\<^sub>r (CRR P) E) = hide\<^sub>r (CRR P) E"
    by (rel_auto, fastforce+)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

lemma hide_rea_CDC [closure]:
  assumes "P is CDC"
  shows "hide\<^sub>r P E is CDC"
proof -
  have "CDC(hide\<^sub>r (CDC P) E) = hide\<^sub>r (CDC P) E"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if Healthy_intro assms)
qed

lemma hide_rea_false [rpred]: "hide\<^sub>r false E = false"
  by (rel_auto)

lemma hide_rea_disj [rpred]: "hide\<^sub>r (P \<or> Q) E = (hide\<^sub>r P E \<or> hide\<^sub>r Q E)"
  by (rel_auto)

lemma hide_rea_csp_enable [rpred]: 
  "hide\<^sub>r \<E>(s, t, E) F = \<E>(s \<and> E - \<guillemotleft>F\<guillemotright> =\<^sub>u E, t \<restriction>\<^sub>u \<guillemotleft>-F\<guillemotright>, E)"
  by (rel_auto)

lemma hide_rea_csp_do [rpred]: "hide\<^sub>r \<Phi>(s,\<sigma>,t) E = \<Phi>(s,\<sigma>,t \<restriction>\<^sub>u \<guillemotleft>-E\<guillemotright>)"
  by (rel_auto)

lemma filter_eval [simp]: 
  "(bop Cons x xs) \<restriction>\<^sub>u E = (bop Cons x (xs \<restriction>\<^sub>u E) \<triangleleft> x \<in>\<^sub>u E \<triangleright> xs\<restriction>\<^sub>uE)"
  by (rel_simp)

lemma hide_rea_seq [rpred]:
  assumes "P is CRR" "$ref\<acute> \<sharp> P" "Q is CRR" 
  shows "hide\<^sub>r (P ;; Q) E = hide\<^sub>r P E ;; hide\<^sub>r Q E"
proof -
  have"hide\<^sub>r (CRR(\<exists> $ref\<acute> \<bullet> P) ;; CRR(Q)) E = hide\<^sub>r (CRR(\<exists> $ref\<acute> \<bullet> P)) E ;; hide\<^sub>r (CRR Q) E"
    apply (simp add: hide_rea_def usubst unrest CRR_seqr_form)
    apply (simp add: CRR_form)
    apply (rel_auto)
    using seq_filter_append apply fastforce
    apply (metis seq_filter_append)
    done
  thus ?thesis
    by (simp add: Healthy_if assms ex_unrest)
qed

lemma hide_rea_true_R1_true [rpred]: 
  "hide\<^sub>r (R1 true) A ;; R1 true = R1 true"
  by (rel_auto, metis append_Nil2 seq_filter_Nil)

lemma hide_rea_empty [rpred]: 
  assumes "P is RR"
  shows "hide\<^sub>r P {} = P"
proof -
  have "hide\<^sub>r (RR P) {} = (RR P)"
    by (rel_auto; force)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma hide_rea_twice [rpred]: "hide\<^sub>r (hide\<^sub>r P A) B = hide\<^sub>r P (A \<union> B)"
  apply (rel_auto)
  apply (metis (no_types, hide_lams) semilattice_sup_class.sup_assoc)
  apply (metis (no_types, lifting) semilattice_sup_class.sup_assoc seq_filter_twice)
  done

lemma st'_unrest_hide_rea [unrest]: "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> hide\<^sub>r P E"
  by (simp add: hide_rea_def unrest)

lemma ref'_unrest_hide_rea [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> hide\<^sub>r P E"
  by (simp add: hide_rea_def unrest usubst)

subsection \<open> Hiding in preconditions \<close>

definition abs_rea :: "('s, 'e) action \<Rightarrow> 'e set \<Rightarrow> ('s, 'e) action" ("abs\<^sub>r") where
[upred_defs]: "abs\<^sub>r P E = (\<not>\<^sub>r (hide\<^sub>r (\<not>\<^sub>r P) E ;; true\<^sub>r))"

lemma abs_rea_false [rpred]: "abs\<^sub>r false E = false"
  by (rel_simp, metis append.right_neutral seq_filter_Nil)

lemma abs_rea_conj [rpred]: "abs\<^sub>r (P \<and> Q) E = (abs\<^sub>r P E \<and> abs\<^sub>r Q E)"
  by (rel_blast)

lemma abs_rea_true [rpred]: "abs\<^sub>r true\<^sub>r E = true\<^sub>r"
  by (rel_auto)

lemma abs_rea_RC_closed [closure]:
  assumes "P is CRR"
  shows "abs\<^sub>r P E is CRC"
proof -
  have "RC1 (abs\<^sub>r (CRR P) E) = abs\<^sub>r (CRR P) E"
    apply (rel_auto)
    apply (metis order_refl)
    apply blast
    done
  hence "abs\<^sub>r P E is RC1"
    by (simp add: assms Healthy_if Healthy_intro closure)
  thus ?thesis
    by (rule_tac CRC_intro'', simp_all add: abs_rea_def closure assms unrest)
qed

lemma hide_rea_impl_under_abs:
  assumes "P is CRC" "Q is CRR"
  shows "(abs\<^sub>r P A \<Rightarrow>\<^sub>r hide\<^sub>r (P \<Rightarrow>\<^sub>r Q) A) = (abs\<^sub>r P A \<Rightarrow>\<^sub>r hide\<^sub>r Q A)"
  by (simp add: RC1_def abs_rea_def rea_impl_def rpred closure assms unrest)
     (rel_auto, metis order_refl )

lemma abs_rea_not_CRR: "P is CRR \<Longrightarrow> abs\<^sub>r (\<not>\<^sub>r P) E = (\<not>\<^sub>r hide\<^sub>r P E ;; R1 true)"
  by (simp add: abs_rea_def rpred closure)

lemma abs_rea_wpR [rpred]: 
  assumes "P is CRR" "$ref\<acute> \<sharp> P" "Q is CRC"
  shows "abs\<^sub>r (P wp\<^sub>r Q) A = (hide\<^sub>r P A) wp\<^sub>r (abs\<^sub>r Q A)"
  by (simp add: wp_rea_def abs_rea_not_CRR hide_rea_seq assms closure)
     (simp add: abs_rea_def rpred closure assms seqr_assoc)

lemma abs_rea_empty [rpred]: 
  assumes "P is RC"
  shows "abs\<^sub>r P {} = P"
proof -
  have "abs\<^sub>r (RC P) {} = (RC P)"
    apply (rel_auto)
    apply (metis diff_add_cancel_left' order_refl plus_list_def)
    using dual_order.trans apply blast
    done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed


lemma abs_rea_twice [rpred]: 
  assumes "P is CRC"
  shows "abs\<^sub>r (abs\<^sub>r P A) B = abs\<^sub>r P (A \<union> B)" (is "?lhs = ?rhs")
proof -
  have "?lhs = abs\<^sub>r (\<not>\<^sub>r hide\<^sub>r (\<not>\<^sub>r P) A ;; R1 true) B"
    by (simp add: abs_rea_def)
  thus ?thesis
    by (simp add: abs_rea_def rpred closure unrest seqr_assoc assms)
qed

subsection \<open> Hiding Operator \<close>

text \<open> In common with the UTP book definition of hiding, this definition does not introduce
  divergence if there is an infinite sequence of events that are hidden. For this, we would
  need a more complex precondition which is left for future work. \<close>

definition HideCSP  :: "('s, 'e) action \<Rightarrow> 'e set \<Rightarrow> ('s, 'e) action" (infixl "\\\<^sub>C" 80) where 
  [upred_defs]: 
  "HideCSP P E = \<^bold>R\<^sub>s(abs\<^sub>r(pre\<^sub>R(P)) E \<turnstile> hide\<^sub>r (peri\<^sub>R(P)) E \<diamondop> hide\<^sub>r (post\<^sub>R(P)) E)"

lemma HideCSP_rdes_def [rdes_def]:
  assumes "P is CRC" "Q is CRR" "R is CRR"
  shows "\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R) \\\<^sub>C A = \<^bold>R\<^sub>s(abs\<^sub>r(P) A \<turnstile> hide\<^sub>r Q A \<diamondop> hide\<^sub>r R A)" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^bold>R\<^sub>s (abs\<^sub>r P A \<turnstile> hide\<^sub>r (P \<Rightarrow>\<^sub>r Q) A \<diamondop> hide\<^sub>r (P \<Rightarrow>\<^sub>r R) A)"
    by (simp add: HideCSP_def rdes assms closure)
  also have "... = \<^bold>R\<^sub>s (abs\<^sub>r P A \<turnstile> (abs\<^sub>r P A \<Rightarrow>\<^sub>r hide\<^sub>r (P \<Rightarrow>\<^sub>r Q) A) \<diamondop> (abs\<^sub>r P A \<Rightarrow>\<^sub>r hide\<^sub>r (P \<Rightarrow>\<^sub>r R) A))"
    by (metis RHS_tri_design_conj conj_idem utp_pred_laws.sup.idem)
  also have "... = ?rhs"
    by (metis RHS_tri_design_conj assms conj_idem hide_rea_impl_under_abs utp_pred_laws.sup.idem)
  finally show ?thesis .
qed

lemma HideCSP_NCSP_closed [closure]: "P is NCSP \<Longrightarrow> P \\\<^sub>C E is NCSP"
  by (simp add: HideCSP_def closure unrest)

lemma HideCSP_C2_closed [closure]: 
  assumes "P is NCSP" "P is C2"
  shows "P \\\<^sub>C E is C2"
  by (rdes_simp cls: assms, simp add: C2_rdes_intro closure unrest assms)

lemma HideCSP_CACT_closed [closure]:
  assumes "P is CACT"
  shows "P \\\<^sub>C E is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lemma HideCSP_Chaos: "Chaos \\\<^sub>C E = Chaos"
  by (rdes_simp)

lemma HideCSP_Miracle: "Miracle \\\<^sub>C A = Miracle"
  by (rdes_eq)

lemma HideCSP_AssignsCSP:
  "\<langle>\<sigma>\<rangle>\<^sub>C \\\<^sub>C A = \<langle>\<sigma>\<rangle>\<^sub>C"
  by (rdes_eq)

lemma HideCSP_cond:
  assumes "P is NCSP" "Q is NCSP"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>R Q) \\\<^sub>C A = (P \\\<^sub>C A \<triangleleft> b \<triangleright>\<^sub>R Q \\\<^sub>C A) "
  by (rdes_eq cls: assms)

lemma HideCSP_int_choice:
  assumes "P is NCSP" "Q is NCSP"
  shows "(P \<sqinter> Q) \\\<^sub>C A = (P \\\<^sub>C A \<sqinter> Q \\\<^sub>C A) "
  by (rdes_eq cls: assms)

lemma HideCSP_guard:
  assumes "P is NCSP"
  shows "(b &\<^sub>u P) \\\<^sub>C A = b &\<^sub>u (P \\\<^sub>C A)"
  by (rdes_eq cls: assms)

lemma HideCSP_seq:
  assumes "P is NCSP" "Q is NCSP"
  shows "(P ;; Q) \\\<^sub>C A = (P \\\<^sub>C A ;; Q \\\<^sub>C A)"
  by (rdes_eq_split cls: assms)

lemma HideCSP_DoCSP [rdes_def]: 
  "do\<^sub>C(a) \\\<^sub>C A = (Skip \<triangleleft> (a \<in>\<^sub>u \<guillemotleft>A\<guillemotright>) \<triangleright>\<^sub>R do\<^sub>C(a))"
  by (rdes_eq)

lemma HideCSP_PrefixCSP:
  assumes "P is NCSP"
  shows "(a \<rightarrow>\<^sub>C P) \\\<^sub>C A = ((P \\\<^sub>C A) \<triangleleft> (a \<in>\<^sub>u \<guillemotleft>A\<guillemotright>) \<triangleright>\<^sub>R (a \<rightarrow>\<^sub>C (P \\\<^sub>C A)))"
  apply (simp add: PrefixCSP_def Healthy_if HideCSP_seq HideCSP_DoCSP closure assms rdes rpred)
  apply (simp add: HideCSP_NCSP_closed Skip_left_unit assms cond_st_distr)
  done

lemma HideCSP_empty:
  assumes "P is NCSP" 
  shows "P \\\<^sub>C {} = P"
  by (rdes_eq cls: assms)

lemma HideCSP_twice:
  assumes "P is NCSP" 
  shows "P \\\<^sub>C A \\\<^sub>C B = P \\\<^sub>C (A \<union> B)"
  by (rdes_simp cls: assms)

lemma HideCSP_Skip: "Skip \\\<^sub>C A = Skip"
  by (rdes_eq)

lemma HideCSP_Stop: "Stop \\\<^sub>C A = Stop"
  by (rdes_eq)

end