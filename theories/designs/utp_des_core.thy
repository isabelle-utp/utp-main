section {* Design Signature and Core Laws *}

theory utp_des_core
imports UTP.utp
begin

text {* UTP designs~\cite{Cavalcanti04,Hoare&98} are a subset of the alphabetised relations that
  use a boolean observational variable $ok$ to record the start and termination of a program. For 
  more information on designs please see Chapter 3 of the UTP book~\cite{Hoare&98}, or
  the more accessible designs tutorial~\cite{Cavalcanti04}. *}

subsection {* Definitions *}

text {* Two named theorem sets exist are created to group theorems that, respectively, provide
  pre-postcondition definitions, and simplify operators to their normal design form. *}

named_theorems ndes and ndes_simp

alphabet des_vars =
  ok :: bool

declare des_vars.defs [lens_defs]
  
text {*
  The two locale interpretations below are a technicality to improve automatic
  proof support via the predicate and relational tactics. This is to enable the
  (re-)interpretation of state spaces to remove any occurrences of lens types
  after the proof tactics @{method pred_simp} and @{method rel_simp}, or any
  of their derivatives have been applied. Eventually, it would be desirable to
  automate both interpretations as part of a custom outer command for defining
  alphabets.
*}

interpretation des_vars: lens_interp "\<lambda>r. (ok\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation des_vars_rel:
  lens_interp "\<lambda>(r, r'). (ok\<^sub>v r, ok\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

lemma ok_ord [usubst]:
  "$ok \<prec>\<^sub>v $ok\<acute>"
  by (simp add: var_name_ord_def)

type_synonym '\<alpha> des  = "'\<alpha> des_vars_scheme"
type_synonym ('\<alpha>, '\<beta>) rel_des = "('\<alpha> des, '\<beta> des) urel"
type_synonym '\<alpha> hrel_des = "('\<alpha> des) hrel"

translations
  (type) "'\<alpha> des" <= (type) "'\<alpha> des_vars_scheme"
  (type) "'\<alpha> des" <= (type) "'\<alpha> des_vars_ext"
  (type) "('\<alpha>, '\<beta>) rel_des" <= (type) "('\<alpha> des, '\<beta> des) urel"
  (type) "'\<alpha> hrel_des" <= (type) "'\<alpha> des hrel"
  
notation des_vars_child_lens ("\<Sigma>\<^sub>D")

lemma ok_des_bij_lens: "bij_lens (ok +\<^sub>L \<Sigma>\<^sub>D)"
  by (unfold_locales, simp_all add: ok_def des_vars_child_lens_def lens_plus_def prod.case_eq_if)

text {* Define the lens functor for designs *}
  
definition lmap_des_vars :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha> des_vars_scheme \<Longrightarrow> '\<beta> des_vars_scheme)" ("lmap\<^sub>D")
where [lens_defs]: "lmap_des_vars = lmap[des_vars]"

lemma lmap_des_vars: "vwb_lens f \<Longrightarrow> vwb_lens (lmap_des_vars f)"
  by (unfold_locales, auto simp add: lens_defs)

lemma lmap_id: "lmap\<^sub>D 1\<^sub>L = 1\<^sub>L"
  by (simp add: lens_defs fun_eq_iff)

lemma lmap_comp: "lmap\<^sub>D (f ;\<^sub>L g) = lmap\<^sub>D f ;\<^sub>L lmap\<^sub>D g"
  by (simp add: lens_defs fun_eq_iff)

text {* The following notations define liftings from non-design predicates into design
  predicates using alphabet extensions. *}

abbreviation lift_desr ("\<lceil>_\<rceil>\<^sub>D")
where "\<lceil>P\<rceil>\<^sub>D \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D)"

abbreviation lift_pre_desr ("\<lceil>_\<rceil>\<^sub>D\<^sub><")
where "\<lceil>p\<rceil>\<^sub>D\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>D"

abbreviation lift_post_desr ("\<lceil>_\<rceil>\<^sub>D\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>D\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>D"

abbreviation drop_desr ("\<lfloor>_\<rfloor>\<^sub>D")
where "\<lfloor>P\<rfloor>\<^sub>D \<equiv> P \<restriction>\<^sub>e (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D)"

abbreviation dcond :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> '\<alpha> upred \<Rightarrow> ('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" 
  ("(3_ \<triangleleft> _ \<triangleright>\<^sub>D/ _)" [52,0,53] 52)
where "P \<triangleleft> b \<triangleright>\<^sub>D Q \<equiv> P \<triangleleft> \<lceil>b\<rceil>\<^sub>D\<^sub>< \<triangleright> Q"
  
definition design::"('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" (infixl "\<turnstile>" 60) where
[upred_defs]: "P \<turnstile> Q = ($ok \<and> P \<Rightarrow> $ok\<acute> \<and> Q)"

text {* An rdesign is a design that uses the Isabelle type system to prevent reference to ok in the
        assumption and commitment. *}

definition rdesign::"('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" (infixl "\<turnstile>\<^sub>r" 60) where 
[upred_defs]: "(P \<turnstile>\<^sub>r Q) = \<lceil>P\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<rceil>\<^sub>D"
  
text {* An ndesign is a normal design, i.e. where the assumption is a condition *}

definition ndesign::"'\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" (infixl "\<turnstile>\<^sub>n" 60) where 
[upred_defs]: "(p \<turnstile>\<^sub>n Q) = (\<lceil>p\<rceil>\<^sub>< \<turnstile>\<^sub>r Q)"

definition skip_d :: "'\<alpha> hrel_des" ("II\<^sub>D") where 
[upred_defs]: "II\<^sub>D \<equiv> (true \<turnstile>\<^sub>r II)"

definition bot_d :: "('\<alpha>, '\<beta>) rel_des" ("\<bottom>\<^sub>D") where
[upred_defs]: "\<bottom>\<^sub>D = (false \<turnstile> false)"

definition pre_design :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("pre\<^sub>D") where
[upred_defs]: "pre\<^sub>D(P) = \<lfloor>\<not> P\<lbrakk>true,false/$ok,$ok\<acute>\<rbrakk>\<rfloor>\<^sub>D"

definition post_design :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) urel" ("post\<^sub>D") where
[upred_defs]: "post\<^sub>D(P) = \<lfloor>P\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>\<rfloor>\<^sub>D"

syntax
  "_ok_f"  :: "logic \<Rightarrow> logic" ("_\<^sup>f" [1000] 1000)
  "_ok_t"  :: "logic \<Rightarrow> logic" ("_\<^sup>t" [1000] 1000)
  "_top_d" :: "logic" ("\<top>\<^sub>D")

translations
  "P\<^sup>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ovar CONST ok) false) P"
  "P\<^sup>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ovar CONST ok) true) P"
  "\<top>\<^sub>D" => "CONST not_upred (CONST utp_expr.var (CONST ivar CONST ok))"

subsection {* Lifting, Unrestriction, and Substitution *}

lemma drop_desr_inv [simp]: "\<lfloor>\<lceil>P\<rceil>\<^sub>D\<rfloor>\<^sub>D = P"
  by (simp add: prod_mwb_lens)

lemma lift_desr_inv:
  fixes P :: "('\<alpha>, '\<beta>) rel_des"
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P"
  shows "\<lceil>\<lfloor>P\<rfloor>\<^sub>D\<rceil>\<^sub>D = P"
proof -
  have "bij_lens (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D +\<^sub>L (in_var ok +\<^sub>L out_var ok) :: (_, '\<alpha> des_vars_scheme \<times> '\<beta> des_vars_scheme) lens)"
    (is "bij_lens (?P)")
  proof -
    have "?P \<approx>\<^sub>L (ok +\<^sub>L \<Sigma>\<^sub>D) \<times>\<^sub>L (ok +\<^sub>L \<Sigma>\<^sub>D)" (is "?P \<approx>\<^sub>L ?Q")
      apply (simp add: in_var_def out_var_def prod_as_plus)
      apply (simp add: prod_as_plus[THEN sym])
      apply (meson lens_equiv_sym lens_equiv_trans lens_indep_prod lens_plus_comm lens_plus_prod_exchange des_vars_indeps(1))
    done
    moreover have "bij_lens ?Q"
      by (simp add: ok_des_bij_lens prod_bij_lens)
    ultimately show ?thesis
      by (metis bij_lens_equiv lens_equiv_sym)
  qed

  with assms show ?thesis
    apply (rule_tac aext_arestr[of _ "in_var ok +\<^sub>L out_var ok"])
    apply (simp add: prod_mwb_lens)
    apply (simp)
    apply (metis alpha_in_var lens_indep_prod lens_indep_sym des_vars_indeps(1) out_var_def prod_as_plus)
    using unrest_var_comp apply blast
  done
qed

lemma unrest_out_des_lift [unrest]: "out\<alpha> \<sharp> p \<Longrightarrow> out\<alpha> \<sharp> \<lceil>p\<rceil>\<^sub>D"
  by (pred_simp)

lemma lift_dist_seq [simp]:
  "\<lceil>P ;; Q\<rceil>\<^sub>D = (\<lceil>P\<rceil>\<^sub>D ;; \<lceil>Q\<rceil>\<^sub>D)"
  by (rel_auto)

lemma lift_des_skip_dr_unit [simp]:
  "(\<lceil>P\<rceil>\<^sub>D ;; \<lceil>II\<rceil>\<^sub>D) = \<lceil>P\<rceil>\<^sub>D"
  "(\<lceil>II\<rceil>\<^sub>D ;; \<lceil>P\<rceil>\<^sub>D) = \<lceil>P\<rceil>\<^sub>D"
  by (rel_auto)+

lemma lift_des_skip_dr_unit_unrest: "$ok\<acute> \<sharp> P \<Longrightarrow> (P ;; \<lceil>II\<rceil>\<^sub>D) = P"
  by (rel_auto)

lemma state_subst_design [usubst]:
  "\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> (P \<turnstile>\<^sub>r Q) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P) \<turnstile>\<^sub>r (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> Q)"
  by (rel_auto)

lemma design_subst [usubst]:
  "\<lbrakk> $ok \<sharp> \<sigma>; $ok\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (P \<turnstile> Q) = (\<sigma> \<dagger> P) \<turnstile> (\<sigma> \<dagger> Q)"
  by (simp add: design_def usubst)

lemma design_msubst [usubst]:
  "(P(x) \<turnstile> Q(x))\<lbrakk>x\<rightarrow>v\<rbrakk> = (P(x)\<lbrakk>x\<rightarrow>v\<rbrakk> \<turnstile> Q(x)\<lbrakk>x\<rightarrow>v\<rbrakk>)"
  by (rel_auto)
    
lemma design_ok_false [usubst]: "(P \<turnstile> Q)\<lbrakk>false/$ok\<rbrakk> = true"
  by (simp add: design_def usubst)

lemma ok_pre: "($ok \<and> \<lceil>pre\<^sub>D(P)\<rceil>\<^sub>D) = ($ok \<and> (\<not> P\<^sup>f))"
  by (pred_auto robust)

lemma ok_post: "($ok \<and> \<lceil>post\<^sub>D(P)\<rceil>\<^sub>D) = ($ok \<and> (P\<^sup>t))"
  by (pred_auto robust)

subsection {* Basic Design Laws *}

lemma design_export_ok: "P \<turnstile> Q = (P \<turnstile> ($ok \<and> Q))"
  by (rel_auto)

lemma design_export_ok': "P \<turnstile> Q = (P \<turnstile> ($ok\<acute> \<and> Q))"
  by (rel_auto)

lemma design_export_pre: "P \<turnstile> (P \<and> Q) = P \<turnstile> Q"
  by (rel_auto)

lemma design_export_spec: "P \<turnstile> (P \<Rightarrow> Q) = P \<turnstile> Q"
  by (rel_auto)

lemma design_ok_pre_conj: "($ok \<and> P) \<turnstile> Q = P \<turnstile> Q"
  by (rel_auto)

lemma true_is_design: "(false \<turnstile> true) = true"
  by (rel_auto)

lemma true_is_rdesign: "(false \<turnstile>\<^sub>r true) = true"
  by (rel_auto)
    
lemma bot_d_true: "\<bottom>\<^sub>D = true"
  by (rel_auto)  
  
lemma bot_d_ndes_def [ndes_simp]: "\<bottom>\<^sub>D = (false \<turnstile>\<^sub>n true)"
  by (rel_auto)

lemma design_false_pre: "(false \<turnstile> P) = true"
  by (rel_auto)

lemma rdesign_false_pre: "(false \<turnstile>\<^sub>r P) = true"
  by (rel_auto)

lemma ndesign_false_pre: "(false \<turnstile>\<^sub>n P) = true"
  by (rel_auto)

lemma ndesign_miracle: "(true \<turnstile>\<^sub>n false) = \<top>\<^sub>D"
  by (rel_auto)

lemma top_d_ndes_def [ndes_simp]: "\<top>\<^sub>D = (true \<turnstile>\<^sub>n false)"
  by (rel_auto)

lemma skip_d_alt_def: "II\<^sub>D = true \<turnstile> II"
  by (rel_auto)

lemma skip_d_ndes_def [ndes_simp]: "II\<^sub>D = true \<turnstile>\<^sub>n II"
  by (rel_auto)

lemma design_subst_ok:
  "(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true/$ok\<rbrakk>) = (P \<turnstile> Q)"
  by (rel_auto)

lemma design_subst_ok_ok':
  "(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>) = (P \<turnstile> Q)"
proof -
  have "(P \<turnstile> Q) = (($ok \<and> P) \<turnstile> ($ok \<and> $ok\<acute> \<and> Q))"
    by (pred_auto)
  also have "... = (($ok \<and> P\<lbrakk>true/$ok\<rbrakk>) \<turnstile> ($ok \<and> ($ok\<acute> \<and> Q\<lbrakk>true/$ok\<acute>\<rbrakk>)\<lbrakk>true/$ok\<rbrakk>))"
    by (metis conj_eq_out_var_subst conj_pos_var_subst upred_eq_true utp_pred_laws.inf_commute ok_vwb_lens)
  also have "... = (($ok \<and> P\<lbrakk>true/$ok\<rbrakk>) \<turnstile> ($ok \<and> $ok\<acute> \<and> Q\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>))"
    by (simp add: usubst)
  also have "... = (P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>)"
    by (pred_auto)
  finally show ?thesis ..
qed

lemma design_subst_ok':
  "(P \<turnstile> Q\<lbrakk>true/$ok\<acute>\<rbrakk>) = (P \<turnstile> Q)"
proof -
  have "(P \<turnstile> Q) = (P \<turnstile> ($ok\<acute> \<and> Q))"
    by (pred_auto)
  also have "... = (P \<turnstile> ($ok\<acute> \<and> Q\<lbrakk>true/$ok\<acute>\<rbrakk>))"
    by (metis conj_eq_out_var_subst upred_eq_true utp_pred_laws.inf_commute ok_vwb_lens)
  also have "... = (P \<turnstile> Q\<lbrakk>true/$ok\<acute>\<rbrakk>)"
    by (pred_auto)
  finally show ?thesis ..
qed

subsection {* Sequential Composition Laws *}

theorem design_skip_idem [simp]:
  "(II\<^sub>D ;; II\<^sub>D) = II\<^sub>D"
  by (rel_auto)

theorem design_composition_subst:
  assumes
    "$ok\<acute> \<sharp> P1" "$ok \<sharp> P2"
  shows "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) =
         (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (\<not> P2))) \<turnstile> (Q1\<lbrakk>true/$ok\<acute>\<rbrakk> ;; Q2\<lbrakk>true/$ok\<rbrakk>))"
proof -
  have "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> ((P1 \<turnstile> Q1)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>))"
    by (rule seqr_middle, simp)
  also have " ...
        = (((P1 \<turnstile> Q1)\<lbrakk>false/$ok\<acute>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>false/$ok\<rbrakk>)
            \<or> ((P1 \<turnstile> Q1)\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (P2 \<turnstile> Q2)\<lbrakk>true/$ok\<rbrakk>))"
    by (simp add: true_alt_def false_alt_def, pred_auto)
  also from assms
  have "... = ((($ok \<and> P1 \<Rightarrow> Q1\<lbrakk>true/$ok\<acute>\<rbrakk>) ;; (P2 \<Rightarrow> $ok\<acute> \<and> Q2\<lbrakk>true/$ok\<rbrakk>)) \<or> ((\<not> ($ok \<and> P1)) ;; true))"
    by (simp add: design_def usubst unrest, pred_auto)
  also have "... = ((\<not>$ok ;; true\<^sub>h) \<or> ((\<not>P1) ;; true) \<or> (Q1\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (\<not>P2)) \<or> ($ok\<acute> \<and> (Q1\<lbrakk>true/$ok\<acute>\<rbrakk> ;; Q2\<lbrakk>true/$ok\<rbrakk>)))"
    by (rel_auto)
  also have "... = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (\<not> P2))) \<turnstile> (Q1\<lbrakk>true/$ok\<acute>\<rbrakk> ;; Q2\<lbrakk>true/$ok\<rbrakk>))"
    by (simp add: precond_right_unit design_def unrest, rel_auto)
  finally show ?thesis .
qed

theorem design_composition:
  assumes
    "$ok\<acute> \<sharp> P1" "$ok \<sharp> P2" "$ok\<acute> \<sharp> Q1" "$ok \<sharp> Q2"
  shows "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile> (Q1 ;; Q2))"
  using assms by (simp add: design_composition_subst usubst)

theorem design_composition_runrest:
  assumes
    "$ok\<acute> \<sharp> P1" "$ok \<sharp> P2" "ok \<sharp>\<sharp> Q1" "ok \<sharp>\<sharp> Q2"
  shows "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1\<^sup>t ;; (\<not> P2))) \<turnstile> (Q1 ;; Q2))"
proof -
  have "($ok \<and> $ok\<acute> \<and> (Q1\<^sup>t ;; Q2\<lbrakk>true/$ok\<rbrakk>)) = ($ok \<and> $ok\<acute> \<and> (Q1 ;; Q2))"
  proof -
    have "($ok \<and> $ok\<acute> \<and> (Q1 ;; Q2)) = (($ok \<and> Q1) ;; (Q2 \<and> $ok\<acute>))"
      by (metis (no_types, lifting) conj_comm seqr_post_var_out seqr_pre_var_out)
    also have "... = ((Q1 \<and> $ok\<acute>) ;; ($ok \<and> Q2))"
      by (simp add: assms(3) assms(4) runrest_ident_var)
    also have "... = (Q1\<^sup>t ;; Q2\<lbrakk>true/$ok\<rbrakk>)"
      by (metis ok_vwb_lens seqr_pre_transfer seqr_right_one_point true_alt_def uovar_convr upred_eq_true utp_pred_laws.inf.left_idem utp_rel.unrest_ouvar vwb_lens_mwb)
    finally show ?thesis
      by (metis utp_pred_laws.inf.left_commute utp_pred_laws.inf_left_idem)
  qed
  moreover have "(\<not> (\<not> P1 ;; true) \<and> \<not> (Q1\<^sup>t ;; (\<not> P2))) \<turnstile> (Q1\<^sup>t ;; Q2\<lbrakk>true/$ok\<rbrakk>) =
                 (\<not> (\<not> P1 ;; true) \<and> \<not> (Q1\<^sup>t ;; (\<not> P2))) \<turnstile> ($ok \<and> $ok\<acute> \<and> (Q1\<^sup>t ;; Q2\<lbrakk>true/$ok\<rbrakk>))"
    by (metis design_export_ok design_export_ok')
  ultimately show ?thesis using assms
    by (simp add: design_composition_subst usubst, metis design_export_ok design_export_ok')
qed

theorem rdesign_composition:
  "((P1 \<turnstile>\<^sub>r Q1) ;; (P2 \<turnstile>\<^sub>r Q2)) = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile>\<^sub>r (Q1 ;; Q2))"
  by (simp add: rdesign_def design_composition unrest alpha)

theorem design_composition_cond:
  assumes
    "out\<alpha> \<sharp> p1" "$ok \<sharp> P2" "$ok\<acute> \<sharp> Q1" "$ok \<sharp> Q2"
  shows "((p1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = ((p1 \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile> (Q1 ;; Q2))"
  using assms
  by (simp add: design_composition unrest precond_right_unit)

theorem rdesign_composition_cond:
  assumes "out\<alpha> \<sharp> p1"
  shows "((p1 \<turnstile>\<^sub>r Q1) ;; (P2 \<turnstile>\<^sub>r Q2)) = ((p1 \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile>\<^sub>r (Q1 ;; Q2))"
  using assms
  by (simp add: rdesign_def design_composition_cond unrest alpha)

theorem design_composition_wp:
  assumes
    "ok \<sharp> p1" "ok \<sharp> p2"
    "$ok \<sharp> Q1" "$ok\<acute> \<sharp> Q1" "$ok \<sharp> Q2" "$ok\<acute> \<sharp> Q2"
  shows "((\<lceil>p1\<rceil>\<^sub>< \<turnstile> Q1) ;; (\<lceil>p2\<rceil>\<^sub>< \<turnstile> Q2)) = ((\<lceil>p1 \<and> Q1 wp p2\<rceil>\<^sub><) \<turnstile> (Q1 ;; Q2))"
  using assms by (rel_blast)

theorem rdesign_composition_wp:
  "((\<lceil>p1\<rceil>\<^sub>< \<turnstile>\<^sub>r Q1) ;; (\<lceil>p2\<rceil>\<^sub>< \<turnstile>\<^sub>r Q2)) = ((\<lceil>p1 \<and> Q1 wp p2\<rceil>\<^sub><) \<turnstile>\<^sub>r (Q1 ;; Q2))"
  by (rel_blast)

theorem ndesign_composition_wp [ndes_simp]:
  "((p1 \<turnstile>\<^sub>n Q1) ;; (p2 \<turnstile>\<^sub>n Q2)) = ((p1 \<and> Q1 wp p2) \<turnstile>\<^sub>n (Q1 ;; Q2))"
  by (rel_blast)

theorem design_true_left_zero: "(true ;; (P \<turnstile> Q)) = true"
proof -
  have "(true ;; (P \<turnstile> Q)) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> true\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (P \<turnstile> Q)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>)"
    by (subst seqr_middle[of ok], simp_all)
  also have "... = ((true\<lbrakk>false/$ok\<acute>\<rbrakk> ;; (P \<turnstile> Q)\<lbrakk>false/$ok\<rbrakk>) \<or> (true\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (P \<turnstile> Q)\<lbrakk>true/$ok\<rbrakk>))"
    by (simp add: disj_comm false_alt_def true_alt_def)
  also have "... = ((true\<lbrakk>false/$ok\<acute>\<rbrakk> ;; true\<^sub>h) \<or> (true ;; ((P \<turnstile> Q)\<lbrakk>true/$ok\<rbrakk>)))"
    by (subst_tac, rel_auto)
  also have "... = true"
    by (subst_tac, simp add: precond_right_unit unrest)
  finally show ?thesis .
qed

theorem design_left_unit_hom:
  fixes P Q :: "'\<alpha> hrel_des"
  shows "(II\<^sub>D ;; (P \<turnstile>\<^sub>r Q)) = (P \<turnstile>\<^sub>r Q)"
proof -
  have "(II\<^sub>D ;; (P \<turnstile>\<^sub>r Q)) = ((true \<turnstile>\<^sub>r II) ;; (P \<turnstile>\<^sub>r Q))"
    by (simp add: skip_d_def)
  also have "... = (true \<and> \<not> (II ;; (\<not> P))) \<turnstile>\<^sub>r (II ;; Q)"
  proof -
    have "out\<alpha> \<sharp> true"
      by unrest_tac
    thus ?thesis
      using rdesign_composition_cond by blast
  qed
  also have "... = (\<not> (\<not> P)) \<turnstile>\<^sub>r Q"
    by simp
  finally show ?thesis by simp
qed

theorem rdesign_left_unit [simp]:
  "II\<^sub>D ;; (P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
  by (rel_auto)

theorem design_right_semi_unit:
  "(P \<turnstile>\<^sub>r Q) ;; II\<^sub>D = ((\<not> (\<not> P) ;; true) \<turnstile>\<^sub>r Q)"
  by (simp add: skip_d_def rdesign_composition)

theorem design_right_cond_unit [simp]:
  assumes "out\<alpha> \<sharp> p"
  shows "(p \<turnstile>\<^sub>r Q) ;; II\<^sub>D = (p \<turnstile>\<^sub>r Q)"
  using assms
  by (simp add: skip_d_def rdesign_composition_cond)

theorem ndesign_left_unit [simp]:
  "II\<^sub>D ;; (p \<turnstile>\<^sub>n Q) = (p \<turnstile>\<^sub>n Q)"
  by (rel_auto)

theorem design_bot_left_zero: "(\<bottom>\<^sub>D ;; (P \<turnstile> Q)) = \<bottom>\<^sub>D"
  by (rel_auto)

theorem design_top_left_zero: "(\<top>\<^sub>D ;; (P \<turnstile> Q)) = \<top>\<^sub>D"
  by (rel_auto)

subsection {* Preconditions and Postconditions *}

theorem design_npre:
  "(P \<turnstile> Q)\<^sup>f = (\<not> $ok \<or> \<not> P\<^sup>f)"
  by (rel_auto)

theorem design_pre:
  "\<not> (P \<turnstile> Q)\<^sup>f = ($ok \<and> P\<^sup>f)"
  by (simp add: design_def, subst_tac)
     (metis (no_types, hide_lams) not_conj_deMorgans true_not_false(2) utp_pred_laws.compl_top_eq
            utp_pred_laws.sup.idem utp_pred_laws.sup_compl_top)

theorem design_post:
  "(P \<turnstile> Q)\<^sup>t = (($ok \<and> P\<^sup>t) \<Rightarrow> Q\<^sup>t)"
  by (rel_auto)

theorem rdesign_pre [simp]: "pre\<^sub>D(P \<turnstile>\<^sub>r Q) = P"
  by (pred_auto)

theorem rdesign_post [simp]: "post\<^sub>D(P \<turnstile>\<^sub>r Q) = (P \<Rightarrow> Q)"
  by (pred_auto)

theorem ndesign_pre [simp]: "pre\<^sub>D(p \<turnstile>\<^sub>n Q) = \<lceil>p\<rceil>\<^sub><"
  by (pred_auto)

theorem ndesign_post [simp]: "post\<^sub>D(p \<turnstile>\<^sub>n Q) = (\<lceil>p\<rceil>\<^sub>< \<Rightarrow> Q)"
  by (pred_auto)

lemma design_pre_choice [simp]:
  "pre\<^sub>D(P \<sqinter> Q) = (pre\<^sub>D(P) \<and> pre\<^sub>D(Q))"
  by (rel_auto)

lemma design_post_choice [simp]:
  "post\<^sub>D(P \<sqinter> Q) = (post\<^sub>D(P) \<or> post\<^sub>D(Q))"
  by (rel_auto)

lemma design_pre_condr [simp]:
  "pre\<^sub>D(P \<triangleleft> \<lceil>b\<rceil>\<^sub>D \<triangleright> Q) = (pre\<^sub>D(P) \<triangleleft> b \<triangleright> pre\<^sub>D(Q))"
  by (rel_auto)

lemma design_post_condr [simp]:
  "post\<^sub>D(P \<triangleleft> \<lceil>b\<rceil>\<^sub>D \<triangleright> Q) = (post\<^sub>D(P) \<triangleleft> b \<triangleright> post\<^sub>D(Q))"
  by (rel_auto)

lemma preD_USUP_mem: "pre\<^sub>D (\<Squnion> i\<in>A \<bullet> P i) = (\<Sqinter> i\<in>A \<bullet> pre\<^sub>D(P i))"
  by (rel_auto)
  
lemma preD_USUP_ind: "pre\<^sub>D (\<Squnion> i \<bullet> P i) = (\<Sqinter> i \<bullet> pre\<^sub>D(P i))"
  by (rel_auto)

subsection {* Distribution Laws *}

theorem design_choice:
  "(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqinter> (Q\<^sub>1 \<turnstile> Q\<^sub>2) = ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<or> Q\<^sub>2))"
  by (rel_auto)

theorem rdesign_choice:
  "(P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) \<sqinter> (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) = ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile>\<^sub>r (P\<^sub>2 \<or> Q\<^sub>2))"
  by (rel_auto)

theorem ndesign_choice [ndes_simp]:
  "(p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<sqinter> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2) = ((p\<^sub>1 \<and> q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<or> Q\<^sub>2))"
  by (rel_auto)

theorem ndesign_choice' [ndes_simp]:
  "((p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<or> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2)) = ((p\<^sub>1 \<and> q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<or> Q\<^sub>2))"
  by (rel_auto)

theorem design_inf:
  "(P\<^sub>1 \<turnstile> P\<^sub>2) \<squnion> (Q\<^sub>1 \<turnstile> Q\<^sub>2) = ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)))"
  by (rel_auto)

theorem rdesign_inf:
  "(P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) \<squnion> (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) = ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile>\<^sub>r ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)))"
  by (rel_auto)

theorem ndesign_inf [ndes_simp]:
  "(p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<squnion> (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2) = ((p\<^sub>1 \<or> q\<^sub>1) \<turnstile>\<^sub>n ((\<lceil>p\<^sub>1\<rceil>\<^sub>< \<Rightarrow> P\<^sub>2) \<and> (\<lceil>q\<^sub>1\<rceil>\<^sub>< \<Rightarrow> Q\<^sub>2)))"
  by (rel_auto)
    
theorem design_condr:
  "((P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> b \<triangleright> (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = ((P\<^sub>1 \<triangleleft> b \<triangleright> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<triangleleft> b \<triangleright> Q\<^sub>2))"
  by (rel_auto)

theorem ndesign_dcond [ndes_simp]:
  "((p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2) \<triangleleft> b \<triangleright>\<^sub>D (q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2)) = ((p\<^sub>1 \<triangleleft> b \<triangleright> q\<^sub>1) \<turnstile>\<^sub>n (P\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>r Q\<^sub>2))"
  by (rel_auto)

lemma design_UINF_mem:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A \<bullet> P(i) \<turnstile> Q(i)) = (\<Squnion> i \<in> A \<bullet> P(i)) \<turnstile> (\<Sqinter> i \<in> A \<bullet> Q(i))"
  using assms by (rel_auto)

lemma ndesign_UINF_mem [ndes_simp]:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A \<bullet> p(i) \<turnstile>\<^sub>n Q(i)) = (\<Squnion> i \<in> A \<bullet> p(i)) \<turnstile>\<^sub>n (\<Sqinter> i \<in> A \<bullet> Q(i))"
  using assms by (rel_auto)

lemma ndesign_UINF_ind [ndes_simp]:
  "(\<Sqinter> i \<bullet> p(i) \<turnstile>\<^sub>n Q(i)) = (\<Squnion> i \<bullet> p(i)) \<turnstile>\<^sub>n (\<Sqinter> i \<bullet> Q(i))"
  by (rel_auto)
    
lemma design_USUP_mem:
  "(\<Squnion> i \<in> A \<bullet> P(i) \<turnstile> Q(i)) = (\<Sqinter> i \<in> A \<bullet> P(i)) \<turnstile> (\<Squnion> i \<in> A \<bullet> P(i) \<Rightarrow> Q(i))"
  by (rel_auto)

lemma ndesign_USUP_mem [ndes_simp]:
  "(\<Squnion> i \<in> A \<bullet> p(i) \<turnstile>\<^sub>n Q(i)) = (\<Sqinter> i \<in> A \<bullet> p(i)) \<turnstile>\<^sub>n (\<Squnion> i \<in> A \<bullet> \<lceil>p(i)\<rceil>\<^sub>< \<Rightarrow> Q(i))"
  by (rel_auto)

lemma ndesign_USUP_ind [ndes_simp]:
  "(\<Squnion> i \<bullet> p(i) \<turnstile>\<^sub>n Q(i)) = (\<Sqinter> i \<bullet> p(i)) \<turnstile>\<^sub>n (\<Squnion> i \<bullet> \<lceil>p(i)\<rceil>\<^sub>< \<Rightarrow> Q(i))"
  by (rel_auto)

subsection {* Refinement Introduction *}

lemma ndesign_eq_intro:
  assumes "p\<^sub>1 = q\<^sub>1" "P\<^sub>2 = Q\<^sub>2"
  shows "p\<^sub>1 \<turnstile>\<^sub>n P\<^sub>2 = q\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>2"
  by (simp add: assms)

theorem design_refinement:
  assumes
    "$ok \<sharp> P1" "$ok\<acute> \<sharp> P1" "$ok \<sharp> P2" "$ok\<acute> \<sharp> P2"
    "$ok \<sharp> Q1" "$ok\<acute> \<sharp> Q1" "$ok \<sharp> Q2" "$ok\<acute> \<sharp> Q2"
  shows "(P1 \<turnstile> Q1 \<sqsubseteq> P2 \<turnstile> Q2) \<longleftrightarrow> (`P1 \<Rightarrow> P2` \<and> `P1 \<and> Q2 \<Rightarrow> Q1`)"
proof -
  have "(P1 \<turnstile> Q1) \<sqsubseteq> (P2 \<turnstile> Q2) \<longleftrightarrow> `($ok \<and> P2 \<Rightarrow> $ok\<acute> \<and> Q2) \<Rightarrow> ($ok \<and> P1 \<Rightarrow> $ok\<acute> \<and> Q1)`"
    by (pred_auto)
  also with assms have "... = `(P2 \<Rightarrow> $ok\<acute> \<and> Q2) \<Rightarrow> (P1 \<Rightarrow> $ok\<acute> \<and> Q1)`"
    by (subst subst_bool_split[of "in_var ok"], simp_all, subst_tac)
  also with assms have "... = `(\<not> P2 \<Rightarrow> \<not> P1) \<and> ((P2 \<Rightarrow> Q2) \<Rightarrow> P1 \<Rightarrow> Q1)`"
    by (subst subst_bool_split[of "out_var ok"], simp_all, subst_tac)
  also have "... \<longleftrightarrow> `(P1 \<Rightarrow> P2)` \<and> `P1 \<and> Q2 \<Rightarrow> Q1`"
    by (pred_auto)
  finally show ?thesis .
qed

theorem rdesign_refinement:
  "(P1 \<turnstile>\<^sub>r Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>r Q2) \<longleftrightarrow> (`P1 \<Rightarrow> P2` \<and> `P1 \<and> Q2 \<Rightarrow> Q1`)"
  by (rel_auto)

lemma design_refine_intro:
  assumes "`P1 \<Rightarrow> P2`" "`P1 \<and> Q2 \<Rightarrow> Q1`"
  shows "P1 \<turnstile> Q1 \<sqsubseteq> P2 \<turnstile> Q2"
  using assms unfolding upred_defs
  by (pred_auto)

lemma design_refine_intro':
  assumes "P\<^sub>2 \<sqsubseteq> P\<^sub>1" "Q\<^sub>1 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2)"
  shows "P\<^sub>1 \<turnstile> Q\<^sub>1 \<sqsubseteq> P\<^sub>2 \<turnstile> Q\<^sub>2"
  using assms design_refine_intro[of P\<^sub>1 P\<^sub>2 Q\<^sub>2 Q\<^sub>1] by (simp add: refBy_order)

lemma rdesign_refine_intro:
  assumes "`P1 \<Rightarrow> P2`" "`P1 \<and> Q2 \<Rightarrow> Q1`"
  shows "P1 \<turnstile>\<^sub>r Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>r Q2"
  using assms unfolding upred_defs
  by (pred_auto)

lemma rdesign_refine_intro':
  assumes "P2 \<sqsubseteq> P1" "Q1 \<sqsubseteq> (P1 \<and> Q2)"
  shows "P1 \<turnstile>\<^sub>r Q1 \<sqsubseteq> P2 \<turnstile>\<^sub>r Q2"
  using assms unfolding upred_defs
  by (pred_auto)

lemma ndesign_refinement: 
  "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2 \<longleftrightarrow> (`p1 \<Rightarrow> p2` \<and> `\<lceil>p1\<rceil>\<^sub>< \<and> Q2 \<Rightarrow> Q1`)"
  by (simp add: ndesign_def rdesign_def design_refinement unrest, rel_auto)

lemma ndesign_refine_intro:
  assumes "`p1 \<Rightarrow> p2`" "`\<lceil>p1\<rceil>\<^sub>< \<and> Q2 \<Rightarrow> Q1`"
  shows "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2"
  using assms unfolding upred_defs
  by (pred_auto)

lemma design_top:
  "(P \<turnstile> Q) \<sqsubseteq> \<top>\<^sub>D"
  by (rel_auto)

lemma design_bottom:
  "\<bottom>\<^sub>D \<sqsubseteq> (P \<turnstile> Q)"
  by (rel_auto)

lemma design_refine_thms:
  assumes "P \<sqsubseteq> Q"
  shows "`pre\<^sub>D(P) \<Rightarrow> pre\<^sub>D(Q)`" "`pre\<^sub>D(P) \<and> post\<^sub>D(Q) \<Rightarrow> post\<^sub>D(P)`"
  apply (metis assms design_pre_choice disj_comm disj_upred_def order_refl rdesign_refinement utp_pred_laws.le_iff_sup)
  apply (metis assms conj_comm design_post_choice disj_upred_def refBy_order semilattice_sup_class.le_iff_sup utp_pred_laws.inf.coboundedI1)
done

end