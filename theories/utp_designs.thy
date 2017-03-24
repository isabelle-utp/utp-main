section {* Designs *}

theory utp_designs
imports
  "../utp/utp"
begin

text {* In UTP, in order to explicitly record the termination of a program,
a subset of alphabetized relations is introduced. These relations are called
designs and their alphabet should contain the special boolean observational variable ok.
It is used to record the start and termination of a program. *}

subsection {* Definitions *}

text {* In the following, the definitions of designs alphabets, designs and
healthiness (well-formedness) conditions are given. The healthiness conditions of
designs are defined by $H1$, $H2$, $H3$ and $H4$.*}

alphabet des_vars =
  ok :: bool

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
type_synonym ('\<alpha>, '\<beta>) rel_des = "('\<alpha> des, '\<beta> des) rel"
type_synonym '\<alpha> hrel_des = "('\<alpha> des) hrel"

translations
  (type) "'\<alpha> des" <= (type) "'\<alpha> des_vars_scheme"
  (type) "'\<alpha> des" <= (type) "'\<alpha> des_vars_ext"
  (type) "('\<alpha>, '\<beta>) rel_des" <= (type) "('\<alpha> des, '\<beta> des) rel"

notation des_vars_child_lens ("\<Sigma>\<^sub>D")

lemma ok_des_bij_lens: "bij_lens (ok +\<^sub>L \<Sigma>\<^sub>D)"
  by (unfold_locales, simp_all add: ok_def des_vars_child_lens_def lens_plus_def prod.case_eq_if)

text {* Define the lens functor for designs *}

definition lmap_des_vars :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha> des_vars_scheme \<Longrightarrow> '\<beta> des_vars_scheme)" ("lmap\<^sub>D")
  where "lmap_des_vars f = \<lparr> lens_get = \<lambda> v. extend (truncate v) (get\<^bsub>f\<^esub> (more v))
                           , lens_put = \<lambda> s v. extend (truncate v) (put\<^bsub>f\<^esub> (more s) (more v)) \<rparr>"

lemma lmap_des_vars: "vwb_lens f \<Longrightarrow> vwb_lens (lmap_des_vars f)"
  by (unfold_locales, simp_all add: lmap_des_vars_def extend_def truncate_def)

lemma lmap_id: "lmap\<^sub>D 1\<^sub>L = 1\<^sub>L"
  by (simp add: lmap_des_vars_def id_lens_def extend_def truncate_def fun_eq_iff)

lemma lmap_comp: "lmap\<^sub>D (f ;\<^sub>L g) = lmap\<^sub>D f ;\<^sub>L lmap\<^sub>D g"
  by (simp add: lmap_des_vars_def id_lens_def lens_comp_def extend_def truncate_def fun_eq_iff)

text {* The following notations define liftings from non-design predicates into design
  predicates using alphabet extensions. *}

abbreviation lift_desr ("\<lceil>_\<rceil>\<^sub>D")
where "\<lceil>P\<rceil>\<^sub>D \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D)"

abbreviation lift_pre_desr ("\<lceil>_\<rceil>\<^sub>D\<^sub><")
where "\<lceil>p\<rceil>\<^sub>D\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>D"

abbreviation lift_post_desr ("\<lceil>_\<rceil>\<^sub>D\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>D\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>D"

abbreviation drop_desr ("\<lfloor>_\<rfloor>\<^sub>D")
where "\<lfloor>P\<rfloor>\<^sub>D \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>D \<times>\<^sub>L \<Sigma>\<^sub>D)"

definition design::"('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" (infixl "\<turnstile>" 60)
where "P \<turnstile> Q = ($ok \<and> P \<Rightarrow> $ok\<acute> \<and> Q)"

text {* An rdesign is a design that uses the Isabelle type system to prevent reference to ok in the
        assumption and commitment. *}

definition rdesign::"('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" (infixl "\<turnstile>\<^sub>r" 60)
where "(P \<turnstile>\<^sub>r Q) = \<lceil>P\<rceil>\<^sub>D \<turnstile> \<lceil>Q\<rceil>\<^sub>D"

text {* An ndesign is a normal design, i.e. where the assumption is a condition *}

definition ndesign::"'\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) rel \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" (infixl "\<turnstile>\<^sub>n" 60)
where "(p \<turnstile>\<^sub>n Q) = (\<lceil>p\<rceil>\<^sub>< \<turnstile>\<^sub>r Q)"

definition skip_d :: "'\<alpha> hrel_des" ("II\<^sub>D")
where "II\<^sub>D \<equiv> (true \<turnstile>\<^sub>r II)"

definition assigns_d :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel_des" ("\<langle>_\<rangle>\<^sub>D")
where "assigns_d \<sigma> = (true \<turnstile>\<^sub>r assigns_r \<sigma>)"

syntax
  "_assignmentd" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>D" 55)

translations
  "_assignmentd xs vs" => "CONST assigns_d (_mk_usubst (CONST id) xs vs)"
  "x :=\<^sub>D v" <= "CONST assigns_d (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x :=\<^sub>D v" <= "CONST assigns_d (CONST subst_upd (CONST id) x v)"
  "x,y :=\<^sub>D u,v" <= "CONST assigns_d (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

definition J :: "'\<alpha> hrel_des"
where "J = (($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D)"

definition "H1 (P)  \<equiv>  $ok \<Rightarrow> P"

definition "H2 (P)  \<equiv>  P ;; J"

definition "H3 (P)  \<equiv>  P ;; II\<^sub>D"

definition "H4 (P)  \<equiv> ((P;;true) \<Rightarrow> P)"

syntax
  "_ok_f"  :: "logic \<Rightarrow> logic" ("_\<^sup>f" [1000] 1000)
  "_ok_t"  :: "logic \<Rightarrow> logic" ("_\<^sup>t" [1000] 1000)
  "_top_d" :: "logic" ("\<top>\<^sub>D")
  "_bot_d" :: "logic" ("\<bottom>\<^sub>D")

translations
  "P\<^sup>f" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ovar CONST ok) false) P"
  "P\<^sup>t" \<rightleftharpoons> "CONST usubst (CONST subst_upd CONST id (CONST ovar CONST ok) true) P"
  "\<top>\<^sub>D" => "CONST not_upred (CONST utp_expr.var (CONST ivar CONST ok))"
  "\<bottom>\<^sub>D" => "true"

definition pre_design :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel" ("pre\<^sub>D'(_')") where
"pre\<^sub>D(P) = \<lfloor>\<not> P\<lbrakk>true,false/$ok,$ok\<acute>\<rbrakk>\<rfloor>\<^sub>D"

definition post_design :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> ('\<alpha>, '\<beta>) rel" ("post\<^sub>D'(_')") where
"post\<^sub>D(P) = \<lfloor>P\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>\<rfloor>\<^sub>D"

definition wp_design :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> '\<beta> cond \<Rightarrow> '\<alpha> cond" (infix "wp\<^sub>D" 60) where
"Q wp\<^sub>D r = (\<lfloor>pre\<^sub>D(Q) ;; true :: ('\<alpha>, '\<beta>) rel\<rfloor>\<^sub>< \<and> (post\<^sub>D(Q) wp r))"

declare design_def [upred_defs]
declare rdesign_def [upred_defs]
declare ndesign_def [upred_defs]
declare skip_d_def [upred_defs]
declare J_def [upred_defs]
declare pre_design_def [upred_defs]
declare post_design_def [upred_defs]
declare wp_design_def [upred_defs]
declare assigns_d_def [upred_defs]

declare H1_def [upred_defs]
declare H2_def [upred_defs]
declare H3_def [upred_defs]
declare H4_def [upred_defs]

lemma drop_desr_inv [simp]: "\<lfloor>\<lceil>P\<rceil>\<^sub>D\<rfloor>\<^sub>D = P"
  by (simp add: arestr_aext prod_mwb_lens)

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

subsection {* Design laws *}

lemma unrest_out_des_lift [unrest]: "out\<alpha> \<sharp> p \<Longrightarrow> out\<alpha> \<sharp> \<lceil>p\<rceil>\<^sub>D"
  by (pred_simp, auto simp add: out\<alpha>_def des_vars_child_lens_def)

lemma lift_dist_seq [simp]:
  "\<lceil>P ;; Q\<rceil>\<^sub>D = (\<lceil>P\<rceil>\<^sub>D ;; \<lceil>Q\<rceil>\<^sub>D)"
  by (rel_auto)

lemma lift_des_skip_dr_unit_unrest: "$ok\<acute> \<sharp> P \<Longrightarrow> (P ;; \<lceil>II\<rceil>\<^sub>D) = P"
  by (rel_auto)

lemma true_is_design:
  "(false \<turnstile> true) = true"
  by (rel_auto)

lemma true_is_rdesign:
  "(false \<turnstile>\<^sub>r true) = true"
  by (rel_auto)

lemma design_false_pre:
  "(false \<turnstile> P) = true"
  by (rel_auto)

lemma rdesign_false_pre:
  "(false \<turnstile>\<^sub>r P) = true"
  by (rel_auto)

lemma ndesign_false_pre:
  "(false \<turnstile>\<^sub>n P) = true"
  by (rel_auto)

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

lemma ndesign_refine_intro:
  assumes "`p1 \<Rightarrow> p2`" "`\<lceil>p1\<rceil>\<^sub>< \<and> Q2 \<Rightarrow> Q1`"
  shows "p1 \<turnstile>\<^sub>n Q1 \<sqsubseteq> p2 \<turnstile>\<^sub>n Q2"
  using assms unfolding upred_defs
  by (pred_auto)

lemma design_subst [usubst]:
  "\<lbrakk> $ok \<sharp> \<sigma>; $ok\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<dagger> (P \<turnstile> Q) = (\<sigma> \<dagger> P) \<turnstile> (\<sigma> \<dagger> Q)"
  by (simp add: design_def usubst)

theorem design_ok_false [usubst]: "(P \<turnstile> Q)\<lbrakk>false/$ok\<rbrakk> = true"
  by (simp add: design_def usubst)

theorem design_npre:
  "(P \<turnstile> Q)\<^sup>f = (\<not> $ok \<or> \<not> P\<^sup>f)"
  by (rel_auto)

theorem design_pre:
  "\<not> (P \<turnstile> Q)\<^sup>f = ($ok \<and> P\<^sup>f)"
  by (simp add: design_def, subst_tac)
     (metis (no_types, hide_lams) not_conj_deMorgans true_not_false(2) utp_pred.compl_top_eq
            utp_pred.sup.idem utp_pred.sup_compl_top)

theorem design_post:
  "(P \<turnstile> Q)\<^sup>t = (($ok \<and> P\<^sup>t) \<Rightarrow> Q\<^sup>t)"
  by (rel_auto)

theorem rdesign_pre [simp]: "pre\<^sub>D(P \<turnstile>\<^sub>r Q) = P"
  by (pred_auto)

theorem rdesign_post [simp]: "post\<^sub>D(P \<turnstile>\<^sub>r Q) = (P \<Rightarrow> Q)"
  by (pred_auto)

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

theorem design_top_left_zero: "(\<top>\<^sub>D ;; (P \<turnstile> Q)) = \<top>\<^sub>D"
  by (rel_auto)

theorem design_choice:
  "(P\<^sub>1 \<turnstile> P\<^sub>2) \<sqinter> (Q\<^sub>1 \<turnstile> Q\<^sub>2) = ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<or> Q\<^sub>2))"
  by (rel_auto)

theorem design_inf:
  "(P\<^sub>1 \<turnstile> P\<^sub>2) \<squnion> (Q\<^sub>1 \<turnstile> Q\<^sub>2) = ((P\<^sub>1 \<or> Q\<^sub>1) \<turnstile> ((P\<^sub>1 \<Rightarrow> P\<^sub>2) \<and> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)))"
  by (rel_auto)

theorem rdesign_choice:
  "(P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) \<sqinter> (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2) = ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile>\<^sub>r (P\<^sub>2 \<or> Q\<^sub>2))"
  by (rel_auto)

theorem design_condr:
  "((P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> b \<triangleright> (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = ((P\<^sub>1 \<triangleleft> b \<triangleright> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<triangleleft> b \<triangleright> Q\<^sub>2))"
  by (rel_auto)

lemma design_top:
  "(P \<turnstile> Q) \<sqsubseteq> \<top>\<^sub>D"
  by (rel_auto)

lemma design_bottom:
  "\<bottom>\<^sub>D \<sqsubseteq> (P \<turnstile> Q)"
  by simp

lemma design_USUP:
  assumes "A \<noteq> {}"
  shows "(\<Sqinter> i \<in> A \<bullet> P(i) \<turnstile> Q(i)) = (\<Squnion> i \<in> A \<bullet> P(i)) \<turnstile> (\<Sqinter> i \<in> A \<bullet> Q(i))"
  using assms by (rel_auto)

lemma design_UINF:
  "(\<Squnion> i \<in> A \<bullet> P(i) \<turnstile> Q(i)) = (\<Sqinter> i \<in> A \<bullet> P(i)) \<turnstile> (\<Squnion> i \<in> A \<bullet> P(i) \<Rightarrow> Q(i))"
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

lemma design_export_ok:
  "P \<turnstile> Q = (P \<turnstile> ($ok \<and> Q))"
  by (rel_auto)

lemma design_export_ok':
  "P \<turnstile> Q = (P \<turnstile> ($ok\<acute> \<and> Q))"
  by (rel_auto)

lemma design_export_pre: "P \<turnstile> (P \<and> Q) = P \<turnstile> Q"
  by (rel_auto)

lemma design_ok_pre_conj: "($ok \<and> P) \<turnstile> Q = P \<turnstile> Q"
  by (rel_auto)

theorem design_composition:
  assumes
    "$ok\<acute> \<sharp> P1" "$ok \<sharp> P2" "$ok\<acute> \<sharp> Q1" "$ok \<sharp> Q2"
  shows "((P1 \<turnstile> Q1) ;; (P2 \<turnstile> Q2)) = (((\<not> ((\<not> P1) ;; true)) \<and> \<not> (Q1 ;; (\<not> P2))) \<turnstile> (Q1 ;; Q2))"
  using assms by (simp add: design_composition_subst usubst)

lemma runrest_ident_var:
  assumes "x \<sharp>\<sharp> P"
  shows "($x \<and> P) = (P \<and> $x\<acute>)"
proof -
  have "P = ($x\<acute> =\<^sub>u $x \<and> P)"
    by (metis RID_def assms unrest_relation_def utp_pred.inf.cobounded2 utp_pred.inf_absorb2)
  moreover have "($x\<acute> =\<^sub>u $x \<and> ($x \<and> P)) = ($x\<acute> =\<^sub>u $x \<and> (P \<and> $x\<acute>))"
    by (rel_auto)
  ultimately show ?thesis
    by (metis utp_pred.inf.assoc utp_pred.inf_left_commute)
qed

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
      by (metis ok_vwb_lens seqr_pre_transfer seqr_right_one_point true_alt_def uovar_convr upred_eq_true utp_pred.inf.left_idem utp_rel.unrest_ouvar vwb_lens_mwb)
    finally show ?thesis
      by (metis utp_pred.inf.left_commute utp_pred.inf_left_idem)
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

lemma skip_d_alt_def: "II\<^sub>D = true \<turnstile> II"
  by (rel_auto)

theorem design_skip_idem [simp]:
  "(II\<^sub>D ;; II\<^sub>D) = II\<^sub>D"
  by (rel_auto)

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

theorem ndesign_composition_wp:
  "((p1 \<turnstile>\<^sub>n Q1) ;; (p2 \<turnstile>\<^sub>n Q2)) = ((p1 \<and> Q1 wp p2) \<turnstile>\<^sub>n (Q1 ;; Q2))"
  by (rel_blast)

theorem rdesign_wp [wp]:
  "(\<lceil>p\<rceil>\<^sub>< \<turnstile>\<^sub>r Q) wp\<^sub>D r = (p \<and> Q wp r)"
  by (rel_auto)

theorem ndesign_wp [wp]:
  "(p \<turnstile>\<^sub>n Q) wp\<^sub>D r = (p \<and> Q wp r)"
  by (simp add: ndesign_def rdesign_wp)

theorem wpd_seq_r:
  fixes Q1 Q2 :: "'\<alpha> hrel"
  shows "(\<lceil>p1\<rceil>\<^sub>< \<turnstile>\<^sub>r Q1 ;; \<lceil>p2\<rceil>\<^sub>< \<turnstile>\<^sub>r Q2) wp\<^sub>D r = (\<lceil>p1\<rceil>\<^sub>< \<turnstile>\<^sub>r Q1) wp\<^sub>D ((\<lceil>p2\<rceil>\<^sub>< \<turnstile>\<^sub>r Q2) wp\<^sub>D r)"
  apply (simp add: wp)
  apply (subst rdesign_composition_wp)
  apply (simp only: wp)
  apply (rel_auto)
done

theorem wpnd_seq_r [wp]:
  fixes Q1 Q2 :: "'\<alpha> hrel"
  shows "(p1 \<turnstile>\<^sub>n Q1 ;; p2 \<turnstile>\<^sub>n Q2) wp\<^sub>D r = (p1 \<turnstile>\<^sub>n Q1) wp\<^sub>D ((p2 \<turnstile>\<^sub>n Q2) wp\<^sub>D r)"
  by (simp add: ndesign_def wpd_seq_r)

lemma design_subst_ok:
  "(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true/$ok\<rbrakk>) = (P \<turnstile> Q)"
  by (rel_auto)

lemma design_subst_ok_ok':
  "(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>) = (P \<turnstile> Q)"
proof -
  have "(P \<turnstile> Q) = (($ok \<and> P) \<turnstile> ($ok \<and> $ok\<acute> \<and> Q))"
    by (pred_auto)
  also have "... = (($ok \<and> P\<lbrakk>true/$ok\<rbrakk>) \<turnstile> ($ok \<and> ($ok\<acute> \<and> Q\<lbrakk>true/$ok\<acute>\<rbrakk>)\<lbrakk>true/$ok\<rbrakk>))"
    by (metis conj_eq_out_var_subst conj_pos_var_subst upred_eq_true utp_pred.inf_commute ok_vwb_lens)
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
    by (metis conj_eq_out_var_subst upred_eq_true utp_pred.inf_commute ok_vwb_lens)
  also have "... = (P \<turnstile> Q\<lbrakk>true/$ok\<acute>\<rbrakk>)"
    by (pred_auto)
  finally show ?thesis ..
qed

theorem design_left_unit_hom:
  fixes P Q :: "'\<alpha> hrel_des"
  shows "(II\<^sub>D ;; P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
proof -
  have "(II\<^sub>D ;; P \<turnstile>\<^sub>r Q) = (true \<turnstile>\<^sub>r II ;; P \<turnstile>\<^sub>r Q)"
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

theorem design_left_unit [simp]:
  "(II\<^sub>D ;; P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
  by (rel_auto)

theorem design_right_semi_unit:
  "(P \<turnstile>\<^sub>r Q ;; II\<^sub>D) = ((\<not> (\<not> P) ;; true) \<turnstile>\<^sub>r Q)"
  by (simp add: skip_d_def rdesign_composition)

theorem design_right_cond_unit [simp]:
  assumes "out\<alpha> \<sharp> p"
  shows "(p \<turnstile>\<^sub>r Q ;; II\<^sub>D) = (p \<turnstile>\<^sub>r Q)"
  using assms
  by (simp add: skip_d_def rdesign_composition_cond)

lemma lift_des_skip_dr_unit [simp]:
  "(\<lceil>P\<rceil>\<^sub>D ;; \<lceil>II\<rceil>\<^sub>D) = \<lceil>P\<rceil>\<^sub>D"
  "(\<lceil>II\<rceil>\<^sub>D ;; \<lceil>P\<rceil>\<^sub>D) = \<lceil>P\<rceil>\<^sub>D"
  by (rel_auto)+

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

subsection {* Design preconditions *}

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

subsection {* H1: No observation is allowed before initiation *}

lemma H1_idem:
  "H1 (H1 P) = H1(P)"
  by (pred_auto)

lemma H1_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> H1(P) \<sqsubseteq> H1(Q)"
  by (pred_auto)

lemma H1_Continuous: "Continuous H1"
  by (rel_auto)

lemma H1_below_top:
  "H1(P) \<sqsubseteq> \<top>\<^sub>D"
  by (pred_auto)

lemma H1_design_skip:
  "H1(II) = II\<^sub>D"
  by (rel_auto)

lemma H1_cond: "H1(P \<triangleleft> b \<triangleright> Q) = H1(P) \<triangleleft> b \<triangleright> H1(Q)"
  by (rel_auto)

lemma H1_conj: "H1(P \<and> Q) = (H1(P) \<and> H1(Q))"
  by (rel_auto)

lemma H1_disj: "H1(P \<or> Q) = (H1(P) \<or> H1(Q))"
  by (rel_auto)

lemma design_export_H1: "(P \<turnstile> Q) = (P \<turnstile> H1(Q))"
  by (rel_auto)

text {* The H1 algebraic laws are valid only when $\alpha(R)$ is homogeneous. This should maybe be
        generalised. *}

theorem H1_algebraic_intro:
  assumes
    "(true\<^sub>h ;; R) = true\<^sub>h"
    "(II\<^sub>D ;; R) = R"
  shows "R is H1"
proof -
  have "R = (II\<^sub>D ;; R)" by (simp add: assms(2))
  also have "... = (H1(II) ;; R)"
    by (simp add: H1_design_skip)
  also have "... = (($ok \<Rightarrow> II) ;; R)"
    by (simp add: H1_def)
  also have "... = (((\<not> $ok) ;; R) \<or> R)"
    by (simp add: impl_alt_def seqr_or_distl)
  also have "... = ((((\<not> $ok) ;; true\<^sub>h) ;; R) \<or> R)"
    by (simp add: precond_right_unit unrest)
  also have "... = (((\<not> $ok) ;; true\<^sub>h) \<or> R)"
    by (metis assms(1) seqr_assoc)
  also have "... = ($ok \<Rightarrow> R)"
    by (simp add: impl_alt_def precond_right_unit unrest)
  finally show ?thesis by (metis H1_def Healthy_def')
qed

lemma nok_not_false:
  "(\<not> $ok) \<noteq> false"
  by (pred_auto)

theorem H1_left_zero:
  assumes "P is H1"
  shows "(true ;; P) = true"
proof -
  from assms have "(true ;; P) = (true ;; ($ok \<Rightarrow> P))"
    by (simp add: H1_def Healthy_def')
  (* The next step ensures we get the right alphabet for true by copying it *)
  also from assms have "... = (true ;; (\<not> $ok \<or> P))" (is "_ = (?true ;; _)")
    by (simp add: impl_alt_def)
  also from assms have "... = ((?true ;; (\<not> $ok)) \<or> (?true ;; P))"
    using seqr_or_distr by blast
  also from assms have "... = (true \<or> (true ;; P))"
    by (simp add: nok_not_false precond_left_zero unrest)
  finally show ?thesis
    by (simp add: upred_defs urel_defs)
qed

theorem H1_left_unit:
  fixes P :: "'\<alpha> hrel_des"
  assumes "P is H1"
  shows "(II\<^sub>D ;; P) = P"
proof -
  have "(II\<^sub>D ;; P) = (($ok \<Rightarrow> II) ;; P)"
    by (metis H1_def H1_design_skip)
  also have "... = (((\<not> $ok) ;; P) \<or> P)"
    by (simp add: impl_alt_def seqr_or_distl)
  also from assms have "... = ((((\<not> $ok) ;; true\<^sub>h) ;; P) \<or> P)"
    by (simp add: precond_right_unit unrest)
  also have "... = (((\<not> $ok) ;; (true\<^sub>h ;; P)) \<or> P)"
    by (simp add: seqr_assoc)
  also from assms have "... = ($ok \<Rightarrow> P)"
    by (simp add: H1_left_zero impl_alt_def precond_right_unit unrest)
  finally show ?thesis using assms
    by (simp add: H1_def Healthy_def')
qed

theorem H1_algebraic:
  "P is H1 \<longleftrightarrow> (true\<^sub>h ;; P) = true\<^sub>h \<and> (II\<^sub>D ;; P) = P"
  using H1_algebraic_intro H1_left_unit H1_left_zero by blast

theorem H1_nok_left_zero:
  fixes P :: "'\<alpha> hrel_des"
  assumes "P is H1"
  shows "((\<not> $ok) ;; P) = (\<not> $ok)"
proof -
  have "((\<not> $ok) ;; P) = (((\<not> $ok) ;; true\<^sub>h) ;; P)"
    by (simp add: precond_right_unit unrest)
  also have "... = ((\<not> $ok) ;; true\<^sub>h)"
    by (metis H1_left_zero assms seqr_assoc)
  also have "... = (\<not> $ok)"
    by (simp add: precond_right_unit unrest)
  finally show ?thesis .
qed

lemma H1_design:
  "H1(P \<turnstile> Q) = (P \<turnstile> Q)"
  by (rel_auto)

lemma H1_rdesign:
  "H1(P \<turnstile>\<^sub>r Q) = (P \<turnstile>\<^sub>r Q)"
  by (rel_auto)

lemma H1_choice_closed:
  "\<lbrakk> P is H1; Q is H1 \<rbrakk> \<Longrightarrow> P \<sqinter> Q is H1"
  by (simp add: H1_def Healthy_def' disj_upred_def impl_alt_def semilattice_sup_class.sup_left_commute)

lemma H1_inf_closed:
  "\<lbrakk> P is H1; Q is H1 \<rbrakk> \<Longrightarrow> P \<squnion> Q is H1"
  by (rel_blast)

lemma H1_USUP:
  assumes "A \<noteq> {}"
  shows "H1(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> H1(P(i)))"
  using assms by (rel_auto)

lemma H1_Sup:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is H1"
  shows "(\<Sqinter> A) is H1"
proof -
  from assms(2) have "H1 ` A = A"
    by (auto simp add: Healthy_def rev_image_eqI)
  with H1_USUP[of A id, OF assms(1)] show ?thesis
    by (simp add: USUP_as_Sup_image Healthy_def, presburger)
qed

lemma H1_UINF:
  shows "H1(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> H1(P(i)))"
  by (rel_auto)

lemma H1_Inf:
  assumes "\<forall> P \<in> A. P is H1"
  shows "(\<Squnion> A) is H1"
proof -
  from assms have "H1 ` A = A"
    by (auto simp add: Healthy_def rev_image_eqI)
  with H1_UINF[of A id] show ?thesis
    by (simp add: UINF_as_Inf_image Healthy_def, presburger)
qed

subsection {* H2: A specification cannot require non-termination *}

lemma J_split:
  shows "(P ;; J) = (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))"
proof -
  have "(P ;; J) = (P ;; (($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D))"
    by (simp add: H2_def J_def design_def)
  also have "... = (P ;; (($ok \<Rightarrow> $ok \<and> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D))"
    by (rel_auto)
  also have "... = ((P ;; (\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D)) \<or> (P ;; ($ok \<and> (\<lceil>II\<rceil>\<^sub>D \<and> $ok\<acute>))))"
    by (rel_auto)
  also have "... = (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))"
  proof -
    have "(P ;; (\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D)) = P\<^sup>f"
    proof -
      have "(P ;; (\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D)) = ((P \<and> \<not> $ok\<acute>) ;; \<lceil>II\<rceil>\<^sub>D)"
        by (rel_auto)
      also have "... = (\<exists> $ok\<acute> \<bullet> P \<and> $ok\<acute> =\<^sub>u false)"
        by (rel_auto)
      also have "... = P\<^sup>f"
        by (metis C1 one_point out_var_uvar unrest_as_exists ok_vwb_lens vwb_lens_mwb)
     finally show ?thesis .
    qed
    moreover have "(P ;; ($ok \<and> (\<lceil>II\<rceil>\<^sub>D \<and> $ok\<acute>))) = (P\<^sup>t \<and> $ok\<acute>)"
    proof -
      have "(P ;; ($ok \<and> (\<lceil>II\<rceil>\<^sub>D \<and> $ok\<acute>))) = (P ;; ($ok \<and> II))"
        by (rel_auto)
      also have "... = (P\<^sup>t \<and> $ok\<acute>)"
        by (rel_auto)
      finally show ?thesis .
    qed
    ultimately show ?thesis
      by simp
  qed
  finally show ?thesis .
qed

lemma H2_split:
  shows "H2(P) = (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))"
  by (simp add: H2_def J_split)

theorem H2_equivalence:
  "P is H2 \<longleftrightarrow> `P\<^sup>f \<Rightarrow> P\<^sup>t`"
proof -
  have "`P \<Leftrightarrow> (P ;; J)` \<longleftrightarrow> `P \<Leftrightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>))`"
    by (simp add: J_split)
  also have "... \<longleftrightarrow> `(P \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>)\<^sup>f \<and> (P \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>)\<^sup>t`"
    by (simp add: subst_bool_split)
  also have "... = `(P\<^sup>f \<Leftrightarrow> P\<^sup>f) \<and> (P\<^sup>t \<Leftrightarrow> P\<^sup>f \<or> P\<^sup>t)`"
    by subst_tac
  also have "... = `P\<^sup>t \<Leftrightarrow> (P\<^sup>f \<or> P\<^sup>t)`"
    by (pred_auto robust)
  also have "... = `(P\<^sup>f \<Rightarrow> P\<^sup>t)`"
    by (pred_auto)
  finally show ?thesis
    by (metis H2_def Healthy_def' taut_iff_eq)
qed

lemma H2_equiv:
  "P is H2 \<longleftrightarrow> P\<^sup>t \<sqsubseteq> P\<^sup>f"
  using H2_equivalence refBy_order by blast

lemma H2_design:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q"
  shows "H2(P \<turnstile> Q) = P \<turnstile> Q"
  using assms
  by (simp add: H2_split design_def usubst unrest, pred_auto)

lemma H2_rdesign:
  "H2(P \<turnstile>\<^sub>r Q) = P \<turnstile>\<^sub>r Q"
  by (simp add: H2_design unrest rdesign_def)

theorem J_idem:
  "(J ;; J) = J"
  by (rel_auto)

theorem H2_idem:
  "H2(H2(P)) = H2(P)"
  by (metis H2_def J_idem seqr_assoc)

theorem H2_Continuous: "Continuous H2"
  by (rel_auto)

theorem H2_not_okay: "H2 (\<not> $ok) = (\<not> $ok)"
proof -
  have "H2 (\<not> $ok) = ((\<not> $ok)\<^sup>f \<or> ((\<not> $ok)\<^sup>t \<and> $ok\<acute>))"
    by (simp add: H2_split)
  also have "... = (\<not> $ok \<or> (\<not> $ok) \<and> $ok\<acute>)"
    by (subst_tac)
  also have "... = (\<not> $ok)"
    by (pred_auto)
  finally show ?thesis .
qed

lemma H2_true: "H2(true) = true"
  by (rel_auto)

lemma H2_choice_closed:
  "\<lbrakk> P is H2; Q is H2 \<rbrakk> \<Longrightarrow> P \<sqinter> Q is H2"
  by (metis H2_def Healthy_def' disj_upred_def seqr_or_distl)

lemma H2_inf_closed:
  assumes "P is H2" "Q is H2"
  shows "P \<squnion> Q is H2"
proof -
  have "P \<squnion> Q = (P\<^sup>f \<or> P\<^sup>t \<and> $ok\<acute>) \<squnion> (Q\<^sup>f \<or> Q\<^sup>t \<and> $ok\<acute>)"
    by (metis H2_def Healthy_def J_split assms(1) assms(2))
  moreover have "H2(...) = ..."
    by (simp add: H2_split usubst, pred_auto)
  ultimately show ?thesis
    by (simp add: Healthy_def)
qed

lemma H2_USUP:
  shows "H2(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> H2(P(i)))"
  by (rel_auto)

theorem H1_H2_commute:
  "H1 (H2 P) = H2 (H1 P)"
proof -
  have "H2 (H1 P) = (($ok \<Rightarrow> P) ;; J)"
    by (simp add: H1_def H2_def)
  also have "... = ((\<not> $ok \<or> P) ;; J)"
    by (rel_auto)
  also have "... = (((\<not> $ok) ;; J) \<or> (P ;; J))"
    using seqr_or_distl by blast
  also have "... =  ((H2 (\<not> $ok)) \<or> H2(P))"
    by (simp add: H2_def)
  also have "... =  ((\<not> $ok) \<or> H2(P))"
    by (simp add: H2_not_okay)
  also have "... = H1(H2(P))"
    by (rel_auto)
  finally show ?thesis by simp
qed

lemma ok_pre: "($ok \<and> \<lceil>pre\<^sub>D(P)\<rceil>\<^sub>D) = ($ok \<and> (\<not> P\<^sup>f))"
  by (pred_auto robust)

lemma ok_post: "($ok \<and> \<lceil>post\<^sub>D(P)\<rceil>\<^sub>D) = ($ok \<and> (P\<^sup>t))"
  by (pred_auto robust)

abbreviation "H1_H2 P \<equiv> H1 (H2 P)"

notation H1_H2 ("\<^bold>H")

lemma H1_H2_comp: "\<^bold>H = H1 \<circ> H2"
  by (auto)

theorem H1_H2_eq_design:
  "\<^bold>H(P) = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
proof -
  have "\<^bold>H(P) = ($ok \<Rightarrow> H2(P))"
    by (simp add: H1_def)
  also have "... = ($ok \<Rightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>)))"
    by (metis H2_split)
  also have "... = ($ok \<and> (\<not> P\<^sup>f) \<Rightarrow> $ok\<acute> \<and> $ok \<and> P\<^sup>t)"
    by (rel_auto)
  also have "... = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
    by (rel_auto)
  finally show ?thesis .
qed

theorem H1_H2_is_design:
  assumes "P is H1" "P is H2"
  shows "P = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
  using assms by (metis H1_H2_eq_design Healthy_def)

theorem H1_H2_eq_rdesign:
  "\<^bold>H(P) = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
proof -
  have "\<^bold>H(P) = ($ok \<Rightarrow> H2(P))"
    by (simp add: H1_def Healthy_def')
  also have "... = ($ok \<Rightarrow> (P\<^sup>f \<or> (P\<^sup>t \<and> $ok\<acute>)))"
    by (metis H2_split)
  also have "... = ($ok \<and> (\<not> P\<^sup>f) \<Rightarrow> $ok\<acute> \<and> P\<^sup>t)"
    by (pred_auto)
  also have "... = ($ok \<and> (\<not> P\<^sup>f) \<Rightarrow> $ok\<acute> \<and> $ok \<and> P\<^sup>t)"
    by (pred_auto)
  also have "... = ($ok \<and> \<lceil>pre\<^sub>D(P)\<rceil>\<^sub>D \<Rightarrow> $ok\<acute> \<and> $ok \<and> \<lceil>post\<^sub>D(P)\<rceil>\<^sub>D)"
    by (simp add: ok_post ok_pre)
  also have "... = ($ok \<and> \<lceil>pre\<^sub>D(P)\<rceil>\<^sub>D \<Rightarrow> $ok\<acute> \<and> \<lceil>post\<^sub>D(P)\<rceil>\<^sub>D)"
    by (pred_auto)
  also have "... =  pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
    by (simp add: rdesign_def design_def)
  finally show ?thesis .
qed

theorem H1_H2_is_rdesign:
  assumes "P is H1" "P is H2"
  shows "P = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
  by (metis H1_H2_eq_rdesign Healthy_def assms(1) assms(2))

lemma H1_H2_idempotent: "\<^bold>H (\<^bold>H P) = \<^bold>H P"
  by (simp add: H1_H2_commute H1_idem H2_idem)

lemma H1_H2_Idempotent: "Idempotent \<^bold>H"
  by (simp add: Idempotent_def H1_H2_idempotent)

lemma H1_H2_monotonic: "Monotonic \<^bold>H"
  by (simp add: H1_monotone H2_def Monotonic_def seqr_mono)

lemma H1_H2_Continuous: "Continuous \<^bold>H"
  by (simp add: Continuous_comp H1_Continuous H1_H2_comp H2_Continuous)

lemma design_is_H1_H2 [closure]:
  "\<lbrakk> $ok\<acute> \<sharp> P; $ok\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> (P \<turnstile> Q) is \<^bold>H"
  by (simp add: H1_design H2_design Healthy_def')

lemma rdesign_is_H1_H2 [closure]:
  "(P \<turnstile>\<^sub>r Q) is \<^bold>H"
  by (simp add: Healthy_def H1_rdesign H2_rdesign)

lemma assigns_d_is_H1_H2 [closure]:
  "\<langle>\<sigma>\<rangle>\<^sub>D is \<^bold>H"
  by (simp add: assigns_d_def rdesign_is_H1_H2)

lemma seq_r_H1_H2_closed [closure]:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P ;; Q) is \<^bold>H"
proof -
  obtain P\<^sub>1 P\<^sub>2 where "P = P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(1))
  moreover obtain Q\<^sub>1 Q\<^sub>2 where "Q = Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2"
   by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def assms(2))
  moreover have "((P\<^sub>1 \<turnstile>\<^sub>r P\<^sub>2) ;; (Q\<^sub>1 \<turnstile>\<^sub>r Q\<^sub>2)) is \<^bold>H"
    by (simp add: rdesign_composition rdesign_is_H1_H2)
  ultimately show ?thesis by simp
qed

lemma assigns_d_comp_ext:
  fixes P :: "'\<alpha> hrel_des"
  assumes "P is \<^bold>H"
  shows "(\<langle>\<sigma>\<rangle>\<^sub>D ;; P) = \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> P"
proof -
  have "(\<langle>\<sigma>\<rangle>\<^sub>D ;; P) = (\<langle>\<sigma>\<rangle>\<^sub>D ;; pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P))"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def' assms)
  also have "... = \<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> pre\<^sub>D(P) \<turnstile>\<^sub>r \<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> post\<^sub>D(P)"
    by (simp add: assign_d_left_comp)
  also have "... = \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> (pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P))"
    by (rel_auto)
  also have "... = \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rceil>\<^sub>s \<dagger> P"
    by (metis H1_H2_commute H1_H2_is_rdesign H2_idem Healthy_def' assms)
  finally show ?thesis .
qed

lemma USUP_H1_H2_closed:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Sqinter> A) is H1_H2"
proof -
  from assms have A: "A = H1_H2 ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Sqinter> ...) = (\<Sqinter> P \<in> A \<bullet> H1_H2(P))"
    by (simp add: USUP_as_Sup_collect)
  also have "... = (\<Sqinter> P \<in> A \<bullet> (\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (meson H1_H2_eq_design)
  also have "... = (\<Squnion> P \<in> A \<bullet> \<not> P\<^sup>f) \<turnstile> (\<Sqinter> P \<in> A \<bullet> P\<^sup>t)"
    by (simp add: design_USUP assms)
  also have "... is H1_H2"
    by (simp add: design_is_H1_H2 unrest)
  finally show ?thesis .
qed

definition design_sup :: "('\<alpha>, '\<beta>) rel_des set \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<Sqinter>\<^sub>D_" [900] 900) where
"\<Sqinter>\<^sub>D A = (if (A = {}) then \<top>\<^sub>D else \<Sqinter> A)"

lemma design_sup_H1_H2_closed:
  assumes "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Sqinter>\<^sub>D A) is \<^bold>H"
  apply (auto simp add: design_sup_def)
  apply (simp add: H1_def H2_not_okay Healthy_def impl_alt_def)
  using USUP_H1_H2_closed assms apply blast
done

lemma design_sup_empty [simp]: "\<Sqinter>\<^sub>D {} = \<top>\<^sub>D"
  by (simp add: design_sup_def)

lemma design_sup_non_empty [simp]: "A \<noteq> {} \<Longrightarrow> \<Sqinter>\<^sub>D A = \<Sqinter> A"
  by (simp add: design_sup_def)

lemma UINF_H1_H2_closed:
  assumes "\<forall> P \<in> A. P is \<^bold>H"
  shows "(\<Squnion> A) is \<^bold>H"
proof -
  from assms have A: "A = \<^bold>H ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Squnion> ...) = (\<Squnion> P \<in> A \<bullet> \<^bold>H(P))"
    by (simp add: UINF_as_Inf_collect)
  also have "... = (\<Squnion> P \<in> A \<bullet> (\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
    by (meson H1_H2_eq_design)
  also have "... = (\<Sqinter> P \<in> A \<bullet> \<not> P\<^sup>f) \<turnstile> (\<Squnion> P \<in> A \<bullet> \<not> P\<^sup>f \<Rightarrow> P\<^sup>t)"
    by (simp add: design_UINF)
  also have "... is \<^bold>H"
    by (simp add: design_is_H1_H2 unrest)
  finally show ?thesis .
qed

abbreviation design_inf :: "('\<alpha>, '\<beta>) rel_des set \<Rightarrow> ('\<alpha>, '\<beta>) rel_des" ("\<Squnion>\<^sub>D_" [900] 900) where
"\<Squnion>\<^sub>D A \<equiv> \<Squnion> A"

subsection {* H3: The design assumption is a precondition *}

theorem H3_idem:
  "H3(H3(P)) = H3(P)"
  by (metis H3_def design_skip_idem seqr_assoc)

theorem H3_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> H3(P) \<sqsubseteq> H3(Q)"
  by (simp add: H3_def seqr_mono)

theorem H3_Monotonic:
  "Monotonic H3"
  by (simp add: H3_mono Monotonic_def)

theorem H3_Continuous: "Continuous H3"
  by (rel_auto)

theorem design_condition_is_H3:
  assumes "out\<alpha> \<sharp> p"
  shows "(p \<turnstile> Q) is H3"
proof -
  have "((p \<turnstile> Q) ;; II\<^sub>D) = (\<not> ((\<not> p) ;; true)) \<turnstile> (Q\<^sup>t ;; II\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: skip_d_alt_def design_composition_subst unrest assms)
  also have "... = p \<turnstile> (Q\<^sup>t ;; II\<lbrakk>true/$ok\<rbrakk>)"
    using assms precond_equiv seqr_true_lemma by force
  also have "... = p \<turnstile> Q"
    by (rel_auto)
  finally show ?thesis
    by (simp add: H3_def Healthy_def')
qed

theorem rdesign_H3_iff_pre:
  "P \<turnstile>\<^sub>r Q is H3 \<longleftrightarrow> P = (P ;; true)"
proof -
  have "(P \<turnstile>\<^sub>r Q ;; II\<^sub>D) = (P \<turnstile>\<^sub>r Q ;; true \<turnstile>\<^sub>r II)"
    by (simp add: skip_d_def)
  also have "... = (\<not> ((\<not> P) ;; true) \<and> \<not> (Q ;; (\<not> true))) \<turnstile>\<^sub>r (Q ;; II)"
    by (simp add: rdesign_composition)
  also have "... = (\<not> ((\<not> P) ;; true) \<and> \<not> (Q ;; (\<not> true))) \<turnstile>\<^sub>r Q"
    by simp
  also have "... = (\<not> ((\<not> P) ;; true)) \<turnstile>\<^sub>r Q"
    by (pred_auto)
  finally have "P \<turnstile>\<^sub>r Q is H3 \<longleftrightarrow> P \<turnstile>\<^sub>r Q = (\<not> ((\<not> P) ;; true)) \<turnstile>\<^sub>r Q"
    by (metis H3_def Healthy_def')
  also have "... \<longleftrightarrow> P = (\<not> ((\<not> P) ;; true))"
    by (metis rdesign_pre)
      thm seqr_true_lemma
  also have "... \<longleftrightarrow> P = (P ;; true)"
    by (simp add: seqr_true_lemma)
  finally show ?thesis .
qed

theorem design_H3_iff_pre:
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$ok \<sharp> Q" "$ok\<acute> \<sharp> Q"
  shows "P \<turnstile> Q is H3 \<longleftrightarrow> P = (P ;; true)"
proof -
  have "P \<turnstile> Q = \<lfloor>P\<rfloor>\<^sub>D \<turnstile>\<^sub>r \<lfloor>Q\<rfloor>\<^sub>D"
    by (simp add: assms lift_desr_inv rdesign_def)
  moreover hence "\<lfloor>P\<rfloor>\<^sub>D \<turnstile>\<^sub>r \<lfloor>Q\<rfloor>\<^sub>D is H3 \<longleftrightarrow> \<lfloor>P\<rfloor>\<^sub>D = (\<lfloor>P\<rfloor>\<^sub>D ;; true)"
    using rdesign_H3_iff_pre by blast
  ultimately show ?thesis
    by (metis assms(1,2) drop_desr_inv lift_desr_inv lift_dist_seq aext_true)
qed

theorem H1_H3_commute:
  "H1 (H3 P) = H3 (H1 P)"
  by (rel_auto)

lemma skip_d_absorb_J_1:
  "(II\<^sub>D ;; J) = II\<^sub>D"
  by (metis H2_def H2_rdesign skip_d_def)

lemma skip_d_absorb_J_2:
  "(J ;; II\<^sub>D) = II\<^sub>D"
proof -
  have "(J ;; II\<^sub>D) = ((($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D) ;; true \<turnstile> II)"
    by (simp add: J_def skip_d_alt_def)
  also have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (true \<turnstile> II)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>)"
    by (subst seqr_middle[of ok], simp_all)
  also have "... = (((($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>false/$ok\<acute>\<rbrakk> ;; (true \<turnstile> II)\<lbrakk>false/$ok\<rbrakk>)
                  \<or> ((($ok \<Rightarrow> $ok\<acute>) \<and> \<lceil>II\<rceil>\<^sub>D)\<lbrakk>true/$ok\<acute>\<rbrakk> ;; (true \<turnstile> II)\<lbrakk>true/$ok\<rbrakk>))"
    by (simp add: disj_comm false_alt_def true_alt_def)
  also have "... = ((\<not> $ok \<and> \<lceil>II\<rceil>\<^sub>D ;; true) \<or> (\<lceil>II\<rceil>\<^sub>D ;; $ok\<acute> \<and> \<lceil>II\<rceil>\<^sub>D))"
    by (rel_auto)
  also have "... = II\<^sub>D"
    by (rel_auto)
  finally show ?thesis .
qed

lemma H2_H3_absorb:
  "H2 (H3 P) = H3 P"
  by (metis H2_def H3_def seqr_assoc skip_d_absorb_J_1)

lemma H3_H2_absorb:
  "H3 (H2 P) = H3 P"
  by (metis H2_def H3_def seqr_assoc skip_d_absorb_J_2)

theorem H2_H3_commute:
  "H2 (H3 P) = H3 (H2 P)"
  by (simp add: H2_H3_absorb H3_H2_absorb)

theorem H3_design_pre:
  assumes "$ok \<sharp> p" "out\<alpha> \<sharp> p" "$ok \<sharp> Q" "$ok\<acute> \<sharp> Q"
  shows "H3(p \<turnstile> Q) = p \<turnstile> Q"
  using assms
  by (metis Healthy_def' design_H3_iff_pre precond_right_unit unrest_out\<alpha>_var ok_vwb_lens vwb_lens_mwb)

theorem H3_rdesign_pre:
  assumes "out\<alpha> \<sharp> p"
  shows "H3(p \<turnstile>\<^sub>r Q) = p \<turnstile>\<^sub>r Q"
  using assms
  by (simp add: H3_def)

theorem H3_ndesign:
  "H3(p \<turnstile>\<^sub>n Q) = (p \<turnstile>\<^sub>n Q)"
  by (simp add: H3_def ndesign_def unrest_pre_out\<alpha>)

theorem H1_H3_is_design:
  assumes "P is H1" "P is H3"
  shows "P = (\<not> P\<^sup>f) \<turnstile> P\<^sup>t"
  by (metis H1_H2_eq_design H2_H3_absorb Healthy_def' assms(1) assms(2))

theorem H1_H3_is_rdesign:
  assumes "P is H1" "P is H3"
  shows "P = pre\<^sub>D(P) \<turnstile>\<^sub>r post\<^sub>D(P)"
  by (metis H1_H2_is_rdesign H2_H3_absorb Healthy_def' assms)

theorem H1_H3_is_normal_design:
  assumes "P is H1" "P is H3"
  shows "P = \<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)"
  by (metis H1_H3_is_rdesign assms drop_pre_inv ndesign_def precond_equiv rdesign_H3_iff_pre)

abbreviation "H1_H3 p \<equiv> H1 (H3 p)"

notation H1_H3 ("\<^bold>N")

lemma H1_H3_comp: "H1_H3 = H1 \<circ> H3"
  by (auto)

lemma H1_H3_idempotent: "\<^bold>N (\<^bold>N P) = \<^bold>N P"
  by (simp add: H1_H3_commute H1_idem H3_idem)

lemma H1_H3_Idempotent: "Idempotent \<^bold>N"
  by (simp add: Idempotent_def H1_H3_idempotent)

lemma H1_H3_monotonic: "Monotonic \<^bold>N"
  by (simp add: H1_monotone H3_mono Monotonic_def)

lemma H1_H3_Continuous: "Continuous \<^bold>N"
  by (simp add: Continuous_comp H1_Continuous H1_H3_comp H3_Continuous)

lemma H1_H3_impl_H2: "P is H1_H3 \<Longrightarrow> P is H1_H2"
  by (metis H1_H2_commute H1_idem H2_H3_absorb Healthy_def')

lemma H1_H3_eq_design_d_comp: "H1 (H3 P) = ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t ;; II\<^sub>D)"
  by (metis H1_H2_eq_design H1_H3_commute H3_H2_absorb H3_def)

lemma H1_H3_eq_design: "H1 (H3 P) = (\<not> (P\<^sup>f ;; true)) \<turnstile> P\<^sup>t"
  apply (simp add: H1_H3_eq_design_d_comp skip_d_alt_def)
  apply (subst design_composition_subst)
  apply (simp_all add: usubst unrest)
  apply (rel_auto)
done

lemma H3_unrest_out_alpha_nok [unrest]:
  assumes "P is H1_H3"
  shows "out\<alpha> \<sharp> P\<^sup>f"
proof -
  have "P = (\<not> (P\<^sup>f ;; true)) \<turnstile> P\<^sup>t"
    by (metis H1_H3_eq_design Healthy_def assms)
  also have "out\<alpha> \<sharp> (...\<^sup>f)"
    by (simp add: design_def usubst unrest, rel_auto)
  finally show ?thesis .
qed

lemma H3_unrest_out_alpha [unrest]: "P is H1_H3 \<Longrightarrow> out\<alpha> \<sharp> pre\<^sub>D(P)"
  by (metis H1_H3_commute H1_H3_is_rdesign H1_idem Healthy_def' precond_equiv rdesign_H3_iff_pre)

lemma ndesign_H1_H3 [closure]: "p \<turnstile>\<^sub>n Q is \<^bold>N"
  by (simp add: H1_rdesign H3_def Healthy_def' ndesign_def unrest_pre_out\<alpha>)

lemma des_bot_H1_H3 [closure]: "\<bottom>\<^sub>D is \<^bold>N"
  by (metis H1_design H3_def Healthy_def' design_false_pre design_true_left_zero skip_d_alt_def)

lemma assigns_d_H1_H3 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>D is \<^bold>N"
  by (metis H1_rdesign H3_ndesign Healthy_def' aext_true assigns_d_def ndesign_def)

lemma seq_r_H1_H3_closed [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P ;; Q) is \<^bold>N"
  by (metis (no_types) H1_H2_eq_design H1_H3_eq_design_d_comp H1_H3_impl_H2 Healthy_def assms(1) assms(2) seq_r_H1_H2_closed seqr_assoc)

lemma wp_assigns_d [wp]: "\<langle>\<sigma>\<rangle>\<^sub>D wp\<^sub>D r = \<sigma> \<dagger> r"
  by (rel_auto)

theorem wpd_seq_r_H1_H3 [wp]:
  fixes P Q :: "'\<alpha> hrel_des"
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P ;; Q) wp\<^sub>D r = P wp\<^sub>D (Q wp\<^sub>D r)"
  by (metis H1_H3_commute H1_H3_is_normal_design H1_idem Healthy_def' assms(1) assms(2) wpnd_seq_r)

text {* If two normal designs have the same weakest precondition for any given postcondition, then
  the two designs are equivalent. *}

theorem wpd_eq_intro: "\<lbrakk> \<And> r. (p\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>1) wp\<^sub>D r = (p\<^sub>2 \<turnstile>\<^sub>n Q\<^sub>2) wp\<^sub>D r \<rbrakk> \<Longrightarrow> (p\<^sub>1 \<turnstile>\<^sub>n Q\<^sub>1) = (p\<^sub>2 \<turnstile>\<^sub>n Q\<^sub>2)"
apply (rel_simp robust; metis curry_conv)
done

theorem wpd_H3_eq_intro: "\<lbrakk> P is H1_H3; Q is H1_H3; \<And> r. P wp\<^sub>D r = Q wp\<^sub>D r \<rbrakk> \<Longrightarrow> P = Q"
  by (metis H1_H3_commute H1_H3_is_normal_design H3_idem Healthy_def' wpd_eq_intro)

subsection {* H4: Feasibility *}

theorem H4_idem:
  "H4(H4(P)) = H4(P)"
  by (pred_auto)

lemma is_H4_alt_def:
  "P is H4 \<longleftrightarrow> (P ;; true) = true"
  by (rel_auto)

lemma H4_assigns_d: "\<langle>\<sigma>\<rangle>\<^sub>D is H4"
proof -
  have "(\<langle>\<sigma>\<rangle>\<^sub>D ;; (false \<turnstile>\<^sub>r true\<^sub>h)) = (false \<turnstile>\<^sub>r true)"
    by (simp add: assigns_d_def rdesign_composition assigns_r_feasible)
  moreover have "... = true"
    by (rel_auto)
  ultimately show ?thesis
    using is_H4_alt_def by auto
qed

subsection {* UTP theories *}

typedecl DES
typedecl NDES

abbreviation "DES \<equiv> UTHY(DES, '\<alpha> des)"
abbreviation "NDES \<equiv> UTHY(NDES, '\<alpha> des)"

overloading
  des_hcond == "utp_hcond :: (DES, '\<alpha> des) uthy \<Rightarrow> ('\<alpha> des \<times> '\<alpha> des) health"
  des_unit == "utp_unit :: (DES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> hrel_des" (unchecked)

  ndes_hcond == "utp_hcond :: (NDES, '\<alpha> des) uthy \<Rightarrow> ('\<alpha> des \<times> '\<alpha> des) health"
  ndes_unit == "utp_unit :: (NDES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> hrel_des" (unchecked)

begin
  definition des_hcond :: "(DES, '\<alpha> des) uthy \<Rightarrow> ('\<alpha> des \<times> '\<alpha> des) health" where
  [upred_defs]: "des_hcond t = H1_H2"

  definition des_unit :: "(DES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> hrel_des" where
  [upred_defs]: "des_unit t = II\<^sub>D"

  definition ndes_hcond :: "(NDES, '\<alpha> des) uthy \<Rightarrow> ('\<alpha> des \<times> '\<alpha> des) health" where
  [upred_defs]: "ndes_hcond t = H1_H3"

  definition ndes_unit :: "(NDES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> hrel_des" where
  [upred_defs]: "ndes_unit t = II\<^sub>D"

end

interpretation des_utp_theory: utp_theory DES
  by (simp add: H1_H2_commute H1_idem H2_idem des_hcond_def utp_theory_def)

interpretation ndes_utp_theory: utp_theory NDES
  by (simp add: H1_H3_commute H1_idem H3_idem ndes_hcond_def utp_theory.intro)

interpretation des_left_unital: utp_theory_left_unital DES
  apply (unfold_locales)
  apply (simp_all add: des_hcond_def des_unit_def)
  using seq_r_H1_H2_closed apply blast
  apply (simp add: rdesign_is_H1_H2 skip_d_def)
  apply (metis H1_idem H1_left_unit Healthy_def')
done

interpretation ndes_unital: utp_theory_unital NDES
  apply (unfold_locales, simp_all add: ndes_hcond_def ndes_unit_def)
  using seq_r_H1_H3_closed apply blast
  apply (metis H1_rdesign H3_def Healthy_def' design_skip_idem skip_d_def)
  apply (metis H1_idem H1_left_unit Healthy_def')
  apply (metis H1_H3_commute H3_def H3_idem Healthy_def')
done

interpretation design_theory_continuous: utp_theory_continuous DES
  rewrites "\<And> P. P \<in> carrier (uthy_order DES) \<longleftrightarrow> P is \<^bold>H"
  and "carrier (uthy_order DES) \<rightarrow> carrier (uthy_order DES) \<equiv> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
  and "le (uthy_order DES) = op \<sqsubseteq>"
  and "eq (uthy_order DES) = op ="
  by (unfold_locales, simp_all add: des_hcond_def H1_H2_Continuous utp_order_def)

interpretation normal_design_theory_mono: utp_theory_continuous NDES
  rewrites "\<And> P. P \<in> carrier (uthy_order NDES) \<longleftrightarrow> P is \<^bold>N"
  and "carrier (uthy_order NDES) \<rightarrow> carrier (uthy_order NDES) \<equiv> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  and "le (uthy_order NDES) = op \<sqsubseteq>"
  and "eq (uthy_order NDES) = op ="
  by (unfold_locales, simp_all add: ndes_hcond_def H1_H3_Continuous utp_order_def)

lemma design_lat_top: "\<^bold>\<top>\<^bsub>DES\<^esub> = \<^bold>H(false)"
  by (simp add: design_theory_continuous.healthy_top, simp add: des_hcond_def)

lemma design_lat_bottom: "\<^bold>\<bottom>\<^bsub>DES\<^esub> = \<^bold>H(true)"
  by (simp add: design_theory_continuous.healthy_bottom, simp add: des_hcond_def)

abbreviation design_lfp :: "('\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des) \<Rightarrow> '\<alpha> hrel_des" ("\<mu>\<^sub>D") where
"\<mu>\<^sub>D F \<equiv> \<mu>\<^bsub>uthy_order DES\<^esub> F"

abbreviation design_gfp :: "('\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des) \<Rightarrow> '\<alpha> hrel_des" ("\<nu>\<^sub>D") where
"\<nu>\<^sub>D F \<equiv> \<nu>\<^bsub>uthy_order DES\<^esub> F"

thm design_theory_continuous.GFP_unfold
thm design_theory_continuous.LFP_unfold

text {* We also set up local variables for designs. *}

overloading
  des_pvar == "pvar :: (DES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> \<Longrightarrow> '\<alpha> des"
  des_assigns == "pvar_assigns :: (DES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> hrel_des"
  ndes_pvar == "pvar :: (NDES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> \<Longrightarrow> '\<alpha> des"
  ndes_assigns == "pvar_assigns :: (NDES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> hrel_des"
begin
  definition des_pvar :: "(DES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> \<Longrightarrow> '\<alpha> des" where
  [upred_defs]: "des_pvar T = \<Sigma>\<^sub>D"
  definition des_assigns :: "(DES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> hrel_des" where
  [upred_defs]: "des_assigns T \<sigma> = \<langle>\<sigma>\<rangle>\<^sub>D"
  definition ndes_pvar :: "(NDES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> \<Longrightarrow> '\<alpha> des" where
  [upred_defs]: "ndes_pvar T = \<Sigma>\<^sub>D"
  definition ndes_assigns :: "(NDES, '\<alpha> des) uthy \<Rightarrow> '\<alpha> usubst \<Rightarrow> '\<alpha> hrel_des" where
  [upred_defs]: "ndes_assigns T \<sigma> = \<langle>\<sigma>\<rangle>\<^sub>D"

end

interpretation des_prog_var: utp_prog_var "UTHY(DES, '\<alpha> des)" "TYPE('\<alpha>)"
  rewrites "\<H>\<^bsub>DES\<^esub> = \<^bold>H"
  apply (unfold_locales, simp_all add: des_pvar_def des_assigns_def des_hcond_def)
  apply (simp add: assigns_d_def rdesign_is_H1_H2)
  apply (simp add: assigns_d_comp_ext assigns_d_is_H1_H2)
  apply (rel_auto)
done

interpretation ndes_prog_var: utp_prog_var "UTHY(NDES, '\<alpha> des)" "TYPE('\<alpha>)"
  rewrites "\<H>\<^bsub>NDES\<^esub> = \<^bold>N"
  apply (unfold_locales, simp_all add: ndes_pvar_def ndes_assigns_def ndes_hcond_def)
  apply (simp add: assigns_d_H1_H3)
  apply (rel_auto)
done

interpretation des_local_var: utp_local_var "UTHY(DES, '\<alpha> des)" "TYPE('\<alpha>)"
  rewrites "\<H>\<^bsub>DES\<^esub> = \<^bold>H"
  by (unfold_locales, simp_all add: des_unit_def des_assigns_def des_hcond_def)

interpretation ndes_local_var: utp_local_var "UTHY(NDES, '\<alpha> des)" "TYPE('\<alpha>)"
  rewrites "\<H>\<^bsub>NDES\<^esub> = \<^bold>N"
  by (unfold_locales, simp_all add: ndes_unit_def ndes_assigns_def ndes_hcond_def)

text {* Weakest precondition laws for design variable scopes *}

lemma wpd_var_begin [wp]:
  fixes x :: "'a list \<Longrightarrow> '\<alpha>" and r :: "'\<alpha> upred"
  shows "(var_begin NDES x) wp\<^sub>D r = r\<lbrakk>\<langle>\<guillemotleft>undefined\<guillemotright>\<rangle> ^\<^sub>u &x/x\<rbrakk>"
  by (simp add: var_begin_def ndes_assigns_def wp)

lemma wpd_var_end [wp]:
  fixes x :: "'a list \<Longrightarrow> '\<alpha>" and r :: "'\<alpha> upred"
  shows "(var_end NDES x) wp\<^sub>D r = r\<lbrakk>tail\<^sub>u(&x)/x\<rbrakk>"
  by (simp add: var_end_def ndes_assigns_def wp)

text {* Example Galois connection between designs and relations. Based on Jim's example in COMPASS
        deliverable D23.5. *}

definition [upred_defs]: "Des(R) = \<^bold>H(\<lceil>R\<rceil>\<^sub>D \<and> $ok\<acute>)"
definition [upred_defs]: "Rel(D) = \<lfloor>D\<lbrakk>true,true/$ok,$ok\<acute>\<rbrakk>\<rfloor>\<^sub>D"

lemma Des_design: "Des(R) = true \<turnstile>\<^sub>r R"
  by (rel_auto)

lemma Rel_design: "Rel(P \<turnstile>\<^sub>r Q) = (P \<Rightarrow> Q)"
  by (rel_auto)

interpretation Des_Rel_coretract:
  coretract "DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL"
  rewrites
    "\<And> x. x \<in> carrier \<X>\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = (x is \<^bold>H)" and
    "\<And> x. x \<in> carrier \<Y>\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = True" and
    "\<pi>\<^sub>*\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = Des" and
    "\<pi>\<^sup>*\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = Rel" and
    "le \<X>\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = op \<sqsubseteq>" and
    "le \<Y>\<^bsub>DES \<leftarrow>\<langle>Des,Rel\<rangle>\<rightarrow> REL\<^esub> = op \<sqsubseteq>"
proof (unfold_locales, simp_all add: rel_hcond_def des_hcond_def)
  show "\<And>x. x is id"
    by (simp add: Healthy_def)
next
  show "Rel \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>id\<rbrakk>\<^sub>H"
    by (auto simp add: Rel_def rel_hcond_def Healthy_def)
next
  show "Des \<in> \<lbrakk>id\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
    by (auto simp add: Des_def des_hcond_def Healthy_def H1_H2_commute H1_idem H2_idem)
next
  fix R :: "'a hrel"
  show "R \<sqsubseteq> Rel (Des R)"
    by (simp add: Des_design Rel_design)
next
  fix R :: "'a hrel" and D :: "'a hrel_des"
  assume a: "D is \<^bold>H"
  then obtain D\<^sub>1 D\<^sub>2 where D: "D = D\<^sub>1 \<turnstile>\<^sub>r D\<^sub>2"
    by (metis H1_H2_commute H1_H2_is_rdesign H1_idem Healthy_def')
  show "(Rel D \<sqsubseteq> R) = (D \<sqsubseteq> Des R)"
  proof -
    have "(D \<sqsubseteq> Des R) = (D\<^sub>1 \<turnstile>\<^sub>r D\<^sub>2 \<sqsubseteq> true \<turnstile>\<^sub>r R)"
      by (simp add: D Des_design)
    also have "... = `D\<^sub>1 \<and> R \<Rightarrow> D\<^sub>2`"
      by (simp add: rdesign_refinement)
    also have "... = ((D\<^sub>1 \<Rightarrow> D\<^sub>2) \<sqsubseteq> R)"
      by (rel_auto)
    also have "... = (Rel D \<sqsubseteq> R)"
      by (simp add: D Rel_design)
    finally show ?thesis ..
  qed
qed

text {* From this interpretation we gain many Galois theorems. Some require simplification to
        remove superfluous assumptions. *}

thm Des_Rel_coretract.deflation[simplified]
thm Des_Rel_coretract.inflation
thm Des_Rel_coretract.upper_comp[simplified]
thm Des_Rel_coretract.lower_comp
end