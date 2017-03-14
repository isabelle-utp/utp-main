section {* Alphabet manipulation *}

theory utp_alphabet
  imports
    utp_pred
begin

named_theorems alpha

method alpha_tac = (simp add: alpha unrest)?

subsection {* Alphabet extension *}

text {* Extend an alphabet by application of a lens that demonstrates how the smaller alphabet
  ($\beta$) injects into the larger alphabet ($\alpha$). *}

lift_definition aext :: "('a, '\<beta>) uexpr \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> ('a, '\<alpha>) uexpr" (infixr "\<oplus>\<^sub>p" 95)
is "\<lambda> P x b. P (get\<^bsub>x\<^esub> b)" .

update_uexpr_rep_eq_thms

lemma aext_id [alpha]: "P \<oplus>\<^sub>p 1\<^sub>L = P"
  by (pred_auto)

lemma aext_lit [alpha]: "\<guillemotleft>v\<guillemotright> \<oplus>\<^sub>p a = \<guillemotleft>v\<guillemotright>"
  by (pred_auto)

lemma aext_zero [alpha]: "0 \<oplus>\<^sub>p a = 0"
  by (pred_auto)

lemma aext_one [alpha]: "1 \<oplus>\<^sub>p a = 1"
  by (pred_auto)

lemma aext_numeral [alpha]: "numeral n \<oplus>\<^sub>p a = numeral n"
  by (pred_auto)

lemma aext_uop [alpha]: "uop f u \<oplus>\<^sub>p a = uop f (u \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_bop [alpha]: "bop f u v \<oplus>\<^sub>p a = bop f (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_trop [alpha]: "trop f u v w \<oplus>\<^sub>p a = trop f (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a) (w \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_qtop [alpha]: "qtop f u v w x \<oplus>\<^sub>p a = qtop f (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a) (w \<oplus>\<^sub>p a) (x \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_plus [alpha]:
  "(x + y) \<oplus>\<^sub>p a = (x \<oplus>\<^sub>p a) + (y \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_minus [alpha]:
  "(x - y) \<oplus>\<^sub>p a = (x \<oplus>\<^sub>p a) - (y \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_uminus [simp]:
  "(- x) \<oplus>\<^sub>p a = - (x \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_times [alpha]:
  "(x * y) \<oplus>\<^sub>p a = (x \<oplus>\<^sub>p a) * (y \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_divide [alpha]:
  "(x / y) \<oplus>\<^sub>p a = (x \<oplus>\<^sub>p a) / (y \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_var [alpha]:
  "var x \<oplus>\<^sub>p a = var (x ;\<^sub>L a)"
  by (pred_auto)

lemma aext_ulambda [alpha]: "((\<lambda> x \<bullet> P(x)) \<oplus>\<^sub>p a) = (\<lambda> x \<bullet> P(x) \<oplus>\<^sub>p a)"
  by (pred_auto)

lemma aext_true [alpha]: "true \<oplus>\<^sub>p a = true"
  by (pred_auto)

lemma aext_false [alpha]: "false \<oplus>\<^sub>p a = false"
  by (pred_auto)

lemma aext_not [alpha]: "(\<not> P) \<oplus>\<^sub>p x = (\<not> (P \<oplus>\<^sub>p x))"
  by (pred_auto)

lemma aext_and [alpha]: "(P \<and> Q) \<oplus>\<^sub>p x = (P \<oplus>\<^sub>p x \<and> Q \<oplus>\<^sub>p x)"
  by (pred_auto)

lemma aext_or [alpha]: "(P \<or> Q) \<oplus>\<^sub>p x = (P \<oplus>\<^sub>p x \<or> Q \<oplus>\<^sub>p x)"
  by (pred_auto)

lemma aext_imp [alpha]: "(P \<Rightarrow> Q) \<oplus>\<^sub>p x = (P \<oplus>\<^sub>p x \<Rightarrow> Q \<oplus>\<^sub>p x)"
  by (pred_auto)

lemma aext_iff [alpha]: "(P \<Leftrightarrow> Q) \<oplus>\<^sub>p x = (P \<oplus>\<^sub>p x \<Leftrightarrow> Q \<oplus>\<^sub>p x)"
  by (pred_auto)

lemma unrest_aext [unrest]:
  "\<lbrakk> mwb_lens a; x \<sharp> p \<rbrakk> \<Longrightarrow> unrest (x ;\<^sub>L a) (p \<oplus>\<^sub>p a)"
  by (transfer, simp add: lens_comp_def)

lemma unrest_aext_indep [unrest]:
  "a \<bowtie> b \<Longrightarrow> b \<sharp> (p \<oplus>\<^sub>p a)"
  by pred_auto

subsection {* Alphabet restriction *}

text {* Restrict an alphabet by application of a lens that demonstrates how the smaller alphabet
  ($\beta$) injects into the larger alphabet ($\alpha$). Unlike extension, this operation
  can lose information if the expressions refers to variables in the larger alphabet. *}

lift_definition arestr :: "('a, '\<alpha>) uexpr \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> ('a, '\<beta>) uexpr" (infixr "\<restriction>\<^sub>p" 90)
is "\<lambda> P x b. P (create\<^bsub>x\<^esub> b)" .

update_uexpr_rep_eq_thms

lemma arestr_id [alpha]: "P \<restriction>\<^sub>p 1\<^sub>L = P"
  by (pred_auto)

lemma arestr_aext [simp]: "mwb_lens a \<Longrightarrow> (P \<oplus>\<^sub>p a) \<restriction>\<^sub>p a = P"
  by (pred_auto)

text {* If an expression's alphabet can be divided into two disjoint sections and the expression
  does not depend on the second half then restricting the expression to the first half is
  lossless. *}

lemma aext_arestr [alpha]:
  assumes "mwb_lens a" "bij_lens (a +\<^sub>L b)" "a \<bowtie> b" "b \<sharp> P"
  shows "(P \<restriction>\<^sub>p a) \<oplus>\<^sub>p a = P"
proof -
  from assms(2) have "1\<^sub>L \<subseteq>\<^sub>L a +\<^sub>L b"
    by (simp add: bij_lens_equiv_id lens_equiv_def)
  with assms(1,3,4) show ?thesis
    apply (auto simp add: alpha_of_def id_lens_def lens_plus_def sublens_def lens_comp_def prod.case_eq_if)
    apply (pred_simp)
    apply (metis lens_indep_comm mwb_lens_weak weak_lens.put_get)
  done
qed

lemma arestr_lit [alpha]: "\<guillemotleft>v\<guillemotright> \<restriction>\<^sub>p a = \<guillemotleft>v\<guillemotright>"
  by (pred_auto)

lemma arestr_zero [alpha]: "0 \<restriction>\<^sub>p a = 0"
  by (pred_auto)

lemma arestr_one [alpha]: "1 \<restriction>\<^sub>p a = 1"
  by (pred_auto)

lemma arestr_numeral [alpha]: "numeral n \<restriction>\<^sub>p a = numeral n"
  by (pred_auto)

lemma arestr_var [alpha]:
  "var x \<restriction>\<^sub>p a = var (x /\<^sub>L a)"
  by (pred_auto)

lemma arestr_true [alpha]: "true \<restriction>\<^sub>p a = true"
  by (pred_auto)

lemma arestr_false [alpha]: "false \<restriction>\<^sub>p a = false"
  by (pred_auto)

lemma arestr_not [alpha]: "(\<not> P)\<restriction>\<^sub>pa = (\<not> (P\<restriction>\<^sub>pa))"
  by (pred_auto)

lemma arestr_and [alpha]: "(P \<and> Q)\<restriction>\<^sub>px = (P\<restriction>\<^sub>px \<and> Q\<restriction>\<^sub>px)"
  by (pred_auto)

lemma arestr_or [alpha]: "(P \<or> Q)\<restriction>\<^sub>px = (P\<restriction>\<^sub>px \<or> Q\<restriction>\<^sub>px)"
  by (pred_auto)

lemma arestr_imp [alpha]: "(P \<Rightarrow> Q)\<restriction>\<^sub>px = (P\<restriction>\<^sub>px \<Rightarrow> Q\<restriction>\<^sub>px)"
  by (pred_auto)

subsection {* Alphabet lens laws *}

lemma alpha_in_var [alpha]: "x ;\<^sub>L fst\<^sub>L = in_var x"
  by (simp add: in_var_def)

lemma alpha_out_var [alpha]: "x ;\<^sub>L snd\<^sub>L = out_var x"
  by (simp add: out_var_def)

lemma in_var_prod_lens [alpha]:
  "wb_lens Y \<Longrightarrow> in_var x ;\<^sub>L (X \<times>\<^sub>L Y) = in_var (x ;\<^sub>L X)"
  by (simp add: in_var_def prod_as_plus lens_comp_assoc fst_lens_plus)

lemma out_var_prod_lens [alpha]:
  "wb_lens X \<Longrightarrow> out_var x ;\<^sub>L (X \<times>\<^sub>L Y) = out_var (x ;\<^sub>L Y)"
  apply (simp add: out_var_def prod_as_plus lens_comp_assoc)
  apply (subst snd_lens_plus)
  using comp_wb_lens fst_vwb_lens vwb_lens_wb apply blast
  apply (simp add: alpha_in_var alpha_out_var)
  apply (simp)
done

subsection {* Alphabet coercion *}

definition id_on :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>" where
[upred_defs]: "id_on x = (\<lambda> s. undefined \<oplus>\<^sub>L s on x)"

definition alpha_coerce :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred"
where [upred_defs]: "alpha_coerce x P = id_on x \<dagger> P"

syntax
  "_alpha_coerce" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("!\<^sub>\<alpha> _ \<bullet> _" [0, 10] 10)

translations
  "_alpha_coerce P x" == "CONST alpha_coerce P x"

subsection {* Substitution alphabet extension *}

definition subst_ext :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> '\<beta> usubst" (infix "\<oplus>\<^sub>s" 65) where
[upred_defs]: "\<sigma> \<oplus>\<^sub>s x = (\<lambda> s. put\<^bsub>x\<^esub> s (\<sigma> (get\<^bsub>x\<^esub> s)))"

lemma id_subst_ext [usubst,alpha]:
  "wb_lens x \<Longrightarrow> id \<oplus>\<^sub>s x = id"
  by pred_auto

lemma upd_subst_ext [alpha]:
  "vwb_lens x \<Longrightarrow> \<sigma>(y \<mapsto>\<^sub>s v) \<oplus>\<^sub>s x = (\<sigma> \<oplus>\<^sub>s x)(&x:y \<mapsto>\<^sub>s v \<oplus>\<^sub>p x)"
  by pred_auto

lemma apply_subst_ext [alpha]:
  "vwb_lens x \<Longrightarrow> (\<sigma> \<dagger> e) \<oplus>\<^sub>p x = (\<sigma> \<oplus>\<^sub>s x) \<dagger> (e \<oplus>\<^sub>p x)"
  by (pred_auto)

lemma aext_upred_eq [alpha]:
  "((e =\<^sub>u f) \<oplus>\<^sub>p a) = ((e \<oplus>\<^sub>p a) =\<^sub>u (f \<oplus>\<^sub>p a))"
  by (pred_auto)

subsection {* Substitution alphabet restriction *}

definition subst_res :: "'\<alpha> usubst \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> usubst" (infix "\<restriction>\<^sub>s" 65) where
[upred_defs]: "\<sigma> \<restriction>\<^sub>s x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> (create\<^bsub>x\<^esub> s)))"

lemma id_subst_res [alpha,usubst]:
  "mwb_lens x \<Longrightarrow> id \<restriction>\<^sub>s x = id"
  by pred_auto

lemma upd_subst_res [alpha]:
  "mwb_lens x \<Longrightarrow> \<sigma>(&x:y \<mapsto>\<^sub>s v) \<restriction>\<^sub>s x = (\<sigma> \<restriction>\<^sub>s x)(&y \<mapsto>\<^sub>s v \<restriction>\<^sub>p x)"
  by (pred_auto)

lemma subst_ext_res [alpha,usubst]:
  "mwb_lens x \<Longrightarrow> (\<sigma> \<oplus>\<^sub>s x) \<restriction>\<^sub>s x = \<sigma>"
  by (pred_auto)

lemma unrest_subst_alpha_ext [unrest]:
  "x \<bowtie> y \<Longrightarrow> x \<sharp> (P \<oplus>\<^sub>s y)"
  by (pred_simp robust, metis lens_indep_def)
end