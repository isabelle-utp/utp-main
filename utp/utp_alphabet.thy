section {* Alphabet manipulation *}

theory utp_alphabet
  imports 
    utp_pred
    utp_unrest
begin

named_theorems alpha

method alpha_tac = (simp add: alpha unrest)?

subsection {* Alphabet extension *}

text {* Extend an alphabet by application of a lens that demonstrates how the smaller alphabet
  ($\beta$) injects into the larger alphabet ($\alpha$). *}

lift_definition aext :: "('a, '\<beta>) uexpr \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> ('a, '\<alpha>) uexpr" (infixr "\<oplus>\<^sub>p" 95)
is "\<lambda> P x b. P (get\<^bsub>x\<^esub> b)" .

lemma aext_id [alpha]: "P \<oplus>\<^sub>p 1\<^sub>L = P"
  by (pred_tac)

lemma aext_lit [alpha]: "\<guillemotleft>v\<guillemotright> \<oplus>\<^sub>p a = \<guillemotleft>v\<guillemotright>"
  by (pred_tac)

lemma aext_uop [alpha]: "uop f u \<oplus>\<^sub>p a = uop f (u \<oplus>\<^sub>p a)"
  by (pred_tac)

lemma aext_bop [alpha]: "bop f u v \<oplus>\<^sub>p a = bop f (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a)"
  by (pred_tac)

lemma aext_trop [alpha]: "trop f u v w \<oplus>\<^sub>p a = trop f (u \<oplus>\<^sub>p a) (v \<oplus>\<^sub>p a) (w \<oplus>\<^sub>p a)"
  by (pred_tac)

lemma aext_plus [alpha]:
  "(x + y) \<oplus>\<^sub>p a = (x \<oplus>\<^sub>p a) + (y \<oplus>\<^sub>p a)" 
  by (pred_tac)

lemma aext_minus [alpha]:
  "(x - y) \<oplus>\<^sub>p a = (x \<oplus>\<^sub>p a) - (y \<oplus>\<^sub>p a)"
  by (pred_tac)

lemma aext_uminus [simp]:
  "(- x) \<oplus>\<^sub>p a = - (x \<oplus>\<^sub>p a)"
  by (pred_tac)

lemma aext_times [alpha]:
  "(x * y) \<oplus>\<^sub>p a = (x \<oplus>\<^sub>p a) * (y \<oplus>\<^sub>p a)"
  by (pred_tac)

lemma aext_divide [alpha]:
  "(x / y) \<oplus>\<^sub>p a = (x \<oplus>\<^sub>p a) / (y \<oplus>\<^sub>p a)"
  by (pred_tac)

lemma aext_var [alpha]:
  "var x \<oplus>\<^sub>p a = var (x ;\<^sub>L a)"
  by (pred_tac)

lemma aext_true [alpha]: "true \<oplus>\<^sub>p a = true"
  by (pred_tac)

lemma aext_false [alpha]: "false \<oplus>\<^sub>p a = false"
  by (pred_tac)

lemma aext_not [alpha]: "(\<not> P) \<oplus>\<^sub>p x = (\<not> (P \<oplus>\<^sub>p x))"
  by (pred_tac)

lemma aext_and [alpha]: "(P \<and> Q) \<oplus>\<^sub>p x = (P \<oplus>\<^sub>p x \<and> Q \<oplus>\<^sub>p x)"
  by (pred_tac)

lemma aext_or [alpha]: "(P \<or> Q) \<oplus>\<^sub>p x = (P \<oplus>\<^sub>p x \<or> Q \<oplus>\<^sub>p x)"
  by (pred_tac) 

lemma aext_imp [alpha]: "(P \<Rightarrow> Q) \<oplus>\<^sub>p x = (P \<oplus>\<^sub>p x \<Rightarrow> Q \<oplus>\<^sub>p x)"
  by (pred_tac) 

lemma aext_iff [alpha]: "(P \<Leftrightarrow> Q) \<oplus>\<^sub>p x = (P \<oplus>\<^sub>p x \<Leftrightarrow> Q \<oplus>\<^sub>p x)"
  by (pred_tac)

lemma unrest_aext [unrest]:
  "\<lbrakk> mwb_lens a; x \<sharp> p \<rbrakk> \<Longrightarrow> unrest (x ;\<^sub>L a) (p \<oplus>\<^sub>p a)"
  by (transfer, simp add: lens_comp_def)

lemma unrest_aext_indep [unrest]:
  "a \<bowtie> b \<Longrightarrow> b \<sharp> (p \<oplus>\<^sub>p a)"
  by pred_tac

subsection {* Alphabet restriction *}

text {* Restrict an alphabet by application of a lens that demonstrates how the smaller alphabet
  ($\beta$) injects into the larger alphabet ($\alpha$). Unlike extension, this operation
  can lose information if the expressions refers to variables in the larger alphabet. *}

lift_definition arestr :: "('a, '\<alpha>) uexpr \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> ('a, '\<beta>) uexpr" (infixr "\<restriction>\<^sub>p" 90)
is "\<lambda> P x b. P (create\<^bsub>x\<^esub> b)" .

lemma arestr_id [alpha]: "P \<restriction>\<^sub>p 1\<^sub>L = P"
  by (pred_tac)

lemma arestr_aext [alpha]: "mwb_lens a \<Longrightarrow> (P \<oplus>\<^sub>p a) \<restriction>\<^sub>p a = P"
  by (pred_tac)

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
    apply (pred_tac)
    apply (metis lens_indep_comm mwb_lens_weak weak_lens.put_get)
  done
qed

lemma arestr_lit [alpha]: "\<guillemotleft>v\<guillemotright> \<restriction>\<^sub>p a = \<guillemotleft>v\<guillemotright>"
  by (pred_tac)

lemma arestr_true [alpha]: "true \<restriction>\<^sub>p a = true"
  by (pred_tac)

lemma arestr_false [alpha]: "false \<restriction>\<^sub>p a = false"
  by (pred_tac)

lemma arestr_not [alpha]: "(\<not> P)\<restriction>\<^sub>pa = (\<not> (P\<restriction>\<^sub>pa))"
  by (pred_tac)

lemma arestr_and [alpha]: "(P \<and> Q)\<restriction>\<^sub>px = (P\<restriction>\<^sub>px \<and> Q\<restriction>\<^sub>px)"
  by (pred_tac)

lemma arestr_or [alpha]: "(P \<or> Q)\<restriction>\<^sub>px = (P\<restriction>\<^sub>px \<or> Q\<restriction>\<^sub>px)"
  by (pred_tac)

lemma arestr_imp [alpha]: "(P \<Rightarrow> Q)\<restriction>\<^sub>px = (P\<restriction>\<^sub>px \<Rightarrow> Q\<restriction>\<^sub>px)"
  by (pred_tac)

subsection {* Alphabet lens laws *}

lemma alpha_in_var [alpha]: "x ;\<^sub>L fst\<^sub>L = in_var x"
  by (simp add: in_var_def)

lemma alpha_out_var [alpha]: "x ;\<^sub>L snd\<^sub>L = out_var x"
  by (simp add: out_var_def)

end
