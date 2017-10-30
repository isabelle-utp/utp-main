section {* Alphabet Manipulation *}

theory utp_alphabet
  imports
    utp_pred utp_event
begin

subsection {* Preliminaries *}
  
text {* Alphabets are simply types that characterise the state-space of an expression. Thus
  the Isabelle type system ensures that predicates cannot refer to variables not in the alphabet
  as this would be a type error. Often one would like to add or remove additional variables, for 
  example if we wish to have a predicate which ranges only a smaller state-space, and then
  lift it into a predicate over a larger one. This is useful, for example, when dealing with
  relations which refer only to undashed variables (conditions) since we can use the type system
  to ensure well-formedness. 

  In this theory we will set up operators for extending and contracting and alphabet. 
  We first set up a theorem attribute for alphabet laws and a tactic. *}
  
named_theorems alpha

method alpha_tac = (simp add: alpha unrest)?

subsection {* Alphabet Extrusion *}

text {* Alter an alphabet by application of a lens that demonstrates how the smaller alphabet
  ($\beta$) injects into the larger alphabet ($\alpha$). This changes the type of the expression
  so it is parametrised over the large alphabet. We do this by using the lens \emph{get}
  function to extract the smaller state binding, and then apply this to the expression. 

  We call this "extrusion" rather than "extension" because if the extension lens is bijective
  then it does not extend the alphabet. Nevertheless, it does have an effect because the type
  will be different which can be useful when converting predicates with equivalent alphabets. *}

lift_definition aext :: "('a, '\<beta>) uexpr \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> ('a, '\<alpha>) uexpr" (infixr "\<oplus>\<^sub>p" 95)
is "\<lambda> P x b. P (get\<^bsub>x\<^esub> b)" .

update_uexpr_rep_eq_thms

text {* Next we prove some of the key laws. Extending an alphabet twice is equivalent to extending
  by the composition of the two lenses. *}
  
lemma aext_twice: "(P \<oplus>\<^sub>p a) \<oplus>\<^sub>p b = P \<oplus>\<^sub>p (a ;\<^sub>L b)"
  by (pred_auto)

text {* The bijective @{term "1\<^sub>L"} lens identifies the source and view types. Thus an alphabet
  extension using this has no effect. *}
    
lemma aext_id [alpha]: "P \<oplus>\<^sub>p 1\<^sub>L = P"
  by (pred_auto)

text {* Literals do not depend on any variables, and thus applying an alphabet extension only
  alters the predicate's type, and not its valuation .*}
    
lemma aext_lit [alpha]: "\<guillemotleft>v\<guillemotright> \<oplus>\<^sub>p a = \<guillemotleft>v\<guillemotright>"
  by (pred_auto)

lemma aext_zero [alpha]: "0 \<oplus>\<^sub>p a = 0"
  by (pred_auto)

lemma aext_one [alpha]: "1 \<oplus>\<^sub>p a = 1"
  by (pred_auto)

lemma aext_numeral [alpha]: "numeral n \<oplus>\<^sub>p a = numeral n"
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
    
lemma aext_shAll [alpha]: "(\<^bold>\<forall> x \<bullet> P(x)) \<oplus>\<^sub>p a = (\<^bold>\<forall> x \<bullet> P(x) \<oplus>\<^sub>p a)"
  by (pred_auto)
    
lemma aext_event [alpha]: "(c\<cdot>v)\<^sub>u \<oplus>\<^sub>p a = (c\<cdot>v \<oplus>\<^sub>p a)\<^sub>u"
  by (pred_auto)
    
text {* Alphabet extension distributes through the function liftings. *}
    
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

text {* Extending a variable expression over $x$ is equivalent to composing $x$ with the alphabet,
  thus effectively yielding a variable whose source is the large alphabet. *}
    
lemma aext_var [alpha]:
  "var x \<oplus>\<^sub>p a = var (x ;\<^sub>L a)"
  by (pred_auto)

lemma aext_ulambda [alpha]: "((\<lambda> x \<bullet> P(x)) \<oplus>\<^sub>p a) = (\<lambda> x \<bullet> P(x) \<oplus>\<^sub>p a)"
  by (pred_auto)

text {* Alphabet extension is monotonic and continuous. *}
    
lemma aext_mono: "P \<sqsubseteq> Q \<Longrightarrow> P \<oplus>\<^sub>p a \<sqsubseteq> Q \<oplus>\<^sub>p a"
  by (pred_auto)

lemma aext_cont [alpha]: "vwb_lens a \<Longrightarrow> (\<Sqinter> A) \<oplus>\<^sub>p a = (\<Sqinter> P\<in>A.  P \<oplus>\<^sub>p a)"
  by (pred_simp)
   
text {* If a variable is unrestricted in a predicate, then the extended variable is unrestricted
  in the predicate with an alphabet extension. *}
    
lemma unrest_aext [unrest]:
  "\<lbrakk> mwb_lens a; x \<sharp> p \<rbrakk> \<Longrightarrow> unrest (x ;\<^sub>L a) (p \<oplus>\<^sub>p a)"
  by (transfer, simp add: lens_comp_def)

text {* If a given variable (or alphabet) $b$ is independent of the extension lens $a$, that is, it is
  outside the original state-space of $p$, then it follows that once $p$ is extended by $a$ then
  $b$ cannot be restricted. *}
    
lemma unrest_aext_indep [unrest]:
  "a \<bowtie> b \<Longrightarrow> b \<sharp> (p \<oplus>\<^sub>p a)"
  by pred_auto
    
subsection {* Alphabet Restriction *}

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
  loss-less. *}

lemma aext_arestr [alpha]:
  assumes "mwb_lens a" "bij_lens (a +\<^sub>L b)" "a \<bowtie> b" "b \<sharp> P"
  shows "(P \<restriction>\<^sub>p a) \<oplus>\<^sub>p a = P"
proof -
  from assms(2) have "1\<^sub>L \<subseteq>\<^sub>L a +\<^sub>L b"
    by (simp add: bij_lens_equiv_id lens_equiv_def)
  with assms(1,3,4) show ?thesis
    apply (auto simp add: id_lens_def lens_plus_def sublens_def lens_comp_def prod.case_eq_if)
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

subsection {* Alphabet Lens Laws *}

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

subsection {* Substitution Alphabet Extension *}

text {* This allows us to extend the alphabet of a substitution, in a similar way to expressions. *}
  
definition subst_ext :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> '\<beta> usubst" (infix "\<oplus>\<^sub>s" 65) where
[upred_defs]: "\<sigma> \<oplus>\<^sub>s x = (\<lambda> s. put\<^bsub>x\<^esub> s (\<sigma> (get\<^bsub>x\<^esub> s)))"

lemma id_subst_ext [usubst]:
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

subsection {* Substitution Alphabet Restriction *}

text {* This allows us to reduce the alphabet of a substitution, in a similar way to expressions. *}
  
definition subst_res :: "'\<alpha> usubst \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> usubst" (infix "\<restriction>\<^sub>s" 65) where
[upred_defs]: "\<sigma> \<restriction>\<^sub>s x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> (create\<^bsub>x\<^esub> s)))"

lemma id_subst_res [usubst]:
  "mwb_lens x \<Longrightarrow> id \<restriction>\<^sub>s x = id"
  by pred_auto

lemma upd_subst_res [alpha]:
  "mwb_lens x \<Longrightarrow> \<sigma>(&x:y \<mapsto>\<^sub>s v) \<restriction>\<^sub>s x = (\<sigma> \<restriction>\<^sub>s x)(&y \<mapsto>\<^sub>s v \<restriction>\<^sub>p x)"
  by (pred_auto)

lemma subst_ext_res [usubst]:
  "mwb_lens x \<Longrightarrow> (\<sigma> \<oplus>\<^sub>s x) \<restriction>\<^sub>s x = \<sigma>"
  by (pred_auto)

lemma unrest_subst_alpha_ext [unrest]:
  "x \<bowtie> y \<Longrightarrow> x \<sharp> (P \<oplus>\<^sub>s y)"
  by (pred_simp robust, metis lens_indep_def)
end