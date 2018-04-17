section \<open> Syntax and Translations for Event Prefix \<close>

theory utp_circus_prefix
  imports "UTP-Stateful-Failures.utp_sf_rdes"
begin

syntax
  "_simple_prefix" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>\<rightarrow> _" [81, 80] 80)

translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a\<guillemotright> P"

text {* We next configure a syntax for mixed prefixes. *}

nonterminal prefix_elem' and mixed_prefix'

syntax "_end_prefix" :: "prefix_elem' \<Rightarrow> mixed_prefix'" ("_")

text {* Input Prefix: @{text "\<dots>?(x)"} *}

syntax "_simple_input_prefix" :: "id \<Rightarrow> prefix_elem'"  ("?'(_')")

text {* Input Prefix with Constraint: @{text "\<dots>?(x : P)"} *}

syntax "_input_prefix" :: "id \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> prefix_elem'" ("?'(_ :/ _')")

text {* Output Prefix: @{text "\<dots>![v]e"} *}

text {* A variable name must currently be provided for outputs, too. Fix?! *}

syntax "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")
syntax "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" (".'(_')")

syntax (output) "_output_prefix_pp" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")

syntax
  "_prefix_aux" :: "pttrn \<Rightarrow> logic \<Rightarrow> prefix_elem'"

text {* Mixed-Prefix Action: @{text "c\<dots>(prefix) \<^bold>\<rightarrow> A"} *}

syntax "_mixed_prefix" :: "prefix_elem' \<Rightarrow> mixed_prefix' \<Rightarrow> mixed_prefix'" ("__")

syntax
  "_prefix_action" ::
  "('a, '\<epsilon>) chan \<Rightarrow> mixed_prefix' \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> ('\<sigma>, '\<epsilon>) action"
  ("(__ \<^bold>\<rightarrow>/ _)" [81, 81, 80] 80)

text {* Syntax translations *}

definition lconj :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('b \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<times> 'b \<Rightarrow> '\<alpha> upred)" (infixr "\<and>\<^sub>l" 35)
where [upred_defs]: "(P \<and>\<^sub>l Q) \<equiv> (\<lambda> (x,y). P x \<and> Q y)"

definition outp_constraint (infix "=\<^sub>o" 60) where
[upred_defs]: "outp_constraint v \<equiv> (\<lambda> x. \<guillemotleft>x\<guillemotright> =\<^sub>u v)"

translations
  "_simple_input_prefix x" \<rightleftharpoons> "_input_prefix x true"
  "_mixed_prefix (_input_prefix x P) (_prefix_aux y Q)" \<rightharpoonup>
  "_prefix_aux (_pattern x y) ((\<lambda> x. P) \<and>\<^sub>l Q)"
  "_mixed_prefix (_output_prefix P) (_prefix_aux y Q)" \<rightharpoonup>
  "_prefix_aux (_pattern _idtdummy y) ((CONST outp_constraint P) \<and>\<^sub>l Q)"
  "_end_prefix (_input_prefix x P)" \<rightharpoonup> "_prefix_aux x (\<lambda> x. P)"
  "_end_prefix (_output_prefix P)" \<rightharpoonup> "_prefix_aux _idtdummy (CONST outp_constraint P)"
  "_prefix_action c (_prefix_aux x P) A" == "(CONST InputCSP) c P (\<lambda>x. A)"

text {* Basic print translations; more work needed *}

translations
  "_simple_input_prefix x" <= "_input_prefix x true"
  "_output_prefix v" <= "_prefix_aux p (CONST outp_constraint v)"
  "_output_prefix u (_output_prefix v)" 
    <= "_prefix_aux p (\<lambda>(x1, y1). CONST outp_constraint u x2 \<and> CONST outp_constraint v y2)"
  "_input_prefix x P" <= "_prefix_aux v (\<lambda>x. P)"
  "x!(v) \<^bold>\<rightarrow> P" <= "CONST OutputCSP x v P"
  
term "x!(1)!(y) \<^bold>\<rightarrow> P"  
term "x?(v) \<^bold>\<rightarrow> P"
term "x?(v:false) \<^bold>\<rightarrow> P"
term "x!(\<langle>1\<rangle>) \<^bold>\<rightarrow> P"
term "x?(v)!(1) \<^bold>\<rightarrow> P"
term "x!(\<langle>1\<rangle>)!(2)?(v:true) \<^bold>\<rightarrow> P"

text {* Basic translations for state variable communications *}

syntax
  "_csp_input_var"  :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?$_:_ \<^bold>\<rightarrow> _" [81, 0, 0, 80] 80)
  "_csp_inputu_var" :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?$_ \<^bold>\<rightarrow> _" [81, 0, 80] 80)

translations
  "c\<^bold>?$x:A \<^bold>\<rightarrow> P" \<rightharpoonup> "CONST InputVarCSP c x A P"
  "c\<^bold>?$x \<^bold>\<rightarrow> P"   \<rightharpoonup> "CONST InputVarCSP c x (\<lambda> x. true) P"
  "c\<^bold>?$x:A \<^bold>\<rightarrow> P" <= "CONST InputVarCSP c x (\<lambda> x'. A) P"
  "c\<^bold>?$x \<^bold>\<rightarrow> P"   <= "c\<^bold>?$x:true \<^bold>\<rightarrow> P"

lemma outp_constraint_prod:
  "(outp_constraint \<guillemotleft>a\<guillemotright> x \<and> outp_constraint \<guillemotleft>b\<guillemotright> y) =
    outp_constraint \<guillemotleft>(a, b)\<guillemotright> (x, y)"
  by (simp add: outp_constraint_def, pred_auto)
  
lemma subst_outp_constraint [usubst]:
  "\<sigma> \<dagger> (v =\<^sub>o x) =  (\<sigma> \<dagger> v =\<^sub>o x)"
  by (rel_auto)
    
lemma UINF_one_point_simp [rpred]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Sqinter> x \<bullet> [\<guillemotleft>i\<guillemotright> =\<^sub>o x]\<^sub>S\<^sub>< \<and> P(x)) = P(i)"
  by (rel_blast)

lemma USUP_one_point_simp [rpred]:
  "\<lbrakk> \<And> i. P i is R1 \<rbrakk> \<Longrightarrow> (\<Squnion> x \<bullet> [\<guillemotleft>i\<guillemotright> =\<^sub>o x]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P(x)) = P(i)"
  by (rel_blast)

lemma USUP_eq_event_eq [rpred]:
  assumes "\<And> y. P(y) is RR"
  shows "(\<Squnion> y \<bullet> [v =\<^sub>o y]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r P(y)) = P(y)\<lbrakk>y\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk>"
proof -
  have "(\<Squnion> y \<bullet> [v =\<^sub>o y]\<^sub>S\<^sub>< \<Rightarrow>\<^sub>r RR(P(y))) = RR(P(y))\<lbrakk>y\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk>"
    apply (rel_simp, safe)
    apply metis
    apply blast
    apply simp
    done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma UINF_eq_event_eq [rpred]:
  assumes "\<And> y. P(y) is RR"
  shows "(\<Sqinter> y \<bullet> [v =\<^sub>o y]\<^sub>S\<^sub>< \<and> P(y)) = P(y)\<lbrakk>y\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk>"
proof -
  have "(\<Sqinter> y \<bullet> [v =\<^sub>o y]\<^sub>S\<^sub>< \<and> RR(P(y))) = RR(P(y))\<lbrakk>y\<rightarrow>\<lceil>v\<rceil>\<^sub>S\<^sub>\<leftarrow>\<rbrakk>"
    by (rel_simp, safe, metis)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

text {* Proofs that the input constrained parser versions of output is the same as the regular definition. *}

lemma output_prefix_is_OutputCSP [simp]:
  assumes "A is NCSP"
  shows "x!(P) \<^bold>\<rightarrow> A = OutputCSP x P A" (is "?lhs = ?rhs")
  by (rule SRD_eq_intro, simp_all add: assms closure rdes, rel_auto+)

lemma OutputCSP_pair_simp [simp]:
  "P is NCSP \<Longrightarrow> a.(\<guillemotleft>i\<guillemotright>).(\<guillemotleft>j\<guillemotright>) \<^bold>\<rightarrow> P = OutputCSP a \<guillemotleft>(i,j)\<guillemotright> P"
  using output_prefix_is_OutputCSP[of "P" a]
  by (simp add: outp_constraint_prod lconj_def InputCSP_def closure del: output_prefix_is_OutputCSP)
    
lemma OutputCSP_triple_simp [simp]:
  "P is NCSP \<Longrightarrow> a.(\<guillemotleft>i\<guillemotright>).(\<guillemotleft>j\<guillemotright>).(\<guillemotleft>k\<guillemotright>) \<^bold>\<rightarrow> P = OutputCSP a \<guillemotleft>(i,j,k)\<guillemotright> P"
  using output_prefix_is_OutputCSP[of "P" a]
  by (simp add: outp_constraint_prod lconj_def InputCSP_def closure del: output_prefix_is_OutputCSP)

end