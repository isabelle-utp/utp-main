section {* Lifting expressions *}

theory utp_lift
  imports 
    utp_expr
    utp_unrest
begin

subsection {* Lifting definitions *}

text {* We define operators for converting an expression to and from a relational state space *}

lift_definition lift_pre :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uexpr" ("\<lceil>_\<rceil>\<^sub><")
is "\<lambda> p (A, A'). p A" .

lift_definition drop_pre :: "('a, '\<alpha> \<times> '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<lfloor>_\<rfloor>\<^sub><")
is "\<lambda> p A. p (A, A)" .

lift_definition lift_post :: "('a, '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uexpr" ("\<lceil>_\<rceil>\<^sub>>")
is "\<lambda> p (A, A'). p A'" .

abbreviation drop_post :: "('a, '\<alpha> \<times> '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<lfloor>_\<rfloor>\<^sub>>")
where "\<lfloor>b\<rfloor>\<^sub>> \<equiv> \<lfloor>b\<rfloor>\<^sub><"

named_theorems ulift

method ulift_tac = (simp add: ulift)?

subsection {* Lifting laws *}

lemma lift_pre_var [simp]:
  "\<lceil>var x\<rceil>\<^sub>< = $x"
  by (simp add: iuvar_def, transfer, auto)

lemma lift_post_var [simp]:
  "\<lceil>var x\<rceil>\<^sub>> = $x\<acute>"
  by (simp add: ouvar_def, transfer, auto)

lemma lift_pre_lit [simp]:
  "\<lceil>\<guillemotleft>v\<guillemotright>\<rceil>\<^sub>< = \<guillemotleft>v\<guillemotright>"
  by (transfer, auto)

lemma lift_post_lit [simp]:
  "\<lceil>\<guillemotleft>v\<guillemotright>\<rceil>\<^sub>> = \<guillemotleft>v\<guillemotright>"
  by (transfer, auto)

lemma lift_pre_uop [simp]:
  "\<lceil>uop f v\<rceil>\<^sub>< = uop f \<lceil>v\<rceil>\<^sub><"
  by (transfer, auto)

lemma lift_post_uop [simp]:
  "\<lceil>uop f v\<rceil>\<^sub>> = uop f \<lceil>v\<rceil>\<^sub>>"
  by (transfer, auto)

lemma lift_pre_bop [simp]:
  "\<lceil>bop f u v\<rceil>\<^sub>< = bop f \<lceil>u\<rceil>\<^sub>< \<lceil>v\<rceil>\<^sub><"
  by (transfer, auto)

lemma lift_post_bop [simp]:
  "\<lceil>bop f u v\<rceil>\<^sub>> = bop f \<lceil>u\<rceil>\<^sub>> \<lceil>v\<rceil>\<^sub>>"
  by (transfer, auto)

lemma lift_pre_trop [simp]:
  "\<lceil>trop f u v w\<rceil>\<^sub>< = trop f \<lceil>u\<rceil>\<^sub>< \<lceil>v\<rceil>\<^sub>< \<lceil>w\<rceil>\<^sub><"
  by (transfer, auto)

lemma lift_post_trop [simp]:
  "\<lceil>trop f u v w\<rceil>\<^sub>> = trop f \<lceil>u\<rceil>\<^sub>> \<lceil>v\<rceil>\<^sub>> \<lceil>w\<rceil>\<^sub>>"
  by (transfer, auto)

end