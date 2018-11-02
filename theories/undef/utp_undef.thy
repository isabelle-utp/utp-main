section \<open> Undefinedness \<close>

theory utp_undef
  imports "UTP-Designs.utp_designs" "UTP.utp_expr_funcs"
begin

type_synonym ('a, '\<alpha>) pexpr = "('a option, '\<alpha>) uexpr"

definition pexpr_undef :: "('a, '\<alpha>) pexpr" ("\<bottom>\<^sub>\<D>") where
[upred_defs]: "\<bottom>\<^sub>\<D> = \<guillemotleft>None\<guillemotright>"

definition pexpr_down :: "('a, '\<alpha>) pexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<lfloor>_\<rfloor>\<^sub>\<D>") where
[upred_defs]: "\<lfloor>e\<rfloor>\<^sub>\<D> = uop the e"

lift_definition pexpr_defined :: "('a, '\<alpha>) pexpr \<Rightarrow> '\<alpha> upred" ("\<D>'(_')") is
"\<lambda> e b. b \<in> dom(e)" .

update_uexpr_rep_eq_thms

lemma undef_defined: "\<D>(\<bottom>\<^sub>\<D>) = false"
  by (rel_simp)

definition src_pred :: "('a \<Longrightarrow> 's) \<Rightarrow> 's upred" ("\<^bold>S'(_')") where
[upred_defs]: "src_pred x = (&\<^bold>v \<in>\<^sub>u \<guillemotleft>\<S>\<^bsub>x\<^esub>\<guillemotright>)"

lemma wb_lens_src_true [simp]: "wb_lens x \<Longrightarrow> \<^bold>S(x) = true"
  by (rel_simp, simp add: wb_lens.source_UNIV) 

definition partial_assign :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('a, '\<alpha>) pexpr \<Rightarrow> '\<alpha> hrel_des" where
[upred_defs]: "partial_assign x e = (\<^bold>S(x) \<and> \<D>(e)) \<turnstile>\<^sub>n x := \<lfloor>e\<rfloor>\<^sub>\<D>"

syntax
  "_passignd" :: "svid \<Rightarrow> uexp \<Rightarrow> logic"  (infixr ":=\<^sub>\<D>" 62)

translations
  "_passignd x e" == "CONST partial_assign x e"

lemma passign_bot: "x :=\<^sub>\<D> \<bottom>\<^sub>\<D> = \<bottom>\<^sub>D"
  by (rel_auto)


end