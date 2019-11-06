section \<open> Undefinedness \<close>

theory utp_undef
  imports "UTP-Designs.utp_designs" "UTP.utp_expr_funcs"
begin

type_synonym ('a, '\<alpha>) pexpr = "('a option, '\<alpha>) uexpr"

definition pexpr_undef :: "('a, '\<alpha>) pexpr" ("\<bottom>\<^sub>\<D>") where
[upred_defs]: "\<bottom>\<^sub>\<D> = \<guillemotleft>None\<guillemotright>"

definition pexpr_down :: "('a, '\<alpha>) pexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<lfloor>_\<rfloor>\<^sub>\<D>") where
[upred_defs]: "\<lfloor>e\<rfloor>\<^sub>\<D> = uop the e"

no_utp_lift pexpr_down (0)

lift_definition pexpr_defined :: "('a, '\<alpha>) pexpr \<Rightarrow> '\<alpha> upred" ("\<D>'(_')") is
"\<lambda> e b. b \<in> dom(e)" .

update_uexpr_rep_eq_thms

lemma undef_defined: "\<D>(\<bottom>\<^sub>\<D>) = false"
  by (rel_simp)


definition partial_assign :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('a, '\<alpha>) pexpr \<Rightarrow> '\<alpha> hrel_des" where
[upred_defs, ndes_simp]: "partial_assign x e = (\<^bold>S(x) \<and> \<D>(e)) \<turnstile>\<^sub>n x := \<lfloor>e\<rfloor>\<^sub>\<D>"

syntax
  "_passignd" :: "svid \<Rightarrow> uexp \<Rightarrow> logic"  (infixr ":=\<^sub>\<D>" 62)

translations
  "_passignd x e" == "CONST partial_assign x e"

lemma passign_bot: "x :=\<^sub>\<D> \<bottom>\<^sub>\<D> = \<bottom>\<^sub>D"
  by (rel_auto)

lemma passign_wp [wp]: "x :=\<^sub>\<D> v wp\<^sub>D b = (\<^bold>S(x) \<and> \<D>(v) \<and> b\<lbrakk>\<lfloor>v\<rfloor>\<^sub>\<D>/&x\<rbrakk>)"
  by (simp add: partial_assign_def wp conj_assoc)

end