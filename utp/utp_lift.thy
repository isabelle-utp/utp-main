section {* Lifting expressions *}

theory utp_lift
  imports 
    utp_alphabet
begin

subsection {* Lifting definitions *}

text {* We define operators for converting an expression to and from a relational state space *}

abbreviation lift_pre :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uexpr" ("\<lceil>_\<rceil>\<^sub><")
where "\<lceil>P\<rceil>\<^sub>< \<equiv> P \<oplus>\<^sub>p fst\<^sub>L"

abbreviation drop_pre :: "('\<alpha> \<times> '\<alpha>) upred \<Rightarrow> '\<alpha> upred" ("\<lfloor>_\<rfloor>\<^sub><")
where "\<lfloor>P\<rfloor>\<^sub>< \<equiv> P \<restriction>\<^sub>p fst\<^sub>L"

abbreviation lift_post :: "('a, '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uexpr" ("\<lceil>_\<rceil>\<^sub>>")
where "\<lceil>P\<rceil>\<^sub>> \<equiv> P \<oplus>\<^sub>p snd\<^sub>L"

abbreviation drop_post :: "('\<alpha> \<times> '\<alpha>) upred \<Rightarrow> '\<alpha> upred" ("\<lfloor>_\<rfloor>\<^sub>>")
where "\<lfloor>P\<rfloor>\<^sub>> \<equiv> P \<restriction>\<^sub>p snd\<^sub>L"

subsection {* Lifting laws *}

lemma lift_pre_var [simp]:
  "\<lceil>var x\<rceil>\<^sub>< = $x"
  by (alpha_tac)

lemma lift_post_var [simp]:
  "\<lceil>var x\<rceil>\<^sub>> = $x\<acute>"
  by (alpha_tac)

subsection {* Substitution laws *}

lemma subst_lift_upd [usubst]: 
  fixes x :: "('a, '\<alpha>) uvar"
  shows "\<lceil>\<sigma>(x \<mapsto>\<^sub>s v)\<rceil>\<^sub>s = \<lceil>\<sigma>\<rceil>\<^sub>s($x \<mapsto>\<^sub>s \<lceil>v\<rceil>\<^sub><)"
  by (simp add: usubst_rel_lift_def subst_upd_uvar_def, transfer, auto simp add: fst_lens_def)

lemma subst_lift_pre [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>b\<rceil>\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub><"
  by pred_tac

(*
lemma subst_drop_upd [usubst]: 
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "out\<alpha> \<sharp> v"
  shows "\<lfloor>\<sigma>($x \<mapsto>\<^sub>s v)\<rfloor>\<^sub>s = \<lfloor>\<sigma>\<rfloor>\<^sub>s(x \<mapsto>\<^sub>s \<lfloor>v\<rfloor>\<^sub><)"
  using assms
  apply (simp add: usubst_rel_drop_def subst_upd_uvar_def, transfer)
  apply (rule ext, auto simp add:in_var_def fst_lens_def lens_create_def lens_comp_def prod.case_eq_if)
  apply (subgoal_tac "\<forall> x x'. (v (A, x)) = (v (A, x'))")
  apply metis
  apply (simp)
  apply (simp)
thm prod.case_eq_if
done
*)

end