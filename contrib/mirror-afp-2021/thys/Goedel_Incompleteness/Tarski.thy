chapter \<open>Abstract Formulation of Tarski's Theorems\<close>

text \<open>We prove Tarski's proof-theoretic and semantic theorems about the
non-definability and respectively non-expressiveness (in the standard model) of truth\<close>

(*<*)
theory Tarski
  imports Goedel_Formula Standard_Model_More
begin
(*>*)

section \<open>Non-Definability of Truth\<close>

context Goedel_Form
begin

context
  fixes T :: 'fmla
  assumes T[simp,intro!]: "T \<in> fmla"
  and Fvars_T[simp]: "Fvars T = {xx}"
  and prv_T: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (eqv (subst T \<langle>\<phi>\<rangle> xx) \<phi>)"
begin

definition \<phi>T :: 'fmla where "\<phi>T \<equiv> diag (neg T)"

lemma \<phi>T[simp,intro!]: "\<phi>T \<in> fmla" and
Fvars_\<phi>T[simp]: "Fvars \<phi>T = {}"
  unfolding \<phi>T_def PP_def by auto

lemma bprv_\<phi>T_eqv:
"bprv (eqv \<phi>T (neg (subst T \<langle>\<phi>T\<rangle> xx)))"
  unfolding \<phi>T_def using bprv_diag_eqv[of "neg T"] by simp

lemma prv_\<phi>T_eqv:
"prv (eqv \<phi>T (neg (subst T \<langle>\<phi>T\<rangle> xx)))"
  using d_dwf.bprv_prv'[OF _ bprv_\<phi>T_eqv, simplified] .

lemma \<phi>T_prv_fls: "prv fls"
using prv_eqv_eqv_neg_prv_fls2[OF _ _ prv_T[OF \<phi>T Fvars_\<phi>T] prv_\<phi>T_eqv] by auto

end \<comment> \<open>context\<close>

theorem Tarski_proof_theoretic:
assumes "T \<in> fmla" "Fvars T = {xx}"
and "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv (eqv (subst T \<langle>\<phi>\<rangle> xx) \<phi>)"
shows "\<not> consistent"
using \<phi>T_prv_fls[OF assms] consistent_def by auto

end \<comment> \<open>context @{locale Goedel_Form}\<close>


section \<open>Non-Expressiveness of Truth\<close>

text \<open>This follows as a corollary of the syntactic version, after taking prv
to be isTrue on sentences.Indeed, this is a virtue of our abstract treatment
of provability: We don't work with a particular predicate, but with any predicate
that is closed under some rules --- which could as well be a semantic notion of truth (for sentences).\<close>

locale Goedel_Form_prv_eq_isTrue =
Goedel_Form
  var trm fmla Var num FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  prv bprv
  enc
  P
  S
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var num FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and prv bprv
and enc ("\<langle>_\<rangle>")
and S
and P
+
fixes isTrue :: "'fmla \<Rightarrow> bool"
assumes prv_eq_isTrue: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> = isTrue \<phi>"
begin

theorem Tarski_semantic:
assumes 0: "T \<in> fmla" "Fvars T = {xx}"
and 1: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> isTrue (eqv (subst T \<langle>\<phi>\<rangle> xx) \<phi>)"
shows "\<not> consistent"
using assms prv_eq_isTrue[of "eqv (subst T \<langle>_\<rangle> xx) _"]
  by (intro Tarski_proof_theoretic[OF 0]) auto

text \<open>NB: To instantiate the semantic version of Tarski's theorem for a truth predicate
isTruth on sentences, one needs to extend it to a predicate "prv" on formulas and verify
that "prv" satisfies the rules of intuitionistic logic.\<close>

end \<comment> \<open>context @{locale Goedel_Form_prv_eq_isTrue}\<close>

(*<*)
end
(*>*)
