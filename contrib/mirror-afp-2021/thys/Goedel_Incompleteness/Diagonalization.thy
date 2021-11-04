chapter \<open>Diagonalization\<close>

text \<open>This theory proves abstract versions of the diagonalization lemma,
with both hard and soft substitution.\<close>


section \<open>Alternative Diagonalization via Self-Substitution\<close>

(*<*)
theory Diagonalization imports Abstract_Representability
begin
(*>*)

text \<open>
Assuming representability of the diagonal instance of the substitution function,
we prove the standard diagonalization lemma. More precisely, we show that it applies
to any logic that
-- embeds intuitionistic first-order logic over numerals
-- has a countable number of formulas
-- has formula self-substitution representable
\<close>

context Repr_SelfSubst
begin

theorem diagonalization:
  assumes \<phi>[simp,intro!]: "\<phi> \<in> fmla" "Fvars \<phi> = {xx}"
  shows "\<exists> \<psi>. \<psi> \<in> fmla \<and> Fvars \<psi> = {} \<and> bprv (eqv \<psi> (subst \<phi> \<langle>\<psi>\<rangle> xx))"
proof-
  let ?phi = "\<lambda> t. subst \<phi> t xx"
  define \<chi> where "\<chi> \<equiv> exi yy (cnj (?phi (Var yy)) (SS (Var xx) (Var yy)))"
  have \<chi>[simp,intro!]: "\<chi> \<in> fmla" unfolding \<chi>_def by auto
  let ?chi = "\<lambda> t. subst \<chi> t xx"
  define \<psi> where "\<psi> \<equiv> ?chi \<langle>\<chi>\<rangle>"
  have \<psi>[simp,intro!]: "\<psi> \<in> fmla" unfolding \<psi>_def by auto
  have f\<chi>[simp]: "Fvars \<chi> = {xx}" unfolding \<chi>_def by auto
  hence Fvars_\<psi>: "Fvars \<psi> = {}" unfolding \<psi>_def by auto
  have 1: "bprv (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)"
    using subst_implies_prv_SS[OF \<chi>] unfolding \<psi>_def by simp
  have 2: "bprv (all yy' (
             imp (cnj (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)
                      (SS \<langle>\<chi>\<rangle> (Var yy')))
                 (eql \<langle>\<psi>\<rangle> (Var yy'))))"
    using Fvars_\<psi> B.prv_allE[OF _ _ _ SS_unique, of \<chi> "\<langle>\<psi>\<rangle>"]
    by fastforce
  have 31: "bprv (all yy'
                     (imp (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)
                          (imp (SS \<langle>\<chi>\<rangle> (Var yy'))
                               (eql \<langle>\<psi>\<rangle> (Var yy')))))"
    using B.prv_all_imp_cnj_rev[OF _ _ _ _ 2] by simp
  have 32: "bprv (imp (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)
                      (all yy' (imp (SS \<langle>\<chi>\<rangle> (Var yy'))
                                    (eql \<langle>\<psi>\<rangle> (Var yy')))))"
    by (intro B.prv_all_imp[OF _ _ _ _ 31]) (auto simp: SS_def2)
  have 33: "bprv (all yy' (imp (SS \<langle>\<chi>\<rangle> (Var yy'))
                               (eql \<langle>\<psi>\<rangle> (Var yy'))))"
    by (rule B.prv_imp_mp [OF _ _ 32 1]) auto
  have 3: "bprv (all yy (imp (SS \<langle>\<chi>\<rangle> (Var yy))
                             (eql \<langle>\<psi>\<rangle> (Var yy))))"
    using B.all_subst_rename_prv[OF _ _ _ _ 33, of yy]
    by fastforce
  have 41: "bprv (imp (?phi \<langle>\<psi>\<rangle>)
                      (cnj (?phi \<langle>\<psi>\<rangle>)
                           (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)))"
    by (auto intro: in_num B.prv_imp_cnj B.prv_imp_refl B.prv_imp_triv[OF _ _ 1])
  have [simp]: "subst (subst \<phi> \<langle>\<psi>\<rangle> xx) \<langle>\<psi>\<rangle> yy = subst \<phi> \<langle>\<psi>\<rangle> xx"
    by (intro subst_notIn) auto
  have [simp]: "subst (subst \<phi> (Var yy) xx) \<langle>\<psi>\<rangle> yy = subst \<phi> \<langle>\<psi>\<rangle> xx"
    by (intro subst_subst) auto
  have 42: "bprv (exi yy (imp (?phi \<langle>\<psi>\<rangle>)
                              (cnj (?phi (Var yy))
                                   (SS \<langle>\<chi>\<rangle> (Var yy)))))"
    using 41 by (intro B.prv_exiI[of _ _ "\<langle>\<psi>\<rangle>"]) auto
  have 4: "bprv (imp (?phi \<langle>\<psi>\<rangle>) (?chi \<langle>\<chi>\<rangle>))"
    using B.prv_imp_exi[OF _ _ _ _ 42,simplified]
    by (subst \<chi>_def) (auto simp add: subst_comp_num)
  have 50: "bprv (all yy (
          (imp (eql \<langle>\<psi>\<rangle> (Var yy))
               (imp (?phi (Var yy))
                    (?phi \<langle>\<psi>\<rangle>)))))"
    using B.prv_all_eql[of yy xx \<phi> "\<langle>\<psi>\<rangle>" "Var yy"] by simp
  have 51: "bprv (all yy (
          (imp (SS \<langle>\<chi>\<rangle> (Var yy))
               (imp (?phi (Var yy))
               (?phi \<langle>\<psi>\<rangle>)))))" using B.prv_all_imp_trans[OF _ _ _ _ 3 50] by simp
  have 52: "bprv (all yy (
          (imp (cnj (?phi (Var yy))
                    (SS \<langle>\<chi>\<rangle> (Var yy)))
               (?phi \<langle>\<psi>\<rangle>))))" using B.prv_all_imp_cnj[OF _ _ _ _ 51] by simp
  have 5: "bprv (imp (?chi \<langle>\<chi>\<rangle>) (?phi \<langle>\<psi>\<rangle>))"
    using B.prv_exi_imp[OF _ _ _ _ 52,simplified]
    by (subst \<chi>_def) (simp add: subst_comp_num)
  have 6: "bprv (eqv (?chi \<langle>\<chi>\<rangle>) (?phi \<langle>\<psi>\<rangle>))"
    using B.prv_cnjI[OF _ _ 5 4] unfolding eqv_def by simp
  have 7: "bprv (eqv \<psi> (?phi \<langle>\<psi>\<rangle>))" using 6 unfolding \<psi>_def .
  show ?thesis using \<psi> 7 Fvars_\<psi> by blast
qed

text \<open>Making this existential into a function.\<close>

definition diag :: "'fmla \<Rightarrow> 'fmla" where
  "diag \<phi> \<equiv> SOME \<psi>. \<psi> \<in> fmla \<and> Fvars \<psi> = {} \<and> bprv (eqv \<psi> (subst \<phi> \<langle>\<psi>\<rangle> xx))"

theorem diag_everything:
  assumes "\<phi> \<in> fmla" and "Fvars \<phi> = {xx}"
  shows "diag \<phi> \<in> fmla \<and> Fvars (diag \<phi>) = {} \<and> bprv (eqv (diag \<phi>) (subst \<phi> \<langle>diag \<phi>\<rangle> xx))"
  unfolding diag_def using someI_ex[OF diagonalization[OF assms]] .

lemmas diag[simp] = diag_everything[THEN conjunct1]
lemmas Fvars_diag[simp] = diag_everything[THEN conjunct2, THEN conjunct1]
lemmas bprv_diag_eqv = diag_everything[THEN conjunct2, THEN conjunct2]

end \<comment> \<open>context @{locale Repr_SelfSubst}\<close>


section \<open>Alternative Diagonalization via Soft Self-Substitution\<close>

context Repr_SelfSoftSubst
begin

theorem diagonalization:
  assumes \<phi>[simp,intro!]: "\<phi> \<in> fmla" "Fvars \<phi> = {xx}"
  shows "\<exists> \<psi>. \<psi> \<in> fmla \<and> Fvars \<psi> = {} \<and> bprv (eqv \<psi> (subst \<phi> \<langle>\<psi>\<rangle> xx))"
proof-
  let ?phi = "\<lambda> t. subst \<phi> t xx"
  define \<chi> where "\<chi> \<equiv> exi yy (cnj (?phi (Var yy)) (SS (Var xx) (Var yy)))"
  have \<chi>[simp,intro!]: "\<chi> \<in> fmla" unfolding \<chi>_def by auto
  let ?chi = "\<lambda> t. softSubst \<chi> t xx"
  define \<psi> where "\<psi> \<equiv> ?chi \<langle>\<chi>\<rangle>"
  have \<psi>[simp,intro!]: "\<psi> \<in> fmla" unfolding \<psi>_def by auto
  have f\<chi>[simp]: "Fvars \<chi> = {xx}" unfolding \<chi>_def by auto
  hence Fvars_\<psi>: "Fvars \<psi> = {}" unfolding \<psi>_def by auto
  have 1: "bprv (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)"
    using softSubst_implies_prv_SS[OF \<chi>] unfolding \<psi>_def by simp
  have 2: "bprv (all yy' (
             imp (cnj (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)
                      (SS \<langle>\<chi>\<rangle> (Var yy')))
                 (eql \<langle>\<psi>\<rangle> (Var yy'))))"
    using Fvars_\<psi> B.prv_allE[OF _ _ _ SS_unique, of \<chi> "\<langle>\<psi>\<rangle>"]
    by fastforce
  have 31: "bprv (all yy'
                     (imp (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)
                          (imp (SS \<langle>\<chi>\<rangle> (Var yy'))
                               (eql \<langle>\<psi>\<rangle> (Var yy')))))"
    using B.prv_all_imp_cnj_rev[OF _ _ _ _ 2] by simp
  have 32: "bprv (imp (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)
                     (all yy' (imp (SS \<langle>\<chi>\<rangle> (Var yy'))
                                   (eql \<langle>\<psi>\<rangle> (Var yy')))))"
    by (intro B.prv_all_imp[OF _ _ _ _ 31]) (auto simp: SS_def2)
  have 33: "bprv (all yy' (imp (SS \<langle>\<chi>\<rangle> (Var yy'))
                              (eql \<langle>\<psi>\<rangle> (Var yy'))))"
    by (rule B.prv_imp_mp [OF _ _ 32 1]) auto
  have 3: "bprv (all yy (imp (SS \<langle>\<chi>\<rangle> (Var yy))
                            (eql \<langle>\<psi>\<rangle> (Var yy))))"
    using B.all_subst_rename_prv[OF _ _ _ _ 33, of yy]
    by fastforce
  have 41: "bprv (imp (?phi \<langle>\<psi>\<rangle>)
                     (cnj (?phi \<langle>\<psi>\<rangle>)
                          (SS \<langle>\<chi>\<rangle> \<langle>\<psi>\<rangle>)))"
    by (auto intro: in_num B.prv_imp_cnj B.prv_imp_refl B.prv_imp_triv[OF _ _ 1])
  have [simp]: "subst (subst \<phi> \<langle>\<psi>\<rangle> xx) \<langle>\<psi>\<rangle> yy = subst \<phi> \<langle>\<psi>\<rangle> xx"
    by (intro subst_notIn) auto
  have [simp]: "subst (subst \<phi> (Var yy) xx) \<langle>\<psi>\<rangle> yy = subst \<phi> \<langle>\<psi>\<rangle> xx"
    by (intro subst_subst) auto
  have 42: "bprv (exi yy (imp (?phi \<langle>\<psi>\<rangle>)
                             (cnj (?phi (Var yy))
                                  (SS \<langle>\<chi>\<rangle> (Var yy)))))"
    using 41 by (intro B.prv_exiI[of _ _ "\<langle>\<psi>\<rangle>"]) auto
  have 4: "bprv (imp (?phi \<langle>\<psi>\<rangle>) (subst \<chi> \<langle>\<chi>\<rangle> xx))"
    using B.prv_imp_exi[OF _ _ _ _ 42,simplified]
    by (subst \<chi>_def) (auto simp add: subst_comp_num)
  moreover have "bprv (imp (subst \<chi> \<langle>\<chi>\<rangle> xx) (?chi \<langle>\<chi>\<rangle>))" by (rule B.prv_subst_imp_softSubst) auto
  ultimately have 4: "bprv (imp (?phi \<langle>\<psi>\<rangle>) (?chi \<langle>\<chi>\<rangle>))"
    by (rule B.prv_prv_imp_trans[rotated -2]) auto
  have 50: "bprv (all yy (
          (imp (eql \<langle>\<psi>\<rangle> (Var yy))
               (imp (?phi (Var yy))
                    (?phi \<langle>\<psi>\<rangle>)))))"
    using B.prv_all_eql[of yy xx \<phi> "\<langle>\<psi>\<rangle>" "Var yy"] by simp
  have 51: "bprv (all yy (
          (imp (SS \<langle>\<chi>\<rangle> (Var yy))
               (imp (?phi (Var yy))
               (?phi \<langle>\<psi>\<rangle>)))))" using B.prv_all_imp_trans[OF _ _ _ _ 3 50] by simp
  have 52: "bprv (all yy (
          (imp (cnj (?phi (Var yy))
                    (SS \<langle>\<chi>\<rangle> (Var yy)))
               (?phi \<langle>\<psi>\<rangle>))))" using B.prv_all_imp_cnj[OF _ _ _ _ 51] by simp
  have "bprv (imp (?chi \<langle>\<chi>\<rangle>) (subst \<chi> \<langle>\<chi>\<rangle> xx))" by (rule B.prv_softSubst_imp_subst) auto
  moreover have "bprv (imp (subst \<chi> \<langle>\<chi>\<rangle> xx) (?phi \<langle>\<psi>\<rangle>))"
    using B.prv_exi_imp[OF _ _ _ _ 52,simplified]
    by (subst \<chi>_def) (simp add: subst_comp_num)
  ultimately have 5: "bprv (imp (?chi \<langle>\<chi>\<rangle>) (?phi \<langle>\<psi>\<rangle>))"
    by (rule B.prv_prv_imp_trans[rotated -2]) auto
  have 6: "bprv (eqv (?chi \<langle>\<chi>\<rangle>) (?phi \<langle>\<psi>\<rangle>))"
    using B.prv_cnjI[OF _ _ 5 4] unfolding eqv_def by simp
  have 7: "bprv (eqv \<psi> (?phi \<langle>\<psi>\<rangle>))" using 6 unfolding \<psi>_def .
  show ?thesis using \<psi> 7 Fvars_\<psi> by blast
qed

text \<open>Making this existential into a function.\<close>

definition diag :: "'fmla \<Rightarrow> 'fmla" where
  "diag \<phi> \<equiv> SOME \<psi>. \<psi> \<in> fmla \<and> Fvars \<psi> = {} \<and> bprv (eqv \<psi> (subst \<phi> \<langle>\<psi>\<rangle> xx))"

theorem diag_everything:
  assumes "\<phi> \<in> fmla" and "Fvars \<phi> = {xx}"
  shows "diag \<phi> \<in> fmla \<and> Fvars (diag \<phi>) = {} \<and> bprv (eqv (diag \<phi>) (subst \<phi> \<langle>diag \<phi>\<rangle> xx))"
  unfolding diag_def using someI_ex[OF diagonalization[OF assms]] .

lemmas diag[simp] = diag_everything[THEN conjunct1]
lemmas Fvars_diag[simp] = diag_everything[THEN conjunct2, THEN conjunct1]
lemmas prv_diag_eqv = diag_everything[THEN conjunct2, THEN conjunct2]

end \<comment> \<open>context @{locale Repr_SelfSoftSubst}\<close>

(*<*)
end
(*>*)
