chapter \<open>Löb's Theorem\<close>

(*<*)
theory Loeb imports Loeb_Formula Derivability_Conditions
begin
(*>*)

text \<open>We have set up the formalization of Gödel's first (easy half) and Gödel's second
so that the following generalizations, leading to Löb's theorem, are trivial
modifications of these, replacing negation with "implies @{term \<phi>}" in all proofs.\<close>

locale Loeb_Assumptions =
HBL1_2_3
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv bprv
  enc
  P
+
Loeb_Form
  var trm fmla Var num FvarsT substT Fvars subst
  eql cnj imp all exi
  prv bprv
  enc
  S
  P
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var num FvarsT substT Fvars subst
and eql cnj imp all exi
and prv bprv
and enc ("\<langle>_\<rangle>")
and S
and P
begin

text \<open>Generalization of $\mathit{goedel\_first\_theEasyHalf\_pos}$, replacing @{term fls} with a sentence @{term \<phi>}:\<close>
lemma loeb_aux_prv:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "prv (\<phi>L \<phi>)"
shows "prv \<phi>"
proof-
  have "prv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)" using assms prv_eqv_prv[OF _ _ p prv_\<phi>L_eqv] by auto
  moreover have "bprv (PP \<langle>\<phi>L \<phi>\<rangle>)" using HBL1[OF \<phi>L[OF \<phi>] _ p] unfolding PP_def by simp
  from bprv_prv[OF _ _ this, simplified] have "prv (PP \<langle>\<phi>L \<phi>\<rangle>)" .
  ultimately show ?thesis using PP \<phi>L by (meson assms enc in_num prv_imp_mp)
qed

lemma loeb_aux_bprv:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "bprv (\<phi>L \<phi>)"
shows "bprv \<phi>"
proof-
  note pp = bprv_prv[OF _ _ p, simplified]
  have "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)" using assms B.prv_eqv_prv[OF _ _ p bprv_\<phi>L_eqv] by auto
  moreover have "bprv (PP \<langle>\<phi>L \<phi>\<rangle>)" using HBL1[OF \<phi>L[OF \<phi>] _ pp] unfolding PP_def by simp
  ultimately show ?thesis using PP \<phi>L by (meson assms enc in_num B.prv_imp_mp)
qed

text \<open>Generalization of $\mathit{P\_G}$, the main lemma used for Gödel's second:\<close>
lemma P_L:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}"
shows "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) (PP \<langle>\<phi>\<rangle>))"
proof-
  have 0: "prv (imp (\<phi>L \<phi>) (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>))"
    using prv_\<phi>L_eqv by (intro prv_imp_eqvEL) auto
  have 1: "bprv (PP \<langle>imp (\<phi>L \<phi>) (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)\<rangle>)"
    using HBL1_PP[OF _ _ 0] by simp
  have 2: "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) (PP \<langle>imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>\<rangle>))"
  using HBL2_imp2[OF _ _ _ _ 1] by simp
  have 3: "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) (PP \<langle>PP \<langle>\<phi>L \<phi>\<rangle>\<rangle>))"
    using HBL3[OF \<phi>L[OF \<phi>] _] by simp
  have 23: "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>)
                      (cnj (PP \<langle>PP \<langle>\<phi>L \<phi>\<rangle>\<rangle>)
                           (PP \<langle>imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>\<rangle>)))"
  using B.prv_imp_cnj[OF _ _ _ 3 2] by simp
  have 4: "bprv (imp (cnj (PP \<langle>PP \<langle>\<phi>L \<phi>\<rangle>\<rangle>)
                          (PP \<langle>imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>\<rangle>))
                    (PP \<langle>\<phi>\<rangle>))"
    using HBL2[of "PP \<langle>\<phi>L \<phi>\<rangle>" \<phi>] by simp
  show ?thesis using B.prv_prv_imp_trans[OF _ _ _ 23 4] by simp
qed

text \<open>Löb's theorem generalizes the positive formulation Gödel's Second
($\mathit{goedel\_second}$). In our two-provability-relation framework, we get two variants of Löb's theorem.
A stronger variant, assuming @{term prv} and proving @{term bprv}, seems impossible.\<close>

theorem loeb_bprv:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "bprv (imp (PP \<langle>\<phi>\<rangle>) \<phi>)"
shows "bprv \<phi>"
proof-
  have "bprv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)"
    by (rule B.prv_prv_imp_trans[OF _ _ _ P_L p]) auto
  hence "bprv (\<phi>L \<phi>)"
    by (rule B.prv_eqv_prv_rev[OF _ _ _ bprv_\<phi>L_eqv, rotated 2]) auto
  thus ?thesis using loeb_aux_bprv[OF \<phi>] by simp
qed

theorem loeb_prv:
assumes \<phi>[simp]: "\<phi> \<in> fmla" "Fvars \<phi> = {}" and p: "prv (imp (PP \<langle>\<phi>\<rangle>) \<phi>)"
shows "prv \<phi>"
proof-
  note PL = bprv_prv[OF _ _ P_L, simplified]
  have "prv (imp (PP \<langle>\<phi>L \<phi>\<rangle>) \<phi>)"
    by (rule prv_prv_imp_trans[OF _ _ _ PL p]) auto
  hence "prv (\<phi>L \<phi>)"
    by (rule prv_eqv_prv_rev[OF _ _ _ prv_\<phi>L_eqv, rotated 2]) auto
  thus ?thesis using loeb_aux_prv[OF \<phi>] by simp
qed

text \<open>We could have of course inferred $\mathit{goedel\_first\_theEasyHalf\_pos}$
and $\mathit{goedel\_second}$ from these more general versions, but we leave the original
arguments as they are more instructive.\<close>

end \<comment> \<open>context @{locale Loeb_Assumptions}\<close>

(*<*)
end
(*>*)



