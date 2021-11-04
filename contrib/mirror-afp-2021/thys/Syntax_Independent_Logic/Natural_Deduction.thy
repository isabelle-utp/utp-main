chapter \<open>Natural Deduction\<close>

(*<*)
theory Natural_Deduction imports Deduction
begin
(*>*)

text \<open>We develop a natural deduction system based on the Hilbert system.\<close>

context Deduct_with_False_Disj
begin

section \<open>Natural Deduction from the Hilbert System\<close>

definition nprv :: "'fmla set \<Rightarrow> 'fmla \<Rightarrow> bool" where
"nprv F \<phi> \<equiv> prv (imp (scnj F) \<phi>)"

lemma nprv_hyp[simp,intro]:
"\<phi> \<in> F \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> nprv F \<phi>"
unfolding nprv_def
by (simp add: prv_scnj_imp_in subset_iff)


section \<open>Structural Rules for the Natural Deduction Relation\<close>

lemma prv_nprv0I: "prv \<phi> \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> nprv {} \<phi>"
unfolding nprv_def by (simp add: prv_imp_triv)

lemma prv_nprv_emp: "\<phi> \<in> fmla \<Longrightarrow> prv \<phi> \<longleftrightarrow> nprv {} \<phi>"
using prv_nprv0I unfolding nprv_def
by (metis asList eqv finite.simps insert_not_empty lcnj.simps(1) ldsj.cases
  list.simps(15) prv_eqvI prv_imp_mp prv_imp_tru scnj_def tru)

lemma nprv_mono:
assumes "nprv G \<phi>"
and "F \<subseteq> fmla" "finite F" "G \<subseteq> F" "\<phi> \<in> fmla"
shows "nprv F \<phi>"
using assms unfolding nprv_def
by (meson order_trans prv_prv_imp_trans prv_scnj_mono rev_finite_subset scnj)

lemma nprv_cut:
assumes "nprv F \<phi>" and "nprv (insert \<phi> F) \<psi>"
and "F \<subseteq> fmla" "finite F"  "\<phi> \<in> fmla"  "\<psi> \<in> fmla"
shows "nprv F \<psi>"
using assms unfolding nprv_def
by (metis (full_types) cnj finite.insertI
  insert_subset prv_imp_cnj prv_imp_cnj_scnj prv_imp_refl prv_prv_imp_trans scnj)

lemma nprv_strong_cut2:
"nprv F \<phi>1 \<Longrightarrow> nprv (insert \<phi>1 F) \<phi>2 \<Longrightarrow> nprv (insert \<phi>2 (insert \<phi>1 F)) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
by (meson finite.insertI insert_subsetI nprv_cut)

lemma nprv_cut2:
"nprv F \<phi>1 \<Longrightarrow> nprv F \<phi>2 \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv (insert \<phi>2 (insert \<phi>1 F)) \<psi> \<Longrightarrow> nprv F \<psi>"
by (meson finite.insertI insert_subsetI nprv_mono nprv_strong_cut2 subset_insertI)

text \<open>Useful for fine control of the eigenformula:\<close>

lemma nprv_insertShiftI:
"nprv (insert \<phi>1 (insert \<phi>2 F)) \<psi> \<Longrightarrow> nprv (insert \<phi>2 (insert \<phi>1 F)) \<psi>"
by (simp add: insert_commute)

lemma nprv_insertShift2I:
"nprv (insert \<phi>3 (insert \<phi>1 (insert \<phi>2 F))) \<psi> \<Longrightarrow> nprv (insert \<phi>1 (insert \<phi>2 (insert \<phi>3 F))) \<psi>"
by (simp add: insert_commute)


section \<open>Back and Forth between Hilbert and Natural Deduction\<close>

text \<open>This is now easy, thanks to the large number of facts we have
proved for Hilbert-style deduction\<close>

lemma prv_nprvI: "prv \<phi> \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> nprv F \<phi>"
using prv_nprv0I
by (simp add: nprv_def prv_imp_triv)

thm prv_nprv0I

lemma prv_nprv1I:
assumes "\<phi> \<in> fmla" "\<psi> \<in> fmla" and "prv (imp \<phi> \<psi>)"
shows "nprv {\<phi>} \<psi>"
using assms unfolding nprv_def by (simp add: prv_scnj_imp)

lemma prv_nprv2I:
assumes "prv (imp \<phi>1 (imp \<phi>2 \<psi>))" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv {\<phi>1,\<phi>2} \<psi>"
using assms unfolding nprv_def
by (meson cnj empty_subsetI finite.simps insert_subsetI prv_cnj_imp_monoR2 prv_prv_imp_trans prv_scnj2_imp_cnj scnj)

lemma nprv_prvI: "nprv {} \<phi> \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> prv \<phi>"
using prv_nprv_emp by auto


section \<open>More Structural Properties\<close>

lemma nprv_clear: "nprv {} \<phi> \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> nprv F \<phi>"
by (rule nprv_mono) auto

lemma nprv_cut_set:
assumes F:  "finite F" "F \<subseteq> fmla" and G: "finite G" "G \<subseteq> fmla" "\<chi> \<in> fmla"
and n1: "\<And> \<psi>. \<psi> \<in> G \<Longrightarrow> nprv F \<psi>" and n2: "nprv (G \<union> F) \<chi>"
shows "nprv F \<chi>"
using G F n1 n2 proof(induction arbitrary: F \<chi>)
  case (insert \<psi> G F \<chi>)
  hence 0: "nprv F \<psi>" by auto
  have 1: "nprv (insert \<psi> F) \<chi>"
  using insert.prems  apply- apply(rule insert.IH)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (meson finite.simps insert_subset nprv_mono subsetD subset_insertI)
  by auto
  show ?case using insert.prems by (intro nprv_cut[OF 0 1]) auto
qed(insert nprv_clear, auto)

lemma nprv_clear2_1:
"nprv {\<phi>2} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear2_2:
"nprv {\<phi>1} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear3_1:
"nprv {\<phi>2,\<phi>3} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear3_2:
"nprv {\<phi>1,\<phi>3} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear3_3:
"nprv {\<phi>1,\<phi>2} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear4_1:
"nprv {\<phi>2,\<phi>3,\<phi>4} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow>\<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear4_2:
"nprv {\<phi>1,\<phi>3,\<phi>4} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear4_3:
"nprv {\<phi>1,\<phi>2,\<phi>4} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow>\<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear4_4:
"nprv {\<phi>1,\<phi>2,\<phi>3} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow>\<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_1:
"nprv {\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_2:
"nprv {\<phi>1,\<phi>3,\<phi>4,\<phi>5} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_3:
"nprv {\<phi>1,\<phi>2,\<phi>4,\<phi>5} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_4:
"nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>5} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto

lemma nprv_clear5_5:
"nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4} \<psi> \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<phi>3 \<in> fmla \<Longrightarrow> \<phi>4 \<in> fmla \<Longrightarrow> \<phi>5 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv {\<phi>1,\<phi>2,\<phi>3,\<phi>4,\<phi>5} \<psi>"
by (rule nprv_mono) auto


section \<open>Properties Involving Substitution\<close>

lemma nprv_subst:
assumes "x \<in> var" "t \<in> trm" "\<psi> \<in> fmla" "finite F" "F \<subseteq> fmla"
and 1: "nprv F \<psi>"
shows "nprv ((\<lambda>\<phi>. subst \<phi> t x) ` F) (subst \<psi> t x)"
using assms using prv_subst[OF _ _ _ 1[unfolded nprv_def]]  unfolding nprv_def
by (intro prv_prv_imp_trans[OF _ _ _ prv_subst_scnj_imp]) auto

lemma nprv_subst_fresh:
assumes 0: "x \<in> var" "t \<in> trm" "\<psi> \<in> fmla" "finite F" "F \<subseteq> fmla"
"nprv F \<psi>" and 1: "x \<notin> \<Union> (Fvars ` F)"
shows "nprv F (subst \<psi> t x)"
proof-
  have 2: "(\<lambda>\<phi>. subst \<phi> t x) ` F = F" unfolding image_def using assms by force
  show ?thesis using nprv_subst[OF 0] unfolding 2 .
qed

lemma nprv_subst_rev:
assumes 0: "x \<in> var" "y \<in> var" "\<psi> \<in> fmla" "finite F" "F \<subseteq> fmla"
and f: "y = x \<or> (y \<notin> Fvars \<psi> \<and> y \<notin> \<Union> (Fvars ` F))"
and 1: "nprv ((\<lambda>\<phi>. subst \<phi> (Var y) x) ` F) (subst \<psi> (Var y) x)"
shows "nprv F \<psi>"
proof-
  have 0: "subst (subst \<psi> (Var y) x) (Var x) y = \<psi>"
  using assms by (auto simp: subst_compose_eq_or)
  have "nprv ((\<lambda>\<phi>. subst \<phi> (Var x) y) ` (\<lambda>\<phi>. subst \<phi> (Var y) x) ` F) \<psi>"
  using assms apply(subst 0[symmetric]) by (rule nprv_subst) auto
  moreover
  have "prv (imp (scnj F)
                 (scnj ((\<lambda>\<phi>. subst \<phi> (Var x) y) ` (\<lambda>\<phi>. subst \<phi> (Var y) x) ` F)))"
  using assms apply(intro prv_scnj_mono_imp)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal apply clarify
    subgoal for _ _ \<phi>
    by (auto simp: subst_compose_eq_or intro!: bexI[of _ \<phi>] prv_imp_refl2) . .
  ultimately show ?thesis
  unfolding nprv_def using assms
  apply- by(rule prv_prv_imp_trans) auto
qed

lemma nprv_psubst:
assumes 0: "snd ` set txs \<subseteq> var" "fst ` set txs \<subseteq> trm" "\<psi> \<in> fmla" "finite F" "F \<subseteq> fmla"
"distinct (map snd txs)"
and 1: "nprv F \<psi>"
shows "nprv ((\<lambda>\<phi>. psubst \<phi> txs) ` F) (psubst \<psi> txs)"
using assms  unfolding nprv_def
apply(intro prv_prv_imp_trans[OF _ _ _ prv_psubst_scnj_imp])
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal using prv_psubst[OF _ _ _ 1[unfolded nprv_def]]
	by (metis imp psubst_imp scnj) .

section \<open>Introduction and Elimination Rules\<close>

text \<open>We systematically leave the side-conditions at the end, to simplify reasoning.\<close>

lemma nprv_impI:
"nprv (insert \<phi> F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F (imp \<phi> \<psi>)"
unfolding nprv_def
by (metis cnj finite.insertI insert_subset prv_cnj_imp prv_imp_cnj_scnj prv_imp_com prv_prv_imp_trans scnj)

lemma nprv_impI_rev:
assumes "nprv F (imp \<phi> \<psi>)"
and "F \<subseteq> fmla" and "finite F" and "\<phi> \<in> fmla" and "\<psi> \<in> fmla"
shows "nprv (insert \<phi> F) \<psi>"
using assms unfolding nprv_def
by (metis cnj finite.insertI insert_subset prv_cnj_imp_monoR2 prv_eqv_imp_transi
    prv_eqv_scnj_insert prv_imp_com scnj)

lemma nprv_impI_rev2:
assumes "nprv F (imp \<phi> \<psi>)" and G: "insert \<phi> F \<subseteq> G"
and "G \<subseteq> fmla" and "finite G" and "\<phi> \<in> fmla" and "\<psi> \<in> fmla"
shows "nprv G \<psi>"
using assms apply- apply(rule nprv_mono[of "insert \<phi> F"])
subgoal by (meson nprv_impI_rev order_trans rev_finite_subset subset_insertI)
by auto

lemma nprv_mp:
"nprv F (imp \<phi> \<psi>) \<Longrightarrow> nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
unfolding nprv_def
by (metis (full_types) cnj prv_cnj_imp_monoR2 prv_imp_cnj prv_imp_refl prv_prv_imp_trans scnj)

lemma nprv_impE:
"nprv F (imp \<phi> \<psi>) \<Longrightarrow> nprv F \<phi> \<Longrightarrow>  nprv (insert \<psi> F) \<chi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow> \<chi> \<in> fmla \<Longrightarrow>
 nprv F \<chi>"
using nprv_cut nprv_mp by blast

lemmas nprv_impE0 = nprv_impE[OF nprv_hyp _ _, simped]
lemmas nprv_impE1 = nprv_impE[OF _ nprv_hyp _, simped]
lemmas nprv_impE2 = nprv_impE[OF _ _ nprv_hyp, simped]
lemmas nprv_impE01 = nprv_impE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_impE02 = nprv_impE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_impE12 = nprv_impE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_impE012 = nprv_impE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

lemma nprv_cnjI:
"nprv F \<phi> \<Longrightarrow> nprv F \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F (cnj \<phi> \<psi>)"
unfolding nprv_def by (simp add: prv_imp_cnj)

lemma nprv_cnjE:
"nprv F (cnj \<phi>1 \<phi>2) \<Longrightarrow> nprv (insert \<phi>1 (insert \<phi>2 F)) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
unfolding nprv_def
by (metis cnj nprv_cut2 nprv_def prv_imp_cnjL prv_imp_cnjR prv_prv_imp_trans scnj)

lemmas nprv_cnjE0 = nprv_cnjE[OF nprv_hyp _, simped]
lemmas nprv_cnjE1 = nprv_cnjE[OF _ nprv_hyp, simped]
lemmas nprv_cnjE01 = nprv_cnjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_dsjIL:
"nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F (dsj \<phi> \<psi>)"
unfolding nprv_def by (meson dsj prv_dsj_impL prv_prv_imp_trans scnj)

lemma nprv_dsjIR:
"nprv F \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F (dsj \<phi> \<psi>)"
unfolding nprv_def by (meson dsj prv_dsj_impR prv_prv_imp_trans scnj)

lemma nprv_dsjE:
assumes "nprv F (dsj \<phi> \<psi>)"
and "nprv (insert \<phi> F) \<chi>" "nprv (insert \<psi> F) \<chi>"
and "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "\<psi> \<in> fmla" "\<chi> \<in> fmla"
shows "nprv F \<chi>"
proof-
  have "nprv F (imp (dsj \<phi> \<psi>) \<chi>)"
    by (meson assms dsj imp nprv_def nprv_impI prv_imp_com prv_imp_dsjEE scnj)
  hence "nprv (insert (dsj \<phi> \<psi>) F) \<chi>" using assms
    by (simp add: nprv_impI_rev)
  thus ?thesis using assms by (meson dsj nprv_cut)
qed

lemmas nprv_dsjE0 = nprv_dsjE[OF nprv_hyp _ _, simped]
lemmas nprv_dsjE1 = nprv_dsjE[OF _ nprv_hyp _, simped]
lemmas nprv_dsjE2 = nprv_dsjE[OF _ _ nprv_hyp, simped]
lemmas nprv_dsjE01 = nprv_dsjE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_dsjE02 = nprv_dsjE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_dsjE12 = nprv_dsjE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_dsjE012 = nprv_dsjE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

lemma nprv_flsE: "nprv F fls \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow>  nprv F \<phi>"
unfolding nprv_def using prv_prv_imp_trans scnj by blast

lemmas nprv_flsE0 = nprv_flsE[OF nprv_hyp, simped]

lemma nprv_truI: "F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> nprv F tru"
unfolding nprv_def by (simp add: prv_imp_tru)

lemma nprv_negI:
"nprv (insert \<phi> F) fls \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow>
 nprv F (neg \<phi>)"
unfolding neg_def by (auto intro: nprv_impI)

lemma nprv_neg_fls:
"nprv F (neg \<phi>) \<Longrightarrow> nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F fls"
unfolding neg_def using nprv_mp by blast

lemma nprv_negE:
"nprv F (neg \<phi>) \<Longrightarrow> nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
using nprv_flsE nprv_neg_fls by blast

lemmas nprv_negE0 = nprv_negE[OF nprv_hyp _, simped]
lemmas nprv_negE1 = nprv_negE[OF _ nprv_hyp, simped]
lemmas nprv_negE01 = nprv_negE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_scnjI:
"(\<And> \<psi>. \<psi> \<in> G \<Longrightarrow> nprv F \<psi>) \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> G \<subseteq> fmla \<Longrightarrow> finite G \<Longrightarrow>
 nprv F (scnj G)"
unfolding nprv_def by (simp add: prv_imp_scnj)

lemma nprv_scnjE:
"nprv F (scnj G) \<Longrightarrow> nprv (G \<union> F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> G \<subseteq> fmla \<Longrightarrow> finite G \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
apply(rule nprv_cut_set[of _ G])
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by (meson in_mono nprv_def prv_prv_imp_trans prv_scnj_imp_in scnj) .

lemmas nprv_scnjE0 = nprv_scnjE[OF nprv_hyp _, simped]
lemmas nprv_scnjE1 = nprv_scnjE[OF _ nprv_hyp, simped]
lemmas nprv_scnjE01 = nprv_scnjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_lcnjI:
"(\<And> \<psi>. \<psi> \<in> set \<psi>s \<Longrightarrow> nprv F \<psi>) \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> set \<psi>s \<subseteq> fmla \<Longrightarrow>
 nprv F (lcnj \<psi>s)"
unfolding nprv_def by (simp add: prv_imp_lcnj)

lemma nprv_lcnjE:
"nprv F (lcnj \<phi>s) \<Longrightarrow> nprv (set \<phi>s \<union> F) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> set \<phi>s \<subseteq> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv F \<psi>"
apply(rule nprv_cut_set[of _ "set \<phi>s \<union> F"])
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal
  apply (elim UnE)
   apply (meson lcnj nprv_def prv_lcnj_imp_in prv_prv_imp_trans scnj subset_code(1))
  by auto
subgoal by auto .

lemmas nprv_lcnjE0 = nprv_lcnjE[OF nprv_hyp _, simped]
lemmas nprv_lcnjE1 = nprv_lcnjE[OF _ nprv_hyp, simped]
lemmas nprv_lcnjE01 = nprv_lcnjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_sdsjI:
"nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> G \<subseteq> fmla \<Longrightarrow> finite G \<Longrightarrow> \<phi> \<in> G \<Longrightarrow>
 nprv F (sdsj G)"
unfolding nprv_def by (simp add: prv_imp_sdsj)

lemma nprv_sdsjE:
assumes "nprv F (sdsj G)"
and "\<And> \<psi>. \<psi> \<in> G \<Longrightarrow> nprv (insert \<psi> F) \<chi>"
and "F \<subseteq> fmla" "finite F" "G \<subseteq> fmla" "finite G" "\<chi> \<in> fmla"
shows "nprv F \<chi>"
proof-
  have 0: "prv (imp (sdsj G) (imp (scnj F) \<chi>))"
    using assms apply(intro prv_sdsj_imp)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (meson nprv_def nprv_impI prv_imp_com scnj set_rev_mp) .
  hence "nprv F (imp (sdsj G) \<chi>)"
    by (simp add: 0 assms nprv_def prv_imp_com)
  thus ?thesis using assms nprv_mp by blast
qed

lemmas nprv_sdsjE0 = nprv_sdsjE[OF nprv_hyp _, simped]
lemmas nprv_sdsjE1 = nprv_sdsjE[OF _ nprv_hyp, simped]
lemmas nprv_sdsjE01 = nprv_sdsjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_ldsjI:
"nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> set \<phi>s \<subseteq> fmla \<Longrightarrow>  \<phi> \<in> set \<phi>s \<Longrightarrow>
 nprv F (ldsj \<phi>s)"
unfolding nprv_def by(simp add: prv_imp_ldsj)

lemma nprv_ldsjE:
assumes "nprv F (ldsj \<psi>s)"
and "\<And> \<psi>. \<psi> \<in> set \<psi>s \<Longrightarrow> nprv (insert \<psi> F) \<chi>"
and "F \<subseteq> fmla" "finite F" "set \<psi>s \<subseteq> fmla"  "\<chi> \<in> fmla"
shows "nprv F \<chi>"
proof-
  have 0: "prv (imp (ldsj \<psi>s) (imp (scnj F) \<chi>))"
  using assms apply(intro prv_ldsj_imp)
    subgoal by auto
    subgoal by auto
    subgoal by (meson nprv_def nprv_impI prv_imp_com scnj set_rev_mp) .
  hence "nprv F (imp (ldsj \<psi>s) \<chi>)"
    by (simp add: 0 assms nprv_def prv_imp_com)
  thus ?thesis using assms nprv_mp by blast
qed

lemmas nprv_ldsjE0 = nprv_ldsjE[OF nprv_hyp _, simped]
lemmas nprv_ldsjE1 = nprv_ldsjE[OF _ nprv_hyp, simped]
lemmas nprv_ldsjE01 = nprv_ldsjE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_allI:
"nprv F \<phi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> x \<in> var \<Longrightarrow> x \<notin> \<Union> (Fvars ` F) \<Longrightarrow>
 nprv F (all x \<phi>)"
unfolding nprv_def by (rule prv_all_imp_gen) auto

lemma nprv_allE:
assumes "nprv F (all x \<phi>)" "nprv (insert (subst \<phi> t x) F) \<psi>"
"F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "t \<in> trm" "x \<in> var" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
proof-
  have "nprv F (subst \<phi> t x)"
  using assms unfolding nprv_def by (meson all subst prv_all_inst prv_prv_imp_trans scnj)
  thus ?thesis by (meson assms local.subst nprv_cut)
qed

lemmas nprv_allE0 = nprv_allE[OF nprv_hyp _, simped]
lemmas nprv_allE1 = nprv_allE[OF _ nprv_hyp, simped]
lemmas nprv_allE01 = nprv_allE[OF nprv_hyp nprv_hyp, simped]

lemma nprv_exiI:
"nprv F (subst \<phi> t x) \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
 nprv F (exi x \<phi>)"
unfolding nprv_def by (meson exi local.subst prv_exi_inst prv_prv_imp_trans scnj)

lemma nprv_exiE:
assumes n: "nprv F (exi x \<phi>)"
and nn: "nprv (insert \<phi> F) \<psi>"
and 0[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "\<psi> \<in> fmla"
and x: "x \<notin> \<Union> (Fvars ` F)" "x \<notin> Fvars \<psi>"
shows "nprv F \<psi>"
proof-
  have "nprv F (imp (exi x \<phi>) \<psi>)" unfolding nprv_def apply(rule prv_imp_com)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal apply(rule prv_exi_imp_gen)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using x by auto
    subgoal apply(rule prv_imp_com)
      subgoal by auto
      subgoal by auto
      subgoal by auto
      subgoal using assms(3-5) assms(7) nn nprv_def nprv_impI by blast . . .
  thus ?thesis using n assms nprv_mp by blast
qed

lemmas nprv_exiE0 = nprv_exiE[OF nprv_hyp _, simped]
lemmas nprv_exiE1 = nprv_exiE[OF _ nprv_hyp, simped]
lemmas nprv_exiE01 = nprv_exiE[OF nprv_hyp nprv_hyp, simped]


section \<open>Adding Lemmas of Various Shapes into the Proof Context\<close>

lemma nprv_addLemmaE:
assumes "prv \<phi>" "nprv (insert \<phi> F) \<psi>"
and "\<phi> \<in> fmla" "\<psi> \<in> fmla" and "F \<subseteq> fmla" and "finite F"
shows "nprv F \<psi>"
using assms nprv_cut prv_nprvI by blast

lemmas nprv_addLemmaE1 = nprv_addLemmaE[OF _ nprv_hyp, simped]

lemma nprv_addImpLemmaI:
assumes "prv (imp \<phi>1 \<phi>2)"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"
and "nprv F \<phi>1"
shows "nprv F \<phi>2"
by (meson assms nprv_def prv_prv_imp_trans scnj)

lemma nprv_addImpLemmaE:
assumes "prv (imp \<phi>1 \<phi>2)" and "nprv F \<phi>1" and "nprv ((insert \<phi>2) F) \<psi>"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
using assms nprv_addImpLemmaI nprv_cut by blast

lemmas nprv_addImpLemmaE1 = nprv_addImpLemmaE[OF _ nprv_hyp _, simped]
lemmas nprv_addImpLemmaE2 = nprv_addImpLemmaE[OF _ _ nprv_hyp, simped]
lemmas nprv_addImpLemmaE12 = nprv_addImpLemmaE[OF _ nprv_hyp nprv_hyp, simped]

lemma nprv_addImp2LemmaI:
assumes "prv (imp \<phi>1 (imp \<phi>2 \<phi>3))"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<phi>3 \<in> fmla"
and "nprv F \<phi>1" "nprv F \<phi>2"
shows "nprv F \<phi>3"
by (meson assms imp nprv_addImpLemmaI nprv_mp)

lemma nprv_addImp2LemmaE:
assumes "prv (imp \<phi>1 (imp \<phi>2 \<phi>3))" and "nprv F \<phi>1" and "nprv F \<phi>2" and "nprv ((insert \<phi>3) F) \<psi>"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla"  "\<phi>3 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
by (meson assms nprv_addImp2LemmaI nprv_cut)

lemmas nprv_addImp2LemmaE1 = nprv_addImp2LemmaE[OF _ nprv_hyp _ _, simped]
lemmas nprv_addImp2LemmaE2 = nprv_addImp2LemmaE[OF _ _ nprv_hyp _, simped]
lemmas nprv_addImp2LemmaE3 = nprv_addImp2LemmaE[OF _ _ _ nprv_hyp, simped]
lemmas nprv_addImp2LemmaE12 = nprv_addImp2LemmaE[OF _ nprv_hyp nprv_hyp _, simped]
lemmas nprv_addImp2LemmaE13 = nprv_addImp2LemmaE[OF _ nprv_hyp _ nprv_hyp, simped]
lemmas nprv_addImp2LemmaE23 = nprv_addImp2LemmaE[OF _ _ nprv_hyp nprv_hyp, simped]
lemmas nprv_addImp2LemmaE123 = nprv_addImp2LemmaE[OF _ nprv_hyp nprv_hyp nprv_hyp, simped]

lemma nprv_addImp3LemmaI:
assumes "prv (imp \<phi>1 (imp \<phi>2 (imp \<phi>3 \<phi>4)))"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<phi>3 \<in> fmla" "\<phi>4 \<in> fmla"
and "nprv F \<phi>1" "nprv F \<phi>2" "nprv F \<phi>3"
shows "nprv F \<phi>4"
by (meson assms imp nprv_addImpLemmaI nprv_mp)

lemma nprv_addImp3LemmaE:
assumes "prv (imp \<phi>1 (imp \<phi>2 (imp \<phi>3 \<phi>4)))"  and "nprv F \<phi>1" and "nprv F \<phi>2" and "nprv F \<phi>3"
and "nprv ((insert \<phi>4) F) \<psi>"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<phi>3 \<in> fmla" "\<phi>4 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
by (meson assms nprv_addImp3LemmaI nprv_cut)

lemmas nprv_addImp3LemmaE1 = nprv_addImp3LemmaE[OF _ nprv_hyp _ _ _, simped]
lemmas nprv_addImp3LemmaE2 = nprv_addImp3LemmaE[OF _ _ nprv_hyp _ _, simped]
lemmas nprv_addImp3LemmaE3 = nprv_addImp3LemmaE[OF _ _ _ nprv_hyp _, simped]
lemmas nprv_addImp3LemmaE4 = nprv_addImp3LemmaE[OF _ _ _ _ nprv_hyp, simped]
lemmas nprv_addImp3LemmaE12 = nprv_addImp3LemmaE[OF _ nprv_hyp nprv_hyp _ _, simped]
lemmas nprv_addImp3LemmaE13 = nprv_addImp3LemmaE[OF _ nprv_hyp _ nprv_hyp _, simped]
lemmas nprv_addImp3LemmaE14 = nprv_addImp3LemmaE[OF _ nprv_hyp _ _ nprv_hyp, simped]
lemmas nprv_addImp3LemmaE23 = nprv_addImp3LemmaE[OF _ _ nprv_hyp nprv_hyp _, simped]
lemmas nprv_addImp3LemmaE24 = nprv_addImp3LemmaE[OF _ _ nprv_hyp _ nprv_hyp, simped]
lemmas nprv_addImp3LemmaE34 = nprv_addImp3LemmaE[OF _ _ _ nprv_hyp nprv_hyp, simped]
lemmas nprv_addImp3LemmaE123 = nprv_addImp3LemmaE[OF _ nprv_hyp nprv_hyp nprv_hyp _, simped]
lemmas nprv_addImp3LemmaE124 = nprv_addImp3LemmaE[OF _ nprv_hyp nprv_hyp _ nprv_hyp, simped]
lemmas nprv_addImp3LemmaE134 = nprv_addImp3LemmaE[OF _ nprv_hyp _ nprv_hyp nprv_hyp, simped]
lemmas nprv_addImp3LemmaE234 = nprv_addImp3LemmaE[OF _ _ nprv_hyp nprv_hyp nprv_hyp, simped]
lemmas nprv_addImp3LemmaE1234 = nprv_addImp3LemmaE[OF _ nprv_hyp nprv_hyp nprv_hyp nprv_hyp, simped]

lemma nprv_addDsjLemmaE:
assumes "prv (dsj \<phi>1 \<phi>2)" and "nprv (insert \<phi>1 F) \<psi>" and "nprv ((insert \<phi>2) F) \<psi>"
and "F \<subseteq> fmla" "finite F" "\<phi>1 \<in> fmla" "\<phi>2 \<in> fmla" "\<psi> \<in> fmla"
shows "nprv F \<psi>"
by (meson assms dsj nprv_clear nprv_dsjE prv_nprv0I)

lemmas nprv_addDsjLemmaE1 = nprv_addDsjLemmaE[OF _ nprv_hyp _, simped]
lemmas nprv_addDsjLemmaE2 = nprv_addDsjLemmaE[OF _ _ nprv_hyp, simped]
lemmas nprv_addDsjLemmaE12 = nprv_addDsjLemmaE[OF _ nprv_hyp nprv_hyp, simped]

section \<open>Rules for Equality\<close>

text \<open>Reflexivity:\<close>
lemma nprv_eql_reflI: "F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> t \<in> trm \<Longrightarrow> nprv F (eql t t)"
by (simp add: prv_eql_reflT prv_nprvI)

lemma nprv_eq_eqlI: "t1 = t2 \<Longrightarrow> F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> t1 \<in> trm \<Longrightarrow> nprv F (eql t1 t2)"
by (simp add: prv_eql_reflT prv_nprvI)

text \<open>Symmetry:\<close>
lemmas nprv_eql_symI =  nprv_addImpLemmaI[OF prv_eql_sym, simped, rotated 4]
lemmas nprv_eql_symE =  nprv_addImpLemmaE[OF prv_eql_sym, simped, rotated 2]

lemmas nprv_eql_symE0 =  nprv_eql_symE[OF nprv_hyp _, simped]
lemmas nprv_eql_symE1 =  nprv_eql_symE[OF _ nprv_hyp, simped]
lemmas nprv_eql_symE01 =  nprv_eql_symE[OF nprv_hyp nprv_hyp, simped]

text \<open>Transitivity:\<close>
lemmas nprv_eql_transI = nprv_addImp2LemmaI[OF prv_eql_imp_trans, simped, rotated 5]
lemmas nprv_eql_transE = nprv_addImp2LemmaE[OF prv_eql_imp_trans, simped, rotated 3]

lemmas nprv_eql_transE0 = nprv_eql_transE[OF nprv_hyp _ _, simped]
lemmas nprv_eql_transE1 = nprv_eql_transE[OF _ nprv_hyp _, simped]
lemmas nprv_eql_transE2 = nprv_eql_transE[OF _ _ nprv_hyp, simped]
lemmas nprv_eql_transE01 = nprv_eql_transE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_eql_transE02 = nprv_eql_transE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_eql_transE12 = nprv_eql_transE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_eql_transE012 = nprv_eql_transE[OF nprv_hyp nprv_hyp nprv_hyp, simped]

text \<open>Substitutivity:\<close>
lemmas nprv_eql_substI =
nprv_addImp2LemmaI[OF prv_eql_subst_trm_rev, simped, rotated 6]
lemmas nprv_eql_substE = nprv_addImp2LemmaE[OF prv_eql_subst_trm_rev, simped, rotated 4]

lemmas nprv_eql_substE0 = nprv_eql_substE[OF nprv_hyp _ _, simped]
lemmas nprv_eql_substE1 = nprv_eql_substE[OF _ nprv_hyp _, simped]
lemmas nprv_eql_substE2 = nprv_eql_substE[OF _ _ nprv_hyp, simped]
lemmas nprv_eql_substE01 = nprv_eql_substE[OF nprv_hyp nprv_hyp _, simped]
lemmas nprv_eql_substE02 = nprv_eql_substE[OF nprv_hyp _ nprv_hyp, simped]
lemmas nprv_eql_substE12 = nprv_eql_substE[OF _ nprv_hyp nprv_hyp, simped]
lemmas nprv_eql_substE012 = nprv_eql_substE[OF nprv_hyp nprv_hyp nprv_hyp, simped]


section \<open>Other Rules\<close>

lemma nprv_cnjH:
"nprv (insert \<phi>1 (insert \<phi>2 F)) \<psi> \<Longrightarrow>
 F \<subseteq> fmla \<Longrightarrow> finite F \<Longrightarrow> \<phi>1 \<in> fmla \<Longrightarrow> \<phi>2 \<in> fmla \<Longrightarrow> \<psi> \<in> fmla \<Longrightarrow>
 nprv (insert (cnj \<phi>1 \<phi>2) F) \<psi>"
apply(rule nprv_cut2[of _ \<phi>1 \<phi>2])
subgoal by (auto simp: nprv_impI_rev prv_imp_cnjL prv_imp_cnjR prv_nprvI)
subgoal by (auto simp: nprv_impI_rev prv_imp_cnjL prv_imp_cnjR prv_nprvI)
subgoal by (auto simp: nprv_impI_rev prv_imp_cnjL prv_imp_cnjR prv_nprvI)
subgoal by (auto simp: nprv_impI_rev prv_imp_cnjL prv_imp_cnjR prv_nprvI)
subgoal by (auto simp: nprv_impI_rev prv_imp_cnjL prv_imp_cnjR prv_nprvI)
subgoal by (auto simp: nprv_impI_rev prv_imp_cnjL prv_imp_cnjR prv_nprvI)
subgoal by (auto simp: nprv_impI_rev prv_imp_cnjL prv_imp_cnjR prv_nprvI)
by (meson cnj finite.insertI insert_iff insert_subset nprv_mono subset_insertI)

lemma nprv_exi_commute:
assumes [simp]: "x \<in> var" "y \<in> var" "\<phi> \<in> fmla"
shows "nprv {exi x (exi y \<phi>)} (exi y (exi x \<phi>))"
apply(rule nprv_exiE0[of x "exi y \<phi>"], auto)
apply(rule nprv_clear2_2, auto)
apply(rule nprv_exiE0[of y \<phi>], auto)
apply(rule nprv_clear2_2, auto)
apply(rule nprv_exiI[of _ _ "Var y"], auto)
by (rule nprv_exiI[of _ _ "Var x"], auto)

lemma prv_exi_commute:
assumes [simp]: "x \<in> var" "y \<in> var" "\<phi> \<in> fmla"
shows "prv (imp (exi x (exi y \<phi>)) (exi y (exi x \<phi>)))"
apply(rule nprv_prvI, auto)
apply(rule nprv_impI, auto)
by (rule nprv_exi_commute, auto)

end (* context Deduct_with_False_Disj *)


section \<open>Natural Deduction for the Exists-Unique Quantifier\<close>

context Deduct_with_False_Disj_Rename
begin

lemma nprv_exuI:
assumes n1: "nprv F (subst \<phi> t x)" and n2: "nprv (insert \<phi> F) (eql (Var x) t)"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "t \<in> trm" "x \<in> var"   "x \<notin> FvarsT t"
and u: "x \<notin> (\<Union>\<phi> \<in> F. Fvars \<phi>)"
shows "nprv F (exu x \<phi>)"
proof-
  define z where "z \<equiv> getFr [x] [t] [\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> x" "x \<noteq> z"   "z \<notin> FvarsT t" "z \<notin> Fvars \<phi>"
  using getFr_FvarsT_Fvars[of "[x]" "[t]" "[\<phi>]"] unfolding z_def[symmetric] by auto
  have 0: "exu x \<phi> = cnj (exi x \<phi>) (exi z (all x (imp \<phi> (eql (Var x) (Var z)))))"
  by (simp add: exu_def_var[of _ z])
  show ?thesis
  unfolding 0
    apply(rule nprv_cnjI, auto)
    apply(rule nprv_exiI[of _ _ t], auto)
    apply(rule n1)
    (**)
    apply(rule nprv_exiI[of _ _ t], auto)
    apply(rule nprv_allI, insert u, auto)
    apply(rule nprv_impI, insert n2, auto)
  done
qed

lemma nprv_exuI_var:
assumes n1: "nprv F (subst \<phi> t x)" and n2: "nprv (insert (subst \<phi> (Var y) x) F) (eql (Var y) t)"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "t \<in> trm" "x \<in> var"
"y \<in> var" "y \<notin> FvarsT t" and u: "y \<notin> (\<Union>\<phi> \<in> F. Fvars \<phi>)" and yx: "y = x \<or> y \<notin> Fvars \<phi>"
shows "nprv F (exu x \<phi>)"
apply(subst exu_rename2[of _ _ y])
subgoal by auto
subgoal by auto
subgoal by auto
subgoal using yx by auto
subgoal apply(intro nprv_exuI[of _ _ t])
  subgoal by (metis i(3) i(4) i(5) i(6) n1 subst_same_Var subst_subst yx)
  using n2 u by auto .

text \<open>This turned out to be the most useful introduction rule for arithmetic:\<close>
lemma nprv_exuI_exi:
assumes n1: "nprv F (exi x \<phi>)" and n2: "nprv (insert (subst \<phi> (Var y) x) (insert \<phi> F)) (eql (Var y) (Var x))"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "y \<in> var" "y \<noteq> x" "y \<notin> Fvars \<phi>"
and u: "x \<notin> (\<Union>\<phi> \<in> F. Fvars \<phi>)" "y \<notin> (\<Union>\<phi> \<in> F. Fvars \<phi>)"
shows "nprv F (exu x \<phi>)"
proof-
  have e: "nprv (insert \<phi> F) (exu x \<phi>)"
  apply(rule nprv_exuI_var[of _ _ "Var x" _ y])
  using n2 u by auto
  show ?thesis
  apply(rule nprv_cut[OF n1], auto)
  apply(rule nprv_exiE0, insert u, auto)
  apply(rule nprv_mono[OF e], auto) .
qed

lemma prv_exu_imp_exi:
assumes [simp]: "\<phi> \<in> fmla" "x \<in> var"
shows "prv (imp (exu x \<phi>) (exi x \<phi>))"
proof-
  define z where z: "z \<equiv> getFr [x] [] [\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> x" "x \<noteq> z" "z \<notin> Fvars \<phi>"
  using getFr_FvarsT_Fvars[of "[x]" "[]" "[\<phi>]"] unfolding z by auto
  show ?thesis unfolding exu_def
  by (simp add: Let_def z[symmetric] prv_imp_cnjL)
qed

lemma prv_exu_exi:
  assumes "x \<in> var" "\<phi> \<in> fmla" "prv (exu x \<phi>)"
  shows "prv (exi x \<phi>)"
  by (meson assms exi exu prv_exu_imp_exi prv_imp_mp)

text \<open>This is just exu behaving for elimination and forward like exi:\<close>
lemma nprv_exuE_exi:
assumes n1: "nprv F (exu x \<phi>)" and n2: "nprv (insert \<phi> F) \<psi>"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "\<psi> \<in> fmla" "x \<notin> Fvars \<psi>"
and u: "x \<notin> (\<Union>\<phi> \<in> F. Fvars \<phi>)"
shows "nprv F \<psi>"
using assms apply- apply(rule nprv_exiE[of _ x \<phi>])
subgoal by (rule nprv_addImpLemmaI[OF prv_exu_imp_exi[of \<phi> x]]) auto
by auto

lemma nprv_exuF_exi:
assumes n1: "exu x \<phi> \<in> F" and n2: "nprv (insert \<phi> F) \<psi>"
and i[simp]: "F \<subseteq> fmla" "finite F" "\<phi> \<in> fmla" "x \<in> var" "\<psi> \<in> fmla" "x \<notin> Fvars \<psi>"
and u: "x \<notin> (\<Union>\<phi> \<in> F. Fvars \<phi>)"
shows "nprv F \<psi>"
using assms  nprv_exuE_exi nprv_hyp by metis

lemma prv_exu_uni:
assumes [simp]: "\<phi> \<in> fmla" "x \<in> var" "t1 \<in> trm" "t2 \<in> trm"
shows "prv (imp (exu x \<phi>) (imp (subst \<phi> t1 x) (imp (subst \<phi> t2 x) (eql t1 t2))))"
proof-
  define z where z: "z \<equiv> getFr [x] [t1,t2] [\<phi>]"
  have z_facts[simp]: "z \<in> var" "z \<noteq> x" "x \<noteq> z" "z \<notin> Fvars \<phi>"  "z \<notin> FvarsT t1" "z \<notin> FvarsT t2"
  using getFr_FvarsT_Fvars[of "[x]" "[t1,t2]" "[\<phi>]"] unfolding z by auto
  show ?thesis
  apply(rule nprv_prvI, auto)
  apply(rule nprv_impI, auto)
  apply(simp add: exu_def_var[of _ z])
  apply(rule nprv_cnjE0, auto)
  apply(rule nprv_clear3_1, auto)
  apply(rule nprv_clear2_2, auto)
  apply(rule nprv_exiE0, auto)
  apply(rule nprv_clear2_2, auto)
  apply(rule nprv_allE0[of _ _ _ t1], auto)
  apply(rule nprv_allE0[of _ _ _ t2], auto)
  apply(rule nprv_clear3_3, auto)
  apply(rule nprv_impI, auto)
  apply(rule nprv_impI, auto)
  apply(rule nprv_impE01, auto)
  apply(rule nprv_clear5_2, auto)
  apply(rule nprv_clear4_3, auto)
  apply(rule nprv_impE01, auto)
  apply(rule nprv_clear4_3, auto)
  apply(rule nprv_clear3_3, auto)
  apply(rule nprv_eql_symE0[of t2 "Var z"], auto)
  apply(rule nprv_eql_transE012, auto) .
qed

lemmas nprv_exuE_uni = nprv_addImp3LemmaE[OF prv_exu_uni,simped,rotated 4]
lemmas nprv_exuF_uni = nprv_exuE_uni[OF nprv_hyp,simped]


end \<comment> \<open>context @{locale Deduct_with_False_Disj}\<close>


section \<open>Eisbach Notation for Natural Deduction Proofs\<close>


text \<open>The proof pattern will be: On a goal of the form @{term "nprv F \<phi>"},
we apply a rule (usually an introduction, elimination, or cut/lemma-addition
rule), then discharge the side-conditions with @{method auto}, ending up with zero,
one or two goals of the same nprv-shape. This process is abstracted away in the
Eisbach nrule method:\<close>

method nrule uses r = (rule r, auto?)
(* For future developments, in case we refine what we do
(and also for documentation): This is supposed to create two main nprv-subgoals: *)
method nrule2 uses r = (rule r, auto?)


text \<open>Methods for chaining several nrule applications:\<close>

method nprover2 uses r1 r2 =
  (-,(((nrule r: r1)?, (nrule r: r2)?) ; fail))
method nprover3 uses r1 r2 r3 =
  (-,(((nrule r: r1)?, (nrule r: r2)?, (nrule r: r3)?) ; fail))
method nprover4 uses r1 r2 r3 r4 =
  (-,(((nrule r: r1)?, (nrule r: r2)?, (nrule r: r3)?, (nrule r: r4)?) ; fail))
method nprover5 uses r1 r2 r3 r4 r5 =
  (-,((nrule r: r1)?, (nrule r: r2)?, (nrule r: r3)?,
   (nrule r: r4)?, (nrule r: r5)?) ; fail)
method nprover6 uses r1 r2 r3 r4 r5 r6 =
  (-,((nrule r: r1)?, (nrule r: r2)?, (nrule r: r3)?,
   (nrule r: r4)?, (nrule r: r5)?, (nrule r: r6)?) ; fail)

(*<*)
end
(*>*)