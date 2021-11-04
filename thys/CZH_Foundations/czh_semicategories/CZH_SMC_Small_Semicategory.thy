(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for semicategories\<close>
theory CZH_SMC_Small_Semicategory
  imports 
    CZH_DG_Small_Digraph
    CZH_SMC_Semicategory
begin



subsection\<open>Background\<close>


text\<open>
An explanation of the methodology chosen for the exposition of all
matters related to the size of the semicategories and associated entities
is given in the previous chapter.
\<close>

named_theorems smc_small_cs_simps
named_theorems smc_small_cs_intros



subsection\<open>Tiny semicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale tiny_semicategory = \<Z> \<alpha> + vfsequence \<CC> + Comp: vsv \<open>\<CC>\<lparr>Comp\<rparr>\<close> for \<alpha> \<CC> +
  assumes tiny_smc_length[smc_cs_simps]: "vcard \<CC> = 5\<^sub>\<nat>"
    and tiny_smc_tiny_digraph[slicing_intros]: "tiny_digraph \<alpha> (smc_dg \<CC>)"
    and tiny_smc_Comp_vdomain: "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<longleftrightarrow>
      (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
    and tiny_smc_Comp_is_arr[smc_cs_intros]: 
      "\<lbrakk> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and tiny_smc_assoc[smc_cs_simps]:
      "\<lbrakk> h : c \<mapsto>\<^bsub>\<CC>\<^esub> d; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow>
        (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"

lemmas [smc_cs_simps] = 
  tiny_semicategory.tiny_smc_length
  tiny_semicategory.tiny_smc_assoc

lemmas [slicing_intros] = 
  tiny_semicategory.tiny_smc_Comp_is_arr


text\<open>Rules.\<close>

lemma (in tiny_semicategory) tiny_semicategory_axioms'[smc_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "tiny_semicategory \<alpha>' \<CC>"
  unfolding assms by (rule tiny_semicategory_axioms)

mk_ide rf tiny_semicategory_def[unfolded tiny_semicategory_axioms_def]
  |intro tiny_semicategoryI|
  |dest tiny_semicategoryD[dest]|
  |elim tiny_semicategoryE[elim]|

lemma tiny_semicategoryI': 
  assumes "semicategory \<alpha> \<CC>" and "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "tiny_semicategory \<alpha> \<CC>"
proof-
  interpret semicategory \<alpha> \<CC> by (rule assms(1))
  show ?thesis
  proof(intro tiny_semicategoryI)
    show "vfsequence \<CC>" by (simp add: vfsequence_axioms)
    from assms show "tiny_digraph \<alpha> (smc_dg \<CC>)"
      by (intro tiny_digraphI') (auto simp: slicing_simps)
  qed (auto simp: smc_cs_simps intro: smc_cs_intros)
qed

lemma tiny_semicategoryI'':
  assumes "\<Z> \<alpha>"
    and "vfsequence \<CC>"
    and "vsv (\<CC>\<lparr>Comp\<rparr>)"
    and "vcard \<CC> = 5\<^sub>\<nat>"
    and "vsv (\<CC>\<lparr>Dom\<rparr>)"
    and "vsv (\<CC>\<lparr>Cod\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>gf. gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<longleftrightarrow>
      (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "\<And>c d h b g a f. \<lbrakk> h : c \<mapsto>\<^bsub>\<CC>\<^esub> d; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow>
        (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
    and "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "tiny_semicategory \<alpha> \<CC>"
  by (intro tiny_semicategoryI tiny_digraphI, unfold slicing_simps) 
    (simp_all add: smc_dg_def nat_omega_simps assms)


text\<open>Slicing.\<close>

context tiny_semicategory
begin

interpretation dg: tiny_digraph \<alpha> \<open>smc_dg \<CC>\<close> by (rule tiny_smc_tiny_digraph)

lemmas_with [unfolded slicing_simps]:
  tiny_smc_Obj_in_Vset[smc_small_cs_intros] = dg.tiny_dg_Obj_in_Vset
  and tiny_smc_Arr_in_Vset[smc_small_cs_intros] = dg.tiny_dg_Arr_in_Vset
  and tiny_smc_Dom_in_Vset[smc_small_cs_intros] = dg.tiny_dg_Dom_in_Vset
  and tiny_smc_Cod_in_Vset[smc_small_cs_intros] = dg.tiny_dg_Cod_in_Vset

end


text\<open>Elementary properties.\<close>

sublocale tiny_semicategory \<subseteq> semicategory
  by (rule semicategoryI)
    (
      auto 
        simp: 
          vfsequence_axioms
          tiny_digraph.tiny_dg_digraph 
          tiny_smc_tiny_digraph
          tiny_smc_Comp_vdomain         
        intro: smc_cs_intros smc_cs_simps 
    )

lemmas (in tiny_semicategory) tiny_dg_semicategory = semicategory_axioms

lemmas [smc_small_cs_intros] = tiny_semicategory.tiny_dg_semicategory


text\<open>Size.\<close>

lemma (in tiny_semicategory) tiny_smc_Comp_in_Vset: "\<CC>\<lparr>Comp\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (simp add: tiny_smc_Arr_in_Vset)
  with Axiom_of_Infinity have "\<CC>\<lparr>Arr\<rparr> ^\<^sub>\<times> 2\<^sub>\<nat> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (intro Limit_vcpower_in_VsetI) auto
  with Comp.pnop_vdomain have D: "\<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  moreover from tiny_smc_Arr_in_Vset smc_Comp_vrange have 
    "\<R>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    by auto
  ultimately show ?thesis by (simp add: Comp.vbrelation_Limit_in_VsetI)
qed

lemma (in tiny_semicategory) tiny_smc_in_Vset: "\<CC> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [smc_cs_intros] = 
    tiny_smc_Obj_in_Vset 
    tiny_smc_Arr_in_Vset
    tiny_smc_Dom_in_Vset
    tiny_smc_Cod_in_Vset
    tiny_smc_Comp_in_Vset
  show ?thesis by (subst smc_def) (cs_concl cs_intro: smc_cs_intros V_cs_intros)
qed

lemma small_tiny_semicategories[simp]: "small {\<CC>. tiny_semicategory \<alpha> \<CC>}"
proof(rule down)
  show "{\<CC>. tiny_semicategory \<alpha> \<CC>} \<subseteq> elts (set {\<CC>. semicategory \<alpha> \<CC>})" 
    by (auto intro: smc_small_cs_intros)
qed

lemma tiny_semicategories_vsubset_Vset: 
  "set {\<CC>. tiny_semicategory \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset \<alpha>" 
  by (rule vsubsetI) (simp add: tiny_semicategory.tiny_smc_in_Vset)

lemma (in semicategory) smc_tiny_semicategory_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_semicategory \<beta> \<CC>"
proof(intro tiny_semicategoryI)
  show "tiny_digraph \<beta> (smc_dg \<CC>)"
    by (rule digraph.dg_tiny_digraph_if_ge_Limit, rule smc_digraph; intro assms)
qed 
  (
    auto simp: 
      assms(1)
      smc_cs_simps 
      smc_cs_intros 
      smc_digraph digraph.dg_tiny_digraph_if_ge_Limit 
      smc_Comp_vdomain vfsequence_axioms
  )


subsubsection\<open>Opposite tiny semicategory\<close>

lemma (in tiny_semicategory) tiny_semicategory_op: 
  "tiny_semicategory \<alpha> (op_smc \<CC>)"
  by (intro tiny_semicategoryI', unfold smc_op_simps)
    (auto simp: smc_op_intros smc_small_cs_intros)

lemmas tiny_semicategory_op[smc_op_intros] = 
  tiny_semicategory.tiny_semicategory_op



subsection\<open>Finite semicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
A finite semicategory is a generalization of the concept of a finite category,
as presented in nLab 
\cite{noauthor_nlab_nodate}
\footnote{\url{https://ncatlab.org/nlab/show/finite+category}}.
\<close>

locale finite_semicategory = \<Z> \<alpha> + vfsequence \<CC> + Comp: vsv \<open>\<CC>\<lparr>Comp\<rparr>\<close> for \<alpha> \<CC> +
  assumes fin_smc_length[smc_cs_simps]: "vcard \<CC> = 5\<^sub>\<nat>"
    and fin_smc_finite_digraph[slicing_intros]: "finite_digraph \<alpha> (smc_dg \<CC>)"
    and fin_smc_Comp_vdomain: "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<longleftrightarrow>
      (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
    and fin_smc_Comp_is_arr[smc_cs_intros]: 
      "\<lbrakk> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and fin_smc_assoc[smc_cs_simps]:
      "\<lbrakk> h : c \<mapsto>\<^bsub>\<CC>\<^esub> d; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow>
        (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"

lemmas [smc_cs_simps] = 
  finite_semicategory.fin_smc_length
  finite_semicategory.fin_smc_assoc

lemmas [slicing_intros] = 
  finite_semicategory.fin_smc_Comp_is_arr


text\<open>Rules.\<close>

lemma (in finite_semicategory) finite_semicategory_axioms'[smc_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "finite_semicategory \<alpha>' \<CC>"
  unfolding assms by (rule finite_semicategory_axioms)

mk_ide rf finite_semicategory_def[unfolded finite_semicategory_axioms_def]
  |intro finite_semicategoryI|
  |dest finite_semicategoryD[dest]|
  |elim finite_semicategoryE[elim]|

lemma finite_semicategoryI': 
  assumes "semicategory \<alpha> \<CC>" and "vfinite (\<CC>\<lparr>Obj\<rparr>)" and "vfinite (\<CC>\<lparr>Arr\<rparr>)"
  shows "finite_semicategory \<alpha> \<CC>"
proof-
  interpret semicategory \<alpha> \<CC> by (rule assms(1))
  show ?thesis
  proof(intro finite_semicategoryI)
    show "vfsequence \<CC>" by (simp add: vfsequence_axioms)
    from assms show "finite_digraph \<alpha> (smc_dg \<CC>)"
      by (intro finite_digraphI) (auto simp: slicing_simps)
  qed (auto simp: smc_cs_simps intro: smc_cs_intros)
qed

lemma finite_semicategoryI'': 
  assumes "tiny_semicategory \<alpha> \<CC>" and "vfinite (\<CC>\<lparr>Obj\<rparr>)" and "vfinite (\<CC>\<lparr>Arr\<rparr>)"
  shows "finite_semicategory \<alpha> \<CC>"
  using assms by (intro finite_semicategoryI') 
    (auto intro: smc_cs_intros smc_small_cs_intros)


text\<open>Slicing.\<close>

context finite_semicategory
begin

interpretation dg: finite_digraph \<alpha> \<open>smc_dg \<CC>\<close> by (rule fin_smc_finite_digraph)

lemmas_with [unfolded slicing_simps]:
  fin_smc_Obj_vfinite[smc_small_cs_intros] = dg.fin_dg_Obj_vfinite
  and fin_smc_Arr_vfinite[smc_small_cs_intros] = dg.fin_dg_Arr_vfinite

end


text\<open>Elementary properties.\<close>

sublocale finite_semicategory \<subseteq> tiny_semicategory
  by (rule tiny_semicategoryI)
    (
      auto simp: 
        vfsequence_axioms
        fin_smc_Comp_vdomain         
        fin_smc_finite_digraph 
        finite_digraph.fin_dg_tiny_digraph
        intro: smc_cs_intros smc_cs_simps 
    )

lemmas (in finite_semicategory) fin_smc_tiny_semicategory = 
  tiny_semicategory_axioms

lemmas [smc_small_cs_intros] = finite_semicategory.fin_smc_tiny_semicategory

lemma (in finite_semicategory) fin_smc_in_Vset: "\<CC> \<in>\<^sub>\<circ> Vset \<alpha>"
  by (rule tiny_smc_in_Vset)


text\<open>Size.\<close>

lemma small_finite_semicategories[simp]: "small {\<CC>. finite_semicategory \<alpha> \<CC>}"
proof(rule down)
  show "{\<CC>. finite_semicategory \<alpha> \<CC>} \<subseteq> elts (set {\<CC>. semicategory \<alpha> \<CC>})" 
    by (auto intro: smc_small_cs_intros)
qed

lemma finite_semicategories_vsubset_Vset: 
  "set {\<CC>. finite_semicategory \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset \<alpha>" 
  by (rule vsubsetI) (simp add: finite_semicategory.fin_smc_in_Vset)
 

subsubsection\<open>Opposite finite semicategory\<close>

lemma (in finite_semicategory) finite_semicategory_op: 
  "finite_semicategory \<alpha> (op_smc \<CC>)"
  by (intro finite_semicategoryI', unfold smc_op_simps)
    (auto simp: smc_op_intros smc_small_cs_intros)

lemmas finite_semicategory_op[smc_op_intros] = 
  finite_semicategory.finite_semicategory_op

text\<open>\newpage\<close>

end