(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for digraphs\<close>
theory CZH_DG_Small_Digraph
  imports CZH_DG_Digraph
begin



subsection\<open>Background\<close>

named_theorems dg_small_cs_simps
named_theorems dg_small_cs_intros



subsection\<open>Tiny digraph\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale tiny_digraph = \<Z> \<alpha> + vfsequence \<CC> + Dom: vsv \<open>\<CC>\<lparr>Dom\<rparr>\<close> + Cod: vsv \<open>\<CC>\<lparr>Cod\<rparr>\<close> 
  for \<alpha> \<CC> +
  assumes tiny_dg_length[dg_cs_simps]: "vcard \<CC> = 4\<^sub>\<nat>"  
    and tiny_dg_Dom_vdomain[dg_cs_simps]: "\<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) = \<CC>\<lparr>Arr\<rparr>"    
    and tiny_dg_Dom_vrange: "\<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and tiny_dg_Cod_vdomain[dg_cs_simps]: "\<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and tiny_dg_Cod_vrange: "\<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and tiny_dg_Obj_in_Vset[dg_small_cs_intros]: "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and tiny_dg_Arr_in_Vset[dg_small_cs_intros]: "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"

lemmas [dg_small_cs_intros] = 
  tiny_digraph.tiny_dg_Obj_in_Vset
  tiny_digraph.tiny_dg_Arr_in_Vset


text\<open>Rules.\<close>

lemma (in tiny_digraph) tiny_digraph_axioms'[dg_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "tiny_digraph \<alpha>' \<CC>"
  unfolding assms by (rule tiny_digraph_axioms)

mk_ide rf tiny_digraph_def[unfolded tiny_digraph_axioms_def]
  |intro tiny_digraphI|
  |dest tiny_digraphD[dest]|
  |elim tiny_digraphE[elim]|

lemma tiny_digraphI':
  assumes "digraph \<alpha> \<CC>" and "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "tiny_digraph \<alpha> \<CC>"
  using assms by (meson digraphD(5,6,7,8,9) digraph_def tiny_digraphI)


text\<open>Elementary properties.\<close>

sublocale tiny_digraph \<subseteq> digraph 
proof(rule digraphI)
  from tiny_dg_Obj_in_Vset show "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>" by auto
  fix A B assume "A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "A \<in>\<^sub>\<circ> Vset \<alpha>" "B \<in>\<^sub>\<circ> Vset \<alpha>" 
  then have "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by auto
  with tiny_dg_Arr_in_Vset show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>" by blast
qed 
  (
    cs_concl 
      cs_simp: dg_cs_simps  
      cs_intro: tiny_dg_Cod_vrange tiny_dg_Dom_vrange dg_cs_intros V_cs_intros
  )+

lemmas (in tiny_digraph) tiny_dg_digraph = digraph_axioms

lemmas [dg_small_cs_intros] = tiny_digraph.tiny_dg_digraph


text\<open>Size.\<close>

lemma (in tiny_digraph) tiny_dg_Dom_in_Vset: "\<CC>\<lparr>Dom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from \<Z>_Limit_\<alpha>\<omega> have "\<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"  
    by (simp add: tiny_dg_Arr_in_Vset dg_cs_simps)
  moreover from tiny_dg_Dom_vrange have "\<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto intro: tiny_dg_Obj_in_Vset)
  ultimately show ?thesis 
    by (simp add: Dom.vbrelation_Limit_in_VsetI \<Z>_Limit_\<alpha>\<omega>)
qed

lemma (in tiny_digraph) tiny_dg_Cod_in_Vset: "\<CC>\<lparr>Cod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from \<Z>_Limit_\<alpha>\<omega> have "\<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"  
    by (simp add: tiny_dg_Arr_in_Vset dg_cs_simps)
  moreover from tiny_dg_Cod_vrange have "\<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (auto intro: tiny_dg_Obj_in_Vset)
  ultimately show ?thesis 
    by (simp add: Cod.vbrelation_Limit_in_VsetI \<Z>_Limit_\<alpha>\<omega>)
qed

lemma (in tiny_digraph) tiny_dg_in_Vset: "\<CC> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [dg_cs_intros] = 
    tiny_dg_Obj_in_Vset 
    tiny_dg_Arr_in_Vset
    tiny_dg_Dom_in_Vset
    tiny_dg_Cod_in_Vset
  show ?thesis
    by (subst dg_def) (cs_concl cs_intro: dg_cs_intros V_cs_intros)
qed

lemma small_tiny_digraphs[simp]: "small {\<CC>. tiny_digraph \<alpha> \<CC>}"
proof(rule down)
  show "{\<CC>. tiny_digraph \<alpha> \<CC>} \<subseteq> elts (set {\<CC>. digraph \<alpha> \<CC>})" 
    by (auto intro: dg_small_cs_intros)
qed

lemma tiny_digraphs_vsubset_Vset: "set {\<CC>. tiny_digraph \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  by (rule vsubsetI) (simp add: tiny_digraph.tiny_dg_in_Vset)

lemma (in digraph) dg_tiny_digraph_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_digraph \<beta> \<CC>"
proof(intro tiny_digraphI')
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "digraph \<beta> \<CC>"
    by (intro dg_digraph_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: dg_cs_intros\<close>)+
  show "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<beta>" "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<beta>" 
    by (auto simp: \<beta>.\<Z>_\<beta> assms(2) dg_Obj_in_Vset dg_Arr_in_Vset)
qed


subsubsection\<open>Opposite tiny digraph\<close>

lemma (in tiny_digraph) tiny_digraph_op: "tiny_digraph \<alpha> (op_dg \<CC>)"
  by (intro tiny_digraphI', unfold dg_op_simps)
    (auto simp: tiny_dg_Obj_in_Vset tiny_dg_Arr_in_Vset dg_cs_simps dg_op_intros)

lemmas tiny_digraph_op[dg_op_intros] = tiny_digraph.tiny_digraph_op



subsection\<open>Finite digraph\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
A finite digraph is a generalization of the concept of a finite category,
as presented in nLab 
\cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/finite+category}
}.
\<close>

locale finite_digraph = digraph \<alpha> \<CC> for \<alpha> \<CC> +
  assumes fin_dg_Obj_vfinite[dg_small_cs_intros]: "vfinite (\<CC>\<lparr>Obj\<rparr>)"
    and fin_dg_Arr_vfinite[dg_small_cs_intros]: "vfinite (\<CC>\<lparr>Arr\<rparr>)"

lemmas [dg_small_cs_intros] = 
  finite_digraph.fin_dg_Obj_vfinite
  finite_digraph.fin_dg_Arr_vfinite


text\<open>Rules.\<close>

lemma (in finite_digraph) finite_digraph_axioms'[dg_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "finite_digraph \<alpha>' \<CC>"
  unfolding assms by (rule finite_digraph_axioms)

mk_ide rf finite_digraph_def[unfolded finite_digraph_axioms_def]
  |intro finite_digraphI|
  |dest finite_digraphD[dest]|
  |elim finite_digraphE[elim]|


text\<open>Elementary properties.\<close>

sublocale finite_digraph \<subseteq> tiny_digraph 
proof(rule tiny_digraphI')
  show "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by
      (
        cs_concl cs_intro: 
          dg_small_cs_intros V_cs_intros 
          dg_Obj_vsubset_Vset Limit_vfinite_in_VsetI
      )
  show "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by 
      (
        cs_concl cs_intro: 
          dg_small_cs_intros V_cs_intros 
          dg_Arr_vsubset_Vset Limit_vfinite_in_VsetI
      )
qed (auto intro: dg_cs_intros)

lemmas (in finite_digraph) fin_dg_tiny_digraph = tiny_digraph_axioms

lemmas [dg_small_cs_intros] = finite_digraph.fin_dg_tiny_digraph


text\<open>Size.\<close>

lemma small_finite_digraphs[simp]: "small {\<CC>. finite_digraph \<alpha> \<CC>}"
proof(rule down)
  show "{\<CC>. finite_digraph \<alpha> \<CC>} \<subseteq> elts (set {\<CC>. digraph \<alpha> \<CC>})" 
    by (auto intro: dg_cs_intros)
qed 

lemma finite_digraphs_vsubset_Vset: "set {\<CC>. finite_digraph \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  by 
    (
      force simp: 
        tiny_digraph.tiny_dg_in_Vset finite_digraph.fin_dg_tiny_digraph
    )


subsubsection\<open>Opposite finite digraph\<close>

lemma (in finite_digraph) fininte_digraph_op: "finite_digraph \<alpha> (op_dg \<CC>)"
  by (intro finite_digraphI, unfold dg_op_simps)
    (auto simp: dg_small_cs_intros dg_op_intros)

lemmas fininte_digraph_op[dg_op_intros] = finite_digraph.fininte_digraph_op

text\<open>\newpage\<close>

end