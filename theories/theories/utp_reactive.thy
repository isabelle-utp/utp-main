(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_reactive.thy                                                     *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* Reactive Processes *}

theory utp_reactive
imports 
  utp_designs
  utp_theory
begin

class REACTIVE_SORT = BOOL_SORT + LIST_SORT + FSET_SORT + STRING_LIST_SORT + MINUS_SORT

default_sort REACTIVE_SORT

abbreviation "wait \<equiv> MkPlain ''wait'' (BoolType) True"
abbreviation tr :: "'a::REACTIVE_SORT VAR" where
"tr   \<equiv> MkPlain ''tr'' (ListType StringType) True"

definition SkipREA :: "'a WF_PREDICATE" where
"SkipREA = `(\<not> ok \<and> ($tr \<le> $tr\<acute>)) \<or> (ok\<acute> \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"

syntax 
  "_upred_skiprea" :: "upred" ("II\<^bsub>rea\<^esub>")

translations
  "_upred_skiprea" == "CONST SkipREA"

definition R1 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R1(P) = `P \<and> ($tr \<le> $tr\<acute>)`"

definition R2 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R2(P) = `P[\<langle>\<rangle> / tr][($tr\<acute> - $tr) / tr\<acute>]`"

definition R3 :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R3(P) = `II\<^bsub>rea\<^esub> \<lhd> $wait \<rhd> P`"

abbreviation "R \<equiv> R1 \<circ> R2 \<circ> R3"

syntax
  "_uexpr_subste"       :: "uexpr \<Rightarrow> uexpr \<Rightarrow> 'a VAR \<Rightarrow> uexpr" ("(_[_'/_])" [999,999] 1000)

translations
  "_uexpr_subste e v x" == "CONST SubstE e v x"

lemma SubstP_ExprP [usubst]:
  "(ExprP e)[v|x] = ExprP (e[v|x])"
  by (utp_pred_tac, utp_expr_tac)

lemma SkipREA_CondR_SkipR: 
  "`II\<^bsub>rea\<^esub>` = `II \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)`"
proof -

  have "`II \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)` = `($okay\<acute> = $okay \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)`"
    by (metis Diff_cancel ExistsP_empty HOMOGENEOUS_REL_VAR MkPlain_UNDASHED SkipRA.rep_eq SkipRA_unfold UnCI hom_alphabet_undash)

  also have "... = `($okay\<acute> = $okay \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)[true/okay] \<lhd> $okay \<rhd> (($tr \<le> $tr\<acute>)[false/okay])`"
    by (rule CondR_VarP_aux, simp_all add:typing defined)

  also have "... = `(ok \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<lhd> ok \<rhd> ($tr \<le> $tr\<acute>)`"
  proof -

    have "(ulesseq :: 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<in> FUNC2 (ListType StringType) (ListType StringType) BoolType"
      by (simp add: closure) 

    thus ?thesis
      apply (insert SubstE_Op2E[of "VarE tr :: 'b WF_EXPRESSION" "ListType StringType" "VarE tr\<acute>" "ListType StringType" "ulesseq" BoolType "FalseE" "okay"])

    apply (simp add:usubst typing defined closure var_simps)


  oops (* FIXME: Can't finish the step without more laws about prefix *)

end