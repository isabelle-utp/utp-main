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
abbreviation tr :: "'a UTYPE \<Rightarrow> 'a::REACTIVE_SORT VAR" where
"tr a \<equiv> MkPlain ''tr'' (ListType a) True"

definition SkipREA :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE" where
"SkipREA a = `(\<not> ok \<and> ($tr a \<le> $(tr a)\<acute>)) \<or> (ok\<acute> \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)`"

syntax 
  "_upred_skiprea" :: "'a UTYPE \<Rightarrow> upred" ("II\<^bsub>rea'(_')\<^esub>")
  "_upred_tr"      :: "'a UTYPE \<Rightarrow> uexpr" ("tr\<^bsub>_\<^esub>")

translations
  "_upred_skiprea a" == "CONST SkipREA a"
  "_upred_tr a" == "CONST VarE (CONST tr a)"

text {* R1 ensures that the trace only gets longer *}

definition R1 :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R1 a P = `P \<and> (tr\<^bsub>a\<^esub> \<le> tr\<^bsub>a\<^esub>\<acute>)`"

text {* R2 ensures that the trace only gets longer *}

definition R2 :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R2 a P = `P[\<langle>\<rangle> / tr a][(tr\<^bsub>a\<^esub>\<acute> - tr\<^bsub>a\<^esub>) / (tr a)\<acute>]`"

definition R3 :: "'a UTYPE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"R3 a P = `II\<^bsub>rea(a)\<^esub> \<lhd> $wait \<rhd> P`"

abbreviation "R a \<equiv> R1 a \<circ> R2 a \<circ> R3 a"

syntax
  "_uexpr_subste"       :: "uexpr \<Rightarrow> uexpr \<Rightarrow> 'a VAR \<Rightarrow> uexpr" ("(_[_'/_])" [999,999] 1000)

translations
  "_uexpr_subste e v x" == "CONST SubstE e v x"

lemma SubstP_ExprP [usubst]:
  "(ExprP e)[v|x] = ExprP (e[v|x])"
  by (utp_pred_tac, utp_expr_tac)

lemma SkipREA_CondR_SkipR: 
  "`II\<^bsub>rea(a)\<^esub>` = `II \<lhd> ok \<rhd> (tr\<^bsub>a\<^esub> \<le> tr\<^bsub>a\<^esub>\<acute>)`"
proof -

  have "`II \<lhd> ok \<rhd> (tr\<^bsub>a\<^esub> \<le> tr\<^bsub>a\<^esub>\<acute>)` = `($okay\<acute> = $okay \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<lhd> ok \<rhd> (tr\<^bsub>a\<^esub> \<le> tr\<^bsub>a\<^esub>\<acute>)`"
    by (metis Diff_cancel ExistsP_empty HOMOGENEOUS_REL_VAR MkPlain_UNDASHED SkipRA.rep_eq SkipRA_unfold UnCI hom_alphabet_undash)

  also have "... = `($okay\<acute> = $okay \<and> II\<^bsub>REL_VAR - OKAY\<^esub>)[true/okay] \<lhd> $okay \<rhd> ((tr\<^bsub>a\<^esub> \<le> tr\<^bsub>a\<^esub>\<acute>)[false/okay])`"
    by (rule CondR_VarP_aux, simp_all add:typing defined)

  also have "... = `(ok \<and> II\<^bsub>REL_VAR - OKAY\<^esub>) \<lhd> ok \<rhd> (tr\<^bsub>a\<^esub> \<le> tr\<^bsub>a\<^esub>\<acute>)`"
  proof -

    have "(ulesseq :: 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<in> FUNC2 (ListType StringType) (ListType StringType) BoolType"
      by (simp add: closure) 

    thus ?thesis
(*
      apply (insert SubstE_Op2E[of "VarE tr :: 'b WF_EXPRESSION" "ListType StringType" "VarE tr\<acute>" "ListType StringType" "ulesseq" BoolType "FalseE" "okay"])

    apply (simp add:usubst typing defined closure var_simps)
*)

  oops (* FIXME: Can't finish the step without more laws about prefix *)

end