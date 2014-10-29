(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs_sig.thy                                                  *)
(* Authors: Simon Foster, University of York                                  *)
(******************************************************************************)

header {* UTP Designs Signature *}

theory utp_designs_sig
imports 
  "../../utp_base"
begin

text {* Most predicates need a boolean type, so we here set the appropriate sort constraint *}

default_sort BOOL_SORT

subsection {* Design Alphabet *}

abbreviation "ok  \<equiv> MkBoolV ''ok'' True"
abbreviation "OKAY \<equiv> {ok\<down>,ok\<down>\<acute>}"

subsection {* Design Signature *}

definition DesignD :: 
  "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" (infixr "\<turnstile>" 60) where
"p \<turnstile> q = `$ok \<and> p \<Rightarrow> $ok\<acute> \<and> q`"

definition SkipDA :: "'a uvar set \<Rightarrow> 'a upred" where
"SkipDA vs = true \<turnstile> II\<^bsub>(vs - OKAY)\<^esub>"

notation SkipDA ("II\<^bsub>D[_]\<^esub>")

abbreviation SkipD :: "'a upred" where
"SkipD \<equiv> SkipDA REL_VAR"

notation SkipD ("II\<^sub>D")

abbreviation AssignDO ::
  "'a uvar \<Rightarrow> 'a uexpr \<Rightarrow> 'a upred" ("(_ /:=\<^sub>o/ _)") where
"AssignDO x v \<equiv> x :=\<^bsub>(REL_VAR - OKAY)\<^esub> v"

abbreviation AssignDOt ::
  "('a :: DEFINED, 'm) pvar \<Rightarrow> ('a, 'm) pexpr \<Rightarrow> 'm upred" where
"AssignDOt x v \<equiv> x\<down> :=\<^sub>o v\<down>"

definition AssignD ::
  "'a uvar \<Rightarrow> 'a uexpr \<Rightarrow> 'a upred" ("(_ /:=\<^sub>D/ _)") where
"AssignD x v = (true \<turnstile> x :=\<^sub>o v)"

abbreviation AssignDt :: 
  "('a :: DEFINED, 'm) pvar \<Rightarrow> ('a, 'm) pexpr \<Rightarrow> 'm upred" where
"AssignDt x v \<equiv> AssignD x\<down> v\<down>"

definition BotD :: "'a upred" ("\<bottom>\<^sub>D") where
"BotD = true"

definition TopD :: "'a upred" ("\<top>\<^sub>D") where
"TopD = `\<not> $ok`"

definition JA_pred :: "'a uvar set \<Rightarrow> 'a upred" ("J\<^bsub>_\<^esub>") where
"J\<^bsub>vs\<^esub> \<equiv> `($ok \<Rightarrow> $ok\<acute>) \<and> II\<^bsub>vs - OKAY\<^esub>`"

abbreviation J_pred :: "'a upred" ("J") where
"J \<equiv> J\<^bsub>REL_VAR\<^esub>"

abbreviation ok'_true :: 
  "'a upred \<Rightarrow> 'a upred" ("_\<^sup>t" [1000] 1000) where
"p\<^sup>t \<equiv> `p[true/ok\<acute>]`"

abbreviation ok'_false :: 
  "'a upred \<Rightarrow> 'a upred" ("_\<^sup>f" [1000] 1000) where
"p\<^sup>f \<equiv> `p[false/ok\<acute>]`"

abbreviation ok_true_ok'_true :: 
  "'a upred \<Rightarrow> 'a upred" ("_\<^bsup>tt\<^esup>" [1000] 1000) where
"p\<^bsup>tt\<^esup> \<equiv> `p[true/ok][true/ok\<acute>]`"

abbreviation ok_true_ok'_false :: 
  "'a upred \<Rightarrow> 'a upred" ("_\<^bsup>tf\<^esup>" [1000] 1000) where
"p\<^bsup>tf\<^esup> \<equiv> `p[true/ok][false/ok\<acute>]`"

definition ParallelD :: 
  "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" (infixr "\<parallel>" 100) where 
"P \<parallel> Q = (\<not>\<^sub>p P\<^sup>f \<and>\<^sub>p \<not>\<^sub>p Q\<^sup>f) \<turnstile> (P\<^sup>t \<and>\<^sub>p Q\<^sup>t)"

definition WF_VALID_MERGE :: "('a uvar set * 'a upred) set" where
"WF_VALID_MERGE = UNIV" (* fst M undashed only *)

definition ParallelMergeD ::
  "'a upred => ('a uvar set * 'a upred) => 'a upred \<Rightarrow> 'a upred"
    (infix "\<parallel>\<^bsub>_\<^esub>" 100) where
"P \<parallel>\<^bsub>M\<^esub> Q = ((
  (add_sub ''0'' on (dash ` fst M) \<bullet> P) \<parallel>
  (add_sub ''1'' on (dash ` fst M) \<bullet> Q)) \<and>\<^sub>p
    II\<^bsub>fst M \<union> (dash ` fst M)\<^esub>) ;\<^sub>R snd M"

declare BotD_def [eval,evalr,evalrx,evalpp,evalpr]
declare TopD_def [eval,evalr,evalrx,evalpp,evalpr]
declare DesignD_def [eval,evalr,evalrx,evalpp,evalpr]
declare JA_pred_def [eval,evalr,evalrx,evalpp,evalpr]
declare SkipDA_def [eval,evalr,evalrx,evalpp,evalpr]
declare AssignD_def [eval,evalr,evalrx,evalpp,evalpr]
declare ParallelD_def [eval,evalr,evalrx,evalpp,evalpr]

syntax
  "_n_upred_desbot"    :: "n_upred" ("\<bottom>\<^sub>D")
  "_n_upred_destop"    :: "n_upred" ("\<top>\<^sub>D")
  "_n_upred_design"    :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<turnstile>" 30)
  "_n_upred_ok'_true"  :: "n_upred \<Rightarrow> n_upred" ("_\<^sup>t" [1000] 1000)
  "_n_upred_ok'_false" :: "n_upred \<Rightarrow> n_upred" ("_\<^sup>f" [1000] 1000)
  "_n_upred_ok_true_ok'_true"  :: "n_upred \<Rightarrow> n_upred" ("_\<^bsup>tt\<^esup>" [1000] 1000)
  "_n_upred_ok_true_ok'_false" :: "n_upred \<Rightarrow> n_upred" ("_\<^bsup>tf\<^esup>" [1000] 1000)

  "_n_upred_SkipD"     :: "n_upred" ("II\<^sub>D")
  "_n_upred_assignd"   :: "('a, 'm) pvar \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_ :=\<^sub>D _" [100] 100)
  "_n_upred_assigndo"  :: "('a, 'm) pvar \<Rightarrow> n_pexpr \<Rightarrow> n_upred" ("_ :=\<^sub>o _" [100] 100)
  "_n_upred_J"         :: "n_upred" ("J")
  "_n_upred_parallel"  :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infix "\<parallel>" 50)

translations
  "_n_upred_desbot"       == "CONST BotD"
  "_n_upred_destop"       == "CONST TopD"
  "_n_upred_design p q"   == "CONST DesignD p q"
  "_n_upred_ok'_true p"   == "CONST ok'_true p"
  "_n_upred_ok'_false p"  == "CONST ok'_false p"
  "_n_upred_ok_true_ok'_true p"   == "CONST ok_true_ok'_true p"
  "_n_upred_ok_true_ok'_false p"  == "CONST ok_true_ok'_false p"
  "_n_upred_SkipD"        == "CONST SkipD"
  "_n_upred_assignd x v"  == "CONST AssignDt x v"
  "_n_upred_assigndo x v" == "CONST AssignDOt x v"
  "_n_upred_J"            == "CONST J_pred"
  "_n_upred_parallel P Q" == "CONST ParallelD P Q"

text {* Lift design syntax to procedure level *}

definition "DesignO p q = (\<lambda> r. DesignD (p r) (q r))"

syntax
  "_n_uproc_design" :: "n_uproc \<Rightarrow> n_uproc \<Rightarrow> n_uproc" (infixr "\<turnstile>" 30)

translations
  "_n_uproc_design p q" == "CONST DesignO p q"

declare DesignO_def [eval, evalpp, evalr, evalpr, uop_defs]

subsection {* Closure / UNREST theorems *}

lemma UNREST_OKAY [unrest]:
  "OKAY \<sharp> p \<Longrightarrow> UNREST {ok\<down>} p"
  "OKAY \<sharp> p \<Longrightarrow> UNREST {ok\<down>\<acute>} p"
  by (auto intro:unrest UNREST_subset)

lemma UNREST_SkipRA_OKAY [unrest]: 
  "OKAY \<sharp> II\<^bsub>REL_VAR - OKAY\<^esub>"
  apply (rule UNREST_subset)
  apply (rule UNREST_SkipRA)
  apply (simp)
done

lemma UNREST_TopD [unrest]:
  "ok\<down> \<notin> vs \<Longrightarrow> vs \<sharp> \<top>\<^sub>D"
  by (simp add:TopD_def unrest)

lemma UNREST_SkipD_NON_REL_VAR [unrest]:
  "NON_REL_VAR \<sharp> II\<^sub>D"
  apply (simp add:SkipDA_def DesignD_def)
  apply (force simp add:PVAR_VAR_MkPVAR intro: unrest)
done

lemma UNREST_DesignD [unrest]:
  "\<lbrakk> vs \<sharp> p; vs \<sharp> q; ok\<down> \<notin> vs; ok\<down>\<acute> \<notin> vs \<rbrakk>
   \<Longrightarrow> vs \<sharp> (p \<turnstile> q)"
  by (simp add:DesignD_def unrest)

lemma UNREST_ParallelD [unrest]:
  "\<lbrakk> vs \<sharp> p; vs \<sharp> q; ok\<down> \<notin> vs; ok\<down>\<acute> \<notin> vs \<rbrakk>
   \<Longrightarrow> vs \<sharp> (p \<parallel> q)"
  by (auto intro!:unrest closure simp add:typing defined closure ParallelD_def)

lemma SubstP_UNREST_OKAY [usubst]:
  "\<lbrakk> x \<in> OKAY; OKAY \<sharp> p; v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> p[v/\<^sub>px] = p"
  by (utp_pred_tac)

lemma UNREST_JA [unrest]:
  "UNREST (VAR - (vs \<union> OKAY)) J\<^bsub>vs\<^esub>"
  by (auto intro:unrest UNREST_subset simp add:JA_pred_def)

lemma UNREST_SkipDA [unrest]:
  "UNREST (VAR - (vs \<union> OKAY)) II\<^bsub>D[vs]\<^esub>"
  by (auto intro:unrest UNREST_subset simp add:SkipDA_def)

lemma TopD_rel_closure [closure]:
  "\<top>\<^sub>D \<in> WF_RELATION"
  by (simp add:TopD_def closure)

lemma TopD_cond_closure [closure]: 
  "\<top>\<^sub>D \<in> WF_CONDITION"
  by (simp add:TopD_def closure)

lemma DesignD_rel_closure [closure]:
  "\<lbrakk>P \<in> WF_RELATION; Q \<in> WF_RELATION\<rbrakk> \<Longrightarrow> P \<turnstile> Q \<in> WF_RELATION"
  by (simp add:DesignD_def closure)

lemma SkipD_rel_closure [closure]:
  "II\<^sub>D \<in> WF_RELATION"
  by (auto intro:closure simp add:SkipDA_def)

lemma EvalP_AssignRA1 [eval]:
  assumes "HOMOGENEOUS xs" "xs \<subseteq> REL_VAR" 
          "x \<in> in(xs)" "REL_VAR - in(xs) \<sharp> e" 
  shows "\<lbrakk>x :=\<^bsub>xs\<^esub> e\<rbrakk>b = (\<forall> v \<in> in(xs). if (v = x) then \<langle>b\<rangle>\<^sub>b (v\<acute>) = (vcoerce (\<lbrakk>e\<rbrakk>\<^sub>eb) x)
                                                 else \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>b\<rangle>\<^sub>b v)"
  using assms
  apply (subgoal_tac "x \<in> D\<^sub>0")
  apply (subst AssignRA_alt_def)
  apply (simp_all)
  apply (force simp add:var_defs)
  apply (force simp add:var_defs)
  apply (rule UNREST_EXPR_subset)
  apply (simp)
  apply (force simp add:var_defs)
  apply (simp add:eval evale closure)
  apply (safe)
  apply (drule_tac x="v" in bspec)
  apply (simp_all add:var_dist)
  apply (force simp add:var_defs)
done

lemma AssignRA_unfold:
  assumes
    "HOMOGENEOUS xs" "xs \<subseteq> REL_VAR"
    "x \<in> in(xs)" "y \<in> in(xs)" "x \<noteq> y" 
    "REL_VAR - in(xs) \<sharp> v" "{y} \<sharp> v"
  shows "AssignRA x xs v = (($\<^sub>ey\<acute> ==\<^sub>p $\<^sub>ey) \<and>\<^sub>p (AssignRA x (xs-{y,y\<acute>}) v))"
  using assms
  apply (subgoal_tac "y \<in> D\<^sub>0")
  apply (utp_pred_tac)
  apply (subst EvalP_AssignRA1)
  apply (simp_all add:closure var_dist)
  apply (metis (full_types) Un_Diff_Int le_sup_iff)
  apply (rule UNREST_EXPR_subset[of "{y} \<union> (REL_VAR - in xs)"])
  apply (metis UNREST_EXPR_union)
  apply (auto)
  apply (metis set_rev_mp utp_var.in_UNDASHED)
done

lemma AssignR_as_AssignRA:
  "\<lbrakk> x \<in> D\<^sub>0; D\<^sub>1 \<sharp> v; NON_REL_VAR \<sharp> v \<rbrakk> \<Longrightarrow> (x :=\<^sub>R v) = (x :=\<^bsub>REL_VAR\<^esub> v)"
  apply (rule EvalP_intro)
  apply (subst EvalP_AssignR1)
  apply (subst EvalP_AssignRA1)
  apply (simp_all add:var_dist unrest)
  apply (metis Diff_subset_conv UNREST_EXPR_subset subset_refl)
done

(* This should probably be shown for untyped expressions *)

lemma AssignD_alt_def:
  fixes x :: "('a :: DEFINED, 'm) pvar" 
  assumes "TYPEUSOUND('a, 'm)"
          "x \<in> PUNDASHED" "x\<down> \<noteq> ok\<down>" "{ok\<down>} \<sharp> v"
          "D\<^sub>1 \<sharp> v" "NON_REL_VAR \<sharp> v"
  shows "`x :=\<^sub>D v` = `(true \<turnstile> x := v)`"
proof -
  have "`x :=\<^sub>D v` = `true \<turnstile> x :=\<^bsub>REL_VAR - OKAY\<^esub> v`"
    by (metis AssignD_def)

  also have "... = `true \<turnstile> ($ok\<acute> = $ok \<and> x :=\<^bsub>REL_VAR - OKAY\<^esub> v)`"
    by (utp_poly_tac)

  also from assms
  have "... = `true \<turnstile> (x :=\<^bsub>REL_VAR\<^esub> v)`"
    apply (subst AssignRA_unfold[of _ _ "ok\<down>"]) back
    apply (simp_all add:closure var_dist typing defined unrest)
    apply (metis Diff_cancel UNDASHED_DASHED_minus(2) UNREST_PExprE Un_commute Un_empty_right union_minus)
    apply (metis (lifting, no_types) EqualP_as_EqualPE PVAR_VAR_pvdash PVarPE_erasure UTypedef_bool pvaux_MkPVAR pvaux_pvdash)
  done

  also from assms
  have "... = `true \<turnstile> (x := v)`"
    by (metis AssignR_as_AssignRA PAssignF_upd_def PUNDASHED_def UNREST_PExprE mem_Collect_eq)

  finally show ?thesis by this
qed

lemma AssignD_rel_closure [closure]:
  "\<lbrakk> x \<in> UNDASHED; NON_REL_VAR \<union> OKAY \<sharp> v; v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow>
     x :=\<^sub>D v \<in> WF_RELATION"
  by (auto intro!:DesignD_rel_closure intro:closure simp add:AssignD_def)

theorem J_closure [closure]:
  "J \<in> WF_RELATION"
  by (simp add:JA_pred_def closure)

lemma ParallelD_rel_closure [closure]:
  "\<lbrakk> P \<in> WF_RELATION; Q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> P \<parallel> Q \<in> WF_RELATION"
  by (simp add:ParallelD_def unrest typing closure defined)

lemma TopD_TrueP_uniqs [simp]:
  "true \<noteq> \<top>\<^sub>D" "\<top>\<^sub>D \<noteq> true"
  by (utp_poly_tac, rule_tac x="\<B>(ok :=\<^sub>* True)" in exI, simp add:typing defined inju)+

lemma TopD_FalseP_uniqs [simp]:
  "false \<noteq> \<top>\<^sub>D" "\<top>\<^sub>D \<noteq> false"
  by (utp_poly_tac, rule_tac x="\<B>(ok :=\<^sub>* False)" in exI, simp add:typing defined inju)+

lemma PExprP_erasure [erasure]:
  fixes e :: "('a :: DEFINED, 'm :: TYPED_MODEL) pexpr"
  assumes "TYPEUSOUND('a, 'm)"
  shows "PExprP (EqualPE e f) = EqualP (e\<down>) (f\<down>)"
  using assms by (utp_poly_tac)

lemma SkipDA_alt_def: 
  assumes "ok\<down> \<in> vs" "HOMOGENEOUS vs"
  shows "II\<^bsub>D[vs]\<^esub> = `true \<turnstile> II\<^bsub>vs\<^esub>`"
proof -
  have "II\<^bsub>D[vs]\<^esub> = `true \<turnstile> II\<^bsub>vs-{ok\<down>, ok\<down>\<acute>}\<^esub>`"
    by (simp add:SkipDA_def)

  also have "... = `true \<turnstile> ($ok\<acute> = $ok \<and> II\<^bsub>vs-OKAY\<^esub>)`"
    by (utp_poly_tac)

  also from assms have "... = `true \<turnstile> II\<^bsub>vs\<^esub>`"
    apply (subst SkipRA_unfold[of "ok\<down>"]) back
    apply (simp_all add:closure)
    apply (metis MkPlain_UNDASHED PVAR_VAR_MkPVAR hom_alphabet_undash)
    apply (simp add:erasure typing defined closure)
  done

  finally show ?thesis .
qed

theorem SkipD_def: "II\<^sub>D = `true \<turnstile> II`"
  by (simp add:SkipDA_alt_def SkipR_as_SkipRA closure)

end
