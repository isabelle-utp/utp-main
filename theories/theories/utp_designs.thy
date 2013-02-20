(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
(******************************************************************************)

header {* UTP Designs *}

theory utp_designs
imports 
  utp_theory
  "../alpha/utp_alpha_laws" 
  "../tactics/utp_alpha_tac" 
  "../tactics/utp_alpha_expr_tac" 
  "../parser/utp_alpha_pred_parser"
begin

(* Everything in here requires booleans *)
default_sort BOOL_SORT

subsection {* Constructs *}

definition "okay  \<equiv> MkVar (MkName ''okay'' 0 NoSub) BoolType True"
abbreviation "okay' \<equiv> dash okay"
abbreviation "okay'' \<equiv> dash (dash okay)"

lemma okay_simps [simp]: 
  "okay \<noteq> okay'" "okay' \<noteq> okay" 
  "okay \<noteq> okay''" "okay'' \<noteq> okay" 
  "okay' \<noteq> okay''" "okay'' \<noteq> okay'"
  "okay \<in> UNDASHED" "okay' \<in> DASHED" "okay'' \<in> DASHED_TWICE"
  "MkBool True \<rhd> okay" "MkBool False \<rhd> okay"
  "MkBool True \<rhd> okay'" "MkBool False \<rhd> okay'"
  "TrueE \<rhd>\<^sub>e okay" "FalseE \<rhd>\<^sub>e okay"
  "TrueE \<rhd>\<^sub>e okay'" "FalseE \<rhd>\<^sub>e okay'"
  "TrueAE \<rhd>\<^sub>\<alpha> okay" "FalseAE \<rhd>\<^sub>\<alpha> okay"
  "TrueAE \<rhd>\<^sub>\<alpha> okay'" "FalseAE \<rhd>\<^sub>\<alpha> okay'"
  "type okay = BoolType" "type okay' = BoolType"
  "aux okay" "aux okay'"
  by (force intro:typing defined simp add:okay_def UNDASHED_def DASHED_def DASHED_TWICE_def var_defs)+

abbreviation OK where "OK \<equiv> \<lbrace>okay, okay'\<rbrace>"

lemma REL_ALPHABET_OK [closure]: "OK \<in> REL_ALPHABET"
  by (simp add:REL_ALPHABET_def)

lemma HOM_ALPHA_OK [closure]: "HOM_ALPHA OK"
  by (auto simp add:HOM_ALPHA_unfold var_simps var_dist)

lemma HOM_ALPHABET_OK [closure]: "OK \<in> HOM_ALPHABET"
  by (simp add:HOM_ALPHABET_def, simp add:closure)

abbreviation ok_true :: 
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("_\<^sup>t" [150]) where
"p\<^sup>t \<equiv> `p[true/okay']`"

abbreviation ok_false :: 
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("_\<^sup>f" [150]) where
"p\<^sup>f \<equiv> `p[false/okay']`"

abbreviation "ok  \<equiv> VarA okay"
abbreviation "ok' \<equiv> VarA okay'"
abbreviation "ok'' \<equiv> VarA okay''"

definition DesignD :: 
"'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
 'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
 'VALUE WF_ALPHA_PREDICATE" (infixr "\<turnstile>" 60) where
"p \<turnstile> q = `ok \<and> p \<Rightarrow> ok' \<and> q`"

definition SkipD ::
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("IID") where
"IID a \<equiv> true a \<turnstile> II\<alpha> a"

declare DesignD_def [evala]
declare SkipD_def [evala]

syntax
  "_uapred_design" :: "uapred \<Rightarrow> uapred \<Rightarrow> uapred" (infixr "\<turnstile>" 50)
  "_uapred_skipd"  :: "'a ALPHABET \<Rightarrow> uapred" ("IID\<^bsub>_\<^esub>")

translations
  "_uapred_skipd"       == "CONST SkipD"
  "_uapred_design p q"  => "CONST DesignD p q"


(*
definition Mk_ALPHA_FUNCTION :: 
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_FUNCTION \<Rightarrow> 'VALUE ALPHA_FUNCTION" where
"Mk_ALPHA_FUNCTION a f = (\<lambda> p. Abs_WF_ALPHA_PREDICATE (\<alpha> p, f (\<pi> p)))"
*)

definition "H1   \<equiv> \<lambda> p. `ok \<Rightarrow> p`"
definition "J a  \<equiv> `(ok \<Rightarrow> ok') \<and> II\<^bsub>a -\<^sub>f OK\<^esub>`"
definition "H2  \<equiv> \<lambda> p. [p\<^sup>t \<Rightarrow>\<alpha> (p\<^sup>f)]\<alpha>"
definition "H2' \<equiv> \<lambda> p. (p ;\<alpha> J (homr (\<alpha> p)))"
definition "H3  \<equiv> \<lambda> p. `p ; IID\<^bsub>\<alpha> p\<^esub>`"
definition "H4  \<equiv> \<lambda> p. `p ; true\<^bsub>\<alpha> p\<^esub> \<Rightarrow> true\<^bsub>\<alpha> p\<^esub>`"

lemma ok_rel_closure [closure]:
  "ok \<in> WF_RELATION"
  by (auto intro:closure)

lemma ok'_rel_closure [closure]:
  "ok' \<in> WF_RELATION"
  by (auto intro:closure)

lemma DesignD_rel_closure [closure]:
  "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION \<rbrakk> \<Longrightarrow>
   p \<turnstile> q \<in> WF_RELATION"
  by (auto intro: closure simp add:DesignD_def)

lemma SkipD_rel_closure [closure]:
  "a \<in> REL_ALPHABET \<Longrightarrow>
   IID a \<in> WF_RELATION"
  by (simp add:SkipD_def closure)

lemma H1_rel_closure [closure]:
  "p \<in> WF_RELATION \<Longrightarrow>
   H1 p \<in> WF_RELATION"
  by (simp add:H1_def closure)

lemma J_rel_closure [closure]:
  "a \<in> REL_ALPHABET \<Longrightarrow> J a \<in> WF_RELATION"
  by (simp add:J_def closure)

lemma H2_rel_closure [closure]:
  "p \<in> WF_RELATION \<Longrightarrow>
   H2 p \<in> WF_RELATION"
  by (simp add:H2_def closure)

lemma H2'_rel_closure [closure]:
  "p \<in> WF_RELATION \<Longrightarrow>
   H2' p \<in> WF_RELATION"
  by (simp add:H2'_def closure)

lemma DesignD_alphabet [alphabet]:
  "\<alpha> (r1 \<turnstile> r2) = \<alpha> r1 \<union>\<^sub>f \<alpha> r2 \<union>\<^sub>f OK"
  by (auto simp add:DesignD_def alphabet)

lemma J_alphabet [alphabet]:
  "a \<in> REL_ALPHABET \<Longrightarrow> \<alpha> (J a) = a \<union>\<^sub>f OK"
  by (auto simp add:J_def alphabet closure)

definition DESIGN_ALPHABET :: "'TYPE ALPHABET set"
where "DESIGN_ALPHABET = REL_ALPHABET \<inter> {a. OK \<subseteq>\<^sub>f a}"

lemma DESIGN_ALPHABET_finsert [simp]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> finsert okay a = a"
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> finsert okay' a = a"
  by (auto simp add:DESIGN_ALPHABET_def)

lemma DESIGN_ALPHABET_REL_ALPHABET [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> a \<in> REL_ALPHABET"
  apply (unfold DESIGN_ALPHABET_def)
  apply (auto)
done

lemma DESIGN_ALPHABET_ok [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> okay \<in>\<^sub>f a"
  apply (unfold DESIGN_ALPHABET_def)
  apply (auto)
done

lemma DESIGN_ALPHABET_ok' [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> okay' \<in>\<^sub>f a"
  apply (unfold DESIGN_ALPHABET_def)
  apply (auto)
done

lemma DESIGN_ALPHABET_homr [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> homr a \<in> DESIGN_ALPHABET"
  apply (unfold DESIGN_ALPHABET_def)
  apply (simp add:closure)
  apply (auto simp add:hom_right_def closure)
  apply (metis Int_iff imageI okay_simps(8) out_vars_def undash_dash)
  apply (metis IntI okay_simps(8) out_vars_def)
done

lemma DESIGN_ALPHABET_homl [closure]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> homl a \<in> DESIGN_ALPHABET"
  apply (unfold DESIGN_ALPHABET_def)
  apply (simp add:closure)
  apply (auto simp add:hom_left_def closure)
  apply (metis Int_iff in_vars_def okay_simps(7))
  apply (metis Int_iff imageI in_vars_def okay_simps(7))
done

lemma extreme_point_true:
  "`false\<^bsub>a \<^esub>\<turnstile> false\<^bsub>a\<^esub>` = `false\<^bsub>a\<^esub> \<turnstile> true\<^bsub>a\<^esub>`"
  by (utp_alpha_tac2)

lemma extreme_point_nok:
  "`true\<^bsub>a\<^esub> \<turnstile> false\<^bsub>a\<^esub>` = `(\<not> ok) \<oplus> OK \<union>\<^sub>f a`"
  by (utp_alpha_tac2)

lemma export_precondition:
  "`p \<turnstile> q` = `p \<turnstile> (p \<and> q)`"
  apply (utp_alpha_tac2)
  apply (utp_pred_tac)
done

lemma BoolType_var_aux_cases [elim]:
  "\<lbrakk> type x = BoolType
   ; \<not> aux x \<Longrightarrow> P
   ; \<langle>b\<rangle>\<^sub>b x = TrueV \<Longrightarrow> P
   ; \<langle>b\<rangle>\<^sub>b x = FalseV \<Longrightarrow> P \<rbrakk> 
   \<Longrightarrow> P"
  by (metis MkBool_cases binding_value_alt var_compat_def)

lemma EvalP_BoolType_cases [intro]:
  "\<lbrakk> type x = BoolType; aux x; \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b TrueV)) ; \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b FalseV)) \<rbrakk> \<Longrightarrow> \<lbrakk>p\<rbrakk>b"
  by (metis (lifting) BoolType_var_aux_cases binding_upd_simps(2))

(*
lemma "\<lbrakk> \<lbrakk>p\<rbrakk>b; \<And> x t. \<lbrakk> v : type x; \<D> v; \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (simp add:EvalP_def)
*)

lemma BoolType_aux_var_split_imp:
  "\<lbrakk> type x = BoolType; aux x \<rbrakk> 
  \<Longrightarrow> `[p]` = `[$x = true \<Rightarrow> p] \<and> [$x = false \<Rightarrow> p]`"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (simp add:evala eval closure evale typing defined)
  apply (auto)
  apply (metis BOOL_SORT_class.Defined BOOL_SORT_class.Inverse BoolType_var_aux_cases MkBool_cases MkBool_type)
done

lemma BoolType_aux_var_split:
  "\<lbrakk> type x = BoolType; aux x \<rbrakk> 
  \<Longrightarrow> `[p]` = `[p[false/x] \<and> p[true/x]]`"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (simp add:evala eval alphabet closure evale typing defined)
  apply (auto)
done

lemma BoolType_aux_var_split_imp_intro:
  "\<lbrakk> type x = BoolType; aux x; [$x = true \<Rightarrow> p]; [$x = false \<Rightarrow> p] \<rbrakk> \<Longrightarrow>
  [p]"
  by (auto simp add:evala eval alphabet closure evale typing defined)

lemma BoolType_aux_var_split_intro:
  "\<lbrakk> type x = BoolType; aux x; [p[false/x] \<and> p[true/x]] \<rbrakk> \<Longrightarrow>
  [p]"
  by (auto simp add:evala eval alphabet closure evale typing defined)

(*
lemma [evala]: "\<epsilon> e = \<lbrakk>e\<rbrakk>\<alpha>\<epsilon>"
  by (simp add:EvalAE_def)
*)

lemma [evala]: 
  "ok[false|okay]\<alpha> = FALSE" "ok[true|okay]\<alpha> = TRUE"
  "ok'[false|okay']\<alpha> = FALSE" "ok'[true|okay']\<alpha> = TRUE"
  by (auto simp add:eval evale evala alphabet)

lemma [evala]: 
  "ok[false|okay']\<alpha> = ok" "ok[true|okay']\<alpha> = ok"
  "ok'[false|okay]\<alpha> = ok'" "ok'[true|okay]\<alpha> = ok'"
  by (auto simp add:eval evale evala alphabet)

lemma [simp]: "\<lbrakk>true\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e okay" "\<lbrakk>false\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e okay"
  by (simp_all add:evala)

lemma DesignA_refinement:
  assumes 
    "\<alpha> p1 \<in> PROGRAM_ALPHABET" "\<alpha> p2 \<in> PROGRAM_ALPHABET"
    "\<alpha> q1 \<in> PROGRAM_ALPHABET" "\<alpha> q2 \<in> PROGRAM_ALPHABET"
  shows "`p1 \<turnstile> q1 \<sqsubseteq> p2 \<turnstile> q2` = `[p1 \<Rightarrow> p2] \<and> [p1 \<and> q2 \<Rightarrow> q1]`"
proof -
  have "`p1 \<turnstile> q1 \<sqsubseteq> p2 \<turnstile> q2` = `[p2 \<turnstile> q2 \<Rightarrow> p1 \<turnstile> q1]`"
    by (utp_alpha_tac, utp_pred_tac)

  also have "... = `[(ok \<and> p2 \<Rightarrow> ok' \<and> q2) \<Rightarrow> (ok \<and> p1 \<Rightarrow> ok' \<and> q1)]`"
    by (utp_alpha_tac2)

  also with assms have "... = `[(p2 \<Rightarrow> ok' \<and> q2) \<Rightarrow> (p1 \<Rightarrow> ok' \<and> q1)]`"
    apply (rule_tac trans)
    apply (rule_tac x="okay" in BoolType_aux_var_split)
    apply (simp_all add:usubst alphabet)
    apply (utp_alpha_tac2)
  done

  also from assms have "... = `[(\<not> p2 \<Rightarrow> \<not> p1) \<and> ((p2 \<Rightarrow> q2) \<Rightarrow> (p1 \<Rightarrow> q1))]`"
    apply (rule_tac trans)
    apply (rule_tac x="okay'" in BoolType_aux_var_split)
    apply (simp_all add:usubst alphabet)
    apply (utp_alpha_tac2)
  done

  also have "... = `[(p1 \<Rightarrow> p2) \<and> ((p2 \<Rightarrow> q2) \<Rightarrow> (p1 \<Rightarrow> q1))]`"
    by (utp_alpha_tac2, utp_pred_auto_tac)

  also have "... = `[(p1 \<Rightarrow> p2)] \<and> [p1 \<and> q2 \<Rightarrow> q1]`"
    by (utp_alpha_tac2, utp_pred_auto_tac)

  ultimately show ?thesis
    by simp
qed

lemma DesignD_diverge:
  "\<lbrakk> \<alpha> p \<in> PROGRAM_ALPHABET; \<alpha> q \<in> PROGRAM_ALPHABET \<rbrakk> \<Longrightarrow>
   (p \<turnstile> q)[false|okay]\<alpha> = true (\<alpha> p \<union>\<^sub>f \<alpha> q \<union>\<^sub>f \<lbrace>okay'\<rbrace>)"
  apply (simp add:DesignD_def)
  apply (simp add:usubst alphabet)
  apply (utp_alpha_tac2)
done

lemma H1_idempotent: "H1 (H1 p) = H1 p"
  apply (simp add:H1_def)
  apply (utp_alpha_tac2)
  apply (utp_pred_tac)
done

lemma H1_DesignD: "p \<turnstile> q is H1 healthy"
  apply (simp add:DesignD_def H1_def is_healthy_def)
  apply (utp_alpha_tac2)
  apply (utp_pred_auto_tac)
done

lemma ClosureA_intro: "\<lbrakk> \<alpha> p = \<alpha> q; [p \<Leftrightarrow> q] \<rbrakk> \<Longrightarrow> p = q"
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
done

lemma eq_iff_taut: "\<lbrakk> \<alpha> P = \<alpha> Q \<rbrakk> \<Longrightarrow> P = Q \<longleftrightarrow> taut (P \<Leftrightarrow>\<alpha> Q)"
  apply (auto)
  apply (utp_alpha_tac)
  apply (rule ClosureA_intro)
  apply (auto)
done

lemma AndA_OrA_dist:
  "`(P \<or> Q) \<and> R` = `(P \<and> R) \<or> (Q \<and> R)`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

lemma OrA_AndA_dist:
  "`(P \<and> Q) \<or> R` = `(P \<or> R) \<and> (Q \<or> R)`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

lemma MkBool_True: "\<lbrakk> \<D> p; p : BoolType; DestBool p \<rbrakk> \<Longrightarrow> p = MkBool True"
  by (auto)

lemma MkBool_False: "\<lbrakk> \<D> p; p : BoolType; \<not> DestBool p \<rbrakk> \<Longrightarrow> p = MkBool False"
  by (auto)

lemma aux_eq_true: 
  "\<lbrakk> type x = BoolType; aux x \<rbrakk> \<Longrightarrow> `$x = true` = `$x`"
  apply (utp_alpha_tac2, utp_pred_tac, utp_expr_tac)
  apply (force intro:defined typing MkBool_True)
done

lemma aux_eq_false: 
  "\<lbrakk> type x = BoolType; aux x \<rbrakk> \<Longrightarrow> `$x = false` = `\<not> $x`"
  apply (utp_alpha_tac2, utp_pred_tac, utp_expr_tac)
  apply (force intro:defined typing MkBool_False)
done

lemma J_split: 
  assumes "P \<in> WF_RELATION" "\<alpha> P \<in> DESIGN_ALPHABET"
          "a \<in> HOM_ALPHABET" "in\<^sub>\<alpha> a = undash `\<^sub>f out\<^sub>\<alpha> (\<alpha> P)"
  shows "P ;\<alpha> J a = (P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> ok'))"
proof - 

  from assms have aDESALPH: "a \<in> DESIGN_ALPHABET"
    apply (unfold DESIGN_ALPHABET_def)
    apply (simp add:HOM_ALPHABET_def)
    apply (simp add:HOM_ALPHA_unfold)
    apply (auto)
    apply (metis (hide_lams, no_types) COMPOSABLE_def alphabet_simps comp_alphabet_dash fimage.rep_eq okay_simps(7) out_alphabet.rep_eq out_dash)
    apply (metis (hide_lams, no_types) COMPOSABLE_def comp_alphabet_dash comp_vars_undash dash_undash_image fimage.rep_eq in_alphabet.rep_eq okay_simps(7) out_alphabet.rep_eq utp_alphabet.out_DASHED)
  done

  have "P ;\<alpha> J a = P ;\<alpha> ((ok \<Rightarrow>\<alpha> ok') \<and>\<alpha> II\<alpha> (a -\<^sub>f OK))"
    by (simp add:J_def)

  also from assms have "... = P ;\<alpha> ((ok \<Rightarrow>\<alpha> (ok \<and>\<alpha> ok')) \<and>\<alpha> II\<alpha> (a -\<^sub>f OK))"
    apply (subgoal_tac "((ok \<Rightarrow>\<alpha> ok') :: 'a WF_ALPHA_PREDICATE) = (ok \<Rightarrow>\<alpha> (ok \<and>\<alpha> ok'))")
    apply (simp)
    apply (utp_alpha_tac)
    apply (utp_pred_tac)
  done

  also from assms have "... = P ;\<alpha> ((\<not>\<alpha> ok \<or>\<alpha> (ok \<and>\<alpha> ok')) \<and>\<alpha> II\<alpha> (a -\<^sub>f OK))"
    apply (subgoal_tac "((ok \<Rightarrow>\<alpha> (ok \<and>\<alpha> ok')) :: 'a WF_ALPHA_PREDICATE) = (\<not>\<alpha> ok \<or>\<alpha> (ok \<and>\<alpha> ok'))")
    apply (simp)
    apply (utp_alpha_tac)
    apply (utp_pred_tac)
  done

  also from assms have "... = `P ; ((\<not> ok \<and> II\<^bsub>a -\<^sub>f OK\<^esub>) \<or> ((ok \<and> ok') \<and> II\<^bsub>a -\<^sub>f OK\<^esub>))`" 
    by (smt AndA_OrA_dist)

  also from assms have "... = `(P ; (\<not> ok \<and> II\<^bsub>a -\<^sub>f OK\<^esub>)) \<or> (P ; ((ok \<and> ok') \<and> II\<^bsub>a -\<^sub>f OK\<^esub>))`"
    by (simp add:SemiA_OrA_distl closure)

  also from assms have "... = (P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> ok'))"
  proof -
    from assms have "`P ; (\<not> ok \<and> II\<^bsub>a -\<^sub>f OK\<^esub>)` = P\<^sup>f"
    proof -
      from assms have "`P ; (\<not> ok \<and> II\<^bsub>a -\<^sub>f OK\<^esub>)` = `(P \<and> (\<not> ok')) ; II\<^bsub>a -\<^sub>f OK\<^esub>`"
        by (simp add:SemiA_ConjA_right_precond closure alphabet urename SS_UNDASHED_app)

      also from assms have "... = (\<exists>-\<alpha> \<lbrace>okay'\<rbrace> . (P \<and>\<alpha> \<not>\<alpha> ok')) ;\<alpha> II\<alpha> (a -\<^sub>f OK)"
        apply (rule_tac trans)
        apply (rule_tac SemiA_ExistsA_left[of "`(P \<and> (\<not> ok'))`" "`II\<^bsub>a -\<^sub>f OK\<^esub>`", THEN sym])
        apply (auto simp add:alphabet alphabet_dist alphabet_simps closure dash_inj)
        apply (subgoal_tac "out\<^sub>\<alpha> (\<alpha> P) -\<^sub>f (out\<^sub>\<alpha> (\<alpha> P) -\<^sub>f \<lbrace>okay'\<rbrace>) = \<lbrace>okay'\<rbrace>")
        apply (auto)
        apply (unfold DESIGN_ALPHABET_def)
        apply (auto)
        apply (simp add:okay_def var_defs)
      done


      also from assms have "... = (\<exists>-\<alpha> \<lbrace>okay'\<rbrace> . (P \<and>\<alpha> \<not>\<alpha> ok'))"
        apply (rule_tac SemiA_SkipA_right)
        apply (simp_all add:alphabet alphabet_dist alphabet_simps closure dash_inj)
        apply (clarsimp)
        apply (smt alphabet_simps dash_image_minus fimage.rep_eq image_empty image_insert out_alphabet.rep_eq undash_dash_image)
      done

      also from assms have "... = P\<^sup>f"
        apply (rule_tac trans) defer
        apply (rule_tac SubstA_one_point)
        apply (simp_all add:alphabet)
        apply (unfold DESIGN_ALPHABET_def)
        apply (force)
        apply (simp add: aux_eq_false[THEN sym])
      done

      ultimately show ?thesis by simp
    qed

    moreover 
    have "`P ; ((ok \<and> ok') \<and> II\<^bsub>a -\<^sub>f OK\<^esub>)` = (P\<^sup>t \<and>\<alpha> ok')"
    proof -

      from assms have "`P ; ((ok \<and> ok') \<and> II\<^bsub>a -\<^sub>f OK\<^esub>)` = `(P ; (ok \<and> II\<^bsub>a -\<^sub>f OK\<^esub>)) \<and> ok'`"
      proof -
        have "\<langle>\<alpha> ok'\<rangle>\<^sub>f \<subseteq> DASHED"
          by (simp add:alphabet)

        thus ?thesis
          by (smt AndA_WF_RELATION AndA_assoc AndA_comm HOM_ALPHABET_REL_ALPHABET REL_ALPHABET_minus SemiA_ConjA_right_postcond SkipA_closure assms ok'_rel_closure ok_rel_closure)
      qed

      also from assms have "... = `((P \<and> ok') ; II\<^bsub>a -\<^sub>f OK\<^esub>) \<and> ok'`"
        by (simp add:SemiA_ConjA_right_precond closure alphabet urename SS_UNDASHED_app)

      also from assms have "... = P\<^sup>t \<and>\<alpha> ok'"
      proof -

        from assms have "out\<^sub>\<alpha> (\<alpha> P) -\<^sub>f (out\<^sub>\<alpha> (\<alpha> P) -\<^sub>f \<lbrace>okay'\<rbrace>) = \<lbrace>okay'\<rbrace>"
          apply (unfold DESIGN_ALPHABET_def)
          apply (auto simp add:okay_def var_defs)
        done

        with assms have "`(P \<and> ok') ; II\<^bsub>a -\<^sub>f OK\<^esub>` = `(\<exists>- okay' . (P \<and> ok')) ; II\<^bsub>a -\<^sub>f OK\<^esub>`"
          apply (rule_tac trans)
          apply (rule_tac SemiA_ExistsA_left[of "`P \<and> ok'`" "`II\<^bsub>a -\<^sub>f OK\<^esub>`", THEN sym])
          apply (auto simp add:alphabet alphabet_dist alphabet_simps closure dash_inj)
        done

        also with assms have "... = `\<exists>- okay' . (P \<and> ok')`"
          apply (rule_tac SemiA_SkipA_right)
          apply (simp_all add:alphabet alphabet_dist alphabet_simps closure dash_inj)
          apply (clarsimp)
          apply (smt alphabet_simps dash_image_minus fimage.rep_eq image_empty image_insert out_alphabet.rep_eq undash_dash_image)
        done
      
        also from assms have "... = P\<^sup>t"
          apply (rule_tac trans) defer
          apply (rule_tac SubstA_one_point)
          apply (simp_all add:alphabet)
          apply (unfold DESIGN_ALPHABET_def)
          apply (force)
          apply (simp add: aux_eq_true[THEN sym])
        done

        ultimately show ?thesis by simp
      qed

      ultimately show ?thesis
        by simp
    qed

    ultimately show ?thesis
      by simp
  qed

  ultimately show ?thesis
    by simp
qed

lemma okay_true_alphabet [alphabet]: "\<alpha> (P\<^sup>t) = \<alpha> P -\<^sub>f \<lbrace>okay'\<rbrace>"
  by (auto simp add:alphabet)

lemma okay_false_alphabet [alphabet]: "\<alpha> (P\<^sup>f) = \<alpha> P -\<^sub>f \<lbrace>okay'\<rbrace>"
  by (auto simp add:alphabet)

lemma H2_equivalence:
  assumes "P \<in> WF_RELATION" "\<alpha> P \<in> DESIGN_ALPHABET"
          "a \<in> HOM_ALPHABET" "in\<^sub>\<alpha> a = undash `\<^sub>f out\<^sub>\<alpha> (\<alpha> P)"
  shows "[P \<Leftrightarrow>\<alpha> (P ;\<alpha> J a)]\<alpha> = [P\<^sup>f \<Rightarrow>\<alpha> (P\<^sup>t)]\<alpha>"
proof -

  from assms have "[P \<Leftrightarrow>\<alpha> (P ;\<alpha> J a)]\<alpha> = [P \<Leftrightarrow>\<alpha> (P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> ok'))]\<alpha>"
    by (simp add:J_split)

  also from assms 
  have "... = [((P \<Leftrightarrow>\<alpha> (P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> ok')))\<^sup>f) \<and>\<alpha> ((P \<Leftrightarrow>\<alpha> (P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> ok')))\<^sup>t)]\<alpha>"
    by (smt AndA_comm BoolType_aux_var_split okay_simps type_dash)

  also from assms
  have "... = [(P\<^sup>f \<Leftrightarrow>\<alpha> (P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> FALSE))) \<and>\<alpha> (P\<^sup>t \<Leftrightarrow>\<alpha> (P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> TRUE)))]\<alpha>"
    by (simp add:usubst closure typing alphabet)

  also from assms
  have "... = [P\<^sup>t \<Leftrightarrow>\<alpha> (P\<^sup>f) \<or>\<alpha> (P\<^sup>t)]\<alpha>"
    by (simp add:alphabet)

  also from assms have "... = [P\<^sup>f \<Rightarrow>\<alpha> (P\<^sup>t)]\<alpha>"
    apply (utp_alpha_tac)
    apply (utp_pred_auto_tac)
  done

  ultimately show ?thesis
    by simp
qed

lemma [simp]: "taut [p]\<alpha> \<longleftrightarrow> taut p"
  by (utp_alpha_tac, utp_pred_tac)

lemma H2_equivalence':
  assumes "P \<in> WF_RELATION" "\<alpha> P \<in> DESIGN_ALPHABET"
          "a \<in> HOM_ALPHABET" "in\<^sub>\<alpha> a = undash `\<^sub>f out\<^sub>\<alpha> (\<alpha> P)"
  shows "P = (P ;\<alpha> J a) \<longleftrightarrow> taut [P\<^sup>f \<Rightarrow>\<alpha> (P\<^sup>t)]\<alpha>"
using assms
  apply (simp add:H2_equivalence[THEN sym])
  apply (subgoal_tac "\<alpha> P = \<alpha> (P ;\<alpha> J a)")
  apply (simp add:eq_iff_taut)
  apply (simp add:alphabet closure alphabet_simps alphabet_dist)
  apply (metis DESIGN_ALPHABET_finsert(2) HOM_ALPHABET_REL_ALPHABET SemiA_SkipA_right SemiA_alphabet SkipA_alphabet SkipA_closure assms(2))
done


lemma [simp]:
  "`p \<Rightarrow> FALSE` = `\<not> p`" 
  "`p \<Rightarrow> TRUE` = `true\<^bsub>\<alpha> p\<^esub>`"
  by (utp_alpha_tac2)+

lemma [simp]:
  "`p \<oplus> a \<and> q` = `(p \<and> q) \<oplus> a`"
  "`p \<oplus> a \<or> q` = `(p \<or> q) \<oplus> a`"
  "`p \<and> q \<oplus> a` = `(p \<and> q) \<oplus> a`"
  "`p \<or> q \<oplus> a` = `(p \<or> q) \<oplus> a`"
  by (utp_alpha_tac2)+

lemma [simp]: "a \<in> HOM_ALPHABET \<Longrightarrow> homr a = a"
  apply (simp add:HOM_ALPHABET_def hom_right_def HOM_ALPHA_unfold alphabet_dist alphabet_simps)
  apply (metis SkipA_alphabet SkipA_closure WF_RELATION_UNDASHED_DASHED alphabet_simps(14))
done

lemma [simp]: "a \<in> HOM_ALPHABET \<Longrightarrow> homl a = a"
  apply (simp add:HOM_ALPHABET_def hom_left_def HOM_ALPHA_unfold alphabet_dist alphabet_simps)
  apply (metis SkipA_alphabet SkipA_closure WF_RELATION_UNDASHED_DASHED alphabet_simps(14))
done

lemma J_H2:
  assumes "a \<in> DESIGN_ALPHABET" "a \<in> HOM_ALPHABET"
  shows "J a is H2' healthy"
proof -

  from assms have "H2' (J a) = J a ;\<alpha> J a"
    by (simp add:H2'_def alphabet closure is_healthy_def)

  also from assms have "... = (J a)\<^sup>f \<or>\<alpha> ((J a)\<^sup>t  \<and>\<alpha> ok')"
    apply (rule_tac J_split)
    apply (simp_all add:alphabet closure)
    apply (simp add:HOM_ALPHABET_def, erule conjE)
    apply (simp add:HOM_ALPHA_unfold)
  done

  also from assms have "... = `(\<not> ok \<and> II\<^bsub>a -\<^sub>f OK\<^esub>) \<or> (ok' \<and> II\<^bsub>a -\<^sub>f OK\<^esub>)`"
    (* FIXME: The set simplifiers should be able to cope with this *)
    apply (subgoal_tac "\<alpha> `((\<not> ok \<and> II\<^bsub>a -\<^sub>f OK\<^esub>) \<or> II\<^bsub>a -\<^sub>f OK\<^esub> \<and> ok')` \<union>\<^sub>f \<lbrace>okay\<rbrace> = 
                        \<alpha> `((\<not> ok \<and> II\<^bsub>a -\<^sub>f OK\<^esub>) \<or> II\<^bsub>a -\<^sub>f OK\<^esub> \<and> ok')`")
    apply (simp add:J_def usubst closure alphabet typing)
    apply (smt AndA_comm)
    apply (auto simp add:alphabet closure)
  done

  also from assms have "... = `(\<not> ok \<or> ok') \<and> II\<^bsub>a -\<^sub>f OK\<^esub>`"
    by (smt AndA_OrA_dist)

  also from assms have "... = `(ok \<Rightarrow> ok') \<and> II\<^bsub>a -\<^sub>f OK\<^esub>`"
    apply (utp_alpha_tac2)
    apply (utp_pred_tac)
  done

  ultimately show ?thesis
    by (simp add:is_healthy_def J_def)
qed

lemma H2_idempotent: 
  assumes "p \<in> WF_RELATION" "\<alpha> p \<in> DESIGN_ALPHABET"
  shows "H2' (H2' p) = H2' p"
proof -

  from assms have "H2' (H2' p) = (p ;\<alpha> J (homr (\<alpha> p))) ;\<alpha> J (homr (\<alpha> p))"
    apply (simp add:H2'_def alphabet closure)
    apply (simp add:hom_right_def alphabet alphabet_simps alphabet_dist)
  done

  also from assms have "... = p ;\<alpha> (J (homr (\<alpha> p)) ;\<alpha> J (homr (\<alpha> p)))"
    by (metis J_rel_closure REL_ALPHABET_hom_right SemiA_assoc)

  also from assms have "... = p ;\<alpha> H2' (J (homr (\<alpha> p)))"
    by (insert J_H2[of "homr (\<alpha> p)"], simp add:is_healthy_def H2'_def alphabet closure)

  also from assms have "... = p ;\<alpha> J (homr (\<alpha> p))"
    by (metis (lifting) DESIGN_ALPHABET_homr HOM_ALPHABET_hom_right J_H2 is_healthy_def)

  also from assms have "... = H2' p"
    by (simp add: H2'_def)

  ultimately show ?thesis
    by simp

qed

lemma H1_H2_DesignD:
  assumes cl: "p \<in> WF_RELATION" 
  and alpha: "\<alpha> p \<in> DESIGN_ALPHABET" 
  and H1:"p is H1 healthy" 
  and H2:"p is H2' healthy"
  shows "p = (\<not>\<alpha> (p\<^sup>f) \<turnstile> (p\<^sup>t))"
proof -

  have "p = `ok \<Rightarrow> p`"
    by (metis H1 H1_def is_healthy_def) 

  also have "... = ok \<Rightarrow>\<alpha> (p ;\<alpha> J (homr (\<alpha> p)))"
    by (metis H2 H2'_def calculation is_healthy_def)

  also have "... = ok \<Rightarrow>\<alpha> ((p\<^sup>f) \<or>\<alpha> (p\<^sup>t \<and>\<alpha> ok'))"
    apply (insert J_split[of p "homr (\<alpha> p)"])
    apply (simp add:closure cl alpha)
    apply (simp add:hom_right_def alphabet_simps alphabet_dist)
  done

  also have "... = ok \<and>\<alpha> \<not>\<alpha> (p\<^sup>f) \<Rightarrow>\<alpha> ok' \<and>\<alpha> (p\<^sup>t)"
    by (utp_alpha_tac2, utp_pred_auto_tac)

  ultimately show ?thesis
    by (simp add:DesignD_def)

qed

   
end
