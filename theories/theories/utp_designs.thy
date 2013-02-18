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

abbreviation ok_true :: 
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("_\<^sup>t" [150]) where
"p\<^sup>t \<equiv> `p \<and> ($okay' = true)`"

abbreviation ok_false :: 
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("_\<^sup>f" [150]) where
"p\<^sup>f \<equiv> `p \<and> ($okay' = false)`"

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
definition "J a  \<equiv> `(ok \<Rightarrow> ok') \<and> II\<^bsub>a\<^esub>`"
definition "H2  \<equiv> \<lambda> p. [p\<^sup>t \<Rightarrow>\<alpha> (p\<^sup>f)]\<alpha>"
definition "H2' \<equiv> \<lambda> p. (p ;\<alpha> J (\<alpha> p))"
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
  by (auto simp add:J_def alphabet)

definition DESIGN_ALPHABET :: "'TYPE ALPHABET set"
where "DESIGN_ALPHABET = REL_ALPHABET \<inter> {a. OK \<subseteq>\<^sub>f a}"

lemma DESIGN_ALPHABET_finsert [simp]:
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> finsert okay a = a"
  "a \<in> DESIGN_ALPHABET \<Longrightarrow> finsert okay' a = a"
  by (auto simp add:DESIGN_ALPHABET_def)

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

lemma ClosureA_intro: "\<lbrakk> \<alpha> p = \<alpha> q; [p \<Leftrightarrow> q] \<rbrakk> \<Longrightarrow> p = q"
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
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
    apply (metis (hide_lams, no_types) COMPOSABLE_def alphabet_simps(12) alphabet_simps(7) comp_alphabet_dash fimage.rep_eq okay_simps(7) out_alphabet.rep_eq out_dash)
    apply (metis (hide_lams, no_types) COMPOSABLE_def comp_alphabet_dash comp_vars_undash dash_undash_image fimage.rep_eq in_alphabet.rep_eq okay_simps(7) out_alphabet.rep_eq utp_alphabet.out_DASHED)
  done

  have "P ;\<alpha> J a = P ;\<alpha> ((ok \<Rightarrow>\<alpha> ok') \<and>\<alpha> II\<alpha> a)"
    by (simp add:J_def)

  also from assms have "... = P ;\<alpha> ((ok \<Rightarrow>\<alpha> (ok \<and>\<alpha> ok')) \<and>\<alpha> II\<alpha> a)"
    apply (subgoal_tac "((ok \<Rightarrow>\<alpha> ok') :: 'a WF_ALPHA_PREDICATE) = (ok \<Rightarrow>\<alpha> (ok \<and>\<alpha> ok'))")
    apply (simp)
    apply (utp_alpha_tac)
    apply (utp_pred_tac)
  done

  also from assms have "... = P ;\<alpha> ((\<not>\<alpha> ok \<or>\<alpha> (ok \<and>\<alpha> ok')) \<and>\<alpha> II\<alpha> a)"
    apply (subgoal_tac "((ok \<Rightarrow>\<alpha> (ok \<and>\<alpha> ok')) :: 'a WF_ALPHA_PREDICATE) = (\<not>\<alpha> ok \<or>\<alpha> (ok \<and>\<alpha> ok'))")
    apply (simp)
    apply (utp_alpha_tac)
    apply (utp_pred_tac)
  done

  also from assms have "... = `P ; ((\<not> ok \<and> II\<^bsub>a\<^esub>) \<or> ((ok \<and> ok') \<and> II\<^bsub>a\<^esub>))`" 
    by (metis AndA_OrA_dist)

  also from assms have "... = `(P ; (\<not> ok \<and> II\<^bsub>a\<^esub>)) \<or> (P ; ((ok \<and> ok') \<and> II\<^bsub>a\<^esub>))`"
    by (simp add:SemiA_OrA_distl closure)

  also from assms have "... = (P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> ok'))"
  proof -
    from assms have "`P ; (\<not> ok \<and> II\<^bsub>a\<^esub>)` = P\<^sup>f"
    proof -
      from assms have "`P ; (\<not> ok \<and> II\<^bsub>a\<^esub>)` = `(P \<and> (\<not> ok')) ; II\<^bsub>a\<^esub>`"
        by (simp add:SemiA_ConjA_cond closure alphabet urename SS_UNDASHED_app)

      also from assms have "... = `P \<and> (\<not> ok')`"
        by (simp add:SemiA_SkipA_right closure alphabet)

      ultimately show ?thesis
        apply (unfold aux_eq_false[of okay',simplified])
        apply (simp)
      done
    qed

    moreover 
    have "`P ; ((ok \<and> ok') \<and> II\<^bsub>a\<^esub>)` = (P\<^sup>t \<and>\<alpha> ok')"
    proof -

      from assms aDESALPH have II_expand: "II\<alpha> a = `($okay' = $okay) \<and> II\<^bsub>(a -\<^sub>f OK)\<^esub>`"
        apply (rule_tac SkipA_unfold)
        apply (unfold DESIGN_ALPHABET_def)
        apply (auto simp add:HOM_ALPHABET_def)
      done

      with assms have "`P ; ((ok \<and> ok') \<and> II\<^bsub>a\<^esub>)` = `P ; ((ok \<and> ok') \<and> ($okay' = $okay \<and> II\<^bsub>a -\<^sub>f OK\<^esub>))`"
        by simp

      also from assms have "... = `P ; (($okay = true \<and> $okay' = true) \<and> ($okay' = $okay \<and> II\<^bsub>a -\<^sub>f OK\<^esub>))`"
        apply (unfold aux_eq_true[of okay,simplified,THEN sym])
        apply (unfold aux_eq_true[of okay',simplified,THEN sym])
        apply (simp)
      done

      also from assms have "... = `P ; (($okay = true) \<and> ($okay' = $okay \<and> II\<^bsub>a -\<^sub>f OK\<^esub>))`"
      proof -
        from assms have "`(($okay = true \<and> $okay' = true) \<and> ($okay' = $okay \<and> II\<^bsub>a -\<^sub>f OK\<^esub>))` = `(($okay = true) \<and> ($okay' = $okay \<and> II\<^bsub>a -\<^sub>f OK\<^esub>))`"
          apply (utp_alpha_tac)
          apply (utp_pred_tac)
          apply (utp_expr_tac)
          apply (auto)
        done

        thus ?thesis
          by simp
      qed
        
      also have "... = `P ; (ok \<and> II\<^bsub>a\<^esub>)`"
        by (metis II_expand aux_eq_true okay_simps(22) okay_simps(24))

      also from assms have "... = `(P \<and> ok') ; II\<^bsub>a\<^esub>`"
        by (simp add:SemiA_ConjA_cond closure alphabet urename SS_UNDASHED_app)

      also from assms have "... = `P \<and> ok'`"
        by (simp add:SemiA_SkipA_right closure alphabet)

      ultimately show ?thesis
        apply (unfold aux_eq_true[of okay',simplified])
        apply (simp)
        apply (metis (lifting) AndA_assoc AndA_idem)
      done
    qed

    ultimately show ?thesis
      by simp
  qed

  ultimately show ?thesis
    by (simp)
qed

lemma 
  assumes "P \<in> WF_RELATION" "\<alpha> P \<in> DESIGN_ALPHABET"
          "\<alpha> P \<in> HOM_ALPHABET" 
  shows "P = P ;\<alpha> J (\<alpha> P) \<longleftrightarrow> taut (P\<^sup>f \<Rightarrow>\<alpha> (P\<^sup>t))"
proof -
  have igd: "in\<^sub>\<alpha> (\<alpha> P) = undash `\<^sub>f out\<^sub>\<alpha> (\<alpha> P)"
    sorry

  with assms have "P = P ;\<alpha> J (\<alpha> P) = (P = P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> ok'))"
   apply (unfold J_split[OF assms(1) assms(2) assms(3) igd])
   apply (simp)
  done

  also have "... \<longleftrightarrow> taut (P\<^sup>f \<Rightarrow>\<alpha> (P\<^sup>t))"
    apply (utp_alpha_tac)
    apply (utp_pred_tac)
    apply (utp_expr_tac)
    apply (auto)

  apply (simp add:H2_def H2'_def)
  apply (subgoal_tac )
   apply (unfold J_split[OF assms(1) assms(2) assms(3)])
  apply (utp_alpha_tac)
  apply (auto)


lemma H2_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H2 (H2 p) = H2 p"
  apply (simp add:H2_def)
  apply (utp_alpha_tac2)
  apply (utp_pred_tac)
  apply (utp_expr_tac)
  apply (auto)
done



lemma H1_DesignD: "p \<turnstile> q is H1 healthy"
  apply (simp add:DesignD_def H1_def)
  apply (utp_alpha_tac2)
  apply (utp_pred_auto_tac)
done



lemma H2_H2': "P is H2 healthy \<longleftrightarrow> taut ([P\<^sup>t \<Rightarrow>\<alpha> (P\<^sup>f)]\<alpha>)"
proof -
  have "P is H2 healthy \<longleftrightarrow> P = P ;\<alpha> J (\<alpha> P)"
    by (simp add: H2_def)
  
  also have "... = 

  apply (simp add:H2_def H2'_def J_def)
  apply (utp_pred_auto_tac)
  apply (utp_rel_auto_tac)

lemma H2_idempotent: "H2 (H2 p) = H2 p"
  apply (simp add:H2_def J_def)
  apply (utp_rel_auto_tac)
done

lemma J_H2: "H2 J = J"
  apply (simp add:H2_def J_def)
  apply (utp_rel_auto_tac)
done

lemma H2_DesignD: "p \<turnstile> q is H2 healthy"
  apply (simp add:DesignD_def H2_def J_def)
  apply (utp_rel_auto_tac)
  apply (auto simp add: EvalR_UNIV)

lemma H1_H2_commute: "H1 (H2 p) = H2 (H1 p)"
  apply (simp add:H1_def H2_def J_def)
  apply (utp_rel_auto_tac)
oops

lemma H3_idempotent: "H3 (H3 p) = H3 p"
  apply (simp add:H3_def SkipD_def DesignD_def)
  apply (utp_rel_tac)
  apply (auto)
oops

lemma H4_idempotent: "H4 (H4 p) = H4 p"
  apply (simp add:H4_def)
  apply (utp_rel_tac)
  apply (auto)

done


(*
definition DESIGN_ALPHABET :: "'TYPE ALPHABET set"
where "DESIGN_ALPHABET = REL_ALPHABET \<inter> {a. OK \<subseteq> a}"


{a. a \<in> WF_ALPHABET \<and> a \<subseteq> UNDASHED \<union> DASHED \<and> OK \<subseteq> a}"
*)

(*
definition DESIGNS :: "('VALUE, 'TYPE) UTP_THEORY" where
"DESIGNS = \<lparr> utp_alphabets = WF_DESIGN_ALPHABET
           , healthconds = {H1, H2, H3, H4} \<rparr>"

definition WF_DESIGN where "WF_DESIGN = TheoryPreds DESIGNS"
*)

subsection {* Basic Laws *}

theorem WF_DESIGN_ALPHABET [closure]:
"a \<in> DESIGN_ALPHABET \<Longrightarrow> a \<in> REL_ALPHABET"
  by (simp add:DESIGN_ALPHABET_def)

theorem WF_DESIGN_UNDASHED_DASHED [closure]:
"a \<in> DESIGN_ALPHABET \<Longrightarrow> a \<subseteq> UNDASHED \<union> DASHED"
  by (simp add:DESIGN_ALPHABET_def REL_ALPHABET_def)

theorem okay_DESIGN_ALPHABET [elim]: 
"\<lbrakk> a \<in> DESIGN_ALPHABET; okay \<in> a \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:DESIGN_ALPHABET_def)

theorem okay'_DESIGN_ALPHABET [elim]: 
"\<lbrakk> a \<in> DESIGN_ALPHABET; okay' \<in> a \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:DESIGN_ALPHABET_def)

theorem UNDASHED_okay [simp]: "okay \<in> UNDASHED" 
  by (simp add:okay_def UNDASHED_def)

theorem DASHED_okay' [simp]: "okay' \<in> DASHED" 
  by (simp add:okay'_def DASHED_def)

subsection {* Basic Alphabet Laws *}

theorem ok_alphabet [alphabet]:
"a \<in> DESIGN_ALPHABET \<Longrightarrow> \<alpha> (ok a) = a"
  by (auto simp add:alphabet closure)

theorem ok'_alphabet [alphabet]:
"a \<in> DESIGN_ALPHABET \<Longrightarrow> \<alpha> (ok' a) = a"
  by (auto simp add:alphabet closure)

theorem DesignD_alphabet [alphabet]: 
"\<lbrakk>r1 \<in> WF_ALPHA_PREDICATE;
  r2 \<in> WF_ALPHA_PREDICATE;
  \<alpha> r1 = \<alpha> r2\<rbrakk> \<Longrightarrow>
  \<alpha> (r1 \<turnstile> r2) = \<alpha> r1 \<union> \<alpha> r2 \<union> OK"
  apply (simp add:DesignD_def)
  apply (simp add:alphabet closure)
  apply (force)
done

theorem SkipD_alphabet [alphabet]: "a \<in> REL_ALPHABET \<Longrightarrow> \<alpha> (IID a) = a \<union> OK"
  by (simp add: SkipD_def alphabet closure)

subsection {* Basic Closure Laws *}

lemma ok_pred [closure]: 
"\<lbrakk> a \<in> WF_ALPHABET; a \<subseteq> UNDASHED \<union> DASHED \<rbrakk> \<Longrightarrow> ok a \<in> WF_RELATION"
  by (force intro:WF_RELATION_intro simp add:closure alphabet)

lemma ok'_pred [closure]: 
"a \<in> WF_ALPHABET \<Longrightarrow> ok' a \<in> WF_ALPHA_PREDICATE"
  by (simp add:closure)

lemma DesignD_rel_closure [closure]: 
"\<lbrakk> r1 \<in> WF_RELATION; r2 \<in> WF_RELATION; \<alpha> r1 = \<alpha> r2 \<rbrakk> \<Longrightarrow>
r1 \<turnstile> r2 \<in> WF_RELATION"
  apply (auto intro:closure simp add:DesignD_def WF_RELATION_def)
  apply (simp add:REL_ALPHABET_def)
  apply (simp add:alphabet closure)
done

lemma SkipD_closure [closure]: "a \<in> REL_ALPHABET \<Longrightarrow> IID a \<in> WF_RELATION"
  by (simp add:SkipD_def closure alphabet)

lemma J_closure [closure]: "a \<in> DESIGN_ALPHABET \<Longrightarrow> J a \<in> WF_RELATION"
  by (rule WF_RELATION_intro, simp_all add:closure alphabet J_def)

subsection {* Laws from the notes *}

theorem DesignD_extreme_point_true:
  assumes "a \<in> DESIGN_ALPHABET"
  shows "false a \<turnstile> false a = false a \<turnstile> true a"
  apply (insert assms)
  apply (simp add:DesignD_def closure alphabet)
  apply (utp_alpha_tac, utp_pred_auto_tac)
done

theorem DesignD_extreme_point_nok:
  assumes "a \<in> DESIGN_ALPHABET"
  shows "true a \<turnstile> false a = \<not>\<alpha> ok a"
proof -
  from assms have "true a \<turnstile> false a = (ok a \<and>\<alpha> true a \<Rightarrow>\<alpha> ok' a \<and>\<alpha> false a)"
    by (simp add:DesignD_def closure alphabet)

  also from assms have "... = ok a \<Rightarrow>\<alpha> ok' a \<and>\<alpha> false a"
    by (utp_alpha_tac, utp_pred_auto_tac)
  
  also from assms have "... = ok a \<Rightarrow>\<alpha> false a"
    by (utp_alpha_tac, utp_pred_auto_tac)

  ultimately show ?thesis using assms
    apply (utp_alpha_tac, utp_pred_auto_tac)
  done
qed

theorem DesignD_export_precondition:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "\<alpha> p = \<alpha> q"
  shows "p \<turnstile> q = p \<turnstile> p \<and>\<alpha> q"
proof -
  from assms have "p \<turnstile> q = ok (\<alpha> p) \<and>\<alpha> p \<Rightarrow>\<alpha> ok' (\<alpha> q) \<and>\<alpha> q"
    by (simp add:DesignD_def closure alphabet)

  also from assms have "... = ok (\<alpha> p) \<and>\<alpha> p \<Rightarrow>\<alpha> ok' (\<alpha> q) \<and>\<alpha> p \<and>\<alpha> q"
    by (utp_alpha_tac, utp_pred_auto_tac)

  ultimately show ?thesis using assms
    by (simp add:DesignD_def closure alphabet)
qed

theorem DesignD_refinement:
  assumes "p1 \<in> WF_RELATION" "p2 \<in> WF_RELATION" 
          "q1 \<in> WF_RELATION" "q2 \<in> WF_RELATION"
          "\<alpha> p1 = \<alpha> q1" "\<alpha> q1 = \<alpha> p2" "\<alpha> p2 = \<alpha> q2" 
  shows   "(p1 \<turnstile> q1) \<sqsubseteq>\<alpha> (p2 \<turnstile> q2) = [p1 \<Rightarrow>\<alpha> p2]\<alpha> \<and>\<alpha> [p1 \<and>\<alpha> q2 \<Rightarrow>\<alpha> q1]\<alpha>"
proof -
  from assms have "(p1 \<turnstile> q1) \<sqsubseteq>\<alpha> (p2 \<turnstile> q2) = [(p2 \<turnstile> q2) \<Rightarrow>\<alpha> (p1 \<turnstile> q1)]\<alpha>"
    by (simp add:RefA_lemma closure alphabet)

  also from assms 
  have "... = [(ok (\<alpha> p2) \<and>\<alpha> p2 \<Rightarrow>\<alpha> ok' (\<alpha> q2) \<and>\<alpha> q2) \<Rightarrow>\<alpha> (ok (\<alpha> p1) \<and>\<alpha> p1 \<Rightarrow>\<alpha> ok' (\<alpha> q1) \<and>\<alpha> q1)]\<alpha>"
    by (simp add:DesignD_def closure alphabet)
  
  also from assms
  have "... = [(p2 \<Rightarrow>\<alpha> ok' (\<alpha> q2) \<and>\<alpha> q2) \<Rightarrow>\<alpha> (p1 \<Rightarrow>\<alpha> ok' (\<alpha> q1) \<and>\<alpha> q1)]\<alpha>"
    apply (utp_alpha_tac)
    apply (utp_pred_auto_tac)
    (* Need more lemmas to get further ... *)
    oops

subsection {* Healthiness Laws properties *}

lemma H1_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H1 (H1 p) = H1 p"
  apply (simp add:H1_def WF_RELATION_def)
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
done

lemma J_split: 
  assumes "p \<in> WF_RELATION" 
  shows "p ;\<alpha> J (\<alpha> p) = p\<^sup>f \<or>\<alpha> (p\<^sup>t \<or>\<alpha> ok' (\<alpha> p))"
proof -
  from assms have "p ;\<alpha> J (\<alpha> p) = p ;\<alpha> (ok (\<alpha> p) \<Rightarrow>\<alpha> ok' (\<alpha> p)) \<and>\<alpha> II\<alpha> (\<alpha> p)"
    by (simp add: J_def)

  also from assms have "... = p ;\<alpha> (ok (\<alpha> p) \<Rightarrow>\<alpha> ok (\<alpha> p) \<and>\<alpha> ok' (\<alpha> p)) \<and>\<alpha> II\<alpha> (\<alpha> p)"
    oops

lemma H2_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H2 (H2 p) = H2 p"
  apply (simp add:H2_def)
  oops

lemma H3_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H3 (H3 p) = H3 p"
  apply (simp add:H3_def)
  oops

lemma H4_idempotent: "p \<in> WF_RELATION \<Longrightarrow> H4 (H4 p) = H4 p"
  oops
  
subsection {* Design Closure Laws *}

(*
lemma DESIGNS_WF: "DESIGNS \<in> WF_UTP_THEORY"
proof (simp add:DESIGNS_def WF_UTP_THEORY_def, rule conjI)
  show wf_alpha:"WF_DESIGN_ALPHABET \<subseteq> WF_ALPHABET"
    by (force simp add:WF_DESIGN_ALPHABET_def)

  moreover from wf_alpha have "H1 \<in> WF_HEALTH_COND WF_DESIGN_ALPHABET"
    apply(simp add:WF_HEALTH_COND_def IDEMPOTENT_OVER_def WF_DESIGN_ALPHABET_def)
    apply(clarify)
    apply(rule H1_idempotent)
    apply(simp add: WF_RELATION_def WF_ALPHA_PREDICATE_OVER_def)
  done

  moreover from wf_alpha have "H2 \<in> WF_HEALTH_COND WF_DESIGN_ALPHABET"
    apply(simp add:WF_HEALTH_COND_def IDEMPOTENT_OVER_def WF_DESIGN_ALPHABET_def)
    apply(clarify)
    apply(rule H2_idempotent)
    apply(simp add: WF_RELATION_def WF_ALPHA_PREDICATE_OVER_def)
  done

  moreover from wf_alpha have "H3 \<in> WF_HEALTH_COND WF_DESIGN_ALPHABET"
    apply(simp add:WF_HEALTH_COND_def IDEMPOTENT_OVER_def WF_DESIGN_ALPHABET_def)
    apply(clarify)
    apply(rule H3_idempotent)
    apply(simp add: WF_RELATION_def WF_ALPHA_PREDICATE_OVER_def)
  done

  moreover from wf_alpha have "H4 \<in> WF_HEALTH_COND WF_DESIGN_ALPHABET"
    apply(simp add:WF_HEALTH_COND_def IDEMPOTENT_OVER_def WF_DESIGN_ALPHABET_def)
    apply(clarify)
    apply(rule H4_idempotent)
    apply(simp add: WF_RELATION_def WF_ALPHA_PREDICATE_OVER_def)
  done


  ultimately show "{H1, H2, H3, H4} \<in> WF_HEALTH_CONDS WF_DESIGN_ALPHABET"
    by (simp add:WF_HEALTH_CONDS_def)
qed
*)

lemma H1_closure[closure]: 
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> H1 p \<in> WF_ALPHA_PREDICATE"
  by (simp add:H1_def closure)


lemma H2_closure[closure]: 
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> H2 p \<in> WF_ALPHA_PREDICATE"
  oops

subsection {* Alphabet theorems *}

subsection {* Design properties *}
 

lemma H1_design: 
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE \<rbrakk> \<Longrightarrow>
 (p \<turnstile> q) = H1 (p \<turnstile> q)"
  apply(simp add:DesignD_def H1_def)
  oops
*)

end
