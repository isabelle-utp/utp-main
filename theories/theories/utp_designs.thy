(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp_designs.thy                                                      *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
(******************************************************************************)

header {* UTP Designs *}

theory utp_designs
imports "../alpha/utp_alpha_laws" "../tactics/utp_alpha_tac" "../tactics/utp_alpha_expr_tac" utp_theory
begin

default_sort BOOL_SORT

subsection {* Constructs *}

definition "okay  \<equiv> MkVar (MkName ''okay'' 0 NoSub) BoolType True"
definition "okay' \<equiv> MkVar (MkName ''okay'' 1 NoSub) BoolType True"

lemma okay_simps [simp]: 
  "okay \<noteq> okay'" "okay' \<noteq> okay"
  "MkBool True \<rhd> okay" "MkBool False \<rhd> okay"
  "MkBool True \<rhd> okay'" "MkBool False \<rhd> okay'"
  "TrueE \<rhd>\<^sub>e okay" "FalseE \<rhd>\<^sub>e okay"
  "TrueE \<rhd>\<^sub>e okay'" "FalseE \<rhd>\<^sub>e okay'"
  "type okay = BoolType" "type okay' = BoolType"
  "control okay" "control okay'"
  by (force intro:typing defined simp add:okay_def okay'_def)+

abbreviation OK where "OK \<equiv> Abs_fset {okay,okay'}"

abbreviation ok_true :: 
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("_\<^sup>t" [150]) where
"p\<^sup>t \<equiv> p[TrueAE|okay]\<alpha>"

abbreviation ok_false :: 
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("_\<^sup>f" [150]) where
"p\<^sup>f \<equiv> p[FalseAE|okay]\<alpha>"


abbreviation "ok  \<equiv> VarA okay"
abbreviation "ok' \<equiv> VarA okay'"

definition DesignA :: 
"'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
 'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
 'VALUE WF_ALPHA_PREDICATE" (infixr "\<turnstile>" 60) where
"p \<turnstile> q \<equiv> (ok \<and>\<alpha> p) \<Rightarrow>\<alpha> (ok' \<and>\<alpha> q)"

(*
lift_definition DesignA ::
"'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
 'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
 'VALUE WF_ALPHA_PREDICATE" (infixr "\<turnstile>\<^sub>\<alpha>" 60) is
"\<lambda> p q. (OK \<union>\<^sub>f \<alpha> p \<union>\<^sub>f \<alpha> q, \<pi> p \<turnstile> \<pi> q)" 
  apply (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (simp add:DesignP_def)
  apply (rule unrest)
  apply (rule unrest)
  apply (force intro: unrest)
  apply (force intro: unrest)
  apply (rule unrest)
  apply (force intro: unrest)+
done
*)

(*
definition SkipD ::
"'VALUE WF_PREDICATE" ("IID") where
"IID = (true \<turnstile> II)"
*)

definition SkipA ::
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("IID") where
"IID a \<equiv> true a \<turnstile> II\<alpha> a"

(*
lift_definition SkipA ::
"'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" ("IID") is
"\<lambda> a. (a \<union>\<^sub>f OK, true \<turnstile> II \<langle>a\<rangle>\<^sub>f)"
  apply (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def DesignP_def)
  apply (rule unrest)
  apply (rule unrest)
  apply (force intro:unrest)
  apply (force intro:unrest)
  apply (rule unrest)
  apply (force intro:unrest)
  apply (force intro:unrest)
done
*)

declare DesignA_def [evala]
declare SkipA_def [evala]

abbreviation is_healthy :: 
  " 'VALUE WF_ALPHA_PREDICATE 
  \<Rightarrow> 'VALUE ALPHA_FUNCTION 
  \<Rightarrow> bool" ("_ is _ healthy") where
"is_healthy p H \<equiv> p = H p"

(*
definition Mk_ALPHA_FUNCTION :: 
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_FUNCTION \<Rightarrow> 'VALUE ALPHA_FUNCTION" where
"Mk_ALPHA_FUNCTION a f = (\<lambda> p. Abs_WF_ALPHA_PREDICATE (\<alpha> p, f (\<pi> p)))"
*)

definition "H1   \<equiv> \<lambda> p. ok \<Rightarrow>\<alpha> p"
definition "J a  \<equiv> (ok \<Rightarrow>\<alpha> ok') \<and>\<alpha> II\<alpha> a"
definition "H2   \<equiv> \<lambda> p. (p ;\<alpha> J (\<alpha> p))"
(* definition "H2'  \<equiv> \<lambda> p. [p\<^sup>t \<Rightarrow>p (p\<^sup>f)]p" *)
definition "H3  \<equiv> \<lambda> p. p ;\<alpha> IID (\<alpha> p)"
definition "H4  \<equiv> \<lambda> p. p ;\<alpha> true (\<alpha> p) \<Rightarrow>\<alpha> true (\<alpha> p)"

lemma extreme_point_true:
  "false a \<turnstile> false a = false a \<turnstile> true a"
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
done

(*
lemma extreme_point_nok:
  "true a \<turnstile> false a = \<not>\<alpha> ok"
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
  by (utp_pred_tac)
*)

lemma export_precondition:
  "p \<turnstile> q = p \<turnstile> p \<and>\<alpha> q"
  by (utp_alpha_tac, utp_pred_auto_tac)

lemma BoolType_var_control_cases [elim]:
  "\<lbrakk> type x = BoolType; \<not> control x \<Longrightarrow> P; \<langle>b\<rangle>\<^sub>b x = TrueV \<Longrightarrow> P; \<langle>b\<rangle>\<^sub>b x = FalseV \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis MkBool_cases binding_value_alt var_compat_def)

lemma EvalP_BoolType_cases [intro]:
  "\<lbrakk> type x = BoolType; control x; \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b TrueV)) ; \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b FalseV)) \<rbrakk> \<Longrightarrow> \<lbrakk>p\<rbrakk>b"
  by (metis (lifting) BoolType_var_control_cases binding_upd_simps(2))



(*
lemma "\<lbrakk> \<lbrakk>p\<rbrakk>b; \<And> x t. \<lbrakk> v : type x; \<D> v; \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b v)) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (simp add:EvalP_def)
*)


lemma BoolType_control_var_split:
  "\<lbrakk> type x = BoolType; control x \<rbrakk> 
  \<Longrightarrow> [p]\<alpha> = [p[FalseAE|x]\<alpha> \<and>\<alpha> p[TrueAE|x]\<alpha>]\<alpha>"
  apply (subgoal_tac "\<lbrakk>TrueAE\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e x")
  apply (subgoal_tac "x \<notin> \<langle>\<alpha> TrueAE\<rangle>\<^sub>f")
  apply (subgoal_tac "\<lbrakk>FalseAE\<rbrakk>\<alpha>\<epsilon> \<rhd>\<^sub>e x")
  apply (subgoal_tac "x \<notin> \<langle>\<alpha> FalseAE\<rangle>\<^sub>f")
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
  apply (utp_expr_tac)
  apply (auto)[1]
  apply (utp_alpha_tac)
  apply (simp add:evala)
  apply (force intro:defined typing)  
  apply (utp_alpha_tac)
  apply (simp add:evala)
  apply (force intro:defined typing)  
done

lemma [evala]: "\<epsilon> e = \<lbrakk>e\<rbrakk>\<alpha>\<epsilon>"
  by (simp add:EvalAE_def)

lemma [evala]: 
  "ok[false|okay]\<alpha> = FALSE" "ok[true|okay]\<alpha> = TRUE"
  "ok'[false|okay']\<alpha> = FALSE" "ok'[true|okay']\<alpha> = TRUE"
  by (auto simp add:eval evale evala alphabet)

lemma [evala]: 
  "ok[false|okay']\<alpha> = ok" "ok[true|okay']\<alpha> = ok"
  "ok'[false|okay]\<alpha> = ok'" "ok'[true|okay]\<alpha> = ok'"
  by (auto simp add:eval evale evala alphabet)

lemma [simp]: "false \<and>p x = false" "false \<Rightarrow>p x = true" "p \<Rightarrow>p true = true" "true \<and>p p = p"
  by (utp_pred_tac)+

lemma DesignA_refinement:
  assumes 
    "PROGRAM_ALPHABET (\<alpha> p1)" "PROGRAM_ALPHABET (\<alpha> p2)"
    "PROGRAM_ALPHABET (\<alpha> q1)" "PROGRAM_ALPHABET (\<alpha> q2)"
  shows "(p1 \<turnstile> q1) \<sqsubseteq>\<alpha> (p2 \<turnstile> q2) = [p1 \<Rightarrow>\<alpha> p2]\<alpha> \<and>\<alpha> [p1 \<and>\<alpha> q2 \<Rightarrow>\<alpha> q1]\<alpha>"
proof -
  have "(p1 \<turnstile> q1) \<sqsubseteq>\<alpha> (p2 \<turnstile> q2) = [(p2 \<turnstile> q2) \<Rightarrow>\<alpha> (p1 \<turnstile> q1)]\<alpha>"
    by (utp_alpha_tac, utp_pred_tac)

  also have "... = [(ok \<and>\<alpha> p2 \<Rightarrow>\<alpha> ok' \<and>\<alpha> q2) \<Rightarrow>\<alpha> (ok \<and>\<alpha> p1 \<Rightarrow>\<alpha> ok' \<and>\<alpha> q1)]\<alpha>"
    by (utp_alpha_tac)

  also have "... = [(p2 \<Rightarrow>\<alpha> ok' \<and>\<alpha> q2) \<Rightarrow>\<alpha> (p1 \<Rightarrow>\<alpha> ok' \<and>\<alpha> q1)]\<alpha>"
    apply (rule_tac trans)
    apply (rule_tac x="okay" in BoolType_control_var_split)
    apply (simp_all)
    apply (simp add:SubstA_ImpliesA SubstA_AndA SubstA_OrA evala alphabet)
    apply (insert assms)
    apply (simp add:alphabet evala)
  done

  also have "... = [(\<not>\<alpha> p2 \<Rightarrow>\<alpha> \<not>\<alpha> p1) \<and>\<alpha> ((p2 \<Rightarrow>\<alpha> q2) \<Rightarrow>\<alpha> (p1 \<Rightarrow>\<alpha> q1))]\<alpha>"
    apply (rule_tac trans)
    apply (rule_tac x="okay'" in BoolType_control_var_split)
    apply (simp_all)
    apply (simp add:SubstA_ImpliesA SubstA_AndA SubstA_OrA evala alphabet)
    apply (insert assms)
    apply (simp add:alphabet evala eval)
  done

  also have "... = [(p1 \<Rightarrow>\<alpha> p2) \<and>\<alpha> ((p2 \<Rightarrow>\<alpha> q2) \<Rightarrow>\<alpha> (p1 \<Rightarrow>\<alpha> q1))]\<alpha>"
    by (auto simp add:alphabet evala eval)

  also have "... = [(p1 \<Rightarrow>\<alpha> p2)]\<alpha> \<and>\<alpha> [p1 \<and>\<alpha> q2 \<Rightarrow>\<alpha> q1]\<alpha>"
    by (auto simp add:alphabet evala eval)

  ultimately show ?thesis
    by simp
qed

lemma DesignA_diverge:
  "\<lbrakk> PROGRAM_ALPHABET (\<alpha> p); PROGRAM_ALPHABET (\<alpha> q) \<rbrakk> \<Longrightarrow>
   (p \<turnstile> q)[false|okay]\<alpha> = true (\<alpha> p \<union>\<^sub>f \<alpha> q \<union>\<^sub>f (finsert okay' {}\<^sub>f))"
  apply (simp add:DesignA_def)
  apply (simp add:SubstA_ImpliesA SubstA_AndA evala alphabet)
  apply (auto)
done

lemma H1_idempotent: "H1 (H1 p) = H1 p"
  apply (simp add:H1_def)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

lemma H1_DesignD: "p \<turnstile> q is H1 healthy"
  apply (simp add:DesignA_def H1_def)
  apply (utp_alpha_tac)
  apply (utp_rel_auto_tac)
done

lemma J_split: "P ;\<alpha> J (\<alpha> P) = P\<^sup>f \<or>\<alpha> (P\<^sup>t \<and>\<alpha> ok')"
  apply (simp add: J_def)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
oops

lemma H2_H2': "P is H2 healthy \<longleftrightarrow> taut ([P\<^sup>t \<Rightarrow>p (P\<^sup>f)]p)"
proof -
  have "P is H2 healthy \<longleftrightarrow> P = P ; J"
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
