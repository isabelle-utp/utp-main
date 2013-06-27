(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_rel_tac.thy                                                      *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Proof Tactic for Relations *}

theory utp_rel_tac
imports 
  "../core/utp_pred" 
  "../core/utp_rel" 
  "../parser/utp_pred_parser"
  "utp_expr_tac"
begin

default_sort VALUE

text {* Theorem Attribute *}

ML {*
  structure evalr =
    Named_Thms (val name = @{binding evalr} val description = "evalr theorems")
*}

setup evalr.setup

ML {*
  structure evalrr =
    Named_Thms (val name = @{binding evalrr} val description = "evalrr theorems")
*}

setup evalrr.setup

subsection {* Type Synonyms *}


subsection {* Relational Model *}

text {*
  We require an arbitrary but fixed binding in our model of relations in order
  to constrain dashed variables which we do not care about. We note that an
  alternative approach is possible that upward closes the relation with respect
  to the values of these variables. In practice, it turns out that a constant
  valuation yields simpler proofs and there is not loss of generality with it.
*}

definition bc :: "'VALUE WF_BINDING" where
"bc = (SOME b . b \<in> UNIV)"

definition WF_REL_BINDING :: "'VALUE WF_BINDING set" where
"WF_REL_BINDING = {b \<oplus>\<^sub>b bc on DASHED | b . b \<in> UNIV}"
abbreviation "WF_REL \<equiv> WF_REL_BINDING \<times> WF_REL_BINDING"

typedef 'VALUE WF_REL_BINDING = "WF_REL_BINDING :: 'VALUE WF_BINDING set"
  morphisms DestRelB MkRelB
  by (auto simp add:WF_REL_BINDING_def)

declare DestRelB [simp]
declare DestRelB_inverse [simp]
declare MkRelB_inverse [simp]

lemma DestRelB_intro [intro]:
  "DestRelB x = DestRelB y \<Longrightarrow> x = y"
  by (simp add:DestRelB_inject)

lemma DestRelB_elim [elim]:
  "\<lbrakk> x = y; DestRelB x = DestRelB y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

notation DestRelB ("\<langle>_\<rangle>\<^sub>r")

type_synonym 'VALUE RELATION =
  "('VALUE WF_BINDING \<times>
    'VALUE WF_BINDING) set"

subsection {* Interpretation Function *}

definition BindR ::
  "'VALUE WF_BINDING \<Rightarrow>
   'VALUE WF_BINDING \<times>
   'VALUE WF_BINDING" where
"BindR b = (b \<oplus>\<^sub>b bc on DASHED, (RenameB SS b) \<oplus>\<^sub>b bc on DASHED)"

lemma BindR_range: 
  "BindR b \<in> WF_REL_BINDING \<times> WF_REL_BINDING"
  by (auto simp add:BindR_def WF_REL_BINDING_def)

definition BindP ::
  "'VALUE WF_BINDING \<times>
   'VALUE WF_BINDING \<Rightarrow>
   'VALUE WF_BINDING" where
"BindP = (\<lambda> (rb1, rb2) . rb1 \<oplus>\<^sub>b (RenameB SS rb2) on DASHED)"

definition EvalR ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE RELATION" ("\<lbrakk>_\<rbrakk>R") where
"EvalR p = BindR ` (destPRED p)"

definition IEvalR ::
  "'VALUE RELATION \<Rightarrow>
   'VALUE WF_PREDICATE" where
"IEvalR r = mkPRED (BindP ` r)"

subsection {* Auxilary Theorems *}

theorem EvalR_range :
"\<lbrakk>p\<rbrakk>R \<subseteq> WF_REL_BINDING \<times> WF_REL_BINDING"
  by (auto simp add: EvalR_def BindR_range)

theorem WF_REL_BINDING_member1 [simp, intro] :
"\<lbrakk>(rb1, rb2) \<in> \<lbrakk>p\<rbrakk>R\<rbrakk> \<Longrightarrow>
 rb1 \<in> WF_REL_BINDING"
  by (insert EvalR_range[of p], force)

theorem WF_REL_BINDING_member2 [simp, intro] :
"\<lbrakk>(rb1, rb2) \<in> \<lbrakk>p\<rbrakk>R\<rbrakk> \<Longrightarrow>
 rb2 \<in> WF_REL_BINDING"
 by (insert EvalR_range[of p], force)

lemma BindR_left_eq_NON_REL_VAR:
  "BindR b = (b1 , b2) \<Longrightarrow> b \<cong> b1 on NON_REL_VAR"
  by (auto simp add: BindR_def)

lemma BindR_right_eq_NON_REL_VAR:
  "BindR b = (b1 , b2) \<Longrightarrow> b \<cong> b2 on NON_REL_VAR"
  by (force simp add: BindR_def closure)

theorem EvalR_NON_REL_VAR:
"(b1, b2) \<in> \<lbrakk>p\<rbrakk>R \<Longrightarrow> b1 \<cong> b2 on NON_REL_VAR"
  by (auto simp add:EvalR_def BindR_def binding_equiv_def NON_REL_VAR_def urename)

theorem BindP_inverse :
"BindP (BindR b) = b"
apply (simp add: BindR_def BindP_def)
apply (rule Rep_WF_BINDING_intro)
apply (rule ext)
apply (case_tac "x \<in> DASHED")
apply (simp add: RenameB_def SS_DASHED_member closure)
apply (simp)
done

theorem IEvalR_inverse :
"IEvalR (EvalR p) = p"
apply (simp add: IEvalR_def EvalR_def)
apply (simp add: image_image)
apply (simp add: image_def)
apply (simp add: BindP_inverse)
done

theorem BindR_inject [simp] :
"BindR b1 = BindR b2 \<longleftrightarrow> b1 = b2"
apply (auto simp add: BindR_def)
apply (erule Rep_WF_BINDING_elim)+
apply (rule Rep_WF_BINDING_intro)
apply (auto simp add: override_on_eq)
apply (rule ext)
apply (case_tac "x \<in> DASHED")
-- {* Subgoal 1 *}
apply (drule_tac x = "undash x" in spec)
back
apply (subgoal_tac "undash x \<notin> DASHED")
apply (simp)
apply (simp add: urename)
apply (simp add: var_defs)
-- {* Subgoal 2 *}
apply (simp)
done

theorem BindR_COMPOSABLE_BINDINGS :
"\<lbrakk>(rb1, rb3) = BindR b1;
 (rb3, rb2) = BindR b2\<rbrakk> \<Longrightarrow>
 (b1, b2) \<in> COMPOSABLE_BINDINGS"
apply (simp add: BindR_def)
apply (simp add: COMPOSABLE_BINDINGS_def)
apply (auto)
apply (erule Rep_WF_BINDING_elim)+
apply (simp add: override_on_eq RenameB_def)
-- {* Subgoal 1 *}
apply (drule_tac x = "v" in spec)
apply (simp add:urename)
-- {* Subgoal 2 *}
apply (simp add: binding_equiv_def)
apply (simp add: NON_REL_VAR_def)
apply (rule ballI)
apply (simp add: urename)
apply (erule Rep_WF_BINDING_elim)+
apply (simp add:override_on_eq)
apply (drule_tac x = "x" in spec)
apply (simp add:RenameB_def)
apply (metis SS_ident_app)
done

theorem BindR_override :
"\<lbrakk>(rb1, rb3) = BindR b1;
 (rb3, rb2) = BindR b2\<rbrakk> \<Longrightarrow>
 (rb1, rb2) = BindR (b1 \<oplus>\<^sub>b b2 on DASHED)"
apply (simp add: BindR_def)
apply (auto elim!:Rep_WF_BINDING_elim intro!:Rep_WF_BINDING_intro)
apply (simp add: override_on_eq)
apply (clarify)
apply (drule_tac x = "x" in spec)
apply (auto simp add: urename)
apply (metis SS_UNDASHED_app SS_ident_app UNDASHED_dash_DASHED override_on_def)
done

subsection {* Transfer Theorems *}

theorem EvalR_inj_on :
"inj EvalR"
  by (metis (lifting) IEvalR_inverse inj_onI)

theorem EvalR_simp [evalr] :
"p1 = p2 \<longleftrightarrow> \<lbrakk>p1\<rbrakk>R = \<lbrakk>p2\<rbrakk>R"
apply (rule inj_on_eval_simp [of EvalR UNIV "p1" "p2"])
apply (simp_all add: EvalR_inj_on)
done

theorem EvalR_intro :
"\<lbrakk>p1\<rbrakk>R = \<lbrakk>p2\<rbrakk>R \<Longrightarrow> p1 = p2"
apply (rule inj_on_eval_intro [of EvalR UNIV "p1" "p2"])
apply (simp_all add: EvalR_inj_on)
done

subsection {* Distribution Theorems *}

theorem EvalR_TrueP_explicit :
"\<lbrakk>true\<rbrakk>R = {(b1, b2) | b1 b2 .
   b1 \<in> WF_REL_BINDING \<and>
   b2 \<in> WF_REL_BINDING \<and>
   b1 \<cong> b2 on DASHED \<and>
   b1 \<cong> b2 on NON_REL_VAR}"
apply (simp add: EvalR_def)
apply (simp add: TrueP_def)
apply (simp add: image_def)
apply (simp add: BindR_def WF_REL_BINDING_def)
apply (simp add: binding_equiv_def)
apply (simp add: set_eq_subset)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "xa" in exI)
apply (simp)
-- {* Subgoal 2 *}
apply (rule_tac x = "RenameB SS xa" in exI)
apply (simp add: closure)
-- {* Subgoal 3 *}
apply (simp)
-- {* Subgoal 4 *}
apply (simp add: NON_REL_VAR_def)
apply (simp add: RenameB_def closure urename)
-- {* Subgoal 5 *}
apply (rule_tac x = "b \<oplus>\<^sub>b (RenameB SS ba) on DASHED" in exI)
apply (auto elim!:Rep_WF_BINDING_elim intro!:Rep_WF_BINDING_intro)
apply (simp add: override_on_eq)
apply (safe)
apply (case_tac "x \<in> UNDASHED")
apply (simp add: SS_simps)
apply (simp add: SS_simps)
apply (drule_tac x = "x" in bspec)
apply (simp add: NON_REL_VAR_def var_defs)
apply (simp)
done

theorem EvalR_TrueP [evalr] :
"\<lbrakk>true\<rbrakk>R = {(x \<oplus>\<^sub>b bc on DASHED, RenameB SS x \<oplus>\<^sub>b bc on DASHED) | x. x \<in> UNIV}"
apply (simp add: EvalR_def)
apply (simp add: TrueP_def)
apply (simp add: image_def BindR_def)
done

theorem EvalR_FalseP [evalr] :
"\<lbrakk>false\<rbrakk>R = {}"
apply (simp add: EvalR_def)
apply (simp add: FalseP_def)
done

theorem EvalR_NotP [evalr] :
"\<lbrakk>\<not>p p\<rbrakk>R = \<lbrakk>true\<rbrakk>R - \<lbrakk>p\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: NotP_def TrueP_def)
apply (auto)
done

theorem EvalR_AndP [evalr] :
"\<lbrakk>p1 \<and>p p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R \<inter> \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: AndP_def)
apply (auto)
done

theorem EvalR_OrP [evalr] :
"\<lbrakk>p1 \<or>p p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R \<union> \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: OrP_def)
apply (auto)
done

declare ImpliesP_def [evalr]

declare IffP_def [evalr]

theorem EvalR_SkipR [evalr] :
"\<lbrakk>II\<rbrakk>R = Id_on WF_REL_BINDING"
apply (simp add: EvalR_def)
apply (simp add: SkipR_def)
apply (simp add: WF_REL_BINDING_def)
apply (simp add: image_def)
apply (simp add: BindR_def)
apply (simp add: Id_on_def)
apply (simp add: set_eq_iff)
apply (safe)
-- {* Subgoal 1 *}
apply (rename_tac x b)
apply (rule_tac x = "b \<oplus>\<^sub>b bc on DASHED" in exI)
apply (simp add: override_on_eq)
apply (rule conjI)
apply (rule_tac x = "b" in exI)
apply (simp)
apply (simp add: RenameB_def closure)
apply (rule Rep_WF_BINDING_intro)
apply (simp add:override_on_eq o_def)
apply (smt SS_UNDASHED_app SS_ident_app)
-- {* Subgoal 2 *}
apply (rule_tac x = "b \<oplus>\<^sub>b (RenameB SS b) on DASHED" in exI)
apply (simp add: override_on_eq)
apply (auto)
-- {* Subgoal 2.1 *}
apply (subgoal_tac "v \<notin> DASHED")
apply (simp)
apply (simp add: RenameB_def closure urename)
apply (auto) [1]
-- {* Subgoal 2.2 *}
apply (simp add: RenameB_def closure)
apply (rule Rep_WF_BINDING_intro)
apply (auto simp add:override_on_eq urename)
apply (metis (no_types) SS_DASHED_app SS_UNDASHED_app SS_ident_app UNDASHED_dash_DASHED o_def override_on_def undash_dash)
done

theorem EvalR_SkipRA [evalr] :
"\<lbrakk> vs \<subseteq> UNDASHED \<union> DASHED; HOMOGENEOUS vs \<rbrakk> \<Longrightarrow>
 \<lbrakk>II vs\<rbrakk>R = { BindR b | b. \<forall>v\<in>in vs. \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b (v\<acute>)}"
  by (simp add:EvalR_def SkipRA_rep_eq_alt image_Collect BindR_def)

lemma EvalP_AssignR1 [eval]:
  "e \<rhd>\<^sub>e x \<Longrightarrow> \<lbrakk>x :=p e\<rbrakk>b = (\<forall> v \<in> UNDASHED. if (v = x) then \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<lbrakk>e\<rbrakk>\<epsilon>b else \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>b\<rangle>\<^sub>b v)"
  by (simp add:EvalP_def EvalE_def AssignsR.rep_eq IdA.rep_eq VarE.rep_eq AssignF_upd_rep_eq)

lemma EvalP_AssignR2 [eval]:
  "\<lbrakk> e \<rhd>\<^sub>e x; f \<rhd>\<^sub>e y \<rbrakk> \<Longrightarrow>
   \<lbrakk>x,y :=p e,f\<rbrakk>b = (\<forall> v \<in> UNDASHED. if (v = y) 
                                     then \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<lbrakk>f\<rbrakk>\<epsilon>b 
                                     else if (v = x) 
                                          then \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<lbrakk>e\<rbrakk>\<epsilon>b 
                                          else \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>b\<rangle>\<^sub>b v)"
  by (simp add:EvalP_def EvalE_def AssignsR.rep_eq IdA.rep_eq VarE.rep_eq AssignF_upd_rep_eq)

lemma EvalP_AssignsR [eval]:
  "\<lbrakk>AssignsR f\<rbrakk>b = (\<forall> v \<in> UNDASHED. \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>Rep_AssignF f v\<rangle>\<^sub>e b)"
  by (simp add:EvalP_def AssignsR.rep_eq)

theorem EvalR_AssignR [evalr] :
"\<lbrakk> x \<in> UNDASHED; e \<rhd>\<^sub>e x; UNREST_EXPR DASHED e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>x :=p e\<rbrakk>R = {(b, b(x:=\<^sub>b (\<lbrakk>e\<rbrakk>\<epsilon> b))) | b. b \<in> WF_REL_BINDING}"
apply (simp add: EvalR_def EvalE_def)
apply (simp add: AssignsR.rep_eq IdA.rep_eq VarE.rep_eq AssignF_upd_rep_eq)
apply (simp add: WF_REL_BINDING_def)
apply (simp add: set_eq_iff)
apply (safe)
apply (simp add:BindR_def)
apply (safe)
apply (frule_tac x="x" in bspec)
apply (force)
apply (simp)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e (xa \<oplus>\<^sub>b bc on DASHED) = \<langle>e\<rangle>\<^sub>e xa")
apply (drule sym)
apply (auto)[1]
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e xa \<rhd> x")
apply (simp)
apply (rule)
apply (simp add:RenameB_rep_eq)
apply (rule)
apply (case_tac "xb \<in> DASHED")
apply (auto)
apply (metis SS_UNDASHED_app)
apply (metis SS_UNDASHED_app SS_ident_app)
apply (simp add:image_def BindR_def)
apply (rule_tac x="ba(x\<acute> :=\<^sub>b \<langle>e\<rangle>\<^sub>e ba) \<oplus>\<^sub>b RenameB SS ba on (DASHED - {x\<acute>})" in exI)
apply (auto)
apply (metis EvalE_compat EvalE_def UNDASHED_dash_DASHED UNREST_EXPR_member binding_override_upd binding_upd_apply var_compat_dash)
apply (subgoal_tac "v\<acute> \<in> DASHED - {x\<acute>}")
apply (simp add:RenameB_rep_eq urename)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e ba \<rhd> x\<acute>")
apply (metis (lifting) UNDASHED_eq_dash_contra binding_upd_apply)
apply (auto)
apply (metis evar_compat_def var_compat_dash)
apply (metis EvalE_compat EvalE_def UNDASHED_dash_DASHED binding_override_simps(3) binding_override_upd evar_compat_dash)
apply (rule)
apply (simp add:RenameB_rep_eq)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e (ba \<oplus>\<^sub>b bc on DASHED) = \<langle>e\<rangle>\<^sub>e ba")
apply (simp)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e ba \<rhd> x")
apply (simp)
apply (rule)
apply (case_tac "xa \<in> DASHED")
apply (simp_all add:urename)
apply (case_tac "xa = x")
apply (simp_all)
apply (metis binding_upd_apply var_compat_dash)
apply (smt Rep_WF_BINDING_rep_eq SS_UNDASHED_app SS_VAR_RENAME_INV SS_ident_app UNDASHED_dash_DASHED VAR_RENAME_INV_app fun_upd_apply member_remove o_apply override_on_apply_in override_on_apply_notin remove_def var_compat_dash)
apply (metis evar_compat_def)
done

theorem EvalR_ExprR [evalr]: 
  "\<lbrakk>ExprP e\<rbrakk>R = {BindR b |b. DestBool (\<lbrakk>e\<rbrakk>\<epsilon> b)}"
  by (simp add:ExprP_def LiftP_def EvalR_def BindR_def EvalE_def UNREST_EXPR_member[THEN sym] etype_rel_def Defined_WF_EXPRESSION_def image_Collect)

theorem EvalR_EqualP [evalr]:
  "\<lbrakk>EqualP e f\<rbrakk>R = {BindR b |b. (\<lbrakk>e\<rbrakk>\<epsilon> b = \<lbrakk>f\<rbrakk>\<epsilon> b)}"
  by (auto simp add:EvalR_def EqualP_def EvalE_def)

lemma EvalR_ConvR [evalr]:
  "\<lbrakk>p\<^sup>\<smile>\<rbrakk>R = \<lbrakk>p\<rbrakk>R\<inverse>"
  apply (auto simp add: EvalR_def ConvR_def RenameP.rep_eq BindR_def urename closure)
  apply (metis BindR_def image_iff)
  apply (metis (lifting) BindR_def RenameB_involution SS_VAR_RENAME_INV image_eqI)
done

theorem SubstP_rel_UNDASHED [evalr] :
"\<lbrakk> x \<in> UNDASHED; e \<rhd>\<^sub>e x; UNREST_EXPR DASHED e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e|x]\<rbrakk>R = {(b1, b2) | b1 b2. (b1(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<epsilon>b1), b2) \<in> \<lbrakk>p\<rbrakk>R}"
apply (auto simp add: EvalR_def EvalE_def BindR_def SubstP_def image_def)
apply (rule_tac x="xa(x :=\<^sub>b \<langle>e\<rangle>\<^sub>e xa)" in bexI)
apply (auto)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e (xa \<oplus>\<^sub>b bc on DASHED) = \<langle>e\<rangle>\<^sub>e xa")
apply (simp)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e xa \<rhd> x")
apply (simp)
apply (metis (lifting) evar_compat_def)
apply (metis (lifting) UNREST_EXPR_member)
apply (rule)
apply (rule)
apply (simp add:RenameB_rep_eq)
apply (case_tac "xb \<in> DASHED")
apply (simp_all add:urename)
apply (case_tac "xb \<in> UNDASHED")
apply (simp_all add:urename)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e xa \<rhd> x")
apply (metis UNDASHED_dash_DASHED UNDASHED_not_DASHED binding_upd_apply evar_compat_def)
apply (metis binding_upd_apply evar_compat_def)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e xa \<rhd> x")
apply (metis binding_upd_apply)
apply (metis binding_upd_apply evar_compat_def)
apply (rule_tac x="xa \<oplus>\<^sub>b xb on DASHED" in exI)
apply (simp)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e (xa \<oplus>\<^sub>b xb on DASHED) = \<langle>e\<rangle>\<^sub>e xa")
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e xa \<rhd> x")
apply (auto)
apply (metis UNDASHED_DASHED_inter(2) binding_override_simps(11) binding_override_simps(4) binding_override_simps(6) binding_upd_override inf_commute)
apply (rule)
apply (rule)
apply (simp add:RenameB_rep_eq)
apply (case_tac "xc \<in> UNDASHED")
apply (simp add:SS_simps)
apply (case_tac "xc \<in> DASHED")
apply (simp)
apply (simp add:SS_simps)
apply (metis binding_override_on_eq binding_override_simps(2) binding_upd_override evar_compat_def)
apply (metis evar_compat_def)
done

theorem SubstP_rel_DASHED [evalr] :
"\<lbrakk> x \<in> UNDASHED; e \<rhd>\<^sub>e x; UNREST_EXPR DASHED e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>SubstP p e[SS]\<epsilon> x\<acute>\<rbrakk>R = {(b1, b2) | b1 b2. (b1, b2(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<epsilon>b2)) \<in> \<lbrakk>p\<rbrakk>R}"
  apply (auto simp add: EvalR_def EvalE_def BindR_def SubstP_def image_def typing defined urename)
  apply (rule_tac x="xa(x\<acute> :=\<^sub>b \<langle>RenameE e SS\<rangle>\<^sub>e xa)" in bexI)
  apply (auto simp add:typing defined urename)
  apply (rule, rule)
  apply (simp)
  apply (case_tac "xb = x")
  apply (simp add:urename typing defined)
  apply (metis EvalE_RenameE EvalE_def SS_inv)
  apply (case_tac "xb \<in> DASHED")
  apply (simp add:urename typing defined)
  apply (simp add:urename typing defined)
  apply (metis SS_UNDASHED_app SS_ident_app UNDASHED_dash_DASHED dash_elim)
  apply (rule_tac x="xb \<oplus>\<^sub>b RenameB SS y on DASHED" in exI)
  apply (auto simp add:typing defined urename)
  apply (subgoal_tac "xb(x\<acute> :=\<^sub>b \<langle>RenameE e SS\<rangle>\<^sub>e (xb \<oplus>\<^sub>b RenameB SS y on DASHED)) \<oplus>\<^sub>b RenameB SS y on DASHED - {x\<acute>} = xb")
  apply (simp)
  apply (rule, rule, simp)
  apply (case_tac "xa \<in> UNDASHED")
  apply (simp add:typing defined)
  apply (metis UNDASHED_dash_not_UNDASHED)
  apply (simp add:typing defined)
  apply (case_tac "xa = x\<acute>")
  apply (simp_all add:typing defined)
  apply (subgoal_tac "\<langle>xb\<rangle>\<^sub>b x\<acute> = \<langle>e\<rangle>\<^sub>e y")
  apply (auto simp add:typing defined urename)
  apply (subgoal_tac "\<langle>RenameE e SS\<rangle>\<^sub>e (xb \<oplus>\<^sub>b RenameB SS y on DASHED) = \<langle>RenameE e SS\<rangle>\<^sub>e (RenameB SS y)")
  apply (metis (hide_lams, no_types) RenameB_inv_cancel1 RenameE.rep_eq comp_apply)
  apply (rule WF_EXPRESSION_UNREST_binding_equiv[of "DASHED \<union> NON_REL_VAR"])
  apply (simp add:unrest UNREST_EXPR_subset urename closure)
  apply (rule UNREST_EXPR_subset)
  apply (rule unrest) back
  apply (simp)
  apply (simp add:urename)
  apply (force)
  apply (subgoal_tac "xb \<cong> RenameB SS y on  NON_REL_VAR")
  apply (smt Compl_iff Int_iff Un_iff binding_equiv_comm binding_equiv_def binding_equiv_override_right_intro sup.commute)
  apply (auto simp add:binding_equiv_def urename)[1]
  apply (erule Rep_WF_BINDING_elim)
  apply (simp)
  apply (drule_tac x="xa" and y="xa" in cong, simp)
  apply (simp add:typing defined)
  apply (metis SS_DASHED_member SS_NON_REL_VAR SS_UNDASHED_app comp_apply dash_uniqs(1) override_on_apply_notin)
  apply (erule Rep_WF_BINDING_elim)
  apply (simp)
  apply (drule_tac x="x" and y="x" in cong, simp, simp add:typing defined urename)
  apply (case_tac "xa \<in> DASHED")
  apply (simp add:urename)
  apply (erule Rep_WF_BINDING_elim)
  apply (simp)
  apply (drule_tac x="undash xa" and y="undash xa" in cong, simp)
  apply (simp add:typing defined urename)
  apply (auto)
  apply (metis dash_undash_DASHED)
  apply (simp add:RenameB_override_distr1 urename closure)
  apply (metis UNDASHED_DASHED_inter(2) binding_override_reorder binding_override_simps(2) binding_upd_override evar_compat)
done


(*
theorem SubstP_rel_DASHED [evalr] :
"\<lbrakk> x \<in> DASHED; e \<rhd>\<^sub>e x; UNREST_EXPR UNDASHED e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e|x]\<rbrakk>R = {(b1, b2) | b1 b2. (b1(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<epsilon>b1), b2) \<in> \<lbrakk>p\<rbrakk>R}"
*)

lemma EvalE_RenameB_VAR_RENAME_ON [evale]:
  assumes "ss \<in> VAR_RENAME_ON vs" "UNREST_EXPR vs e"
  shows "\<lbrakk>e\<rbrakk>\<epsilon> (RenameB ss b) = \<lbrakk>e\<rbrakk>\<epsilon> b"
proof -

  have "RenameB ss b = RenameB ss b \<oplus>\<^sub>b b on - vs"
    by (fact RenameB_override_VAR_RENAME_ON[OF assms(1)])

  with assms(2) show ?thesis
    by (metis EvalE_UNREST_override binding_override_minus)

qed

theorem SubstP_rel_NON_REL_VAR [evalr] :
"\<lbrakk> x \<in> NON_REL_VAR; e \<rhd>\<^sub>e x; UNREST_EXPR REL_VAR e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e|x]\<rbrakk>R = {(b1, b2) | b1 b2. (b1(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<epsilon>b1), b2(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<epsilon>b2)) \<in> \<lbrakk>p\<rbrakk>R}"
apply (subgoal_tac "x \<notin> DASHED")
apply (subgoal_tac "UNREST_EXPR DASHED e")
apply (auto simp add: EvalR_def BindR_def SubstP_def image_def typing urename evale closure)
apply (metis EvalE_RenameB_VAR_RENAME_ON EvalE_def SS_VAR_RENAME_ON)
apply (simp add:EvalE_def[THEN sym])
apply (subgoal_tac "\<langle>xb\<rangle>\<^sub>b x = \<lbrakk>e\<rbrakk>\<epsilon>xa") (* Verified by sledgehammer *)
apply (subgoal_tac "\<langle>xb\<rangle>\<^sub>b x = \<lbrakk>e\<rbrakk>\<epsilon>y") (* Verified by sledgehammer *)
apply (subgoal_tac "xb \<oplus>\<^sub>b RenameB SS y on DASHED = xb")
apply (rule_tac x="xa \<oplus>\<^sub>b RenameB SS y on DASHED" in exI)
apply (simp add:typing defined urename evale)
apply (rule)
apply (rule binding_override_equiv[THEN sym])
apply (metis (hide_lams, no_types) ComplI EvalE_compat binding_override_equiv1 binding_override_minus binding_override_simps(2) binding_override_simps(3) binding_upd_override)
apply (simp add:RenameB_override_distr1 urename closure)
apply (subgoal_tac "y \<cong> bc on DASHED")
apply (subgoal_tac "y \<cong> RenameB SS xa on NON_REL_VAR")
apply (metis (hide_lams, no_types) NON_REL_VAR_def binding_equiv_override binding_override_equiv binding_override_minus binding_override_simps(1))
apply (subgoal_tac "y \<cong> xb on NON_REL_VAR")
sorry

theorem RenameB_SS_COMPOSABLE_BINDINGS_1 :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS\<rbrakk> \<Longrightarrow>
 RenameB SS b1 \<oplus>\<^sub>b bc on DASHED = b2 \<oplus>\<^sub>b bc on DASHED"
apply (rule Rep_WF_BINDING_intro)
apply (simp add: override_on_eq)
apply (safe)
apply (auto simp add: COMPOSABLE_BINDINGS_def)
apply (metis (lifting) Compl_iff NON_REL_VAR_def SS_UNDASHED_app SS_ident_app UnE binding_equiv_def)
done

theorem RenameB_SS_COMPOSABLE_BINDINGS_2 :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS\<rbrakk> \<Longrightarrow>
 RenameB SS (b1 \<oplus>\<^sub>b b2 on DASHED) \<oplus>\<^sub>b bc on DASHED = RenameB SS b2 \<oplus>\<^sub>b bc on DASHED"
apply (rule Rep_WF_BINDING_intro)
apply (simp add: override_on_eq)
apply (auto simp add: COMPOSABLE_BINDINGS_def binding_equiv_def NON_REL_VAR_def)
apply (metis Compl_iff Int_iff SS_UNDASHED_app SS_ident_app UNDASHED_dash_DASHED override_on_def)
done

theorems RenameB_SS_COMPOSABLE_BINDINGS =
  RenameB_SS_COMPOSABLE_BINDINGS_1
  RenameB_SS_COMPOSABLE_BINDINGS_2

theorem EvalR_SemiR [evalr] :
"\<lbrakk>p1 ; p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R O \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: SemiR_def)
apply (simp add: set_eq_iff)
apply (simp add: relcomp_unfold image_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rename_tac x rb1 rb2 xa b1 b2)
apply (rule_tac x = "(RenameB SS b1) \<oplus>\<^sub>b bc on DASHED" in exI)
apply (rule conjI)
-- {* Subgoal 1.1 *}
apply (rule_tac x = "b1" in bexI)
apply (simp add: BindR_def)
apply (assumption)
-- {* Subgoal 1.2 *}
apply (rule_tac x = "b2" in bexI)
apply (simp add: BindR_def)
apply (simp add: RenameB_SS_COMPOSABLE_BINDINGS)
apply (assumption)
-- {* Subgoal 2 *}
apply (rename_tac x rb1 rb2 rb3 b1 b2)
apply (rule_tac x = "b1 \<oplus>\<^sub>b b2 on DASHED" in exI)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (rule_tac x = "b1" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
apply (simp add: BindR_COMPOSABLE_BINDINGS)
-- {* Subgoal 2.1 *}
apply (metis BindR_override)
done

declare CondR_def [evalr,evalrr]

lemma EvalR_as_EvalP [eval]: "\<lbrakk>p\<rbrakk>R = {BindR b | b. \<lbrakk>p\<rbrakk>b}"
  by (auto simp add:EvalR_def EvalP_def)

lemma EvalR_refinement [evalr]: "p \<sqsubseteq> q \<longleftrightarrow> \<lbrakk>q\<rbrakk>R \<subseteq> \<lbrakk>p\<rbrakk>R"
  by (auto simp add:EvalR_as_EvalP less_eq_WF_PREDICATE_def eval)

definition MkRel :: "'VALUE RELATION \<Rightarrow> ('VALUE WF_REL_BINDING) rel" where
"MkRel R = map_pair MkRelB MkRelB ` R"

lemma MkRelB_inj: "inj_on MkRelB WF_REL_BINDING"
  by (rule inj_onI, metis MkRelB_inverse)

lemma MkRel_inj: "\<lbrakk> P \<subseteq> WF_REL; Q \<subseteq> WF_REL; MkRel P = MkRel Q \<rbrakk> \<Longrightarrow> P = Q"
  apply (subgoal_tac "inj_on (map_pair MkRelB MkRelB) (P \<union> Q)")
  apply (drule inj_on_Un_image_eq_iff)
  apply (simp add:MkRel_def)
  apply (rule subset_inj_on)
  apply (rule map_pair_inj_on)
  apply (rule MkRelB_inj)
  apply (rule MkRelB_inj)
  apply (auto)
done

theorem MkRel_EvalR_simp :
"p1 = p2 \<longleftrightarrow> MkRel \<lbrakk>p1\<rbrakk>R = MkRel \<lbrakk>p2\<rbrakk>R"
  apply (simp add:evalr)
  apply (rule)
  apply (force)
  apply (rule MkRel_inj)
  apply (simp_all add:EvalR_range)
done

lemma MkRel_subset:
  "\<lbrakk> p \<subseteq> WF_REL; q \<subseteq> WF_REL \<rbrakk> \<Longrightarrow> p \<subseteq> q \<longleftrightarrow> MkRel p \<subseteq> MkRel q"
  apply (simp add:MkRel_def)
  apply (smt MkRel_def MkRel_inj subset_image_iff subset_trans)
done

theorem MkRel_EvalR_intro :
"MkRel \<lbrakk>p1\<rbrakk>R = MkRel \<lbrakk>p2\<rbrakk>R \<Longrightarrow> p1 = p2"
  by (simp add:MkRel_EvalR_simp)

abbreviation EvalRR ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   ('VALUE WF_REL_BINDING) rel" ("\<lbrakk>_\<rbrakk>\<R>") where
"EvalRR p \<equiv> MkRel \<lbrakk>p\<rbrakk>R"

lemma EvalRR_simp [evalrr] :
"p1 = p2 \<longleftrightarrow> \<lbrakk>p1\<rbrakk>\<R> = \<lbrakk>p2\<rbrakk>\<R>"
  by (simp add: MkRel_EvalR_simp)

lemma EvalRR_intro :
"\<lbrakk>p1\<rbrakk>\<R> = \<lbrakk>p2\<rbrakk>\<R> \<Longrightarrow> p1 = p2"
  by (simp add:evalrr)

lemma EvalRR_SkipR [evalrr]: "\<lbrakk>II\<rbrakk>\<R> = Id"
  apply (simp add:evalr)
  apply (auto simp add:MkRel_def Id_on_def image_def)
  apply (metis DestRelB DestRelB_inverse)
done

theorem EvalRR_FalseP [evalrr] :
"\<lbrakk>false\<rbrakk>\<R> = {}"
  by (simp add: evalr MkRel_def)

theorem EvalRR_AndP [evalrr] :
"\<lbrakk>p1 \<and>p p2\<rbrakk>\<R> = \<lbrakk>p1\<rbrakk>\<R> \<inter> \<lbrakk>p2\<rbrakk>\<R>"
  by (force simp add: evalr MkRel_def)

theorem EvalRR_OrP [evalrr] :
"\<lbrakk>p1 \<or>p p2\<rbrakk>\<R> = \<lbrakk>p1\<rbrakk>\<R> \<union> \<lbrakk>p2\<rbrakk>\<R>"
  by (force simp add: evalr MkRel_def)

theorem EvalRR_SemiR [evalrr] :
"\<lbrakk>p1 ; p2\<rbrakk>\<R> = \<lbrakk>p1\<rbrakk>\<R> O \<lbrakk>p2\<rbrakk>\<R>"
  by (force simp add: evalr MkRel_def)

lemma EvalRR_ConvR [evalrr]:
  "\<lbrakk>p\<^sup>\<smile>\<rbrakk>\<R> = \<lbrakk>p\<rbrakk>\<R>\<inverse>"
  by (force simp add:evalr MkRel_def)

lemma EvalRR_refinement [evalrr]: "p \<sqsubseteq> q \<longleftrightarrow> \<lbrakk>q\<rbrakk>\<R> \<subseteq> \<lbrakk>p\<rbrakk>\<R>"
  by (simp add:evalr evalrr MkRel_subset[THEN sym] EvalR_range)


(* The following are useless since quantifications are not supported yet. *)

(*
declare Tautology_def [evalr]
declare Contradiction_def [evalr]
declare Refinement_def [evalr]
*)

subsection {* Proof Tactics *}

text {*
  We note that the proof method is also generic and does not have to be
  recreated for concrete instantiations of the @{term PRED} locale.
*}

ML {*
  fun utp_rel_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evalr.get ctxt)
      addsimps (closure.get ctxt);
*}

ML {*
  fun utp_rel_auto_simpset ctxt =
    (simpset_of ctxt)
      addsimps @{thms "relcomp_unfold"}
*}

ML {*
  fun utp_rel_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_rel_simpset ctxt) i)
*}

ML {*
  fun utp_rel_auto_tac thms ctxt i =
    TRY (asm_full_simp_tac (utp_rel_simpset ctxt) i) THEN
    TRY (asm_full_simp_tac (utp_rel_auto_simpset ctxt) i) THEN
    (auto_tac ctxt)
*}

method_setup utp_rel_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_rel_tac thms ctxt))
*} "proof tactic for relations"

method_setup utp_rel_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_rel_auto_tac thms ctxt))
*} "proof tactic for relations with auto"

subsection {* Algebraic Laws *}

lemma "x \<noteq> y \<Longrightarrow> x :=p e; y :=p f = x,y :=p e,f"
  apply (utp_rel_tac)
oops

(*
lemma "{(F x, G x) | x . P x} O {(H x, I x) | x . Q x} = {(F x, I x) | x. P x \<and> Q x \<and> G x = H x}"
  apply (auto)
*)

(*
lemma "VarP ok \<Rightarrow>p VarP ok\<acute> ; VarP ok \<Rightarrow>p VarP ok\<acute> = VarP ok \<Rightarrow>p VarP ok\<acute>"
  apply (rule EvalR_intro)
  apply (simp add:EvalR_SemiR)
  apply (simp add:eval)
  apply (auto)
  apply (simp add:evalr)
*)

lemma AssignR_alt_def: 
  "\<lbrakk>v \<rhd>\<^sub>e x ; x \<in> UNDASHED \<rbrakk> \<Longrightarrow> `x := v` = `($x\<acute> = v) \<and> II\<^bsub>REL_VAR - {x,x\<acute>}\<^esub>`"
  apply (simp add:SkipRA_def)
  apply (utp_pred_tac, utp_expr_tac)
  apply (safe)
  apply (simp_all add:IdA.rep_eq AssignF_upd_rep_eq evale VarE.rep_eq EvalE_def urename)
  apply (rule_tac x="b(x\<acute> :=\<^sub>b \<langle>b\<rangle>\<^sub>b x)" in exI)
  apply (simp_all)
  apply (rule)
  apply (metis (lifting) UNDASHED_eq_dash_contra undash_dash)
  apply (drule_tac x="va" in bspec, simp_all)
  apply (metis UNDASHED_eq_dash_contra undash_dash)
done

end