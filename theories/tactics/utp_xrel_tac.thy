(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_xrel_tac.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Proof Tactic for Wellformed Relations *}

theory utp_xrel_tac
imports utp_rel_tac
begin

text {* Theorem Attribute *}

ML {*
  structure evalrx =
    Named_Thms (val name = @{binding evalrx} val description = "evalrx theorems")
*}

setup evalrx.setup

definition WF_XREL_BINDING :: "'VALUE WF_BINDING set" where
"WF_XREL_BINDING = {b \<oplus>\<^sub>b bc on DASHED \<union> NON_REL_VAR | b . b \<in> UNIV}"

lemma WF_XREL_BINDING: 
  "WF_XREL_BINDING \<subseteq> WF_REL_BINDING"
  apply (auto simp add:WF_REL_BINDING_def WF_XREL_BINDING_def)
  apply (metis binding_override_simps(1) sup_commute)
done

abbreviation "WF_XREL \<equiv> WF_XREL_BINDING \<times> WF_XREL_BINDING"

typedef 'VALUE WF_XREL_BINDING = "WF_XREL_BINDING :: 'VALUE WF_BINDING set"
  morphisms DestXRelB MkXRelB
  by (auto simp add:WF_XREL_BINDING_def)

declare DestXRelB [simp]
declare DestXRelB_inverse [simp]
declare MkXRelB_inverse [simp]

lemma DestXRelB_intro [intro]:
  "DestXRelB x = DestXRelB y \<Longrightarrow> x = y"
  by (simp add:DestXRelB_inject)

lemma DestXRelB_elim [elim]:
  "\<lbrakk> x = y; DestXRelB x = DestXRelB y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

notation DestXRelB ("\<langle>_\<rangle>\<^sub>x")

setup_lifting type_definition_WF_XREL_BINDING

lemma DestXRelB_DASHED [simp]: 
  "x \<in> DASHED \<Longrightarrow> \<langle>\<langle>b\<rangle>\<^sub>x\<rangle>\<^sub>b x = \<langle>bc\<rangle>\<^sub>b x"
  by (insert DestXRelB[of b], auto simp add:WF_XREL_BINDING_def)

lemma DestXRelB_NON_REL_VAR [simp]: 
  "x \<in> NON_REL_VAR \<Longrightarrow> \<langle>\<langle>b\<rangle>\<^sub>x\<rangle>\<^sub>b x = \<langle>bc\<rangle>\<^sub>b x"
  by (insert DestXRelB[of b], auto simp add:WF_XREL_BINDING_def)

lemma DestXRelB_NOT_UNDASHED [simp]:
  "x \<notin> UNDASHED \<Longrightarrow> \<langle>\<langle>b\<rangle>\<^sub>x\<rangle>\<^sub>b x = \<langle>bc\<rangle>\<^sub>b x"
  by (metis Compl_iff DestXRelB_DASHED DestXRelB_NON_REL_VAR NON_REL_VAR_def Un_iff)

lemma DestXRelB_binding_equiv:
  "\<langle>b1\<rangle>\<^sub>x \<cong> bc on DASHED \<union> NON_REL_VAR"
  apply (insert DestXRelB[of b1])
  apply (auto simp add:WF_XREL_BINDING_def)
done

lift_definition xbinding_override_on ::
  "'VALUE WF_XREL_BINDING \<Rightarrow>
   'VALUE WF_XREL_BINDING \<Rightarrow>
   'VALUE VAR set \<Rightarrow>
   'VALUE WF_XREL_BINDING" ("_ \<oplus>\<^sub>x _ on _" [56, 56, 0] 55) is "binding_override_on"
  apply (auto simp add:WF_XREL_BINDING_def)
  apply (metis (hide_lams, no_types) binding_override_assoc binding_override_simps(1) binding_override_simps(4) sup_commute)
done

declare xbinding_override_on.rep_eq [simp]

definition xbinding_upd :: 
  "'VALUE WF_XREL_BINDING \<Rightarrow>
   'VALUE VAR \<Rightarrow>
   'VALUE \<Rightarrow>
   'VALUE WF_XREL_BINDING" where
"xbinding_upd b x v = MkXRelB (binding_upd \<langle>b\<rangle>\<^sub>x x v)"

lemma DestXRelB_rep_eq [simp]:
  "\<lbrakk> v \<rhd> x; x \<in> UNDASHED \<rbrakk> \<Longrightarrow> \<langle>xbinding_upd b x v\<rangle>\<^sub>x = binding_upd \<langle>b\<rangle>\<^sub>x x v"
  apply (subgoal_tac "\<langle>b\<rangle>\<^sub>x(x :=\<^sub>b v) \<in> WF_XREL_BINDING")
  apply (simp add:var_compat_def xbinding_upd_def)
  apply (insert DestXRelB[of b])
  apply (simp add:WF_XREL_BINDING_def)
  apply (rule_tac x="\<langle>b\<rangle>\<^sub>x(x :=\<^sub>b v)" in exI)
  apply (auto)
  apply (subgoal_tac "DASHED \<union> NON_REL_VAR - {x} \<union> (DASHED \<union> NON_REL_VAR) = DASHED \<union> NON_REL_VAR - {x}")
  apply (auto simp add:NON_REL_VAR_def)
done

nonterminal xbupdbinds and xbupdbind

syntax
  "_xbupdbind" :: "['a, 'a] => xbupdbind"                 ("(2_ :=\<^sub>x/ _)")
  ""           :: "xbupdbind => xbupdbinds"               ("_")
  "_xbupdbinds":: "[xbupdbind, xbupdbinds] => xbupdbinds" ("_,/ _")
  "_XBUpdate"  :: "['a, xbupdbinds] => 'a"                ("_/'((_)')" [1000, 0] 900)

translations
  "_XBUpdate f (_xbupdbinds b bs)" == "_XBUpdate (_XBUpdate f b) bs"
  "f(x:=\<^sub>xy)" == "CONST xbinding_upd f x y"

type_synonym 'VALUE XRELATION =
  "('VALUE WF_XREL_BINDING \<times>
    'VALUE WF_XREL_BINDING) set"

subsection {* Interpretation Function *}

definition BindRX ::
  "'VALUE WF_BINDING \<Rightarrow>
   'VALUE WF_XREL_BINDING \<times> 'VALUE WF_XREL_BINDING" where
"BindRX b = (MkXRelB (b \<oplus>\<^sub>b bc on DASHED \<union> NON_REL_VAR), MkXRelB ((RenameB SS b) \<oplus>\<^sub>b bc on DASHED \<union> NON_REL_VAR))"

lemma BindRX_left_XREL [simp]:"(b \<oplus>\<^sub>b bc on DASHED \<union> NON_REL_VAR) \<in> WF_XREL_BINDING"
  by (auto simp add:WF_XREL_BINDING_def)

lemma BindRX_right_XREL [simp]:"((RenameB SS b) \<oplus>\<^sub>b bc on DASHED \<union> NON_REL_VAR) \<in> WF_XREL_BINDING"
  by (auto simp add:WF_XREL_BINDING_def)

theorem BindRX_override :
"\<lbrakk>(rb1, rb3) = BindRX b1;
 (rb3, rb2) = BindRX b2\<rbrakk> \<Longrightarrow>
 (rb1, rb2) = BindRX (b1 \<oplus>\<^sub>b b2 on DASHED \<union> NON_REL_VAR)"
apply (simp add: BindRX_def)
apply (auto elim!:Rep_WF_BINDING_elim DestXRelB_elim intro!:Rep_WF_BINDING_intro DestXRelB_intro)
apply (simp add: override_on_eq)
apply (clarify)
apply (drule_tac x = "x" in spec)
apply (auto simp add: urename)
done

lemma BindRX_override_NON_REL_VAR: 
  "BindRX (b1 \<oplus>\<^sub>b b2 on NON_REL_VAR) = BindRX b1"
  apply (auto intro!:DestXRelB_intro simp add:BindRX_def)
apply (metis (hide_lams, no_types) binding_override_assoc binding_override_simps(4) sup.right_idem sup_commute)
  apply (metis (hide_lams, no_types) RenameB_override_distr2 SS_NON_REL_VAR_image binding_override_assoc binding_override_simps(4) sup.right_idem sup_commute)
done
  
lemma BindRX_inj:
  "BindRX b1 = BindRX b2 \<Longrightarrow> b1 \<cong> b2 on UNDASHED \<union> DASHED"
  apply (auto simp add:BindRX_def)
  apply (erule DestXRelB_elim)+
  apply (simp)
  apply ((erule Rep_WF_BINDING_elim)+, auto simp add:RenameB_rep_eq binding_equiv_def)
  apply (smt Compl_eq_Diff_UNIV Diff_iff NON_REL_VAR_def UNDASHED_not_DASHED Un_iff override_on_eq)
  apply (drule_tac x="undash x" and y="undash x" in cong) back
  apply (simp_all)
  apply (subgoal_tac "undash x \<notin> DASHED \<union> NON_REL_VAR")
  apply (simp add:urename)
  apply (metis Compl_eq_Diff_UNIV DASHED_undash_UNDASHED Diff_iff NON_REL_VAR_def UNDASHED_not_DASHED Un_iff)
done
  
definition BindPX ::
  "'VALUE WF_XREL_BINDING \<times> 'VALUE WF_XREL_BINDING \<Rightarrow>
   'VALUE WF_BINDING" where
"BindPX = (\<lambda> (rb1, rb2) . DestXRelB rb1 \<oplus>\<^sub>b (RenameB SS (DestXRelB rb2)) on DASHED)"

lemma UNDASHED_DASHED_NON_REL_VAR :
  "UNDASHED \<union> DASHED = - NON_REL_VAR"
  by (auto simp add:NON_REL_VAR_def)

lemma NON_REL_VAR_UNDASHED_DASHED :
  "NON_REL_VAR = - (UNDASHED \<union> DASHED)"
  by (auto simp add:NON_REL_VAR_def)

lemma BindPX_inverse [simp]: "BindRX (BindPX b) = b"
  apply (case_tac b)
  apply (auto simp add:BindPX_def BindRX_def)
  apply (rule)
  apply (simp)
  apply (rule)
  apply (rule ext)
  apply (simp)
  apply (case_tac "x \<in> DASHED \<union> NON_REL_VAR")
  apply (auto)
  apply (rule)
  apply (rule)
  apply (rule ext)
  apply (case_tac "x \<in> DASHED \<union> NON_REL_VAR")
  apply (auto)
  apply (smt DestXRelB_NOT_UNDASHED SS_DASHED_app SS_UNDASHED_app SS_ident_app UNDASHED_dash_DASHED comp_apply override_on_def undash_dash)
done

lemma BindRX_inverse: "BindPX (BindRX p) \<cong> p on UNDASHED \<union> DASHED"
  apply (simp add:BindPX_def BindRX_def urename closure RenameB_override_distr1 binding_override_overshadow)
  apply (auto simp add:binding_equiv_def NON_REL_VAR_def)
done

definition EvalRX ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE XRELATION" ("\<lbrakk>_\<rbrakk>RX") where
"EvalRX p = BindRX ` (destPRED p)"

definition IEvalRX ::
  "'VALUE XRELATION \<Rightarrow>
   'VALUE WF_PREDICATE" where
"IEvalRX p = mkPRED {BindPX b1 \<oplus>\<^sub>b b2 on NON_REL_VAR | b1 b2. b1 \<in> p }"


lemma EvalRX_intro:
  "\<lbrakk>p1 \<in> WF_RELATION; p2 \<in> WF_RELATION; \<lbrakk>p1\<rbrakk>RX = \<lbrakk>p2\<rbrakk>RX \<rbrakk> \<Longrightarrow> p1 = p2"
  apply (auto simp add:EvalRX_def)
  apply (subgoal_tac "BindRX x \<in> BindRX ` destPRED p2")
  apply (auto)
  apply (drule_tac "BindRX_inj")
  apply (auto simp add: WF_RELATION_def UNREST_def)
  apply (drule_tac x="xa" in bspec) back
  apply (simp_all)
  apply (drule_tac x="x" in spec)
  apply (drule binding_override_equiv)
  apply (metis NON_REL_VAR_def binding_override_minus)
  apply (subgoal_tac "BindRX x \<in> BindRX ` destPRED p1")
  apply (safe)
  apply (drule_tac "BindRX_inj")
  apply (auto simp add: WF_RELATION_def UNREST_def)
  apply (drule_tac x="xa" in bspec)
  apply (simp_all)
  apply (drule_tac x="x" in spec)
  apply (drule binding_override_equiv)
  apply (metis NON_REL_VAR_def binding_override_minus)
done

lemma EvalRX_inverse [simp]:
  "p \<in> WF_RELATION \<Longrightarrow> IEvalRX (EvalRX p) = p"
  apply (auto simp add: EvalRX_def IEvalRX_def WF_RELATION_def UNREST_def)
  apply (drule_tac x="xa" in bspec, simp)
  apply (drule_tac x="b2" in spec)
  apply (metis binding_equiv_override BindRX_inverse NON_REL_VAR_UNDASHED_DASHED)
  apply (rule_tac x="BindRX x" in exI)
  apply (simp)
  apply (rule_tac x="x" in exI)
  apply (rule trans) defer
  apply (unfold NON_REL_VAR_UNDASHED_DASHED)
  apply (rule binding_equiv_override[OF BindRX_inverse, THEN sym])
  apply (simp)
done

lemma EvalRX_simp [evalrx]: "\<lbrakk>p1 \<in> WF_RELATION; p2 \<in> WF_RELATION \<rbrakk> \<Longrightarrow> p1 = p2 \<longleftrightarrow> \<lbrakk>p1\<rbrakk>RX = \<lbrakk>p2\<rbrakk>RX"
  by (rule, simp, rule EvalRX_intro, simp_all)

lemma EvalRX_TrueP [evalrx]: "\<lbrakk>true\<rbrakk>RX = UNIV"
  apply (auto simp add:EvalRX_def image_def TrueP.rep_eq)
  apply (metis BindPX_inverse)
done

lemma EvalRX_FalseP [evalrx]: "\<lbrakk>false\<rbrakk>RX = {}"
  by (auto simp add:EvalRX_def image_def FalseP.rep_eq)

lemma EvalRX_AndP [evalrx]: 
  "\<lbrakk>p \<in> WF_RELATION; q \<in> WF_RELATION\<rbrakk> \<Longrightarrow> \<lbrakk>p \<and>p q\<rbrakk>RX = \<lbrakk>p\<rbrakk>RX \<inter> \<lbrakk>q\<rbrakk>RX"
  apply (auto simp add:EvalRX_def AndP.rep_eq image_def WF_RELATION_def UNREST_def)
  apply (drule BindRX_inj)
  apply (metis Int_iff UNDASHED_DASHED_NON_REL_VAR binding_override_equiv binding_override_minus binding_override_simps(2) binding_override_simps(3))
done

lemma EvalRX_OrP [evalrx]: 
  "\<lbrakk>p \<or>p q\<rbrakk>RX = \<lbrakk>p\<rbrakk>RX \<union> \<lbrakk>q\<rbrakk>RX"
  by (auto simp add:EvalRX_def OrP.rep_eq image_def WF_RELATION_def UNREST_def)

lemma EvalRX_NotP [evalrx]:
  "p \<in> WF_RELATION \<Longrightarrow> \<lbrakk>\<not>p p\<rbrakk>RX = - \<lbrakk>p\<rbrakk>RX"
  apply (auto simp add:EvalRX_def NotP.rep_eq image_def BindRX_def WF_RELATION_def UNREST_def)
  apply (metis (hide_lams, no_types) BindRX_def BindRX_inverse UNDASHED_DASHED_NON_REL_VAR binding_equiv_override binding_override_minus binding_override_simps(2))
  apply (metis BindPX_inverse BindRX_def Compl_iff)
done

lemma EvalRX_SkipR [evalrx]: "\<lbrakk>II\<rbrakk>RX = Id"
  apply (auto intro!:DestXRelB_intro Rep_WF_BINDING_intro simp add:EvalRX_def SkipR.rep_eq BindRX_def RenameB_rep_eq)
  apply (rule)
  apply (case_tac "x \<in> DASHED \<union> NON_REL_VAR")
  apply (force)
  apply (subgoal_tac "x \<in> UNDASHED")
  apply (simp add:urename)
  apply (metis Compl_iff NON_REL_VAR_def Un_iff)
  apply (simp add:image_Collect)
  apply (rule_tac x="BindPX (xa, xa)" in exI)
  apply (simp)
  apply (simp add:BindPX_def RenameB_rep_eq urename)
done

lemma EvalRX_SkipRA [evalrx]: 
  "\<lbrakk> vs \<subseteq> UNDASHED \<union> DASHED; HOMOGENEOUS vs \<rbrakk> \<Longrightarrow>
     \<lbrakk>II vs\<rbrakk>RX = {(b1,b2) | b1 b2. \<forall> x \<in> vs. \<langle>\<langle>b1\<rangle>\<^sub>x\<rangle>\<^sub>b x = \<langle>\<langle>b2\<rangle>\<^sub>x\<rangle>\<^sub>b x}"
  apply (auto)
  apply (auto simp add:EvalRX_def SkipRA_rep_eq_alt image_Collect BindRX_def RenameB_rep_eq)[1]
  apply (smt SS_UNDASHED_app Un_iff comp_apply in_member in_mono override_on_def)
  apply (simp add:EvalRX_def SkipRA_rep_eq_alt image_Collect)
  apply (rule_tac x="BindPX (xa, y)" in exI)
  apply (auto)
  apply (simp add:BindPX_def RenameB_rep_eq)
  apply (subgoal_tac "v \<in> UNDASHED")
  apply (simp add:urename in_vars_def)
  apply (simp add:in_vars_def)
done

theorem BindRX_COMPOSABLE_BINDINGS :
"\<lbrakk>(rb1, rb3) = BindRX b1;
 (rb3, rb2) = BindRX b2;
 b1 \<cong> b2 on NON_REL_VAR\<rbrakk> \<Longrightarrow>
 (b1, b2) \<in> COMPOSABLE_BINDINGS"
apply (simp add: BindRX_def)
apply (simp add: COMPOSABLE_BINDINGS_def)
apply (auto)
apply (erule DestXRelB_elim)+
apply (erule Rep_WF_BINDING_elim)+
apply (simp add: override_on_eq RenameB_def)
-- {* Subgoal 1 *}
apply (drule_tac x = "v" in spec)
apply (simp add:urename NON_REL_VAR_def)
-- {* Subgoal 2 *}
done

lemma EvalRX_SemiR [evalrx]: 
  "\<lbrakk>P \<in> WF_RELATION; Q \<in> WF_RELATION\<rbrakk> \<Longrightarrow> \<lbrakk>P ; Q\<rbrakk>RX = \<lbrakk>P\<rbrakk>RX O \<lbrakk>Q\<rbrakk>RX"
apply (simp add: EvalRX_def)
apply (simp add: SemiR_def)
apply (simp add: set_eq_iff)
apply (simp add: relcomp_unfold image_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rename_tac x rb1 rb2 xa b1 b2)
apply (rule_tac x = "MkXRelB ((RenameB SS b1) \<oplus>\<^sub>b bc on DASHED \<union> NON_REL_VAR)" in exI)
apply (rule conjI)
-- {* Subgoal 1.1 *}
apply (rule_tac x = "b1" in bexI)
apply (simp add: BindRX_def)
apply (metis binding_override_simps(1) binding_override_simps(3))
apply (simp)
-- {* Subgoal 1.2 *}
apply (rule_tac x = "b2" in bexI)
apply (simp add: BindRX_def)
apply (metis RenameB_SS_COMPOSABLE_BINDINGS_1 RenameB_SS_COMPOSABLE_BINDINGS_2 binding_override_simps(1))
-- {* Subgoal 2 *}
apply (simp)
apply (rename_tac x rb1 rb2 rb3 b1 b2)
apply (rule_tac x = "b1 \<oplus>\<^sub>b b2 on DASHED \<union> NON_REL_VAR" in exI)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (rule_tac x = "b1 \<oplus>\<^sub>b b2 on NON_REL_VAR" in exI)
apply (rule_tac x = "b2" in exI)
apply (auto)
apply (metis Un_commute)
apply (simp add:WF_RELATION_def UNREST_def)
apply (rule_tac ?rb1.0="rb1" and ?rb2.0="rb2" and ?rb3.0="rb3" in BindRX_COMPOSABLE_BINDINGS)
apply (simp_all)
apply (simp add:BindRX_override_NON_REL_VAR)
apply (metis BindRX_override)
done

lemma EvalRX_ConvR [evalrx]:
"\<lbrakk>p\<^sup>\<smile>\<rbrakk>RX = \<lbrakk>p\<rbrakk>RX\<inverse>"
  by (auto simp add: EvalRX_def ConvR_def RenameP.rep_eq BindRX_def urename closure image_def)

lemma Rep_WF_EXPRESSION_compat [typing]: 
  "v \<rhd>\<^sub>e x \<Longrightarrow> \<langle>v\<rangle>\<^sub>e b \<rhd> x"
  by (metis evar_compat_def)

theorem EvalRX_AssignR [evalrx] :
"\<lbrakk> x \<in> UNDASHED; e \<rhd>\<^sub>e x; UNREST_EXPR (DASHED \<union> NON_REL_VAR) e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>x :=p e\<rbrakk>RX = {(b, b(x:=\<^sub>x(\<lbrakk>e\<rbrakk>\<epsilon> \<langle>b\<rangle>\<^sub>x))) | b. True}"
  apply (simp add:EvalRX_def AssignsR.rep_eq IdA.rep_eq VarE.rep_eq AssignF_upd_rep_eq image_Collect)
  apply (simp add: set_eq_iff)
  apply (safe)
  apply (simp add: BindRX_def)
  apply (rule)
  apply (simp)
  apply (rule)
  apply (rule)
  apply (case_tac "xa \<in> DASHED \<union> NON_REL_VAR")
  apply (simp)
  apply (subgoal_tac "xa \<noteq> x")
  apply (simp)
  apply (safe)
  apply (simp add:var_contra)
  apply (simp add:var_contra NON_REL_VAR_def)
  apply (case_tac "xa \<in> UNDASHED")
  apply (simp)
  apply (case_tac "xa = x")
  apply (simp_all add:urename RenameB_rep_eq EvalE_def unrest)
  apply (simp add:NON_REL_VAR_def var_contra)
  apply (rule_tac x="BindPX (b, b(x :=\<^sub>x \<langle>e\<rangle>\<^sub>e \<langle>b\<rangle>\<^sub>x))" in exI)
  apply (auto)
  apply (auto simp add:BindPX_def RenameB_rep_eq urename typing defined)
  apply (metis (hide_lams, no_types) EvalE_UNREST_override EvalE_compat EvalE_def UNDASHED_dash_DASHED binding_override_assoc binding_override_simps(2) binding_override_upd evar_comp_dash)
done

theorem EvalRX_AssignR_alt [evalrx] :
"\<lbrakk> x \<in> UNDASHED; e \<rhd>\<^sub>e x; UNREST_EXPR (DASHED \<union> NON_REL_VAR) e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>x :=p e\<rbrakk>RX = {(b1, b2). \<forall> v \<in> UNDASHED. if (v = x) then (\<langle>\<langle>b2\<rangle>\<^sub>x\<rangle>\<^sub>b v = \<lbrakk>e\<rbrakk>\<epsilon> \<langle>b1\<rangle>\<^sub>x) 
                                                      else \<langle>\<langle>b2\<rangle>\<^sub>x\<rangle>\<^sub>b v = \<langle>\<langle>b1\<rangle>\<^sub>x\<rangle>\<^sub>b v}"
  apply (simp add:evalrx typing)
  apply (safe)
  apply (simp_all add:typing)
  apply (rule, rule, rule)
  apply (case_tac "xb \<in> UNDASHED")
  apply (auto)
done

lemma EvalRX_ExprP_UNDASHED [evalrx]:
  "UNREST_EXPR (DASHED \<union> NON_REL_VAR) e \<Longrightarrow> \<lbrakk>ExprP e\<rbrakk>RX = {(b1, b2) | b1 b2. DestBool (\<lbrakk>e\<rbrakk>\<epsilon>\<langle>b1\<rangle>\<^sub>x) }"
  apply (auto simp add:EvalRX_def ExprP_def LiftP_def BindRX_def EvalE_def image_def)
  apply (rule_tac x="\<langle>b1\<rangle>\<^sub>x \<oplus>\<^sub>b RenameB SS \<langle>b2\<rangle>\<^sub>x on DASHED" in exI)
  apply (auto)
  apply (metis (mono_tags) UNREST_EXPR_def binding_override_simps(6) inf_sup_absorb)
  apply (rule, simp)
  apply (metis DestXRelB_binding_equiv binding_override_equiv binding_override_simps(1) binding_override_simps(3))
  apply (rule, simp add:RenameB_override_distr1 urename closure)
  apply (rule, rule)
  apply (auto)
  apply (case_tac "x \<in> DASHED \<union> NON_REL_VAR")
  apply (auto)
done

lemma EvalRX_ExprP_DASHED [evalrx]:
  "UNREST_EXPR (UNDASHED \<union> NON_REL_VAR) e \<Longrightarrow> \<lbrakk>ExprP e\<rbrakk>RX = {(b1, b2) | b1 b2. DestBool (\<lbrakk>e\<rbrakk>\<epsilon>(RenameB SS \<langle>b2\<rangle>\<^sub>x)) }"
  apply (auto simp add:EvalRX_def ExprP_def LiftP_def BindRX_def EvalE_def closure RenameB_override_distr1 urename)
  apply (auto simp add:image_def BindRX_def)
  apply (rule_tac x="\<langle>xa\<rangle>\<^sub>x \<oplus>\<^sub>b RenameB SS \<langle>y\<rangle>\<^sub>x on DASHED" in exI)
  apply (auto)
  apply (smt RenameB_def SS_inv UNDASHED_DASHED_NON_REL_VAR UNREST_EXPR_def Un_assoc Un_commute binding_override_assoc binding_override_minus binding_override_simps(2))
  apply (rule, simp)
  apply (metis DestXRelB_binding_equiv binding_override_equiv binding_override_simps(1) binding_override_simps(3))
  apply (rule, simp add:RenameB_override_distr1 urename closure)
  apply (rule, rule)
  apply (auto)
  apply (case_tac "x \<in> DASHED \<union> NON_REL_VAR")
  apply (auto)
done

lemma EvalRX_VarP_UNDASHED [evalrx]:
  "\<lbrakk> vtype x = BoolType; aux x; x \<in> UNDASHED \<rbrakk> \<Longrightarrow> \<lbrakk>VarP x\<rbrakk>RX = {(b1, b2) | b1 b2. \<langle>\<langle>b1\<rangle>\<^sub>x\<rangle>\<^sub>b x = TrueV}"
  apply (rule trans)
  apply (rule EvalRX_ExprP_UNDASHED)
  apply (rule unrest)
  apply (auto intro: unrest)[1]
  apply (simp add:evale)
  apply (rule)
  apply (auto)
  apply (metis BOOL_SORT_class.Inverse FalseV_def MkBool_cases Rep_WF_BINDING TrueV_def WF_BINDING_app_type WF_BINDING_aux_defined)
done

lemma EvalRX_VarP_DASHED [evalrx]:
  "\<lbrakk> vtype x = BoolType; aux x; x \<in> DASHED \<rbrakk> \<Longrightarrow> \<lbrakk>VarP x\<rbrakk>RX = {(b1, b2) | b1 b2. \<langle>\<langle>b2\<rangle>\<^sub>x\<rangle>\<^sub>b (undash x) = TrueV}"
  apply (rule trans)
  apply (rule EvalRX_ExprP_DASHED)
  apply (auto intro: unrest)[1]
  apply (simp add:evale)
  apply (rule)
  apply (auto simp add:urename)
  apply (metis BOOL_SORT_class.Inverse FalseV_def MkBool_cases Rep_WF_BINDING TrueV_def WF_BINDING_app_type aux_defined aux_undash vtype_undash)
done

theorem EvalR_EqualP_UNDASHED [evalrx]:
  "\<lbrakk> UNREST_EXPR (DASHED \<union> NON_REL_VAR) e; UNREST_EXPR (DASHED \<union> NON_REL_VAR) f \<rbrakk> \<Longrightarrow>
     \<lbrakk>EqualP e f\<rbrakk>RX = {(b1, b2) |b1 b2. (\<lbrakk>e\<rbrakk>\<epsilon> \<langle>b1\<rangle>\<^sub>x = \<lbrakk>f\<rbrakk>\<epsilon> \<langle>b1\<rangle>\<^sub>x)}"
  apply (auto simp add:EvalRX_def EqualP_def EvalE_def)
  apply (metis BindRX_def BindRX_left_XREL MkXRelB_inverse UNREST_EXPR_def)
  apply (simp add:image_Collect)
  apply (rule_tac x="BindPX (b1, b2)" in exI)
  apply (simp)
  apply (auto simp add: BindPX_def UNREST_EXPR_def)
  apply (metis Un_left_absorb binding_override_simps(1))
done

theorem EvalR_EqualP_DASHED [evalrx]:
  "\<lbrakk> UNREST_EXPR (DASHED \<union> NON_REL_VAR) e; UNREST_EXPR (DASHED \<union> NON_REL_VAR) f \<rbrakk> \<Longrightarrow>
     \<lbrakk>`e\<acute> = f\<acute>`\<rbrakk>RX = {(b1, b2) |b1 b2. (\<lbrakk>e\<rbrakk>\<epsilon> \<langle>b2\<rangle>\<^sub>x = \<lbrakk>f\<rbrakk>\<epsilon> \<langle>b2\<rangle>\<^sub>x)}"
  apply (auto simp add:EvalRX_def EqualP_def EvalE_def)
  apply (auto simp add:BindRX_def)
  apply (metis (hide_lams, no_types) RenameE.rep_eq SS_inv comp_apply)
  apply (simp add:image_Collect)
  apply (rule_tac x="BindPX (xa, y)" in exI)
  apply (simp)
  apply (simp add: BindPX_def UNREST_EXPR_def RenameE.rep_eq RenameB_override_distr1 urename RenameB_compose closure)
  apply (metis UNDASHED_DASHED_inter(15) binding_override_assoc binding_override_minus binding_override_simps(1) binding_override_simps(2))
done

lemma binding_override_overshadow2 [simp]:
  "(b1 \<oplus>\<^sub>b b2 on - vs) \<oplus>\<^sub>b b3 on vs = b2 \<oplus>\<^sub>b b3 on vs"
  by (force simp add:override_on_def)

lemma binding_override_overshadow3 [simp]:
  "b1 \<oplus>\<^sub>b (b2 \<oplus>\<^sub>b b3 on - vs) on vs = b1 \<oplus>\<^sub>b b2 on vs"
  by (force simp add:override_on_def)

lemma binding_override_commute:
  "vs1 \<inter> vs2 = {} \<Longrightarrow> (b1 \<oplus>\<^sub>b b2 on vs1) \<oplus>\<^sub>b b3 on vs2 = (b1 \<oplus>\<^sub>b b3 on vs2) \<oplus>\<^sub>b b2 on vs1"
  by (force simp add:override_on_def)

lemma binding_upd_override2 [simp]:
  "\<lbrakk> x \<notin> vs; v \<rhd> x \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v) \<oplus>\<^sub>b b on vs = b(x :=\<^sub>b v)"
  by (force simp add:override_on_def)

lemma union_minus: "(x \<union> y) - z = (x - z) \<union> (y - z)"
  by (auto)

theorem EvalRX_SubstP_UNDASHED [evalrx] :
"\<lbrakk> p \<in> WF_RELATION; x \<in> UNDASHED; e \<rhd>\<^sub>e x; UNREST_EXPR (DASHED \<union> NON_REL_VAR) e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e|x]\<rbrakk>RX = {(b1, b2) | b1 b2. (b1(x :=\<^sub>x \<lbrakk>e\<rbrakk>\<epsilon>\<langle>b1\<rangle>\<^sub>x), b2) \<in> \<lbrakk>p\<rbrakk>RX}"
  apply (simp add: EvalRX_def EvalE_def SubstP_def image_Collect union_minus)
  apply (auto simp add:image_def)
  apply (rule_tac x="BindPX (a(x :=\<^sub>x \<langle>e\<rangle>\<^sub>e \<langle>a\<rangle>\<^sub>x), b)" in bexI)
  apply (simp)
  apply (auto simp add:BindPX_def BindRX_def typing defined RenameB_override_distr1 urename closure union_minus)[1]
  apply (subgoal_tac "UNDASHED \<union> NON_REL_VAR = - (DASHED :: 'a VAR set)")
  apply (simp add:binding_override_overshadow)
  apply (subgoal_tac "(ba(x :=\<^sub>b \<langle>e\<rangle>\<^sub>e ba) \<oplus>\<^sub>b bc on NON_REL_VAR - {x}) \<oplus>\<^sub>b ba on DASHED =
                      ba(x :=\<^sub>b \<langle>e\<rangle>\<^sub>e ba) \<oplus>\<^sub>b bc on NON_REL_VAR - {x}")
  apply (simp add:WF_RELATION_def UNREST_def)
  apply (metis (hide_lams, full_types) binding_override_simps(5))
  apply (subgoal_tac "(NON_REL_VAR - {x}) \<inter> DASHED = {}")
  apply (simp add:binding_override_commute typing)
  apply (auto)
  apply (rule_tac x="BindPX (xa, y)" in exI, simp)
  apply (auto simp add:BindPX_def BindRX_def urename closure typing defined RenameB_compose RenameB_override_distr1 unrest)
  apply (subgoal_tac "UNREST_EXPR DASHED e")
  apply (simp)
  apply (subgoal_tac "UNDASHED \<union> NON_REL_VAR = - (DASHED :: 'a VAR set)")
  apply (simp)
  apply (erule DestXRelB_elim) 
  apply (simp add:typing defined)
  apply (metis EvalP_UNREST_override EvalP_def UNREST_NON_REL_VAR_WF_RELATION binding_override_assoc binding_override_minus binding_override_overshadow binding_override_simps(2))
  apply (auto intro:UNREST_EXPR_subset)
done

theorem EvalRX_SubstP_DASHED [evalrx] :
"\<lbrakk> p \<in> WF_RELATION; x \<in> UNDASHED; e \<rhd>\<^sub>e x; UNREST_EXPR (DASHED \<union> NON_REL_VAR) e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>`p[e\<acute>/x\<acute>]`\<rbrakk>RX = {(b1, b2) | b1 b2. (b1, b2(x :=\<^sub>x \<lbrakk>e\<rbrakk>\<epsilon>\<langle>b2\<rangle>\<^sub>x)) \<in> \<lbrakk>p\<rbrakk>RX}"
  apply (simp add: EvalRX_def EvalE_def SubstP_def image_Collect)
  apply (auto simp add:image_def)
  apply (rule_tac x="BindPX (a, b(x :=\<^sub>x \<langle>e\<rangle>\<^sub>e \<langle>b\<rangle>\<^sub>x))" in bexI)
  apply (simp)
  apply (auto simp add:BindPX_def BindRX_def typing defined RenameB_override_distr1 urename closure)[1]
  apply (simp add:binding_override_overshadow)
  apply (subgoal_tac "DASHED \<union> NON_REL_VAR = - (UNDASHED :: 'a VAR set)")
  apply (simp add:binding_override_overshadow)
sorry

lemma EvalRX_Tautology [evalrx]:
  "p \<in> WF_RELATION \<Longrightarrow> taut p \<longleftrightarrow> \<lbrakk>p\<rbrakk>RX = UNIV"
  apply (utp_pred_tac)
  apply (simp add:EvalP_def)
  apply (rule iffI)
  apply (metis EvalRX_TrueP TrueP_def UNIV_eq_I destPRED_inverse)
  apply (metis EvalRX_TrueP EvalRX_intro TrueP.rep_eq TrueP_rel_closure UNIV_I)
done
  
declare ImpliesP_def [evalrx]
declare IffP_def [evalrx]
declare CondR_def [evalrx]

subsection {* Proof Tactics *}

ML {*
  fun utp_xrel_simpset ctxt =
    (simpset_of ctxt)
      addsimps (evalrx.get ctxt)
      addsimps (typing.get ctxt)
      addsimps (defined.get ctxt)
      addsimps (closure.get ctxt);
*}

ML {*
  fun utp_xrel_auto_simpset ctxt =
    (simpset_of ctxt)
      addsimps @{thms "relcomp_unfold"}
*}

ML {*
  fun utp_xrel_tac thms ctxt i =
    CHANGED (asm_full_simp_tac (utp_xrel_simpset ctxt) i)
*}

ML {*
  fun utp_rel_deep_auto_tac thms ctxt i =
    TRY (asm_full_simp_tac (utp_xrel_simpset ctxt) i) THEN
    TRY (asm_full_simp_tac (utp_xrel_auto_simpset ctxt) i) THEN
    (auto_tac ctxt)
*}

method_setup utp_xrel_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_xrel_tac thms ctxt))
*} "proof tactic for deep relations"

method_setup utp_xrel_auto_tac = {*
  Attrib.thms >>
  (fn thms => fn ctxt =>
    SIMPLE_METHOD' (utp_rel_deep_auto_tac thms ctxt))
*} "proof tactic for relations with auto"


(* Tests *)

lemma 
  "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; c \<in> WF_RELATION; (c ; true = c) \<rbrakk> 
    \<Longrightarrow> p ; (c \<and>p q) = (p \<and>p c\<^sup>\<smile>) ; q"
  by (utp_xrel_auto_tac)

lemma 
  "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; c \<in> WF_RELATION; (true ; c = c) \<rbrakk> \<Longrightarrow>
  (p \<and>p c) ; q = p ; (c\<^sup>\<smile> \<and>p q)"
  by (utp_xrel_auto_tac)

(* De Morgan *)


lemma
  "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> (p\<^sup>\<smile> ; \<not>p (p ; q)) \<or>p \<not>p q = \<not>p q"
  by (utp_xrel_auto_tac)


lemma "\<lbrakk> x \<in> UNDASHED; x \<in> xs; xs \<subseteq> UNDASHED \<union> DASHED; HOMOGENEOUS xs; v \<rhd>\<^sub>e x; UNREST_EXPR (DASHED \<union> NON_REL_VAR) v \<rbrakk> \<Longrightarrow> x :=p v ; II xs = x :=p v"
  oops

end


