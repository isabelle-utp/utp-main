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

lemma WF_REL_BINDING_bc_DASHED:
  "b \<in> WF_REL_BINDING \<Longrightarrow> b \<cong> bc on DASHED"
  by (auto simp add:WF_REL_BINDING_def)

lemma WF_REL_BINDING_override_closure [closure]:
  "b \<oplus>\<^sub>b bc on DASHED \<in> WF_REL_BINDING"
  by (auto simp add:WF_REL_BINDING_def)

lemma WF_REL_BINDING_binding_upd [closure]:
  "\<lbrakk> x \<in> UNDASHED; b \<in> WF_REL_BINDING \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v) \<in> WF_REL_BINDING"
  by (auto simp add:WF_REL_BINDING_def)

lemma WF_REL_BINDING_bc_DASHED_eq:
  "b \<in> WF_REL_BINDING \<longleftrightarrow> b \<cong> bc on DASHED"
  by (metis WF_REL_BINDING_bc_DASHED WF_REL_BINDING_override_closure binding_override_equiv)

lemma WF_REL_BINDING_binding_upd_remove:
  "\<lbrakk> b(x :=\<^sub>b v) \<in> WF_REL_BINDING; x \<in> UNDASHED \<rbrakk> \<Longrightarrow> b \<in> WF_REL_BINDING"
  by (simp add:WF_REL_BINDING_bc_DASHED_eq)

lemma WF_REL_BINDING_override_UNDASHED [closure]:
  "b \<in> WF_REL_BINDING \<Longrightarrow> b \<oplus>\<^sub>b b' on D\<^sub>0 \<in> WF_REL_BINDING"
  apply (auto simp add:WF_REL_BINDING_def)
  apply (metis (hide_lams, no_types) UNDASHED_DASHED_minus(2) binding_equiv_override_subsume binding_override_equiv binding_override_equiv1 binding_override_simps(5))
done

lemma WF_REL_BINDING_override_DASHED [closure]:
  "b' \<in> WF_REL_BINDING \<Longrightarrow> b \<oplus>\<^sub>b b' on D\<^sub>1 \<in> WF_REL_BINDING"
  by (auto simp add:WF_REL_BINDING_def)

lemma WF_REL_BINDING_override_DASHED_NON_REL_VAR [closure]:
  "b' \<in> WF_REL_BINDING \<Longrightarrow> b \<oplus>\<^sub>b b' on NON_REL_VAR \<union> D\<^sub>1 \<in> WF_REL_BINDING"
  apply (auto simp add:WF_REL_BINDING_def)
  apply (metis binding_override_assoc)
done

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

lemma BindR_image: 
  "BindR ` {x. P x}  = {BindR x| x. P x}"
  by (auto)

lemma BindR_inverse:
  "\<lbrakk> b1 \<in> WF_REL_BINDING; b2 \<in> WF_REL_BINDING; b1 \<cong> b2 on NON_REL_VAR \<rbrakk>
           \<Longrightarrow> BindR (BindP (b1, b2)) = (b1, b2)"
  apply (auto simp add:BindR_def BindP_def RenameB_override_distr1 urename closure)
  apply (metis WF_REL_BINDING_bc_DASHED binding_override_equiv)
  apply (metis (hide_lams, no_types) NON_REL_VAR_def SS_VAR_RENAME_ON WF_REL_BINDING_bc_DASHED_eq binding_equiv_override binding_override_RENAME_ON_overshadow binding_override_minus binding_override_simps(1) binding_override_simps(2))
done

lemma BindR_Collect_form:
  "{BindR b | b. P b} = {(b1, b2). P (BindP (b1, b2)) 
                                 \<and> b1 \<in> WF_REL_BINDING  
                                 \<and> b2 \<in> WF_REL_BINDING 
                                 \<and> b1 \<cong> b2 on NON_REL_VAR}"
  apply (auto simp add: BindP_inverse)
  apply (metis (full_types) EvalR_def UNIV_I WF_REL_BINDING_member1 imageI mkPRED_inverse)
  apply (metis (full_types) EvalR_def UNIV_I WF_REL_BINDING_member2 imageI mkPRED_inverse)
  apply (metis BindR_left_eq_NON_REL_VAR BindR_right_eq_NON_REL_VAR binding_equiv_comm binding_equiv_trans)
  apply (metis BindR_inverse)
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

lemma EvalP_WF_RELATION: "\<lbrakk> p \<in> WF_RELATION; \<lbrakk>p\<rbrakk>b1; b1 \<cong> b2 on REL_VAR \<rbrakk> \<Longrightarrow> \<lbrakk>p\<rbrakk>b2"
  apply (simp add:WF_RELATION_def UNREST_def EvalP_def)
  apply (drule_tac x="b1" in bspec, simp)
  apply (drule_tac x="b2" in spec)
  apply (metis NON_REL_VAR_def binding_equiv_override binding_override_simps(2))
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
"\<lbrakk>\<not>\<^sub>p p\<rbrakk>R = \<lbrakk>true\<rbrakk>R - \<lbrakk>p\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: NotP_def TrueP_def)
apply (auto)
done

theorem EvalR_AndP [evalr] :
"\<lbrakk>p1 \<and>\<^sub>p p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R \<inter> \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: AndP_def)
apply (auto)
done

theorem EvalR_OrP [evalr] :
"\<lbrakk>p1 \<or>\<^sub>p p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R \<union> \<lbrakk>p2\<rbrakk>R"
apply (simp add: EvalR_def)
apply (simp add: OrP_def)
apply (auto)
done

lemma image_Inter: "\<lbrakk> inj_on f (\<Union>S); S \<noteq> {} \<rbrakk> \<Longrightarrow> f ` \<Inter>S = (\<Inter>x\<in>S. f ` x)"
  apply (auto simp add:image_def)
  apply (metis (full_types) InterI UnionI the_inv_into_f_eq)
done

(* We have to block out empty sets in distributive and because they end up being 
   true (UNIV), which does not correspond to the range of BindR. *)

theorem EvalR_AndDistP [evalr] :
"ps \<noteq> {} \<Longrightarrow> \<lbrakk>\<And>\<^sub>p ps\<rbrakk>R = \<Inter> {\<lbrakk>p\<rbrakk>R | p. p \<in> ps}"
  apply (auto simp add: EvalR_def AndDistP_rep_eq)
  apply (subst image_Inter)
  apply (auto)
  apply (metis (lifting, no_types) BindR_inject inj_onI)
done

theorem EvalR_OrDistP [evalr]:
"\<lbrakk>\<Or>\<^sub>p ps\<rbrakk>R = \<Union> {\<lbrakk>p\<rbrakk>R | p. p \<in> ps}"
  by (auto simp add: EvalR_def OrDistP_rep_eq)

theorem EvalR_ANDI_enum [evalr]:
  "A \<noteq> {} \<Longrightarrow> \<lbrakk>\<And>\<^sub>pi:A. P i\<rbrakk>R = (\<Inter> i\<in>A. \<lbrakk>P i\<rbrakk>R)"
  by (auto simp add:ANDI_def evalr)

theorem EvalR_ORDI_enum [evalr]:
  "\<lbrakk>\<Or>\<^sub>pi:A. P i\<rbrakk>R = (\<Union> i\<in>A. \<lbrakk>P i\<rbrakk>R)"
  by (auto simp add:ORDI_def evalr)

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
apply (metis SS_UNDASHED_app SS_ident_app)
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
 \<lbrakk>II\<^bsub>vs\<^esub>\<rbrakk>R = { BindR b | b. \<forall>v\<in>in vs. \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b (v\<acute>)}"
  by (simp add:EvalR_def SkipRA_rep_eq_alt image_Collect BindR_def)

theorem EvalR_SkipRA' :
"\<lbrakk> vs \<subseteq> UNDASHED \<union> DASHED; HOMOGENEOUS vs \<rbrakk> \<Longrightarrow>
 \<lbrakk>II\<^bsub>vs\<^esub>\<rbrakk>R = { (b \<oplus>\<^sub>b bc on DASHED, b' \<oplus>\<^sub>b bc on DASHED) 
           | b b'. b \<cong> b' on in vs \<and> b \<cong> b' on NON_REL_VAR}"
  apply (auto simp add:EvalR_SkipRA BindR_def)
  apply (rule_tac x="b" in exI)
  apply (simp)
  apply (rule_tac x="SS\<bullet>b" in exI)
  apply (auto)
  apply (auto simp add:binding_equiv_def)[1]
  apply (metis SS_UNDASHED_app in_UNDASHED in_mono)
  apply (auto simp add:binding_equiv_def)[1]
  apply (metis SS_NON_REL_VAR)
  apply (rule_tac x="b \<oplus>\<^sub>b SS\<bullet>b' on DASHED" in exI)
  apply (simp add: RenameB_override_distr1 urename closure)
  apply (auto)
  apply (rule binding_override_eq_intro)
  apply (subgoal_tac "(- DASHED :: 'a VAR set) = UNDASHED \<union> NON_REL_VAR")
  apply (simp)
  apply (rule binding_equiv_union_intro)
  apply (metis binding_equiv_comm binding_override_equiv1)
  apply (simp add: binding_equiv_UNDASHED_overshadow)
  apply (metis NON_REL_VAR_def RenameB_equiv_VAR_RENAME_ON_2 SS_VAR_RENAME_ON binding_equiv_comm binding_equiv_trans double_compl)
  apply (auto)[1]
  apply (simp)
  apply (auto simp add:override_on_def)
  apply (metis SS_DASHED_app binding_equiv_def undash_dash)
  apply (metis UNDASHED_dash_DASHED in_UNDASHED in_mono)
done

lemma EvalR_SkipRA'' [evalr] :
"\<lbrakk> vs \<subseteq> UNDASHED \<union> DASHED; HOMOGENEOUS vs \<rbrakk> \<Longrightarrow>
 \<lbrakk>II\<^bsub>vs\<^esub>\<rbrakk>R = { (b, b') 
           . b \<cong> b' on in vs \<and> b \<cong> b' on NON_REL_VAR
           \<and> b \<in> WF_REL_BINDING \<and> b' \<in> WF_REL_BINDING}"
  apply (auto intro: binding_override_left_eq simp add:EvalR_SkipRA' closure)
  apply (metis WF_REL_BINDING_bc_DASHED binding_override_equiv)
done

lemma Collect_eq_pair_intro:
  "\<lbrakk> \<And> x y. P x y \<longleftrightarrow> Q x y \<rbrakk> \<Longrightarrow> {(x, y). P x y} = {(x, y) . Q x y}"
  by simp

lemma Collect_conj_pair_eq: 
  "{(x, y). P x y} \<inter> {(x, y). Q x y} = {(x, y). P x y & Q x y}"
  by auto

lemma EvalP_AssignR1 [eval]:
  "\<lbrakk>x :=\<^sub>R e\<rbrakk>b = (\<forall> v \<in> UNDASHED. if (v = x) then \<langle>b\<rangle>\<^sub>b (v\<acute>) = (vcoerce (\<lbrakk>e\<rbrakk>\<^sub>eb) x)
                                            else \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>b\<rangle>\<^sub>b v)"
  by (simp add:EvalP_def EvalE_def AssignsR.rep_eq IdA.rep_eq VarE.rep_eq AssignF_upd_rep_eq AssignF_upd.rep_eq ecoerce_rep_eq)

(*
lemma EvalP_AssignR1 [eval]:
  "e \<rhd>\<^sub>e x \<Longrightarrow>
   \<lbrakk>x :=\<^sub>R e\<rbrakk>b = (\<forall> v \<in> UNDASHED. if (v = x) then \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<lbrakk>e\<rbrakk>\<^sub>eb 
                                            else \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>b\<rangle>\<^sub>b v)"
  apply (simp add:eval typing)
  by (simp add:EvalP_def EvalE_def AssignsR.rep_eq IdA.rep_eq VarE.rep_eq AssignF_upd_rep_eq AssignF_upd.rep_eq)
*)

lemma EvalP_AssignR2 [eval]:
  "\<lbrakk> e \<rhd>\<^sub>e x; f \<rhd>\<^sub>e y \<rbrakk> \<Longrightarrow>
   \<lbrakk>x,y :=\<^sub>R e,f\<rbrakk>b = (\<forall> v \<in> UNDASHED. if (v = y) 
                                     then \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<lbrakk>f\<rbrakk>\<^sub>eb 
                                     else if (v = x) 
                                          then \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<lbrakk>e\<rbrakk>\<^sub>eb 
                                          else \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>b\<rangle>\<^sub>b v)"
  by (simp add:EvalP_def EvalE_def AssignsR.rep_eq IdA.rep_eq VarE.rep_eq AssignF_upd_rep_eq)

lemma EvalP_AssignsR [eval]:
  "\<lbrakk>AssignsR f\<rbrakk>b = (\<forall> v \<in> UNDASHED. \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>\<langle>f\<rangle>\<^sub>a v\<rangle>\<^sub>e b)"
  by (simp add:EvalP_def AssignsR.rep_eq)

lemma EvalR_AssignsR: 
  "\<lbrakk>AssignsR f\<rbrakk>R = {(b1, b2). (\<forall> x \<in> UNDASHED. \<langle>b2\<rangle>\<^sub>b x = \<lbrakk>\<langle>f\<rangle>\<^sub>a x\<rbrakk>\<^sub>e (BindP (b1, b2)))
                            \<and> b1 \<in> WF_REL_BINDING
                            \<and> b2 \<in> WF_REL_BINDING
                            \<and> b1 \<cong> b2 on NON_REL_VAR}"
  by (auto simp add:EvalR_def AssignsR_def BindR_image BindR_Collect_form BindP_def EvalE_def urename)

lemma AssignF_upd_apply [simp]:
  "v \<rhd>\<^sub>e x \<Longrightarrow> \<langle>f(x :=\<^sub>a v)\<rangle>\<^sub>a x = v"
  apply (auto simp add:AssignF_upd_def)
  apply (metis AssignF_upd_rep_eq Rep_AssignF_inverse fun_upd_same)
done

lemma EvalE_BindP_UNDASHED [evale]:
  "D\<^sub>1 \<sharp> e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e(BindP (b1, b2)) = \<lbrakk>e\<rbrakk>\<^sub>eb1"
  by (simp add:BindP_def evale)

lemma binding_upd_vcoerce [simp]:
  "b(x :=\<^sub>b vcoerce v x) = b(x :=\<^sub>b v)"
  by (auto simp add:binding_upd.rep_eq)

theorem EvalR_AssignR [evalr] :
"\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>x :=\<^sub>R e\<rbrakk>R = {(b, b(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>e b)) | b. b \<in> WF_REL_BINDING}"
apply (simp add: EvalR_def EvalE_def AssignsR.rep_eq IdA.rep_eq VarE.rep_eq AssignF_upd_rep_eq BindR_image)
apply (safe, simp_all add:urename closure AssignF_upd.rep_eq IdA.rep_eq)
apply (simp add:BindR_def closure urename)
apply (rule Rep_WF_BINDING_intro)
apply (rule ext)
apply (case_tac "xa = x")
apply (drule_tac x="x" in bspec, simp_all add:ecoerce_rep_eq urename binding_upd.rep_eq)
apply (case_tac "xa \<in> D\<^sub>0")
apply (drule_tac x="xa" in bspec, simp_all add:ecoerce_rep_eq urename binding_upd.rep_eq VarE.rep_eq)
apply (case_tac "xa \<in> D\<^sub>1")
apply (simp_all add:urename)
apply (rule_tac x="BindP (b, b(x :=\<^sub>b vcoerce (\<langle>e\<rangle>\<^sub>e b) x))" in exI)
apply (simp add:BindR_inverse closure)
apply (auto simp add:BindP_def urename)
done

theorem EvalR_ExprR [evalr]: 
  "\<lbrakk>ExprP e\<rbrakk>R = {BindR b |b. DestBool (\<lbrakk>e\<rbrakk>\<^sub>e b)}"
  by (simp add:ExprP_def LiftP_def EvalR_def BindR_def EvalE_def UNREST_EXPR_member[THEN sym] etype_rel_def Defined_WF_EXPRESSION_def image_Collect)

theorem EvalR_EqualP:
  "\<lbrakk>EqualP e f\<rbrakk>R = {BindR b |b. (\<lbrakk>e\<rbrakk>\<^sub>e b = \<lbrakk>f\<rbrakk>\<^sub>e b)}"
  by (auto simp add:EvalR_def EqualP_def EvalE_def)

lemma EvalR_ConvR [evalr]:
  "\<lbrakk>p\<^sup>\<smile>\<rbrakk>R = \<lbrakk>p\<rbrakk>R\<inverse>"
  apply (auto simp add: EvalR_def ConvR_def PermP.rep_eq BindR_def urename closure)
  apply (metis BindR_def image_iff)
  apply (metis (lifting) BindR_def RenameB_involution SS_VAR_RENAME_INV image_eqI)
done

theorem SubstP_rel_UNDASHED [evalr] :
"\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e/\<^sub>px]\<rbrakk>R = {(b1, b2) | b1 b2. (b1(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>eb1), b2) \<in> \<lbrakk>p\<rbrakk>R}"
apply (auto simp add: EvalR_def EvalE_def BindR_def SubstP_def image_def)
apply (rule_tac x="xa(x :=\<^sub>b \<langle>e\<rangle>\<^sub>e xa)" in bexI)
apply (auto)
apply (metis RenameB_binding_upd_1 SS_UNDASHED_app UNDASHED_dash_DASHED binding_upd_override)
apply (rule_tac x="xa \<oplus>\<^sub>b xb on DASHED" in exI)
apply (simp)
apply (subgoal_tac "\<langle>e\<rangle>\<^sub>e (xa \<oplus>\<^sub>b xb on DASHED) = \<langle>e\<rangle>\<^sub>e xa")
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
done

lemma binding_override_subsume1 [simp]: 
  "(b1 \<oplus>\<^sub>b b2 on vs2) \<oplus>\<^sub>b b3 on vs1 \<union> vs2 = b1 \<oplus>\<^sub>b b3 on vs1 \<union> vs2"
  by (metis binding_override_simps(1) binding_override_simps(3) sup_commute)

lemma binding_override_assoc':
  "b1 \<oplus>\<^sub>b (b2 \<oplus>\<^sub>b b3 on vs1) on vs2 = (b1 \<oplus>\<^sub>b b2 on vs2 - vs1) \<oplus>\<^sub>b b3 on vs1 \<inter> vs2"
  by (force simp add:binding_override_on.rep_eq override_on_def)

lemma binding_override_subsume2 [simp]: 
  "(b1 \<oplus>\<^sub>b b2 on vs1 \<union> vs2) \<oplus>\<^sub>b b3 on vs1 = (b1 \<oplus>\<^sub>b b2 on vs2) \<oplus>\<^sub>b b3 on vs1"
  by (force simp add:binding_override_on.rep_eq override_on_def)

lemma binding_upd_eq: 
  "b(x :=\<^sub>b v) = b' \<Longrightarrow> \<langle>b'\<rangle>\<^sub>b x = vcoerce v x"
  by (metis binding_upd_apply)

lemma vcoerce_dash [simp]:
  "vcoerce e x\<acute> = vcoerce e x"
  apply (auto simp add:vcoerce_def typing)
  apply (metis undash_dash var_compat_undash)
done

theorem SubstP_rel_DASHED [evalr] :
"\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[(SS\<bullet>e)/\<^sub>px\<acute>]\<rbrakk>R = {(b1, b2) | b1 b2. (b1, b2(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>eb2)) \<in> \<lbrakk>p\<rbrakk>R}"
  apply (auto simp add: EvalR_def SubstP_def BindR_image image_def)
  apply (rule_tac x="BindP (a, b(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>e b))" in bexI)
  apply (subst BindR_inverse)
  apply (simp_all add: closure)
  apply (metis BindR_def WF_REL_BINDING_override_closure prod.inject)
  apply (metis EvalR_def UNIV_I WF_REL_BINDING_binding_upd WF_REL_BINDING_member2 destPRED_cases rangeI)
  apply (metis BindR_left_eq_NON_REL_VAR BindR_right_eq_NON_REL_VAR binding_equiv_comm binding_equiv_trans)
  apply (simp add:BindP_def BindR_def RenameB_override_distr1 urename closure binding_override_assoc' EvalE_def PermE.rep_eq)
  apply (rule_tac x="BindP (xa, y)" in exI)
  apply (subst BindR_inverse)
  apply (simp_all add: closure)
  apply (metis EvalR_def WF_REL_BINDING_member1 imageI)
  apply (metis EvalR_def WF_REL_BINDING_binding_upd_remove WF_REL_BINDING_member2 image_eqI)
  apply (metis EvalR_NON_REL_VAR EvalR_def UNDASHED_not_NON_REL_VAR binding_equiv_update_subsume' imageI)
  apply (simp add:BindP_def BindR_def RenameB_override_distr1 urename closure PermE.rep_eq EvalE_def)
  apply (auto)
  apply (subgoal_tac "xb(x\<acute> :=\<^sub>b \<langle>RenameE e SS\<rangle>\<^sub>e (xb \<oplus>\<^sub>b RenameB SS y on DASHED)) \<oplus>\<^sub>b RenameB SS y on DASHED - {x\<acute>} = xb")
  apply (simp add: RenameB_override_distr1 urename closure PermE.rep_eq EvalE_def)
  apply (rule, rule, simp)
  apply (case_tac "xa \<in> UNDASHED")
  apply (simp add:typing defined)
  apply (metis UNDASHED_dash_not_UNDASHED)
  apply (case_tac "xa = x\<acute>")
  apply (simp_all add:typing defined)
  apply (subgoal_tac "\<langle>xb\<rangle>\<^sub>b x\<acute> = vcoerce (\<langle>e\<rangle>\<^sub>e y) x")
  apply (auto simp add:typing defined urename)
  apply (subgoal_tac "\<langle>RenameE e SS\<rangle>\<^sub>e (xb \<oplus>\<^sub>b RenameB SS y on DASHED) = \<langle>RenameE e SS\<rangle>\<^sub>e (RenameB SS y)")
  apply (simp_all add: RenameB_override_distr1 urename closure PermE.rep_eq EvalE_def)
  apply (rule WF_EXPRESSION_UNREST_binding_equiv[of "UNDASHED \<union> NON_REL_VAR"])
  apply (simp add:unrest UNREST_EXPR_subset urename closure)
  apply (rule UNREST_EXPR_subset)
  apply (simp)
  apply (auto)[1]
  apply (metis NON_REL_VAR_def binding_equiv_UNDASHED_overshadow binding_equiv_comm binding_equiv_union_intro binding_override_equiv1 binding_override_minus binding_override_simps(1) binding_upd_override sup.commute)
  apply (drule binding_upd_eq)
  apply (simp add:urename)
  apply (case_tac "xa \<in> D\<^sub>1 - {x\<acute>}")
  apply (simp add:urename)
  apply (erule Rep_WF_BINDING_elim)
  apply (simp)
  apply (drule_tac x="undash xa" and y="undash xa" in cong, simp)
  apply (simp add:typing defined urename)
  apply (metis dash_undash_DASHED)
  apply (simp add:RenameB_override_distr1 urename closure)
done

theorem SubstP_rel_DASHED_PrimeE [evalr] :
"\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e\<acute>/\<^sub>px\<acute>]\<rbrakk>R = {(b1, b2) | b1 b2. (b1, b2(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>eb2)) \<in> \<lbrakk>p\<rbrakk>R}"
  by (simp add:PrimeE_def evalr)

lemma SS_dash_DASHED: "x \<in> DASHED \<Longrightarrow> (SS\<bullet>x)\<acute> = x"
  by (metis SS_DASHED_app dash_undash_DASHED)

theorem SubstP_rel_DASHED' [evalr] :
"\<lbrakk> x \<in> DASHED; UNDASHED \<sharp> e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e/\<^sub>px]\<rbrakk>R = {(b1, b2) | b1 b2. (b1, b2(x~ :=\<^sub>b \<lbrakk>e\<acute>\<rbrakk>\<^sub>eb2)) \<in> \<lbrakk>p\<rbrakk>R}"
  apply (subst PrimeE_double[of e, THEN sym])
  apply (subst SS_dash_DASHED[of x, THEN sym], simp)
  apply (subst SubstP_rel_DASHED_PrimeE)
  apply (simp_all add:closure urename typing unrest)
done

(*
theorem SubstP_rel_DASHED [evalr] :
"\<lbrakk> x \<in> DASHED; e \<rhd>\<^sub>e x; UNREST_EXPR UNDASHED e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e|x]\<rbrakk>R = {(b1, b2) | b1 b2. (b1(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<epsilon>b1), b2) \<in> \<lbrakk>p\<rbrakk>R}"
*)

lemma EvalE_RenameB_VAR_RENAME_ON [evale]:
  assumes "ss \<in> VAR_RENAME_ON vs" "UNREST_EXPR vs e"
  shows "\<lbrakk>e\<rbrakk>\<^sub>e (ss\<bullet>b) = \<lbrakk>e\<rbrakk>\<^sub>e b"
proof -

  have "ss\<bullet>b = (ss\<bullet>b) \<oplus>\<^sub>b b on - vs"
    by (fact RenameB_override_VAR_RENAME_ON[OF assms(1)])

  with assms(2) show ?thesis
    by (metis EvalE_UNREST_override binding_override_minus)

qed

lemma UNREST_EXPR_REL_VAR_DASHED [unrest]:
  "UNREST_EXPR REL_VAR e \<Longrightarrow> UNREST_EXPR DASHED e"
  by (metis UNREST_EXPR_unionE)

lemma UNREST_EXPR_REL_VAR_UNDASHED [unrest]:
  "UNREST_EXPR REL_VAR e \<Longrightarrow> UNREST_EXPR UNDASHED e"
  by (metis UNREST_EXPR_unionE)

lemma SS_REL_VAR_expr [urename]:
  "REL_VAR \<sharp> e \<Longrightarrow> \<langle>e\<rangle>\<^sub>e (SS\<bullet>b) = \<langle>e\<rangle>\<^sub>e b"
  by (metis EvalE_RenameB_VAR_RENAME_ON EvalE_def SS_VAR_RENAME_ON)

lemma SS_REL_VAR_overshadow [urename]:
  "(SS\<bullet>b1) \<oplus>\<^sub>b b2 on REL_VAR = b1 \<oplus>\<^sub>b b2 on REL_VAR"
  by (metis SS_VAR_RENAME_ON binding_override_RENAME_ON_overshadow)

lemma UNDASHED_minus_NON_REL_VAR [simp]:
  "xs \<subseteq> NON_REL_VAR \<Longrightarrow> UNDASHED - xs = UNDASHED"
  by auto

lemma DASHED_minus_NON_REL_VAR [simp]:
  "xs \<subseteq> NON_REL_VAR \<Longrightarrow> DASHED - xs = DASHED"
  by auto
  
lemma WF_REL_BINDING_BindR_fst [closure]:
  "(b1, b2) = BindR b \<Longrightarrow> b1 \<in> WF_REL_BINDING"
  by (auto simp add:WF_REL_BINDING_def BindR_def)

lemma WF_REL_BINDING_BindR_snd [closure]:
  "(b1, b2) = BindR b \<Longrightarrow> b2 \<in> WF_REL_BINDING"
  by (auto simp add:WF_REL_BINDING_def BindR_def)

lemma WF_REL_BINDING_BindR_equiv:
  "(b1, b2) = BindR b \<Longrightarrow> b1 \<cong> b2 on NON_REL_VAR"
  by (metis EvalR_NON_REL_VAR EvalR_def TrueP.rep_eq rangeI)

lemma WF_REL_BINDING_NON_REL_VAR_binding_upd [closure]:
  "\<lbrakk> x \<in> NON_REL_VAR; b \<in> WF_REL_BINDING \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v) \<in> WF_REL_BINDING"
  by (auto simp add:WF_REL_BINDING_def)

theorem SubstP_rel_NON_REL_VAR [evalr] :
"\<lbrakk> x \<in> NON_REL_VAR; REL_VAR \<sharp> e \<rbrakk> \<Longrightarrow> 
  \<lbrakk>p[e/\<^sub>px]\<rbrakk>R = {(b1, b2) | b1 b2. (b1(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>eb1), b2(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>eb2)) \<in> \<lbrakk>p\<rbrakk>R 
                                \<and> \<langle>b1\<rangle>\<^sub>b x = \<langle>b2\<rangle>\<^sub>b x}"
  apply (auto simp add: EvalR_def SubstP_def BindR_image image_def)
  apply (rule_tac x="BindP (a(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>e b), b(x :=\<^sub>b \<lbrakk>e\<rbrakk>\<^sub>e b))" in bexI)
  apply (subst BindR_inverse)
  apply (simp_all add: closure)
  apply (metis (hide_lams, no_types) WF_REL_BINDING_BindR_equiv binding_equiv_minus binding_equiv_update_drop)
  apply (subgoal_tac "a \<cong> b on - REL_VAR")
  apply (metis Compl_eq_Diff_UNIV EvalE_def NON_REL_VAR_def UNDASHED_DASHED_inter(16) VAR_def utp_expr_tac.EvalP_UNREST_binding_equiv)
  apply (metis NON_REL_VAR_def WF_REL_BINDING_BindR_equiv)
  apply (simp add:BindP_def BindR_def unrest urename)
  apply (simp add: EvalE_UNREST_override UNREST_EXPR_REL_VAR_DASHED urename closure RenameB_override_distr1)
  apply (metis EvalE_def SS_REL_VAR_expr)
  apply (subgoal_tac "x \<notin> D\<^sub>1")
  apply (auto simp add:BindR_def closure urename)[1]
  apply (auto)[1]
  apply (rule_tac x="BindP (xa, y)" in exI)
  apply (subst BindR_inverse)
  apply (metis WF_REL_BINDING_BindR_fst WF_REL_BINDING_NON_REL_VAR_binding_upd binding_upd_simps(1) binding_upd_triv)
  apply (metis WF_REL_BINDING_BindR_snd WF_REL_BINDING_NON_REL_VAR_binding_upd binding_upd_simps(1) binding_upd_triv)
  apply (metis (hide_lams, no_types) Diff_insert_absorb Set.set_insert WF_REL_BINDING_BindR_equiv binding_equiv_insert binding_equiv_update_drop2)
  apply (auto simp add:BindR_def BindP_def urename)
  apply (subst UNREST_EXPR_member)
  apply (simp add:unrest)
  apply (simp add:EvalE_def)
  apply (subgoal_tac "y \<cong> SS\<bullet>xb on UNDASHED")
  defer
  apply (subgoal_tac "y(x :=\<^sub>b \<langle>e\<rangle>\<^sub>e y) \<cong> SS\<bullet>xb on UNDASHED")
  defer
  apply (simp)
  apply (metis ComplI UNDASHED_not_DASHED binding_equiv_subset binding_override_equiv2 subsetI)
  defer
  apply (metis UNDASHED_not_NON_REL_VAR binding_equiv_update_subsume evar_compat)
  apply (subgoal_tac "SS\<bullet>y \<cong> xb on DASHED")
  defer
  apply (simp add:binding_equiv_def)
  apply (auto)
  apply (drule_tac x="SS\<bullet>xc" in bspec)
  apply (metis DASHED_undash_UNDASHED SS_DASHED_app)
  apply (metis SS_VAR_RENAME_INV VAR_RENAME_INV_app)
  apply (metis binding_equiv_comm binding_override_equiv)
done

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
"\<lbrakk>p1 ;\<^sub>R p2\<rbrakk>R = \<lbrakk>p1\<rbrakk>R O \<lbrakk>p2\<rbrakk>R"
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

lemma EvalP_SemiR [eval]:
  "\<lbrakk>p ;\<^sub>R q\<rbrakk>b = (\<exists> b1 b2. b = b1 \<oplus>\<^sub>b b2 on D\<^sub>1 \<and> \<lbrakk>p\<rbrakk>b1 \<and> \<lbrakk>q\<rbrakk>b2 \<and> (b1, b2) \<in> COMPOSABLE_BINDINGS)"
  by (simp add:EvalP_def SemiR.rep_eq)

declare CondR_def [evalr,evalrr]

lemma EvalR_as_EvalP [eval]: "\<lbrakk>p\<rbrakk>R = {BindR b | b. \<lbrakk>p\<rbrakk>b}"
  by (auto simp add:EvalR_def EvalP_def)

lemma EvalR_as_EvalP':
  "\<lbrakk>P\<rbrakk>R = {(b1, b2). \<lbrakk>P\<rbrakk>(b1 \<oplus>\<^sub>b SS\<bullet>b2 on D\<^sub>1)
                   \<and> b1 \<in> WF_REL_BINDING
                   \<and> b2 \<in> WF_REL_BINDING
                   \<and> b1 \<cong> b2 on NON_REL_VAR}"
  apply (auto simp add:EvalR_as_EvalP eval BindR_def RenameB_override_distr1 urename closure)
  apply (metis BindR_def WF_REL_BINDING_BindR_equiv)
  apply (rule_tac x="xa \<oplus>\<^sub>b SS\<bullet>y on D\<^sub>1" in exI)
  apply (auto simp add:RenameB_override_distr1 urename closure)
  apply (auto simp add:WF_REL_BINDING_def RenameB_override_distr1 urename closure)
  apply (metis (hide_lams, no_types) SS_REL_VAR_overshadow binding_eq_split_equiv binding_equiv_UNDASHED_overshadow binding_equiv_idem binding_equiv_trans binding_override_equiv1 binding_override_simps(1) binding_override_simps(4) sup.commute)
done

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
"\<lbrakk>p1 \<and>\<^sub>p p2\<rbrakk>\<R> = \<lbrakk>p1\<rbrakk>\<R> \<inter> \<lbrakk>p2\<rbrakk>\<R>"
  by (force simp add: evalr MkRel_def)

theorem EvalRR_OrP [evalrr] :
"\<lbrakk>p1 \<or>\<^sub>p p2\<rbrakk>\<R> = \<lbrakk>p1\<rbrakk>\<R> \<union> \<lbrakk>p2\<rbrakk>\<R>"
  by (force simp add: evalr MkRel_def)

theorem EvalRR_SemiR [evalrr] :
"\<lbrakk>p1 ;\<^sub>R p2\<rbrakk>\<R> = \<lbrakk>p1\<rbrakk>\<R> O \<lbrakk>p2\<rbrakk>\<R>"
  by (force simp add: evalr MkRel_def)

lemma EvalRR_ConvR [evalrr]:
  "\<lbrakk>p\<^sup>\<smile>\<rbrakk>\<R> = \<lbrakk>p\<rbrakk>\<R>\<inverse>"
  by (force simp add:evalr MkRel_def)

lemma EvalRR_refinement [evalrr]: "p \<sqsubseteq> q \<longleftrightarrow> \<lbrakk>q\<rbrakk>\<R> \<subseteq> \<lbrakk>p\<rbrakk>\<R>"
  by (simp add:evalr evalrr MkRel_subset[THEN sym] EvalR_range)

(* I opt for EvalR_TrueP_explicit because I think it's in general more useful *)

declare EvalR_TrueP [evalr del]
declare EvalR_TrueP_explicit [evalr]

text {* Set up some introduction / elimination laws which facilitate proving binding 
        equivalence laws needed by the relational tactic. *}

lemma EvalR_UNREST_UNDASHED_intro [intro]:
  "\<lbrakk> D\<^sub>0 \<sharp> p ; (b1, b2) \<in> \<lbrakk>p\<rbrakk>R
   ; b1 \<cong> b1' on NON_REL_VAR 
   ; b1 \<cong> b1' on DASHED \<rbrakk> \<Longrightarrow> (b1', b2) \<in> \<lbrakk>p\<rbrakk>R"
  apply (auto simp add:EvalR_def BindR_def image_def urename unrest RenameB_override_distr1)
  apply (rule_tac  x="x \<oplus>\<^sub>b b1' on D\<^sub>0" in bexI)
  apply (simp add:binding_equiv_overshadow_left urename RenameB_override_distr1 closure)
  apply (metis (hide_lams, no_types) UNDASHED_DASHED_inter(15) binding_override_equiv binding_override_simps(10) binding_override_simps(2) binding_override_simps(4) binding_override_simps(5) binding_override_simps(6))
  apply (metis UNREST_binding_override)
done

lemma EvalR_UNREST_DASHED_intro [intro]:
  "\<lbrakk> D\<^sub>1 \<sharp> p ; (b1, b2) \<in> \<lbrakk>p\<rbrakk>R
   ; b2 \<cong> b2' on NON_REL_VAR 
   ; b2 \<cong> b2' on DASHED \<rbrakk> \<Longrightarrow> (b1, b2') \<in> \<lbrakk>p\<rbrakk>R"
  apply (auto simp add:EvalR_def BindR_def image_def urename unrest RenameB_override_distr1)
  apply (rule_tac  x="x \<oplus>\<^sub>b (SS\<bullet>b2') on D\<^sub>1" in bexI)
  apply (simp)
  apply (subgoal_tac "D\<^sub>1 \<inter> NON_REL_VAR = {}")
  apply (simp add:binding_equiv_overshadow_left urename RenameB_override_distr1 closure)
  apply (metis (hide_lams, no_types) UNDASHED_DASHED_inter(16) binding_equiv_comm binding_override_assoc binding_override_equiv binding_override_minus)
  apply (force)
  apply (metis UNREST_binding_override)
done

lemma EvalR_binding_equiv_DASHED: "(b1, b2) \<in> \<lbrakk>p\<rbrakk>R \<Longrightarrow> b1 \<cong> b2 on D\<^sub>1"
  by (metis WF_REL_BINDING_bc_DASHED WF_REL_BINDING_member1 WF_REL_BINDING_member2 binding_equiv_comm binding_equiv_trans)

lemma EvalR_DASHED_elim [elim]: "\<lbrakk> (b1, b2) \<in> \<lbrakk>p\<rbrakk>R; b1 \<cong> b2 on D\<^sub>1 \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis EvalR_binding_equiv_DASHED)

lemma EvalR_NON_REL_VAR_elim [elim]: "\<lbrakk> (b1, b2) \<in> \<lbrakk>p\<rbrakk>R; b1 \<cong> b2 on NON_REL_VAR \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis EvalR_NON_REL_VAR)

lemma binding_equiv_sym_elim [elim]:
  "\<lbrakk> b1 \<cong> b2 on vs; b2 \<cong> b1 on vs \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis binding_equiv_comm)

lemma EvalR_WF_REL_BINDING_left [elim]:
  "\<lbrakk> (b1, b2) \<in> \<lbrakk>p\<rbrakk>R; b1 \<in> WF_REL_BINDING \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis WF_REL_BINDING_member1)

lemma EvalR_WF_REL_BINDING_right [elim]:
  "\<lbrakk> (b1, b2) \<in> \<lbrakk>p\<rbrakk>R; b2 \<in> WF_REL_BINDING \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis WF_REL_BINDING_member2)

lemma EvalR_UNREST_DASHED_refl_intro:
  "\<lbrakk> REL_VAR \<sharp> p ; (b1, b2) \<in> \<lbrakk>p\<rbrakk>R \<rbrakk> \<Longrightarrow> (b1, b1) \<in> \<lbrakk>p\<rbrakk>R"
  apply (auto simp add:EvalR_def BindR_def image_def urename unrest RenameB_override_distr1)
  apply (metis (hide_lams, no_types) BindR_COMPOSABLE_BINDINGS BindR_def RenameB_SS_COMPOSABLE_BINDINGS_2 RenameB_inv_cancel2 SS_inv UNREST_def UNREST_unionE binding_override_simps(3))
done

lemma EvalR_UNREST_DASHED_left_intro:
  "\<lbrakk> REL_VAR \<sharp> p ; (b1, b2) \<in> \<lbrakk>p\<rbrakk>R
   ; (b2 \<cong> b2' on NON_REL_VAR)
   ; b2 \<cong> b2' on DASHED \<rbrakk> \<Longrightarrow> (b1, b2') \<in> \<lbrakk>p\<rbrakk>R"
  apply (auto simp add:EvalR_def BindR_def image_def urename unrest RenameB_override_distr1)
  apply (rule_tac  x="x \<oplus>\<^sub>b SS\<bullet>b2' on D\<^sub>1" in bexI)
  apply (simp add:binding_equiv_overshadow_left urename RenameB_override_distr1 closure)
  apply (metis (hide_lams, no_types) UNDASHED_DASHED_inter(16) binding_equiv_comm binding_override_assoc binding_override_equiv binding_override_minus)
  apply (metis UNREST_binding_override UNREST_unionE)
done

lemma EvalR_UNREST_DASHED_right_intro:
  "\<lbrakk> REL_VAR \<sharp> p ; (b1, b2) \<in> \<lbrakk>p\<rbrakk>R
   ; (b1 \<cong> b1' on NON_REL_VAR)
   ; b1 \<cong> b1' on DASHED \<rbrakk> \<Longrightarrow> (b1', b2) \<in> \<lbrakk>p\<rbrakk>R"
  apply (auto simp add:EvalR_def BindR_def image_def urename unrest RenameB_override_distr1)
  apply (rule_tac  x="x \<oplus>\<^sub>b b1' on D\<^sub>0" in bexI)
  apply (simp add:binding_equiv_overshadow_left urename RenameB_override_distr1 closure)
  apply (metis NON_REL_VAR_def binding_equiv_comm binding_override_assoc binding_override_equiv binding_override_minus)
  apply (metis UNREST_binding_override UNREST_unionE)
done

declare binding_equiv_trans [intro]


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
      addsimps (closure.get ctxt)
      addsimps @{thms "var_dist"};
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

lemma "\<lbrakk> x \<in> UNDASHED; y \<in> UNDASHED; UNREST_EXPR DASHED e; UNREST_EXPR DASHED f; e \<rhd>\<^sub>e x; f \<rhd>\<^sub>e y; x \<noteq> y \<rbrakk> \<Longrightarrow> x :=\<^sub>R e ;\<^sub>R y :=\<^sub>R f = x,y :=\<^sub>R e,f"
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


lemma EvalR_EqualP_alt:
  "\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> v \<rbrakk> \<Longrightarrow>
   \<lbrakk>($\<^sub>ex\<acute> ==\<^sub>p v)\<rbrakk>R = { (b1 \<oplus>\<^sub>b bc on DASHED, b2 \<oplus>\<^sub>b bc on DASHED) 
                     | b1 b2. \<langle>b2\<rangle>\<^sub>b x = \<lbrakk>v\<rbrakk>\<^sub>eb1 \<and> b1 \<cong> b2 on NON_REL_VAR }"
  apply (auto simp add:EvalR_EqualP evale BindR_def)

  apply (auto simp add:EvalR_def EqualP_def BindR_def image_def EvalE_def VarE.rep_eq)
  apply (metis (hide_lams, mono_tags) CompB_def CompB_rep_eq NON_REL_VAR_def RenameB_def SS_REL_VAR_overshadow SS_UNDASHED_app SS_inv binding_override_equiv2 binding_override_simps(2) comp_apply)
  apply (rule_tac x="b1 \<oplus>\<^sub>b (SS\<bullet>b2) on DASHED" in exI)
  apply (auto simp add:urename RenameB_override_distr1 closure)
  apply (rule binding_override_eq_intro)
  apply (metis NON_REL_VAR_def SS_REL_VAR_overshadow binding_equiv_override binding_equiv_trans binding_override_equiv1 binding_override_minus binding_override_simps(1) binding_override_simps(2))
  apply (simp)
done

lemma EvalR_EqualP_alt' [evalr]:
  "\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> v \<rbrakk> \<Longrightarrow>
   \<lbrakk>$\<^sub>ex\<acute> ==\<^sub>p v\<rbrakk>R = { (b1, b2). \<langle>b2\<rangle>\<^sub>b x = \<lbrakk>v\<rbrakk>\<^sub>eb1 \<and> b1 \<cong> b2 on NON_REL_VAR 
                            \<and> b1 \<in> WF_REL_BINDING \<and> b2 \<in> WF_REL_BINDING }"
  apply (auto simp add:EvalR_EqualP_alt closure)
  apply (metis EvalE_UNREST_override UNREST_EXPR_unionE)
  apply (metis binding_override_left_eq)
  apply (metis WF_REL_BINDING_bc_DASHED binding_override_equiv)
done

lemma EvalR_EqualP_UNDASHED [evalr]:
  "\<lbrakk> x \<in> UNDASHED; DASHED \<sharp> v \<rbrakk> \<Longrightarrow>
   \<lbrakk>$\<^sub>ex ==\<^sub>p v\<rbrakk>R = { (b1, b2). \<langle>b1\<rangle>\<^sub>b x = \<lbrakk>v\<rbrakk>\<^sub>eb1 \<and> b1 \<cong> b2 on NON_REL_VAR 
                            \<and> b1 \<in> WF_REL_BINDING \<and> b2 \<in> WF_REL_BINDING }"
  apply (auto simp add:EvalR_EqualP evale BindR_def closure)
  apply (metis RenameB_equiv_VAR_RENAME_ON_2 SS_VAR_RENAME_ON UNDASHED_DASHED_inter(16) binding_override_left_eq)
  apply (smt BindR_def BindR_inverse EvalE_UNREST_override Pair_inject UNDASHED_DASHED_contra WF_REL_BINDING_bc_DASHED binding_override_equiv binding_override_on_eq)
done

lemma EvalR_EqualP_DASHED [evalr]:
  "\<lbrakk> x \<in> D\<^sub>0; D\<^sub>1 \<sharp> v \<rbrakk> \<Longrightarrow>
   \<lbrakk>$\<^sub>ex\<acute> ==\<^sub>p v\<acute>\<rbrakk>R = { (b1, b2). \<langle>b2\<rangle>\<^sub>b x = \<lbrakk>v\<rbrakk>\<^sub>eb2 \<and> b1 \<cong> b2 on NON_REL_VAR 
                            \<and> b1 \<in> WF_REL_BINDING \<and> b2 \<in> WF_REL_BINDING }"
  apply (auto simp add:EvalR_EqualP evale BindR_def closure)
  apply (metis SS_UNDASHED_app)
  apply (metis RenameB_equiv_VAR_RENAME_ON_2 SS_VAR_RENAME_ON UNDASHED_DASHED_inter(16) binding_override_left_eq)
  apply (rule_tac x="(SS\<bullet>y) \<oplus>\<^sub>b xa on D\<^sub>0" in exI)
  apply (auto simp add:urename closure RenameB_override_distr1 unrest evale)
  apply (metis NON_REL_VAR_def SS_REL_VAR_overshadow WF_REL_BINDING_bc_DASHED binding_override_assoc binding_override_equiv binding_override_minus)
  apply (metis WF_REL_BINDING_bc_DASHED binding_override_equiv)
done

lemma AssignR_alt_def: 
  "\<lbrakk>v \<rhd>\<^sub>e x; x \<in> UNDASHED \<rbrakk> \<Longrightarrow> x :=\<^sub>R v = ($\<^sub>ex\<acute> ==\<^sub>p v) \<and>\<^sub>p II\<^bsub>REL_VAR - {x,x\<acute>}\<^esub>"
  apply (simp add:SkipRA_def)
  apply (utp_pred_tac)
  apply (safe)
  apply (simp_all add:IdA.rep_eq AssignF_upd_rep_eq evale VarE.rep_eq EvalE_def urename)
  apply (rule_tac x="b(x\<acute> :=\<^sub>b \<langle>b\<rangle>\<^sub>b x)" in exI)
  apply (simp_all)
  apply (rule)
  apply (metis (lifting) UNDASHED_eq_dash_contra undash_dash)
  apply (drule_tac x="va" in bspec, simp_all)
  apply (metis UNDASHED_eq_dash_contra undash_dash)
done

lemma SS_equiv_UNDASHED: "\<forall>v\<in>D\<^sub>0. \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b v\<acute> \<Longrightarrow> SS\<bullet>b = b"
  apply (rule Rep_WF_BINDING_intro)
  apply (simp add:RenameB_rep_eq)
  apply (rule ext)
  apply (auto)
  apply (case_tac "x \<in> D\<^sub>0")
  apply (simp add:urename)
  apply (case_tac "x \<in> D\<^sub>1")
  apply (simp_all add:urename)
done

lemma EvalR_ExistsP_UNDASHED:
  "xs \<subseteq> D\<^sub>0 \<Longrightarrow> \<lbrakk>\<exists>\<^sub>p xs. P\<rbrakk>R = { (b1 \<oplus>\<^sub>b b on xs, b2) 
                             | b1 b2 b. (b1, b2) \<in> \<lbrakk>P\<rbrakk>R \<and> b \<in> WF_REL_BINDING }"
  apply (subst EvalR_as_EvalP')
  apply (subst EvalR_as_EvalP')
  apply (simp add:eval)
  apply (auto)
  apply (rule_tac x="xa \<oplus>\<^sub>b b' on xs" in exI)
  apply (auto)
  apply (rule_tac x="xa" in exI)
  apply (auto)
  apply (subst binding_override_assoc)
  apply (subst binding_override_minus)
  apply (subst binding_override_assoc')
  apply (simp)
  apply (subgoal_tac "- D\<^sub>1 \<inter> (xs \<union> D\<^sub>1) = xs")
  apply (simp)
  apply (auto)[1]
  apply (metis WF_REL_BINDING_override_UNDASHED binding_override_left_subset binding_override_simps(2))
  apply (metis binding_equiv_UNDASHED_overshadow binding_equiv_comm binding_override_left_subset binding_override_simps(2))
  apply (metis (hide_lams, no_types) binding_override_overshadow binding_override_simps(1) binding_override_simps(2) binding_override_simps(3))
  apply (metis WF_REL_BINDING_override_UNDASHED binding_override_left_subset binding_override_simps(2))
  apply (metis binding_equiv_UNDASHED_overshadow binding_equiv_comm binding_override_left_subset)
done

theorem SS_UNDASHED_subset_image :
"xs \<subseteq> UNDASHED \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s`xs = dash`xs"
  by (metis SS_UNDASHED_app image_cong set_mp)

theorem SS_DASHED_subset_image :
"xs \<subseteq> DASHED \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s`xs = undash`xs"
  by (metis (hide_lams, no_types) SS_DASHED_image SS_UNDASHED_subset_image SS_VAR_RENAME_INV SS_inv' VAR_RENAME_INV_app image_mono image_surj_f_inv_f surj_iff_all undash_dash_image)

lemma WF_REL_BINDING_override_UNDASHED_subset:
  "\<lbrakk> b \<in> WF_REL_BINDING; vs \<subseteq> D\<^sub>0 \<rbrakk> \<Longrightarrow> b \<oplus>\<^sub>b b' on vs \<in> WF_REL_BINDING"
  by (metis WF_REL_BINDING_override_UNDASHED binding_override_left_subset binding_override_simps(2))
  
lemma EvalR_ExistsP_DASHED:
  "xs \<subseteq> D\<^sub>1 \<Longrightarrow> \<lbrakk>\<exists>\<^sub>p xs. P\<rbrakk>R = { (b1, b2 \<oplus>\<^sub>b b on undash ` xs) 
                             | b1 b2 b. (b1, b2) \<in> \<lbrakk>P\<rbrakk>R \<and> b \<in> WF_REL_BINDING }"
  apply (subst EvalR_as_EvalP')
  apply (subst EvalR_as_EvalP')
  apply (simp add:eval)
  apply (auto)
  apply (rule_tac x="y \<oplus>\<^sub>b SS\<bullet>b' on undash`xs" in exI)
  apply (simp add:RenameB_override_distr1 urename closure)
  apply (rule_tac x="y" in exI)
  apply (auto)
  apply (subst SS_UNDASHED_subset_image)
  apply (force)
  apply (metis Un_absorb2 binding_override_assoc dash_undash_image)
  apply (rule WF_REL_BINDING_override_UNDASHED_subset)
  apply (simp_all)
  apply (force)
  apply (metis (hide_lams, no_types) SS_DASHED_image SS_DASHED_subset_image binding_equiv_UNDASHED_overshadow binding_override_left_subset image_mono)
  apply (simp add:RenameB_override_distr1 urename closure)
  apply (subst SS_UNDASHED_subset_image)  
  apply (force)
  apply (simp)
  apply (subst binding_override_assoc)
  apply (simp)
  apply (metis binding_override_assoc binding_override_simps(2))
  apply (metis WF_REL_BINDING_override_UNDASHED_subset image_mono undash_DASHED_image)
  apply (metis (hide_lams, no_types) binding_equiv_UNDASHED_overshadow binding_override_left_subset image_mono undash_DASHED_image)
done


lemma EvalR_VarOpenP [evalr]:
  "x \<in> D\<^sub>0 \<Longrightarrow> \<lbrakk>var x\<rbrakk>R = {(b,b'). b \<cong> b' on D\<^sub>0 - {x} \<and> b \<cong> b' on NON_REL_VAR
                                \<and> b  \<in> WF_REL_BINDING \<and> b' \<in> WF_REL_BINDING}"
  apply (simp add:VarOpenP_def)
  apply (subst EvalR_ExistsP_UNDASHED)
  apply (auto simp add:evalr)
  apply (metis WF_REL_BINDING_binding_upd)
  apply (rule_tac x="y" in exI)
  apply (rule_tac x="xa" in exI)
  apply (auto simp add:evalr WF_REL_BINDING_binding_upd)
  apply (rule binding_eq_split_equiv)
  apply (simp_all add:closure)
  apply (metis binding_equiv_update_drop binding_upd_triv)
  apply (metis WF_REL_BINDING_bc_DASHED binding_equiv_comm binding_equiv_trans)
done  

lemma EvalR_VarCloseP [evalr]:
  "x \<in> D\<^sub>0 \<Longrightarrow> \<lbrakk>end x\<rbrakk>R = {(b,b'). b \<cong> b' on D\<^sub>0 - {x} \<and> b \<cong> b' on NON_REL_VAR
                                \<and> b  \<in> WF_REL_BINDING \<and> b' \<in> WF_REL_BINDING}"
  apply (simp add:VarCloseP_def)
  apply (subst EvalR_ExistsP_DASHED)
  apply (auto simp add:evalr)
  apply (metis WF_REL_BINDING_binding_upd)
  apply (rule_tac x="xa" in exI)
  apply (rule_tac x="y" in exI)
  apply (auto simp add:evalr WF_REL_BINDING_binding_upd)
  apply (rule binding_eq_split_equiv)
  apply (simp_all add:closure)
  apply (metis binding_equiv_comm binding_equiv_update_drop binding_upd_triv)
  apply (metis WF_REL_BINDING_bc_DASHED binding_equiv_sym_elim binding_equiv_trans)
  apply (metis binding_equiv_comm)
done  

lemma EvalR_VarExtP [evalr]:
  "x \<in> D\<^sub>0 \<Longrightarrow> \<lbrakk>P\<^bsub>+x\<^esub>\<rbrakk>R = {(b,b'). (b,b') \<in> \<lbrakk>P\<rbrakk>R \<and> \<langle>b\<rangle>\<^sub>b x = \<langle>b'\<rangle>\<^sub>b x 
                              \<and> b \<in> WF_REL_BINDING \<and> b' \<in> WF_REL_BINDING
                              \<and> b \<cong> b' on NON_REL_VAR}"
  by (auto simp add: VarExtP_def evalr unrest evale)

declare binding_equiv_trans [intro]

end