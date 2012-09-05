(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_unrest.thy                                                       *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Unrestricted Variables *}

theory utp_unrest
imports utp_pred utp_subst
begin

subsection {* Theorem Attributes *}

ML {*
  structure unrest =
    Named_Thms (val name = @{binding unrest} val description = "unrest theorems")
*}

setup unrest.setup

context PRED
begin

subsubsection {* @{term UNREST} Function *}

definition UNREST ::
  "('TYPE VAR) set \<Rightarrow> ('VALUE, 'TYPE) PREDICATE \<Rightarrow> bool" where
"UNREST vs p \<longleftrightarrow> (\<forall> b1 \<in> p . \<forall> b2 \<in> WF_BINDING . b1 \<oplus> b2 on vs \<in> p)"

subsubsection {* Restricted Predicates *}

definition WF_PREDICATE_OVER ::
  "('TYPE VAR) set \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE set" where
"WF_PREDICATE_OVER vs = {p . p \<in> WF_PREDICATE \<and> UNREST (VAR - vs) p}"

subsubsection {* Theorems *}

theorem UNREST_binding_override [intro] :
"\<lbrakk>p \<in> WF_PREDICATE; b \<in> p;
 b' \<in> WF_BINDING;
 UNREST vs p\<rbrakk> \<Longrightarrow>
 (b \<oplus> b' on vs) \<in> p"
apply (simp add: UNREST_def)
done

theorem UNREST_empty :
"p \<in> WF_PREDICATE \<Longrightarrow> UNREST {} p"
apply (simp add: UNREST_def)
done

theorem UNREST_subset :
"\<lbrakk>UNREST vs1 p;
 vs2 \<subseteq> vs1;
 p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 UNREST vs2 p"
apply (simp add: UNREST_def)
apply (clarify)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (drule_tac x = "b2 \<oplus> b1 on (vs1 - vs2)" in bspec)
apply (simp add: closure)
apply (simp)
apply (subgoal_tac "vs1 - (vs1 - vs2) = vs2")
apply (simp)
apply (auto)
done

theorem UNREST_union :
"\<lbrakk>p \<in> WF_PREDICATE;
 UNREST vs1 p;
 UNREST vs2 p\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<union> vs2) p"
apply (simp add: UNREST_def)
apply (clarify)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (drule_tac x = "b2" in bspec) back
apply (assumption)
apply (drule_tac x = "b1 \<oplus> b2 on vs1" in bspec)
apply (assumption)
apply (drule_tac x = "b2" in bspec)
apply (assumption)
apply (simp)
done

theorem UNREST_LiftP :
"\<lbrakk>f \<in> WF_BINDING_BFUN vs\<rbrakk> \<Longrightarrow>
 UNREST (VAR - vs) (LiftP f)"
apply (simp add: UNREST_def LiftP_def)
apply (simp add: WF_BINDING_BFUN_def)
apply (safe)
apply (simp add: closure)
apply (drule_tac x = "b1" in spec)
apply (drule_tac x = "b1 \<oplus> b2 on (VAR - vs)" in spec)
apply (simp add: binding_equiv_def)
done

theorem UNREST_LiftP_alt :
"\<lbrakk>f \<in> WF_BINDING_BFUN vs1;
 vs2 \<subseteq> VAR - vs1\<rbrakk> \<Longrightarrow>
 UNREST vs2 (LiftP f)"
apply (auto intro: UNREST_LiftP UNREST_subset simp: closure)
done

theorem UNREST_TrueP :
"UNREST vs true"
apply (simp add: UNREST_def TrueP_def)
apply (simp add: closure)
done

theorem UNREST_FalseP :
"UNREST vs false"
apply (simp add: UNREST_def FalseP_def)
done

theorem UNREST_NotP :
"\<lbrakk>p \<in> WF_PREDICATE;
 UNREST vs p\<rbrakk> \<Longrightarrow>
 UNREST vs (\<not>p p)"
apply (simp add: UNREST_def NotP_def)
apply (clarify)
apply (simp add: closure)
apply (erule_tac Q = "b1 \<notin> p" in contrapos_pp)
apply (simp)
apply (drule_tac x = "b1 \<oplus> b2 on vs" in bspec)
apply (assumption)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (simp)
done

theorem UNREST_AndP :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<and>p p2)"
apply (simp add: UNREST_def AndP_def)
done

theorem UNREST_OrP :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<or>p p2)"
apply (simp add: UNREST_def OrP_def)
apply (clarify)
apply (drule_tac x = "b1" in bspec)
apply (auto) [1]
apply (drule_tac x = "b2" in bspec) back
apply (assumption)
apply (assumption)
done

theorem UNREST_ImpliesP :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<Rightarrow>p p2)"
apply (simp add: ImpliesP_def)
apply (auto intro: UNREST_OrP UNREST_NotP)
done

theorem UNREST_IffP :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<Leftrightarrow>p p2)"
apply (simp add: IffP_def)
apply (auto intro: UNREST_ImpliesP UNREST_AndP)
done

theorem UNREST_ExistsP :
"\<lbrakk>UNREST vs1 p;
 p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<union> vs2) (\<exists>p vs2 . p)"
apply (simp add: UNREST_def ExistsP_def)
apply (clarify)
apply (simp add: override_on_assoc)
apply (subgoal_tac "vs2 \<union> (vs1 \<union> vs2) = (vs1 \<union> vs2)")
apply (simp)
apply (rule_tac x = "b1a \<oplus> b2 on vs1" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
apply (auto)
done

theorem UNREST_ForallP :
"\<lbrakk>UNREST vs1 p;
 p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<union> vs2) (\<forall>p vs2 . p)"
apply (simp add: ForallP_def)
apply (auto intro: UNREST_ExistsP UNREST_NotP)
done

theorem UNREST_ExistsP_alt :
"\<lbrakk>UNREST vs1 p;
 vs3 \<subseteq> vs1 \<union> vs2;
 p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 UNREST vs3 (\<exists>p vs2 . p)"
apply (auto intro: UNREST_ExistsP UNREST_subset simp: closure)
done

theorem UNREST_ForallP_alt :
"\<lbrakk>UNREST vs1 p;
 vs3 \<subseteq> vs1 \<union> vs2;
 p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 UNREST vs3 (\<forall>p vs2 . p)"
apply (auto intro: UNREST_ForallP UNREST_subset simp: closure)
done

theorem UNREST_ExistsP_simple :
"\<lbrakk>p \<in> WF_PREDICATE;
 vs1 \<subseteq> vs2\<rbrakk> \<Longrightarrow>
 UNREST vs1 (\<exists>p vs2 . p)"
apply (auto intro: UNREST_ExistsP_alt UNREST_empty)
done

theorem UNREST_ForallP_simple :
"\<lbrakk>p \<in> WF_PREDICATE;
 vs1 \<subseteq> vs2\<rbrakk> \<Longrightarrow>
 UNREST vs1 (\<forall>p vs2 . p)"
apply (auto intro: UNREST_ForallP_alt UNREST_empty)
done

theorem UNREST_SubstP :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST;
 UNREST vs p\<rbrakk> \<Longrightarrow>
 UNREST (ss ` vs) p[ss]"
apply (simp add: UNREST_def)
apply (simp add: SubstP_def)
apply (safe)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (drule_tac x = "SubstB (inv ss) b2" in bspec)
apply (simp add: closure)
apply (drule imageI [where f = "SubstB ss"])
back back
apply (simp add: SubstB_override_distr1 closure)
done

theorem UNREST_SubstP_alt :
"\<lbrakk>UNREST vs1 p;
 vs2 \<subseteq> (ss ` vs1);
 p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 UNREST vs2 p[ss]"
apply (auto intro: UNREST_SubstP UNREST_subset simp: closure)
done

subsubsection {* Proof Support *}

declare UNREST_empty [unrest]
declare UNREST_subset [unrest]
declare UNREST_union [unrest]
declare UNREST_LiftP_alt [unrest]
declare UNREST_TrueP [unrest]
declare UNREST_FalseP [unrest]
declare UNREST_NotP [unrest]
declare UNREST_AndP [unrest]
declare UNREST_OrP [unrest]
declare UNREST_ImpliesP [unrest]
declare UNREST_IffP [unrest]
declare UNREST_ExistsP_alt [unrest]
declare UNREST_ForallP_alt [unrest]
declare UNREST_ExistsP_simple [unrest]
declare UNREST_ForallP_simple [unrest]
declare UNREST_SubstP_alt [unrest]
end
end