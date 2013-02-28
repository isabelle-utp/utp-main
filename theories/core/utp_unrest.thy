(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_unrest.thy                                                       *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Unrestricted Variables *}

theory utp_unrest
imports utp_pred utp_rename
begin

subsection {* Theorem Attributes *}

ML {*
  structure unrest =
    Named_Thms (val name = @{binding unrest} val description = "unrest theorems")
*}

setup unrest.setup

subsubsection {* @{term UNREST} Function *}

definition UNREST ::
  "('VALUE VAR) set \<Rightarrow> 'VALUE WF_PREDICATE \<Rightarrow> bool" where
"UNREST vs p \<longleftrightarrow> (\<forall> b1 \<in> destPRED p . \<forall> b2. b1 \<oplus>\<^sub>b b2 on vs \<in> destPRED p)"

subsubsection {* Restricted variables *}

definition rv :: 
  "'VALUE WF_PREDICATE \<Rightarrow> ('VALUE VAR) set" where
"rv p = - (GREATEST vs. UNREST vs p)"

subsubsection {* Fresh variables *}

definition fresh_var :: "'VALUE WF_PREDICATE \<Rightarrow> 'VALUE UTYPE \<Rightarrow> 'VALUE VAR" where
"fresh_var p t \<equiv> SOME x. UNREST {x} p \<and> vtype x = t"

subsubsection {* Restricted Predicates *}

definition WF_PREDICATE_OVER ::
  "('VALUE VAR) set \<Rightarrow>
   'VALUE WF_PREDICATE set" where
"WF_PREDICATE_OVER vs = {p . UNREST (VAR - vs) p}"

subsubsection {* Theorems *}

theorem UNREST_binding_override [intro] :
"\<lbrakk>b \<in> destPRED p; UNREST vs p\<rbrakk> \<Longrightarrow>
 (b \<oplus>\<^sub>b b' on vs) \<in> destPRED p"
apply (simp add: UNREST_def)
done

theorem UNREST_empty :
"UNREST {} p"
apply (simp add: UNREST_def)
done

theorem UNREST_subset :
"\<lbrakk>UNREST vs1 p;
 vs2 \<subseteq> vs1\<rbrakk> \<Longrightarrow>
 UNREST vs2 p"
apply (simp add: UNREST_def)
apply (clarify)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (drule_tac x = "b2 \<oplus>\<^sub>b b1 on (vs1 - vs2)" in spec)
apply (simp add: closure)
apply (subgoal_tac "vs1 - (vs1 - vs2) = vs2")
apply (simp)
apply (auto)
done

theorem UNREST_union :
"\<lbrakk>UNREST vs1 p;
 UNREST vs2 p\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<union> vs2) p"
apply (simp add: UNREST_def)
apply (clarify)
apply (metis binding_override_simps(1))
done

theorem UNREST_LiftP :
"\<lbrakk>f \<in> WF_BINDING_PRED vs\<rbrakk> \<Longrightarrow>
 UNREST (VAR - vs) (LiftP f)"
apply (simp add: UNREST_def LiftP_def)
apply (simp add: WF_BINDING_PRED_def)
apply (auto)
apply (drule_tac x = "b1" in spec, auto)
apply (drule_tac x = "b1 \<oplus>\<^sub>b b2 on (VAR - vs)" in spec)
apply (simp add: binding_equiv_def)
done

theorem UNREST_EqualsP :
"UNREST (VAR - {v}) (v =p x)"
apply (simp add: EqualsP_def)
apply (rule UNREST_LiftP)
apply (simp add: WF_BINDING_PRED_def)
apply (simp add: binding_equiv_def)
done

theorem UNREST_TrueP :
"UNREST vs true"
  by (simp add: UNREST_def TrueP_def)

theorem UNREST_FalseP :
"UNREST vs false"
  by (simp add: UNREST_def FalseP_def)

theorem UNREST_NotP :
"\<lbrakk>UNREST vs p\<rbrakk> \<Longrightarrow>
 UNREST vs (\<not>p p)"
apply (simp add: UNREST_def NotP.rep_eq)
apply (auto)
apply (drule_tac x = "b1 \<oplus>\<^sub>b b2 on vs" in bspec)
apply (assumption)
apply (drule_tac x = "b1" in spec)
apply (simp)
done

theorem UNREST_AndP :
"\<lbrakk>UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<and>p p2)"
  by (simp add: UNREST_def AndP_def)


theorem UNREST_AndP_alt :
"\<lbrakk>UNREST vs1 p1;
 UNREST vs2 p2\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<inter> vs2) (p1 \<and>p p2)"
apply (simp add: UNREST_def AndP_def)
apply (metis Int_iff binding_override_simps(6) inf_commute)
done

theorem UNREST_OrP :
"\<lbrakk>UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<or>p p2)"
  by (auto simp add: UNREST_def OrP_def)

theorem UNREST_ImpliesP :
"\<lbrakk>UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<Rightarrow>p p2)"
apply (simp add: ImpliesP_def)
apply (auto intro: UNREST_OrP UNREST_NotP closure)
done

theorem UNREST_IffP :
"\<lbrakk>UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<Leftrightarrow>p p2)"
apply (simp add: IffP_def)
apply (auto intro: UNREST_ImpliesP UNREST_AndP closure)
done

theorem UNREST_ExistsP :
"\<lbrakk>UNREST vs1 p\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<union> vs2) (\<exists>p vs2 . p)"
apply (simp add: UNREST_def ExistsP_def)
apply (clarify)
apply (simp)
apply (rule_tac x = "b1a \<oplus>\<^sub>b b2 on vs1" in exI)
apply (simp)
apply (rule_tac x = "b2" in exI)
apply (simp)
apply (metis (hide_lams, no_types) binding_override_simps(1) binding_override_simps(3) sup.commute)
done

theorem UNREST_ForallP :
"\<lbrakk>UNREST vs1 p\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<union> vs2) (\<forall>p vs2 . p)"
apply (simp add: ForallP_def)
apply (auto intro: UNREST_ExistsP UNREST_NotP closure)
done

theorem UNREST_ExistsP_simple :
"\<lbrakk>vs1 \<subseteq> vs2\<rbrakk> \<Longrightarrow>
 UNREST vs1 (\<exists>p vs2 . p)"
apply (insert UNREST_ExistsP [of "{}" "p" "vs2"])
apply (simp add: UNREST_empty)
apply (auto intro: UNREST_subset closure)
done

theorem UNREST_ForallP_simple :
"\<lbrakk>vs1 \<subseteq> vs2\<rbrakk> \<Longrightarrow>
 UNREST vs1 (\<forall>p vs2 . p)"
apply (insert UNREST_ForallP [of "{}" "p" "vs2"])
apply (simp add: UNREST_empty)
apply (auto intro: UNREST_subset closure)
done

theorem UNREST_ClosureP :
"UNREST VAR [p]p"
apply (simp add: ClosureP_def)
apply (insert UNREST_ForallP [of "{}" "p" "VAR"])
apply (simp add: UNREST_empty)
done

theorem UNREST_RefP :
"UNREST VAR (p1 \<sqsubseteq>p p2)"
apply (simp add: RefP_def)
apply (auto intro: UNREST_ClosureP closure)
done

theorem UNREST_RenameP :
"UNREST vs p \<Longrightarrow>
 UNREST (\<langle>ss\<rangle>\<^sub>s ` vs) p[ss]"
apply (simp add: UNREST_def)
apply (simp add: RenameP_def)
apply (safe)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (drule_tac x = "RenameB (inv\<^sub>s ss) b2" in spec)
apply (drule imageI [where f = "RenameB ss"]) back
apply (simp add: RenameB_override_distr1 closure)
done

subsubsection {* Proof Support *}

theorem UNREST_LiftP_alt :
"\<lbrakk>f \<in> WF_BINDING_PRED vs1;
 vs2 \<subseteq> VAR - vs1\<rbrakk> \<Longrightarrow>
 UNREST vs2 (LiftP f)"
apply (auto intro: UNREST_LiftP UNREST_subset simp: closure)
done

theorem UNREST_ExistsP_alt :
"\<lbrakk>UNREST vs1 p;
 vs3 \<subseteq> vs1 \<union> vs2\<rbrakk> \<Longrightarrow>
 UNREST vs3 (\<exists>p vs2 . p)"
apply (auto intro: UNREST_ExistsP UNREST_subset simp: closure)
done

theorem UNREST_ExistsP_minus :
"\<lbrakk>UNREST (vs1 - vs2) p\<rbrakk> \<Longrightarrow>
 UNREST vs1 (\<exists>p vs2 . p)"
apply (auto intro: UNREST_ExistsP UNREST_subset simp: closure)
done

theorem UNREST_ForallP_alt :
"\<lbrakk>UNREST vs1 p;
 vs3 \<subseteq> vs1 \<union> vs2\<rbrakk> \<Longrightarrow>
 UNREST vs3 (\<forall>p vs2 . p)"
apply (auto intro: UNREST_ForallP UNREST_subset simp: closure)
done

theorem UNREST_RenameP_alt :
"\<lbrakk>UNREST vs1 p;
 vs2 \<subseteq> (\<langle>ss\<rangle>\<^sub>s ` vs1)\<rbrakk> \<Longrightarrow>
 UNREST vs2 p[ss]"
apply (auto intro: UNREST_RenameP UNREST_subset simp: closure)
done

theorem UNREST_RenameP_single :
"\<lbrakk> x \<noteq> y; vtype x = vtype y; aux x = aux y; x \<in> vs; y \<notin> vs;
   UNREST ((vs - {x}) \<union> {y})  p \<rbrakk> \<Longrightarrow> 
   UNREST vs p\<^bsup>[x \<mapsto> y]\<^esup>"
  apply (simp add:RenamePMap_def)
  apply (rule UNREST_RenameP_alt)
  apply (simp)
  apply (simp add:closure)
  apply (simp add: MapR_rep_eq[of "[x]" "[y]", simplified])
  apply (simp add: MapRename_image[of "[x]" "[y]" "(vs - {x})",simplified])
  apply (force)
done

(*
theorem UNREST_RenameP_single :
"\<lbrakk> x \<noteq> y; vtype x = vtype y; aux x = aux y;
   UNREST {y} p \<rbrakk> \<Longrightarrow> 
   UNREST {x} p\<^bsup>[x \<mapsto> y]\<^esup>"
  apply (simp add:RenamePMap_def)
  apply (rule UNREST_RenameP_alt)
  apply (auto simp add:closure)
done
*)

theorem UNREST_fresh_var: 
  "\<exists> v. UNREST {v} p \<and> vtype v = t \<Longrightarrow> UNREST {fresh_var p t} p"
  apply (auto simp add:fresh_var_def)
  apply (smt someI_ex)
done

text {* A predicate unrestricted on all variables is either true or false *}

theorem UNREST_true_false: 
  "UNREST VAR p \<Longrightarrow> p = true \<or> p = false"
  by (auto simp add:UNREST_def TrueP_def FalseP_def)

declare UNREST_empty [unrest]
declare UNREST_subset [unrest]
declare UNREST_union [unrest]
declare UNREST_LiftP_alt [unrest]
declare UNREST_EqualsP [unrest]
declare UNREST_TrueP [unrest]
declare UNREST_FalseP [unrest]
declare UNREST_NotP [unrest]
declare UNREST_AndP [unrest]
declare UNREST_AndP_alt [unrest]
declare UNREST_OrP [unrest]
declare UNREST_ImpliesP [unrest]
declare UNREST_IffP [unrest]
declare UNREST_ExistsP_alt [unrest]
declare UNREST_ExistsP_minus [unrest]
declare UNREST_ForallP_alt [unrest]
declare UNREST_ExistsP_simple [unrest]
declare UNREST_ForallP_simple [unrest]
declare UNREST_ClosureP [unrest]
declare UNREST_RefP [unrest]
declare UNREST_RenameP_alt [unrest]
declare UNREST_RenameP_single [unrest]
declare UNREST_fresh_var [unrest]

end
