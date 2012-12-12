(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Substitution *}

theory utp_subst
imports utp_pred "../tactics/utp_pred_tac"
begin

context PRED
begin

subsection {* Variable Substitution *}

text {* Substitutions are total bijections that respect typing. *}

definition VAR_SUBST :: "('TYPE VAR \<Rightarrow> 'TYPE VAR) set" where
"VAR_SUBST = {ss . bij ss \<and> (\<forall> v . type (ss v) = type v)}"

text {* Variable substitutions confined to a set of variables. *}

definition VAR_SUBST_ON ::
  "('TYPE VAR) set \<Rightarrow> ('TYPE VAR \<Rightarrow> 'TYPE VAR) set" where
"VAR_SUBST_ON vs =
 {ss . ss \<in> VAR_SUBST \<and> (\<forall> v . v \<notin> vs \<longrightarrow> ss v = v)}"

text {* Variable substitutions that are also involutions. *}

definition VAR_SUBST_INV :: "('TYPE VAR \<Rightarrow> 'TYPE VAR) set" where
"VAR_SUBST_INV = {ss . ss \<in> VAR_SUBST \<and> ss = inv ss}"

subsection {* Binding Substitution *}

definition SubstB ::
  "('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING" where
"\<lbrakk>ss \<in> VAR_SUBST; b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b = b \<circ> (inv ss)"

subsection {* Predicate Substitution *}

definition SubstP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" ("_[_]" [200]) where
"\<lbrakk>ss \<in> VAR_SUBST; p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 SubstP p ss = (SubstB ss) ` p"

subsection {* Substitution builder *}

definition MapSubst :: 
  "('TYPE VAR \<rightharpoonup> 'TYPE VAR) \<Rightarrow>
   ('TYPE VAR \<Rightarrow> 'TYPE VAR)" where
"MapSubst f = the \<circ> (Some ++ (map_inv f ++ f))"

definition SubstPMap :: 
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow> 
   ('TYPE VAR \<rightharpoonup> 'TYPE VAR) \<Rightarrow> 
   ('VALUE, 'TYPE) PREDICATE" ("_\<^bsup>_\<^esup>" [200]) where
"SubstPMap p ss \<equiv> SubstP p (MapSubst ss)"

subsection {* Theorems *}

subsubsection {* Auxiliary Theorems *}

theorem bij_comp_inject [simp] :
"bij g \<Longrightarrow> (f1 \<circ> g = f2 \<circ> g) = (f1 = f2)"
apply (safe)
apply (rule ext)
apply (subgoal_tac "\<exists> y . x = g y")
apply (clarify)
apply (drule_tac x = "y" in fun_cong)
apply (auto)
apply (simp add: bij_def surj_def)
done

declare bij_imp_bij_inv [simp, intro!]

subsubsection {* @{term "MapSubst"} theorems *}

lemma MapSubst_empty[simp]:
  "MapSubst empty = id"
  by (auto simp add:MapSubst_def)

lemma MapSubst_fwd [simp]:
  "x \<in> dom f \<Longrightarrow> MapSubst f x = the (f x)"
  by (simp add:MapSubst_def)

lemma MapSubst_bwd [simp]: 
  "\<lbrakk>x \<notin> dom f; x \<in> ran f\<rbrakk> \<Longrightarrow> MapSubst f x = the (map_inv f x)"
  by (simp add:MapSubst_def)

lemma MapSubst_copy [simp]:
  "\<lbrakk>x \<notin> dom f; x \<notin> ran f\<rbrakk> \<Longrightarrow> MapSubst f x = x"
  by (simp add:MapSubst_def)

lemma MapSubst_bij [intro]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "set xs \<inter> set ys = {}"
  shows "bij (MapSubst [xs [\<mapsto>] ys])"
proof (unfold MapSubst_def, rule bij_map_Some, rule bij_completed_map)

  from assms 
  have ran_dist: "ran (map_inv [xs [\<mapsto>] ys] ++ [xs [\<mapsto>] ys]) = 
                  ran [xs [\<mapsto>] ys] \<union> ran (map_inv [xs [\<mapsto>] ys])"
    by (force intro!:ran_map_add)

  from assms have minj:"inj_on [xs [\<mapsto>] ys] (set xs)"
    by (rule maplets_distinct_inj)

  with assms show "dom (map_inv [xs [\<mapsto>] ys] ++ [xs [\<mapsto>] ys]) =
                   ran (map_inv [xs [\<mapsto>] ys] ++ [xs [\<mapsto>] ys])"
    by (unfold ran_dist, force)

  from assms show "inj_on (map_inv [xs [\<mapsto>] ys] ++ [xs [\<mapsto>] ys])
                          (dom (map_inv [xs [\<mapsto>] ys] ++ [xs [\<mapsto>] ys]))"
    apply (simp only:dom_map_add dom_map_inv)
    apply (rule map_self_adjoin_complete)
    apply (simp_all add:minj)
  done
qed

lemma MapSubst_inj [intro]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "set xs \<inter> set ys = {}"
  shows "inj (MapSubst [xs [\<mapsto>] ys])"
  by (metis MapSubst_bij assms bij_betw_imp_inj_on)

lemma MapSubst_image_out [simp]:
  "\<lbrakk> length xs = length ys; distinct xs; vs \<inter> (set xs \<union> set ys) = {} \<rbrakk> \<Longrightarrow>
       MapSubst [xs [\<mapsto>] ys] ` vs = vs"
  apply (auto)
  apply (subgoal_tac "xa \<notin> ran [xs [\<mapsto>] ys]")
  apply (subgoal_tac "xa \<notin> dom [xs [\<mapsto>] ys]")
  apply (simp)
  apply (force)
  apply (force)
  apply (simp add:image_def)
  apply (rule_tac x="x" in bexI)
  apply (subgoal_tac "x \<notin> ran [xs [\<mapsto>] ys]")
  apply (subgoal_tac "x \<notin> dom [xs [\<mapsto>] ys]")
  apply (auto)
done

lemma list_set_index_elim [elim]:
  "\<lbrakk> v \<in> set xs; \<And>i. \<lbrakk> xs!i = v; i < length xs \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis in_set_conv_nth)

lemma MapSubst_image_fwd [simp]:
  assumes "length xs = length ys" "distinct xs" "vs \<subseteq> set xs" "set xs \<inter> set ys = {}"
  shows "MapSubst [xs [\<mapsto>] ys] ` vs = the ` [xs [\<mapsto>] ys] ` (set xs \<inter> vs)"
using assms proof (auto)
  fix x
  assume assms':"x \<in> set xs" "x \<in> vs"
  
  moreover then obtain i where "x = xs!i" "i < length xs"
    by (auto)

  ultimately show "the ([xs [\<mapsto>] ys] x) \<in> MapSubst [xs [\<mapsto>] ys] ` vs" using assms
    apply (simp add:image_def)
    apply (rule_tac x="x" in bexI)
    apply (simp_all)
  done
qed

lemma MapSubst_image_bwd [simp]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "vs \<subseteq> set ys" "set xs \<inter> set ys = {}"
  shows "MapSubst [xs [\<mapsto>] ys] ` vs = the ` [ys [\<mapsto>] xs] ` (set ys \<inter> vs)"
using assms
  apply (auto)
  apply (subgoal_tac "xa \<in> ran [xs [\<mapsto>] ys]")
  apply (subgoal_tac "xa \<notin> dom [xs [\<mapsto>] ys]")
  apply (auto)
  apply (simp add:image_def)
  apply (rule_tac x="xb" in bexI)
  apply (simp_all)
  apply (subgoal_tac "xb \<in> ran [xs [\<mapsto>] ys]")
  apply (subgoal_tac "xb \<notin> dom [xs [\<mapsto>] ys]")
  apply (auto)
done

lemma MapSubst_image [simp]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "set xs \<inter> set ys = {}"
  shows "MapSubst [xs [\<mapsto>] ys] ` vs = vs - (set xs \<union> set ys) 
                              \<union> the ` [xs [\<mapsto>] ys] ` (set xs \<inter> vs)
                              \<union> the ` [ys [\<mapsto>] xs] ` (set ys \<inter> vs)"
proof -
  have "MapSubst [xs [\<mapsto>] ys] ` vs = 
        MapSubst [xs [\<mapsto>] ys] ` (vs - (set xs \<union> set ys)) \<union> 
        MapSubst [xs [\<mapsto>] ys] ` (vs \<inter> set xs) \<union>
        MapSubst [xs [\<mapsto>] ys] ` (vs \<inter> set ys)"
    apply (subgoal_tac "vs = (vs - (set xs \<union> set ys)) \<union> (vs \<inter> set xs) \<union> (vs \<inter> set ys)")
    apply (metis image_Un)
    apply (force)
  done

  moreover have "MapSubst [xs [\<mapsto>] ys] ` (vs - (set xs \<union> set ys)) = vs - (set xs \<union> set ys)"
    apply (rule MapSubst_image_out)
    apply (simp_all add:assms)
    apply (force)
  done

  ultimately show ?thesis using assms
    by (force)
qed


subsubsection {* Variable Substitution *}

text {* Theorems about @{term "VAR_SUBST"} *}

theorem VAR_SUBST_bij [dest] :
"ss \<in> VAR_SUBST \<Longrightarrow> bij ss"
apply (simp add: VAR_SUBST_def)
done

theorem VAR_SUBST_id [closure]:
"id \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
done

theorem VAR_SUBST_inv [closure] :
"ss \<in> VAR_SUBST \<Longrightarrow> (inv ss) \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (safe)
apply (drule_tac x = "inv ss v" in spec)
apply (erule subst)
apply (simp add: bij_def surj_f_inv_f)
done

theorem VAR_SUBST_compose [closure]:
"\<lbrakk>ss1 \<in> VAR_SUBST;
 ss2 \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 ss1 \<circ> ss2 \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (clarify)
apply (simp add: bij_comp)
done

theorem VAR_SUBST_WF_BINDING [closure] :
"\<lbrakk>b \<in> WF_BINDING;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 b \<circ> ss \<in> WF_BINDING"
apply (simp add: VAR_SUBST_def WF_BINDING_def)
apply (safe)
apply (drule_tac x = "ss v" in spec)
apply (drule_tac x = "v" in spec)
apply (auto)
done

theorem VAR_SUBST_inject [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> (f1 \<circ> ss = f2 \<circ> ss) = (f1 = f2)"
apply (drule VAR_SUBST_bij)
apply (simp)
done

theorem VAR_SUBST_inv_inv [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> inv (inv ss) = ss"
apply (simp add: VAR_SUBST_def)
apply (simp add: inv_inv_eq)
done

theorem VAR_SUBST_comp_inv [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> ss \<circ> inv ss = id"
apply (drule VAR_SUBST_bij)
apply (rule ext)
apply (clarsimp)
apply (simp add: surj_f_inv_f bij_def)
done

theorem VAR_SUBST_inv_comp [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> inv ss \<circ> ss = id"
apply (drule VAR_SUBST_bij)
apply (rule ext)
apply (clarsimp)
apply (simp add: bij_def inv_f_f)
done

theorem VAR_SUBST_inv_distr [simp] :
"\<lbrakk>ss1 \<in> VAR_SUBST;
 ss2 \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 inv (ss1 \<circ> ss2) = (inv ss2) \<circ> (inv ss1)"
apply (drule VAR_SUBST_bij)
apply (drule VAR_SUBST_bij)
apply (simp add: o_inv_distrib)
done

theorem VAR_SUBST_ss_inv_app [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> ss (inv ss x) = x"
apply (simp add: VAR_SUBST_def)
apply (simp add: surj_f_inv_f bij_def)
done

theorem VAR_SUBST_inv_ss_app [simp] :
"ss \<in> VAR_SUBST \<Longrightarrow> inv ss (ss x) = x"
apply (simp add: VAR_SUBST_def)
apply (simp add: inv_f_f bij_def)
done

theorem VAR_SUBST_image_comp [simp] :
"\<lbrakk>ss1 \<in> VAR_SUBST;
 ss2 \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 ss1 ` ss2 ` vs = (ss1 \<circ> ss2) ` vs"
apply (simp add: image_def)
apply (auto)
done

theorem VAR_SUBST_in_image [simp] :
"\<lbrakk>ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow> ss x \<in> (ss ` a) = (x \<in> a)"
apply (simp add: VAR_SUBST_def)
apply (auto simp: bij_def inj_eq)
done

lemma VAR_SUBST_MapSubst [closure]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" 
          "set xs \<inter> set ys = {}" "\<forall>i<length xs. type (xs!i) = type (ys!i)"
  shows "MapSubst [xs [\<mapsto>] ys] \<in> VAR_SUBST"
proof -

  from assms  have "\<And> v. type (MapSubst [xs [\<mapsto>] ys] v) = type v"
    apply (case_tac "v \<in> set xs")
    apply (erule list_set_index_elim)
    apply (auto)
    apply (case_tac "v \<in> set ys")
    apply (erule list_set_index_elim)
    apply (auto)
  done

  with assms show ?thesis
    by (auto simp add:VAR_SUBST_def)
qed

text {* Theorems about @{term "VAR_SUBST_ON"} *}

theorem VAR_SUBST_ON_bij [dest] :
"ss \<in> VAR_SUBST_ON vs \<Longrightarrow> bij ss"
apply (simp add: VAR_SUBST_ON_def VAR_SUBST_def)
done

theorem VAR_SUBST_ON_VAR_SUBST [closure] :
"ss \<in> VAR_SUBST_ON vs \<Longrightarrow> ss \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_ON_def)
done

theorem VAR_SUBST_ON_id [closure]:
"id \<in> VAR_SUBST_ON vs"
apply (simp add: VAR_SUBST_ON_def VAR_SUBST_id)
done

theorem VAR_SUBST_ON_inv [closure] :
"ss \<in> VAR_SUBST_ON vs \<Longrightarrow>
 (inv ss) \<in> VAR_SUBST_ON vs"
apply (simp add: VAR_SUBST_ON_def)
apply (simp add: closure)
apply (safe)
apply (drule_tac x = "v" in spec)
apply (clarify)
apply (drule sym)
apply (erule ssubst)
back back
apply (simp)
done

text {* Should the following three theorems be default simplifications? *}

text {* This causes a loop though when simplifying @{term VAR_SUBST_ON}. *}

theorem VAR_SUBST_ON_app_simp :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<notin> vs\<rbrakk> \<Longrightarrow> ss x = x"
apply (simp add: VAR_SUBST_ON_def)
done

theorem VAR_SUBST_ON_app_member :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<in> vs\<rbrakk> \<Longrightarrow> ss x \<in> vs"
apply (simp only: VAR_SUBST_ON_def)
apply (clarify)
apply (drule VAR_SUBST_bij)
apply (simp add: bij_def)
apply (clarify)
apply (case_tac "ss x \<in> vs")
apply (assumption)
apply (drule_tac x = "ss x" in spec)
apply (clarify)
apply (subgoal_tac "ss x = x")
apply (auto dest: injD)
done

theorem VAR_SUBST_ON_app_not_member :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<notin> vs\<rbrakk> \<Longrightarrow> ss x \<notin> vs"
apply (simp only: VAR_SUBST_ON_def)
apply (clarify)
apply (drule VAR_SUBST_bij)
apply (simp add: bij_def)
done

theorem VAR_SUBST_ON_image [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1\<rbrakk> \<Longrightarrow>
 ss ` vs1 = vs1"
apply (simp add: image_def)
apply (safe)
apply (simp add: VAR_SUBST_ON_app_member)
apply (rule_tac x = "inv ss x" in bexI)
apply (simp add: VAR_SUBST_ON_VAR_SUBST)
apply (subgoal_tac "ss x \<in> vs1")
apply (drule VAR_SUBST_ON_inv)
apply (simp add: VAR_SUBST_ON_app_member)
apply (simp add: VAR_SUBST_ON_app_member)
done

theorem VAR_SUBST_ON_disj_image [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss ` vs2 = vs2"
apply (simp add: VAR_SUBST_ON_def)
apply (clarify)
apply (simp add: image_def)
apply (safe)
apply (auto) [1]
apply (rule_tac x = "x" in bexI)
apply (auto)
done

theorem VAR_SUBST_ON_commute :
"\<lbrakk>ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss1 \<circ> ss2 = ss2 \<circ> ss1"
apply (rule ext)
apply (simp)
apply (case_tac "x \<notin> vs1")
apply (simp add: VAR_SUBST_ON_app_simp)
apply (case_tac "x \<in> vs2")
apply (subgoal_tac "ss2 x \<notin> vs1")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "ss2 x \<in> vs2")
apply (auto) [1]
apply (simp add: VAR_SUBST_ON_app_member)
apply (case_tac "x \<notin> vs2")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "ss1 x \<notin> vs2")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "ss1 x \<in> vs1")
apply (auto) [1]
apply (simp add: VAR_SUBST_ON_app_member)
apply (auto)
done

text {* Theorems about @{term "VAR_SUBST_INV"} *}

theorem VAR_SUBST_INV_bij [dest] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> bij ss"
apply (simp add: VAR_SUBST_INV_def VAR_SUBST_def)
done

theorem VAR_SUBST_INV_VAR_SUBST [closure] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> ss \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_INV_def)
done

theorem VAR_SUBST_INV_inv_closure [closure] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> (inv ss) \<in> VAR_SUBST_INV"
apply (simp add: VAR_SUBST_INV_def)
done

text {* Should the following theorem be a default simplifications? *}

text {* This causes a loop though when simplifying @{term VAR_SUBST_INV}. *}

theorem VAR_SUBST_INV_inv :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> (inv ss) = ss"
apply (simp add: VAR_SUBST_INV_def)
done

theorem VAR_SUBST_INV_comp [simp] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> (ss \<circ> ss) = id"
apply (simp add: VAR_SUBST_INV_def)
apply (clarify)
apply (erule ssubst) back
apply (simp)
done

theorem VAR_SUBST_INV_app [simp] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> ss (ss x) = x"
apply (simp add: sym [OF o_apply])
done

subsubsection {* Binding Substitution *}

theorem SubstB_closure [closure] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b \<in> WF_BINDING"
apply (simp add: SubstB_def closure)
done

theorem SubstB_inject [simp]:
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 (SubstB ss b1 = SubstB ss b2) = (b1 = b2)"
apply (simp add: SubstB_def)
apply (simp add: VAR_SUBST_def)
done

theorem SubstB_id [simp] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB id b = b"
apply (simp add: SubstB_def closure)
done

theorem SubstB_compose :
"\<lbrakk>ss1 \<in> VAR_SUBST; ss2 \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss1 (SubstB ss2 b) = SubstB (ss1 \<circ> ss2) b"
apply (subgoal_tac "SubstB ss2 b \<in> WF_BINDING")
apply (simp add: SubstB_def closure)
apply (simp add: o_assoc)
apply (simp add: closure)
done

theorem SubstB_commute :
"\<lbrakk>ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {};
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss1 (SubstB ss2 b) = SubstB ss2 (SubstB ss1 b)"
apply (simp add: SubstB_compose VAR_SUBST_ON_VAR_SUBST)
apply (subgoal_tac "ss1 \<circ> ss2 = ss2 \<circ> ss1")
apply (simp)
apply (auto intro: VAR_SUBST_ON_commute)
done

theorem SubstB_inv_cancel1 [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB (inv ss) (SubstB ss b) = b"
apply (subgoal_tac "SubstB ss b \<in> WF_BINDING")
apply (simp add: SubstB_def closure)
apply (rule ext)
apply (simp_all add: closure)
done

theorem SubstB_inv_cancel2 [simp] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss (SubstB (inv ss) b) = b"
apply (subgoal_tac "SubstB (inv ss) b \<in> WF_BINDING")
apply (simp add: SubstB_def closure)
apply (rule ext)
apply (simp_all add: closure)
done

theorem SubstB_override_distr1 :
"\<lbrakk>ss \<in> VAR_SUBST;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss (b1 \<oplus> b2 on vs) = (SubstB ss b1) \<oplus> (SubstB ss b2) on (ss ` vs)"
apply (simp add: SubstB_def closure)
apply (simp add: override_on_def)
apply (rule ext)
apply (clarsimp)
apply (safe)
apply (subgoal_tac "a = ss (inv ss a)")
apply (simp_all)
done

theorem SubstB_override_distr2 :
"\<lbrakk>ss \<in> VAR_SUBST;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 (SubstB ss b1) \<oplus> (SubstB ss b2) on (ss ` vs) = SubstB ss (b1 \<oplus> b2 on vs)"
apply (simp add: SubstB_override_distr1)
done

theorem SubstB_override_distr3 :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 SubstB ss (b1 \<oplus> b2 on vs2) = (SubstB ss b1) \<oplus> (SubstB ss b2) on vs2"
apply (subst SubstB_override_distr1 [of ss b1 b2 vs2])
apply (simp_all add: closure)
done

theorem SubstB_override_distr4 :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (SubstB ss b1) \<oplus> (SubstB ss b2) on vs2 = SubstB ss (b1 \<oplus> b2 on vs2)"
apply (simp add: SubstB_override_distr3)
done

theorem SubstB_involution [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_INV;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss (SubstB ss b) = b"
apply (subgoal_tac "ss \<circ> ss = id")
apply (drule VAR_SUBST_INV_VAR_SUBST)
apply (simp add: SubstB_compose)
apply (simp)
done

subsubsection {* Predicate Substitution *}

theorem SubstP_closure [closure] :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss] \<in> WF_PREDICATE"
apply (simp add: SubstP_def)
apply (simp add: WF_PREDICATE_def)
apply (safe)
apply (subgoal_tac "xa \<in> WF_BINDING")
apply (simp add: closure)
apply (auto)
done

theorem SubstPMap_single_closure [closure]:
  "\<lbrakk> p \<in> WF_PREDICATE; x \<noteq> y; type x = type y \<rbrakk> \<Longrightarrow> p\<^bsup>[x \<mapsto> y] \<^esup>\<in> WF_PREDICATE"
  apply (simp add:SubstPMap_def)
  apply (rule closure, simp)
  apply (rule VAR_SUBST_MapSubst[of "[x]" "[y]",simplified])
  apply (auto)
done

theorem EvalP_SubstP [eval] :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 \<lbrakk>p[ss]\<rbrakk>b = \<lbrakk>p\<rbrakk>(SubstB (inv ss) b)"
apply (simp add: EvalP_def)
apply (simp add: SubstP_def)
apply (simp add: image_def)
apply (safe)
apply (simp)
apply (rule_tac x = "SubstB (inv ss) b" in bexI)
apply (simp)
apply (assumption)
done

theorem SubstP_id :
"p \<in> WF_PREDICATE \<Longrightarrow> p[id] = p"
apply (utp_pred_auto_tac)
done

theorem SubstP_inverse1 :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss][inv ss] = p"
apply (utp_pred_auto_tac)
done

theorem SubstP_inverse2 :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[inv ss][ss] = p"
apply (utp_pred_auto_tac)
done

theorem SubstP_compose :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss1 \<in> VAR_SUBST;
 ss2 \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss1][ss2] = p[ss2 \<circ> ss1]"
apply (utp_pred_tac)
apply (simp add: SubstB_compose closure)
done

theorem SubstP_commute :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 p[ss1][ss2] = p[ss2][ss1]"
apply (utp_pred_tac)
apply (clarify)
apply (subst SubstB_commute [of "(inv ss1)" "vs1" "(inv ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

theorem SubstP_involution [simp] :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_SUBST_INV\<rbrakk> \<Longrightarrow>
 p[ss][ss] = p"
apply (utp_pred_auto_tac)
done

end
end