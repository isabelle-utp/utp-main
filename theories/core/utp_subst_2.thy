(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Substitution *}

theory utp_subst_2
imports utp_pred_2 "../tactics/utp_pred_tac_2"
begin

subsection {* Variable Substitution *}

text {* Substitutions are total bijections that respect typing. *}

definition VAR_SUBST :: "('VALUE VAR \<Rightarrow> 'VALUE VAR) set" where
"VAR_SUBST = {ss . bij ss \<and> (\<forall> v . type (ss v) = type v \<and> control (ss v) = control v)}"

typedef (open) 'VALUE VAR_SUBST = "VAR_SUBST :: ('VALUE VAR \<Rightarrow> 'VALUE VAR) set"
  by (auto simp add:VAR_SUBST_def)

declare Rep_VAR_SUBST [simp]
declare Rep_VAR_SUBST_inverse [simp]
declare Abs_VAR_SUBST_inverse [simp]

lemma Rep_VAR_SUBST_intro [intro]:
  "Rep_VAR_SUBST x = Rep_VAR_SUBST y \<Longrightarrow> x = y"
  by (simp add:Rep_VAR_SUBST_inject)

lemma Rep_VAR_SUBST_elim [elim]:
  "\<lbrakk> x = y; Rep_VAR_SUBST x = Rep_VAR_SUBST y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_VAR_SUBST

notation Rep_VAR_SUBST ("\<langle>_\<rangle>\<^sub>s")

lemma Rep_VAR_SUBST_bij [simp]: "bij \<langle>ss\<rangle>\<^sub>s"
  apply (insert Rep_VAR_SUBST[of ss])
  apply (simp add:VAR_SUBST_def)
done

lemma Rep_VAR_SUBST_inj [simp]: "inj \<langle>ss\<rangle>\<^sub>s"
  by (metis (lifting) Rep_VAR_SUBST_bij bij_def)

lemma Rep_VAR_SUBST_surj [simp]: "surj \<langle>ss\<rangle>\<^sub>s"
  by (metis Rep_VAR_SUBST_bij bij_betw_def)

subsection {* Substitution builder *}

definition MapSubst :: 
  "('VALUE VAR \<rightharpoonup> 'VALUE VAR) \<Rightarrow>
    'VALUE VAR \<Rightarrow> 'VALUE VAR" where
"MapSubst f = the \<circ> (Some ++ (map_inv f ++ f))"

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
  "x \<in> dom f \<Longrightarrow> (MapSubst f) x = the (f x)"
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

(*
(* This is a long and incredibly boring proof, so I can't be bothered with it right now *)
theorem MapSubst_inv [simp]: 
  "inj_on f (dom f) \<Longrightarrow> inv (MapSubst f) = MapSubst (map_inv f)"
  apply (auto simp add:MapSubst_def)
  apply (rule_tac ext)
  apply (simp)
sorry
*)

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
apply (clarify)
apply (erule subst)
apply (simp_all add: bij_def surj_f_inv_f)
apply (metis surj_f_inv_f)
apply (metis surj_f_inv_f)
done

theorem VAR_SUBST_compose [closure]:
"\<lbrakk>ss1 \<in> VAR_SUBST;
 ss2 \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 ss1 \<circ> ss2 \<in> VAR_SUBST"
apply (simp add: VAR_SUBST_def)
apply (clarify)
apply (simp add: bij_comp)
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

subsubsection {* Derived substitution operators *}

definition subst_comp :: 
  "'VALUE VAR_SUBST \<Rightarrow> 'VALUE VAR_SUBST \<Rightarrow> 'VALUE VAR_SUBST" (infixl "\<circ>\<^sub>s" 55) where 
"subst_comp x y = Abs_VAR_SUBST (\<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s)"

lemma subst_comp_rep_eq [simp]:
  "\<langle>x \<circ>\<^sub>s y\<rangle>\<^sub>s = \<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s"
  apply (subgoal_tac "\<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s \<in> VAR_SUBST")
  apply (simp add: subst_comp_def comp_def)
  apply (simp add:closure)
done

definition subst_inv :: 
  "'VALUE VAR_SUBST \<Rightarrow> 'VALUE VAR_SUBST" ("inv\<^sub>s") where
"inv\<^sub>s ss = Abs_VAR_SUBST (inv \<langle>ss\<rangle>\<^sub>s)"

lemma subst_inv_rep_eq [simp]:
  "\<langle>inv\<^sub>s ss\<rangle>\<^sub>s = inv \<langle>ss\<rangle>\<^sub>s"
  by (simp add:subst_inv_def closure)

definition subst_id :: 
  "'VALUE VAR_SUBST" ("id\<^sub>s") where
"id\<^sub>s = Abs_VAR_SUBST id"

lemma subst_id_rep_eq [simp]:
  "\<langle>id\<^sub>s\<rangle>\<^sub>s = id"
  by (simp add: subst_id_def closure)

lemma subst_inv_id [simp]:
  "inv\<^sub>s id\<^sub>s = id\<^sub>s"
  by force

lemma subst_inv_inv [simp]:
  "inv\<^sub>s (inv\<^sub>s ss) = ss"
  by force

lemma subst_inv_comp [simp]:
  "inv\<^sub>s (ss1 \<circ>\<^sub>s ss2) = inv\<^sub>s ss2 \<circ>\<^sub>s inv\<^sub>s ss1"
  by force

definition subst_image :: 
  "('VALUE VAR_SUBST) \<Rightarrow> 'VALUE VAR set \<Rightarrow> 'VALUE VAR set" (infixr "`\<^sub>s" 90) where
"ss `\<^sub>s vs = \<langle>ss\<rangle>\<^sub>s ` vs"

declare subst_image_def [simp]

text {* More theorems about @{term "VAR_SUBST"} *}

lemma VAR_SUBST_MapSubst [closure]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" 
          "set xs \<inter> set ys = {}" "\<forall>i<length xs. type (xs!i) = type (ys!i) \<and> control (xs!i) = control (ys!i)"
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

  moreover from assms  have "\<And> v. control (MapSubst [xs [\<mapsto>] ys] v) = control v"
    apply (case_tac "v \<in> set xs")
    apply (erule list_set_index_elim)
    apply (force)
    apply (case_tac "v \<in> set ys")
    apply (erule list_set_index_elim)
    apply (auto)
  done


  ultimately show ?thesis using assms
    by (auto simp add:VAR_SUBST_def)
qed

lemma VAR_SUBST_MapSubst_one [closure]:
  "\<lbrakk> type x = type y; control x = control y \<rbrakk> \<Longrightarrow> MapSubst [x \<mapsto> y] \<in> VAR_SUBST"
  apply (case_tac "x \<noteq> y")
  apply (rule VAR_SUBST_MapSubst[of "[x]" "[y]",simplified])
  apply (simp_all)
  apply (simp add:MapSubst_def closure)
done

text {* Variable substitutions confined to a set of variables. *}

definition VAR_SUBST_ON ::
  "('VALUE VAR) set \<Rightarrow> 'VALUE VAR_SUBST set" where
"VAR_SUBST_ON vs =
 {ss. (\<forall> v . v \<notin> vs \<longrightarrow> \<langle>ss\<rangle>\<^sub>s v = v)}"

text {* Variable substitutions that are also involutions. *}

definition VAR_SUBST_INV :: "'VALUE VAR_SUBST set" where
"VAR_SUBST_INV = {ss. ss = inv\<^sub>s ss}"

text {* Theorems about @{term "VAR_SUBST_ON"} *}

theorem VAR_SUBST_ON_inv [closure] :
"ss \<in> VAR_SUBST_ON vs \<Longrightarrow>
 (inv\<^sub>s ss) \<in> VAR_SUBST_ON vs"
apply (auto simp add: VAR_SUBST_ON_def)
apply (drule_tac x = "v" in spec)
apply (auto)
apply (drule sym)
apply (erule ssubst)
back back
apply (simp)
done

text {* Should the following three theorems be default simplifications? *}

text {* This causes a loop though when simplifying @{term VAR_SUBST_ON}. *}

theorem VAR_SUBST_ON_app_simp :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<notin> vs\<rbrakk> \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s x = x"
  by (simp add: VAR_SUBST_ON_def)

theorem VAR_SUBST_ON_app_member :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<in> vs\<rbrakk> \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s x \<in> vs"
apply (simp only: VAR_SUBST_ON_def)
apply (auto)
(*apply (drule VAR_SUBST_bij)
apply (simp add: bij_def)
apply (clarify) *)
apply (case_tac "\<langle>ss\<rangle>\<^sub>s x \<in> vs")
apply (assumption)
apply (drule_tac x = "\<langle>ss\<rangle>\<^sub>s x" in spec)
apply (clarify)
apply (subgoal_tac "\<langle>ss\<rangle>\<^sub>s x = x")
apply (auto dest: injD)
apply (metis Rep_VAR_SUBST VAR_SUBST_in_image)
done

theorem VAR_SUBST_ON_app_not_member :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs; x \<notin> vs\<rbrakk> \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s x \<notin> vs"
apply (simp only: VAR_SUBST_ON_def)
apply (clarify)
apply (simp add: bij_def)
done

theorem VAR_SUBST_ON_image [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1\<rbrakk> \<Longrightarrow>
 ss `\<^sub>s vs1 = vs1"
apply (simp add: image_def)
apply (safe)
apply (simp add: VAR_SUBST_ON_app_member)
apply (rule_tac x = "inv \<langle>ss\<rangle>\<^sub>s x" in bexI)
apply (simp)
apply (subgoal_tac "\<langle>ss\<rangle>\<^sub>s x \<in> vs1")
apply (drule VAR_SUBST_ON_inv)
apply (metis (lifting) VAR_SUBST_ON_app_member subst_inv_rep_eq)
apply (simp add: VAR_SUBST_ON_app_member)
done

theorem VAR_SUBST_ON_disj_image [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss `\<^sub>s vs2 = vs2"
apply (simp add: VAR_SUBST_ON_def)
apply (auto)
apply (simp add: image_def)
apply (rule_tac x = "x" in bexI)
apply (auto)
done

theorem VAR_SUBST_ON_commute :
"\<lbrakk>ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss1 \<circ>\<^sub>s ss2 = ss2 \<circ>\<^sub>s ss1"
apply (rule Rep_VAR_SUBST_intro)
apply (simp)
apply (rule ext)
apply (simp)
apply (case_tac "x \<notin> vs1")
apply (simp add: VAR_SUBST_ON_app_simp)
apply (case_tac "x \<in> vs2")
apply (subgoal_tac "\<langle>ss2\<rangle>\<^sub>s x \<notin> vs1")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "\<langle>ss2\<rangle>\<^sub>s x \<in> vs2")
apply (auto) [1]
apply (simp add: VAR_SUBST_ON_app_member)
apply (case_tac "x \<notin> vs2")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "\<langle>ss1\<rangle>\<^sub>s x \<notin> vs2")
apply (simp_all add: VAR_SUBST_ON_app_simp)
apply (subgoal_tac "\<langle>ss1\<rangle>\<^sub>s x \<in> vs1")
apply (auto) [1]
apply (simp add: VAR_SUBST_ON_app_member)
apply (auto)
done

text {* Theorems about @{term "VAR_SUBST_INV"} *}

theorem VAR_SUBST_INV_inv_closure [closure] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> (inv\<^sub>s ss) \<in> VAR_SUBST_INV"
apply (simp add: VAR_SUBST_INV_def)
done

text {* Should the following theorem be a default simplifications? *}

text {* This causes a loop though when simplifying @{term VAR_SUBST_INV}. *}

theorem VAR_SUBST_INV_inv :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> (inv\<^sub>s ss) = ss"
apply (simp add: VAR_SUBST_INV_def)
done

theorem VAR_SUBST_INV_comp [simp] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> (ss \<circ>\<^sub>s ss) = id\<^sub>s"
apply (simp add: VAR_SUBST_INV_def)
apply (rule Rep_VAR_SUBST_intro)
apply (simp)
apply (erule Rep_VAR_SUBST_elim)
apply (erule ssubst) back
apply (simp)
done

theorem VAR_SUBST_INV_app [simp] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s (\<langle>ss\<rangle>\<^sub>s x) = x"
  by (metis VAR_SUBST_INV_comp id_apply o_eq_dest_lhs subst_comp_rep_eq subst_id_rep_eq)

subsection {* Binding Substitution *}

definition CompB ::   
  "'VALUE WF_BINDING \<Rightarrow>
   'VALUE VAR_SUBST \<Rightarrow>
   'VALUE WF_BINDING" where
"CompB b ss = Abs_WF_BINDING (\<langle>b\<rangle>\<^sub>b \<circ> \<langle>ss\<rangle>\<^sub>s)"

lemma CompB_rep_eq [simp]:
  "\<langle>CompB b ss\<rangle>\<^sub>b = \<langle>b\<rangle>\<^sub>b \<circ> \<langle>ss\<rangle>\<^sub>s"
  by (simp add:CompB_def closure)

definition SubstB ::
  "'VALUE VAR_SUBST \<Rightarrow>
   'VALUE WF_BINDING \<Rightarrow>
   'VALUE WF_BINDING" where
"SubstB ss b = CompB b (inv\<^sub>s ss)"

subsection {* Predicate Substitution *}

lift_definition SubstP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE VAR_SUBST \<Rightarrow>
   'VALUE WF_PREDICATE" ("_[_]" [200]) is
"\<lambda> p ss. (SubstB ss) ` p" done

definition SubstPMap :: 
  "'VALUE  WF_PREDICATE \<Rightarrow> 
   ('VALUE VAR \<rightharpoonup> 'VALUE VAR) \<Rightarrow> 
   'VALUE WF_PREDICATE" ("_\<^bsup>_\<^esup>" [200]) where
"SubstPMap p ss \<equiv> SubstP p (Abs_VAR_SUBST (MapSubst ss))"

subsubsection {* Binding Substitution *}

(*
theorem SubstB_closure [closure] :
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b \<in> WF_BINDING"
apply (simp add: SubstB_def closure)
done
*)

lemma WF_BINDING_VAR_SUBST [closure]: "\<langle>b\<rangle>\<^sub>b \<circ> inv \<langle>ss\<rangle>\<^sub>s \<in> WF_BINDING"
  by (metis Rep_VAR_SUBST Rep_WF_BINDING VAR_SUBST_WF_BINDING VAR_SUBST_inv)

theorem SubstB_inject [simp]:
  "(SubstB ss b1 = SubstB ss b2) = (b1 = b2)"
  by (force simp add:SubstB_def CompB_rep_eq)

theorem SubstB_id [simp] :
"SubstB id\<^sub>s b = b"
  by (auto simp add: SubstB_def CompB_rep_eq closure)


theorem SubstB_compose :
"SubstB ss1 (SubstB ss2 b) = SubstB (ss1 \<circ>\<^sub>s ss2) b"
  by (auto simp add: SubstB_def closure o_assoc CompB_rep_eq)

theorem SubstB_commute :
"\<lbrakk>ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 SubstB ss1 (SubstB ss2 b) = SubstB ss2 (SubstB ss1 b)"
apply (simp add: SubstB_compose)
apply (subgoal_tac "ss1 \<circ>\<^sub>s ss2 = ss2 \<circ>\<^sub>s ss1")
apply (simp)
apply (metis Rep_VAR_SUBST_inverse VAR_SUBST_ON_commute subst_comp_rep_eq)
done

theorem SubstB_inv_cancel1 [simp] :
"SubstB (inv\<^sub>s ss) (SubstB ss b) = b"
  by (force simp add: SubstB_def closure CompB_rep_eq)

theorem SubstB_inv_cancel2 [simp] :
"SubstB ss (SubstB (inv\<^sub>s ss) b) = b"
  by (force simp add: SubstB_def closure CompB_rep_eq)

theorem SubstB_override_distr1 :
"SubstB ss (b1 \<oplus>\<^sub>b b2 on vs) = (SubstB ss b1) \<oplus>\<^sub>b (SubstB ss b2) on (\<langle>ss\<rangle>\<^sub>s ` vs)"
apply (simp add: SubstB_def closure)
apply (rule Rep_WF_BINDING_intro)
apply (simp add: closure CompB_rep_eq)
apply (simp add: override_on_def)
apply (rule ext)
apply (clarsimp)
apply (auto)
apply (subgoal_tac "a = \<langle>ss\<rangle>\<^sub>s (inv \<langle>ss\<rangle>\<^sub>s a)")
apply (simp_all)
done

theorem SubstB_override_distr2 :
"(SubstB ss b1) \<oplus>\<^sub>b (SubstB ss b2) on (\<langle>ss\<rangle>\<^sub>s ` vs) = SubstB ss (b1 \<oplus>\<^sub>b b2 on vs)"
apply (simp add: SubstB_override_distr1)
done

theorem SubstB_override_distr3 :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 SubstB ss (b1 \<oplus>\<^sub>b b2 on vs2) = (SubstB ss b1) \<oplus>\<^sub>b (SubstB ss b2) on vs2"
apply (subst SubstB_override_distr1 [of ss b1 b2 vs2])
apply (metis VAR_SUBST_ON_disj_image subst_image_def)
done

theorem SubstB_override_distr4 :
"\<lbrakk>ss \<in> VAR_SUBST_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (SubstB ss b1) \<oplus>\<^sub>b (SubstB ss b2) on vs2 = SubstB ss (b1 \<oplus>\<^sub>b b2 on vs2)"
apply (simp add: SubstB_override_distr3)
done

theorem SubstB_involution [simp] :
"ss \<in> VAR_SUBST_INV \<Longrightarrow>
 SubstB ss (SubstB ss b) = b"
apply (subgoal_tac "ss \<circ>\<^sub>s ss = id\<^sub>s")
apply (simp add: SubstB_compose)
apply (force simp add:closure)
done

subsubsection {* Predicate Substitution *}

(*
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
*)

theorem EvalP_SubstP [eval] :
"\<lbrakk>p[ss]\<rbrakk>b = \<lbrakk>p\<rbrakk>(SubstB (inv\<^sub>s ss) b)"
apply (simp add: EvalP_def)
apply (simp add: SubstP_def)
apply (simp add: image_def)
apply (safe)
apply (simp)
apply (rule_tac x = "SubstB (inv\<^sub>s ss) b" in bexI)
apply (simp)
apply (assumption)
done

theorem EvalP_SubstPMap_one [eval] :
"\<lbrakk> type x' = type x; control x' = control x \<rbrakk> \<Longrightarrow>
 \<lbrakk>p\<^bsup>[x \<mapsto> x']\<^esup>\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x', x' :=\<^sub>b \<langle>b\<rangle>\<^sub>b x))"
apply (simp add: SubstPMap_def)
apply (simp add: eval closure)
apply (simp add: EvalP_def)
apply (simp add: SubstP_def SubstB_def image_def closure)
apply (simp add: CompB_def)
apply (subgoal_tac "Abs_WF_BINDING (\<langle>b\<rangle>\<^sub>b \<circ> MapSubst [x \<mapsto> x']) = b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x', x' :=\<^sub>b \<langle>b\<rangle>\<^sub>b x)")
apply (simp add: closure)
apply (rule Rep_WF_BINDING_intro)
apply (simp add:closure)
apply (subgoal_tac "\<langle>b\<rangle>\<^sub>b x \<rhd> x'")
apply (simp)
apply (rule ext)
apply (simp add: MapSubst_def closure)
apply (auto)
sorry


theorem SubstP_id :
"p[id\<^sub>s] = p"
apply (utp_pred_auto_tac)
done

theorem SubstP_inverse1 :
"p[ss][inv\<^sub>s ss] = p"
apply (utp_pred_auto_tac)
done

theorem SubstP_inverse2 :
"p[inv\<^sub>s ss][ss] = p"
apply (utp_pred_auto_tac)
done

theorem SubstP_compose :
"p[ss1][ss2] = SubstP p (ss2 \<circ>\<^sub>s ss1)"
apply (utp_pred_tac)
apply (simp add: SubstB_compose closure)
done

theorem SubstP_commute :
"\<lbrakk>ss1 \<in> VAR_SUBST_ON vs1;
 ss2 \<in> VAR_SUBST_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (p::'VALUE WF_PREDICATE)[ss1][ss2] = p[ss2][ss1]"
apply (utp_pred_tac)
apply (clarify)
apply (subst SubstB_commute [of "(inv\<^sub>s ss1)" "vs1" "(inv\<^sub>s ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

theorem SubstP_involution [simp] :
"\<lbrakk>ss \<in> VAR_SUBST_INV\<rbrakk> \<Longrightarrow>
 p[ss][ss] = p"
apply (utp_pred_auto_tac)
done

end