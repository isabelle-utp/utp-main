(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_rename.thy                                                       *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Renaming *}

theory utp_rename
imports utp_pred "../tactics/utp_pred_tac"
begin

ML {*
  structure urename =
    Named_Thms (val name = @{binding urename} val description = "renaming theorems")
*}

setup urename.setup

subsection {* Variable Renaming *}

text {* Renamings are total bijections that respect typing. *}

definition VAR_RENAME :: "('VALUE VAR \<Rightarrow> 'VALUE VAR) set" where
"VAR_RENAME = {ss . bij ss \<and> (\<forall> v . vtype (ss v) = vtype v \<and> aux (ss v) = aux v)}"

typedef (open) 'VALUE VAR_RENAME = "VAR_RENAME :: ('VALUE VAR \<Rightarrow> 'VALUE VAR) set"
  by (auto simp add:VAR_RENAME_def)

declare Rep_VAR_RENAME [simp]
declare Rep_VAR_RENAME_inverse [simp]
declare Abs_VAR_RENAME_inverse [simp]

lemma Rep_VAR_RENAME_intro [intro]:
  "Rep_VAR_RENAME x = Rep_VAR_RENAME y \<Longrightarrow> x = y"
  by (simp add:Rep_VAR_RENAME_inject)

lemma Rep_VAR_RENAME_elim [elim]:
  "\<lbrakk> x = y; Rep_VAR_RENAME x = Rep_VAR_RENAME y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_VAR_RENAME

notation Rep_VAR_RENAME ("\<langle>_\<rangle>\<^sub>s")

lemma Rep_VAR_RENAME_bij [simp]: "bij \<langle>ss\<rangle>\<^sub>s"
  apply (insert Rep_VAR_RENAME[of ss])
  apply (simp add:VAR_RENAME_def)
done

lemma Rep_VAR_RENAME_inj [simp]: "inj \<langle>ss\<rangle>\<^sub>s"
  by (metis (lifting) Rep_VAR_RENAME_bij bij_def)

lemma Rep_VAR_RENAME_surj [simp]: "surj \<langle>ss\<rangle>\<^sub>s"
  by (metis Rep_VAR_RENAME_bij bij_betw_def)

lemma Rep_VAR_RENAME_type [simp]: "vtype (\<langle>ss\<rangle>\<^sub>s x) = vtype x"
  apply (insert Rep_VAR_RENAME[of ss])
  apply (simp add:VAR_RENAME_def)
done

lemma Rep_VAR_RENAME_aux [simp]: "aux (\<langle>ss\<rangle>\<^sub>s x) = aux x"
  apply (insert Rep_VAR_RENAME[of ss])
  apply (simp add:VAR_RENAME_def)
done

subsection {* Renaming builder *}

definition MapRename :: 
  "('VALUE VAR \<rightharpoonup> 'VALUE VAR) \<Rightarrow>
    'VALUE VAR \<Rightarrow> 'VALUE VAR" where
"MapRename f = the \<circ> (Some ++ (map_inv f ++ f))"

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

subsubsection {* @{term "MapRename"} theorems *}

lemma MapRename_empty[simp]:
  "MapRename empty = id"
  by (auto simp add:MapRename_def)

lemma MapRename_fwd [simp]:
  "x \<in> dom f \<Longrightarrow> (MapRename f) x = the (f x)"
  by (simp add:MapRename_def)

lemma MapRename_bwd [simp]: 
  "\<lbrakk>x \<notin> dom f; x \<in> ran f\<rbrakk> \<Longrightarrow> MapRename f x = the (map_inv f x)"
  by (simp add:MapRename_def)

lemma MapRename_copy [simp]:
  "\<lbrakk>x \<notin> dom f; x \<notin> ran f\<rbrakk> \<Longrightarrow> MapRename f x = x"
  by (simp add:MapRename_def)

lemma MapRename_bij [intro]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "set xs \<inter> set ys = {}"
  shows "bij (MapRename [xs [\<mapsto>] ys])"
proof (unfold MapRename_def, rule bij_map_Some, rule bij_completed_map)

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

lemma MapRename_inj [intro]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "set xs \<inter> set ys = {}"
  shows "inj (MapRename [xs [\<mapsto>] ys])"
  by (metis MapRename_bij assms bij_betw_imp_inj_on)

lemma MapRename_image_out [simp]:
  "\<lbrakk> length xs = length ys; distinct xs; vs \<inter> (set xs \<union> set ys) = {} \<rbrakk> \<Longrightarrow>
       MapRename [xs [\<mapsto>] ys] ` vs = vs"
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

lemma MapRename_image_fwd [simp]:
  assumes "length xs = length ys" "distinct xs" "vs \<subseteq> set xs" "set xs \<inter> set ys = {}"
  shows "MapRename [xs [\<mapsto>] ys] ` vs = the ` [xs [\<mapsto>] ys] ` (set xs \<inter> vs)"
using assms proof (auto)
  fix x
  assume assms':"x \<in> set xs" "x \<in> vs"
  
  moreover then obtain i where "x = xs!i" "i < length xs"
    by (auto)

  ultimately show "the ([xs [\<mapsto>] ys] x) \<in> MapRename [xs [\<mapsto>] ys] ` vs" using assms
    apply (simp add:image_def)
    apply (rule_tac x="x" in bexI)
    apply (simp_all)
  done
qed

lemma MapRename_image_bwd [simp]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "vs \<subseteq> set ys" "set xs \<inter> set ys = {}"
  shows "MapRename [xs [\<mapsto>] ys] ` vs = the ` [ys [\<mapsto>] xs] ` (set ys \<inter> vs)"
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

lemma MapRename_image [simp]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" "set xs \<inter> set ys = {}"
  shows "MapRename [xs [\<mapsto>] ys] ` vs = vs - (set xs \<union> set ys) 
                              \<union> the ` [xs [\<mapsto>] ys] ` (set xs \<inter> vs)
                              \<union> the ` [ys [\<mapsto>] xs] ` (set ys \<inter> vs)"
proof -
  have "MapRename [xs [\<mapsto>] ys] ` vs = 
        MapRename [xs [\<mapsto>] ys] ` (vs - (set xs \<union> set ys)) \<union> 
        MapRename [xs [\<mapsto>] ys] ` (vs \<inter> set xs) \<union>
        MapRename [xs [\<mapsto>] ys] ` (vs \<inter> set ys)"
    apply (subgoal_tac "vs = (vs - (set xs \<union> set ys)) \<union> (vs \<inter> set xs) \<union> (vs \<inter> set ys)")
    apply (metis image_Un)
    apply (force)
  done

  moreover have "MapRename [xs [\<mapsto>] ys] ` (vs - (set xs \<union> set ys)) = vs - (set xs \<union> set ys)"
    apply (rule MapRename_image_out)
    apply (simp_all add:assms)
    apply (force)
  done

  ultimately show ?thesis using assms
    by (force)
qed

theorem MapRename_inv [simp]: 
  assumes "inj_on f (dom f)" "ran f \<inter> dom f = {}"
  shows "inv (MapRename f) = MapRename (map_inv f)"
proof -

  from assms have "inv (MapRename f) = inv (the \<circ> Some ++ (map_inv f ++ f))"
    by (simp add:MapRename_def)

  also from assms have "... = the \<circ> map_inv (Some ++ (map_inv f ++ f))"
  proof -
    from assms have "dom (map_inv f ++ f) = ran (map_inv f ++ f)"
      apply (simp)
      by (auto)

    moreover from assms have "inj_on (map_inv f ++ f) (dom (map_inv f ++ f))"
      by (auto)

    ultimately show ?thesis
      apply (rule_tac ext)
      apply (simp only:inv_map_inv)
    done
  qed

  also from assms have "... = the \<circ> map_inv (map_id_on (-(dom f \<union> ran f)) ++ (map_inv f ++ f))"
    by (metis (no_types) dom_map_add dom_map_inv map_add_Some)


  also from assms have "... = the \<circ> (map_inv (map_id_on (-(dom f \<union> ran f))) ++ map_inv (map_inv f ++ f))" (is "the \<circ> ?P = the \<circ> ?Q")
  proof -
    from assms have "?P = ?Q"
      by (rule_tac map_inv_add, auto)

    thus ?thesis by simp
  qed

  also from assms have "... = the \<circ> ((map_id_on (-(dom f \<union> ran f))) ++ (f ++ map_inv f))"
  proof -
    from assms have "map_inv (map_inv f ++ f) = (f ++ map_inv f)"
      by (smt dom_map_inv inf_sup_aci(1) inj_map_inv map_inv_add map_inv_map_inv)

    thus ?thesis by simp
  qed

  also from assms have "... = MapRename (map_inv f)"
    apply (simp add: MapRename_def)
    apply (smt compl_sup dom_map_add dom_map_inv map_add_Some map_add_assoc sup_commute)
  done

  ultimately show ?thesis by simp
qed

theorem MapRename_map_inv [simp]: 
  assumes "inj_on f (dom f)" "ran f \<inter> dom f = {}"
  shows "MapRename (map_inv f) = MapRename f"
  by (metis MapRename_def assms dom_map_inv map_add_comm map_inv_map_inv)

subsubsection {* Variable Renaming *}

text {* Theorems about @{term "VAR_RENAME"} *}

theorem VAR_RENAME_bij [dest] :
"ss \<in> VAR_RENAME \<Longrightarrow> bij ss"
apply (simp add: VAR_RENAME_def)
done

theorem VAR_RENAME_id [closure]:
"id \<in> VAR_RENAME"
apply (simp add: VAR_RENAME_def)
done

theorem VAR_RENAME_inv [closure] :
"ss \<in> VAR_RENAME \<Longrightarrow> (inv ss) \<in> VAR_RENAME"
apply (simp add: VAR_RENAME_def)
apply (safe)
apply (drule_tac x = "inv ss v" in spec)
apply (clarify)
apply (erule subst)
apply (simp_all add: bij_def surj_f_inv_f)
apply (metis surj_f_inv_f)
apply (metis surj_f_inv_f)
done

theorem VAR_RENAME_compose [closure]:
"\<lbrakk>ss1 \<in> VAR_RENAME;
 ss2 \<in> VAR_RENAME\<rbrakk> \<Longrightarrow>
 ss1 \<circ> ss2 \<in> VAR_RENAME"
apply (simp add: VAR_RENAME_def)
apply (clarify)
apply (simp add: bij_comp)
done

theorem VAR_RENAME_inv_comp [simp] :
"ss \<in> VAR_RENAME \<Longrightarrow> inv ss \<circ> ss = id"
apply (drule VAR_RENAME_bij)
apply (rule ext)
apply (clarsimp)
apply (simp add: bij_def inv_f_f)
done

theorem VAR_RENAME_inv_distr [simp] :
"\<lbrakk>ss1 \<in> VAR_RENAME;
 ss2 \<in> VAR_RENAME\<rbrakk> \<Longrightarrow>
 inv (ss1 \<circ> ss2) = (inv ss2) \<circ> (inv ss1)"
apply (drule VAR_RENAME_bij)
apply (drule VAR_RENAME_bij)
apply (simp add: o_inv_distrib)
done

theorem VAR_RENAME_WF_BINDING [closure] :
"\<lbrakk>b \<in> WF_BINDING;
 ss \<in> VAR_RENAME\<rbrakk> \<Longrightarrow>
 b \<circ> ss \<in> WF_BINDING"
apply (simp add: VAR_RENAME_def WF_BINDING_def)
apply (safe)
apply (drule_tac x = "ss v" in spec)
apply (drule_tac x = "v" in spec)
apply (force)
done

theorem VAR_RENAME_inject [simp] :
"ss \<in> VAR_RENAME \<Longrightarrow> (f1 \<circ> ss = f2 \<circ> ss) = (f1 = f2)"
apply (drule VAR_RENAME_bij)
apply (simp)
done

theorem VAR_RENAME_inv_inv [simp] :
"ss \<in> VAR_RENAME \<Longrightarrow> inv (inv ss) = ss"
apply (simp add: VAR_RENAME_def)
apply (simp add: inv_inv_eq)
done

theorem VAR_RENAME_comp_inv [simp] :
"ss \<in> VAR_RENAME \<Longrightarrow> ss \<circ> inv ss = id"
apply (drule VAR_RENAME_bij)
apply (rule ext)
apply (clarsimp)
apply (simp add: surj_f_inv_f bij_def)
done

theorem VAR_RENAME_ss_inv_app [simp] :
"ss \<in> VAR_RENAME \<Longrightarrow> ss (inv ss x) = x"
apply (simp add: VAR_RENAME_def)
apply (simp add: surj_f_inv_f bij_def)
done

theorem VAR_RENAME_inv_ss_app [simp] :
"ss \<in> VAR_RENAME \<Longrightarrow> inv ss (ss x) = x"
apply (simp add: VAR_RENAME_def)
apply (simp add: inv_f_f bij_def)
done

theorem VAR_RENAME_image_comp [simp] :
"\<lbrakk>ss1 \<in> VAR_RENAME;
 ss2 \<in> VAR_RENAME\<rbrakk> \<Longrightarrow>
 ss1 ` ss2 ` vs = (ss1 \<circ> ss2) ` vs"
apply (simp add: image_def)
apply (auto)
done

theorem VAR_RENAME_in_image [simp] :
"\<lbrakk>ss \<in> VAR_RENAME\<rbrakk> \<Longrightarrow> ss x \<in> (ss ` a) = (x \<in> a)"
apply (simp add: VAR_RENAME_def)
apply (auto simp: bij_def inj_eq)
done

subsubsection {* Derived renaming operators *}

definition rename_comp :: 
  "'VALUE VAR_RENAME \<Rightarrow> 'VALUE VAR_RENAME \<Rightarrow> 'VALUE VAR_RENAME" (infixl "\<circ>\<^sub>s" 55) where 
"rename_comp x y = Abs_VAR_RENAME (\<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s)"

lemma rename_comp_rep_eq [simp]:
  "\<langle>x \<circ>\<^sub>s y\<rangle>\<^sub>s = \<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s"
  apply (subgoal_tac "\<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s \<in> VAR_RENAME")
  apply (simp add: rename_comp_def comp_def)
  apply (simp add:closure)
done

definition rename_inv :: 
  "'VALUE VAR_RENAME \<Rightarrow> 'VALUE VAR_RENAME" ("inv\<^sub>s") where
"inv\<^sub>s ss = Abs_VAR_RENAME (inv \<langle>ss\<rangle>\<^sub>s)"

lemma rename_inv_rep_eq [simp]:
  "\<langle>inv\<^sub>s ss\<rangle>\<^sub>s = inv \<langle>ss\<rangle>\<^sub>s"
  by (simp add:rename_inv_def closure)

definition rename_id :: 
  "'VALUE VAR_RENAME" ("id\<^sub>s") where
"id\<^sub>s = Abs_VAR_RENAME id"

lemma rename_id_rep_eq [simp]:
  "\<langle>id\<^sub>s\<rangle>\<^sub>s = id"
  by (simp add: rename_id_def closure)

lemma rename_inv_id [simp]:
  "inv\<^sub>s id\<^sub>s = id\<^sub>s"
  by force

lemma rename_inv_inv [simp]:
  "inv\<^sub>s (inv\<^sub>s ss) = ss"
  by force

lemma rename_inv_comp [simp]:
  "inv\<^sub>s (ss1 \<circ>\<^sub>s ss2) = inv\<^sub>s ss2 \<circ>\<^sub>s inv\<^sub>s ss1"
  by force

definition rename_image :: 
  "('VALUE VAR_RENAME) \<Rightarrow> 'VALUE VAR set \<Rightarrow> 'VALUE VAR set" (infixr "`\<^sub>s" 90) where
"ss `\<^sub>s vs = \<langle>ss\<rangle>\<^sub>s ` vs"

declare rename_image_def [simp]

definition rename_equiv ::
  "'VALUE VAR_RENAME \<Rightarrow> 'VALUE VAR_RENAME \<Rightarrow> 'VALUE VAR set \<Rightarrow> bool" where
"rename_equiv ss1 ss2 vs \<equiv> \<forall>x \<in> vs. (\<langle>ss1\<rangle>\<^sub>s x = \<langle>ss2\<rangle>\<^sub>s x)"

notation rename_equiv ("_ \<cong>\<^sub>s _ on _")

text {* More theorems about @{term "VAR_RENAME"} *}

lemma VAR_RENAME_MapRename [closure]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" 
          "set xs \<inter> set ys = {}" "\<forall>i<length xs. vtype (xs!i) = vtype (ys!i) \<and> aux (xs!i) = aux (ys!i)"
  shows "MapRename [xs [\<mapsto>] ys] \<in> VAR_RENAME"
proof -

  from assms  have "\<And> v. vtype (MapRename [xs [\<mapsto>] ys] v) = vtype v"
    apply (case_tac "v \<in> set xs")
    apply (erule list_set_index_elim)
    apply (auto)
    apply (case_tac "v \<in> set ys")
    apply (erule list_set_index_elim)
    apply (auto)
  done

  moreover from assms  have "\<And> v. aux (MapRename [xs [\<mapsto>] ys] v) = aux v"
    apply (case_tac "v \<in> set xs")
    apply (erule list_set_index_elim)
    apply (force)
    apply (case_tac "v \<in> set ys")
    apply (erule list_set_index_elim)
    apply (auto)
  done


  ultimately show ?thesis using assms
    by (auto simp add:VAR_RENAME_def)
qed

lemma MapRename_invol:
  assumes "length xs = length ys" "distinct xs" "distinct ys" 
          "set xs \<inter> set ys = {}" "\<forall>i<length xs. vtype (xs!i) = vtype (ys!i) \<and> aux (xs!i) = aux (ys!i)"
  shows "inv (MapRename [xs [\<mapsto>] ys]) = MapRename [xs [\<mapsto>] ys]"
proof -

  from assms have "inv (MapRename [xs [\<mapsto>] ys]) = MapRename (map_inv [xs [\<mapsto>] ys])"
    by (smt Int_commute MapRename_inv dom_map_inv map_inv_maplets maplets_distinct_inj ran_maplets)

  also from assms have "... = MapRename [xs [\<mapsto>] ys]"
    by (metis (no_types) Int_commute MapRename_map_inv dom_map_inv map_inv_maplets maplets_distinct_inj ran_maplets)

  ultimately show ?thesis by simp

qed

lemma VAR_RENAME_MapRename_one [closure]:
  "\<lbrakk> vtype x = vtype y; aux x = aux y \<rbrakk> \<Longrightarrow> MapRename [x \<mapsto> y] \<in> VAR_RENAME"
  apply (case_tac "x \<noteq> y")
  apply (rule VAR_RENAME_MapRename[of "[x]" "[y]",simplified])
  apply (simp_all)
  apply (simp add:MapRename_def closure)
done

text {* Variable renamings confined to a set of variables. *}

definition VAR_RENAME_ON ::
  "('VALUE VAR) set \<Rightarrow> 'VALUE VAR_RENAME set" where
"VAR_RENAME_ON vs =
 {ss. (\<forall> v . v \<notin> vs \<longrightarrow> \<langle>ss\<rangle>\<^sub>s v = v)}"

text {* Variable renamings that are also involutions. *}

definition VAR_RENAME_INV :: "'VALUE VAR_RENAME set" where
"VAR_RENAME_INV = {ss. ss = inv\<^sub>s ss}"

text {* Theorems about @{term "VAR_RENAME_ON"} *}

theorem VAR_RENAME_ON_inv [closure] :
"ss \<in> VAR_RENAME_ON vs \<Longrightarrow>
 (inv\<^sub>s ss) \<in> VAR_RENAME_ON vs"
apply (auto simp add: VAR_RENAME_ON_def)
apply (drule_tac x = "v" in spec)
apply (auto)
apply (drule sym)
apply (erule ssubst)
back back
apply (simp)
done

text {* Should the following three theorems be default simplifications? *}

text {* This causes a loop though when simplifying @{term VAR_RENAME_ON}. *}

theorem VAR_RENAME_ON_app_simp :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs; x \<notin> vs\<rbrakk> \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s x = x"
  by (simp add: VAR_RENAME_ON_def)

theorem VAR_RENAME_ON_app_member :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs; x \<in> vs\<rbrakk> \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s x \<in> vs"
apply (simp only: VAR_RENAME_ON_def)
apply (auto)
(*apply (drule VAR_RENAME_bij)
apply (simp add: bij_def)
apply (clarify) *)
apply (case_tac "\<langle>ss\<rangle>\<^sub>s x \<in> vs")
apply (assumption)
apply (drule_tac x = "\<langle>ss\<rangle>\<^sub>s x" in spec)
apply (clarify)
apply (subgoal_tac "\<langle>ss\<rangle>\<^sub>s x = x")
apply (auto dest: injD)
apply (metis Rep_VAR_RENAME VAR_RENAME_in_image)
done

theorem VAR_RENAME_ON_app_not_member :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs; x \<notin> vs\<rbrakk> \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s x \<notin> vs"
apply (simp only: VAR_RENAME_ON_def)
apply (clarify)
apply (simp add: bij_def)
done

theorem VAR_RENAME_ON_image [simp] :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1\<rbrakk> \<Longrightarrow>
 ss `\<^sub>s vs1 = vs1"
apply (simp add: image_def)
apply (safe)
apply (simp add: VAR_RENAME_ON_app_member)
apply (rule_tac x = "inv \<langle>ss\<rangle>\<^sub>s x" in bexI)
apply (simp)
apply (subgoal_tac "\<langle>ss\<rangle>\<^sub>s x \<in> vs1")
apply (drule VAR_RENAME_ON_inv)
apply (metis (lifting) VAR_RENAME_ON_app_member rename_inv_rep_eq)
apply (simp add: VAR_RENAME_ON_app_member)
done

theorem VAR_RENAME_ON_disj_image [simp] :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss `\<^sub>s vs2 = vs2"
apply (simp add: VAR_RENAME_ON_def)
apply (auto)
apply (simp add: image_def)
apply (rule_tac x = "x" in bexI)
apply (auto)
done

theorem VAR_RENAME_ON_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss1 \<circ>\<^sub>s ss2 = ss2 \<circ>\<^sub>s ss1"
apply (rule Rep_VAR_RENAME_intro)
apply (simp)
apply (rule ext)
apply (simp)
apply (case_tac "x \<notin> vs1")
apply (simp add: VAR_RENAME_ON_app_simp)
apply (case_tac "x \<in> vs2")
apply (subgoal_tac "\<langle>ss2\<rangle>\<^sub>s x \<notin> vs1")
apply (simp_all add: VAR_RENAME_ON_app_simp)
apply (subgoal_tac "\<langle>ss2\<rangle>\<^sub>s x \<in> vs2")
apply (auto) [1]
apply (simp add: VAR_RENAME_ON_app_member)
apply (case_tac "x \<notin> vs2")
apply (simp_all add: VAR_RENAME_ON_app_simp)
apply (subgoal_tac "\<langle>ss1\<rangle>\<^sub>s x \<notin> vs2")
apply (simp_all add: VAR_RENAME_ON_app_simp)
apply (subgoal_tac "\<langle>ss1\<rangle>\<^sub>s x \<in> vs1")
apply (auto) [1]
apply (simp add: VAR_RENAME_ON_app_member)
apply (auto)
done

text {* Theorems about @{term "VAR_RENAME_INV"} *}

theorem VAR_RENAME_INV_inv_closure [closure] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow> (inv\<^sub>s ss) \<in> VAR_RENAME_INV"
apply (simp add: VAR_RENAME_INV_def)
done

text {* Should the following theorem be a default simplifications? *}

text {* This causes a loop though when simplifying @{term VAR_RENAME_INV}. *}

theorem VAR_RENAME_INV_inv :
"ss \<in> VAR_RENAME_INV \<Longrightarrow> (inv\<^sub>s ss) = ss"
apply (simp add: VAR_RENAME_INV_def)
done

theorem VAR_RENAME_INV_comp [simp] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow> (ss \<circ>\<^sub>s ss) = id\<^sub>s"
apply (simp add: VAR_RENAME_INV_def)
apply (rule Rep_VAR_RENAME_intro)
apply (simp)
apply (erule Rep_VAR_RENAME_elim)
apply (erule ssubst) back
apply (simp)
done

theorem VAR_RENAME_INV_app [simp] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s (\<langle>ss\<rangle>\<^sub>s x) = x"
  by (metis VAR_RENAME_INV_comp id_apply o_eq_dest_lhs rename_comp_rep_eq rename_id_rep_eq)

subsection {* Binding Renaming *}

definition CompB ::   
  "'VALUE WF_BINDING \<Rightarrow>
   'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_BINDING" where
"CompB b ss = Abs_WF_BINDING (\<langle>b\<rangle>\<^sub>b \<circ> \<langle>ss\<rangle>\<^sub>s)"

lemma CompB_rep_eq [simp]:
  "\<langle>CompB b ss\<rangle>\<^sub>b = \<langle>b\<rangle>\<^sub>b \<circ> \<langle>ss\<rangle>\<^sub>s"
  by (simp add:CompB_def closure)

definition RenameB ::
  "'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_BINDING \<Rightarrow>
   'VALUE WF_BINDING" where
"RenameB ss b = CompB b (inv\<^sub>s ss)"

subsection {* Predicate Renaming *}

lift_definition RenameP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_PREDICATE" ("_[_]" [200]) is
"\<lambda> p ss. (RenameB ss) ` p" done

definition MapR ::
  "('VALUE VAR \<rightharpoonup> 'VALUE VAR) \<Rightarrow>
   'VALUE VAR_RENAME" where
"MapR f = Abs_VAR_RENAME (MapRename f)"


lemma MapR_rep_eq:
  assumes "length xs = length ys" "distinct xs" "distinct ys" 
          "set xs \<inter> set ys = {}" "\<forall>i<length xs. vtype (xs!i) = vtype (ys!i) \<and> aux (xs!i) = aux (ys!i)"

  shows "\<langle>MapR [xs [\<mapsto>] ys]\<rangle>\<^sub>s = MapRename [xs [\<mapsto>] ys]"
  by (simp add:MapR_def closure assms)

definition RenamePMap :: 
  "'VALUE  WF_PREDICATE \<Rightarrow> 
   ('VALUE VAR \<rightharpoonup> 'VALUE VAR) \<Rightarrow> 
   'VALUE WF_PREDICATE" ("_\<^bsup>_\<^esup>" [200]) where
"RenamePMap p ss \<equiv> RenameP p (MapR ss)"

subsubsection {* Binding Renaming *}

(*
theorem RenameB_closure [closure] :
"\<lbrakk>ss \<in> VAR_RENAME;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 RenameB ss b \<in> WF_BINDING"
apply (simp add: RenameB_def closure)
done
*)

lemma WF_BINDING_VAR_RENAME [closure]: "\<langle>b\<rangle>\<^sub>b \<circ> inv \<langle>ss\<rangle>\<^sub>s \<in> WF_BINDING"
  by (metis Rep_VAR_RENAME Rep_WF_BINDING VAR_RENAME_WF_BINDING VAR_RENAME_inv)

theorem RenameB_inject [simp]:
  "(RenameB ss b1 = RenameB ss b2) = (b1 = b2)"
  by (force simp add:RenameB_def CompB_rep_eq)

theorem RenameB_id [simp] :
"RenameB id\<^sub>s b = b"
  by (auto simp add: RenameB_def CompB_rep_eq closure)

theorem RenameB_compose :
"RenameB ss1 (RenameB ss2 b) = RenameB (ss1 \<circ>\<^sub>s ss2) b"
  by (auto simp add: RenameB_def closure o_assoc CompB_rep_eq)

theorem RenameB_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 RenameB ss1 (RenameB ss2 b) = RenameB ss2 (RenameB ss1 b)"
apply (simp add: RenameB_compose)
apply (subgoal_tac "ss1 \<circ>\<^sub>s ss2 = ss2 \<circ>\<^sub>s ss1")
apply (simp)
apply (metis Rep_VAR_RENAME_inverse VAR_RENAME_ON_commute rename_comp_rep_eq)
done

theorem RenameB_inv_cancel1 [simp] :
"RenameB (inv\<^sub>s ss) (RenameB ss b) = b"
  by (force simp add: RenameB_def closure CompB_rep_eq)

theorem RenameB_inv_cancel2 [simp] :
"RenameB ss (RenameB (inv\<^sub>s ss) b) = b"
  by (force simp add: RenameB_def closure CompB_rep_eq)

theorem RenameB_override_distr1 :
"RenameB ss (b1 \<oplus>\<^sub>b b2 on vs) = (RenameB ss b1) \<oplus>\<^sub>b (RenameB ss b2) on (\<langle>ss\<rangle>\<^sub>s ` vs)"
apply (simp add: RenameB_def closure)
apply (rule Rep_WF_BINDING_intro)
apply (simp add: closure CompB_rep_eq)
apply (simp add: override_on_def)
apply (rule ext)
apply (clarsimp)
apply (auto)
apply (subgoal_tac "a = \<langle>ss\<rangle>\<^sub>s (inv \<langle>ss\<rangle>\<^sub>s a)")
apply (simp_all)
done

theorem RenameB_override_distr2 :
"(RenameB ss b1) \<oplus>\<^sub>b (RenameB ss b2) on (\<langle>ss\<rangle>\<^sub>s ` vs) = RenameB ss (b1 \<oplus>\<^sub>b b2 on vs)"
apply (simp add: RenameB_override_distr1)
done

theorem RenameB_override_distr3 :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 RenameB ss (b1 \<oplus>\<^sub>b b2 on vs2) = (RenameB ss b1) \<oplus>\<^sub>b (RenameB ss b2) on vs2"
apply (subst RenameB_override_distr1 [of ss b1 b2 vs2])
apply (metis VAR_RENAME_ON_disj_image rename_image_def)
done

theorem RenameB_override_distr4 :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (RenameB ss b1) \<oplus>\<^sub>b (RenameB ss b2) on vs2 = RenameB ss (b1 \<oplus>\<^sub>b b2 on vs2)"
apply (simp add: RenameB_override_distr3)
done

theorem RenameB_involution [simp] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow>
 RenameB ss (RenameB ss b) = b"
apply (subgoal_tac "ss \<circ>\<^sub>s ss = id\<^sub>s")
apply (simp add: RenameB_compose)
apply (force simp add:closure)
done

subsubsection {* Predicate Renaming *}

(*
theorem RenameP_closure [closure] :
"\<lbrakk>p \<in> WF_PREDICATE;
 ss \<in> VAR_RENAME\<rbrakk> \<Longrightarrow>
 p[ss] \<in> WF_PREDICATE"
apply (simp add: RenameP_def)
apply (simp add: WF_PREDICATE_def)
apply (safe)
apply (subgoal_tac "xa \<in> WF_BINDING")
apply (simp add: closure)
apply (auto)
done

theorem RenamePMap_single_closure [closure]:
  "\<lbrakk> p \<in> WF_PREDICATE; x \<noteq> y; vtype x = vtype y \<rbrakk> \<Longrightarrow> p\<^bsup>[x \<mapsto> y] \<^esup>\<in> WF_PREDICATE"
  apply (simp add:RenamePMap_def)
  apply (rule closure, simp)
  apply (rule VAR_RENAME_MapRename[of "[x]" "[y]",simplified])
  apply (auto)
done
*)

theorem EvalP_RenameP [eval] :
"\<lbrakk>p[ss]\<rbrakk>b = \<lbrakk>p\<rbrakk>(RenameB (inv\<^sub>s ss) b)"
apply (simp add: EvalP_def)
apply (simp add: RenameP_def)
apply (simp add: image_def)
apply (safe)
apply (simp)
apply (rule_tac x = "RenameB (inv\<^sub>s ss) b" in bexI)
apply (simp)
apply (assumption)
done

theorem EvalP_RenamePMap_one [eval] :
"\<lbrakk> x \<noteq> x'; vtype x' = vtype x; aux x' = aux x \<rbrakk> \<Longrightarrow>
 \<lbrakk>p\<^bsup>[x \<mapsto> x']\<^esup>\<rbrakk>b = \<lbrakk>p\<rbrakk>(b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x', x' :=\<^sub>b \<langle>b\<rangle>\<^sub>b x))"
apply (simp add: RenamePMap_def)
apply (simp add: eval closure)
apply (simp add: EvalP_def)
apply (simp add: RenameP_def RenameB_def image_def closure)
apply (simp add: MapR_rep_eq[of "[x]" "[x']",simplified] CompB_def)
apply (subgoal_tac "Abs_WF_BINDING (\<langle>b\<rangle>\<^sub>b \<circ> MapRename [x \<mapsto> x']) = b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x', x' :=\<^sub>b \<langle>b\<rangle>\<^sub>b x)")
apply (simp add: closure)
apply (rule Rep_WF_BINDING_intro)
apply (simp add:closure)
apply (subgoal_tac "\<langle>b\<rangle>\<^sub>b x \<rhd> x'")
apply (simp)
apply (rule ext)
apply (simp add: MapRename_def closure)
apply (auto)
done

subsection {* Simplification theorems *}

theorem RenameP_id :
"p[id\<^sub>s] = p"
apply (utp_pred_auto_tac)
done

theorem RenameP_inverse1 :
"p[ss][inv\<^sub>s ss] = p"
apply (utp_pred_auto_tac)
done

theorem RenameP_inverse2 :
"p[inv\<^sub>s ss][ss] = p"
apply (utp_pred_auto_tac)
done

theorem RenameP_compose :
"p[ss1][ss2] = RenameP p (ss2 \<circ>\<^sub>s ss1)"
apply (utp_pred_tac)
apply (simp add: RenameB_compose closure)
done

theorem RenameP_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (p::'VALUE WF_PREDICATE)[ss1][ss2] = p[ss2][ss1]"
apply (utp_pred_tac)
apply (clarify)
apply (subst RenameB_commute [of "(inv\<^sub>s ss1)" "vs1" "(inv\<^sub>s ss2)" "vs2" "b"])
apply (simp_all add: closure)
done

theorem RenameP_involution [simp] :
"\<lbrakk>ss \<in> VAR_RENAME_INV\<rbrakk> \<Longrightarrow>
 p[ss][ss] = p"
apply (utp_pred_auto_tac)
done

theorem RenameP_VAR:
  "\<langle>ss\<rangle>\<^sub>s ` VAR = VAR"
  by (auto simp add:VAR_def)

theorems rename_simps =
  RenameP_id
  RenameP_inverse1
  RenameP_inverse2
  RenameP_compose
  RenameP_involution
  RenameP_VAR

subsection {* Distribution theorems *}

theorem RenameP_image_union [urename]:
  "\<langle>ss\<rangle>\<^sub>s ` (vs1 \<union> vs2) = \<langle>ss\<rangle>\<^sub>s ` vs1 \<union> \<langle>ss\<rangle>\<^sub>s ` vs2"
  by auto

theorem RenameP_image_inter [urename]:
  "\<langle>ss\<rangle>\<^sub>s ` (vs1 \<inter> vs2) = \<langle>ss\<rangle>\<^sub>s ` vs1 \<inter> \<langle>ss\<rangle>\<^sub>s ` vs2"
  by (auto, metis Rep_VAR_RENAME VAR_RENAME_in_image)

theorem RenameP_image_minus [urename]:
  "\<langle>ss\<rangle>\<^sub>s ` (vs1 - vs2) = \<langle>ss\<rangle>\<^sub>s ` vs1 - \<langle>ss\<rangle>\<^sub>s ` vs2"
  by (metis Rep_VAR_RENAME_inj image_set_diff)
  
theorems rename_dist =
  RenameP_image_union
  RenameP_image_inter
  RenameP_image_minus

end