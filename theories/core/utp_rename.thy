(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_rename.thy                                                       *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Renaming *}

theory utp_rename
imports 
  utp_value
  utp_var
  utp_binding
begin

subsection {* Permutation Polymorphic Constant *}

default_sort type

consts
  permute  :: "'r \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<bullet>" 80)

default_sort VALUE

subsection {* Variable Renaming *}

text {* Renamings are total bijections that respect typing. *}

definition VAR_RENAME :: "('a uvar \<Rightarrow> 'a uvar) set" where
"VAR_RENAME = {ss . bij ss \<and> (\<forall> v . vtype (ss v) = vtype v \<and> aux (ss v) = aux v)}"

typedef 'a VAR_RENAME = "VAR_RENAME :: ('a uvar \<Rightarrow> 'a uvar) set"
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

adhoc_overloading
  permute Rep_VAR_RENAME

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

theorem Rep_VAR_RENAME_VAR [simp]:
  "\<langle>ss\<rangle>\<^sub>s ` VAR = VAR"
  by (auto simp add:VAR_def)

subsection {* Renaming builder *}

definition MapRename :: 
  "('a uvar \<rightharpoonup> 'a uvar) \<Rightarrow>
    'a uvar \<Rightarrow> 'a uvar" where
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

theorem VAR_RENAME_binding [closure] :
"\<lbrakk>b \<in> binding;
 ss \<in> VAR_RENAME\<rbrakk> \<Longrightarrow>
 b \<circ> ss \<in> binding"
apply (simp add: VAR_RENAME_def binding_def)
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
  "'a VAR_RENAME \<Rightarrow> 'a VAR_RENAME \<Rightarrow> 'a VAR_RENAME" (infixl "\<circ>\<^sub>s" 55) where 
"rename_comp x y = Abs_VAR_RENAME (\<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s)"

lemma rename_comp_rep_eq [simp]:
  "\<langle>x \<circ>\<^sub>s y\<rangle>\<^sub>s = \<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s"
  apply (subgoal_tac "\<langle>x\<rangle>\<^sub>s \<circ> \<langle>y\<rangle>\<^sub>s \<in> VAR_RENAME")
  apply (simp add: rename_comp_def comp_def)
  apply (simp add:closure)
done

definition rename_inv :: 
  "'a VAR_RENAME \<Rightarrow> 'a VAR_RENAME" ("inv\<^sub>s") where
"inv\<^sub>s ss = Abs_VAR_RENAME (inv \<langle>ss\<rangle>\<^sub>s)"

lemma rename_inv_rep_eq [simp]:
  "\<langle>inv\<^sub>s ss\<rangle>\<^sub>s = inv \<langle>ss\<rangle>\<^sub>s"
  by (simp add:rename_inv_def closure)

definition rename_id :: 
  "'a VAR_RENAME" ("id\<^sub>s") where
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
  "('a VAR_RENAME) \<Rightarrow> 'a uvar set \<Rightarrow> 'a uvar set" (infixr "`\<^sub>s" 90) where
"ss `\<^sub>s vs = \<langle>ss\<rangle>\<^sub>s ` vs"

declare rename_image_def [simp]

definition rename_equiv ::
  "'a VAR_RENAME \<Rightarrow> 'a VAR_RENAME \<Rightarrow> 'a uvar set \<Rightarrow> bool" where
"rename_equiv ss1 ss2 vs \<equiv> \<forall>x \<in> vs. (\<langle>ss1\<rangle>\<^sub>s x = \<langle>ss2\<rangle>\<^sub>s x)"

notation rename_equiv ("_ \<cong>\<^sub>s _ on _")

lemma rename_equiv_empty [intro]:
  "ss1 \<cong>\<^sub>s ss2 on {}"
  by (simp add: rename_equiv_def)

lemma rename_equiv_refl [intro]:
  "ss \<cong>\<^sub>s ss on vs"
  by (simp add: rename_equiv_def)

lemma rename_equiv_sym:
  "ss1 \<cong>\<^sub>s ss2 on vs \<Longrightarrow> ss2 \<cong>\<^sub>s ss1 on vs"
  by (simp add: rename_equiv_def)

lemma rename_equiv_trans :
"\<lbrakk>ss1 \<cong>\<^sub>s ss2 on vs;
 ss2 \<cong>\<^sub>s ss3 on vs\<rbrakk> \<Longrightarrow>
 ss1 \<cong>\<^sub>s ss3 on vs"
  by (simp add: rename_equiv_def)

lemma rename_equiv_union [intro]:
"\<lbrakk>ss1 \<cong>\<^sub>s ss2 on vs1;
 ss1 \<cong>\<^sub>s ss2 on vs2\<rbrakk> \<Longrightarrow>
 ss1 \<cong>\<^sub>s ss2 on (vs1 \<union> vs2)"
  by (auto simp add: rename_equiv_def)

definition rename_func_on :: "('a uvar \<Rightarrow> 'a uvar) \<Rightarrow> 'a uvar set \<Rightarrow> bool" where
"rename_func_on f vs \<longleftrightarrow> (inj_on f vs \<and> f ` vs \<inter> vs = {} \<and> (\<forall> x. vtype x = vtype (f x)) \<and> (\<forall> x. aux x = aux (f x)))"

lemma rename_func_onE [elim]:
  "\<lbrakk> rename_func_on f vs; \<lbrakk> inj_on f vs; f ` vs \<inter> vs = {}; \<forall> x. vtype x = vtype (f x); \<forall> x. aux x = aux (f x) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:rename_func_on_def)

lemma dash_UNDASHED_rename_func [closure]:
  "xs \<subseteq> UNDASHED \<Longrightarrow> rename_func_on dash xs"
  by (auto simp add:rename_func_on_def)

lemma comp_rename_func [closure]:
  "\<lbrakk> rename_func_on f vs; rename_func_on g (f ` vs); vs \<inter> g ` f ` vs = {} \<rbrakk> 
   \<Longrightarrow> rename_func_on (g \<circ> f) vs"
  by (auto intro: comp_inj_on simp add:rename_func_on_def)

lemma dash_DASHED_rename_func [closure]:
  "xs \<subseteq> DASHED \<Longrightarrow> rename_func_on dash xs"
  by (auto simp add:rename_func_on_def)

lemma undash_DASHED_rename_func [closure]:
  "xs \<subseteq> DASHED \<Longrightarrow> rename_func_on undash xs"
  apply (auto simp add:rename_func_on_def)
  apply (metis subset_inj_on undash_inj_on_DASHED)
done

lemma undash_DASHED_TWICE_rename_func [closure]:
  "xs \<subseteq> DASHED_TWICE \<Longrightarrow> rename_func_on undash xs"
  apply (auto simp add:rename_func_on_def)
  apply (metis subset_inj_on undash_inj_on_DASHED_TWICE)
done

lemma dash_dash_UNDASHED_rename_func [closure]:
  "xs \<subseteq> UNDASHED \<Longrightarrow> rename_func_on (dash \<circ> dash) xs"
  by (auto intro: closure)

definition rename_on ::
  "('a uvar \<Rightarrow> 'a uvar) 
   \<Rightarrow> ('a uvar) set
   \<Rightarrow> 'a VAR_RENAME" (infix "on" 100) where
"rename_on f vs = Abs_VAR_RENAME (complete_inj f vs)"

lemma rename_on_empty [simp]:
  "rename_on f {} = id\<^sub>s"
  by (metis complete_inj_empty rename_id_def rename_on_def)

lemma rename_on_VAR_RENAME [closure]:
  "rename_func_on f vs \<Longrightarrow>
   complete_inj f vs \<in> VAR_RENAME"
  apply (erule rename_func_onE)
  apply (simp add:VAR_RENAME_def)
  apply (rule)
  apply (metis bij_complete_inj)
  apply (rule)
  apply (case_tac "v \<in> vs")
  apply (simp_all)
  apply (case_tac "v \<in> f ` vs")
  apply (simp_all)
  apply (metis f_inv_into_f)
done

lemma rename_on_rep_eq:
  "rename_func_on f vs \<Longrightarrow>
     \<langle>rename_on f vs\<rangle>\<^sub>s = complete_inj f vs"
  by (metis Abs_VAR_RENAME_inverse rename_on_VAR_RENAME rename_on_def)

lemma rename_on_split:
  "\<lbrakk> rename_func_on f vs; vs = vs1 \<union> vs2; vs1 \<inter> vs2 = {} \<rbrakk> \<Longrightarrow>
     f on vs1 \<circ>\<^sub>s f on vs2 = f on vs"
  apply (rule)
  apply (subgoal_tac "rename_func_on f vs1")
  apply (subgoal_tac "rename_func_on f vs2")
  apply (simp add:rename_on_rep_eq)
  apply (auto)
  apply (auto simp add:rename_func_on_def)
  apply (metis inj_on_Un)+
done

lemma rename_on_image:
  "rename_func_on f vs1 \<Longrightarrow> 
     f on vs1 `\<^sub>s vs2 = 
     f ` (vs2 \<inter> vs1) \<union> inv_into vs1 f ` (vs2 \<inter> f ` vs1) \<union> (vs2 \<inter> -(vs1 \<union> f ` vs1))"
  apply (simp add:rename_on_rep_eq)
  apply (erule rename_func_onE)
  apply (simp)
done

lemma rename_on_perm1:
  fixes x :: "'a uvar"
  assumes "rename_func_on f vs" "x \<in> vs"
  shows "(f on vs)\<bullet>x = f x"
  by (simp add:rename_on_rep_eq assms)

lemma rename_on_perm2:
  fixes x :: "'a uvar"
  assumes "rename_func_on f vs" "x \<notin> vs" "x \<in> f ` vs"
  shows "(f on vs)\<bullet>x = inv_into vs f x"
  by (simp add:rename_on_rep_eq assms)

lemma rename_on_perm3:
  fixes x :: "'a uvar"
  assumes "rename_func_on f vs" "x \<notin> vs" "x \<notin> f ` vs"
  shows "(f on vs)\<bullet>x = x"
  by (simp add:rename_on_rep_eq assms)

lemma rename_on_image1 [simp]: 
  "rename_func_on f vs \<Longrightarrow> \<langle>f on vs\<rangle>\<^sub>s ` vs = f ` vs" 
  by (metis image_cong rename_on_perm1)

lemma rename_on_image2 [simp]: 
  "rename_func_on f vs \<Longrightarrow> \<langle>f on vs\<rangle>\<^sub>s ` f ` vs = vs"
  by (metis (hide_lams, no_types) Rep_VAR_RENAME_inj image_inv_f_f inv_complete_inj rename_func_on_def rename_inv_rep_eq rename_on_image1 rename_on_rep_eq)

lemma rename_func_on_subset:
  "\<lbrakk> rename_func_on f B; A \<subseteq> B \<rbrakk> \<Longrightarrow> rename_func_on f A"
  apply (auto simp add:rename_func_on_def)
  apply (metis subset_inj_on)
  apply (metis IntI empty_iff imageI in_mono)
done

lemma rename_func_on_vtype:
  "\<lbrakk> rename_func_on f vs; x \<in> vs \<rbrakk> \<Longrightarrow> vtype (f x) = vtype x"
  by (metis Rep_VAR_RENAME_type rename_on_perm1)


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
  "('a uvar) set \<Rightarrow> 'a VAR_RENAME set" where
"VAR_RENAME_ON vs =
 {ss. (\<forall> v . v \<notin> vs \<longrightarrow> \<langle>ss\<rangle>\<^sub>s v = v)}"

text {* Variable renamings that are also involutions. *}

definition VAR_RENAME_INV :: "'a VAR_RENAME set" where
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

theorem VAR_RENAME_ON_rename_on [closure]:
  "rename_func_on f vs \<Longrightarrow>
   rename_on f vs \<in> VAR_RENAME_ON (vs \<union> f ` vs)"
  by (simp add:VAR_RENAME_ON_def rename_on_rep_eq)

text {* Theorems about @{term "VAR_RENAME_INV"} *}

theorem VAR_RENAME_INV_inv_closure [closure] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow> (inv\<^sub>s ss) \<in> VAR_RENAME_INV"
apply (simp add: VAR_RENAME_INV_def)
done

text {* Should the following theorem be a default simplifications? *}

text {* This causes a loop though when simplifying @{term VAR_RENAME_INV}. *}

theorem VAR_RENAME_INV_inv [simp]:
"ss \<in> VAR_RENAME_INV \<Longrightarrow> (inv\<^sub>s ss) = ss"
apply (simp add: VAR_RENAME_INV_def)
done

theorem VAR_RENAME_INV_inv' [simp]:
"ss \<in> VAR_RENAME_INV \<Longrightarrow> (inv \<langle>ss\<rangle>\<^sub>s) = \<langle>ss\<rangle>\<^sub>s"
  by (metis VAR_RENAME_INV_inv rename_inv_rep_eq)

theorem VAR_RENAME_INV_comp [simp] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow> (ss \<circ>\<^sub>s ss) = id\<^sub>s"
apply (rule Rep_VAR_RENAME_intro)
apply (simp)
apply (unfold VAR_RENAME_INV_def)
apply (simp)
apply (erule Rep_VAR_RENAME_elim)
apply (erule ssubst) back
apply (simp)
done

theorem VAR_RENAME_INV_app [simp] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s (\<langle>ss\<rangle>\<^sub>s x) = x"
  by (metis VAR_RENAME_INV_comp id_apply o_eq_dest_lhs rename_comp_rep_eq rename_id_rep_eq)

theorem VAR_RENAME_INV_comp' [simp] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s \<circ> \<langle>ss\<rangle>\<^sub>s = id"
  by (metis VAR_RENAME_INV_comp id_apply o_eq_dest_lhs rename_comp_rep_eq rename_id_rep_eq)

theorem VAR_RENAME_INV_rename_on [closure]:
  "\<lbrakk> rename_func_on f vs \<rbrakk> \<Longrightarrow>
   rename_on f vs \<in> VAR_RENAME_INV"
  unfolding VAR_RENAME_INV_def by (force simp add: rename_on_rep_eq)

lemma inv_rename_func_on:
  "rename_func_on f vs \<Longrightarrow> inv\<^sub>s (f on vs) = f on vs"
  by (metis VAR_RENAME_INV_inv VAR_RENAME_INV_rename_on)

lemma inv_rename_func_on' [simp]: 
  "rename_func_on f A \<Longrightarrow> inv \<langle>f on A\<rangle>\<^sub>s = \<langle>f on A\<rangle>\<^sub>s"
  by (metis VAR_RENAME_INV_inv' VAR_RENAME_INV_rename_on)

subsection {* Binding Renaming *}

definition CompB ::   
  "'a binding \<Rightarrow>
   'a VAR_RENAME \<Rightarrow>
   'a binding" where
"CompB b ss = Abs_binding (\<langle>b\<rangle>\<^sub>b \<circ> \<langle>ss\<rangle>\<^sub>s)"

lemma CompB_rep_eq [simp]:
  "\<langle>CompB b ss\<rangle>\<^sub>b = \<langle>b\<rangle>\<^sub>b \<circ> \<langle>ss\<rangle>\<^sub>s"
  by (simp add:CompB_def closure)

definition RenameB ::
  "'a VAR_RENAME \<Rightarrow>
   'a binding \<Rightarrow>
   'a binding" where
"RenameB ss b = CompB b (inv\<^sub>s ss)"

adhoc_overloading
  permute RenameB

lemma RenameB_rep_eq [simp]:
  "\<langle>ss \<bullet> b\<rangle>\<^sub>b = \<langle>b\<rangle>\<^sub>b \<circ> inv \<langle>ss\<rangle>\<^sub>s"
  by (simp add:RenameB_def)

lemma VAR_RENAME_INV_image_twice [urename]:
  "ss \<in> VAR_RENAME_INV \<Longrightarrow> \<langle>ss\<rangle>\<^sub>s ` \<langle>ss\<rangle>\<^sub>s ` vs = vs"
  by (auto)

subsection {* Building renamings from a partial map *}

definition MapR ::
  "('a uvar \<rightharpoonup> 'a uvar) \<Rightarrow>
   'a VAR_RENAME" where
"MapR f = Abs_VAR_RENAME (MapRename f)"

lemma MapR_rep_eq [simp]:
  assumes "length xs = length ys" "distinct xs" "distinct ys" 
          "set xs \<inter> set ys = {}" "\<forall>i<length xs. vtype (xs!i) = vtype (ys!i) \<and> aux (xs!i) = aux (ys!i)"

  shows "\<langle>MapR [xs [\<mapsto>] ys]\<rangle>\<^sub>s = MapRename [xs [\<mapsto>] ys]"
  by (simp add:MapR_def closure assms)

lemma MapR_rep_eq_one [simp]:
  assumes "x \<noteq> y" "vtype x = vtype y" "aux x = aux y"
  shows "\<langle>MapR [x \<mapsto> y]\<rangle>\<^sub>s = MapRename [x \<mapsto> y]"
  by (simp add:MapR_def closure assms)

lemma VAR_RENAME_ON_MapR:
  assumes "length xs = length ys" "distinct xs" "distinct ys" 
          "set xs \<inter> set ys = {}"   
          "\<forall>i<length xs. vtype (xs!i) = vtype (ys!i) \<and> aux (xs!i) = aux (ys!i)"
  shows "MapR [xs [\<mapsto>] ys] \<in> VAR_RENAME_ON (set xs \<union> set ys)"
  using assms
  by (simp add:VAR_RENAME_ON_def MapR_rep_eq)

(*
lemma MapR_split: 
  assumes "length xs = length ys" "distinct xs" "distinct ys" 
          "set xs \<inter> set ys = {}" 
          "\<forall>i<length xs. vtype (xs!i) = vtype (ys!i) \<and> aux (xs!i) = aux (ys!i)"
          "x \<in> set xs" "y \<in> set ys" "vtype x = vtype y" "aux x = aux y"
  shows "MapR [xs [\<mapsto>] ys] = MapR [x \<mapsto> y] \<circ>\<^sub>s MapR [remove1 x xs [\<mapsto>] remove1 y ys]"
proof -

  from assms have "x \<noteq> y"
    by auto

  moreover from assms have "length (remove1 x xs) = length (remove1 y ys)"
    by (metis length_remove1)

  moreover from assms have "distinct (remove1 x xs)" "distinct (remove1 y ys)"
    by (metis distinct_remove1)+

  moreover from assms have  "set (remove1 x xs) \<inter> set (remove1 y ys) = {}" 
    by (auto)

  moreover
  from assms have "\<forall>i<length (remove1 y ys)
                   . vtype (remove1 x xs ! i) = vtype (remove1 y ys ! i) 
                   \<and> aux (remove1 x xs ! i) = aux (remove1 y ys ! i)"
    sorry

  ultimately show ?thesis using assms
    apply (rule_tac Rep_VAR_RENAME_intro)
    apply (simp add:MapR_rep_eq)
    apply (rule ext)
    apply (case_tac "xa \<in> set (remove1 x xs)")
    apply (simp)
  sorry
qed
*)

subsubsection {* Binding Renaming Laws *}

(*
theorem RenameB_closure [closure] :
"\<lbrakk>ss \<in> VAR_RENAME;
 b \<in> binding\<rbrakk> \<Longrightarrow>
 RenameB ss b \<in> binding"
apply (simp add: RenameB_def closure)
done
*)

lemma binding_VAR_RENAME [closure]: "\<langle>b\<rangle>\<^sub>b \<circ> inv \<langle>ss\<rangle>\<^sub>s \<in> binding"
  by (metis Rep_VAR_RENAME Rep_binding VAR_RENAME_binding VAR_RENAME_inv)

theorem RenameB_inject [simp]:
  fixes b1 :: "'a binding" 
  shows "(ss\<bullet>b1 = ss\<bullet>b2) = (b1 = b2)"
  by (force simp add:RenameB_def CompB_rep_eq)

theorem RenameB_id [simp] :
  fixes b :: "'a binding" 
  shows "id\<^sub>s\<bullet>b = b"
  by (auto simp add: RenameB_def CompB_rep_eq closure)

theorem RenameB_compose :
  fixes b :: "'a binding" 
  shows "ss1\<bullet>(ss2\<bullet>b) = (ss1 \<circ>\<^sub>s ss2)\<bullet>b"
  by (auto simp add: RenameB_def closure o_assoc CompB_rep_eq)

theorem RenameB_commute :
"\<lbrakk>ss1 \<in> VAR_RENAME_ON vs1;
 ss2 \<in> VAR_RENAME_ON vs2;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss1\<bullet>ss2\<bullet>(b :: 'a binding) = ss2\<bullet>ss1\<bullet>b"
apply (simp add: RenameB_compose)
apply (subgoal_tac "ss1 \<circ>\<^sub>s ss2 = ss2 \<circ>\<^sub>s ss1")
apply (simp)
apply (metis Rep_VAR_RENAME_inverse VAR_RENAME_ON_commute rename_comp_rep_eq)
done

theorem RenameB_inv_cancel1 [simp] :
  fixes b :: "'a binding" 
  shows "(inv\<^sub>s ss)\<bullet>ss\<bullet>b = b"
  by (force simp add: RenameB_def closure CompB_rep_eq)

theorem RenameB_inv_cancel2 [simp] :
  fixes b :: "'a binding" 
  shows "ss\<bullet>(inv\<^sub>s ss)\<bullet>b = b"
  by (force simp add: RenameB_def closure CompB_rep_eq)

theorem RenameB_override_distr1 :
"ss\<bullet>(b1 \<oplus>\<^sub>b b2 on vs) = (ss\<bullet>b1) \<oplus>\<^sub>b (ss\<bullet>b2) on (\<langle>ss\<rangle>\<^sub>s ` vs)"
apply (simp add: RenameB_def closure)
apply (rule Rep_binding_intro)
apply (simp add: closure CompB_rep_eq)
apply (simp add: override_on_def)
apply (rule ext)
apply (clarsimp)
apply (auto)
apply (subgoal_tac "a = \<langle>ss\<rangle>\<^sub>s (inv \<langle>ss\<rangle>\<^sub>s a)")
apply (simp_all)
done

theorem RenameB_override_distr2 :
"(ss\<bullet>b1) \<oplus>\<^sub>b (ss\<bullet>b2) on (\<langle>ss\<rangle>\<^sub>s ` vs) = ss\<bullet>(b1 \<oplus>\<^sub>b b2 on vs)"
  by (simp add: RenameB_override_distr1)

theorem RenameB_override_distr3 :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 ss\<bullet>(b1 \<oplus>\<^sub>b b2 on vs2) = (RenameB ss b1) \<oplus>\<^sub>b (RenameB ss b2) on vs2"
apply (subst RenameB_override_distr1 [of ss b1 b2 vs2])
apply (metis VAR_RENAME_ON_disj_image rename_image_def)
done

theorem RenameB_override_distr4 :
"\<lbrakk>ss \<in> VAR_RENAME_ON vs1;
 vs1 \<inter> vs2 = {}\<rbrakk> \<Longrightarrow>
 (RenameB ss b1) \<oplus>\<^sub>b (RenameB ss b2) on vs2 = RenameB ss (b1 \<oplus>\<^sub>b b2 on vs2)"
apply (simp add: RenameB_override_distr3)
done

lemma binding_override_RENAME_ON_overshadow [simp]:
  "\<lbrakk> ss \<in> VAR_RENAME_ON vs \<rbrakk> \<Longrightarrow> RenameB ss b1 \<oplus>\<^sub>b b2 on vs = b1 \<oplus>\<^sub>b b2 on vs"
  apply (auto simp add:VAR_RENAME_ON_def)
  apply (rule, rule)
  apply (auto)
  apply (case_tac "x \<in> vs")
  apply (auto)
  apply (metis Rep_VAR_RENAME_inj in_mono inv_f_eq)
done

theorem RenameB_involution [simp] :
"ss \<in> VAR_RENAME_INV \<Longrightarrow>
 RenameB ss (RenameB ss b) = b"
apply (subgoal_tac "ss \<circ>\<^sub>s ss = id\<^sub>s")
apply (simp add: RenameB_compose)
apply (force simp add:closure)
done

lemma var_compat_rename [typing]: 
  "v \<rhd> x \<Longrightarrow> v \<rhd> \<langle>ss\<rangle>\<^sub>s x"
  by (metis (lifting) Rep_VAR_RENAME_aux Rep_VAR_RENAME_type var_compat_def)

lemma vcoerce_perm [simp]:
  "vcoerce v (ss\<bullet>x) = vcoerce v x"
  by (auto simp add:vcoerce_def var_compat_def)

lemma RenameB_binding_upd_1 :
  "RenameB ss (b(x :=\<^sub>b v)) = (RenameB ss b)(\<langle>ss\<rangle>\<^sub>s x :=\<^sub>b v)"
  by (force simp add:RenameB_rep_eq binding_upd.rep_eq typing)

lemma RenameB_binding_upd_2 [simp]:
  "(RenameB ss b)(x :=\<^sub>b v) = RenameB ss (b(inv \<langle>ss\<rangle>\<^sub>s x :=\<^sub>b v))"
  apply (rule Rep_binding_intro)
  apply (auto simp add:binding_upd.rep_eq fun_upd_def)
  apply (rule ext, auto)
  apply (metis rename_inv_rep_eq vcoerce_perm)
  apply (metis Rep_VAR_RENAME_surj UNIV_I inv_into_injective)
done

lemma RenameB_override_VAR_RENAME_ON:
  "ss \<in> VAR_RENAME_ON vs \<Longrightarrow> RenameB ss b = RenameB ss b \<oplus>\<^sub>b b on - vs"
  apply (rule, rule ext)
  apply (case_tac "x \<in> vs")
  apply (auto simp add:VAR_RENAME_ON_def)
  apply (metis Rep_VAR_RENAME_inj inv_f_eq)
done

lemma RenameB_equiv_VAR_RENAME_ON_1 [intro]:
  "ss \<in> VAR_RENAME_ON (- vs) \<Longrightarrow> RenameB ss b \<cong> b on vs"
  by (metis RenameB_override_VAR_RENAME_ON binding_override_equiv1 binding_override_minus)

lemma RenameB_equiv_VAR_RENAME_ON_2 [intro]:
  "ss \<in> VAR_RENAME_ON (- vs) \<Longrightarrow> b \<cong> RenameB ss b on vs"
  by (metis RenameB_equiv_VAR_RENAME_ON_1 binding_equiv_comm)

lemma RenameB_equiv_cong: 
  "b1 \<cong> b2 on vs \<Longrightarrow> RenameB ss b1 \<cong> RenameB ss b2 on (ss `\<^sub>s vs)"
  by (auto simp add: binding_equiv_def)

text {* Subscript addition permutation *}

lift_definition SUB :: "nat \<Rightarrow> 'a VAR_RENAME" is "(\<lambda> x y. vchsub y x)"
  by (simp add:VAR_RENAME_def add_sub_bij)

lemma SUB_rename_func_on [closure]:
  "rename_func_on (add_sub n) NOSUB"
  apply (auto simp add:rename_func_on_def)
  apply (metis (no_types) add_sub_inv inj_onI)
  apply (simp add: NOSUB_def)
done

lemma SUB_var [urename]:
  fixes x :: "'m uvar"
  shows "SUB n\<bullet>x = x\<^bsub>n\<^esub>"
  by (simp add:SUB.rep_eq)

definition "USUB n \<equiv> (add_sub n) on (UNDASHED \<inter> NOSUB)"

lemma USUB_rename_func_on [closure]:
  "rename_func_on (add_sub n) (UNDASHED \<inter> NOSUB)"
  apply (auto simp add:rename_func_on_def)
  apply (metis (full_types) add_sub_inv inj_on_inverseI)
  apply (metis (mono_tags) NOSUB_def SUBSCRIPT.distinct(1) mem_Collect_eq vsub_NOSUB)
done

lemma USUB_UNDASHED_NOSUB [urename]:
  assumes "x \<in> UNDASHED" "x \<in> NOSUB"
  shows "USUB n\<bullet>x = x\<^bsub>n\<^esub>"
  by (simp add:USUB_def closure rename_on_perm1 assms)

lemma USUB_DASHED [urename]:
  "x \<in> DASHED \<Longrightarrow> USUB n\<bullet>x = x"
  apply (subgoal_tac "x \<notin> (UNDASHED \<inter> NOSUB)")
  apply (subgoal_tac "x \<notin> add_sub n ` (UNDASHED \<inter> NOSUB)")
  apply (simp add:USUB_def closure rename_on_perm3 assms)
  apply (auto simp add:var_defs)
done

definition "DSUB n \<equiv> (add_sub n) on (DASHED \<inter> NOSUB)"

lemma DSUB_rename_func_on [closure]:
  "rename_func_on (add_sub n) (DASHED \<inter> NOSUB)"
  apply (auto simp add:rename_func_on_def)
  apply (metis (full_types) add_sub_inv inj_on_inverseI)
  apply (metis (mono_tags) NOSUB_def SUBSCRIPT.distinct(1) mem_Collect_eq vsub_NOSUB)
done

lemma DSUB_DASHED_NOSUB [urename]:
  assumes "x \<in> DASHED" "x \<in> NOSUB"
  shows "DSUB n\<bullet>x = x\<^bsub>n\<^esub>"
  by (simp add:DSUB_def closure rename_on_perm1 assms)

lemma DSUB_UNDASHED [urename]:
  "x \<in> UNDASHED \<Longrightarrow> DSUB n\<bullet>x = x"
  apply (subgoal_tac "x \<notin> (DASHED \<inter> NOSUB)")
  apply (subgoal_tac "x \<notin> add_sub n ` (DASHED \<inter> NOSUB)")
  apply (simp add:DSUB_def closure rename_on_perm3)
  apply (auto simp add:var_defs)
done

text {* Some extra rename on laws *}

lemma rename_on_insert:
  "\<lbrakk> rename_func_on f (insert x xs); x \<notin> xs \<rbrakk> \<Longrightarrow> f on insert x xs \<bullet> b = (f on xs)\<bullet>b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b (f x), f x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x)"
  apply (subgoal_tac "rename_func_on f xs")
  apply (rule)
  apply (rule ext)
  apply (case_tac "xa = x")
  apply (simp add:rename_on_rep_eq)
  apply (auto)[1]
  apply (case_tac "xa = f(x)")
  apply (simp add:rename_on_rep_eq)
  apply (auto)[1]
  apply (auto)[1]
  apply (smt VAR_RENAME_INV_app VAR_RENAME_INV_rename_on insertI1 insertI2 inv_into_into rename_on_perm1 rename_on_perm2 rename_on_perm3)
  apply (auto simp add:rename_on_rep_eq rename_func_on_def)
  apply (metis complete_inj_inverse complete_inj_none)
  apply (metis (hide_lams, no_types) Diff_idemp Diff_insert_absorb complete_inj_insert_3 inj_on_insert)
done

end