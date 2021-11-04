(*  Title:       An Executable Simple Ordered Resolution Prover for First-Order Clauses
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2017, 2018
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2018
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>An Executable Simple Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
This theory provides an executable functional implementation of the
\<open>deterministic_RP\<close> prover, building on the \textsf{IsaFoR} library
for the notion of terms and on the Knuth--Bendix order.
\<close>

theory Executable_FO_Ordered_Resolution_Prover
  imports
    Deterministic_FO_Ordered_Resolution_Prover
    Executable_Subsumption
    "HOL-Library.Code_Target_Nat"
    Show.Show_Instances
    IsaFoR_Term
begin

global_interpretation RP: deterministic_FO_resolution_prover where
  S = "\<lambda>_. {#}" and
  subst_atm = "(\<cdot>)" and
  id_subst = "Var :: _ \<Rightarrow> ('f :: {weighted, compare_order}, nat) term" and
  comp_subst = "(\<circ>\<^sub>s)" and
  renamings_apart = renamings_apart and
  atm_of_atms = "Fun undefined" and
  mgu = mgu_sets and
  less_atm = less_kbo and
  size_atm = size and
  timestamp_factor = 1 and
  size_factor = 1
  defines deterministic_RP = RP.deterministic_RP
  and deterministic_RP_step = RP.deterministic_RP_step
  and is_final_dstate = RP.is_final_dstate
  and is_reducible_lit = RP.is_reducible_lit
  and is_tautology = RP.is_tautology
  and maximal_wrt = RP.maximal_wrt
  and reduce = RP.reduce
  and reduce_all = RP.reduce_all
  and reduce_all2 = RP.reduce_all2
  and remdups_clss = RP.remdups_clss
  and resolve = RP.resolve
  and resolve_on = RP.resolve_on
  and resolvable = RP.resolvable
  and resolvent = RP.resolvent
  and resolve_rename = RP.resolve_rename
  and resolve_rename_either_way = RP.resolve_rename_either_way
  and select_min_weight_clause = RP.select_min_weight_clause
  and strictly_maximal_wrt = RP.strictly_maximal_wrt
  and strictly_subsume = RP.strictly_subsume
  and subsume = RP.subsume
  and weight = RP.weight
  and St0 = RP.St0
  and sorted_list_of_set = "linorder.sorted_list_of_set (le_of_comp compare)"
  and sort_key = "linorder.sort_key (le_of_comp compare)"
  and insort_key = "linorder.insort_key (le_of_comp compare)"
  by (unfold_locales)
    (auto simp: less_kbo_subst is_ground_atm_ground less_kbo_less intro: ground_less_less_kbo)

declare
  RP.deterministic_RP.simps[code]
  RP.deterministic_RP_step.simps[code]
  RP.is_final_dstate.simps[code]
  RP.is_tautology_def[code]
  RP.reduce.simps[code]
  RP.reduce_all_def[code]
  RP.reduce_all2.simps[code]
  RP.resolve_rename_def[code]
  RP.resolve_rename_either_way_def[code]
  RP.select_min_weight_clause.simps[code]
  RP.weight.simps[code]
  St0_def[code]
  substitution_ops.strictly_subsumes_def[code]
  substitution_ops.subst_cls_lists_def[code]
  substitution_ops.subst_lit_def[code]
  substitution_ops.subst_cls_def[code]

lemma remove1_mset_subset_eq: "remove1_mset a A \<subseteq># B \<longleftrightarrow> A \<subseteq># add_mset a B"
  by (metis add_mset_add_single subset_eq_diff_conv)

lemma Bex_cong: "(\<And>b. b \<in> B \<Longrightarrow> P b = Q b) \<Longrightarrow> Bex B P = Bex B Q"
  by auto

lemma is_reducible_lit_code[code]: "RP.is_reducible_lit Ds C L =
  (\<exists>D \<in> set Ds. (\<exists>L' \<in> set D.
     if is_pos L' = is_neg L then
       (case match_term_list [(atm_of L', atm_of L)] Map.empty of
         None \<Rightarrow> False
       | Some \<sigma> \<Rightarrow> subsumes_list (remove1 L' D) C \<sigma>)
     else False))"
  unfolding RP.is_reducible_lit_def subsumes_list_alt subsumes_modulo_def
  apply (rule Bex_cong)+
  subgoal for D L'
    apply (split if_splits option.splits)+
    apply safe
    subgoal for \<sigma>
      using term_subst_eq[of _ "subst_of_map Var (\<lambda>x. if x \<in> vars_lit L' then Some (\<sigma> x) else None)" \<sigma>]
      by (cases L; cases L';
        auto simp add: subst_lit_def subst_of_map_def
          dest!:  match_term_list_complete[of _ _ "\<lambda>x. if x \<in> vars_lit L' then Some (\<sigma> x) else None"])
    subgoal for \<sigma>
      using term_subst_eq[of _ "subst_of_map Var (\<lambda>x. if x \<in> vars_lit L' then Some (\<sigma> x) else None)" \<sigma>]
      by (cases L; cases L';
        auto simp add: subst_lit_def subst_of_map_def
          dest!:  match_term_list_complete[of _ _ "\<lambda>x. if x \<in> vars_lit L' then Some (\<sigma> x) else None"])
    subgoal for \<sigma>
      by (cases L; cases L'; simp add: subst_lit_def)
    subgoal for \<sigma>
      by (cases L; cases L'; simp add: subst_lit_def)
    subgoal for \<sigma> \<tau>
      using same_on_vars_clause[of "mset (remove1 L' D)" "subst_of_map Var
        (\<lambda>x. if x \<in> vars_clause (remove1_mset L' (mset D)) \<union> dom \<sigma> then Some (\<tau> x) else None)" \<tau>]
      apply (cases L; cases L'; auto simp add: subst_lit_def dom_def subst_of_map_def
        dest!: match_term_list_sound split: option.splits if_splits
        intro!: exI[of _ "\<lambda>x. if x \<in> vars_clause (remove1_mset L' (mset D)) \<union> dom \<sigma> then Some (\<tau> x) else None"])
      by (auto 0 4 simp: extends_subst_def subst_of_map_def split: option.splits dest!: term_subst_eq_rev)
    subgoal for \<sigma> \<tau>
      by (cases L; cases L'; auto simp add: subst_lit_def subst_of_map_def extends_subst_def
        dest!: match_term_list_sound intro!: exI[of _ "subst_of_map Var \<tau>"] term_subst_eq)
    subgoal for \<sigma> \<tau>
      using same_on_vars_clause[of "mset (remove1 L' D)" "subst_of_map Var
        (\<lambda>x. if x \<in> vars_clause (remove1_mset L' (mset D)) \<union> dom \<sigma> then Some (\<tau> x) else None)" \<tau>]
      apply (cases L; cases L'; auto simp add: subst_lit_def dom_def subst_of_map_def
        dest!: match_term_list_sound split: option.splits if_splits
        intro!: exI[of _ "\<lambda>x. if x \<in> vars_clause (remove1_mset L' (mset D)) \<union> dom \<sigma> then Some (\<tau> x) else None"])
      by (auto 0 4 simp: extends_subst_def subst_of_map_def split: option.splits dest!: term_subst_eq_rev)
    subgoal for \<sigma> \<tau>
      by (cases L; cases L'; auto simp add: subst_lit_def subst_of_map_def extends_subst_def
        dest!: match_term_list_sound intro!: exI[of _ "subst_of_map Var \<tau>"] term_subst_eq)
    subgoal for \<sigma> \<tau>
      by (cases L; cases L'; simp add: subst_lit_def)
    subgoal for \<sigma> \<tau>
      by (cases L; cases L'; simp add: subst_lit_def)
    done
  done

declare
  Pairs_def[folded sorted_list_of_set_def, code]
  linorder.sorted_list_of_set_sort_remdups[OF class_linorder_compare,
    folded sorted_list_of_set_def sort_key_def, code]
  linorder.sort_key_def[OF class_linorder_compare, folded sort_key_def insort_key_def, code]
  linorder.insort_key.simps[OF class_linorder_compare, folded insort_key_def, code]

export_code St0 in SML
export_code deterministic_RP in SML module_name RP

(*arbitrary*)
instantiation nat :: weighted begin
definition weights_nat :: "nat weights" where "weights_nat =
  \<lparr>w = Suc \<circ> prod_encode, w0 = 1, pr_strict = \<lambda>(f, n) (g, m). f > g \<or> f = g \<and> n > m, least = \<lambda>n. n = 0, scf = \<lambda>_ _. 1\<rparr>"

instance
  by (intro_classes, unfold_locales)
    (auto simp: weights_nat_def SN_iff_wf asymp.simps irreflp_def prod_encode_def
      intro!: wf_subset[OF wf_lex_prod])
end

definition prover :: "((nat, nat) Term.term literal list \<times> nat) list \<Rightarrow> bool" where
  "prover N = (case deterministic_RP (St0 N 0) of
      None \<Rightarrow> True
    | Some R \<Rightarrow> [] \<notin> set R)"

theorem prover_complete_refutation: "prover N \<longleftrightarrow> satisfiable (RP.grounded_N0 N)"
  unfolding prover_def St0_def
  using RP.deterministic_RP_complete[of N 0] RP.deterministic_RP_refutation[of N 0]
  by (force simp: grounding_of_clss_def grounding_of_cls_def ex_ground_subst
    split: option.splits if_splits)

definition string_literal_of_nat :: "nat \<Rightarrow> String.literal" where
  "string_literal_of_nat n = String.implode (show n)"

export_code prover Fun Var Pos Neg string_literal_of_nat "0::nat" "Suc" in SML module_name RPx

abbreviation "\<pp> \<equiv> Fun 42"
abbreviation "\<aa> \<equiv> Fun 0 []"
abbreviation "\<bb> \<equiv> Fun 1 []"
abbreviation "\<cc> \<equiv> Fun 2 []"
abbreviation "X \<equiv> Var 0"
abbreviation "Y \<equiv> Var 1"
abbreviation "Z \<equiv> Var 2"

value "prover
  ([([Neg (\<pp>[X,Y,Z]), Pos (\<pp>[Y,Z,X])], 1),
    ([Pos (\<pp>[\<cc>,\<aa>,\<bb>])], 1),
    ([Neg (\<pp>[\<bb>,\<cc>,\<aa>])], 1)]
  :: ((nat, nat) Term.term literal list \<times> nat) list)"

value "prover
  ([([Pos (\<pp>[X,Y])], 1), ([Neg (\<pp>[X,X])], 1)]
  :: ((nat, nat) Term.term literal list \<times> nat) list)"

value "prover ([([Neg (\<pp>[X,Y,Z]), Pos (\<pp>[Y,Z,X])], 1)]
  :: ((nat, nat) Term.term literal list \<times> nat) list)"

definition mk_MSC015_1 :: "nat \<Rightarrow> ((nat, nat) Term.term literal list \<times> nat) list" where
  "mk_MSC015_1 n =
     (let
       init = ([Pos (\<pp> (replicate n \<aa>))], 1);
       rules = map (\<lambda>i. ([Neg (\<pp> (map Var [0 ..< n - i - 1] @ \<aa> # replicate i \<bb>)),
                         Pos (\<pp> (map Var [0 ..< n - i - 1] @ \<bb> # replicate i \<aa>))], 1)) [0 ..< n];
       goal = ([Neg (\<pp> (replicate n \<bb>))], 1)
     in init # rules @ [goal])"

value "prover (mk_MSC015_1 1)"
value "prover (mk_MSC015_1 2)"
value "prover (mk_MSC015_1 3)"
value "prover (mk_MSC015_1 4)"
value "prover (mk_MSC015_1 5)"
value "prover (mk_MSC015_1 10)"

lemma
  assumes
     "p a a a a a a a a a a a a a a"
     "(\<forall>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.
       \<not> p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 a \<or>
       p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 b)"
     "(\<forall>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.
       \<not> p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 a b \<or>
       p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 b a)"
     "(\<forall>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.
       \<not> p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 a b b \<or>
       p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 b a a)"
     "(\<forall>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.
       \<not> p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 a b b b \<or>
       p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 b a a a)"
     "(\<forall>x1 x2 x3 x4 x5 x6 x7 x8 x9.
       \<not> p x1 x2 x3 x4 x5 x6 x7 x8 x9 a b b b b \<or>
       p x1 x2 x3 x4 x5 x6 x7 x8 x9 b a a a a)"
     "(\<forall>x1 x2 x3 x4 x5 x6 x7 x8.
       \<not> p x1 x2 x3 x4 x5 x6 x7 x8 a b b b b b \<or>
       p x1 x2 x3 x4 x5 x6 x7 x8 b a a a a a)"
     "(\<forall>x1 x2 x3 x4 x5 x6 x7.
       \<not> p x1 x2 x3 x4 x5 x6 x7 a b b b b b b \<or>
       p x1 x2 x3 x4 x5 x6 x7 b a a a a a a)"
     "(\<forall>x1 x2 x3 x4 x5 x6.
       \<not> p x1 x2 x3 x4 x5 x6 a b b b b b b b \<or>
       p x1 x2 x3 x4 x5 x6 b a a a a a a a)"
     "(\<forall>x1 x2 x3 x4 x5.
       \<not> p x1 x2 x3 x4 x5 a b b b b b b b b \<or>
       p x1 x2 x3 x4 x5 b a a a a a a a a)"
     "(\<forall>x1 x2 x3 x4.
       \<not> p x1 x2 x3 x4 a b b b b b b b b b \<or>
       p x1 x2 x3 x4 b a a a a a a a a a)"
     "(\<forall>x1 x2 x3.
       \<not> p x1 x2 x3 a b b b b b b b b b b \<or>
       p x1 x2 x3 b a a a a a a a a a a)"
     "(\<forall>x1 x2.
       \<not> p x1 x2 a b b b b b b b b b b b \<or>
       p x1 x2 b a a a a a a a a a a a)"
     "(\<forall>x1.
       \<not> p x1 a b b b b b b b b b b b b \<or>
       p x1 b a a a a a a a a a a a a)"
     "(\<not> p a b b b b b b b b b b b b b \<or>
       p b a a a a a a a a a a a a a)"
     "\<not> p b b b b b b b b b b b b b b"
   shows False
  using assms by metis

end
