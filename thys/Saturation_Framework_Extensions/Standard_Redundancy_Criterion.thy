(*  Title:       Counterexample-Reducing Inference Systems and the Standard Redundancy Criterion
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
*)

section \<open>Counterexample-Reducing Inference Systems and the Standard Redundancy Criterion\<close>

theory Standard_Redundancy_Criterion
  imports
    Saturation_Framework.Calculus
    "HOL-Library.Multiset_Order"
begin

text \<open>
The standard redundancy criterion can be defined uniformly for all inference systems equipped with
a compact consequence relation. The essence of the refutational completeness argument can be carried
out abstractly for counterexample-reducing inference systems, which enjoy a ``smallest
counterexample'' property. This material is partly based on Section 4.2 of Bachmair and Ganzinger's
\emph{Handbook} chapter, but adapted to the saturation framework of Waldmann et al.
\<close>


subsection \<open>Counterexample-Reducing Inference Systems\<close>

abbreviation main_prem_of :: "'f inference \<Rightarrow> 'f" where
  "main_prem_of \<iota> \<equiv> last (prems_of \<iota>)"

abbreviation side_prems_of :: "'f inference \<Rightarrow> 'f list" where
  "side_prems_of \<iota> \<equiv> butlast (prems_of \<iota>)"

lemma set_prems_of:
  "set (prems_of \<iota>) = (if prems_of \<iota> = [] then {} else {main_prem_of \<iota>} \<union> set (side_prems_of \<iota>))"
  by clarsimp (metis Un_insert_right append_Nil2 append_butlast_last_id list.set(2) set_append)

locale counterex_reducing_inference_system = inference_system Inf + consequence_relation
  for Inf :: "('f :: wellorder) inference set" +
  fixes I_of :: "'f set \<Rightarrow> 'f set"
  assumes Inf_counterex_reducing:
    "N \<inter> Bot = {} \<Longrightarrow> D \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> {D} \<Longrightarrow> (\<And>C. C \<in> N \<Longrightarrow> \<not> I_of N \<Turnstile> {C} \<Longrightarrow> D \<le> C) \<Longrightarrow>
     \<exists>\<iota> \<in> Inf. prems_of \<iota> \<noteq> [] \<and> main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N \<and> I_of N
         \<Turnstile> set (side_prems_of \<iota>)
       \<and> \<not> I_of N \<Turnstile> {concl_of \<iota>} \<and> concl_of \<iota> < D"
begin

lemma ex_min_counterex:
  fixes N :: "('f :: wellorder) set"
  assumes "\<not> I \<Turnstile> N"
  shows "\<exists>C \<in> N. \<not> I \<Turnstile> {C} \<and> (\<forall>D \<in> N. D < C \<longrightarrow> I \<Turnstile> {D})"
proof -
  obtain C where
    "C \<in> N" and "\<not> I \<Turnstile> {C}"
    using assms all_formulas_entailed by blast
  then have c_in: "C \<in> {C \<in> N. \<not> I \<Turnstile> {C}}"
    by blast
  show ?thesis
    using wf_eq_minimal[THEN iffD1, rule_format, OF wellorder_class.wf c_in] by blast
qed

end

text \<open>
Theorem 4.4 (generalizes Theorems 3.9 and 3.16):
\<close>

locale counterex_reducing_inference_system_with_trivial_redundancy =
  counterex_reducing_inference_system _ _ Inf + calculus _ Inf _ "\<lambda>_. {}" "\<lambda>_. {}"
  for Inf :: "('f :: wellorder) inference set"
begin

theorem saturated_model:
  assumes
    satur: "saturated N" and
    bot_ni_n: "N \<inter> Bot = {}"
  shows "I_of N \<Turnstile> N"
proof (rule ccontr)
  assume "\<not> I_of N \<Turnstile> N"
  then obtain D :: 'f where
    d_in_n: "D \<in> N" and
    d_cex: "\<not> I_of N \<Turnstile> {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> C < D \<Longrightarrow> I_of N \<Turnstile> {C}"
    by (meson ex_min_counterex)
  then obtain \<iota> :: "'f inference" where
    \<iota>_inf: "\<iota> \<in> Inf" and
    concl_cex: "\<not> I_of N \<Turnstile> {concl_of \<iota>}" and
    concl_lt_d: "concl_of \<iota> < D"
    using Inf_counterex_reducing[OF bot_ni_n] by force
  have "concl_of \<iota> \<in> N"
    using \<iota>_inf Red_I_of_Inf_to_N by blast
  then show False
    using concl_cex concl_lt_d d_min by blast
qed

text \<open>
An abstract version of Corollary 3.10 does not hold without some conditions, according to Nitpick:
\<close>

corollary saturated_complete:
  assumes
    satur: "saturated N" and
    unsat: "N \<Turnstile> Bot"
  shows "N \<inter> Bot \<noteq> {}"
  oops

end


subsection \<open>Compactness\<close>

locale concl_compact_consequence_relation = consequence_relation +
  assumes
    entails_concl_compact: "finite EE \<Longrightarrow> CC \<Turnstile> EE \<Longrightarrow> \<exists>CC' \<subseteq> CC. finite CC' \<and> CC' \<Turnstile> EE"
begin

lemma entails_concl_compact_union:
  assumes
    fin_e: "finite EE" and
    cd_ent: "CC \<union> DD \<Turnstile> EE"
  shows "\<exists>CC' \<subseteq> CC. finite CC' \<and> CC' \<union> DD \<Turnstile> EE"
proof -
  obtain CCDD' where
    cd1_fin: "finite CCDD'" and
    cd1_sub: "CCDD' \<subseteq> CC \<union> DD" and
    cd1_ent: "CCDD' \<Turnstile> EE"
    using entails_concl_compact[OF fin_e cd_ent] by blast

  define CC' where
    "CC' = CCDD' - DD"
  have "CC' \<subseteq> CC"
    unfolding CC'_def using cd1_sub by blast
  moreover have "finite CC'"
    unfolding CC'_def using cd1_fin by blast
  moreover have "CC' \<union> DD \<Turnstile> EE"
    unfolding CC'_def using cd1_ent
    by (metis Un_Diff_cancel2 Un_upper1 entails_trans subset_entailed)
  ultimately show ?thesis
    by blast
qed

end


subsection \<open>The Standard Redundancy Criterion\<close>

locale calculus_with_standard_redundancy =
  inference_system Inf + concl_compact_consequence_relation Bot entails
  for
    Inf :: "('f :: wellorder) inference set" and
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) +
  assumes
    Inf_has_prem: "\<iota> \<in> Inf \<Longrightarrow> prems_of \<iota> \<noteq> []" and
    Inf_reductive: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> < main_prem_of \<iota>"
begin

definition redundant_infer :: "'f set \<Rightarrow> 'f inference \<Rightarrow> bool" where
  "redundant_infer N \<iota> \<longleftrightarrow>
   (\<exists>DD \<subseteq> N. DD \<union> set (side_prems_of \<iota>) \<Turnstile> {concl_of \<iota>} \<and> (\<forall>D \<in> DD. D < main_prem_of \<iota>))"

definition Red_I :: "'f set \<Rightarrow> 'f inference set" where
  "Red_I N = {\<iota> \<in> Inf. redundant_infer N \<iota>}"

definition Red_F :: "'f set \<Rightarrow> 'f set" where
  "Red_F N = {C. \<exists>DD \<subseteq> N. DD \<Turnstile> {C} \<and> (\<forall>D \<in> DD. D < C)}"

text \<open>
The following results correspond to Lemma 4.5. The lemma \<open>wlog_non_Red_F\<close> generalizes the core of
the argument.
\<close>

lemma Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'"
  unfolding Red_F_def by fast

lemma wlog_non_Red_F:
  assumes
    dd0_sub: "DD0 \<subseteq> N" and
    dd0_ent: "DD0 \<union> CC \<Turnstile> {E}" and
    dd0_lt: "\<forall>D' \<in> DD0. D' < D"
  shows "\<exists>DD \<subseteq> N - Red_F N. DD \<union> CC \<Turnstile> {E} \<and> (\<forall>D' \<in> DD. D' < D)"
proof -
  obtain DD1 where
    "finite DD1" and
    "DD1 \<subseteq> N" and
    "DD1 \<union> CC \<Turnstile> {E}" and
    "\<forall>D' \<in> DD1. D' < D"
    using entails_concl_compact_union[OF _ dd0_ent] dd0_lt dd0_sub by fast
  then obtain DD2 :: "'f multiset" where
    "set_mset DD2 \<subseteq> N \<and> set_mset DD2 \<union> CC \<Turnstile> {E} \<and> (\<forall>D' \<in> set_mset DD2. D' < D)"
    using assms by (metis finite_set_mset_mset_set)
  hence dd2: "DD2 \<in> {DD. set_mset DD \<subseteq> N \<and> set_mset DD \<union> CC \<Turnstile> {E} \<and> (\<forall>D' \<in> set_mset DD. D' < D)}"
    by blast
  have "\<exists>DD. set_mset DD \<subseteq> N \<and> set_mset DD \<union> CC \<Turnstile> {E} \<and> (\<forall>D' \<in># DD. D' < D) \<and>
    (\<forall>DDa. set_mset DDa \<subseteq> N \<and> set_mset DDa \<union> CC \<Turnstile> {E} \<and> (\<forall>D' \<in># DDa. D' < D) \<longrightarrow> DD \<le> DDa)"
    using wf_eq_minimal[THEN iffD1, rule_format, OF wf_less_multiset, OF dd2]
    unfolding not_le[symmetric] by blast
  then obtain DD :: "'f multiset" where
    dd_subs_n: "set_mset DD \<subseteq> N" and
    ddcc_ent_e: "set_mset DD \<union> CC \<Turnstile> {E}" and
    dd_lt_d: "\<forall>D' \<in># DD. D' < D" and
    d_min: "\<forall>DDa. set_mset DDa \<subseteq> N \<and> set_mset DDa \<union> CC \<Turnstile> {E} \<and> (\<forall>D' \<in># DDa. D' < D) \<longrightarrow> DD \<le> DDa"
    by blast

  have "\<forall>Da \<in># DD. Da \<notin> Red_F N"
  proof clarify
    fix Da
    assume
      da_in_dd: "Da \<in># DD" and
      da_rf: "Da \<in> Red_F N"

    obtain DDa0 where
      "DDa0 \<subseteq> N"
      "finite DDa0"
      "DDa0 \<Turnstile> {Da}"
      "\<forall>D \<in> DDa0. D < Da"
      using da_rf unfolding Red_F_def mem_Collect_eq
      by (smt entails_concl_compact finite.emptyI finite.insertI subset_iff)
    then obtain DDa1 :: "'f multiset" where
      dda1_subs_n: "set_mset DDa1 \<subseteq> N" and
      dda1_ent_da: "set_mset DDa1 \<Turnstile> {Da}" and
      dda1_lt_da: "\<forall>D' \<in># DDa1. D' < Da"
      by (metis finite_set_mset_mset_set)

    define DDa :: "'f multiset" where
      "DDa = DD - {#Da#} + DDa1"

    have "set_mset DDa \<subseteq> N"
      unfolding DDa_def using dd_subs_n dda1_subs_n
      by (meson contra_subsetD in_diffD subsetI union_iff)
    moreover have "set_mset DDa \<union> CC \<Turnstile> {E}"
      by (rule entails_trans_strong[of _ "{Da}"],
          metis DDa_def dda1_ent_da entail_union entails_trans order_refl set_mset_union
            subset_entailed,
          smt DDa_def da_in_dd ddcc_ent_e entails_trans insert_DiffM2 set_mset_add_mset_insert
            set_mset_empty set_mset_union subset_entailed sup_assoc sup_commute sup_ge1)
    moreover have "\<forall>D' \<in># DDa. D' < D"
      using dd_lt_d dda1_lt_da da_in_dd unfolding DDa_def
      by (metis insert_DiffM2 order.strict_trans union_iff)
    moreover have "DDa < DD"
      unfolding DDa_def
      by (meson da_in_dd dda1_lt_da mset_lt_single_right_iff single_subset_iff union_le_diff_plus)
    ultimately show False
      using d_min unfolding less_eq_multiset_def by (auto intro!: antisym)
  qed
  then show ?thesis
    using dd_subs_n ddcc_ent_e dd_lt_d by blast
qed

lemma Red_F_imp_ex_non_Red_F:
  assumes c_in: "C \<in> Red_F N"
  shows "\<exists>CC \<subseteq> N - Red_F N. CC \<Turnstile> {C} \<and> (\<forall>C' \<in> CC. C' < C)"
proof -
  obtain DD :: "'f set" where
    dd_sub: "DD \<subseteq> N" and
    dd_ent: "DD \<Turnstile> {C}" and
    dd_lt: "\<forall>D \<in> DD. D < C"
    using c_in[unfolded Red_F_def] by fast
  show ?thesis
    by (rule wlog_non_Red_F[of "DD" N "{}" C C, simplified, OF dd_sub dd_ent dd_lt])
qed

lemma Red_F_subs_Red_F_diff_Red_F: "Red_F N \<subseteq> Red_F (N - Red_F N)"
proof
  fix C
  assume c_rf: "C \<in> Red_F N"
  then obtain CC :: "'f set" where
    cc_subs: "CC \<subseteq> N - Red_F N" and
    cc_ent_c: "CC \<Turnstile> {C}" and
    cc_lt_c: "\<forall>C' \<in> CC. C' < C"
    using Red_F_imp_ex_non_Red_F[of C N] by blast
  have "\<forall>D \<in> CC. D \<notin> Red_F N"
    using cc_subs by fast
  then have cc_nr:
    "\<forall>C \<in> CC. \<forall>DD \<subseteq> N. DD \<Turnstile> {C} \<longrightarrow> (\<exists>D \<in> DD. \<not> D < C)"
    unfolding Red_F_def by simp
  have "CC \<subseteq> N"
    using cc_subs by auto
  then have "CC \<subseteq> N - {C. \<exists>DD \<subseteq> N. DD \<Turnstile> {C} \<and> (\<forall>D \<in> DD. D < C)}"
    using cc_nr by blast
  then show "C \<in> Red_F (N - Red_F N)"
    using cc_ent_c cc_lt_c unfolding Red_F_def by blast
qed

lemma Red_F_eq_Red_F_diff_Red_F: "Red_F N = Red_F (N - Red_F N)"
  by (simp add: Red_F_of_subset Red_F_subs_Red_F_diff_Red_F set_eq_subset)

text \<open>
The following results correspond to Lemma 4.6. It also uses \<open>wlog_non_Red_F\<close>.
\<close>

lemma Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'"
  unfolding Red_I_def redundant_infer_def by auto

lemma Red_I_subs_Red_I_diff_Red_F: "Red_I N \<subseteq> Red_I (N - Red_F N)"
proof
  fix \<iota>
  assume \<iota>_ri: "\<iota> \<in> Red_I N"
  define CC :: "'f set" where
    "CC = set (side_prems_of \<iota>)"
  define D :: 'f where
    "D = main_prem_of \<iota>"
  define E :: 'f where
    "E = concl_of \<iota>"
  obtain DD :: "'f set" where
    dd_sub: "DD \<subseteq> N" and
    dd_ent: "DD \<union> CC \<Turnstile> {E}" and
    dd_lt_d: "\<forall>C \<in> DD. C < D"
    using \<iota>_ri unfolding Red_I_def redundant_infer_def CC_def D_def E_def by blast
  obtain DDa :: "'f set" where
    "DDa \<subseteq> N - Red_F N" and "DDa \<union> CC \<Turnstile> {E}" and "\<forall>D' \<in> DDa. D' < D"
    using wlog_non_Red_F[OF dd_sub dd_ent dd_lt_d] by blast
  then show "\<iota> \<in> Red_I (N - Red_F N)"
    using \<iota>_ri unfolding Red_I_def redundant_infer_def CC_def D_def E_def by blast
qed

lemma Red_I_eq_Red_I_diff_Red_F: "Red_I N = Red_I (N - Red_F N)"
  by (metis Diff_subset Red_I_of_subset Red_I_subs_Red_I_diff_Red_F subset_antisym)

lemma Red_I_to_Inf: "Red_I N \<subseteq> Inf"
  unfolding Red_I_def by blast

lemma Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')"
  by (metis Diff_mono Red_F_eq_Red_F_diff_Red_F Red_F_of_subset order_refl)

lemma Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')"
  by (metis Diff_mono Red_I_eq_Red_I_diff_Red_F Red_I_of_subset order_refl)

lemma Red_F_model: "M \<Turnstile> N - Red_F N \<Longrightarrow> M \<Turnstile> N"
  by (metis (no_types) DiffI Red_F_imp_ex_non_Red_F entail_set_all_formulas entails_trans
      subset_entailed)

lemma Red_F_Bot: "B \<in> Bot \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> N - Red_F N \<Turnstile> {B}"
  using Red_F_model entails_trans subset_entailed by blast

lemma Red_I_of_Inf_to_N:
  assumes
    in_\<iota>: "\<iota> \<in> Inf" and
    concl_in: "concl_of \<iota> \<in> N"
  shows "\<iota> \<in> Red_I N"
proof -
  have "concl_of \<iota> \<in> N \<Longrightarrow> redundant_infer N \<iota>"
    unfolding redundant_infer_def
    by (metis (no_types) Inf_reductive empty_iff empty_subsetI entail_union in_\<iota> insert_iff
        insert_subset subset_entailed subset_refl)
  then show "\<iota> \<in> Red_I N"
    by (simp add: Red_I_def concl_in in_\<iota>)
qed

text \<open>
The following corresponds to Theorems 4.7 and 4.8:
\<close>

sublocale calculus Bot Inf "(\<Turnstile>)" Red_I Red_F
  by (unfold_locales, fact Red_I_to_Inf, fact Red_F_Bot, fact Red_F_of_subset,
      fact Red_I_of_subset, fact Red_F_of_Red_F_subset, fact Red_I_of_Red_F_subset,
      fact Red_I_of_Inf_to_N)

end

locale counterex_reducing_calculus_with_standard_redundancy =
  calculus_with_standard_redundancy Inf + counterex_reducing_inference_system _ _ Inf
  for Inf :: "('f :: wellorder) inference set"
begin


subsection \<open>Refutational Completeness\<close>

text \<open>
The following result loosely corresponds to Theorem 4.9.
\<close>

lemma saturated_model:
  assumes
    satur: "saturated N" and
    bot_ni_n: "N \<inter> Bot = {}"
  shows "I_of N \<Turnstile> N"
proof (rule ccontr)
  assume "\<not> I_of N \<Turnstile> N"
  then obtain D :: 'f where
    d_in_n: "D \<in> N" and
    d_cex: "\<not> I_of N \<Turnstile> {D}" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> C < D \<Longrightarrow> I_of N \<Turnstile> {C}"
    using ex_min_counterex by blast
  then obtain \<iota> :: "'f inference" where
    \<iota>_in: "\<iota> \<in> Inf" and
    \<iota>_mprem: "D = main_prem_of \<iota>" and
    sprem_subs_n: "set (side_prems_of \<iota>) \<subseteq> N" and
    sprem_true: "I_of N \<Turnstile> set (side_prems_of \<iota>)" and
    concl_cex: "\<not> I_of N \<Turnstile> {concl_of \<iota>}" and
    concl_lt_d: "concl_of \<iota> < D"
    using Inf_counterex_reducing[OF bot_ni_n] not_le by metis
  have "\<iota> \<in> Red_I N"
    by (rule subsetD[OF satur[unfolded saturated_def Inf_from_def]],
        simp add: \<iota>_in set_prems_of Inf_has_prem)
      (use \<iota>_mprem d_in_n sprem_subs_n  in blast)
  then have "\<iota> \<in> Red_I N"
    using Red_I_without_red_F by blast
  then obtain DD :: "'f set" where
    dd_subs_n: "DD \<subseteq> N" and
    dd_cc_ent_d: "DD \<union> set (side_prems_of \<iota>) \<Turnstile> {concl_of \<iota>}" and
    dd_lt_d: "\<forall>C \<in> DD. C < D"
    unfolding Red_I_def redundant_infer_def \<iota>_mprem by blast
  from dd_subs_n dd_lt_d have "I_of N \<Turnstile> DD"
    using d_min by (meson ex_min_counterex subset_iff)
  then have "I_of N \<Turnstile> {concl_of \<iota>}"
    using entails_trans dd_cc_ent_d entail_union sprem_true by blast
  then show False
    using concl_cex by auto
qed

text \<open>
A more faithful abstract version of Theorem 4.9 does not hold without some conditions, according to
Nitpick:
\<close>

corollary saturated_complete:
  assumes
    satur: "saturated N" and
    unsat: "N \<Turnstile> Bot"
  shows "N \<inter> Bot \<noteq> {}"
  oops

end

end
