(*  Title:       Calculi Based on a Redundancy Criterion
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020 *)

section \<open>Calculi Based on a Redundancy Criterion\<close>

text \<open>This section introduces the most basic notions upon which the framework is
  built: consequence relations and inference systems. It also defines the notion
  of a family of consequence relations and of redundancy criteria. This
  corresponds to sections 2.1 and 2.2 of the report.\<close>

theory Calculus
  imports
    Ordered_Resolution_Prover.Lazy_List_Liminf
    Ordered_Resolution_Prover.Lazy_List_Chain
begin


subsection \<open>Consequence Relations\<close>

locale consequence_relation =
  fixes
    Bot :: "'f set" and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  assumes
    bot_not_empty: "Bot \<noteq> {}" and
    bot_entails_all: "B \<in> Bot \<Longrightarrow> {B} \<Turnstile> N1" and
    subset_entailed: "N2 \<subseteq> N1 \<Longrightarrow> N1 \<Turnstile> N2" and
    all_formulas_entailed: "(\<forall>C \<in> N2. N1 \<Turnstile> {C}) \<Longrightarrow> N1 \<Turnstile> N2" and
    entails_trans[trans]: "N1 \<Turnstile> N2 \<Longrightarrow> N2 \<Turnstile> N3 \<Longrightarrow> N1 \<Turnstile> N3"
begin

lemma entail_set_all_formulas: "N1 \<Turnstile> N2 \<longleftrightarrow> (\<forall>C \<in> N2. N1 \<Turnstile> {C})"
  by (meson all_formulas_entailed empty_subsetI insert_subset subset_entailed entails_trans)

lemma entail_union: "N \<Turnstile> N1 \<and> N \<Turnstile> N2 \<longleftrightarrow> N \<Turnstile> N1 \<union> N2"
  using entail_set_all_formulas[of N N1] entail_set_all_formulas[of N N2]
    entail_set_all_formulas[of N "N1 \<union> N2"] by blast

lemma entail_unions: "(\<forall>i \<in> I. N \<Turnstile> Ni i) \<longleftrightarrow> N \<Turnstile> \<Union> (Ni ` I)"
  using entail_set_all_formulas[of N "\<Union> (Ni ` I)"] entail_set_all_formulas[of N]
    Complete_Lattices.UN_ball_bex_simps(2)[of Ni I "\<lambda>C. N \<Turnstile> {C}", symmetric]
  by meson

lemma entail_all_bot: "(\<exists>B \<in> Bot. N \<Turnstile> {B}) \<Longrightarrow> \<forall>B' \<in> Bot. N \<Turnstile> {B'}"
  using bot_entails_all entails_trans by blast

lemma entails_trans_strong: "N1 \<Turnstile> N2 \<Longrightarrow> N1 \<union> N2 \<Turnstile> N3 \<Longrightarrow> N1 \<Turnstile> N3"
  by (meson entail_union entails_trans order_refl subset_entailed)

end


subsection \<open>Families of Consequence Relations\<close>

locale consequence_relation_family =
  fixes
    Bot :: "'f set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool"
  assumes
    Q_nonempty: "Q \<noteq> {}" and
    q_cons_rel: "\<forall>q \<in> Q. consequence_relation Bot (entails_q q)"
begin

lemma bot_not_empty: "Bot \<noteq> {}"
  using Q_nonempty consequence_relation.bot_not_empty consequence_relation_family.q_cons_rel
    consequence_relation_family_axioms by blast

definition entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>Q" 50) where
  "N1 \<Turnstile>Q N2 \<longleftrightarrow> (\<forall>q \<in> Q. entails_q q N1 N2)"

(* lem:intersection-of-conseq-rel *)
lemma intersect_cons_rel_family: "consequence_relation Bot entails"
  unfolding consequence_relation_def entails_def
  by (intro conjI bot_not_empty) (metis consequence_relation_def q_cons_rel)+

end


subsection \<open>Inference Systems\<close>

datatype 'f inference =
  Infer (prems_of: "'f list") (concl_of: "'f")

locale inference_system =
  fixes
    Inf :: \<open>'f inference set\<close>
begin

definition Inf_from :: "'f set \<Rightarrow> 'f inference set" where
  "Inf_from N = {\<iota> \<in> Inf. set (prems_of \<iota>) \<subseteq> N}"

definition Inf_between :: "'f set \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Inf_between N M = Inf_from (N \<union> M) - Inf_from (N - M)"

lemma Inf_if_Inf_from: "\<iota> \<in> Inf_from N \<Longrightarrow> \<iota> \<in> Inf"
  unfolding Inf_from_def by simp

lemma Inf_if_Inf_between: "\<iota> \<in> Inf_between N M \<Longrightarrow> \<iota> \<in> Inf"
  unfolding Inf_between_def Inf_from_def by simp

lemma Inf_between_alt:
  "Inf_between N M = {\<iota> \<in> Inf. \<iota> \<in> Inf_from (N \<union> M) \<and> set (prems_of \<iota>) \<inter> M \<noteq> {}}"
  unfolding Inf_from_def Inf_between_def by auto

lemma Inf_from_mono: "N \<subseteq> N' \<Longrightarrow> Inf_from N \<subseteq> Inf_from N'"
  unfolding Inf_from_def by auto

lemma Inf_between_mono: "N \<subseteq> N' \<Longrightarrow> M \<subseteq> M' \<Longrightarrow> Inf_between N M \<subseteq> Inf_between N' M'"
  unfolding Inf_between_alt using Inf_from_mono[of "N \<union> M" "N' \<union> M'"] by auto

end


subsection \<open>Families of Inference Systems\<close>

locale inference_system_family =
  fixes
    Q :: "'q set" and
    Inf_q :: "'q \<Rightarrow> 'f inference set"
  assumes
    Q_nonempty: "Q \<noteq> {}"
begin

definition Inf_from_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Inf_from_q q = inference_system.Inf_from (Inf_q q)"

definition Inf_between_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Inf_between_q q = inference_system.Inf_between (Inf_q q)"

lemma Inf_between_q_alt:
  "Inf_between_q q N M = {\<iota> \<in> Inf_q q. \<iota> \<in> Inf_from_q q (N \<union> M) \<and> set (prems_of \<iota>) \<inter> M \<noteq> {}}"
  unfolding Inf_from_q_def Inf_between_q_def inference_system.Inf_between_alt by auto

end


subsection \<open>Calculi Based on a Single Redundancy Criterion\<close>

locale calculus = inference_system Inf + consequence_relation Bot entails
  for
    Bot :: "'f set" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50)
  + fixes
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
  assumes
    Red_I_to_Inf: "Red_I N \<subseteq> Inf" and
    Red_F_Bot: "B \<in> Bot \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> N - Red_F N \<Turnstile> {B}" and
    Red_F_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_F N \<subseteq> Red_F N'" and
    Red_I_of_subset: "N \<subseteq> N' \<Longrightarrow> Red_I N \<subseteq> Red_I N'" and
    Red_F_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_F N \<subseteq> Red_F (N - N')" and
    Red_I_of_Red_F_subset: "N' \<subseteq> Red_F N \<Longrightarrow> Red_I N \<subseteq> Red_I (N - N')" and
    Red_I_of_Inf_to_N: "\<iota> \<in> Inf \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I N"
begin

lemma Red_I_of_Inf_to_N_subset: "{\<iota> \<in> Inf. concl_of \<iota> \<in> N} \<subseteq> Red_I N"
  using Red_I_of_Inf_to_N by blast

(* lem:red-concl-implies-red-inf *)
lemma red_concl_to_red_inf:
  assumes
    i_in: "\<iota> \<in> Inf" and
    concl: "concl_of \<iota> \<in> Red_F N"
  shows "\<iota> \<in> Red_I N"
proof -
  have "\<iota> \<in> Red_I (Red_F N)" by (simp add: Red_I_of_Inf_to_N i_in concl)
  then have i_in_Red: "\<iota> \<in> Red_I (N \<union> Red_F N)" by (simp add: Red_I_of_Inf_to_N concl i_in)
  have red_n_subs: "Red_F N \<subseteq> Red_F (N \<union> Red_F N)" by (simp add: Red_F_of_subset)
  then have "\<iota> \<in> Red_I ((N \<union> Red_F N) - (Red_F N - N))" using Red_I_of_Red_F_subset i_in_Red
    by (meson Diff_subset subsetCE subset_trans)
  then show ?thesis by (metis Diff_cancel Diff_subset Un_Diff Un_Diff_cancel contra_subsetD
    calculus.Red_I_of_subset calculus_axioms sup_bot.right_neutral)
qed

definition saturated :: "'f set \<Rightarrow> bool" where
  "saturated N \<longleftrightarrow> Inf_from N \<subseteq> Red_I N"

definition reduc_saturated :: "'f set \<Rightarrow> bool" where
  "reduc_saturated N \<longleftrightarrow> Inf_from (N - Red_F N) \<subseteq> Red_I N"

lemma Red_I_without_red_F:
  "Red_I (N - Red_F N) = Red_I N"
  using Red_I_of_subset [of "N - Red_F N" N]
    and Red_I_of_Red_F_subset [of "Red_F N" N] by blast

lemma saturated_without_red_F:
  assumes saturated: "saturated N"
  shows "saturated (N - Red_F N)"
proof -
  have "Inf_from (N - Red_F N) \<subseteq> Inf_from N" unfolding Inf_from_def by auto
  also have "Inf_from N \<subseteq> Red_I N" using saturated unfolding saturated_def by auto
  also have "Red_I N \<subseteq> Red_I (N - Red_F N)" using Red_I_of_Red_F_subset by auto
  finally have "Inf_from (N - Red_F N) \<subseteq> Red_I (N - Red_F N)" by auto
  then show ?thesis unfolding saturated_def by auto
qed

definition fair :: "'f set llist \<Rightarrow> bool" where
  "fair Ns \<longleftrightarrow> Inf_from (Liminf_llist Ns) \<subseteq> Sup_llist (lmap Red_I Ns)"

inductive "derive" :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<rhd>" 50) where
  derive: "M - N \<subseteq> Red_F N \<Longrightarrow> M \<rhd> N"

lemma gt_Max_notin: \<open>finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> x > Max A \<Longrightarrow> x \<notin> A\<close> by auto

lemma equiv_Sup_Liminf:
  assumes
    in_Sup: "C \<in> Sup_llist Ns" and
    not_in_Liminf: "C \<notin> Liminf_llist Ns"
  shows
    "\<exists>i \<in> {i. enat (Suc i) < llength Ns}. C \<in> lnth Ns i - lnth Ns (Suc i)"
proof -
  obtain i where C_D_i: "C \<in> Sup_upto_llist Ns (enat i)" and "enat i < llength Ns"
    using elem_Sup_llist_imp_Sup_upto_llist in_Sup by fast
  then obtain j where j: "j \<ge> i \<and> enat j < llength Ns \<and> C \<notin> lnth Ns j"
    using not_in_Liminf unfolding Sup_upto_llist_def chain_def Liminf_llist_def by auto
  obtain k where k: "C \<in> lnth Ns k" "enat k < llength Ns" "k \<le> i" using C_D_i
    unfolding Sup_upto_llist_def by auto
  let ?S = "{i. i < j \<and> i \<ge> k \<and> C \<in> lnth Ns i}"
  define l where "l = Max ?S"
  have \<open>k \<in> {i. i < j \<and> k \<le> i \<and> C \<in> lnth Ns i}\<close> using k j by (auto simp: order.order_iff_strict)
  then have nempty: "{i. i < j \<and> k \<le> i \<and> C \<in> lnth Ns i} \<noteq> {}" by auto
  then have l_prop: "l < j \<and> l \<ge> k \<and> C \<in> lnth Ns l" using Max_in[of ?S, OF _ nempty]
    unfolding l_def by auto
  then have "C \<in> lnth Ns l - lnth Ns (Suc l)" using j gt_Max_notin[OF _ nempty, of "Suc l"]
    unfolding l_def[symmetric] by (auto intro: Suc_lessI)
  then show ?thesis
  proof (rule bexI[of _ l])
    show "l \<in> {i. enat (Suc i) < llength Ns}"
      using l_prop j
      by (clarify, metis Suc_leI dual_order.order_iff_strict enat_ord_simps(2) less_trans)
  qed
qed

(* lem:nonpersistent-is-redundant *)
lemma Red_in_Sup:
  assumes deriv: "chain (\<rhd>) Ns"
  shows "Sup_llist Ns - Liminf_llist Ns \<subseteq> Red_F (Sup_llist Ns)"
proof
  fix C
  assume C_in_subset: "C \<in> Sup_llist Ns - Liminf_llist Ns"
  {
    fix C i
    assume
      in_ith_elem: "C \<in> lnth Ns i - lnth Ns (Suc i)" and
      i: "enat (Suc i) < llength Ns"
    have "lnth Ns i \<rhd> lnth Ns (Suc i)" using i deriv in_ith_elem chain_lnth_rel by auto
    then have "C \<in> Red_F (lnth Ns (Suc i))" using in_ith_elem derive.cases by blast
    then have "C \<in> Red_F (Sup_llist Ns)" using Red_F_of_subset
      by (meson contra_subsetD i lnth_subset_Sup_llist)
  }
  then show "C \<in> Red_F (Sup_llist Ns)" using equiv_Sup_Liminf[of C] C_in_subset by fast
qed

(* lem:redundant-remains-redundant-during-run 1/2 *)
lemma Red_I_subset_Liminf:
  assumes deriv: \<open>chain (\<rhd>) Ns\<close> and
    i: \<open>enat i < llength Ns\<close>
  shows \<open>Red_I (lnth Ns i) \<subseteq> Red_I (Liminf_llist Ns)\<close>
proof -
  have Sup_in_diff: \<open>Red_I (Sup_llist Ns) \<subseteq> Red_I (Sup_llist Ns - (Sup_llist Ns - Liminf_llist Ns))\<close>
    using Red_I_of_Red_F_subset[OF Red_in_Sup] deriv by auto
  also have \<open>Sup_llist Ns - (Sup_llist Ns - Liminf_llist Ns) = Liminf_llist Ns\<close>
    by (simp add: Liminf_llist_subset_Sup_llist double_diff)
  then have Red_I_Sup_in_Liminf: \<open>Red_I (Sup_llist Ns) \<subseteq> Red_I (Liminf_llist Ns)\<close>
    using Sup_in_diff by auto
  have \<open>lnth Ns i \<subseteq> Sup_llist Ns\<close> unfolding Sup_llist_def using i by blast
  then have "Red_I (lnth Ns i) \<subseteq> Red_I (Sup_llist Ns)" using Red_I_of_subset
    unfolding Sup_llist_def by auto
  then show ?thesis using Red_I_Sup_in_Liminf by auto
qed

(* lem:redundant-remains-redundant-during-run 2/2 *)
lemma Red_F_subset_Liminf:
  assumes deriv: \<open>chain (\<rhd>) Ns\<close> and
    i: \<open>enat i < llength Ns\<close>
  shows \<open>Red_F (lnth Ns i) \<subseteq> Red_F (Liminf_llist Ns)\<close>
proof -
  have Sup_in_diff: \<open>Red_F (Sup_llist Ns) \<subseteq> Red_F (Sup_llist Ns - (Sup_llist Ns - Liminf_llist Ns))\<close>
    using Red_F_of_Red_F_subset[OF Red_in_Sup] deriv by auto
  also have \<open>Sup_llist Ns - (Sup_llist Ns - Liminf_llist Ns) = Liminf_llist Ns\<close>
    by (simp add: Liminf_llist_subset_Sup_llist double_diff)
  then have Red_F_Sup_in_Liminf: \<open>Red_F (Sup_llist Ns) \<subseteq> Red_F (Liminf_llist Ns)\<close>
    using Sup_in_diff by auto
  have \<open>lnth Ns i \<subseteq> Sup_llist Ns\<close> unfolding Sup_llist_def using i by blast
  then have "Red_F (lnth Ns i) \<subseteq> Red_F (Sup_llist Ns)" using Red_F_of_subset
    unfolding Sup_llist_def by auto
  then show ?thesis using Red_F_Sup_in_Liminf by auto
qed

(* lem:N-i-is-persistent-or-redundant *)
lemma i_in_Liminf_or_Red_F:
  assumes
    deriv: \<open>chain (\<rhd>) Ns\<close> and
    i: \<open>enat i < llength Ns\<close>
  shows \<open>lnth Ns i \<subseteq> Red_F (Liminf_llist Ns) \<union> Liminf_llist Ns\<close>
proof (rule,rule)
  fix C
  assume C: \<open>C \<in> lnth Ns i\<close>
  and C_not_Liminf: \<open>C \<notin> Liminf_llist Ns\<close>
  have \<open>C \<in> Sup_llist Ns\<close> unfolding Sup_llist_def using C i by auto
  then obtain j where j: \<open>C \<in> lnth Ns j - lnth Ns (Suc j)\<close> \<open>enat (Suc j) < llength Ns\<close>
    using equiv_Sup_Liminf[of C Ns] C_not_Liminf by auto
  then have \<open>C \<in> Red_F (lnth Ns (Suc j))\<close>
    using deriv by (meson chain_lnth_rel contra_subsetD derive.cases)
  then show \<open>C \<in> Red_F (Liminf_llist Ns)\<close> using Red_F_subset_Liminf[of Ns "Suc j"] deriv j(2) by blast
qed

(* lem:fairness-implies-saturation *)
lemma fair_implies_Liminf_saturated:
  assumes
    deriv: \<open>chain (\<rhd>) Ns\<close> and
    fair: \<open>fair Ns\<close>
  shows \<open>saturated (Liminf_llist Ns)\<close>
  unfolding saturated_def
proof
  fix \<iota>
  assume \<iota>: \<open>\<iota> \<in> Inf_from (Liminf_llist Ns)\<close>
  have \<open>\<iota> \<in> Sup_llist (lmap Red_I Ns)\<close> using fair \<iota> unfolding fair_def by auto
  then obtain i where i: \<open>enat i < llength Ns\<close> \<open>\<iota> \<in> Red_I (lnth Ns i)\<close>
    unfolding Sup_llist_def by auto
  then show \<open>\<iota> \<in> Red_I (Liminf_llist Ns)\<close>
    using deriv i_in_Liminf_or_Red_F[of Ns i] Red_I_subset_Liminf by blast
qed

end

locale statically_complete_calculus = calculus +
  assumes statically_complete: "B \<in> Bot \<Longrightarrow> saturated N \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> \<exists>B'\<in>Bot. B' \<in> N"
begin

lemma dynamically_complete_Liminf:
  fixes B Ns
  assumes
    bot_elem: \<open>B \<in> Bot\<close> and
    deriv: \<open>chain (\<rhd>) Ns\<close> and
    fair: \<open>fair Ns\<close> and
    unsat: \<open>lhd Ns \<Turnstile> {B}\<close>
  shows \<open>\<exists>B'\<in>Bot. B' \<in> Liminf_llist Ns\<close>
proof -
  note lhd_is = lhd_conv_lnth[OF chain_not_lnull[OF deriv]]
  have non_empty: \<open>\<not> lnull Ns\<close> using chain_not_lnull[OF deriv] .
  have subs: \<open>lhd Ns \<subseteq> Sup_llist Ns\<close>
    using lhd_subset_Sup_llist[of Ns] non_empty by (simp add: lhd_conv_lnth)
  have \<open>Sup_llist Ns \<Turnstile> {B}\<close>
    using unsat subset_entailed[OF subs] entails_trans[of "Sup_llist Ns" "lhd Ns"] by auto
  then have Sup_no_Red: \<open>Sup_llist Ns - Red_F (Sup_llist Ns) \<Turnstile> {B}\<close>
    using bot_elem Red_F_Bot by auto
  have Sup_no_Red_in_Liminf: \<open>Sup_llist Ns - Red_F (Sup_llist Ns) \<subseteq> Liminf_llist Ns\<close>
    using deriv Red_in_Sup by auto
  have Liminf_entails_Bot: \<open>Liminf_llist Ns \<Turnstile> {B}\<close>
    using Sup_no_Red subset_entailed[OF Sup_no_Red_in_Liminf] entails_trans by blast
  have \<open>saturated (Liminf_llist Ns)\<close>
    using deriv fair fair_implies_Liminf_saturated unfolding saturated_def by auto
  then show ?thesis
    using bot_elem statically_complete Liminf_entails_Bot by auto
qed

end

locale dynamically_complete_calculus = calculus +
  assumes
    dynamically_complete: "B \<in> Bot \<Longrightarrow> chain (\<rhd>) Ns \<Longrightarrow> fair Ns \<Longrightarrow> lhd Ns \<Turnstile> {B} \<Longrightarrow>
      \<exists>i \<in> {i. enat i < llength Ns}. \<exists>B'\<in>Bot. B' \<in> lnth Ns i"
begin

(* lem:dynamic-ref-compl-implies-static *)
sublocale statically_complete_calculus
proof
  fix B N
  assume
    bot_elem: \<open>B \<in> Bot\<close> and
    saturated_N: "saturated N" and
    refut_N: "N \<Turnstile> {B}"
  define Ns where "Ns = LCons N LNil"
  have[simp]: \<open>\<not> lnull Ns\<close> by (auto simp: Ns_def)
  have deriv_Ns: \<open>chain (\<rhd>) Ns\<close> by (simp add: chain.chain_singleton Ns_def)
  have liminf_is_N: "Liminf_llist Ns = N" by (simp add: Ns_def Liminf_llist_LCons)
  have head_Ns: "N = lhd Ns" by (simp add: Ns_def)
  have "Sup_llist (lmap Red_I Ns) = Red_I N" by (simp add: Ns_def)
  then have fair_Ns: "fair Ns" using saturated_N by (simp add: fair_def saturated_def liminf_is_N)
  obtain i B' where B'_is_bot: \<open>B' \<in> Bot\<close> and B'_in: "B' \<in> lnth Ns i" and \<open>i < llength Ns\<close>
    using dynamically_complete[of B Ns] bot_elem fair_Ns head_Ns saturated_N deriv_Ns refut_N
    by auto
  then have "i = 0"
    by (auto simp: Ns_def enat_0_iff)
  show \<open>\<exists>B'\<in>Bot. B' \<in> N\<close>
    using B'_is_bot B'_in unfolding \<open>i = 0\<close> head_Ns[symmetric] Ns_def by auto
qed

end

(* lem:static-ref-compl-implies-dynamic *)
sublocale statically_complete_calculus \<subseteq> dynamically_complete_calculus
proof
  fix B Ns
  assume
    \<open>B \<in> Bot\<close> and
    \<open>chain (\<rhd>) Ns\<close> and
    \<open>fair Ns\<close> and
    \<open>lhd Ns \<Turnstile> {B}\<close>
  then have \<open>\<exists>B'\<in>Bot. B' \<in> Liminf_llist Ns\<close>
    by (rule dynamically_complete_Liminf)
  then show \<open>\<exists>i\<in>{i. enat i < llength Ns}. \<exists>B'\<in>Bot. B' \<in> lnth Ns i\<close>
    unfolding Liminf_llist_def by auto
qed

end
