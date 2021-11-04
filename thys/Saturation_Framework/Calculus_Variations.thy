(*  Title:       Variations on a Theme
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020 *)

section \<open>Variations on a Theme\<close>

text \<open>In this section, section 2.4 of the report is covered, demonstrating
  that various notions of redundancy are equivalent.\<close>

theory Calculus_Variations
  imports Calculus
begin

locale reduced_calculus = calculus Bot Inf entails Red_I Red_F
  for
    Bot :: "'f set" and
    Inf :: \<open>'f inference set\<close> and
    entails :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>" 50) and
    Red_I :: "'f set \<Rightarrow> 'f inference set" and
    Red_F :: "'f set \<Rightarrow> 'f set"
 + assumes
   inf_in_red_inf: "Inf_between UNIV (Red_F N) \<subseteq> Red_I N"
begin

(* lem:reduced-rc-implies-sat-equiv-reduced-sat *)
lemma sat_eq_reduc_sat: "saturated N \<longleftrightarrow> reduc_saturated N"
proof
  fix N
  assume "saturated N"
  then show "reduc_saturated N"
    using Red_I_without_red_F saturated_without_red_F
    unfolding saturated_def reduc_saturated_def
    by blast
next
  fix N
  assume red_sat_n: "reduc_saturated N"
  show "saturated N" unfolding saturated_def
    using red_sat_n inf_in_red_inf unfolding reduc_saturated_def Inf_from_def Inf_between_def
    by blast
qed

end

locale reducedly_statically_complete_calculus = calculus +
  assumes reducedly_statically_complete:
    "B \<in> Bot \<Longrightarrow> reduc_saturated N \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> \<exists>B'\<in>Bot. B' \<in> N"

locale reducedly_statically_complete_reduced_calculus = reduced_calculus +
  assumes reducedly_statically_complete:
    "B \<in> Bot \<Longrightarrow> reduc_saturated N \<Longrightarrow> N \<Turnstile> {B} \<Longrightarrow> \<exists>B'\<in>Bot. B' \<in> N"
begin

sublocale reducedly_statically_complete_calculus
  by (simp add: calculus_axioms reducedly_statically_complete
    reducedly_statically_complete_calculus_axioms.intro
    reducedly_statically_complete_calculus_def)

(* cor:reduced-rc-implies-st-ref-comp-equiv-reduced-st-ref-comp 1/2 *)
sublocale statically_complete_calculus
proof
  fix B N
  assume
    bot_elem: \<open>B \<in> Bot\<close> and
    saturated_N: "saturated N" and
    refut_N: "N \<Turnstile> {B}"
  have reduc_saturated_N: "reduc_saturated N" using saturated_N sat_eq_reduc_sat by blast
  show "\<exists>B'\<in>Bot. B' \<in> N" using reducedly_statically_complete[OF bot_elem reduc_saturated_N refut_N] .
qed

end

context reduced_calculus
begin

(* cor:reduced-rc-implies-st-ref-comp-equiv-reduced-st-ref-comp 2/2 *)
lemma stat_ref_comp_imp_red_stat_ref_comp:
  "statically_complete_calculus Bot Inf entails Red_I Red_F \<Longrightarrow>
   reducedly_statically_complete_calculus Bot Inf entails Red_I Red_F"
proof
  fix B N
  assume
    stat_ref_comp: "statically_complete_calculus Bot Inf (\<Turnstile>) Red_I Red_F" and
    bot_elem: \<open>B \<in> Bot\<close> and
    saturated_N: "reduc_saturated N" and
    refut_N: "N \<Turnstile> {B}"
  have reduc_saturated_N: "saturated N" using saturated_N sat_eq_reduc_sat by blast
  show "\<exists>B'\<in>Bot. B' \<in> N"
    using statically_complete_calculus.statically_complete[OF stat_ref_comp
      bot_elem reduc_saturated_N refut_N] .
qed

end

context calculus
begin

definition Red_Red_I :: "'f set \<Rightarrow> 'f inference set" where
  "Red_Red_I N = Red_I N \<union> Inf_between UNIV (Red_F N)"

lemma reduced_calc_is_calc: "calculus Bot Inf entails Red_Red_I Red_F"
proof
  fix N
  show "Red_Red_I N \<subseteq> Inf"
    unfolding Red_Red_I_def Inf_between_def Inf_from_def using Red_I_to_Inf by auto
next
  fix B N
  assume
    b_in: "B \<in> Bot" and
    n_entails: "N \<Turnstile> {B}"
  show "N - Red_F N \<Turnstile> {B}"
    by (simp add: Red_F_Bot b_in n_entails)
next
  fix N N' :: "'f set"
  assume "N \<subseteq> N'"
  then show "Red_F N \<subseteq> Red_F N'" by (simp add: Red_F_of_subset)
next
  fix N N' :: "'f set"
  assume n_in: "N \<subseteq> N'"
  then have "Inf_from (UNIV - (Red_F N')) \<subseteq> Inf_from (UNIV - (Red_F N))"
    using Red_F_of_subset[OF n_in] unfolding Inf_from_def by auto
  then have "Inf_between UNIV (Red_F N) \<subseteq> Inf_between UNIV (Red_F N')"
    unfolding Inf_between_def by auto
  then show "Red_Red_I N \<subseteq> Red_Red_I N'"
    unfolding Red_Red_I_def using Red_I_of_subset[OF n_in] by blast
next
  fix N N' :: "'f set"
  assume "N' \<subseteq> Red_F N"
  then show "Red_F N \<subseteq> Red_F (N - N')" by (simp add: Red_F_of_Red_F_subset)
next
  fix N N' :: "'f set"
  assume np_subs: "N' \<subseteq> Red_F N"
  have "Red_F N \<subseteq> Red_F (N - N')" by (simp add: Red_F_of_Red_F_subset np_subs)
  then have "Inf_from (UNIV - (Red_F (N - N'))) \<subseteq> Inf_from (UNIV - (Red_F N))"
    by (metis Diff_subset Red_F_of_subset eq_iff)
  then have "Inf_between UNIV (Red_F N) \<subseteq> Inf_between UNIV (Red_F (N - N'))"
    unfolding Inf_between_def by auto
  then show "Red_Red_I N \<subseteq> Red_Red_I (N - N')"
    unfolding Red_Red_I_def using Red_I_of_Red_F_subset[OF np_subs] by blast
next
  fix \<iota> N
  assume "\<iota> \<in> Inf"
    "concl_of \<iota> \<in> N"
  then show "\<iota> \<in> Red_Red_I N"
    by (simp add: Red_I_of_Inf_to_N Red_Red_I_def)
qed

lemma inf_subs_reduced_red_inf: "Inf_between UNIV (Red_F N) \<subseteq> Red_Red_I N"
  unfolding Red_Red_I_def by simp

(* lem:red'-is-reduced-redcrit *)
text \<open>The following is a lemma and not a sublocale as was previously used in similar cases.
  Here, a sublocale cannot be used because it would create an infinitely descending
  chain of sublocales. \<close>
lemma reduc_calc: "reduced_calculus Bot Inf entails Red_Red_I Red_F"
  using inf_subs_reduced_red_inf reduced_calc_is_calc
  by (simp add: reduced_calculus.intro reduced_calculus_axioms_def)

interpretation reduc_calc: reduced_calculus Bot Inf entails Red_Red_I Red_F
  by (fact reduc_calc)

(* lem:saturation-red-vs-red'-1 *)
lemma sat_imp_red_calc_sat: "saturated N \<Longrightarrow> reduc_calc.saturated N"
  unfolding saturated_def reduc_calc.saturated_def Red_Red_I_def by blast

(* lem:saturation-red-vs-red'-2 1/2 (i) \<longleftrightarrow> (ii) *)
lemma red_sat_eq_red_calc_sat: "reduc_saturated N \<longleftrightarrow> reduc_calc.saturated N"
proof
  assume red_sat_n: "reduc_saturated N"
  show "reduc_calc.saturated N"
    unfolding reduc_calc.saturated_def
  proof
    fix \<iota>
    assume i_in: "\<iota> \<in> Inf_from N"
    show "\<iota> \<in> Red_Red_I N"
      using i_in red_sat_n
      unfolding reduc_saturated_def Inf_between_def Inf_from_def Red_Red_I_def by blast
  qed
next
  assume red_sat_n: "reduc_calc.saturated N"
  show "reduc_saturated N"
    unfolding reduc_saturated_def
  proof
    fix \<iota>
    assume i_in: "\<iota> \<in> Inf_from (N - Red_F N)"
    show "\<iota> \<in> Red_I N"
      using i_in red_sat_n
      unfolding Inf_from_def reduc_calc.saturated_def Red_Red_I_def Inf_between_def by blast
  qed
qed

(* lem:saturation-red-vs-red'-2 2/2 (i) \<longleftrightarrow> (iii) *)
lemma red_sat_eq_sat: "reduc_saturated N \<longleftrightarrow> saturated (N - Red_F N)"
  unfolding reduc_saturated_def saturated_def by (simp add: Red_I_without_red_F)

(* thm:reduced-stat-ref-compl 1/3 (i) \<longleftrightarrow> (iii) *)
theorem stat_is_stat_red: "statically_complete_calculus Bot Inf entails Red_I Red_F \<longleftrightarrow>
  statically_complete_calculus Bot Inf entails Red_Red_I Red_F"
proof
  assume
    stat_ref1: "statically_complete_calculus Bot Inf entails Red_I Red_F"
  show "statically_complete_calculus Bot Inf entails Red_Red_I Red_F"
    using reduc_calc.calculus_axioms
    unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
  proof
    show "\<forall>B N. B \<in> Bot \<longrightarrow> reduc_calc.saturated N \<longrightarrow> N \<Turnstile> {B} \<longrightarrow> (\<exists>B'\<in>Bot. B' \<in> N)"
    proof (clarify)
      fix B N
      assume
        b_in: "B \<in> Bot" and
        n_sat: "reduc_calc.saturated N" and
        n_imp_b: "N \<Turnstile> {B}"
      have "saturated (N - Red_F N)" using red_sat_eq_red_calc_sat[of N] red_sat_eq_sat[of N] n_sat by blast
      moreover have "(N - Red_F N) \<Turnstile> {B}" using n_imp_b b_in by (simp add: reduc_calc.Red_F_Bot)
      ultimately show "\<exists>B'\<in>Bot. B'\<in> N"
        using stat_ref1 by (meson DiffD1 b_in statically_complete_calculus.statically_complete)
    qed
  qed
next
  assume
    stat_ref3: "statically_complete_calculus Bot Inf entails Red_Red_I Red_F"
  show "statically_complete_calculus Bot Inf entails Red_I Red_F"
    unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
    using calculus_axioms
  proof
    show "\<forall>B N. B \<in> Bot \<longrightarrow> saturated N \<longrightarrow> N \<Turnstile> {B} \<longrightarrow> (\<exists>B'\<in>Bot. B' \<in> N)"
    proof clarify
      fix B N
      assume
        b_in: "B \<in> Bot" and
        n_sat: "saturated N" and
        n_imp_b: "N \<Turnstile> {B}"
      then show "\<exists>B'\<in> Bot. B' \<in> N"
        using stat_ref3 sat_imp_red_calc_sat[OF n_sat]
        by (meson statically_complete_calculus.statically_complete)
    qed
  qed
qed

(* thm:reduced-stat-ref-compl 2/3 (iv) \<longleftrightarrow> (iii) *)
theorem red_stat_red_is_stat_red:
  "reducedly_statically_complete_calculus Bot Inf entails Red_Red_I Red_F \<longleftrightarrow>
   statically_complete_calculus Bot Inf entails Red_Red_I Red_F"
  using reduc_calc.stat_ref_comp_imp_red_stat_ref_comp
  by (metis reduc_calc.sat_eq_reduc_sat reducedly_statically_complete_calculus.axioms(2)
    reducedly_statically_complete_calculus_axioms_def reduced_calc_is_calc
    statically_complete_calculus.intro statically_complete_calculus_axioms.intro)

(* thm:reduced-stat-ref-compl 3/3 (ii) \<longleftrightarrow> (iii) *)
theorem red_stat_is_stat_red:
  "reducedly_statically_complete_calculus Bot Inf entails Red_I Red_F \<longleftrightarrow>
   statically_complete_calculus Bot Inf entails Red_Red_I Red_F"
  using reduc_calc.calculus_axioms calculus_axioms red_sat_eq_red_calc_sat
  unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
    reducedly_statically_complete_calculus_def reducedly_statically_complete_calculus_axioms_def
  by blast

lemma sup_red_f_in_red_liminf:
  "chain derive Ns \<Longrightarrow> Sup_llist (lmap Red_F Ns) \<subseteq> Red_F (Liminf_llist Ns)"
proof
  fix N
  assume
    deriv: "chain derive Ns" and
    n_in_sup: "N \<in> Sup_llist (lmap Red_F Ns)"
  obtain i0 where i_smaller: "enat i0 < llength Ns" and n_in: "N \<in> Red_F (lnth Ns i0)"
    using n_in_sup by (metis Sup_llist_imp_exists_index llength_lmap lnth_lmap)
  have "Red_F (lnth Ns i0) \<subseteq> Red_F (Liminf_llist Ns)"
    using i_smaller by (simp add: deriv Red_F_subset_Liminf)
  then show "N \<in> Red_F (Liminf_llist Ns)"
    using n_in by fast
qed

lemma sup_red_inf_in_red_liminf:
  "chain derive Ns \<Longrightarrow> Sup_llist (lmap Red_I Ns) \<subseteq> Red_I (Liminf_llist Ns)"
proof
  fix \<iota>
  assume
    deriv: "chain derive Ns" and
    i_in_sup: "\<iota> \<in> Sup_llist (lmap Red_I Ns)"
  obtain i0 where i_smaller: "enat i0 < llength Ns" and n_in: "\<iota> \<in> Red_I (lnth Ns i0)"
    using i_in_sup unfolding Sup_llist_def by auto
  have "Red_I (lnth Ns i0) \<subseteq> Red_I (Liminf_llist Ns)"
    using i_smaller by (simp add: deriv Red_I_subset_Liminf)
  then show "\<iota> \<in> Red_I (Liminf_llist Ns)"
    using n_in by fast
qed

definition reduc_fair :: "'f set llist \<Rightarrow> bool" where
  "reduc_fair Ns \<longleftrightarrow>
   Inf_from (Liminf_llist Ns - Sup_llist (lmap Red_F Ns)) \<subseteq> Sup_llist (lmap Red_I Ns)"

(* lem:red-fairness-implies-red-saturation *)
lemma reduc_fair_imp_Liminf_reduc_sat:
  "chain derive Ns \<Longrightarrow> reduc_fair Ns \<Longrightarrow> reduc_saturated (Liminf_llist Ns)"
  unfolding reduc_saturated_def
proof -
  fix Ns
  assume
    deriv: "chain derive Ns" and
    red_fair: "reduc_fair Ns"
  have "Inf_from (Liminf_llist Ns - Red_F (Liminf_llist Ns))
    \<subseteq> Inf_from (Liminf_llist Ns - Sup_llist (lmap Red_F Ns))"
    using sup_red_f_in_red_liminf[OF deriv] unfolding Inf_from_def by blast
  then have "Inf_from (Liminf_llist Ns - Red_F (Liminf_llist Ns)) \<subseteq> Sup_llist (lmap Red_I Ns)"
    using red_fair unfolding reduc_fair_def by simp
  then show "Inf_from (Liminf_llist Ns - Red_F (Liminf_llist Ns)) \<subseteq> Red_I (Liminf_llist Ns)"
    using sup_red_inf_in_red_liminf[OF deriv] by fast
qed

end

locale reducedly_dynamically_complete_calculus = calculus +
  assumes
    reducedly_dynamically_complete: "B \<in> Bot \<Longrightarrow> chain derive Ns \<Longrightarrow> reduc_fair Ns \<Longrightarrow>
      lhd Ns \<Turnstile> {B} \<Longrightarrow> \<exists>i \<in> {i. enat i < llength Ns}. \<exists> B'\<in>Bot. B' \<in> lnth Ns i"
begin

sublocale reducedly_statically_complete_calculus
proof
  fix B N
  assume
    bot_elem: \<open>B \<in> Bot\<close> and
    saturated_N: "reduc_saturated N" and
    refut_N: "N \<Turnstile> {B}"
  define Ns where "Ns = LCons N LNil"
  have[simp]: \<open>\<not> lnull Ns\<close> by (auto simp: Ns_def)
  have deriv_D: \<open>chain (\<rhd>) Ns\<close> by (simp add: chain.chain_singleton Ns_def)
  have liminf_is_N: "Liminf_llist Ns = N" by (simp add: Ns_def Liminf_llist_LCons)
  have head_D: "N = lhd Ns" by (simp add: Ns_def)
  have "Sup_llist (lmap Red_F Ns) = Red_F N" by (simp add: Ns_def)
  moreover have "Sup_llist (lmap Red_I Ns) = Red_I N" by (simp add: Ns_def)
  ultimately have fair_D: "reduc_fair Ns"
    using saturated_N liminf_is_N unfolding reduc_fair_def reduc_saturated_def
    by (simp add: reduc_fair_def reduc_saturated_def liminf_is_N)
  obtain i B' where B'_is_bot: \<open>B' \<in> Bot\<close> and B'_in: "B' \<in> lnth Ns i" and \<open>i < llength Ns\<close>
    using reducedly_dynamically_complete[of B Ns] bot_elem fair_D head_D saturated_N deriv_D refut_N
    by auto
  then have "i = 0"
    by (auto simp: Ns_def enat_0_iff)
  show \<open>\<exists>B'\<in>Bot. B' \<in> N\<close>
    using B'_is_bot B'_in unfolding \<open>i = 0\<close> head_D[symmetric] Ns_def by auto
qed

end

sublocale reducedly_statically_complete_calculus \<subseteq> reducedly_dynamically_complete_calculus
proof
  fix B Ns
  assume
    bot_elem: \<open>B \<in> Bot\<close> and
    deriv: \<open>chain (\<rhd>) Ns\<close> and
    fair: \<open>reduc_fair Ns\<close> and
    unsat: \<open>lhd Ns \<Turnstile> {B}\<close>
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
    have \<open>reduc_saturated (Liminf_llist Ns)\<close>
    using deriv fair reduc_fair_imp_Liminf_reduc_sat unfolding reduc_saturated_def
      by auto
   then have \<open>\<exists>B'\<in>Bot. B' \<in> Liminf_llist Ns\<close>
     using bot_elem reducedly_statically_complete Liminf_entails_Bot
     by auto
   then show \<open>\<exists>i\<in>{i. enat i < llength Ns}. \<exists>B'\<in>Bot. B' \<in> lnth Ns i\<close>
     unfolding Liminf_llist_def by auto
qed

context calculus
begin

lemma dyn_equiv_stat: "dynamically_complete_calculus Bot Inf entails Red_I Red_F =
  statically_complete_calculus Bot Inf entails Red_I Red_F"
proof
  assume "dynamically_complete_calculus Bot Inf entails Red_I Red_F"
  then interpret dynamically_complete_calculus Bot Inf entails Red_I Red_F
    by simp
  show "statically_complete_calculus Bot Inf entails Red_I Red_F"
    by (simp add: statically_complete_calculus_axioms)
next
  assume "statically_complete_calculus Bot Inf entails Red_I Red_F"
  then interpret statically_complete_calculus Bot Inf entails Red_I Red_F
    by simp
  show "dynamically_complete_calculus Bot Inf entails Red_I Red_F"
    by (simp add: dynamically_complete_calculus_axioms)
qed

lemma red_dyn_equiv_red_stat:
  "reducedly_dynamically_complete_calculus Bot Inf entails Red_I Red_F =
   reducedly_statically_complete_calculus Bot Inf entails Red_I Red_F"
proof
  assume "reducedly_dynamically_complete_calculus Bot Inf entails Red_I Red_F"
  then interpret reducedly_dynamically_complete_calculus Bot Inf entails Red_I Red_F
    by simp
  show "reducedly_statically_complete_calculus Bot Inf entails Red_I Red_F"
    by (simp add: reducedly_statically_complete_calculus_axioms)
next
  assume "reducedly_statically_complete_calculus Bot Inf entails Red_I Red_F"
  then interpret reducedly_statically_complete_calculus Bot Inf entails Red_I Red_F
    by simp
  show "reducedly_dynamically_complete_calculus Bot Inf entails Red_I Red_F"
    by (simp add: reducedly_dynamically_complete_calculus_axioms)
qed

interpretation reduc_calc: reduced_calculus Bot Inf entails Red_Red_I Red_F
  by (fact reduc_calc)

(* thm:reduced-dyn-ref-compl 1/3 (v) \<longleftrightarrow> (vii) *)
theorem dyn_ref_eq_dyn_ref_red:
  "dynamically_complete_calculus Bot Inf entails Red_I Red_F \<longleftrightarrow>
   dynamically_complete_calculus Bot Inf entails Red_Red_I Red_F"
  using dyn_equiv_stat stat_is_stat_red reduc_calc.dyn_equiv_stat by meson

(* thm:reduced-dyn-ref-compl 2/3 (viii) \<longleftrightarrow> (vii) *)
theorem red_dyn_ref_red_eq_dyn_ref_red:
  "reducedly_dynamically_complete_calculus Bot Inf entails Red_Red_I Red_F \<longleftrightarrow>
   dynamically_complete_calculus Bot Inf entails Red_Red_I Red_F"
  using red_dyn_equiv_red_stat dyn_equiv_stat red_stat_red_is_stat_red
  by (simp add: reduc_calc.dyn_equiv_stat reduc_calc.red_dyn_equiv_red_stat)

(* thm:reduced-dyn-ref-compl 3/3 (vi) \<longleftrightarrow> (vii) *)
theorem red_dyn_ref_eq_dyn_ref_red:
  "reducedly_dynamically_complete_calculus Bot Inf entails Red_I Red_F \<longleftrightarrow>
   dynamically_complete_calculus Bot Inf entails Red_Red_I Red_F"
  using red_dyn_equiv_red_stat dyn_equiv_stat red_stat_is_stat_red
    reduc_calc.dyn_equiv_stat reduc_calc.red_dyn_equiv_red_stat
  by blast

end

end
