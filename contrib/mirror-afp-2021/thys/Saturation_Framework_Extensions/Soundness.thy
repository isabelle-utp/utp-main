(*  Title:       Soundness
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2020
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017, 2020
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
*)

section \<open>Soundness\<close>

theory Soundness
  imports Saturation_Framework.Calculus
begin

text \<open>
Although consistency-preservation usually suffices, soundness is a more precise concept and is
sometimes useful.
\<close>

locale sound_inference_system = inference_system + consequence_relation +
  assumes
    sound: \<open>\<iota> \<in> Inf \<Longrightarrow> set (prems_of \<iota>) \<Turnstile> {concl_of \<iota>}\<close>
begin

lemma Inf_consist_preserving:
  assumes n_cons: "\<not> N \<Turnstile> Bot"
  shows "\<not> N \<union> concl_of ` Inf_from N \<Turnstile> Bot"
proof -
  have "N \<Turnstile> concl_of ` Inf_from N"
    using sound unfolding Inf_from_def image_def Bex_def mem_Collect_eq
    by (smt all_formulas_entailed entails_trans mem_Collect_eq subset_entailed)
  then show ?thesis
    using n_cons entails_trans_strong by blast
qed

end

text \<open>
The limit of a derivation based on a redundancy criterion is satisfiable if and only if the initial
set is satisfiable. This material is partly based on Section 4.1 of Bachmair and Ganzinger's
\emph{Handbook} chapter, but adapted to the saturation framework of Waldmann et al.
\<close>

context calculus
begin

text \<open>
The next three lemmas correspond to Lemma 4.2:
\<close>

lemma Red_F_Sup_subset_Red_F_Liminf:
  "chain (\<rhd>) Ns \<Longrightarrow> Red_F (Sup_llist Ns) \<subseteq> Red_F (Liminf_llist Ns)"
  by (metis Liminf_llist_subset_Sup_llist Red_in_Sup Un_absorb1 calculus.Red_F_of_Red_F_subset
      calculus_axioms double_diff sup_ge2)

lemma Red_I_Sup_subset_Red_I_Liminf:
  "chain (\<rhd>) Ns \<Longrightarrow> Red_I (Sup_llist Ns) \<subseteq> Red_I (Liminf_llist Ns)"
  by (metis Liminf_llist_subset_Sup_llist Red_I_of_Red_F_subset Red_in_Sup double_diff subset_refl)

text \<open>
Proof idea due to Uwe Waldmann:
\<close>

lemma unsat_limit_iff:
  assumes
    chain_red: "chain (\<rhd>) Ns" and
    chain_ent: "chain (\<Turnstile>) Ns"
  shows "Liminf_llist Ns \<Turnstile> Bot \<longleftrightarrow> lhd Ns \<Turnstile> Bot"
proof
  assume "Liminf_llist Ns \<Turnstile> Bot"
  moreover have "Sup_llist Ns \<Turnstile> Liminf_llist Ns"
    by (simp add: Liminf_llist_subset_Sup_llist subset_entailed)
  moreover have "lhd Ns \<Turnstile> Sup_llist Ns"
  proof -
    have "lhd Ns \<Turnstile> lnth Ns i" if "i < llength Ns" for i
      using that
    proof (induct i)
      case 0
      then show ?case
        using chain_ent chain_not_lnull lhd_conv_lnth subset_entailed by fastforce
    next
      case (Suc i)
      then show ?case
        using Suc_ile_eq chain_ent chain_lnth_rel entails_trans less_le by blast
    qed
    thus ?thesis
      unfolding Sup_llist_def using entail_unions by fastforce
  qed
  ultimately show "lhd Ns \<Turnstile> Bot"
    using entails_trans by blast
next
  assume "lhd Ns \<Turnstile> Bot"
  then have "Sup_llist Ns \<Turnstile> Bot"
    by (meson chain_ent chain_not_lnull entails_trans lhd_subset_Sup_llist subset_entailed)
  then have "Sup_llist Ns - Red_F (Sup_llist Ns) \<Turnstile> Bot"
    using Red_F_Bot entail_set_all_formulas by blast
  then have "Liminf_llist Ns - Red_F (Sup_llist Ns) \<Turnstile> Bot"
    by (smt Diff_idemp Diff_mono Diff_subset Liminf_llist_subset_Sup_llist
        Red_F_Sup_subset_Red_F_Liminf Red_F_of_subset Red_in_Sup antisym_conv chain_red double_diff
        entail_set_all_formulas order_refl order_trans subset_antisym)
  then show "Liminf_llist Ns \<Turnstile> Bot"
    by (meson Diff_subset entails_trans subset_entailed)
qed

text \<open>Some easy consequences:\<close>

lemma Red_F_limit_Sup: "chain (\<rhd>) Ns \<Longrightarrow> Red_F (Liminf_llist Ns) = Red_F (Sup_llist Ns)"
  by (metis Liminf_llist_subset_Sup_llist Red_F_of_Red_F_subset Red_F_of_subset Red_in_Sup
      double_diff order_refl subset_antisym)

lemma Red_I_limit_Sup: "chain (\<rhd>) Ns \<Longrightarrow> Red_I (Liminf_llist Ns) = Red_I (Sup_llist Ns)"
  by (metis Liminf_llist_subset_Sup_llist Red_I_of_Red_F_subset Red_I_of_subset Red_in_Sup
      double_diff order_refl subset_antisym)

end

end
