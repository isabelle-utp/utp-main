(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Intermission: upper bound on the cardinality of the continuum (HOL)\<close>
theory HOL_CContinuum
  imports CZH_Sets_Introduction 
begin


text\<open>
The section presents a proof of \<open>|\<real>|\<le>|\<P>(\<nat>)|\<close> in Isabelle/HOL. The proof is 
based on an outline at the beginning of Chapter 4 in the textbook 
\<open>Set Theory\<close> by Thomas Jech \cite{jech_set_2006}.
\<close>

lemma Pow_lepoll_mono: 
  assumes "A \<lesssim> B"
  shows "Pow A \<lesssim> Pow B"
  using assms by (metis Pow_mono image_Pow_surj lepoll_iff)
  
lemma rat_lepoll_nat: "(UNIV::rat set) \<lesssim> (UNIV::nat set)" 
  unfolding lepoll_def by auto

definition rcut :: "real \<Rightarrow> real set" where "rcut r = {x\<in>\<rat>. x < r}"

lemma inj_rcut: "inj rcut"
  unfolding rcut_def
proof(intro inj_onI)
  have xy: "x < y \<Longrightarrow> {r\<in>\<rat>. r < x} = {r\<in>\<rat>. r < y} \<Longrightarrow> x = y" for x y :: real
  proof(rule ccontr)
    assume prems: "x < y" "{r\<in>\<rat>. r < x} = {r\<in>\<rat>. r < y}"
    then have "{r\<in>\<rat>. r < y} - {r\<in>\<rat>. r < x} = {}" by simp
    with prems(1) Rats_dense_in_real show False by force
  qed
  then have yx: "y < x \<Longrightarrow> {r\<in>\<rat>. r < x} = {r\<in>\<rat>. r < y} \<Longrightarrow> x = y" 
    for x y :: real
    by auto
  show "{z \<in> \<rat>. z < x} = {z \<in> \<rat>. z < y} \<Longrightarrow> x = y" for x y :: real 
  proof(rule ccontr)
    fix x y :: real assume prems: "{xa \<in> \<rat>. xa < x} = {x \<in> \<rat>. x < y}" "x \<noteq> y"
    from this(2) consider "x < y" | "y < x" by force
    with xy[OF _ prems(1)] yx[OF _ prems(1)] show False by cases auto
  qed
qed

lemma range_rcut_subset_Pow_rat: "range rcut \<subseteq> Pow \<rat>"
proof(intro subsetI)
  fix x assume "x \<in> range rcut" 
  then obtain r where "x = {x\<in>\<rat>. x < r}" unfolding rcut_def by clarsimp
  then show "x \<in> Pow \<rat>" by simp
qed

lemma inj_on_inv_of_rat_rat: "inj_on (inv of_rat) \<rat>"
  using inv_into_injective by (intro inj_onI) (fastforce simp: Rats_def)

lemma inj_on_inv_image_inv_of_rat_Pow_rat: "inj_on (image (inv of_rat)) (Pow \<rat>)"
  by (simp add: inj_on_inv_of_rat_rat inj_on_image_Pow)

lemma inj_on_image_inv_of_rat_range_rcut: 
  "inj_on (image (inv of_rat)) (range rcut)"
  using range_rcut_subset_Pow_rat inj_on_inv_image_inv_of_rat_Pow_rat
  by (auto intro: inj_on_subset)

lemma real_lepoll_ratrat: "(UNIV::real set) \<lesssim> (UNIV::rat set set)" 
  unfolding lepoll_def
proof(intro exI conjI)
  from inj_rcut inj_on_image_inv_of_rat_range_rcut show 
    "inj (image (inv of_rat) \<circ> rcut)"
    by (rule comp_inj_on)
qed auto

lemma nat_lepoll_real: "(UNIV::nat set) \<lesssim> (UNIV::real set)"
  using infinite_UNIV_char_0 infinite_countable_subset 
  unfolding lepoll_def 
  by blast

lemma real_lepoll_natnat: "(UNIV::real set) \<lesssim> Pow (UNIV::nat set)"
proof-
  have "(UNIV::rat set set) \<lesssim> (UNIV::nat set set)" 
    unfolding Pow_UNIV[symmetric] by (intro Pow_lepoll_mono rat_lepoll_nat)
  from lepoll_trans[OF real_lepoll_ratrat this] show ?thesis by simp
qed

text\<open>\newpage\<close>

end