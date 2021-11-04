(*  Title:       Labeled Lifting to Non-Ground Calculi
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2019-2020 *)

section \<open>Labeled Lifting to Non-Ground Calculi\<close>

text \<open>This section formalizes the extension of the lifting results to labeled
  calculi. This corresponds to section 3.4 of the report.\<close>

theory Labeled_Lifting_to_Non_Ground_Calculi
  imports Lifting_to_Non_Ground_Calculi
begin

lemma po_on_empty_rel[simp]: "po_on (\<lambda>_ _. False) UNIV"
  unfolding po_on_def irreflp_on_def transp_on_def by auto

subsection \<open>Labeled Lifting with a Family of Tiebreaker Orderings\<close>

locale labeled_tiebreaker_lifting = no_labels: tiebreaker_lifting Bot_F Inf_F
  Bot_G entails_G Inf_G Red_I_G Red_F_G \<G>_F \<G>_I Prec_F
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    entails_G :: "'g set \<Rightarrow> 'g set \<Rightarrow> bool"  (infix "\<Turnstile>G" 50) and
    Inf_G :: "'g inference set" and
    Red_I_G :: "'g set \<Rightarrow> 'g inference set" and
    Red_F_G :: "'g set \<Rightarrow> 'g set" and
    \<G>_F :: "'f \<Rightarrow> 'g set" and
    \<G>_I :: "'f inference \<Rightarrow> 'g inference set option" and
    Prec_F :: "'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool" (infix "\<sqsubset>" 50)
  + fixes
    Inf_FL :: \<open>('f \<times> 'l) inference set\<close>
  assumes
    Inf_F_to_Inf_FL: \<open>\<iota>\<^sub>F \<in> Inf_F \<Longrightarrow> length (Ll :: 'l list) = length (prems_of \<iota>\<^sub>F) \<Longrightarrow>
      \<exists>L0. Infer (zip (prems_of \<iota>\<^sub>F) Ll) (concl_of \<iota>\<^sub>F, L0) \<in> Inf_FL\<close> and
    Inf_FL_to_Inf_F: \<open>\<iota>\<^sub>F\<^sub>L \<in> Inf_FL \<Longrightarrow> Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L)) \<in> Inf_F\<close>
begin

definition to_F :: \<open>('f \<times> 'l) inference \<Rightarrow> 'f inference\<close> where
  \<open>to_F \<iota>\<^sub>F\<^sub>L = Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L))\<close>

abbreviation Bot_FL :: \<open>('f \<times> 'l) set\<close> where
  \<open>Bot_FL \<equiv> Bot_F \<times> UNIV\<close>

abbreviation \<G>_F_L :: \<open>('f \<times> 'l) \<Rightarrow> 'g set\<close> where
  \<open>\<G>_F_L CL \<equiv> \<G>_F (fst CL)\<close>

abbreviation \<G>_I_L :: \<open>('f \<times> 'l) inference \<Rightarrow> 'g inference set option\<close> where
  \<open>\<G>_I_L \<iota>\<^sub>F\<^sub>L \<equiv> \<G>_I (to_F \<iota>\<^sub>F\<^sub>L)\<close>

(* lem:labeled-grounding-function *)
sublocale standard_lifting Inf_FL Bot_G Inf_G "(\<Turnstile>G)" Red_I_G Red_F_G Bot_FL \<G>_F_L \<G>_I_L
proof
  show "Bot_FL \<noteq> {}"
    using no_labels.Bot_F_not_empty by simp
next
  show "B \<in> Bot_FL \<Longrightarrow> \<G>_F_L B \<noteq> {}" for B
    using no_labels.Bot_map_not_empty by auto
next
  show "B \<in> Bot_FL \<Longrightarrow> \<G>_F_L B \<subseteq> Bot_G" for B
    using no_labels.Bot_map by force
next
  fix CL
  show "\<G>_F_L CL \<inter> Bot_G \<noteq> {} \<longrightarrow> CL \<in> Bot_FL"
    using no_labels.Bot_cond by (metis SigmaE UNIV_I UNIV_Times_UNIV mem_Sigma_iff prod.sel(1))
next
  fix \<iota>
  assume
    i_in: \<open>\<iota> \<in> Inf_FL\<close> and
    ground_not_none: \<open>\<G>_I_L \<iota> \<noteq> None\<close>
  then show "the (\<G>_I_L \<iota>) \<subseteq> Red_I_G (\<G>_F_L (concl_of \<iota>))"
    unfolding to_F_def using no_labels.inf_map Inf_FL_to_Inf_F by fastforce
qed

(* sublocale tiebreaker_lifting Bot_FL Inf_FL Bot_G entails_G Inf_G Red_I_G Red_F_G \<G>_F_L \<G>_I_L
 *   "\<lambda>g Cl Cl'. False"
 *   by unfold_locales simp+ *)

notation entails_\<G> (infix "\<Turnstile>\<G>L" 50)

(* lem:labeled-consequence *)
lemma labeled_entailment_lifting: "NL1 \<Turnstile>\<G>L NL2 \<longleftrightarrow> fst ` NL1 \<Turnstile>\<G> fst ` NL2"
  by simp

lemma red_inf_impl: "\<iota> \<in> Red_I_\<G> NL \<Longrightarrow> to_F \<iota> \<in> no_labels.Red_I_\<G> (fst ` NL)"
  unfolding Red_I_\<G>_def no_labels.Red_I_\<G>_def using Inf_FL_to_Inf_F by (auto simp: to_F_def)

(* lem:labeled-saturation *)
lemma labeled_saturation_lifting: "saturated NL \<Longrightarrow> no_labels.saturated (fst ` NL)"
  unfolding saturated_def no_labels.saturated_def Inf_from_def no_labels.Inf_from_def
proof clarify
  fix \<iota>
  assume
    subs_Red_I: "{\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL} \<subseteq> Red_I_\<G> NL" and
    i_in: "\<iota> \<in> Inf_F" and
    i_prems: "set (prems_of \<iota>) \<subseteq> fst ` NL"
  define Lli where "Lli i = (SOME x. ((prems_of \<iota>)!i,x) \<in> NL)" for i
  have [simp]:"((prems_of \<iota>)!i,Lli i) \<in> NL" if "i < length (prems_of \<iota>)" for i
    using that i_prems unfolding Lli_def by (metis nth_mem someI_ex DomainE Domain_fst subset_eq)
  define Ll where "Ll = map Lli [0..<length (prems_of \<iota>)]"
  have Ll_length: "length Ll = length (prems_of \<iota>)" unfolding Ll_def by auto
  have subs_NL: "set (zip (prems_of \<iota>) Ll) \<subseteq> NL" unfolding Ll_def by (auto simp:in_set_zip)
  obtain L0 where L0: "Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0) \<in> Inf_FL"
    using Inf_F_to_Inf_FL[OF i_in Ll_length] ..
  define \<iota>_FL where "\<iota>_FL = Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0)"
  then have "set (prems_of \<iota>_FL) \<subseteq> NL" using subs_NL by simp
  then have "\<iota>_FL \<in> {\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL}" unfolding \<iota>_FL_def using L0 by blast
  then have "\<iota>_FL \<in> Red_I_\<G> NL" using subs_Red_I by fast
  moreover have "\<iota> = to_F \<iota>_FL" unfolding to_F_def \<iota>_FL_def using Ll_length by (cases \<iota>) auto
  ultimately show "\<iota> \<in> no_labels.Red_I_\<G> (fst ` NL)" by (auto intro: red_inf_impl)
qed

(* lem:labeled-static-ref-compl *)
lemma stat_ref_comp_to_labeled_sta_ref_comp:
  assumes static:
    "statically_complete_calculus Bot_F Inf_F (\<Turnstile>\<G>) no_labels.Red_I_\<G> no_labels.Red_F_\<G>"
  shows "statically_complete_calculus Bot_FL Inf_FL (\<Turnstile>\<G>L) Red_I_\<G> Red_F_\<G>"
proof
  fix Bl :: \<open>'f \<times> 'l\<close> and Nl :: \<open>('f \<times> 'l) set\<close>
  assume
    Bl_in: \<open>Bl \<in> Bot_FL\<close> and
    Nl_sat: \<open>saturated Nl\<close> and
    Nl_entails_Bl: \<open>Nl \<Turnstile>\<G>L {Bl}\<close>
  define B where "B = fst Bl"
  have B_in: "B \<in> Bot_F" using Bl_in B_def SigmaE by force
  define N where "N = fst ` Nl"
  have N_sat: "no_labels.saturated N"
    using N_def Nl_sat labeled_saturation_lifting by blast
  have N_entails_B: "N \<Turnstile>\<G> {B}"
    using Nl_entails_Bl unfolding labeled_entailment_lifting N_def B_def by force
  have "\<exists>B' \<in> Bot_F. B' \<in> N" using B_in N_sat N_entails_B
    using static[unfolded statically_complete_calculus_def
        statically_complete_calculus_axioms_def] by blast
  then obtain B' where in_Bot: "B' \<in> Bot_F" and in_N: "B' \<in> N" by force
  then have "B' \<in> fst ` Bot_FL" by fastforce
  obtain Bl' where in_Nl: "Bl' \<in> Nl" and fst_Bl': "fst Bl' = B'"
    using in_N unfolding N_def by blast
  have "Bl' \<in> Bot_FL" using fst_Bl' in_Bot vimage_fst by fastforce
  then show \<open>\<exists>Bl'\<in>Bot_FL. Bl' \<in> Nl\<close> using in_Nl by blast
qed

end


subsection \<open>Labeled Lifting with a Family of Redundancy Criteria\<close>

locale labeled_lifting_intersection = no_labels: lifting_intersection Inf_F
  Bot_G Q Inf_G_q entails_q Red_I_q Red_F_q Bot_F \<G>_F_q \<G>_I_q "\<lambda>g Cl Cl'. False"
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Q :: "'q set" and
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool"  and
    Inf_G_q :: "'q \<Rightarrow> 'g inference set" and
    Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option"
  + fixes
    Inf_FL :: \<open>('f \<times> 'l) inference set\<close>
  assumes
    Inf_F_to_Inf_FL:
      \<open>\<iota>\<^sub>F \<in> Inf_F \<Longrightarrow> length (Ll :: 'l list) = length (prems_of \<iota>\<^sub>F) \<Longrightarrow>
       \<exists>L0. Infer (zip (prems_of \<iota>\<^sub>F) Ll) (concl_of \<iota>\<^sub>F, L0) \<in> Inf_FL\<close> and
    Inf_FL_to_Inf_F: \<open>\<iota>\<^sub>F\<^sub>L \<in> Inf_FL \<Longrightarrow> Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L)) \<in> Inf_F\<close>
begin

definition to_F :: \<open>('f \<times> 'l) inference \<Rightarrow> 'f inference\<close> where
  \<open>to_F \<iota>\<^sub>F\<^sub>L = Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L))\<close>

abbreviation Bot_FL :: \<open>('f \<times> 'l) set\<close> where
  \<open>Bot_FL \<equiv> Bot_F \<times> UNIV\<close>

abbreviation \<G>_F_L_q :: \<open>'q \<Rightarrow> ('f \<times> 'l) \<Rightarrow> 'g set\<close> where
  \<open>\<G>_F_L_q q CL \<equiv> \<G>_F_q q (fst CL)\<close>

abbreviation \<G>_I_L_q :: \<open>'q \<Rightarrow> ('f \<times> 'l) inference \<Rightarrow> 'g inference set option\<close> where
  \<open>\<G>_I_L_q q \<iota>\<^sub>F\<^sub>L \<equiv> \<G>_I_q q (to_F \<iota>\<^sub>F\<^sub>L)\<close>

abbreviation \<G>_Fset_L_q :: "'q \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> 'g set" where
  "\<G>_Fset_L_q q N \<equiv> \<Union> (\<G>_F_L_q q ` N)"

definition Red_I_\<G>_L_q :: "'q \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) inference set" where
  "Red_I_\<G>_L_q q N =
   {\<iota> \<in> Inf_FL. (\<G>_I_L_q q \<iota> \<noteq> None \<and> the (\<G>_I_L_q q \<iota>) \<subseteq> Red_I_q q (\<G>_Fset_L_q q N))
    \<or> (\<G>_I_L_q q \<iota> = None \<and> \<G>_F_L_q q (concl_of \<iota>) \<subseteq> \<G>_Fset_L_q q N \<union> Red_F_q q (\<G>_Fset_L_q q N))}"

abbreviation Red_I_\<G>_L :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) inference set" where
  "Red_I_\<G>_L N \<equiv> (\<Inter>q \<in> Q. Red_I_\<G>_L_q q N)"

abbreviation entails_\<G>_L_q :: "'q \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" where
  "entails_\<G>_L_q q N1 N2 \<equiv> entails_q q (\<G>_Fset_L_q q N1) (\<G>_Fset_L_q q N2)"

lemma lifting_q:
  assumes "q \<in> Q"
  shows "labeled_tiebreaker_lifting Bot_F Inf_F Bot_G (entails_q q) (Inf_G_q q) (Red_I_q q)
    (Red_F_q q) (\<G>_F_q q) (\<G>_I_q q) (\<lambda>g Cl Cl'. False) Inf_FL"
  using assms no_labels.standard_lifting_family Inf_F_to_Inf_FL Inf_FL_to_Inf_F
  by (simp add: labeled_tiebreaker_lifting_axioms_def labeled_tiebreaker_lifting_def)

lemma lifted_q:
  assumes q_in: "q \<in> Q"
  shows "standard_lifting Inf_FL Bot_G (Inf_G_q q) (entails_q q) (Red_I_q q) (Red_F_q q)
    Bot_FL (\<G>_F_L_q q) (\<G>_I_L_q q)"
proof -
  interpret q_lifting: labeled_tiebreaker_lifting Bot_F Inf_F Bot_G "entails_q q" "Inf_G_q q"
    "Red_I_q q" "Red_F_q q" "\<G>_F_q q" "\<G>_I_q q" "\<lambda>g Cl Cl'. False" Inf_FL
    using lifting_q[OF q_in] .
  have "\<G>_I_L_q q = q_lifting.\<G>_I_L"
    unfolding to_F_def q_lifting.to_F_def by simp
  then show ?thesis
    using q_lifting.standard_lifting_axioms by simp
qed

lemma ord_fam_lifted_q:
  assumes q_in: "q \<in> Q"
  shows "tiebreaker_lifting Bot_FL Inf_FL Bot_G (entails_q q) (Inf_G_q q) (Red_I_q q)
    (Red_F_q q) (\<G>_F_L_q q) (\<G>_I_L_q q) (\<lambda>g Cl Cl'. False)"
proof -
  interpret standard_q_lifting: standard_lifting Inf_FL Bot_G "Inf_G_q q" "entails_q q"
    "Red_I_q q" "Red_F_q q" Bot_FL "\<G>_F_L_q q" "\<G>_I_L_q q"
    using lifted_q[OF q_in] .
  have "minimal_element (\<lambda>Cl Cl'. False) UNIV"
    by (simp add: minimal_element.intro po_on_def transp_onI wfp_on_imp_irreflp_on)
  then show ?thesis
    using standard_q_lifting.standard_lifting_axioms
    by (simp add: tiebreaker_lifting_axioms_def tiebreaker_lifting_def)
qed

definition Red_F_\<G>_empty_L_q :: "'q \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set" where
  "Red_F_\<G>_empty_L_q q N = {C. \<forall>D \<in> \<G>_F_L_q q C. D \<in> Red_F_q q (\<G>_Fset_L_q q N) \<or>
    (\<exists>E \<in> N. False \<and> D \<in> \<G>_F_L_q q E)}"

abbreviation Red_F_\<G>_empty_L :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set" where
  "Red_F_\<G>_empty_L N \<equiv> (\<Inter>q \<in> Q. Red_F_\<G>_empty_L_q q N)"

lemma all_lifted_red_crit:
  assumes q_in: "q \<in> Q"
  shows "calculus Bot_FL Inf_FL (entails_\<G>_L_q q) (Red_I_\<G>_L_q q) (Red_F_\<G>_empty_L_q q)"
proof -
  interpret ord_q_lifting: tiebreaker_lifting Bot_FL Inf_FL Bot_G "entails_q q"
    "Inf_G_q q" "Red_I_q q" "Red_F_q q" "\<G>_F_L_q q" "\<G>_I_L_q q" "\<lambda>g Cl Cl'. False"
    using ord_fam_lifted_q[OF q_in] .
  have "Red_I_\<G>_L_q q = ord_q_lifting.Red_I_\<G>"
    unfolding Red_I_\<G>_L_q_def ord_q_lifting.Red_I_\<G>_def by simp
  moreover have "Red_F_\<G>_empty_L_q q = ord_q_lifting.Red_F_\<G>"
    unfolding Red_F_\<G>_empty_L_q_def ord_q_lifting.Red_F_\<G>_def by simp
  ultimately show ?thesis
    using ord_q_lifting.calculus_axioms by argo
qed

lemma all_lifted_cons_rel:
  assumes q_in: "q \<in> Q"
  shows "consequence_relation Bot_FL (entails_\<G>_L_q q)"
  using all_lifted_red_crit calculus_def q_in by blast

sublocale consequence_relation_family Bot_FL Q entails_\<G>_L_q
  using all_lifted_cons_rel by (simp add: consequence_relation_family.intro no_labels.Q_nonempty)

sublocale intersection_calculus Bot_FL Inf_FL Q entails_\<G>_L_q Red_I_\<G>_L_q Red_F_\<G>_empty_L_q
  using intersection_calculus.intro[OF consequence_relation_family_axioms]
  by (simp add: all_lifted_red_crit intersection_calculus_axioms_def no_labels.Q_nonempty)

lemma in_Inf_FL_imp_to_F_in_Inf_F: "\<iota> \<in> Inf_FL \<Longrightarrow> to_F \<iota> \<in> Inf_F"
  by (simp add: Inf_FL_to_Inf_F to_F_def)

lemma in_Inf_from_imp_to_F_in_Inf_from: "\<iota> \<in> Inf_from N \<Longrightarrow> to_F \<iota> \<in> no_labels.Inf_from (fst ` N)"
  unfolding Inf_from_def no_labels.Inf_from_def to_F_def by (auto intro: Inf_FL_to_Inf_F)

notation no_labels.entails_\<G> (infix "\<Turnstile>\<inter>\<G>" 50)

abbreviation entails_\<G>_L :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" (infix "\<Turnstile>\<inter>\<G>L" 50) where
  "(\<Turnstile>\<inter>\<G>L) \<equiv> entails"

lemmas entails_\<G>_L_def = entails_def

(* lem:labeled-consequence-intersection *)
lemma labeled_entailment_lifting: "NL1 \<Turnstile>\<inter>\<G>L NL2 \<longleftrightarrow> fst ` NL1 \<Turnstile>\<inter>\<G> fst ` NL2"
  unfolding no_labels.entails_\<G>_def entails_\<G>_L_def by force

lemma red_inf_impl: "\<iota> \<in> Red_I NL \<Longrightarrow> to_F \<iota> \<in> no_labels.Red_I_\<G> (fst ` NL)"
  unfolding no_labels.Red_I_\<G>_def Red_I_def
proof clarify
  fix X Xa q
  assume
    q_in: "q \<in> Q" and
    i_in_inter: "\<iota> \<in> (\<Inter>q \<in> Q. Red_I_\<G>_L_q q NL)"
  have i_in_q: "\<iota> \<in> Red_I_\<G>_L_q q NL" using q_in i_in_inter image_eqI by blast
  then have i_in: "\<iota> \<in> Inf_FL" unfolding Red_I_\<G>_L_q_def by blast
  have to_F_in: "to_F \<iota> \<in> Inf_F" unfolding to_F_def using Inf_FL_to_Inf_F[OF i_in] .
  have rephrase1: "(\<Union>CL\<in>NL. \<G>_F_q q (fst CL)) = (\<Union> (\<G>_F_q q ` fst ` NL))" by blast
  have rephrase2: "fst (concl_of \<iota>) = concl_of (to_F \<iota>)"
    unfolding concl_of_def to_F_def by simp
  have subs_red: "(\<G>_I_L_q q \<iota> \<noteq> None \<and> the (\<G>_I_L_q q \<iota>) \<subseteq> Red_I_q q (\<G>_Fset_L_q q NL))
    \<or> (\<G>_I_L_q q \<iota> = None \<and> \<G>_F_L_q q (concl_of \<iota>) \<subseteq> \<G>_Fset_L_q q NL \<union> Red_F_q q (\<G>_Fset_L_q q NL))"
    using i_in_q unfolding Red_I_\<G>_L_q_def by blast
  then have to_F_subs_red: "(\<G>_I_q q (to_F \<iota>) \<noteq> None \<and>
      the (\<G>_I_q q (to_F \<iota>)) \<subseteq> Red_I_q q (no_labels.\<G>_Fset_q q (fst ` NL)))
    \<or> (\<G>_I_q q (to_F \<iota>) = None \<and>
      \<G>_F_q q (concl_of (to_F \<iota>))
      \<subseteq> no_labels.\<G>_Fset_q q (fst ` NL) \<union> Red_F_q q (no_labels.\<G>_Fset_q q (fst ` NL)))"
    using rephrase1 rephrase2 by metis
  then show "to_F \<iota> \<in> no_labels.Red_I_\<G>_q q (fst ` NL)"
    using to_F_in unfolding no_labels.Red_I_\<G>_q_def by simp
qed

(* lem:labeled-saturation-intersection *)
lemma labeled_family_saturation_lifting: "saturated NL \<Longrightarrow> no_labels.saturated (fst ` NL)"
  unfolding saturated_def no_labels.saturated_def Inf_from_def no_labels.Inf_from_def
proof clarify
  fix \<iota>F
  assume
    labeled_sat: "{\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL} \<subseteq> Red_I NL" and
    iF_in: "\<iota>F \<in> Inf_F" and
    iF_prems: "set (prems_of \<iota>F) \<subseteq> fst ` NL"
  define Lli where "Lli i = (SOME x. ((prems_of \<iota>F)!i,x) \<in> NL)" for i
  have [simp]:"((prems_of \<iota>F)!i,Lli i) \<in> NL" if "i < length (prems_of \<iota>F)" for i
    using that iF_prems nth_mem someI_ex unfolding Lli_def by (metis DomainE Domain_fst subset_eq)
  define Ll where "Ll = map Lli [0..<length (prems_of \<iota>F)]"
  have Ll_length: "length Ll = length (prems_of \<iota>F)" unfolding Ll_def by auto
  have subs_NL: "set (zip (prems_of \<iota>F) Ll) \<subseteq> NL" unfolding Ll_def by (auto simp:in_set_zip)
  obtain L0 where L0: "Infer (zip (prems_of \<iota>F) Ll) (concl_of \<iota>F, L0) \<in> Inf_FL"
    using Inf_F_to_Inf_FL[OF iF_in Ll_length] ..
  define \<iota>FL where "\<iota>FL = Infer (zip (prems_of \<iota>F) Ll) (concl_of \<iota>F, L0)"
  then have "set (prems_of \<iota>FL) \<subseteq> NL" using subs_NL by simp
  then have "\<iota>FL \<in> {\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL}" unfolding \<iota>FL_def using L0 by blast
  then have "\<iota>FL \<in> Red_I NL" using labeled_sat by fast
  moreover have "\<iota>F = to_F \<iota>FL" unfolding to_F_def \<iota>FL_def using Ll_length by (cases \<iota>F) auto
  ultimately show "\<iota>F \<in> no_labels.Red_I_\<G> (fst ` NL)"
    by (auto intro: red_inf_impl)
qed

(* thm:labeled-static-ref-compl-intersection *)
theorem labeled_static_ref:
  assumes calc: "statically_complete_calculus Bot_F Inf_F (\<Turnstile>\<inter>\<G>) no_labels.Red_I_\<G>
    no_labels.Red_F_\<G>_empty"
  shows "statically_complete_calculus Bot_FL Inf_FL (\<Turnstile>\<inter>\<G>L) Red_I Red_F"
proof
  fix Bl :: \<open>'f \<times> 'l\<close> and Nl :: \<open>('f \<times> 'l) set\<close>
  assume
    Bl_in: \<open>Bl \<in> Bot_FL\<close> and
    Nl_sat: \<open>saturated Nl\<close> and
    Nl_entails_Bl: \<open>Nl \<Turnstile>\<inter>\<G>L {Bl}\<close>
  define B where "B = fst Bl"
  have B_in: "B \<in> Bot_F" using Bl_in B_def SigmaE by force
  define N where "N = fst ` Nl"
  have N_sat: "no_labels.saturated N"
    using N_def Nl_sat labeled_family_saturation_lifting by blast
  have N_entails_B: "N \<Turnstile>\<inter>\<G> {B}"
    using Nl_entails_Bl unfolding labeled_entailment_lifting N_def B_def by force
  have "\<exists>B' \<in> Bot_F. B' \<in> N" using B_in N_sat N_entails_B
      calc[unfolded statically_complete_calculus_def
        statically_complete_calculus_axioms_def]
    by blast
  then obtain B' where in_Bot: "B' \<in> Bot_F" and in_N: "B' \<in> N" by force
  then have "B' \<in> fst ` Bot_FL" by fastforce
  obtain Bl' where in_Nl: "Bl' \<in> Nl" and fst_Bl': "fst Bl' = B'"
    using in_N unfolding N_def by blast
  have "Bl' \<in> Bot_FL" using fst_Bl' in_Bot vimage_fst by fastforce
  then show \<open>\<exists>Bl'\<in>Bot_FL. Bl' \<in> Nl\<close> using in_Nl by blast
qed

end

end
