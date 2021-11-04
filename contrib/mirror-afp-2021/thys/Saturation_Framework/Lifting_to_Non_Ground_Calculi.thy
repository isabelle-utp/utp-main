(*  Title:       Lifting to Non-Ground Calculi
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020 *)

section \<open>Lifting to Non-ground Calculi\<close>

text \<open>The section 3.1 to 3.3 of the report are covered by the current section.
  Various forms of lifting are proven correct. These allow to obtain the dynamic
  refutational completeness of a non-ground calculus from the static refutational
  completeness of its ground counterpart.\<close>

theory Lifting_to_Non_Ground_Calculi
  imports
    Intersection_Calculus
    Calculus_Variations
    Well_Quasi_Orders.Minimal_Elements
begin


subsection \<open>Standard Lifting\<close>

locale standard_lifting = inference_system Inf_F +
  ground: calculus Bot_G Inf_G entails_G Red_I_G Red_F_G
  for
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    Inf_G ::  \<open>'g inference set\<close> and
    entails_G ::  \<open>'g set \<Rightarrow> 'g set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Red_I_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close>
  + fixes
    Bot_F :: \<open>'f set\<close> and
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_I :: \<open>'f inference \<Rightarrow> 'g inference set option\<close>
  assumes
    Bot_F_not_empty: "Bot_F \<noteq> {}" and
    Bot_map_not_empty: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<noteq> {}\<close> and
    Bot_map: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<subseteq> Bot_G\<close> and
    Bot_cond: \<open>\<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_F\<close> and
    inf_map: \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_I \<iota> \<noteq> None \<Longrightarrow> the (\<G>_I \<iota>) \<subseteq> Red_I_G (\<G>_F (concl_of \<iota>))\<close>
begin

abbreviation \<G>_Fset :: \<open>'f set \<Rightarrow> 'g set\<close> where
  \<open>\<G>_Fset N \<equiv> \<Union> (\<G>_F ` N)\<close>

lemma \<G>_subset: \<open>N1 \<subseteq> N2 \<Longrightarrow> \<G>_Fset N1 \<subseteq> \<G>_Fset N2\<close> by auto

abbreviation entails_\<G>  :: \<open>'f set \<Rightarrow> 'f set \<Rightarrow> bool\<close> (infix "\<Turnstile>\<G>" 50) where
  \<open>N1 \<Turnstile>\<G> N2 \<equiv> \<G>_Fset N1 \<Turnstile>G \<G>_Fset N2\<close>

lemma subs_Bot_G_entails:
  assumes
    not_empty: \<open>sB \<noteq> {}\<close> and
    in_bot: \<open>sB \<subseteq> Bot_G\<close>
  shows \<open>sB \<Turnstile>G N\<close>
proof -
  have \<open>\<exists>B. B \<in> sB\<close> using not_empty by auto
  then obtain B where B_in: \<open>B \<in> sB\<close> by auto
  then have r_trans: \<open>{B} \<Turnstile>G N\<close> using ground.bot_entails_all in_bot by auto
  have l_trans: \<open>sB \<Turnstile>G {B}\<close> using B_in ground.subset_entailed by auto
  then show ?thesis using r_trans ground.entails_trans[of sB "{B}"] by auto
qed

(* lem:derived-consequence-relation *)
sublocale consequence_relation Bot_F entails_\<G>
proof
  show "Bot_F \<noteq> {}" using Bot_F_not_empty .
next
  show \<open>B\<in>Bot_F \<Longrightarrow> {B} \<Turnstile>\<G> N\<close> for B N
  proof -
    assume \<open>B \<in> Bot_F\<close>
    then show \<open>{B} \<Turnstile>\<G> N\<close>
      using Bot_map ground.bot_entails_all[of _ "\<G>_Fset N"] subs_Bot_G_entails Bot_map_not_empty
      by auto
  qed
next
  fix N1 N2 :: \<open>'f set\<close>
  assume
    \<open>N2 \<subseteq> N1\<close>
  then show \<open>N1 \<Turnstile>\<G> N2\<close> using \<G>_subset ground.subset_entailed by auto
next
  fix N1 N2
  assume
    N1_entails_C: \<open>\<forall>C \<in> N2. N1 \<Turnstile>\<G> {C}\<close>
  show \<open>N1 \<Turnstile>\<G> N2\<close> using ground.all_formulas_entailed N1_entails_C
    by (smt UN_E UN_I ground.entail_set_all_formulas singletonI)
next
  fix N1 N2 N3
  assume
    \<open>N1 \<Turnstile>\<G> N2\<close> and \<open>N2 \<Turnstile>\<G> N3\<close>
  then show \<open>N1 \<Turnstile>\<G> N3\<close> using ground.entails_trans by blast
qed

definition Red_I_\<G> :: "'f set \<Rightarrow> 'f inference set" where
  \<open>Red_I_\<G> N = {\<iota> \<in> Inf_F. (\<G>_I \<iota> \<noteq> None \<and> the (\<G>_I \<iota>) \<subseteq> Red_I_G (\<G>_Fset N))
  \<or> (\<G>_I \<iota> = None \<and> \<G>_F (concl_of \<iota>) \<subseteq> \<G>_Fset N \<union> Red_F_G (\<G>_Fset N))}\<close>

definition Red_F_\<G> :: "'f set \<Rightarrow> 'f set" where
  \<open>Red_F_\<G> N = {C. \<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_Fset N)}\<close>
end

subsection \<open>Strong Standard Lifting\<close>

(* rmk:strong-standard-lifting *)
locale strong_standard_lifting = inference_system Inf_F +
  ground: calculus Bot_G Inf_G entails_G Red_I_G Red_F_G
  for
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    Inf_G ::  \<open>'g inference set\<close> and
    entails_G ::  \<open>'g set  \<Rightarrow> 'g set  \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Red_I_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close>
  + fixes
    Bot_F :: \<open>'f set\<close> and
    \<G>_F :: \<open>'f \<Rightarrow> 'g set\<close> and
    \<G>_I :: \<open>'f inference \<Rightarrow> 'g inference set option\<close>
  assumes
    Bot_F_not_empty: "Bot_F \<noteq> {}" and
    Bot_map_not_empty: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<noteq> {}\<close> and
    Bot_map: \<open>B \<in> Bot_F \<Longrightarrow> \<G>_F B \<subseteq> Bot_G\<close> and
    Bot_cond: \<open>\<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_F\<close> and
    strong_inf_map: \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_I \<iota> \<noteq> None \<Longrightarrow> concl_of ` (the (\<G>_I \<iota>)) \<subseteq> (\<G>_F (concl_of \<iota>))\<close> and
    inf_map_in_Inf: \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_I \<iota> \<noteq> None \<Longrightarrow> the (\<G>_I \<iota>) \<subseteq> Inf_G\<close>
begin

sublocale standard_lifting Inf_F Bot_G Inf_G "(\<Turnstile>G)" Red_I_G Red_F_G Bot_F \<G>_F \<G>_I
proof
  show "Bot_F \<noteq> {}" using Bot_F_not_empty .
next
  fix B
  assume b_in: "B \<in> Bot_F"
  show "\<G>_F B \<noteq> {}" using Bot_map_not_empty[OF b_in] .
next
  fix B
  assume b_in: "B \<in> Bot_F"
  show "\<G>_F B \<subseteq> Bot_G" using Bot_map[OF b_in] .
next
  show "\<And>C. \<G>_F C \<inter> Bot_G \<noteq> {} \<longrightarrow> C \<in> Bot_F" using Bot_cond .
next
  fix \<iota>
  assume i_in: "\<iota> \<in> Inf_F" and
    some_g: "\<G>_I \<iota> \<noteq> None"
  show "the (\<G>_I \<iota>) \<subseteq> Red_I_G (\<G>_F (concl_of \<iota>))"
  proof
    fix \<iota>G
    assume ig_in1: "\<iota>G \<in> the (\<G>_I \<iota>)"
    then have ig_in2: "\<iota>G \<in> Inf_G" using inf_map_in_Inf[OF i_in some_g] by blast
    show "\<iota>G \<in> Red_I_G (\<G>_F (concl_of \<iota>))"
      using strong_inf_map[OF i_in some_g] ground.Red_I_of_Inf_to_N[OF ig_in2]
        ig_in1 by blast
  qed
qed

end
  

subsection \<open>Lifting with a Family of Tiebreaker Orderings\<close>

locale tiebreaker_lifting =
  empty_ord?: standard_lifting Inf_F Bot_G Inf_G entails_G Red_I_G Red_F_G Bot_F \<G>_F \<G>_I
  for
    Bot_F :: \<open>'f set\<close> and
    Inf_F :: \<open>'f inference set\<close> and
    Bot_G :: \<open>'g set\<close> and
    entails_G :: \<open>'g set \<Rightarrow> 'g set \<Rightarrow> bool\<close> (infix "\<Turnstile>G" 50) and
    Inf_G :: \<open>'g inference set\<close> and
    Red_I_G :: \<open>'g set \<Rightarrow> 'g inference set\<close> and
    Red_F_G :: \<open>'g set \<Rightarrow> 'g set\<close> and
    \<G>_F :: "'f \<Rightarrow> 'g set" and
    \<G>_I :: "'f inference \<Rightarrow> 'g inference set option"
  + fixes
    Prec_F_g :: \<open>'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool\<close>
  assumes
    all_wf: "minimal_element (Prec_F_g g) UNIV"
begin

definition Red_F_\<G> :: "'f set \<Rightarrow> 'f set" where
  \<open>Red_F_\<G> N = {C. \<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_Fset N) \<or> (\<exists>E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)}\<close>

lemma Prec_trans:
  assumes
    \<open>Prec_F_g D A B\<close> and
    \<open>Prec_F_g D B C\<close>
  shows
    \<open>Prec_F_g D A C\<close>
  using minimal_element.po assms unfolding po_on_def transp_on_def by (smt UNIV_I all_wf)

lemma prop_nested_in_set: "D \<in> P C \<Longrightarrow> C \<in> {C. \<forall>D \<in> P C. A D \<or> B C D} \<Longrightarrow> A D \<or> B C D"
  by blast

(* lem:wolog-C'-nonredundant *)
lemma Red_F_\<G>_equiv_def:
  \<open>Red_F_\<G> N = {C. \<forall>Di \<in> \<G>_F C. Di \<in> Red_F_G (\<G>_Fset N) \<or>
    (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g Di E C \<and> Di \<in> \<G>_F E)}\<close>
proof (rule; clarsimp)
  fix C D
  assume
    C_in: \<open>C \<in> Red_F_\<G> N\<close> and
    D_in: \<open>D \<in> \<G>_F C\<close> and
    not_sec_case: \<open>\<forall>E \<in> N - Red_F_\<G> N. Prec_F_g D E C \<longrightarrow> D \<notin> \<G>_F E\<close>
  have C_in_unfolded: "C \<in> {C. \<forall>Di \<in> \<G>_F C. Di \<in> Red_F_G (\<G>_Fset N) \<or>
    (\<exists>E\<in>N. Prec_F_g Di E C \<and> Di \<in> \<G>_F E)}"
    using C_in unfolding Red_F_\<G>_def .
  have neg_not_sec_case: \<open>\<not> (\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    using not_sec_case by clarsimp
  have unfol_C_D: \<open>D \<in> Red_F_G (\<G>_Fset N) \<or> (\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    using prop_nested_in_set[of D \<G>_F C "\<lambda>x. x \<in> Red_F_G (\<Union> (\<G>_F ` N))"
      "\<lambda>x y. \<exists>E \<in> N. Prec_F_g y E x \<and> y \<in> \<G>_F E", OF D_in C_in_unfolded] by blast
  show \<open>D \<in> Red_F_G (\<G>_Fset N)\<close>
  proof (rule ccontr)
    assume contrad: \<open>D \<notin> Red_F_G (\<G>_Fset N)\<close>
    have non_empty: \<open>\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close> using contrad unfol_C_D by auto
    define B where \<open>B = {E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F E}\<close>
    then have B_non_empty: \<open>B \<noteq> {}\<close> using non_empty by auto
    interpret minimal_element "Prec_F_g D" UNIV using all_wf[of D] .
    obtain F :: 'f where F: \<open>F = min_elt B\<close> by auto
    then have D_in_F: \<open>D \<in> \<G>_F F\<close> unfolding B_def using non_empty
      by (smt Sup_UNIV Sup_upper UNIV_I contra_subsetD empty_iff empty_subsetI mem_Collect_eq
        min_elt_mem unfol_C_D)
    have F_prec: \<open>Prec_F_g D F C\<close> using F min_elt_mem[of B, OF _ B_non_empty] unfolding B_def by auto
    have F_not_in: \<open>F \<notin> Red_F_\<G> N\<close>
    proof
      assume F_in: \<open>F \<in> Red_F_\<G> N\<close>
      have unfol_F_D: \<open>D \<in> Red_F_G (\<G>_Fset N) \<or> (\<exists>G\<in>N. Prec_F_g D G F \<and> D \<in> \<G>_F G)\<close>
        using F_in D_in_F unfolding Red_F_\<G>_def by auto
      then have \<open>\<exists>G\<in>N. Prec_F_g D G F \<and> D \<in> \<G>_F G\<close> using contrad D_in unfolding Red_F_\<G>_def by auto
      then obtain G where G_in: \<open>G \<in> N\<close> and G_prec: \<open>Prec_F_g D G F\<close> and G_map: \<open>D \<in> \<G>_F G\<close> by auto
      have \<open>Prec_F_g D G C\<close> using G_prec F_prec Prec_trans by blast
      then have \<open>G \<in> B\<close> unfolding B_def using G_in G_map by auto
      then show \<open>False\<close> using F G_prec min_elt_minimal[of B G, OF _ B_non_empty] by auto
    qed
    have \<open>F \<in> N\<close> using F by (metis B_def B_non_empty mem_Collect_eq min_elt_mem top_greatest)
    then have \<open>F \<in> N - Red_F_\<G> N\<close> using F_not_in by auto
    then show \<open>False\<close>
      using D_in_F neg_not_sec_case F_prec by blast
  qed
next
  fix C
  assume only_if: \<open>\<forall>D\<in>\<G>_F C. D \<in> Red_F_G (\<G>_Fset N) \<or> (\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
  show \<open>C \<in> Red_F_\<G> N\<close> unfolding Red_F_\<G>_def using only_if by auto
qed

(* lem:lifting-main-technical *)
lemma not_red_map_in_map_not_red: \<open>\<G>_Fset N - Red_F_G (\<G>_Fset N) \<subseteq> \<G>_Fset (N - Red_F_\<G> N)\<close>
proof
  fix D
  assume
    D_hyp: \<open>D \<in> \<G>_Fset N - Red_F_G (\<G>_Fset N)\<close>
  interpret minimal_element "Prec_F_g D" UNIV using all_wf[of D] .
  have D_in: \<open>D \<in> \<G>_Fset N\<close> using D_hyp by blast
  have  D_not_in: \<open>D \<notin> Red_F_G (\<G>_Fset N)\<close> using D_hyp by blast
  have exist_C: \<open>\<exists>C. C \<in> N \<and> D \<in> \<G>_F C\<close> using D_in by auto
  define B where \<open>B = {C \<in> N. D \<in> \<G>_F C}\<close>
  obtain C where C: \<open>C = min_elt B\<close> by auto
  have C_in_N: \<open>C \<in> N\<close>
    using exist_C by (metis B_def C empty_iff mem_Collect_eq min_elt_mem top_greatest)
  have D_in_C: \<open>D \<in> \<G>_F C\<close>
    using exist_C by (metis B_def C empty_iff mem_Collect_eq min_elt_mem top_greatest)
  have C_not_in: \<open>C \<notin> Red_F_\<G> N\<close>
  proof
    assume C_in: \<open>C \<in> Red_F_\<G> N\<close>
    have \<open>D \<in> Red_F_G (\<G>_Fset N) \<or> (\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
      using C_in D_in_C unfolding Red_F_\<G>_def by auto
    then show \<open>False\<close>
      proof
        assume \<open>D \<in> Red_F_G (\<G>_Fset N)\<close>
        then show \<open>False\<close> using D_not_in by simp
      next
        assume \<open>\<exists>E\<in>N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close>
        then show \<open>False\<close>
          using C by (metis (no_types, lifting) B_def UNIV_I empty_iff mem_Collect_eq
              min_elt_minimal top_greatest)
      qed
  qed
  show \<open>D \<in> \<G>_Fset (N - Red_F_\<G> N)\<close> using D_in_C C_not_in C_in_N by blast
qed
  
(* lem:nonredundant-entails-redundant *)
lemma Red_F_Bot_F: \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>\<G> {B} \<Longrightarrow> N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close>
proof -
  fix B N
  assume
    B_in: \<open>B \<in> Bot_F\<close> and
    N_entails: \<open>N \<Turnstile>\<G> {B}\<close>
  then have to_bot: \<open>\<G>_Fset N - Red_F_G (\<G>_Fset N) \<Turnstile>G \<G>_F B\<close>
    using ground.Red_F_Bot Bot_map
      by (smt cSup_singleton ground.entail_set_all_formulas image_insert image_is_empty subsetCE)
  have from_f: \<open>\<G>_Fset (N - Red_F_\<G> N) \<Turnstile>G \<G>_Fset N - Red_F_G (\<G>_Fset N)\<close>
    using ground.subset_entailed[OF not_red_map_in_map_not_red] by blast
  then have \<open>\<G>_Fset (N - Red_F_\<G> N) \<Turnstile>G \<G>_F B\<close> using to_bot ground.entails_trans by blast
  then show \<open>N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close> using Bot_map by simp
qed

(* lem:redundancy-monotonic-addition 1/2 *)
lemma Red_F_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close>
  using ground.Red_F_of_subset unfolding Red_F_\<G>_def by clarsimp (meson \<G>_subset subsetD)

(* lem:redundancy-monotonic-addition 2/2 *)
lemma Red_I_of_subset_F: \<open>N \<subseteq> N' \<Longrightarrow> Red_I_\<G> N \<subseteq> Red_I_\<G> N'\<close>
  using Collect_mono \<G>_subset subset_iff ground.Red_I_of_subset unfolding Red_I_\<G>_def
  by (smt ground.Red_F_of_subset Un_iff)

(* lem:redundancy-monotonic-deletion-forms *)
lemma Red_F_of_Red_F_subset_F: \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> (N - N')\<close>
proof
  fix N N' C
  assume
    N'_in_Red_F_N: \<open>N' \<subseteq> Red_F_\<G> N\<close> and
    C_in_red_F_N: \<open>C \<in> Red_F_\<G> N\<close>
  have lem8: \<open>\<forall>D \<in> \<G>_F C. D \<in> Red_F_G (\<G>_Fset N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    using Red_F_\<G>_equiv_def C_in_red_F_N by blast
  show \<open>C \<in> Red_F_\<G> (N - N')\<close> unfolding Red_F_\<G>_def
  proof (rule,rule)
    fix D
    assume \<open>D \<in> \<G>_F C\<close>
    then have \<open>D \<in> Red_F_G (\<G>_Fset N) \<or> (\<exists>E \<in> (N - Red_F_\<G> N). Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
      using lem8 by auto
    then show \<open>D \<in> Red_F_G (\<G>_Fset (N - N')) \<or> (\<exists>E\<in>N - N'. Prec_F_g D E C \<and> D \<in> \<G>_F E)\<close>
    proof
      assume \<open>D \<in> Red_F_G (\<G>_Fset N)\<close>
      then have \<open>D \<in> Red_F_G (\<G>_Fset N - Red_F_G (\<G>_Fset N))\<close>
        using ground.Red_F_of_Red_F_subset[of "Red_F_G (\<G>_Fset N)" "\<G>_Fset N"] by auto
      then have \<open>D \<in> Red_F_G (\<G>_Fset (N - Red_F_\<G> N))\<close>
        using ground.Red_F_of_subset[OF not_red_map_in_map_not_red[of N]] by auto
      then have \<open>D \<in> Red_F_G (\<G>_Fset (N - N'))\<close>
        using N'_in_Red_F_N \<G>_subset[of "N - Red_F_\<G> N" "N - N'"]
        by (smt DiffE DiffI ground.Red_F_of_subset subsetCE subsetI)
      then show ?thesis by blast
    next
      assume \<open>\<exists>E\<in>N - Red_F_\<G> N. Prec_F_g D E C \<and> D \<in> \<G>_F E\<close>
      then obtain E where
        E_in: \<open>E\<in>N - Red_F_\<G> N\<close> and
        E_prec_C: \<open>Prec_F_g D E C\<close> and
        D_in: \<open>D \<in> \<G>_F E\<close>
        by auto
      have \<open>E \<in> N - N'\<close> using E_in N'_in_Red_F_N by blast
      then show ?thesis using E_prec_C D_in by blast
    qed
  qed
qed

(* lem:redundancy-monotonic-deletion-infs *)
lemma Red_I_of_Red_F_subset_F: \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_I_\<G> N \<subseteq> Red_I_\<G> (N - N') \<close>
proof
  fix N N' \<iota>
  assume
    N'_in_Red_F_N: \<open>N' \<subseteq> Red_F_\<G> N\<close> and
    i_in_Red_I_N: \<open>\<iota> \<in> Red_I_\<G> N\<close>
  have i_in: \<open>\<iota> \<in> Inf_F\<close> using i_in_Red_I_N unfolding Red_I_\<G>_def by blast
  {
    assume not_none: "\<G>_I \<iota> \<noteq> None"
    have \<open>\<forall>\<iota>' \<in> the (\<G>_I \<iota>). \<iota>' \<in> Red_I_G (\<G>_Fset N)\<close>
      using not_none i_in_Red_I_N unfolding Red_I_\<G>_def by auto
    then have \<open>\<forall>\<iota>' \<in> the (\<G>_I \<iota>). \<iota>' \<in> Red_I_G (\<G>_Fset N - Red_F_G (\<G>_Fset N))\<close>
      using not_none ground.Red_I_of_Red_F_subset by blast
    then have ip_in_Red_I_G: \<open>\<forall>\<iota>' \<in> the (\<G>_I \<iota>). \<iota>' \<in> Red_I_G (\<G>_Fset (N - Red_F_\<G> N))\<close>
      using not_none ground.Red_I_of_subset[OF not_red_map_in_map_not_red[of N]] by auto
    then have not_none_in: \<open>\<forall>\<iota>' \<in> the (\<G>_I \<iota>). \<iota>' \<in> Red_I_G (\<G>_Fset (N - N'))\<close>
      using not_none N'_in_Red_F_N
      by (meson Diff_mono ground.Red_I_of_subset \<G>_subset subset_iff subset_refl)
    then have "the (\<G>_I \<iota>) \<subseteq> Red_I_G (\<G>_Fset (N - N'))" by blast
  }
  moreover {
    assume none: "\<G>_I \<iota> = None"
    have ground_concl_subs: "\<G>_F (concl_of \<iota>) \<subseteq> (\<G>_Fset N \<union> Red_F_G (\<G>_Fset N))"
      using none i_in_Red_I_N unfolding Red_I_\<G>_def by blast
    then have d_in_imp12: "D \<in> \<G>_F (concl_of \<iota>) \<Longrightarrow> D \<in> \<G>_Fset N - Red_F_G (\<G>_Fset N) \<or> D \<in> Red_F_G (\<G>_Fset N)"
      by blast
    have d_in_imp1: "D \<in> \<G>_Fset N - Red_F_G (\<G>_Fset N) \<Longrightarrow> D \<in> \<G>_Fset (N - N')"
      using not_red_map_in_map_not_red N'_in_Red_F_N by blast
    have d_in_imp_d_in: "D \<in> Red_F_G (\<G>_Fset N) \<Longrightarrow> D \<in> Red_F_G (\<G>_Fset N - Red_F_G (\<G>_Fset N))"
      using ground.Red_F_of_Red_F_subset[of "Red_F_G (\<G>_Fset N)" "\<G>_Fset N"] by blast
    have g_subs1: "\<G>_Fset N - Red_F_G (\<G>_Fset N) \<subseteq> \<G>_Fset (N - Red_F_\<G> N)"
      using not_red_map_in_map_not_red unfolding Red_F_\<G>_def by auto
    have g_subs2: "\<G>_Fset (N - Red_F_\<G> N) \<subseteq> \<G>_Fset (N - N')"
      using N'_in_Red_F_N by blast
    have d_in_imp2: "D \<in> Red_F_G (\<G>_Fset N) \<Longrightarrow> D \<in> Red_F_G (\<G>_Fset (N - N'))"
      using ground.Red_F_of_subset ground.Red_F_of_subset[OF g_subs1]
        ground.Red_F_of_subset[OF g_subs2] d_in_imp_d_in by blast
    have "\<G>_F (concl_of \<iota>) \<subseteq> (\<G>_Fset (N - N') \<union> Red_F_G (\<G>_Fset (N - N')))"
      using d_in_imp12 d_in_imp1 d_in_imp2
      by (smt ground.Red_F_of_Red_F_subset ground.Red_F_of_subset UnCI UnE Un_Diff_cancel2
        ground_concl_subs g_subs1 g_subs2 subset_iff)
  }
  ultimately show \<open>\<iota> \<in> Red_I_\<G> (N - N')\<close> using i_in unfolding Red_I_\<G>_def by auto
qed

(* lem:concl-contained-implies-red-inf *)
lemma Red_I_of_Inf_to_N_F:
  assumes
    i_in: \<open>\<iota> \<in> Inf_F\<close> and
    concl_i_in: \<open>concl_of \<iota> \<in> N\<close>
  shows
    \<open>\<iota> \<in> Red_I_\<G> N \<close>
proof -
  have \<open>\<iota> \<in> Inf_F \<Longrightarrow> \<G>_I \<iota> \<noteq> None \<Longrightarrow> the (\<G>_I \<iota>) \<subseteq> Red_I_G (\<G>_F (concl_of \<iota>))\<close> using inf_map by simp
  moreover have \<open>Red_I_G (\<G>_F (concl_of \<iota>)) \<subseteq> Red_I_G (\<G>_Fset N)\<close>
    using concl_i_in ground.Red_I_of_subset by blast
  moreover have "\<iota> \<in> Inf_F \<Longrightarrow> \<G>_I \<iota> = None \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<G>_F (concl_of \<iota>) \<subseteq> \<G>_Fset N"
    by blast
  ultimately show ?thesis using i_in concl_i_in unfolding Red_I_\<G>_def by auto
qed

(* thm:FRedsqsubset-is-red-crit and also thm:lifted-red-crit if ordering empty *)
sublocale calculus Bot_F Inf_F entails_\<G> Red_I_\<G> Red_F_\<G>
proof
  fix B N N' \<iota>
  show \<open>Red_I_\<G> N \<subseteq> Inf_F\<close> unfolding Red_I_\<G>_def by blast
  show \<open>B \<in> Bot_F \<Longrightarrow> N \<Turnstile>\<G> {B} \<Longrightarrow> N - Red_F_\<G> N \<Turnstile>\<G> {B}\<close> using Red_F_Bot_F by simp
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> N'\<close> using Red_F_of_subset_F by simp
  show \<open>N \<subseteq> N' \<Longrightarrow> Red_I_\<G> N \<subseteq> Red_I_\<G> N'\<close> using Red_I_of_subset_F by simp
  show \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_F_\<G> N \<subseteq> Red_F_\<G> (N - N')\<close> using Red_F_of_Red_F_subset_F by simp
  show \<open>N' \<subseteq> Red_F_\<G> N \<Longrightarrow> Red_I_\<G> N \<subseteq> Red_I_\<G> (N - N')\<close> using Red_I_of_Red_F_subset_F by simp
  show \<open>\<iota> \<in> Inf_F \<Longrightarrow> concl_of \<iota> \<in> N \<Longrightarrow> \<iota> \<in> Red_I_\<G> N\<close> using Red_I_of_Inf_to_N_F by simp
qed

end

lemma wf_empty_rel: "minimal_element (\<lambda>_ _. False) UNIV"
  by (simp add: minimal_element.intro po_on_def transp_onI wfp_on_imp_irreflp_on)

lemma standard_empty_tiebreaker_equiv: "standard_lifting Inf_F Bot_G Inf_G entails_G Red_I_G
  Red_F_G Bot_F \<G>_F \<G>_I = tiebreaker_lifting Bot_F Inf_F Bot_G entails_G Inf_G Red_I_G
  Red_F_G \<G>_F \<G>_I (\<lambda>g C C'. False)"
proof -
  have "tiebreaker_lifting_axioms (\<lambda>g C C'. False)"
    unfolding tiebreaker_lifting_axioms_def using wf_empty_rel by simp
  then show ?thesis
    unfolding standard_lifting_def tiebreaker_lifting_def by blast
qed

context standard_lifting
begin

  interpretation empt_ord: tiebreaker_lifting Bot_F Inf_F Bot_G entails_G Inf_G Red_I_G
    Red_F_G \<G>_F \<G>_I "\<lambda>g C C'. False"
    using standard_empty_tiebreaker_equiv using standard_lifting_axioms by blast

  lemma red_f_equiv: "empt_ord.Red_F_\<G> = Red_F_\<G>"
    unfolding Red_F_\<G>_def empt_ord.Red_F_\<G>_def by simp

  sublocale calc?: calculus Bot_F Inf_F entails_\<G> Red_I_\<G> Red_F_\<G>
    using empt_ord.calculus_axioms red_f_equiv by fastforce

  lemma grounded_inf_in_ground_inf: "\<iota> \<in> Inf_F \<Longrightarrow> \<G>_I \<iota> \<noteq> None \<Longrightarrow> the (\<G>_I \<iota>) \<subseteq> Inf_G"
    using inf_map ground.Red_I_to_Inf by blast

  abbreviation ground_Inf_overapproximated :: "'f set \<Rightarrow> bool" where
    "ground_Inf_overapproximated N \<equiv> ground.Inf_from (\<G>_Fset N)
      \<subseteq> {\<iota>. \<exists>\<iota>'\<in> Inf_from N. \<G>_I \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_I \<iota>')} \<union> Red_I_G (\<G>_Fset N)"

(* abbreviation "saturated \<equiv> calc.saturated" *)

  lemma sat_inf_imp_ground_red:
    assumes
      "saturated N" and
      "\<iota>' \<in> Inf_from N" and
      "\<G>_I \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_I \<iota>')"
    shows "\<iota> \<in> Red_I_G (\<G>_Fset N)"
      using assms Red_I_\<G>_def unfolding saturated_def by auto

(* lem:sat-wrt-finf *)
  lemma sat_imp_ground_sat:
    "saturated N \<Longrightarrow> ground_Inf_overapproximated N \<Longrightarrow> ground.saturated (\<G>_Fset N)"
    unfolding ground.saturated_def using sat_inf_imp_ground_red by auto

(* thm:finf-complete *)
  theorem stat_ref_comp_to_non_ground:
    assumes
      stat_ref_G: "statically_complete_calculus Bot_G Inf_G entails_G Red_I_G Red_F_G" and
      sat_n_imp: "\<And>N. saturated N \<Longrightarrow> ground_Inf_overapproximated N"
    shows
      "statically_complete_calculus Bot_F Inf_F entails_\<G> Red_I_\<G> Red_F_\<G>"
  proof
    fix B N
    assume
      b_in: "B \<in> Bot_F" and
      sat_n: "saturated N" and
      n_entails_bot: "N \<Turnstile>\<G> {B}"
    have ground_n_entails: "\<G>_Fset N \<Turnstile>G \<G>_F B"
      using n_entails_bot by simp
    then obtain BG where bg_in1: "BG \<in> \<G>_F B"
      using Bot_map_not_empty[OF b_in] by blast
    then have bg_in: "BG \<in> Bot_G"
      using Bot_map[OF b_in] by blast
    have ground_n_entails_bot: "\<G>_Fset N \<Turnstile>G {BG}"
      using ground_n_entails bg_in1 ground.entail_set_all_formulas by blast
    have "ground.Inf_from (\<G>_Fset N) \<subseteq>
      {\<iota>. \<exists>\<iota>'\<in> Inf_from N. \<G>_I \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_I \<iota>')} \<union> Red_I_G (\<G>_Fset N)"
      using sat_n_imp[OF sat_n] .
    have "ground.saturated (\<G>_Fset N)"
      using sat_imp_ground_sat[OF sat_n sat_n_imp[OF sat_n]] .
    then have "\<exists>BG'\<in>Bot_G. BG' \<in> (\<G>_Fset N)"
      using stat_ref_G ground.calculus_axioms bg_in ground_n_entails_bot
      unfolding statically_complete_calculus_def statically_complete_calculus_axioms_def
      by blast
    then show "\<exists>B'\<in> Bot_F. B' \<in> N"
      using bg_in Bot_cond Bot_map_not_empty Bot_cond
      by blast
  qed
    
end

context tiebreaker_lifting 
begin

  (* lem:saturation-indep-of-sqsubset *)
  lemma saturated_empty_order_equiv_saturated:
    "saturated N = calc.saturated N"
    by (rule refl)
    
    (* lem:static-ref-compl-indep-of-sqsubset *)
  lemma static_empty_order_equiv_static:
    "statically_complete_calculus Bot_F Inf_F entails_\<G> Red_I_\<G> Red_F_\<G> =
      statically_complete_calculus Bot_F Inf_F entails_\<G> Red_I_\<G> empty_ord.Red_F_\<G>"
    unfolding statically_complete_calculus_def
    by (rule iffI) (standard,(standard)[],simp)+

    (* thm:FRedsqsubset-is-dyn-ref-compl *)
  theorem static_to_dynamic:
    "statically_complete_calculus Bot_F Inf_F entails_\<G> Red_I_\<G> empty_ord.Red_F_\<G> =
      dynamically_complete_calculus Bot_F Inf_F entails_\<G> Red_I_\<G> Red_F_\<G>"
    using dyn_equiv_stat static_empty_order_equiv_static
    by blast
   
end

subsection \<open>Lifting with a Family of Redundancy Criteria\<close>

locale lifting_intersection = inference_system Inf_F +
  ground: inference_system_family Q Inf_G_q +
  ground: consequence_relation_family Bot_G Q entails_q
  for
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Q :: "'q set" and
    Inf_G_q :: \<open>'q \<Rightarrow> 'g inference set\<close> and
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool" and
    Red_I_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set"
  + fixes
    Bot_F :: "'f set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_I_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option" and
    Prec_F_g :: "'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"
  assumes
    standard_lifting_family:
      "\<forall>q \<in> Q. tiebreaker_lifting Bot_F Inf_F Bot_G (entails_q q) (Inf_G_q q) (Red_I_q q)
         (Red_F_q q) (\<G>_F_q q) (\<G>_I_q q) Prec_F_g"
begin

abbreviation \<G>_Fset_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'g set" where
  "\<G>_Fset_q q N \<equiv> \<Union> (\<G>_F_q q ` N)"

definition Red_I_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f inference set" where
  "Red_I_\<G>_q q N = {\<iota> \<in> Inf_F. (\<G>_I_q q \<iota> \<noteq> None \<and> the (\<G>_I_q q \<iota>) \<subseteq> Red_I_q q (\<G>_Fset_q q N))
   \<or> (\<G>_I_q q \<iota> = None \<and> \<G>_F_q q (concl_of \<iota>) \<subseteq> (\<G>_Fset_q q N \<union> Red_F_q q (\<G>_Fset_q q N)))}"

definition Red_F_\<G>_empty_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty_q q N = {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_Fset_q q N)}"

definition Red_F_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_q q N =
   {C. \<forall>D \<in> \<G>_F_q q C. D \<in> Red_F_q q (\<G>_Fset_q q N) \<or> (\<exists>E \<in> N. Prec_F_g D E C \<and> D \<in> \<G>_F_q q E)}"

abbreviation entails_\<G>_q :: "'q \<Rightarrow> 'f set \<Rightarrow> 'f set \<Rightarrow> bool" where
  "entails_\<G>_q q N1 N2 \<equiv> entails_q q (\<G>_Fset_q q N1) (\<G>_Fset_q q N2)"

lemma red_crit_lifting_family:
  assumes q_in: "q \<in> Q"
  shows "calculus Bot_F Inf_F (entails_\<G>_q q) (Red_I_\<G>_q q) (Red_F_\<G>_q q)"
proof -
  interpret wf_lift:
    tiebreaker_lifting Bot_F Inf_F Bot_G "entails_q q" "Inf_G_q q" "Red_I_q q"
      "Red_F_q q" "\<G>_F_q q" "\<G>_I_q q" Prec_F_g
    using standard_lifting_family q_in by metis
  have "Red_I_\<G>_q q = wf_lift.Red_I_\<G>"
    unfolding Red_I_\<G>_q_def wf_lift.Red_I_\<G>_def by blast
  moreover have "Red_F_\<G>_q q = wf_lift.Red_F_\<G>"
    unfolding Red_F_\<G>_q_def wf_lift.Red_F_\<G>_def by blast
  ultimately show ?thesis
    using wf_lift.calculus_axioms by simp
qed

lemma red_crit_lifting_family_empty_ord:
  assumes q_in: "q \<in> Q"
  shows "calculus Bot_F Inf_F (entails_\<G>_q q) (Red_I_\<G>_q q) (Red_F_\<G>_empty_q q)"
proof -
  interpret wf_lift:
    tiebreaker_lifting Bot_F Inf_F Bot_G "entails_q q" "Inf_G_q q" "Red_I_q q"
      "Red_F_q q" "\<G>_F_q q" "\<G>_I_q q" Prec_F_g
    using standard_lifting_family q_in by metis
  have "Red_I_\<G>_q q = wf_lift.Red_I_\<G>"
    unfolding Red_I_\<G>_q_def wf_lift.Red_I_\<G>_def by blast
  moreover have "Red_F_\<G>_empty_q q = wf_lift.empty_ord.Red_F_\<G>"
    unfolding Red_F_\<G>_empty_q_def wf_lift.empty_ord.Red_F_\<G>_def by blast
  ultimately show ?thesis
    using wf_lift.calc.calculus_axioms by simp
qed

sublocale consequence_relation_family Bot_F Q entails_\<G>_q
proof (unfold_locales; (intro ballI)?)
  show "Q \<noteq> {}"
    by (rule ground.Q_nonempty)
next
  fix qi
  assume qi_in: "qi \<in> Q"

  interpret lift: tiebreaker_lifting Bot_F Inf_F Bot_G "entails_q qi" "Inf_G_q qi"
    "Red_I_q qi" "Red_F_q qi" "\<G>_F_q qi" "\<G>_I_q qi" Prec_F_g
    using qi_in by (metis standard_lifting_family)

  show "consequence_relation Bot_F (entails_\<G>_q qi)"
    by unfold_locales
qed

sublocale intersection_calculus Bot_F Inf_F Q entails_\<G>_q Red_I_\<G>_q Red_F_\<G>_q
  by unfold_locales (auto simp: Q_nonempty red_crit_lifting_family)

abbreviation entails_\<G> :: "'f set \<Rightarrow> 'f set \<Rightarrow> bool" (infix "\<Turnstile>\<inter>\<G>" 50) where
  "(\<Turnstile>\<inter>\<G>) \<equiv> entails"

abbreviation Red_I_\<G> :: "'f set \<Rightarrow> 'f inference set" where
  "Red_I_\<G> \<equiv> Red_I"

abbreviation Red_F_\<G> :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G> \<equiv> Red_F"

lemmas entails_\<G>_def = entails_def
lemmas Red_I_\<G>_def = Red_I_def
lemmas Red_F_\<G>_def = Red_F_def

sublocale empty_ord: intersection_calculus Bot_F Inf_F Q entails_\<G>_q Red_I_\<G>_q Red_F_\<G>_empty_q
  by unfold_locales (auto simp: Q_nonempty red_crit_lifting_family_empty_ord)

abbreviation Red_F_\<G>_empty :: "'f set \<Rightarrow> 'f set" where
  "Red_F_\<G>_empty \<equiv> empty_ord.Red_F"

lemmas Red_F_\<G>_empty_def = empty_ord.Red_F_def

lemma sat_inf_imp_ground_red_fam_inter:
  assumes
    sat_n: "saturated N" and
    i'_in: "\<iota>' \<in> Inf_from N" and
    q_in: "q \<in> Q" and
    grounding: "\<G>_I_q q \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_I_q q \<iota>')"
  shows "\<iota> \<in> Red_I_q q (\<G>_Fset_q q N)"
proof -
  have "\<iota>' \<in> Red_I_\<G>_q q N"
    using sat_n i'_in q_in all_red_crit calculus.saturated_def sat_int_to_sat_q
    by blast
  then have "the (\<G>_I_q q \<iota>') \<subseteq> Red_I_q q (\<G>_Fset_q q N)"
    by (simp add: Red_I_\<G>_q_def grounding)
  then show ?thesis
    using grounding by blast
qed

abbreviation ground_Inf_overapproximated :: "'q \<Rightarrow> 'f set \<Rightarrow> bool" where
  "ground_Inf_overapproximated q N \<equiv>
   ground.Inf_from_q q (\<G>_Fset_q q N)
   \<subseteq> {\<iota>. \<exists>\<iota>'\<in> Inf_from N. \<G>_I_q q \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_I_q q \<iota>')} \<union> Red_I_q q (\<G>_Fset_q q N)"

abbreviation ground_saturated :: "'q \<Rightarrow> 'f set \<Rightarrow> bool" where
  "ground_saturated q N \<equiv> ground.Inf_from_q q (\<G>_Fset_q q N) \<subseteq> Red_I_q q (\<G>_Fset_q q N)"

lemma sat_imp_ground_sat_fam_inter:
  "saturated N \<Longrightarrow> q \<in> Q \<Longrightarrow> ground_Inf_overapproximated q N \<Longrightarrow> ground_saturated q N"
  using sat_inf_imp_ground_red_fam_inter by auto

(* thm:intersect-finf-complete *)
theorem stat_ref_comp_to_non_ground_fam_inter:
  assumes
    stat_ref_G:
      "\<forall>q \<in> Q. statically_complete_calculus Bot_G (Inf_G_q q) (entails_q q) (Red_I_q q)
        (Red_F_q q)" and
    sat_n_imp: "\<And>N. saturated N \<Longrightarrow> \<exists>q \<in> Q. ground_Inf_overapproximated q N"
  shows
    "statically_complete_calculus Bot_F Inf_F entails_\<G> Red_I_\<G> Red_F_\<G>_empty"
    using empty_ord.calculus_axioms unfolding statically_complete_calculus_def
      statically_complete_calculus_axioms_def
proof (standard, clarify)
  fix B N
  assume
    b_in: "B \<in> Bot_F" and
    sat_n: "saturated N" and
    entails_bot: "N \<Turnstile>\<inter>\<G> {B}"
  then obtain q where
    q_in: "q \<in> Q" and
    inf_subs: "ground.Inf_from_q q (\<G>_Fset_q q N) \<subseteq>
      {\<iota>. \<exists>\<iota>'\<in> Inf_from N. \<G>_I_q q \<iota>' \<noteq> None \<and> \<iota> \<in> the (\<G>_I_q q \<iota>')}
      \<union> Red_I_q q (\<G>_Fset_q q N)"
    using sat_n_imp[of N] by blast
  interpret q_calc: calculus Bot_F Inf_F "entails_\<G>_q q" "Red_I_\<G>_q q" "Red_F_\<G>_q q"
    using all_red_crit[rule_format, OF q_in] .
  have n_q_sat: "q_calc.saturated N"
    using q_in sat_int_to_sat_q sat_n by simp
  interpret lifted_q_calc:
    tiebreaker_lifting Bot_F Inf_F Bot_G "entails_q q" "Inf_G_q q" "Red_I_q q"
      "Red_F_q q" "\<G>_F_q q" "\<G>_I_q q"
    using q_in by (simp add: standard_lifting_family)
  have n_lift_sat: "lifted_q_calc.calc.saturated N"
    using n_q_sat unfolding Red_I_\<G>_q_def lifted_q_calc.Red_I_\<G>_def
      lifted_q_calc.saturated_def q_calc.saturated_def by auto
  have ground_sat_n: "lifted_q_calc.ground.saturated (\<G>_Fset_q q N)"
    by (rule lifted_q_calc.sat_imp_ground_sat[OF n_lift_sat])
      (use n_lift_sat inf_subs ground.Inf_from_q_def in auto)
  have ground_n_entails_bot: "entails_\<G>_q q N {B}"
    using q_in entails_bot unfolding entails_\<G>_def by simp
  interpret statically_complete_calculus Bot_G "Inf_G_q q" "entails_q q" "Red_I_q q"
    "Red_F_q q"
    using stat_ref_G[rule_format, OF q_in] .
  obtain BG where bg_in: "BG \<in> \<G>_F_q q B"
    using lifted_q_calc.Bot_map_not_empty[OF b_in] by blast
  then have "BG \<in> Bot_G" using lifted_q_calc.Bot_map[OF b_in] by blast
  then have "\<exists>BG'\<in>Bot_G. BG' \<in> \<G>_Fset_q q N"
    using ground_sat_n ground_n_entails_bot statically_complete[of BG, OF _ ground_sat_n]
      bg_in lifted_q_calc.ground.entail_set_all_formulas[of "\<G>_Fset_q q N" "\<G>_Fset_q q {B}"]
    by simp
  then show "\<exists>B'\<in> Bot_F. B' \<in> N" using lifted_q_calc.Bot_cond by blast
qed

(* lem:intersect-saturation-indep-of-sqsubset *)
lemma sat_eq_sat_empty_order: "saturated N = empty_ord.saturated N"
  by (rule refl)

(* lem:intersect-static-ref-compl-indep-of-sqsubset *)
lemma static_empty_ord_inter_equiv_static_inter:
  "statically_complete_calculus Bot_F Inf_F entails Red_I Red_F =
  statically_complete_calculus Bot_F Inf_F entails Red_I Red_F_\<G>_empty"
  unfolding statically_complete_calculus_def
  by (simp add: empty_ord.calculus_axioms calculus_axioms)

(* thm:intersect-static-ref-compl-is-dyn-ref-compl-with-order *)
theorem stat_eq_dyn_ref_comp_fam_inter: "statically_complete_calculus Bot_F Inf_F
    entails Red_I Red_F_\<G>_empty =
  dynamically_complete_calculus Bot_F Inf_F entails Red_I Red_F"
  using dyn_equiv_stat static_empty_ord_inter_equiv_static_inter
  by blast

end

end
