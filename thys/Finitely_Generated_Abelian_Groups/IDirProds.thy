(*
    File:     IDirProds.thy
    Author:   Joseph Thommes, TU München
*)
section \<open>Internal direct product\<close>

theory IDirProds
  imports Generated_Groups_Extend General_Auxiliary
begin

subsection \<open>Complementarity\<close>

text \<open>We introduce the notion of complementarity, that plays a central role in the internal
direct group product and prove some basic properties about it.\<close>

definition (in group) complementary :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "complementary H1 H2 \<longleftrightarrow> H1 \<inter> H2 = {\<one>}"

lemma (in group) complementary_symm: "complementary A B \<longleftrightarrow> complementary B A"
  unfolding complementary_def by blast

lemma (in group) subgroup_carrier_complementary:
  assumes "complementary H J" "subgroup I (G\<lparr>carrier := H\<rparr>)" "subgroup K (G\<lparr>carrier := J\<rparr>)"
  shows "complementary I K"
proof -
  have "\<one> \<in> I"  "\<one> \<in> K" using subgroup.one_closed assms by fastforce+
  moreover have "I \<inter> K \<subseteq> H \<inter> J" using subgroup.subset assms by force
  ultimately show ?thesis using assms unfolding complementary_def by blast
qed

lemma (in group) subgroup_subset_complementary:
  assumes "subgroup H G" "subgroup J G" "subgroup I G"
  and "I \<subseteq> J" "complementary H J"
shows "complementary H I"
  by (intro subgroup_carrier_complementary[OF assms(5), of H I] subgroup_incl, use assms in auto)

lemma (in group) complementary_subgroup_iff:
  assumes "subgroup H G"
  shows "complementary A B \<longleftrightarrow> group.complementary (G\<lparr>carrier := H\<rparr>) A B"
proof -
  interpret H: group "G\<lparr>carrier := H\<rparr>" using subgroup.subgroup_is_group assms by blast
  have "\<one>\<^bsub>G\<^esub> = \<one>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub>" by simp
  then show ?thesis unfolding complementary_def H.complementary_def by simp
qed

lemma (in group) subgroups_card_coprime_imp_compl:
  assumes "subgroup H G" "subgroup J G" "coprime (card H) (card J)"
  shows "complementary H J" unfolding complementary_def
proof -
  interpret JH: subgroup "(H \<inter> J)" G using assms subgroups_Inter_pair by blast
  from subgroups_card_coprime_inter_card_one[OF assms] show "H \<inter> J = {\<one>}" using JH.one_closed
    by (metis card_1_singletonE singletonD)
qed

lemma (in group) prime_power_complementary_groups:
  assumes "Factorial_Ring.prime p" "Factorial_Ring.prime q" "p \<noteq> q"
  and "subgroup P G" "card P = p ^ x"
  and "subgroup Q G" "card Q = q ^ y"
  shows "complementary P Q"
proof -
  from assms have "coprime (card P) (card Q)"
    by (metis coprime_power_right_iff primes_coprime coprime_def)
  then show ?thesis using subgroups_card_coprime_imp_compl assms complementary_def by blast
qed

text \<open>With the previous work from the theory about set multiplication we can characterize
complementarity of two subgroups in abelian groups by the cardinality of their product.\<close>

lemma (in comm_group) compl_imp_diff_cosets:
  assumes "subgroup H G" "subgroup J G" "finite H" "finite J"
  and "complementary H J"
  shows "\<And>a b. \<lbrakk>a \<in> J; b \<in> J; a \<noteq> b\<rbrakk> \<Longrightarrow> (H #> a) \<noteq> (H #> b)"
proof (rule ccontr; safe)
  fix a b
  assume ab: "a \<in> J" "b \<in> J" "a \<noteq> b"
  then have [simp]: "a \<in> carrier G" "b \<in> carrier G" using assms subgroup.subset by auto
  assume "H #> a = H #> b"
  then have "a \<otimes> inv b \<in> H" using assms(1, 2) ab
    by (metis comm_group_axioms comm_group_def rcos_self
              subgroup.mem_carrier subgroup.rcos_module_imp)
  moreover have "a \<otimes> inv b \<in> J"
    by (rule subgroup.m_closed[OF assms(2) ab(1) subgroup.m_inv_closed[OF assms(2) ab(2)]])
  moreover have "a \<otimes> inv b \<noteq> \<one>" using ab inv_equality by fastforce
  ultimately have "H \<inter> J \<noteq> {\<one>}" by blast
  thus False using assms(5) unfolding complementary_def by blast
qed

lemma (in comm_group) finite_sub_card_eq_mult_imp_comp:
  assumes "subgroup H G" "subgroup J G" "finite H" "finite J"
  and "card (H <#> J) = (card J * card H)"
  shows "complementary H J"
  unfolding complementary_def
proof (rule ccontr)
  assume "H \<inter> J \<noteq> {\<one>}"
  have "\<one> \<in> H" using subgroup.one_closed assms(1) by blast
  moreover have "\<one> \<in> J" using subgroup.one_closed assms(2) by blast
  ultimately have "\<one> \<in> (H \<inter> J)" by blast

  then obtain a where a_def: "a \<in> (H \<inter> J) \<and> a \<noteq> \<one>" using \<open>H \<inter> J \<noteq> {\<one>}\<close> by blast
  then have aH: "a \<in> H" by blast
  then have a_inv_H: "inv a \<in> H \<and> inv a \<noteq> \<one>" using assms(1)
    by (meson a_def inv_eq_1_iff subgroup.mem_carrier subgroupE(3))
  from a_def have aJ: "a \<in> J" by blast
  then have a_inv_J: "inv a \<in> J \<and> inv a \<noteq> \<one>" using assms(2)
    by (meson a_def inv_eq_1_iff subgroup.mem_carrier subgroupE(3))
  from a_def have a_c: "a \<in> carrier G" using subgroup.subset[of J G] assms(2) by blast

  from set_mult_card_eq_impl_empty_inter'[of H J]
  have empty: "\<And>a b. \<lbrakk>a \<in> H; b \<in> H; a \<noteq> b\<rbrakk> \<Longrightarrow> (l_coset G a J) \<inter> (l_coset G b J) = {}"
    using assms subgroup.subset[of _ G] by simp

  have "\<one> \<in> \<one> <# J" using \<open>\<one> \<in> J\<close> unfolding l_coset_def by force
  moreover have "\<one> \<in> a <# J" using a_inv_J aJ a_c assms \<open>\<one> \<in> J\<close> coset_join3 by blast
  ultimately have "(l_coset G \<one> J) \<inter> (l_coset G a J) \<noteq> {}" by blast

  then show "False" using empty[of "\<one>" a] a_def aH \<open>\<one> \<in> H\<close> by blast
qed

lemma (in comm_group) finite_sub_comp_imp_card_eq_mult:
  assumes "subgroup H G" "subgroup J G" "finite H" "finite J"
  and "complementary H J"
shows "card (H <#> J) = card J * card H"
proof -
  have carr: "H \<subseteq> carrier G" "J \<subseteq> carrier G" using assms subgroup.subset by auto

  from coset_neq_imp_empty_inter[OF assms(1)] compl_imp_diff_cosets[OF assms(1,2)]
  have em_inter: "\<And>a b. \<lbrakk>a \<in> J; b \<in> J; a \<noteq> b\<rbrakk> \<Longrightarrow> (H #> a) \<inter> (H #> b) = {}"
    by (meson assms subgroup.mem_carrier)

  have "card (\<Union>a\<in>J. (H #> a)) = card J * card H" using assms(4) carr(2) em_inter
  proof (induction J rule: finite_induct)
    case empty
    then show ?case by auto
  next
    case i: (insert x F)
    then have cF:"card (\<Union> ((#>) H ` F)) = card F * card H" by blast
    have xc[simp]: "x \<in> carrier G" using i(4) by simp
    let ?J = "insert x F"
    from i(2, 4, 5) have em:"(H #> x) \<inter> (\<Union>y\<in>F. (H #> y)) = {}" by auto
    have "finite (H #> x)"
      by (meson carr(1) rcosetsI rcosets_finite assms(3) xc)
    moreover have "finite (H <#> F)" using set_mult_finite[OF assms(3) i(1) carr(1)] i(4) by blast
    moreover have "H <#> F = (\<Union>a\<in>F. (H #> a))"
      unfolding set_mult_def using r_coset_def[of G H] by auto
    ultimately have "card(H #> x) + card(\<Union>y\<in>F. (H #> y))
                   = card((H #> x) \<union> (\<Union>y\<in>F. (H #> y))) + card((H #> x) \<inter> (\<Union>y\<in>F. (H #> y)))"
      using card_Un_Int by auto
    then have "card(H #> x) + card(\<Union>y\<in>F. (H #> y)) = card((H #> x) \<union> (\<Union>y\<in>F. (H #> y)))"
      using i(5) em by simp
    moreover have "card (H #> x) = card H"
      using card_rcosets_equal[of _ H] rcosetsI[of H] carr(1) xc by metis
    moreover have "card (insert x F) * card H = card F * card H + card H"
      by (simp add: i)
    ultimately show ?case using cF by simp
  qed
  moreover have "H <#> J = (\<Union>a\<in>J. (H #> a))"
    unfolding set_mult_def using r_coset_def[of G H] by auto
  ultimately show "card (H <#> J) = card J * card H" by argo
qed

lemma (in comm_group) finite_sub_comp_iff_card_eq_mult:
  assumes "subgroup H G" "subgroup J G" "finite H" "finite J"
  shows "card (H <#> J) = card J * card H  \<longleftrightarrow> complementary H J"
  using finite_sub_comp_imp_card_eq_mult[OF assms] finite_sub_card_eq_mult_imp_comp[OF assms]
  by blast

subsection \<open>\<open>IDirProd\<close> - binary internal direct product\<close>

text \<open>We introduce the internal direct product formed by two subgroups (so in its binary form).\<close>

definition IDirProd :: "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "IDirProd G Y Z = generate G (Y \<union> Z)"

text \<open>Some trivial lemmas about the binary internal direct product.\<close>

lemma (in group) IDirProd_comm:
  "IDirProd G A B = IDirProd G B A"
  unfolding IDirProd_def by (simp add: sup_commute)

lemma (in group) IDirProd_empty_right:
  assumes "A \<subseteq> carrier G"
  shows "IDirProd G A {} = generate G A"
  unfolding IDirProd_def by simp

lemma (in group) IDirProd_empty_left:
  assumes "A \<subseteq> carrier G"
  shows "IDirProd G {} A = generate G A"
  unfolding IDirProd_def by simp

lemma (in group) IDirProd_one_right:
  assumes "A \<subseteq> carrier G"
  shows "IDirProd G A {\<one>} = generate G A"
  unfolding IDirProd_def
proof
  interpret sA: subgroup "(generate G A)" G using assms generate_is_subgroup by simp
  interpret sAone: subgroup "(generate G (A \<union> {\<one>}))" G using assms generate_is_subgroup by simp
  show "generate G (A \<union> {\<one>}) \<subseteq> generate G A"
    using generate_subgroup_incl[of "A \<union> {\<one>}" "generate G A"]
          generate.incl assms sA.one_closed sA.subgroup_axioms by fast
  show "generate G A \<subseteq> generate G (A \<union> {\<one>})"
    using mono_generate[of A "A \<union> {\<one>}"] by blast
qed

lemma (in group) IDirProd_one_left:
  assumes "A \<subseteq> carrier G"
  shows "IDirProd G {\<one>} A = generate G A"
  using IDirProd_one_right[of A] assms unfolding IDirProd_def by force

lemma (in group) IDirProd_is_subgroup:
  assumes "Y \<subseteq> carrier G" "Z \<subseteq> carrier G"
  shows "subgroup (IDirProd G Y Z) G"
  unfolding IDirProd_def using generate_is_subgroup[of "Y \<union> Z"] assms by simp


text \<open>Using the theory about set multiplication we can also show the connection of the underlying
set in the internal direct product with the set multiplication in the case of an abelian group.
Together with the facts about complementarity and the set multiplication we can characterize
complementarity by the cardinality of the internal direct product and vice versa.\<close>

lemma (in comm_group) IDirProd_eq_subgroup_mult:
  assumes "subgroup H G" "subgroup J G"
  shows "IDirProd G H J = H <#> J"
  unfolding IDirProd_def
  by (rule set_mult_eq_generate_subgroup[OF assms])

lemma (in comm_group) finite_sub_comp_iff_card_eq_IDirProd:
  assumes "subgroup H G" "subgroup J G" "finite H" "finite J"
  shows "card (IDirProd G H J) = card J * card H  \<longleftrightarrow> complementary H J"
  using finite_sub_comp_iff_card_eq_mult IDirProd_eq_subgroup_mult assms by presburger

subsection \<open>\<open>IDirProds\<close> - indexed internal direct product\<close>

text \<open>The indexed version of the internal direct product acting on a family of subgroups.\<close>

definition IDirProds :: "('a, 'b) monoid_scheme \<Rightarrow> ('c \<Rightarrow> 'a set) \<Rightarrow> 'c set \<Rightarrow> 'a set" where
  "IDirProds G S I = generate G (\<Union>(S ` I))"

text \<open>Lemmas about the indexed internal direct product.\<close>

lemma (in group) IDirProds_incl:
  assumes "i \<in> I"
  shows "S i \<subseteq> IDirProds G S I"
  unfolding IDirProds_def using assms generate.incl[of _ "\<Union>(S ` I)" G] by blast

lemma (in group) IDirProds_empty:
  "IDirProds G S {} = {\<one>}"
  unfolding IDirProds_def using generate_empty by simp

lemma (in group) IDirProds_is_subgroup:
  assumes "\<Union>(S ` I) \<subseteq> (carrier G)"
  shows "subgroup (IDirProds G S I) G"
  unfolding IDirProds_def using generate_is_subgroup[of "\<Union>(S ` I)"] assms by auto

lemma (in group) IDirProds_subgroup_id: "subgroup (S i) G \<Longrightarrow> IDirProds G S {i} = S i"
  by (simp add: generate_subgroup_id IDirProds_def)

lemma (in comm_group) IDirProds_Un:
  assumes "\<forall>i\<in>A. subgroup (S i) G" "\<forall>j\<in>B. subgroup (S j) G"
  shows   "IDirProds G S (A \<union> B) = IDirProds G S A <#> IDirProds G S B"
proof -
  have subset: "\<Union> (S ` A) \<subseteq> carrier G" "\<Union> (S ` B) \<subseteq> carrier G"
    using subgroup.subset assms(1, 2) by blast+
  have "IDirProds G S A <#> IDirProds G S B = IDirProd G (IDirProds G S A) (IDirProds G S B)"
    using assms by (intro IDirProd_eq_subgroup_mult [symmetric] IDirProds_is_subgroup subset)
  also have "\<dots> = generate G (\<Union> (S ` A) \<union> IDirProds G S B)"
    unfolding IDirProds_def IDirProd_def by (intro generate_idem' generate_incl subset)
  also have "\<dots> = generate G (\<Union>(S ` A) \<union> \<Union>(S ` B))"
    unfolding IDirProds_def IDirProd_def
    by (intro generate_idem'_right generate_incl subset)
  also have "\<Union>(S ` A) \<union> \<Union>(S ` B) = \<Union>(S ` (A \<union> B))"
    by blast
  also have "generate G \<dots> = IDirProds G S (A \<union> B)"
    unfolding IDirProds_def ..
  finally show ?thesis ..
qed

lemma (in comm_group) IDirProds_finite:
  assumes "finite I" "\<forall>i\<in>I. subgroup (S i) G" "\<forall>i\<in>I. finite (S i)"
  shows "finite (IDirProds G S I)" using assms
proof (induction I rule: finite_induct)
  case empty
  thus ?case using IDirProds_empty[of S] by simp
next
  case i: (insert x I)
  interpret Sx: subgroup "S x" G using i by blast
  have cx: "(S x) \<subseteq> carrier G" by force
  have cI: "\<Union>(S ` I) \<subseteq> carrier G" using i subgroup.subset by blast
  interpret subgroup "IDirProds G S I" G using IDirProds_is_subgroup[OF cI] .
  have cIP: "(IDirProds G S I) \<subseteq> carrier G" by force
  from i have f: "finite (S x)" "finite (IDirProds G S I)" "finite {x}" by blast+
  from IDirProds_Un[of "{x}" S I]
  have "IDirProds G S ({x} \<union> I) = IDirProds G S {x} <#> IDirProds G S I" using i by blast
  also have "\<dots> = S x <#> IDirProds G S I"
    using IDirProds_subgroup_id[of S x] Sx.subgroup_axioms by force
  also have "finite (\<dots>)" using set_mult_finite[OF f(1, 2) cx cIP] .
  finally show ?case unfolding insert_def by simp
qed

lemma (in comm_group) IDirProds_compl_imp_compl:
  assumes "\<forall>i \<in> I. subgroup (S i) G" and "subgroup H G"
  assumes "complementary H (IDirProds G S I)" "i \<in> I"
  shows   "complementary H (S i)"
proof -
  have "S i \<subseteq> IDirProds G S I" using assms IDirProds_incl by fast
  then have "H \<inter> (S i) \<subseteq> H \<inter> IDirProds G S I" by blast
  moreover have "\<one> \<in> H \<inter> (S i)" using subgroup.one_closed assms by auto
  ultimately show "complementary H (S i)" using assms(3) unfolding complementary_def by blast
qed

text \<open>Using the knowledge about the binary internal direct product, we can - in case that all
subgroups in the family have coprime orders - also derive the cardinality of the indexed internal
direct product.\<close>

lemma (in comm_group) IDirProds_card:
  assumes "finite I" "\<forall>i\<in>I. subgroup (S i) G"
          "\<forall>i\<in>I. finite (S i)" "pairwise (\<lambda>x y. coprime (card (S x)) (card (S y))) I"
  shows "card (IDirProds G S I) = (\<Prod>i \<in> I. card (S i))" using assms
proof (induction I rule: finite_induct)
  case empty
  then show ?case using IDirProds_empty[of S] by simp
next
  case i: (insert x I)
  have sx: "subgroup (S x) G" using i(4) by blast
  have cx: "(S x) \<subseteq> carrier G" using subgroup.subset[OF sx] .
  have fx: "finite (S x)" using i by blast
  have cI: "\<Union>(S ` I) \<subseteq> carrier G" using subgroup.subset[of _ G] i(4) by blast
  from generate_is_subgroup[OF this] have sIP: "subgroup (IDirProds G S I) G"
    unfolding IDirProds_def .
  then have cIP: "(IDirProds G S I) \<subseteq> carrier G" using subgroup.subset by blast
  have fIP: "finite (IDirProds G S I)" using IDirProds_finite[OF i(1)] i by blast

  from i have ih: "card (IDirProds G S I) = (\<Prod>i\<in>I. card (S i))" unfolding pairwise_def by blast
  hence cop: "coprime (card (IDirProds G S I)) (card (S x))"
  proof -
    have cFI0: "card (IDirProds G S I) \<noteq> 0" using finite_subgroup_card_neq_0[OF sIP fIP] .
    moreover have cx0: "card (S x) \<noteq> 0" using finite_subgroup_card_neq_0[OF sx fx] .
    moreover have  "prime_factors (card (IDirProds G S I)) \<inter> prime_factors (card (S x)) = {}"
    proof (rule ccontr)
      have n0: "\<And>i. i \<in> I \<Longrightarrow> card (S i) \<noteq> 0" using finite_subgroup_card_neq_0 i(4, 5) by blast
      assume "prime_factors (card (IDirProds G S I)) \<inter> prime_factors (card (S x)) \<noteq> {}"
      moreover have "prime_factors (card (IDirProds G S I)) = \<Union>(prime_factors ` (card \<circ> S) ` I)"
        using n0 prime_factors_Prod[OF i(1), of "card \<circ> S"] by (subst ih; simp)
      moreover have "\<And>i. i \<in> I \<Longrightarrow> prime_factors (card (S i)) \<inter> prime_factors (card (S x)) = {}"
      proof -
        fix i
        assume ind: "i \<in> I"
        then have coPx: "coprime (card (S i)) (card (S x))"
          using i(2, 6) unfolding pairwise_def by auto
        have "card (S i) \<noteq> 0" using n0 ind by blast
        from coprime_eq_empty_prime_inter[OF this cx0]
        show "prime_factors (card (S i)) \<inter> prime_factors (card (S x)) = {}" using coPx by blast
      qed
      ultimately show "False" by auto
    qed
    ultimately show ?thesis using coprime_eq_empty_prime_inter by blast
  qed
  have "card (IDirProds G S (insert x I)) = card (S x) * card (IDirProds G S I)"
  proof -
    from finite_sub_comp_iff_card_eq_IDirProd[OF sIP sx fIP fx]
         subgroups_card_coprime_imp_compl[OF sIP sx cop]
    have "card (IDirProd G (IDirProds G S I) (S x)) = card (S x) * card (IDirProds G S I)" by blast
    moreover have "generate G (\<Union> (S ` insert x I)) = generate G (generate G (\<Union> (S ` I)) \<union> S x)"
      by (simp add: Un_commute cI cx generate_idem'_right)
    ultimately show ?thesis unfolding IDirProds_def IDirProd_def by argo
  qed
  also have "\<dots> = card (S x) * prod (card \<circ> S) I" using ih by simp
  also have "\<dots> = prod (card \<circ> S) ({x} \<union> I)" using i.hyps by auto
  finally show ?case by simp
qed

subsection "Complementary family of subgroups"

text \<open>The notion of a complementary family is introduced. Note that the subgroups are complementary
not only to the other subgroups but to the product of the other subgroups.\<close>

definition (in group) compl_fam :: "('c \<Rightarrow> 'a set) \<Rightarrow> 'c set \<Rightarrow> bool" where
  "compl_fam S I = (\<forall>i \<in> I. complementary (S i) (IDirProds G S (I - {i})))"

text \<open>Some lemmas about \<open>compl_fam\<close>.\<close>

lemma (in group) compl_fam_empty[simp]: "compl_fam S {}"
  unfolding compl_fam_def by simp

lemma (in group) compl_fam_cong:
  assumes "compl_fam (f \<circ> g) A" "inj_on g A"
  shows "compl_fam f (g ` A)"
proof -
  have "((f \<circ> g) ` (A - {i})) =  (f ` (g ` A - {g i}))" if "i \<in> A" for i
    using assms that unfolding inj_on_def comp_def by blast
  thus ?thesis using assms unfolding compl_fam_def IDirProds_def complementary_def by simp
qed

text \<open>We now connect \<open>compl_fam\<close> with \<open>generate\<close> as this will be its main application.\<close>

lemma (in comm_group) compl_fam_imp_generate_inj:
  assumes "gs \<subseteq> carrier G" "compl_fam (\<lambda>g. generate G {g}) gs"
  shows "inj_on (\<lambda>g. generate G {g}) gs"
proof(rule, rule ccontr)
  fix x y
  assume xy: "x \<in> gs" "y \<in> gs" "x \<noteq> y"
  have gen: "generate G (\<Union>g\<in>gs - {y}. generate G {g}) = generate G (gs - {y})"
    by (intro generate_idem_Un, use assms in blast)
  assume g: "generate G {x} = generate G {y}"
  with xy have "generate G {y} \<subseteq> generate G (gs - {y})" using mono_generate[of "{x}" "gs - {y}"] by auto
  with xy have gyo: "generate G {y} = {\<one>}" using assms(2) generate.one gen
    unfolding compl_fam_def complementary_def IDirProds_def by blast
  hence yo: "y = \<one>" using generate_singleton_one by simp
  from gyo g generate_singleton_one have xo: "x = \<one>" by simp
  from xy yo xo show False by blast
qed  

lemma (in comm_group) compl_fam_generate_subset:
  assumes "compl_fam (\<lambda>g. generate G {g}) gs"
          "gs \<subseteq> carrier G" "A \<subseteq> gs"
  shows "compl_fam (\<lambda>g. generate G {g}) A"
proof(unfold compl_fam_def complementary_def IDirProds_def, subst generate_idem_Un)
  show "\<And>i. A - {i} \<subseteq> carrier G" using assms by blast
  have "generate G {i} \<inter> generate G (A - {i}) = {\<one>}" if "i \<in> A" for i
  proof -
    have "\<one> \<in> generate G {i} \<inter> generate G (A - {i})" using generate.one by blast
    moreover have "generate G (A - {i}) \<subseteq> generate G (gs - {i})"
      by (intro mono_generate, use assms in fast)
    moreover have "generate G {i} \<inter> generate G (gs - {i}) = {\<one>}"
      using assms that generate_idem_Un[of "gs - {i}"]
      unfolding compl_fam_def IDirProds_def complementary_def by blast
    ultimately show ?thesis by blast
  qed
  thus "\<forall>i\<in>A. generate G {i} \<inter> generate G (A - {i}) = {\<one>}" by auto
qed

subsection \<open>\<open>is_idirprod\<close>\<close>

text \<open>In order to identify a group as the internal direct product of a family of subgroups, they all
have to be normal subgroups, complementary to the product of the rest of the subgroups and generate
all of the group - this is captured in the definition of \<open>is_idirprod\<close>.\<close>

definition (in group) is_idirprod :: "'a set \<Rightarrow> ('c \<Rightarrow> 'a set) \<Rightarrow> 'c set \<Rightarrow> bool" where
  "is_idirprod A S I = ((\<forall>i \<in> I. S i \<lhd> G) \<and> A = IDirProds G S I \<and> compl_fam S I)"

text \<open>Very basic lemmas about \<open>is_idirprod\<close>.\<close>

lemma (in comm_group) is_idirprod_subgroup_suffices:
  assumes "A = IDirProds G S I" "\<forall>i\<in>I. subgroup (S i) G" "compl_fam S I"
  shows "is_idirprod A S I"
  unfolding is_idirprod_def using assms subgroup_imp_normal by blast

lemma (in comm_group) is_idirprod_generate:
  assumes "A = generate G gs" "gs \<subseteq> carrier G" "compl_fam (\<lambda>g. generate G {g}) gs"
  shows "is_idirprod A (\<lambda>g. generate G {g}) gs"
proof(intro is_idirprod_subgroup_suffices)
  show "A = IDirProds G (\<lambda>g. generate G {g}) gs"
    using assms generate_idem_Un[OF assms(2)] unfolding IDirProds_def by argo
  show "\<forall>i\<in>gs. subgroup (generate G {i}) G" using assms generate_is_subgroup by auto
  show "compl_fam (\<lambda>g. generate G {g}) gs" by fact
qed

lemma (in comm_group) is_idirprod_imp_compl_fam[simp]:
  assumes "is_idirprod A S I"
  shows "compl_fam S I"
  using assms unfolding is_idirprod_def by blast

lemma (in comm_group) is_idirprod_generate_imp_generate[simp]:
  assumes "is_idirprod A (\<lambda>g. generate G {g}) gs"
  shows "A = generate G gs"
proof -
  have "gs \<subseteq> carrier G"
  proof
    show "g \<in> carrier G" if "g \<in> gs" for g
    proof -
      interpret g: subgroup "generate G {g}" G
        using assms that normal_imp_subgroup unfolding is_idirprod_def by blast
      show ?thesis using g.subset generate.incl by fast
    qed
  qed
  thus ?thesis using assms generate_idem_Un unfolding is_idirprod_def IDirProds_def by presburger
qed

end