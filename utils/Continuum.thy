section {* Cardinality of the continuum *}

theory Continuum
  imports 
    cardinals
    Transcendental
    Real_Bit
    Countable_Set_Type
    "Library_extra/Countable_Set_extra"
begin

subsection {* Cardinality $\mathfrak{c}$ *}

text {* This theory introduces definitions and type class that group Isabelle types that have
        cardinality of up to the cardinality of the continuum (i.e. $|\mathbb{R}| = \mathfrak{c}$). We can
        then use the type class to exhibit injections into a universe of types of up to cardinality
        $\mathfrak{c}, which we can then can then be used to introduce deeply encoded types into the UTP model.
        Though restricting ourselves to types of cardinality $\mathfrak{c}$ may seem limiting, this seems
        to be a decently large universe that even for instance includes countable sets of real numbers.

        Countable types in HOL are specified using the @{term countable} predicate, which includes both
        types that are finite, and also countably infinite. Effectively then, the @{term countable} predicate
        characterises types with cardinality up to $\aleph_0$. We will create an analogous constant called
        \emph{continuum} that characterises types up to cardinality $\mathfrak{c}$.
        Since we don't have the continuum hypothesis in HOL, we explicitly require that types of up to cardinality $\mathfrak{c}$ 
        either exhibit an injection into the natural numbers (for types of finite or $\aleph_0$ cardinality)
        or a bijection with the set of natural numbers ($\mathbb{P}\,\mathbb{N}$). With informal justification by 
        the continuum hypothesis there should be no types in between these two possibilities. *}

definition continuum :: "'a set \<Rightarrow> bool" where
"continuum A \<longleftrightarrow> (\<exists> to_nat :: 'a \<Rightarrow> nat. inj_on to_nat A) \<or> (\<exists> to_nat_set :: 'a \<Rightarrow> nat set. bij_betw to_nat_set A UNIV)"

abbreviation "\<N> \<equiv> UNIV :: nat set"
abbreviation "\<P>\<N> \<equiv> UNIV :: nat set set"

text {* The continuum can be equivalently characterised using HOL cardinals as types whose cardinality
        is less than or equal to $\aleph_0$, or else with cardinality equal to $\mathfrak{c}$. *}

lemma continuum_as_card:
  "continuum A \<longleftrightarrow> |A| \<le>o |\<N>| \<or> |A| =o |\<P>\<N>|"
  by (simp add: continuum_def card_of_ordIso[THEN sym] card_of_ordLeq[THEN sym])

text {* We now prove that certain sets are within the continuum; firstly empty sets. *}

lemma continuum_empty [simp]:
  "continuum {}"
  by (simp add: continuum_def)

lemma countable_continuum:
  "countable A \<Longrightarrow> continuum A"
  by (simp add: continuum_def countable_def)

lemma continuum_prod_lemma:
  assumes "A \<noteq> {}" "|A| \<le>o |\<N>|" "|B| =o |\<P>\<N>|"
  shows "|A \<times> B| =o |\<P>\<N>|"
proof -
  have "|A| \<le>o |B|"
  proof -
    have "|\<N>| <o |\<P>\<N>|"
      by (rule card_of_set_type)
    with assms(2) have "|A| <o |\<P>\<N>|"
      using ordIso_ordLess_trans ordLess_lemma ordLess_transitive by blast
    with assms(3)[THEN ordIso_symmetric] have "|A| <o |B|"
      using ordLess_ordIso_trans by blast
    thus ?thesis
      using ordLess_imp_ordLeq by blast
  qed
  moreover from assms(3) have "infinite B"
    using Finite_Set.finite_set card_of_ordIso_finite by blast
  ultimately have "|A \<times> B| =o |B|"
    using assms(1) card_of_Times_infinite
      by (auto)
  with assms(3) show ?thesis
    using ordIso_transitive by (blast)
qed

text {* The product of two types, both of whose cardinality is up to $\mathfrak{c}$, is again $\mathfrak{c}$ *}

lemma continuum_prod:
  assumes "continuum A" "continuum B"
  shows "continuum (A \<times> B)"
proof (cases "A = {} \<or> B = {}")
  case True
  thus ?thesis by (auto)
next
  case False
  hence nemp: "A \<noteq> {}" "B \<noteq> {}"
    by (auto)

  with nemp have "|A| \<le>o |\<N>| \<Longrightarrow> |B| =o |\<P>\<N>| \<Longrightarrow> |A \<times> B| =o |\<P>\<N>|"
    by (auto intro: continuum_prod_lemma)

  moreover have "|A| =o |\<P>\<N>| \<Longrightarrow> |B| \<le>o |\<N>| \<Longrightarrow> |A \<times> B| =o |\<P>\<N>|"
  proof -
    assume as: "|A| =o |\<P>\<N>|" "|B| \<le>o |\<N>|"
    have "|A \<times> B| =o |B \<times> A|"
      using card_of_Times_commute by fastforce
    with as show ?thesis
      using nemp continuum_prod_lemma[of B A] ordIso_transitive
      by (auto)
  qed

  moreover have "|A| =o |\<P>\<N>| \<Longrightarrow> |B| =o |\<P>\<N>| \<Longrightarrow> |A \<times> B| =o |\<P>\<N>|"
  proof -
    assume as: "|A| =o |\<P>\<N>|" "|B| =o |\<P>\<N>|"
    have "|\<P>\<N> \<times> \<P>\<N>| =o |\<P>\<N>|"
      using card_of_Times_same_infinite
      by force
    moreover from as have "|A \<times> B| =o |\<P>\<N> \<times> \<P>\<N>|"
      by (rule card_of_Times_cong)
    ultimately show ?thesis
      using ordIso_transitive by blast
  qed
    
  ultimately show ?thesis using assms
    apply (simp add: continuum_as_card)
    apply (erule disjE; erule disjE)
    apply (blast intro: card_of_Times_ordLeq_infinite)
    apply (rule disjI2)
    apply (simp_all)
  done
qed

text {* A countable set over a type of cardinality up to $\mathfrak{c}$ has cardinality up to $\mathfrak{c}$. *}

lemma continuum_csets:
  assumes "continuum A"
  shows "continuum (csets A)"
proof (cases "countable A")
  case True note count = this
  thus ?thesis
  proof (cases "finite A")
    case True
    hence "finite (csets A)"
      by (simp add: csets_def)
    thus ?thesis
      using countable_continuum uncountable_infinite by blast
  next
    case False
    with count obtain to_nat where "bij_betw to_nat A \<N>"
      by blast
    moreover hence "bij_betw (\<lambda> B. to_nat ` B) (Pow A) \<P>\<N>"
      using bij_betw_image_Pow by force
    moreover have "rcset ` csets A \<subseteq> Pow A"
      by (auto simp add: csets_def)
    ultimately have "bij_betw (\<lambda> B. to_nat ` B) (rcset ` csets A) \<P>\<N>"
      by (metis (no_types, lifting) Collect_mono Pow_def count countable_subset csets.rep_eq subset_antisym)
    moreover have "bij_betw rcset (csets A) (rcset ` csets A)"
      by (auto intro: bij_betwI' simp add: rcset_inject)
    ultimately have "bij_betw ((\<lambda> B. to_nat ` B) \<circ> rcset) (csets A) \<P>\<N>"
      by (simp add: bij_betw_def comp_inj_on image_comp)
    thus ?thesis
      by (auto simp add: continuum_def)
  qed
next
  case False
  then obtain to_nat_set :: "'a \<Rightarrow> nat set" where "bij_betw to_nat_set A \<P>\<N>"
    using assms continuum_def countableI by blast
  hence "bij_betw (\<lambda> B. to_nat_set `\<^sub>c B) (csets A) UNIV"
    by (metis bij_betw_image_csets csets_UNIV)
    thm bij_betw_trans
  hence "bij_betw (nat_set_cset_bij \<circ> (\<lambda> B. to_nat_set `\<^sub>c B)) (csets A) \<P>\<N>"
    using bij_betw_trans bij_nat_set_cset_bij by blast
  thus ?thesis
    by (auto simp add: continuum_def)
qed

subsection {* Continuum class *}

class continuum =
  assumes ex_continuum_inj: "(\<exists> to_nat :: 'a \<Rightarrow> nat. inj to_nat) \<or> (\<exists> to_nat_set :: 'a \<Rightarrow> nat set. bij to_nat_set)"
begin
  lemma continuum: "continuum (UNIV :: 'a set)"
    by (simp add: continuum_def ex_continuum_inj)
end

lemma uncountable_continuum:
  "uncountable (UNIV :: 'a::continuum set) \<Longrightarrow> (\<exists> to_nat_set :: 'a \<Rightarrow> nat set. bij to_nat_set)"
  using countableI ex_continuum_inj by blast

definition to_nat_set :: "'a\<Colon>continuum \<Rightarrow> nat set" where
  "to_nat_set = (if (countable (UNIV::'a set)) then (SOME f. inj f) else (SOME f. bij f))"

definition from_nat_set :: "nat set \<Rightarrow> 'a\<Colon>continuum" where
  "from_nat_set = inv (to_nat_set \<Colon> 'a \<Rightarrow> nat set)"

lemma to_nat_set_inj [simp]: "inj to_nat_set"
proof (cases "countable (UNIV :: 'a set)")
  case False
  then obtain to_nat_set :: "'a \<Rightarrow> nat set" where "bij to_nat_set"
    using uncountable_continuum by auto
  thus ?thesis
    by (simp add: to_nat_set_def, metis bij_betw_imp_inj_on someI_ex)
next
  case True
  hence "(\<exists> to_nat :: 'a \<Rightarrow> nat. inj to_nat)"
    using ex_continuum_inj by blast
  then obtain to_nat :: "'a \<Rightarrow> nat" where "inj to_nat"
    by auto
  hence "inj (\<lambda> x. {to_nat x})"
    by (meson injD injI singleton_inject)
  thus ?thesis using True
    by (auto simp add: to_nat_set_def, metis someI_ex)
qed

lemma to_nat_set_bij:
  assumes "uncountable (UNIV :: 'a::continuum set)"
  shows "bij (to_nat_set :: 'a \<Rightarrow> nat set)"
proof - 
  obtain to_nat_set :: "'a \<Rightarrow> nat set" where "bij to_nat_set"
    using assms uncountable_continuum by blast
  thus ?thesis
    by (auto simp add: to_nat_set_def assms, metis someI_ex)
qed

lemma inj_on_to_nat_set[simp, intro]: "inj_on to_nat_set S"
  using to_nat_set_inj by (auto simp: inj_on_def)

lemma surj_from_nat_set [simp]: "surj from_nat_set"
  unfolding from_nat_set_def by (simp add: inj_imp_surj_inv)

lemma to_nat_set_split [simp]: "to_nat_set x = to_nat_set y \<longleftrightarrow> x = y"
  using injD [OF to_nat_set_inj] by auto

lemma from_nat_set_to_nat_set [simp]:
  "from_nat_set (to_nat_set x) = x"
  by (simp add: from_nat_set_def)

text {* Every countable type is within the continuum *}

instance countable \<subseteq> continuum
  by (intro_classes, simp add: countable_infinite_type_inj_ex)

text {* We construct bijective versions of {@const to_nat_set} and {@const from_nat_set} *}

definition to_nat_set_bij :: "'a::{continuum, infinite} \<Rightarrow> nat set" where
"to_nat_set_bij = (SOME f. bij f)"

lemma to_nat_bij:
  "bij to_nat_set_bij"
  apply (auto simp add: bij_def)
  oops

definition from_nat_bij :: "nat \<Rightarrow> 'a::{countable, infinite}" where
"from_nat_bij = inv to_nat_bij"

text {* The real numbers are in the continuum -- this requires a proof that $|\mathbb{P}\,\mathbb{N}| = |\mathbb{R}|$ 
 that we have proved elsewhere. *}

instance real :: continuum
  using real_nats_bij by (intro_classes, blast)

text {* Any set over a countable type is within the continuum *}

instance set :: (countable) continuum
proof
  show "(\<exists>to_nat :: 'a set \<Rightarrow> nat. inj to_nat) \<or> (\<exists>to_nat_set :: 'a set \<Rightarrow> nat set. bij to_nat_set)"
  proof (cases "finite (UNIV :: 'a set)")
    case True
    hence "countable (UNIV :: 'a set set)"
      by (simp add: Finite_Set.finite_set countable_finite)
    then obtain to_nat :: "'a set \<Rightarrow> nat" where "inj to_nat"
      by auto
    thus ?thesis
      by (auto)
  next
    case False
    then obtain to_nat :: "'a \<Rightarrow> nat" where bij_to_nat: "bij to_nat"
      using to_nat_on_infinite[of "UNIV :: 'a set"] by auto
          
    let ?f = "(\<lambda> A. to_nat ` A) :: 'a set \<Rightarrow> nat set"
      
    from bij_to_nat have "bij ?f"
    proof -
      have "inj ?f"
        by (meson bij_betw_imp_inj_on bij_to_nat injI inj_image_eq_iff)
      moreover have "surj ?f"
      proof (clarsimp simp add: surj_def)
        fix y :: "nat set"
        have "y = to_nat ` inv to_nat ` y"
          by (simp add: bij_is_surj bij_to_nat image_surj_f_inv_f)            
        thus "\<exists>x\<Colon>'a set. y = to_nat ` x"
          by (auto)
      qed
      ultimately show ?thesis
        by (simp add: bij_betw_def)
    qed
    thus ?thesis
      by (auto)
  qed
qed

text {* A product of two continuum types is within the continuum *}

instance prod :: (continuum, continuum) continuum
proof
  have "continuum (UNIV :: 'a set)" "continuum (UNIV :: 'b set)"
    by (simp_all add: continuum)
  hence "continuum ((UNIV :: 'a set) \<times> (UNIV :: 'b set))"
    by (rule continuum_prod)
  hence "continuum (UNIV :: ('a \<times> 'b) set)"
    by simp
  thus "(\<exists>to_nat :: ('a\<times>'b) \<Rightarrow> nat. inj to_nat) \<or> (\<exists>to_nat_set :: ('a\<times>'b) \<Rightarrow> nat set. bij to_nat_set)"
    by (simp add: continuum_def)
qed

text {* A countable set over a continuum type is within the continuum *}

instance cset :: (continuum) continuum
proof
  have "continuum (UNIV :: 'a cset set)"
    by (metis continuum continuum_csets csets_UNIV)
  thus "(\<exists>to_nat :: 'a cset \<Rightarrow> nat. inj to_nat) \<or> (\<exists>to_nat_set :: 'a cset \<Rightarrow> nat set. bij to_nat_set)"
    by (simp add: continuum_def)
qed

end