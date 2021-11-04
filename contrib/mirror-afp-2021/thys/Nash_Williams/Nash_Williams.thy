section \<open>The Nash-Williams Theorem\<close>

text \<open>Following S. Todorčević, \emph{Introduction to Ramsey Spaces}, 
Princeton University Press (2010), 11--12.\<close>

theory Nash_Williams
  imports Nash_Extras 
begin

lemma finite_nat_Int_greaterThan_iff:
  fixes N :: "nat set"
  shows "finite (N \<inter> {n<..}) \<longleftrightarrow> finite N"
  apply (simp add: finite_nat_iff_bounded subset_iff)
  by (metis dual_order.strict_trans2 nat_less_le not_less_eq)

subsection \<open>Initial segments\<close>

definition init_segment :: "nat set \<Rightarrow> nat set \<Rightarrow> bool"
  where "init_segment S T \<equiv> \<exists>S'. T = S \<union> S' \<and> S \<lless> S'"

lemma init_segment_subset: "init_segment S T \<Longrightarrow> S \<subseteq> T"
  by (auto simp: init_segment_def)

lemma init_segment_refl: "init_segment S S"
  by (metis empty_iff init_segment_def less_sets_def sup_bot.right_neutral)

lemma init_segment_antisym: "\<lbrakk>init_segment S T; init_segment T S\<rbrakk> \<Longrightarrow> S=T"
  by (auto simp: init_segment_def)

lemma init_segment_trans: "\<lbrakk>init_segment S T; init_segment T U\<rbrakk> \<Longrightarrow> init_segment S U"
  unfolding init_segment_def
  by (meson UnE Un_assoc Un_upper1 less_sets_def less_sets_weaken1)

lemma init_segment_empty2 [iff]: "init_segment S {} \<longleftrightarrow> S={}"
  by (auto simp: init_segment_def less_sets_def)

lemma init_segment_Un: "S \<lless> S' \<Longrightarrow> init_segment S (S \<union> S')"
  by (auto simp: init_segment_def less_sets_def)

lemma init_segment_iff:
  shows "init_segment S T \<longleftrightarrow> S=T \<or> (\<exists>m \<in> T. S = {n \<in> T. n < m})" (is "?lhs=?rhs")
proof
  assume ?lhs
  then obtain S' where S': "T = S \<union> S'" "S \<lless> S'"
    by (meson init_segment_def)
  then have "S \<subseteq> T"
    by auto
  then have eq: "S' = T-S"
    using S' by (auto simp: less_sets_def)
  show ?rhs
  proof (cases "T \<subseteq> S")
    case True
    with \<open>S \<subseteq> T\<close> show ?rhs by blast
  next
    case False
    then have "Inf S' \<in> T"
      by (metis Diff_eq_empty_iff Diff_iff Inf_nat_def1 eq)
    moreover have "\<And>x. x \<in> S \<Longrightarrow> x < Inf S'"
      using S' False by (auto simp: less_sets_def intro!: Inf_nat_def1)
    moreover have "{n \<in> T. n < Inf S'} \<subseteq> S"
      using Inf_nat_def eq not_less_Least by fastforce
    ultimately show ?rhs
      using \<open>S \<subseteq> T\<close> by blast
  qed
next
  assume ?rhs
  then show ?lhs
  proof (elim disjE bexE)
    assume "S = T"
    then show "init_segment S T"
      using init_segment_refl by blast
  next
    fix m
    assume m: "m \<in> T" "S = {n \<in> T. n < m}"
    then have "T = S \<union> {n \<in> T. m \<le> n}"
      by auto
    moreover have "S \<lless> {n \<in> T. m \<le> n}"
      using m by (auto simp: less_sets_def)
    ultimately show "init_segment S T"
      using init_segment_Un by force
  qed
qed

lemma init_segment_empty [iff]: "init_segment {} S"
  by (auto simp: init_segment_def less_sets_def)

lemma init_segment_insert_iff:
  assumes Sn: "S \<lless> {n}" and TS: "\<And>x. x \<in> T-S \<Longrightarrow> n\<le>x"
  shows "init_segment (insert n S) T \<longleftrightarrow> init_segment S T \<and> n \<in> T"
proof 
  assume "init_segment (insert n S) T"
  then have "init_segment ({n} \<union> S) T"
    by auto
  then show "init_segment S T \<and> n \<in> T"
    by (metis Sn Un_iff init_segment_def init_segment_trans insertI1 sup_commute)
next
  assume rhs: "init_segment S T \<and> n \<in> T"
  then obtain R where R: "T = S \<union> R" "S \<lless> R"
    by (auto simp: init_segment_def less_sets_def)
  then have "S\<union>R = insert n (S \<union> (R-{n})) \<and> insert n S \<lless> R-{n}"
    unfolding less_sets_def using rhs TS nat_less_le by auto
  then show "init_segment (insert n S) T"
    using R init_segment_Un by force
qed

lemma init_segment_insert:
  assumes "init_segment S T" and T: "T \<lless> {n}"
  shows "init_segment S (insert n T)"
proof (cases "T={}")
  case False
  obtain S' where S': "T = S \<union> S'" "S \<lless> S'"
    by (meson assms init_segment_def)
  then have "insert n T = S \<union> (insert n S')" "S \<lless> (insert n S')"
    using T False by (auto simp: less_sets_def)
  then show ?thesis
    using init_segment_Un by presburger
qed (use assms in auto)

subsection \<open>Definitions and basic properties\<close>

definition Ramsey :: "[nat set set, nat] \<Rightarrow> bool"
  where "Ramsey \<F> r \<equiv> \<forall>f \<in> \<F> \<rightarrow> {..<r}.
                       \<forall>M. infinite M \<longrightarrow>
                           (\<exists>N i. N \<subseteq> M \<and> infinite N \<and> i<r \<and> (\<forall>j<r. j\<noteq>i \<longrightarrow> f -` {j} \<inter> \<F> \<inter> Pow N = {}))"

definition thin_set :: "nat set set \<Rightarrow> bool"
  where "thin_set \<F> \<equiv> \<F> \<subseteq> Collect finite \<and> (\<forall>S\<in>\<F>. \<forall>T\<in>\<F>. init_segment S T \<longrightarrow> S=T)"

definition comparables :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set set"
  where "comparables S M \<equiv> {T. finite T \<and> (init_segment T S \<or> init_segment S T \<and> T-S \<subseteq> M)}"

lemma comparables_iff: "T \<in> comparables S M \<longleftrightarrow> finite T \<and> (init_segment T S \<or> init_segment S T \<and> T \<subseteq> S \<union> M)"
  by (auto simp: comparables_def init_segment_def)

lemma comparables_subset: "\<Union>(comparables S M) \<subseteq> S \<union> M"
  by (auto simp: comparables_def init_segment_def)

lemma comparables_empty [simp]: "comparables {} M = Fpow M"
  by (auto simp: comparables_def Fpow_def)

lemma comparables_mono: "N \<subseteq> M \<Longrightarrow> comparables S N \<subseteq> comparables S M"
  by (auto simp: comparables_def)

definition "rejects \<F> S M \<equiv> comparables S M \<inter> \<F> = {}"

abbreviation accepts
  where "accepts \<F> S M \<equiv> \<not> rejects \<F> S M"

definition strongly_accepts
  where "strongly_accepts \<F> S M \<equiv> (\<forall>N\<subseteq>M. rejects \<F> S N \<longrightarrow> finite N)"

definition decides
  where "decides \<F> S M \<equiv> rejects \<F> S M \<or> strongly_accepts \<F> S M"

definition decides_subsets
  where "decides_subsets \<F> M \<equiv> \<forall>T. T \<subseteq> M \<longrightarrow> finite T \<longrightarrow> decides \<F> T M"

lemma strongly_accepts_imp_accepts:
  "\<lbrakk>strongly_accepts \<F> S M; infinite M\<rbrakk> \<Longrightarrow> accepts \<F> S M"
  unfolding strongly_accepts_def by blast

lemma rejects_trivial: "\<lbrakk>rejects \<F> S M; thin_set \<F>; init_segment F S; F \<in> \<F>\<rbrakk> \<Longrightarrow> False"
  unfolding rejects_def thin_set_def
  using comparables_iff by blast

lemma rejects_subset: "\<lbrakk>rejects \<F> S M; N \<subseteq> M\<rbrakk> \<Longrightarrow> rejects \<F> S N"
  by (fastforce simp add: rejects_def comparables_def)

lemma strongly_accepts_subset: "\<lbrakk>strongly_accepts \<F> S M; N \<subseteq> M\<rbrakk> \<Longrightarrow> strongly_accepts \<F> S N"
  by (auto simp: strongly_accepts_def)

lemma decides_subset: "\<lbrakk>decides \<F> S M; N \<subseteq> M\<rbrakk> \<Longrightarrow> decides \<F> S N"
  unfolding decides_def
  using rejects_subset strongly_accepts_subset by blast

lemma decides_subsets_subset: "\<lbrakk>decides_subsets \<F> M; N \<subseteq> M\<rbrakk> \<Longrightarrow> decides_subsets \<F> N"
  by (meson decides_subset decides_subsets_def subset_trans)

lemma rejects_empty [simp]: "rejects \<F> {} M \<longleftrightarrow> Fpow M \<inter> \<F> = {}"
  by (auto simp: rejects_def comparables_def Fpow_def)

lemma strongly_accepts_empty [simp]: "strongly_accepts \<F> {} M \<longleftrightarrow> (\<forall>N\<subseteq>M. Fpow N \<inter> \<F> = {} \<longrightarrow> finite N)"
  by (simp add: strongly_accepts_def Fpow_def disjoint_iff)

lemma ex_infinite_decides_1:
  assumes "infinite M"
  obtains N where "N \<subseteq> M" "infinite N" "decides \<F> S N"
  by (meson assms decides_def order_refl strongly_accepts_def)

proposition ex_infinite_decides_finite:
  assumes "infinite M" "finite S"
  obtains N where "N \<subseteq> M" "infinite N" "\<And>T. T \<subseteq> S \<Longrightarrow> decides \<F> T N"
proof -
  have "finite (Pow S)"
    by (simp add: \<open>finite S\<close>)
  then obtain f :: "nat \<Rightarrow> nat set" where f: "f ` {..< card (Pow S)} = Pow S"
    by (metis bij_betw_imp_surj_on [OF bij_betw_from_nat_into_finite])
  obtain M0 where M0: "infinite M0" "M0 \<subseteq> M" "decides \<F> (f 0) M0"
    by (meson \<open>infinite M\<close> ex_infinite_decides_1)
  define F where "F \<equiv> rec_nat M0 (\<lambda>n N. @N'. N' \<subseteq> N \<and> infinite N' \<and> decides \<F> (f (Suc n)) N')"
  have P_Suc: "F (Suc n) = (@N'. N' \<subseteq> F n \<and> infinite N' \<and> decides \<F> (f (Suc n)) N')" for n
    by (auto simp: F_def)
  have *: "infinite (F n) \<and> decides \<F> (f n) (F n) \<and> F n \<subseteq> M" for n
  proof (induction n)
    case 0
    with \<open>infinite M\<close> show ?case
      by (auto simp: F_def M0)
  next
    case (Suc n)
    let ?\<Phi> = "\<lambda>N'. N' \<subseteq> F n \<and> infinite N' \<and> decides \<F> (f (Suc n)) N'"
    have "\<exists>N'. ?\<Phi> N'"
      by (meson Suc ex_infinite_decides_1 subset_trans)
    then have "Eps ?\<Phi> \<subseteq> F n \<and> infinite (Eps ?\<Phi>) \<and> decides \<F> (f (Suc n)) (Eps ?\<Phi>)"
      by (rule someI_ex)
    with Suc.IH show ?case
      by (auto simp: P_Suc)
  qed
  then have telescope: "F (Suc n) \<subseteq> F n" for n
    unfolding P_Suc by (metis (no_types, lifting) ex_infinite_decides_1 someI_ex)
  let ?N = "\<Inter>n<card (Pow S). F n"
  show thesis
  proof
    show "?N \<subseteq> M"
      by (metis "*" INF_lower2 Pow_iff f imageE order_refl)
  next
    have eq: "(\<Inter>n\<le>m. F n) = F m" for m
      by (induction m) (use telescope in \<open>auto simp: atMost_Suc\<close>)
    then show "infinite ?N"
      by (metis "*" Suc_le_D Suc_le_eq finite_subset le_INF_iff lessThan_Suc_atMost lessThan_iff)
  next
    fix T
    assume "T \<subseteq> S"
    then obtain m where "f m = T" "m < card (Pow S)"
      using f by (blast elim: equalityE)
    then show "decides \<F> T ?N"
      by (metis "*" INT_lower decides_subset lessThan_iff)
  qed
qed


lemma sorted_wrt_subset: "\<lbrakk>X \<in> list.set l; sorted_wrt (\<le>) l\<rbrakk> \<Longrightarrow> hd l \<subseteq> X"
  by (induction l) auto

text \<open>Todorčević's Lemma 1.18\<close>
proposition ex_infinite_decides_subsets:
  assumes "thin_set \<F>" "infinite M"
  obtains N where "N \<subseteq> M" "infinite N" "decides_subsets \<F> N"
proof -
  obtain M0 where M0: "infinite M0" "M0 \<subseteq> M" "decides \<F> {} M0"
    by (meson \<open>infinite M\<close> ex_infinite_decides_1)
  define decides_all where "decides_all \<equiv> \<lambda>S N. \<forall>T \<subseteq> S. decides \<F> T N"
  define \<Phi> where "\<Phi> \<equiv> \<lambda>NL N. N \<subseteq> hd NL \<and> Inf N > Inf (hd NL) \<and> infinite N \<and> decides_all (List.set (map Inf NL)) N"
  have "\<exists>N. \<Phi> NL N" if "infinite (hd NL)" for NL
  proof -
    obtain N where N: "N \<subseteq> hd NL \<and> infinite N \<and> decides_all (List.set (map Inf NL)) N"
      unfolding \<Phi>_def decides_all_def
      by (metis List.finite_set ex_infinite_decides_finite \<open>infinite (hd NL)\<close>)
    then have "Inf (N \<inter> {Inf (hd NL)<..}) > Inf (hd NL)"
      by (metis Inf_nat_def1 Int_iff finite.emptyI finite_nat_Int_greaterThan_iff greaterThan_iff)
    then show ?thesis
      unfolding \<Phi>_def decides_all_def
      by (meson Int_lower1 N decides_all_def decides_subset finite_nat_Int_greaterThan_iff subset_trans)
  qed
  then have \<Phi>_Eps: "\<Phi> NL (Eps (\<Phi> NL))" if "infinite (hd NL)" for NL
    by (simp add: someI_ex that)
  define F where "F \<equiv> rec_nat [M0] (\<lambda>n NL. (Eps (\<Phi> NL)) # NL)"
  have F_simps [simp]: "F 0 = [M0]" "F (Suc n) = Eps (\<Phi> (F n)) # F n" for n
    by (auto simp: F_def)
  have F: "F n \<noteq> [] \<and> sorted_wrt (\<le>) (F n) \<and> list.set (F n) \<subseteq> Collect infinite \<and> list.set (F n) \<subseteq> Pow M" for n
  proof (induction n)
    case 0
    then show ?case
      by (simp add: M0)
  next
    case (Suc n)
    then have *: "\<Phi> (F n) (Eps (\<Phi> (F n)))"
      using \<Phi>_Eps hd_in_set by blast
    show ?case
    proof (intro conjI)
      show "sorted_wrt (\<subseteq>) (F (Suc n))"
        using subset_trans [OF _ sorted_wrt_subset] Suc.IH \<Phi>_def "*" by auto
      show "list.set (F (Suc n)) \<subseteq> {S. infinite S}"
        using "*" \<Phi>_def Suc.IH by force
      show "list.set (F (Suc n)) \<subseteq> Pow M"
        using "*" Suc.IH \<Phi>_def hd_in_set by force
    qed auto
  qed
  have \<Phi>F: "\<Phi> (F n) (Eps (\<Phi> (F n)))" for n
    using F \<Phi>_Eps hd_in_set by blast
  then have decides: "decides_all (List.set (map Inf (F n))) (Eps (\<Phi> (F n)))" for n
    using \<Phi>_def by blast
  have Eps_subset_hd: "Eps (\<Phi> (F n)) \<subseteq> hd (F n) " for n
    using \<Phi>F \<Phi>_def by blast
  have "List.set (map Inf (F n)) \<subseteq> List.set (map Inf (F (Suc n)))" for n
    by auto
  then have map_Inf_subset: "m \<le> n \<Longrightarrow> List.set (map Inf (F m)) \<subseteq> List.set (map Inf (F n))" for m n
    by (rule order_class.lift_Suc_mono_le) auto
  define mmap where "mmap \<equiv> \<lambda>n. Inf (hd (F (Suc n)))"
  have "mmap n < mmap (Suc n)" for n
    by (metis F_simps(2) \<Phi>F \<Phi>_def list.sel(1) mmap_def)
  then have "strict_mono mmap"
    by (simp add: lift_Suc_mono_less strict_mono_def)
  then have "inj mmap"
    by (simp add: strict_mono_imp_inj_on)
  have finite_F_bound: "\<exists>n. S \<subseteq> List.set (map Inf (F n))"
    if S: "S \<subseteq> range mmap" "finite S" for S
  proof -
    obtain K where "finite K" "S \<subseteq> mmap ` K"
      by (metis S finite_subset_image order_refl)
    show ?thesis
    proof
      have "mmap ` K \<subseteq> list.set (map Inf (F (Suc (Max K))))"
        unfolding mmap_def image_subset_iff
        by (metis F Max_ge \<open>finite K\<close> hd_in_set imageI map_Inf_subset not_less_eq_eq set_map subsetD)
      with S show "S \<subseteq> list.set (map Inf (F (Suc (Max K))))"
        using \<open>S \<subseteq> mmap ` K\<close> by auto
    qed
  qed
  have "Eps (\<Phi> (F (Suc n))) \<subseteq> Eps (\<Phi> (F n))" for n
    by (metis F_simps(2) \<Phi>F \<Phi>_def list.sel(1))
  then have Eps_\<Phi>_decreasing: "m \<le> n \<Longrightarrow> Eps (\<Phi> (F n)) \<subseteq> Eps (\<Phi> (F m))" for m n
    by (rule order_class.lift_Suc_antimono_le)
  have hd_Suc_eq_Eps: "hd (F (Suc n)) = Eps (\<Phi> (F n))" for n
    by simp
  have Inf_hd_in_hd: "Inf (hd (F n)) \<in> hd (F n)" for n
    by (metis Inf_nat_def1 \<Phi>F \<Phi>_def finite.emptyI rev_finite_subset)
  then have Inf_hd_in_Eps: "Inf (hd (F m)) \<in> Eps (\<Phi> (F n))" if "m>n" for m n
    by (metis Eps_\<Phi>_decreasing Nat.lessE leD mmap_def not_less_eq_eq subsetD that hd_Suc_eq_Eps)
  then have image_mmap_subset_hd_F: "mmap ` {n..} \<subseteq> hd (F (Suc n))" for n
    by (metis hd_Suc_eq_Eps atLeast_iff image_subsetI le_imp_less_Suc mmap_def)
  have "list.set (F k) \<subseteq> list.set (F n)" if "k \<le> n" for k n
    by (rule order_class.lift_Suc_mono_le) (use that in auto)
  then have hd_F_in_F: "hd (F k) \<in> list.set (F n)" if "k \<le> n" for k n
    by (meson F hd_in_set subsetD that)
  show thesis
  proof
    show infinite_mm: "infinite (range mmap)"
      using \<open>inj mmap\<close> range_inj_infinite by blast
    show "range mmap \<subseteq> M"
      using Eps_subset_hd \<open>M0 \<subseteq> M\<close> image_mmap_subset_hd_F by fastforce
    show "decides_subsets \<F> (range mmap)"
      unfolding decides_subsets_def
    proof (intro strip)
      fix S
      assume "S \<subseteq> range mmap" "finite S"
      define n where "n \<equiv> LEAST n. S \<subseteq> List.set (map Inf (F n))"
      have "\<exists>n. S \<subseteq> List.set (map Inf (F n))"
        using \<open>S \<subseteq> range mmap\<close> \<open>finite S\<close> finite_F_bound by blast
      then have S: "S \<subseteq> List.set (map Inf (F n))" and minS: "\<And>m. m<n \<Longrightarrow> \<not> S \<subseteq> List.set (map Inf (F m))"
        unfolding n_def by (meson LeastI_ex not_less_Least)+
      have decides_Fn: "decides \<F> S (Eps (\<Phi> (F n)))"
        using S decides decides_all_def by blast
      show "decides \<F> S (range mmap)"
      proof (cases "n=0")
        case True
        then show ?thesis
          by (metis image_mmap_subset_hd_F decides_Fn decides_subset hd_Suc_eq_Eps atLeast_0)
      next
        case False
        have notin_map_Inf: "x \<notin> List.set (map Inf (F n))" if "S \<lless> {x}" for x
        proof clarsimp
          fix T
          assume "x = Inf T" and "T \<in> list.set (F n)"
          with that have ls: "S \<lless> {Inf T}"
            by auto
          have "S \<subseteq> List.set (map Inf (F j))"
            if  T: "T \<in> list.set (F (Suc j))" for j
          proof clarsimp
            fix x
            assume "x \<in> S"
            then have "x < Inf T"
              using less_setsD ls by blast
            then have "x \<notin> T"
              using Inf_nat_def not_less_Least by auto
            obtain k where k: "x = mmap k"
              using \<open>S \<subseteq> range mmap\<close> \<open>x \<in> S\<close> by blast
            with T \<open>x < Inf T\<close> have "k < j"
              by (metis Eps_\<Phi>_decreasing F Inf_hd_in_hd hd_Suc_eq_Eps \<open>x \<notin> T\<close> mmap_def not_le sorted_wrt_subset subsetD)
            then have "Eps (\<Phi> (F k)) \<in> list.set (F j)"
              by (metis Suc_leI hd_Suc_eq_Eps hd_F_in_F)
            then show "x \<in> Inf ` list.set (F j)"
              by (auto simp: k image_iff mmap_def)
          qed
          then obtain m where "m<n" "S \<subseteq> List.set (map Inf (F m))"
            using \<open>n \<noteq> 0\<close> by (metis \<open>T \<in> list.set (F n)\<close> lessI less_Suc_eq_0_disj)
          then show False
            using minS by blast
        qed
        have Inf_hd_F: "Inf (hd (F m)) \<in> Eps (\<Phi> (F n))" if "S \<lless> {Inf (hd (F m))}" for m
          by (metis Inf_hd_in_Eps hd_F_in_F notin_map_Inf imageI leI set_map that)
        have less_S: "S \<lless> {Inf (hd (F m))}"
          if "init_segment S T" "Inf (hd (F m)) \<in> T" "Inf (hd (F m)) \<notin> S" for T m
          using \<open>finite S\<close> that by (auto simp: init_segment_iff less_sets_def)
        consider "rejects \<F> S (Eps (\<Phi> (F n)))" | "strongly_accepts \<F> S (Eps (\<Phi> (F n)))"
          using decides_Fn by (auto simp: decides_def)
        then show ?thesis
        proof cases
          case 1
          have "rejects \<F> S (range mmap)"
          proof (clarsimp simp: rejects_def disjoint_iff)
            fix X
            assume "X \<in> comparables S (range mmap)" and "X \<in> \<F>"
            moreover have "\<And>x X. \<lbrakk>X \<in> \<F>; init_segment S X; x \<in> X; x \<notin> S; x \<in> range mmap\<rbrakk>
                                \<Longrightarrow> x \<in> Eps (\<Phi> (F n))"
              using less_S Inf_hd_F mmap_def by blast
            ultimately have "X \<in> comparables S (Eps (\<Phi> (F n)))"
              by (auto simp: comparables_def disjoint_iff subset_iff)
            with 1 \<open>X \<in> \<F>\<close> show False by (auto simp: rejects_def)
          qed
          then show ?thesis
            by (auto simp: decides_def)
        next
          case 2
          have False
            if "N \<subseteq> range mmap" and "rejects \<F> S N" and "infinite N" for N
          proof -
            have "N = mmap ` {n..} \<inter> N \<union> mmap ` {..<n} \<inter> N"
              using in_mono that(1) by fastforce
            then have "infinite (mmap ` {n..} \<inter> N)"
              by (metis finite_Int finite_Un finite_imageI finite_lessThan that(3))
            moreover have "rejects \<F> S (mmap ` {n..} \<inter> N)"
              using rejects_subset \<open>rejects \<F> S N\<close> by fastforce
            moreover have "mmap ` {n..} \<inter> N \<subseteq>Eps (\<Phi> (F n))"
              using image_mmap_subset_hd_F by fastforce
            ultimately show ?thesis
              using 2 by (auto simp: strongly_accepts_def)
          qed
          with 2 have "strongly_accepts \<F> S (range mmap)"
            by (auto simp: strongly_accepts_def)
          then show ?thesis
            by (auto simp: decides_def)
        qed
      qed
    qed
  qed
qed


text \<open>Todorčević's Lemma 1.19\<close>
proposition strongly_accepts_1_19:
  assumes acc: "strongly_accepts \<F> S M"
    and "thin_set \<F>" "infinite M" "S \<subseteq> M" "finite S"
    and dsM: "decides_subsets \<F> M"
  shows "finite {n \<in> M. \<not> strongly_accepts \<F> (insert n S) M}"
proof (rule ccontr)
  define N where "N = {n \<in> M. rejects \<F> (insert n S) M} \<inter> {Sup S<..}"
  have "N \<subseteq> M" and N: "\<And>n. n \<in> N \<longleftrightarrow> n \<in> M \<and> rejects \<F> (insert n S) M \<and> n > Sup S"
    by (auto simp: N_def)
  assume "\<not> ?thesis"
  moreover have "{n \<in> M. \<not> strongly_accepts \<F> (insert n S) M} = {n \<in> M. rejects \<F> (insert n S) M}"
    using dsM \<open>finite S\<close> \<open>infinite M\<close> \<open>S \<subseteq> M\<close> unfolding decides_subsets_def
    by (meson decides_def finite.insertI insert_subset strongly_accepts_imp_accepts)
  ultimately have "infinite {n \<in> M. rejects \<F> (insert n S) M}"
    by simp
  then have "infinite N"
    by (simp add: N_def finite_nat_Int_greaterThan_iff)
  then have "accepts \<F> S N"
    using acc strongly_accepts_def \<open>N \<subseteq> M\<close> by blast
  then obtain T where T: "T \<in> comparables S N" "T \<in> \<F>" and TSN: "T \<subseteq> S \<union> N"
    unfolding rejects_def
    using comparables_iff init_segment_subset by fastforce
  then consider "init_segment T S" | "init_segment S T" "S\<noteq>T"
    by (auto simp: comparables_def)
  then show False
  proof cases
    case 1
    then have "init_segment T (insert n S)" if "n \<in> N" for n
      by (meson Sup_nat_less_sets_singleton N \<open>finite S\<close> init_segment_insert that)
    with \<open>infinite N\<close> \<open>thin_set \<F>\<close> \<open>T \<in> \<F>\<close> show False
      by (meson N infinite_nat_iff_unbounded rejects_trivial)
  next
    let ?n = "Min (T-S)"
    case 2
    then have "?n \<in> N"
      by (metis Diff_partition Diff_subset_conv Min_in T(1) TSN comparables_iff finite_Diff init_segment_subset subsetD sup_bot.right_neutral)
    then have "rejects \<F> (insert ?n S) N"
      using rejects_subset \<open>N \<subseteq> M\<close> by (auto simp: N_def)
    then have \<section>: "\<not> init_segment T (insert ?n S) \<and> (\<not> init_segment (insert ?n S) T \<or> insert ?n S = T)"
      using T Diff_partition TSN \<open>Min (T - S) \<in> N\<close> \<open>finite S\<close>
      unfolding rejects_def comparables_iff disjoint_iff
      by auto
    then have T_nS: "T \<subseteq> insert ?n S"
    proof (elim conjE disjE)
      assume "\<not> init_segment T (insert ?n S)" "\<not> init_segment (insert ?n S) T"
      moreover have "S \<lless> {Min (T - S)}"
        using Sup_nat_less_sets_singleton N \<open>Min (T - S) \<in> N\<close> assms(5) by blast
      moreover have "finite (T - S)"
        using T comparables_iff by blast
      ultimately show ?thesis
        using \<open>init_segment S T\<close> Min_in init_segment_insert_iff by auto
    qed auto
    have non_TS: "\<not> init_segment T S"
      by (meson Sup_nat_less_sets_singleton N \<open>?n \<in> N\<close> \<open>\<not> init_segment T (insert (?n) S) \<and> (\<not> init_segment (insert (?n) S) T \<or> insert (?n) S = T)\<close> assms(5) init_segment_insert)
    consider (ST) "S \<subseteq> T" | (TS) "T \<subseteq> S"
      using 2 init_segment_subset by blast
    then show False
    proof cases
      case ST
      with \<section> show ?thesis
        using 2 T(1) \<open>T \<subseteq> insert (?n) S\<close>  comparables_iff init_segment_iff by auto
    next
      case TS
      then show ?thesis
      proof -
        have "\<not> init_segment T S"
          by (meson Sup_nat_less_sets_singleton N \<open>?n \<in> N\<close> \<section> assms(5) init_segment_insert)
        then show ?thesis
          using 2 TS init_segment_subset by fastforce
      qed
    qed
  qed
qed

text \<open>Much work is needed for this slight strengthening of the previous result!\<close>
proposition strongly_accepts_1_19_plus:
  assumes "thin_set \<F>" "infinite M"
    and dsM: "decides_subsets \<F> M"
  obtains N where "N \<subseteq> M" "infinite N"
       "\<And>S n. \<lbrakk>S \<subseteq> N; finite S; strongly_accepts \<F> S N; n \<in> N; S \<lless> {n}\<rbrakk>
              \<Longrightarrow> strongly_accepts \<F> (insert n S) N"
proof -
  define insert_closed where
    "insert_closed \<equiv> \<lambda>NL N. \<forall>T \<subseteq> Inf ` set NL. \<forall>n \<in> N.
                      strongly_accepts \<F> T ((Inf ` set NL) \<union> hd NL) \<longrightarrow>
                      T \<lless> {n} \<longrightarrow> strongly_accepts \<F> (insert n T) ((Inf ` set NL) \<union> hd NL)"
  define \<Phi> where "\<Phi> \<equiv> \<lambda>NL N. N \<subseteq> hd NL \<and> Inf N > Inf (hd NL) \<and> infinite N \<and> insert_closed NL N"
  have "\<exists>N. \<Phi> NL N" if NL: "infinite (hd NL)" "Inf ` set NL \<union> hd NL \<subseteq> M" for NL
  proof -
    let ?m = "Inf ` set NL"
    let ?M = "?m \<union> hd NL"
    define P where "P \<equiv> \<lambda>S. {n \<in> ?M. \<not> strongly_accepts \<F> (insert n S) ?M}"
    have "\<exists>k. P S \<subseteq> {..k}"
      if "S \<subseteq> Inf ` set NL" "strongly_accepts \<F> S ?M" for S
    proof -
      have "finite (P S)"
        unfolding P_def
      proof (rule strongly_accepts_1_19)
        show "decides_subsets \<F> ?M"
          using NL(2) decides_subsets_subset dsM by blast
        show "finite S"
          using finite_surj that(1) by blast
      qed (use that NL assms in auto)
      then show ?thesis
        by (simp add: finite_nat_iff_bounded_le)
    qed
    then obtain f where f: "\<And>S. \<lbrakk>S \<subseteq> Inf ` set NL; strongly_accepts \<F> S ?M\<rbrakk> \<Longrightarrow> P S \<subseteq> {..f S}"
      by metis
    define m where "m \<equiv> Max (insert (Inf (hd NL)) (f ` Pow (Inf ` set NL)))"
    have \<section>: "strongly_accepts \<F> (insert n S) ?M"
      if S: "S \<subseteq> Inf ` set NL" "strongly_accepts \<F> S ?M" and n: "n \<in> hd NL \<inter> {m<..}" for S n
    proof -
      have "f S \<le> m"
        unfolding m_def using that(1) by auto
      then show ?thesis
        using f [OF S] n unfolding P_def by auto
    qed
    have "\<Phi> NL (hd NL \<inter> {m<..})"
      unfolding \<Phi>_def
    proof (intro conjI)
    have "Inf (hd NL) \<le> m"
      by (simp add: m_def)
    then show "Inf (hd NL) < Inf (hd NL \<inter> {m<..})"
      by (metis Inf_nat_def1 Int_iff finite.emptyI finite_nat_Int_greaterThan_iff greaterThan_iff le_less_trans that(1))
      show "infinite (hd NL \<inter> {m<..})"
        by (simp add: finite_nat_Int_greaterThan_iff that(1))
      show "insert_closed NL (hd NL \<inter> {m<..})"
        by (auto intro: \<section> simp: insert_closed_def)
    qed auto
    then show ?thesis ..
  qed
  then have \<Phi>_Eps: "\<Phi> NL (Eps (\<Phi> NL))" if "infinite (hd NL)"  "Inf ` set NL \<union> hd NL \<subseteq> M" for NL
    by (meson someI_ex that)
  define F where "F \<equiv> rec_nat [M] (\<lambda>n NL. (Eps (\<Phi> NL)) # NL)"
  have F_simps [simp]: "F 0 = [M]" "F (Suc n) = Eps (\<Phi> (F n)) # F n" for n
    by (auto simp: F_def)
  have InfM: "Inf M \<in> M"
    by (metis Inf_nat_def1 assms(2) finite.emptyI)
  have F: "F n \<noteq> [] \<and> sorted_wrt (\<le>) (F n) \<and> list.set (F n) \<subseteq> Collect infinite \<and> set (F n) \<subseteq> Pow M \<and> Inf ` list.set (F n) \<subseteq> M" for n
  proof (induction n)
    case (Suc n)
    have "hd (F n) \<subseteq> M"
      by (meson Pow_iff Suc.IH hd_in_set subsetD)
    then have 1: "Ball (list.set (F n)) ((\<subseteq>) (Eps (\<Phi> (F n))))"
      using order_trans [OF _ sorted_wrt_subset]
      by (metis Suc.IH Un_subset_iff \<Phi>_Eps \<Phi>_def hd_in_set mem_Collect_eq subsetD)
    have 2: "infinite (Eps (\<Phi> (F n)))"
      by (metis Ball_Collect Pow_iff Suc.IH Un_subset_iff \<Phi>_Eps \<Phi>_def hd_in_set subset_iff)
    have 3: "Eps (\<Phi> (F n)) \<subseteq> M"
      by (meson Pow_iff Suc.IH 1 hd_in_set subset_iff)
    have "Inf (Eps (\<Phi> (F n))) \<in> M"
      by (metis 2 3 Inf_nat_def1 finite.simps in_mono)
    with 1 2 3 show ?case
      using Suc by simp
  qed (auto simp: InfM \<open>infinite M\<close>)
  have \<Phi>F: "\<Phi> (F n) (Eps (\<Phi> (F n)))" for n
    by (metis Ball_Collect F Pow_iff Un_subset_iff \<Phi>_Eps hd_in_set subset_code(1))
  then have insert_closed: "insert_closed (F n) (Eps (\<Phi> (F n)))" for n
    using \<Phi>_def by blast
  have Eps_subset_hd: "Eps (\<Phi> (F n)) \<subseteq> hd (F n)" for n
    using \<Phi>F \<Phi>_def by blast
  define mmap where "mmap \<equiv> \<lambda>n. Inf (hd (F (Suc n)))"
  have "mmap n < mmap (Suc n)" for n
    by (metis F_simps(2) \<Phi>F \<Phi>_def list.sel(1) mmap_def)
  then have "strict_mono mmap"
    by (simp add: lift_Suc_mono_less strict_mono_def)
  then have "inj mmap"
    by (simp add: strict_mono_imp_inj_on)
  have "Eps (\<Phi> (F (Suc n))) \<subseteq> Eps (\<Phi> (F n))" for n
    by (metis F_simps(2) \<Phi>F \<Phi>_def list.sel(1))
  then have Eps_\<Phi>_decreasing: "m \<le> n \<Longrightarrow> Eps (\<Phi> (F n)) \<subseteq> Eps (\<Phi> (F m))" for m n
    by (rule order_class.lift_Suc_antimono_le)
  have hd_Suc_eq_Eps: "hd (F (Suc n)) = Eps (\<Phi> (F n))" for n
    by simp
  have "Inf (hd (F n)) \<in> hd (F n)" for n
    by (metis Inf_nat_def1 \<Phi>F \<Phi>_def finite.emptyI finite_subset)
  then have Inf_hd_in_Eps: "Inf (hd (F m)) \<in> Eps (\<Phi> (F n))" if "m>n" for m n
    by (metis Eps_\<Phi>_decreasing Nat.lessE hd_Suc_eq_Eps less_imp_le_nat subsetD that)
  then have image_mmap_subset_hd_F: "mmap ` {n..} \<subseteq> hd (F (Suc n))" for n
    by (metis hd_Suc_eq_Eps atLeast_iff image_subsetI le_imp_less_Suc mmap_def)
  have "list.set (F k) \<subseteq> list.set (F n)" if "k \<le> n" for k n
    by (rule order_class.lift_Suc_mono_le) (use that in auto)
  then have hd_F_in_F: "hd (F k) \<in> list.set (F n)" if "k \<le> n" for k n
    by (meson F hd_in_set subsetD that)
  show ?thesis
  proof
    show infinite_mm: "infinite (range mmap)"
      using \<open>inj mmap\<close> range_inj_infinite by blast
    show "range mmap \<subseteq> M"
      using Eps_subset_hd image_mmap_subset_hd_F by fastforce
  next
    fix S a
    assume "S \<subseteq> range mmap" "finite S" and acc: "strongly_accepts \<F> S (range mmap)"
       and a: "a \<in> range mmap" and Sn: "S \<lless> {a}"
    then obtain n where n: "a = mmap n"
      by auto
    define N where "N \<equiv> LEAST n. S \<subseteq> mmap ` {..<n}"
    have "\<exists>n. S \<subseteq> mmap ` {..<n}"
      by (metis \<open>S \<subseteq> range mmap\<close> \<open>finite S\<close> finite_nat_iff_bounded finite_subset_image image_mono)
    then have S: "S \<subseteq> mmap ` {..<N}" and minS: "\<And>m. m<N \<Longrightarrow> \<not> S \<subseteq> mmap ` {..<m}"
      unfolding N_def by (meson LeastI_ex not_less_Least)+
    have range_mmap_subset: "range mmap \<subseteq> Inf ` list.set (F n) \<union> hd (F n)" for n
    proof (induction n)
      case 0
      then show ?case
        using Eps_subset_hd image_mmap_subset_hd_F by fastforce
    next
      case (Suc n)
      then show ?case
        by clarsimp (metis Inf_hd_in_Eps hd_F_in_F image_iff leI mmap_def)
    qed
    have subM: "(Inf ` list.set (F N) \<union> hd (F N)) \<subseteq> M"
      by (meson F PowD hd_in_set subsetD sup.boundedI)
    have "strongly_accepts \<F> (insert a S) (Inf ` list.set (F N) \<union> hd (F N))"
    proof (rule insert_closed [unfolded insert_closed_def, rule_format])
      have "mmap ` {..<N} \<subseteq> Inf ` list.set (F N)"
        using Suc_leI hd_F_in_F by (fastforce simp: mmap_def le_eq_less_or_eq)
      with S show Ssub: "S \<subseteq> Inf ` list.set (F N)"
        by auto
      have "S \<subseteq> mmap ` {..<n}"
        using Sn S \<open>strict_mono mmap\<close> strict_mono_less
        by (fastforce simp: less_sets_def n  image_iff subset_iff Bex_def)
      with leI minS have "n\<ge>N" by blast
      then show "a \<in> Eps (\<Phi> (F N))"
        using image_mmap_subset_hd_F n by fastforce
      show "strongly_accepts \<F> S (Inf ` list.set (F N) \<union> hd (F N))"
      proof (rule ccontr)
        assume "\<not> strongly_accepts \<F> S (Inf ` list.set (F N) \<union> hd (F N))"
        then have "rejects \<F> S (Inf ` list.set (F N) \<union> hd (F N))"
          using dsM subM unfolding decides_subsets_def
          by (meson F Ssub \<open>finite S\<close> decides_def decides_subset subset_trans)
        moreover have "accepts \<F> S (range mmap)"
          using \<open>inj mmap\<close> acc range_inj_infinite strongly_accepts_imp_accepts by blast
        ultimately show False
          by (meson range_mmap_subset rejects_subset)
      qed
    qed (auto simp: Sn)
    then show "strongly_accepts \<F> (insert a S) (range mmap)"
      using range_mmap_subset strongly_accepts_subset by auto
  qed
qed


subsection \<open>Main Theorem\<close>

text\<open>Weirdly, the assumption  @{term "f ` \<F> \<subseteq> {..<2}"} is not used here; it's perhaps unnecessary due to
     the particular way that @{term Ramsey} is defined. It's only needed for @{term "r > 2"}\<close>
theorem Nash_Williams_2:
  assumes "thin_set \<F>" shows "Ramsey \<F> 2"
  unfolding Ramsey_def
proof clarify
  fix f :: "nat set \<Rightarrow> nat" and M :: "nat set"
  assume "infinite M"
  let ?\<F> = "\<lambda>i. f -` {i} \<inter> \<F>"
  have fin\<F>: "\<And>X. X \<in> \<F> \<Longrightarrow> finite X"
    using assms thin_set_def by auto
  have thin: "thin_set (?\<F> i)" for i
    using assms thin_set_def by auto
  obtain N where "N \<subseteq> M" "infinite N" and N: "decides_subsets (?\<F> 0) N"
    using \<open>infinite M\<close> ex_infinite_decides_subsets thin by blast
  then consider "rejects (?\<F> 0) {} N" | "strongly_accepts (?\<F> 0) {} N"
    unfolding decides_def decides_subsets_def by blast
  then show "\<exists>N i. N \<subseteq> M \<and> infinite N \<and> i<2 \<and> (\<forall>j<2. j \<noteq> i \<longrightarrow> f -` {j} \<inter> \<F> \<inter> Pow N = {})"
  proof cases
    case 1
    then have "?\<F> 0 \<inter> Pow N = {}"
      unfolding rejects_def disjoint_iff
      by (metis IntD2 PowD comparables_iff fin\<F> init_segment_empty sup_bot.left_neutral)
    then show ?thesis
      using \<open>N \<subseteq> M\<close> \<open>infinite N\<close> less_2_cases_iff by auto
  next
    case 2
    then have \<section>: "\<And>P. \<lbrakk>P\<subseteq>N; \<And>S. \<lbrakk>S \<subseteq> P; finite S\<rbrakk> \<Longrightarrow> S \<notin> (?\<F> 0)\<rbrakk> \<Longrightarrow> finite P"
      by (auto simp: Fpow_def disjoint_iff)
    obtain P where "P \<subseteq> N" "infinite P" and P:
      "\<And>S n. \<lbrakk>S \<subseteq> P; finite S; strongly_accepts (?\<F> 0) S P; n \<in> P; S \<lless> {n}\<rbrakk>
              \<Longrightarrow> strongly_accepts (?\<F> 0) (insert n S) P"
      using strongly_accepts_1_19_plus [OF thin \<open>infinite N\<close> N] by blast
    have "?\<F> 1 \<inter> Pow P = {}"
    proof (clarsimp simp: disjoint_iff)
      fix T
      assume T: "f T = Suc 0" "T \<in> \<F>" and "T \<subseteq> P"
      then have "finite T"
        using fin\<F> by blast
      moreover have "strongly_accepts (?\<F> 0) S P" if "finite S" "S \<subseteq> P" for S
        using that
      proof (induction "card S" arbitrary: S)
        case (Suc n)
        then have Seq: "S = insert (Sup S) (S - {Sup S})"
          using Sup_nat_def Max_eq_iff by fastforce
        then have "card (S - {Sup S}) = n"
          using Suc card_Diff_singleton by fastforce
        then have sacc: "strongly_accepts (?\<F> 0) (S - {Sup S}) P"
          using Suc by blast
        have "S \<noteq> {}"
          using Suc.hyps(2) by auto
        have "S - {Sup S} \<lless> {Sup S}"
          by (simp add: Suc.prems(1) Sup_nat_def \<open>S \<noteq> {}\<close> dual_order.strict_iff_order less_sets_def)
        then have "strongly_accepts (?\<F> 0) (insert (Sup S) (S - {Sup S})) P"
          by (metis P Seq Suc.prems finite_Diff insert_subset sacc)
        then show ?case
          using Seq by auto
      qed (use 2 \<open>P \<subseteq> N\<close> in auto)
      ultimately have "\<exists>x\<in>comparables T P. f x = 0 \<and> x \<in> \<F>"
        unfolding strongly_accepts_def rejects_def disjoint_iff
        by (metis \<open>T \<subseteq> P\<close> \<open>infinite P\<close> IntE order_refl vimage_singleton_eq)
      then show False
        using T assms thin_set_def comparables_def by force
    qed
    then show ?thesis
      by (metis One_nat_def \<open>N \<subseteq> M\<close> \<open>P \<subseteq> N\<close> \<open>infinite P\<close> less_2_cases_iff subset_trans)
  qed
qed

theorem Nash_Williams:
  assumes \<F>: "thin_set \<F>" "r > 0" shows "Ramsey \<F> r"
  using \<open>r > 0\<close>
proof (induction r)
  case (Suc r)
  show ?case
  proof (cases "r<2")
    case True
    then show ?thesis
      by (metis Nash_Williams_2 One_nat_def Ramsey_def assms(1) less_2_cases less_one numeral_2_eq_2 order_refl)
  next
    case False
    with Suc.IH have Ram: "Ramsey \<F> r"
      by auto
    have "r \<ge> 2"
      by (simp add: False leI)
    show ?thesis
      unfolding Ramsey_def
    proof clarify
      fix f and M :: "nat set"
      assume fim: "f \<in> \<F> \<rightarrow> {..<Suc r}"
        and "infinite M"
      define g where "g \<equiv> \<lambda>x. if f x = r then r-1 else f x"
      have gim: "g \<in> \<F> \<rightarrow> {..<r}"
        using fim False by (force simp: g_def)
      then obtain N i where  "N \<subseteq> M" "infinite N" "i<r" and i: "\<And>j. \<lbrakk>j<r; i\<noteq>j\<rbrakk> \<Longrightarrow> g -` {j} \<inter> \<F> \<inter> Pow N = {}"
        using Ram \<open>infinite M\<close> by (metis Ramsey_def)
      show "\<exists>N i. N \<subseteq> M \<and> infinite N \<and> i < Suc r \<and> (\<forall>j<Suc r. j \<noteq> i \<longrightarrow> f -` {j} \<inter> \<F> \<inter> Pow N = {})"
      proof (cases "i<r-1")
        case True
        have "f -` {j} \<inter> \<F> \<inter> Pow N = {}" if "j < Suc r" "i \<noteq> j" for j
          using \<open>N \<subseteq> M\<close> \<open>infinite N\<close> \<open>i<r\<close> i that
          apply (clarsimp simp add: disjoint_iff g_def less_Suc_eq)
          by (metis True diff_less less_nat_zero_code nat_neq_iff zero_less_one)
        then show ?thesis
          by (metis \<open>N \<subseteq> M\<close> \<open>infinite N\<close> less_Suc_eq)
      next
        case False
        then have "i = r-1"
          using \<open>i<r\<close> by linarith
        then have null: "f -` {j} \<inter> \<F> \<inter> Pow N = {}" if "j<r-1" for j
          using that i [of j] \<open>i < r\<close> by (auto simp: g_def disjoint_iff split: if_split_asm)
        define h where "h \<equiv> \<lambda>x. if f x = r then 0 else f x"
        have him: "h \<in> \<F> \<rightarrow> {..<r}"
          using fim i False \<open>i<r\<close> by (force simp: h_def)
        then obtain P j where "P \<subseteq> N" "infinite P" "j<r" and j: "\<forall>k<r. j\<noteq>k \<longrightarrow> h -` {k} \<inter> \<F> \<inter> Pow P = {}"
          by (metis Ramsey_def Ram \<open>infinite N\<close>)
        have "\<exists>i. \<forall>j<Suc r. j \<noteq> i \<longrightarrow> f -` {j} \<inter> \<F> \<inter> Pow P = {}"
        proof (cases "j=0")
          case True
          then show ?thesis
            apply (rule_tac x=r in exI)
            using null [of 0] \<open>r \<ge> 2\<close> \<open>P \<subseteq> N\<close> j by (force simp: h_def disjoint_iff less_Suc_eq)
        next
          case False
          then show ?thesis
            apply (rule_tac x=j in exI)
            using j \<open>j < r\<close> by (auto simp: h_def less_Suc_eq disjoint_iff intro: less_trans)
        qed
        then show ?thesis
          by (metis Suc.prems \<open>N \<subseteq> M\<close> \<open>P \<subseteq> N\<close> \<open>infinite P\<close> subset_trans)
      qed
    qed
  qed
qed auto

end
