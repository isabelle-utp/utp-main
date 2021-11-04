section \<open>\<open>Extra_General\<close> -- General missing things\<close>

theory Extra_General
  imports
    "HOL-Library.Cardinality"
    "HOL-Analysis.Elementary_Topology"
    Jordan_Normal_Form.Conjugate
    "HOL-Analysis.Uniform_Limit"
    "HOL-Library.Set_Algebras"
    "HOL-Types_To_Sets.Types_To_Sets"
begin

subsection \<open>Misc\<close>

lemma reals_zero_comparable_iff:
  "(x::complex)\<in>\<real> \<longleftrightarrow> x \<le> 0 \<or> x \<ge> 0"
  unfolding complex_is_Real_iff less_eq_complex_def
  by auto

lemma reals_zero_comparable:
  fixes x::complex
  assumes "x\<in>\<real>"
  shows "x \<le> 0 \<or> x \<ge> 0"
  using assms unfolding reals_zero_comparable_iff by assumption

lemma unique_choice: "\<forall>x. \<exists>!y. Q x y \<Longrightarrow> \<exists>!f. \<forall>x. Q x (f x)"
  apply (auto intro!: choice ext) by metis

lemma sum_single: 
  assumes "finite A"
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "sum f A = (if i\<in>A then f i else 0)"
  apply (subst sum.mono_neutral_cong_right[where S=\<open>A \<inter> {i}\<close> and h=f])
  using assms by auto

lemma image_set_plus: 
  assumes \<open>linear U\<close>
  shows \<open>U ` (A + B) = U ` A + U ` B\<close>
  unfolding image_def set_plus_def
  using assms by (force simp: linear_add)

consts heterogenous_identity :: \<open>'a \<Rightarrow> 'b\<close>
overloading heterogenous_identity_id \<equiv> "heterogenous_identity :: 'a \<Rightarrow> 'a" begin
definition heterogenous_identity_def[simp]: \<open>heterogenous_identity_id = id\<close>
end

lemma bdd_above_image_mono:
  assumes \<open>\<And>x. x\<in>S \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>bdd_above (g ` S)\<close>
  shows \<open>bdd_above (f ` S)\<close>
  by (smt (verit, ccfv_threshold) assms(1) assms(2) bdd_aboveI2 bdd_above_def order_trans rev_image_eqI)


lemma L2_set_mono2:
  assumes a1: "finite L" and a2: "K \<le> L"
  shows "L2_set f K \<le> L2_set f L"
proof-
  have "(\<Sum>i\<in>K. (f i)\<^sup>2) \<le> (\<Sum>i\<in>L. (f i)\<^sup>2)"
  proof (rule sum_mono2)
    show "finite L"
      using a1.
    show "K \<subseteq> L"
      using a2.
    show "0 \<le> (f b)\<^sup>2"
      if "b \<in> L - K"
      for b :: 'a
      using that
      by simp 
  qed
  hence "sqrt (\<Sum>i\<in>K. (f i)\<^sup>2) \<le> sqrt (\<Sum>i\<in>L. (f i)\<^sup>2)"
    by (rule real_sqrt_le_mono)
  thus ?thesis
    unfolding L2_set_def.
qed

lemma Sup_real_close:
  fixes e :: real
  assumes "0 < e"
    and S: "bdd_above S" "S \<noteq> {}"
  shows "\<exists>x\<in>S. Sup S - e < x"
proof -
  have \<open>Sup (ereal ` S) \<noteq> \<infinity>\<close>
    by (metis assms(2) bdd_above_def ereal_less_eq(3) less_SUP_iff less_ereal.simps(4) not_le)
  moreover have \<open>Sup (ereal ` S) \<noteq> -\<infinity>\<close>
    by (simp add: SUP_eq_iff assms(3))
  ultimately have Sup_bdd: \<open>\<bar>Sup (ereal ` S)\<bar> \<noteq> \<infinity>\<close>
    by auto
  then have \<open>\<exists>x'\<in>ereal ` S. Sup (ereal ` S) - ereal e < x'\<close>
    apply (rule_tac Sup_ereal_close)
    using assms by auto
  then obtain x where \<open>x \<in> S\<close> and Sup_x: \<open>Sup (ereal ` S) - ereal e < ereal x\<close>
    by auto
  have \<open>Sup (ereal ` S) = ereal (Sup S)\<close>
    using Sup_bdd by (rule ereal_Sup[symmetric])
  with Sup_x have \<open>ereal (Sup S - e) < ereal x\<close>
    by auto
  then have \<open>Sup S - e < x\<close>
    by auto
  with \<open>x \<in> S\<close> show ?thesis
    by auto
qed

text \<open>Improved version of @{attribute internalize_sort}: It is not necessary to specify the sort of the type variable.\<close>
attribute_setup internalize_sort' = \<open>let
fun find_tvar thm v = let
  val tvars = Term.add_tvars (Thm.prop_of thm) []
  val tv = case find_first (fn (n,sort) => n=v) tvars of
              SOME tv => tv | NONE => raise THM ("Type variable " ^ string_of_indexname v ^ " not found", 0, [thm])
in 
TVar tv
end

fun internalize_sort_attr (tvar:indexname) =
  Thm.rule_attribute [] (fn context => fn thm =>
    (snd (Internalize_Sort.internalize_sort (Thm.ctyp_of (Context.proof_of context) (find_tvar thm tvar)) thm)));
in
  Scan.lift Args.var >> internalize_sort_attr
end\<close>
  "internalize a sort"

subsection \<open>Not singleton\<close>

class not_singleton =
  assumes not_singleton_card: "\<exists>x y. x \<noteq> y"

lemma not_singleton_existence[simp]:
  \<open>\<exists> x::('a::not_singleton). x \<noteq> t\<close>
  using not_singleton_card[where ?'a = 'a] by (metis (full_types))

lemma UNIV_not_singleton[simp]: "(UNIV::_::not_singleton set) \<noteq> {x}"
  using not_singleton_existence[of x] by blast

lemma UNIV_not_singleton_converse: 
  assumes"\<And>x::'a. UNIV \<noteq> {x}"
  shows "\<exists>x::'a. \<exists>y. x \<noteq> y"
  using assms
  by fastforce 

subclass (in card2) not_singleton
  apply standard using two_le_card
  by (meson card_2_iff' obtain_subset_with_card_n)

subclass (in perfect_space) not_singleton
  apply intro_classes
  by (metis (mono_tags) Collect_cong Collect_mem_eq UNIV_I local.UNIV_not_singleton local.not_open_singleton local.open_subopen)

lemma class_not_singletonI_monoid_add:
  assumes "(UNIV::'a set) \<noteq> {0}"
  shows "class.not_singleton TYPE('a::monoid_add)"
proof intro_classes
  let ?univ = "UNIV :: 'a set"
  from assms obtain x::'a where "x \<noteq> 0"
    by auto
  thus "\<exists>x y :: 'a. x \<noteq> y"
    by auto
qed

lemma not_singleton_vs_CARD_1:
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>class.CARD_1 TYPE('a)\<close>
  using assms unfolding class.not_singleton_def class.CARD_1_def
  by (metis (full_types) One_nat_def UNIV_I card.empty card.insert empty_iff equalityI finite.intros(1) insert_iff subsetI)

subsection \<open>\<^class>\<open>CARD_1\<close>\<close>

context CARD_1 begin

lemma everything_the_same[simp]: "(x::'a)=y"
  by (metis (full_types) UNIV_I card_1_singletonE empty_iff insert_iff local.CARD_1)

lemma CARD_1_UNIV: "UNIV = {x::'a}"
  by (metis (full_types) UNIV_I card_1_singletonE local.CARD_1 singletonD)

lemma CARD_1_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
proof (rule ext)
  show "x t = y t"
    if "x a = y b"
    for t :: 'a
    using that  apply (subst (asm) everything_the_same[where x=a])
    apply (subst (asm) everything_the_same[where x=b])
    by simp
qed 

end

instance unit :: CARD_1
  apply standard by auto

instance prod :: (CARD_1, CARD_1) CARD_1
  apply intro_classes
  by (simp add: CARD_1)

instance "fun" :: (CARD_1, CARD_1) CARD_1
  apply intro_classes
  by (auto simp add: card_fun CARD_1)


lemma enum_CARD_1: "(Enum.enum :: 'a::{CARD_1,enum} list) = [a]"
proof -
  let ?enum = "Enum.enum :: 'a::{CARD_1,enum} list"
  have "length ?enum = 1"
    apply (subst card_UNIV_length_enum[symmetric])
    by (rule CARD_1)
  then obtain b where "?enum = [b]"
    apply atomize_elim
    apply (cases ?enum, auto)
    by (metis length_0_conv length_Cons nat.inject)
  thus "?enum = [a]"
    by (subst everything_the_same[of _ b], simp)
qed



subsection \<open>Topology\<close>

lemma cauchy_filter_metricI:
  fixes F :: "'a::metric_space filter"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
  shows "cauchy_filter F"
proof (unfold cauchy_filter_def le_filter_def, auto)
  fix P :: "'a \<times> 'a \<Rightarrow> bool"
  assume "eventually P uniformity"
  then obtain e where e: "e > 0" and P: "dist x y < e \<Longrightarrow> P (x, y)" for x y
    unfolding eventually_uniformity_metric by auto

  obtain P' where evP': "eventually P' F" and P'_dist: "P' x \<and> P' y \<Longrightarrow> dist x y < e" for x y
    apply atomize_elim using assms e by auto

  from evP' P'_dist P
  show "eventually P (F \<times>\<^sub>F F)"
    unfolding eventually_uniformity_metric eventually_prod_filter eventually_filtermap by metis
qed

lemma cauchy_filter_metric_filtermapI:
  fixes F :: "'a filter" and f :: "'a\<Rightarrow>'b::metric_space"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e)"
  shows "cauchy_filter (filtermap f F)"
proof (rule cauchy_filter_metricI)
  fix e :: real assume e: "e > 0"
  with assms obtain P where evP: "eventually P F" and dist: "P x \<and> P y \<Longrightarrow> dist (f x) (f y) < e" for x y
    by atomize_elim auto
  define P' where "P' y = (\<exists>x. P x \<and> y = f x)" for y
  have "eventually P' (filtermap f F)"
    unfolding eventually_filtermap P'_def 
    using evP
    by (smt eventually_mono) 
  moreover have "P' x \<and> P' y \<longrightarrow> dist x y < e" for x y
    unfolding P'_def using dist by metis
  ultimately show "\<exists>P. eventually P (filtermap f F) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
    by auto
qed


lemma tendsto_add_const_iff:
  \<comment> \<open>This is a generalization of \<open>Limits.tendsto_add_const_iff\<close>, 
      the only difference is that the sort here is more general.\<close>
  "((\<lambda>x. c + f x :: 'a::topological_group_add) \<longlongrightarrow> c + d) F \<longleftrightarrow> (f \<longlongrightarrow> d) F"
  using tendsto_add[OF tendsto_const[of c], of f d]
    and tendsto_add[OF tendsto_const[of "-c"], of "\<lambda>x. c + f x" "c + d"] by auto

lemma finite_subsets_at_top_minus: 
  assumes "A\<subseteq>B"
  shows "finite_subsets_at_top (B - A) \<le> filtermap (\<lambda>F. F - A) (finite_subsets_at_top B)"
proof (rule filter_leI)
  fix P assume "eventually P (filtermap (\<lambda>F. F - A) (finite_subsets_at_top B))"
  then obtain X where "finite X" and "X \<subseteq> B" 
    and P: "finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P (Y - A)" for Y
    unfolding eventually_filtermap eventually_finite_subsets_at_top by auto

  hence "finite (X-A)" and "X-A \<subseteq> B - A"
    by auto
  moreover have "finite Y \<and> X-A \<subseteq> Y \<and> Y \<subseteq> B - A \<longrightarrow> P Y" for Y
    using P[where Y="Y\<union>X"] \<open>finite X\<close> \<open>X \<subseteq> B\<close>
    by (metis Diff_subset Int_Diff Un_Diff finite_Un inf.orderE le_sup_iff sup.orderE sup_ge2)
  ultimately show "eventually P (finite_subsets_at_top (B - A))"
    unfolding eventually_finite_subsets_at_top by meson
qed


lemma finite_subsets_at_top_inter: 
  assumes "A\<subseteq>B"
  shows "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) \<le> finite_subsets_at_top A"
proof (rule filter_leI)
  show "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
    if "eventually P (finite_subsets_at_top A)"
    for P :: "'a set \<Rightarrow> bool"
    using that unfolding eventually_filtermap
    unfolding eventually_finite_subsets_at_top
    by (metis Int_subset_iff assms finite_Int inf_le2 subset_trans)
qed


lemma tendsto_principal_singleton:
  shows "(f \<longlongrightarrow> f x) (principal {x})"
  unfolding tendsto_def eventually_principal by simp

lemma complete_singleton: 
  "complete {s::'a::uniform_space}"
proof-
  have "F \<le> principal {s} \<Longrightarrow>
         F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> F \<le> nhds s" for F
    by (metis eventually_nhds eventually_principal le_filter_def singletonD)
  thus ?thesis
    unfolding complete_uniform
    by simp
qed

subsection \<open>Complex numbers\<close>

lemma cmod_Re:
  assumes "x \<ge> 0"
  shows "cmod x = Re x"
  using assms unfolding less_eq_complex_def cmod_def
  by auto

lemma abs_complex_real[simp]: "abs x \<in> \<real>" for x :: complex
  by (simp add: abs_complex_def)

lemma Im_abs[simp]: "Im (abs x) = 0"
  using abs_complex_real complex_is_Real_iff by blast


lemma cnj_x_x: "cnj x * x = (abs x)\<^sup>2"
proof (cases x)
  show "cnj x * x = \<bar>x\<bar>\<^sup>2"
    if "x = Complex x1 x2"
    for x1 :: real
      and x2 :: real
    using that   by (auto simp: complex_cnj complex_mult abs_complex_def 
        complex_norm power2_eq_square complex_of_real_def)
qed

lemma cnj_x_x_geq0[simp]: "cnj x * x \<ge> 0"
proof (cases x)
  show "0 \<le> cnj x * x"
    if "x = Complex x1 x2"
    for x1 :: real
      and x2 :: real
    using that by (auto simp: complex_cnj complex_mult complex_of_real_def)
qed


subsection \<open>List indices and enum\<close>


fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

lemma index_of_length: "index_of x y \<le> length y"
  apply (induction y) by auto

lemma index_of_correct:
  assumes "x \<in> set y"
  shows "y ! index_of x y = x"
  using assms apply (induction y arbitrary: x)
  by auto

lemma enum_idx_correct: 
  "Enum.enum ! enum_idx i = i"
proof-
  have "i \<in> set enum_class.enum"
    using UNIV_enum by blast 
  thus ?thesis
    unfolding enum_idx_def
    using index_of_correct by metis
qed

lemma index_of_bound: 
  assumes "y \<noteq> []" and "x \<in> set y"
  shows "index_of x y < length y"
  using assms proof(induction y arbitrary: x)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  show ?case 
  proof(cases "a = x")
    case True
    thus ?thesis by auto
  next
    case False
    moreover have "a \<noteq> x \<Longrightarrow> index_of x y < length y"
      using Cons.IH Cons.prems(2) by fastforce      
    ultimately show ?thesis by auto
  qed
qed

lemma enum_idx_bound: "enum_idx x < length (Enum.enum :: 'a list)" for x :: "'a::enum"
proof-
  have p1: "False"
    if "(Enum.enum :: 'a list) = []"
  proof-
    have "(UNIV::'a set) = set ([]::'a list)"
      using that UNIV_enum by metis
    also have "\<dots> = {}"
      by blast
    finally have "(UNIV::'a set) = {}".
    thus ?thesis by simp
  qed    
  have p2: "x \<in> set (Enum.enum :: 'a list)"
    using UNIV_enum by auto
  moreover have "(enum_class.enum::'a list) \<noteq> []"
    using p2 by auto
  ultimately show ?thesis
    unfolding enum_idx_def     
    using index_of_bound [where x = x and y = "(Enum.enum :: 'a list)"]
    by auto   
qed

lemma index_of_nth:
  assumes "distinct xs"
  assumes "i < length xs"
  shows "index_of (xs ! i) xs = i"
  using assms
  by (metis gr_implies_not_zero index_of_bound index_of_correct length_0_conv nth_eq_iff_index_eq nth_mem)

lemma enum_idx_enum: 
  assumes \<open>i < CARD('a::enum)\<close>
  shows \<open>enum_idx (enum_class.enum ! i :: 'a) = i\<close>
  unfolding enum_idx_def apply (rule index_of_nth)
  using assms by (simp_all add: card_UNIV_length_enum enum_distinct)

subsection \<open>Filtering lists/sets\<close>

lemma map_filter_map: "List.map_filter f (map g l) = List.map_filter (f o g) l"
proof (induction l)
  show "List.map_filter f (map g []) = List.map_filter (f \<circ> g) []"
    by (simp add: map_filter_simps)
  show "List.map_filter f (map g (a # l)) = List.map_filter (f \<circ> g) (a # l)"
    if "List.map_filter f (map g l) = List.map_filter (f \<circ> g) l"
    for a :: 'c
      and l :: "'c list"
    using that  map_filter_simps(1)
    by (metis comp_eq_dest_lhs list.simps(9))
qed

lemma map_filter_Some[simp]: "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
proof (induction l)
  show "List.map_filter (\<lambda>x. Some (f x)) [] = map f []"
    by (simp add: map_filter_simps)
  show "List.map_filter (\<lambda>x. Some (f x)) (a # l) = map f (a # l)"
    if "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
    for a :: 'b
      and l :: "'b list"
    using that by (simp add: map_filter_simps(1))
qed

lemma filter_Un: "Set.filter f (x \<union> y) = Set.filter f x \<union> Set.filter f y"
  unfolding Set.filter_def by auto  

lemma Set_filter_unchanged: "Set.filter P X = X" if "\<And>x. x\<in>X \<Longrightarrow> P x" for P and X :: "'z set"
  using that unfolding Set.filter_def by auto

subsection \<open>Maps\<close>

definition "inj_map \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"

definition "inv_map \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (inv \<pi> (Some y)) else None)"

lemma inj_map_total[simp]: "inj_map (Some o \<pi>) = inj \<pi>"
  unfolding inj_map_def inj_def by simp

lemma inj_map_Some[simp]: "inj_map Some"
  by (simp add: inj_map_def)

lemma inv_map_total: 
  assumes "surj \<pi>"
  shows "inv_map (Some o \<pi>) = Some o inv \<pi>"
proof-
  have "(if Some y \<in> range (\<lambda>x. Some (\<pi> x))
          then Some (SOME x. Some (\<pi> x) = Some y)
          else None) =
         Some (SOME b. \<pi> b = y)"
    if "surj \<pi>"
    for y
    using that by auto
  hence  "surj \<pi> \<Longrightarrow>
    (\<lambda>y. if Some y \<in> range (\<lambda>x. Some (\<pi> x))
         then Some (SOME x. Some (\<pi> x) = Some y) else None) =
    (\<lambda>x. Some (SOME xa. \<pi> xa = x))"
    by (rule ext) 
  thus ?thesis 
    unfolding inv_map_def o_def inv_def
    using assms by linarith
qed

lemma inj_map_map_comp[simp]: 
  assumes a1: "inj_map f" and a2: "inj_map g" 
  shows "inj_map (f \<circ>\<^sub>m g)"
  using a1 a2
  unfolding inj_map_def
  by (metis (mono_tags, lifting) map_comp_def option.case_eq_if option.expand)

lemma inj_map_inv_map[simp]: "inj_map (inv_map \<pi>)"
proof (unfold inj_map_def, rule allI, rule allI, rule impI, erule conjE)
  fix x y
  assume same: "inv_map \<pi> x = inv_map \<pi> y"
    and pix_not_None: "inv_map \<pi> x \<noteq> None"
  have x_pi: "Some x \<in> range \<pi>" 
    using pix_not_None unfolding inv_map_def apply auto
    by (meson option.distinct(1))
  have y_pi: "Some y \<in> range \<pi>" 
    using pix_not_None unfolding same unfolding inv_map_def apply auto
    by (meson option.distinct(1))
  have "inv_map \<pi> x = Some (Hilbert_Choice.inv \<pi> (Some x))"
    unfolding inv_map_def using x_pi by simp
  moreover have "inv_map \<pi> y = Some (Hilbert_Choice.inv \<pi> (Some y))"
    unfolding inv_map_def using y_pi by simp
  ultimately have "Hilbert_Choice.inv \<pi> (Some x) = Hilbert_Choice.inv \<pi> (Some y)"
    using same by simp
  thus "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed

end
