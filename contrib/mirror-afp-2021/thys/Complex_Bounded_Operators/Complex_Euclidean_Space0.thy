(*  Title:      HOL/Analysis/Euclidean_Space.thy
    Author:     Johannes Hölzl, TU München
    Author:     Brian Huffman, Portland State University
*)

section \<open>\<open>Complex_Euclidean_Space0\<close> -- Finite-Dimensional Inner Product Spaces\<close>

theory Complex_Euclidean_Space0
  imports
    "HOL-Analysis.L2_Norm"
    "Complex_Inner_Product"
    "HOL-Analysis.Product_Vector"
    "HOL-Library.Rewrite"
begin


(* subsection\<^marker>\<open>tag unimportant\<close> \<open>Interlude: Some properties of real sets\<close> *)

(* Complex analogue not needed *)
(* lemma seq_mono_lemma:
  assumes "\<forall>(n::nat) \<ge> m. (d n :: real) < e n"
    and "\<forall>n \<ge> m. e n \<le> e m"
  shows "\<forall>n \<ge> m. d n < e m" *)

subsection \<open>Type class of Euclidean spaces\<close>

class ceuclidean_space = complex_inner +
  fixes CBasis :: "'a set"
  assumes nonempty_CBasis [simp]: "CBasis \<noteq> {}"
  assumes finite_CBasis [simp]: "finite CBasis"
  assumes cinner_CBasis:
    "\<lbrakk>u \<in> CBasis; v \<in> CBasis\<rbrakk> \<Longrightarrow> cinner u v = (if u = v then 1 else 0)"
  assumes ceuclidean_all_zero_iff:
    "(\<forall>u\<in>CBasis. cinner x u = 0) \<longleftrightarrow> (x = 0)"

syntax "_type_cdimension" :: "type \<Rightarrow> nat"  ("(1CDIM/(1'(_')))")
translations "CDIM('a)" \<rightharpoonup> "CONST card (CONST CBasis :: 'a set)"
typed_print_translation \<open>
  [(\<^const_syntax>\<open>card\<close>,
    fn ctxt => fn _ => fn [Const (\<^const_syntax>\<open>CBasis\<close>, Type (\<^type_name>\<open>set\<close>, [T]))] =>
      Syntax.const \<^syntax_const>\<open>_type_cdimension\<close> $ Syntax_Phases.term_of_typ ctxt T)]
\<close>

lemma (in ceuclidean_space) norm_CBasis[simp]: "u \<in> CBasis \<Longrightarrow> norm u = 1"
  unfolding norm_eq_sqrt_cinner by (simp add: cinner_CBasis)

lemma (in ceuclidean_space) cinner_same_CBasis[simp]: "u \<in> CBasis \<Longrightarrow> cinner u u = 1"
  by (simp add: cinner_CBasis)

lemma (in ceuclidean_space) cinner_not_same_CBasis: "u \<in> CBasis \<Longrightarrow> v \<in> CBasis \<Longrightarrow> u \<noteq> v \<Longrightarrow> cinner u v = 0"
  by (simp add: cinner_CBasis)

lemma (in ceuclidean_space) sgn_CBasis: "u \<in> CBasis \<Longrightarrow> sgn u = u"
  unfolding sgn_div_norm by (simp add: scaleR_one)

lemma (in ceuclidean_space) CBasis_zero [simp]: "0 \<notin> CBasis"
proof
  assume "0 \<in> CBasis" thus "False"
    using cinner_CBasis [of 0 0] by simp
qed

lemma (in ceuclidean_space) nonzero_CBasis: "u \<in> CBasis \<Longrightarrow> u \<noteq> 0"
  by clarsimp

lemma (in ceuclidean_space) SOME_CBasis: "(SOME i. i \<in> CBasis) \<in> CBasis"
  by (metis ex_in_conv nonempty_CBasis someI_ex)

lemma norm_some_CBasis [simp]: "norm (SOME i. i \<in> CBasis) = 1"
  by (simp add: SOME_CBasis)

lemma (in ceuclidean_space) cinner_sum_left_CBasis[simp]:
  "b \<in> CBasis \<Longrightarrow> cinner (\<Sum>i\<in>CBasis. f i *\<^sub>C i) b = cnj (f b)"
  by (simp add: cinner_sum_left cinner_CBasis if_distrib comm_monoid_add_class.sum.If_cases)

(* Not present in Euclidean_Space *)
(* lemma (in ceuclidean_space) cinner_sum_right_CBasis[simp]:
    "b \<in> CBasis \<Longrightarrow> cinner b (\<Sum>i\<in>CBasis. f i *\<^sub>C i) = f b"
  by (metis (mono_tags, lifting) cinner_commute cinner_sum_left_CBasis comm_monoid_add_class.sum.cong complex_cnj_cnj) *)

lemma (in ceuclidean_space) ceuclidean_eqI:
  assumes b: "\<And>b. b \<in> CBasis \<Longrightarrow> cinner x b = cinner y b" shows "x = y"
proof -
  from b have "\<forall>b\<in>CBasis. cinner (x - y) b = 0"
    by (simp add: cinner_diff_left)
  then show "x = y"
    by (simp add: ceuclidean_all_zero_iff)
qed

lemma (in ceuclidean_space) ceuclidean_eq_iff:
  "x = y \<longleftrightarrow> (\<forall>b\<in>CBasis. cinner x b = cinner y b)"
  by (auto intro: ceuclidean_eqI)

lemma (in ceuclidean_space) ceuclidean_representation_sum:
  "(\<Sum>i\<in>CBasis. f i *\<^sub>C i) = b \<longleftrightarrow> (\<forall>i\<in>CBasis. f i = cnj (cinner b i))"
  apply (subst ceuclidean_eq_iff) 
  apply simp by (metis complex_cnj_cnj cinner_commute)

lemma (in ceuclidean_space) ceuclidean_representation_sum':
  "b = (\<Sum>i\<in>CBasis. f i *\<^sub>C i) \<longleftrightarrow> (\<forall>i\<in>CBasis. f i = cinner i b)"
  apply (auto simp add: ceuclidean_representation_sum[symmetric])
   apply (metis ceuclidean_representation_sum cinner_commute)
  by (metis local.ceuclidean_representation_sum local.cinner_commute)

lemma (in ceuclidean_space) ceuclidean_representation: "(\<Sum>b\<in>CBasis. cinner b x *\<^sub>C b) = x"
  unfolding ceuclidean_representation_sum
  using local.cinner_commute by blast

lemma (in ceuclidean_space) ceuclidean_cinner: "cinner x y = (\<Sum>b\<in>CBasis. cinner x b * cnj (cinner y b))"
  apply (subst (1 2) ceuclidean_representation [symmetric])
  apply (simp add: cinner_sum_right cinner_CBasis ac_simps)
  by (metis local.cinner_commute mult.commute)

lemma (in ceuclidean_space) choice_CBasis_iff:
  fixes P :: "'a \<Rightarrow> complex \<Rightarrow> bool"
  shows "(\<forall>i\<in>CBasis. \<exists>x. P i x) \<longleftrightarrow> (\<exists>x. \<forall>i\<in>CBasis. P i (cinner x i))"
  unfolding bchoice_iff
proof safe
  fix f assume "\<forall>i\<in>CBasis. P i (f i)"
  then show "\<exists>x. \<forall>i\<in>CBasis. P i (cinner x i)"
    by (auto intro!: exI[of _ "\<Sum>i\<in>CBasis. cnj (f i) *\<^sub>C i"])
qed auto

lemma (in ceuclidean_space) bchoice_CBasis_iff:
  fixes P :: "'a \<Rightarrow> complex \<Rightarrow> bool"
  shows "(\<forall>i\<in>CBasis. \<exists>x\<in>A. P i x) \<longleftrightarrow> (\<exists>x. \<forall>i\<in>CBasis. cinner x i \<in> A \<and> P i (cinner x i))"
  by (simp add: choice_CBasis_iff Bex_def)

lemma (in ceuclidean_space) ceuclidean_representation_sum_fun:
  "(\<lambda>x. \<Sum>b\<in>CBasis. cinner b (f x) *\<^sub>C b) = f"
  apply (rule ext) 
  apply (simp add: ceuclidean_representation_sum)
  by (meson local.cinner_commute)

lemma euclidean_isCont:
  assumes "\<And>b. b \<in> CBasis \<Longrightarrow> isCont (\<lambda>x. (cinner b (f x)) *\<^sub>C b) x"
  shows "isCont f x"
  apply (subst ceuclidean_representation_sum_fun [symmetric])
  apply (rule isCont_sum)
  by (blast intro: assms)

lemma CDIM_positive [simp]: "0 < CDIM('a::ceuclidean_space)"
  by (simp add: card_gt_0_iff)

lemma CDIM_ge_Suc0 [simp]: "Suc 0 \<le> card CBasis"
  by (meson CDIM_positive Suc_leI)


lemma sum_cinner_CBasis_scaleC [simp]:
  fixes f :: "'a::ceuclidean_space \<Rightarrow> 'b::complex_vector"
  assumes "b \<in> CBasis" shows "(\<Sum>i\<in>CBasis. (cinner i b) *\<^sub>C f i) = f b"
  by (simp add: comm_monoid_add_class.sum.remove [OF finite_CBasis assms]
      assms cinner_not_same_CBasis comm_monoid_add_class.sum.neutral)

lemma sum_cinner_CBasis_eq [simp]:
  assumes "b \<in> CBasis" shows "(\<Sum>i\<in>CBasis. (cinner i b) * f i) = f b"
  by (simp add: comm_monoid_add_class.sum.remove [OF finite_CBasis assms]
      assms cinner_not_same_CBasis comm_monoid_add_class.sum.neutral)

lemma sum_if_cinner [simp]:
  assumes "i \<in> CBasis" "j \<in> CBasis"
  shows "cinner (\<Sum>k\<in>CBasis. if k = i then f i *\<^sub>C i else g k *\<^sub>C k) j = (if j=i then cnj (f j) else cnj (g j))"
proof (cases "i=j")
  case True
  with assms show ?thesis
    by (auto simp: cinner_sum_left if_distrib [of "\<lambda>x. cinner x j"] cinner_CBasis cong: if_cong)
next
  case False
  have "(\<Sum>k\<in>CBasis. cinner (if k = i then f i *\<^sub>C i else g k *\<^sub>C k) j) =
        (\<Sum>k\<in>CBasis. if k = j then cnj (g k) else 0)"
    apply (rule sum.cong)
    using False assms by (auto simp: cinner_CBasis)
  also have "... = cnj (g j)"
    using assms by auto
  finally show ?thesis
    using False by (auto simp: cinner_sum_left)
qed

lemma norm_le_componentwise:
  "(\<And>b. b \<in> CBasis \<Longrightarrow> cmod(cinner x b) \<le> cmod(cinner y b)) \<Longrightarrow> norm x \<le> norm y"
  apply (auto simp: cnorm_le ceuclidean_cinner [of x x] ceuclidean_cinner [of y y] power2_eq_square intro!: sum_mono)
   apply (smt (verit, best) mult.commute sum.cong)
  by (simp add: ordered_field_class.sign_simps(33))

lemma CBasis_le_norm: "b \<in> CBasis \<Longrightarrow> cmod (cinner x b) \<le> norm x"
  by (rule order_trans [OF Cauchy_Schwarz_ineq2]) simp

lemma norm_bound_CBasis_le: "b \<in> CBasis \<Longrightarrow> norm x \<le> e \<Longrightarrow> cmod (inner x b) \<le> e"
  by (metis inner_commute mult.left_neutral norm_CBasis norm_of_real order_trans real_inner_class.Cauchy_Schwarz_ineq2)

lemma norm_bound_CBasis_lt: "b \<in> CBasis \<Longrightarrow> norm x < e \<Longrightarrow> cmod (inner x b) < e"
  by (metis inner_commute le_less_trans mult.left_neutral norm_CBasis norm_of_real real_inner_class.Cauchy_Schwarz_ineq2)

lemma cnorm_le_l1: "norm x \<le> (\<Sum>b\<in>CBasis. cmod (cinner x b))"
  apply (subst ceuclidean_representation[of x, symmetric])
  apply (rule order_trans[OF norm_sum])
  apply (auto intro!: sum_mono)
  by (metis cinner_commute complex_inner_1_left complex_inner_class.Cauchy_Schwarz_ineq2 mult.commute mult.left_neutral norm_one)

(* Maybe it holds in the complex case but the proof does not adapt trivially *)
(* lemma csum_norm_allsubsets_bound:
  fixes f :: "'a \<Rightarrow> 'n::ceuclidean_space"
  assumes fP: "finite P"
    and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (sum f Q) \<le> e"
  shows "(\<Sum>x\<in>P. norm (f x)) \<le> 2 * real CDIM('n) * e" *)


(* subsection\<^marker>\<open>tag unimportant\<close> \<open>Subclass relationships\<close> *)
(* Everything is commented out, so we comment out the heading, too. *)

(* If we include this, instantiation prod :: (ceuclidean_space, ceuclidean_space) ceuclidean_space below fails *)
(* instance ceuclidean_space \<subseteq> perfect_space
proof
  fix x :: 'a show "\<not> open {x}"
  proof
    assume "open {x}"
    then obtain e where "0 < e" and e: "\<forall>y. dist y x < e \<longrightarrow> y = x"
      unfolding open_dist by fast
    define y where "y = x + scaleR (e/2) (SOME b. b \<in> CBasis)"
    have [simp]: "(SOME b. b \<in> CBasis) \<in> CBasis"
      by (rule someI_ex) (auto simp: ex_in_conv)
    from \<open>0 < e\<close> have "y \<noteq> x"
      unfolding y_def by (auto intro!: nonzero_CBasis)
    from \<open>0 < e\<close> have "dist y x < e"
      unfolding y_def by (simp add: dist_norm)
    from \<open>y \<noteq> x\<close> and \<open>dist y x < e\<close> show "False"
      using e by simp
  qed
qed *)

subsection \<open>Class instances\<close>

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Type \<^typ>\<open>complex\<close>\<close>

(* No analogue *)
(* instantiation real :: ceuclidean_space *)

instantiation complex :: ceuclidean_space
begin

definition
  [simp]: "CBasis = {1::complex}"

instance
  by standard auto

end

lemma CDIM_complex[simp]: "CDIM(complex) = 1"
  by simp

(* lemma CDIM_complex[simp]: "DIM(complex) = 2"
lemma complex_CBasis_1 [iff]: "(1::complex) \<in> CBasis"
lemma complex_CBasis_i [iff]: "\<i> \<in> CBasis" *)

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Type \<^typ>\<open>'a \<times> 'b\<close>\<close>

instantiation prod :: (complex_inner, complex_inner) complex_inner
begin

definition cinner_prod_def:
  "cinner x y = cinner (fst x) (fst y) + cinner (snd x) (snd y)"

lemma cinner_Pair [simp]: "cinner (a, b) (c, d) = cinner a c + cinner b d"
  unfolding cinner_prod_def by simp

instance
proof
  fix r :: complex
  fix x y z :: "'a::complex_inner \<times> 'b::complex_inner"
  show "cinner x y = cnj (cinner y x)"
    unfolding cinner_prod_def
    by simp
  show "cinner (x + y) z = cinner x z + cinner y z"
    unfolding cinner_prod_def
    by (simp add: cinner_add_left)
  show "cinner (scaleC r x) y = cnj r * cinner x y"
    unfolding cinner_prod_def
    by (simp add: distrib_left)
  show "0 \<le> cinner x x"
    unfolding cinner_prod_def
    by (intro add_nonneg_nonneg cinner_ge_zero)
  show "cinner x x = 0 \<longleftrightarrow> x = 0"
    unfolding cinner_prod_def prod_eq_iff
    by (metis antisym cinner_eq_zero_iff cinner_ge_zero fst_zero le_add_same_cancel2 snd_zero verit_sum_simplify)
  show "norm x = sqrt (cmod (cinner x x))"
    unfolding norm_prod_def cinner_prod_def
    by (metis (no_types, lifting) Re_complex_of_real add_nonneg_nonneg cinner_ge_zero complex_of_real_cmod plus_complex.simps(1) power2_norm_eq_cinner')
qed

end

lemma cinner_Pair_0: "cinner x (0, b) = cinner (snd x) b" "cinner x (a, 0) = cinner (fst x) a"
  by (cases x, simp)+

instantiation prod :: (ceuclidean_space, ceuclidean_space) ceuclidean_space
begin

definition
  "CBasis = (\<lambda>u. (u, 0)) ` CBasis \<union> (\<lambda>v. (0, v)) ` CBasis"

lemma sum_CBasis_prod_eq:
  fixes f::"('a*'b)\<Rightarrow>('a*'b)"
  shows "sum f CBasis = sum (\<lambda>i. f (i, 0)) CBasis + sum (\<lambda>i. f (0, i)) CBasis"
proof -
  have "inj_on (\<lambda>u. (u::'a, 0::'b)) CBasis" "inj_on (\<lambda>u. (0::'a, u::'b)) CBasis"
    by (auto intro!: inj_onI Pair_inject)
  thus ?thesis
    unfolding CBasis_prod_def
    by (subst sum.union_disjoint) (auto simp: CBasis_prod_def sum.reindex)
qed

instance proof
  show "(CBasis :: ('a \<times> 'b) set) \<noteq> {}"
    unfolding CBasis_prod_def by simp
next
  show "finite (CBasis :: ('a \<times> 'b) set)"
    unfolding CBasis_prod_def by simp
next
  fix u v :: "'a \<times> 'b"
  assume "u \<in> CBasis" and "v \<in> CBasis"
  thus "cinner u v = (if u = v then 1 else 0)"
    unfolding CBasis_prod_def cinner_prod_def
    by (auto simp add: cinner_CBasis split: if_split_asm)
next
  fix x :: "'a \<times> 'b"
  show "(\<forall>u\<in>CBasis. cinner x u = 0) \<longleftrightarrow> x = 0"
    unfolding CBasis_prod_def ball_Un ball_simps
    by (simp add: cinner_prod_def prod_eq_iff ceuclidean_all_zero_iff)
qed

lemma CDIM_prod[simp]: "CDIM('a \<times> 'b) = CDIM('a) + CDIM('b)"
  unfolding CBasis_prod_def
  by (subst card_Un_disjoint) (auto intro!: card_image arg_cong2[where f="(+)"] inj_onI)

end


subsection \<open>Locale instances\<close>

lemma finite_dimensional_vector_space_euclidean:
  "finite_dimensional_vector_space (*\<^sub>C) CBasis"
proof unfold_locales
  show "finite (CBasis::'a set)" by (metis finite_CBasis)
  show "complex_vector.independent (CBasis::'a set)"
    unfolding complex_vector.dependent_def cdependent_raw_def[symmetric]
    apply (subst complex_vector.span_finite)
     apply simp
    apply clarify
    apply (drule_tac f="cinner a" in arg_cong)
    by (simp add: cinner_CBasis cinner_sum_right eq_commute)
  show "module.span (*\<^sub>C) CBasis = UNIV"
    unfolding complex_vector.span_finite [OF finite_CBasis] cspan_raw_def[symmetric]
    by (auto intro!: ceuclidean_representation[symmetric])
qed

interpretation ceucl: finite_dimensional_vector_space "scaleC :: complex => 'a => 'a::ceuclidean_space" "CBasis"
  rewrites "module.dependent (*\<^sub>C) = cdependent"
    and "module.representation (*\<^sub>C) = crepresentation"
    and "module.subspace (*\<^sub>C) = csubspace"
    and "module.span (*\<^sub>C) = cspan"
    and "vector_space.extend_basis (*\<^sub>C) = cextend_basis"
    and "vector_space.dim (*\<^sub>C) = cdim"
    and "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
    and "finite_dimensional_vector_space.dimension CBasis = CDIM('a)"
    (* and "dimension = CDIM('a)" *) (* This line leads to a type error. Not sure why *)
  by (auto simp add: cdependent_raw_def crepresentation_raw_def
      csubspace_raw_def cspan_raw_def cextend_basis_raw_def cdim_raw_def clinear_def
      complex_scaleC_def[abs_def]
      finite_dimensional_vector_space.dimension_def
      intro!: finite_dimensional_vector_space.dimension_def
      finite_dimensional_vector_space_euclidean)

interpretation ceucl: finite_dimensional_vector_space_pair_1
  "scaleC::complex\<Rightarrow>'a::ceuclidean_space\<Rightarrow>'a" CBasis
  "scaleC::complex\<Rightarrow>'b::complex_vector \<Rightarrow> 'b"
  by unfold_locales

interpretation ceucl?: finite_dimensional_vector_space_prod scaleC scaleC CBasis CBasis
  rewrites "Basis_pair = CBasis"
    and "module_prod.scale (*\<^sub>C) (*\<^sub>C) = (scaleC::_\<Rightarrow>_\<Rightarrow>('a \<times> 'b))"
proof -
  show "finite_dimensional_vector_space_prod (*\<^sub>C) (*\<^sub>C) CBasis CBasis"
    by unfold_locales
  interpret finite_dimensional_vector_space_prod "(*\<^sub>C)" "(*\<^sub>C)" "CBasis::'a set" "CBasis::'b set"
    by fact
  show "Basis_pair = CBasis"
    unfolding Basis_pair_def CBasis_prod_def by auto
  show "module_prod.scale (*\<^sub>C) (*\<^sub>C) = scaleC"
    by (fact module_prod_scale_eq_scaleC)
qed

end
