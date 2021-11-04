(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

section \<open>Complex Vectors\<close>

theory Complex_Vectors
imports 
  Quantum
  VectorSpace.VectorSpace
begin


subsection \<open>The Vector Space of Complex Vectors of Dimension n\<close>

definition module_cpx_vec:: "nat \<Rightarrow> (complex, complex vec) module" where
"module_cpx_vec n \<equiv> module_vec TYPE(complex) n"

definition cpx_rng:: "complex ring" where
"cpx_rng \<equiv> \<lparr>carrier = UNIV, mult = (*), one = 1, zero = 0, add = (+)\<rparr>"

lemma cpx_cring_is_field [simp]:
  "field cpx_rng"
  apply unfold_locales
                   apply (auto intro: right_inverse simp: cpx_rng_def Units_def field_simps)
  by (metis add.right_neutral add_diff_cancel_left' add_uminus_conv_diff)

lemma cpx_abelian_monoid [simp]:
  "abelian_monoid cpx_rng"
  using cpx_cring_is_field
  by (simp add: field_def abelian_group_def cring_def domain_def ring_def)

lemma vecspace_cpx_vec [simp]:
  "vectorspace cpx_rng (module_cpx_vec n)"
  apply unfold_locales
                      apply (auto simp: cpx_rng_def module_cpx_vec_def module_vec_def Units_def field_simps)
    apply (auto intro: right_inverse add_inv_exists_vec)
  by (metis add.right_neutral add_diff_cancel_left' add_uminus_conv_diff)

lemma module_cpx_vec [simp]:
  "Module.module cpx_rng (module_cpx_vec n)"
  using vecspace_cpx_vec by (simp add: vectorspace_def)

definition state_basis:: "nat \<Rightarrow> nat \<Rightarrow> complex vec" where
"state_basis n i \<equiv> unit_vec (2^n) i"

definition unit_vectors:: "nat \<Rightarrow> (complex vec) set" where
"unit_vectors n \<equiv> {unit_vec n i | i::nat. 0 \<le> i \<and> i < n}"

lemma unit_vectors_carrier_vec [simp]:
  "unit_vectors n \<subseteq> carrier_vec n"
  using unit_vectors_def by auto

lemma (in Module.module) finsum_over_singleton [simp]:
  assumes "f x \<in> carrier M"
  shows "finsum M f {x} = f x"
  using assms by simp

lemma lincomb_over_singleton [simp]:
  assumes "x \<in> carrier_vec n" and "f \<in> {x} \<rightarrow> UNIV"
  shows "module.lincomb (module_cpx_vec n) f {x} = f x \<cdot>\<^sub>v x" 
  using assms module.lincomb_def module_cpx_vec module_cpx_vec_def module.finsum_over_singleton
  by (smt module_vec_simps(3) module_vec_simps(4) smult_carrier_vec)

lemma dim_vec_lincomb [simp]:
  assumes "finite F" and "f: F \<rightarrow> UNIV" and "F \<subseteq> carrier_vec n"
  shows "dim_vec (module.lincomb (module_cpx_vec n) f F) = n"
  using assms
proof(induct F)
  case empty
  show "dim_vec (module.lincomb (module_cpx_vec n) f {}) = n"
  proof -
    have "module.lincomb (module_cpx_vec n) f {} = 0\<^sub>v n"
      using module.lincomb_def abelian_monoid.finsum_empty module_cpx_vec_def vecspace_cpx_vec vectorspace_def
      by (smt abelian_group_def Module.module_def module_vec_simps(2))
    thus ?thesis by simp
  qed
next
  case (insert x F)
  hence "module.lincomb (module_cpx_vec n) f (insert x F) = 
    (f x \<cdot>\<^sub>v x) \<oplus>\<^bsub>module_cpx_vec n\<^esub> module.lincomb (module_cpx_vec n) f F"
    using module_cpx_vec_def module_vec_def module_cpx_vec module.lincomb_insert cpx_rng_def insert_subset
    by (smt Pi_I' UNIV_I Un_insert_right module_vec_simps(4) partial_object.select_convs(1) sup_bot.comm_neutral)
  hence "dim_vec (module.lincomb (module_cpx_vec n) f (insert x F)) = 
    dim_vec (module.lincomb (module_cpx_vec n) f F)"
    using index_add_vec by (simp add: module_cpx_vec_def module_vec_simps(1))
  thus "dim_vec (module.lincomb (module_cpx_vec n) f (insert x F)) = n"
    using insert.hyps(3) insert.prems(2) by simp
qed

lemma lincomb_vec_index [simp]:
  assumes "finite F" and a2:"i < n" and "F \<subseteq> carrier_vec n" and "f: F \<rightarrow> UNIV"
  shows "module.lincomb (module_cpx_vec n) f F $ i = (\<Sum>v\<in>F. f v * (v $ i))"
  using assms
proof(induct F)
  case empty
  then show "module.lincomb (module_cpx_vec n) f {} $ i = (\<Sum>v\<in>{}. f v * v $ i)"
    apply auto
    using a2 module.lincomb_def abelian_monoid.finsum_empty module_cpx_vec_def
    by (metis (mono_tags) abelian_group_def index_zero_vec(1) module_cpx_vec Module.module_def module_vec_simps(2))
next
  case(insert x F)
  have "module.lincomb (module_cpx_vec n) f (insert x F) = 
      f x \<cdot>\<^sub>v x \<oplus>\<^bsub>module_cpx_vec n\<^esub> module.lincomb (module_cpx_vec n) f F"
    using module.lincomb_insert module_cpx_vec insert.hyps(1) module_cpx_vec_def module_vec_def
      insert.prems(2) insert.hyps(2) insert.prems(3) insert_def
    by (smt Pi_I' UNIV_I Un_insert_right cpx_rng_def insert_subset module_vec_simps(4) 
        partial_object.select_convs(1) sup_bot.comm_neutral)
  then have "module.lincomb (module_cpx_vec n) f (insert x F) $ i = 
      (f x \<cdot>\<^sub>v x) $ i + module.lincomb (module_cpx_vec n) f F $ i"
    using index_add_vec(1) a2 dim_vec_lincomb
    by (metis Pi_split_insert_domain  insert.hyps(1) insert.prems(2) insert.prems(3) insert_subset 
        module_cpx_vec_def module_vec_simps(1))
  hence "module.lincomb (module_cpx_vec n) f (insert x F) $ i = f x * x $ i + (\<Sum>v\<in>F. f v * v $ i)"
    using index_smult_vec a2 insert.prems(2) insert_def insert.hyps(3) by auto
  with insert show "module.lincomb (module_cpx_vec n) f (insert x F) $ i = (\<Sum>v\<in>insert x F. f v * v $ i)"
    by auto
qed

lemma unit_vectors_is_lin_indpt [simp]:
  "module.lin_indpt cpx_rng (module_cpx_vec n) (unit_vectors n)"
proof
  assume "module.lin_dep cpx_rng (module_cpx_vec n) (unit_vectors n)"
  hence "\<exists>A a v. (finite A \<and> A \<subseteq> (unit_vectors n) \<and> (a \<in> A \<rightarrow> UNIV) \<and> 
    (module.lincomb (module_cpx_vec n) a A = \<zero>\<^bsub>module_cpx_vec n\<^esub>) \<and> (v \<in> A) \<and> (a v \<noteq> \<zero>\<^bsub>cpx_rng\<^esub>))"
    using module.lin_dep_def cpx_rng_def module_cpx_vec by (smt Pi_UNIV UNIV_I)
  moreover obtain A and a and v where f1:"finite A" and f2:"A \<subseteq> (unit_vectors n)" and "a \<in> A \<rightarrow> UNIV" 
    and f4:"module.lincomb (module_cpx_vec n) a A = \<zero>\<^bsub>module_cpx_vec n\<^esub>" and f5:"v \<in> A" and 
    f6:"a v \<noteq> \<zero>\<^bsub>cpx_rng\<^esub>"
    using calculation by blast
  moreover obtain i where f7:"v = unit_vec n i" and f8:"i < n"
    using unit_vectors_def calculation by auto
  ultimately have f9:"module.lincomb (module_cpx_vec n) a A $ i = (\<Sum>u\<in>A. a u * (u $ i))"
    using lincomb_vec_index 
    by (smt carrier_dim_vec index_unit_vec(3) mem_Collect_eq subset_iff sum.cong unit_vectors_def)
  moreover have "\<forall>u\<in>A.\<forall>j<n. u = unit_vec n j \<longrightarrow> j \<noteq> i \<longrightarrow> a u * (u $ i) = 0"
    using unit_vectors_def index_unit_vec by (simp add: f8)
  then have "(\<Sum>u\<in>A. a u * (u $ i)) = (\<Sum>u\<in>A. if u=v then a v * v $ i else 0)"
    using f2 unit_vectors_def f7 by (smt mem_Collect_eq subsetCE sum.cong)
  also have "\<dots> = a v * (v $ i)"
    using abelian_monoid.finsum_singleton[of cpx_rng v A "\<lambda>u\<in>A. a u * (u $ i)"] cpx_abelian_monoid
      f5 f1 cpx_rng_def by simp
  also have "\<dots> = a v"
    using f7 index_unit_vec f8 by simp
  also have "\<dots> \<noteq> 0"
    using f6 by (simp add: cpx_rng_def)
  finally show False
    using f4 module_cpx_vec_def module_vec_def index_zero_vec f8 f9 by (simp add: module_vec_simps(2))
qed

lemma unit_vectors_is_genset [simp]:
  "module.gen_set cpx_rng (module_cpx_vec n) (unit_vectors n)"
proof
  show "module.span cpx_rng (module_cpx_vec n) (unit_vectors n) \<subseteq> carrier (module_cpx_vec n)"
    using module.span_def dim_vec_lincomb carrier_vec_def cpx_rng_def
    by (smt Collect_mono index_unit_vec(3) module.span_is_subset2 module_cpx_vec module_cpx_vec_def 
        module_vec_simps(3) unit_vectors_def)
next
  show "carrier (module_cpx_vec n) \<subseteq> module.span cpx_rng (module_cpx_vec n) (unit_vectors n)"
  proof
    fix v
    assume a1:"v \<in> carrier (module_cpx_vec n)"
    define A a lc where "A = {unit_vec n i ::complex vec| i::nat. i < n \<and> v $ i \<noteq> 0}" and 
      "a = (\<lambda>u\<in>A. u \<bullet> v)" and "lc = module.lincomb (module_cpx_vec n) a A"
    then have f1:"finite A" by simp
    have f2:"A \<subseteq> carrier_vec n"
      using carrier_vec_def A_def by auto
    have f3:"a \<in> A \<rightarrow> UNIV"
      using a_def by simp
    then have f4:"dim_vec v = dim_vec lc"
      using f1 f2 f3 a1 module_cpx_vec_def dim_vec_lincomb lc_def by (simp add: module_vec_simps(3))
    then have f5:"i < n \<Longrightarrow> lc $ i = (\<Sum>u\<in>A. u \<bullet> v * u $ i)" for i
      using lincomb_vec_index lc_def a_def f1 f2 f3 by simp
    then have "i < n \<Longrightarrow> j < n \<Longrightarrow> j \<noteq> i \<Longrightarrow> unit_vec n j \<bullet> v * unit_vec n j $ i = 0" for i j by simp
    then have "i < n \<Longrightarrow> lc $ i = (\<Sum>u\<in>A. if u = unit_vec n i then v $ i else 0)" for i
      using a1 A_def f5 scalar_prod_left_unit
      by (smt f4 carrier_vecI dim_vec_lincomb f1 f2 f3 index_unit_vec(2) lc_def 
          mem_Collect_eq mult.right_neutral sum.cong)
    then have "i < n \<Longrightarrow> lc $ i = v $ i" for i
      using abelian_monoid.finsum_singleton[of cpx_rng i] A_def cpx_rng_def by simp
    then have f6:"v = lc"
      using eq_vecI f4 dim_vec_lincomb f1 f2 lc_def by auto
    have "A \<subseteq> unit_vectors n"
      using A_def unit_vectors_def by auto
    thus "v \<in> module.span cpx_rng (module_cpx_vec n) (unit_vectors n)"
      using f6 module.span_def[of cpx_rng "module_cpx_vec n"] lc_def f1 f2 cpx_rng_def module_cpx_vec
      by (smt Pi_I' UNIV_I mem_Collect_eq partial_object.select_convs(1))
  qed
qed
    
lemma unit_vectors_is_basis [simp]:
  "vectorspace.basis cpx_rng (module_cpx_vec n) (unit_vectors n)"
proof -
  fix n
  have "unit_vectors n \<subseteq> carrier (module_cpx_vec n)"
    using unit_vectors_def module_cpx_vec_def module_vec_simps(3) by fastforce
  then show ?thesis
    using vectorspace.basis_def unit_vectors_is_lin_indpt unit_vectors_is_genset vecspace_cpx_vec
    by(smt carrier_dim_vec index_unit_vec(3) mem_Collect_eq module_cpx_vec_def module_vec_simps(3) 
        subsetI unit_vectors_def)
qed

lemma state_qbit_is_lincomb [simp]:
  "state_qbit n = 
  {module.lincomb (module_cpx_vec (2^n)) a A|a A. 
    finite A \<and> A\<subseteq>(unit_vectors (2^n)) \<and> a\<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2^n)) a A\<parallel> = 1}"
proof
  show "state_qbit n
    \<subseteq> {module.lincomb (module_cpx_vec (2^n)) a A |a A.
        finite A \<and> A \<subseteq> unit_vectors (2^n) \<and> a \<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2^n)) a A\<parallel> = 1}"
  proof
    fix v
    assume a1:"v \<in> state_qbit n"
    then show "v \<in> {module.lincomb (module_cpx_vec (2^n)) a A |a A.
               finite A \<and> A \<subseteq> unit_vectors (2^n) \<and> a \<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2^n)) a A\<parallel> = 1}"
    proof -
      obtain a and A where "finite A" and "a\<in> A \<rightarrow> UNIV" and "A \<subseteq> unit_vectors (2^n)" and 
        "v = module.lincomb (module_cpx_vec (2^n)) a A"
        using a1 state_qbit_def unit_vectors_is_basis vectorspace.basis_def module.span_def 
        vecspace_cpx_vec module_cpx_vec module_cpx_vec_def module_vec_def carrier_vec_def
        by(smt Pi_UNIV UNIV_I mem_Collect_eq module_vec_simps(3))
      thus ?thesis
        using a1 state_qbit_def by auto
    qed
  qed
  show "{module.lincomb (module_cpx_vec (2 ^ n)) a A |a A.
     finite A \<and> A \<subseteq> unit_vectors (2 ^ n) \<and> a \<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2 ^ n)) a A\<parallel> = 1}
    \<subseteq> state_qbit n"
  proof
    fix v
    assume "v \<in> {module.lincomb (module_cpx_vec (2 ^ n)) a A |a A.
              finite A \<and> A \<subseteq> unit_vectors (2 ^ n) \<and> a \<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2 ^ n)) a A\<parallel> = 1}"
    then show "v \<in> state_qbit n"
      using state_qbit_def dim_vec_lincomb unit_vectors_carrier_vec by(smt mem_Collect_eq order_trans)
  qed
qed

end