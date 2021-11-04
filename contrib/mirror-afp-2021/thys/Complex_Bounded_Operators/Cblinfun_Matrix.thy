section \<open>\<open>Cblinfun_Matrix\<close> -- Matrix representation of bounded operators\<close>

theory Cblinfun_Matrix
  imports
    Complex_L2

    "Jordan_Normal_Form.Gram_Schmidt"
    "HOL-Analysis.Starlike"
    "Complex_Bounded_Operators.Extra_Jordan_Normal_Form"
begin

hide_const (open) Order.bottom Order.top
hide_type (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_fact (open) Finite_Cartesian_Product.mat_def
hide_const (open) Finite_Cartesian_Product.vec
hide_fact (open) Finite_Cartesian_Product.vec_def
hide_const (open) Finite_Cartesian_Product.row
hide_fact (open) Finite_Cartesian_Product.row_def
no_notation Finite_Cartesian_Product.vec_nth (infixl "$" 90)

unbundle jnf_notation
unbundle cblinfun_notation

subsection \<open>Isomorphism between vectors\<close>

text \<open>We define the canonical isomorphism between vectors in some complex vector space \<^typ>\<open>'a::basis_enum\<close> and the
  complex \<^term>\<open>n\<close>-dimensional vectors (where \<^term>\<open>n\<close> is the dimension of \<^typ>\<open>'a\<close>).
  This is possible if \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close> are of class \<^class>\<open>basis_enum\<close>
  since that class fixes a finite canonical basis. Vector are represented using
  the \<^typ>\<open>complex vec\<close> type from \<^session>\<open>Jordan_Normal_Form\<close>.
  (The isomorphism will be called \<^term>\<open>vec_of_onb_enum\<close> below.)\<close>

definition vec_of_basis_enum :: \<open>'a::basis_enum \<Rightarrow> complex vec\<close> where
  \<comment> \<open>Maps \<^term>\<open>v\<close> to a \<^typ>\<open>'a vec\<close> represented in basis \<^const>\<open>canonical_basis\<close>\<close>
  \<open>vec_of_basis_enum v = vec_of_list (map (crepresentation (set canonical_basis) v) canonical_basis)\<close>

lemma dim_vec_of_basis_enum'[simp]:
  \<open>dim_vec (vec_of_basis_enum (v::'a)) = length (canonical_basis::'a::basis_enum list)\<close>
  unfolding vec_of_basis_enum_def 
  by simp  


definition basis_enum_of_vec :: \<open>complex vec \<Rightarrow> 'a::basis_enum\<close> where
  \<open>basis_enum_of_vec v = 
    (if dim_vec v = length (canonical_basis :: 'a list)
     then sum_list (map2 (*\<^sub>C) (list_of_vec v) (canonical_basis::'a list))
     else 0)\<close>

lemma vec_of_basis_enum_inverse[simp]:
  fixes w::"'a::basis_enum"
  shows  "basis_enum_of_vec (vec_of_basis_enum w) = w"
  unfolding vec_of_basis_enum_def basis_enum_of_vec_def 
  unfolding list_vec zip_map1 zip_same_conv_map map_map 
  apply (simp add: o_def)
  apply (subst sum.distinct_set_conv_list[symmetric], simp)
  apply (rule complex_vector.sum_representation_eq)
  using  is_generator_set by auto

lemma basis_enum_of_vec_inverse[simp]:
  fixes v::"complex vec"
  defines "n \<equiv> length (canonical_basis :: 'a::basis_enum list)"
  assumes f1: "dim_vec v = n"
  shows "vec_of_basis_enum ((basis_enum_of_vec v)::'a) = v"
proof (rule eq_vecI)
  show \<open>dim_vec (vec_of_basis_enum (basis_enum_of_vec v :: 'a)) = dim_vec v\<close>
    by (auto simp: vec_of_basis_enum_def f1 n_def)
next
  fix j assume j_v: \<open>j < dim_vec v\<close> 
  define w where "w = list_of_vec v"
  define basis where "basis = (canonical_basis::'a list)"
  have [simp]: "length w = n" "length basis = n" \<open>dim_vec v = n\<close> \<open>length (canonical_basis::'a list) = n\<close>
    \<open>j < n\<close>
    using j_v by (auto simp: f1 basis_def w_def n_def)
  have [simp]: \<open>cindependent (set basis)\<close> \<open>cspan (set basis) = UNIV\<close>
    by (auto simp: basis_def is_cindependent_set is_generator_set)

  have \<open>vec_of_basis_enum ((basis_enum_of_vec v)::'a) $ j
       = map (crepresentation (set basis) (sum_list (map2 (*\<^sub>C) w basis))) basis ! j\<close>
    by (auto simp: vec_of_list_index vec_of_basis_enum_def basis_enum_of_vec_def simp flip: w_def basis_def)
  also have \<open>\<dots> = crepresentation (set basis) (sum_list (map2 (*\<^sub>C) w basis)) (basis!j)\<close>
    by simp
  also have \<open>\<dots> = crepresentation (set basis) (\<Sum>i<n. (w!i) *\<^sub>C (basis!i)) (basis!j)\<close>
    by (auto simp: sum_list_sum_nth atLeast0LessThan)
  also have \<open>\<dots> = (\<Sum>i<n. (w!i) *\<^sub>C crepresentation (set basis) (basis!i) (basis!j))\<close>
    by (auto simp: complex_vector.representation_sum complex_vector.representation_scale)
  also have \<open>\<dots> = w!j\<close>
    apply (subst sum_single[where i=j])
      apply (auto simp: complex_vector.representation_basis)
    using \<open>j < n\<close> \<open>length basis = n\<close> basis_def distinct_canonical_basis nth_eq_iff_index_eq by blast
  also have \<open>\<dots> = v $ j\<close>
    by (simp add: w_def)
  finally show \<open>vec_of_basis_enum (basis_enum_of_vec v :: 'a) $ j = v $ j\<close>
    by -
qed

lemma basis_enum_eq_vec_of_basis_enumI:
  fixes a b :: "_::basis_enum"
  assumes "vec_of_basis_enum a = vec_of_basis_enum b"
  shows "a = b"
  by (metis assms vec_of_basis_enum_inverse)

subsection \<open>Operations on vectors\<close>


lemma basis_enum_of_vec_add:
  assumes [simp]: \<open>dim_vec v1 = length (canonical_basis :: 'a::basis_enum list)\<close> 
    \<open>dim_vec v2 = length (canonical_basis :: 'a list)\<close>
  shows \<open>((basis_enum_of_vec (v1 + v2)) :: 'a) = basis_enum_of_vec v1 + basis_enum_of_vec v2\<close>
proof -
  have \<open>length (list_of_vec v1) = length (list_of_vec v2)\<close> and \<open>length (list_of_vec v2) = length (canonical_basis :: 'a list)\<close>
    by simp_all
  then have \<open>sum_list (map2 (*\<^sub>C) (map2 (+) (list_of_vec v1) (list_of_vec v2)) (canonical_basis::'a list))
    = sum_list (map2 (*\<^sub>C) (list_of_vec v1) canonical_basis) + sum_list (map2 (*\<^sub>C) (list_of_vec v2) canonical_basis)\<close>
    apply (induction rule: list_induct3)
    by (auto simp: scaleC_add_left)
  then show ?thesis
    using assms by (auto simp: basis_enum_of_vec_def list_of_vec_plus)
qed

lemma basis_enum_of_vec_mult:
  assumes [simp]: \<open>dim_vec v = length (canonical_basis :: 'a::basis_enum list)\<close> 
  shows \<open>((basis_enum_of_vec (c \<cdot>\<^sub>v v)) :: 'a) =  c *\<^sub>C basis_enum_of_vec v\<close>
proof -
  have *: \<open>monoid_add_hom ((*\<^sub>C) c :: 'a \<Rightarrow> _)\<close>
    by (simp add: monoid_add_hom_def plus_hom.intro scaleC_add_right semigroup_add_hom.intro zero_hom.intro)
  show ?thesis
    apply (auto simp: basis_enum_of_vec_def list_of_vec_mult map_zip_map
        monoid_add_hom.hom_sum_list[OF *])
    by (metis case_prod_unfold comp_apply scaleC_scaleC)
qed


lemma vec_of_basis_enum_add:
  "vec_of_basis_enum (b1 + b2) = vec_of_basis_enum b1 + vec_of_basis_enum b2"
  by (auto simp: vec_of_basis_enum_def complex_vector.representation_add)

lemma vec_of_basis_enum_scaleC:
  "vec_of_basis_enum (c *\<^sub>C b) = c \<cdot>\<^sub>v (vec_of_basis_enum b)"
  by (auto simp: vec_of_basis_enum_def complex_vector.representation_scale)

lemma vec_of_basis_enum_scaleR:
  "vec_of_basis_enum (r *\<^sub>R b) = complex_of_real r \<cdot>\<^sub>v (vec_of_basis_enum b)"
  by (simp add: scaleR_scaleC vec_of_basis_enum_scaleC)

lemma vec_of_basis_enum_uminus:
  "vec_of_basis_enum (- b2) = - vec_of_basis_enum b2"
  unfolding scaleC_minus1_left[symmetric, of b2]
  unfolding scaleC_minus1_left_vec[symmetric]
  by (rule vec_of_basis_enum_scaleC)


lemma vec_of_basis_enum_minus:
  "vec_of_basis_enum (b1 - b2) = vec_of_basis_enum b1 - vec_of_basis_enum b2"
  by (metis (mono_tags, hide_lams) carrier_vec_dim_vec diff_conv_add_uminus diff_zero index_add_vec(2) minus_add_uminus_vec vec_of_basis_enum_add vec_of_basis_enum_uminus)

lemma cinner_basis_enum_of_vec:
  defines "n \<equiv> length (canonical_basis :: 'a::onb_enum list)"
  assumes [simp]: "dim_vec x = n" "dim_vec y = n"
  shows  "\<langle>basis_enum_of_vec x :: 'a, basis_enum_of_vec y\<rangle> = y \<bullet>c x"
proof -
  have \<open>\<langle>basis_enum_of_vec x :: 'a, basis_enum_of_vec y\<rangle>
    = (\<Sum>i<n. x$i *\<^sub>C canonical_basis ! i :: 'a) \<bullet>\<^sub>C (\<Sum>i<n. y$i *\<^sub>C canonical_basis ! i)\<close>
    by (auto simp: basis_enum_of_vec_def sum_list_sum_nth atLeast0LessThan simp flip: n_def)
  also have \<open>\<dots> = (\<Sum>i<n. \<Sum>j<n. cnj (x$i) *\<^sub>C y$j *\<^sub>C ((canonical_basis ! i :: 'a) \<bullet>\<^sub>C (canonical_basis ! j)))\<close>
    apply (subst cinner_sum_left)
    apply (subst cinner_sum_right)
    by (auto simp: mult_ac)
  also have \<open>\<dots> = (\<Sum>i<n. \<Sum>j<n. cnj (x$i) *\<^sub>C y$j *\<^sub>C (if i=j then 1 else 0))\<close>
    apply (rule sum.cong[OF refl])
    apply (rule sum.cong[OF refl])
    by (auto simp: cinner_canonical_basis n_def)
  also have \<open>\<dots> = (\<Sum>i<n. cnj (x$i) *\<^sub>C y$i)\<close>
    apply (rule sum.cong[OF refl])
    apply (subst sum_single)
    by auto
  also have \<open>\<dots> = y \<bullet>c x\<close>
    by (smt (z3) assms(2) complex_scaleC_def conjugate_complex_def dim_vec_conjugate lessThan_atLeast0 lessThan_iff mult.commute scalar_prod_def sum.cong vec_index_conjugate)
  finally show ?thesis
    by -
qed

lemma cscalar_prod_vec_of_basis_enum: "cscalar_prod (vec_of_basis_enum \<phi>) (vec_of_basis_enum \<psi>) = cinner \<psi> \<phi>"
  for \<psi> :: "'a::onb_enum"
  apply (subst cinner_basis_enum_of_vec[symmetric, where 'a='a])
  by simp_all

lemma norm_ell2_vec_of_basis_enum: "norm \<psi> =
  (let \<psi>' = vec_of_basis_enum \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  (is "_ = ?rhs") for \<psi> :: "'a::onb_enum"
proof -
  have "norm \<psi> = sqrt (cmod (\<Sum>i = 0..<dim_vec (vec_of_basis_enum \<psi>). 
            vec_of_basis_enum \<psi> $ i * conjugate (vec_of_basis_enum \<psi>) $ i))"
    unfolding norm_eq_sqrt_cinner[where 'a='a] cscalar_prod_vec_of_basis_enum[symmetric] scalar_prod_def dim_vec_conjugate
    by rule
  also have "\<dots> = sqrt (cmod (\<Sum>x = 0..<dim_vec (vec_of_basis_enum \<psi>). 
                    let z = vec_of_basis_enum \<psi> $ x in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
    apply (subst sum.cong, rule refl)
     apply (subst vec_index_conjugate)
    by (auto simp: Let_def complex_mult_cnj)
  also have "\<dots> = ?rhs"
    unfolding Let_def norm_of_real
    apply (subst abs_of_nonneg)
     apply (rule sum_nonneg)
    by auto
  finally show ?thesis
    by -
qed

lemma basis_enum_of_vec_unit_vec:
  defines "basis \<equiv> (canonical_basis::'a::basis_enum list)"
    and "n \<equiv> length (canonical_basis :: 'a list)"
  assumes a3: "i < n"  
  shows "basis_enum_of_vec (unit_vec n i) = basis!i"
proof-
  define L::"complex list" where "L = list_of_vec (unit_vec n i)"
  define I::"nat list" where "I = [0..<n]"
  have "length L = n"
    by (simp add: L_def)    
  moreover have "length basis = n"
    by (simp add: basis_def n_def)
  ultimately have "map2 (*\<^sub>C) L basis = map (\<lambda>j. L!j *\<^sub>C basis!j) I"
    by (simp add: I_def list_eq_iff_nth_eq)  
  hence "sum_list (map2 (*\<^sub>C) L basis) = sum_list (map (\<lambda>j. L!j *\<^sub>C basis!j) I)"
    by simp
  also have "\<dots> = sum (\<lambda>j. L!j *\<^sub>C basis!j) {0..n-1}"
  proof-
    have "set I = {0..n-1}"
      using I_def a3 by auto      
    thus ?thesis 
      using Groups_List.sum_code[where xs = I and g = "(\<lambda>j. L!j *\<^sub>C basis!j)"]
      by (simp add: I_def)      
  qed
  also have "\<dots> = sum (\<lambda>j. (list_of_vec (unit_vec n i))!j *\<^sub>C basis!j) {0..n-1}"
    unfolding L_def by blast
  finally have "sum_list (map2 (*\<^sub>C) (list_of_vec (unit_vec n i)) basis)
       = sum (\<lambda>j. (list_of_vec (unit_vec n i))!j *\<^sub>C basis!j) {0..n-1}"
    using L_def by blast    
  also have "\<dots> = basis ! i"
  proof-
    have "(\<Sum>j = 0..n - 1. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j) =
          (\<Sum>j \<in> {0..n - 1}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)"
      by simp
    also have "\<dots> = list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i
               + (\<Sum>j \<in> {0..n - 1}-{i}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)"
    proof-
      define a where "a j = list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j" for j
      define S where "S = {0..n - 1}"
      have "finite S"
        by (simp add: S_def)        
      hence "(\<Sum>j \<in> insert i S. a j) = a i + (\<Sum>j\<in>S-{i}. a j)"
        using Groups_Big.comm_monoid_add_class.sum.insert_remove
        by auto
      moreover have "S-{i} = {0..n-1}-{i}"
        unfolding S_def
        by blast 
      moreover have "insert i S = {0..n-1}"
        using S_def Suc_diff_1 a3 atLeastAtMost_iff diff_is_0_eq' le_SucE le_numeral_extra(4) 
          less_imp_le not_gr_zero
        by fastforce 
      ultimately show ?thesis
        using \<open>a \<equiv> \<lambda>j. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j\<close>
        by simp 
    qed
    also have "\<dots> = list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i"
    proof-
      have "j \<in> {0..n - 1}-{i} \<Longrightarrow> list_of_vec (unit_vec n i) ! j = 0"
        for j
        using a3 atMost_atLeast0 atMost_iff diff_Suc_less index_unit_vec(1) le_less_trans 
          list_of_vec_index member_remove zero_le by fastforce         
      hence "j \<in> {0..n - 1}-{i} \<Longrightarrow> list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j = 0"
        for j
        by auto         
      hence "(\<Sum>j \<in> {0..n - 1}-{i}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j) = 0"
        by (simp add: \<open>\<And>j. j \<in> {0..n - 1} - {i} \<Longrightarrow> list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j = 0\<close>)        
      thus ?thesis by simp
    qed
    also have "\<dots> = basis ! i"
      by (simp add: a3)      
    finally show ?thesis
      using \<open>(\<Sum>j = 0..n - 1. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)
             = list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i + (\<Sum>j\<in>{0..n - 1} - {i}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)\<close>
        \<open>list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i + (\<Sum>j\<in>{0..n - 1} - {i}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)
           = list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i\<close>
        \<open>list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i = basis ! i\<close> 
      by auto 
  qed
  finally have "sum_list (map2 (*\<^sub>C) (list_of_vec (unit_vec n i)) basis)
      = basis ! i"
    by (simp add: assms)    
  hence "sum_list (map2 scaleC (list_of_vec (unit_vec n i)) (canonical_basis::'a list))
      = (canonical_basis::'a list) ! i"     
    by (simp add: assms)
  thus ?thesis 
    unfolding basis_enum_of_vec_def
    by (simp add: assms) 
qed


lemma vec_of_basis_enum_ket:
  "vec_of_basis_enum (ket i) = unit_vec (CARD('a)) (enum_idx i)" 
  for i::"'a::enum"
proof-
  have "dim_vec (vec_of_basis_enum (ket i)) 
      = dim_vec (unit_vec (CARD('a)) (enum_idx i))"
  proof-
    have "dim_vec (unit_vec (CARD('a)) (enum_idx i)) 
      = CARD('a)"
      by simp     
    moreover have "dim_vec (vec_of_basis_enum (ket i)) = CARD('a)"
      unfolding vec_of_basis_enum_def vec_of_basis_enum_def by auto
    ultimately show ?thesis by simp
  qed
  moreover have "vec_of_basis_enum (ket i) $ j =
    (unit_vec (CARD('a)) (enum_idx i)) $ j"
    if "j < dim_vec (vec_of_basis_enum (ket i))"
    for j
  proof-
    have j_bound: "j < length (canonical_basis::'a ell2 list)"
      by (metis dim_vec_of_basis_enum' that)
    have y1: "cindependent (set (canonical_basis::'a ell2 list))"
      using is_cindependent_set by blast
    have y2: "canonical_basis ! j \<in> set (canonical_basis::'a ell2 list)"
      using j_bound by auto
    have p1: "enum_class.enum ! enum_idx i = i"
      using enum_idx_correct by blast
    moreover have p2: "(canonical_basis::'a ell2 list) ! t  = ket ((enum_class.enum::'a list) ! t)"
      if "t < length (enum_class.enum::'a list)"
      for t
      unfolding canonical_basis_ell2_def 
      using that by auto
    moreover have p3: "enum_idx i < length (enum_class.enum::'a list)"
    proof-
      have "set (enum_class.enum::'a list) = UNIV"
        using UNIV_enum by blast
      hence "i \<in> set (enum_class.enum::'a list)"
        by blast
      thus ?thesis
        unfolding enum_idx_def
        by (metis index_of_bound length_greater_0_conv length_pos_if_in_set) 
    qed
    ultimately have p4: "(canonical_basis::'a ell2 list) ! (enum_idx i)  = ket i"
      by auto
    have "enum_idx i < length (enum_class.enum::'a list)"
      using p3
      by auto
    moreover have "length (enum_class.enum::'a list) = dim_vec (vec_of_basis_enum (ket i))"
      unfolding vec_of_basis_enum_def canonical_basis_ell2_def
      using dim_vec_of_basis_enum'[where v = "ket i"]
      unfolding canonical_basis_ell2_def by simp              
    ultimately have enum_i_dim_vec: "enum_idx i < dim_vec (unit_vec (CARD('a)) (enum_idx i))"
      using \<open>dim_vec (vec_of_basis_enum (ket i)) = dim_vec (unit_vec (CARD('a)) (enum_idx i))\<close> by auto            
    hence r1: "(unit_vec (CARD('a)) (enum_idx i)) $ j
        = (if enum_idx i = j then 1 else 0)"
      using \<open>dim_vec (vec_of_basis_enum (ket i)) = dim_vec (unit_vec (CARD('a)) (enum_idx i))\<close> that by auto
    moreover have "vec_of_basis_enum (ket i) $ j = (if enum_idx i = j then 1 else 0)"
    proof(cases "enum_idx i = j")
      case True                        
      have "crepresentation (set (canonical_basis::'a ell2 list)) 
          ((canonical_basis::'a ell2 list) ! j) ((canonical_basis::'a ell2 list) ! j) = 1"        
        using y1 y2 complex_vector.representation_basis[where 
            basis = "set (canonical_basis::'a ell2 list)" 
            and b = "(canonical_basis::'a ell2 list) ! j"]
        by smt

      hence "vec_of_basis_enum ((canonical_basis::'a ell2 list) ! j) $ j = 1"
        unfolding vec_of_basis_enum_def
        by (metis j_bound nth_map vec_of_list_index) 
      hence "vec_of_basis_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) 
            $ enum_idx i = 1"
        using True by simp
      hence "vec_of_basis_enum (ket i) $ enum_idx i = 1"
        using p4
        by simp
      thus ?thesis using True unfolding vec_of_basis_enum_def by auto
    next
      case False
      have "crepresentation (set (canonical_basis::'a ell2 list)) 
          ((canonical_basis::'a ell2 list) ! (enum_idx i)) ((canonical_basis::'a ell2 list) ! j) = 0"        
        using y1 y2 complex_vector.representation_basis[where 
            basis = "set (canonical_basis::'a ell2 list)" 
            and b = "(canonical_basis::'a ell2 list) ! j"]
        by (metis (mono_tags, hide_lams) False enum_i_dim_vec basis_enum_of_vec_inverse basis_enum_of_vec_unit_vec canonical_basis_length_ell2 index_unit_vec(3) j_bound list_of_vec_index list_vec nth_map r1 vec_of_basis_enum_def)
      hence "vec_of_basis_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) $ j = 0"
        unfolding vec_of_basis_enum_def by (smt j_bound nth_map vec_of_list_index)        
      hence "vec_of_basis_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) $ j = 0"
        by auto
      hence "vec_of_basis_enum (ket i) $ j = 0"
        using p4
        by simp
      thus ?thesis using False unfolding vec_of_basis_enum_def by simp
    qed
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis 
    using Matrix.eq_vecI
    by auto
qed

lemma vec_of_basis_enum_zero:
  defines "nA \<equiv> length (canonical_basis :: 'a::basis_enum list)" 
  shows "vec_of_basis_enum (0::'a) = 0\<^sub>v nA"
  by (metis assms carrier_vecI dim_vec_of_basis_enum' minus_cancel_vec right_minus_eq vec_of_basis_enum_minus)

lemma (in complex_vec_space) vec_of_basis_enum_cspan:
  fixes X :: "'a::basis_enum set"
  assumes "length (canonical_basis :: 'a list) = n"
  shows "vec_of_basis_enum ` cspan X = span (vec_of_basis_enum ` X)"
proof -
  have carrier: "vec_of_basis_enum ` X \<subseteq> carrier_vec n"
    by (metis assms carrier_vecI dim_vec_of_basis_enum' image_subsetI)
  have lincomb_sum: "lincomb c A = vec_of_basis_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)" 
    if B_def: "B = basis_enum_of_vec ` A" and \<open>finite A\<close>
      and AX: "A \<subseteq> vec_of_basis_enum ` X" and c'_def: "\<And>b. c' b = c (vec_of_basis_enum b)"
    for c c' A and B::"'a set"
    unfolding B_def using \<open>finite A\<close> AX
  proof induction
    case empty
    then show ?case
      by (simp add: assms vec_of_basis_enum_zero)
  next
    case (insert x F)
    then have IH: "lincomb c F = vec_of_basis_enum (\<Sum>b\<in>basis_enum_of_vec ` F. c' b *\<^sub>C b)"
      (is "_ = ?sum")
      by simp
    have xx: "vec_of_basis_enum (basis_enum_of_vec x :: 'a) = x"
      apply (rule basis_enum_of_vec_inverse)
      using assms carrier carrier_vecD insert.prems by auto
    have "lincomb c (insert x F) = c x \<cdot>\<^sub>v x + lincomb c F"
      apply (rule lincomb_insert2)
      using insert.hyps insert.prems carrier by auto
    also have "c x \<cdot>\<^sub>v x = vec_of_basis_enum (c' (basis_enum_of_vec x) *\<^sub>C (basis_enum_of_vec x :: 'a))"
      by (simp add: xx vec_of_basis_enum_scaleC c'_def)
    also note IH
    also have
      "vec_of_basis_enum (c' (basis_enum_of_vec x) *\<^sub>C (basis_enum_of_vec x :: 'a)) + ?sum
          = vec_of_basis_enum (\<Sum>b\<in>basis_enum_of_vec ` insert x F. c' b *\<^sub>C b)"
      apply simp apply (rule sym)
      apply (subst sum.insert)
      using \<open>finite F\<close> \<open>x \<notin> F\<close> dim_vec_of_basis_enum' insert.prems 
        vec_of_basis_enum_add c'_def by auto
    finally show ?case
      by -
  qed

  show ?thesis
  proof auto
    fix x assume "x \<in> local.span (vec_of_basis_enum ` X)"
    then obtain c A where xA: "x = lincomb c A" and "finite A" and AX: "A \<subseteq> vec_of_basis_enum ` X"
      unfolding span_def by auto
    define B::"'a set" and c' where "B = basis_enum_of_vec ` A"
      and "c' b = c (vec_of_basis_enum b)" for b::'a
    note xA
    also have "lincomb c A = vec_of_basis_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)"
      using B_def \<open>finite A\<close> AX c'_def by (rule lincomb_sum)
    also have "\<dots> \<in> vec_of_basis_enum ` cspan X"
      unfolding complex_vector.span_explicit
      apply (rule imageI) apply (rule CollectI)
      apply (rule exI) apply (rule exI)
      using \<open>finite A\<close> AX by (auto simp: B_def)
    finally show "x \<in> vec_of_basis_enum ` cspan X"
      by -
  next
    fix x assume "x \<in> cspan X" 
    then obtain c' B where x: "x = (\<Sum>b\<in>B. c' b *\<^sub>C b)" and "finite B" and BX: "B \<subseteq> X"
      unfolding complex_vector.span_explicit by auto
    define A and c where "A = vec_of_basis_enum ` B"
      and "c b = c' (basis_enum_of_vec b)" for b
    have "vec_of_basis_enum x = vec_of_basis_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)"
      using x by simp
    also have "\<dots> = lincomb c A"
      apply (rule lincomb_sum[symmetric])
      unfolding A_def c_def using BX \<open>finite B\<close>
      by (auto simp: image_image)
    also have "\<dots> \<in> span (vec_of_basis_enum ` X)"
      unfolding span_def apply (rule CollectI)
      apply (rule exI, rule exI)
      unfolding A_def using \<open>finite B\<close> BX by auto
    finally show "vec_of_basis_enum x \<in> local.span (vec_of_basis_enum ` X)"
      by -
  qed
qed

lemma (in complex_vec_space) basis_enum_of_vec_span:
  assumes "length (canonical_basis :: 'a list) = n"
  assumes "Y \<subseteq> carrier_vec n"
  shows "basis_enum_of_vec ` local.span Y = cspan (basis_enum_of_vec ` Y :: 'a::basis_enum set)"
proof -
  define X::"'a set" where "X = basis_enum_of_vec ` Y"
  then have "cspan (basis_enum_of_vec ` Y :: 'a set) = basis_enum_of_vec ` vec_of_basis_enum ` cspan X"
    by (simp add: image_image)
  also have "\<dots> = basis_enum_of_vec ` local.span (vec_of_basis_enum ` X)"
    apply (subst vec_of_basis_enum_cspan)
    using assms by simp_all
  also have "vec_of_basis_enum ` X = Y"
    unfolding X_def image_image
    apply (rule image_cong[where g=id and M=Y and N=Y, simplified])
    using assms(1) assms(2) by auto
  finally show ?thesis
    by simp
qed

lemma vec_of_basis_enum_canonical_basis:
  assumes "i < length (canonical_basis :: 'a list)"
  shows "vec_of_basis_enum (canonical_basis!i :: 'a)
       = unit_vec (length (canonical_basis :: 'a::basis_enum list)) i"
  by (metis assms basis_enum_of_vec_inverse basis_enum_of_vec_unit_vec index_unit_vec(3))

lemma vec_of_basis_enum_times: 
  fixes \<psi> \<phi> :: "'a::one_dim"
  shows "vec_of_basis_enum (\<psi> * \<phi>)
   = vec_of_list [vec_index (vec_of_basis_enum \<psi>) 0 * vec_index (vec_of_basis_enum \<phi>) 0]"
proof -
  have [simp]: \<open>crepresentation {1} x 1 = one_dim_iso x\<close> for x :: 'a
    apply (subst one_dim_scaleC_1[where x=x, symmetric])
    apply (subst complex_vector.representation_scale)
    by (auto simp add: complex_vector.span_base complex_vector.representation_basis)
  show ?thesis
    apply (rule eq_vecI)
    by (auto simp: vec_of_basis_enum_def)
qed

lemma vec_of_basis_enum_to_inverse: 
  fixes \<psi> :: "'a::one_dim"
  shows "vec_of_basis_enum (inverse \<psi>) = vec_of_list [inverse (vec_index (vec_of_basis_enum \<psi>) 0)]"
proof -
  have [simp]: \<open>crepresentation {1} x 1 = one_dim_iso x\<close> for x :: 'a
    apply (subst one_dim_scaleC_1[where x=x, symmetric])
    apply (subst complex_vector.representation_scale)
    by (auto simp add: complex_vector.span_base complex_vector.representation_basis)
  show ?thesis
    apply (rule eq_vecI)
     apply (auto simp: vec_of_basis_enum_def)
    by (metis complex_vector.scale_cancel_right one_dim_inverse one_dim_scaleC_1 zero_neq_one)
qed

lemma vec_of_basis_enum_divide: 
  fixes \<psi> \<phi> :: "'a::one_dim"
  shows "vec_of_basis_enum (\<psi> / \<phi>)
   = vec_of_list [vec_index (vec_of_basis_enum \<psi>) 0 / vec_index (vec_of_basis_enum \<phi>) 0]"
  by (simp add: divide_inverse vec_of_basis_enum_to_inverse vec_of_basis_enum_times)

lemma vec_of_basis_enum_1: "vec_of_basis_enum (1 :: 'a::one_dim) = vec_of_list [1]"
proof -
  have [simp]: \<open>crepresentation {1} x 1 = one_dim_iso x\<close> for x :: 'a
    apply (subst one_dim_scaleC_1[where x=x, symmetric])
    apply (subst complex_vector.representation_scale)
    by (auto simp add: complex_vector.span_base complex_vector.representation_basis)
  show ?thesis
    apply (rule eq_vecI)
    by (auto simp: vec_of_basis_enum_def)
qed

lemma vec_of_basis_enum_ell2_component:
  fixes \<psi> :: \<open>'a::enum ell2\<close> 
  assumes [simp]: \<open>i < CARD('a)\<close>
  shows \<open>vec_of_basis_enum \<psi> $ i = Rep_ell2 \<psi> (Enum.enum ! i)\<close>
proof -
  let ?i = \<open>Enum.enum ! i\<close>
  have \<open>Rep_ell2 \<psi> (Enum.enum ! i) = \<langle>ket ?i, \<psi>\<rangle>\<close>
    by (simp add: cinner_ket_left)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> \<bullet>c vec_of_basis_enum (ket ?i :: 'a ell2)\<close>
    by (rule cscalar_prod_vec_of_basis_enum[symmetric])
  also have \<open>\<dots> = vec_of_basis_enum \<psi> \<bullet>c unit_vec (CARD('a)) i\<close>
    by (simp add: vec_of_basis_enum_ket enum_idx_enum)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> \<bullet> unit_vec (CARD('a)) i\<close>
    by (smt (verit, best) assms carrier_vecI conjugate_conjugate_sprod conjugate_id conjugate_vec_sprod_comm dim_vec_conjugate eq_vecI index_unit_vec(3) scalar_prod_left_unit vec_index_conjugate)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> $ i\<close>
    by simp
  finally show ?thesis
    by simp
qed


lemma corthogonal_vec_of_basis_enum:
  fixes S :: "'a::onb_enum list"
  shows "corthogonal (map vec_of_basis_enum S) \<longleftrightarrow> is_ortho_set (set S) \<and> distinct S"
proof auto
  assume assm: \<open>corthogonal (map vec_of_basis_enum S)\<close>
  then show \<open>is_ortho_set (set S)\<close>
    by (smt (verit, ccfv_SIG) cinner_eq_zero_iff corthogonal_def cscalar_prod_vec_of_basis_enum in_set_conv_nth is_ortho_set_def length_map nth_map)
  show \<open>distinct S\<close>
    using assm corthogonal_distinct distinct_map by blast 
next
  assume \<open>is_ortho_set (set S)\<close> and \<open>distinct S\<close>
  then show \<open>corthogonal (map vec_of_basis_enum S)\<close>
    by (smt (verit, ccfv_threshold) cinner_eq_zero_iff corthogonalI cscalar_prod_vec_of_basis_enum is_ortho_set_def length_map length_map nth_eq_iff_index_eq nth_map nth_map nth_mem nth_mem)
qed

subsection \<open>Isomorphism between bounded linear functions and matrices\<close>


text \<open>We define the canonical isomorphism between \<^typ>\<open>'a::basis_enum \<Rightarrow>\<^sub>C\<^sub>L'b::basis_enum\<close>
  and the complex \<^term>\<open>n*m\<close>-matrices (where n,m are the dimensions of \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close>, 
  respectively). This is possible if \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close> are of class \<^class>\<open>basis_enum\<close>
  since that class fixes a finite canonical basis. Matrices are represented using
  the \<^typ>\<open>complex mat\<close> type from \<^session>\<open>Jordan_Normal_Form\<close>.
  (The isomorphism will be called \<^term>\<open>mat_of_cblinfun\<close> below.)\<close>

definition mat_of_cblinfun :: \<open>'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'b::{basis_enum,complex_normed_vector} \<Rightarrow> complex mat\<close> where
  \<open>mat_of_cblinfun f = 
    mat (length (canonical_basis :: 'b list)) (length (canonical_basis :: 'a list)) (
    \<lambda> (i, j). crepresentation (set (canonical_basis::'b list)) (f *\<^sub>V ((canonical_basis::'a list)!j)) ((canonical_basis::'b list)!i))\<close>
  for f

lift_definition cblinfun_of_mat :: \<open>complex mat \<Rightarrow> 'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'b::{basis_enum,complex_normed_vector}\<close> is  
  \<open>\<lambda>M. \<lambda>v. (if M\<in>carrier_mat (length (canonical_basis :: 'b list)) (length (canonical_basis :: 'a list))
           then basis_enum_of_vec (M *\<^sub>v vec_of_basis_enum v)
           else 0)\<close>
proof
  fix M :: "complex mat"
  define m where "m = length (canonical_basis :: 'b list)"
  define n where "n = length (canonical_basis :: 'a list)"
  define f::"complex mat \<Rightarrow> 'a \<Rightarrow> 'b" 
    where "f M v = (if M\<in>carrier_mat m n
        then basis_enum_of_vec (M *\<^sub>v vec_of_basis_enum (v::'a)) 
        else (0::'b))" 
    for M::"complex mat" and v::'a

  show add: \<open>f M (b1 + b2) = f M b1 + f M b2\<close> for b1 b2
    apply (auto simp: f_def)
    by (metis (mono_tags, lifting) carrier_matD(1) carrier_vec_dim_vec dim_mult_mat_vec dim_vec_of_basis_enum' m_def mult_add_distrib_mat_vec n_def basis_enum_of_vec_add vec_of_basis_enum_add)

  show scale: \<open>f M (c *\<^sub>C b) = c *\<^sub>C f M b\<close> for c b
    apply (auto simp: f_def)
    by (metis carrier_matD(1) carrier_vec_dim_vec dim_mult_mat_vec dim_vec_of_basis_enum' m_def mult_mat_vec n_def basis_enum_of_vec_mult vec_of_basis_enum_scaleC)

  from add scale have \<open>clinear (f M)\<close>
    by (simp add: clinear_iff)

  show \<open>\<exists>K. \<forall>b. norm (f M b) \<le> norm b * K\<close>
  proof (cases "M\<in>carrier_mat m n")
    case True
    have f_def': "f M v = basis_enum_of_vec (M *\<^sub>v (vec_of_basis_enum v))" for v
      using True f_def 
        m_def n_def by auto      
    have M_carrier_mat: 
      "M \<in> carrier_mat m n"
      by (simp add: True)
    have "bounded_clinear (f M)"
      apply (rule bounded_clinear_finite_dim) using \<open>clinear (f M)\<close> by auto
    thus ?thesis
      by (simp add: bounded_clinear.bounded) 
  next
    case False
    thus ?thesis
      unfolding f_def m_def n_def
      by (metis (full_types) order_refl mult_eq_0_iff norm_eq_zero)
  qed
qed

lemma mat_of_cblinfun_ell2_carrier[simp]: \<open>mat_of_cblinfun (a::'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2) \<in> carrier_mat CARD('b) CARD('a)\<close>
  by (simp add: mat_of_cblinfun_def)

lemma dim_row_mat_of_cblinfun[simp]: \<open>dim_row (mat_of_cblinfun (a::'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2)) = CARD('b)\<close>
  by (simp add: mat_of_cblinfun_def)

lemma dim_col_mat_of_cblinfun[simp]: \<open>dim_col (mat_of_cblinfun (a::'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2)) = CARD('a)\<close>
  by (simp add: mat_of_cblinfun_def)

lemma mat_of_cblinfun_cblinfun_apply:
  "vec_of_basis_enum (F *\<^sub>V u) = mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u"
  for F::"'a::{basis_enum,complex_normed_vector}  \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector}" and u::'a
proof (rule eq_vecI)
  show \<open>dim_vec (vec_of_basis_enum (F *\<^sub>V u)) = dim_vec (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u)\<close>
    by (simp add: dim_vec_of_basis_enum' mat_of_cblinfun_def)
next
  fix i
  define BasisA where "BasisA = (canonical_basis::'a list)"
  define BasisB where "BasisB = (canonical_basis::'b list)"
  define nA where "nA = length (canonical_basis :: 'a list)"
  define nB where "nB = length (canonical_basis :: 'b list)"
  assume \<open>i < dim_vec (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u)\<close>
  then have [simp]: \<open>i < nB\<close>
    by (simp add: mat_of_cblinfun_def nB_def)
  define v where \<open>v = BasisB ! i\<close>

  have [simp]: \<open>dim_row (mat_of_cblinfun F) = nB\<close>
    by (simp add: mat_of_cblinfun_def nB_def)
  have [simp]: \<open>length BasisB = nB\<close>
    by (simp add: nB_def BasisB_def)
  have [simp]: \<open>length BasisA = nA\<close>
    using BasisA_def nA_def by auto
  have [simp]: \<open>cindependent (set BasisA)\<close>
    using BasisA_def is_cindependent_set by auto
  have [simp]: \<open>cindependent (set BasisB)\<close>
    using BasisB_def is_cindependent_set by blast
  have [simp]: \<open>cspan (set BasisB) = UNIV\<close>
    by (simp add: BasisB_def is_generator_set)
  have [simp]: \<open>cspan (set BasisA) = UNIV\<close>
    by (simp add: BasisA_def is_generator_set)

  have \<open>(mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u) $ i = 
          (\<Sum>j = 0..<nA. row (mat_of_cblinfun F) i $ j * crepresentation (set BasisA) u (vec_of_list BasisA $ j))\<close>
    by (auto simp: vec_of_basis_enum_def scalar_prod_def simp flip: BasisA_def)
  also have \<open>\<dots> = (\<Sum>j = 0..<nA. crepresentation (set BasisB) (F *\<^sub>V BasisA ! j) v
                                 * crepresentation (set BasisA) u (BasisA ! j))\<close>
    apply (rule sum.cong[OF refl])
    by (auto simp: vec_of_list_index mat_of_cblinfun_def scalar_prod_def v_def simp flip: BasisA_def BasisB_def)
  also have \<open>\<dots> = crepresentation (set BasisB) (F *\<^sub>V u) v\<close> (is \<open>(\<Sum>j=_..<_. ?lhs v j) = _\<close>)
  proof (rule complex_vector.representation_eqI[symmetric, THEN fun_cong])
    show \<open>cindependent (set BasisB)\<close> \<open>F *\<^sub>V u \<in> cspan (set BasisB)\<close>
      by simp_all
    show only_basis: \<open>(\<Sum>j = 0..<nA. ?lhs b j) \<noteq> 0 \<Longrightarrow> b \<in> set BasisB\<close> for b
      by (metis (mono_tags, lifting) complex_vector.representation_ne_zero mult_not_zero sum.not_neutral_contains_not_neutral)
    then show \<open>finite {b. (\<Sum>j = 0..<nA. ?lhs b j) \<noteq> 0}\<close>
      by (smt (z3) List.finite_set finite_subset mem_Collect_eq subsetI)
    have \<open>(\<Sum>b | (\<Sum>j = 0..<nA. ?lhs b j) \<noteq> 0. (\<Sum>j = 0..<nA. ?lhs b j) *\<^sub>C b) = 
            (\<Sum>b\<in>set BasisB. (\<Sum>j = 0..<nA. ?lhs b j) *\<^sub>C b)\<close>
      apply (rule sum.mono_neutral_left)
      using only_basis by auto
    also have \<open>\<dots> = (\<Sum>b\<in>set BasisB. (\<Sum>a\<in>set BasisA. crepresentation (set BasisB) (F *\<^sub>V a) b * crepresentation (set BasisA) u a) *\<^sub>C b)\<close>
      apply (subst sum.reindex_bij_betw[where h=\<open>nth BasisA\<close> and T=\<open>set BasisA\<close>])
       apply (metis BasisA_def \<open>length BasisA = nA\<close> atLeast0LessThan bij_betw_nth distinct_canonical_basis)
      by simp
    also have \<open>\<dots> = (\<Sum>a\<in>set BasisA. crepresentation (set BasisA) u a *\<^sub>C (\<Sum>b\<in>set BasisB. crepresentation (set BasisB) (F *\<^sub>V a) b *\<^sub>C b))\<close>
      apply (simp add: scaleC_sum_left scaleC_sum_right)
      apply (subst sum.swap)
      by (metis (no_types, lifting) mult.commute sum.cong)
    also have \<open>\<dots> = (\<Sum>a\<in>set BasisA. crepresentation (set BasisA) u a *\<^sub>C (F *\<^sub>V a))\<close>
      apply (subst complex_vector.sum_representation_eq)
      by auto
    also have \<open>\<dots> = F *\<^sub>V (\<Sum>a\<in>set BasisA. crepresentation (set BasisA) u a *\<^sub>C a)\<close>
      by (simp flip: cblinfun.scaleC_right cblinfun.sum_right)
    also have \<open>\<dots> = F *\<^sub>V u\<close>
      apply (subst complex_vector.sum_representation_eq)
      by auto
    finally show \<open>(\<Sum>b | (\<Sum>j = 0..<nA. ?lhs b j) \<noteq> 0. (\<Sum>j = 0..<nA. ?lhs b j) *\<^sub>C b) = F *\<^sub>V u\<close>
      by auto
  qed
  also have \<open>crepresentation (set BasisB) (F *\<^sub>V u) v = vec_of_basis_enum (F *\<^sub>V u) $ i\<close>
    by (auto simp: vec_of_list_index vec_of_basis_enum_def v_def simp flip: BasisB_def)
  finally show \<open>vec_of_basis_enum (F *\<^sub>V u) $ i = (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u) $ i\<close>
    by simp
qed

lemma basis_enum_of_vec_cblinfun_apply:
  fixes M :: "complex mat"
  defines "nA \<equiv> length (canonical_basis :: 'a::{basis_enum,complex_normed_vector} list)"
    and "nB \<equiv> length (canonical_basis :: 'b::{basis_enum,complex_normed_vector} list)"
  assumes "M \<in> carrier_mat nB nA" and "dim_vec x = nA"
  shows "basis_enum_of_vec (M *\<^sub>v x) = (cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) *\<^sub>V basis_enum_of_vec x"
  by (metis assms basis_enum_of_vec_inverse cblinfun_of_mat.rep_eq)


lemma mat_of_cblinfun_inverse:
  "cblinfun_of_mat (mat_of_cblinfun B) = B"
  for B::"'a::{basis_enum,complex_normed_vector}  \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector}"
proof (rule cblinfun_eqI)
  fix x :: 'a define y where \<open>y = vec_of_basis_enum x\<close>
  then have \<open>cblinfun_of_mat (mat_of_cblinfun B) *\<^sub>V x = ((cblinfun_of_mat (mat_of_cblinfun B) :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b) *\<^sub>V basis_enum_of_vec y)\<close>
    by simp
  also have \<open>\<dots> = basis_enum_of_vec (mat_of_cblinfun B *\<^sub>v vec_of_basis_enum (basis_enum_of_vec y :: 'a))\<close>
    apply (transfer fixing: B)
    by (simp add: mat_of_cblinfun_def)
  also have \<open>\<dots> = basis_enum_of_vec (vec_of_basis_enum (B *\<^sub>V x))\<close>
    by (simp add: mat_of_cblinfun_cblinfun_apply y_def)
  also have \<open>\<dots> = B *\<^sub>V x\<close>
    by simp
  finally show \<open>cblinfun_of_mat (mat_of_cblinfun B) *\<^sub>V x = B *\<^sub>V x\<close>
    by -
qed

lemma mat_of_cblinfun_inj: "inj mat_of_cblinfun"
  by (metis inj_on_def mat_of_cblinfun_inverse)

lemma cblinfun_of_mat_inverse:
  fixes M::"complex mat"
  defines "nA \<equiv> length (canonical_basis :: 'a::{basis_enum,complex_normed_vector} list)"
    and "nB \<equiv> length (canonical_basis :: 'b::{basis_enum,complex_normed_vector} list)"
  assumes "M \<in> carrier_mat nB nA"
  shows "mat_of_cblinfun (cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = M"
  by (smt (verit) assms(3) basis_enum_of_vec_inverse carrier_matD(1) carrier_vecD cblinfun_of_mat.rep_eq dim_mult_mat_vec eq_mat_on_vecI mat_carrier mat_of_cblinfun_def mat_of_cblinfun_cblinfun_apply nA_def nB_def)

lemma cblinfun_of_mat_inj: "inj_on (cblinfun_of_mat::complex mat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) 
      (carrier_mat (length (canonical_basis :: 'b::{basis_enum,complex_normed_vector} list))
                   (length (canonical_basis :: 'a::{basis_enum,complex_normed_vector} list)))"
  using cblinfun_of_mat_inverse
  by (metis inj_onI)


lemma cblinfun_eq_mat_of_cblinfunI:
  assumes "mat_of_cblinfun a = mat_of_cblinfun b"
  shows "a = b"
  by (metis assms mat_of_cblinfun_inverse)


subsection \<open>Matrix operations\<close>

lemma cblinfun_of_mat_plus:
  defines "nA \<equiv> length (canonical_basis :: 'a::{basis_enum,complex_normed_vector} list)" 
    and "nB \<equiv> length (canonical_basis :: 'b::{basis_enum,complex_normed_vector} list)"
  assumes [simp,intro]: "M \<in> carrier_mat nB nA" and [simp,intro]: "N \<in> carrier_mat nB nA"
  shows "(cblinfun_of_mat (M + N) :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = ((cblinfun_of_mat M + cblinfun_of_mat N))"
proof -
  have [simp]: \<open>vec_of_basis_enum (v :: 'a) \<in> carrier_vec nA\<close> for v
    by (auto simp add: carrier_dim_vec dim_vec_of_basis_enum' nA_def)
  have [simp]: \<open>dim_row M = nB\<close> \<open>dim_row N = nB\<close>
    using carrier_matD(1) by auto
  show ?thesis
    apply (transfer fixing: M N)
    by (auto intro!: ext simp add: add_mult_distrib_mat_vec nA_def[symmetric] nB_def[symmetric]
        add_mult_distrib_mat_vec[where nr=nB and nc=nA] basis_enum_of_vec_add)
qed

lemma mat_of_cblinfun_zero:
  "mat_of_cblinfun (0 :: ('a::{basis_enum,complex_normed_vector}  \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector})) 
  = 0\<^sub>m (length (canonical_basis :: 'b list)) (length (canonical_basis :: 'a list))"
  unfolding mat_of_cblinfun_def
  by (auto simp: complex_vector.representation_zero)

lemma mat_of_cblinfun_plus:
  "mat_of_cblinfun (F + G) = mat_of_cblinfun F + mat_of_cblinfun G"
  for F G::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'b::{basis_enum,complex_normed_vector}"
  by (auto simp add: mat_of_cblinfun_def cblinfun.add_left complex_vector.representation_add)

lemma mat_of_cblinfun_id:
  "mat_of_cblinfun (id_cblinfun :: ('a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'a)) = 1\<^sub>m (length (canonical_basis :: 'a list))"
  apply (rule eq_matI)
  by (auto simp: mat_of_cblinfun_def complex_vector.representation_basis is_cindependent_set nth_eq_iff_index_eq)

lemma mat_of_cblinfun_1:
  "mat_of_cblinfun (1 :: ('a::one_dim \<Rightarrow>\<^sub>C\<^sub>L'b::one_dim)) = 1\<^sub>m 1"
  apply (rule eq_matI)
  by (auto simp: mat_of_cblinfun_def complex_vector.representation_basis nth_eq_iff_index_eq)

lemma mat_of_cblinfun_uminus:
  "mat_of_cblinfun (- M) = - mat_of_cblinfun M" 
  for M::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'b::{basis_enum,complex_normed_vector}"
proof-
  define nA where "nA = length (canonical_basis :: 'a list)"
  define nB where "nB = length (canonical_basis :: 'b list)"
  have M1: "mat_of_cblinfun M \<in> carrier_mat nB nA"
    unfolding nB_def nA_def
    by (metis add.right_neutral add_carrier_mat mat_of_cblinfun_plus mat_of_cblinfun_zero nA_def
        nB_def zero_carrier_mat) 
  have M2: "mat_of_cblinfun (-M) \<in> carrier_mat nB nA"
    by (metis add_carrier_mat mat_of_cblinfun_plus mat_of_cblinfun_zero diff_0 nA_def nB_def 
        uminus_add_conv_diff zero_carrier_mat)
  have "mat_of_cblinfun (M - M) =  0\<^sub>m nB nA"
    unfolding nA_def nB_def
    by (simp add: mat_of_cblinfun_zero)
  moreover have "mat_of_cblinfun (M - M) = mat_of_cblinfun M + mat_of_cblinfun (- M)"
    by (metis mat_of_cblinfun_plus pth_2)
  ultimately have "mat_of_cblinfun M + mat_of_cblinfun (- M) = 0\<^sub>m nB nA"
    by simp
  thus ?thesis
    using M1 M2
    by (smt add_uminus_minus_mat assoc_add_mat comm_add_mat left_add_zero_mat minus_r_inv_mat 
        uminus_carrier_mat) 
qed

lemma mat_of_cblinfun_minus:
  "mat_of_cblinfun (M - N) = mat_of_cblinfun M - mat_of_cblinfun N" 
  for M::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector}" and N::"'a \<Rightarrow>\<^sub>C\<^sub>L'b"
  by (smt (z3) add_uminus_minus_mat mat_of_cblinfun_uminus mat_carrier mat_of_cblinfun_def mat_of_cblinfun_plus pth_2)

lemma cblinfun_of_mat_uminus:
  defines "nA \<equiv> length (canonical_basis :: 'a::{basis_enum,complex_normed_vector} list)" 
    and "nB \<equiv> length (canonical_basis :: 'b::{basis_enum,complex_normed_vector} list)"
  assumes "M \<in> carrier_mat nB nA"
  shows "(cblinfun_of_mat (-M) :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = - cblinfun_of_mat M"
  by (smt assms add.group_axioms add.right_neutral add_minus_cancel add_uminus_minus_mat 
      cblinfun_of_mat_plus group.inverse_inverse mat_of_cblinfun_inverse mat_of_cblinfun_zero 
      minus_r_inv_mat uminus_carrier_mat)

lemma cblinfun_of_mat_minus:
  fixes M::"complex mat"
  defines "nA \<equiv> length (canonical_basis :: 'a::{basis_enum,complex_normed_vector} list)" 
    and "nB \<equiv> length (canonical_basis :: 'b::{basis_enum,complex_normed_vector} list)"
  assumes "M \<in> carrier_mat nB nA" and "N \<in> carrier_mat nB nA"
  shows "(cblinfun_of_mat (M - N) :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = cblinfun_of_mat M - cblinfun_of_mat N"
  by (metis assms add_uminus_minus_mat cblinfun_of_mat_plus cblinfun_of_mat_uminus pth_2 uminus_carrier_mat)

lemma cblinfun_of_mat_times:
  fixes M N ::"complex mat"
  defines "nA \<equiv> length (canonical_basis :: 'a::{basis_enum,complex_normed_vector} list)" 
    and "nB \<equiv> length (canonical_basis :: 'b::{basis_enum,complex_normed_vector} list)"
    and "nC \<equiv> length (canonical_basis :: 'c::{basis_enum,complex_normed_vector} list)"
  assumes a1: "M \<in> carrier_mat nC nB" and a2: "N \<in> carrier_mat nB nA"
  shows  "cblinfun_of_mat (M * N) = ((cblinfun_of_mat M)::'b \<Rightarrow>\<^sub>C\<^sub>L'c) o\<^sub>C\<^sub>L ((cblinfun_of_mat N)::'a \<Rightarrow>\<^sub>C\<^sub>L'b)"
proof -
  have b1: "((cblinfun_of_mat M)::'b \<Rightarrow>\<^sub>C\<^sub>L'c) v = basis_enum_of_vec (M *\<^sub>v vec_of_basis_enum v)"
    for v
    by (metis assms(4) cblinfun_of_mat.rep_eq nB_def nC_def)
  have b2: "((cblinfun_of_mat N)::'a \<Rightarrow>\<^sub>C\<^sub>L'b) v = basis_enum_of_vec (N *\<^sub>v vec_of_basis_enum v)"
    for v
    by (metis assms(5) cblinfun_of_mat.rep_eq nA_def nB_def)
  have b3: "((cblinfun_of_mat (M * N))::'a \<Rightarrow>\<^sub>C\<^sub>L'c) v
       = basis_enum_of_vec ((M * N) *\<^sub>v vec_of_basis_enum v)"
    for v
    by (metis assms(4) assms(5) cblinfun_of_mat.rep_eq mult_carrier_mat nA_def nC_def)
  have "(basis_enum_of_vec ((M * N) *\<^sub>v vec_of_basis_enum v)::'c)
      = (basis_enum_of_vec (M *\<^sub>v ( vec_of_basis_enum ( (basis_enum_of_vec (N *\<^sub>v vec_of_basis_enum v))::'b ))))"
    for v::'a
  proof-
    have c1: "vec_of_basis_enum (basis_enum_of_vec x :: 'b) = x"
      if "dim_vec x = nB"
      for x::"complex vec"
      using that unfolding nB_def
      by simp
    have c2: "vec_of_basis_enum v \<in> carrier_vec nA"
      by (metis (mono_tags, hide_lams) add.commute carrier_vec_dim_vec index_add_vec(2) 
          index_zero_vec(2) nA_def vec_of_basis_enum_add basis_enum_of_vec_inverse)      
    have "(M * N) *\<^sub>v vec_of_basis_enum v = M *\<^sub>v (N *\<^sub>v vec_of_basis_enum v)"
      using Matrix.assoc_mult_mat_vec a1 a2 c2 by blast      
    hence "(basis_enum_of_vec ((M * N) *\<^sub>v vec_of_basis_enum v)::'c)
        = (basis_enum_of_vec (M *\<^sub>v (N *\<^sub>v vec_of_basis_enum v))::'c)"
      by simp
    also have "\<dots> = 
      (basis_enum_of_vec (M *\<^sub>v ( vec_of_basis_enum ( (basis_enum_of_vec (N *\<^sub>v vec_of_basis_enum v))::'b ))))"
      using c1 a2 by auto 
    finally show ?thesis by simp
  qed
  thus ?thesis using b1 b2 b3
    by (simp add: cblinfun_eqI scaleC_cblinfun.rep_eq)    
qed

lemma cblinfun_of_mat_adjoint:
  defines "nA \<equiv> length (canonical_basis :: 'a::onb_enum list)"
    and "nB \<equiv> length (canonical_basis :: 'b::onb_enum list)" 
  fixes M:: "complex mat"
  assumes "M \<in> carrier_mat nB nA"
  shows "((cblinfun_of_mat (mat_adjoint M)) :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a) = (cblinfun_of_mat M)*"
proof (rule adjoint_eqI)
  show "\<langle>cblinfun_of_mat (mat_adjoint M) *\<^sub>V x, y\<rangle> =
           \<langle>x, cblinfun_of_mat M *\<^sub>V y\<rangle>"
    for x::'b and y::'a
  proof-
    define u where "u = vec_of_basis_enum x"
    define v where "v = vec_of_basis_enum y"
    have c1: "vec_of_basis_enum ((cblinfun_of_mat (mat_adjoint M) *\<^sub>V x)::'a) = (mat_adjoint M) *\<^sub>v u"
      unfolding u_def
      by (metis (mono_tags, lifting) assms(3) cblinfun_of_mat_inverse map_carrier_mat mat_adjoint_def' mat_of_cblinfun_cblinfun_apply nA_def nB_def transpose_carrier_mat)
    have c2: "(vec_of_basis_enum ((cblinfun_of_mat M *\<^sub>V y)::'b))
        = M *\<^sub>v v"
      by (metis assms(3) cblinfun_of_mat_inverse mat_of_cblinfun_cblinfun_apply nA_def nB_def v_def)
    have c3: "dim_vec v = nA"
      unfolding v_def nA_def vec_of_basis_enum_def
      by (simp add:)
    have c4: "dim_vec u = nB"
      unfolding u_def nB_def vec_of_basis_enum_def
      by (simp add:)
    have "v \<bullet>c ((mat_adjoint M) *\<^sub>v u) = (M *\<^sub>v v) \<bullet>c u"
      using c3 c4 cscalar_prod_adjoint assms(3) by blast      
    hence "v \<bullet>c (vec_of_basis_enum ((cblinfun_of_mat (mat_adjoint M) *\<^sub>V x)::'a))
        = (vec_of_basis_enum ((cblinfun_of_mat M *\<^sub>V y)::'b)) \<bullet>c u"
      using c1 c2 by simp
    thus "\<langle>cblinfun_of_mat (mat_adjoint M) *\<^sub>V x, y\<rangle> =
          \<langle>x, cblinfun_of_mat M *\<^sub>V y\<rangle>"
      unfolding u_def v_def
      by (simp add: cscalar_prod_vec_of_basis_enum)      
  qed
qed

lemma mat_of_cblinfun_classical_operator:
  fixes f::"'a::enum \<Rightarrow> 'b::enum option"
  shows "mat_of_cblinfun (classical_operator f) = mat (CARD('b)) (CARD('a))
           (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)"
proof -
  define nA where "nA = CARD('a)"
  define nB where "nB = CARD('b)"
  define BasisA where "BasisA = (canonical_basis::'a ell2 list)"
  define BasisB where "BasisB = (canonical_basis::'b ell2 list)"
  have "mat_of_cblinfun (classical_operator f) \<in> carrier_mat nB nA"
    unfolding nA_def nB_def by simp
  moreover have "nA = CARD ('a)"
    unfolding nA_def
    by (simp add:)    
  moreover have "nB = CARD ('b)"
    unfolding nB_def
    by (simp add:)
  ultimately have "mat_of_cblinfun (classical_operator f) \<in> carrier_mat (CARD('b)) (CARD('a))"
    unfolding nA_def nB_def
    by simp
  moreover have "(mat_of_cblinfun (classical_operator f))$$(r,c) 
  = (mat (CARD('b)) (CARD('a))
    (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0))$$(r,c)"
    if a1: "r < CARD('b)" and a2: "c < CARD('a)"
    for r c
  proof-
    have "CARD('a) = length (enum_class.enum::'a list)"
      using card_UNIV_length_enum[where 'a = 'a] .
    hence x1: "BasisA!c = ket ((Enum.enum::'a list)!c)"
      unfolding BasisA_def using a2 canonical_basis_ell2_def 
        nth_map[where n = c and xs = "Enum.enum::'a list" and f = ket] by metis
    have cardb: "CARD('b) = length (enum_class.enum::'b list)"
      using card_UNIV_length_enum[where 'a = 'b] .
    hence x2: "BasisB!r = ket ((Enum.enum::'b list)!r)"
      unfolding BasisB_def using a1 canonical_basis_ell2_def 
        nth_map[where n = r and xs = "Enum.enum::'b list" and f = ket] by metis
    have "inj (map (ket::'b \<Rightarrow>_))"
      by (meson injI ket_injective list.inj_map)      
    hence "length (Enum.enum::'b list) = length (map (ket::'b \<Rightarrow>_) (Enum.enum::'b list))"
      by simp      
    hence lengthBasisB: "CARD('b) = length BasisB"
      unfolding BasisB_def canonical_basis_ell2_def using cardb 
      by smt
    have v1: "(mat_of_cblinfun (classical_operator f))$$(r,c) = 0"
      if c1: "f (Enum.enum!c) = None"
    proof-
      have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) 
          = (case f (Enum.enum!c) of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)"
        using classical_operator_ket_finite .
      also have "\<dots> = 0"
        using c1 by simp
      finally have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) = 0" .
      hence *: "(classical_operator f) *\<^sub>V BasisA!c = 0"
        using x1 by simp
      hence "\<langle>BasisB!r, (classical_operator f) *\<^sub>V BasisA!c\<rangle> = 0"
        by simp
      thus ?thesis
        unfolding mat_of_cblinfun_def BasisA_def BasisB_def
        by (smt (verit, del_insts) BasisA_def * a1 a2 canonical_basis_length_ell2 complex_vector.representation_zero index_mat(1) old.prod.case)
    qed
    have v2: "(mat_of_cblinfun (classical_operator f))$$(r,c) = 0"
      if c1: "f (Enum.enum!c) = Some (Enum.enum!r')" and c2: "r\<noteq>r'" 
        and c3: "r' < CARD('b)"
      for r'
    proof-
      have x3: "BasisB!r' = ket ((Enum.enum::'b list)!r')"
        unfolding BasisB_def using cardb c3 canonical_basis_ell2_def 
          nth_map[where n = r' and xs = "Enum.enum::'b list" and f = ket] 
        by smt
      have "distinct BasisB"
        unfolding BasisB_def 
        by simp        
      moreover have "r < length BasisB"
        using a1 lengthBasisB by simp
      moreover have "r' < length BasisB"
        using c3 lengthBasisB by simp        
      ultimately have h1: "BasisB!r \<noteq> BasisB!r'"
        using nth_eq_iff_index_eq[where xs = BasisB and i = r and j = r'] c2
        by blast
      have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) 
          = (case f (Enum.enum!c) of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)"
        using classical_operator_ket_finite .
      also have "\<dots> = ket (Enum.enum!r')"
        using c1 by simp
      finally have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) = ket (Enum.enum!r')" .
      hence *: "(classical_operator f) *\<^sub>V BasisA!c = BasisB!r'"
        using x1 x3 by simp
      moreover have "\<langle>BasisB!r, BasisB!r'\<rangle> = 0"
        using h1
        using BasisB_def \<open>r < length BasisB\<close> \<open>r' < length BasisB\<close> is_ortho_set_def is_orthonormal nth_mem
        by metis
      ultimately have "\<langle>BasisB!r, (classical_operator f) *\<^sub>V BasisA!c\<rangle> = 0"
        by simp
      thus ?thesis
        unfolding mat_of_cblinfun_def BasisA_def BasisB_def
        by (smt (z3) BasisA_def BasisB_def * \<open>r < length BasisB\<close> \<open>r' < length BasisB\<close> a2 canonical_basis_length_ell2 case_prod_conv complex_vector.representation_basis h1 index_mat(1) is_cindependent_set nth_mem)
    qed
    have "(mat_of_cblinfun (classical_operator f))$$(r,c) = 0"
      if b1: "f (Enum.enum!c) \<noteq> Some (Enum.enum!r)"
    proof (cases "f (Enum.enum!c) = None")
      case True thus ?thesis using v1 by blast
    next
      case False
      hence "\<exists>R. f (Enum.enum!c) = Some R"
        apply (induction "f (Enum.enum!c)")
         apply simp
        by simp
      then obtain R where R0: "f (Enum.enum!c) = Some R"
        by blast
      have "R \<in> set (Enum.enum::'b list)"
        using UNIV_enum by blast
      hence "\<exists>r'. R = (Enum.enum::'b list)!r' \<and> r' < length (Enum.enum::'b list)"
        by (metis in_set_conv_nth)
      then obtain r' where u1: "R = (Enum.enum::'b list)!r'" 
        and u2: "r' < length (Enum.enum::'b list)"
        by blast
      have R1: "f (Enum.enum!c) = Some (Enum.enum!r')"
        using R0 u1 by blast
      have "Some ((Enum.enum::'b list)!r') \<noteq> Some ((Enum.enum::'b list)!r)"
      proof(rule classical)
        assume "\<not>(Some ((Enum.enum::'b list)!r') \<noteq> Some ((Enum.enum::'b list)!r))"
        hence "Some ((Enum.enum::'b list)!r') = Some ((Enum.enum::'b list)!r)"
          by blast
        hence "f (Enum.enum!c) = Some ((Enum.enum::'b list)!r)"
          using R1 by auto
        thus ?thesis
          using b1 by blast
      qed
      hence "((Enum.enum::'b list)!r') \<noteq> ((Enum.enum::'b list)!r)"
        by simp
      hence "r' \<noteq> r"
        by blast
      moreover have "r' < CARD('b)"
        using u2 cardb by simp
      ultimately show ?thesis using R1 v2[where r' = r'] by blast
    qed
    moreover have "(mat_of_cblinfun (classical_operator f))$$(r,c) = 1"
      if b1: "f (Enum.enum!c) = Some (Enum.enum!r)"
    proof-
      have "CARD('b) = length (enum_class.enum::'b list)"
        using card_UNIV_length_enum[where 'a = 'b].
      hence "length (map (ket::'b\<Rightarrow>_) enum_class.enum) = CARD('b)"
        by simp        
      hence w0: "map (ket::'b\<Rightarrow>_) enum_class.enum ! r = ket (enum_class.enum ! r)"
        by (simp add: a1)
      have "CARD('a) = length (enum_class.enum::'a list)"
        using card_UNIV_length_enum[where 'a = 'a].
      hence "length (map (ket::'a\<Rightarrow>_) enum_class.enum) = CARD('a)"
        by simp        
      hence "map (ket::'a\<Rightarrow>_) enum_class.enum ! c = ket (enum_class.enum ! c)"
        by (simp add: a2)        
      hence "(classical_operator f) *\<^sub>V (BasisA!c) = (classical_operator f) *\<^sub>V (ket (Enum.enum!c))"
        unfolding BasisA_def canonical_basis_ell2_def by simp
      also have "... = (case f (enum_class.enum ! c) of None \<Rightarrow> 0 | Some x \<Rightarrow> ket x)"
        by (rule classical_operator_ket_finite)
      also have "\<dots> = BasisB!r"
        using w0 b1 by (simp add: BasisB_def canonical_basis_ell2_def) 
      finally have w1: "(classical_operator f) *\<^sub>V (BasisA!c) = BasisB!r"
        by simp        
      have "(mat_of_cblinfun (classical_operator f))$$(r,c)
        = \<langle>BasisB!r, (classical_operator f) *\<^sub>V (BasisA!c)\<rangle>"
        unfolding BasisB_def BasisA_def mat_of_cblinfun_def
        using \<open>nA = CARD('a)\<close> \<open>nB = CARD('b)\<close> a1 a2 nA_def nB_def apply auto
        by (metis BasisA_def BasisB_def canonical_basis_length_ell2 cinner_canonical_basis complex_vector.representation_basis is_cindependent_set nth_mem w1)
      also have "\<dots> = \<langle>BasisB!r, BasisB!r\<rangle>"
        using w1 by simp        
      also have "\<dots> = 1"
        unfolding BasisB_def
        using \<open>nB = CARD('b)\<close> a1 nB_def
        by (simp add: cinner_canonical_basis)
      finally show ?thesis by blast
    qed
    ultimately show ?thesis
      by (simp add: a1 a2)            
  qed
  ultimately show ?thesis 
    apply (rule_tac eq_matI) by auto
qed

lemma mat_of_cblinfun_compose:
  "mat_of_cblinfun (F o\<^sub>C\<^sub>L G) = mat_of_cblinfun F * mat_of_cblinfun G" 
  for F::"'b::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'c::{basis_enum,complex_normed_vector}"
    and G::"'a::{basis_enum,complex_normed_vector}  \<Rightarrow>\<^sub>C\<^sub>L 'b"
  by (smt (verit, del_insts) cblinfun_of_mat_inverse mat_carrier mat_of_cblinfun_def mat_of_cblinfun_inverse cblinfun_of_mat_times mult_carrier_mat)

lemma mat_of_cblinfun_scaleC:
  "mat_of_cblinfun ((a::complex) *\<^sub>C F) = a \<cdot>\<^sub>m (mat_of_cblinfun F)"
  for F :: "'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector}"
  by (auto simp add: complex_vector.representation_scale mat_of_cblinfun_def)

lemma mat_of_cblinfun_scaleR:
  "mat_of_cblinfun ((a::real) *\<^sub>R F) = (complex_of_real a) \<cdot>\<^sub>m (mat_of_cblinfun F)"
  unfolding scaleR_scaleC by (rule mat_of_cblinfun_scaleC)

lemma mat_of_cblinfun_adj:
  "mat_of_cblinfun (F*) = mat_adjoint (mat_of_cblinfun F)"
  for F :: "'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  by (metis (no_types, lifting) cblinfun_of_mat_inverse map_carrier_mat mat_adjoint_def' mat_carrier cblinfun_of_mat_adjoint mat_of_cblinfun_def mat_of_cblinfun_inverse transpose_carrier_mat)

lemma mat_of_cblinfun_vector_to_cblinfun:
  "mat_of_cblinfun (vector_to_cblinfun \<psi>)
       = mat_of_cols (length (canonical_basis :: 'a list)) [vec_of_basis_enum \<psi>]"
  for \<psi>::"'a::{basis_enum,complex_normed_vector}"  
  by (auto simp: mat_of_cols_Cons_index_0 mat_of_cblinfun_def vec_of_basis_enum_def vec_of_list_index)

lemma mat_of_cblinfun_proj:
  fixes a::"'a::onb_enum"
  defines   "d \<equiv> length (canonical_basis :: 'a list)"
    and "norm2 \<equiv> (vec_of_basis_enum a) \<bullet>c (vec_of_basis_enum a)"
  shows  "mat_of_cblinfun (proj a) = 
      1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_basis_enum a]
                 * mat_of_rows d [conjugate (vec_of_basis_enum a)])" (is \<open>_ = ?rhs\<close>)
proof (cases "a = 0")
  case False 
  have norm2: \<open>norm2 = (norm a)\<^sup>2\<close>
    by (simp add: cscalar_prod_vec_of_basis_enum norm2_def cdot_square_norm[symmetric, simplified])
  have [simp]: \<open>vec_of_basis_enum a \<in> carrier_vec d\<close>
    by (simp add: carrier_vecI d_def dim_vec_of_basis_enum')

  have \<open>mat_of_cblinfun (proj a) = mat_of_cblinfun (proj (a /\<^sub>R norm a))\<close>
    by (metis (mono_tags, hide_lams) ccspan_singleton_scaleC complex_vector.scale_eq_0_iff nonzero_imp_inverse_nonzero norm_eq_zero scaleR_scaleC scale_left_imp_eq)
  also have \<open>\<dots> = mat_of_cblinfun (selfbutter (a /\<^sub>R norm a))\<close>
    apply (subst butterfly_eq_proj)
    by (auto simp add: False)
  also have \<open>\<dots> = 1/norm2 \<cdot>\<^sub>m mat_of_cblinfun (selfbutter a)\<close>
    apply (simp add: mat_of_cblinfun_scaleC norm2)
    by (simp add: inverse_eq_divide power2_eq_square)
  also have \<open>\<dots> = 1 / norm2 \<cdot>\<^sub>m (mat_of_cblinfun (vector_to_cblinfun a :: complex \<Rightarrow>\<^sub>C\<^sub>L 'a) * mat_adjoint (mat_of_cblinfun (vector_to_cblinfun a :: complex \<Rightarrow>\<^sub>C\<^sub>L 'a)))\<close>
    by (simp add: butterfly_def mat_of_cblinfun_compose mat_of_cblinfun_adj)
  also have \<open>\<dots> = ?rhs\<close>
    by (simp add: mat_of_cblinfun_vector_to_cblinfun mat_adjoint_def flip: d_def)
  finally show ?thesis
    by -
next
  case True
  show ?thesis
    apply (rule eq_matI)
    by (auto simp: True mat_of_cblinfun_zero vec_of_basis_enum_zero scalar_prod_def  mat_of_rows_index
        simp flip: d_def)
qed


lemma mat_of_cblinfun_ell2_component:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> 
  assumes [simp]: \<open>i < CARD('b)\<close> \<open>j < CARD('a)\<close>
  shows \<open>mat_of_cblinfun a $$ (i,j) = Rep_ell2 (a *\<^sub>V ket (Enum.enum ! j)) (Enum.enum ! i)\<close>
proof -
  let ?i = \<open>Enum.enum ! i\<close> and ?j = \<open>Enum.enum ! j\<close> and ?aj = \<open>a *\<^sub>V ket (Enum.enum ! j)\<close>
  have \<open>Rep_ell2 ?aj (Enum.enum ! i) = vec_of_basis_enum ?aj $ i\<close>
    by (rule vec_of_basis_enum_ell2_component[symmetric], simp)
  also have \<open>\<dots> = (mat_of_cblinfun a *\<^sub>v vec_of_basis_enum (ket (enum_class.enum ! j) :: 'a ell2)) $ i\<close>
    by (simp add: mat_of_cblinfun_cblinfun_apply)
  also have \<open>\<dots> = (mat_of_cblinfun a *\<^sub>v unit_vec CARD('a) j) $ i\<close>
    by (simp add: vec_of_basis_enum_ket enum_idx_enum)
  also have \<open>\<dots> = mat_of_cblinfun a $$ (i, j)\<close>
    apply (subst mat_entry_explicit[where m=\<open>CARD('b)\<close>])
    by auto
  finally show ?thesis
    by auto
qed


lemma mat_of_cblinfun_sandwich:
  fixes a :: "(_::onb_enum, _::onb_enum) cblinfun"
  shows \<open>mat_of_cblinfun (sandwich a *\<^sub>V b) = (let a' = mat_of_cblinfun a in a' * mat_of_cblinfun b * mat_adjoint a')\<close>
  by (simp add: mat_of_cblinfun_compose sandwich_apply Let_def mat_of_cblinfun_adj)


subsection \<open>Operations on subspaces\<close>

lemma ccspan_gram_schmidt0_invariant:
  defines "basis_enum \<equiv> (basis_enum_of_vec :: _ \<Rightarrow> 'a::{basis_enum,complex_normed_vector})"
  defines "n \<equiv> length (canonical_basis :: 'a list)"
  assumes "set ws \<subseteq> carrier_vec n"
  shows "ccspan (set (map basis_enum (gram_schmidt0 n ws))) = ccspan (set (map basis_enum ws))"
proof (transfer fixing: n ws basis_enum)
  interpret complex_vec_space.
  define gs where "gs = gram_schmidt0 n ws"
  have "closure (cspan (set (map basis_enum gs)))
     = cspan (set (map basis_enum gs))"
    apply (rule closure_finite_cspan)
    by simp
  also have "\<dots> = cspan (basis_enum ` set gs)"
    by simp
  also have "\<dots> = basis_enum ` span (set gs)"
    unfolding basis_enum_def
    apply (rule basis_enum_of_vec_span[symmetric])
    using n_def apply simp
    by (simp add: assms(3) cof_vec_space.gram_schmidt0_result(1) gs_def)
  also have "\<dots> = basis_enum ` span (set ws)"
    unfolding gs_def
    apply (subst gram_schmidt0_result(4)[where ws=ws, symmetric])
    using assms by auto
  also have "\<dots> = cspan (basis_enum ` set ws)"
    unfolding basis_enum_def
    apply (rule basis_enum_of_vec_span)
    using n_def apply simp
    by (simp add: assms(3))
  also have "\<dots> = cspan (set (map basis_enum ws))"
    by simp
  also have "\<dots> = closure (cspan (set (map basis_enum ws)))"
    apply (rule closure_finite_cspan[symmetric])
    by simp
  finally show "closure (cspan (set (map basis_enum gs)))
              = closure (cspan (set (map basis_enum ws)))".
qed

definition "is_subspace_of_vec_list n vs ws = 
  (let ws' = gram_schmidt0 n ws in
     \<forall>v\<in>set vs. adjuster n v ws' = - v)"

lemma ccspan_leq_using_vec:
  fixes A B :: "'a::{basis_enum,complex_normed_vector} list"
  shows "(ccspan (set A) \<le> ccspan (set B)) \<longleftrightarrow>
    is_subspace_of_vec_list (length (canonical_basis :: 'a list)) 
      (map vec_of_basis_enum A) (map vec_of_basis_enum B)"
proof -
  define d Av Bv Bo
    where "d = length (canonical_basis :: 'a list)"
      and "Av = map vec_of_basis_enum A"
      and "Bv = map vec_of_basis_enum B"
      and "Bo = gram_schmidt0 d Bv" 
  interpret complex_vec_space d.

  have Av_carrier: "set Av \<subseteq> carrier_vec d"
    unfolding Av_def apply auto
    by (simp add: carrier_vecI d_def dim_vec_of_basis_enum')
  have Bv_carrier: "set Bv \<subseteq> carrier_vec d"
    unfolding Bv_def apply auto
    by (simp add: carrier_vecI d_def dim_vec_of_basis_enum')
  have Bo_carrier: "set Bo \<subseteq> carrier_vec d"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(1))
  have orth_Bo: "corthogonal Bo"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(3))
  have distinct_Bo: "distinct Bo"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(2))

  have "ccspan (set A) \<le> ccspan (set B) \<longleftrightarrow> cspan (set A) \<subseteq> cspan (set B)"
    apply (transfer fixing: A B)
    apply (subst closure_finite_cspan, simp)
    by (subst closure_finite_cspan, simp_all)
  also have "\<dots> \<longleftrightarrow> span (set Av) \<subseteq> span (set Bv)"
    apply (simp add: Av_def Bv_def)
    apply (subst vec_of_basis_enum_cspan[symmetric], simp add: d_def)
    apply (subst vec_of_basis_enum_cspan[symmetric], simp add: d_def)
    by (metis inj_image_subset_iff inj_on_def vec_of_basis_enum_inverse)
  also have "\<dots> \<longleftrightarrow> span (set Av) \<subseteq> span (set Bo)"
    unfolding Bo_def Av_def Bv_def
    apply (subst gram_schmidt0_result(4)[symmetric])
    by (simp_all add: carrier_dim_vec d_def dim_vec_of_basis_enum' image_subset_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>v\<in>set Av. adjuster d v Bo = - v)"
  proof (intro iffI ballI)
    fix v assume "v \<in> set Av" and "span (set Av) \<subseteq> span (set Bo)"
    then have "v \<in> span (set Bo)"
      using Av_carrier span_mem by auto
    have "adjuster d v Bo + v = 0\<^sub>v d"
      apply (rule adjuster_already_in_span)
      using Av_carrier \<open>v \<in> set Av\<close> Bo_carrier orth_Bo
        \<open>v \<in> span (set Bo)\<close> by simp_all
    then show "adjuster d v Bo = - v"
      using Av_carrier Bo_carrier \<open>v \<in> set Av\<close>
      by (metis (no_types, lifting) add.inv_equality adjuster_carrier' local.vec_neg subsetD)
  next
    fix v
    assume adj_minusv: "\<forall>v\<in>set Av. adjuster d v Bo = - v"
    have *: "adjuster d v Bo \<in> span (set Bo)" if "v \<in> set Av" for v
      apply (rule adjuster_in_span)
      using Bo_carrier that Av_carrier distinct_Bo by auto
    have "v \<in> span (set Bo)" if "v \<in> set Av" for v
      using *[OF that] adj_minusv[rule_format, OF that]
      apply auto
      by (metis (no_types, lifting) Av_carrier Bo_carrier adjust_nonzero distinct_Bo subsetD that uminus_l_inv_vec)
    then show "span (set Av) \<subseteq> span (set Bo)"
      apply auto
      by (meson Bo_carrier in_mono span_subsetI subsetI)
  qed
  also have "\<dots> = is_subspace_of_vec_list d Av Bv"
    by (simp add: is_subspace_of_vec_list_def d_def Bo_def)
  finally show "ccspan (set A) \<le> ccspan (set B) \<longleftrightarrow> is_subspace_of_vec_list d Av Bv"
    by simp
qed

lemma cblinfun_apply_ccspan_using_vec: 
  "A *\<^sub>S ccspan (set S) = ccspan (basis_enum_of_vec ` set (map ((*\<^sub>v) (mat_of_cblinfun A)) (map vec_of_basis_enum S)))"
  apply (auto simp: cblinfun_image_ccspan image_image)
  by (metis mat_of_cblinfun_cblinfun_apply vec_of_basis_enum_inverse)

text \<open>\<^term>\<open>mk_projector_orthog d L\<close> takes a list L of d-dimensional vectors
and returns the projector onto the span of L. (Assuming that all vectors in L are 
orthogonal and nonzero.)\<close>
fun mk_projector_orthog :: "nat \<Rightarrow> complex vec list \<Rightarrow> complex mat" where
  "mk_projector_orthog d [] = zero_mat d d"
| "mk_projector_orthog d [v] = (let norm2 = cscalar_prod v v in
                                smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [conjugate v]))"
| "mk_projector_orthog d (v#vs) = (let norm2 = cscalar_prod v v in
                                   smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [conjugate v]) 
                                        + mk_projector_orthog d vs)"

lemma mk_projector_orthog_correct:
  fixes S :: "'a::onb_enum list"
  defines "d \<equiv> length (canonical_basis :: 'a list)"
  assumes ortho: "is_ortho_set (set S)" and distinct: "distinct S"
  shows "mk_projector_orthog d (map vec_of_basis_enum S) 
       = mat_of_cblinfun (Proj (ccspan (set S)))"
proof -
  define Snorm where "Snorm = map (\<lambda>s. s /\<^sub>R norm s) S"

  have "distinct Snorm"
  proof (insert ortho distinct, unfold Snorm_def, induction S)
    case Nil
    show ?case by simp
  next
    case (Cons s S)
    then have "is_ortho_set (set S)" and "distinct S"
      unfolding is_ortho_set_def by auto
    note IH = Cons.IH[OF this]
    have "s /\<^sub>R norm s \<notin> (\<lambda>s. s /\<^sub>R norm s) ` set S"
    proof auto
      fix s' assume "s' \<in> set S" and same: "s /\<^sub>R norm s = s' /\<^sub>R norm s'"
      with Cons.prems have "s \<noteq> s'" by auto
      have "s \<noteq> 0"
        by (metis Cons.prems(1) is_ortho_set_def list.set_intros(1))
      then have "0 \<noteq> \<langle>s /\<^sub>R norm s, s /\<^sub>R norm s\<rangle>"
        by simp
      also have \<open>\<langle>s /\<^sub>R norm s, s /\<^sub>R norm s\<rangle> = \<langle>s /\<^sub>R norm s, s' /\<^sub>R norm s'\<rangle>\<close>
        by (simp add: same)
      also have \<open>\<langle>s /\<^sub>R norm s, s' /\<^sub>R norm s'\<rangle> = \<langle>s, s'\<rangle> / (norm s * norm s')\<close>
        by (simp add: scaleR_scaleC divide_inverse_commute)
      also from \<open>s' \<in> set S\<close> \<open>s \<noteq> s'\<close> have "\<dots> = 0"
        using Cons.prems unfolding is_ortho_set_def by simp
      finally show False
        by simp
    qed
    then show ?case
      using IH by simp
  qed

  have norm_Snorm: "norm s = 1" if "s \<in> set Snorm" for s
    using that ortho unfolding Snorm_def is_ortho_set_def apply auto
    by (metis left_inverse norm_eq_zero)

  have ortho_Snorm: "is_ortho_set (set Snorm)"
    unfolding is_ortho_set_def
  proof (intro conjI ballI impI)
    fix x y
    show "0 \<notin> set Snorm"
      using norm_Snorm[of 0] by auto
    assume "x \<in> set Snorm" and "y \<in> set Snorm" and "x \<noteq> y"
    from \<open>x \<in> set Snorm\<close>
    obtain x' where x: "x = x' /\<^sub>R norm x'" and x': "x' \<in> set S"
      unfolding Snorm_def by auto
    from \<open>y \<in> set Snorm\<close>
    obtain y' where y: "y = y' /\<^sub>R norm y'" and y': "y' \<in> set S"
      unfolding Snorm_def by auto
    from \<open>x \<noteq> y\<close> x y have \<open>x' \<noteq> y'\<close> by auto
    with x' y' ortho have "cinner x' y' = 0"
      unfolding is_ortho_set_def by auto
    then show "cinner x y = 0"
      unfolding x y scaleR_scaleC by auto
  qed

  have inj_butter: "inj_on selfbutter (set Snorm)"
  proof (rule inj_onI)
    fix x y 
    assume "x \<in> set Snorm" and "y \<in> set Snorm"
    assume "selfbutter x = selfbutter y"
    then obtain c where xcy: "x = c *\<^sub>C y" and "cmod c = 1"
      using inj_selfbutter_upto_phase by auto
    have "0 \<noteq> cmod (cinner x x)"
      using \<open>x \<in> set Snorm\<close> norm_Snorm
      by force
    also have "cmod (cinner x x) = cmod (c * \<langle>x, y\<rangle>)"
      apply (subst (2) xcy) by simp
    also have "\<dots> = cmod \<langle>x, y\<rangle>"
      using \<open>cmod c = 1\<close> by (simp add: norm_mult)
    finally have "\<langle>x, y\<rangle> \<noteq> 0"
      by simp
    then show "x = y"
      using ortho_Snorm \<open>x \<in> set Snorm\<close> \<open>y \<in> set Snorm\<close>
      unfolding is_ortho_set_def by auto
  qed

  from \<open>distinct Snorm\<close> inj_butter
  have distinct': "distinct (map selfbutter Snorm)"
    unfolding distinct_map by simp

  have Span_Snorm: "ccspan (set Snorm) = ccspan (set S)"
    apply (transfer fixing: Snorm S)
    apply (simp add: scaleR_scaleC Snorm_def)
    apply (subst complex_vector.span_image_scale) 
    using is_ortho_set_def ortho by fastforce+

  have "mk_projector_orthog d (map vec_of_basis_enum S)
      = mat_of_cblinfun (sum_list (map selfbutter Snorm))"
    unfolding Snorm_def
  proof (induction S)
    case Nil
    show ?case 
      by (simp add: d_def mat_of_cblinfun_zero)
  next
    case (Cons a S)
    define sumS where "sumS = sum_list (map selfbutter (map (\<lambda>s. s /\<^sub>R norm s) S))"
    with Cons have IH: "mk_projector_orthog d (map vec_of_basis_enum S)
                  = mat_of_cblinfun sumS"
      by simp

    define factor where "factor = inverse ((complex_of_real (norm a))\<^sup>2)"
    have factor': "factor = 1 / (vec_of_basis_enum a \<bullet>c vec_of_basis_enum a)"
      unfolding factor_def cscalar_prod_vec_of_basis_enum
      by (simp add: inverse_eq_divide power2_norm_eq_cinner)

    have "mk_projector_orthog d (map vec_of_basis_enum (a # S))
          = factor \<cdot>\<^sub>m (mat_of_cols d [vec_of_basis_enum a] 
                    * mat_of_rows d [conjugate (vec_of_basis_enum a)])
            + mat_of_cblinfun sumS"
      apply (cases S)
       apply (auto simp add: factor' sumS_def d_def mat_of_cblinfun_zero)[1]
      by (auto simp add: IH[symmetric] factor' d_def)

    also have "\<dots> = factor \<cdot>\<^sub>m (mat_of_cols d [vec_of_basis_enum a] *
         mat_adjoint (mat_of_cols d [vec_of_basis_enum a])) + mat_of_cblinfun sumS"
      apply (rule arg_cong[where f="\<lambda>x. _ \<cdot>\<^sub>m (_ * x) + _"])
      apply (rule mat_eq_iff[THEN iffD2])
      apply (auto simp add: mat_adjoint_def)
      apply (subst mat_of_rows_index) apply auto
      apply (subst mat_of_rows_index) apply auto
      apply (subst mat_of_cols_index) apply auto
      by (simp add: assms(1) dim_vec_of_basis_enum')
    also have "\<dots> = mat_of_cblinfun (selfbutter (a /\<^sub>R norm a)) + mat_of_cblinfun sumS"
      apply (simp add: butterfly_scaleR_left butterfly_scaleR_right power_inverse mat_of_cblinfun_scaleR factor_def)
      apply (simp add: butterfly_def mat_of_cblinfun_compose
          mat_of_cblinfun_adj mat_of_cblinfun_vector_to_cblinfun d_def)
      by (simp add: mat_of_cblinfun_compose mat_of_cblinfun_adj mat_of_cblinfun_vector_to_cblinfun mat_of_cblinfun_scaleC power2_eq_square)
    finally show ?case
      by (simp add: mat_of_cblinfun_plus sumS_def)
  qed
  also have "\<dots> = mat_of_cblinfun (\<Sum>s\<in>set Snorm. selfbutter s)"
    by (metis distinct' distinct_map sum.distinct_set_conv_list)
  also have "\<dots> = mat_of_cblinfun (\<Sum>s\<in>set Snorm. proj s)"
    apply (rule arg_cong[where f="mat_of_cblinfun"])
    apply (rule sum.cong[OF refl])
    apply (rule butterfly_eq_proj)
    using norm_Snorm by simp
  also have "\<dots> = mat_of_cblinfun (Proj (ccspan (set Snorm)))"
    apply (rule arg_cong[of _ _ mat_of_cblinfun])
  proof (insert ortho_Snorm, insert \<open>distinct Snorm\<close>, induction Snorm)
    case Nil
    show ?case
      by simp
  next
    case (Cons a Snorm)
    from Cons.prems have [simp]: "a \<notin> set Snorm"
      by simp

    have "sum proj (set (a # Snorm))
        = proj a + sum proj (set Snorm)"
      by auto
    also have "\<dots> = proj a + Proj (ccspan (set Snorm))"
      apply (subst Cons.IH)
      using Cons.prems apply auto
      by (meson Cons.prems(1) is_ortho_set_antimono set_subset_Cons)
    also have "\<dots> = Proj (ccspan ({a} \<union> set Snorm))"
      apply (rule Proj_orthog_ccspan_union[symmetric])
      by (metis Cons.prems(1) \<open>a \<notin> set Snorm\<close> is_ortho_set_def list.set_intros(1) list.set_intros(2) singleton_iff)
    finally show ?case
      by simp
  qed
  also have "\<dots> = mat_of_cblinfun (Proj (ccspan (set S)))"
    unfolding Span_Snorm by simp
  finally show ?thesis
    by -
qed

lemma mat_of_cblinfun_Proj_ccspan: 
  fixes S :: "'a::onb_enum list"
  shows "mat_of_cblinfun (Proj (ccspan (set S))) =
    (let d = length (canonical_basis :: 'a list) in 
      mk_projector_orthog d (gram_schmidt0 d (map vec_of_basis_enum S)))"
proof-
  define d gs 
    where "d = length (canonical_basis :: 'a list)"
      and "gs = gram_schmidt0 d (map vec_of_basis_enum S)"
  interpret complex_vec_space d.
  have gs_dim: "x \<in> set gs \<Longrightarrow> dim_vec x = d" for x
    by (smt carrier_vecD carrier_vec_dim_vec d_def dim_vec_of_basis_enum' ex_map_conv gram_schmidt0_result(1) gs_def subset_code(1))
  have ortho_gs: "is_ortho_set (set (map basis_enum_of_vec gs :: 'a list))"
    apply (subst corthogonal_vec_of_basis_enum[THEN iffD1], auto)
    by (smt carrier_dim_vec cof_vec_space.gram_schmidt0_result(1) d_def dim_vec_of_basis_enum' gram_schmidt0_result(3) gs_def imageE map_idI map_map o_apply set_map subset_code(1) basis_enum_of_vec_inverse)
  have distinct_gs: "distinct (map basis_enum_of_vec gs :: 'a list)"
    by (metis (mono_tags, hide_lams) carrier_vec_dim_vec cof_vec_space.gram_schmidt0_result(2) d_def dim_vec_of_basis_enum' distinct_map gs_def gs_dim image_iff inj_on_inverseI set_map subsetI basis_enum_of_vec_inverse)

  have "mk_projector_orthog d gs 
      = mk_projector_orthog d (map vec_of_basis_enum (map basis_enum_of_vec gs :: 'a list))"
    apply simp
    apply (subst map_cong[where ys=gs and g=id], simp)
    using gs_dim by (auto intro!: vec_of_basis_enum_inverse simp: d_def)
  also have "\<dots> = mat_of_cblinfun (Proj (ccspan (set (map basis_enum_of_vec gs :: 'a list))))"
    unfolding d_def
    apply (subst mk_projector_orthog_correct)
    using ortho_gs distinct_gs by auto
  also have "\<dots> = mat_of_cblinfun (Proj (ccspan (set S)))"
    apply (rule arg_cong[where f="\<lambda>x. mat_of_cblinfun (Proj x)"])
    unfolding gs_def d_def
    apply (subst ccspan_gram_schmidt0_invariant)
    by (auto simp add: carrier_vecI dim_vec_of_basis_enum')
  finally show ?thesis
    unfolding d_def gs_def by auto
qed

unbundle no_jnf_notation
unbundle no_cblinfun_notation

end
