
subsection \<open>Soundness of the algorithm\<close>

theory HNF_Mod_Det_Soundness
  imports
    HNF_Mod_Det_Algorithm
    Signed_Modulo
begin

hide_const(open) Determinants.det Determinants2.upper_triangular
  Finite_Cartesian_Product.row Finite_Cartesian_Product.rows
  Finite_Cartesian_Product.vec

subsubsection \<open>Results connecting lattices and Hermite normal form\<close>

text \<open>The following results will also be useful for proving the soundness of the certification 
approach.\<close>

lemma of_int_mat_hom_int_id[simp]:
  fixes A::"int mat"
  shows "of_int_hom.mat_hom A = A" unfolding map_mat_def by auto


definition "is_sound_HNF algorithm associates res 
    = (\<forall>A. let (P,H) = algorithm A; m = dim_row A; n = dim_col A in 
        P \<in> carrier_mat m m \<and> H \<in> carrier_mat m n \<and> invertible_mat P \<and> A = P * H 
        \<and> Hermite_JNF associates res H)"

lemma HNF_A_eq_HNF_PA:
  fixes A::"'a::{bezout_ring_div,normalization_euclidean_semiring,unique_euclidean_ring} mat"
  assumes A: "A \<in> carrier_mat n n" and inv_A: "invertible_mat A" 
    and inv_P: "invertible_mat P" and P: "P \<in> carrier_mat n n"
    and sound_HNF: "is_sound_HNF HNF associates res"
    and P1_H1: "(P1,H1) = HNF (P*A)"
    and P2_H2: "(P2,H2) = HNF A"
  shows "H1 = H2"
proof -
  obtain inv_P where P_inv_P: "inverts_mat P inv_P" and inv_P_P: "inverts_mat inv_P P"
    and inv_P: "inv_P \<in> carrier_mat n n"
    using P inv_P obtain_inverse_matrix by blast
  have P1: "P1 \<in> carrier_mat n n"
      using P1_H1 sound_HNF unfolding is_sound_HNF_def Let_def
      by (metis (no_types, lifting) P carrier_matD(1) index_mult_mat(2) old.prod.case)
    have H1: "H1 \<in> carrier_mat n n" using P1_H1 sound_HNF unfolding is_sound_HNF_def Let_def
  by (metis (no_types, lifting) A P carrier_matD(1) carrier_matD(2) case_prodD index_mult_mat(2,3))
  have invertible_inv_P: "invertible_mat inv_P"
      using P_inv_P inv_P inv_P_P invertible_mat_def square_mat.simps by blast
  have P_A_P1_H1: "P * A = P1 * H1" using P1_H1 sound_HNF unfolding is_sound_HNF_def Let_def
    by (metis (mono_tags, lifting) case_prod_conv)
  hence "A = inv_P * (P1 * H1)"
    by (smt A P inv_P_P inv_P assoc_mult_mat carrier_matD(1) inverts_mat_def left_mult_one_mat)
  hence A_inv_P_P1_H1: "A = (inv_P * P1) * H1"
    by (smt P P1_H1 assoc_mult_mat carrier_matD(1) fst_conv index_mult_mat(2) inv_P 
        is_sound_HNF_def prod.sel(2) sound_HNF split_beta)
  have A_P2_H2: "A = P2 * H2" using P2_H2 sound_HNF unfolding is_sound_HNF_def Let_def
    by (metis (mono_tags, lifting) case_prod_conv)
  have invertible_inv_P_P1: "invertible_mat (inv_P * P1)"
  proof (rule invertible_mult_JNF[OF inv_P P1 invertible_inv_P])   
    show "invertible_mat P1"
      by (smt P1_H1 is_sound_HNF_def prod.sel(1) sound_HNF split_beta)
  qed
  show ?thesis
  proof (rule Hermite_unique_JNF[OF A _ H1 _ _ A_inv_P_P1_H1 A_P2_H2 inv_A invertible_inv_P_P1])
    show "inv_P * P1 \<in> carrier_mat n n"
      by (metis carrier_matD(1) carrier_matI index_mult_mat(2) inv_P
          invertible_inv_P_P1 invertible_mat_def square_mat.simps)
    show "P2 \<in> carrier_mat n n" 
      by (smt A P2_H2 carrier_matD(1) is_sound_HNF_def prod.sel(1) sound_HNF split_beta)
    show "H2 \<in> carrier_mat n n"
      by (smt A P2_H2 carrier_matD(1) carrier_matD(2) is_sound_HNF_def prod.sel(2) sound_HNF split_beta)
    show "invertible_mat P2"
      by (smt P2_H2 is_sound_HNF_def prod.sel(1) sound_HNF split_beta)
    show "Hermite_JNF associates res H1" 
      by (smt P1_H1 is_sound_HNF_def prod.sel(2) sound_HNF split_beta)
    show "Hermite_JNF associates res H2"
      by (smt P2_H2 is_sound_HNF_def prod.sel(2) sound_HNF split_beta)
  qed
qed


context vec_module
begin

lemma mat_mult_invertible_lattice_eq: 
  assumes fs: "set fs \<subseteq> carrier_vec n"
  and gs: "set gs \<subseteq> carrier_vec n"  
  and P: "P \<in> carrier_mat m m" and invertible_P: "invertible_mat P"
  and length_fs: "length fs = m" and length_gs: "length gs = m"
  and prod: "mat_of_rows n fs = (map_mat of_int P) * mat_of_rows n gs" 
  shows "lattice_of fs = lattice_of gs" 
proof thm mat_mult_sub_lattice
  show "lattice_of fs \<subseteq> lattice_of gs"
    by (rule mat_mult_sub_lattice[OF fs gs _ prod],simp add: length_fs length_gs P)
next
  obtain inv_P where P_inv_P: "inverts_mat P inv_P" and inv_P_P: "inverts_mat inv_P P"
    and inv_P: "inv_P \<in> carrier_mat m m"
    using P invertible_P obtain_inverse_matrix by blast
  have "of_int_hom.mat_hom (inv_P) * mat_of_rows n fs 
      = of_int_hom.mat_hom (inv_P) * ((map_mat of_int P) * mat_of_rows n gs)" 
    using prod by auto
  also have "... = of_int_hom.mat_hom (inv_P) * (map_mat of_int P) * mat_of_rows n gs"
    by (smt P assoc_mult_mat inv_P length_gs map_carrier_mat mat_of_rows_carrier(1))
  also have "... = of_int_hom.mat_hom (inv_P * P) * mat_of_rows n gs"
    by (metis P inv_P of_int_hom.mat_hom_mult)
  also have "... = mat_of_rows n gs"
    by (metis carrier_matD(1) inv_P inv_P_P inverts_mat_def left_mult_one_mat' 
        length_gs mat_of_rows_carrier(2) of_int_hom.mat_hom_one)    
  finally have prod: "mat_of_rows n gs = of_int_hom.mat_hom (inv_P) * mat_of_rows n fs" ..
  show "lattice_of gs \<subseteq> lattice_of fs"
    by (rule mat_mult_sub_lattice[OF gs fs _ prod], simp add: length_fs length_gs inv_P)
qed                     

end


context
  fixes n :: nat
begin

interpretation vec_module "TYPE(int)" .

lemma lattice_of_HNF:
  assumes sound_HNF: "is_sound_HNF HNF associates res"
    and P1_H1: "(P,H) = HNF (mat_of_rows n fs)"
    and fs: "set fs \<subseteq> carrier_vec n" and len: "length fs = m"
  shows "lattice_of fs = lattice_of (rows H)"
proof (rule mat_mult_invertible_lattice_eq[OF fs])
  have H: "H \<in> carrier_mat m n" using sound_HNF P1_H1 unfolding is_sound_HNF_def Let_def
    by (metis (mono_tags, lifting) assms(4) mat_of_rows_carrier(2) mat_of_rows_carrier(3) prod.sel(2) split_beta)
  have H_rw: "mat_of_rows n (Matrix.rows H) = H" using mat_of_rows_rows H by fast
  have PH_fs_init: "mat_of_rows n fs = P * H" using sound_HNF P1_H1 unfolding is_sound_HNF_def Let_def
    by (metis (mono_tags, lifting) case_prodD)
  show "mat_of_rows n fs = of_int_hom.mat_hom P * mat_of_rows n (Matrix.rows H)"
    unfolding H_rw of_int_mat_hom_int_id using PH_fs_init by simp  
  show "set (Matrix.rows H) \<subseteq> carrier_vec n" using H rows_carrier by blast
  show "P \<in> carrier_mat m m" using sound_HNF P1_H1 unfolding is_sound_HNF_def Let_def
    by (metis (no_types, lifting) len case_prodD mat_of_rows_carrier(2))    
  show "invertible_mat P" using sound_HNF P1_H1 unfolding is_sound_HNF_def Let_def
    by (metis (no_types, lifting) case_prodD)
  show "length fs = m" using len by simp
  show "length (Matrix.rows H) = m" using H by auto
qed
end


context LLL_with_assms 
begin            

(*For this proof, it seems that is not necessary fs_init to be a list of independent vectors. 
The context assumes it, though.*)
lemma certification_via_eq_HNF:
  assumes sound_HNF: "is_sound_HNF HNF associates res"
    and P1_H1: "(P1,H1) = HNF (mat_of_rows n fs_init)"
    and P2_H2: "(P2,H2) = HNF (mat_of_rows n gs)"
    and H1_H2: "H1 = H2" (*The HNF are equal*)
    and gs: "set gs \<subseteq> carrier_vec n" and len_gs: "length gs = m"
  shows "lattice_of gs = lattice_of fs_init" "LLL_with_assms n m gs \<alpha>"
proof -                                           
  have "lattice_of fs_init = lattice_of (rows H1)"
    by (rule lattice_of_HNF[OF sound_HNF P1_H1 fs_init], simp add: len)
  also have "... = lattice_of (rows H2)" using H1_H2 by auto
  also have "... = lattice_of gs" 
    by (rule lattice_of_HNF[symmetric, OF sound_HNF P2_H2 gs len_gs])
  finally show "lattice_of gs = lattice_of fs_init" ..
    have invertible_P1: "invertible_mat P1" 
      using sound_HNF P1_H1 unfolding is_sound_HNF_def
      by (metis (mono_tags, lifting) case_prodD)
  have invertible_P2: "invertible_mat P2"
      using sound_HNF P2_H2 unfolding is_sound_HNF_def
      by (metis (mono_tags, lifting) case_prodD)
    have P2: "P2 \<in> carrier_mat m m" 
      using sound_HNF P2_H2 unfolding is_sound_HNF_def
      by (metis (no_types, lifting) len_gs case_prodD mat_of_rows_carrier(2))
    obtain inv_P2 where P2_inv_P2: "inverts_mat P2 inv_P2" and inv_P2_P2: "inverts_mat inv_P2 P2"
    and inv_P2: "inv_P2 \<in> carrier_mat m m"
      using P2 invertible_P2 obtain_inverse_matrix by blast
    have P1: "P1 \<in> carrier_mat m m" 
      using sound_HNF P1_H1 unfolding is_sound_HNF_def
      by (metis (no_types, lifting) len case_prodD mat_of_rows_carrier(2))
    have H1: "H1 \<in> carrier_mat m n" 
      using sound_HNF P1_H1 unfolding is_sound_HNF_def
      by (metis (no_types, lifting) case_prodD len mat_of_rows_carrier(2) mat_of_rows_carrier(3))
    have H2: "H2 \<in> carrier_mat m n" 
      using sound_HNF P2_H2 unfolding is_sound_HNF_def
      by (metis (no_types, lifting) len_gs case_prodD mat_of_rows_carrier(2) mat_of_rows_carrier(3))
    have P2_H2: "P2 * H2 = mat_of_rows n gs"
      by (smt P2_H2 sound_HNF case_prodD is_sound_HNF_def)
    have P1_H1_fs: "P1 * H1 = mat_of_rows n fs_init"
      by (smt P1_H1 sound_HNF case_prodD is_sound_HNF_def)
    obtain inv_P1 where P1_inv_P1: "inverts_mat P1 inv_P1" and inv_P1_P1: "inverts_mat inv_P1 P1"
    and inv_P1: "inv_P1 \<in> carrier_mat m m"
      using P1 invertible_P1 obtain_inverse_matrix by blast
  show "LLL_with_assms n m gs \<alpha>"
  proof (rule LLL_change_basis(2)[OF gs len_gs])
    show "P1 * inv_P2 \<in> carrier_mat m m" using P1 inv_P2 by auto
    have "mat_of_rows n fs_init = P1 * H1" using sound_HNF P2_H2 unfolding is_sound_HNF_def
      by (metis (mono_tags, lifting) P1_H1 case_prodD)
    also have "... = P1 * inv_P2 * P2 * H1"
      by (smt P1 P2 assoc_mult_mat carrier_matD(1) inv_P2 inv_P2_P2 inverts_mat_def right_mult_one_mat)
    also have "... = P1 * inv_P2 * P2 * H2" using H1_H2 by blast
    also have "... = P1 * inv_P2 * (P2 * H2)" 
      using H2 P2 \<open>P1 * inv_P2 \<in> carrier_mat m m\<close> assoc_mult_mat by blast
    also have "... = P1 * (inv_P2 * P2 * H2)"
      by (metis H2 \<open>P1 * H1 = P1 * inv_P2 * P2 * H1\<close> \<open>P1 * inv_P2 * P2 * H2 = P1 * inv_P2 * (P2 * H2)\<close> 
          H1_H2 carrier_matD(1) inv_P2 inv_P2_P2 inverts_mat_def left_mult_one_mat)
    also have "... = P1 * (inv_P2 * (P2 * H2))" using H2 P2 inv_P2 by auto
    also have "... =  P1 * inv_P2 * mat_of_rows n gs"
      using P2_H2 \<open>P1 * (inv_P2 * P2 * H2) = P1 * (inv_P2 * (P2 * H2))\<close> 
        \<open>P1 * inv_P2 * (P2 * H2) = P1 * (inv_P2 * P2 * H2)\<close> by auto
    finally show "mat_of_rows n fs_init = P1 * inv_P2 * mat_of_rows n gs" .
    show "P2 * inv_P1 \<in> carrier_mat m m" 
      using P2 inv_P1 by auto
    have "mat_of_rows n gs = P2 * H2" using sound_HNF P2_H2 unfolding is_sound_HNF_def by metis
    also have "... = P2 * inv_P1 * P1 * H2"
      by (smt P1 P2 assoc_mult_mat carrier_matD(1) inv_P1 inv_P1_P1 inverts_mat_def right_mult_one_mat)
    also have "... = P2 * inv_P1 * P1 * H1" using H1_H2 by blast
    also have "... = P2 * inv_P1 * (P1 * H1)" 
      using H1 P1 \<open>P2 * inv_P1 \<in> carrier_mat m m\<close> assoc_mult_mat by blast
    also have "... = P2 * (inv_P1 * P1 * H1)"
      by (metis H2 \<open>P2 * H2 = P2 * inv_P1 * P1 * H2\<close> \<open>P2 * inv_P1 * P1 * H1 = P2 * inv_P1 * (P1 * H1)\<close> 
          H1_H2 carrier_matD(1) inv_P1 inv_P1_P1 inverts_mat_def left_mult_one_mat)
    also have "... = P2 * (inv_P1 * (P1 * H1))" using H1 P1 inv_P1 by auto
    also have "... =  P2 * inv_P1 * mat_of_rows n fs_init"
      using P1_H1_fs \<open>P2 * (inv_P1 * P1 * H1) = P2 * (inv_P1 * (P1 * H1))\<close> 
        \<open>P2 * inv_P1 * (P1 * H1) = P2 * (inv_P1 * P1 * H1)\<close> by auto
    finally show "mat_of_rows n gs = P2 * inv_P1 * mat_of_rows n fs_init" .
  qed
qed

end

text \<open>Now, we need to generalize some lemmas.\<close>

context vec_module
begin

(*Generalized version of thm vec_space.finsum_index, now in vec_module*)
lemma finsum_index:
  assumes i: "i < n"
    and f: "f \<in> A \<rightarrow> carrier_vec n"
    and A: "A \<subseteq> carrier_vec n"
  shows "finsum V f A $ i = sum (\<lambda>x. f x $ i) A"
  using A f
proof (induct A rule: infinite_finite_induct)
  case empty
    then show ?case using i by simp next
  case (insert x X)
    then have Xf: "finite X"
      and xX: "x \<notin> X"
      and x: "x \<in> carrier_vec n"
      and X: "X \<subseteq> carrier_vec n"
      and fx: "f x \<in> carrier_vec n"
      and f: "f \<in> X \<rightarrow> carrier_vec n" by auto
    have i2: "i < dim_vec (finsum V f X)"
      using i finsum_closed[OF f] by auto
    have ix: "i < dim_vec x" using x i by auto
    show ?case
      unfolding finsum_insert[OF Xf xX f fx]
      unfolding sum.insert[OF Xf xX]
      unfolding index_add_vec(1)[OF i2]
      using insert lincomb_def
      by auto
qed (insert i, auto)

(*Generalized version of thm vec_space.mat_of_rows_mult_as_finsum, now in vec_module*)
lemma mat_of_rows_mult_as_finsum:
  assumes "v \<in> carrier_vec (length lst)" "\<And> i. i < length lst \<Longrightarrow> lst ! i \<in> carrier_vec n"
  defines "f l \<equiv> sum (\<lambda> i. if l = lst ! i then v $ i else 0) {0..<length lst}"
  shows mat_of_cols_mult_as_finsum:"mat_of_cols n lst *\<^sub>v v = lincomb f (set lst)"
proof -
  from assms have "\<forall> i < length lst. lst ! i \<in> carrier_vec n" by blast
  note an = all_nth_imp_all_set[OF this] hence slc:"set lst \<subseteq> carrier_vec n" by auto
  hence dn [simp]:"\<And> x. x \<in> set lst \<Longrightarrow> dim_vec x = n" by auto
  have dl [simp]:"dim_vec (lincomb f (set lst)) = n" using an
    by (simp add: slc)
  show ?thesis proof
    show "dim_vec (mat_of_cols n lst *\<^sub>v v) = dim_vec (lincomb f (set lst))" using assms(1,2) by auto
    fix i assume i:"i < dim_vec (lincomb f (set lst))" hence i':"i < n" by auto
    with an have fcarr:"(\<lambda>v. f v \<cdot>\<^sub>v v) \<in> set lst \<rightarrow> carrier_vec n" by auto
    from i' have "(mat_of_cols n lst *\<^sub>v v) $ i = row (mat_of_cols n lst) i \<bullet> v" by auto
    also have "\<dots> = (\<Sum>ia = 0..<dim_vec v. lst ! ia $ i * v $ ia)"
      unfolding mat_of_cols_def row_def scalar_prod_def
      apply(rule sum.cong[OF refl]) using i an assms(1) by auto
    also have "\<dots> = (\<Sum>ia = 0..<length lst. lst ! ia $ i * v $ ia)" using assms(1) by auto
    also have "\<dots> = (\<Sum>x\<in>set lst. f x * x $ i)"
      unfolding f_def sum_distrib_right apply (subst sum.swap)
      apply(rule sum.cong[OF refl])
      unfolding if_distrib if_distribR mult_zero_left sum.delta[OF finite_set] by auto
    also have "\<dots> = (\<Sum>x\<in>set lst. (f x \<cdot>\<^sub>v x) $ i)"
      apply(rule sum.cong[OF refl],subst index_smult_vec) using i slc by auto
    also have "\<dots> = (\<Oplus>\<^bsub>V\<^esub>v\<in>set lst. f v \<cdot>\<^sub>v v) $ i" 
      unfolding finsum_index[OF i' fcarr slc] by auto
    finally show "(mat_of_cols n lst *\<^sub>v v) $ i = lincomb f (set lst) $ i"
      by (auto simp:lincomb_def)
  qed
qed


lemma lattice_of_altdef_lincomb:
  assumes "set fs \<subseteq> carrier_vec n"
  shows "lattice_of fs = {y. \<exists>f. lincomb (of_int \<circ> f) (set fs) = y}"
  unfolding lincomb_def lattice_of_altdef[OF assms] image_def by auto

end

context vec_module
begin

(*Generalized version of thm idom_vec.lincomb_as_lincomb_list, now in vec_module*)
lemma lincomb_as_lincomb_list:
  fixes ws f
  assumes s: "set ws \<subseteq> carrier_vec n"
  shows "lincomb f (set ws) = lincomb_list (\<lambda>i. if \<exists>j<i. ws!i = ws!j then 0 else f (ws ! i)) ws"
  using assms
proof (induct ws rule: rev_induct)
  case (snoc a ws)
  let ?f = "\<lambda>i. if \<exists>j<i. ws ! i = ws ! j then 0 else f (ws ! i)"
  let ?g = "\<lambda>i. (if \<exists>j<i. (ws @ [a]) ! i = (ws @ [a]) ! j then 0 else f ((ws @ [a]) ! i)) \<cdot>\<^sub>v (ws @ [a]) ! i"
  let ?g2= "(\<lambda>i. (if \<exists>j<i. ws ! i = ws ! j then 0 else f (ws ! i)) \<cdot>\<^sub>v ws ! i)"
  have [simp]: "\<And>v. v \<in> set ws \<Longrightarrow> v \<in> carrier_vec n" using snoc.prems(1) by auto
  then have ws: "set ws \<subseteq> carrier_vec n" by auto
  have hyp: "lincomb f (set ws) = lincomb_list ?f ws"
    by (intro snoc.hyps ws)  
  show ?case
  proof (cases "a\<in>set ws")
    case True    
    have g_length: "?g (length ws) = 0\<^sub>v n" using True
      by (auto, metis in_set_conv_nth nth_append)
    have "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [?g (length ws)]"
       by auto
    also have "... = (map ?g [0..<length ws]) @ [0\<^sub>v n]" using g_length by simp
    finally have map_rw: "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [0\<^sub>v n]" .
    have "M.sumlist (map ?g2 [0..<length ws]) = M.sumlist (map ?g [0..<length ws])"
      by (rule arg_cong[of _ _ "M.sumlist"], intro nth_equalityI, auto simp add: nth_append)
    also have "... =  M.sumlist (map ?g [0..<length ws]) + 0\<^sub>v n "
      by (metis M.r_zero calculation hyp lincomb_closed lincomb_list_def ws)
    also have "... = M.sumlist (map ?g [0..<length ws] @ [0\<^sub>v n])" 
      by (rule M.sumlist_snoc[symmetric], auto simp add: nth_append)
    finally have summlist_rw: "M.sumlist (map ?g2 [0..<length ws]) 
      = M.sumlist (map ?g [0..<length ws] @ [0\<^sub>v n])" .
    have "lincomb f (set (ws @ [a])) = lincomb f (set ws)" using True unfolding lincomb_def
      by (simp add: insert_absorb)
    thus ?thesis 
      unfolding hyp lincomb_list_def map_rw summlist_rw
      by auto
  next
    case False    
    have g_length: "?g (length ws) = f a \<cdot>\<^sub>v a" using False by (auto simp add: nth_append)
    have "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [?g (length ws)]"
       by auto
    also have "... = (map ?g [0..<length ws]) @ [(f a \<cdot>\<^sub>v a)]" using g_length by simp
    finally have map_rw: "(map ?g [0..<length (ws @ [a])]) = (map ?g [0..<length ws]) @ [(f a \<cdot>\<^sub>v a)]" .
    have summlist_rw: "M.sumlist (map ?g2 [0..<length ws]) = M.sumlist (map ?g [0..<length ws])"
      by (rule arg_cong[of _ _ "M.sumlist"], intro nth_equalityI, auto simp add: nth_append)
    have "lincomb f (set (ws @ [a])) = lincomb f (set (a # ws))" by auto
    also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in>set (a # ws). f v \<cdot>\<^sub>v v)" unfolding lincomb_def ..
    also have "... = (\<Oplus>\<^bsub>V\<^esub>v\<in> insert a (set ws). f v \<cdot>\<^sub>v v)" by simp    
    also have "... = (f a \<cdot>\<^sub>v a) + (\<Oplus>\<^bsub>V\<^esub>v\<in> (set ws). f v \<cdot>\<^sub>v v)"
    proof (rule finsum_insert)
      show "finite (set ws)" by auto
      show "a \<notin> set ws" using False by auto
      show "(\<lambda>v. f v \<cdot>\<^sub>v v) \<in> set ws \<rightarrow> carrier_vec n"
        using snoc.prems(1) by auto
      show "f a \<cdot>\<^sub>v a \<in> carrier_vec n" using snoc.prems by auto
    qed
    also have "... = (f a \<cdot>\<^sub>v a) + lincomb f (set ws)" unfolding lincomb_def ..
    also have "... = (f a \<cdot>\<^sub>v a) + lincomb_list ?f ws" using hyp by auto
    also have "... =  lincomb_list ?f ws  + (f a \<cdot>\<^sub>v a)"
      using M.add.m_comm lincomb_list_carrier snoc.prems by auto
    also have "... = lincomb_list (\<lambda>i. if \<exists>j<i. (ws @ [a]) ! i 
      = (ws @ [a]) ! j then 0 else f ((ws @ [a]) ! i)) (ws @ [a])" 
    proof (unfold lincomb_list_def map_rw summlist_rw, rule M.sumlist_snoc[symmetric])
      show "set (map ?g [0..<length ws]) \<subseteq> carrier_vec n" using snoc.prems
        by (auto simp add: nth_append)
      show "f a \<cdot>\<^sub>v a \<in> carrier_vec n"
        using snoc.prems by auto
    qed
    finally show ?thesis .
  qed
qed auto
end

context 
begin

interpretation vec_module "TYPE(int)" .

lemma lattice_of_cols_as_mat_mult:
  assumes A: "A \<in> carrier_mat n nc" (*Integer matrix*)
  shows "lattice_of (cols A) = {y\<in>carrier_vec (dim_row A). \<exists>x\<in>carrier_vec (dim_col A). A *\<^sub>v x = y}"
proof -
  let ?ws = "cols A"
  have set_cols_in: "set (cols A) \<subseteq> carrier_vec n" using A unfolding cols_def by auto
  have "lincomb (of_int \<circ> f)(set  ?ws) \<in> carrier_vec (dim_row A)" for f 
    using lincomb_closed A
    by (metis (full_types) carrier_matD(1) cols_dim lincomb_closed)
  moreover have "\<exists>x\<in>carrier_vec (dim_col A). A *\<^sub>v x = lincomb (of_int \<circ> f) (set (cols A))" for f
  proof -    
    let ?g = "(\<lambda>v. of_int (f v))"
    let ?g' = "(\<lambda>i. if \<exists>j<i. ?ws ! i = ?ws ! j then 0 else ?g (?ws ! i))"           
    have "lincomb (of_int \<circ> f) (set (cols A)) = lincomb ?g (set ?ws)" unfolding o_def by auto
    also have "... = lincomb_list ?g' ?ws" 
      by (rule lincomb_as_lincomb_list[OF set_cols_in])
    also have "... = mat_of_cols n ?ws *\<^sub>v vec (length ?ws) ?g'" 
      by (rule lincomb_list_as_mat_mult, insert set_cols_in A, auto)
    also have "... = A *\<^sub>v (vec (length ?ws) ?g')" using mat_of_cols_cols A by auto
    finally show ?thesis by auto
  qed 
  moreover have "\<exists>f. A *\<^sub>v x = lincomb (of_int \<circ> f) (set (cols A))" 
    if Ax: "A *\<^sub>v x \<in> carrier_vec (dim_row A)" and x: "x \<in> carrier_vec (dim_col A)" for x 
  proof -
    let ?c = "\<lambda>i. x $ i"
    have x_vec: "vec (length ?ws) ?c = x" using x by auto
    have "A *\<^sub>v x = mat_of_cols n ?ws *\<^sub>v vec (length ?ws) ?c" using mat_of_cols_cols A x_vec by auto
    also have "... = lincomb_list ?c ?ws"
      by (rule lincomb_list_as_mat_mult[symmetric], insert set_cols_in A, auto)
    also have "... = lincomb (mk_coeff ?ws ?c) (set ?ws)" 
      by (rule lincomb_list_as_lincomb, insert set_cols_in A, auto)    
    finally show ?thesis by auto
  qed
  ultimately show ?thesis unfolding lattice_of_altdef_lincomb[OF set_cols_in]
    by (metis (mono_tags, hide_lams))
qed


corollary lattice_of_as_mat_mult:
  assumes fs: "set fs \<subseteq> carrier_vec n"
  shows "lattice_of fs = {y\<in>carrier_vec n. \<exists>x\<in>carrier_vec (length fs). (mat_of_cols n fs) *\<^sub>v x = y}"
proof -
  have cols_eq: "cols (mat_of_cols n fs) = fs" using cols_mat_of_cols[OF fs] by simp
  have m: "(mat_of_cols n fs) \<in> carrier_mat n (length fs)" using mat_of_cols_carrier(1) by auto
  show ?thesis using lattice_of_cols_as_mat_mult[OF m] unfolding cols_eq using m by auto
qed
end

context vec_space
begin

lemma lin_indpt_cols_imp_det_not_0:
  fixes A::"'a mat"
  assumes A: "A \<in> carrier_mat n n" and li: "lin_indpt (set (cols A))" and d: "distinct (cols A)" 
  shows "det A \<noteq> 0"  
  using A li d det_rank_iff lin_indpt_full_rank by blast

corollary lin_indpt_rows_imp_det_not_0:
  fixes A::"'a mat"
  assumes A: "A \<in> carrier_mat n n" and li: "lin_indpt (set (rows A))" and d: "distinct (rows A)" 
  shows "det A \<noteq> 0"  
  using A li d det_rank_iff lin_indpt_full_rank
  by (metis (full_types) Determinant.det_transpose cols_transpose transpose_carrier_mat)
end

context LLL
begin

lemma eq_lattice_imp_mat_mult_invertible_cols:
  assumes fs: "set fs \<subseteq> carrier_vec n"
  and gs: "set gs \<subseteq> carrier_vec n"  and ind_fs: "lin_indep fs" (*fs is a basis*)
  and length_fs: "length fs = n" and length_gs: "length gs = n" (*For the moment, only valid for square matrices*)
  and l: "lattice_of fs = lattice_of gs" 
shows "\<exists>Q \<in> carrier_mat n n. invertible_mat Q \<and> mat_of_cols n fs = mat_of_cols n gs * Q"
proof (cases "n=0")
  case True
  show ?thesis
    by (rule bexI[of _ "1\<^sub>m 0"], insert True assms, auto) 
next
  case False
  hence n: "0<n" by simp
  have ind_RAT_fs: "gs.lin_indpt (set (RAT fs))" using ind_fs
    by (simp add: cof_vec_space.lin_indpt_list_def)
  have fs_carrier: "mat_of_cols n fs \<in> carrier_mat n n" by (simp add: length_fs carrier_matI)
  let ?f = "(\<lambda>i. SOME x. x\<in>carrier_vec (length gs) \<and> (mat_of_cols n gs) *\<^sub>v x = fs ! i)"
  let ?cols_Q = "map ?f [0..<length fs]"
  let ?Q = "mat_of_cols n ?cols_Q"
  show ?thesis
  proof (rule bexI[of _ ?Q], rule conjI)
    show Q: "?Q \<in> carrier_mat n n" using length_fs by auto
    show fs_gs_Q: "mat_of_cols n fs = mat_of_cols n gs * ?Q"
    proof (rule mat_col_eqI)
      fix j assume j: "j < dim_col (mat_of_cols n gs * ?Q)"
      have j2: "j<n" using j Q length_gs by auto
      have fs_j_in_gs: "fs ! j \<in> lattice_of gs" using fs l basis_in_latticeI j by auto
      have fs_j_carrier_vec: "fs ! j \<in> carrier_vec n"
        using fs_j_in_gs gs lattice_of_as_mat_mult by blast      
      let ?x = "SOME x. x\<in>carrier_vec (length gs) \<and> (mat_of_cols n gs) *\<^sub>v x = fs ! j"
      have "?x\<in>carrier_vec (length gs) \<and> (mat_of_cols n gs) *\<^sub>v ?x = fs ! j"
        by (rule someI_ex, insert fs_j_in_gs lattice_of_as_mat_mult[OF gs], auto)
      hence x: "?x \<in> carrier_vec (length gs)"
        and gs_x: "(mat_of_cols n gs) *\<^sub>v ?x = fs ! j" by blast+
      have "col ?Q j = ?cols_Q ! j"
      proof (rule col_mat_of_cols)
        show "j < length (map ?f [0..<length fs])" using length_fs j2 by auto
        have "map ?f [0..<length fs] ! j = ?f ([0..<length fs] ! j)" 
          by (rule nth_map, insert j2 length_fs, auto) 
        also have "... = ?f j" by (simp add: length_fs j2)
        also have "... \<in> carrier_vec n" using x length_gs by auto        
        finally show "map ?f [0..<length fs] ! j \<in> carrier_vec n" .
      qed
      also have "... = ?f ([0..<length fs] ! j)" 
        by (rule nth_map, insert j2 length_fs, auto)
      also have "... = ?x" by (simp add: length_fs j2)
      finally have col_Qj_x: "col ?Q j = ?x" .
      have "col (mat_of_cols n fs) j = fs ! j"
        by (metis (no_types, lifting) j Q fs length_fs carrier_matD(2) cols_mat_of_cols cols_nth
            index_mult_mat(3) mat_of_cols_carrier(3))
      also have "... = (mat_of_cols n gs) *\<^sub>v ?x" using gs_x by auto
      also have "... = (mat_of_cols n gs) *\<^sub>v (col ?Q j)" unfolding col_Qj_x by simp
      also have "... = col (mat_of_cols n gs * ?Q) j"
        by (rule col_mult2[symmetric, OF _ Q j2], insert length_gs mat_of_cols_def, auto)
      finally show "col (mat_of_cols n fs) j = col (mat_of_cols n gs * ?Q) j" .      
    qed (insert length_gs gs, auto)
    show "invertible_mat ?Q"
    (* Sketch of the proof:
      1) fs = gs * Q, proved previously
      2) gs = fs * Q', similar proof as the previous one.
      3) fs = fs * Q' * Q
      4) fs * (?Q' * ?Q - 1\<^sub>m n) = 0\<^sub>m n n and hence (?Q' * ?Q - 1\<^sub>m n) = 0 since fs independent
      5) det ?Q' = det ?Q = det 1 = 1, then det ?Q = \<plusminus>1 and ?Q invertible since the determinant 
         divides a unit.
    *)
    proof -
      let ?f' = "(\<lambda>i. SOME x. x\<in>carrier_vec (length fs) \<and> (mat_of_cols n fs) *\<^sub>v x = gs ! i)"
      let ?cols_Q' = "map ?f' [0..<length gs]"
      let ?Q' = "mat_of_cols n ?cols_Q'"
      have Q': "?Q' \<in> carrier_mat n n" using length_gs by auto
      have gs_fs_Q': "mat_of_cols n gs = mat_of_cols n fs * ?Q'"
      proof (rule mat_col_eqI)
        fix j assume j: "j < dim_col (mat_of_cols n fs * ?Q')"
        have j2: "j<n" using j Q length_gs by auto
        have gs_j_in_fs: "gs ! j \<in> lattice_of fs" using gs l basis_in_latticeI j by auto
        have gs_j_carrier_vec: "gs ! j \<in> carrier_vec n"
          using gs_j_in_fs fs lattice_of_as_mat_mult by blast      
        let ?x = "SOME x. x\<in>carrier_vec (length fs) \<and> (mat_of_cols n fs) *\<^sub>v x = gs ! j"
        have "?x\<in>carrier_vec (length fs) \<and> (mat_of_cols n fs) *\<^sub>v ?x = gs ! j"
          by (rule someI_ex, insert gs_j_in_fs lattice_of_as_mat_mult[OF fs], auto)
        hence x: "?x \<in> carrier_vec (length fs)"
          and fs_x: "(mat_of_cols n fs) *\<^sub>v ?x = gs ! j" by blast+
        have "col ?Q' j = ?cols_Q' ! j"
        proof (rule col_mat_of_cols)
          show "j < length (map ?f' [0..<length gs])" using length_gs j2 by auto
          have "map ?f' [0..<length gs] ! j = ?f' ([0..<length gs] ! j)" 
            by (rule nth_map, insert j2 length_gs, auto) 
          also have "... = ?f' j" by (simp add: length_gs j2)
          also have "... \<in> carrier_vec n" using x length_fs by auto        
          finally show "map ?f' [0..<length gs] ! j \<in> carrier_vec n" .
        qed
        also have "... = ?f' ([0..<length gs] ! j)" 
          by (rule nth_map, insert j2 length_gs, auto)
        also have "... = ?x" by (simp add: length_gs j2)
        finally have col_Qj_x: "col ?Q' j = ?x" .
        have "col (mat_of_cols n gs) j = gs ! j" by (simp add: length_gs gs_j_carrier_vec j2)
        also have "... = (mat_of_cols n fs) *\<^sub>v ?x" using fs_x by auto
        also have "... = (mat_of_cols n fs) *\<^sub>v (col ?Q' j)" unfolding col_Qj_x by simp
        also have "... = col (mat_of_cols n fs * ?Q') j"
          by (rule col_mult2[symmetric, OF _ Q' j2], insert length_fs mat_of_cols_def, auto)
        finally show "col (mat_of_cols n gs) j = col (mat_of_cols n fs * ?Q') j" .      
      qed (insert length_fs fs, auto)
      
      have det_fs_not_zero: "rat_of_int (det (mat_of_cols n fs)) \<noteq> 0"
      proof -
        let ?A = "(of_int_hom.mat_hom (mat_of_cols n fs)):: rat mat"
        have "rat_of_int (det (mat_of_cols n fs)) = det ?A"
          by simp
        moreover have "det ?A \<noteq> 0"
        proof (rule gs.lin_indpt_cols_imp_det_not_0[of ?A])
          have c_eq: "(set (cols ?A)) = set (RAT fs)"
            by (metis assms(3) cof_vec_space.lin_indpt_list_def cols_mat_of_cols fs mat_of_cols_map)
          show "?A \<in> carrier_mat n n" by (simp add: fs_carrier)
          show "gs.lin_indpt (set (cols ?A))" using ind_RAT_fs c_eq by auto
          show "distinct (cols ?A)"
            by (metis ind_fs cof_vec_space.lin_indpt_list_def cols_mat_of_cols fs mat_of_cols_map)
        qed
        ultimately show ?thesis by auto
      qed
      have Q'Q: "?Q' * ?Q \<in> carrier_mat n n" using Q Q' mult_carrier_mat by blast
      have fs_fs_Q'Q: "mat_of_cols n fs = mat_of_cols n fs * ?Q' * ?Q" using gs_fs_Q' fs_gs_Q by presburger
      hence "0\<^sub>m n n = mat_of_cols n fs * ?Q' * ?Q - mat_of_cols n fs" using length_fs by auto
      also have "... = mat_of_cols n fs * ?Q' * ?Q - mat_of_cols n fs * 1\<^sub>m n"
        using fs_carrier by auto
      also have "... = mat_of_cols n fs * (?Q' * ?Q) - mat_of_cols n fs * 1\<^sub>m n"
        using Q Q' fs_carrier by auto
      also have "... = mat_of_cols n fs * (?Q' * ?Q - 1\<^sub>m n)"
        by (rule mult_minus_distrib_mat[symmetric, OF fs_carrier Q'Q], auto)      
      finally have "mat_of_cols n fs * (?Q' * ?Q - 1\<^sub>m n) = 0\<^sub>m n n" ..
      have "det (?Q' * ?Q) = 1"
        by (smt Determinant.det_mult Q Q' Q'Q fs_fs_Q'Q assoc_mult_mat det_fs_not_zero 
            fs_carrier mult_cancel_left2 of_int_code(2))
      hence det_Q'_Q_1: "det ?Q * det ?Q' = 1"
        by (metis (no_types, lifting) Determinant.det_mult Groups.mult_ac(2) Q Q')
      hence "det ?Q = 1 \<or> det ?Q = -1" by (rule pos_zmult_eq_1_iff_lemma)
      thus ?thesis using invertible_iff_is_unit_JNF[OF Q] by fastforce
    qed
  qed
qed


corollary eq_lattice_imp_mat_mult_invertible_rows:
  assumes fs: "set fs \<subseteq> carrier_vec n"
  and gs: "set gs \<subseteq> carrier_vec n"  and ind_fs: "lin_indep fs" (*fs is a basis*)
  and length_fs: "length fs = n" and length_gs: "length gs = n" (*For the moment, only valid for square matrices*)
  and l: "lattice_of fs = lattice_of gs" 
shows "\<exists>P \<in> carrier_mat n n. invertible_mat P \<and> mat_of_rows n fs = P * mat_of_rows n gs"
proof -
  obtain Q where Q: "Q \<in> carrier_mat n n" and inv_Q: "invertible_mat Q" 
    and fs_gs_Q: "mat_of_cols n fs = mat_of_cols n gs * Q" 
    using eq_lattice_imp_mat_mult_invertible_cols[OF assms] by auto
  have "invertible_mat Q\<^sup>T" by (simp add: inv_Q invertible_mat_transpose)
  moreover have "mat_of_rows n fs = Q\<^sup>T * mat_of_rows n gs" using fs_gs_Q
    by (metis Matrix.transpose_mult Q length_gs mat_of_cols_carrier(1) transpose_mat_of_cols)
  moreover have "Q\<^sup>T \<in> carrier_mat n n" using Q by auto
  ultimately show ?thesis by blast
qed
end

subsubsection \<open>Missing results\<close>

text \<open>This is a new definition for upper triangular matrix, valid for rectangular matrices. 
This definition will allow us to prove that echelon form implies upper triangular for any matrix.\<close>

definition "upper_triangular' A = (\<forall>i < dim_row A. \<forall> j<dim_col A. j < i \<longrightarrow> A $$ (i,j) = 0)"

lemma upper_triangular'D[elim] :
  "upper_triangular' A \<Longrightarrow> j<dim_col A \<Longrightarrow> j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0"
unfolding upper_triangular'_def by auto

lemma upper_triangular'I[intro] :
  "(\<And>i j. j<dim_col A \<Longrightarrow> j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0) \<Longrightarrow> upper_triangular' A"
  unfolding upper_triangular'_def by auto

lemma prod_list_abs(*[simp]?*):
  fixes xs:: "int list"
  shows "prod_list (map abs xs) = abs (prod_list xs)"
  by (induct xs, auto simp add: abs_mult)

lemma euclid_ext2_works:
  assumes "euclid_ext2 a b = (p,q,u,v,d)"
  shows "p*a+q*b = d" and "d = gcd a b" and "gcd a b * u = -b" and "gcd a b * v = a"
  and "u = -b div gcd a b" and "v = a div gcd a b"
  using assms unfolding euclid_ext2_def
  by (auto simp add: bezout_coefficients_fst_snd)

lemma res_function_euclidean2: 
  "res_function (\<lambda>b n::'a::{unique_euclidean_ring}. n mod b)"
proof- 
  have "n mod b = n" if "b=0" for n b::"'a :: unique_euclidean_ring" using that by auto
  hence "res_function_euclidean = (\<lambda>b n::'a. n mod b)" 
    by (unfold fun_eq_iff res_function_euclidean_def, auto)
  thus ?thesis using res_function_euclidean by auto
qed

lemma mult_row_1_id:
  fixes A:: "'a::semiring_1^'n^'m"
  shows "mult_row A b 1 = A" unfolding mult_row_def by vector

text \<open>Results about appending rows\<close>

lemma row_append_rows1:
  assumes A: "A \<in> carrier_mat m n"
  and B: "B \<in> carrier_mat p n"
  assumes i: "i < dim_row A"
  shows "Matrix.row (A @\<^sub>r B) i = Matrix.row A i"  
proof (rule eq_vecI)
  have AB_carrier[simp]: "(A @\<^sub>r B) \<in> carrier_mat (m+p) n" by (rule carrier_append_rows[OF A B])
  thus "dim_vec (Matrix.row (A @\<^sub>r B) i) = dim_vec (Matrix.row A i)"
    using A B by (auto, insert carrier_matD(2), blast)
  fix j assume j: "j < dim_vec (Matrix.row A i)" 
  have "Matrix.row (A @\<^sub>r B) i $v j = (A @\<^sub>r B) $$ (i, j)"
    by (metis AB_carrier Matrix.row_def j A carrier_matD(2) index_row(2) index_vec)
  also have "... = (if i < dim_row A then A $$ (i, j) else B $$ (i - m, j))"
    by (rule append_rows_nth, insert assms j, auto)
  also have "... = A$$ (i,j)" using i by simp
  finally show "Matrix.row (A @\<^sub>r B) i $v j = Matrix.row A i $v j" using i j by simp  
qed

lemma row_append_rows2:
  assumes A: "A \<in> carrier_mat m n"
  and B: "B \<in> carrier_mat p n"
  assumes i: "i \<in> {m..<m+p}"
  shows "Matrix.row (A @\<^sub>r B) i = Matrix.row B (i - m)"
proof (rule eq_vecI)
  have AB_carrier[simp]: "(A @\<^sub>r B) \<in> carrier_mat (m+p) n" by (rule carrier_append_rows[OF A B])
  thus "dim_vec (Matrix.row (A @\<^sub>r B) i) = dim_vec (Matrix.row B (i-m))"
    using A B by (auto, insert carrier_matD(2), blast)
  fix j assume j: "j < dim_vec (Matrix.row B (i-m))" 
  have "Matrix.row (A @\<^sub>r B) i $v j = (A @\<^sub>r B) $$ (i, j)"
    by (metis AB_carrier Matrix.row_def j B carrier_matD(2) index_row(2) index_vec)
  also have "... = (if i < dim_row A then A $$ (i, j) else B $$ (i - m, j))"
    by (rule append_rows_nth, insert assms j, auto)
  also have "... = B $$ (i - m, j)" using i A by simp
  finally show "Matrix.row (A @\<^sub>r B) i $v j = Matrix.row B (i-m) $v j" using i j A B by auto  
qed


lemma rows_append_rows:
  assumes A: "A \<in> carrier_mat m n"
  and B: "B \<in> carrier_mat p n"
shows "Matrix.rows (A @\<^sub>r B) = Matrix.rows A @ Matrix.rows B"
proof -
  have AB_carrier: "(A @\<^sub>r B) \<in> carrier_mat (m+p) n" 
    by (rule carrier_append_rows, insert A B, auto)
  hence 1: "dim_row (A @\<^sub>r B) = dim_row A + dim_row B" using A B by blast
  moreover have "Matrix.row (A @\<^sub>r B) i = (Matrix.rows A @ Matrix.rows B) ! i"
    if i: "i < dim_row (A @\<^sub>r B)" for i
  proof (cases "i<dim_row A")
    case True
    have "Matrix.row (A @\<^sub>r B) i = Matrix.row A i" using A True B row_append_rows1 by blast
    also have "... = Matrix.rows A ! i" unfolding Matrix.rows_def using True by auto
    also have "... = (Matrix.rows A @ Matrix.rows B) ! i" using True by (simp add: nth_append)
    finally show ?thesis .
  next
    case False
    have i_mp: "i < m + p" using AB_carrier A B i by fastforce
    have "Matrix.row (A @\<^sub>r B) i = Matrix.row B (i-m)" using A False B i row_append_rows2 i_mp
      by (smt AB_carrier atLeastLessThan_iff carrier_matD(1) le_add1
          linordered_semidom_class.add_diff_inverse row_append_rows2)
    also have "... = Matrix.rows B ! (i-m)" unfolding Matrix.rows_def using False i A 1 by auto
    also have "... = (Matrix.rows A @ Matrix.rows B) ! (i-m+m)"
      by (metis add_diff_cancel_right' A carrier_matD(1) length_rows not_add_less2 nth_append)
    also have "... =  (Matrix.rows A @ Matrix.rows B) ! i" using False A by auto
    finally show ?thesis .
  qed  
  ultimately show ?thesis unfolding list_eq_iff_nth_eq by auto  
qed



lemma append_rows_nth2:
  assumes A': "A' \<in> carrier_mat m n"
  and B: "B \<in> carrier_mat p n"
  and A_def: "A = (A' @\<^sub>r  B)"
  and a: "a<m" and ap: "a < p" and j: "j<n"
  shows "A $$ (a + m, j) = B $$ (a,j)" 
proof -
  have "A $$ (a + m, j) = (if a + m < dim_row A' then A' $$ (a + m, j) else B $$ (a + m - m, j))"
    unfolding A_def by (rule append_rows_nth[OF A' B _ j], insert ap a, auto)
  also have "... = B $$ (a,j)" using ap a A' by auto
  finally show ?thesis .
qed


lemma append_rows_nth3:
  assumes A': "A' \<in> carrier_mat m n"
  and B: "B \<in> carrier_mat p n"
  and A_def: "A = (A' @\<^sub>r  B)"
  and a: "a\<ge>m" and ap: "a < m + p" and j: "j<n"
  shows "A $$ (a, j) = B $$ (a-m,j)" 
proof -
  have "A $$ (a, j) = (if a < dim_row A' then A' $$ (a, j) else B $$ (a - m, j))"
    unfolding A_def by (rule append_rows_nth[OF A' B _ j], insert ap a, auto)
  also have "... = B $$ (a-m,j)" using ap a A' by auto
  finally show ?thesis .
qed


text \<open>Results about submatrices\<close>

lemma pick_first_id: assumes i: "i<n" shows "pick {0..<n} i = i"
proof -
  have "i = (card {a \<in> {0..<n}. a < i})" using i
    by (auto, smt Collect_cong card_Collect_less_nat nat_SN.gt_trans)
  thus ?thesis using pick_card_in_set i
    by (metis atLeastLessThan_iff zero_order(1))
qed

lemma submatrix_index_id:
  assumes H: "H \<in> carrier_mat m n" and i: "i<k1" and j: "j<k2"
  and k1: "k1\<le>m" and k2: "k2\<le>n"
  shows "(submatrix H {0..<k1} {0..<k2}) $$ (i,j) = H $$ (i,j)" 
proof -
  let ?I = "{0..<k1}"
  let ?J = "{0..<k2}"
  let ?H = "submatrix H ?I ?J"  
  have km: "k1\<le>m" and kn: "k2\<le>n" using k1 k2 by simp+
  have card_mk: "card {i. i < m \<and> i < k1} = k1" using km 
    by (smt Collect_cong card_Collect_less_nat le_eq_less_or_eq nat_less_induct nat_neq_iff)
  have card_nk: "card {i. i < n \<and> i < k2} = k2" using kn 
    by (smt Collect_cong card_Collect_less_nat le_eq_less_or_eq nat_less_induct nat_neq_iff)
  show ?thesis
  proof- 
    have pick_j: "pick ?J j = j" by (rule pick_first_id[OF j])
    have pick_i: "pick ?I i = i" by (rule pick_first_id[OF i])
    have "submatrix H ?I ?J $$ (i, j) = H $$ (pick ?I i, pick ?J j)" 
      by (rule submatrix_index, insert H i j card_mk card_nk, auto)
    also have "... = H $$ (i,j)" using pick_i pick_j by simp
    finally show ?thesis .
  qed
qed

lemma submatrix_carrier_first:
  assumes H: "H \<in> carrier_mat m n"
  and k1: "k1 \<le> m" and k2: "k2 \<le> n"
  shows"submatrix H {0..<k1} {0..<k2} \<in> carrier_mat k1 k2"
proof -  
  have km: "k1\<le>m" and kn: "k2\<le>n" using k1 k2 by simp+
  have card_mk: "card {i. i < m \<and> i < k1} = k1" using km 
    by (smt Collect_cong card_Collect_less_nat le_eq_less_or_eq nat_less_induct nat_neq_iff)
  have card_nk: "card {i. i < n \<and> i < k2} = k2" using kn 
    by (smt Collect_cong card_Collect_less_nat le_eq_less_or_eq nat_less_induct nat_neq_iff)
  show ?thesis
    by (smt Collect_cong H atLeastLessThan_iff card_mk card_nk carrier_matD 
        carrier_matI dim_submatrix zero_order(1))
qed



lemma Units_eq_invertible_mat:
  assumes "A \<in> carrier_mat n n"
  shows "A \<in> Group.Units (ring_mat TYPE('a::comm_ring_1) n b) = invertible_mat A" (is "?lhs = ?rhs")
proof -
  interpret m: ring "ring_mat TYPE('a) n b" by (rule ring_mat)
  show ?thesis
  proof
    assume "?lhs" thus "?rhs"
      unfolding Group.Units_def 
      by (insert assms, auto simp add: ring_mat_def invertible_mat_def inverts_mat_def)
  next
    assume "?rhs" 
    from this obtain B where AB: "A * B = 1\<^sub>m n" and BA: "B * A = 1\<^sub>m n" and B: "B \<in> carrier_mat n n"
      by (metis assms carrier_matD(1) inverts_mat_def obtain_inverse_matrix)
    hence "\<exists>x\<in>carrier (ring_mat TYPE('a) n b). x \<otimes>\<^bsub>ring_mat TYPE('a) n b\<^esub> A = \<one>\<^bsub>ring_mat TYPE('a) n b\<^esub> 
      \<and> A \<otimes>\<^bsub>ring_mat TYPE('a) n b\<^esub> x = \<one>\<^bsub>ring_mat TYPE('a) n b\<^esub>"
      unfolding ring_mat_def by auto
    thus "?lhs" unfolding Group.Units_def using assms unfolding ring_mat_def by auto
  qed
qed

lemma map_first_rows_index:
  assumes "A \<in> carrier_mat M n" and "m \<le> M" and "i<m" and "ja<n"
  shows "map (Matrix.row A) [0..<m] ! i $v ja = A $$ (i, ja)"
  using assms by auto

lemma matrix_append_rows_eq_if_preserves:
  assumes A: "A \<in> carrier_mat (m+p) n" and B: "B \<in> carrier_mat p n"
    and eq: "\<forall>i\<in>{m..<m+p}.\<forall>j<n. A$$(i,j) = B $$ (i-m,j)"
  shows "A = mat_of_rows n [Matrix.row A i. i \<leftarrow> [0..<m]] @\<^sub>r B" (is "_ = ?A' @\<^sub>r _")
proof (rule eq_matI)
  have A': "?A' \<in> carrier_mat m n" by (simp add: mat_of_rows_def)
  hence A'B: "?A' @\<^sub>r B \<in> carrier_mat (m+p) n" using B by blast
  show "dim_row A = dim_row (?A' @\<^sub>r B)" and "dim_col A = dim_col (?A' @\<^sub>r B)" using A'B A by auto
  fix i j assume i: "i < dim_row (?A' @\<^sub>r B)"
    and j: "j < dim_col (?A' @\<^sub>r B)" 
  have jn: "j<n" using A
    by (metis append_rows_def dim_col_mat(1) index_mat_four_block(3) index_zero_mat(3) 
        j mat_of_rows_def nat_arith.rule0)
  let ?xs = "(map (Matrix.row A) [0..<m])"
  show "A $$ (i, j) = (?A' @\<^sub>r B) $$ (i, j)"
  proof (cases "i<m")
    case True
    have "(?A' @\<^sub>r B) $$ (i, j) = ?A' $$ (i,j)"      
      by (metis (no_types, lifting) Nat.add_0_right True append_rows_def diff_zero i 
          index_mat_four_block index_zero_mat(3) j length_map length_upt mat_of_rows_carrier(2))
    also have "... = ?xs ! i $v j" 
      by (rule mat_of_rows_index, insert i True j, auto simp add: append_rows_def)
    also have "... = A $$ (i,j)"
      by (rule map_first_rows_index, insert assms A True i jn, auto)
    finally show ?thesis ..
  next
    case False
    have "(?A' @\<^sub>r B) $$ (i, j) = B $$ (i-m,j)"      
      by (smt (z3) A' carrier_matD(1) False append_rows_def i index_mat_four_block j jn length_map
          length_upt mat_of_rows_carrier(2,3))
    also have "... = A $$ (i,j)"
      by (metis False append_rows_def B eq atLeastLessThan_iff carrier_matD(1) diff_zero i 
          index_mat_four_block(2) index_zero_mat(2) jn le_add1 length_map length_upt 
          linordered_semidom_class.add_diff_inverse mat_of_rows_carrier(2))
    finally show ?thesis ..
  qed
qed

lemma invertible_mat_first_column_not0:
  fixes A::"'a :: comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat n n" and inv_A: "invertible_mat A" and n0: "0<n"
  shows "col A 0 \<noteq> (0\<^sub>v n)"
proof (rule ccontr)
  assume " \<not> col A 0 \<noteq> 0\<^sub>v n" hence col_A0: "col A 0 = 0\<^sub>v n" by simp
  have "(det A dvd 1)" using inv_A invertible_iff_is_unit_JNF[OF A] by auto
  hence 1: "det A \<noteq> 0" by auto
  have "det A = (\<Sum>i<n. A $$ (i, 0) * Determinant.cofactor A i 0)" 
    by (rule laplace_expansion_column[OF A n0])
  also have "... = 0" 
    by (rule sum.neutral, insert col_A0 n0 A, auto simp add: col_def,
        metis Matrix.zero_vec_def index_vec mult_zero_left)
  finally show False using 1 by contradiction 
qed

lemma invertible_mat_mult_int:
  assumes "A = P * B" 
    and "P \<in> carrier_mat n n"
    and "B \<in> carrier_mat n n"
    and "invertible_mat P" 
    and "invertible_mat (map_mat rat_of_int B)"
  shows "invertible_mat (map_mat rat_of_int A)"
  by (metis (no_types, hide_lams) assms dvd_field_iff 
      invertible_iff_is_unit_JNF invertible_mult_JNF map_carrier_mat not_is_unit_0 
      of_int_hom.hom_0 of_int_hom.hom_det of_int_hom.mat_hom_mult)


lemma echelon_form_JNF_intro: 
  assumes "(\<forall>i<dim_row A. is_zero_row_JNF i A \<longrightarrow> \<not> (\<exists>j. j < dim_row A \<and> j>i \<and> \<not> is_zero_row_JNF j A))"
  and "(\<forall>i j. i<j \<and> j<dim_row A \<and> \<not> (is_zero_row_JNF i A) \<and> \<not> (is_zero_row_JNF j A) 
         \<longrightarrow> ((LEAST n. A $$ (i, n) \<noteq> 0) < (LEAST n. A $$ (j, n) \<noteq> 0)))"
  shows "echelon_form_JNF A" using assms unfolding echelon_form_JNF_def by simp


lemma echelon_form_submatrix:
  assumes ef_H: "echelon_form_JNF H" and H: "H \<in> carrier_mat m n"
  and k: "k \<le> min m n"
shows "echelon_form_JNF (submatrix H {0..<k} {0..<k})" 
proof -
  let ?I = "{0..<k}"
  let ?H = "submatrix H ?I ?I"  
  have km: "k\<le>m" and kn: "k\<le>n" using k by simp+
  have card_mk: "card {i. i < m \<and> i < k} = k" using km 
    by (smt Collect_cong card_Collect_less_nat le_eq_less_or_eq nat_less_induct nat_neq_iff)
  have card_nk: "card {i. i < n \<and> i < k} = k" using kn 
    by (smt Collect_cong card_Collect_less_nat le_eq_less_or_eq nat_less_induct nat_neq_iff)
  have H_ij: "H $$ (i,j) = (submatrix H ?I ?I) $$ (i,j)"  if i: "i<k" and j: "j<k" for i j
  proof- 
    have pick_j: "pick ?I j = j" by (rule pick_first_id[OF j])
    have pick_i: "pick ?I i = i" by (rule pick_first_id[OF i])
    have "submatrix H ?I ?I $$ (i, j) = H $$ (pick ?I i, pick ?I j)" 
      by (rule submatrix_index, insert H i j card_mk card_nk, auto)
    also have "... = H $$ (i,j)" using pick_i pick_j by simp
    finally show ?thesis ..
  qed
  have H'[simp]: "?H \<in> carrier_mat k k" 
    using H dim_submatrix[of H "{0..<k}" "{0..<k}"] card_mk card_nk by auto
  show ?thesis
  proof (rule echelon_form_JNF_intro, auto)   
    fix i j assume iH'_0: "is_zero_row_JNF i ?H" and ij: "i < j" and j: "j < dim_row ?H"  
    have jm: "j<m"
      by (metis H' carrier_matD(1) j km le_eq_less_or_eq nat_SN.gt_trans)
    show "is_zero_row_JNF j ?H"
    proof (rule ccontr)
      assume j_not0_H': "\<not> is_zero_row_JNF j ?H"
      define a where "a = (LEAST n. ?H $$ (j,n) \<noteq> 0)"
      have H'_ja: "?H $$ (j,a) \<noteq> 0" 
        by (metis (mono_tags) LeastI j_not0_H' a_def is_zero_row_JNF_def)
      have a: "a < dim_col ?H"
        by (smt j_not0_H' a_def is_zero_row_JNF_def linorder_neqE_nat not_less_Least order_trans_rules(19))
      have j_not0_H: "\<not> is_zero_row_JNF j H"
        by (metis H' H'_ja H_ij a assms(2) basic_trans_rules(19) carrier_matD is_zero_row_JNF_def j kn le_eq_less_or_eq)
      hence i_not0_H: "\<not> is_zero_row_JNF i H" using ef_H j ij unfolding echelon_form_JNF_def
        by (metis H' \<open>\<not> is_zero_row_JNF j H\<close> assms(2) carrier_matD(1) ij j km 
            not_less_iff_gr_or_eq order.strict_trans order_trans_rules(21))
      hence least_ab: "(LEAST n. H $$ (i, n) \<noteq> 0) < (LEAST n. H $$ (j, n) \<noteq> 0)" using jm
        using j_not0_H assms(2) echelon_form_JNF_def ef_H ij by blast
      define b where "b = (LEAST n. H $$ (i, n) \<noteq> 0)"
      have H_ib: "H $$ (i, b) \<noteq> 0"
        by (metis (mono_tags, lifting) LeastI b_def i_not0_H is_zero_row_JNF_def)
      have b: "b < dim_col ?H" using least_ab a unfolding a_def b_def
        by (metis (mono_tags, lifting) H' H'_ja H_ij a_def carrier_matD dual_order.strict_trans j nat_neq_iff not_less_Least)
      have H'_ib: "?H $$ (i,b) \<noteq> 0" using H_ib b H_ij H' ij j 
        by (metis H' carrier_matD dual_order.strict_trans ij j)
      hence "\<not> is_zero_row_JNF i ?H" using b is_zero_row_JNF_def by blast
      thus False using iH'_0 by contradiction
    qed  
  next
    fix i j assume ij: "i < j" and j: "j < dim_row ?H"
    have jm: "j<m"
      by (metis H' carrier_matD(1) j km le_eq_less_or_eq nat_SN.gt_trans)
    assume not0_iH': "\<not> is_zero_row_JNF i ?H"
      and not0_jH': "\<not> is_zero_row_JNF j ?H"
    define a where "a = (LEAST n. ?H $$ (i, n) \<noteq> 0)"
    define b where "b = (LEAST n. ?H $$ (j, n) \<noteq> 0)"
    have H'_ia: "?H $$ (i,a) \<noteq> 0"
      by (metis (mono_tags) LeastI_ex a_def is_zero_row_JNF_def not0_iH')
    have H'_jb: "?H $$ (j,b) \<noteq> 0"
      by (metis (mono_tags) LeastI_ex b_def is_zero_row_JNF_def not0_jH')
    have a: "a < dim_row ?H"
      by (smt H' a_def carrier_matD is_zero_row_JNF_def less_trans linorder_neqE_nat not0_iH' not_less_Least)
    have b: "b < dim_row ?H"
      by (smt H' b_def carrier_matD is_zero_row_JNF_def less_trans linorder_neqE_nat not0_jH' not_less_Least)
    have a_eq: "a = (LEAST n. H $$ (i, n) \<noteq> 0)"
      by (smt H' H'_ia H_ij LeastI_ex a a_def carrier_matD(1) ij j linorder_neqE_nat not_less_Least order_trans_rules(19))
    have b_eq: "b = (LEAST n. H $$ (j, n) \<noteq> 0)"
      by (smt H' H'_jb H_ij LeastI_ex b b_def carrier_matD(1) ij j linorder_neqE_nat not_less_Least order_trans_rules(19)) 
    have not0_iH: "\<not> is_zero_row_JNF i H" 
      by (metis H' H'_ia H_ij a H carrier_matD ij is_zero_row_JNF_def j kn le_eq_less_or_eq order.strict_trans)
    have not0_jH: "\<not> is_zero_row_JNF j H" 
      by (metis H' H'_jb H_ij b H carrier_matD is_zero_row_JNF_def j kn le_eq_less_or_eq order.strict_trans)
    show "(LEAST n. ?H $$ (i, n) \<noteq> 0) < (LEAST n. ?H $$ (j, n) \<noteq> 0)"
      unfolding a_def[symmetric] b_def[symmetric] a_eq b_eq using not0_iH not0_jH ef_H ij jm H 
      unfolding echelon_form_JNF_def by auto
  qed
qed


lemma HNF_submatrix:
  assumes HNF_H: "Hermite_JNF associates res H" and H: "H \<in> carrier_mat m n"
  and k: "k \<le> min m n"
  shows "Hermite_JNF associates res (submatrix H {0..<k} {0..<k})" 
proof -
  let ?I = "{0..<k}"
  let ?H = "submatrix H ?I ?I"  
  have km: "k\<le>m" and kn: "k\<le>n" using k by simp+
  have card_mk: "card {i. i < m \<and> i < k} = k" using km 
    by (smt Collect_cong card_Collect_less_nat le_eq_less_or_eq nat_less_induct nat_neq_iff)
  have card_nk: "card {i. i < n \<and> i < k} = k" using kn 
    by (smt Collect_cong card_Collect_less_nat le_eq_less_or_eq nat_less_induct nat_neq_iff)
  have H_ij: "H $$ (i,j) = (submatrix H ?I ?I) $$ (i,j)"  if i: "i<k" and j: "j<k" for i j
  proof- 
    have pick_j: "pick ?I j = j" by (rule pick_first_id[OF j])
    have pick_i: "pick ?I i = i" by (rule pick_first_id[OF i])
    have "submatrix H ?I ?I $$ (i, j) = H $$ (pick ?I i, pick ?I j)" 
      by (rule submatrix_index, insert H i j card_mk card_nk, auto)
    also have "... = H $$ (i,j)" using pick_i pick_j by simp
    finally show ?thesis ..
  qed
  have H'[simp]: "?H \<in> carrier_mat k k" 
    using H dim_submatrix[of H "{0..<k}" "{0..<k}"] card_mk card_nk by auto
  have CS_ass: "Complete_set_non_associates associates" using HNF_H unfolding Hermite_JNF_def by simp
  moreover have CS_res: "Complete_set_residues res"  using HNF_H unfolding Hermite_JNF_def by simp
  have ef_H: "echelon_form_JNF H" using HNF_H unfolding Hermite_JNF_def by auto
  have ef_H': "echelon_form_JNF ?H"
    by (rule echelon_form_submatrix[OF ef_H H k])
  have HNF1: "?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0) \<in> associates" 
    and HNF2: "(\<forall>j<i. ?H $$ (j, LEAST n. ?H $$ (i, n) \<noteq> 0)
               \<in> res (?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0)))"
    if i: "i<dim_row ?H" and not0_iH': "\<not> is_zero_row_JNF i ?H" for i
  proof -
    define a where "a = (LEAST n. ?H $$ (i, n) \<noteq> 0)"
    have im: "i<m"
      by (metis H' carrier_matD(1) km order.strict_trans2 that(1))
    have H'_ia: "?H $$ (i,a) \<noteq> 0"
      by (metis (mono_tags) LeastI_ex a_def is_zero_row_JNF_def not0_iH')
    have a: "a < dim_row ?H"
      by (smt H' a_def carrier_matD is_zero_row_JNF_def less_trans linorder_neqE_nat not0_iH' not_less_Least)
    have a_eq: "a = (LEAST n. H $$ (i, n) \<noteq> 0)"
      by (smt H' H'_ia H_ij LeastI_ex a a_def carrier_matD(1) i linorder_neqE_nat not_less_Least order_trans_rules(19))
    have H'_ia_H_ia: "?H $$ (i, a) = H $$ (i, a)"  by (metis H' H_ij a carrier_matD(1) i)
    have not'_iH: "\<not> is_zero_row_JNF i H"
      by (metis H' H'_ia H'_ia_H_ia a assms(2) carrier_matD(1) carrier_matD(2) is_zero_row_JNF_def kn order.strict_trans2)
    thus "?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0) \<in> associates" using im
      by (metis H'_ia_H_ia Hermite_JNF_def a_def a_eq HNF_H H carrier_matD(1))
    show "(\<forall>j<i. ?H $$ (j, LEAST n. ?H $$ (i, n) \<noteq> 0)
               \<in> res (?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0)))" 
    proof -
      { fix nn :: nat
    have ff1: "\<forall>n. ?H $$ (n, a) = H $$ (n, a) \<or> \<not> n < k"
      by (metis (no_types) H' H_ij a carrier_matD(1))
      have ff2: "i < k"
    by (metis H' carrier_matD(1) that(1))
    then have "H $$ (nn, a) \<in> res (H $$ (i, a)) \<longrightarrow> H $$ (nn, a) \<in> res (?H $$ (i, a))"
    using ff1 by (metis (no_types))
      moreover
      { assume "H $$ (nn, a) \<in> res (?H $$ (i, a))"
        then have "?H $$ (nn, a) = H $$ (nn, a) \<longrightarrow> ?H $$ (nn, a) \<in> res (?H $$ (i, a))"
            by presburger
          then have "\<not> nn < i \<or> ?H $$ (nn, LEAST n. ?H $$ (i, n) \<noteq> 0) \<in> res (?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0))"
            using ff2 ff1 a_def order.strict_trans by blast }
        ultimately have "\<not> nn < i \<or> ?H $$ (nn, LEAST n. ?H $$ (i, n) \<noteq> 0) \<in> res (?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0))"
          using Hermite_JNF_def a_eq assms(1) assms(2) im not'_iH by blast }
      then show ?thesis
        by meson
    qed
  qed
  show ?thesis using HNF1 HNF2 ef_H' CS_res CS_ass unfolding Hermite_JNF_def by blast
qed

lemma HNF_of_HNF_id:
  fixes H :: "int mat"
  assumes HNF_H: "Hermite_JNF associates res H"
  and H: "H \<in> carrier_mat n n"
  and H_P1_H1: "H = P1 * H1"
  and inv_P1: "invertible_mat P1"
  and H1: "H1 \<in> carrier_mat n n" 
  and P1: "P1 \<in> carrier_mat n n"
  and HNF_H1: "Hermite_JNF associates res H1"
  and inv_H: "invertible_mat (map_mat rat_of_int H)"
  shows "H1 = H" 
proof (rule HNF_unique_generalized_JNF[OF H P1 H1 _ H H_P1_H1])   
  show "H = (1\<^sub>m n) * H" using H by auto  
qed (insert assms, auto)


(*Some of the following lemmas could be moved outside this context*)

context
  fixes n :: nat
begin

interpretation vec_module "TYPE(int)" .        

lemma lattice_is_monotone:
  fixes S T
  assumes S: "set S \<subseteq> carrier_vec n"
  assumes T: "set T \<subseteq> carrier_vec n"
  assumes subs: "set S \<subseteq> set T"
  shows "lattice_of S \<subseteq> lattice_of T"
proof -
  have "\<exists>fa. lincomb fa (set T) = lincomb f (set S)" for f
  proof -
    let ?f = "\<lambda>i. if i \<in> set T - set S then 0 else f i"
    have set_T_eq: "set T = set S \<union> (set T - set S)" using subs by blast
    have l0: "lincomb ?f (set T - set S) = 0\<^sub>v n" by (rule lincomb_zero, insert T, auto)
    have "lincomb ?f (set T) = lincomb ?f (set S \<union> (set T - set S))" using set_T_eq by simp
    also have "... = lincomb ?f (set S) + lincomb ?f (set T - set S)"
      by (rule lincomb_union, insert S T subs, auto)
    also have "... = lincomb ?f (set S)" using l0 by (auto simp add: S)
    also have "... = lincomb f (set S)" using S by fastforce
    finally show ?thesis by blast    
  qed
  thus ?thesis unfolding lattice_of_altdef_lincomb[OF S] lattice_of_altdef_lincomb[OF T]
    by auto
qed

lemma lattice_of_append:
  assumes fs: "set fs \<subseteq> carrier_vec n"
  assumes gs: "set gs \<subseteq> carrier_vec n" 
  shows "lattice_of (fs @ gs) = lattice_of (gs @ fs)"
proof -
  have fsgs: "set (fs @ gs) \<subseteq> carrier_vec n" using fs gs by auto
  have gsfs: "set (gs @ fs) \<subseteq> carrier_vec n" using fs gs by auto
  show ?thesis
    unfolding lattice_of_altdef_lincomb[OF fsgs] lattice_of_altdef_lincomb[OF gsfs] 
    by auto (metis Un_commute)+
qed

lemma lattice_of_append_cons:
  assumes fs: "set fs \<subseteq> carrier_vec n"   and v: "v \<in> carrier_vec n"
  shows "lattice_of (v # fs) = lattice_of (fs @ [v])"
proof -
  have v_fs: "set (v # fs) \<subseteq> carrier_vec n" using fs v by auto
  hence fs_v: "set (fs @ [v]) \<subseteq> carrier_vec n" by simp
  show ?thesis
    unfolding lattice_of_altdef_lincomb[OF v_fs] lattice_of_altdef_lincomb[OF fs_v] by auto
qed

lemma already_in_lattice_subset:
  assumes fs: "set fs \<subseteq> carrier_vec n" and inlattice: "v \<in> lattice_of fs"
  and v: "v \<in> carrier_vec n"
  shows "lattice_of (v # fs) \<subseteq> lattice_of fs"
proof (cases "v\<in>set fs")
  case True
  then show ?thesis
    by (metis fs lattice_is_monotone set_ConsD subset_code(1))
next
  case False note v_notin_fs = False  
  obtain g where v_g: "lincomb g (set fs) = v"
    using lattice_of_altdef_lincomb[OF fs] inlattice by auto
  have v_fs: "set (v # fs) \<subseteq> carrier_vec n" using v fs by auto
  have "\<exists>fa. lincomb fa (set fs) = lincomb f (insert v (set fs))" for f
  proof -
    have smult_rw: "f v \<cdot>\<^sub>v (lincomb g (set fs)) = lincomb (\<lambda>w. f v * g w) (set fs)" 
      by (rule lincomb_smult[symmetric, OF fs])
    have "lincomb f (insert v (set fs)) =  f v \<cdot>\<^sub>v v + lincomb f (set fs)" 
      by (rule lincomb_insert2[OF _ fs _ v_notin_fs v], auto)
    also have "... = f v \<cdot>\<^sub>v (lincomb g (set fs)) + lincomb f (set fs)" using v_g by simp
    also have "... = lincomb (\<lambda>w. f v * g w) (set fs)  + lincomb f (set fs)"
      unfolding smult_rw by auto
    also have "... = lincomb (\<lambda>w. (\<lambda>w. f v * g w) w + f w) (set fs)"
      by (rule lincomb_sum[symmetric, OF _ fs], simp)
    finally show ?thesis by auto
  qed
  thus ?thesis unfolding lattice_of_altdef_lincomb[OF v_fs] lattice_of_altdef_lincomb[OF fs] by auto
qed


lemma already_in_lattice:
  assumes fs: "set fs \<subseteq> carrier_vec n" and inlattice: "v \<in> lattice_of fs"
  and v: "v \<in> carrier_vec n"
  shows "lattice_of fs = lattice_of (v # fs)"
proof - 
  have dir1: "lattice_of fs \<subseteq> lattice_of (v # fs)"
    by (intro lattice_is_monotone, insert fs v, auto)
  moreover have dir2: "lattice_of (v # fs) \<subseteq> lattice_of fs"
    by (rule already_in_lattice_subset[OF assms])
  ultimately show ?thesis by auto
qed


lemma already_in_lattice_append:
  assumes fs: "set fs \<subseteq> carrier_vec n" and inlattice: "lattice_of gs \<subseteq> lattice_of fs"
  and gs: "set gs \<subseteq> carrier_vec n"
shows "lattice_of fs = lattice_of (fs @ gs)"
  using assms
proof (induct gs arbitrary: fs)
  case Nil
  then show ?case by auto
next
  case (Cons a gs)
  note fs = Cons.prems(1)
  note inlattice = Cons.prems(2)
  note gs = Cons.prems(3)
  have gs_in_fs: "lattice_of gs \<subseteq> lattice_of fs"
    by (meson basic_trans_rules(23) gs lattice_is_monotone local.Cons(3) set_subset_Cons)
  have a: "a \<in> lattice_of (fs @ gs)"
    using basis_in_latticeI fs gs gs_in_fs local.Cons(1) local.Cons(3) by auto
  have "lattice_of (fs @ a # gs) = lattice_of ((a # gs) @ fs)"
    by (rule lattice_of_append, insert fs gs, auto) 
  also have "... = lattice_of (a # (gs @ fs))" by auto
  also have "... = lattice_of (a # (fs @ gs))"
    by (rule lattice_of_eq_set, insert gs fs, auto)
  also have "... = lattice_of (fs @ gs)"
    by (rule already_in_lattice[symmetric, OF _ a], insert fs gs, auto)
  also have "... = lattice_of fs" by (rule Cons.hyps[symmetric, OF fs gs_in_fs], insert gs, auto)     
  finally show ?case ..
qed

lemma zero_in_lattice:
  assumes fs_carrier: "set fs \<subseteq> carrier_vec n"
  shows "0\<^sub>v n \<in> lattice_of fs"
proof - 
  have "\<forall>f. lincomb (\<lambda>v. 0 * f v) (set fs) = 0\<^sub>v n"
      using fs_carrier lincomb_closed lincomb_smult lmult_0 by presburger
  hence "lincomb (\<lambda>i. 0) (set fs) = 0\<^sub>v n" by fastforce 
  thus ?thesis unfolding lattice_of_altdef_lincomb[OF fs_carrier] by auto
qed


lemma lattice_zero_rows_subset:
  assumes H: "H \<in> carrier_mat a n"
  shows "lattice_of (Matrix.rows (0\<^sub>m m n)) \<subseteq> lattice_of (Matrix.rows H)"
proof 
  let ?fs = "Matrix.rows (0\<^sub>m m n)"
  let ?gs = "Matrix.rows H"
  have fs_carrier: "set ?fs \<subseteq> carrier_vec n" unfolding Matrix.rows_def by auto
  have gs_carrier: "set ?gs \<subseteq> carrier_vec n" using H unfolding Matrix.rows_def by auto
  fix x assume x: "x \<in> lattice_of (Matrix.rows (0\<^sub>m m n))"
  obtain f where fx: "lincomb (of_int \<circ> f) (set (Matrix.rows (0\<^sub>m m n))) = x"
    using x lattice_of_altdef_lincomb[OF fs_carrier] by blast
  have "lincomb (of_int \<circ> f) (set (Matrix.rows (0\<^sub>m m n))) = 0\<^sub>v n"
    unfolding lincomb_def by (rule M.finsum_all0, unfold Matrix.rows_def, auto)
  hence "x = 0\<^sub>v n" using fx by auto
  thus "x \<in> lattice_of (Matrix.rows H)" using zero_in_lattice[OF gs_carrier] by auto 
qed

(*TODO: move outside this context (the previous lemmas too)*)
lemma lattice_of_append_zero_rows:
  assumes H': "H' \<in> carrier_mat m n"
  and H: "H = H' @\<^sub>r (0\<^sub>m m n)"
shows "lattice_of (Matrix.rows H) = lattice_of (Matrix.rows H')"
proof -
  have "Matrix.rows H = Matrix.rows H' @ Matrix.rows (0\<^sub>m m n)"
    by (unfold H, rule rows_append_rows[OF H'], auto)
  also have "lattice_of ... = lattice_of (Matrix.rows H')"
  proof (rule already_in_lattice_append[symmetric])
    show "lattice_of (Matrix.rows (0\<^sub>m m n)) \<subseteq> lattice_of (Matrix.rows H')"
      by (rule lattice_zero_rows_subset[OF H'])
  qed (insert H', auto simp add: Matrix.rows_def)
  finally show ?thesis .
qed
end

text \<open>Lemmas about echelon form\<close>

lemma echelon_form_JNF_1xn:
  assumes "A\<in>carrier_mat m n" and "m<2"  
shows "echelon_form_JNF A"
  using assms unfolding echelon_form_JNF_def is_zero_row_JNF_def by fastforce


lemma echelon_form_JNF_mx1:
  assumes "A\<in>carrier_mat m n" and "n<2"
  and "\<forall>i \<in> {1..<m}. A$$(i,0) = 0"
shows "echelon_form_JNF A"
  using assms unfolding echelon_form_JNF_def is_zero_row_JNF_def
    using atLeastLessThan_iff less_2_cases by fastforce


lemma echelon_form_mx0:
  assumes "A \<in> carrier_mat m 0"
  shows "echelon_form_JNF A" using assms unfolding echelon_form_JNF_def is_zero_row_JNF_def by auto

lemma echelon_form_JNF_first_column_0:
  assumes eA: "echelon_form_JNF A" and A: "A \<in> carrier_mat m n"
    and i0: "0<i" and im: "i<m" and n0: "0<n"
  shows "A $$ (i,0) =0"
proof (rule ccontr)
  assume Ai0: "A $$ (i, 0) \<noteq> 0"
  hence nz_iA:  "\<not> is_zero_row_JNF i A" using n0 A unfolding is_zero_row_JNF_def by auto
  hence nz_0A: "\<not> is_zero_row_JNF 0 A" using eA A unfolding echelon_form_JNF_def using i0 im by auto
  have "(LEAST n. A $$ (0, n) \<noteq> 0) < (LEAST n. A $$ (i, n) \<noteq> 0)"
    using nz_iA nz_0A eA A unfolding echelon_form_JNF_def using i0 im by blast
  moreover have "(LEAST n. A $$ (i, n) \<noteq> 0) = 0" using Ai0 by simp
  ultimately show False by auto
qed


lemma is_zero_row_JNF_multrow[simp]: 
  fixes A::"'a::comm_ring_1 mat"
  assumes "i<dim_row A"
  shows "is_zero_row_JNF i (multrow j (- 1) A) = is_zero_row_JNF i A"
  using assms unfolding is_zero_row_JNF_def by auto

lemma echelon_form_JNF_multrow:
  assumes "A : carrier_mat m n" and "i<m" and eA: "echelon_form_JNF A"
  shows "echelon_form_JNF (multrow i (- 1) A)"
proof (rule echelon_form_JNF_intro)
  have "A $$ (j, ja) = 0" if  "\<forall>j'<dim_col A. A $$ (ia, j') = 0" 
    and iaj: "ia < j" and j: "j < dim_row A" and ja: "ja < dim_col A" for ia j ja
    using assms that unfolding echelon_form_JNF_def is_zero_row_JNF_def 
    by (meson order.strict_trans) 
  thus " \<forall>ia<dim_row (multrow i (- 1) A). is_zero_row_JNF ia (multrow i (- 1) A) 
      \<longrightarrow> \<not> (\<exists>j<dim_row (multrow i (- 1) A). ia < j \<and> \<not> is_zero_row_JNF j (multrow i (- 1) A))"
    unfolding is_zero_row_JNF_def by simp 
  have Least_eq: "(LEAST n. multrow i (- 1) A $$ (ia, n) \<noteq> 0) = (LEAST n. A $$ (ia, n) \<noteq> 0)"
    if ia: "ia < dim_row A" and nz_ia_mrA: "\<not> is_zero_row_JNF ia (multrow i (- 1) A)" for ia
  proof (rule Least_equality)
    have nz_ia_A: "\<not> is_zero_row_JNF ia A" using nz_ia_mrA ia by auto
    have Least_Aian_n: "(LEAST n. A $$ (ia, n) \<noteq> 0) < dim_col A"
      by (smt dual_order.strict_trans is_zero_row_JNF_def not_less_Least not_less_iff_gr_or_eq nz_ia_A)
    show "multrow i (- 1) A $$ (ia, LEAST n. A $$ (ia, n) \<noteq> 0) \<noteq> 0"
      by (smt LeastI Least_Aian_n class_cring.cring_simprules(22) equation_minus_iff ia
          index_mat_multrow(1) is_zero_row_JNF_def mult_minus1 nz_ia_A)
    show " \<And>y. multrow i (- 1) A $$ (ia, y) \<noteq> 0 \<Longrightarrow> (LEAST n. A $$ (ia, n) \<noteq> 0) \<le> y"
      by (metis (mono_tags, lifting) Least_Aian_n class_cring.cring_simprules(22) ia 
          index_mat_multrow(1) leI mult_minus1 order.strict_trans wellorder_Least_lemma(2))
  qed
  have "(LEAST n. multrow i (- 1) A $$ (ia, n) \<noteq> 0) < (LEAST n. multrow i (- 1) A $$ (j, n) \<noteq> 0)"
    if ia_j: "ia < j" and
      j: "j < dim_row A"
      and nz_ia_A: "\<not> is_zero_row_JNF ia A"
      and nz_j_A: "\<not> is_zero_row_JNF j A"
    for ia j
  proof -
    have ia: "ia < dim_row A" using ia_j j by auto
    show ?thesis using Least_eq[OF ia] Least_eq[OF j] nz_ia_A nz_j_A 
        is_zero_row_JNF_multrow[OF ia] is_zero_row_JNF_multrow[OF j] eA ia_j j
      unfolding echelon_form_JNF_def by simp
  qed 
  thus "\<forall>ia j.
       ia < j \<and> j < dim_row (multrow i (- 1) A) \<and> \<not> is_zero_row_JNF ia (multrow i (- 1) A)
        \<and> \<not> is_zero_row_JNF j (multrow i (- 1) A) \<longrightarrow>
       (LEAST n. multrow i (- 1) A $$ (ia, n) \<noteq> 0) < (LEAST n. multrow i (- 1) A $$ (j, n) \<noteq> 0)"
    by auto 
qed


(*The following lemma is already in HOL Analysis (thm echelon_form_imp_upper_triagular),
but only for square matrices. We prove it here for rectangular matrices.*)
thm echelon_form_imp_upper_triagular

(*First we prove an auxiliary statement*)
lemma echelon_form_JNF_least_position_ge_diagonal:
  assumes eA: "echelon_form_JNF A" 
  and A: "A: carrier_mat m n"
  and nz_iA: "\<not> is_zero_row_JNF i A"
  and im: "i<m"
shows "i\<le>(LEAST n. A $$ (i,n) \<noteq> 0)"
  using nz_iA im
proof (induct i rule: less_induct)
  case (less i)
  note nz_iA = less.prems(1) 
  note im = less.prems(2)
  show ?case
  proof (cases "i=0")
    case True show ?thesis using True by blast
  next
    case False
    show ?thesis
    proof (rule ccontr)
      assume " \<not> i \<le> (LEAST n. A $$ (i, n) \<noteq> 0)"
      hence i_least: "i > (LEAST n. A $$ (i, n) \<noteq> 0)" by auto
      have nz_i1A: "\<not> is_zero_row_JNF (i-1) A" 
        using nz_iA im False A eA unfolding echelon_form_JNF_def
        by (metis Num.numeral_nat(7) Suc_pred carrier_matD(1) gr_implies_not0 
            lessI linorder_neqE_nat order.strict_trans)  
      have "i-1\<le>(LEAST n. A $$ (i-1,n) \<noteq> 0)" by (rule less.hyps, insert im nz_i1A False, auto)
      moreover have "(LEAST n. A $$ (i,n) \<noteq> 0) > (LEAST n. A $$ (i-1,n) \<noteq> 0)"
        using nz_i1A nz_iA im False A eA unfolding echelon_form_JNF_def by auto   
      ultimately show False using i_least by auto
    qed
  qed
qed


lemma echelon_form_JNF_imp_upper_triangular:
  assumes eA: "echelon_form_JNF A" 
  shows "upper_triangular A"
proof
  fix i j assume ji: "j<i" and i: "i<dim_row A"
  have A: "A \<in> carrier_mat (dim_row A) (dim_col A)" by auto
  show "A $$ (i,j) = 0"
  proof (cases "is_zero_row_JNF i A")
    case False
    have "i\<le> (LEAST n. A $$(i,n) \<noteq> 0)"
      by (rule echelon_form_JNF_least_position_ge_diagonal[OF eA A False i])
    then show ?thesis 
      using ji not_less_Least order.strict_trans2 by blast
  next
    case True
      (*
    Problem detected: at this point, we don't know if j < dim_col A. 
    That is, upper_triangular definition only works for matrices \<in> carrier_mat m n with n\<ge>m.
    The definition is: 
       - upper_triangular A \<equiv> \<forall>i < dim_row A. \<forall> j < i. A $$ (i,j) = 0
     But we need here:
       - upper_triangular A \<equiv> \<forall>i < dim_row A. \<forall> j < dim_col A. j < i  \<longrightarrow> A $$ (i,j) = 0
  
    Anyway, the existing definition makes sense since upper triangular is usually 
    restricted to square matrices.
  *)
    then show ?thesis unfolding is_zero_row_JNF_def oops


(*We do the same with the new definition upper_triangular'*)
lemma echelon_form_JNF_imp_upper_triangular:
  assumes eA: "echelon_form_JNF A" 
  shows "upper_triangular' A"
proof
  fix i j assume ji: "j<i" and i: "i<dim_row A" and j: "j<dim_col A"
  have A: "A \<in> carrier_mat (dim_row A) (dim_col A)" by auto
  show "A $$ (i,j) = 0"
  proof (cases "is_zero_row_JNF i A")
    case False
    have "i\<le> (LEAST n. A $$(i,n) \<noteq> 0)"
      by (rule echelon_form_JNF_least_position_ge_diagonal[OF eA A False i])
    then show ?thesis 
      using ji not_less_Least order.strict_trans2 by blast
  next
    case True     
    then show ?thesis unfolding is_zero_row_JNF_def using j by auto
  qed
qed


lemma upper_triangular_append_zero:
  assumes uH: "upper_triangular' H" 
  and H: "H \<in> carrier_mat (m+m) n" and mn: "n\<le>m"
  shows "H = mat_of_rows n (map (Matrix.row H) [0..<m]) @\<^sub>r 0\<^sub>m m n" (is "_ = ?H' @\<^sub>r 0\<^sub>m m n")
proof 
  have H': "?H' \<in> carrier_mat m n" using H uH by auto
  have H'0: "(?H' @\<^sub>r 0\<^sub>m m n) \<in> carrier_mat (m+m) n" by (simp add: H')
  thus dr: "dim_row H = dim_row (?H' @\<^sub>r 0\<^sub>m m n)" using H H'  by (simp add: append_rows_def) 
  show dc: "dim_col H = dim_col (?H' @\<^sub>r 0\<^sub>m m n)" using H H'  by (simp add: append_rows_def) 
  fix i j assume i: "i < dim_row (?H' @\<^sub>r 0\<^sub>m m n)" and j: "j < dim_col (?H' @\<^sub>r 0\<^sub>m m n)"
  show "H $$ (i, j) = (?H' @\<^sub>r 0\<^sub>m m n) $$ (i, j)"
  proof (cases "i<m")
    case True
    have "H $$ (i, j) = ?H' $$ (i,j)"
      by (metis True H' append_rows_def H carrier_matD index_mat_four_block(3) index_zero_mat(3) j 
          le_add1 map_first_rows_index mat_of_rows_carrier(2) mat_of_rows_index nat_arith.rule0)
    then show ?thesis
      by (metis (mono_tags, lifting) H' True add.comm_neutral append_rows_def 
          carrier_matD(1) i index_mat_four_block index_zero_mat(3) j)
  next
    case False 
    have imn: "i<m+m" using i dr H by auto
    have jn: "j<n" using j dc H by auto
    have ji: "j<i" using j i False mn jn by linarith
    hence "H $$ (i, j) = 0" using uH unfolding upper_triangular'_def dr imn using i jn 
      by (simp add: dc j)
    also have "... = (?H' @\<^sub>r 0\<^sub>m m n) $$ (i, j)"
      by (smt False H' append_rows_def assms(2) carrier_matD(1) carrier_matD(2) dc imn
          index_mat_four_block(1,3) index_zero_mat j less_diff_conv2 linorder_not_less)
    finally show ?thesis .
  qed
qed

subsubsection \<open>The algorithm is sound\<close>

lemma find_fst_non0_in_row: 
  assumes A: "A \<in> carrier_mat m n"
  and res: "find_fst_non0_in_row l A = Some j"
  shows "A $$ (l,j) \<noteq> 0" "l \<le> j" "j < dim_col A"
proof -
  let ?xs = "filter (\<lambda>j. A $$ (l, j) \<noteq> 0) [l ..< dim_col A]"
  from res[unfolded find_fst_non0_in_row_def Let_def]
  have xs: "?xs \<noteq> []" by (cases ?xs, auto)
  have j_in_xs: "j \<in> set ?xs" using res unfolding find_fst_non0_in_row_def Let_def
    by (metis (no_types, lifting) length_greater_0_conv list.case(2) list.exhaust nth_mem option.simps(1) xs)
  show "A $$ (l,j) \<noteq> 0" "l \<le> j" "j < dim_col A" using j_in_xs by auto+  
qed


lemma find_fst_non0_in_row_zero_before: 
  assumes A: "A \<in> carrier_mat m n"
  and res: "find_fst_non0_in_row l A = Some j"
  shows "\<forall>j'\<in>{l..<j}. A $$ (l,j') = 0"
proof -
  let ?xs = "filter (\<lambda>j. A $$ (l, j) \<noteq> 0) [l ..< dim_col A]"
  from res[unfolded find_fst_non0_in_row_def Let_def]
  have xs: "?xs \<noteq> []" by (cases ?xs, auto)
  have j_in_xs: "j \<in> set ?xs" using res unfolding find_fst_non0_in_row_def Let_def
    by (metis (no_types, lifting) length_greater_0_conv list.case(2) list.exhaust nth_mem option.simps(1) xs)
  have j_xs0: "j = ?xs ! 0"
    by (smt res[unfolded find_fst_non0_in_row_def Let_def] list.case(2) list.exhaust option.inject xs)
  show "\<forall>j'\<in>{l..<j}. A $$ (l,j') = 0"
  proof (rule+, rule ccontr)
    fix j' assume j': "j' : {l..<j}" and Alj': "A $$ (l, j') \<noteq> 0"
    have j'j: "j'<j" using j' by auto
    have j'_in_xs: "j' \<in> set ?xs"
      by (metis (mono_tags, lifting) A Set.member_filter j' Alj' res atLeastLessThan_iff filter_set
          find_fst_non0_in_row(3) nat_SN.gt_trans set_upt)  
    have l_rw: "[l..<dim_col A] = [l ..<j] @[j..<dim_col A]"
      using assms(1) assms(2) find_fst_non0_in_row(3) j' upt_append by auto
    have xs_rw: "?xs = filter (\<lambda>j. A $$ (l, j) \<noteq> 0) ([l ..<j] @[j..<dim_col A])"
      using l_rw by auto
    hence "filter (\<lambda>j. A $$ (l, j) \<noteq> 0) [l ..<j] = []" using j_xs0 
      by (metis (no_types, lifting) Set.member_filter atLeastLessThan_iff filter_append filter_set
          length_greater_0_conv nth_append nth_mem order_less_irrefl set_upt)
    thus False using j_xs0 j' j_xs0 
      by (metis Set.member_filter filter_empty_conv filter_set j'_in_xs set_upt)
  qed
qed


corollary find_fst_non0_in_row_zero_before': 
  assumes A: "A \<in> carrier_mat m n"
  and res: "find_fst_non0_in_row l A = Some j"
  and "j' \<in> {l..<j}"
  shows "A $$ (l,j') = 0" using find_fst_non0_in_row_zero_before assms by auto

lemma find_fst_non0_in_row_LEAST: 
  assumes A: "A \<in> carrier_mat m n"
  and ut_A: "upper_triangular' A"
  and res: "find_fst_non0_in_row l A = Some j"
  and lm: "l<m"
shows "j = (LEAST n. A $$ (l,n) \<noteq> 0)"
proof (rule Least_equality[symmetric])
  show " A $$ (l, j) \<noteq> 0" using res find_fst_non0_in_row(1) by blast
  show "\<And>y. A $$ (l, y) \<noteq> 0 \<Longrightarrow> j \<le> y"
  proof (rule ccontr)
    fix y assume Aly: "A $$ (l, y) \<noteq> 0" and jy: " \<not> j \<le> y "
    have yn: "y < n"
      by (metis A jy carrier_matD(2) find_fst_non0_in_row(3) leI less_imp_le_nat nat_SN.compat res)
    have "A $$(l,y) = 0"
    proof (cases "y\<in>{l..<j}")
      case True
      show ?thesis by (rule find_fst_non0_in_row_zero_before'[OF A res True])
    next
      case False hence "y<l" using jy by auto
      thus ?thesis using ut_A A lm unfolding upper_triangular'_def using yn by blast
    qed
    thus False using Aly by contradiction
  qed 
qed



lemma find_fst_non0_in_row_None': 
  assumes A: "A \<in> carrier_mat m n"  
  and lm: "l<m"
shows "(find_fst_non0_in_row l A = None) = (\<forall>j\<in>{l..<dim_col A}. A $$ (l,j) = 0)" (is "?lhs = ?rhs")
proof
  assume res: ?lhs
  let ?xs = "filter (\<lambda>j. A $$ (l, j) \<noteq> 0) [l ..< dim_col A]"
  from res[unfolded find_fst_non0_in_row_def Let_def]
  have xs: "?xs = []" by (cases ?xs, auto)
  have "A $$ (l, j) = 0" if j: "j\<in>{l..<dim_col A}" for j
    using xs by (metis (mono_tags, lifting) empty_filter_conv j set_upt)
  thus "?rhs" by blast
next
  assume rhs: ?rhs
  show ?lhs
  proof (rule ccontr)
    assume "find_fst_non0_in_row l A \<noteq> None" 
    from this obtain j where r: "find_fst_non0_in_row l A = Some j" by blast
    hence "A $$ (l,j) \<noteq> 0" and  "l\<le>j" and "j<dim_col A" using find_fst_non0_in_row[OF A r] by blast+
    thus False using rhs by auto  
  qed
qed


lemma find_fst_non0_in_row_None: 
  assumes A: "A \<in> carrier_mat m n"
  and ut_A: "upper_triangular' A"
  and lm: "l<m"
shows "(find_fst_non0_in_row l A = None) = (is_zero_row_JNF l A)" (is "?lhs = ?rhs")
proof
  assume res: ?lhs
  let ?xs = "filter (\<lambda>j. A $$ (l, j) \<noteq> 0) [l ..< dim_col A]"
  from res[unfolded find_fst_non0_in_row_def Let_def]
  have xs: "?xs = []" by (cases ?xs, auto)
  have "A $$ (l, j) = 0" if j: "j < dim_col A" for j
  proof (cases "j<l")
    case True
    then show ?thesis using ut_A A lm j unfolding upper_triangular'_def by blast
  next
    case False
    hence j_ln: "j \<in> {l..<dim_col A}" using A lm j by simp
    then show ?thesis using xs by (metis (mono_tags, lifting) empty_filter_conv set_upt)
  qed
  thus "?rhs" unfolding is_zero_row_JNF_def by blast
next
  assume rhs: ?rhs
  show ?lhs
  proof (rule ccontr)
    assume "find_fst_non0_in_row l A \<noteq> None" 
    from this obtain j where r: "find_fst_non0_in_row l A = Some j" by blast
    hence "A $$ (l,j) \<noteq> 0" and "j<dim_col A" using find_fst_non0_in_row[OF A r] by blast+
    hence "\<not> is_zero_row_JNF l A" unfolding is_zero_row_JNF_def using lm A by auto
    thus False using rhs by contradiction    
  qed
qed

lemma make_first_column_positive_preserves_dimensions:
  shows [simp]: "dim_row (make_first_column_positive A) = dim_row A" 
    and [simp]: "dim_col (make_first_column_positive A) = dim_col A"
  by (auto)


lemma make_first_column_positive_works: 
  assumes "A\<in>carrier_mat m n" and i: "i<m" and "0<n"
  shows "make_first_column_positive A $$ (i,0) \<ge> 0"
  and "j<n \<Longrightarrow> A $$ (i,0) < 0 \<Longrightarrow> (make_first_column_positive A) $$ (i,j) = - A $$ (i,j)"
  and "j<n \<Longrightarrow> A $$ (i,0) \<ge> 0 \<Longrightarrow> (make_first_column_positive A) $$ (i,j) = A $$ (i,j)"
  using assms by auto 


lemma make_first_column_positive_invertible: 
  shows  "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (dim_row A) (dim_row A) 
  \<and> make_first_column_positive A = P * A" 
proof -
  let ?P = "Matrix.mat (dim_row A) (dim_row A)
          (\<lambda>(i,j). if i = j then if A $$(i,0) < 0 then - 1 else 1 else 0::int)"
  have "invertible_mat ?P"
  proof -
    have "(map abs (diag_mat ?P)) = replicate (length ((map abs (diag_mat ?P)))) 1" 
      by (rule replicate_length_same[symmetric], auto simp add: diag_mat_def)
    hence m_rw: "(map abs (diag_mat ?P)) = replicate (dim_row A) 1" by (auto simp add: diag_mat_def)
    have "Determinant.det ?P = prod_list (diag_mat ?P)" by (rule det_upper_triangular, auto)
    also have "abs ... = prod_list (map abs (diag_mat ?P))" unfolding prod_list_abs by blast
    also have " ... = prod_list (replicate (dim_row A) 1)" using m_rw by simp
    also have "... = 1" by auto
    finally have "\<bar>Determinant.det ?P\<bar> = 1" by blast
    hence "Determinant.det ?P dvd 1" by fastforce
    thus ?thesis using invertible_iff_is_unit_JNF mat_carrier by blast (*Thanks to the new bridge*)
  qed    
  moreover have "make_first_column_positive A = ?P * A" (is "?M = _")
  proof (rule eq_matI)
    show "dim_row ?M = dim_row (?P * A)" and "dim_col ?M = dim_col (?P * A)" by auto
    fix i j assume i: "i < dim_row (?P * A)" and j: "j < dim_col (?P * A)"
    have set_rw: "{0..<dim_row A} = insert i ({0..<dim_row A} - {i})" using i by auto
      have rw0: "(\<Sum>ia \<in> {0..<dim_row A } - {i}. Matrix.row ?P i $v ia * col A j $v ia) = 0"
        by (rule sum.neutral, insert i, auto)        
    have "(?P * A) $$ (i, j) = Matrix.row ?P i \<bullet> col A j" using i j by auto
    also have "... = (\<Sum>ia = 0..<dim_row A. Matrix.row ?P i $v ia * col A j $v ia)"
        unfolding scalar_prod_def by auto
      also have "... =  (\<Sum>ia \<in> insert i ({0..<dim_row A} - {i}). Matrix.row ?P i $v ia * col A j $v ia)"
        using set_rw by argo
      also have "... = Matrix.row ?P i $v i * col A j $v i 
        + (\<Sum>ia \<in> {0..<dim_row A } - {i}. Matrix.row ?P i $v ia * col A j $v ia)" 
        by (rule sum.insert, auto)
      also have "... = Matrix.row ?P i $v i * col A j $v i" unfolding rw0 by simp
      finally have *: "(?P * A) $$ (i, j) = Matrix.row ?P i $v i * col A j $v i" .
    also have "... = ?M $$ (i,j)" 
      by (cases " A $$ (i, 0) < 0", insert i j, auto simp add: col_def)
    finally show "?M $$ (i, j) = (?P * A) $$ (i, j)" ..
  qed
  moreover have "?P \<in> carrier_mat (dim_row A) (dim_row A)" by auto
  ultimately show ?thesis by blast
qed

locale proper_mod_operation = mod_operation +
  assumes dvd_gdiv_mult_right[simp]: "b > 0 \<Longrightarrow> b dvd a \<Longrightarrow> (a gdiv b) * b = a"
    and gmod_gdiv: "y > 0 \<Longrightarrow> x gmod y = x - x gdiv y * y"
    and dvd_imp_gmod_0: "0 < a \<Longrightarrow> a dvd b \<Longrightarrow> b gmod a = 0" 
    and gmod_0_imp_dvd: "a gmod b = 0 \<Longrightarrow> b dvd a" 
    and gmod_0[simp]: "n gmod 0 = n" "n > 0 \<Longrightarrow> 0 gmod n = 0"
begin
lemma reduce_alt_def_not0: 
  assumes "A $$ (a,0) \<noteq> 0" and pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A $$ (b,0))"
  shows "reduce a b D A =
       Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then let r = (p*A$$(a,k) + q*A$$(b,k)) in
                              if k = 0 then if D dvd r then D else r else r gmod D
                   else if i = b then let r = u * A$$(a,k) + v * A$$(b,k) in
                              if k = 0 then r else r gmod D
                   else A$$(i,k))" (is "_ = ?rhs")
  and 
   "reduce_abs a b D A =
       Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then let r = (p*A$$(a,k) + q*A$$(b,k)) in
                              if abs r > D then if k = 0 \<and> D dvd r then D else r gmod D else r 
                   else if i = b then let r = u * A$$(a,k) + v * A$$(b,k) in
                              if abs r > D then r gmod D else r
                   else A$$(i,k))" (is "_ = ?rhs_abs")
proof -
  have "reduce a b D A =
       (case euclid_ext2 (A$$(a,0)) (A $$ (b,0)) of (p,q,u,v,d) \<Rightarrow>
       Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then let r = (p*A$$(a,k) + q*A$$(b,k)) in
                               if k = 0 then if D dvd r then D else r else r gmod D
                   else if i = b then let r = u * A$$(a,k) + v * A$$(b,k) in
                                if k = 0 then r else r gmod D
                   else A$$(i,k)
            ))" using assms by auto
  also have "... = ?rhs" unfolding reduce.simps Let_def 
    by (rule eq_matI, insert pquvd) (metis (no_types, lifting) split_conv)+
  finally show "reduce a b D A = ?rhs" .
  have "reduce_abs a b D A =
       (case euclid_ext2 (A$$(a,0)) (A $$ (b,0)) of (p,q,u,v,d) \<Rightarrow>
       Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then let r = (p*A$$(a,k) + q*A$$(b,k)) in
                               if abs r > D then if k = 0 \<and> D dvd r then D else r gmod D else r 
                   else if i = b then let r = u * A$$(a,k) + v * A$$(b,k) in
                               if abs r > D then r gmod D else r
                   else A$$(i,k)
            ))" using assms by auto
  also have "... = ?rhs_abs" unfolding reduce.simps Let_def 
    by (rule eq_matI, insert pquvd) (metis (no_types, lifting) split_conv)+
  finally show "reduce_abs a b D A = ?rhs_abs" .
qed

lemma reduce_preserves_dimensions:
  shows [simp]: "dim_row (reduce a b D A) = dim_row A" 
    and [simp]: "dim_col (reduce a b D A) = dim_col A"
  and [simp]: "dim_row (reduce_abs a b D A) = dim_row A" 
    and [simp]: "dim_col (reduce_abs a b D A) = dim_col A"
  by (auto simp add: Let_def split_beta)

lemma reduce_carrier:
  assumes "A \<in> carrier_mat m n"
  shows "(reduce a b D A) \<in> carrier_mat m n" 
    and "(reduce_abs a b D A) \<in> carrier_mat m n" 
  by (insert assms, auto simp add: Let_def split_beta)

lemma reduce_gcd: 
  assumes A: "A \<in> carrier_mat m n" and a: "a<m" and j: "0<n" 
  and Aaj: "A $$ (a,0) \<noteq> 0"
shows "(reduce a b D A) $$ (a,0) = (let r = gcd (A$$(a,0)) (A$$(b,0)) in if D dvd r then D else r)" (is "?lhs = ?rhs")
  and "(reduce_abs a b D A) $$ (a,0) = (let r = gcd (A$$(a,0)) (A$$(b,0)) in if D < r then
                      if D dvd r then D else r gmod D else r)" (is "?lhs_abs = ?rhs_abs")
proof -
  obtain p q u v d where pquvd: "euclid_ext2 (A$$(a,0)) (A$$(b,0)) = (p,q,u,v,d)"
    using prod_cases5 by blast
  have "p * A $$ (a, 0) + q * A $$ (b, 0) = d" 
    using Aaj pquvd is_bezout_ext_euclid_ext2 unfolding is_bezout_ext_def 
    by (smt Pair_inject bezout_coefficients_fst_snd euclid_ext2_def)
  also have " ... = gcd (A$$(a,0)) (A$$(b,0))" by (metis euclid_ext2_def pquvd prod.sel(2))
  finally have pAaj_qAbj_gcd: "p * A $$ (a, 0) + q * A $$ (b, 0) = gcd (A$$(a,0)) (A$$(b,0))" .
  let ?f = "(\<lambda>(i, k). if i = a then let r = p * A $$ (a, k) + q * A $$ (b, k) in if k = 0 then if D dvd r then D else r else r gmod D
              else if i = b then let r = u * A $$ (a, k) + v * A $$ (b, k) in if k = 0 then r else r gmod D else A $$ (i, k))"
  have "(reduce a b D A) $$ (a,0) = Matrix.mat (dim_row A) (dim_col A) ?f $$ (a, 0)"
    using Aaj pquvd by auto 
  also have "... = (let r = p * A $$ (a, 0) + q * A $$ (b, 0) in if (0::nat) = 0 then if D dvd r then D else r else r gmod D)"
    using A a j by auto
  also have "... = (if D dvd gcd (A$$(a,0)) (A$$(b,0)) then D else 
      gcd (A$$(a,0)) (A$$(b,0)))" 
    by (simp add: pAaj_qAbj_gcd)
  finally show "?lhs = ?rhs" by auto
  let ?g = "(\<lambda>(i, k). if i = a then let r = p * A $$ (a, k) + q * A $$ (b, k) in 
                if D < \<bar>r\<bar> then if k = 0 \<and> D dvd r then D else r gmod D else r
              else if i = b then let r = u * A $$ (a, k) + v * A $$ (b, k) in 
                    if D < \<bar>r\<bar> then r gmod D else r else A $$ (i, k))"
  have "(reduce_abs a b D A) $$ (a,0) = Matrix.mat (dim_row A) (dim_col A) ?g $$ (a, 0)"
    using Aaj pquvd by auto 
  also have "... = (let r = p * A $$ (a, 0) + q * A $$ (b, 0) in if D < \<bar>r\<bar> then
            if (0::nat) = 0 \<and> D dvd r then D else r gmod D else r)"
    using A a j by auto
  also have "... = (if D < \<bar>gcd (A$$(a,0)) (A$$(b,0))\<bar> then if D dvd gcd (A$$(a,0)) (A$$(b,0)) then D else 
      gcd (A$$(a,0)) (A$$(b,0)) gmod D else gcd (A$$(a,0)) (A$$(b,0)))"
    by (simp add: pAaj_qAbj_gcd)
  finally show "?lhs_abs = ?rhs_abs" by auto
qed




lemma reduce_preserves: 
  assumes A: "A \<in> carrier_mat m n" and j: "j<n" 
  and Aaj: "A $$ (a,0) \<noteq> 0" and ib: "i\<noteq>b" and ia: "i\<noteq>a" and im: "i<m"
shows "(reduce a b D A) $$ (i,j) = A $$ (i,j)"  (is "?thesis1")
and "(reduce_abs a b D A) $$ (i,j) = A $$ (i,j)" (is "?thesis2") 
proof -
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(b,0))"
    using prod_cases5 by metis
  show ?thesis1 unfolding reduce_alt_def_not0[OF Aaj pquvd] using ia im j A ib by auto
  show ?thesis2 unfolding reduce_alt_def_not0[OF Aaj pquvd] using ia im j A ib by auto
qed


lemma reduce_0: 
  assumes A: "A \<in> carrier_mat m n" and a: "a<m" and j: "0<n" and b: "b<m" and ab: "a \<noteq> b"
  and Aaj: "A $$ (a,0) \<noteq> 0"
  and D: "D \<ge> 0" 
shows "(reduce a b D A) $$ (b,0) = 0" (is "?thesis1")
and "(reduce_abs a b D A) $$ (b,0) = 0" (is "?thesis2")
proof -
  obtain p q u v d where pquvd: "euclid_ext2 (A$$(a,0)) (A$$(b,0)) = (p,q,u,v,d)"
    using prod_cases5 by blast
  hence u: "u = - (A$$(b,0)) div gcd (A$$(a,0)) (A$$(b,0))"
    using euclid_ext2_works[OF pquvd] by auto
  have v: "v = A$$(a,0) div gcd (A$$(a,0)) (A$$(b,0))" using euclid_ext2_works[OF pquvd] by auto
  have uv0: "u * A$$(a,0) + v * A$$(b,0) = 0" using u v
  proof -
    have "\<forall>i ia. gcd (ia::int) i * (ia div gcd ia i) = ia"
    by (meson dvd_mult_div_cancel gcd_dvd1)
    then have "v * - A $$ (b, 0) = u * A $$ (a, 0)"
      by (metis (no_types) dvd_minus_iff dvd_mult_div_cancel gcd_dvd2 minus_minus mult.assoc mult.commute u v)
    then show ?thesis
      by simp
  qed
  let ?f = "(\<lambda>(i, k). if i = a then let r = p * A $$ (a, k) + q * A $$ (b, k) in 
            if k = 0 then if D dvd r then D else r else r gmod D
              else if i = b then let r = u * A $$ (a, k) + v * A $$ (b, k) in 
                   if k = 0 then r else r gmod D else A $$ (i, k))" 
  have "(reduce a b D A) $$ (b,0) = Matrix.mat (dim_row A) (dim_col A) ?f $$ (b, 0)"
    using Aaj pquvd by auto 
  also have "... = (let r = u * A$$(a,0) + v * A$$(b,0) in r)"
    using A a j ab b by auto
  also have "... = 0" using uv0 D 
    by (smt (z3) gmod_0(1) gmod_0(2)) 
  finally show ?thesis1 .
  let ?g = "(\<lambda>(i, k). if i = a then let r = p * A $$ (a, k) + q * A $$ (b, k) in 
          if D < \<bar>r\<bar> then if k = 0 \<and> D dvd r then D else r gmod D else r
              else if i = b then let r = u * A $$ (a, k) + v * A $$ (b, k) in 
                  if D < \<bar>r\<bar> then r gmod D else r else A $$ (i, k))" 
  have "(reduce_abs a b D A) $$ (b,0) = Matrix.mat (dim_row A) (dim_col A) ?g $$ (b, 0)"
    using Aaj pquvd by auto 
  also have "... = (let r = u * A$$(a,0) + v * A$$(b,0) in if D < \<bar>r\<bar> then r gmod D else r)"
    using A a j ab b by auto
  also have "... = 0" using uv0 D by simp
  finally show ?thesis2 .
qed
end


text \<open>Let us show the key lemma: operations modulo determinant don't modify the (integer) row span.\<close>

context LLL_with_assms
begin

lemma lattice_of_kId_subset_fs_init: 
  assumes k_det: "k = Determinant.det (mat_of_rows n fs_init)"
  and mn: "m=n"
  shows "lattice_of (Matrix.rows (k \<cdot>\<^sub>m (1\<^sub>m m))) \<subseteq> lattice_of fs_init"
proof -
  let ?Z = "(mat_of_rows n fs_init)"
  let ?RAT = "of_int_hom.mat_hom :: int mat \<Rightarrow> rat mat"
  have RAT_fs_init: "?RAT (mat_of_rows n fs_init) \<in> carrier_mat n n"
      using len map_carrier_mat mat_of_rows_carrier(1) mn by blast
  have det_RAT_fs_init: "Determinant.det (?RAT ?Z) \<noteq> 0"
  proof (rule gs.lin_indpt_rows_imp_det_not_0[OF RAT_fs_init])   
    have rw: "Matrix.rows (?RAT (mat_of_rows n fs_init)) = RAT fs_init"
      by (metis cof_vec_space.lin_indpt_list_def fs_init lin_dep mat_of_rows_map rows_mat_of_rows)
    thus "gs.lin_indpt (set (Matrix.rows (?RAT (mat_of_rows n fs_init))))" 
      by (insert lin_dep, simp add: cof_vec_space.lin_indpt_list_def)
    show "distinct (Matrix.rows (?RAT (mat_of_rows n fs_init)))"
      using rw cof_vec_space.lin_indpt_list_def lin_dep by auto
  qed
  obtain inv_Z where inverts_Z: "inverts_mat (?RAT ?Z) inv_Z" and inv_Z: "inv_Z \<in> carrier_mat m m"
    by (metis mn det_RAT_fs_init dvd_field_iff invertible_iff_is_unit_JNF
        len map_carrier_mat mat_of_rows_carrier(1) obtain_inverse_matrix)
  have det_rat_Z_k: "Determinant.det (?RAT ?Z) = rat_of_int k"
    using k_det of_int_hom.hom_det by blast
  have "?RAT ?Z *  adj_mat (?RAT ?Z) = Determinant.det (?RAT ?Z) \<cdot>\<^sub>m 1\<^sub>m n" 
    by (rule adj_mat[OF RAT_fs_init])
  hence "inv_Z * (?RAT ?Z *  adj_mat (?RAT ?Z)) = inv_Z * (Determinant.det (?RAT ?Z) \<cdot>\<^sub>m 1\<^sub>m n)" by simp
  hence k_inv_Z_eq_adj: "(rat_of_int k) \<cdot>\<^sub>m inv_Z = adj_mat (?RAT ?Z)"
    by (smt Determinant.mat_mult_left_right_inverse RAT_fs_init adj_mat(1,3) mn 
        carrier_matD det_RAT_fs_init det_rat_Z_k gs.det_nonzero_congruence inv_Z inverts_Z 
        inverts_mat_def mult_smult_assoc_mat smult_carrier_mat)
  have adj_mat_Z: "adj_mat (?RAT ?Z) $$ (i,j) \<in> \<int>" if i: "i<m" and j: "j<n" for i j
  proof -
    have det_mat_delete_Z: "Determinant.det (mat_delete (?RAT ?Z) j i) \<in> \<int>"
    proof (rule Ints_det)
      fix ia ja
      assume ia: "ia < dim_row  (mat_delete (?RAT ?Z) j i)"
        and ja: "ja < dim_col  (mat_delete (?RAT ?Z) j i)"
      have "(mat_delete (?RAT ?Z) j i) $$ (ia, ja) =  (?RAT ?Z) $$ (insert_index j ia, insert_index i ja)"        
        by (rule mat_delete_index[symmetric], insert i j mn len ia ja RAT_fs_init, auto)
      also have "... = rat_of_int (?Z $$ (insert_index j ia, insert_index i ja))"
        by (rule index_map_mat, insert i j ia ja, auto simp add: insert_index_def)
      also have "... \<in> \<int>" using Ints_of_int by blast
      finally show "(mat_delete (?RAT ?Z) j i) $$ (ia, ja) \<in> \<int>" .
    qed
    have "adj_mat (?RAT ?Z) $$ (i,j) = Determinant.cofactor (?RAT ?Z) j i"
      unfolding adj_mat_def
      by (simp add: len i j)
    also have "... =  (- 1) ^ (j + i) * Determinant.det (mat_delete (?RAT ?Z) j i)"
      unfolding Determinant.cofactor_def by auto
    also have "... \<in> \<int>" using det_mat_delete_Z by auto
    finally show ?thesis .
  qed                
  have kinvZ_in_Z: "((rat_of_int k) \<cdot>\<^sub>m inv_Z) $$ (i,j) \<in> \<int>" if i: "i<m" and j: "j<n" for i j
    using k_inv_Z_eq_adj by (simp add: adj_mat_Z i j)
  have "?RAT (k \<cdot>\<^sub>m (1\<^sub>m m)) = Determinant.det (?RAT ?Z) \<cdot>\<^sub>m (inv_Z * ?RAT ?Z)" (is "?lhs = ?rhs")
  proof - 
    have "(inv_Z * ?RAT ?Z) = (1\<^sub>m m)"
      by (metis Determinant.mat_mult_left_right_inverse RAT_fs_init mn carrier_matD(1)
          inv_Z inverts_Z inverts_mat_def)
    from this have "?rhs = rat_of_int k \<cdot>\<^sub>m (1\<^sub>m m)" using det_rat_Z_k by auto
    also have "... = ?lhs" by auto
    finally show ?thesis ..
  qed
  also have "... = (Determinant.det (?RAT ?Z) \<cdot>\<^sub>m inv_Z) * ?RAT ?Z"
    by (metis RAT_fs_init mn inv_Z mult_smult_assoc_mat)
  also have "... = ((rat_of_int k) \<cdot>\<^sub>m inv_Z) * ?RAT ?Z" by (simp add: k_det)
  finally have r': "?RAT (k \<cdot>\<^sub>m (1\<^sub>m m)) = ((rat_of_int k) \<cdot>\<^sub>m inv_Z) * ?RAT ?Z" .
  have r: "(k \<cdot>\<^sub>m (1\<^sub>m m)) = ((map_mat int_of_rat ((rat_of_int k) \<cdot>\<^sub>m inv_Z))) * ?Z"
  proof -
    have "?RAT ((map_mat int_of_rat ((rat_of_int k) \<cdot>\<^sub>m inv_Z))) = ((rat_of_int k) \<cdot>\<^sub>m inv_Z)"
    proof (rule eq_matI, auto)
      fix i j assume i: "i < dim_row inv_Z" and j: "j < dim_col inv_Z"
      have "((rat_of_int k) \<cdot>\<^sub>m inv_Z) $$ (i,j) =  (rat_of_int k * inv_Z $$ (i, j))"
        using index_smult_mat i j by auto
      hence kinvZ_in_Z': "... \<in> \<int>" using kinvZ_in_Z i j inv_Z mn by simp
      show "rat_of_int (int_of_rat (rat_of_int k * inv_Z $$ (i, j))) = rat_of_int k * inv_Z $$ (i, j)" 
        by (rule int_of_rat, insert kinvZ_in_Z', auto)
    qed
    hence "?RAT (k \<cdot>\<^sub>m (1\<^sub>m m)) = ?RAT ((map_mat int_of_rat ((rat_of_int k) \<cdot>\<^sub>m inv_Z))) * ?RAT ?Z"
      using r' by simp
    also have "... = ?RAT ((map_mat int_of_rat ((rat_of_int k) \<cdot>\<^sub>m inv_Z)) * ?Z)"
      by (metis RAT_fs_init adj_mat(1) k_inv_Z_eq_adj map_carrier_mat of_int_hom.mat_hom_mult)
    finally show ?thesis by (rule of_int_hom.mat_hom_inj)
  qed
  show ?thesis
  proof (rule mat_mult_sub_lattice[OF _ fs_init])
    have rw: "of_int_hom.mat_hom (map_mat int_of_rat ((rat_of_int k) \<cdot>\<^sub>m inv_Z)) 
      = map_mat int_of_rat ((rat_of_int k) \<cdot>\<^sub>m inv_Z)" by auto
    have "mat_of_rows n (Matrix.rows (k \<cdot>\<^sub>m 1\<^sub>m m)) = (k \<cdot>\<^sub>m (1\<^sub>m m))" 
      by (metis mn index_one_mat(3) index_smult_mat(3) mat_of_rows_rows)
    also have "... = of_int_hom.mat_hom (map_mat int_of_rat ((rat_of_int k) \<cdot>\<^sub>m inv_Z)) * mat_of_rows n fs_init" 
       using r rw by auto 
    finally show "mat_of_rows n (Matrix.rows (k \<cdot>\<^sub>m 1\<^sub>m m)) 
      = of_int_hom.mat_hom (map_mat int_of_rat ((rat_of_int k) \<cdot>\<^sub>m inv_Z)) * mat_of_rows n fs_init" .
   show "set (Matrix.rows (k \<cdot>\<^sub>m 1\<^sub>m m)) \<subseteq> carrier_vec n"using mn unfolding Matrix.rows_def by auto
   show "map_mat int_of_rat (rat_of_int k \<cdot>\<^sub>m inv_Z) \<in> carrier_mat (length (Matrix.rows (k \<cdot>\<^sub>m 1\<^sub>m m))) (length fs_init)"
     using len fs_init by (simp add: inv_Z)
  qed
qed

end

context LLL_with_assms
begin


lemma lattice_of_append_det_preserves:  
  assumes k_det: "k = abs (Determinant.det (mat_of_rows n fs_init))"
  and mn: "m = n"
  and A: "A = (mat_of_rows n fs_init) @\<^sub>r (k \<cdot>\<^sub>m (1\<^sub>m m))"
shows "lattice_of (Matrix.rows A) = lattice_of fs_init"
proof -
  have "Matrix.rows (mat_of_rows n fs_init @\<^sub>r k \<cdot>\<^sub>m 1\<^sub>m m) = (Matrix.rows (mat_of_rows n fs_init) @ Matrix.rows (k \<cdot>\<^sub>m (1\<^sub>m m)))"
    by (rule rows_append_rows, insert fs_init len mn, auto)
  also have "... = (fs_init @ Matrix.rows (k \<cdot>\<^sub>m (1\<^sub>m m)))" by (simp add: fs_init)
  finally have rw: "Matrix.rows (mat_of_rows n fs_init @\<^sub>r k \<cdot>\<^sub>m 1\<^sub>m m) 
    = (fs_init @ Matrix.rows (k \<cdot>\<^sub>m (1\<^sub>m m)))" .
  have "lattice_of (Matrix.rows A) = lattice_of (fs_init @ Matrix.rows (k \<cdot>\<^sub>m (1\<^sub>m m)))"
    by (rule arg_cong[of _ _ lattice_of], auto simp add: A rw)
  also have "... = lattice_of fs_init" 
  proof (cases "k = Determinant.det (mat_of_rows n fs_init)")
    case True
    then show ?thesis 
    by (rule already_in_lattice_append[symmetric, OF fs_init 
             lattice_of_kId_subset_fs_init[OF _ mn]], insert mn, auto simp add: Matrix.rows_def)
  next
    case False
    hence k2: "k = -Determinant.det (mat_of_rows n fs_init)" using k_det by auto
    have l: "lattice_of (Matrix.rows (- k \<cdot>\<^sub>m 1\<^sub>m m)) \<subseteq> lattice_of fs_init"
      by (rule lattice_of_kId_subset_fs_init[OF _ mn], insert k2, auto)
    have l2: "lattice_of (Matrix.rows (- k \<cdot>\<^sub>m 1\<^sub>m m)) = lattice_of (Matrix.rows (k \<cdot>\<^sub>m 1\<^sub>m m))" 
    proof (rule mat_mult_invertible_lattice_eq)
      let ?P = "(- 1::int) \<cdot>\<^sub>m 1\<^sub>m m"
      show P: "?P \<in> carrier_mat m m" by simp
      have "det ?P = 1 \<or> det ?P = -1" unfolding det_smult by (auto simp add: minus_1_power_even)
      hence "det ?P dvd 1" by (smt minus_dvd_iff one_dvd)
      thus " invertible_mat ?P" unfolding invertible_iff_is_unit_JNF[OF P] .
      have "(- k \<cdot>\<^sub>m 1\<^sub>m m) = ?P * (k \<cdot>\<^sub>m 1\<^sub>m m)"
        unfolding mat_diag_smult[symmetric] unfolding mat_diag_diag by auto
      thus " mat_of_rows n (Matrix.rows (- k \<cdot>\<^sub>m 1\<^sub>m m)) = of_int_hom.mat_hom ?P * mat_of_rows n (Matrix.rows (k \<cdot>\<^sub>m 1\<^sub>m m))"
        by (metis mn index_one_mat(3) index_smult_mat(3) mat_of_rows_rows of_int_mat_hom_int_id)
      show " set (Matrix.rows (- k \<cdot>\<^sub>m 1\<^sub>m m)) \<subseteq> carrier_vec n"
        and "set (Matrix.rows (k \<cdot>\<^sub>m 1\<^sub>m m)) \<subseteq> carrier_vec n"
        using assms(2) one_carrier_mat set_rows_carrier smult_carrier_mat by blast+
    qed (insert mn, auto)
    hence l2: "lattice_of (Matrix.rows (k \<cdot>\<^sub>m 1\<^sub>m m)) \<subseteq> lattice_of fs_init" using l by auto
    show ?thesis by (rule already_in_lattice_append[symmetric, OF fs_init l2],
          insert mn one_carrier_mat set_rows_carrier smult_carrier_mat, blast)
  qed  
  finally show ?thesis .
qed

text \<open>This is another key lemma.
Here, $A$ is the initial matrix @{text "(mat_of_rows n fs_init)"} augmented with $m$ rows 
$(k,0,\dots,0),(0,k,0,\dots,0), \dots , (0,\dots,0,k)$ where $k$ is the determinant of 
@{text "(mat_of_rows n fs_init)"}. 
With the algorithm of the article, we obtain @{text "H = H' @\<^sub>r (0\<^sub>m m n)"} by means of an invertible 
matrix $P$ (which is computable). Then, $H$ is the HNF of $A$.
The lemma shows that $H'$ is the HNF of @{text "(mat_of_rows n fs_init)"}
and that there exists an invertible matrix to carry out the transformation.\<close>

lemma Hermite_append_det_id:
  assumes k_det: "k = abs (Determinant.det (mat_of_rows n fs_init))"
  and mn: "m = n"
  and A: "A = (mat_of_rows n fs_init) @\<^sub>r (k \<cdot>\<^sub>m (1\<^sub>m m))"
  and H': "H'\<in> carrier_mat m n"
  and H_append: "H = H' @\<^sub>r (0\<^sub>m m n)"
  and P: "P \<in> carrier_mat (m+m) (m+m)"
  and inv_P: "invertible_mat P"
  and A_PH: "A = P * H"
  and HNF_H: "Hermite_JNF associates res H"
shows "Hermite_JNF associates res H'" 
  and "(\<exists>P'. invertible_mat P' \<and> P' \<in> carrier_mat m m \<and> (mat_of_rows n fs_init) = P' * H')"
proof -
  have A_carrier: "A \<in> carrier_mat (m+m) n" using A mn len by auto
  let ?A' = "(mat_of_rows n fs_init)"
  let ?H' = "submatrix H {0..<m} {0..<n}"
  have nm: "n\<le>m" by (simp add: mn) 
  have H: "H \<in> carrier_mat (m + m) n" using H_append H' by auto
  have submatrix_carrier: "submatrix H {0..<m} {0..<n} \<in> carrier_mat m n"
    by (rule submatrix_carrier_first[OF H], auto)
  have H'_eq: "H' = ?H'"
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row ?H'" and j: "j < dim_col ?H'"
    have im: "i<m" and jn: "j<n" using i j submatrix_carrier by auto
    have "?H' $$ (i,j) = H $$ (i,j)"
      by (rule submatrix_index_id[OF H], insert i j submatrix_carrier, auto)
    also have "... =  (if i < dim_row H' then H' $$ (i, j) else (0\<^sub>m m n) $$ (i - m, j))"
      unfolding H_append by (rule append_rows_nth[OF H'], insert im jn, auto)
    also have "... = H' $$ (i,j)" using H' im jn by simp
    finally show "H' $$ (i, j) = ?H' $$ (i, j)" ..
  qed (insert H' submatrix_carrier, auto)  
  show HNF_H': "Hermite_JNF associates res H'"
    unfolding H'_eq mn by (rule HNF_submatrix[OF HNF_H H], insert nm, simp)
  have L_fs_init_A: "lattice_of (fs_init) = lattice_of (Matrix.rows A)" 
    by (rule lattice_of_append_det_preserves[symmetric, OF k_det mn A])
  have L_H'_H: "lattice_of (Matrix.rows H') = lattice_of (Matrix.rows H)"
    using H_append H' lattice_of_append_zero_rows by blast
  have L_A_H: "lattice_of (Matrix.rows A) = lattice_of (Matrix.rows H)"
  proof (rule mat_mult_invertible_lattice_eq[OF _ _ P inv_P])
    show "set (Matrix.rows A) \<subseteq> carrier_vec n" using A_carrier set_rows_carrier by blast
    show "set (Matrix.rows H) \<subseteq> carrier_vec n" using H set_rows_carrier by blast
    show "length (Matrix.rows A) = m + m" using A_carrier by auto      
    show "length (Matrix.rows H) = m + m" using H by auto
    show "mat_of_rows n (Matrix.rows A) = of_int_hom.mat_hom P * mat_of_rows n (Matrix.rows H)"      
      by (metis A_carrier H A_PH carrier_matD(2) mat_of_rows_rows of_int_mat_hom_int_id)
  qed
  have L_fs_init_H': "lattice_of fs_init = lattice_of (Matrix.rows H')"
    using L_fs_init_A L_A_H L_H'_H by auto
  have exists_P2: 
      "\<exists>P2. P2 \<in> carrier_mat n n \<and> invertible_mat P2 \<and> mat_of_rows n  (Matrix.rows H') = P2 * H'"
    by (rule exI[of _ "1\<^sub>m n"], insert H' mn, auto)
  have exist_P': "\<exists>P'\<in>carrier_mat n n. invertible_mat P' 
      \<and> mat_of_rows n fs_init = P' * mat_of_rows n (Matrix.rows H')"
    by (rule eq_lattice_imp_mat_mult_invertible_rows[OF fs_init _ lin_dep len[unfolded mn] _ L_fs_init_H'],
        insert H' mn set_rows_carrier, auto)
  thus "\<exists>P'. invertible_mat P' \<and> P' \<in> carrier_mat m m \<and> (mat_of_rows n fs_init) = P' * H'"
    by (metis mn H' carrier_matD(2) mat_of_rows_rows)
qed
end



context proper_mod_operation
begin

(* Perform the modulo D operation to reduce the element A$$(a,j), assuming A = A' @\<^sub>r  (D \<cdot>\<^sub>m (1\<^sub>m m))*)
definition "reduce_element_mod_D (A::int mat) a j D m =  
  (if j = 0 then if D dvd A$$(a,j) then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A else A
  else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)"

definition "reduce_element_mod_D_abs (A::int mat) a j D m =  
  (if j = 0 \<and> D dvd A$$(a,j) then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A 
  else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)"

lemma reduce_element_mod_D_preserves_dimensions:
  shows [simp]: "dim_row (reduce_element_mod_D A a j D m) = dim_row A" 
    and [simp]: "dim_col (reduce_element_mod_D A a j D m) = dim_col A"
    and [simp]: "dim_row (reduce_element_mod_D_abs A a j D m) = dim_row A" 
    and [simp]: "dim_col (reduce_element_mod_D_abs A a j D m) = dim_col A"
  by (auto simp add: reduce_element_mod_D_def reduce_element_mod_D_abs_def Let_def split_beta)

lemma reduce_element_mod_D_carrier:
  shows "reduce_element_mod_D A a j D m \<in> carrier_mat (dim_row A) (dim_col A)" 
    and "reduce_element_mod_D_abs A a j D m \<in> carrier_mat (dim_row A) (dim_col A)" by auto


lemma reduce_element_mod_D_invertible_mat:
  assumes A_def: "A = A' @\<^sub>r  (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "j<n" and mn: "m\<ge>n"
  shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_element_mod_D A a j D m = P * A" (is ?thesis1)
    and "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_element_mod_D_abs A a j D m = P * A" (is ?thesis2)
  unfolding atomize_conj
proof (rule conjI; cases "j = 0 \<and> D dvd A$$(a,j)")
  case True
  let ?P = "addrow_mat (m+n) (- (A $$ (a, j) gdiv D) + 1) a (j + m)"
  have A: "A \<in> carrier_mat (m + n) n" using A_def A' mn by auto
  have "reduce_element_mod_D A a j D m = addrow (- (A $$ (a, j) gdiv D) + 1) a (j + m) A"
    unfolding reduce_element_mod_D_def using True by auto
  also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
  finally have "reduce_element_mod_D A a j D m = ?P * A" .
  moreover have P: "?P \<in> carrier_mat (m+n) (m+n)" by simp
  moreover have inv_P: "invertible_mat ?P"
    by (metis addrow_mat_carrier a det_addrow_mat dvd_mult_right 
        invertible_iff_is_unit_JNF mult.right_neutral not_add_less2 semiring_gcd_class.gcd_dvd1)
  ultimately show ?thesis1 by blast
  have "reduce_element_mod_D_abs A a j D m = addrow (- (A $$ (a, j) gdiv D) + 1) a (j + m) A"
    unfolding reduce_element_mod_D_abs_def using True by auto
  also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
  finally have "reduce_element_mod_D_abs A a j D m = ?P * A" .
  thus ?thesis2 using P inv_P by blast
next
  case False note nc1 = False
  let ?P = "addrow_mat (m+n) (- (A $$ (a, j) gdiv D)) a (j + m)"
  have A: "A \<in> carrier_mat (m + n) n" using A_def A' mn by auto
  have P: "?P \<in> carrier_mat (m+n) (m+n)" by simp
  have inv_P: "invertible_mat ?P"
    by (metis addrow_mat_carrier a det_addrow_mat dvd_mult_right 
        invertible_iff_is_unit_JNF mult.right_neutral not_add_less2 semiring_gcd_class.gcd_dvd1)
  show ?thesis1
  proof (cases "j = 0")
    case True
    have "reduce_element_mod_D A a j D m = A" 
      unfolding reduce_element_mod_D_def using True nc1 by auto
    thus ?thesis1
      by (metis A_def A' carrier_append_rows invertible_mat_one 
          left_mult_one_mat one_carrier_mat smult_carrier_mat)
  next
    case False   
    have "reduce_element_mod_D A a j D m =  addrow (- (A $$ (a, j) gdiv D)) a (j + m) A"
      unfolding reduce_element_mod_D_def using False by auto
    also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
    finally have "reduce_element_mod_D A a j D m = ?P * A" .    
    thus ?thesis using P inv_P by blast
  qed
  have "reduce_element_mod_D_abs A a j D m =  addrow (- (A $$ (a, j) gdiv D)) a (j + m) A"
    unfolding reduce_element_mod_D_abs_def using False by auto
  also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
  finally have "reduce_element_mod_D_abs A a j D m = ?P * A" .    
  thus ?thesis2 using P inv_P by blast
qed


lemma reduce_element_mod_D_append:
  assumes A_def: "A = A' @\<^sub>r  (D \<cdot>\<^sub>m (1\<^sub>m n))"
  and A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "j<n" and mn: "m\<ge>n"
shows "reduce_element_mod_D A a j D m 
  = mat_of_rows n [Matrix.row (reduce_element_mod_D A a j D m) i. i \<leftarrow> [0..<m]] @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))" (is "?lhs = ?A' @\<^sub>r ?D")
and "reduce_element_mod_D_abs A a j D m 
  = mat_of_rows n [Matrix.row (reduce_element_mod_D_abs A a j D m) i. i \<leftarrow> [0..<m]] @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))" (is "?lhs_abs = ?A'_abs @\<^sub>r ?D")
  unfolding atomize_conj
proof (rule conjI; rule eq_matI)
  let ?xs = "(map (Matrix.row (reduce_element_mod_D A a j D m)) [0..<m])"
  let ?xs_abs = "(map (Matrix.row (reduce_element_mod_D_abs A a j D m)) [0..<m])"
  have lhs_carrier: "?lhs \<in> carrier_mat (m+n) n"
    and lhs_carrier_abs: "?lhs_abs \<in> carrier_mat (m+n) n"
    by (metis (no_types, lifting) add.comm_neutral append_rows_def A_def A' carrier_matD 
        carrier_mat_triv index_mat_four_block(2,3) index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) 
        reduce_element_mod_D_preserves_dimensions)+
  have map_A_carrier[simp]: "?A' \<in> carrier_mat m n" 
    and map_A_carrier_abs[simp]: "?A'_abs \<in> carrier_mat m n"
    by (simp add: mat_of_rows_def)+
  have AD_carrier[simp]: "?A' @\<^sub>r ?D \<in> carrier_mat (m+n) n" 
    and AD_carrier_abs[simp]: "?A'_abs @\<^sub>r ?D \<in> carrier_mat (m+n) n" 
    by (rule carrier_append_rows, insert lhs_carrier mn, auto)
  show "dim_row (?lhs) = dim_row (?A' @\<^sub>r ?D)"  and "dim_col (?lhs) = dim_col (?A' @\<^sub>r ?D)"
    "dim_row (?lhs_abs) = dim_row (?A'_abs @\<^sub>r ?D)"  and "dim_col (?lhs_abs) = dim_col (?A'_abs @\<^sub>r ?D)"
    using lhs_carrier lhs_carrier_abs AD_carrier AD_carrier_abs unfolding carrier_mat_def by simp+
  show "?lhs $$ (i, ja) = (?A' @\<^sub>r ?D) $$ (i, ja)" if i: "i < dim_row (?A' @\<^sub>r ?D)" and ja: "ja < dim_col (?A' @\<^sub>r ?D)" for i ja
  proof (cases "i<m")
    case True
    have ja_n: "ja < n"
      by (metis Nat.add_0_right append_rows_def index_mat_four_block(3) index_zero_mat(3) ja mat_of_rows_carrier(3))
    have "(?A' @\<^sub>r ?D) $$ (i, ja) = ?A' $$ (i,ja)"
      by (metis (no_types, lifting) Nat.add_0_right True append_rows_def diff_zero i 
          index_mat_four_block index_zero_mat(3) ja length_map length_upt mat_of_rows_carrier(2))
    also have "... = ?xs ! i $v ja" 
      by (rule mat_of_rows_index, insert i True ja , auto simp add: append_rows_def)
    also have "... = ?lhs $$ (i,ja)"
      by (rule map_first_rows_index, insert assms lhs_carrier True i ja_n, auto)
    finally show ?thesis ..
  next
    case False
    have ja_n: "ja < n"
      by (metis Nat.add_0_right append_rows_def index_mat_four_block(3) index_zero_mat(3) ja mat_of_rows_carrier(3))
    have "(?A' @\<^sub>r ?D) $$ (i, ja) =?D $$ (i-m,ja)"
      by (smt False Nat.add_0_right map_A_carrier append_rows_def carrier_matD i 
          index_mat_four_block index_zero_mat(3) ja_n)
    also have "... = ?lhs $$ (i,ja)"
      by (metis (no_types, lifting) False Nat.add_0_right map_A_carrier append_rows_def A_def A' a 
          carrier_matD i index_mat_addrow(1) index_mat_four_block(1,2) index_zero_mat(3) ja_n 
          lhs_carrier reduce_element_mod_D_def reduce_element_mod_D_preserves_dimensions)
    finally show ?thesis ..
  qed
  fix i ja assume i: "i < dim_row (?A'_abs @\<^sub>r ?D)" and ja: "ja < dim_col (?A'_abs @\<^sub>r ?D)"
  have ja_n: "ja < n"
    by (metis Nat.add_0_right append_rows_def index_mat_four_block(3) index_zero_mat(3) ja mat_of_rows_carrier(3))
  show "?lhs_abs $$ (i, ja) = (?A'_abs @\<^sub>r ?D) $$ (i, ja)"
  proof (cases "i<m")
    case True
    have "(?A'_abs @\<^sub>r ?D) $$ (i, ja) = ?A'_abs $$ (i,ja)"
      by (metis (no_types, lifting) Nat.add_0_right True append_rows_def diff_zero i 
          index_mat_four_block index_zero_mat(3) ja length_map length_upt mat_of_rows_carrier(2))
    also have "... = ?xs_abs ! i $v ja" 
      by (rule mat_of_rows_index, insert i True ja , auto simp add: append_rows_def)
    also have "... = ?lhs_abs $$ (i,ja)"
      by (rule map_first_rows_index, insert assms lhs_carrier_abs True i ja_n, auto)
    finally show ?thesis ..
  next
    case False
    have "(?A'_abs @\<^sub>r ?D) $$ (i, ja) = ?D $$ (i-m,ja)"
      by (smt False Nat.add_0_right map_A_carrier_abs append_rows_def carrier_matD i 
          index_mat_four_block index_zero_mat(3) ja_n)
    also have "... = ?lhs_abs $$ (i,ja)"
      by (metis (no_types, lifting) False Nat.add_0_right map_A_carrier_abs append_rows_def A_def A' a 
          carrier_matD i index_mat_addrow(1) index_mat_four_block(1,2) index_zero_mat(3) ja_n 
          lhs_carrier_abs reduce_element_mod_D_abs_def reduce_element_mod_D_preserves_dimensions)
    finally show ?thesis ..
  qed
qed


lemma reduce_append_rows_eq:
  assumes A': "A' \<in> carrier_mat m n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))" and a: "a<m" and xm: "x<m" and "0<n"
  and Aaj: "A $$ (a,0) \<noteq> 0" 
  shows "reduce a x D A 
  = mat_of_rows n [Matrix.row ((reduce a x D A)) i. i \<leftarrow> [0..<m]] @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" (is ?thesis1)
  and "reduce_abs a x D A 
  = mat_of_rows n [Matrix.row ((reduce_abs a x D A)) i. i \<leftarrow> [0..<m]] @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" (is ?thesis2)
  unfolding atomize_conj
proof (rule conjI; rule matrix_append_rows_eq_if_preserves)
  let ?reduce_ax = "reduce a x D A"
  let ?reduce_abs = "reduce_abs a x D A"
 obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
   by (metis prod_cases5)
  have A: "A: carrier_mat (m+n) n" by (simp add: A_def A')
  show D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" and "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by simp+
  show "?reduce_ax \<in> carrier_mat (m + n) n"  "?reduce_abs \<in> carrier_mat (m + n) n"
    by (metis Nat.add_0_right append_rows_def A' A_def carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2) index_zero_mat(3) reduce_preserves_dimensions)+
  show "\<forall>i\<in>{m..<m + n}. \<forall>ja<n. ?reduce_ax $$ (i, ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" 
    and "\<forall>i\<in>{m..<m + n}. \<forall>ja<n. ?reduce_abs $$ (i, ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)"
    unfolding atomize_conj
  proof (rule conjI; rule+)
    fix i ja assume i: "i \<in> {m..<m + n}" and ja: "ja < n"
    have ja_dc: "ja < dim_col A" and i_dr: "i < dim_row A" using i ja A by auto
    have i_not_a: "i \<noteq> a" using i a by auto
    have i_not_x: "i \<noteq> x" using i xm by auto
    have "?reduce_ax $$ (i,ja) = A $$ (i,ja)" 
      unfolding reduce_alt_def_not0[OF Aaj pquvd] using ja_dc i_dr i_not_a i_not_x by auto 
    also have "... = (if i < dim_row A' then A' $$(i,ja) else (D \<cdot>\<^sub>m (1\<^sub>m n))$$(i-m,ja))"
      by (unfold A_def, rule append_rows_nth[OF A' D1 _ ja], insert A i_dr, simp)
    also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" using i A' by auto
    finally show "?reduce_ax $$ (i,ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" .   
    have "?reduce_abs $$ (i,ja) = A $$ (i,ja)" 
      unfolding reduce_alt_def_not0[OF Aaj pquvd] using ja_dc i_dr i_not_a i_not_x by auto 
    also have "... = (if i < dim_row A' then A' $$(i,ja) else (D \<cdot>\<^sub>m (1\<^sub>m n))$$(i-m,ja))"
      by (unfold A_def, rule append_rows_nth[OF A' D1 _ ja], insert A i_dr, simp)
    also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" using i A' by auto
    finally show "?reduce_abs $$ (i,ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" .   
  qed
qed

fun reduce_row_mod_D
  where "reduce_row_mod_D A a [] D m = A" |
        "reduce_row_mod_D A a (x # xs) D m = reduce_row_mod_D (reduce_element_mod_D A a x D m) a xs D m"

fun reduce_row_mod_D_abs
  where "reduce_row_mod_D_abs A a [] D m = A" |
        "reduce_row_mod_D_abs A a (x # xs) D m = reduce_row_mod_D_abs (reduce_element_mod_D_abs A a x D m) a xs D m"


lemma reduce_row_mod_D_preserves_dimensions:
  shows [simp]: "dim_row (reduce_row_mod_D A a xs D m) = dim_row A" 
    and [simp]: "dim_col (reduce_row_mod_D A a xs D m) = dim_col A"
  by (induct A a xs D m rule: reduce_row_mod_D.induct, auto)
  
lemma reduce_row_mod_D_preserves_dimensions_abs:
  shows [simp]: "dim_row (reduce_row_mod_D_abs A a xs D m) = dim_row A" 
    and [simp]: "dim_col (reduce_row_mod_D_abs A a xs D m) = dim_col A"
  by (induct A a xs D m rule: reduce_row_mod_D_abs.induct, auto)

lemma reduce_row_mod_D_invertible_mat:
  assumes A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
  and A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "\<forall>j\<in>set xs. j<n" and mn: "m\<ge>n"
  shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_row_mod_D A a xs D m = P * A"
  using assms
proof (induct A a xs D m arbitrary: A' rule: reduce_row_mod_D.induct)
  case (1 A a D m)
  show ?case by (rule exI[of _ "1\<^sub>m (m+n)"], insert "1.prems", auto simp add: append_rows_def)
next
  case (2 A a x xs D m)
  let ?reduce_xs = "(reduce_element_mod_D A a x D m)"
  have 1: "reduce_row_mod_D A a (x # xs) D m 
    = reduce_row_mod_D ?reduce_xs a xs D m" by simp
  have "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_element_mod_D A a x D m = P * A" 
    by (rule reduce_element_mod_D_invertible_mat, insert "2.prems", auto)
  from this obtain P where P: "P \<in> carrier_mat (m+n) (m+n)" and inv_P: "invertible_mat P"
    and R_P: "reduce_element_mod_D A a x D m = P * A" by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> reduce_row_mod_D ?reduce_xs a xs D m = P * ?reduce_xs"
  proof (rule "2.hyps")
    let ?A' = "mat_of_rows n [Matrix.row (reduce_element_mod_D A a x D m) i. i \<leftarrow> [0..<m]]"
    show "reduce_element_mod_D A a x D m = ?A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
      by (rule reduce_element_mod_D_append, insert "2.prems", auto)
  qed (insert "2.prems", auto)   
  from this obtain P2 where P2: "P2 \<in> carrier_mat (m + n) (m + n)" and inv_P2: "invertible_mat P2"
    and R_P2: "reduce_row_mod_D ?reduce_xs a xs D m = P2 * ?reduce_xs"
    by auto
  have "invertible_mat (P2 * P)" using P P2 inv_P inv_P2 invertible_mult_JNF by blast
  moreover have "(P2 * P) \<in> carrier_mat (m+n) (m+n)" using P2 P by auto
  moreover have "reduce_row_mod_D A a (x # xs) D m = (P2 * P) * A" 
    by (smt P P2 R_P R_P2 1 assoc_mult_mat carrier_matD carrier_mat_triv
        index_mult_mat reduce_row_mod_D_preserves_dimensions)
  ultimately show ?case by blast
qed


lemma reduce_row_mod_D_abs_invertible_mat:
  assumes A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
  and A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "\<forall>j\<in>set xs. j<n" and mn: "m\<ge>n"
  shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_row_mod_D_abs A a xs D m = P * A"
  using assms
proof (induct A a xs D m arbitrary: A' rule: reduce_row_mod_D_abs.induct)
  case (1 A a D m)
  show ?case by (rule exI[of _ "1\<^sub>m (m+n)"], insert "1.prems", auto simp add: append_rows_def)
next
  case (2 A a x xs D m)
  let ?reduce_xs = "(reduce_element_mod_D_abs A a x D m)"
  have 1: "reduce_row_mod_D_abs A a (x # xs) D m 
    = reduce_row_mod_D_abs ?reduce_xs a xs D m" by simp
  have "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_element_mod_D_abs A a x D m = P * A" 
    by (rule reduce_element_mod_D_invertible_mat, insert "2.prems", auto)
  from this obtain P where P: "P \<in> carrier_mat (m+n) (m+n)" and inv_P: "invertible_mat P"
    and R_P: "reduce_element_mod_D_abs A a x D m = P * A" by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> reduce_row_mod_D_abs ?reduce_xs a xs D m = P * ?reduce_xs"
  proof (rule "2.hyps")
    let ?A' = "mat_of_rows n [Matrix.row (reduce_element_mod_D_abs A a x D m) i. i \<leftarrow> [0..<m]]"
    show "reduce_element_mod_D_abs A a x D m = ?A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
      by (rule reduce_element_mod_D_append, insert "2.prems", auto)
  qed (insert "2.prems", auto)   
  from this obtain P2 where P2: "P2 \<in> carrier_mat (m + n) (m + n)" and inv_P2: "invertible_mat P2"
    and R_P2: "reduce_row_mod_D_abs ?reduce_xs a xs D m = P2 * ?reduce_xs"
    by auto
  have "invertible_mat (P2 * P)" using P P2 inv_P inv_P2 invertible_mult_JNF by blast
  moreover have "(P2 * P) \<in> carrier_mat (m+n) (m+n)" using P2 P by auto
  moreover have "reduce_row_mod_D_abs A a (x # xs) D m = (P2 * P) * A" 
    by (smt P P2 R_P R_P2 1 assoc_mult_mat carrier_matD carrier_mat_triv
        index_mult_mat reduce_row_mod_D_preserves_dimensions_abs)
  ultimately show ?case by blast
qed
end

context proper_mod_operation
begin
lemma dvd_gdiv_mult_left[simp]: assumes "b > 0" "b dvd a" shows "b * (a gdiv b) = a"
  using dvd_gdiv_mult_right[OF assms] by (auto simp: ac_simps)


lemma reduce_element_mod_D:
  assumes A_def: "A = A' @\<^sub>r  (D \<cdot>\<^sub>m (1\<^sub>m n))"
  and A': "A' \<in> carrier_mat m n" and a: "a\<le>m" and j: "j<n" and mn: "m\<ge>n"
  and D: "D > 0" 
  shows "reduce_element_mod_D A a j D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 then if D dvd A$$(i,k) 
          then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" (is "_ = ?A")
    and "reduce_element_mod_D_abs A a j D m = Matrix.mat (dim_row A) (dim_col A)
      (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 \<and> D dvd A$$(i,k) then D else A$$(i,k) gmod D else A$$(i,k))" (is "_ = ?A_abs")
unfolding atomize_conj
proof (rule conjI; rule eq_matI)
  have A: "A \<in> carrier_mat (m+n) n" using A_def A'  by simp
  have dr: "dim_row ?A = dim_row ?A_abs" and dc: "dim_col ?A = dim_col ?A_abs" by auto
  have 1: "reduce_element_mod_D A a j D m $$ (i, ja) = ?A $$ (i, ja)" (is ?thesis1)
    and 2: "reduce_element_mod_D_abs A a j D m $$ (i, ja) = ?A_abs $$ (i, ja)" (is ?thesis2)
    if i: "i < dim_row ?A" and ja: "ja < dim_col ?A" for i ja
    unfolding atomize_conj
  proof (rule conjI; cases "i=a")
    case False
    have "reduce_element_mod_D A a j D m = (if j = 0 then if D dvd A$$(a,j) then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A 
    else A
    else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)"
      unfolding reduce_element_mod_D_def by simp
    also have "... $$ (i,ja) = A $$ (i, ja)" unfolding mat_addrow_def using False ja i by auto     
    also have "... = ?A $$ (i,ja)" using False using i ja by auto
    finally show ?thesis1 .
    have "reduce_element_mod_D_abs A a j D m $$ (i,ja) = A $$ (i, ja)"
      unfolding reduce_element_mod_D_abs_def mat_addrow_def using False ja i by auto     
    also have "... = ?A_abs $$ (i,ja)" using False using i ja by auto
    finally show ?thesis2 .
  next
    case True note ia = True
    have "reduce_element_mod_D A a j D m 
      = (if j = 0 then if D dvd A$$(a,j) then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A else A
        else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)" 
      unfolding reduce_element_mod_D_def by simp
    also have "... $$ (i,ja) = ?A $$ (i,ja)"
    proof (cases "ja = j")
      case True note ja_j = True
      have "A $$ (j + m, ja) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (j,ja)"
        by (rule append_rows_nth2[OF A' _ A_def ], insert j ja A mn, auto)       
      also have "... = D * (1\<^sub>m n) $$ (j,ja)" by (rule index_smult_mat, insert ja j A mn, auto)
      also have "... = D" by (simp add: True j mn)
      finally have A_ja_jaD: "A $$ (j + m, ja) = D" .
      show ?thesis
      proof (cases "j=0 \<and> D dvd A$$(a,j)")
        case True         
        have 1: "reduce_element_mod_D A a j D m = addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A "
          using True ia ja_j unfolding reduce_element_mod_D_def by auto
        also have "... $$(i,ja) = (- (A $$ (a, j) gdiv D) + 1) * A $$ (j + m, ja) + A $$ (i, ja)"
          unfolding mat_addrow_def using True ja_j ia
          using A i j by auto
        also have "... = D"
        proof -
          have "A $$ (i, ja) + D * - (A $$ (i, ja) gdiv D) = 0"
            using True ia ja_j D by force
          then show ?thesis
            by (metis A_ja_jaD ab_semigroup_add_class.add_ac(1) add.commute add_right_imp_eq ia int_distrib(2)
                ja_j more_arith_simps(3) mult.commute mult_cancel_right1)
        qed   
        also have "... = ?A $$ (i,ja)" using True ia A i j ja_j by auto
        finally show ?thesis
          using True 1 by auto
      next
        case False
        show ?thesis
        proof (cases "ja=0")
          case True
          then show ?thesis
            using False i ja ja_j by force
        next
          case False
        have "?A $$ (i,ja) = A $$ (i, ja) gmod D" using True ia A i j False by auto
        also have "... = A $$ (i, ja) - ((A $$ (i, ja) gdiv D) * D)"
          by (subst gmod_gdiv[OF D], auto)
        also have "... =  - (A $$ (a, j) gdiv D) * A $$ (j + m, ja) + A $$ (i, ja)"
          unfolding A_ja_jaD by (simp add: True ia)
        finally show ?thesis 
          using A False True i ia j by auto
      qed
    qed
  next
      case False
      have "A $$ (j + m, ja) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (j,ja)"
        by (rule append_rows_nth2[OF A' _ A_def ], insert j mn ja A, auto)       
      also have "... = D * (1\<^sub>m n) $$ (j,ja)" by (rule index_smult_mat, insert ja j A mn, auto)
      also have "... = 0" using False using A a mn ja j by force        
      finally have A_am_ja0: "A $$ (j + m, ja) = 0" .
      then show ?thesis using False i ja by fastforce
    qed
    finally show ?thesis1 .
    have "reduce_element_mod_D_abs A a j D m 
      = (if j = 0 \<and> D dvd A$$(a,j) then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A
        else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)" 
      unfolding reduce_element_mod_D_abs_def by simp
    also have "... $$ (i,ja) = ?A_abs $$ (i,ja)"
    proof (cases "ja = j")
      case True note ja_j = True
      have "A $$ (j + m, ja) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (j,ja)"
        by (rule append_rows_nth2[OF A' _ A_def ], insert j ja A mn, auto)       
      also have "... = D * (1\<^sub>m n) $$ (j,ja)" by (rule index_smult_mat, insert ja j A mn, auto)
      also have "... = D" by (simp add: True j mn)
      finally have A_ja_jaD: "A $$ (j + m, ja) = D" .
      show ?thesis
      proof (cases "j=0 \<and> D dvd A$$(a,j)")
        case True         
        have 1: "reduce_element_mod_D_abs A a j D m = addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A "
          using True ia ja_j unfolding reduce_element_mod_D_abs_def by auto
        also have "... $$(i,ja) = (- (A $$ (a, j) gdiv D) + 1) * A $$ (j + m, ja) + A $$ (i, ja)"
          unfolding mat_addrow_def using True ja_j ia
          using A i j by auto
        also have "... = D"
        proof -
          have "A $$ (i, ja) + D * - (A $$ (i, ja) gdiv D) = 0"
            using True ia ja_j D by force
          then show ?thesis
            by (metis A_ja_jaD ab_semigroup_add_class.add_ac(1) add.commute add_right_imp_eq ia int_distrib(2)
                ja_j more_arith_simps(3) mult.commute mult_cancel_right1)
        qed   
        also have "... = ?A_abs $$ (i,ja)" using True ia A i j ja_j by auto
        finally show ?thesis
          using True 1 by auto
      next
        case False
        have i: "i<dim_row ?A_abs" and ja: "ja<dim_col ?A_abs" using i ja by auto
        have "?A_abs $$ (i,ja) = A $$ (i, ja) gmod D" using True ia A i j False by auto
        also have "... = A $$ (i, ja) - ((A $$ (i, ja) gdiv D) * D)"
          by (subst gmod_gdiv[OF D], auto)
        also have "... =  - (A $$ (a, j) gdiv D) * A $$ (j + m, ja) + A $$ (i, ja)"
          unfolding A_ja_jaD by (simp add: True ia)
        finally show ?thesis 
          using A False True i ia j by auto
      qed    
  next
      case False
      have "A $$ (j + m, ja) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (j,ja)"
        by (rule append_rows_nth2[OF A' _ A_def ], insert j mn ja A, auto)       
      also have "... = D * (1\<^sub>m n) $$ (j,ja)" by (rule index_smult_mat, insert ja j A mn, auto)
      also have "... = 0" using False using A a mn ja j by force        
      finally have A_am_ja0: "A $$ (j + m, ja) = 0" .
      then show ?thesis using False i ja by fastforce
    qed
    finally show ?thesis2 .  
  qed
  from this
  show "\<And>i ja. i<dim_row ?A \<Longrightarrow> ja < dim_col ?A \<Longrightarrow> reduce_element_mod_D A a j D m $$ (i, ja) = ?A $$ (i, ja)" 
    and "\<And>i ja. i<dim_row ?A_abs \<Longrightarrow> ja < dim_col ?A_abs \<Longrightarrow> reduce_element_mod_D_abs A a j D m $$ (i, ja) = ?A_abs $$ (i, ja)" 
    using dr dc by auto
next
  show "dim_row (reduce_element_mod_D A a j D m) = dim_row ?A" 
    and "dim_col (reduce_element_mod_D A a j D m) = dim_col ?A"
    "dim_row (reduce_element_mod_D_abs A a j D m) = dim_row ?A_abs" 
    and "dim_col (reduce_element_mod_D_abs A a j D m) = dim_col ?A_abs"
    by auto
qed


lemma reduce_row_mod_D:
  assumes A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "\<forall>j\<in>set xs. j<n"
    and d: "distinct xs" and "m\<ge>n"
    and "D > 0" 
  shows "reduce_row_mod_D A a xs D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set xs then if k = 0 then if D dvd A$$(i,k) 
           then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))"
  using assms
proof (induct A a xs D m arbitrary: A' rule: reduce_row_mod_D.induct)
  case (1 A a D m)
  then show ?case by force
next
  case (2 A a x xs D m)
  let ?reduce_xs = "(reduce_element_mod_D A a x D m)"
  have 1: "reduce_row_mod_D A a (x # xs) D m 
    = reduce_row_mod_D ?reduce_xs a xs D m" by simp
  have 2: "reduce_element_mod_D A a j D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 then if D dvd A$$(i,k)
          then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" if "j<n" for j
    by (rule reduce_element_mod_D, insert "2.prems" that, auto)
  have "reduce_row_mod_D ?reduce_xs a xs D m =
    Matrix.mat (dim_row ?reduce_xs) (dim_col ?reduce_xs) (\<lambda>(i,k). if i = a \<and> k \<in> set xs then 
    if k=0 then if D dvd ?reduce_xs $$ (i, k) then D else ?reduce_xs $$ (i, k)
    else ?reduce_xs $$ (i, k) gmod D else ?reduce_xs $$ (i, k))"
  proof (rule "2.hyps")
    let ?A' = "mat_of_rows n [Matrix.row (reduce_element_mod_D A a x D m) i. i \<leftarrow> [0..<m]]"
    show "reduce_element_mod_D A a x D m = ?A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
      by (rule reduce_element_mod_D_append, insert "2.prems", auto)
  qed (insert "2.prems", auto)
  also have "... = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set (x # xs) then if k = 0 then if D dvd A$$(i,k)
          then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" (is "?lhs = ?rhs")
  proof (rule eq_matI) 
    show "dim_row ?lhs = dim_row ?rhs" and "dim_col ?lhs = dim_col ?rhs" by auto
    fix i j assume i: "i<dim_row ?rhs" and j: "j < dim_col ?rhs"
    have jn: "j<n" using j "2.prems" by (simp add: append_rows_def)
    have xn: "x < n" by (simp add: "2.prems"(4))
    show "?lhs $$ (i,j) = ?rhs $$ (i,j)"
    proof (cases "i=a \<and> j \<in> set xs")
      case True note ia_jxs = True
      have j_not_x: "j\<noteq>x"
        using "2.prems"(5) True by auto
      show ?thesis
      proof (cases "j=0 \<and> D dvd ?reduce_xs $$(i,j)")
        case True
        have "?lhs $$ (i,j) = D"
          using True i j ia_jxs by auto
        also have "... = ?rhs $$ (i,j)" using i j j_not_x 
          by (smt "2" calculation dim_col_mat(1) dim_row_mat(1) index_mat(1) insert_iff list.set(2) prod.simps(2) xn)
        finally show ?thesis .
      next
        case False note nc1 = False
        show ?thesis
        proof (cases "j=0")
          case True
          then show ?thesis
            by (smt (z3) "2" False case_prod_conv dim_col_mat(1) dim_row_mat(1) i index_mat(1) j j_not_x xn)
        next
          case False          
      have "?lhs $$ (i,j) = ?reduce_xs $$ (i, j) gmod D"
        using True False i j by auto
      also have "... = A $$ (i,j) gmod D" using 2[OF xn] j_not_x i j by auto
      also have "... = ?rhs $$ (i,j)" using i j j_not_x \<open>D > 0\<close>        
        using False True dim_col_mat(1) dim_row_mat(1) index_mat(1) list.set_intros(2) old.prod.case
        by auto
      finally show ?thesis .
    qed
  qed
  next
      case False
      show ?thesis using 2 i j xn 
        by (smt False dim_col_mat(1) dim_row_mat(1) index_mat(1) insert_iff list.set(2) prod.simps(2))
    qed   
  qed  
  finally show ?case using 1 by simp
qed




lemma reduce_row_mod_D_abs:
  assumes A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "\<forall>j\<in>set xs. j<n"
    and d: "distinct xs" and "m\<ge>n"
    and "D > 0" 
  shows "reduce_row_mod_D_abs A a xs D m = Matrix.mat (dim_row A) (dim_col A)
             (\<lambda>(i,k). if i = a \<and> k \<in> set xs then if k = 0 \<and> D dvd A$$(i,k)
              then D else A$$(i,k) gmod D else A$$(i,k))"
  using assms
proof (induct A a xs D m arbitrary: A' rule: reduce_row_mod_D_abs.induct)
  case (1 A a D m)
  then show ?case by force
next
  case (2 A a x xs D m)
  let ?reduce_xs = "(reduce_element_mod_D_abs A a x D m)"
  have 1: "reduce_row_mod_D_abs A a (x # xs) D m 
    = reduce_row_mod_D_abs ?reduce_xs a xs D m" by simp
  have 2: "reduce_element_mod_D_abs A a j D m = Matrix.mat (dim_row A) (dim_col A)
  (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 \<and> D dvd A$$(i,k) then D 
    else A$$(i,k) gmod D else A$$(i,k))" if "j<n" for j
    by (rule reduce_element_mod_D, insert "2.prems" that, auto)
  have "reduce_row_mod_D_abs ?reduce_xs a xs D m =
    Matrix.mat (dim_row ?reduce_xs) (dim_col ?reduce_xs) (\<lambda>(i,k). if i = a \<and> k \<in> set xs then 
    if k=0 \<and> D dvd ?reduce_xs $$ (i, k) then D
    else ?reduce_xs $$ (i, k) gmod D else ?reduce_xs $$ (i, k))"
  proof (rule "2.hyps")
    let ?A' = "mat_of_rows n [Matrix.row (reduce_element_mod_D_abs A a x D m) i. i \<leftarrow> [0..<m]]"
    show "reduce_element_mod_D_abs A a x D m = ?A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
      by (rule reduce_element_mod_D_append, insert "2.prems", auto)
  qed (insert "2.prems", auto)
  also have "... = Matrix.mat (dim_row A) (dim_col A)
            (\<lambda>(i,k). if i = a \<and> k \<in> set (x # xs) then if k = 0 \<and> D dvd A$$(i,k)
            then D else A$$(i,k) gmod D else A$$(i,k))" (is "?lhs = ?rhs")
  proof (rule eq_matI) 
    show "dim_row ?lhs = dim_row ?rhs" and "dim_col ?lhs = dim_col ?rhs" by auto
    fix i j assume i: "i<dim_row ?rhs" and j: "j < dim_col ?rhs"
    have jn: "j<n" using j "2.prems" by (simp add: append_rows_def)
    have xn: "x < n" by (simp add: "2.prems"(4))
    show "?lhs $$ (i,j) = ?rhs $$ (i,j)"
    proof (cases "i=a \<and> j \<in> set xs")
      case True note ia_jxs = True
      have j_not_x: "j\<noteq>x"
        using "2.prems"(5) True by auto
      show ?thesis
      proof (cases "j=0 \<and> D dvd ?reduce_xs $$(i,j)")
        case True
        have "?lhs $$ (i,j) = D"
          using True i j ia_jxs by auto
        also have "... = ?rhs $$ (i,j)" using i j j_not_x 
          by (smt "2" calculation dim_col_mat(1) dim_row_mat(1) index_mat(1) insert_iff list.set(2) prod.simps(2) xn)
        finally show ?thesis .
      next
        case False 
      have "?lhs $$ (i,j) = ?reduce_xs $$ (i, j) gmod D"
        using True False i j by auto
      also have "... = A $$ (i,j) gmod D" using 2[OF xn] j_not_x i j by auto
      also have "... = ?rhs $$ (i,j)" using i j j_not_x \<open>D > 0\<close>  
        using "2" False True dim_col_mat(1) dim_row_mat(1) index_mat(1) list.set_intros(2) 
          old.prod.case xn by auto     
      finally show ?thesis .
    qed  
  next
      case False
      show ?thesis using 2 i j xn 
        by (smt False dim_col_mat(1) dim_row_mat(1) index_mat(1) insert_iff list.set(2) prod.simps(2))
    qed   
  qed  
  finally show ?case using 1 by simp
qed
end


text \<open>Now, we prove some transfer rules to connect B\'ezout matrices in HOL Analysis and JNF\<close>
(*Connecting Bezout Matrix in HOL Analysis (thm bezout_matrix_def) and JNF (thm bezout_matrix_JNF_def)*)
lemma HMA_bezout_matrix[transfer_rule]:
  shows "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: {bezout_ring} ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) 
  ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow> 'm \<Rightarrow> _) ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow> 'm \<Rightarrow> _) 
  ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow> 'n \<Rightarrow> _) ===> (=) ===> (Mod_Type_Connect.HMA_M)) 
  (bezout_matrix_JNF) (bezout_matrix)" 
proof (intro rel_funI, goal_cases)
  case (1 A A' a a' b b' j j' bezout bezout')
  note HMA_AA'[transfer_rule] = "1"(1)
  note HMI_aa'[transfer_rule] = "1"(2)
  note HMI_bb'[transfer_rule] = "1"(3)
  note HMI_jj'[transfer_rule] = "1"(4)
  note eq_bezout'[transfer_rule] = "1"(5)
  show ?case unfolding Mod_Type_Connect.HMA_M_def Mod_Type_Connect.from_hma\<^sub>m_def 
  proof (rule eq_matI) 
    let ?A = "Matrix.mat CARD('m) CARD('m) (\<lambda>(i, j). bezout_matrix A' a' b' j' bezout' 
        $h mod_type_class.from_nat i $h mod_type_class.from_nat j)"
    show "dim_row (bezout_matrix_JNF A a b j bezout) = dim_row ?A"
      and "dim_col (bezout_matrix_JNF A a b j bezout) = dim_col ?A"
      using Mod_Type_Connect.dim_row_transfer_rule[OF HMA_AA']
      unfolding bezout_matrix_JNF_def by auto  
    fix i ja assume i: "i < dim_row ?A" and ja: "ja < dim_col ?A"
    let ?i = "mod_type_class.from_nat i :: 'm"
    let ?ja = "mod_type_class.from_nat ja :: 'm"    
    have i_A: "i < dim_row A"
      using HMA_AA' Mod_Type_Connect.dim_row_transfer_rule i by fastforce
    have ja_A: "ja < dim_row A"
      using Mod_Type_Connect.dim_row_transfer_rule[OF HMA_AA'] ja by fastforce
    have HMA_I_ii'[transfer_rule]: "Mod_Type_Connect.HMA_I i ?i"
      unfolding Mod_Type_Connect.HMA_I_def using from_nat_not_eq i by auto
    have HMA_I_ja'[transfer_rule]: "Mod_Type_Connect.HMA_I ja ?ja"
      unfolding Mod_Type_Connect.HMA_I_def using from_nat_not_eq ja by auto
    have Aaj: "A' $h a' $h j' = A $$ (a,j)" unfolding index_hma_def[symmetric] by (transfer, simp)
    have Abj: "A' $h b' $h j' = A $$ (b, j)" unfolding index_hma_def[symmetric] by (transfer, simp) 
    have "?A $$ (i, ja) = bezout_matrix A' a' b' j' bezout' $h ?i $h ?ja" using i ja by auto
    also have "... = (let (p, q, u, v, d) = bezout' (A' $h a' $h j') (A' $h b' $h j')
            in if ?i = a' \<and> ?ja = a' then p else if ?i = a' \<and> ?ja = b' then q else if ?i = b' \<and> ?ja = a' 
            then u else if ?i = b' \<and> ?ja = b' then v else if ?i = ?ja then 1 else 0)" 
      unfolding bezout_matrix_def by auto
    also have "... =  (let 
        (p, q, u, v, d) = bezout (A $$ (a, j)) (A $$ (b, j)) 
       in
         if i = a \<and> ja = a then p else
         if i = a \<and> ja = b then q else
         if i = b \<and> ja = a then u else
         if i = b \<and> ja = b then v else
         if i = ja then 1 else 0)" unfolding eq_bezout' Aaj Abj by (transfer, simp)
    also have "... = bezout_matrix_JNF A a b j bezout $$ (i,ja)"
      unfolding bezout_matrix_JNF_def using i_A ja_A by auto
    finally show "bezout_matrix_JNF A a b j bezout $$ (i, ja) = ?A $$ (i, ja)" ..
  qed
qed

(*thm invertible_bezout_matrix must be transferred from HOL Analysis to JNF*)

context
begin

private lemma invertible_bezout_matrix_JNF_mod_type:
  fixes A::"'a::{bezout_ring_div} mat"
  assumes "A \<in> carrier_mat CARD('m::mod_type) CARD('n::mod_type)"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b" and b: "b<CARD('m)" and j: "j<CARD('n)"
  and aj: "A $$ (a, j) \<noteq> 0"
shows "invertible_mat (bezout_matrix_JNF A a b j bezout)" 
proof -
  define A' where "A' = (Mod_Type_Connect.to_hma\<^sub>m A :: 'a ^'n :: mod_type ^'m :: mod_type)"
  define a' where "a' = (Mod_Type.from_nat a :: 'm)"
  define b' where "b' = (Mod_Type.from_nat b :: 'm)"
  define j' where "j' = (Mod_Type.from_nat j :: 'n)"
  have AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'"
    unfolding Mod_Type_Connect.HMA_M_def using assms A'_def by auto
  have aa'[transfer_rule]: "Mod_Type_Connect.HMA_I a a'"
    unfolding Mod_Type_Connect.HMA_I_def a'_def using assms
    using from_nat_not_eq order.strict_trans by blast
  have bb'[transfer_rule]: "Mod_Type_Connect.HMA_I b b'"
    unfolding Mod_Type_Connect.HMA_I_def b'_def using assms
    using from_nat_not_eq order.strict_trans by blast
  have jj'[transfer_rule]: "Mod_Type_Connect.HMA_I j j'"
    unfolding Mod_Type_Connect.HMA_I_def j'_def using assms
    using from_nat_not_eq order.strict_trans by blast
  have [transfer_rule]: "bezout = bezout" ..
  have [transfer_rule]: "Mod_Type_Connect.HMA_M (bezout_matrix_JNF A a b j bezout) 
      (bezout_matrix A' a' b' j' bezout)"
    by transfer_prover
  have "invertible (bezout_matrix A' a' b' j' bezout)"
  proof (rule invertible_bezout_matrix[OF ib])
    show "a' < b'" using a_less_b by (simp add: a'_def b b'_def from_nat_mono)
    show "A' $h a' $h j' \<noteq> 0" unfolding index_hma_def[symmetric] using aj by (transfer, simp)
  qed
  thus ?thesis by (transfer, simp)
qed 

private lemma invertible_bezout_matrix_JNF_nontriv_mod_ring:
  fixes A::"'a::{bezout_ring_div} mat"
  assumes "A \<in> carrier_mat CARD('m::nontriv mod_ring) CARD('n::nontriv mod_ring)"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b" and b: "b<CARD('m)" and j: "j<CARD('n)"
  and aj: "A $$ (a, j) \<noteq> 0"
shows "invertible_mat (bezout_matrix_JNF A a b j bezout)" 
  using assms invertible_bezout_matrix_JNF_mod_type by (smt CARD_mod_ring) 


(*We internalize both sort constraints in one step*)
lemmas invertible_bezout_matrix_JNF_internalized = 
  invertible_bezout_matrix_JNF_nontriv_mod_ring[unfolded CARD_mod_ring, 
      internalize_sort "'m::nontriv", internalize_sort "'c::nontriv"]

context
  fixes m::nat and n::nat
  assumes local_typedef1: "\<exists>(Rep :: ('b \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<m :: int}"
  assumes local_typedef2: "\<exists>(Rep :: ('c \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<n :: int}"
  and m: "m>1"
  and n: "n>1"
begin

lemma type_to_set1:
  shows "class.nontriv TYPE('b)" (is ?a) and "m=CARD('b)" (is ?b)
proof -
  from local_typedef1 obtain Rep::"('b \<Rightarrow> int)" and Abs 
    where t: "type_definition Rep Abs {0..<m :: int}" by auto
  have "card (UNIV :: 'b set) = card {0..<m}" using t type_definition.card by fastforce
  also have "... = m" by auto
  finally show ?b ..
  then show ?a unfolding class.nontriv_def using m by auto
qed

lemma type_to_set2:
  shows "class.nontriv TYPE('c)" (is ?a) and "n=CARD('c)" (is ?b)
proof -
  from local_typedef2 obtain Rep::"('c \<Rightarrow> int)" and Abs 
    where t: "type_definition Rep Abs {0..<n :: int}" by blast
  have "card (UNIV :: 'c set) = card {0..<n}" using t type_definition.card by force
  also have "... = n" by auto
  finally show ?b ..
  then show ?a unfolding class.nontriv_def using n by auto
qed


lemma invertible_bezout_matrix_JNF_nontriv_mod_ring_aux:
  fixes A::"'a::{bezout_ring_div} mat"
  assumes "A \<in> carrier_mat m n"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b" and b: "b<m" and j: "j<n"
  and aj: "A $$ (a, j) \<noteq> 0"
shows "invertible_mat (bezout_matrix_JNF A a b j bezout)" 
  using invertible_bezout_matrix_JNF_internalized[OF type_to_set2(1) type_to_set(1), where ?'aa = 'b]
  using assms 
  using type_to_set1(2) type_to_set2(2) local_typedef1 m by blast
end


(*Canceling the first local type definitions*)
context
begin

(*Canceling the first*)
private lemma invertible_bezout_matrix_JNF_cancelled_first:
"\<exists>Rep Abs. type_definition Rep Abs {0..<int n} \<Longrightarrow> {0..<int m} \<noteq> {} \<Longrightarrow>
1 < m \<Longrightarrow> 1 < n \<Longrightarrow>
(A::'a::bezout_ring_div mat) \<in> carrier_mat m n \<Longrightarrow> is_bezout_ext bezout 
\<Longrightarrow> a < b \<Longrightarrow> b < m \<Longrightarrow> j < n \<Longrightarrow> A $$ (a, j) \<noteq> 0 \<Longrightarrow> invertible_mat (bezout_matrix_JNF A a b j bezout)"
  using invertible_bezout_matrix_JNF_nontriv_mod_ring_aux[cancel_type_definition] by blast

(*Canceling the second*)
private lemma invertible_bezout_matrix_JNF_cancelled_both:
"{0..<int n} \<noteq> {} \<Longrightarrow> {0..<int m} \<noteq> {} \<Longrightarrow> 1 < m \<Longrightarrow> 1 < n \<Longrightarrow>
1 < m \<Longrightarrow> 1 < n \<Longrightarrow>
(A::'a::bezout_ring_div mat) \<in> carrier_mat m n \<Longrightarrow> is_bezout_ext bezout 
\<Longrightarrow> a < b \<Longrightarrow> b < m \<Longrightarrow> j < n \<Longrightarrow> A $$ (a, j) \<noteq> 0 \<Longrightarrow> invertible_mat (bezout_matrix_JNF A a b j bezout)"
  using invertible_bezout_matrix_JNF_cancelled_first[cancel_type_definition] by blast

(*The final result in JNF*)
lemma invertible_bezout_matrix_JNF':
  fixes A::"'a::{bezout_ring_div} mat"
  assumes "A \<in> carrier_mat m n"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b" and b: "b<m" and j: "j<n" 
  and "n>1" (* Required from the mod_type restrictions*)
  and aj: "A $$ (a, j) \<noteq> 0"
shows "invertible_mat (bezout_matrix_JNF A a b j bezout)" 
  using invertible_bezout_matrix_JNF_cancelled_both assms by auto

(*Trick: we want to get rid out the "n>1" assumption, which has appeared since CARD('m::mod_type)>1.
Given an mx1 matrix, we just append another column and the bezout_matrix is the same, so it will
also be invertible by the previous transfered theorem
*)
lemma invertible_bezout_matrix_JNF_n1:
  fixes A::"'a::{bezout_ring_div} mat"
  assumes A: "A \<in> carrier_mat m n"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b" and b: "b<m" and j: "j<n" 
  and n1: "n=1" (* Required from the mod_type restrictions*)
  and aj: "A $$ (a, j) \<noteq> 0"
shows "invertible_mat (bezout_matrix_JNF A a b j bezout)" 
proof -
  let ?A = "A @\<^sub>c (0\<^sub>m m n)"
  have "(A @\<^sub>c 0\<^sub>m m n) $$ (a, j) =  (if j < dim_col A then A $$ (a, j) else (0\<^sub>m m n) $$ (a, j - n))"     
    by (rule append_cols_nth[OF A], insert assms, auto)
  also have "... = A $$ (a,j)" using assms by auto
  finally have Aaj: "(A @\<^sub>c 0\<^sub>m m n) $$ (a, j) =  A $$ (a,j)" .
  have "(A @\<^sub>c 0\<^sub>m m n) $$ (b, j) =  (if j < dim_col A then A $$ (b, j) else (0\<^sub>m m n) $$ (b, j - n))"     
    by (rule append_cols_nth[OF A], insert assms, auto)
  also have "... = A $$ (b,j)" using assms by auto
  finally have Abj: "(A @\<^sub>c 0\<^sub>m m n) $$ (b, j) = A $$ (b, j)" .
  have dr: "dim_row A = dim_row ?A"  by (simp add: append_cols_def)
  have dc: "dim_col ?A = 2"
    by (metis Suc_1 append_cols_def A n1 carrier_matD(2) index_mat_four_block(3) 
        index_zero_mat(3) plus_1_eq_Suc)
  have bz_eq: "bezout_matrix_JNF A a b j bezout = bezout_matrix_JNF ?A a b j bezout"
    unfolding bezout_matrix_JNF_def Aaj Abj dr by auto
  have "invertible_mat (bezout_matrix_JNF ?A a b j bezout)"
    by (rule invertible_bezout_matrix_JNF', insert assms Aaj Abj dr dc, auto)
  thus ?thesis using bz_eq by simp
qed

(*The final result in JNF without requiring n>1*)
corollary invertible_bezout_matrix_JNF:
  fixes A::"'a::{bezout_ring_div} mat"
  assumes "A \<in> carrier_mat m n"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b" and b: "b<m" and j: "j<n" 
  and aj: "A $$ (a, j) \<noteq> 0"
shows "invertible_mat (bezout_matrix_JNF A a b j bezout)" 
  using invertible_bezout_matrix_JNF_n1 invertible_bezout_matrix_JNF' assms
  by (metis One_nat_def gr_implies_not0 less_Suc0 not_less_iff_gr_or_eq)

end
end

text \<open>We continue with the soundness of the algorithm\<close>

lemma bezout_matrix_JNF_mult_eq:
  assumes A': "A' \<in> carrier_mat m n" and a: "a\<le>m"  and b: "b\<le>m" and ab: "a \<noteq> b" 
  and A_def: "A = A' @\<^sub>r B" and B: "B \<in> carrier_mat n n"
  assumes pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,j)) (A$$(b,j))"
  shows "Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(b,k))
                   else if i = b then u * A$$(a,k) + v * A$$(b,k)
                   else A$$(i,k)
            ) = (bezout_matrix_JNF A a b j euclid_ext2) * A" (is "?A = ?BM * A")
proof (rule eq_matI) 
  have A: "A \<in> carrier_mat (m+n) n" using A_def A' B by simp
  hence A_carrier: "?A \<in> carrier_mat (m+n) n" by auto  
  show dr: "dim_row ?A = dim_row (?BM * A)" and dc: "dim_col ?A = dim_col (?BM * A)"
    unfolding bezout_matrix_JNF_def by auto
  fix i ja assume i: "i < dim_row  (?BM * A)" and ja: "ja < dim_col (?BM * A)"
  let ?f = "\<lambda>ia. (bezout_matrix_JNF A a b j euclid_ext2) $$ (i,ia) * A $$ (ia,ja)"
  have dv: "dim_vec (col A ja) = m+n" using A by auto
  have i_dr: "i<dim_row A" using i A unfolding bezout_matrix_JNF_def by auto
  have a_dr: "a<dim_row A" using A a ja by auto
  have b_dr: "b<dim_row A" using A b ja by auto
  show "?A $$ (i,ja) = (?BM * A) $$ (i,ja)"
  proof -
    have "(?BM * A) $$ (i,ja) = Matrix.row ?BM i \<bullet> col A ja"
      by (rule index_mult_mat, insert i ja, auto)
    also have "... = (\<Sum>ia = 0..<dim_vec (col A ja). 
          Matrix.row (bezout_matrix_JNF A a b j euclid_ext2) i $v ia * col A ja $v ia)"
      by (simp add: scalar_prod_def)
    also have "... = (\<Sum>ia = 0..<m+n. ?f ia)"
      by (rule sum.cong, insert A i dr dc, auto) (smt bezout_matrix_JNF_def carrier_matD(1) 
          dim_col_mat(1) index_col index_mult_mat(3) index_row(1) ja)
    also have "... = (\<Sum>ia \<in> ({a,b} \<union> ({0..<m+n} - {a,b})). ?f ia)"
      by (rule sum.cong, insert a a_dr b A ja, auto)
    also have "... = sum ?f {a,b} + sum ?f ({0..<m+n} - {a,b})" 
      by (rule sum.union_disjoint, auto)
    finally have BM_A_ija_eq: "(?BM * A) $$ (i,ja) = sum ?f {a,b} + sum ?f ({0..<m+n} - {a,b})" by auto
    show ?thesis
    proof (cases "i = a")
      case True
      have sum0: "sum ?f ({0..<m+n} - {a,b}) = 0"
      proof (rule sum.neutral, rule)
        fix x assume x: "x \<in> {0..<m + n} - {a, b}"
        hence xm: "x < m+n" by auto
        have x_not_i: "x \<noteq> i" using True x by blast
        have x_dr: "x < dim_row A" using x A by auto
        have "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) = 0"
          unfolding bezout_matrix_JNF_def 
          unfolding index_mat(1)[OF i_dr x_dr] using x_not_i x by auto
        thus "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) * A $$ (x, ja) = 0" by auto
      qed
      have fa: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, a) = p" 
        unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr a_dr] using True pquvd 
        by (auto, metis split_conv)
      have fb: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, b) = q"
        unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr b_dr] using True pquvd ab
        by (auto, metis split_conv)
      have "sum ?f {a,b} + sum ?f ({0..<m+n} - {a,b}) = ?f a + ?f b" using sum0 by (simp add: ab)
      also have "... = p * A $$ (a, ja) + q * A $$ (b, ja)" unfolding fa fb by simp
      also have "... = ?A $$ (i,ja)" using A True dr i ja by auto
      finally show ?thesis using BM_A_ija_eq by simp
    next
      case False note i_not_a = False
      show ?thesis
      proof (cases "i=b")
        case True
        have sum0: "sum ?f ({0..<m+n} - {a,b}) = 0"
        proof (rule sum.neutral, rule)
          fix x assume x: "x \<in> {0..<m + n} - {a, b}"
          hence xm: "x < m+n" by auto
          have x_not_i: "x \<noteq> i" using True x by blast
          have x_dr: "x < dim_row A" using x A by auto
          have "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) = 0"
            unfolding bezout_matrix_JNF_def 
            unfolding index_mat(1)[OF i_dr x_dr] using x_not_i x by auto
          thus "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) * A $$ (x, ja) = 0" by auto
        qed
        have fa: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, a) = u" 
          unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr a_dr] using True i_not_a pquvd 
          by (auto, metis split_conv)
        have fb: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, b) = v"
          unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr b_dr] using True i_not_a pquvd ab
          by (auto, metis split_conv)
        have "sum ?f {a,b} + sum ?f ({0..<m+n} - {a,b}) = ?f a + ?f b" using sum0 by (simp add: ab)
        also have "... = u * A $$ (a, ja) + v * A $$ (b, ja)" unfolding fa fb by simp
        also have "... = ?A $$ (i,ja)" using A True i_not_a dr i ja by auto
        finally show ?thesis using BM_A_ija_eq by simp
      next
        case False note i_not_b = False
        have sum0: "sum ?f ({0..<m+n} - {a,b} - {i}) = 0" 
        proof (rule sum.neutral, rule)
          fix x assume x: "x \<in> {0..<m + n} - {a, b} - {i}"
          hence xm: "x < m+n" by auto
          have x_not_i: "x \<noteq> i" using x by blast
          have x_dr: "x < dim_row A" using x A by auto
          have "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) = 0"
            unfolding bezout_matrix_JNF_def 
            unfolding index_mat(1)[OF i_dr x_dr] using x_not_i x by auto
          thus "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) * A $$ (x, ja) = 0" by auto
        qed
        have fa: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, a) = 0" 
          unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr a_dr] using False i_not_a pquvd 
          by auto
        have fb: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, b) = 0" 
          unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr b_dr] using False i_not_a pquvd 
          by auto
        have "sum ?f ({0..<m+n} - {a,b}) = sum ?f (insert i ({0..<m+n} - {a,b} - {i}))"
          by (rule sum.cong, insert i_dr A i_not_a i_not_b, auto)
        also have "... = ?f i + sum ?f ({0..<m+n} - {a,b} - {i})" by (rule sum.insert, auto)
        also have "... = ?f i" using sum0 by simp
        also have "... = ?A $$ (i,ja)"
          unfolding bezout_matrix_JNF_def using i_not_a i_not_b  A dr i ja by fastforce
        finally show ?thesis unfolding BM_A_ija_eq by (simp add: ab fa fb)
      qed    
    qed
  qed
qed




context proper_mod_operation
begin

lemma reduce_invertible_mat: 
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n" and b: "b<m" and ab: "a \<noteq> b" 
  and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
  and Aaj: "A $$ (a,0) \<noteq> 0"
  and a_less_b: "a < b"
  and mn: "m\<ge>n"
  and D_ge0: "D > 0"
shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m+n) (m+n) \<and> (reduce a b D A) = P * A" (is ?thesis1)
proof -
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(b,0))"
    by (metis prod_cases5)
  let ?A = "Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(b,k))
                   else if i = b then u * A$$(a,k) + v * A$$(b,k)
                   else A$$(i,k)
            )"
  have D: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by auto
  have A: "A \<in> carrier_mat (m+n) n" using A_def A' by simp
  hence A_carrier: "?A \<in> carrier_mat (m+n) n" by auto

  let ?BM = "bezout_matrix_JNF A a b 0 euclid_ext2" 
  have A'_BZ_A: "?A = ?BM * A"
    by (rule bezout_matrix_JNF_mult_eq[OF A' _ _ ab A_def D pquvd], insert a b, auto)  
  have invertible_bezout: "invertible_mat ?BM"
    by (rule invertible_bezout_matrix_JNF[OF A is_bezout_ext_euclid_ext2 a_less_b _ j Aaj],
        insert a_less_b b, auto)      
  have BM: "?BM \<in> carrier_mat (m+n) (m+n)" unfolding bezout_matrix_JNF_def using A by auto

  define xs where "xs = [0..<n]"
  let ?reduce_a = "reduce_row_mod_D ?A a xs D m"
  let ?A' = "mat_of_rows n [Matrix.row ?A i. i \<leftarrow> [0..<m]]"
  have A_A'_D: "?A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  proof (rule matrix_append_rows_eq_if_preserves[OF A_carrier D], rule+)
    fix i j assume i: "i \<in> {m..<m + n}" and j: "j < n"
    have "?A $$ (i,j) = A $$ (i,j)" using i a b A j by auto
    also have "... = (if i < dim_row A' then A' $$(i,j) else (D \<cdot>\<^sub>m (1\<^sub>m n))$$(i-m,j))"
      by (unfold A_def, rule append_rows_nth[OF A' D _ j], insert i, auto)
    also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, j)" using i A' by auto
    finally show "?A $$ (i,j) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, j)" .   
  qed
  have reduce_a_eq: "?reduce_a = Matrix.mat (dim_row ?A) (dim_col ?A) 
    (\<lambda>(i, k). if i = a \<and> k \<in> set xs then if k = 0 then if D dvd ?A$$(i,k) then D
              else ?A $$ (i, k) else ?A $$ (i, k) gmod D else ?A $$ (i, k))"
    by (rule reduce_row_mod_D[OF A_A'_D _ a _], insert xs_def mn D_ge0, auto)  
  have reduce_a: "?reduce_a \<in> carrier_mat (m+n) n"  using reduce_a_eq A by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?reduce_a = P * ?A"
    by (rule reduce_row_mod_D_invertible_mat[OF A_A'_D _ a], insert xs_def mn, auto)    
  from this obtain P where P: "P \<in> carrier_mat (m + n) (m + n)" and inv_P: "invertible_mat P" 
    and reduce_a_PA: "?reduce_a = P * ?A" by blast
  define ys where "ys = [1..<n]"
  let ?reduce_b = "reduce_row_mod_D ?reduce_a b ys D m"
  let ?B' = "mat_of_rows n [Matrix.row ?reduce_a i. i \<leftarrow> [0..<m]]"
  have reduce_a_B'_D: "?reduce_a = ?B' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  proof (rule matrix_append_rows_eq_if_preserves[OF reduce_a D], rule+)
    fix i ja assume i: "i \<in> {m..<m + n}" and ja: "ja < n"
    have i_not_a:"i\<noteq>a" and i_not_b: "i\<noteq>b" using i a b by auto
    have "?reduce_a $$ (i,ja) = ?A $$ (i, ja)"
      unfolding reduce_a_eq using i i_not_a i_not_b ja A by auto      
    also have "... = A $$ (i,ja)"  using i i_not_a i_not_b ja A by auto
    also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)"
      by (smt D append_rows_nth A' A_def atLeastLessThan_iff 
          carrier_matD(1) i ja less_irrefl_nat nat_SN.compat)    
    finally show "?reduce_a $$ (i,ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" .
  qed
  have reduce_b_eq: "?reduce_b = Matrix.mat (dim_row ?reduce_a) (dim_col ?reduce_a) 
    (\<lambda>(i, k). if i = b \<and> k \<in> set ys then if k = 0 then if D dvd ?reduce_a$$(i,k) then D else ?reduce_a $$ (i, k)
      else ?reduce_a $$ (i, k) gmod D else ?reduce_a $$ (i, k))"
    by (rule reduce_row_mod_D[OF reduce_a_B'_D _ b _ _ mn], unfold ys_def, insert D_ge0, auto)
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?reduce_b = P * ?reduce_a"
    by (rule reduce_row_mod_D_invertible_mat[OF reduce_a_B'_D _ b _ mn], insert ys_def, auto)    
  from this obtain Q where Q: "Q \<in> carrier_mat (m + n) (m + n)" and inv_Q: "invertible_mat Q" 
    and reduce_b_Q_reduce: "?reduce_b = Q * ?reduce_a" by blast
  have reduce_b_eq_reduce: "?reduce_b = (reduce a b D A)"
  proof (rule eq_matI)
    show dr_eq: "dim_row ?reduce_b = dim_row (reduce a b D A)" 
      and dc_eq: "dim_col ?reduce_b = dim_col (reduce a b D A)"
      using reduce_preserves_dimensions by auto
    fix i ja assume i: "i<dim_row (reduce a b D A)" and ja: "ja< dim_col (reduce a b D A)"
    have im: "i<m+n" using A i reduce_preserves_dimensions(1) by auto
    have ja_n: "ja<n" using A ja reduce_preserves_dimensions(2) by auto
    show "?reduce_b $$ (i,ja) = (reduce a b D A) $$ (i,ja)"
    proof (cases "(i\<noteq>a \<and> i\<noteq>b)")
      case True
      have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq 
        by (smt True dr_eq dc_eq i index_mat(1) ja prod.simps(2) reduce_row_mod_D_preserves_dimensions)
      also have "... = ?A $$ (i,ja)"
        by (smt A True carrier_matD(2) dim_col_mat(1) dim_row_mat(1) i index_mat(1) ja_n 
            reduce_a_eq reduce_preserves_dimensions(1) split_conv)
      also have "... = A $$ (i,ja)" using A True im ja_n by auto
      also have "... = (reduce a b D A) $$ (i,ja)" unfolding reduce_alt_def_not0[OF Aaj pquvd]
        using im ja_n A True by auto
      finally show ?thesis .      
    next
      case False note a_or_b = False
      show ?thesis
      proof (cases "i=a")
        case True note ia = True
        hence i_not_b: "i\<noteq>b" using ab by auto
        show ?thesis
        proof -
          have ja_in_xs: "ja \<in> set xs"
            unfolding xs_def using True ja_n im a A unfolding set_filter by auto
          have 1: "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq             
            by (smt ab dc_eq dim_row_mat(1) dr_eq i ia index_mat(1) ja prod.simps(2)
                reduce_b_eq reduce_row_mod_D_preserves_dimensions(2))
          show ?thesis 
          proof (cases "ja = 0 \<and> D dvd p*A$$(a,ja) + q*A$$(b,ja)")
            case True
            have "?reduce_a $$ (i,ja) = D"
              unfolding reduce_a_eq using True ab a_or_b i_not_b ja_n im a A ja_in_xs False by auto
            also have "... = (reduce a b D A) $$ (i,ja)"
              unfolding reduce_alt_def_not0[OF Aaj pquvd]
              using True a_or_b i_not_b ja_n im A False                
              by auto 
            finally show ?thesis using 1 by simp
          next
            case False note nc1 = False
            show ?thesis
            proof (cases "ja=0")
              case True
              then show ?thesis
                by (smt (z3) "1" A assms(3) assms(7) dim_col_mat(1) dim_row_mat(1) euclid_ext2_works i ia im index_mat(1)
                    ja ja_in_xs old.prod.case pquvd reduce_gcd reduce_preserves_dimensions reduce_a_eq)
            next
              case False
              have "?reduce_a $$ (i,ja) = ?A $$ (i, ja) gmod D"
                unfolding reduce_a_eq using True ab a_or_b i_not_b ja_n im a A ja_in_xs False by auto
              also have "... = (reduce a b D A) $$ (i,ja)"
                unfolding reduce_alt_def_not0[OF Aaj pquvd] using True a_or_b i_not_b ja_n im A False by auto
              finally show ?thesis using 1 by simp
          qed    
        qed        
      qed
      next
        case False note i_not_a = False
        have i_drb: "i<dim_row ?reduce_b"
          and i_dra: "i<dim_row ?reduce_a"
          and ja_drb: "ja < dim_col ?reduce_b"
          and ja_dra: "ja < dim_col ?reduce_a" using reduce_carrier[OF A] i ja A dr_eq dc_eq by auto
          have ib: "i=b" using False a_or_b by auto
        show ?thesis
        proof (cases "ja \<in> set  ys")
          case True note ja_in_ys = True     
          hence ja_not0: "ja \<noteq> 0" unfolding ys_def by auto
          have "?reduce_b $$ (i,ja) = (if ja = 0 then if D dvd ?reduce_a$$(i,ja) then D
                else ?reduce_a $$ (i, ja) else ?reduce_a $$ (i, ja) gmod D)"
            unfolding reduce_b_eq using i_not_a True  ja ja_in_ys 
            by (smt i_dra ja_dra a_or_b index_mat(1) prod.simps(2))
          also have "... = (if ja = 0 then if D dvd ?reduce_a$$(i,ja) then D else ?A $$ (i, ja) else ?A $$ (i, ja) gmod D)"
            unfolding reduce_a_eq using True ab a_or_b ib False ja_n im a A ja_in_ys by auto
          also have "... = (reduce a b D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using True ja_not0 False a_or_b ib ja_n im A 
            using i_not_a by auto                
          finally show ?thesis .
        next
          case False
          hence ja0:"ja = 0" using ja_n unfolding ys_def by auto
          have rw0: "u * A $$ (a, ja) + v * A $$ (b, ja) = 0"
            unfolding euclid_ext2_works[OF pquvd[symmetric]] ja0
            by (smt euclid_ext2_works[OF pquvd[symmetric]] more_arith_simps(11) mult.commute mult_minus_left)
          have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq             
            by (smt False a_or_b dc_eq dim_row_mat(1) dr_eq i index_mat(1) ja 
                prod.simps(2) reduce_b_eq reduce_row_mod_D_preserves_dimensions(2))
          also have "... = ?A $$ (i, ja)"
            unfolding reduce_a_eq using False ab a_or_b i_not_a ja_n im a A  by auto
          also have "... = u * A $$ (a, ja) + v * A $$ (b, ja)" 
            by (smt (verit, ccfv_SIG) A \<open>ja = 0\<close> assms(3) assms(5) carrier_matD(2) i ib index_mat(1)
                old.prod.case reduce_preserves_dimensions(1))  
          also have "... = (reduce a b D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd] 
            using False a_or_b i_not_a ja_n im A ja0 by auto
          finally show ?thesis .
        qed
      qed      
    qed    
  qed
  have inv_QPBM: "invertible_mat (Q * P * ?BM)"
    by (meson BM P Q inv_P inv_Q invertible_bezout invertible_mult_JNF mult_carrier_mat)
  moreover have "(Q*P*?BM) \<in> carrier_mat (m + n) (m + n)" using BM P Q by auto
  moreover have "(reduce a b D A) = (Q*P*?BM) * A"
  proof -
    have "?BM * A = ?A" using A'_BZ_A by auto
    hence "P * (?BM * A) = ?reduce_a" using reduce_a_PA by auto
    hence "Q * (P * (?BM * A)) = ?reduce_b" using reduce_b_Q_reduce by auto
    thus ?thesis using reduce_b_eq_reduce
      by (smt A A'_BZ_A A_carrier BM P Q assoc_mult_mat mn mult_carrier_mat reduce_a_PA)  
  qed
  ultimately show ?thesis by blast
qed


lemma reduce_abs_invertible_mat: 
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n" and b: "b<m" and ab: "a \<noteq> b" 
  and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
  and Aaj: "A $$ (a,0) \<noteq> 0"
  and a_less_b: "a < b"
  and mn: "m\<ge>n"
  and D_ge0: "D > 0"
shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m+n) (m+n) \<and> (reduce_abs a b D A) = P * A" (is ?thesis1)
proof -
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(b,0))"
    by (metis prod_cases5)
  let ?A = "Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(b,k))
                   else if i = b then u * A$$(a,k) + v * A$$(b,k)
                   else A$$(i,k)
            )"
  have D: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by auto
  have A: "A \<in> carrier_mat (m+n) n" using A_def A' by simp
  hence A_carrier: "?A \<in> carrier_mat (m+n) n" by auto

  let ?BM = "bezout_matrix_JNF A a b 0 euclid_ext2" 
  have A'_BZ_A: "?A = ?BM * A"
    by (rule bezout_matrix_JNF_mult_eq[OF A' _ _ ab A_def D pquvd], insert a b, auto)  
  have invertible_bezout: "invertible_mat ?BM"
    by (rule invertible_bezout_matrix_JNF[OF A is_bezout_ext_euclid_ext2 a_less_b _ j Aaj],
        insert a_less_b b, auto)      
  have BM: "?BM \<in> carrier_mat (m+n) (m+n)" unfolding bezout_matrix_JNF_def using A by auto

  define xs where "xs = filter (\<lambda>i. abs (?A $$ (a,i)) > D) [0..<n]"
  let ?reduce_a = "reduce_row_mod_D_abs ?A a xs D m"
  let ?A' = "mat_of_rows n [Matrix.row ?A i. i \<leftarrow> [0..<m]]"
  have A_A'_D: "?A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  proof (rule matrix_append_rows_eq_if_preserves[OF A_carrier D], rule+)
    fix i j assume i: "i \<in> {m..<m + n}" and j: "j < n"
    have "?A $$ (i,j) = A $$ (i,j)" using i a b A j by auto
    also have "... = (if i < dim_row A' then A' $$(i,j) else (D \<cdot>\<^sub>m (1\<^sub>m n))$$(i-m,j))"
      by (unfold A_def, rule append_rows_nth[OF A' D _ j], insert i, auto)
    also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, j)" using i A' by auto
    finally show "?A $$ (i,j) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, j)" .   
  qed
  have reduce_a_eq: "?reduce_a = Matrix.mat (dim_row ?A) (dim_col ?A) 
    (\<lambda>(i, k). if i = a \<and> k \<in> set xs then 
      if k = 0 \<and> D dvd ?A$$(i,k) then D else ?A $$ (i, k) gmod D else ?A $$ (i, k))"
    by (rule reduce_row_mod_D_abs[OF A_A'_D _ a _], insert xs_def mn D_ge0, auto)  
  have reduce_a: "?reduce_a \<in> carrier_mat (m+n) n"  using reduce_a_eq A by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?reduce_a = P * ?A"
    by (rule reduce_row_mod_D_abs_invertible_mat[OF A_A'_D _ a], insert xs_def mn, auto)    
  from this obtain P where P: "P \<in> carrier_mat (m + n) (m + n)" and inv_P: "invertible_mat P" 
    and reduce_a_PA: "?reduce_a = P * ?A" by blast
  define ys where "ys = filter (\<lambda>i. abs (?A $$ (b,i)) > D) [0..<n]"
  let ?reduce_b = "reduce_row_mod_D_abs ?reduce_a b ys D m"
  let ?B' = "mat_of_rows n [Matrix.row ?reduce_a i. i \<leftarrow> [0..<m]]"
  have reduce_a_B'_D: "?reduce_a = ?B' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  proof (rule matrix_append_rows_eq_if_preserves[OF reduce_a D], rule+)
    fix i ja assume i: "i \<in> {m..<m + n}" and ja: "ja < n"
    have i_not_a:"i\<noteq>a" and i_not_b: "i\<noteq>b" using i a b by auto
    have "?reduce_a $$ (i,ja) = ?A $$ (i, ja)"
      unfolding reduce_a_eq using i i_not_a i_not_b ja A by auto      
    also have "... = A $$ (i,ja)"  using i i_not_a i_not_b ja A by auto
    also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)"
      by (smt D append_rows_nth A' A_def atLeastLessThan_iff 
          carrier_matD(1) i ja less_irrefl_nat nat_SN.compat)    
    finally show "?reduce_a $$ (i,ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" .
  qed
  have reduce_b_eq: "?reduce_b = Matrix.mat (dim_row ?reduce_a) (dim_col ?reduce_a) 
    (\<lambda>(i, k). if i = b \<and> k \<in> set ys then if k = 0 \<and> D dvd ?reduce_a$$(i,k) then D 
      else ?reduce_a $$ (i, k) gmod D else ?reduce_a $$ (i, k))"
    by (rule reduce_row_mod_D_abs[OF reduce_a_B'_D _ b _ _ mn], unfold ys_def, insert D_ge0, auto)
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?reduce_b = P * ?reduce_a"
    by (rule reduce_row_mod_D_abs_invertible_mat[OF reduce_a_B'_D _ b _ mn], insert ys_def, auto)    
  from this obtain Q where Q: "Q \<in> carrier_mat (m + n) (m + n)" and inv_Q: "invertible_mat Q" 
    and reduce_b_Q_reduce: "?reduce_b = Q * ?reduce_a" by blast
  have reduce_b_eq_reduce: "?reduce_b = (reduce_abs a b D A)"
  proof (rule eq_matI)
    show dr_eq: "dim_row ?reduce_b = dim_row (reduce_abs a b D A)" 
      and dc_eq: "dim_col ?reduce_b = dim_col (reduce_abs a b D A)"
      using reduce_preserves_dimensions by auto
    fix i ja assume i: "i<dim_row (reduce_abs a b D A)" and ja: "ja< dim_col (reduce_abs a b D A)"
    have im: "i<m+n" using A i reduce_preserves_dimensions(3) by auto
    have ja_n: "ja<n" using A ja reduce_preserves_dimensions(4) by auto
    show "?reduce_b $$ (i,ja) = (reduce_abs a b D A) $$ (i,ja)"
    proof (cases "(i\<noteq>a \<and> i\<noteq>b)")
      case True
      have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq 
        by (smt True dr_eq dc_eq i index_mat(1) ja prod.simps(2) reduce_row_mod_D_preserves_dimensions_abs)
      also have "... = ?A $$ (i,ja)"
        by (smt A True carrier_matD(2) dim_col_mat(1) dim_row_mat(1) i index_mat(1) ja_n 
            reduce_a_eq reduce_preserves_dimensions(3) split_conv)
      also have "... = A $$ (i,ja)" using A True im ja_n by auto
      also have "... = (reduce_abs a b D A) $$ (i,ja)" unfolding reduce_alt_def_not0[OF Aaj pquvd]
        using im ja_n A True by auto
      finally show ?thesis .      
    next
      case False note a_or_b = False
      show ?thesis
      proof (cases "i=a")
        case True note ia = True
        hence i_not_b: "i\<noteq>b" using ab by auto
        show ?thesis
        proof (cases "abs((p*A$$(a,ja) + q*A$$(b,ja))) > D")
          case True note ge_D = True
          have ja_in_xs: "ja \<in> set xs"
            unfolding xs_def using True ja_n im a A unfolding set_filter by auto
          have 1: "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq             
            by (smt ab dc_eq dim_row_mat(1) dr_eq i ia index_mat(1) ja prod.simps(2)
                reduce_b_eq reduce_row_mod_D_preserves_dimensions_abs(2))
          show ?thesis 
          proof (cases "ja = 0 \<and> D dvd p*A$$(a,ja) + q*A$$(b,ja)")
            case True
            have "?reduce_a $$ (i,ja) = D"
              unfolding reduce_a_eq using True ab a_or_b i_not_b ja_n im a A ja_in_xs False by auto
            also have "... = (reduce_abs a b D A) $$ (i,ja)"
              unfolding reduce_alt_def_not0[OF Aaj pquvd]
              using True a_or_b i_not_b ja_n im A False ge_D               
              by auto 
            finally show ?thesis using 1 by simp
          next
            case False
            have "?reduce_a $$ (i,ja) = ?A $$ (i, ja) gmod D"
              unfolding reduce_a_eq using True ab a_or_b i_not_b ja_n im a A ja_in_xs False by auto
            also have "... = (reduce_abs a b D A) $$ (i,ja)"
              unfolding reduce_alt_def_not0[OF Aaj pquvd] using True a_or_b i_not_b ja_n im A False by auto
            finally show ?thesis using 1 by simp
          qed        
        next
          case False
          have ja_in_xs: "ja \<notin> set xs"
            unfolding xs_def using False ja_n im a A unfolding set_filter by auto
          have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq             
            by (smt ab dc_eq dim_row_mat(1) dr_eq i ia index_mat(1) ja prod.simps(2)
                reduce_b_eq reduce_row_mod_D_preserves_dimensions_abs(2))
          also have "... = ?A $$ (i, ja)"
            unfolding reduce_a_eq using False ab a_or_b i_not_b ja_n im a A ja_in_xs by auto
          also have "... = (reduce_abs a b D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using False a_or_b i_not_b ja_n im A by auto
          finally show ?thesis .
        qed      
      next
        case False note i_not_a = False
        have i_drb: "i<dim_row ?reduce_b"
          and i_dra: "i<dim_row ?reduce_a"
          and ja_drb: "ja < dim_col ?reduce_b"
          and ja_dra: "ja < dim_col ?reduce_a" using reduce_carrier[OF A] i ja A dr_eq dc_eq by auto
          have ib: "i=b" using False a_or_b by auto
        show ?thesis
        proof (cases "abs((u*A$$(a,ja) + v * A$$(b,ja))) > D")
          case True note ge_D = True
          have ja_in_ys: "ja \<in> set ys"
            unfolding ys_def using True False ib ja_n im a b A unfolding set_filter by auto
          have "?reduce_b $$ (i,ja) = (if ja = 0 \<and> D dvd ?reduce_a$$(i,ja) then D else ?reduce_a $$ (i, ja) gmod D)"          
            unfolding reduce_b_eq using i_not_a True  ja ja_in_ys 
            by (smt i_dra ja_dra a_or_b index_mat(1) prod.simps(2))
          also have "... = (if ja = 0 \<and> D dvd ?reduce_a$$(i,ja) then D else ?A $$ (i, ja) gmod D)"   
            unfolding reduce_a_eq using True ab a_or_b ib False ja_n im a A ja_in_ys by auto
          also have "... = (reduce_abs a b D A) $$ (i,ja)"
          proof (cases "ja = 0 \<and> D dvd ?reduce_a$$(i,ja)")
            case True
            have ja0: "ja=0" using True by auto
            have "u * A $$ (a, ja) + v * A $$ (b, ja) = 0"
              unfolding euclid_ext2_works[OF pquvd[symmetric]] ja0
              by (smt euclid_ext2_works[OF pquvd[symmetric]] more_arith_simps(11) mult.commute mult_minus_left)
            hence abs_0: "abs((u*A$$(a,ja) + v * A$$(b,ja))) = 0" by auto
            show ?thesis using abs_0 D_ge0 ge_D by linarith           
          next
            case False
            then show ?thesis 
              unfolding reduce_alt_def_not0[OF Aaj pquvd] using True ge_D False a_or_b ib ja_n im A 
              using i_not_a by auto           
          qed              
          finally show ?thesis .
        next
          case False
          have ja_in_ys: "ja \<notin> set ys"
            unfolding ys_def using i_not_a False ib ja_n im a b A unfolding set_filter by auto
          have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq                         
            using i_dra ja_dra ja_in_ys by auto
          also have "... = ?A $$ (i, ja)"
            unfolding reduce_a_eq using False ab a_or_b i_not_a ja_n im a A  by auto
          also have "... = u * A $$ (a, ja) + v * A $$ (b, ja)" 
            unfolding reduce_a_eq using False ab a_or_b i_not_a ja_n im a A ja_in_ys by auto            
          also have "... = (reduce_abs a b D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd] 
            using False a_or_b i_not_a ja_n im A by auto
          finally show ?thesis .
        qed
      qed      
    qed    
  qed
  have inv_QPBM: "invertible_mat (Q * P * ?BM)"
    by (meson BM P Q inv_P inv_Q invertible_bezout invertible_mult_JNF mult_carrier_mat)
  moreover have "(Q*P*?BM) \<in> carrier_mat (m + n) (m + n)" using BM P Q by auto
  moreover have "(reduce_abs a b D A) = (Q*P*?BM) * A"
  proof -
    have "?BM * A = ?A" using A'_BZ_A by auto
    hence "P * (?BM * A) = ?reduce_a" using reduce_a_PA by auto
    hence "Q * (P * (?BM * A)) = ?reduce_b" using reduce_b_Q_reduce by auto
    thus ?thesis using reduce_b_eq_reduce
      by (smt A A'_BZ_A A_carrier BM P Q assoc_mult_mat mn mult_carrier_mat reduce_a_PA)  
  qed
  ultimately show ?thesis by blast
qed




lemma reduce_element_mod_D_case_m':
  assumes A_def: "A = A' @\<^sub>r  B" and B: "B\<in>carrier_mat n n"
  and A': "A' \<in> carrier_mat m n" and a: "a\<le>m" and j: "j<n" 
  and mn: "m>=n" and B1: "B $$ (j, j) = D" and B2: "(\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)"
  and D0: "D > 0" 
  shows "reduce_element_mod_D A a j D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 then if D dvd A$$(i,k) then D
                   else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" (is "_ = ?A")
proof (rule eq_matI)
  have jm: "j<m" using mn j by auto
  have A: "A \<in> carrier_mat (m+n) n" using A_def A' B mn by simp
  fix i ja assume i: "i < dim_row ?A" and ja: "ja < dim_col ?A"
  show "reduce_element_mod_D A a j D m $$ (i, ja) = ?A $$ (i, ja)"
 proof (cases "i=a")
    case False
    have "reduce_element_mod_D A a j D m = (if j = 0 then if D dvd A$$(a,j)
        then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A else A
        else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)"
      unfolding reduce_element_mod_D_def by simp
    also have "... $$ (i,ja) = A $$ (i, ja)" unfolding mat_addrow_def using False ja i by auto     
    also have "... = ?A $$ (i,ja)" using False using i ja by auto
    finally show ?thesis .
  next
    case True note ia = True
    have "reduce_element_mod_D A a j D m 
      = (if j = 0 then if D dvd A$$(a,j) then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A else A
        else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)" 
      unfolding reduce_element_mod_D_def by simp
    also have "... $$ (i,ja) = ?A $$ (i,ja)"
    proof (cases "ja = j")
      case True note ja_j = True
      have "A $$ (j + m, ja) = B $$ (j,ja)"
        by (rule append_rows_nth2[OF A' _ A_def ], insert j ja A B mn, auto)  
      also have "... = D" using True j mn B1 B2 B by auto      
      finally have A_ja_jaD: "A $$ (j + m, ja) = D" .

      show ?thesis
      proof (cases "j=0 \<and> D dvd A$$(a,j)")
        case True         
        have 1: "reduce_element_mod_D A a j D m = addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A "
          using True ia ja_j unfolding reduce_element_mod_D_def by auto
        also have "... $$(i,ja) = (- (A $$ (a, j) gdiv D) + 1) * A $$ (j + m, ja) + A $$ (i, ja)"
          unfolding mat_addrow_def using True ja_j ia
          using A i j by auto
        also have "... = D"
        proof -
          have "A $$ (i, ja) + D * - (A $$ (i, ja) gdiv D) = 0"
            using True ia ja_j using D0 by force
          then show ?thesis
            by (metis A_ja_jaD ab_semigroup_add_class.add_ac(1) add.commute add_right_imp_eq ia int_distrib(2)
                ja_j more_arith_simps(3) mult.commute mult_cancel_right1)
        qed   
        also have "... = ?A $$ (i,ja)" using True ia A i j ja_j by auto
        finally show ?thesis
          using True 1 by auto
      next
        case False
        show ?thesis
        proof (cases "j=0")
          case True
          then show ?thesis 
            using False i ja by auto
        next
          case False
          have "?A $$ (i,ja) = A $$ (i, ja) gmod D" using True ia A i j False by auto
          also have "... = A $$ (i, ja) - ((A $$ (i, ja) gdiv D) * D)"
            by (subst gmod_gdiv[OF D0], auto)
          also have "... =  - (A $$ (a, j) gdiv D) * A $$ (j + m, ja) + A $$ (i, ja)"
            unfolding A_ja_jaD by (simp add: True ia)
          finally show ?thesis 
            using A False True i ia j by auto
      qed
    qed
    next
      case False
      have "A $$ (j + m, ja) = B $$ (j,ja)"
        by (rule append_rows_nth2[OF A' _ A_def ], insert j mn ja A B, auto)
      also have "... = 0" using False using A a mn ja j B2 by force        
      finally have A_am_ja0: "A $$ (j + m, ja) = 0" .
      then show ?thesis using False i ja by fastforce
    qed
    finally show ?thesis .
  qed
next
  show "dim_row (reduce_element_mod_D A a j D m) = dim_row ?A" 
    and "dim_col (reduce_element_mod_D A a j D m) = dim_col ?A"
    using reduce_element_mod_D_def by auto
qed




lemma reduce_element_mod_D_abs_case_m':
  assumes A_def: "A = A' @\<^sub>r  B" and B: "B\<in>carrier_mat n n"
  and A': "A' \<in> carrier_mat m n" and a: "a\<le>m" and j: "j<n" 
  and mn: "m>=n" and B1: "B $$ (j, j) = D" and B2: "(\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)"
  and D0: "D > 0" 
  shows "reduce_element_mod_D_abs A a j D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 \<and> D dvd A$$(i,k) then D else A$$(i,k) gmod D else A$$(i,k))" (is "_ = ?A")
proof (rule eq_matI)
  have jm: "j<m" using mn j by auto
  have A: "A \<in> carrier_mat (m+n) n" using A_def A' B mn by simp
  fix i ja assume i: "i < dim_row ?A" and ja: "ja < dim_col ?A"
  show "reduce_element_mod_D_abs A a j D m $$ (i, ja) = ?A $$ (i, ja)"
 proof (cases "i=a")
    case False
    have "reduce_element_mod_D_abs A a j D m = (if j = 0 \<and> D dvd A$$(a,j)
        then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A
        else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)"
      unfolding reduce_element_mod_D_abs_def by simp
    also have "... $$ (i,ja) = A $$ (i, ja)" unfolding mat_addrow_def using False ja i by auto     
    also have "... = ?A $$ (i,ja)" using False using i ja by auto
    finally show ?thesis .
  next
    case True note ia = True
    have "reduce_element_mod_D_abs A a j D m 
      = (if j = 0 \<and> D dvd A$$(a,j) then addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A
        else addrow (-((A$$(a,j) gdiv D))) a (j + m) A)" 
      unfolding reduce_element_mod_D_abs_def by simp
    also have "... $$ (i,ja) = ?A $$ (i,ja)"
    proof (cases "ja = j")
      case True note ja_j = True
      have "A $$ (j + m, ja) = B $$ (j,ja)"
        by (rule append_rows_nth2[OF A' _ A_def ], insert j ja A B mn, auto)  
      also have "... = D" using True j mn B1 B2 B by auto      
      finally have A_ja_jaD: "A $$ (j + m, ja) = D" .

      show ?thesis
      proof (cases "j=0 \<and> D dvd A$$(a,j)")
        case True         
        have 1: "reduce_element_mod_D_abs A a j D m = addrow (-((A$$(a,j) gdiv D)) + 1) a (j + m) A "
          using True ia ja_j unfolding reduce_element_mod_D_abs_def by auto
        also have "... $$(i,ja) = (- (A $$ (a, j) gdiv D) + 1) * A $$ (j + m, ja) + A $$ (i, ja)"
          unfolding mat_addrow_def using True ja_j ia
          using A i j by auto
        also have "... = D"
        proof -
          have "A $$ (i, ja) + D * - (A $$ (i, ja) gdiv D) = 0"
            using True ia ja_j using D0 by force
          then show ?thesis
            by (metis A_ja_jaD ab_semigroup_add_class.add_ac(1) add.commute add_right_imp_eq ia int_distrib(2)
                ja_j more_arith_simps(3) mult.commute mult_cancel_right1)
        qed   
        also have "... = ?A $$ (i,ja)" using True ia A i j ja_j by auto
        finally show ?thesis
          using True 1 by auto
      next
        case False        
          have "?A $$ (i,ja) = A $$ (i, ja) gmod D" using True ia A i j False by auto
          also have "... = A $$ (i, ja) - ((A $$ (i, ja) gdiv D) * D)"
            by (subst gmod_gdiv[OF D0], auto)
          also have "... =  - (A $$ (a, j) gdiv D) * A $$ (j + m, ja) + A $$ (i, ja)"
            unfolding A_ja_jaD by (simp add: True ia)
          finally show ?thesis 
            using A False True i ia j by auto
        qed    
    next
      case False
      have "A $$ (j + m, ja) = B $$ (j,ja)"
        by (rule append_rows_nth2[OF A' _ A_def ], insert j mn ja A B, auto)
      also have "... = 0" using False using A a mn ja j B2 by force        
      finally have A_am_ja0: "A $$ (j + m, ja) = 0" .
      then show ?thesis using False i ja by fastforce
    qed
    finally show ?thesis .
  qed
next
  show "dim_row (reduce_element_mod_D_abs A a j D m) = dim_row ?A" 
    and "dim_col (reduce_element_mod_D_abs A a j D m) = dim_col ?A"
    using reduce_element_mod_D_abs_def by auto
qed


lemma reduce_row_mod_D_case_m':
  assumes A_def: "A = A' @\<^sub>r B" and "B \<in> carrier_mat n n"
    and A': "A' \<in> carrier_mat m n" and "a < m" 
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)" 
    and d: "distinct xs" and "m\<ge>n"
    and D: "D > 0" 
  shows "reduce_row_mod_D A a xs D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set xs then if k = 0 then if D dvd A$$(i,k) then D
                   else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))"
  using assms
proof (induct A a xs D m arbitrary: A' B rule: reduce_row_mod_D.induct)
  case (1 A a D m)
  then show ?case by force
next
  case (2 A a x xs D m)
  note A_A'B = "2.prems"(1)
  note B = "2.prems"(2)
  note A' = "2.prems"(3)
  note a = "2.prems"(4)
  note j = "2.prems"(5)
  note mn = "2.prems"(7)
  note d = "2.prems"(6)
  let ?reduce_xs = "(reduce_element_mod_D A a x D m)"
  have reduce_xs_carrier: "?reduce_xs \<in> carrier_mat (m + n) n"
    by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) add.right_neutral append_rows_def 
            carrier_matD carrier_mat_triv index_mat_four_block(2,3) index_zero_mat(2,3)
            reduce_element_mod_D_preserves_dimensions)
  have 1: "reduce_row_mod_D A a (x # xs) D m 
    = reduce_row_mod_D ?reduce_xs a xs D m" by simp
  have 2: "reduce_element_mod_D A a j D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 then if D dvd A$$(i,k) 
          then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" if "j\<in>set (x#xs)" for j
    by (rule reduce_element_mod_D_case_m'[OF A_A'B B A'], insert "2.prems" that, auto)
  have "reduce_row_mod_D ?reduce_xs a xs D m =
    Matrix.mat (dim_row ?reduce_xs) (dim_col ?reduce_xs) (\<lambda>(i,k). if i = a \<and> k \<in> set xs 
    then if k = 0 then if D dvd ?reduce_xs $$ (i, k) then D else ?reduce_xs $$ (i, k) else
    ?reduce_xs $$ (i, k) gmod D else ?reduce_xs $$ (i, k))"
  proof (rule "2.hyps"[OF _ B _ a _ _ mn])
    let ?A' = "mat_of_rows n [Matrix.row (reduce_element_mod_D A a x D m) i. i \<leftarrow> [0..<m]]"
    show "reduce_element_mod_D A a x D m = ?A' @\<^sub>r B"
    proof (rule matrix_append_rows_eq_if_preserves[OF reduce_xs_carrier B])
      show " \<forall>i\<in>{m..<m + n}. \<forall>j<n. reduce_element_mod_D A a x D m $$ (i, j) = B $$ (i - m, j) "       
        by (smt A_A'B A' B a Metric_Arith.nnf_simps(7) add_diff_cancel_left' atLeastLessThan_iff
            carrier_matD index_mat_addrow(1) index_row(1) le_add_diff_inverse2 less_diff_conv
            reduce_element_mod_D_def reduce_element_mod_D_preserves_dimensions reduce_xs_carrier
            row_append_rows2)        
    qed
  qed (insert "2.prems", auto simp add: mat_of_rows_def)
  also have "... = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set (x # xs) then if k = 0 then if D dvd A$$(i,k)
          then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" (is "?lhs = ?rhs")
  proof (rule eq_matI) 
    show "dim_row ?lhs = dim_row ?rhs" and "dim_col ?lhs = dim_col ?rhs" by auto
    fix i j assume i: "i<dim_row ?rhs" and j: "j < dim_col ?rhs"
    have jn: "j<n" using j "2.prems" by (simp add: append_rows_def)
    have xn: "x < n" 
      by (simp add: "2.prems"(5))
    show "?lhs $$ (i,j) = ?rhs $$ (i,j)"
    proof (cases "i=a \<and> j \<in> set xs")
      case True note ia_jxs = True
      have j_not_x: "j\<noteq>x" using d True by auto
      show ?thesis
      proof (cases "j=0 \<and> D dvd ?reduce_xs $$(i,j)")
        case True
        have "?lhs $$ (i,j) = D"
          using True i j ia_jxs by auto
        also have "... = ?rhs $$ (i,j)" using i j j_not_x 
          by (smt "2" calculation dim_col_mat(1) dim_row_mat(1) index_mat(1) insert_iff list.set(2) prod.simps(2) xn)
        finally show ?thesis .
      next
        case False
        show ?thesis
        proof (cases "j=0")
          case True
          then show ?thesis
            by (smt (z3) "2" dim_col_mat(1) dim_row_mat(1) i index_mat(1) insert_iff j list.set(2) old.prod.case)
        next
          case False
          have "?lhs $$ (i,j) = ?reduce_xs $$ (i, j) gmod D"
            using True False i j by auto
          also have "... = A $$ (i,j) gmod D" using 2[OF ] j_not_x i j by auto
          also have "... = ?rhs $$ (i,j)" using i j j_not_x 
            using False True dim_col_mat(1) dim_row_mat(1) index_mat(1) 
              list.set_intros(2) old.prod.case by auto
          finally show ?thesis .
        qed
    qed
  next
      case False
      show ?thesis using 2 i j xn 
        by (smt False dim_col_mat(1) dim_row_mat(1) index_mat(1) insert_iff list.set(2) prod.simps(2))
    qed   
  qed  
  finally show ?case using 1 by simp
qed




lemma reduce_row_mod_D_abs_case_m':
  assumes A_def: "A = A' @\<^sub>r B" and "B \<in> carrier_mat n n"
    and A': "A' \<in> carrier_mat m n" and "a < m" 
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)" 
    and d: "distinct xs" and "m\<ge>n"
    and D: "D > 0" 
  shows "reduce_row_mod_D_abs A a xs D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set xs then if k = 0 \<and> D dvd A$$(i,k) then D
                   else A$$(i,k) gmod D else A$$(i,k))"
  using assms
proof (induct A a xs D m arbitrary: A' B rule: reduce_row_mod_D_abs.induct)
  case (1 A a D m)
  then show ?case by force
next
  case (2 A a x xs D m)
  note A_A'B = "2.prems"(1)
  note B = "2.prems"(2)
  note A' = "2.prems"(3)
  note a = "2.prems"(4)
  note j = "2.prems"(5)
  note mn = "2.prems"(7)
  note d = "2.prems"(6)
  let ?reduce_xs = "(reduce_element_mod_D_abs A a x D m)"
  have reduce_xs_carrier: "?reduce_xs \<in> carrier_mat (m + n) n"
    by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) add.right_neutral append_rows_def 
            carrier_matD carrier_mat_triv index_mat_four_block(2,3) index_zero_mat(2,3)
            reduce_element_mod_D_preserves_dimensions)
  have 1: "reduce_row_mod_D_abs A a (x # xs) D m 
    = reduce_row_mod_D_abs ?reduce_xs a xs D m" by simp
  have 2: "reduce_element_mod_D_abs A a j D m = Matrix.mat (dim_row A) (dim_col A)
           (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 \<and> D dvd A$$(i,k) 
            then D else A$$(i,k) gmod D else A$$(i,k))" if "j\<in>set (x#xs)" for j
    by (rule reduce_element_mod_D_abs_case_m'[OF A_A'B B A'], insert "2.prems" that, auto)
  have "reduce_row_mod_D_abs ?reduce_xs a xs D m =
    Matrix.mat (dim_row ?reduce_xs) (dim_col ?reduce_xs) (\<lambda>(i,k). if i = a \<and> k \<in> set xs 
    then if k = 0 \<and> D dvd ?reduce_xs $$ (i, k) then D else
    ?reduce_xs $$ (i, k) gmod D else ?reduce_xs $$ (i, k))"
  proof (rule "2.hyps"[OF _ B _ a _ _ mn])
    let ?A' = "mat_of_rows n [Matrix.row (reduce_element_mod_D_abs A a x D m) i. i \<leftarrow> [0..<m]]"
    show "reduce_element_mod_D_abs A a x D m = ?A' @\<^sub>r B"
    proof (rule matrix_append_rows_eq_if_preserves[OF reduce_xs_carrier B])
      show " \<forall>i\<in>{m..<m + n}. \<forall>j<n. reduce_element_mod_D_abs A a x D m $$ (i, j) = B $$ (i - m, j) "       
        by (smt A_A'B A' B a Metric_Arith.nnf_simps(7) add_diff_cancel_left' atLeastLessThan_iff
            carrier_matD index_mat_addrow(1) index_row(1) le_add_diff_inverse2 less_diff_conv
            reduce_element_mod_D_abs_def reduce_element_mod_D_preserves_dimensions reduce_xs_carrier
            row_append_rows2)        
    qed
  qed (insert "2.prems", auto simp add: mat_of_rows_def)
  also have "... = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set (x # xs) then if k = 0 \<and> D dvd A$$(i,k)
          then D else A$$(i,k) gmod D else A$$(i,k))" (is "?lhs = ?rhs")
  proof (rule eq_matI) 
    show "dim_row ?lhs = dim_row ?rhs" and "dim_col ?lhs = dim_col ?rhs" by auto
    fix i j assume i: "i<dim_row ?rhs" and j: "j < dim_col ?rhs"
    have jn: "j<n" using j "2.prems" by (simp add: append_rows_def)
    have xn: "x < n" 
      by (simp add: "2.prems"(5))
    show "?lhs $$ (i,j) = ?rhs $$ (i,j)"
    proof (cases "i=a \<and> j \<in> set xs")
      case True note ia_jxs = True
      have j_not_x: "j\<noteq>x" using d True by auto
      show ?thesis
      proof (cases "j=0 \<and> D dvd ?reduce_xs $$(i,j)")
        case True
        have "?lhs $$ (i,j) = D"
          using True i j ia_jxs by auto
        also have "... = ?rhs $$ (i,j)" using i j j_not_x 
          by (smt "2" calculation dim_col_mat(1) dim_row_mat(1) index_mat(1) insert_iff list.set(2) prod.simps(2) xn)
        finally show ?thesis .
      next
        case False        
        have "?lhs $$ (i,j) = ?reduce_xs $$ (i, j) gmod D"
         using True False i j by auto
       also have "... = A $$ (i,j) gmod D" using 2[OF ] j_not_x i j by auto
       also have "... = ?rhs $$ (i,j)" using i j j_not_x
         by (smt False True \<open>Matrix.mat (dim_row ?reduce_xs) 
           (dim_col ?reduce_xs) (\<lambda>(i, k). if i = a \<and> k \<in> set xs 
           then if k = 0 \<and> D dvd  ?reduce_xs $$ (i, k) 
           then D else  ?reduce_xs $$ (i, k) gmod D 
           else  ?reduce_xs $$ (i, k)) $$ (i, j) =  ?reduce_xs $$ (i, j) gmod D\<close> 
               calculation dim_col_mat(1) dim_row_mat(1) dvd_imp_gmod_0[OF \<open>D > 0\<close>] index_mat(1) 
               insert_iff list.set(2) gmod_0_imp_dvd prod.simps(2))
       finally show ?thesis .
     qed   
  next
      case False
      show ?thesis using 2 i j xn 
        by (smt False dim_col_mat(1) dim_row_mat(1) index_mat(1) insert_iff list.set(2) prod.simps(2))
    qed   
  qed  
  finally show ?case using 1 by simp
qed



lemma
  assumes A_def: "A = A' @\<^sub>r B" and B: "B \<in> carrier_mat n n"
  and A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "j<n" and mn: "m\<ge>n"
shows reduce_element_mod_D_invertible_mat_case_m: 
  "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> reduce_element_mod_D A a j D m = P * A" (is ?thesis1)
  and reduce_element_mod_D_abs_invertible_mat_case_m:
  "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
      reduce_element_mod_D_abs A a j D m = P * A" (is ?thesis2)
  unfolding atomize_conj
proof (rule conjI; cases "j = 0 \<and> D dvd A$$(a,j)")
  case True
  let ?P = "addrow_mat (m+n) (- (A $$ (a, j) gdiv D) + 1) a (j + m)"
  have A: "A \<in> carrier_mat (m + n) n" using A_def A' B mn by auto
  have "reduce_element_mod_D_abs A a j D m =  addrow (- (A $$ (a, j) gdiv D) + 1) a (j + m) A"
    unfolding reduce_element_mod_D_abs_def using True by auto
  also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
  finally have rw: "reduce_element_mod_D_abs A a j D m = ?P * A" .
  have "reduce_element_mod_D A a j D m =  addrow (- (A $$ (a, j) gdiv D) + 1) a (j + m) A"
    unfolding reduce_element_mod_D_def using True by auto
  also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
  finally have "reduce_element_mod_D A a j D m = ?P * A" .
  moreover have "?P \<in> carrier_mat (m+n) (m+n)" by simp
  moreover have "invertible_mat ?P"
    by (metis addrow_mat_carrier a det_addrow_mat dvd_mult_right 
        invertible_iff_is_unit_JNF mult.right_neutral not_add_less2 semiring_gcd_class.gcd_dvd1)
  ultimately show ?thesis1 and ?thesis2 using rw by blast+
next
  case False
  show ?thesis1
  proof (cases "j=0")
    case True
    have "reduce_element_mod_D A a j D m = A" unfolding reduce_element_mod_D_def using False True by auto
    then show ?thesis
      by (metis A_def assms(2) assms(3) carrier_append_rows invertible_mat_one left_mult_one_mat one_carrier_mat)
  next
    case False
    let ?P = "addrow_mat (m+n) (- (A $$ (a, j) gdiv D)) a (j + m)"
    have A: "A \<in> carrier_mat (m + n) n" using A_def B A' mn by auto
    have "reduce_element_mod_D A a j D m =  addrow (- (A $$ (a, j) gdiv D)) a (j + m) A"
      unfolding reduce_element_mod_D_def using False by auto
    also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
    finally have "reduce_element_mod_D A a j D m = ?P * A" .
    moreover have "?P \<in> carrier_mat (m+n) (m+n)" by simp
    moreover have "invertible_mat ?P"
      by (metis addrow_mat_carrier a det_addrow_mat dvd_mult_right 
          invertible_iff_is_unit_JNF mult.right_neutral not_add_less2 semiring_gcd_class.gcd_dvd1)
    ultimately show ?thesis by blast
  qed
  show ?thesis2
  proof -
    let ?P = "addrow_mat (m+n) (- (A $$ (a, j) gdiv D)) a (j + m)"
    have A: "A \<in> carrier_mat (m + n) n" using A_def B A' mn by auto
    have "reduce_element_mod_D_abs A a j D m =  addrow (- (A $$ (a, j) gdiv D)) a (j + m) A"
      unfolding reduce_element_mod_D_abs_def using False by auto
    also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
    finally have "reduce_element_mod_D_abs A a j D m = ?P * A" .
    moreover have "?P \<in> carrier_mat (m+n) (m+n)" by simp
    moreover have "invertible_mat ?P"
      by (metis addrow_mat_carrier a det_addrow_mat dvd_mult_right 
          invertible_iff_is_unit_JNF mult.right_neutral not_add_less2 semiring_gcd_class.gcd_dvd1)
    ultimately show ?thesis by blast
  qed
qed


lemma reduce_row_mod_D_invertible_mat_case_m:
  assumes A_def: "A = A' @\<^sub>r B" and "B \<in> carrier_mat n n"
    and A': "A' \<in> carrier_mat m n" and a: "a < m" 
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)" 
    and mn: "m\<ge>n"
  shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_row_mod_D A a xs D m = P * A"
  using assms
proof (induct A a xs D m arbitrary: A' B rule: reduce_row_mod_D.induct)
  case (1 A a D m)
  show ?case by (rule exI[of _ "1\<^sub>m (m+n)"], insert "1.prems", auto simp add: append_rows_def)
next
  case (2 A a x xs D m)
  note A_def = "2.prems"(1)
  note B = "2.prems"(2)
  note A' = "2.prems"(3)
  note a = "2.prems"(4)
  note j = "2.prems"(5)
  note mn = "2.prems"(6)  
  let ?reduce_xs = "(reduce_element_mod_D A a x D m)"
  have 1: "reduce_row_mod_D A a (x # xs) D m 
    = reduce_row_mod_D ?reduce_xs a xs D m" by simp
  have "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_element_mod_D A a x D m = P * A" 
    by (rule reduce_element_mod_D_invertible_mat_case_m, insert "2.prems", auto)
  from this obtain P where P: "P \<in> carrier_mat (m+n) (m+n)" and inv_P: "invertible_mat P"
    and R_P: "reduce_element_mod_D A a x D m = P * A" by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P 
      \<and> reduce_row_mod_D ?reduce_xs a xs D m = P * ?reduce_xs"
  proof (rule "2.hyps")
    let ?A' = "mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [0..<m]]"
    let ?B' = "mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [m..<m+n]]"

    show reduce_xs_A'B': "?reduce_xs = ?A' @\<^sub>r ?B'"
      by (smt "2"(2) "2"(4) P R_P add.comm_neutral append_rows_def append_rows_split carrier_matD
          index_mat_four_block(3) index_mult_mat(2) index_zero_mat(3) le_add1 reduce_element_mod_D_preserves_dimensions(2))
    show "\<forall>j\<in>set xs. j < n \<and> ?B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0)"
    proof
      fix j assume j_in_xs: "j \<in> set xs"
      have jn: "j<n" using j_in_xs j by auto
      have "?B' $$ (j, j) = ?reduce_xs $$ (m+j,j)"
        by (smt "2"(7) Groups.add_ac(2) jn reduce_xs_A'B' add_diff_cancel_left' append_rows_nth2
            diff_zero length_map length_upt mat_of_rows_carrier(1) nat_SN.compat)
      also have "... = B $$ (j,j)" 
        by (smt "2"(2) "2"(5) A' P R_P add_diff_cancel_left' append_rows_def carrier_matD
            group_cancel.rule0 index_mat_addrow(1) index_mat_four_block(1) index_mat_four_block(2,3)
            index_mult_mat(2) index_zero_mat(3) jn le_add1 linorder_not_less nat_SN.plus_gt_right_mono 
            reduce_element_mod_D_def reduce_element_mod_D_preserves_dimensions(1))
      also have "... = D" using j j_in_xs by auto
      finally have B'_jj: "?B' $$ (j, j) = D" by auto
      moreover have "\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0" 
      proof 
        fix j' assume j': "j' \<in>{0..<n} - {j}"
        have "?B' $$ (j, j') = ?reduce_xs $$ (m+j,j')"
          by (smt mn Diff_iff j' add.commute add_diff_cancel_left' 
              append_rows_nth2 atLeastLessThan_iff diff_zero jn length_map length_upt 
              mat_of_rows_carrier(1) nat_SN.compat reduce_xs_A'B')
        also have "... = B $$ (j,j')"
          by (smt "2"(2) "2"(5) A' Diff_iff P R_P j' add.commute add_diff_cancel_left'  
            append_rows_def atLeastLessThan_iff carrier_matD group_cancel.rule0 index_mat_addrow(1)
            index_mat_four_block index_mult_mat(2) index_zero_mat(3) jn nat_SN.plus_gt_right_mono 
            not_add_less2 reduce_element_mod_D_def reduce_element_mod_D_preserves_dimensions(1))
        also have "... = 0" using j j_in_xs j' by auto
        finally show "?B' $$ (j, j') = 0" .
      qed
      ultimately show "j < n \<and> ?B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0)"
        using jn by blast
    qed
    show "?A' : carrier_mat m n" by auto      
    show "?B' : carrier_mat n n" by auto
    show "a<m" using "2.prems" by auto
    show "n\<le>m" using "2.prems" by auto    
  qed
  from this obtain P2 where P2: "P2 \<in> carrier_mat (m + n) (m + n)" and inv_P2: "invertible_mat P2"
    and R_P2: "reduce_row_mod_D ?reduce_xs a xs D m = P2 * ?reduce_xs"
    by auto
  have "invertible_mat (P2 * P)" using P P2 inv_P inv_P2 invertible_mult_JNF by blast
  moreover have "(P2 * P) \<in> carrier_mat (m+n) (m+n)" using P2 P by auto
  moreover have "reduce_row_mod_D A a (x # xs) D m = (P2 * P) * A" 
    by (smt P P2 R_P R_P2 1 assoc_mult_mat carrier_matD carrier_mat_triv
        index_mult_mat reduce_row_mod_D_preserves_dimensions)
  ultimately show ?case by blast
qed




lemma reduce_row_mod_D_abs_invertible_mat_case_m:
  assumes A_def: "A = A' @\<^sub>r B" and "B \<in> carrier_mat n n"
    and A': "A' \<in> carrier_mat m n" and a: "a < m" 
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)" 
    and mn: "m\<ge>n"
  shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_row_mod_D_abs A a xs D m = P * A"
  using assms
proof (induct A a xs D m arbitrary: A' B rule: reduce_row_mod_D_abs.induct)
  case (1 A a D m)
  show ?case by (rule exI[of _ "1\<^sub>m (m+n)"], insert "1.prems", auto simp add: append_rows_def)
next
  case (2 A a x xs D m)
  note A_def = "2.prems"(1)
  note B = "2.prems"(2)
  note A' = "2.prems"(3)
  note a = "2.prems"(4)
  note j = "2.prems"(5)
  note mn = "2.prems"(6)  
  let ?reduce_xs = "(reduce_element_mod_D_abs A a x D m)"
  have 1: "reduce_row_mod_D_abs A a (x # xs) D m 
    = reduce_row_mod_D_abs ?reduce_xs a xs D m" by simp
  have "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_element_mod_D_abs A a x D m = P * A" 
    by (rule reduce_element_mod_D_abs_invertible_mat_case_m, insert "2.prems", auto)
  from this obtain P where P: "P \<in> carrier_mat (m+n) (m+n)" and inv_P: "invertible_mat P"
    and R_P: "reduce_element_mod_D_abs A a x D m = P * A" by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P 
      \<and> reduce_row_mod_D_abs ?reduce_xs a xs D m = P * ?reduce_xs"
  proof (rule "2.hyps")
    let ?A' = "mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [0..<m]]"
    let ?B' = "mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [m..<m+n]]"

    show reduce_xs_A'B': "?reduce_xs = ?A' @\<^sub>r ?B'"
      by (smt "2"(2) "2"(4) P R_P add.comm_neutral append_rows_def append_rows_split carrier_matD
          index_mat_four_block(3) index_mult_mat(2) index_zero_mat(3) le_add1 reduce_element_mod_D_preserves_dimensions(4))
    show "\<forall>j\<in>set xs. j < n \<and> ?B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0)"
    proof
      fix j assume j_in_xs: "j \<in> set xs"
      have jn: "j<n" using j_in_xs j by auto
      have "?B' $$ (j, j) = ?reduce_xs $$ (m+j,j)"
        by (smt "2"(7) Groups.add_ac(2) jn reduce_xs_A'B' add_diff_cancel_left' append_rows_nth2
            diff_zero length_map length_upt mat_of_rows_carrier(1) nat_SN.compat)
      also have "... = B $$ (j,j)" 
        by (smt "2"(2) "2"(5) A' P R_P add_diff_cancel_left' append_rows_def carrier_matD
            group_cancel.rule0 index_mat_addrow(1) index_mat_four_block(1) index_mat_four_block(2,3)
            index_mult_mat(2) index_zero_mat(3) jn le_add1 linorder_not_less nat_SN.plus_gt_right_mono 
            reduce_element_mod_D_abs_def reduce_element_mod_D_preserves_dimensions(3))
      also have "... = D" using j j_in_xs by auto
      finally have B'_jj: "?B' $$ (j, j) = D" by auto
      moreover have "\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0" 
      proof 
        fix j' assume j': "j' \<in>{0..<n} - {j}"
        have "?B' $$ (j, j') = ?reduce_xs $$ (m+j,j')"
          by (smt mn Diff_iff j' add.commute add_diff_cancel_left' 
              append_rows_nth2 atLeastLessThan_iff diff_zero jn length_map length_upt 
              mat_of_rows_carrier(1) nat_SN.compat reduce_xs_A'B')
        also have "... = B $$ (j,j')"
          by (smt "2"(2) "2"(5) A' Diff_iff P R_P j' add.commute add_diff_cancel_left'  
            append_rows_def atLeastLessThan_iff carrier_matD group_cancel.rule0 index_mat_addrow(1)
            index_mat_four_block index_mult_mat(2) index_zero_mat(3) jn nat_SN.plus_gt_right_mono 
            not_add_less2 reduce_element_mod_D_abs_def reduce_element_mod_D_preserves_dimensions(3))
        also have "... = 0" using j j_in_xs j' by auto
        finally show "?B' $$ (j, j') = 0" .
      qed
      ultimately show "j < n \<and> ?B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0)"
        using jn by blast
    qed
    show "?A' : carrier_mat m n" by auto      
    show "?B' : carrier_mat n n" by auto
    show "a<m" using "2.prems" by auto
    show "n\<le>m" using "2.prems" by auto    
  qed
  from this obtain P2 where P2: "P2 \<in> carrier_mat (m + n) (m + n)" and inv_P2: "invertible_mat P2"
    and R_P2: "reduce_row_mod_D_abs ?reduce_xs a xs D m = P2 * ?reduce_xs"
    by auto
  have "invertible_mat (P2 * P)" using P P2 inv_P inv_P2 invertible_mult_JNF by blast
  moreover have "(P2 * P) \<in> carrier_mat (m+n) (m+n)" using P2 P by auto
  moreover have "reduce_row_mod_D_abs A a (x # xs) D m = (P2 * P) * A" 
    by (smt P P2 R_P R_P2 1 assoc_mult_mat carrier_matD carrier_mat_triv
        index_mult_mat reduce_row_mod_D_preserves_dimensions_abs)
  ultimately show ?case by blast
qed




(*Similar to thm reduce_row_mod_D_case_m' but including the case a = m. 
This could substitute the previous version.*)
lemma reduce_row_mod_D_case_m'':
  assumes A_def: "A = A' @\<^sub>r B" and "B \<in> carrier_mat n n"
    and A': "A' \<in> carrier_mat m n" and "a \<le> m" 
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)" 
    and d: "distinct xs" and "m\<ge>n" and "0 \<notin> set xs"
    and "D > 0" 
  shows "reduce_row_mod_D A a xs D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set xs then if k = 0 then if D dvd A$$(i,k) then D
                    else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))"
  using assms
proof (induct A a xs D m arbitrary: A' B rule: reduce_row_mod_D.induct)
  case (1 A a D m)
  then show ?case by force
next
  case (2 A a x xs D m)
  note A_A'B = "2.prems"(1)
  note B = "2.prems"(2)
  note A' = "2.prems"(3)
  note a = "2.prems"(4)
  note j = "2.prems"(5)
  note mn = "2.prems"(7)
  note d = "2.prems"(6)
  note zero_not_xs = "2.prems"(8)
  let ?reduce_xs = "(reduce_element_mod_D A a x D m)"
  have reduce_xs_carrier: "?reduce_xs \<in> carrier_mat (m + n) n"
    by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) add.right_neutral append_rows_def 
            carrier_matD carrier_mat_triv index_mat_four_block(2,3) index_zero_mat(2,3)
            reduce_element_mod_D_preserves_dimensions)
  have A: "A:carrier_mat (m+n) n" using A' B A_A'B by blast
  have 1: "reduce_row_mod_D A a (x # xs) D m 
    = reduce_row_mod_D ?reduce_xs a xs D m" by simp
  have 2: "reduce_element_mod_D A a j D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 then if D dvd A$$(i,k)
          then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" if "j\<in>set (x#xs)" for j
    by (rule reduce_element_mod_D_case_m'[OF A_A'B B A'], insert "2.prems" that, auto)
  have "reduce_row_mod_D ?reduce_xs a xs D m =
    Matrix.mat (dim_row ?reduce_xs) (dim_col ?reduce_xs) (\<lambda>(i,k). if i = a \<and> k \<in> set xs 
    then if k=0 then if D dvd ?reduce_xs $$ (i, k) then D else ?reduce_xs $$ (i, k)
    else ?reduce_xs $$ (i, k) gmod D else ?reduce_xs $$ (i, k))"
  proof (rule "2.hyps"[OF _ _ _ a _ _ mn])
    let ?A' = "mat_of_rows n [Matrix.row (reduce_element_mod_D A a x D m) i. i \<leftarrow> [0..<m]]"
    define B' where "B' = mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [m..<dim_row A]]"
    show A'': "?A' : carrier_mat m n" by auto
    show B': "B' : carrier_mat n n" unfolding B'_def using mn A by auto 
    show reduce_split: "?reduce_xs = ?A' @\<^sub>r B'" 
      by (metis B'_def append_rows_split carrier_matD
          reduce_element_mod_D_preserves_dimensions(1) reduce_xs_carrier le_add1)
    show "\<forall>j\<in>set xs. j<n \<and> (B' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B' $$ (j, j') = 0)"
    proof 
      fix j assume j_xs: "j\<in>set xs"
      have "B $$ (j,j') = B' $$ (j,j')" if j': "j'<n" for j'
      proof -
        have "B $$ (j,j') = A $$ (m+j,j')"
          by (smt A_A'B A A' Groups.add_ac(2) j_xs add_diff_cancel_left' append_rows_def carrier_matD j'
              index_mat_four_block(1) index_mat_four_block(2,3) insert_iff j less_diff_conv list.set(2) not_add_less1)
        also have "... = ?reduce_xs $$ (m+j,j')"
          by (smt (verit, ccfv_threshold) A'' diff_add_zero index_mat_addrow(3) neq0_conv
              a j zero_not_xs A add.commute add_diff_cancel_left' reduce_element_mod_D_def
              cancel_comm_monoid_add_class.diff_cancel carrier_matD index_mat_addrow(1) j'
              j_xs le_eq_less_or_eq less_diff_conv less_not_refl2 list.set_intros(2) nat_SN.compat)
        also have "... = B'$$ (j,j')"
          by (smt B A A' A_A'B B' A'' reduce_split add.commute add_diff_cancel_left' j' not_add_less1
              append_rows_def carrier_matD index_mat_four_block j j_xs less_diff_conv list.set_intros(2))
        finally show ?thesis .
      qed
      thus "j < n \<and> B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. B' $$ (j, j') = 0)" using j
        by (metis Diff_iff atLeastLessThan_iff insert_iff j_xs list.simps(15))
    qed          
  qed (insert "2.prems", auto simp add: mat_of_rows_def)
  also have "... = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set (x # xs) then if k = 0 then if D dvd A$$(i,k) 
          then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" (is "?lhs = ?rhs")
  proof (rule eq_matI) 
    show "dim_row ?lhs = dim_row ?rhs" and "dim_col ?lhs = dim_col ?rhs" by auto
    fix i j assume i: "i<dim_row ?rhs" and j: "j < dim_col ?rhs"
    have jn: "j<n" using j "2.prems" by (simp add: append_rows_def)
    have xn: "x < n" 
      by (simp add: "2.prems"(5))
    show "?lhs $$ (i,j) = ?rhs $$ (i,j)"
    proof (cases "i=a \<and> j \<in> set xs")
      case True note ia_jxs = True
      have j_not_x: "j\<noteq>x" using d True by auto
      show ?thesis
      proof (cases "j=0 \<and> D dvd ?reduce_xs $$(i,j)")
        case True
        have "?lhs $$ (i,j) = D"
          using True i j ia_jxs by auto
        also have "... = ?rhs $$ (i,j)" using i j j_not_x
          by (metis "2.prems"(8) True ia_jxs list.set_intros(2))
        finally show ?thesis .
      next
        case False   
        show ?thesis
          by (smt (z3) "2" "2.prems"(8) dim_col_mat(1) dim_row_mat(1) i index_mat(1) insert_iff j j_not_x list.set(2) old.prod.case)     
    qed
  next
      case False
      show ?thesis using 2 i j xn
        by (smt (z3) "2.prems"(8) False carrier_matD(2) dim_row_mat(1) index_mat(1) 
            insert_iff jn list.set(2) old.prod.case reduce_element_mod_D_preserves_dimensions(2) reduce_xs_carrier)
    qed   
  qed  
  finally show ?case using 1 by simp
qed




(*Similar to thm reduce_row_mod_D_abs_case_m' but including the case a = m. 
This could substitute the previous version.*)
lemma reduce_row_mod_D_abs_case_m'':
  assumes A_def: "A = A' @\<^sub>r B" and "B \<in> carrier_mat n n"
    and A': "A' \<in> carrier_mat m n" and "a \<le> m" 
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)" 
    and d: "distinct xs" and "m\<ge>n" and "0 \<notin> set xs"
    and "D > 0" 
  shows "reduce_row_mod_D_abs A a xs D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set xs then if k = 0 \<and> D dvd A$$(i,k) then D
                   else A$$(i,k) gmod D else A$$(i,k))"
  using assms
proof (induct A a xs D m arbitrary: A' B rule: reduce_row_mod_D_abs.induct)
  case (1 A a D m)
  then show ?case by force
next
  case (2 A a x xs D m)
  note A_A'B = "2.prems"(1)
  note B = "2.prems"(2)
  note A' = "2.prems"(3)
  note a = "2.prems"(4)
  note j = "2.prems"(5)
  note mn = "2.prems"(7)
  note d = "2.prems"(6)
  note zero_not_xs = "2.prems"(8)
  let ?reduce_xs = "(reduce_element_mod_D_abs A a x D m)"
  have reduce_xs_carrier: "?reduce_xs \<in> carrier_mat (m + n) n"
    by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) add.right_neutral append_rows_def 
            carrier_matD carrier_mat_triv index_mat_four_block(2,3) index_zero_mat(2,3)
            reduce_element_mod_D_preserves_dimensions)
  have A: "A:carrier_mat (m+n) n" using A' B A_A'B by blast
  have 1: "reduce_row_mod_D_abs A a (x # xs) D m 
    = reduce_row_mod_D_abs ?reduce_xs a xs D m" by simp
  have 2: "reduce_element_mod_D_abs A a j D m = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k = j then if j = 0 \<and> D dvd A$$(i,k)
          then D else A$$(i,k) gmod D else A$$(i,k))" if "j\<in>set (x#xs)" for j
    by (rule reduce_element_mod_D_abs_case_m'[OF A_A'B B A'], insert "2.prems" that, auto)
  have "reduce_row_mod_D_abs ?reduce_xs a xs D m =
    Matrix.mat (dim_row ?reduce_xs) (dim_col ?reduce_xs) (\<lambda>(i,k). if i = a \<and> k \<in> set xs 
    then if k=0 \<and> D dvd ?reduce_xs $$ (i, k) then D 
    else ?reduce_xs $$ (i, k) gmod D else ?reduce_xs $$ (i, k))"
  proof (rule "2.hyps"[OF _ _ _ a _ _ mn])
    let ?A' = "mat_of_rows n [Matrix.row (reduce_element_mod_D_abs A a x D m) i. i \<leftarrow> [0..<m]]"
    define B' where "B' = mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [m..<dim_row A]]"
    show A'': "?A' : carrier_mat m n" by auto
    show B': "B' : carrier_mat n n" unfolding B'_def using mn A by auto 
    show reduce_split: "?reduce_xs = ?A' @\<^sub>r B'" 
      by (metis B'_def append_rows_split carrier_matD
          reduce_element_mod_D_preserves_dimensions(3) reduce_xs_carrier le_add1)
    show "\<forall>j\<in>set xs. j<n \<and> (B' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B' $$ (j, j') = 0)"
    proof 
      fix j assume j_xs: "j\<in>set xs"
      have "B $$ (j,j') = B' $$ (j,j')" if j': "j'<n" for j'
      proof -
        have "B $$ (j,j') = A $$ (m+j,j')"
          by (smt A_A'B A A' Groups.add_ac(2) j_xs add_diff_cancel_left' append_rows_def carrier_matD j'
              index_mat_four_block(1) index_mat_four_block(2,3) insert_iff j less_diff_conv list.set(2) not_add_less1)
        also have "... = ?reduce_xs $$ (m+j,j')"
          by (smt (verit, ccfv_threshold) A'' diff_add_zero index_mat_addrow(3) neq0_conv
              a j zero_not_xs A add.commute add_diff_cancel_left' reduce_element_mod_D_abs_def
              cancel_comm_monoid_add_class.diff_cancel carrier_matD index_mat_addrow(1) j'
              j_xs le_eq_less_or_eq less_diff_conv less_not_refl2 list.set_intros(2) nat_SN.compat)
        also have "... = B'$$ (j,j')"
          by (smt B A A' A_A'B B' A'' reduce_split add.commute add_diff_cancel_left' j' not_add_less1
              append_rows_def carrier_matD index_mat_four_block j j_xs less_diff_conv list.set_intros(2))
        finally show ?thesis .
      qed
      thus "j < n \<and> B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. B' $$ (j, j') = 0)" using j
        by (metis Diff_iff atLeastLessThan_iff insert_iff j_xs list.simps(15))
    qed          
  qed (insert "2.prems", auto simp add: mat_of_rows_def)
  also have "... = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a \<and> k \<in> set (x # xs) then if k = 0 then if D dvd A$$(i,k) 
          then D else A$$(i,k) else A$$(i,k) gmod D else A$$(i,k))" (is "?lhs = ?rhs")
  proof (rule eq_matI) 
    show "dim_row ?lhs = dim_row ?rhs" and "dim_col ?lhs = dim_col ?rhs" by auto
    fix i j assume i: "i<dim_row ?rhs" and j: "j < dim_col ?rhs"
    have jn: "j<n" using j "2.prems" by (simp add: append_rows_def)
    have xn: "x < n" 
      by (simp add: "2.prems"(5))
    show "?lhs $$ (i,j) = ?rhs $$ (i,j)"
    proof (cases "i=a \<and> j \<in> set xs")
      case True note ia_jxs = True
      have j_not_x: "j\<noteq>x" using d True by auto
      show ?thesis
      proof (cases "j=0 \<and> D dvd ?reduce_xs $$(i,j)")
        case True
        have "?lhs $$ (i,j) = D"
          using True i j ia_jxs by auto
        also have "... = ?rhs $$ (i,j)" using i j j_not_x
          by (metis "2.prems"(8) True ia_jxs list.set_intros(2))
        finally show ?thesis .
      next
        case False   
        show ?thesis
          by (smt (z3) "2" "2.prems"(8) dim_col_mat(1) dim_row_mat(1) i index_mat(1) insert_iff j j_not_x list.set(2) old.prod.case)     
    qed
  next
      case False
      show ?thesis using 2 i j xn
        by (smt (z3) "2.prems"(8) False carrier_matD(2) dim_row_mat(1) index_mat(1) 
            insert_iff jn list.set(2) old.prod.case reduce_element_mod_D_preserves_dimensions(4) reduce_xs_carrier)
    qed   
  qed  
  finally show ?case using 1
    by (smt (verit, ccfv_SIG) "2.prems"(8) cong_mat split_conv)
qed



lemma
  assumes A_def: "A = A' @\<^sub>r B" and B: "B \<in> carrier_mat n n"
  and A': "A' \<in> carrier_mat m n" and a: "a\<le>m" and j: "j<n" and mn: "m\<ge>n" and j0: "j\<noteq>0"
shows reduce_element_mod_D_invertible_mat_case_m':
  "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> reduce_element_mod_D A a j D m = P * A" (is ?thesis1)
  and reduce_element_mod_D_abs_invertible_mat_case_m': 
  "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> reduce_element_mod_D_abs A a j D m = P * A" (is ?thesis2)
proof -
  let ?P = "addrow_mat (m+n) (- (A $$ (a, j) gdiv D)) a (j + m)"
  have jm: "j+m \<noteq>a" using j0 a by auto
  have A: "A \<in> carrier_mat (m + n) n" using A_def A' B mn by auto
  have rw: "reduce_element_mod_D A a j D m = reduce_element_mod_D_abs A a j D m" 
    unfolding reduce_element_mod_D_def reduce_element_mod_D_abs_def using j0 by auto
  have "reduce_element_mod_D A a j D m =  addrow (- (A $$ (a, j) gdiv D)) a (j + m) A"
    unfolding reduce_element_mod_D_def using j0 by auto
  also have "... = ?P * A" by (rule addrow_mat[OF A], insert j mn, auto)
  finally have "reduce_element_mod_D A a j D m = ?P * A" .
  moreover have "?P \<in> carrier_mat (m+n) (m+n)" by simp
  moreover have "invertible_mat ?P"
    by (metis addrow_mat_carrier det_addrow_mat dvd_mult_right jm
        invertible_iff_is_unit_JNF mult.right_neutral semiring_gcd_class.gcd_dvd1)
  ultimately show ?thesis1 and ?thesis2 using rw by metis+
qed

(*Similar to reduce_row_mod_D_invertible_mat_case_m but including the case a = m, and then
adding the assumption 0 not in set xs.*)
lemma reduce_row_mod_D_invertible_mat_case_m':
  assumes A_def: "A = A' @\<^sub>r B" and "B \<in> carrier_mat n n"
    and A': "A' \<in> carrier_mat m n" and a: "a \<le> m" 
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)" 
    and d: "distinct xs" and mn: "m\<ge>n" and "0\<notin> set xs"
  shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_row_mod_D A a xs D m = P * A"
  using assms
proof (induct A a xs D m arbitrary: A' B rule: reduce_row_mod_D.induct)
  case (1 A a D m)
  show ?case by (rule exI[of _ "1\<^sub>m (m+n)"], insert "1.prems", auto simp add: append_rows_def)
next
  case (2 A a x xs D m)
  note A_A'B = "2.prems"(1)
  note B = "2.prems"(2)
  note A' = "2.prems"(3)
  note a = "2.prems"(4)
  note j = "2.prems"(5)
  note mn = "2.prems"(7)
  note d = "2.prems"(6)
  note zero_not_xs = "2.prems"(8)
  let ?reduce_xs = "(reduce_element_mod_D A a x D m)"
  have reduce_xs_carrier: "?reduce_xs \<in> carrier_mat (m + n) n"
    by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) add.right_neutral append_rows_def 
            carrier_matD carrier_mat_triv index_mat_four_block(2,3) index_zero_mat(2,3)
            reduce_element_mod_D_preserves_dimensions)
  have A: "A:carrier_mat (m+n) n" using A' B A_A'B by blast 
  let ?reduce_xs = "(reduce_element_mod_D A a x D m)"
  have 1: "reduce_row_mod_D A a (x # xs) D m 
    = reduce_row_mod_D ?reduce_xs a xs D m" by simp
  have "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_element_mod_D A a x D m = P * A"
    by (rule reduce_element_mod_D_invertible_mat_case_m'[OF A_A'B B A' a _ mn],
        insert zero_not_xs j, auto)
  from this obtain P where P: "P \<in> carrier_mat (m+n) (m+n)" and inv_P: "invertible_mat P"
    and R_P: "reduce_element_mod_D A a x D m = P * A" by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P 
      \<and> reduce_row_mod_D ?reduce_xs a xs D m = P * ?reduce_xs"
  proof (rule "2.hyps")
    let ?A' = "mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [0..<m]]"
    let ?B' = "mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [m..<m+n]]"
    show B': "?B' \<in> carrier_mat n n" by auto
    show A'': "?A' : carrier_mat m n" by auto
    show reduce_split: "?reduce_xs = ?A' @\<^sub>r ?B'"
      by (smt "2"(2) "2"(4) P R_P add.comm_neutral append_rows_def append_rows_split carrier_matD
          index_mat_four_block(3) index_mult_mat(2) index_zero_mat(3) le_add1 reduce_element_mod_D_preserves_dimensions(2))
    show "\<forall>j\<in>set xs. j < n \<and> ?B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0)"
    proof
      fix j assume j_xs: "j\<in>set xs"
      have "B $$ (j,j') = ?B' $$ (j,j')" if j': "j'<n" for j'
      proof -
        have "B $$ (j,j') = A $$ (m+j,j')"
          by (smt A_A'B A A' Groups.add_ac(2) j_xs add_diff_cancel_left' append_rows_def carrier_matD j'
              index_mat_four_block(1) index_mat_four_block(2,3) insert_iff j less_diff_conv list.set(2) not_add_less1)
        also have "... = ?reduce_xs $$ (m+j,j')"
          by (smt (verit, ccfv_SIG) not_add_less1
              a j zero_not_xs A add.commute add_diff_cancel_left' reduce_element_mod_D_def
              cancel_comm_monoid_add_class.diff_cancel carrier_matD index_mat_addrow(1) j'
              j_xs le_eq_less_or_eq less_diff_conv less_not_refl2 list.set_intros(2) nat_SN.compat)
        also have "... = ?B'$$ (j,j')"
          by (smt B A A' A_A'B B' A'' reduce_split add.commute add_diff_cancel_left' j' not_add_less1
              append_rows_def carrier_matD index_mat_four_block j j_xs less_diff_conv list.set_intros(2))
        finally show ?thesis .
      qed
      thus "j < n \<and> ?B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0)" using j
        by (metis Diff_iff atLeastLessThan_iff insert_iff j_xs list.simps(15))
    qed        
  qed (insert d zero_not_xs a mn, auto)
  from this obtain P2 where P2: "P2 \<in> carrier_mat (m + n) (m + n)" and inv_P2: "invertible_mat P2"
    and R_P2: "reduce_row_mod_D ?reduce_xs a xs D m = P2 * ?reduce_xs"
    by auto
  have "invertible_mat (P2 * P)" using P P2 inv_P inv_P2 invertible_mult_JNF by blast
  moreover have "(P2 * P) \<in> carrier_mat (m+n) (m+n)" using P2 P by auto
  moreover have "reduce_row_mod_D A a (x # xs) D m = (P2 * P) * A" 
    by (smt P P2 R_P R_P2 1 assoc_mult_mat carrier_matD carrier_mat_triv
        index_mult_mat reduce_row_mod_D_preserves_dimensions)
  ultimately show ?case by blast
qed



lemma reduce_row_mod_D_abs_invertible_mat_case_m':
  assumes A_def: "A = A' @\<^sub>r B" and "B \<in> carrier_mat n n"
    and A': "A' \<in> carrier_mat m n" and a: "a \<le> m" 
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)" 
    and d: "distinct xs" and mn: "m\<ge>n" and "0\<notin> set xs"
  shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_row_mod_D_abs A a xs D m = P * A"
  using assms
proof (induct A a xs D m arbitrary: A' B rule: reduce_row_mod_D_abs.induct)
  case (1 A a D m)
  show ?case by (rule exI[of _ "1\<^sub>m (m+n)"], insert "1.prems", auto simp add: append_rows_def)
next
  case (2 A a x xs D m)
  note A_A'B = "2.prems"(1)
  note B = "2.prems"(2)
  note A' = "2.prems"(3)
  note a = "2.prems"(4)
  note j = "2.prems"(5)
  note mn = "2.prems"(7)
  note d = "2.prems"(6)
  note zero_not_xs = "2.prems"(8)
  let ?reduce_xs = "(reduce_element_mod_D_abs A a x D m)"
  have reduce_xs_carrier: "?reduce_xs \<in> carrier_mat (m + n) n"
    by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) add.right_neutral append_rows_def 
            carrier_matD carrier_mat_triv index_mat_four_block(2,3) index_zero_mat(2,3)
            reduce_element_mod_D_preserves_dimensions)
  have A: "A:carrier_mat (m+n) n" using A' B A_A'B by blast 
  let ?reduce_xs = "(reduce_element_mod_D_abs A a x D m)"
  have 1: "reduce_row_mod_D_abs A a (x # xs) D m 
    = reduce_row_mod_D_abs ?reduce_xs a xs D m" by simp
  have "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> 
    reduce_element_mod_D_abs A a x D m = P * A"
    by (rule reduce_element_mod_D_abs_invertible_mat_case_m'[OF A_A'B B A' a _ mn],
        insert zero_not_xs j, auto)
  from this obtain P where P: "P \<in> carrier_mat (m+n) (m+n)" and inv_P: "invertible_mat P"
    and R_P: "reduce_element_mod_D_abs A a x D m = P * A" by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P 
      \<and> reduce_row_mod_D_abs ?reduce_xs a xs D m = P * ?reduce_xs"
  proof (rule "2.hyps")
    let ?A' = "mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [0..<m]]"
    let ?B' = "mat_of_rows n [Matrix.row ?reduce_xs i. i \<leftarrow> [m..<m+n]]"
    show B': "?B' \<in> carrier_mat n n" by auto
    show A'': "?A' : carrier_mat m n" by auto
    show reduce_split: "?reduce_xs = ?A' @\<^sub>r ?B'"
      by (smt "2"(2) "2"(4) P R_P add.comm_neutral append_rows_def append_rows_split carrier_matD
          index_mat_four_block(3) index_mult_mat(2) index_zero_mat(3) le_add1 reduce_element_mod_D_preserves_dimensions(4))
    show "\<forall>j\<in>set xs. j < n \<and> ?B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0)"
    proof
      fix j assume j_xs: "j\<in>set xs"
      have "B $$ (j,j') = ?B' $$ (j,j')" if j': "j'<n" for j'
      proof -
        have "B $$ (j,j') = A $$ (m+j,j')"
          by (smt A_A'B A A' Groups.add_ac(2) j_xs add_diff_cancel_left' append_rows_def carrier_matD j'
              index_mat_four_block(1) index_mat_four_block(2,3) insert_iff j less_diff_conv list.set(2) not_add_less1)
        also have "... = ?reduce_xs $$ (m+j,j')"
          by (smt (verit, ccfv_SIG) not_add_less1
              a j zero_not_xs A add.commute add_diff_cancel_left' reduce_element_mod_D_abs_def
              cancel_comm_monoid_add_class.diff_cancel carrier_matD index_mat_addrow(1) j'
              j_xs le_eq_less_or_eq less_diff_conv less_not_refl2 list.set_intros(2) nat_SN.compat)
        also have "... = ?B'$$ (j,j')"
          by (smt B A A' A_A'B B' A'' reduce_split add.commute add_diff_cancel_left' j' not_add_less1
              append_rows_def carrier_matD index_mat_four_block j j_xs less_diff_conv list.set_intros(2))
        finally show ?thesis .
      qed
      thus "j < n \<and> ?B' $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. ?B' $$ (j, j') = 0)" using j
        by (metis Diff_iff atLeastLessThan_iff insert_iff j_xs list.simps(15))
    qed        
  qed (insert d zero_not_xs a mn, auto)
  from this obtain P2 where P2: "P2 \<in> carrier_mat (m + n) (m + n)" and inv_P2: "invertible_mat P2"
    and R_P2: "reduce_row_mod_D_abs ?reduce_xs a xs D m = P2 * ?reduce_xs"
    by auto
  have "invertible_mat (P2 * P)" using P P2 inv_P inv_P2 invertible_mult_JNF by blast
  moreover have "(P2 * P) \<in> carrier_mat (m+n) (m+n)" using P2 P by auto
  moreover have "reduce_row_mod_D_abs A a (x # xs) D m = (P2 * P) * A" 
    by (smt P P2 R_P R_P2 1 assoc_mult_mat carrier_matD carrier_mat_triv
        index_mult_mat reduce_row_mod_D_preserves_dimensions_abs)
  ultimately show ?case by blast
qed


lemma reduce_invertible_mat_case_m: 
  assumes A': "A' \<in> carrier_mat m n" and B: "B \<in> carrier_mat n n"
    and a: "a<m" and ab: "a \<noteq> m" 
  and A_def: "A = A' @\<^sub>r B"
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)"  
  and Aaj: "A $$ (a,0) \<noteq> 0"
  and mn: "m\<ge>n"
  and n0: "0<n"
  and pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(m,0))"
  and A2_def: "A2 = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(m,k))
                   else if i = m then u * A$$(a,k) + v * A$$(m,k)
                   else A$$(i,k)
            )"
  and xs_def: "xs = [1..<n]"
  and ys_def: "ys = [1..<n]"
    and j_ys: "\<forall>j\<in>set ys. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)"
    and D0: "D > 0"
  and Am0_D: "A $$ (m, 0) \<in> {0,D}"
  and Am0_D2: "A $$ (m, 0) = 0 \<longrightarrow> A $$ (a, 0) = D"
shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m+n) (m+n) \<and> (reduce a m D A) = P * A"
proof -
  let ?A = "Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(m,k))
                   else if i = m then u * A$$(a,k) + v * A$$(m,k)
                   else A$$(i,k)
            )"
  have D: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" using mn by auto
  have A: "A \<in> carrier_mat (m+n) n" using A_def A' B mn by simp
  hence A_carrier: "?A \<in> carrier_mat (m+n) n" by auto

  let ?BM = "bezout_matrix_JNF A a m 0 euclid_ext2"
  
  have A'_BZ_A: "?A = ?BM * A"
    by (rule bezout_matrix_JNF_mult_eq[OF A' _ _ ab A_def B pquvd], insert a, auto)  
  have invertible_bezout: "invertible_mat ?BM"
    by (rule invertible_bezout_matrix_JNF[OF A is_bezout_ext_euclid_ext2 a _ _ Aaj], insert a n0, auto)      
  have BM: "?BM \<in> carrier_mat (m+n) (m+n)" unfolding bezout_matrix_JNF_def using A by auto
  let ?reduce_a = "reduce_row_mod_D ?A a xs D m"
  define A'1 where "A'1 = mat_of_rows n [Matrix.row ?A i. i \<leftarrow> [0..<m]]"
  define A'2 where "A'2 = mat_of_rows n [Matrix.row ?A i. i \<leftarrow> [m..<dim_row A]]"
  have A_A'_D: "?A = A'1 @\<^sub>r A'2" using append_rows_split A
    by (metis (no_types, lifting) A'1_def A'2_def A_carrier carrier_matD le_add1)
  have j_A'1_A'2: "\<forall>j\<in>set xs. j < n \<and> A'2 $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. A'2 $$ (j, j') = 0)"
    proof (rule ballI)
      fix ja assume ja: "ja\<in>set xs"
      have ja_n: "ja < n" using ja unfolding xs_def by auto
      have ja2: "ja < dim_row A - m" using A mn ja_n by auto
      have ja_m: "ja < m" using ja_n mn by auto
      have ja_not_0: "ja \<noteq> 0" using ja unfolding xs_def by auto
      show "ja < n \<and> A'2 $$ (ja, ja) = D \<and> (\<forall>j'\<in>{0..<n} - {ja}. A'2 $$ (ja, j') = 0)"
      proof -
        have "A'2 $$ (ja, ja) = [Matrix.row ?A i. i \<leftarrow> [m..<dim_row A]] ! ja $v ja"
          by (metis (no_types, lifting) A A'2_def add_diff_cancel_left' carrier_matD(1) 
              ja_n length_map length_upt mat_of_rows_index)
        also have "... = ?A $$ (m + ja, ja)" using A mn ja_n by auto
        also have "... = A $$ (m+ja, ja)" using A a mn ja_n ja_not_0 by auto
        also have "... =  (A' @\<^sub>r B) $$ (m + ja, ja)" unfolding A_def ..
        also have "... = B $$ (ja, ja)"
          by (metis B Groups.add_ac(2) append_rows_nth2 assms(1) ja_n mn nat_SN.compat)
        also have "... = D" using j ja by blast
        finally have A2_D: "A'2 $$ (ja, ja) = D" .

        moreover have "(\<forall>j'\<in>{0..<n} - {ja}. A'2 $$ (ja, j') = 0)"
        proof (rule ballI)
          fix j' assume j': "j': {0..<n} - {ja}"
          have "A'2 $$ (ja, j') = [Matrix.row ?A i. i \<leftarrow> [m..<dim_row A]] ! ja $v j'"
            unfolding A'2_def by (rule mat_of_rows_index, insert j' ja_n ja2, auto)
          also have "... = ?A $$ (m + ja, j')" using A mn ja_n j' by auto
          also have "... = A $$ (m+ja, j')" using A a mn ja_n ja_not_0 j' by auto
          also have "... =  (A' @\<^sub>r B) $$ (ja + m, j')" unfolding A_def
            by (simp add: add.commute)
          also have "... = B $$ (ja, j')"
            by (rule append_rows_nth2[OF A' B _ ja_m ja_n], insert j', auto)
          also have "... = 0" using mn j' ja_n j ja by auto
          finally show "A'2 $$ (ja, j') = 0" .
        qed
        ultimately show ?thesis using ja_n by simp
      qed
    qed
  have reduce_a_eq: "?reduce_a = Matrix.mat (dim_row ?A) (dim_col ?A) 
    (\<lambda>(i, k). if i = a \<and> k \<in> set xs then if k = 0 then if D dvd ?A $$ (i, k) then D
    else ?A $$ (i, k) else ?A $$ (i, k) gmod D else ?A $$ (i, k))"
  proof (rule reduce_row_mod_D_case_m'[OF A_A'_D _ _ a j_A'1_A'2 _ mn D0])    
    show "A'2 \<in> carrier_mat n n" using A A'2_def by auto
    show "A'1 \<in> carrier_mat m n" by (simp add: A'1_def mat_of_rows_def) 
    show "distinct xs" using distinct_filter distinct_upt xs_def by blast
  qed
  have reduce_a: "?reduce_a \<in> carrier_mat (m+n) n" using reduce_a_eq A by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?reduce_a = P * ?A"
    by (rule reduce_row_mod_D_invertible_mat_case_m[OF A_A'_D _ _ _ j_A'1_A'2 mn],
        insert a A A'2_def A'1_def, auto)
  from this obtain P where P: "P \<in> carrier_mat (m + n) (m + n)" and inv_P: "invertible_mat P" 
    and reduce_a_PA: "?reduce_a = P * ?A" by blast
  let ?reduce_b = "reduce_row_mod_D ?reduce_a m ys D m"
  let ?B' = "mat_of_rows n [Matrix.row ?reduce_a i. i \<leftarrow> [0..<m]]"
  define reduce_a1 where "reduce_a1 = mat_of_rows (dim_col ?reduce_a) [Matrix.row ?reduce_a i. i \<leftarrow> [0..<m]]"
  define reduce_a2 where "reduce_a2 = mat_of_rows (dim_col ?reduce_a) [Matrix.row ?reduce_a i. i \<leftarrow> [m..<dim_row ?reduce_a]]"
  have reduce_a_split: "?reduce_a = reduce_a1 @\<^sub>r reduce_a2"
    by (unfold reduce_a1_def reduce_a2_def, rule append_rows_split, insert mn A, auto)  
  have zero_notin_ys: "0 \<notin> set ys"
  proof -
    have m: "m<dim_row A" using A n0 by auto
    have "?A $$ (m,0) =  u * A $$ (a, 0) + v * A $$ (m, 0)" using m n0 a A by auto
    also have "... = 0" using pquvd
      by (smt dvd_mult_div_cancel euclid_ext2_def euclid_ext2_works(3) more_arith_simps(11)
          mult.commute mult_minus_left prod.sel(1) prod.sel(2) semiring_gcd_class.gcd_dvd1)
    finally show ?thesis using D0 unfolding ys_def by auto
  qed
  have reduce_a2: "reduce_a2 \<in> carrier_mat n n" unfolding reduce_a2_def using A by auto
  have reduce_a1: "reduce_a1 \<in> carrier_mat m n" unfolding reduce_a1_def using A by auto
  have j2: "\<forall>j\<in>set ys. j < n \<and> reduce_a2 $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. reduce_a2 $$ (j, j') = 0)"
  proof
    fix j assume j_in_ys: "j \<in> set ys"
    have a_jm: "a \<noteq> j+m" using a by auto
    have m_not_jm: "m \<noteq> j + m" using zero_notin_ys j_in_ys by fastforce
    have jm: "j+m < dim_row ?A" using A_carrier j_in_ys unfolding ys_def by auto
    have jn: "j < dim_col ?A" using A_carrier j_in_ys unfolding ys_def by auto
    have jm': "j+m < dim_row A" using A_carrier j_in_ys unfolding ys_def by auto
    have jn': "j < dim_col A" using A_carrier j_in_ys unfolding ys_def by auto
    have "reduce_a2 $$ (j, j') = B $$ (j,j')" if j': "j'<n" for j'
    proof -
      have "reduce_a2 $$ (j, j') = ?reduce_a $$ (j+m,j')"
        by (rule append_rows_nth2[symmetric, OF reduce_a1 reduce_a2 reduce_a_split],
            insert j_in_ys mn j', auto simp add: ys_def)
      also have "... = ?A $$ (j+m, j')" using reduce_a_eq jm jn a_jm j' A_carrier by auto          
      also have "... = A $$ (j+m, j')" using a_jm m_not_jm jm' jn' j' A_carrier by auto
      also have "... = B $$ (j,j')"
        by (smt A append_rows_nth2 A' B A_def mn carrier_matD(2) jn' le_Suc_ex that trans_less_add1)
      finally show ?thesis .
    qed
    thus "j < n \<and> reduce_a2 $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. reduce_a2 $$ (j, j') = 0)"
      using j_ys j_in_ys by auto
  qed
  have reduce_b_eq: "?reduce_b = Matrix.mat (dim_row ?reduce_a) (dim_col ?reduce_a) 
    (\<lambda>(i, k). if i = m \<and> k \<in> set ys then if k = 0 then if D dvd ?reduce_a $$ (i, k) then D
      else ?reduce_a $$ (i, k) else ?reduce_a $$ (i, k) gmod D else ?reduce_a $$ (i, k))"
    by (rule reduce_row_mod_D_case_m''[OF reduce_a_split reduce_a2 reduce_a1 _ j2 _ mn zero_notin_ys],
        insert D0, auto simp add: ys_def)    
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?reduce_b = P * ?reduce_a"
    by (rule reduce_row_mod_D_invertible_mat_case_m'[OF reduce_a_split reduce_a2 reduce_a1 _ j2 _ mn zero_notin_ys],
        auto simp add: ys_def) 
  from this obtain Q where Q: "Q \<in> carrier_mat (m + n) (m + n)" and inv_Q: "invertible_mat Q" 
    and reduce_b_Q_reduce: "?reduce_b = Q * ?reduce_a" by blast
  have reduce_b_eq_reduce: "?reduce_b = (reduce a m D A)"
  proof (rule eq_matI)
    show dr_eq: "dim_row ?reduce_b = dim_row (reduce a m D A)" 
      and dc_eq: "dim_col ?reduce_b = dim_col (reduce a m D A)"
      using reduce_preserves_dimensions by auto
    fix i ja assume i: "i<dim_row (reduce a m D A)" and ja: "ja< dim_col (reduce a m D A)"
    have im: "i<m+n" using A i reduce_preserves_dimensions(1) by auto
    have ja_n: "ja<n" using A ja reduce_preserves_dimensions(2) by auto
    show "?reduce_b $$ (i,ja) = (reduce a m D A) $$ (i,ja)"    
    proof (cases "(i\<noteq>a \<and> i\<noteq>m)")
      case True
      have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq 
        by (smt True dr_eq dc_eq i index_mat(1) ja prod.simps(2) reduce_row_mod_D_preserves_dimensions)
      also have "... = ?A $$ (i,ja)"
        by (smt A True carrier_matD(2) dim_col_mat(1) dim_row_mat(1) i index_mat(1) ja_n 
            reduce_a_eq reduce_preserves_dimensions(1) split_conv)
      also have "... = A $$ (i,ja)" using A True im ja_n by auto
      also have "... = (reduce a m D A) $$ (i,ja)" unfolding reduce_alt_def_not0[OF Aaj pquvd]
        using im ja_n A True by auto
      finally show ?thesis .      
    next
      case False note a_or_b = False
      have gcd_pq: "p * A $$ (a, 0) + q * A $$ (m, 0) = gcd (A $$ (a, 0)) (A $$ (m, 0))"
        by (metis assms(10) euclid_ext2_works(1) euclid_ext2_works(2))
      have gcd_le_D: "gcd (A $$ (a, 0)) (A $$ (m, 0)) \<le> D"        
        by (metis Am0_D D0 assms(17) empty_iff gcd_le1_int gcd_le2_int insert_iff)
      show ?thesis
      proof (cases "i=a")
        case True note ia = True
        hence i_not_b: "i\<noteq>m" using ab by auto
        have 1: "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq             
            by (smt ab dc_eq dim_row_mat(1) dr_eq i ia index_mat(1) ja prod.simps(2)
                reduce_b_eq reduce_row_mod_D_preserves_dimensions(2))
        show ?thesis
        proof (cases "ja=0")
          case True note ja0 = True           
          hence ja_notin_xs: "ja \<notin> set xs" unfolding xs_def by auto
          have "?reduce_a $$ (i,ja) = p * A $$ (a, 0) + q * A $$ (m, 0)" 
            unfolding reduce_a_eq using True ja0 ab a_or_b i_not_b ja_n im a A False ja_notin_xs
            by auto
          also have "... = (reduce a m D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd]
            using True a_or_b i_not_b ja_n im A False               
            using gcd_le_D gcd_pq Am0_D Am0_D2 by auto 
          finally show ?thesis using 1 by auto
        next
          case False
          hence ja_in_xs: "ja \<in> set xs"
            unfolding xs_def using True ja_n im a A unfolding set_filter by auto
          have "?reduce_a $$ (i,ja) = ?A $$ (i, ja) gmod D"
            unfolding reduce_a_eq using True ab a_or_b i_not_b ja_n im a A ja_in_xs False by auto
          also have "... = (reduce a m D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using True a_or_b i_not_b ja_n im A False by auto
          finally show ?thesis using 1 by simp
        qed
      next
        case False note i_not_a = False
        have i_drb: "i<dim_row ?reduce_b" 
          and i_dra: "i<dim_row ?reduce_a" 
          and ja_drb: "ja < dim_col ?reduce_b"
          and ja_dra: "ja < dim_col ?reduce_a" using i ja reduce_carrier[OF A] A ja_n im by auto
        have ib: "i=m" using False a_or_b by auto
        show ?thesis
        proof (cases "ja = 0")
          case True note ja0 = True
          have uv: "u * A $$ (a, ja) + v * A $$ (m, ja) = 0"
            unfolding euclid_ext2_works[OF pquvd[symmetric]] True
            by (smt euclid_ext2_works[OF pquvd[symmetric]] more_arith_simps(11) mult.commute mult_minus_left)
          have "?reduce_b $$ (i,ja) = u * A $$ (a, ja) + v * A $$ (m, ja)"
            by (smt (z3) A A_carrier True assms(4) carrier_matD i ib index_mat(1) reduce_a_eq
                ja_dra old.prod.case reduce_preserves_dimensions(1) zero_notin_ys reduce_b_eq
                reduce_row_mod_D_preserves_dimensions)
          also have "... = 0" using uv by blast
          also have "... = (reduce a m D A) $$ (i,ja)" 
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using True False a_or_b ib ja_n im A 
              using i_not_a uv by auto
          finally show ?thesis by auto
        next
          case False
          have ja_in_ys: "ja \<in> set ys"
            unfolding ys_def using False ib ja_n im a  A unfolding set_filter by auto
          have "?reduce_b $$ (i,ja) = (if ja = 0 then if D dvd ?reduce_a$$(i,ja) then D
                                  else ?reduce_a $$ (i, ja) else ?reduce_a $$ (i, ja) gmod D)"
            unfolding reduce_b_eq using i_not_a  ja ja_in_ys 
            by (smt i_dra ja_dra a_or_b index_mat(1) prod.simps(2))
          also have "... = (if ja = 0 then if D dvd ?reduce_a$$(i,ja) then D
                            else ?A $$ (i, ja) else ?A $$ (i, ja) gmod D)"
            unfolding reduce_a_eq using ab a_or_b ib False ja_n im a A ja_in_ys by auto
          also have "... = (reduce a m D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using  False a_or_b ib ja_n im A 
            using i_not_a  by auto         
          finally show ?thesis .
        qed
      qed
    qed
  qed
  have r: "?reduce_a = (P*?BM) * A" using A A'_BZ_A BM P reduce_a_PA by auto
  have "Q * P * ?BM : carrier_mat (m+n) (m+n)" using P BM Q by auto
  moreover have "invertible_mat (Q * P*?BM)"
    using inv_P invertible_bezout BM P invertible_mult_JNF inv_Q Q by (metis mult_carrier_mat)
  moreover have "(reduce a m D A) = (Q * P * ?BM) * A" using reduce_a_eq r reduce_b_eq_reduce
    by (smt BM P Q assoc_mult_mat carrier_matD carrier_mat_triv 
        dim_row_mat(1) index_mult_mat(2,3) reduce_b_Q_reduce)
  ultimately show ?thesis by auto
qed



lemma reduce_abs_invertible_mat_case_m: 
  assumes A': "A' \<in> carrier_mat m n" and B: "B \<in> carrier_mat n n"
    and a: "a<m" and ab: "a \<noteq> m" 
  and A_def: "A = A' @\<^sub>r B"
    and j: "\<forall>j\<in>set xs. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)"  
  and Aaj: "A $$ (a,0) \<noteq> 0"
  and mn: "m\<ge>n"
  and n0: "0<n"
  and pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(m,0))"
  and A2_def: "A2 = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(m,k))
                   else if i = m then u * A$$(a,k) + v * A$$(m,k)
                   else A$$(i,k)
            )"
  and xs_def: "xs = filter (\<lambda>i. abs (A2 $$ (a,i)) > D) [0..<n]"
  and ys_def: "ys = filter (\<lambda>i. abs (A2 $$ (m,i)) > D) [0..<n]"
    and j_ys: "\<forall>j\<in>set ys. j<n \<and> (B $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. B $$ (j, j') = 0)"
    and D0: "D > 0"
shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m+n) (m+n) \<and> (reduce_abs a m D A) = P * A"
proof -
  let ?A = "Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(m,k))
                   else if i = m then u * A$$(a,k) + v * A$$(m,k)
                   else A$$(i,k)
            )"
  note xs_def = xs_def[unfolded A2_def]
  note ys_def = ys_def[unfolded A2_def]
  have D: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" using mn by auto
  have A: "A \<in> carrier_mat (m+n) n" using A_def A' B mn by simp
  hence A_carrier: "?A \<in> carrier_mat (m+n) n" by auto

  let ?BM = "bezout_matrix_JNF A a m 0 euclid_ext2"
  
  have A'_BZ_A: "?A = ?BM * A"
    by (rule bezout_matrix_JNF_mult_eq[OF A' _ _ ab A_def B pquvd], insert a, auto)  
  have invertible_bezout: "invertible_mat ?BM"
    by (rule invertible_bezout_matrix_JNF[OF A is_bezout_ext_euclid_ext2 a _ _ Aaj], insert a n0, auto)      
  have BM: "?BM \<in> carrier_mat (m+n) (m+n)" unfolding bezout_matrix_JNF_def using A by auto
  let ?reduce_a = "reduce_row_mod_D_abs ?A a xs D m"
  define A'1 where "A'1 = mat_of_rows n [Matrix.row ?A i. i \<leftarrow> [0..<m]]"
  define A'2 where "A'2 = mat_of_rows n [Matrix.row ?A i. i \<leftarrow> [m..<dim_row A]]"
  have A_A'_D: "?A = A'1 @\<^sub>r A'2" using append_rows_split A
    by (metis (no_types, lifting) A'1_def A'2_def A_carrier carrier_matD le_add1)
  have j_A'1_A'2: "\<forall>j\<in>set xs. j < n \<and> A'2 $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. A'2 $$ (j, j') = 0)"
    proof (rule ballI)
      fix ja assume ja: "ja\<in>set xs"
      have ja_n: "ja < n" using ja unfolding xs_def by auto
      have ja2: "ja < dim_row A - m" using A mn ja_n by auto
      have ja_m: "ja < m" using ja_n mn by auto
      have abs_A_a_ja_D: "\<bar>(?A $$ (a,ja))\<bar> > D" using ja unfolding xs_def by auto
      have ja_not_0: "ja \<noteq> 0"
      proof (rule ccontr, simp)
        assume ja_a: "ja = 0" 
        have A_mja_D: "A$$(m,ja) = D"
        proof -
          have "A$$(m,ja) = (A' @\<^sub>r B) $$ (m, ja)" unfolding A_def ..
          also have "... = B $$ (m-m,ja)"                        
            by (metis B append_rows_nth A' assms(9) carrier_matD(1) ja_a less_add_same_cancel1 less_irrefl_nat)
          also have "... = B $$ (0,0)" unfolding ja_a by auto
          also have "... = D" using mn unfolding ja_a using ja_n ja j ja_a by auto 
          finally show ?thesis .
        qed
        have "?A $$ (a, ja) = p*A$$(a,ja) + q*A$$(m,ja)" using A_carrier ja_n a A by auto
        also have "... = d" using pquvd A assms(2) ja_n ja_a
          by (simp add: bezout_coefficients_fst_snd euclid_ext2_def)
        also have "... = gcd (A$$(a,ja)) (A$$(m,ja))"
          by (metis euclid_ext2_works(2) ja_a pquvd)
        also have "abs(...) \<le> D" using A_mja_D  by (simp add: D0)       
        finally have "abs (?A $$ (a, ja)) \<le> D" .
        thus False using abs_A_a_ja_D by auto
      qed      
      show "ja < n \<and> A'2 $$ (ja, ja) = D \<and> (\<forall>j'\<in>{0..<n} - {ja}. A'2 $$ (ja, j') = 0)"
      proof -
        have "A'2 $$ (ja, ja) = [Matrix.row ?A i. i \<leftarrow> [m..<dim_row A]] ! ja $v ja"
          by (metis (no_types, lifting) A A'2_def add_diff_cancel_left' carrier_matD(1) 
              ja_n length_map length_upt mat_of_rows_index)
        also have "... = ?A $$ (m + ja, ja)" using A mn ja_n by auto
        also have "... = A $$ (m+ja, ja)" using A a mn ja_n ja_not_0 by auto
        also have "... =  (A' @\<^sub>r B) $$ (m + ja, ja)" unfolding A_def ..
        also have "... = B $$ (ja, ja)"
          by (metis B Groups.add_ac(2) append_rows_nth2 assms(1) ja_n mn nat_SN.compat)
        also have "... = D" using j ja by blast
        finally have A2_D: "A'2 $$ (ja, ja) = D" .

        moreover have "(\<forall>j'\<in>{0..<n} - {ja}. A'2 $$ (ja, j') = 0)"
        proof (rule ballI)
          fix j' assume j': "j': {0..<n} - {ja}"
          have "A'2 $$ (ja, j') = [Matrix.row ?A i. i \<leftarrow> [m..<dim_row A]] ! ja $v j'"
            unfolding A'2_def by (rule mat_of_rows_index, insert j' ja_n ja2, auto)
          also have "... = ?A $$ (m + ja, j')" using A mn ja_n j' by auto
          also have "... = A $$ (m+ja, j')" using A a mn ja_n ja_not_0 j' by auto
          also have "... =  (A' @\<^sub>r B) $$ (ja + m, j')" unfolding A_def
            by (simp add: add.commute)
          also have "... = B $$ (ja, j')"
            by (rule append_rows_nth2[OF A' B _ ja_m ja_n], insert j', auto)
          also have "... = 0" using mn j' ja_n j ja by auto
          finally show "A'2 $$ (ja, j') = 0" .
        qed
        ultimately show ?thesis using ja_n by simp
      qed
    qed
  have reduce_a_eq: "?reduce_a = Matrix.mat (dim_row ?A) (dim_col ?A) 
    (\<lambda>(i, k). if i = a \<and> k \<in> set xs then if k = 0 \<and> D dvd ?A $$ (i, k) then D else ?A $$ (i, k) gmod D else ?A $$ (i, k))"
  proof (rule reduce_row_mod_D_abs_case_m'[OF A_A'_D _ _ a j_A'1_A'2 _ mn D0])    
    show "A'2 \<in> carrier_mat n n" using A A'2_def by auto
    show "A'1 \<in> carrier_mat m n" by (simp add: A'1_def mat_of_rows_def) 
    show "distinct xs" using distinct_filter distinct_upt xs_def by blast
  qed
  have reduce_a: "?reduce_a \<in> carrier_mat (m+n) n" using reduce_a_eq A by auto
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?reduce_a = P * ?A"
    by (rule reduce_row_mod_D_abs_invertible_mat_case_m[OF A_A'_D _ _ _ j_A'1_A'2 mn],
        insert a A A'2_def A'1_def, auto)
  from this obtain P where P: "P \<in> carrier_mat (m + n) (m + n)" and inv_P: "invertible_mat P" 
    and reduce_a_PA: "?reduce_a = P * ?A" by blast
  let ?reduce_b = "reduce_row_mod_D_abs ?reduce_a m ys D m"
  let ?B' = "mat_of_rows n [Matrix.row ?reduce_a i. i \<leftarrow> [0..<m]]"
  define reduce_a1 where "reduce_a1 = mat_of_rows (dim_col ?reduce_a) [Matrix.row ?reduce_a i. i \<leftarrow> [0..<m]]"
  define reduce_a2 where "reduce_a2 = mat_of_rows (dim_col ?reduce_a) [Matrix.row ?reduce_a i. i \<leftarrow> [m..<dim_row ?reduce_a]]"
  have reduce_a_split: "?reduce_a = reduce_a1 @\<^sub>r reduce_a2"
    by (unfold reduce_a1_def reduce_a2_def, rule append_rows_split, insert mn A, auto)  
  have zero_notin_ys: "0 \<notin> set ys"
  proof -
    have m: "m<dim_row A" using A n0 by auto
    have "?A $$ (m,0) =  u * A $$ (a, 0) + v * A $$ (m, 0)" using m n0 a A by auto
    also have "... = 0" using pquvd
      by (smt dvd_mult_div_cancel euclid_ext2_def euclid_ext2_works(3) more_arith_simps(11)
          mult.commute mult_minus_left prod.sel(1) prod.sel(2) semiring_gcd_class.gcd_dvd1)
    finally show ?thesis using D0 unfolding ys_def by auto
  qed
  have reduce_a2: "reduce_a2 \<in> carrier_mat n n" unfolding reduce_a2_def using A by auto
  have reduce_a1: "reduce_a1 \<in> carrier_mat m n" unfolding reduce_a1_def using A by auto
  have j2: "\<forall>j\<in>set ys. j < n \<and> reduce_a2 $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. reduce_a2 $$ (j, j') = 0)"
  proof
    fix j assume j_in_ys: "j \<in> set ys"
    have a_jm: "a \<noteq> j+m" using a by auto
    have m_not_jm: "m \<noteq> j + m" using zero_notin_ys j_in_ys by fastforce
    have jm: "j+m < dim_row ?A" using A_carrier j_in_ys unfolding ys_def by auto
    have jn: "j < dim_col ?A" using A_carrier j_in_ys unfolding ys_def by auto
    have jm': "j+m < dim_row A" using A_carrier j_in_ys unfolding ys_def by auto
    have jn': "j < dim_col A" using A_carrier j_in_ys unfolding ys_def by auto
    have "reduce_a2 $$ (j, j') = B $$ (j,j')" if j': "j'<n" for j'
    proof -
      have "reduce_a2 $$ (j, j') = ?reduce_a $$ (j+m,j')"
        by (rule append_rows_nth2[symmetric, OF reduce_a1 reduce_a2 reduce_a_split],
            insert j_in_ys mn j', auto simp add: ys_def)
      also have "... = ?A $$ (j+m, j')" using reduce_a_eq jm jn a_jm j' A_carrier by auto          
      also have "... = A $$ (j+m, j')" using a_jm m_not_jm jm' jn' j' A_carrier by auto
      also have "... = B $$ (j,j')"
        by (smt A append_rows_nth2 A' B A_def mn carrier_matD(2) jn' le_Suc_ex that trans_less_add1)
      finally show ?thesis .
    qed
    thus "j < n \<and> reduce_a2 $$ (j, j) = D \<and> (\<forall>j'\<in>{0..<n} - {j}. reduce_a2 $$ (j, j') = 0)"
      using j_ys j_in_ys by auto
  qed
  have reduce_b_eq: "?reduce_b = Matrix.mat (dim_row ?reduce_a) (dim_col ?reduce_a) 
    (\<lambda>(i, k). if i = m \<and> k \<in> set ys then if k = 0 \<and> D dvd ?reduce_a $$ (i, k) then D else ?reduce_a $$ (i, k) gmod D else ?reduce_a $$ (i, k))"
    by (rule reduce_row_mod_D_abs_case_m''[OF reduce_a_split reduce_a2 reduce_a1 _ j2 _ mn zero_notin_ys],
        insert D0, auto simp add: ys_def)    
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?reduce_b = P * ?reduce_a"
    by (rule reduce_row_mod_D_abs_invertible_mat_case_m'[OF reduce_a_split reduce_a2 reduce_a1 _ j2 _ mn zero_notin_ys],
        auto simp add: ys_def) 
  from this obtain Q where Q: "Q \<in> carrier_mat (m + n) (m + n)" and inv_Q: "invertible_mat Q" 
    and reduce_b_Q_reduce: "?reduce_b = Q * ?reduce_a" by blast
  have reduce_b_eq_reduce: "?reduce_b = (reduce_abs a m D A)"
  proof (rule eq_matI)
    show dr_eq: "dim_row ?reduce_b = dim_row (reduce_abs a m D A)" 
      and dc_eq: "dim_col ?reduce_b = dim_col (reduce_abs a m D A)"
      using reduce_preserves_dimensions by auto
    fix i ja assume i: "i<dim_row (reduce_abs a m D A)" and ja: "ja< dim_col (reduce_abs a m D A)"
    have im: "i<m+n" using A i reduce_preserves_dimensions(3) by auto
    have ja_n: "ja<n" using A ja reduce_preserves_dimensions(4) by auto
    show "?reduce_b $$ (i,ja) = (reduce_abs a m D A) $$ (i,ja)"    
    proof (cases "(i\<noteq>a \<and> i\<noteq>m)")
      case True
      have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq 
        by (smt True dr_eq dc_eq i index_mat(1) ja prod.simps(2) reduce_row_mod_D_preserves_dimensions_abs)
      also have "... = ?A $$ (i,ja)"
        by (smt A True carrier_matD(2) dim_col_mat(1) dim_row_mat(1) i index_mat(1) ja_n 
            reduce_a_eq reduce_preserves_dimensions(3) split_conv)
      also have "... = A $$ (i,ja)" using A True im ja_n by auto
      also have "... = (reduce_abs a m D A) $$ (i,ja)" unfolding reduce_alt_def_not0[OF Aaj pquvd]
        using im ja_n A True by auto
      finally show ?thesis .      
    next
      case False note a_or_b = False
      show ?thesis
      proof (cases "i=a")
        case True note ia = True
        hence i_not_b: "i\<noteq>m" using ab by auto
        show ?thesis
        proof (cases "abs((p*A$$(a,ja) + q*A$$(m,ja))) > D")
          case True note ge_D = True
          have ja_in_xs: "ja \<in> set xs"
            unfolding xs_def using True ja_n im a A unfolding set_filter by auto
          have 1: "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq             
            by (smt ab dc_eq dim_row_mat(1) dr_eq i ia index_mat(1) ja prod.simps(2)
                reduce_b_eq reduce_row_mod_D_preserves_dimensions_abs(2))
          show ?thesis 
          proof (cases "ja = 0 \<and> D dvd p*A$$(a,ja) + q*A$$(m,ja)")
            case True
            have "?reduce_a $$ (i,ja) = D"
              unfolding reduce_a_eq using True ab a_or_b i_not_b ja_n im a A ja_in_xs False by auto
            also have "... = (reduce_abs a m D A) $$ (i,ja)"
              unfolding reduce_alt_def_not0[OF Aaj pquvd]
              using True a_or_b i_not_b ja_n im A False ge_D               
              by auto 
            finally show ?thesis using 1 by simp
          next
            case False
            have "?reduce_a $$ (i,ja) = ?A $$ (i, ja) gmod D"
              unfolding reduce_a_eq using True ab a_or_b i_not_b ja_n im a A ja_in_xs False by auto
            also have "... = (reduce_abs a m D A) $$ (i,ja)"
              unfolding reduce_alt_def_not0[OF Aaj pquvd] using True a_or_b i_not_b ja_n im A False by auto
            finally show ?thesis using 1 by simp
          qed        
        next
          case False
          have ja_in_xs: "ja \<notin> set xs"
            unfolding xs_def using False ja_n im a A unfolding set_filter by auto
          have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq             
            by (smt ab dc_eq dim_row_mat(1) dr_eq i ia index_mat(1) ja prod.simps(2)
                reduce_b_eq reduce_row_mod_D_preserves_dimensions_abs(2))
          also have "... = ?A $$ (i, ja)"
            unfolding reduce_a_eq using False ab a_or_b i_not_b ja_n im a A ja_in_xs by auto
          also have "... = (reduce_abs a m D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using False a_or_b i_not_b ja_n im A by auto
          finally show ?thesis .
        qed
      next
        case False note i_not_a = False
        have i_drb: "i<dim_row ?reduce_b" 
          and i_dra: "i<dim_row ?reduce_a" 
          and ja_drb: "ja < dim_col ?reduce_b"
          and ja_dra: "ja < dim_col ?reduce_a" using i ja reduce_carrier[OF A] A ja_n im by auto
          have ib: "i=m" using False a_or_b by auto
        show ?thesis
        proof (cases "abs((u*A$$(a,ja) + v * A$$(m,ja))) > D")
          case True note ge_D = True
          have ja_in_ys: "ja \<in> set ys"
            unfolding ys_def using True False ib ja_n im a  A unfolding set_filter by auto
          have "?reduce_b $$ (i,ja) = (if ja = 0 \<and> D dvd ?reduce_a$$(i,ja) then D else ?reduce_a $$ (i, ja) gmod D)"
            unfolding reduce_b_eq using i_not_a True  ja ja_in_ys 
            by (smt i_dra ja_dra a_or_b index_mat(1) prod.simps(2))
          also have "... = (if ja = 0 \<and> D dvd ?reduce_a$$(i,ja) then D else ?A $$ (i, ja) gmod D)"
            unfolding reduce_a_eq using True ab a_or_b ib False ja_n im a A ja_in_ys by auto
          also have "... = (reduce_abs a m D A) $$ (i,ja)"
          proof (cases "ja = 0 \<and> D dvd ?reduce_a$$(i,ja)")
            case True
            have ja0: "ja=0" using True by auto
            have "u * A $$ (a, ja) + v * A $$ (m, ja) = 0"
              unfolding euclid_ext2_works[OF pquvd[symmetric]] ja0
              by (smt euclid_ext2_works[OF pquvd[symmetric]] more_arith_simps(11) mult.commute mult_minus_left)
            hence abs_0: "abs((u*A$$(a,ja) + v * A$$(m,ja))) = 0" by auto
            show ?thesis using abs_0 D0 ge_D by linarith           
          next
            case False
            then show ?thesis 
              unfolding reduce_alt_def_not0[OF Aaj pquvd] using True ge_D False a_or_b ib ja_n im A 
              using i_not_a by auto           
          qed      
          finally show ?thesis .
        next
          case False
          have ja_in_ys: "ja \<notin> set ys"
            unfolding ys_def using i_not_a False ib ja_n im a  A unfolding set_filter by auto
          have "?reduce_b $$ (i,ja) = ?reduce_a $$ (i,ja)" unfolding reduce_b_eq             
            by (smt False a_or_b dc_eq dim_row_mat(1) dr_eq i index_mat(1) ja ja_in_ys
                prod.simps(2) reduce_b_eq reduce_row_mod_D_preserves_dimensions_abs(2))
          also have "... = ?A $$ (i, ja)"
            unfolding reduce_a_eq using False ab a_or_b i_not_a ja_n im a A ja_in_ys by auto
          also have "... = (reduce_abs a m D A) $$ (i,ja)"
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using False a_or_b i_not_a ja_n im A by auto
          finally show ?thesis .
        qed
      qed      
    qed    
  qed
  have r: "?reduce_a = (P*?BM) * A" using A A'_BZ_A BM P reduce_a_PA by auto
  have "Q * P * ?BM : carrier_mat (m+n) (m+n)" using P BM Q by auto
  moreover have "invertible_mat (Q * P*?BM)"
    using inv_P invertible_bezout BM P invertible_mult_JNF inv_Q Q by (metis mult_carrier_mat)
  moreover have "(reduce_abs a m D A) = (Q * P * ?BM) * A" using reduce_a_eq r reduce_b_eq_reduce
    by (smt BM P Q assoc_mult_mat carrier_matD carrier_mat_triv 
        dim_row_mat(1) index_mult_mat(2,3) reduce_b_Q_reduce)
  ultimately show ?thesis by auto
qed




lemma reduce_not0:
  assumes A: "A \<in> carrier_mat m n" and a: "a<m" and a_less_b: "a<b" and j: "0<n" and b: "b<m"
    and Aaj: "A $$ (a,0) \<noteq> 0" and D0: "D \<noteq> 0"
  shows "reduce a b D A $$ (a, 0) \<noteq> 0" (is "?reduce $$ (a,0) \<noteq> _")
  and "reduce_abs a b D A $$ (a, 0) \<noteq> 0" (is "?reduce_abs $$ (a,0) \<noteq> _")
proof -
  have "?reduce $$ (a,0) = (let r = gcd (A $$ (a, 0)) (A $$ (b, 0)) in if D dvd r then D else r)" 
    by (rule reduce_gcd[OF A _ j Aaj], insert a, simp)
  also have "... \<noteq> 0" unfolding Let_def using D0 
    by (smt Aaj gcd_eq_0_iff gmod_0_imp_dvd)
  finally show "reduce a b D A $$ (a, 0) \<noteq> 0" .
  have "?reduce_abs $$ (a,0) = (let r = gcd (A $$ (a, 0)) (A $$ (b, 0)) in 
        if D < r then if D dvd r then D else r gmod D else r)"
    by (rule reduce_gcd[OF A _ j Aaj], insert a, simp)
  also have "... \<noteq> 0" unfolding Let_def using D0 
    by (smt Aaj gcd_eq_0_iff gmod_0_imp_dvd)
  finally show "reduce_abs a b D A $$ (a, 0) \<noteq> 0" .
qed

lemma reduce_below_not0:
 assumes A: "A \<in> carrier_mat m n" and a: "a<m" and j: "0<n" 
    and Aaj: "A $$ (a,0) \<noteq> 0" 
and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
  and "D\<noteq> 0"
  shows "reduce_below a xs D A $$ (a, 0) \<noteq> 0" (is "?R $$ (a,0) \<noteq> _")
  using assms
proof (induct a xs D A arbitrary: A rule: reduce_below.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note Aaj = "2.prems"(4)
  note d = "2.prems"(5)
  note D0 = "2.prems"(7)
  note x_less_xxs = "2.prems"(6)
  have xm: "x < m" using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by simp
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat m n"
    by (metis (no_types, lifting) A carrier_matD carrier_mat_triv reduce_preserves_dimensions)
  have h: "reduce_below a xs D (reduce a x D A) $$ (a,0) \<noteq> 0"
  proof (rule "2.hyps")
    show "reduce a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A a _ j xm Aaj D0], insert x_less_xxs, simp)
  qed (insert A a j Aaj d x_less_xxs xm reduce_ax D0, auto)
  thus ?case by auto
qed



lemma reduce_below_abs_not0:
 assumes A: "A \<in> carrier_mat m n" and a: "a<m" and j: "0<n" 
    and Aaj: "A $$ (a,0) \<noteq> 0" 
and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
  and "D\<noteq> 0"
  shows "reduce_below_abs a xs D A $$ (a, 0) \<noteq> 0" (is "?R $$ (a,0) \<noteq> _")
  using assms
proof (induct a xs D A arbitrary: A rule: reduce_below_abs.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note Aaj = "2.prems"(4)
  note d = "2.prems"(5)
  note D0 = "2.prems"(7)
  note x_less_xxs = "2.prems"(6)
  have xm: "x < m" using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by simp
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce_abs a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat m n"
    by (metis (no_types, lifting) A carrier_matD carrier_mat_triv reduce_preserves_dimensions)
  have h: "reduce_below_abs a xs D (reduce_abs a x D A) $$ (a,0) \<noteq> 0"
  proof (rule "2.hyps")
    show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A a _ j xm Aaj D0], insert x_less_xxs, simp)
  qed (insert A a j Aaj d x_less_xxs xm reduce_ax D0, auto)
  thus ?case by auto
qed



lemma reduce_below_not0_case_m:
 assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
    and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "D \<noteq> 0"
  shows "reduce_below a (xs@[m]) D A $$ (a, 0) \<noteq> 0" (is "?R $$ (a,0) \<noteq> _")
  using assms
proof (induct a xs D A arbitrary: A A' rule: reduce_below.induct)
  case (1 a D A)
  note A' = "1.prems"(1)
  note a = "1.prems"(2)
  note n = "1.prems"(3)
  note A_def = "1.prems"(4)
  note Aaj = "1.prems"(5)
  note mn = "1.prems"(6)
  note all_less_xxs = "1.prems"(7)
  note D0 = "1.prems"(8)
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  have "reduce_below a ([] @ [m]) D A $$ (a, 0) = reduce_below a [m] D A $$ (a, 0)" by auto
  also have "... = reduce a m D A $$ (a, 0)" by auto
  also have "... \<noteq> 0"
    by (rule reduce_not0[OF A _ a n _ Aaj D0], insert a n, auto)
  finally show ?case .
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note n = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note x_less_xxs = "2.prems"(7)
  note D0= "2.prems"(8)
  have xm: "x < m" using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m+n) n"
    by (metis (no_types, lifting) A carrier_matD carrier_mat_triv reduce_preserves_dimensions)
  have h: "reduce_below a (xs@[m]) D (reduce a x D A) $$ (a,0) \<noteq> 0"
  proof (rule "2.hyps")
    show "reduce a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ _ _ _ D0], insert x_less_xxs j Aaj, auto)
    let ?reduce_ax' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "?reduce_ax = ?reduce_ax' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" by (rule reduce_append_rows_eq[OF A' A_def a xm n Aaj])
  qed (insert A a j Aaj x_less_xxs xm reduce_ax mn D0, auto)
  thus ?case by auto
qed

lemma reduce_below_abs_not0_case_m:
 assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
    and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "D \<noteq> 0"
  shows "reduce_below_abs a (xs@[m]) D A $$ (a, 0) \<noteq> 0" (is "?R $$ (a,0) \<noteq> _")
  using assms
proof (induct a xs D A arbitrary: A A' rule: reduce_below_abs.induct)
  case (1 a D A)
  note A' = "1.prems"(1)
  note a = "1.prems"(2)
  note n = "1.prems"(3)
  note A_def = "1.prems"(4)
  note Aaj = "1.prems"(5)
  note mn = "1.prems"(6)
  note all_less_xxs = "1.prems"(7)
  note D0 = "1.prems"(8)
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  have "reduce_below_abs a ([] @ [m]) D A $$ (a, 0) = reduce_below_abs a [m] D A $$ (a, 0)" by auto
  also have "... = reduce_abs a m D A $$ (a, 0)" by auto
  also have "... \<noteq> 0"
    by (rule reduce_not0[OF A _ a n _ Aaj D0], insert a n, auto)
  finally show ?case .
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note n = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note x_less_xxs = "2.prems"(7)
  note D0= "2.prems"(8)
  have xm: "x < m" using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce_abs a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m+n) n"
    by (metis (no_types, lifting) A carrier_matD carrier_mat_triv reduce_preserves_dimensions)
  have h: "reduce_below_abs a (xs@[m]) D (reduce_abs a x D A) $$ (a,0) \<noteq> 0"
  proof (rule "2.hyps")
    show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ _ _ _ D0], insert x_less_xxs j Aaj, auto)
    let ?reduce_ax' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "?reduce_ax = ?reduce_ax' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" by (rule reduce_append_rows_eq[OF A' A_def a xm n Aaj])
  qed (insert A a j Aaj x_less_xxs xm reduce_ax mn D0, auto)
  thus ?case by auto
qed





lemma reduce_below_invertible_mat:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "m\<ge>n"
    and "D>0"
  shows "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m+n) (m+n) \<and> reduce_below a xs D A = P * A)"
  using assms
proof (induct a xs D A arbitrary: A' rule: reduce_below.induct)
  case (1 a D A)
  then show ?case
    by (metis append_rows_def carrier_matD(1) index_mat_four_block(2) reduce_below.simps(1)
        index_smult_mat(2) index_zero_mat(2) invertible_mat_one left_mult_one_mat' one_carrier_mat)
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note d = "2.prems"(6)
  note x_less_xxs = "2.prems"(7)
  note mn = "2.prems"(8)
  note D_ge0 = "2.prems"(9)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  have xm: "x < m" using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by simp
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have h: "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) 
    \<and> reduce_below a xs D (reduce a x D A) = P * reduce a x D A)"
  proof (rule "2.hyps"[OF _ a j _ _ ])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm j Aaj])  
    show "reduce a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
  qed (insert mn d x_less_xxs D_ge0, auto)
  from this obtain P where inv_P: "invertible_mat P" and P: "P \<in> carrier_mat (m + n) (m + n)"
    and rb_Pr: "reduce_below a xs D (reduce a x D A) = P * reduce a x D A" by blast
  have *: "reduce_below a (x # xs) D A = reduce_below a xs D (reduce a x D A)" by simp
  have "\<exists>Q. invertible_mat Q \<and> Q \<in> carrier_mat (m+n) (m+n) \<and> (reduce a x D A) = Q * A"
    by (rule reduce_invertible_mat[OF A' a j xm _ A_def Aaj ], insert "2.prems", auto)
  from this obtain Q where inv_Q: "invertible_mat Q" and Q: "Q \<in> carrier_mat (m + n) (m + n)"
    and r_QA: "reduce a x D A = Q * A" by blast
  have "invertible_mat (P*Q)" using inv_P inv_Q P Q invertible_mult_JNF by blast
  moreover have "P * Q \<in> carrier_mat (m+n) (m+n)" using P Q by auto
  moreover have "reduce_below a (x # xs) D A = (P*Q) * A" 
    by (smt P Q * assoc_mult_mat carrier_matD(1) carrier_mat_triv index_mult_mat(2) 
        r_QA rb_Pr reduce_preserves_dimensions(1))
  ultimately show ?case by blast
qed


lemma reduce_below_abs_invertible_mat:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "m\<ge>n"
    and "D>0"
  shows "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m+n) (m+n) \<and> reduce_below_abs a xs D A = P * A)"
  using assms
proof (induct a xs D A arbitrary: A' rule: reduce_below_abs.induct)
  case (1 a D A)
  then show ?case
    by (metis carrier_append_rows invertible_mat_one left_mult_one_mat one_carrier_mat
        reduce_below_abs.simps(1) smult_carrier_mat)
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note d = "2.prems"(6)
  note x_less_xxs = "2.prems"(7)
  note mn = "2.prems"(8)
  note D_ge0 = "2.prems"(9)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  have xm: "x < m" using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by simp
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce_abs a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have h: "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) 
    \<and> reduce_below_abs a xs D (reduce_abs a x D A) = P * reduce_abs a x D A)"
  proof (rule "2.hyps"[OF _ a j _ _ ])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm j Aaj])  
    show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
  qed (insert mn d x_less_xxs D_ge0, auto)
  from this obtain P where inv_P: "invertible_mat P" and P: "P \<in> carrier_mat (m + n) (m + n)"
    and rb_Pr: "reduce_below_abs a xs D (reduce_abs a x D A) = P * reduce_abs a x D A" by blast
  have *: "reduce_below_abs a (x # xs) D A = reduce_below_abs a xs D (reduce_abs a x D A)" by simp
  have "\<exists>Q. invertible_mat Q \<and> Q \<in> carrier_mat (m+n) (m+n) \<and> (reduce_abs a x D A) = Q * A"
    by (rule reduce_abs_invertible_mat[OF A' a j xm _ A_def Aaj ], insert "2.prems", auto)
  from this obtain Q where inv_Q: "invertible_mat Q" and Q: "Q \<in> carrier_mat (m + n) (m + n)"
    and r_QA: "reduce_abs a x D A = Q * A" by blast
  have "invertible_mat (P*Q)" using inv_P inv_Q P Q invertible_mult_JNF by blast
  moreover have "P * Q \<in> carrier_mat (m+n) (m+n)" using P Q by auto
  moreover have "reduce_below_abs a (x # xs) D A = (P*Q) * A" 
    by (smt P Q * assoc_mult_mat carrier_matD(1) carrier_mat_triv index_mult_mat(2) 
        r_QA rb_Pr reduce_preserves_dimensions(3))
  ultimately show ?case by blast
qed



lemma reduce_below_preserves:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "j<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<notin> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "i\<noteq>a" and "i<m+n"
  and "D>0"
  shows "reduce_below a xs D A $$ (i,j) = A $$ (i,j)"
  using assms
proof (induct a xs D A arbitrary: A' i rule: reduce_below.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note i_set_xxs = "2.prems"(7)
  note d = "2.prems"(8)
  note xxs_less_m = "2.prems"(9)
  note ia = "2.prems"(10)
  note imm = "2.prems"(11)
  note D_ge0 = "2.prems"(12)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) 2 add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have "reduce_below a (x # xs) D A $$ (i, j) = reduce_below a xs D (reduce a x D A) $$ (i, j)"
    by auto
  also have "... = reduce a x D A $$ (i, j)"
  proof (rule "2.hyps"[OF _ a j _ _ mn _ _ _ ia imm D_ge0])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm _ Aaj], insert j, auto)  
    show "i \<notin> set xs" using i_set_xxs by auto
    show "distinct xs" using d by auto
    show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
    show "reduce a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ _ _ Aaj], insert "2.prems", auto)
    show "?A' \<in> carrier_mat m n" by auto    
  qed  
  also have "... = A $$ (i,j)" by (rule reduce_preserves[OF A j Aaj], insert "2.prems", auto)
  finally show ?case .
qed




lemma reduce_below_abs_preserves:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "j<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<notin> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "i\<noteq>a" and "i<m+n"
  and "D>0"
  shows "reduce_below_abs a xs D A $$ (i,j) = A $$ (i,j)"
  using assms
proof (induct a xs D A arbitrary: A' i rule: reduce_below_abs.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note i_set_xxs = "2.prems"(7)
  note d = "2.prems"(8)
  note xxs_less_m = "2.prems"(9)
  note ia = "2.prems"(10)
  note imm = "2.prems"(11)
  note D_ge0 = "2.prems"(12)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce_abs a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) 2 add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have "reduce_below_abs a (x # xs) D A $$ (i, j) = reduce_below_abs a xs D (reduce_abs a x D A) $$ (i, j)"
    by auto
  also have "... = reduce_abs a x D A $$ (i, j)"
  proof (rule "2.hyps"[OF _ a j _ _ mn _ _ _ ia imm D_ge0])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm _ Aaj], insert j, auto)  
    show "i \<notin> set xs" using i_set_xxs by auto
    show "distinct xs" using d by auto
    show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
    show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ _ _ Aaj], insert "2.prems", auto)
    show "?A' \<in> carrier_mat m n" by auto    
  qed  
  also have "... = A $$ (i,j)" by (rule reduce_preserves[OF A j Aaj], insert "2.prems", auto)
  finally show ?case .
qed



lemma reduce_below_0:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<in> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
  and "D>0"
  shows "reduce_below a xs D A $$ (i,0) = 0"
  using assms
proof (induct a xs D A arbitrary: A' i rule: reduce_below.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note i_set_xxs = "2.prems"(7)
  note d = "2.prems"(8)
  note xxs_less_m = "2.prems"(9)
  note D_ge0 = "2.prems"(10)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  show ?case
  proof (cases "i=x")
    case True
    have "reduce_below a (x # xs) D A $$ (i, 0) = reduce_below a xs D (reduce a x D A) $$ (i, 0)"
      by auto
    also have "... = (reduce a x D A) $$ (i, 0)"
    proof (rule reduce_below_preserves[OF _ a j _ _ mn ])
      let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
      show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
        by (rule reduce_append_rows_eq[OF A' A_def a xm j Aaj])      
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce a x D A $$ (a, 0) \<noteq> 0"
        by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
      show "?A' \<in> carrier_mat m n" by auto
      show "i \<notin> set xs" using True d by auto
      show "i \<noteq> a" using "2.prems" by blast
      show "i < m + n"
        by (simp add: True trans_less_add1 xm)
    qed (insert D_ge0)
    also have "... = 0" unfolding True by (rule reduce_0[OF A _ j _ _ Aaj], insert "2.prems", auto)
    finally show ?thesis .
  next
    case False note i_not_x = False    
    have h: "reduce_below a xs D (reduce a x D A) $$ (i, 0) = 0 "
    proof (rule "2.hyps"[OF _ a j _ _ mn])
      let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
      show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      proof (rule matrix_append_rows_eq_if_preserves[OF reduce_ax D1])
        show "\<forall>i\<in>{m..<m + n}. \<forall>ja<n. ?reduce_ax $$ (i, ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" 
        proof (rule+)
          fix i ja assume i: "i \<in> {m..<m + n}" and ja: "ja < n"
          have ja_dc: "ja < dim_col A" and i_dr: "i < dim_row A" using i ja A by auto
          have i_not_a: "i \<noteq> a" using i a by auto
          have i_not_x: "i \<noteq> x" using i xm by auto
          have "?reduce_ax $$ (i,ja) = A $$ (i,ja)" 
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using ja_dc i_dr i_not_a i_not_x by auto 
          also have "... = (if i < dim_row A' then A' $$(i,ja) else (D \<cdot>\<^sub>m (1\<^sub>m n))$$(i-m,ja))"
            by (unfold A_def, rule append_rows_nth[OF A' D1 _ ja], insert A i_dr, simp)
          also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" using i A' by auto
          finally show "?reduce_ax $$ (i,ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" .   
        qed
      qed
      show "i \<in> set xs" using i_set_xxs i_not_x by auto
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce a x D A $$ (a, 0) \<noteq> 0"
        by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
      show "?A' \<in> carrier_mat m n" by auto
    qed (insert D_ge0)
    have "reduce_below a (x # xs) D A $$ (i, 0) = reduce_below a xs D (reduce a x D A) $$ (i, 0)"
      by auto
    also have "... = 0" using h .
    finally show ?thesis .
  qed
qed

lemma reduce_below_abs_0:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<in> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
  and "D>0"
  shows "reduce_below_abs a xs D A $$ (i,0) = 0"
  using assms
proof (induct a xs D A arbitrary: A' i rule: reduce_below_abs.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note i_set_xxs = "2.prems"(7)
  note d = "2.prems"(8)
  note xxs_less_m = "2.prems"(9)
  note D_ge0 = "2.prems"(10)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce_abs a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  show ?case
  proof (cases "i=x")
    case True
    have "reduce_below_abs a (x # xs) D A $$ (i, 0) = reduce_below_abs a xs D (reduce_abs a x D A) $$ (i, 0)"
      by auto
    also have "... = (reduce_abs a x D A) $$ (i, 0)"
    proof (rule reduce_below_abs_preserves[OF _ a j _ _ mn ])
      let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
      show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
        by (rule reduce_append_rows_eq[OF A' A_def a xm j Aaj])      
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
        by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
      show "?A' \<in> carrier_mat m n" by auto
      show "i \<notin> set xs" using True d by auto
      show "i \<noteq> a" using "2.prems" by blast
      show "i < m + n"
        by (simp add: True trans_less_add1 xm)
    qed (insert D_ge0)
    also have "... = 0" unfolding True by (rule reduce_0[OF A _ j _ _ Aaj], insert "2.prems", auto)
    finally show ?thesis .
  next
    case False note i_not_x = False    
    have h: "reduce_below_abs a xs D (reduce_abs a x D A) $$ (i, 0) = 0 "
    proof (rule "2.hyps"[OF _ a j _ _ mn])
      let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
      show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      proof (rule matrix_append_rows_eq_if_preserves[OF reduce_ax D1])
        show "\<forall>i\<in>{m..<m + n}. \<forall>ja<n. ?reduce_ax $$ (i, ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" 
        proof (rule+)
          fix i ja assume i: "i \<in> {m..<m + n}" and ja: "ja < n"
          have ja_dc: "ja < dim_col A" and i_dr: "i < dim_row A" using i ja A by auto
          have i_not_a: "i \<noteq> a" using i a by auto
          have i_not_x: "i \<noteq> x" using i xm by auto
          have "?reduce_ax $$ (i,ja) = A $$ (i,ja)" 
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using ja_dc i_dr i_not_a i_not_x by auto 
          also have "... = (if i < dim_row A' then A' $$(i,ja) else (D \<cdot>\<^sub>m (1\<^sub>m n))$$(i-m,ja))"
            by (unfold A_def, rule append_rows_nth[OF A' D1 _ ja], insert A i_dr, simp)
          also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" using i A' by auto
          finally show "?reduce_ax $$ (i,ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" .   
        qed
      qed
      show "i \<in> set xs" using i_set_xxs i_not_x by auto
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
        by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
      show "?A' \<in> carrier_mat m n" by auto
    qed (insert D_ge0)
    have "reduce_below_abs a (x # xs) D A $$ (i, 0) = reduce_below_abs a xs D (reduce_abs a x D A) $$ (i, 0)"
      by auto
    also have "... = 0" using h .
    finally show ?thesis .
  qed
qed




lemma reduce_below_preserves_case_m:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "j<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<notin> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "i\<noteq>a" and "i<m+n" and "i\<noteq> m"
  and "D>0"
  shows "reduce_below a (xs @ [m]) D A $$ (i,j) = A $$ (i,j)"
  using assms
proof (induct a xs D A arbitrary: A' i rule: reduce_below.induct)
  case (1 a D A)
  have "reduce_below a ([] @ [m]) D A $$ (i, j) =  reduce_below a [m] D A $$ (i, j)" by auto
  also have "... = reduce a m D A $$ (i,j)" by auto
  also have "... = A $$ (i,j)"
    by (rule reduce_preserves, insert "1", auto)
  finally show ?case .
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note i_set_xxs = "2.prems"(7)
  note d = "2.prems"(8)
  note xxs_less_m = "2.prems"(9)
  note ia = "2.prems"(10)
  note imm = "2.prems"(11)
  note D_ge0 = "2.prems"(13)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) A' A_def add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have "reduce_below a ((x # xs) @ [m]) D A $$ (i, j) 
      = reduce_below a (xs@[m]) D (reduce a x D A) $$ (i, j)"
    by auto
  also have "... = reduce a x D A $$ (i, j)"
  proof (rule "2.hyps"[OF _ a j _ _ mn _ _ _ ia imm _ D_ge0])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm _ Aaj], insert j, auto)  
    show "i \<notin> set xs" using i_set_xxs by auto
    show "distinct xs" using d by auto
    show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
    show "reduce a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ _ _ Aaj], insert "2.prems", auto)
    show "?A' \<in> carrier_mat m n" by auto    
    show "i\<noteq>m" using "2.prems" by auto
  qed  
  also have "... = A $$ (i,j)" by (rule reduce_preserves[OF A j Aaj], insert "2.prems", auto)
  finally show ?case .
qed


lemma reduce_below_abs_preserves_case_m:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "j<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<notin> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "i\<noteq>a" and "i<m+n" and "i\<noteq> m"
  and "D>0"
  shows "reduce_below_abs a (xs @ [m]) D A $$ (i,j) = A $$ (i,j)"
  using assms
proof (induct a xs D A arbitrary: A' i rule: reduce_below_abs.induct)
  case (1 a D A)
  have "reduce_below_abs a ([] @ [m]) D A $$ (i, j) = reduce_below_abs a [m] D A $$ (i, j)" by auto
  also have "... = reduce_abs a m D A $$ (i,j)" by auto
  also have "... = A $$ (i,j)"
    by (rule reduce_preserves, insert "1", auto)
  finally show ?case .
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note i_set_xxs = "2.prems"(7)
  note d = "2.prems"(8)
  note xxs_less_m = "2.prems"(9)
  note ia = "2.prems"(10)
  note imm = "2.prems"(11)
  note D_ge0 = "2.prems"(13)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce_abs a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) A' A_def add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have "reduce_below_abs a ((x # xs) @ [m]) D A $$ (i, j) 
      = reduce_below_abs a (xs@[m]) D (reduce_abs a x D A) $$ (i, j)"
    by auto
  also have "... = reduce_abs a x D A $$ (i, j)"
  proof (rule "2.hyps"[OF _ a j _ _ mn _ _ _ ia imm _ D_ge0])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm _ Aaj], insert j, auto)  
    show "i \<notin> set xs" using i_set_xxs by auto
    show "distinct xs" using d by auto
    show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
    show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ _ _ Aaj], insert "2.prems", auto)
    show "?A' \<in> carrier_mat m n" by auto    
    show "i\<noteq>m" using "2.prems" by auto
  qed  
  also have "... = A $$ (i,j)" by (rule reduce_preserves[OF A j Aaj], insert "2.prems", auto)
  finally show ?case .
qed



lemma reduce_below_0_case_m1:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "m\<noteq>a"
  and "D>0"
  shows "reduce_below a (xs @ [m]) D A $$ (m,0) = 0"
  using assms
proof (induct a xs D A arbitrary: A' rule: reduce_below.induct)
  case (1 a D A)
  have A: "A \<in> carrier_mat (m+n) n" using "1" by auto
  have " reduce_below a ([] @ [m]) D A $$ (m, 0) =  reduce_below a [m] D A $$ (m, 0)" by auto
  also have "... = reduce a m D A $$ (m,0)" by auto
  also have "... = 0" by (rule reduce_0[OF A], insert "1.prems", auto)
  finally show ?case .
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note d = "2.prems"(7)
  note xxs_less_m = "2.prems"(8)
  note ma = "2.prems"(9)
  note D_ge0 = "2.prems"(10)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have "reduce_below a ((x # xs) @ [m]) D A $$ (m, 0) = reduce_below a (xs@[m]) D (reduce a x D A) $$ (m, 0)"
    by auto
  also have "... = 0"
  proof (rule "2.hyps"[OF ])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm j Aaj])  
    show "distinct xs" using d by auto
    show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
    show "reduce a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
    show "?A' \<in> carrier_mat m n" by auto    
  qed (insert "2.prems", auto)
  finally show ?case .
qed

lemma reduce_below_abs_0_case_m1:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "m\<noteq>a"
  and "D>0"
  shows "reduce_below_abs a (xs @ [m]) D A $$ (m,0) = 0"
  using assms
proof (induct a xs D A arbitrary: A' rule: reduce_below_abs.induct)
  case (1 a D A)
  have A: "A \<in> carrier_mat (m+n) n" using "1" by auto
  have " reduce_below_abs a ([] @ [m]) D A $$ (m, 0) =  reduce_below_abs a [m] D A $$ (m, 0)" by auto
  also have "... = reduce_abs a m D A $$ (m,0)" by auto
  also have "... = 0" by (rule reduce_0[OF A], insert "1.prems", auto)
  finally show ?case .
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note d = "2.prems"(7)
  note xxs_less_m = "2.prems"(8)
  note ma = "2.prems"(9)
  note D_ge0 = "2.prems"(10)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce_abs a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have "reduce_below_abs a ((x # xs) @ [m]) D A $$ (m, 0) = reduce_below_abs a (xs@[m]) D (reduce_abs a x D A) $$ (m, 0)"
    by auto
  also have "... = 0"
  proof (rule "2.hyps"[OF ])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm j Aaj])  
    show "distinct xs" using d by auto
    show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
    show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
    show "?A' \<in> carrier_mat m n" by auto    
  qed (insert "2.prems", auto)
  finally show ?case .
qed



lemma reduce_below_preserves_case_m2:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<in> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "i\<noteq>a" and "i<m+n"
  and "D>0"
  shows "reduce_below a (xs @ [m]) D A $$ (i,0) = reduce_below a xs D A $$ (i,0)"
  using assms
proof (induct a xs D A arbitrary: A' i rule: reduce_below.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note i_set_xxs = "2.prems"(7)
  note d = "2.prems"(8)
  note xxs_less_m = "2.prems"(9)
  note ia = "2.prems"(10)
  note imm = "2.prems"(11)
  note D_ge0 = "2.prems"(12)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) A_def A' add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  show ?case
  proof (cases "i=x")
    case True
    have "reduce_below a ((x # xs) @ [m]) D A $$ (i, 0) 
      = reduce_below a (xs @ [m]) D (reduce a x D A) $$ (i, 0)"
      by auto
    also have "... = (reduce a x D A) $$ (i, 0)"
    proof (rule reduce_below_preserves_case_m[OF _ a j _ _ mn _ _ _ _ _ _ D_ge0])
      let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
      show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      proof (rule matrix_append_rows_eq_if_preserves[OF reduce_ax D1])
        show "\<forall>i\<in>{m..<m + n}. \<forall>ja<n. ?reduce_ax $$ (i, ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" 
        proof (rule+)
          fix i ja assume i: "i \<in> {m..<m + n}" and ja: "ja < n"
          have ja_dc: "ja < dim_col A" and i_dr: "i < dim_row A" using i ja A by auto
          have i_not_a: "i \<noteq> a" using i a by auto
          have i_not_x: "i \<noteq> x" using i xm by auto
          have "?reduce_ax $$ (i,ja) = A $$ (i,ja)" 
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using ja_dc i_dr i_not_a i_not_x by auto 
          also have "... = (if i < dim_row A' then A' $$(i,ja) else (D \<cdot>\<^sub>m (1\<^sub>m n))$$(i-m,ja))"
            by (unfold A_def, rule append_rows_nth[OF A' D1 _ ja], insert A i_dr, simp)
          also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" using i A' by auto
          finally show "?reduce_ax $$ (i,ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" .   
        qed
      qed
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce a x D A $$ (a, 0) \<noteq> 0"
        by (rule reduce_not0[OF A _ _ _ _ Aaj], insert "2.prems", auto)
      show "?A' \<in> carrier_mat m n" by auto
      show "i \<notin> set xs" using True d by auto
      show "i \<noteq> a" using "2.prems" by blast
      show "i < m + n" 
        by (simp add: True trans_less_add1 xm)
      show "i \<noteq> m"  by (simp add: True less_not_refl3 xm)
    qed
    also have "... = 0" unfolding True by (rule reduce_0[OF A _ _ _ _ Aaj], insert "2.prems", auto)
    also have "... = reduce_below a (x # xs) D A $$ (i, 0) "
      unfolding True by (rule reduce_below_0[symmetric], insert "2.prems", auto)
    finally show ?thesis .
  next
    case False
    have "reduce_below a ((x # xs) @ [m]) D A $$ (i, 0) 
      = reduce_below a (xs@[m]) D (reduce a x D A) $$ (i, 0)"
      by auto
    also have "... = reduce_below a xs D (reduce a x D A) $$ (i, 0)"
    proof (rule "2.hyps"[OF _ a j _ _ mn _ _ _ ia imm D_ge0])
      let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
      show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
        by (rule reduce_append_rows_eq[OF A' A_def a xm j Aaj])  
      show "i \<in> set xs" using i_set_xxs False by auto
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce a x D A $$ (a, 0) \<noteq> 0"
        by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
      show "?A' \<in> carrier_mat m n" by auto    
    qed  
    also have "... = reduce_below a (x # xs) D A $$ (i, 0)" by auto
    finally show ?thesis .
  qed
qed


lemma reduce_below_abs_preserves_case_m2:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<in> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "i\<noteq>a" and "i<m+n"
  and "D>0"
  shows "reduce_below_abs a (xs @ [m]) D A $$ (i,0) = reduce_below_abs a xs D A $$ (i,0)"
  using assms
proof (induct a xs D A arbitrary: A' i rule: reduce_below_abs.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note i_set_xxs = "2.prems"(7)
  note d = "2.prems"(8)
  note xxs_less_m = "2.prems"(9)
  note ia = "2.prems"(10)
  note imm = "2.prems"(11)
  note D_ge0 = "2.prems"(12)
  have D0: "D\<noteq>0" using D_ge0 by simp
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce_abs a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) A_def A' add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  show ?case
  proof (cases "i=x")
    case True
    have "reduce_below_abs a ((x # xs) @ [m]) D A $$ (i, 0) 
      = reduce_below_abs a (xs @ [m]) D (reduce_abs a x D A) $$ (i, 0)"
      by auto
    also have "... = (reduce_abs a x D A) $$ (i, 0)"
    proof (rule reduce_below_abs_preserves_case_m[OF _ a j _ _ mn _ _ _ _ _ _ D_ge0])
      let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
      show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      proof (rule matrix_append_rows_eq_if_preserves[OF reduce_ax D1])
        show "\<forall>i\<in>{m..<m + n}. \<forall>ja<n. ?reduce_ax $$ (i, ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" 
        proof (rule+)
          fix i ja assume i: "i \<in> {m..<m + n}" and ja: "ja < n"
          have ja_dc: "ja < dim_col A" and i_dr: "i < dim_row A" using i ja A by auto
          have i_not_a: "i \<noteq> a" using i a by auto
          have i_not_x: "i \<noteq> x" using i xm by auto
          have "?reduce_ax $$ (i,ja) = A $$ (i,ja)" 
            unfolding reduce_alt_def_not0[OF Aaj pquvd] using ja_dc i_dr i_not_a i_not_x by auto 
          also have "... = (if i < dim_row A' then A' $$(i,ja) else (D \<cdot>\<^sub>m (1\<^sub>m n))$$(i-m,ja))"
            by (unfold A_def, rule append_rows_nth[OF A' D1 _ ja], insert A i_dr, simp)
          also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" using i A' by auto
          finally show "?reduce_ax $$ (i,ja) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, ja)" .   
        qed
      qed
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
        by (rule reduce_not0[OF A _ _ _ _ Aaj], insert "2.prems", auto)
      show "?A' \<in> carrier_mat m n" by auto
      show "i \<notin> set xs" using True d by auto
      show "i \<noteq> a" using "2.prems" by blast
      show "i < m + n" 
        by (simp add: True trans_less_add1 xm)
      show "i \<noteq> m"  by (simp add: True less_not_refl3 xm)
    qed
    also have "... = 0" unfolding True by (rule reduce_0[OF A _ _ _ _ Aaj], insert "2.prems", auto)
    also have "... = reduce_below_abs a (x # xs) D A $$ (i, 0) "
      unfolding True by (rule reduce_below_abs_0[symmetric], insert "2.prems", auto)
    finally show ?thesis .
  next
    case False
    have "reduce_below_abs a ((x # xs) @ [m]) D A $$ (i, 0) 
      = reduce_below_abs a (xs@[m]) D (reduce_abs a x D A) $$ (i, 0)"
      by auto
    also have "... = reduce_below_abs a xs D (reduce_abs a x D A) $$ (i, 0)"
    proof (rule "2.hyps"[OF _ a j _ _ mn _ _ _ ia imm D_ge0])
      let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
      show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
        by (rule reduce_append_rows_eq[OF A' A_def a xm j Aaj])  
      show "i \<in> set xs" using i_set_xxs False by auto
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
        by (rule reduce_not0[OF A _ _ j _ Aaj], insert "2.prems", auto)
      show "?A' \<in> carrier_mat m n" by auto    
    qed  
    also have "... = reduce_below_abs a (x # xs) D A $$ (i, 0)" by auto
    finally show ?thesis .
  qed
qed


lemma reduce_below_0_case_m:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<in> set (xs @ [m])" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
  and "D>0"
  shows "reduce_below a (xs @ [m]) D A $$ (i,0) = 0"
proof (cases "i=m")
  case True
  show ?thesis by (unfold True, rule reduce_below_0_case_m1, insert assms, auto)
next
  case False
  have "reduce_below a (xs @ [m]) D A $$ (i,0) = reduce_below a (xs) D A $$ (i,0)"
    by (rule reduce_below_preserves_case_m2[OF A' a j A_def Aaj mn], insert assms False, auto) 
  also have "... = 0" by (rule reduce_below_0, insert assms False, auto)
  finally show ?thesis .
qed


lemma reduce_below_abs_0_case_m:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes "i \<in> set (xs @ [m])" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
  and "D>0"
  shows "reduce_below_abs a (xs @ [m]) D A $$ (i,0) = 0"
proof (cases "i=m")
  case True
  show ?thesis by (unfold True, rule reduce_below_abs_0_case_m1, insert assms, auto)
next
  case False
  have "reduce_below_abs a (xs @ [m]) D A $$ (i,0) = reduce_below_abs a (xs) D A $$ (i,0)"
    by (rule reduce_below_abs_preserves_case_m2[OF A' a j A_def Aaj mn], insert assms False, auto) 
  also have "... = 0" by (rule reduce_below_abs_0, insert assms False, auto)
  finally show ?thesis .
qed


lemma reduce_below_0_case_m_complete:
  assumes A': "A' \<in> carrier_mat m n" and a: "0<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (0,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes i_mn: "i < m+n" and d_xs: "distinct xs" and xs: "\<forall>x \<in> set xs. x < m \<and> 0 < x"
    and ia: "i\<noteq>0"
  and xs_def: "xs = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  and D: "D>0"
  shows "reduce_below 0 (xs @ [m]) D A $$ (i,0) = 0"
proof (cases "i \<in> set (xs @ [m])")
  case True
  show ?thesis by (rule reduce_below_0_case_m[OF A' a j A_def Aaj mn True d_xs xs D])
next
  case False
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by simp
  have "reduce_below 0 (xs @ [m]) D A $$ (i,0) = A $$ (i,0)"    
    by (rule reduce_below_preserves_case_m[OF A' a j A_def Aaj mn _ _ _ _ _ _ D],
        insert i_mn d_xs xs ia False, auto) 
  also have "... = 0"  using False ia i_mn A unfolding xs_def by auto    
  finally show ?thesis .
qed



lemma reduce_below_abs_0_case_m_complete:
  assumes A': "A' \<in> carrier_mat m n" and a: "0<m" and j: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (0,0) \<noteq> 0"
    and mn: "m\<ge>n"
  assumes i_mn: "i < m+n" and d_xs: "distinct xs" and xs: "\<forall>x \<in> set xs. x < m \<and> 0 < x"
    and ia: "i\<noteq>0"
  and xs_def: "xs = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  and D: "D>0"
  shows "reduce_below_abs 0 (xs @ [m]) D A $$ (i,0) = 0"
proof (cases "i \<in> set (xs @ [m])")
  case True
  show ?thesis by (rule reduce_below_abs_0_case_m[OF A' a j A_def Aaj mn True d_xs xs D])
next
  case False
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by simp
  have "reduce_below_abs 0 (xs @ [m]) D A $$ (i,0) = A $$ (i,0)"    
    by (rule reduce_below_abs_preserves_case_m[OF A' a j A_def Aaj mn _ _ _ _ _ _ D],
        insert i_mn d_xs xs ia False, auto) 
  also have "... = 0"  using False ia i_mn A unfolding xs_def by auto    
  finally show ?thesis .
qed


(*Now we take care of the mth row of A*)
lemma reduce_below_invertible_mat_case_m:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and n0: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x" 
    and D0: "D>0"
  shows "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m+n) (m+n) \<and> reduce_below a (xs@[m]) D A = P * A)"
  using assms
proof (induct a xs D A arbitrary: A' rule: reduce_below.induct)
  case (1 a D A)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(m,0))"
    by (metis prod_cases5)
  have D: "D \<cdot>\<^sub>m (1\<^sub>m n) : carrier_mat n n" by auto
  note A' = "1.prems"(1)
  note a = "1.prems"(2)
  note j = "1.prems"(3)
  note A_def = "1.prems"(4)
  note Aaj = "1.prems"(5)
  note mn = "1.prems"(6)  
  note D0 = "1.prems"(9)
  have Am0_D: "A $$ (m, 0) = D"
  proof -
    have "A $$ (m, 0) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (m-m,0)"
      by (smt (z3) "1"(1) "1"(3) "1"(4) D append_rows_nth3 diff_is_0_eq diff_self_eq_0 less_add_same_cancel1)
    also have "... = D" by (simp add: n0)
    finally show ?thesis .
  qed
  have "reduce_below a ([]@[m]) D A = reduce a m D A" by auto
  let ?A = "Matrix.mat (dim_row A) (dim_col A) 
      (\<lambda>(i, k). if i = a then p * A $$ (a, k) + q * A $$ (m, k) else 
        if i = m then u * A $$ (a, k) + v * A $$ (m, k) else A $$ (i, k))"
  let ?xs = "[1..<n]"
  let ?ys = "[1..<n]"  
  have "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) \<and> reduce a m D A = P * A"
    by (rule reduce_invertible_mat_case_m[OF A' D a _ A_def _ Aaj mn n0 pquvd, of ?xs _ _ ?ys],
        insert a D0 Am0_D, auto)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note n0 = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note d = "2.prems"(7)
  note xxs_less_m = "2.prems"(8)
  note D0 = "2.prems"(9)
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  have Am0_D: "A $$ (m, 0) = D"
  proof -
    have "A $$ (m, 0) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (m-m,0)"
      by (smt (z3) "2"(2) "2"(4) "2"(5) D1 append_rows_nth3 
          cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq less_add_same_cancel1)
    also have "... = D" by (simp add: n0)
    finally show ?thesis .
  qed
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have h: "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) 
    \<and> reduce_below a (xs@[m]) D (reduce a x D A) = P * reduce a x D A)"
  proof (rule "2.hyps"[OF _ a n0 _ _ ])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm n0 Aaj])  
    show "reduce a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ n0 _ Aaj], insert "2.prems", auto)
  qed (insert d xxs_less_m mn n0 D0, auto)
  from this obtain P where inv_P: "invertible_mat P" and P: "P \<in> carrier_mat (m + n) (m + n)"
    and rb_Pr: "reduce_below a (xs@[m]) D (reduce a x D A) = P * reduce a x D A" by blast
  have *: "reduce_below a ((x # xs)@[m]) D A = reduce_below a (xs@[m]) D (reduce a x D A)" by simp
  have "\<exists>Q. invertible_mat Q \<and> Q \<in> carrier_mat (m+n) (m+n) \<and> (reduce a x D A) = Q * A"
    by (rule reduce_invertible_mat[OF A' a n0 xm _ A_def Aaj _ mn D0], insert xxs_less_m, auto)
  from this obtain Q where inv_Q: "invertible_mat Q" and Q: "Q \<in> carrier_mat (m + n) (m + n)"
    and r_QA: "reduce a x D A = Q * A" by blast
  have "invertible_mat (P*Q)" using inv_P inv_Q P Q invertible_mult_JNF by blast
  moreover have "P * Q \<in> carrier_mat (m+n) (m+n)" using P Q by auto
  moreover have "reduce_below a ((x # xs)@[m]) D A = (P*Q) * A" 
    by (smt P Q * assoc_mult_mat carrier_matD(1) carrier_mat_triv index_mult_mat(2) 
        r_QA rb_Pr reduce_preserves_dimensions(1))
  ultimately show ?case by blast
qed




(*Now we take care of the mth row of A*)
lemma reduce_below_abs_invertible_mat_case_m:
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m" and n0: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and Aaj: "A $$ (a,0) \<noteq> 0"
    and mn: "m\<ge>n" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x" 
    and D0: "D>0"
  shows "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m+n) (m+n) \<and> reduce_below_abs a (xs@[m]) D A = P * A)"
  using assms
proof (induct a xs D A arbitrary: A' rule: reduce_below_abs.induct)
  case (1 a D A)
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(m,0))"
    by (metis prod_cases5)
  have D: "D \<cdot>\<^sub>m (1\<^sub>m n) : carrier_mat n n" by auto
  note A' = "1.prems"(1)
  note a = "1.prems"(2)
  note j = "1.prems"(3)
  note A_def = "1.prems"(4)
  note Aaj = "1.prems"(5)
  note mn = "1.prems"(6)  
  note D0 = "1.prems"(9)
  have Am0_D: "A $$ (m, 0) = D"
  proof -
    have "A $$ (m, 0) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (m-m,0)"
      by (smt (z3) "1"(1) "1"(3) "1"(4) D append_rows_nth3 diff_is_0_eq diff_self_eq_0 less_add_same_cancel1)
    also have "... = D" by (simp add: n0)
    finally show ?thesis .
  qed
  have "reduce_below_abs a ([]@[m]) D A = reduce_abs a m D A" by auto
  let ?A = "Matrix.mat (dim_row A) (dim_col A) 
      (\<lambda>(i, k). if i = a then p * A $$ (a, k) + q * A $$ (m, k) else 
        if i = m then u * A $$ (a, k) + v * A $$ (m, k) else A $$ (i, k))"
  let ?xs = "filter (\<lambda>i. D < \<bar>?A $$ (a, i)\<bar>) [0..<n]"
  let ?ys = "filter (\<lambda>i. D < \<bar>?A $$ (m, i)\<bar>) [0..<n]"  
  have "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) \<and> reduce_abs a m D A = P * A"
    by (rule reduce_abs_invertible_mat_case_m[OF A' D a _ A_def _ Aaj mn n0 pquvd, of ?xs _ _ ?ys],
        insert a D0 Am0_D, auto)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A' = "2.prems"(1)
  note a = "2.prems"(2)
  note n0 = "2.prems"(3)
  note A_def = "2.prems"(4)
  note Aaj = "2.prems"(5)
  note mn = "2.prems"(6)
  note d = "2.prems"(7)
  note xxs_less_m = "2.prems"(8)
  note D0 = "2.prems"(9)
  have A: "A \<in> carrier_mat (m+n) n" using A' mn A_def by auto
  have xm: "x < m"  using "2.prems" by auto
  have D1: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" by (simp add: mn)
  have Am0_D: "A $$ (m, 0) = D"
  proof -
    have "A $$ (m, 0) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (m-m,0)"
      by (smt (z3) "2"(2) "2"(4) "2"(5) D1 append_rows_nth3 
          cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq less_add_same_cancel1)
    also have "... = D" by (simp add: n0)
    finally show ?thesis .
  qed
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce_abs a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat (m + n) n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have h: "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) 
    \<and> reduce_below_abs a (xs@[m]) D (reduce_abs a x D A) = P * reduce_abs a x D A)"
  proof (rule "2.hyps"[OF _ a n0 _ _ ])
    let ?A' = "mat_of_rows n (map (Matrix.row ?reduce_ax) [0..<m])"
    show "reduce_abs a x D A = ?A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
      by (rule reduce_append_rows_eq[OF A' A_def a xm n0 Aaj])  
    show "reduce_abs a x D A $$ (a, 0) \<noteq> 0"
      by (rule reduce_not0[OF A _ _ n0 _ Aaj], insert "2.prems", auto)
  qed (insert d xxs_less_m mn n0 D0, auto)
  from this obtain P where inv_P: "invertible_mat P" and P: "P \<in> carrier_mat (m + n) (m + n)"
    and rb_Pr: "reduce_below_abs a (xs@[m]) D (reduce_abs a x D A) = P * reduce_abs a x D A" by blast
  have *: "reduce_below_abs a ((x # xs)@[m]) D A = reduce_below_abs a (xs@[m]) D (reduce_abs a x D A)" by simp
  have "\<exists>Q. invertible_mat Q \<and> Q \<in> carrier_mat (m+n) (m+n) \<and> (reduce_abs a x D A) = Q * A"
    by (rule reduce_abs_invertible_mat[OF A' a n0 xm _ A_def Aaj _ mn D0], insert xxs_less_m, auto)
  from this obtain Q where inv_Q: "invertible_mat Q" and Q: "Q \<in> carrier_mat (m + n) (m + n)"
    and r_QA: "reduce_abs a x D A = Q * A" by blast
  have "invertible_mat (P*Q)" using inv_P inv_Q P Q invertible_mult_JNF by blast
  moreover have "P * Q \<in> carrier_mat (m+n) (m+n)" using P Q by auto
  moreover have "reduce_below_abs a ((x # xs)@[m]) D A = (P*Q) * A" 
    by (smt P Q * assoc_mult_mat carrier_matD(1) carrier_mat_triv index_mult_mat(2) 
        r_QA rb_Pr reduce_preserves_dimensions(3))
  ultimately show ?case by blast
qed

end

hide_const (open) C

text \<open>This lemma will be very important, since it will allow us to prove that the output
matrix is in echelon form.\<close>

lemma echelon_form_four_block_mat:
  assumes A: "A \<in> carrier_mat 1 1"
  and B: "B \<in> carrier_mat 1 (n-1)"
  and D: "D \<in> carrier_mat (m-1) (n-1)"
  and H_def: "H = four_block_mat A B (0\<^sub>m (m-1) 1) D"
  and A00: "A $$ (0,0) \<noteq> 0"
  and e_D: "echelon_form_JNF D"
  and m: "m>0" and n: "n>0"
shows "echelon_form_JNF H"
proof (rule echelon_form_JNF_intro)
  have H: "H \<in> carrier_mat m n"
    by (metis H_def Num.numeral_nat(7) A D m n carrier_matD carrier_mat_triv
        index_mat_four_block(2,3) linordered_semidom_class.add_diff_inverse not_less_eq)
  have Hij_Dij: "H $$ (i+1,j+1) = D $$ (i,j)" if i: "i<m-1" and j: "j<n-1" for i j
  proof -
    have "H $$ (i+1,j+1) =  (if (i+1) < dim_row A then if (j+1) < dim_col A then A $$ ((i+1), (j+1)) 
    else B $$ ((i+1), (j+1) - dim_col A) else if (j+1) < dim_col A then 
    (0\<^sub>m (m-1) 1) $$ ((i+1) - dim_row A, (j+1)) else D $$ ((i+1) - dim_row A, (j+1) - dim_col A))"
      unfolding H_def by (rule index_mat_four_block, insert A D i j, auto)
    also have "... = D $$ ((i+1) - dim_row A, (j+1) - dim_col A)" using A D i j B m n by auto
    also have "... = D $$ (i,j)" using A by auto
    finally show ?thesis .
  qed
  have Hij_Dij':  "H $$ (i,j) = D $$ (i-1,j-1)" 
    if i: "i<m" and j: "j<n" and i0: "i>0" and j0: "j>0" for i j
    by (metis (no_types, lifting) H H_def Num.numeral_nat(7) A carrier_matD 
        index_mat_four_block less_Suc0 less_not_refl3 i j i0 j0)
  have Hi0: "H$$(i,0) = 0" if i: "i\<in>{1..<m}" for i
  proof -
    have "H $$ (i,0) =  (if i < dim_row A then if 0 < dim_col A then A $$ (i, 0) 
      else B $$ (i, 0 - dim_col A) else if 0 < dim_col A then 
      (0\<^sub>m (m-1) 1) $$ (i - dim_row A, 0) else D $$ (i - dim_row A, 0 - dim_col A))"
      unfolding H_def by (rule index_mat_four_block, insert A D i, auto)
    also have "... = (0\<^sub>m (m-1) 1) $$ (i - dim_row A, 0)" using A D i m n by auto
    also have "... = 0" using i A n by auto
    finally show ?thesis .
  qed
  have A00_H00: "A $$ (0,0) = H $$ (0,0)" unfolding H_def using A by auto
  have "is_zero_row_JNF j H" if zero_iH: "is_zero_row_JNF i H" and ij: "i < j" and j: "j < dim_row H"
    for i j 
  proof -
    have "\<not> is_zero_row_JNF 0 H" unfolding is_zero_row_JNF_def using m n H A00 A00_H00 by auto
    hence i_not0: "i\<noteq>0" using zero_iH by meson
    have "is_zero_row_JNF (i-1) D" using zero_iH i_not0 Hij_Dij m n D H unfolding is_zero_row_JNF_def
      by (auto, smt (z3) Suc_leI carrier_matD(1) le_add_diff_inverse2 Hij_Dij One_nat_def Suc_pred carrier_matD(1) j le_add_diff_inverse2
          less_diff_conv less_imp_add_positive plus_1_eq_Suc that(2) trans_less_add1)
    hence "is_zero_row_JNF (j-1) D" using ij e_D D j m i_not0 unfolding echelon_form_JNF_def
      by (auto, smt H Nat.lessE Suc_pred carrier_matD(1) diff_Suc_1 diff_Suc_less order.strict_trans)
    thus ?thesis
      by (smt A H H_def Hi0 D atLeastLessThan_iff carrier_matD index_mat_four_block(1)
          is_zero_row_JNF_def le_add1 less_one linordered_semidom_class.add_diff_inverse not_less_eq
          plus_1_eq_Suc ij j zero_order(3))
  qed
  thus "\<forall>i<dim_row H. is_zero_row_JNF i H \<longrightarrow> \<not> (\<exists>j<dim_row H. i < j \<and> \<not> is_zero_row_JNF j H)"
    by blast
  have "(LEAST n. H $$ (i, n) \<noteq> 0) < (LEAST n. H $$ (j, n) \<noteq> 0)"
    if ij: "i < j" and j: "j < dim_row H" and not_zero_iH: "\<not> is_zero_row_JNF i H" 
    and not_zero_jH: "\<not> is_zero_row_JNF j H" for i j
  proof (cases "i = 0")
    case True
    have "(LEAST n. H $$ (i, n) \<noteq> 0) = 0" unfolding True using A00_H00 A00 by auto
    then show ?thesis
      by (metis (mono_tags) H Hi0 LeastI True atLeastLessThan_iff carrier_matD(1) 
          is_zero_row_JNF_def leI less_one not_gr0 ij j not_zero_jH)
  next
    case False note i_not0 = False
    let ?least_H = "(LEAST n. H $$ (i, n) \<noteq> 0)"
    let ?least_Hj = "(LEAST n. H $$ (j, n) \<noteq> 0)"

    have least_not0: "(LEAST n. H $$ (i, n) \<noteq> 0) \<noteq> 0" 
    proof -
      have "\<exists>n. H $$ (i, n) \<noteq> 0 \<and> H $$ (i, 0) = 0"
        by (metis (no_types) False H Hi0 Num.numeral_nat(7) atLeastLessThan_iff carrier_matD(1)
            is_zero_row_JNF_def j nat_LEAST_True nat_neq_iff not_less_Least not_less_eq order.strict_trans
            ij not_zero_iH wellorder_Least_lemma(1) wellorder_Least_lemma(2))
      then show ?thesis
        by (metis (mono_tags, lifting) LeastI_ex)
    qed
    have least_not0j: "(LEAST n. H $$ (j, n) \<noteq> 0) \<noteq> 0"
    proof -
      have "\<exists>n. H $$ (j, 0) = 0 \<and> H $$ (j, n) \<noteq> 0"
        by (metis (no_types) H Hi0 LeastI_ex Num.numeral_nat(7) atLeastLessThan_iff carrier_matD(1)
            is_zero_row_JNF_def linorder_neqE_nat not_gr0 not_less_Least not_less_eq order_trans_rules(19)
            ij j not_zero_jH wellorder_Least_lemma(2))
      then show ?thesis
        by (metis (mono_tags, lifting) LeastI_ex)
    qed
    have least_n: "?least_H<n"
      by (smt H carrier_matD(2) dual_order.strict_trans is_zero_row_JNF_def 
          not_less_Least not_less_iff_gr_or_eq not_zero_iH)
    have Hil: "H $$ (i,?least_H) \<noteq> 0" and ln':"(\<forall>n'. (H $$ (i, n') \<noteq> 0) \<longrightarrow> ?least_H \<le> n')" 
      by (metis (mono_tags, lifting) is_zero_row_JNF_def that(3) wellorder_Least_lemma)+
    have Hil_Dil: "H $$ (i,?least_H) = D $$ (i-1,?least_H - 1)"      
    proof -
      have "H $$ (i,?least_H) = (if i < dim_row A then if ?least_H < dim_col A then A $$ (i, ?least_H) 
      else B $$ (i, ?least_H - dim_col A) else if ?least_H < dim_col A then 
      (0\<^sub>m (m-1) 1) $$ (i - dim_row A, ?least_H) else D $$ (i - dim_row A, ?least_H - dim_col A))"
        unfolding H_def
        by (rule index_mat_four_block, insert False j ij H A D n least_n, auto simp add: H_def)
      also have "... = D $$ (i - 1, ?least_H - 1)"
        using False j ij H A D n least_n B Hi0 Hil by auto
      finally show ?thesis .
    qed
    have not_zero_iD: "\<not> is_zero_row_JNF (i-1) D" 
      by (metis (no_types, lifting) Hil Hil_Dil D carrier_matD(2) is_zero_row_JNF_def le_add1 
          le_add_diff_inverse2 least_n least_not0 less_diff_conv less_one
          linordered_semidom_class.add_diff_inverse)
    have not_zero_jD: "\<not> is_zero_row_JNF (j-1) D"
      by (smt H Hij_Dij' One_nat_def Suc_pred D m carrier_matD diff_Suc_1 ij is_zero_row_JNF_def j
          least_not0j less_Suc0 less_Suc_eq_0_disj less_one neq0_conv not_less_Least not_less_eq
          plus_1_eq_Suc not_zero_jH zero_order(3))
    have "?least_H - 1 = (LEAST n. D $$ (i-1, n) \<noteq> 0 \<and> n<dim_col D)"
    proof (rule Least_equality[symmetric], rule)
      show "D $$ (i - 1, ?least_H - 1) \<noteq> 0" using Hil Hil_Dil by auto
      show "(LEAST n. H $$ (i, n) \<noteq> 0) - 1 < dim_col D" using least_n least_not0 H D n by auto
      fix n' assume "D $$ (i - 1, n') \<noteq> 0 \<and> n' < dim_col D" 
      hence Di1n'1: "D $$ (i - 1, n') \<noteq> 0" and n': "n' < dim_col D" by auto
      have "(LEAST n. H $$ (i, n) \<noteq> 0) \<le> n' + 1"
      proof (rule Least_le)
        have "H $$ (i, n'+1) = D $$ (i -1, (n'+1)-1)"
          by (rule Hij_Dij', insert i_not0 False H A ij j n' D, auto)
        thus Hin': "H $$ (i, n'+1) \<noteq> 0" using False Di1n'1 Hij_Dij' by auto
      qed
      thus  "(LEAST n. H $$ (i, n) \<noteq> 0) -1 \<le> n'" using least_not0 by auto
    qed
    also have "... = (LEAST n. D $$ (i-1, n) \<noteq> 0)"
    proof (rule Least_equality)
      have "D $$ (i - 1, LEAST n. D $$ (i - 1, n) \<noteq> 0) \<noteq> 0" 
        by (metis (mono_tags, lifting) Hil Hil_Dil LeastI_ex)
      moreover have leastD: "(LEAST n. D $$ (i - 1, n) \<noteq> 0) < dim_col D"
        by (smt dual_order.strict_trans is_zero_row_JNF_def linorder_neqE_nat
            not_less_Least not_zero_iD) 
      ultimately show "D $$ (i - 1, LEAST n. D $$ (i - 1, n) \<noteq> 0) \<noteq> 0 
        \<and> (LEAST n. D $$ (i - 1, n) \<noteq> 0) < dim_col D" by simp  
      fix y assume "D $$ (i - 1, y) \<noteq> 0 \<and> y < dim_col D" 
      thus "(LEAST n. D $$ (i - 1, n) \<noteq> 0) \<le> y" by (meson wellorder_Least_lemma(2))
    qed
    finally have leastHi_eq: "?least_H - 1 = (LEAST n. D $$ (i-1, n) \<noteq> 0)" .
    have least_nj: "?least_Hj<n"
      by (smt H carrier_matD(2) dual_order.strict_trans is_zero_row_JNF_def 
          not_less_Least not_less_iff_gr_or_eq not_zero_jH)
    have Hjl: "H $$ (j,?least_Hj) \<noteq> 0" and ln':"(\<forall>n'. (H $$ (j, n') \<noteq> 0) \<longrightarrow> ?least_Hj \<le> n')" 
      by (metis (mono_tags, lifting) is_zero_row_JNF_def not_zero_jH wellorder_Least_lemma)+
    have Hjl_Djl: "H $$ (j,?least_Hj) = D $$ (j-1,?least_Hj - 1)"      
    proof -
      have "H $$ (j,?least_Hj) = (if j < dim_row A then if ?least_Hj < dim_col A then A $$ (j, ?least_Hj) 
      else B $$ (j, ?least_Hj - dim_col A) else if ?least_Hj < dim_col A then 
      (0\<^sub>m (m-1) 1) $$ (j - dim_row A, ?least_Hj) else D $$ (j - dim_row A, ?least_Hj - dim_col A))"
        unfolding H_def
        by (rule index_mat_four_block, insert False j ij H A D n least_nj, auto simp add: H_def)
      also have "... = D $$ (j - 1, ?least_Hj - 1)"
        using False j ij H A D n least_n B Hi0 Hjl by auto
      finally show ?thesis .
    qed
    have "(LEAST n. H $$ (j, n) \<noteq> 0) - 1 = (LEAST n. D $$ (j-1, n) \<noteq> 0 \<and> n<dim_col D)"
    proof (rule Least_equality[symmetric], rule)
      show "D $$ (j - 1, ?least_Hj - 1) \<noteq> 0" using Hil Hil_Dil
        by (smt H Hij_Dij' LeastI_ex carrier_matD is_zero_row_JNF_def j least_not0j 
            linorder_neqE_nat not_gr0 not_less_Least order.strict_trans ij not_zero_jH)
      show "(LEAST n. H $$ (j, n) \<noteq> 0) - 1 < dim_col D" using least_nj least_not0j H D n by auto
      fix n' assume "D $$ (j - 1, n') \<noteq> 0 \<and> n' < dim_col D" 
      hence Di1n'1: "D $$ (j - 1, n') \<noteq> 0" and n': "n' < dim_col D" by auto
      have "(LEAST n. H $$ (j, n) \<noteq> 0) \<le> n' + 1"
      proof (rule Least_le)
        have "H $$ (j, n'+1) = D $$ (j -1, (n'+1)-1)"
          by (rule Hij_Dij', insert i_not0 False H A ij j n' D, auto)
        thus Hin': "H $$ (j, n'+1) \<noteq> 0" using False Di1n'1 Hij_Dij' by auto
      qed
      thus  "(LEAST n. H $$ (j, n) \<noteq> 0) -1 \<le> n'" using least_not0 by auto
    qed
    also have "... = (LEAST n. D $$ (j-1, n) \<noteq> 0)"
    proof (rule Least_equality)
      have "D $$ (j - 1, LEAST n. D $$ (j - 1, n) \<noteq> 0) \<noteq> 0" 
        by (metis (mono_tags, lifting) Hjl Hjl_Djl LeastI_ex)
      moreover have leastD: "(LEAST n. D $$ (j - 1, n) \<noteq> 0) < dim_col D"
        by (smt dual_order.strict_trans is_zero_row_JNF_def linorder_neqE_nat
            not_less_Least not_zero_jD) 
      ultimately show "D $$ (j - 1, LEAST n. D $$ (j - 1, n) \<noteq> 0) \<noteq> 0 
        \<and> (LEAST n. D $$ (j - 1, n) \<noteq> 0) < dim_col D" by simp  
      fix y assume "D $$ (j - 1, y) \<noteq> 0 \<and> y < dim_col D" 
      thus "(LEAST n. D $$ (j - 1, n) \<noteq> 0) \<le> y" by (meson wellorder_Least_lemma(2))
    qed
    finally have leastHj_eq: "(LEAST n. H $$ (j, n) \<noteq> 0) - 1 = (LEAST n. D $$ (j-1, n) \<noteq> 0)" .
    have ij': "i-1 < j-1" using ij False by auto
    have "j-1 < dim_row D "  using D H ij j by auto
    hence "(LEAST n. D $$ (i-1, n) \<noteq> 0) < (LEAST n. D $$ (j-1, n) \<noteq> 0)" 
      using e_D echelon_form_JNF_def ij' not_zero_jD order.strict_trans by blast    
    thus ?thesis using leastHj_eq leastHi_eq by auto
  qed
  thus "\<forall>i j. i < j \<and> j < dim_row H \<and> \<not> is_zero_row_JNF i H \<and> \<not> is_zero_row_JNF j H 
  \<longrightarrow> (LEAST n. H $$ (i, n) \<noteq> 0) < (LEAST n. H $$ (j, n) \<noteq> 0)" by blast    
qed

context mod_operation
begin


lemma reduce_below:
  assumes "A \<in> carrier_mat m n"
  shows "reduce_below a xs D A \<in> carrier_mat m n" 
  using assms 
  by (induct a xs D A rule: reduce_below.induct, auto simp add: Let_def euclid_ext2_def) 

lemma reduce_below_preserves_dimensions:
 shows [simp]: "dim_row (reduce_below a xs D A) = dim_row A" 
    and [simp]: "dim_col (reduce_below a xs D A) = dim_col A"
  using reduce_below[of A "dim_row A" "dim_col A"] by auto


lemma reduce_below_abs:
  assumes "A \<in> carrier_mat m n"
  shows "reduce_below_abs a xs D A \<in> carrier_mat m n" 
  using assms 
  by (induct a xs D A rule: reduce_below_abs.induct, auto simp add: Let_def euclid_ext2_def) 

lemma reduce_below_abs_preserves_dimensions:
 shows [simp]: "dim_row (reduce_below_abs a xs D A) = dim_row A" 
    and [simp]: "dim_col (reduce_below_abs a xs D A) = dim_col A"
  using reduce_below_abs[of A "dim_row A" "dim_col A"] by auto


lemma FindPreHNF_1xn:
 assumes A: "A \<in> carrier_mat m n" and "m<2 \<or> n = 0"
 shows "FindPreHNF abs_flag D A \<in> carrier_mat m n" using assms by auto

lemma FindPreHNF_mx1:
 assumes A: "A \<in> carrier_mat m n" and "m\<ge>2" and "n \<noteq> 0" "n<2"
 shows "FindPreHNF abs_flag D A \<in> carrier_mat m n"
proof (cases "abs_flag")
  case True
  let ?nz = "(filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<m])"
  have "FindPreHNF abs_flag D A =  (let non_zero_positions = filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [Suc 0..<m]
     in reduce_below_abs 0 non_zero_positions D (if A $$ (0, 0) \<noteq> 0 then A else 
  let i = non_zero_positions ! 0 in swaprows 0 i A))" 
    using assms True by auto
  also have "... =  reduce_below_abs 0 ?nz D (if A $$ (0, 0) \<noteq> 0 then A 
  else let i = ?nz ! 0 in swaprows 0 i A)" unfolding Let_def by auto
  also have "... \<in> carrier_mat m n" using A by auto
  finally show ?thesis .  
next
  case False
  let ?nz = "(filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<m])"
  have "FindPreHNF abs_flag D A =  (let non_zero_positions = filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [Suc 0..<m]
     in reduce_below 0 non_zero_positions D (if A $$ (0, 0) \<noteq> 0 then A else 
  let i = non_zero_positions ! 0 in swaprows 0 i A))" 
    using assms False by auto
  also have "... =  reduce_below 0 ?nz D (if A $$ (0, 0) \<noteq> 0 then A 
  else let i = ?nz ! 0 in swaprows 0 i A)" unfolding Let_def by auto
  also have "... \<in> carrier_mat m n" using A by auto
  finally show ?thesis .
qed
  

lemma FindPreHNF_mxn2:
 assumes A: "A \<in> carrier_mat m n" and m: "m\<ge>2" and n: "n\<ge>2"
 shows "FindPreHNF abs_flag D A \<in> carrier_mat m n" 
using assms
proof (induct abs_flag D A arbitrary: m n rule: FindPreHNF.induct)
  case (1 abs_flag D A)
  note A = "1.prems"(1)
  note m = "1.prems"(2)
  note n = "1.prems"(3)
  define non_zero_positions where "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  define A' where "A' = (if A $$ (0, 0) \<noteq> 0 then A else let i = non_zero_positions ! 0 in swaprows 0 i A)"
  define Reduce where [simp]: "Reduce = (if abs_flag then reduce_below_abs else reduce_below)"
  obtain A'_UL A'_UR A'_DL A'_DR where A'_split: "(A'_UL, A'_UR, A'_DL, A'_DR) 
    = split_block (Reduce 0 non_zero_positions D (make_first_column_positive A')) 1 1"     
    by (metis prod_cases4)
  define sub_PreHNF where "sub_PreHNF = FindPreHNF abs_flag D A'_DR"
  have A': "A' \<in> carrier_mat m n" unfolding A'_def using A by auto
  have A'_DR: "A'_DR \<in> carrier_mat (m -1) (n-1)"
    by (cases abs_flag; rule split_block(4)[OF A'_split[symmetric]], insert Reduce_def A A' m n, auto)
  have sub_PreHNF: "sub_PreHNF \<in> carrier_mat (m - 1) (n-1)"
  proof (cases "m-1<2")
    case True
    show ?thesis using A'_DR True unfolding sub_PreHNF_def by auto
  next
    case False note m' = False
    show ?thesis
    proof (cases "n-1<2")
      case True
      show ?thesis 
        unfolding sub_PreHNF_def by (rule FindPreHNF_mx1[OF A'_DR _ _ True], insert n m', auto)
    next
      case False
      show ?thesis
        by (unfold sub_PreHNF_def, rule "1.hyps"
            [of m n, OF _ _ _ non_zero_positions_def A'_def Reduce_def _ A'_split _ _ _ A'_DR],
            insert A False n m' Reduce_def, auto)
    qed  
  qed      
  have A'_UL: "A'_UL \<in> carrier_mat 1 1"
    by (cases abs_flag; rule split_block(1)[OF A'_split[symmetric], of "m-1" "n-1"], insert n m A', auto) 
  have A'_UR: "A'_UR \<in> carrier_mat 1 (n-1)"
    by (cases abs_flag; rule split_block(2)[OF A'_split[symmetric], of "m-1"], insert n m A', auto)
  have A'_DL: "A'_DL \<in> carrier_mat (m - 1) 1"
     by (cases abs_flag; rule split_block(3)[OF A'_split[symmetric], of _ "n-1"], insert n m A', auto)
  have *: "(dim_col A = 0) = False" using 1(2-) by auto
  have FindPreHNF_as_fbm: "FindPreHNF abs_flag D A = four_block_mat A'_UL A'_UR A'_DL sub_PreHNF" 
    unfolding FindPreHNF.simps[of abs_flag D A] using A'_split m n A
    unfolding Let_def sub_PreHNF_def  A'_def non_zero_positions_def * 
    apply (cases abs_flag)
    by (smt (z3) Reduce_def carrier_matD(1) carrier_matD(2) linorder_not_less prod.simps(2))+
  also have "... \<in> carrier_mat m n"
    by (smt m A'_UL One_nat_def add.commute carrier_matD carrier_mat_triv index_mat_four_block(2,3) 
        le_add_diff_inverse2 le_eq_less_or_eq lessI n nat_SN.compat numerals(2) sub_PreHNF)  
  finally show ?case .
qed


lemma FindPreHNF:
 assumes A: "A \<in> carrier_mat m n"
 shows "FindPreHNF abs_flag D A \<in> carrier_mat m n" 
  using assms FindPreHNF_mxn2[OF A] FindPreHNF_mx1[OF A] FindPreHNF_1xn[OF A]
  using linorder_not_less by blast
end

lemma make_first_column_positive_append_id:
 assumes A': "A' \<in> carrier_mat m n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
  and D0: "D>0"
  and n0: "0<n"
  shows "make_first_column_positive A 
  = mat_of_rows n (map (Matrix.row (make_first_column_positive A)) [0..<m]) @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
proof (rule matrix_append_rows_eq_if_preserves)
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  thus "make_first_column_positive A \<in> carrier_mat (m + n) n" by auto
  have "make_first_column_positive A $$ (i, j) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, j)"
    if j: "j<n" and i: "i \<in> {m..<m + n}" for i j
  proof -
    have i_mn: "i<m+n" using i by auto
    have "A $$ (i,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, 0)" unfolding A_def
      by (smt A append_rows_def assms(1) assms(2) atLeastLessThan_iff carrier_matD 
          index_mat_four_block less_irrefl_nat nat_SN.compat j i n0)
    also have "... \<ge> 0" using D0 mult_not_zero that(2) by auto
    finally have Ai0: "A$$(i,0)\<ge>0" .
    have "make_first_column_positive A $$ (i, j) = A$$(i,j)"
      using make_first_column_positive_works[OF A i_mn n0] j Ai0 by auto
    also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, j)" unfolding A_def
      by (smt A append_rows_def A' A_def atLeastLessThan_iff carrier_matD 
          index_mat_four_block less_irrefl_nat nat_SN.compat i j)
    finally show ?thesis .
  qed
  thus "\<forall>i\<in>{m..<m + n}. \<forall>j<n. make_first_column_positive A $$ (i, j) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i - m, j)"
    by simp
qed (auto)


lemma A'_swaprows_invertible_mat:
  fixes A::"int mat"
  assumes A: "A\<in>carrier_mat m n"
  assumes A'_def: "A' = (if A $$ (0, 0) \<noteq> 0 then A else let i = non_zero_positions ! 0 in swaprows 0 i A)"
  and nz_def: "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  and nz_empty: "A$$(0,0) =0 \<Longrightarrow> non_zero_positions \<noteq> []"
  and m0: "0<m"
shows "\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> A' = P * A"
proof (cases "A$$(0,0) \<noteq> 0")
  case True
  then show ?thesis
    by (metis A A'_def invertible_mat_one left_mult_one_mat one_carrier_mat)
next
  case False
  have nz_empty: "non_zero_positions \<noteq> []" using nz_empty False by simp
  let ?i = "non_zero_positions ! 0"
  let ?M = "(swaprows_mat m 0 ?i) :: int mat"
  have i_set_nz: "?i \<in> set (non_zero_positions)" using nz_empty by auto
  have im: "?i < m" using A nz_def i_set_nz by auto
  have i_not0: "?i \<noteq> 0" using A nz_def i_set_nz by auto
  have "A' = swaprows 0 ?i A" using False A'_def by simp
  also have "... = ?M * A"
    by (rule swaprows_mat[OF A], insert nz_def nz_empty False A m0 im, auto) 
  finally have 1: "A' = ?M * A" .
  have 2: "?M \<in> carrier_mat m m" by auto
  have "Determinant.det ?M = - 1"
    by (rule det_swaprows_mat[OF m0 im i_not0[symmetric]])
  hence 3: "invertible_mat ?M" using invertible_iff_is_unit_JNF[OF 2] by auto  
  show ?thesis using 1 2 3 by blast
qed

lemma swaprows_append_id:
 assumes A': "A' \<in> carrier_mat m n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
  and i:"i<m"
  shows "swaprows 0 i A 
  = mat_of_rows n (map (Matrix.row (swaprows 0 i A)) [0..<m]) @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
proof (rule matrix_append_rows_eq_if_preserves)
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  show swap: "swaprows 0 i A \<in> carrier_mat (m + n) n" by (simp add: A)
  have "swaprows 0 i A $$ (ia, j) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (ia - m, j)"
    if ia: "ia \<in> {m..<m + n}" and j: "j<n" for ia j
  proof -
    have "swaprows 0 i A $$ (ia, j) = A $$ (ia,j)" using i ia j A by auto
    also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (ia - m, j)" 
      by (smt A append_rows_def A' A_def atLeastLessThan_iff carrier_matD 
          index_mat_four_block less_irrefl_nat nat_SN.compat ia j)
    finally show "swaprows 0 i A $$ (ia, j) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (ia - m, j)" .
  qed
  thus "\<forall>ia\<in>{m..<m + n}. \<forall>j<n. swaprows 0 i A $$ (ia, j) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (ia - m, j)" by simp
qed (simp)



lemma non_zero_positions_xs_m:
  fixes A::"'a::comm_ring_1 mat"
  assumes A_def: "A = A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A': "A' \<in> carrier_mat m n" 
  and nz_def: "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  and m0: "0<m" and n0: "0<n"
  and D0: "D \<noteq> 0"
shows "\<exists>xs. non_zero_positions = xs @ [m] \<and> distinct xs \<and> (\<forall>x\<in>set xs. x < m \<and> 0 < x)"
proof -  
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  let ?xs = "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]"
  have l_rw: "[1..<dim_row A] = [1..<m+1]@[m+1..<dim_row A]" using A m0 n0
    by (auto, metis Suc_leI less_add_same_cancel1 upt_add_eq_append upt_conv_Cons)
  have f0: "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([m+1..<dim_row A]) = []"
  proof (rule filter_False) 
    have "A $$ (i,0) = 0" if i: "i\<in>set [m + 1..<dim_row A]" for i
    proof -
      have "A $$ (i,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i-m,0)"
        by (rule append_rows_nth3[OF A' _ A_def _ _ n0], insert i A, auto)
      also have "... = 0" using i A by auto
      finally show ?thesis .        
    qed
    thus "\<forall>x\<in>set [m + 1..<dim_row A]. \<not> A $$ (x, 0) \<noteq> 0" by blast
  qed
  have fm: "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [m] = [m]"
  proof -
    have "A $$ (m, 0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m,0)"
      by (rule append_rows_nth3[OF A' _ A_def _ _ n0], insert n0, auto)
    also have "... = D" using m0 n0 by auto
    finally show ?thesis using D0 by auto
  qed
  have "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([1..<m+1]@[m+1..<dim_row A])"
    using nz_def l_rw by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m+1] @ filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([m+1..<dim_row A])"
    by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m+1]" using f0 by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([1..<m]@[m])" using m0 by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m] @ [m]" using fm by auto
  finally have "non_zero_positions = ?xs @ [m]" .
  moreover have "distinct ?xs" by auto
  moreover have "(\<forall>x\<in>set ?xs. x < m \<and> 0 < x)" by auto
  ultimately show ?thesis by blast
qed




lemma non_zero_positions_xs_m':
  fixes A::"'a::comm_ring_1 mat"
  assumes A_def: "A = A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A': "A' \<in> carrier_mat m n" 
  and nz_def: "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  and m0: "0<m" and n0: "0<n"
  and D0: "D \<noteq> 0"
shows "non_zero_positions = (filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]) @ [m] 
  \<and> distinct (filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]) 
  \<and> (\<forall>x\<in>set (filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]). x < m \<and> 0 < x)"
proof -  
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  let ?xs = "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]"
  have l_rw: "[1..<dim_row A] = [1..<m+1]@[m+1..<dim_row A]" using A m0 n0
    by (auto, metis Suc_leI less_add_same_cancel1 upt_add_eq_append upt_conv_Cons)
  have f0: "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([m+1..<dim_row A]) = []"
  proof (rule filter_False) 
    have "A $$ (i,0) = 0" if i: "i\<in>set [m + 1..<dim_row A]" for i
    proof -
      have "A $$ (i,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i-m,0)"
        by (rule append_rows_nth3[OF A' _ A_def _ _ n0], insert i A, auto)
      also have "... = 0" using i A by auto
      finally show ?thesis .        
    qed
    thus "\<forall>x\<in>set [m + 1..<dim_row A]. \<not> A $$ (x, 0) \<noteq> 0" by blast
  qed
  have fm: "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [m] = [m]"
  proof -
    have "A $$ (m, 0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m,0)"
      by (rule append_rows_nth3[OF A' _ A_def _ _ n0], insert n0, auto)
    also have "... = D" using m0 n0 by auto
    finally show ?thesis using D0 by auto
  qed
  have "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([1..<m+1]@[m+1..<dim_row A])"
    using nz_def l_rw by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m+1] @ filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([m+1..<dim_row A])"
    by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m+1]" using f0 by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([1..<m]@[m])" using m0 by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m] @ [m]" using fm by auto
  finally have "non_zero_positions = ?xs @ [m]" .
  moreover have "distinct ?xs" by auto
  moreover have "(\<forall>x\<in>set ?xs. x < m \<and> 0 < x)" by auto
  ultimately show ?thesis by blast
qed

lemma A_A'D_eq_first_n_rows:
 assumes A_def: "A = A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A': "A' \<in> carrier_mat m n" 
  and mn: "m\<ge>n"
shows "(mat_of_rows n (map (Matrix.row A') [0..<n])) 
  = (mat_of_rows n (map (Matrix.row A) [0..<n]))" (is "?lhs = ?rhs")
proof (rule eq_matI) 
  show dr: "dim_row ?lhs = dim_row ?rhs" and dc: "dim_col ?lhs = dim_col ?rhs" by auto
  have D: "D \<cdot>\<^sub>m 1\<^sub>m n : carrier_mat n n" by simp
  fix i j assume i: "i<dim_row ?rhs" and j: "j<dim_col ?rhs"
  have "?lhs $$ (i,j) = A' $$ (i,j)" using i j dr dc A' mn by (simp add: mat_of_rows_def)
  also have "... = A $$ (i,j)" using append_rows_nth[OF A' D] i j dr dc A' mn A_def by auto
  also have "... = ?rhs $$ (i,j)" using i j dr dc A' A_def mn
    by (metis D calculation carrier_matD(1) diff_zero gr_implies_not0 length_map length_upt 
        linordered_semidom_class.add_diff_inverse mat_of_rows_carrier(2,3)
        mat_of_rows_index nat_SN.compat nth_map_upt row_append_rows1)
  finally show "?lhs $$ (i,j) = ?rhs $$ (i,j)" .
qed

lemma non_zero_positions_xs_m_invertible:  
  assumes A_def: "A = A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A': "A' \<in> carrier_mat m n" 
  and nz_def: "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  and m0: "0<m" and n0: "0<n"
  and D0: "D \<noteq> 0"
  and inv_A'': "invertible_mat (map_mat rat_of_int (mat_of_rows n (map (Matrix.row A') [0..<n])))"
  and A'00: "A' $$ (0,0) = 0"
  and mn: "m\<ge>n"
shows "length non_zero_positions > 1"
proof -  
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  have D: "D \<cdot>\<^sub>m 1\<^sub>m n : carrier_mat n n" by auto
  let ?RAT = "map_mat rat_of_int"
  let ?A'' = "(mat_of_rows n (map (Matrix.row A') [0..<n]))"
  have A'': "?A'' \<in> carrier_mat n n" by auto
  have RAT_A'': "?RAT ?A'' \<in> carrier_mat n n" by auto
  let ?ys = "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]"
  let ?xs = "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<n]"
  have xs_not_empty:"?xs \<noteq> []"
  proof (rule ccontr)
    assume "\<not> ?xs \<noteq> []" hence xs0: "?xs = []" by simp
    have A00: "A $$ (0,0) = 0" 
    proof -
      have "A $$ (0,0) = A'$$(0,0)" unfolding A_def using append_rows_nth[OF A' D] m0 n0 A' by auto
      thus ?thesis using A'00 by simp
    qed
    hence "(\<forall>i\<in>set [1..<n]. A $$ (i,0) = 0)"
      by (metis (mono_tags, lifting) empty_filter_conv xs0)
    hence *: "(\<forall>i<n. A $$ (i,0) = 0)" using A00 n0 using linorder_not_less by force
    have "col ?A'' 0 = 0\<^sub>v n"
    proof (rule eq_vecI)
      show "dim_vec (col ?A'' 0) = dim_vec (0\<^sub>vn)" using A' by auto
      fix i assume i: "i < dim_vec (0\<^sub>v n)" 
      have "col ?A'' 0 $v i = ?A'' $$ (i,0)" by (rule index_col, insert i A' n0, auto)
      also have "... = A $$ (i,0)" 
        unfolding A_def using i A append_rows_nth[OF A' D _ n0] A' mn 
        by (metis A'' n0 carrier_matD(1) index_zero_vec(2) le_add2 map_first_rows_index
            mat_of_rows_carrier(2) mat_of_rows_index nat_SN.compat)
      also have "... = 0" using * i by auto
      finally show "col ?A'' 0 $v i = 0\<^sub>v n $v i" using i by auto
    qed
    hence "col (?RAT ?A'') 0 = 0\<^sub>v n" by auto
    hence "\<not> invertible_mat (?RAT ?A'')"
      using invertible_mat_first_column_not0[OF RAT_A'' _ n0] by auto
    thus False using inv_A'' by contradiction
  qed
  have l_rw: "[1..<dim_row A] = [1..<m+1]@[m+1..<dim_row A]" using A m0 n0
    by (auto, metis Suc_leI less_add_same_cancel1 upt_add_eq_append upt_conv_Cons)
  have f0: "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([m+1..<dim_row A]) = []"
  proof (rule filter_False) 
    have "A $$ (i,0) = 0" if i: "i\<in>set [m + 1..<dim_row A]" for i
    proof -
      have "A $$ (i,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i-m,0)"
        by (rule append_rows_nth3[OF A' _ A_def _ _ n0], insert i A, auto)
      also have "... = 0" using i A by auto
      finally show ?thesis .        
    qed
    thus "\<forall>x\<in>set [m + 1..<dim_row A]. \<not> A $$ (x, 0) \<noteq> 0" by blast
  qed
  have fm: "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [m] = [m]"
  proof -
    have "A $$ (m, 0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m,0)"
      by (rule append_rows_nth3[OF A' _ A_def _ _ n0], insert n0, auto)
    also have "... = D" using m0 n0 by auto
    finally show ?thesis using D0 by auto
  qed
  have "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([1..<m+1]@[m+1..<dim_row A])"
    using nz_def l_rw by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m+1] @ filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([m+1..<dim_row A])"
    by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m+1]" using f0 by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) ([1..<m]@[m])" using m0 by auto
  also have "... = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m] @ [m]" using fm by auto
  finally have nz: "non_zero_positions = ?ys @ [m]" .
  moreover have ys_not_empty: "?ys \<noteq> []" using xs_not_empty mn
    by (metis (no_types, lifting) atLeastLessThan_iff empty_filter_conv nat_SN.compat set_upt)
  show ?thesis unfolding nz using ys_not_empty by auto  
qed



corollary non_zero_positions_length_xs:  
  assumes A_def: "A = A' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A': "A' \<in> carrier_mat m n" 
  and nz_def: "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  and m0: "0<m" and n0: "0<n"
  and D0: "D \<noteq> 0"
  and inv_A'': "invertible_mat (map_mat rat_of_int (mat_of_rows n (map (Matrix.row A') [0..<n])))"
  and A'00: "A' $$ (0,0) = 0"
  and mn: "m\<ge>n"
  and nz_xs_m: "non_zero_positions = xs @ [m]"
shows "length xs > 0"
proof -  
  have "length non_zero_positions > 1" 
    by (rule non_zero_positions_xs_m_invertible[OF A_def A' nz_def m0 n0 D0 inv_A'' A'00 mn])
  thus ?thesis using nz_xs_m by auto  
qed



lemma make_first_column_positive_nz_conv:
  assumes "i<dim_row A" and "j<dim_col A"
  shows "(make_first_column_positive A $$ (i, j) \<noteq> 0) = (A $$ (i, j) \<noteq> 0)"
  using assms unfolding make_first_column_positive.simps by auto



lemma make_first_column_positive_00:
  assumes A_def: "A = A'' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
    and A'': "A'' : carrier_mat m n"
  assumes nz_def: "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
    and A'_def: "A' = (if A $$ (0, 0) \<noteq> 0 then A else let i = non_zero_positions ! 0 in swaprows 0 i A)"
    and m0: "0<m" and n0: "0<n" and D0: "D \<noteq> 0" and mn: "m\<ge>n"
  shows "make_first_column_positive A' $$ (0, 0) \<noteq> 0"
proof -
  have A: "A \<in> carrier_mat (m+n) n" using A_def A'' by auto
  hence A': "A' \<in> carrier_mat (m+n) n" unfolding A'_def by auto 
  have "(make_first_column_positive A' $$ (0, 0) \<noteq> 0) = (A' $$ (0, 0) \<noteq> 0)"
    by (rule make_first_column_positive_nz_conv, insert m0 n0 A', auto)
  moreover have "A' $$ (0, 0) \<noteq> 0"
  proof (cases "A $$ (0, 0) \<noteq> 0")
    case True
    then show ?thesis unfolding A'_def by auto
  next
    case False
    have "A $$ (0, 0) = A'' $$ (0, 0)"
      by (smt add_gr_0 append_rows_def A_def A'' carrier_matD index_mat_four_block(1) mn n0 nat_SN.compat)
    hence A''00: "A''$$(0,0) = 0" using False by auto
    let ?i = "non_zero_positions ! 0"
    obtain xs where non_zero_positions_xs_m: "non_zero_positions = xs @ [m]" and d_xs: "distinct xs"
      and all_less_m: "\<forall>x\<in>set xs. x < m \<and> 0 < x" 
      using non_zero_positions_xs_m[OF A_def A'' nz_def m0 n0] using D0 by fast    
    have Ai0:"A $$ (?i,0) \<noteq> 0"
      by (smt append.simps(1) append_Cons append_same_eq nz_def in_set_conv_nth length_greater_0_conv
          list.simps(3) local.non_zero_positions_xs_m mem_Collect_eq set_filter)  
    have "A' $$ (0, 0) = swaprows 0 ?i A $$ (0,0)"  using False A'_def by auto
    also have "... \<noteq> 0" using A Ai0 n0 by auto  
    finally show ?thesis .
  qed
  ultimately show ?thesis by blast
qed


context proper_mod_operation
begin
lemma reduce_below_0_case_m_make_first_column_positive:
  assumes A': "A' \<in> carrier_mat m n" and m0: "0<m" and n0: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and mn: "m\<ge>n"
  assumes i_mn: "i < m+n" and d_xs: "distinct xs" and xs: "\<forall>x \<in> set xs. x < m \<and> 0 < x"
    and ia: "i\<noteq>0"
    and A''_def: "A'' = (if A $$ (0, 0) \<noteq> 0 then A else let i = non_zero_positions ! 0 in swaprows 0 i A)"
    and D0: "D>0"
    and nz_def: "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  shows "reduce_below 0 non_zero_positions D (make_first_column_positive A'') $$ (i,0) = 0"
proof -
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  define xs where "xs = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]"
  have nz_xs_m: "non_zero_positions = xs @ [m]" and d_xs: "distinct xs"
    and all_less_m: "\<forall>x\<in>set xs. x < m \<and> 0 < x" 
    using non_zero_positions_xs_m'[OF A_def A' nz_def m0 n0] using D0 A unfolding nz_def xs_def by auto
  have A'': "A'' \<in> carrier_mat (m+n) n" using A' A_def A''_def by auto
  have D_not0: "D\<noteq>0" using D0 by auto
  have Ai0: "A $$ (i, 0) = 0" if im: "i>m" and imn: "i<m+n" for i
  proof-
    have D: "(D \<cdot>\<^sub>m (1\<^sub>m n)) \<in> carrier_mat n n" by simp
    have "A $$ (i, 0) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (i-m, 0)"
      unfolding A_def using append_rows_nth[OF A' D imn n0] im A' by auto 
    also have "... = 0" using im imn n0 by auto
    finally show ?thesis .
  qed
  let ?M' = "mat_of_rows n (map (Matrix.row (make_first_column_positive A'')) [0..<m])"
  have M': "?M' \<in> carrier_mat m n" using A'' by auto
  have mk0: "make_first_column_positive A'' $$ (0, 0) \<noteq> 0"
    by (rule make_first_column_positive_00[OF A_def A' nz_def A''_def m0 n0 D_not0 mn])
  have M_M'D: "make_first_column_positive A'' = ?M' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" if xs_empty: "xs \<noteq> []"
  proof (cases "A$$(0,0) \<noteq> 0")
    case True
    then have *: "make_first_column_positive A'' = make_first_column_positive A"
      unfolding A''_def by auto        
    show ?thesis 
      by (unfold *, rule make_first_column_positive_append_id[OF A' A_def D0 n0])
  next
    case False
    then have *: "make_first_column_positive A'' 
                  = make_first_column_positive (swaprows 0 (non_zero_positions ! 0) A)"
      unfolding A''_def by auto
    show ?thesis
    proof (unfold *, rule make_first_column_positive_append_id)
      let ?S = "mat_of_rows n (map (Matrix.row (swaprows 0 (non_zero_positions ! 0) A)) [0..<m])"
      show "swaprows 0 (non_zero_positions ! 0) A =  ?S @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
      proof (rule swaprows_append_id[OF A' A_def])
        have A'00: "A' $$ (0, 0) = 0"          
          by (metis (no_types, lifting) A False add_pos_pos append_rows_def A' A_def 
              carrier_matD index_mat_four_block m0 n0)
        have length_xs: "length xs > 0" using xs_empty by auto
        have "non_zero_positions ! 0 = xs ! 0" unfolding nz_xs_m
          by (meson length_xs nth_append)
        thus "non_zero_positions ! 0 < m" using all_less_m length_xs by simp
      qed
    qed (insert n0 D0, auto)            
  qed
  show ?thesis
  proof (cases "xs = []")
    case True note xs_empty = True
    have "reduce_below 0 non_zero_positions D (make_first_column_positive A'') 
      = reduce 0 m D (make_first_column_positive A'')"
      unfolding nz_xs_m True by auto

    also have "...  $$ (i, 0) = 0"
    proof (cases "i=m")
      case True
      from D0 have "D \<ge> 1" "D \<ge> 0" by auto
      then show ?thesis using D0 True
        by (metis A add_sign_intros(2) A''_def carrier_matD(1) carrier_matD(2) carrier_matI 
            index_mat_swaprows(2) index_mat_swaprows(3) less_add_same_cancel1 m0 
            make_first_column_positive_preserves_dimensions mk0 n0 neq0_conv reduce_0)
    next
      case False note i_not_m = False
      have nz_m: "non_zero_positions ! 0 = m" unfolding nz_xs_m True by auto
      let ?M = "make_first_column_positive A''"
      have M: "?M \<in> carrier_mat (m+n) n" using A'' by auto
      show ?thesis
      proof (cases "A$$(0,0) = 0")
        case True
        have "reduce 0 m D ?M $$ (i, 0) = ?M $$ (i,0)" 
          by (rule reduce_preserves[OF M n0 mk0 False ia i_mn])
        also have Mi0: "... = abs (A'' $$ (i,0))"
          by (smt M carrier_matD(1) carrier_matD(2) i_mn index_mat(1) make_first_column_positive.simps
              make_first_column_positive_preserves_dimensions n0 prod.simps(2))
        also have Mi02: "... = abs (A $$ (i,0)) " unfolding A''_def nz_m
          using True A False i_mn ia n0 by auto
        also have "... = 0"
        proof -
          have "filter (\<lambda>n. A $$ (n, 0) \<noteq> 0) [1..<m] = []"
            using xs_empty xs_def by presburger
          then have "\<forall>n. A $$ (n, 0) = 0 \<or> n \<notin> set [1..<m]" using filter_empty_conv by fast          
          then show ?thesis
            by (metis (no_types) Ai0 False arith_simps(43) assms(9) atLeastLessThan_iff i_mn
                le_eq_less_or_eq less_one linorder_neqE_nat set_upt)
        qed
        finally show ?thesis .
      next
        case False hence A00: "A $$ (0,0) \<noteq> 0" by simp
        have "reduce 0 m D ?M $$ (i, 0) = ?M $$ (i,0)" 
          by (rule reduce_preserves[OF M n0 mk0 i_not_m ia i_mn])
        also have Mi0: "... = abs (A'' $$ (i,0))"
          by (smt M carrier_matD(1) carrier_matD(2) i_mn index_mat(1) make_first_column_positive.simps
              make_first_column_positive_preserves_dimensions n0 prod.simps(2))
        also have Mi02: "... = abs (swaprows 0 m A $$ (i,0)) " unfolding A''_def nz_m
          using A00 A i_not_m i_mn ia n0 by auto
        also have "... = abs (A $$ (i,0))" using False ia A00 Mi0 A''_def calculation Mi02 by presburger  
        also have "... = 0"
        proof -
          have "filter (\<lambda>n. A $$ (n, 0) \<noteq> 0) [1..<m] = []"
            using True xs_def by presburger
          then have "\<forall>n. A $$ (n, 0) = 0 \<or> n \<notin> set [1..<m]" using filter_empty_conv by fast          
          then show ?thesis
            by (metis (no_types) Ai0 i_not_m arith_simps(43) ia atLeastLessThan_iff i_mn
                le_eq_less_or_eq less_one linorder_neqE_nat set_upt)
        qed
        finally show ?thesis .
      qed
    qed
    finally show ?thesis .
  next
    case False note xs_not_empty = False
    note M_M'D = M_M'D[OF xs_not_empty]
    show ?thesis   
    proof (cases "i \<in> set (xs @ [m])")
      case True
      show ?thesis  
        by (unfold nz_xs_m, rule reduce_below_0_case_m[OF M' m0 n0 M_M'D mk0 mn True d_xs all_less_m D0])
    next
      case False note i_notin_xs_m = False
      have 1: "reduce_below 0 (xs @ [m]) D (make_first_column_positive A'') $$ (i,0) 
        = (make_first_column_positive A'') $$ (i,0)"    
        by (rule reduce_below_preserves_case_m[OF M' m0 n0 M_M'D mk0 mn _ d_xs all_less_m ia i_mn _ D0],
            insert False, auto) 
      have "((make_first_column_positive A'') $$ (i,0) \<noteq> 0) = (A'' $$ (i,0) \<noteq> 0)"
        by (rule make_first_column_positive_nz_conv, insert A'' i_mn n0, auto)
      hence 2: "((make_first_column_positive A'') $$ (i,0) = 0) = (A'' $$ (i,0) = 0)" by auto
      have 3: "(A'' $$ (i,0) = 0)"
      proof (cases "A$$(0,0) \<noteq> 0")
        case True
        then have "A'' $$ (i, 0) = A $$ (i, 0)" unfolding A''_def by auto
        also have "... = 0" using False ia i_mn A nz_xs_m Ai0 unfolding nz_def xs_def by auto
        finally show ?thesis by auto
      next
        case False hence A00: "A $$ (0,0) = 0" by simp
        let ?i = "non_zero_positions ! 0"
        have i_noti: "i\<noteq>?i" 
          using i_notin_xs_m unfolding nz_xs_m
          by (metis Nil_is_append_conv length_greater_0_conv list.distinct(2) nth_mem)
        have "A''$$(i,0) = (swaprows 0 ?i A) $$ (i,0)" using False unfolding A''_def by auto
        also have "... = A $$ (i,0)" using i_notin_xs_m ia i_mn A i_noti n0 unfolding xs_def by fastforce  
        also have "... = 0" using i_notin_xs_m ia i_mn A i_noti n0 unfolding xs_def 
          by (smt nz_def atLeastLessThan_iff carrier_matD(1) less_one linorder_not_less
              mem_Collect_eq nz_xs_m set_filter set_upt xs_def) 
        finally show ?thesis .
      qed
      show ?thesis using 1 2 3 nz_xs_m by argo
    qed
  qed
qed


lemma reduce_below_abs_0_case_m_make_first_column_positive:
  assumes A': "A' \<in> carrier_mat m n" and m0: "0<m" and n0: "0<n"
    and A_def: "A = A' @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
    and mn: "m\<ge>n"
  assumes i_mn: "i < m+n" and d_xs: "distinct xs" and xs: "\<forall>x \<in> set xs. x < m \<and> 0 < x"
    and ia: "i\<noteq>0"
    and A''_def: "A'' = (if A $$ (0, 0) \<noteq> 0 then A else let i = non_zero_positions ! 0 in swaprows 0 i A)"
    and D0: "D>0"
    and nz_def: "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  shows "reduce_below_abs 0 non_zero_positions D (make_first_column_positive A'') $$ (i,0) = 0"
proof -
  have A: "A \<in> carrier_mat (m+n) n" using A' A_def by auto
  define xs where "xs = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]"
  have nz_xs_m: "non_zero_positions = xs @ [m]" and d_xs: "distinct xs"
    and all_less_m: "\<forall>x\<in>set xs. x < m \<and> 0 < x" 
    using non_zero_positions_xs_m'[OF A_def A' nz_def m0 n0] using D0 A unfolding nz_def xs_def by auto
  have A'': "A'' \<in> carrier_mat (m+n) n" using A' A_def A''_def by auto
  have D_not0: "D\<noteq>0" using D0 by auto
  have Ai0: "A $$ (i, 0) = 0" if im: "i>m" and imn: "i<m+n" for i
  proof-
    have D: "(D \<cdot>\<^sub>m (1\<^sub>m n)) \<in> carrier_mat n n" by simp
    have "A $$ (i, 0) = (D \<cdot>\<^sub>m (1\<^sub>m n)) $$ (i-m, 0)"
      unfolding A_def using append_rows_nth[OF A' D imn n0] im A' by auto 
    also have "... = 0" using im imn n0 by auto
    finally show ?thesis .
  qed
  let ?M' = "mat_of_rows n (map (Matrix.row (make_first_column_positive A'')) [0..<m])"
  have M': "?M' \<in> carrier_mat m n" using A'' by auto
  have mk0: "make_first_column_positive A'' $$ (0, 0) \<noteq> 0"
    by (rule make_first_column_positive_00[OF A_def A' nz_def A''_def m0 n0 D_not0 mn])
  have M_M'D: "make_first_column_positive A'' = ?M' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" if xs_empty: "xs \<noteq> []"
  proof (cases "A$$(0,0) \<noteq> 0")
    case True
    then have *: "make_first_column_positive A'' = make_first_column_positive A"
      unfolding A''_def by auto        
    show ?thesis 
      by (unfold *, rule make_first_column_positive_append_id[OF A' A_def D0 n0])
  next
    case False
    then have *: "make_first_column_positive A'' 
                  = make_first_column_positive (swaprows 0 (non_zero_positions ! 0) A)"
      unfolding A''_def by auto
    show ?thesis
    proof (unfold *, rule make_first_column_positive_append_id)
      let ?S = "mat_of_rows n (map (Matrix.row (swaprows 0 (non_zero_positions ! 0) A)) [0..<m])"
      show "swaprows 0 (non_zero_positions ! 0) A =  ?S @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
      proof (rule swaprows_append_id[OF A' A_def])
        have A'00: "A' $$ (0, 0) = 0"          
          by (metis (no_types, lifting) A False add_pos_pos append_rows_def A' A_def 
              carrier_matD index_mat_four_block m0 n0)
        have length_xs: "length xs > 0" using xs_empty by auto
        have "non_zero_positions ! 0 = xs ! 0" unfolding nz_xs_m
          by (meson length_xs nth_append)
        thus "non_zero_positions ! 0 < m" using all_less_m length_xs by simp
      qed
    qed (insert n0 D0, auto)            
  qed
  show ?thesis
  proof (cases "xs = []")
    case True note xs_empty = True
    have "reduce_below_abs 0 non_zero_positions D (make_first_column_positive A'') 
      = reduce_abs 0 m D (make_first_column_positive A'')"
      unfolding nz_xs_m True by auto

    also have "...  $$ (i, 0) = 0"
    proof (cases "i=m")
      case True
      from D0 have "D \<ge> 1" "D \<ge> 0" by auto
      then show ?thesis using D0 True
        by (metis A add_sign_intros(2) A''_def carrier_matD(1) carrier_matD(2) carrier_matI 
            index_mat_swaprows(2) index_mat_swaprows(3) less_add_same_cancel1 m0 
            make_first_column_positive_preserves_dimensions mk0 n0 neq0_conv reduce_0)
    next
      case False note i_not_m = False
      have nz_m: "non_zero_positions ! 0 = m" unfolding nz_xs_m True by auto
      let ?M = "make_first_column_positive A''"
      have M: "?M \<in> carrier_mat (m+n) n" using A'' by auto
      show ?thesis
      proof (cases "A$$(0,0) = 0")
        case True
        have "reduce_abs 0 m D ?M $$ (i, 0) = ?M $$ (i,0)" 
          by (rule reduce_preserves[OF M n0 mk0 False ia i_mn])
        also have Mi0: "... = abs (A'' $$ (i,0))"
          by (smt M carrier_matD(1) carrier_matD(2) i_mn index_mat(1) make_first_column_positive.simps
              make_first_column_positive_preserves_dimensions n0 prod.simps(2))
        also have Mi02: "... = abs (A $$ (i,0)) " unfolding A''_def nz_m
          using True A False i_mn ia n0 by auto
        also have "... = 0"
        proof -
          have "filter (\<lambda>n. A $$ (n, 0) \<noteq> 0) [1..<m] = []"
            using xs_empty xs_def by presburger
          then have "\<forall>n. A $$ (n, 0) = 0 \<or> n \<notin> set [1..<m]" using filter_empty_conv by fast          
          then show ?thesis
            by (metis (no_types) Ai0 False arith_simps(43) assms(9) atLeastLessThan_iff i_mn
                le_eq_less_or_eq less_one linorder_neqE_nat set_upt)
        qed
        finally show ?thesis .
      next
        case False hence A00: "A $$ (0,0) \<noteq> 0" by simp
        have "reduce_abs 0 m D ?M $$ (i, 0) = ?M $$ (i,0)" 
          by (rule reduce_preserves[OF M n0 mk0 i_not_m ia i_mn])
        also have Mi0: "... = abs (A'' $$ (i,0))"
          by (smt M carrier_matD(1) carrier_matD(2) i_mn index_mat(1) make_first_column_positive.simps
              make_first_column_positive_preserves_dimensions n0 prod.simps(2))
        also have Mi02: "... = abs (swaprows 0 m A $$ (i,0)) " unfolding A''_def nz_m
          using A00 A i_not_m i_mn ia n0 by auto
        also have "... = abs (A $$ (i,0))" using False ia A00 Mi0 A''_def calculation Mi02 by presburger  
        also have "... = 0"
        proof -
          have "filter (\<lambda>n. A $$ (n, 0) \<noteq> 0) [1..<m] = []"
            using True xs_def by presburger
          then have "\<forall>n. A $$ (n, 0) = 0 \<or> n \<notin> set [1..<m]" using filter_empty_conv by fast          
          then show ?thesis
            by (metis (no_types) Ai0 i_not_m arith_simps(43) ia atLeastLessThan_iff i_mn
                le_eq_less_or_eq less_one linorder_neqE_nat set_upt)
        qed
        finally show ?thesis .
      qed
    qed
    finally show ?thesis .
  next
    case False note xs_not_empty = False
    note M_M'D = M_M'D[OF xs_not_empty]
    show ?thesis   
    proof (cases "i \<in> set (xs @ [m])")
      case True
      show ?thesis  
        by (unfold nz_xs_m, rule reduce_below_abs_0_case_m[OF M' m0 n0 M_M'D mk0 mn True d_xs all_less_m D0])
    next
      case False note i_notin_xs_m = False
      have 1: "reduce_below_abs 0 (xs @ [m]) D (make_first_column_positive A'') $$ (i,0) 
        = (make_first_column_positive A'') $$ (i,0)"    
        by (rule reduce_below_abs_preserves_case_m[OF M' m0 n0 M_M'D mk0 mn _ d_xs all_less_m ia i_mn _ D0],
            insert False, auto) 
      have "((make_first_column_positive A'') $$ (i,0) \<noteq> 0) = (A'' $$ (i,0) \<noteq> 0)"
        by (rule make_first_column_positive_nz_conv, insert A'' i_mn n0, auto)
      hence 2: "((make_first_column_positive A'') $$ (i,0) = 0) = (A'' $$ (i,0) = 0)" by auto
      have 3: "(A'' $$ (i,0) = 0)"
      proof (cases "A$$(0,0) \<noteq> 0")
        case True
        then have "A'' $$ (i, 0) = A $$ (i, 0)" unfolding A''_def by auto
        also have "... = 0" using False ia i_mn A nz_xs_m Ai0 unfolding nz_def xs_def by auto
        finally show ?thesis by auto
      next
        case False hence A00: "A $$ (0,0) = 0" by simp
        let ?i = "non_zero_positions ! 0"
        have i_noti: "i\<noteq>?i" 
          using i_notin_xs_m unfolding nz_xs_m
          by (metis Nil_is_append_conv length_greater_0_conv list.distinct(2) nth_mem)
        have "A''$$(i,0) = (swaprows 0 ?i A) $$ (i,0)" using False unfolding A''_def by auto
        also have "... = A $$ (i,0)" using i_notin_xs_m ia i_mn A i_noti n0 unfolding xs_def by fastforce  
        also have "... = 0" using i_notin_xs_m ia i_mn A i_noti n0 unfolding xs_def 
          by (smt nz_def atLeastLessThan_iff carrier_matD(1) less_one linorder_not_less
              mem_Collect_eq nz_xs_m set_filter set_upt xs_def) 
        finally show ?thesis .
      qed
      show ?thesis using 1 2 3 nz_xs_m by argo
    qed
  qed
qed


lemma FindPreHNF_invertible_mat_2xn:
  assumes A: "A \<in> carrier_mat m n" and "m<2"
  shows "\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> FindPreHNF abs_flag D A = P * A"
  using assms
  by (auto, metis invertible_mat_one left_mult_one_mat one_carrier_mat)


lemma FindPreHNF_invertible_mat_mx2:
  assumes A_def: "A = A'' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A'': "A'' \<in> carrier_mat m n" and n2: "n<2" and n0: "0<n" and D_g0: "D>0" and mn: "m\<ge>n"
shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> FindPreHNF abs_flag D A = P * A"
proof -
  have A: "A \<in> carrier_mat (m+n) n" using A_def A'' by auto
  have m0: "m>0" using mn n2 n0 by auto
  have D0: "D\<noteq>0" using D_g0 by auto
  show ?thesis
  proof (cases "m+n<2")
    case True
    show ?thesis by (rule FindPreHNF_invertible_mat_2xn[OF A True])
  next
    case False note mn_le_2 = False
    have dr_A: "dim_row A \<ge>2" using False n2 A by auto
    have dc_A: "dim_col A < 2" using n2 A by auto
    let ?non_zero_positions = "filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [Suc 0..<dim_row A]" 
    let ?A' = "(if A $$ (0, 0) \<noteq> 0 then A else let i = ?non_zero_positions ! 0 in swaprows 0 i A)"
    define xs where "xs = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]"
    let ?Reduce = "(if abs_flag then reduce_below_abs else reduce_below)"
    have nz_xs_m: "?non_zero_positions = xs @ [m]" and d_xs: "distinct xs"
      and all_less_m: "\<forall>x\<in>set xs. x < m \<and> 0 < x" 
      using non_zero_positions_xs_m'[OF A_def A'' _ m0 n0 D0] using D0 A unfolding xs_def by auto  
    have *: "FindPreHNF abs_flag D A = (if abs_flag then reduce_below_abs 0 ?non_zero_positions D ?A' 
        else reduce_below 0 ?non_zero_positions D ?A')"
      using dr_A dc_A by (auto simp add: Let_def) 
    have l: "length ?non_zero_positions > 1" if "xs\<noteq>[]" using that unfolding nz_xs_m by auto
    have inv: "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) 
      \<and> reduce_below 0 ?non_zero_positions D ?A' = P * ?A'"
    proof (cases "A $$ (0,0) \<noteq>0")
      case True
      show ?thesis
        by (unfold nz_xs_m, rule reduce_below_invertible_mat_case_m
            [OF A'' m0 n0 _ _ mn d_xs all_less_m], insert A_def True D_g0, auto)
    next
      case False hence A00: "A $$ (0,0) = 0" by auto
      let ?S = "swaprows 0 (?non_zero_positions ! 0) A"
      have rw: "(if A $$ (0, 0) \<noteq> 0 then A else let i = ?non_zero_positions ! 0 in swaprows 0 i A)
          = ?S" using False by auto
      show ?thesis
      proof (cases "xs = []")
        case True
        have nz_m: "?non_zero_positions = [m]" using True nz_xs_m by simp
        obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (swaprows 0 m A $$ (0, 0)) (swaprows 0 m A $$ (m, 0))"
          by (metis prod_cases5)        
        have Am0: "A $$ (m,0) = D"
        proof -
          have "A $$ (m,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m, 0)"
            by (smt (z3) A append_rows_def A_def A'' n0 carrier_matD diff_self_eq_0 index_mat_four_block
                less_add_same_cancel1 less_diff_conv diff_add nat_less_le)
          also have "... = D" by (simp add: n0)
          finally show ?thesis .
        qed
        have Sm0: "(swaprows 0 m A) $$ (m,0) = 0" using A False n0 by auto
        have S00: "(swaprows 0 m A) $$ (0,0) = D" using A Am0 n0 by auto
        have pquvd2: "(p,q,u,v,d) = euclid_ext2 (A $$ (m, 0)) (A $$ (0, 0))"
          using pquvd Sm0 S00 Am0 A00 by auto
        have "reduce_below 0 ?non_zero_positions D ?A' = reduce 0 m D ?A'" unfolding nz_m by auto
        also have "... = reduce 0 m D (swaprows 0 m A)" using True False rw nz_m by auto
        have " \<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) \<and>
           reduce 0 m D (swaprows 0 m A) = P * (swaprows 0 m A)"
        proof (rule reduce_invertible_mat_case_m[OF _ _ m0 _ _ _ _ mn n0])
          show "swaprows 0 m A $$ (0, 0) \<noteq> 0" using S00 D0 by auto
          define S' where  "S' = mat_of_rows n (map (Matrix.row ?S) [0..<m])"
          define S'' where "S'' = mat_of_rows n (map (Matrix.row ?S) [m..<m+n])"
          define A2 where "A2 = Matrix.mat (dim_row (swaprows 0 m A)) (dim_col (swaprows 0 m A))
             (\<lambda>(i, k). if i = 0 then p * A $$ (m, k) + q * A $$ (0, k)
             else if i = m then u * A $$ (m, k) + v * A $$ (0, k) else A $$ (i, k))"
          show S_S'_S'': "swaprows 0 m A = S' @\<^sub>r S''" unfolding S'_def S''_def
            by (metis A append_rows_split carrier_matD index_mat_swaprows(2,3) le_add1 nth_Cons_0 nz_m)
          show S': "S' \<in> carrier_mat m n" unfolding S'_def by fastforce
          show S'': "S'' \<in> carrier_mat n n" unfolding S''_def by fastforce
          show "0 \<noteq> m" using m0 by simp
          show "(p,q,u,v,d) = euclid_ext2 (swaprows 0 m A $$ (0, 0)) (swaprows 0 m A $$ (m, 0))"
            using pquvd by simp
          show "A2 = Matrix.mat (dim_row (swaprows 0 m A)) (dim_col (swaprows 0 m A))
         (\<lambda>(i, k). if i = 0 then p * swaprows 0 m A $$ (0, k) + q * swaprows 0 m A $$ (m, k)
         else if i = m then u * swaprows 0 m A $$ (0, k) + v * swaprows 0 m A $$ (m, k) else swaprows 0 m A $$ (i, k))"
            (is "_ = ?rhs") using A A2_def by auto
          define xs' where "xs' = [1..<n]"
          define ys' where  "ys' = [1..<n]"
          show "xs' = [1..<n]" unfolding xs'_def by auto
          show "ys' = [1..<n]" unfolding ys'_def by auto
          have S''D: "(S'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. S'' $$ (j, j') = 0)"
            if jn: "j<n" and j0: "j>0" for j
          proof -
            have "S'' $$ (j, i) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)" if i_n: "i<n" for i
            proof -
              have "S'' $$ (j, i) = swaprows 0 m A $$ (j+m,i)"
                by (metis S' S'' S_S'_S'' append_rows_nth2 mn nat_SN.compat i_n jn)
              also have "... = A $$ (j+m,i)" using A jn j0 i_n by auto
              also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)"
                by (smt A Groups.add_ac(2) add_mono_thms_linordered_field(1) append_rows_def A_def A'' i_n
                    carrier_matD index_mat_four_block(1,2) add_diff_cancel_right' not_add_less2 jn trans_less_add1)
              finally show ?thesis .
            qed
            thus ?thesis using jn j0 by auto
          qed
          have "0 \<notin> set xs'"
          proof -
            have "A2 $$ (0,0) = p * A $$ (m, 0) + q * A $$ (0, 0)" 
              using A A2_def n0 by auto
            also have "... = gcd (A $$ (m, 0)) (A $$ (0, 0))"
              by (metis euclid_ext2_works(1) euclid_ext2_works(2) pquvd2)
            also have "... = D" using Am0 A00 D_g0 by auto             
            finally have "A2 $$ (0,0) = D" .
            thus ?thesis unfolding xs'_def using D_g0 by auto
          qed
          thus "\<forall>j\<in>set xs'. j<n \<and> (S'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. S'' $$ (j, j') = 0)"  
            using S''D xs'_def by auto
          have "0 \<notin> set ys'"
          proof -
            have "A2 $$ (m,0) = u * A $$ (m, 0) + v * A $$ (0, 0)"
              using A A2_def n0 m0 by auto
            also have "... = - A $$ (0, 0) div gcd (A $$ (m, 0)) (A $$ (0, 0)) * A $$ (m, 0) 
              + A $$ (m, 0) div gcd (A $$ (m, 0)) (A $$ (0, 0)) * A $$ (0, 0)"
              by (simp add: euclid_ext2_works[OF pquvd2[symmetric]])
            also have "... = 0" using A00 Am0 by auto
            finally have "A2 $$ (m,0) = 0" .
            thus ?thesis unfolding ys'_def using D_g0 by auto
          qed
          thus "\<forall>j\<in>set ys'. j<n \<and> (S'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. S'' $$ (j, j') = 0)"
            using S''D ys'_def by auto    
          show "swaprows 0 m A $$ (m, 0) \<in> {0, D}" using Sm0 by blast
          thus "swaprows 0 m A $$ (m, 0) = 0 \<longrightarrow> swaprows 0 m A $$ (0, 0) = D"
            using S00 by linarith                  
        qed (insert D_g0)      
        then show ?thesis by (simp add: False nz_m)
      next
        case False note xs_not_empty = False
        show ?thesis       
      proof (unfold nz_xs_m, rule reduce_below_invertible_mat_case_m[OF _ m0 n0 _ _ mn d_xs all_less_m D_g0])
        let ?S' = "mat_of_rows n (map (Matrix.row ?S) [0..<m])"
        show "?S' \<in> carrier_mat m n" by auto
        have l: "length ?non_zero_positions > 1" using l False by blast
        hence nz0_less_m: "?non_zero_positions ! 0 < m"
          by (metis One_nat_def add.commute add.left_neutral all_less_m append_Cons_nth_left 
              length_append less_add_same_cancel1 list.size(3,4) nth_mem nz_xs_m)    
        have "?S = ?S' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" by (rule swaprows_append_id[OF A'' A_def nz0_less_m])
        thus "(if A $$ (0, 0) \<noteq> 0 then A else let i = (xs @ [m]) ! 0 in swaprows 0 i A)= ?S' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" 
          using rw nz_xs_m by argo
        have "?S $$ (0, 0) \<noteq> 0"
          by (smt A l add_pos_pos carrier_matD index_mat_swaprows(1) le_eq_less_or_eq length_greater_0_conv
              less_one linorder_not_less list.size(3) m0 mem_Collect_eq n0 nth_mem set_filter)
        thus "(if A $$ (0, 0) \<noteq> 0 then A else let i = (xs @ [m]) ! 0 in swaprows 0 i A) $$ (0, 0) \<noteq> 0"
          using rw nz_xs_m by algebra
      qed
    qed
  qed
    have inv2: "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) 
      \<and> reduce_below_abs 0 ?non_zero_positions D ?A' = P * ?A'"
    proof (cases "A $$ (0,0) \<noteq>0")
      case True
      show ?thesis
        by (unfold nz_xs_m, rule reduce_below_abs_invertible_mat_case_m
            [OF A'' m0 n0 _ _ mn d_xs all_less_m], insert A_def True D_g0, auto)
    next
      case False hence A00: "A $$ (0,0) = 0" by auto
      let ?S = "swaprows 0 (?non_zero_positions ! 0) A"
      have rw: "(if A $$ (0, 0) \<noteq> 0 then A else let i = ?non_zero_positions ! 0 in swaprows 0 i A)
          = ?S" using False by auto
      show ?thesis
      proof (cases "xs = []")
        case True
        have nz_m: "?non_zero_positions = [m]" using True nz_xs_m by simp
        obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (swaprows 0 m A $$ (0, 0)) (swaprows 0 m A $$ (m, 0))"
          by (metis prod_cases5)        
        have Am0: "A $$ (m,0) = D"
        proof -
          have "A $$ (m,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m, 0)"
            by (smt (z3) A append_rows_def A_def A'' n0 carrier_matD diff_self_eq_0 index_mat_four_block
                less_add_same_cancel1 less_diff_conv diff_add nat_less_le)
          also have "... = D" by (simp add: n0)
          finally show ?thesis .
        qed
        have Sm0: "(swaprows 0 m A) $$ (m,0) = 0" using A False n0 by auto
        have S00: "(swaprows 0 m A) $$ (0,0) = D" using A Am0 n0 by auto
        have pquvd2: "(p,q,u,v,d) = euclid_ext2 (A $$ (m, 0)) (A $$ (0, 0))"
          using pquvd Sm0 S00 Am0 A00 by auto
        have "reduce_below 0 ?non_zero_positions D ?A' = reduce 0 m D ?A'" unfolding nz_m by auto
        also have "... = reduce 0 m D (swaprows 0 m A)" using True False rw nz_m by auto
        have " \<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) \<and>
           reduce_abs 0 m D (swaprows 0 m A) = P * (swaprows 0 m A)"
        proof (rule reduce_abs_invertible_mat_case_m[OF _ _ m0 _ _ _ _ mn n0])
          show "swaprows 0 m A $$ (0, 0) \<noteq> 0" using S00 D0 by auto
          define S' where  "S' = mat_of_rows n (map (Matrix.row ?S) [0..<m])"
          define S'' where "S'' = mat_of_rows n (map (Matrix.row ?S) [m..<m+n])"
          define A2 where "A2 = Matrix.mat (dim_row (swaprows 0 m A)) (dim_col (swaprows 0 m A))
             (\<lambda>(i, k). if i = 0 then p * A $$ (m, k) + q * A $$ (0, k)
             else if i = m then u * A $$ (m, k) + v * A $$ (0, k) else A $$ (i, k))"
          show S_S'_S'': "swaprows 0 m A = S' @\<^sub>r S''" unfolding S'_def S''_def
            by (metis A append_rows_split carrier_matD index_mat_swaprows(2,3) le_add1 nth_Cons_0 nz_m)
          show S': "S' \<in> carrier_mat m n" unfolding S'_def by fastforce
          show S'': "S'' \<in> carrier_mat n n" unfolding S''_def by fastforce
          show "0 \<noteq> m" using m0 by simp
          show "(p,q,u,v,d) = euclid_ext2 (swaprows 0 m A $$ (0, 0)) (swaprows 0 m A $$ (m, 0))"
            using pquvd by simp
          show "A2 = Matrix.mat (dim_row (swaprows 0 m A)) (dim_col (swaprows 0 m A))
         (\<lambda>(i, k). if i = 0 then p * swaprows 0 m A $$ (0, k) + q * swaprows 0 m A $$ (m, k)
         else if i = m then u * swaprows 0 m A $$ (0, k) + v * swaprows 0 m A $$ (m, k) else swaprows 0 m A $$ (i, k))"
            (is "_ = ?rhs") using A A2_def by auto
          define xs' where "xs' = filter (\<lambda>i. abs (A2 $$ (0,i)) > D) [0..<n]"
          define ys' where  "ys' = filter (\<lambda>i. abs (A2 $$ (m,i)) > D) [0..<n]"
          show "xs' = filter (\<lambda>i. abs (A2 $$ (0,i)) > D) [0..<n]" unfolding xs'_def by auto
          show "ys' = filter (\<lambda>i. abs (A2 $$ (m,i)) > D) [0..<n]" unfolding ys'_def by auto
          have S''D: "(S'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. S'' $$ (j, j') = 0)"
            if jn: "j<n" and j0: "j>0" for j
          proof -
            have "S'' $$ (j, i) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)" if i_n: "i<n" for i
            proof -
              have "S'' $$ (j, i) = swaprows 0 m A $$ (j+m,i)"
                by (metis S' S'' S_S'_S'' append_rows_nth2 mn nat_SN.compat i_n jn)
              also have "... = A $$ (j+m,i)" using A jn j0 i_n by auto
              also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)"
                by (smt A Groups.add_ac(2) add_mono_thms_linordered_field(1) append_rows_def A_def A'' i_n
                    carrier_matD index_mat_four_block(1,2) add_diff_cancel_right' not_add_less2 jn trans_less_add1)
              finally show ?thesis .
            qed
            thus ?thesis using jn j0 by auto
          qed
          have "0 \<notin> set xs'"
          proof -
            have "A2 $$ (0,0) = p * A $$ (m, 0) + q * A $$ (0, 0)" 
              using A A2_def n0 by auto
            also have "... = gcd (A $$ (m, 0)) (A $$ (0, 0))"
              by (metis euclid_ext2_works(1) euclid_ext2_works(2) pquvd2)
            also have "... = D" using Am0 A00 D_g0 by auto             
            finally have "A2 $$ (0,0) = D" .
            thus ?thesis unfolding xs'_def using D_g0 by auto
          qed
          thus "\<forall>j\<in>set xs'. j<n \<and> (S'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. S'' $$ (j, j') = 0)"  
            using S''D xs'_def by auto
          have "0 \<notin> set ys'"
          proof -
            have "A2 $$ (m,0) = u * A $$ (m, 0) + v * A $$ (0, 0)"
              using A A2_def n0 m0 by auto
            also have "... = - A $$ (0, 0) div gcd (A $$ (m, 0)) (A $$ (0, 0)) * A $$ (m, 0) 
              + A $$ (m, 0) div gcd (A $$ (m, 0)) (A $$ (0, 0)) * A $$ (0, 0)"
              by (simp add: euclid_ext2_works[OF pquvd2[symmetric]])
            also have "... = 0" using A00 Am0 by auto
            finally have "A2 $$ (m,0) = 0" .
            thus ?thesis unfolding ys'_def using D_g0 by auto
          qed
          thus "\<forall>j\<in>set ys'. j<n \<and> (S'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. S'' $$ (j, j') = 0)"
            using S''D ys'_def by auto    
        qed (insert D_g0)      
        then show ?thesis by (simp add: False nz_m)
      next
        case False note xs_not_empty = False
        show ?thesis       
      proof (unfold nz_xs_m, rule reduce_below_abs_invertible_mat_case_m[OF _ m0 n0 _ _ mn d_xs all_less_m D_g0])
        let ?S' = "mat_of_rows n (map (Matrix.row ?S) [0..<m])"
        show "?S' \<in> carrier_mat m n" by auto
        have l: "length ?non_zero_positions > 1" using l False by blast
        hence nz0_less_m: "?non_zero_positions ! 0 < m"
          by (metis One_nat_def add.commute add.left_neutral all_less_m append_Cons_nth_left 
              length_append less_add_same_cancel1 list.size(3,4) nth_mem nz_xs_m)    
        have "?S = ?S' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" by (rule swaprows_append_id[OF A'' A_def nz0_less_m])
        thus "(if A $$ (0, 0) \<noteq> 0 then A else let i = (xs @ [m]) ! 0 in swaprows 0 i A)= ?S' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" 
          using rw nz_xs_m by argo
        have "?S $$ (0, 0) \<noteq> 0"
          by (smt A l add_pos_pos carrier_matD index_mat_swaprows(1) le_eq_less_or_eq length_greater_0_conv
              less_one linorder_not_less list.size(3) m0 mem_Collect_eq n0 nth_mem set_filter)
        thus "(if A $$ (0, 0) \<noteq> 0 then A else let i = (xs @ [m]) ! 0 in swaprows 0 i A) $$ (0, 0) \<noteq> 0"
          using rw nz_xs_m by algebra
      qed
    qed
  qed
  show ?thesis
  proof (cases abs_flag)
    case False
    from inv obtain P where inv_P: "invertible_mat P" and P: "P \<in> carrier_mat (m + n) (m + n)"
      and r_PA': "reduce_below 0 ?non_zero_positions D ?A' = P * ?A'" by blast
    have Find_rw: "FindPreHNF abs_flag D A = reduce_below 0 ?non_zero_positions D ?A'"
      using n0 A dr_A dc_A False * by (auto simp add: Let_def)
    have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?A' = P * A" 
      by (rule A'_swaprows_invertible_mat[OF A], insert non_zero_positions_xs_m n0 m0 l nz_xs_m, auto) 
    from this obtain Q where Q: "Q \<in> carrier_mat (m + n) (m + n)"
      and inv_Q: "invertible_mat Q" and A'_QA: "?A' = Q * A" by blast
    have "reduce_below 0 ?non_zero_positions D ?A' = (P * Q) * A" using Q A'_QA P r_PA' A by auto
    moreover have "invertible_mat (P*Q)" using P Q inv_P inv_Q invertible_mult_JNF by blast
    moreover have "(P*Q) \<in> carrier_mat (m + n) (m + n)" using P Q by auto
    ultimately show ?thesis using Find_rw by metis
  next
    case True
    from inv2 obtain P where inv_P: "invertible_mat P" and P: "P \<in> carrier_mat (m + n) (m + n)"
      and r_PA': "reduce_below_abs 0 ?non_zero_positions D ?A' = P * ?A'" by blast
    have Find_rw: "FindPreHNF abs_flag D A = reduce_below_abs 0 ?non_zero_positions D ?A'"
      using n0 A dr_A dc_A True * by (auto simp add: Let_def)
    have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> ?A' = P * A" 
      by (rule A'_swaprows_invertible_mat[OF A], insert non_zero_positions_xs_m n0 m0 l nz_xs_m, auto) 
    from this obtain Q where Q: "Q \<in> carrier_mat (m + n) (m + n)"
      and inv_Q: "invertible_mat Q" and A'_QA: "?A' = Q * A" by blast
    have "reduce_below_abs 0 ?non_zero_positions D ?A' = (P * Q) * A" using Q A'_QA P r_PA' A by auto
    moreover have "invertible_mat (P*Q)" using P Q inv_P inv_Q invertible_mult_JNF by blast
    moreover have "(P*Q) \<in> carrier_mat (m + n) (m + n)" using P Q by auto
    ultimately show ?thesis using Find_rw by metis
  qed     
  qed
qed


corollary FindPreHNF_echelon_form_mx0:
  assumes "A \<in> carrier_mat m 0"
  shows "echelon_form_JNF (FindPreHNF abs_flag D A)"
  by (rule echelon_form_mx0, rule FindPreHNF[OF assms])
               

lemma FindPreHNF_echelon_form_mx1:
  assumes A_def: "A = A'' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A'': "A'' \<in> carrier_mat m n" and n2: "n<2" and D_g0: "D>0" and mn: "m\<ge>n"
shows "echelon_form_JNF (FindPreHNF abs_flag D A)"
proof (cases "n=0")
  case True
  have A: "A \<in> carrier_mat m 0" using A_def A'' True 
    by (metis add.comm_neutral append_rows_def carrier_matD carrier_matI index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3)) 
  show ?thesis unfolding True by (rule FindPreHNF_echelon_form_mx0, insert A, auto)
next
  case False hence n0: "0<n" by auto
  have A: "A \<in> carrier_mat (m+n) n" using A_def A'' by auto
  have m0: "m>0" using mn n2 n0 by auto
  have D0: "D\<noteq>0" using D_g0 by auto
  show ?thesis
  proof (cases "m+n<2")
    case True
    show ?thesis by (rule echelon_form_JNF_1xn[OF _ True], rule FindPreHNF[OF A])
  next
    case False note mn_le_2 = False
    have dr_A: "dim_row A \<ge>2" using False n2 A by auto
    have dc_A: "dim_col A < 2" using n2 A by auto
    let ?non_zero_positions = "filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [Suc 0..<dim_row A]" 
    let ?A' = "(if A $$ (0, 0) \<noteq> 0 then A else let i = ?non_zero_positions ! 0 in swaprows 0 i A)" 
    define xs where "xs = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<m]"
    let ?Reduce = "(if abs_flag then reduce_below_abs else reduce_below)"
    have nz_xs_m: "?non_zero_positions = xs @ [m]" and d_xs: "distinct xs"
      and all_less_m: "\<forall>x\<in>set xs. x < m \<and> 0 < x" 
      using non_zero_positions_xs_m'[OF A_def A'' _ m0 n0 D0] using D0 A unfolding xs_def by auto  
    have *: "FindPreHNF abs_flag D A = (if abs_flag then reduce_below_abs 0 ?non_zero_positions D ?A' 
        else reduce_below 0 ?non_zero_positions D ?A')"
      using dr_A dc_A by (auto simp add: Let_def) 
    have l: "length ?non_zero_positions > 1" if "xs\<noteq>[]" using that unfolding nz_xs_m by auto
    have e: "echelon_form_JNF (reduce_below 0 ?non_zero_positions D ?A')"
    proof (cases "A $$ (0,0) \<noteq>0")
      case True note A00 = True
      have 1: "reduce_below 0 ?non_zero_positions D ?A' = reduce_below 0 ?non_zero_positions D A"
        using True by auto
      have "echelon_form_JNF (reduce_below 0 ?non_zero_positions D A)"
      proof (rule echelon_form_JNF_mx1[OF _ n2]) 
        show "reduce_below 0 ?non_zero_positions D A \<in> carrier_mat (m+n) n" using A by auto
        show "\<forall>i\<in>{1..<m + n}. reduce_below 0 ?non_zero_positions D A $$ (i, 0) = 0"
        proof 
          fix i assume i: "i \<in> {1..<m + n}"
          show "reduce_below 0 ?non_zero_positions D A $$ (i, 0) =0"
          proof (cases "i\<in>set ?non_zero_positions")
            case True
            show ?thesis unfolding nz_xs_m 
              by (rule reduce_below_0_case_m[OF A'' m0 n0 A_def A00 mn _ d_xs all_less_m D_g0],
                  insert nz_xs_m True, auto)
          next
            case False note i_notin_set = False
            have "reduce_below 0 ?non_zero_positions D A $$ (i, 0) = A $$ (i, 0)" unfolding nz_xs_m 
              by (rule reduce_below_preserves_case_m[OF A'' m0 n0 A_def A00 mn _ d_xs all_less_m _ _ _ D_g0],
                  insert i nz_xs_m i_notin_set, auto)
            also have "... = 0" using i_notin_set i A unfolding set_filter by auto
            finally show ?thesis .        
          qed
        qed
      qed
      thus ?thesis using 1 by argo
    next
      case False hence A00: "A $$ (0,0) = 0" by simp
      let ?i = "((xs @ [m]) ! 0)"
      let ?S = "swaprows 0 ?i A"
      let ?S' = "mat_of_rows n (map (Matrix.row (swaprows 0 ?i A)) [0..<m])"
      have rw: "(if A$$(0, 0) \<noteq> 0 then A else let i = ?non_zero_positions!0 in swaprows 0 i A) = ?S"
        using A00 nz_xs_m by auto
      have S: "?S \<in> carrier_mat (m+n) n" using A by auto
      have A00_eq_A'00: "A $$ (0, 0) = A'' $$ (0, 0)" 
        by (metis A'' A_def add_gr_0 append_rows_def n0 carrier_matD index_mat_four_block(1) m0)
      show ?thesis
      proof (cases "xs=[]")
        case True
        have nz_m: "?non_zero_positions = [m]" using True nz_xs_m by simp
        obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (swaprows 0 m A $$ (0, 0)) (swaprows 0 m A $$ (m, 0))"
          by (metis prod_cases5)        
        have Am0: "A $$ (m,0) = D"
        proof -
          have "A $$ (m,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m, 0)"
            by (smt A append_rows_def A_def A'' n0 carrier_matD diff_self_eq_0 index_mat_four_block
                less_add_same_cancel1 less_diff_conv ordered_cancel_comm_monoid_diff_class.diff_add
                nat_less_le)
          also have "... = D" by (simp add: n0)
          finally show ?thesis .
        qed
        have Sm0: "(swaprows 0 m A) $$ (m,0) = 0" using A False n0 by auto
        have S00: "(swaprows 0 m A) $$ (0,0) = D" using A Am0 n0 by auto
        have pquvd2: "(p,q,u,v,d) = euclid_ext2 (A $$ (m, 0)) (A $$ (0, 0))"
          using pquvd Sm0 S00 Am0 A00 by auto
        have "reduce_below 0 ?non_zero_positions D ?A' = reduce 0 m D ?A'" unfolding nz_m by auto
        also have "... = reduce 0 m D (swaprows 0 m A)" using True False rw nz_m by auto
        finally have *: "reduce_below 0 ?non_zero_positions D ?A' = reduce 0 m D (swaprows 0 m A)" .
        have "echelon_form_JNF (reduce 0 m D (swaprows 0 m A))"
        proof (rule echelon_form_JNF_mx1[OF _ n2])
          show "reduce 0 m D (swaprows 0 m A) \<in> carrier_mat (m+n) n"
            using A n2 reduce_carrier by (auto simp add: Let_def) 
          show "\<forall>i\<in>{1..<m+n}. reduce 0 m D (swaprows 0 m A) $$ (i, 0) = 0"
          proof
            fix i assume i: "i \<in> {1..<m+n}"
            show "reduce 0 m D (swaprows 0 m A) $$ (i, 0) = 0"
            proof (cases "i=m")
              case True
              show ?thesis
              proof (unfold True, rule reduce_0[OF _ _ n0])
                show "swaprows 0 m A \<in> carrier_mat (m+n) n" using A by auto
              qed (insert m0 n0 S00 D_g0, auto)
            next
              case False
              have "reduce 0 m D (swaprows 0 m A) $$ (i, 0) = (swaprows 0 m A) $$ (i, 0)"
              proof (rule reduce_preserves[OF _ n0])
                show "swaprows 0 m A \<in> carrier_mat (m+n) n" using A by auto  
              qed (insert m0 n0 S00 D_g0 False i, auto)
              also have "... = A $$ (i, 0)" using i False A n0 by auto
              also have "... = 0"
              proof (rule ccontr)
                assume "A $$ (i, 0) \<noteq> 0" hence "i \<in> set ?non_zero_positions" using i A by auto 
                hence "i=m" using nz_xs_m True by auto
                thus False using False by contradiction
              qed
              finally show ?thesis .
            qed 
          qed
        qed       
        then show ?thesis using * by presburger
      next
        case False        
      have l: "length ?non_zero_positions > 1"    using False nz_xs_m by auto   
      hence l_xs: "length xs > 0" using nz_xs_m by auto
      hence xs_m_less_m: "(xs@[m]) ! 0 < m" by (simp add: all_less_m nth_append)
      have S00: "?S $$ (0,0) \<noteq> 0"
        by (smt A add_pos_pos append_Cons_nth_left n0 carrier_matD index_mat_swaprows(1)
            l_xs m0 mem_Collect_eq nth_mem set_filter xs_def)
      have S': "?S' \<in> carrier_mat m n" using A by auto
      have S_S'D: "?S = ?S' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" by (rule swaprows_append_id[OF A'' A_def xs_m_less_m]) 
      have 2: "reduce_below 0 ?non_zero_positions D ?A' = reduce_below 0 ?non_zero_positions D ?S"
        using A00 nz_xs_m by algebra
      have "echelon_form_JNF (reduce_below 0 ?non_zero_positions D ?S)"
      proof (rule echelon_form_JNF_mx1[OF _ n2])
        show "reduce_below 0 ?non_zero_positions D ?S \<in> carrier_mat (m+n) n" using A by auto
        show "\<forall>i\<in>{1..<m + n}. reduce_below 0 ?non_zero_positions D ?S $$ (i, 0) = 0"
        proof 
          fix i assume i: "i \<in> {1..<m + n}"
          show "reduce_below 0 ?non_zero_positions D ?S $$ (i, 0) =0"
          proof (cases "i\<in>set ?non_zero_positions")
            case True
            show ?thesis unfolding nz_xs_m 
              by (rule reduce_below_0_case_m[OF S' m0 n0 S_S'D S00 mn _ d_xs all_less_m D_g0],
                  insert True nz_xs_m, auto)
          next
            case False note i_notin_set = False
            have "reduce_below 0 ?non_zero_positions D ?S $$ (i, 0) = ?S $$ (i, 0)" unfolding nz_xs_m 
              by (rule reduce_below_preserves_case_m[OF S' m0 n0 S_S'D S00 mn _ d_xs all_less_m _ _ _ D_g0],
                  insert i nz_xs_m i_notin_set, auto)
            also have "... = 0" using i_notin_set i A S00 n0 unfolding set_filter by auto              
            finally show ?thesis .        
          qed
        qed
      qed
      thus ?thesis using 2 by argo
    qed
  qed
    have e2: "echelon_form_JNF (reduce_below_abs 0 ?non_zero_positions D ?A')"
    proof (cases "A $$ (0,0) \<noteq>0")
      case True note A00 = True
      have 1: "reduce_below_abs 0 ?non_zero_positions D ?A' = reduce_below_abs 0 ?non_zero_positions D A"
        using True by auto
      have "echelon_form_JNF (reduce_below_abs 0 ?non_zero_positions D A)"
      proof (rule echelon_form_JNF_mx1[OF _ n2]) 
        show "reduce_below_abs 0 ?non_zero_positions D A \<in> carrier_mat (m+n) n" using A by auto
        show "\<forall>i\<in>{1..<m + n}. reduce_below_abs 0 ?non_zero_positions D A $$ (i, 0) = 0"
        proof 
          fix i assume i: "i \<in> {1..<m + n}"
          show "reduce_below_abs 0 ?non_zero_positions D A $$ (i, 0) =0"
          proof (cases "i\<in>set ?non_zero_positions")
            case True
            show ?thesis unfolding nz_xs_m 
              by (rule reduce_below_abs_0_case_m[OF A'' m0 n0 A_def A00 mn _ d_xs all_less_m D_g0],
                  insert nz_xs_m True, auto)
          next
            case False note i_notin_set = False
            have "reduce_below_abs 0 ?non_zero_positions D A $$ (i, 0) = A $$ (i, 0)" unfolding nz_xs_m 
              by (rule reduce_below_abs_preserves_case_m[OF A'' m0 n0 A_def A00 mn _ d_xs all_less_m _ _ _ D_g0],
                  insert i nz_xs_m i_notin_set, auto)
            also have "... = 0" using i_notin_set i A unfolding set_filter by auto
            finally show ?thesis .        
          qed
        qed
      qed
      thus ?thesis using 1 by argo
    next
      case False hence A00: "A $$ (0,0) = 0" by simp
      let ?i = "((xs @ [m]) ! 0)"
      let ?S = "swaprows 0 ?i A"
      let ?S' = "mat_of_rows n (map (Matrix.row (swaprows 0 ?i A)) [0..<m])"
      have rw: "(if A$$(0, 0) \<noteq> 0 then A else let i = ?non_zero_positions!0 in swaprows 0 i A) = ?S"
        using A00 nz_xs_m by auto
      have S: "?S \<in> carrier_mat (m+n) n" using A by auto
      have A00_eq_A'00: "A $$ (0, 0) = A'' $$ (0, 0)" 
        by (metis A'' A_def add_gr_0 append_rows_def n0 carrier_matD index_mat_four_block(1) m0)
      show ?thesis
      proof (cases "xs=[]")
        case True
        have nz_m: "?non_zero_positions = [m]" using True nz_xs_m by simp
        obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (swaprows 0 m A $$ (0, 0)) (swaprows 0 m A $$ (m, 0))"
          by (metis prod_cases5)        
        have Am0: "A $$ (m,0) = D"
        proof -
          have "A $$ (m,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m, 0)"
            by (smt A append_rows_def A_def A'' n0 carrier_matD diff_self_eq_0 index_mat_four_block
                less_add_same_cancel1 less_diff_conv ordered_cancel_comm_monoid_diff_class.diff_add
                nat_less_le)
          also have "... = D" by (simp add: n0)
          finally show ?thesis .
        qed
        have Sm0: "(swaprows 0 m A) $$ (m,0) = 0" using A False n0 by auto
        have S00: "(swaprows 0 m A) $$ (0,0) = D" using A Am0 n0 by auto
        have pquvd2: "(p,q,u,v,d) = euclid_ext2 (A $$ (m, 0)) (A $$ (0, 0))"
          using pquvd Sm0 S00 Am0 A00 by auto
        have "reduce_below_abs 0 ?non_zero_positions D ?A' = reduce_abs 0 m D ?A'" unfolding nz_m by auto
        also have "... = reduce_abs 0 m D (swaprows 0 m A)" using True False rw nz_m by auto
        finally have *: "reduce_below_abs 0 ?non_zero_positions D ?A' = reduce_abs 0 m D (swaprows 0 m A)" .
        have "echelon_form_JNF (reduce_abs 0 m D (swaprows 0 m A))"
        proof (rule echelon_form_JNF_mx1[OF _ n2])
          show "reduce_abs 0 m D (swaprows 0 m A) \<in> carrier_mat (m+n) n"
            using A n2 reduce_carrier by (auto simp add: Let_def) 
          show "\<forall>i\<in>{1..<m+n}. reduce_abs 0 m D (swaprows 0 m A) $$ (i, 0) = 0"
          proof
            fix i assume i: "i \<in> {1..<m+n}"
            show "reduce_abs 0 m D (swaprows 0 m A) $$ (i, 0) = 0"
            proof (cases "i=m")
              case True
              show ?thesis
              proof (unfold True, rule reduce_0[OF _ _ n0])
                show "swaprows 0 m A \<in> carrier_mat (m+n) n" using A by auto
              qed (insert m0 n0 S00 D_g0, auto)
            next
              case False
              have "reduce_abs 0 m D (swaprows 0 m A) $$ (i, 0) = (swaprows 0 m A) $$ (i, 0)"
              proof (rule reduce_preserves[OF _ n0])
                show "swaprows 0 m A \<in> carrier_mat (m+n) n" using A by auto  
              qed (insert m0 n0 S00 D_g0 False i, auto)
              also have "... = A $$ (i, 0)" using i False A n0 by auto
              also have "... = 0"
              proof (rule ccontr)
                assume "A $$ (i, 0) \<noteq> 0" hence "i \<in> set ?non_zero_positions" using i A by auto 
                hence "i=m" using nz_xs_m True by auto
                thus False using False by contradiction
              qed
              finally show ?thesis .
            qed 
          qed
        qed       
        then show ?thesis using * by presburger
      next
        case False        
      have l: "length ?non_zero_positions > 1"    using False nz_xs_m by auto   
      hence l_xs: "length xs > 0" using nz_xs_m by auto
      hence xs_m_less_m: "(xs@[m]) ! 0 < m" by (simp add: all_less_m nth_append)
      have S00: "?S $$ (0,0) \<noteq> 0"
        by (smt A add_pos_pos append_Cons_nth_left n0 carrier_matD index_mat_swaprows(1)
            l_xs m0 mem_Collect_eq nth_mem set_filter xs_def)
      have S': "?S' \<in> carrier_mat m n" using A by auto
      have S_S'D: "?S = ?S' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" by (rule swaprows_append_id[OF A'' A_def xs_m_less_m]) 
      have 2: "reduce_below_abs 0 ?non_zero_positions D ?A' = reduce_below_abs 0 ?non_zero_positions D ?S"
        using A00 nz_xs_m by algebra
      have "echelon_form_JNF (reduce_below_abs 0 ?non_zero_positions D ?S)"
      proof (rule echelon_form_JNF_mx1[OF _ n2])
        show "reduce_below_abs 0 ?non_zero_positions D ?S \<in> carrier_mat (m+n) n" using A by auto
        show "\<forall>i\<in>{1..<m + n}. reduce_below_abs 0 ?non_zero_positions D ?S $$ (i, 0) = 0"
        proof 
          fix i assume i: "i \<in> {1..<m + n}"
          show "reduce_below_abs 0 ?non_zero_positions D ?S $$ (i, 0) =0"
          proof (cases "i\<in>set ?non_zero_positions")
            case True
            show ?thesis unfolding nz_xs_m 
              by (rule reduce_below_abs_0_case_m[OF S' m0 n0 S_S'D S00 mn _ d_xs all_less_m D_g0],
                  insert True nz_xs_m, auto)
          next
            case False note i_notin_set = False
            have "reduce_below_abs 0 ?non_zero_positions D ?S $$ (i, 0) = ?S $$ (i, 0)" unfolding nz_xs_m 
              by (rule reduce_below_abs_preserves_case_m[OF S' m0 n0 S_S'D S00 mn _ d_xs all_less_m _ _ _ D_g0],
                  insert i nz_xs_m i_notin_set, auto)
            also have "... = 0" using i_notin_set i A S00 n0 unfolding set_filter by auto              
            finally show ?thesis .        
          qed
        qed
      qed
      thus ?thesis using 2 by argo
    qed
  qed
    thus ?thesis using * e by presburger
  qed
qed


lemma FindPreHNF_works_n_ge2:
  assumes A_def: "A = A'' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A'': "A'' \<in> carrier_mat m n" and "n\<ge>2" and m_le_n: "m\<ge>n" and "D>0"
shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> FindPreHNF abs_flag D A = P * A \<and> echelon_form_JNF (FindPreHNF abs_flag D A)"
  using assms
proof (induct abs_flag D A arbitrary: A'' m n rule: FindPreHNF.induct)
  case (1 abs_flag D A)  
  note A_def = "1.prems"(1)
  note A'' = "1.prems"(2)
  note n = "1.prems"(3)
  note m_le_n = "1.prems"(4)
  note D0 = "1.prems"(5)
  let ?RAT = "map_mat rat_of_int"
  have A: "A \<in> carrier_mat (m+n) n" using A_def A'' by auto
  have mn: "2\<le>m+n" using n by auto
  have m0: "0<m" using n m_le_n by auto
  have n0: "0<n" using n by simp
  have D_not0: "D\<noteq>0" using D0 by auto
  define non_zero_positions where "non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]"
  define A' where "A' = (if A $$ (0, 0) \<noteq> 0 then A else let i = non_zero_positions ! 0 in swaprows 0 i A)"
  let ?Reduce = "(if abs_flag then reduce_below_abs else reduce_below)"
  obtain A'_UL A'_UR A'_DL A'_DR where A'_split: "(A'_UL, A'_UR, A'_DL, A'_DR) 
    = split_block (?Reduce 0 non_zero_positions D (make_first_column_positive A')) 1 1"     
    by (metis prod_cases4)
  define sub_PreHNF where "sub_PreHNF = FindPreHNF abs_flag D A'_DR"
  obtain xs where non_zero_positions_xs_m: "non_zero_positions = xs @ [m]" and d_xs: "distinct xs"
    and all_less_m: "\<forall>x\<in>set xs. x < m \<and> 0 < x" 
    using non_zero_positions_xs_m[OF A_def A'' non_zero_positions_def m0 n0] using D0 by fast
  define M where "M = (make_first_column_positive A')"  
  have A': "A' \<in> carrier_mat (m+n) n" unfolding A'_def using A by auto 
  have mk_A'_not0:"make_first_column_positive A' $$ (0,0) \<noteq> 0"
    by (rule make_first_column_positive_00[OF A_def A'' non_zero_positions_def
          A'_def m0 n0 D_not0 m_le_n])  
  have M: "M \<in> carrier_mat (m+n) n" using A' M_def by auto
  let ?M' = "mat_of_rows n (map (Matrix.row (make_first_column_positive A')) [0..<m])"
  have M': "?M' \<in> carrier_mat m n" by auto            
  have M_M'D: "make_first_column_positive A' = ?M' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" if xs_empty: "xs \<noteq> []"
  proof (cases "A$$(0,0) \<noteq> 0")
    case True
    then have *: "make_first_column_positive A' = make_first_column_positive A"
      unfolding A'_def by auto        
    show ?thesis 
      by (unfold *, rule make_first_column_positive_append_id[OF A'' A_def D0 n0])
  next
    case False
    then have *: "make_first_column_positive A' 
                  = make_first_column_positive (swaprows 0 (non_zero_positions ! 0) A)"
      unfolding A'_def by auto
    show ?thesis
    proof (unfold *, rule make_first_column_positive_append_id)
      let ?S = "mat_of_rows n (map (Matrix.row (swaprows 0 (non_zero_positions ! 0) A)) [0..<m])"
      show "swaprows 0 (non_zero_positions ! 0) A =  ?S @\<^sub>r (D \<cdot>\<^sub>m (1\<^sub>m n))"
      proof (rule swaprows_append_id[OF A'' A_def])
        have A''00: "A'' $$ (0, 0) = 0"
          by (metis (no_types, lifting) A A'' A_def False add_sign_intros(2) append_rows_def
              carrier_matD index_mat_four_block m0 n0)
        have length_xs: "length xs > 0" using xs_empty by auto
        have "non_zero_positions ! 0 = xs ! 0" unfolding non_zero_positions_xs_m
          by (meson length_xs nth_append)
        thus "non_zero_positions ! 0 < m" using all_less_m length_xs by simp
      qed
    qed (insert n0 D0, auto)            
  qed
  have A'_DR: "A'_DR \<in> carrier_mat (m + (n-1)) (n-1)"
    by (rule split_block(4)[OF A'_split[symmetric]], insert n M M_def, auto)  
  have sub_PreHNF: "sub_PreHNF \<in> carrier_mat (m + (n -1)) (n-1)"
    unfolding sub_PreHNF_def by (rule FindPreHNF[OF A'_DR])
  hence sub_PreHNF': "sub_PreHNF \<in> carrier_mat (m+n - 1) (n-1)" using n by auto
  have A'_UL: "A'_UL \<in> carrier_mat 1 1"
    by (rule split_block(1)[OF A'_split[symmetric], of "m+n-1" "n-1"], insert n A', auto) 
  have A'_UR: "A'_UR \<in> carrier_mat 1 (n-1)"
    by (rule split_block(2)[OF A'_split[symmetric], of "m+n-1"], insert n A', auto)
  have A'_DL: "A'_DL \<in> carrier_mat (m + (n - 1)) 1"
    by (rule split_block(3)[OF A'_split[symmetric], of _ "n-1"], insert n A', auto)

  show ?case
  proof (cases abs_flag)
    case True note abs_flag = True
      hence A'_split: "(A'_UL, A'_UR, A'_DL, A'_DR) 
    = split_block (reduce_below_abs 0 non_zero_positions D (make_first_column_positive A')) 1 1"   using A'_split by auto
    let ?R = "reduce_below_abs 0 non_zero_positions D (make_first_column_positive A')"
   have fbm_R: "four_block_mat A'_UL A'_UR A'_DL A'_DR 
     = reduce_below_abs 0 non_zero_positions D (make_first_column_positive A')"
    by (rule split_block(5)[symmetric, OF A'_split[symmetric], of "m+n-1" "n-1"], insert A' n, auto)
  have A'_DL0: "A'_DL = (0\<^sub>m (m + (n - 1)) 1)"   
  proof (rule eq_matI)
    show "dim_row A'_DL = dim_row (0\<^sub>m (m + (n - 1)) 1)"
      and "dim_col A'_DL = dim_col (0\<^sub>m (m + (n - 1)) 1)" using A'_DL by auto    
    fix i j assume i: "i < dim_row (0\<^sub>m (m + (n - 1)) 1)" and j: "j < dim_col (0\<^sub>m (m + (n - 1)) 1)"
    have j0: "j=0" using j by auto
    have "0 = ?R $$ (i+1,j)"
    proof (unfold M_def non_zero_positions_xs_m j0, 
        rule reduce_below_abs_0_case_m_make_first_column_positive[symmetric,
          OF A'' m0 n0 A_def m_le_n _  d_xs all_less_m _ _ D0 _ ])
      show "A' = (if A $$ (0, 0) \<noteq> 0 then A else let i = (xs @ [m]) ! 0 in swaprows 0 i A)"
        using A'_def non_zero_positions_def non_zero_positions_xs_m by presburger
      show "xs @ [m] = filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A]"
        using A'_def non_zero_positions_def non_zero_positions_xs_m by presburger
    qed (insert i n0, auto)
    also have "... = four_block_mat A'_UL A'_UR A'_DL A'_DR $$ (i+1,j)" unfolding fbm_R ..
    also have "... = (if i+1 < dim_row A'_UL then if j < dim_col A'_UL 
            then A'_UL $$ (i+1, j) else A'_UR $$ (i+1, j - dim_col A'_UL)
            else if j < dim_col A'_UL then A'_DL $$ (i+1 - dim_row A'_UL, j)
            else A'_DR $$ (i+1 - dim_row A'_UL, j - dim_col A'_UL))"
      by (rule index_mat_four_block, insert A'_UL A'_DR i j, auto)
    also have "... = A'_DL $$ (i, j)" using A'_UL A'_UR i j by auto
    finally show "A'_DL $$ (i, j) = 0\<^sub>m (m + (n - 1)) 1 $$ (i, j)" using i j by auto
  qed

  let ?A'_DR_m = "mat_of_rows (n-1) [Matrix.row A'_DR i. i \<leftarrow> [0..<m]]"
  have A'_DR_m: "?A'_DR_m \<in> carrier_mat m (n-1)" by auto
  have A'DR_A'DR_m_D: "A'_DR = ?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1)"
  proof (rule eq_matI)
    show dr: "dim_row A'_DR = dim_row (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1))" 
      by (metis A'_DR A'_DR_m append_rows_def carrier_matD(1) index_mat_four_block(2) 
          index_one_mat(2) index_smult_mat(2) index_zero_mat(2))
    show dc: "dim_col A'_DR = dim_col (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1))"
      by (metis A'_DR A'_DR_m add.comm_neutral append_rows_def
          carrier_matD(2) index_mat_four_block(3) index_zero_mat(3))  
    fix i j assume i: "i < dim_row(?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1))"
      and j: "j<dim_col (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1))"
    have jn1: "j<n-1" using dc j A'_DR by auto
    show "A'_DR $$ (i,j) = (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i,j)"
    proof (cases "i<m")
      case True
      have "A'_DR $$ (i,j) = ?A'_DR_m $$ (i,j)"
        by (metis A'_DR A'_DR_m True dc carrier_matD(1) carrier_matD(2) j le_add1 
            map_first_rows_index mat_of_rows_carrier(2) mat_of_rows_index)
      also have "... = (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i,j)"
        by (metis (mono_tags, lifting) A'_DR A'_DR_m True append_rows_def 
            carrier_matD dc i index_mat_four_block j)
      finally show ?thesis .
    next
      case False note i_ge_m = False
      let ?reduce_below = "reduce_below_abs 0 non_zero_positions D (make_first_column_positive A')"
      have 1: "(?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i,j) = (D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i-m,j)"
        by (smt A'_DR A'_DR_m False append_rows_nth carrier_matD carrier_mat_triv dc dr i
            index_one_mat(2) index_one_mat(3) index_smult_mat(2,3) j)
      have "?reduce_below = four_block_mat A'_UL A'_UR A'_DL A'_DR" using fbm_R ..
      also have "... $$ (i+1,j+1) = (if i+1 < dim_row A'_UL then if j+1 < dim_col A'_UL 
              then A'_UL $$ (i+1, j+1) else A'_UR $$ (i+1, j+1 - dim_col A'_UL)
              else if j+1 < dim_col A'_UL then A'_DL $$ (i+1 - dim_row A'_UL, j+1)
              else A'_DR $$ (i+1 - dim_row A'_UL, j+1 - dim_col A'_UL))"
        by (rule index_mat_four_block, insert i j A'_UL A'_DR dr dc, auto)
      also have "... = A'_DR $$ (i,j)" using A'_UL by auto
      finally have 2: "?reduce_below $$ (i+1,j+1) = A'_DR $$ (i,j)" .
      show ?thesis 
      proof (cases "xs = []")
        case True note xs_empty = True
        have i1_m: "i + 1 \<noteq> m" 
          using False less_add_one by blast
        have j1n: "j+1<n"
          using jn1 less_diff_conv by blast
        have i1_mn: "i+1<m + n"
          using i i_ge_m
          by (metis A'_DR carrier_matD(1) dr less_diff_conv sub_PreHNF sub_PreHNF')
        have "?reduce_below = reduce_abs 0 m D M"
          unfolding non_zero_positions_xs_m xs_empty M_def by auto
        also have "... $$ (i+1,j+1) = M $$ (i+1, j+1)"
          by (rule reduce_preserves[OF M j1n _ i1_m _ i1_mn], insert M_def mk_A'_not0, auto)         
        also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ ((i+1)-m, j+1)"
        proof (cases "A $$ (0,0) = 0")
          case True
          let ?S = "(swaprows 0 m A)"
          have S: "?S \<in> carrier_mat (m+n) n" using A by auto
          have Si10: "?S $$ (i+1,0) = 0"
          proof -
            have "?S $$ (i+1,0) = A $$ (i+1,0)" using i1_m n0 i1_mn S by auto
            also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1 - m,0)"
              by (smt A_def A'' A i_ge_m append_rows_def carrier_matD diff_add_inverse2 i1_mn 
                  index_mat_four_block less_imp_diff_less n0)
            also have "... = 0" using i_ge_m n0 i1_mn by auto
            finally show ?thesis .
          qed
          have "M $$ (i+1, j+1) = (make_first_column_positive ?S) $$ (i+1,j+1)"
            by (simp add: A'_def M_def True non_zero_positions_xs_m xs_empty)
          also have "... = (if ?S $$ (i+1,0) < 0 then - ?S $$ (i+1,j+1) else ?S $$ (i+1,j+1))" 
            unfolding make_first_column_positive.simps using S i1_mn j1n by auto
          also have "... = ?S $$ (i+1,j+1)" using Si10 by auto
          also have "... = A $$ (i+1,j+1)" using i1_m n0 i1_mn S jn1 by auto
          also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1 - m,j+1)"
            by (smt A_def A'' A i_ge_m append_rows_def carrier_matD i1_mn index_mat_four_block(1,3)
                index_one_mat(2) index_smult_mat(2) index_zero_mat(2) j1n less_imp_diff_less add_diff_cancel_right')
          finally show ?thesis .
        next
          case False         
          have Ai10: "A $$ (i+1,0) = 0"
          proof -
            have "A $$ (i+1,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1 - m,0)"
              by (smt A_def A'' A i_ge_m append_rows_def carrier_matD diff_add_inverse2 i1_mn 
                  index_mat_four_block less_imp_diff_less n0)
            also have "... = 0" using i_ge_m n0 i1_mn by auto
            finally show ?thesis .
          qed          
          have "M $$ (i+1, j+1) = (make_first_column_positive A) $$ (i+1,j+1)"
            by (simp add: A'_def M_def False True non_zero_positions_xs_m)
          also have "... = (if A $$ (i+1,0) < 0 then - A $$ (i+1,j+1) else A $$ (i+1,j+1))" 
            unfolding make_first_column_positive.simps using A i1_mn j1n by auto
          also have "... = A $$ (i+1,j+1)" using Ai10 by auto
          also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1 - m,j+1)"
            by (smt A_def A'' A i_ge_m append_rows_def carrier_matD i1_mn index_mat_four_block(1,3)
                index_one_mat(2) index_smult_mat(2) index_zero_mat(2) j1n less_imp_diff_less add_diff_cancel_right')
          finally show ?thesis .
        qed
        also have "... = D * (1\<^sub>m n) $$ ((i+1)-m, j+1)"
          by (rule index_smult_mat, insert i jn1 A'_DR False dr, auto)            
        also have "... = D *(1\<^sub>m (n - 1)) $$ (i-m,j)" using dc dr i j A'_DR i_ge_m
          by (smt Nat.add_diff_assoc2 carrier_matD(1) index_one_mat(1) jn1 less_diff_conv 
              linorder_not_less add_diff_cancel_right' add_diff_cancel_right' add_diff_cancel_left')
        also have "... = (D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i-m,j)"
          by (rule index_smult_mat[symmetric], insert i jn1 A'_DR False dr, auto)
        finally show ?thesis using 1 2 by auto
      next
        case False     
      have "?reduce_below $$ (i+1, j+1) = M $$ (i+1, j+1)"
      proof (unfold non_zero_positions_xs_m M_def,
          rule reduce_below_abs_preserves_case_m[OF M' m0 _ M_M'D mk_A'_not0 m_le_n _ d_xs all_less_m _ _ _ D0])            
        show "j + 1 < n" using jn1 by auto
        show "i + 1 \<notin> set xs" using all_less_m i_ge_m non_zero_positions_xs_m by auto
        show "i + 1 \<noteq> 0" by auto
        show " i + 1 < m + n" using i_ge_m i dr A'_DR by auto
        show " i + 1 \<noteq> m" using i_ge_m by auto
      qed (insert False)
      also have "... = (?M' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1, j+1)" unfolding M_def using False M_M'D by argo
      also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ ((i+1)-m, j+1)"
      proof -
        have f1: "1 + j < n"
          by (metis Groups.add_ac(2) jn1 less_diff_conv)
        have f2: "\<forall>n. \<not> n + i < m"
          by (meson i_ge_m linorder_not_less nat_SN.compat not_add_less2)
        have "i < m + (n - 1)"
          by (metis (no_types) A'_DR carrier_matD(1) dr i)
        then have "1 + i < m + n"
          using f1 by linarith
        then show ?thesis
          using f2 f1 by (metis (no_types) Groups.add_ac(2) M' append_rows_def carrier_matD(1) 
              dim_col_mat(1) index_mat_four_block(1) index_one_mat(2) index_smult_mat(2) 
              index_zero_mat(2,3) mat_of_rows_def nat_arith.rule0)
      qed
      also have "... = D * (1\<^sub>m n) $$ ((i+1)-m, j+1)"
        by (rule index_smult_mat, insert i jn1 A'_DR False dr, auto)            
      also have "... = D *(1\<^sub>m (n - 1)) $$ (i-m,j)" using dc dr i j A'_DR i_ge_m
        by (smt Nat.add_diff_assoc2 carrier_matD(1) index_one_mat(1) jn1 less_diff_conv 
            linorder_not_less add_diff_cancel_right' add_diff_cancel_left')
      also have "... = (D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i-m,j)"
        by (rule index_smult_mat[symmetric], insert i jn1 A'_DR False dr, auto)
      finally have 3: "?reduce_below $$ (i+1,j+1) = (D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i-m,j)" .            
      show ?thesis using 1 2 3 by presburger
    qed              
  qed
qed
  let ?A'_DR_n = "mat_of_rows (n - 1) (map (Matrix.row A'_DR) [0..<n - 1])"
  have hyp: "\<exists>P. P\<in>carrier_mat (m + (n-1)) (m + (n-1)) \<and> invertible_mat P \<and> sub_PreHNF = P * A'_DR 
  \<and> echelon_form_JNF sub_PreHNF" 
  proof (cases "2 \<le> n - 1")
    case True
    show ?thesis
      by (unfold sub_PreHNF_def, rule "1.hyps"[OF _ _ _ non_zero_positions_def A'_def _ _ _ _ _])
         (insert A n D0 m_le_n True A'DR_A'DR_m_D A A'_split abs_flag, auto)
  next
    case False
    have "\<exists>P. P\<in>carrier_mat (m + (n-1)) (m + (n-1)) \<and> invertible_mat P \<and> sub_PreHNF = P * A'_DR"
      by (unfold sub_PreHNF_def, rule FindPreHNF_invertible_mat_mx2
          [OF A'DR_A'DR_m_D A'_DR_m _ _ D0 _])
          (insert False m_le_n n0 m0 "1"(4), auto)
    moreover have "echelon_form_JNF sub_PreHNF" unfolding sub_PreHNF_def 
      by (rule FindPreHNF_echelon_form_mx1[OF A'DR_A'DR_m_D A'_DR_m _ D0 _],
          insert False n0 m_le_n, auto) 
    ultimately show ?thesis by simp
  qed  
  from this obtain P where P: "P \<in> carrier_mat (m + (n - 1)) (m + (n - 1))"
    and inv_P: "invertible_mat P" and sub_PreHNF_P_A'_DR: "sub_PreHNF = P * A'_DR" by blast
  define P' where "P' = (four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (m+(n-1))) (0\<^sub>m (m+(n-1)) 1) P)"
  have P': "P' \<in> carrier_mat (m+n) (m+n)" 
  proof -
    have "P' \<in> carrier_mat (1 + (m+(n-1))) (1 + (m+(n-1))) "
      unfolding P'_def by (rule four_block_carrier_mat[OF _ P], simp) 
    thus ?thesis using n by auto
  qed
  have inv_P': "invertible_mat P'" 
    unfolding P'_def by (rule invertible_mat_four_block_mat_lower_right[OF P inv_P])
  have dr_A2: "dim_row A \<ge> 2" using A m0 n by auto
  have dc_A2: "dim_col A \<ge> 2" using n A by blast
  have *: "(dim_col A = 0) = False" using dc_A2 by auto
  have FindPreHNF_as_fbm: "FindPreHNF abs_flag D A = four_block_mat A'_UL A'_UR A'_DL sub_PreHNF" 
    unfolding FindPreHNF.simps[of abs_flag D A] using A'_split mn n A dr_A2 dc_A2 abs_flag
    unfolding Let_def sub_PreHNF_def M_def A'_def non_zero_positions_def *    
    by (smt (z3) linorder_not_less split_conv)
  also have "... = P' * (reduce_below_abs 0 non_zero_positions D M)"
  proof -
    have "P' * (reduce_below_abs 0 non_zero_positions D M) 
      = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (m + (n - 1))) (0\<^sub>m (m + (n - 1)) 1) P 
      * four_block_mat A'_UL A'_UR A'_DL A'_DR"
      unfolding P'_def fbm_R[unfolded M_def[symmetric], symmetric] ..
    also have "... = four_block_mat 
            ((1\<^sub>m 1) * A'_UL + (0\<^sub>m 1 (m + (n - 1)) * A'_DL)) 
            ((1\<^sub>m 1) * A'_UR + (0\<^sub>m 1 (m + (n - 1))) * A'_DR) 
            ((0\<^sub>m (m + (n - 1)) 1) * A'_UL + P * A'_DL) 
            ((0\<^sub>m (m + (n - 1)) 1) * A'_UR + P * A'_DR)" 
      by (rule mult_four_block_mat[OF _ _ _ P A'_UL A'_UR A'_DL A'_DR], auto)
    also have "... = four_block_mat A'_UL A'_UR (P * A'_DL) (P * A'_DR)"
      by (rule cong_four_block_mat, insert A'_UL A'_UR A'_DL A'_DR P, auto)
    also have "... = four_block_mat A'_UL A'_UR (0\<^sub>m (m + (n - 1)) 1) sub_PreHNF"
      unfolding A'_DL0 sub_PreHNF_P_A'_DR using P by simp
    also have "... = four_block_mat A'_UL A'_UR A'_DL sub_PreHNF"
      unfolding A'_DL0 by simp
    finally show ?thesis ..
  qed
  finally have Find_P'_reduceM: "FindPreHNF abs_flag D A =  P' * (reduce_below_abs 0 non_zero_positions D M)" .
  have "\<exists>Q. invertible_mat Q \<and> Q \<in> carrier_mat (m + n) (m + n) 
    \<and> reduce_below_abs 0 (xs @ [m]) D M = Q * M"
  proof (cases "xs = []")
    case True note xs_empty = True
    have rw: "reduce_below_abs 0 (xs @ [m]) D M = reduce_abs 0 m D M" using True by auto
    obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 (M $$ (0, 0)) (M $$ (m, 0))"
      by (simp add: euclid_ext2_def)
    have "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) \<and> reduce_abs 0 m D M = P * M"  
    proof (rule reduce_abs_invertible_mat_case_m[OF _ _ m0 _ _ _ _ m_le_n n0 pquvd])
          show "M $$ (0, 0) \<noteq> 0" 
            using M_def mk_A'_not0 by blast
          define M' where  "M' = mat_of_rows n (map (Matrix.row M) [0..<m])"
          define M'' where "M'' = mat_of_rows n (map (Matrix.row M) [m..<m+n])"
          define A2 where "A2 = Matrix.mat (dim_row M) (dim_col M)
          (\<lambda>(i, k). if i = 0 then p * M $$ (0, k) + q * M $$ (m, k) 
                    else if i = m then u * M $$ (0, k) + v * M $$ (m, k)
                    else M $$ (i, k))"
          show M_M'_M'': "M = M' @\<^sub>r M''" unfolding M'_def M''_def            
            by (metis M append_rows_split carrier_matD le_add1)
          show M': "M' \<in> carrier_mat m n" unfolding M'_def by fastforce
          show M'': "M'' \<in> carrier_mat n n" unfolding M''_def by fastforce
          show "0 \<noteq> m" using m0 by simp
          show "A2 = Matrix.mat (dim_row M) (dim_col M)
          (\<lambda>(i, k). if i = 0 then p * M $$ (0, k) + q * M $$ (m, k) 
                    else if i = m then u * M $$ (0, k) + v * M $$ (m, k)
                    else M $$ (i, k))"
            (is "_ = ?rhs") using A A2_def by auto
          define xs' where "xs' =  filter (\<lambda>i. abs (A2 $$ (0,i)) > D) [0..<n]"
          define ys' where  "ys' = filter (\<lambda>i. abs (A2 $$ (m,i)) > D) [0..<n]"
          show "xs' = filter (\<lambda>i. abs (A2 $$ (0,i)) > D) [0..<n]" unfolding xs'_def by auto
          show "ys' = filter (\<lambda>i. abs (A2 $$ (m,i)) > D) [0..<n]" unfolding ys'_def by auto
          have M''D: "(M'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. M'' $$ (j, j') = 0)"
            if jn: "j<n" and j0: "j>0" for j
          proof -
            have Ajm0: "A $$ (j+m,0) = 0"
            proof -
              have "A $$ (j+m,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j+m-m,0)"
                by (smt "1"(2) "1"(3) M M' M'' M_M'_M'' add.commute append_rows_def carrier_matD
                    diff_add_inverse2 index_mat_four_block index_one_mat(2) index_smult_mat(2)
                    le_add2 less_diff_conv2 n0 not_add_less2 that(1))
              also have "... = 0" using jn j0 by auto
              finally show ?thesis .
            qed
            have "M'' $$ (j, i) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)" if i_n: "i<n" for i
            proof (cases "A$$(0,0) = 0")
              case True 
              have "M'' $$ (j, i) = make_first_column_positive (swaprows 0 m A) $$ (j+m,i)"                
                by (smt A'_def Groups.add_ac(2) M' M'' M_M'_M'' M_def True append.simps(1) 
                    append_rows_nth3 diff_add_inverse2 jn le_add2 local.non_zero_positions_xs_m
                    nat_add_left_cancel_less nth_Cons_0 that xs_empty)
              also have "... = A $$ (j+m,i)" using A jn j0 i_n Ajm0 by auto
              also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)"
                by (smt A Groups.add_ac(2) add_mono_thms_linordered_field(1) append_rows_def A_def A'' i_n
                    carrier_matD index_mat_four_block(1,2) add_diff_cancel_right' not_add_less2 jn trans_less_add1)
              finally show ?thesis .            
            next
              case False
              have "A' = A" unfolding A'_def non_zero_positions_xs_m using False True by auto
              hence "M'' $$ (j, i) = make_first_column_positive A $$ (j+m,i)"                
                by (smt m_le_n M' M'' M_M'_M'' M_def append_rows_nth2 jn nat_SN.compat that)                
              also have "... = A $$ (j+m,i)" using A jn j0 i_n Ajm0 by auto
              also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)"
                by (smt A Groups.add_ac(2) add_mono_thms_linordered_field(1) append_rows_def A_def A'' i_n
                    carrier_matD index_mat_four_block(1,2) add_diff_cancel_right' not_add_less2 jn trans_less_add1)
              finally show ?thesis .
            qed                           
            thus ?thesis using jn j0 by auto
          qed
          have Am0D: "A$$(m,0) = D"
          proof -
            have "A$$(m,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m,0)"
              by (smt "1"(2) "1"(3) M M' M'' M_M'_M'' append_rows_def carrier_matD
                  diff_less_mono2 diff_self_eq_0 index_mat_four_block index_one_mat(2) 
                  index_smult_mat(2) less_add_same_cancel1 n0 semiring_norm(137))
            also have "... = D" using m0 n0 by auto
            finally show ?thesis .
          qed
          hence S00D: "(swaprows 0 m A) $$ (0,0) = D" using n0 m0 A by auto
          have Sm00: "(swaprows 0 m A) $$ (m,0) = A$$(0,0)" using n0 m0 A by auto
          have M00D: "M $$ (0, 0) = D" if A00: "A$$(0,0) = 0"
          proof -
            have "M $$ (0,0) = (make_first_column_positive (swaprows 0 m A)) $$ (0,0)"
              unfolding M_def A'_def using A00
              by (simp add: True non_zero_positions_xs_m)
            also have "... = (if (swaprows 0 m A) $$ (0,0) < 0 then - (swaprows 0 m A) $$(0,0)
                              else (swaprows 0 m A) $$(0,0))"
              unfolding make_first_column_positive.simps using m0 n0 A by auto
            also have "... = (swaprows 0 m A) $$(0,0)" using S00D D0 by auto
            also have "... = D" using S00D by auto
            finally show ?thesis .
          qed
          have Mm00: "M $$ (m, 0) = 0" if A00: "A$$(0,0) = 0"
          proof -
            have "M $$ (m,0) = (make_first_column_positive (swaprows 0 m A)) $$ (m,0)"
              unfolding M_def A'_def using A00
              by (simp add: True non_zero_positions_xs_m)
            also have "... = (if (swaprows 0 m A) $$ (m,0) < 0 then - (swaprows 0 m A) $$(m,0)
                              else (swaprows 0 m A) $$(m,0))"
              unfolding make_first_column_positive.simps using m0 n0 A by auto
            also have "... = (swaprows 0 m A) $$(m,0)" using Sm00 A00 D0 by auto
            also have "... = 0" using Sm00 A00 by auto
            finally show ?thesis .
          qed
          have M000: "M $$ (0, 0) = abs (A$$(0,0))" if A00: "A$$(0,0) \<noteq> 0"
          proof -
            have "M $$ (0,0) = (make_first_column_positive A) $$ (0,0)"
              unfolding M_def A'_def using A00
              by (simp add: True non_zero_positions_xs_m)
            also have "... = (if A $$ (0,0) < 0 then - A $$(0,0)
                              else A $$(0,0))"
              unfolding make_first_column_positive.simps using m0 n0 A by auto
            also have "... = abs (A$$(0,0))" using Sm00 A00 by auto
            finally show ?thesis .
          qed
          have Mm0D: "M $$ (m, 0) = D" if A00: "A $$ (0,0) \<noteq> 0"
          proof -
            have "M $$ (m,0) = (make_first_column_positive A) $$ (m,0)"
              unfolding M_def A'_def using A00
              by (simp add: True non_zero_positions_xs_m)
            also have "... = (if A $$ (m,0) < 0 then - A $$(m,0)
                              else A $$(m,0))"
              unfolding make_first_column_positive.simps using m0 n0 A by auto
            also have "... = A $$(m,0)" using S00D D0 Am0D by auto
            also have "... = D" using Am0D D0 by auto
            finally show ?thesis .
          qed
          have "0 \<notin> set xs'"
          proof -
            have "A2 $$ (0,0) = p * M $$ (0, 0) + q * M $$ (m, 0)" 
              using A A2_def n0 M by auto
            also have "... = gcd (M $$ (0, 0)) (M $$ (m, 0))"
              by (metis euclid_ext2_works(1,2) pquvd)
            also have "abs ... \<le> D" using M00D Mm00 M000 Mm0D using gcd_0_int D0 by fastforce
            finally have "abs (A2 $$ (0,0)) \<le> D" .
            thus ?thesis unfolding xs'_def using D0 by auto
          qed
          thus "\<forall>j\<in>set xs'. j<n \<and> (M'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. M'' $$ (j, j') = 0)"  
            using M''D xs'_def by auto
          have "0 \<notin> set ys'"
          proof -
            have "A2 $$ (m,0) = u * M $$ (0, 0) + v * M $$ (m, 0)"
              using A A2_def n0 m0 M by auto
            also have "... = - M $$ (m, 0) div gcd (M $$ (0, 0)) (M $$ (m, 0)) * M $$ (0, 0) 
                + M $$ (0, 0) div gcd (M $$ (0, 0)) (M $$ (m, 0)) * M $$ (m, 0) "
              by (simp add: euclid_ext2_works[OF pquvd[symmetric]])
            also have "... = 0" using M00D Mm00 M000 Mm0D
              by (smt dvd_div_mult_self euclid_ext2_works(3) euclid_ext2_works(5)
                  more_arith_simps(11) mult.commute mult_minus_left pquvd semiring_gcd_class.gcd_dvd1)
            finally have "A2 $$ (m,0) = 0" .
            thus ?thesis unfolding ys'_def using D0 by auto
          qed
          thus "\<forall>j\<in>set ys'. j<n \<and> (M'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. M'' $$ (j, j') = 0)"
            using M''D ys'_def by auto   
        qed (insert D0)
        then show ?thesis using rw by auto
  next
    case False
    show ?thesis
      by (unfold M_def, rule reduce_below_abs_invertible_mat_case_m[OF M' m0 n0 M_M'D[OF False] 
          mk_A'_not0 m_le_n d_xs all_less_m D0])
  qed
   
  from this obtain Q where inv_Q: "invertible_mat Q" and Q: "Q \<in> carrier_mat (m + n) (m + n)"
    and reduce_QM: "reduce_below_abs 0 (xs @ [m]) D M = Q * M" by blast
  have "\<exists>R. invertible_mat R 
    \<and> R \<in> carrier_mat (dim_row A') (dim_row A') \<and> M = R * A'"
    by (unfold M_def, rule make_first_column_positive_invertible)
  from this obtain R where inv_R: "invertible_mat R"
    and R: "R \<in> carrier_mat (dim_row A') (dim_row A')" and M_RA': "M = R * A'" by blast
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> A' = P * A" 
    by (rule A'_swaprows_invertible_mat[OF A A'_def non_zero_positions_def],
        insert non_zero_positions_xs_m n m0, auto)
  from this obtain S where inv_S: "invertible_mat S"
   and S: "S \<in> carrier_mat (dim_row A) (dim_row A)" and A'_SA: "A' = S * A" 
    using A by auto
  have "(P'*Q*R*S) \<in> carrier_mat (m+n) (m+n)" using P' Q R S A' A by auto
  moreover have "FindPreHNF abs_flag D A = (P'*Q*R*S) * A" using Find_P'_reduceM reduce_QM 
    unfolding  M_RA' A'_SA M_def
    by (smt A' A'_SA P' Q R S assoc_mult_mat carrier_matD carrier_mat_triv index_mult_mat(2,3) 
        non_zero_positions_xs_m)
  moreover have "invertible_mat (P'*Q*R*S)" using inv_P' inv_Q inv_R inv_S using P' Q R S A' A 
    by (metis carrier_matD carrier_mat_triv index_mult_mat(2,3) invertible_mult_JNF)
  ultimately have exists_inv: "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P 
    \<and> FindPreHNF abs_flag D A = P * A" by blast
  moreover have "echelon_form_JNF (FindPreHNF abs_flag D A)" 
  proof (rule echelon_form_four_block_mat[OF A'_UL A'_UR sub_PreHNF'   ])
    show "FindPreHNF abs_flag D A = four_block_mat A'_UL A'_UR (0\<^sub>m (m + n - 1) 1) sub_PreHNF" 
      using A'_DL0 FindPreHNF_as_fbm sub_PreHNF sub_PreHNF' by auto
    have "A'_UL $$ (0, 0) = ?R $$ (0,0)"
      by (metis (mono_tags, lifting) A A'_DR A'_UL Find_P'_reduceM M_def 
          \<open>FindPreHNF abs_flag D A = P' * Q * R * S * A\<close> add_Suc_right add_sign_intros(2) carrier_matD fbm_R
          index_mat_four_block(1,3) index_mult_mat(3) m0 n0 plus_1_eq_Suc
          zero_less_one_class.zero_less_one)
    also have "... \<noteq> 0"
    proof (cases "xs=[]")
      case True
      have "?R $$ (0,0) = reduce_abs 0 m D M $$ (0,0)"
        unfolding non_zero_positions_xs_m True M_def by simp
      also have "... \<noteq> 0"
        by (metis D_not0 M M_def add_pos_pos less_add_same_cancel1 m0 mk_A'_not0 n0 reduce_not0)
      finally show ?thesis .
    next
      case False
      show ?thesis
        by (unfold non_zero_positions_xs_m,
          rule reduce_below_abs_not0_case_m[OF M' m0 n0 M_M'D[OF False] mk_A'_not0 m_le_n all_less_m D_not0])     
    qed       
    finally show "A'_UL $$ (0, 0) \<noteq> 0" .
  qed (insert mn n hyp, auto)
  ultimately show ?thesis by blast
  next
    case False
      hence A'_split: "(A'_UL, A'_UR, A'_DL, A'_DR) 
    = split_block (reduce_below 0 non_zero_positions D (make_first_column_positive A')) 1 1"   using A'_split by auto
    let ?R = "reduce_below 0 non_zero_positions D (make_first_column_positive A')"
   have fbm_R: "four_block_mat A'_UL A'_UR A'_DL A'_DR 
     = reduce_below 0 non_zero_positions D (make_first_column_positive A')"
    by (rule split_block(5)[symmetric, OF A'_split[symmetric], of "m+n-1" "n-1"], insert A' n, auto)
  have A'_DL0: "A'_DL = (0\<^sub>m (m + (n - 1)) 1)"   
  proof (rule eq_matI)
    show "dim_row A'_DL = dim_row (0\<^sub>m (m + (n - 1)) 1)"
      and "dim_col A'_DL = dim_col (0\<^sub>m (m + (n - 1)) 1)" using A'_DL by auto    
    fix i j assume i: "i < dim_row (0\<^sub>m (m + (n - 1)) 1)" and j: "j < dim_col (0\<^sub>m (m + (n - 1)) 1)"
    have j0: "j=0" using j by auto
    have "0 = ?R $$ (i+1,j)"
    proof (unfold M_def non_zero_positions_xs_m j0, 
        rule reduce_below_0_case_m_make_first_column_positive[symmetric,
          OF A'' m0 n0 A_def m_le_n _  d_xs all_less_m _ _ D0 _ ])
      show "A' = (if A $$ (0, 0) \<noteq> 0 then A else let i = (xs @ [m]) ! 0 in swaprows 0 i A)"
        using A'_def non_zero_positions_def non_zero_positions_xs_m by presburger
      show "xs @ [m] = filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A]"
        using A'_def non_zero_positions_def non_zero_positions_xs_m by presburger
    qed (insert i n0, auto)
    also have "... = four_block_mat A'_UL A'_UR A'_DL A'_DR $$ (i+1,j)" unfolding fbm_R ..
    also have "... = (if i+1 < dim_row A'_UL then if j < dim_col A'_UL 
            then A'_UL $$ (i+1, j) else A'_UR $$ (i+1, j - dim_col A'_UL)
            else if j < dim_col A'_UL then A'_DL $$ (i+1 - dim_row A'_UL, j)
            else A'_DR $$ (i+1 - dim_row A'_UL, j - dim_col A'_UL))"
      by (rule index_mat_four_block, insert A'_UL A'_DR i j, auto)
    also have "... = A'_DL $$ (i, j)" using A'_UL A'_UR i j by auto
    finally show "A'_DL $$ (i, j) = 0\<^sub>m (m + (n - 1)) 1 $$ (i, j)" using i j by auto
  qed

  let ?A'_DR_m = "mat_of_rows (n-1) [Matrix.row A'_DR i. i \<leftarrow> [0..<m]]"
  have A'_DR_m: "?A'_DR_m \<in> carrier_mat m (n-1)" by auto
  have A'DR_A'DR_m_D: "A'_DR = ?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1)"
  proof (rule eq_matI)
    show dr: "dim_row A'_DR = dim_row (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1))" 
      by (metis A'_DR A'_DR_m append_rows_def carrier_matD(1) index_mat_four_block(2) 
          index_one_mat(2) index_smult_mat(2) index_zero_mat(2))
    show dc: "dim_col A'_DR = dim_col (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1))"
      by (metis A'_DR A'_DR_m add.comm_neutral append_rows_def
          carrier_matD(2) index_mat_four_block(3) index_zero_mat(3))  
    fix i j assume i: "i < dim_row(?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1))"
      and j: "j<dim_col (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1))"
    have jn1: "j<n-1" using dc j A'_DR by auto
    show "A'_DR $$ (i,j) = (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i,j)"
    proof (cases "i<m")
      case True
      have "A'_DR $$ (i,j) = ?A'_DR_m $$ (i,j)"
        by (metis A'_DR A'_DR_m True dc carrier_matD(1) carrier_matD(2) j le_add1 
            map_first_rows_index mat_of_rows_carrier(2) mat_of_rows_index)
      also have "... = (?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i,j)"
        by (metis (mono_tags, lifting) A'_DR A'_DR_m True append_rows_def 
            carrier_matD dc i index_mat_four_block j)
      finally show ?thesis .
    next
      case False note i_ge_m = False
      let ?reduce_below = "reduce_below 0 non_zero_positions D (make_first_column_positive A')"
      have 1: "(?A'_DR_m @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i,j) = (D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i-m,j)"
        by (smt A'_DR A'_DR_m False append_rows_nth carrier_matD carrier_mat_triv dc dr i
            index_one_mat(2) index_one_mat(3) index_smult_mat(2,3) j)
      have "?reduce_below = four_block_mat A'_UL A'_UR A'_DL A'_DR" using fbm_R ..
      also have "... $$ (i+1,j+1) = (if i+1 < dim_row A'_UL then if j+1 < dim_col A'_UL 
              then A'_UL $$ (i+1, j+1) else A'_UR $$ (i+1, j+1 - dim_col A'_UL)
              else if j+1 < dim_col A'_UL then A'_DL $$ (i+1 - dim_row A'_UL, j+1)
              else A'_DR $$ (i+1 - dim_row A'_UL, j+1 - dim_col A'_UL))"
        by (rule index_mat_four_block, insert i j A'_UL A'_DR dr dc, auto)
      also have "... = A'_DR $$ (i,j)" using A'_UL by auto
      finally have 2: "?reduce_below $$ (i+1,j+1) = A'_DR $$ (i,j)" .
      show ?thesis 
      proof (cases "xs = []")
        case True note xs_empty = True
        have i1_m: "i + 1 \<noteq> m" 
          using False less_add_one by blast
        have j1n: "j+1<n"
          using jn1 less_diff_conv by blast
        have i1_mn: "i+1<m + n"
          using i i_ge_m
          by (metis A'_DR carrier_matD(1) dr less_diff_conv sub_PreHNF sub_PreHNF')
        have "?reduce_below = reduce 0 m D M"
          unfolding non_zero_positions_xs_m xs_empty M_def by auto
        also have "... $$ (i+1,j+1) = M $$ (i+1, j+1)"
          by (rule reduce_preserves[OF M j1n _ i1_m _ i1_mn], insert M_def mk_A'_not0, auto)         
        also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ ((i+1)-m, j+1)"
        proof (cases "A $$ (0,0) = 0")
          case True
          let ?S = "(swaprows 0 m A)"
          have S: "?S \<in> carrier_mat (m+n) n" using A by auto
          have Si10: "?S $$ (i+1,0) = 0"
          proof -
            have "?S $$ (i+1,0) = A $$ (i+1,0)" using i1_m n0 i1_mn S by auto
            also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1 - m,0)"
              by (smt A_def A'' A i_ge_m append_rows_def carrier_matD diff_add_inverse2 i1_mn 
                  index_mat_four_block less_imp_diff_less n0)
            also have "... = 0" using i_ge_m n0 i1_mn by auto
            finally show ?thesis .
          qed
          have "M $$ (i+1, j+1) = (make_first_column_positive ?S) $$ (i+1,j+1)"
            by (simp add: A'_def M_def True non_zero_positions_xs_m xs_empty)
          also have "... = (if ?S $$ (i+1,0) < 0 then - ?S $$ (i+1,j+1) else ?S $$ (i+1,j+1))" 
            unfolding make_first_column_positive.simps using S i1_mn j1n by auto
          also have "... = ?S $$ (i+1,j+1)" using Si10 by auto
          also have "... = A $$ (i+1,j+1)" using i1_m n0 i1_mn S jn1 by auto
          also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1 - m,j+1)"
            by (smt A_def A'' A i_ge_m append_rows_def carrier_matD i1_mn index_mat_four_block(1,3)
                index_one_mat(2) index_smult_mat(2) index_zero_mat(2) j1n less_imp_diff_less add_diff_cancel_right')
          finally show ?thesis .
        next
          case False         
          have Ai10: "A $$ (i+1,0) = 0"
          proof -
            have "A $$ (i+1,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1 - m,0)"
              by (smt A_def A'' A i_ge_m append_rows_def carrier_matD diff_add_inverse2 i1_mn 
                  index_mat_four_block less_imp_diff_less n0)
            also have "... = 0" using i_ge_m n0 i1_mn by auto
            finally show ?thesis .
          qed          
          have "M $$ (i+1, j+1) = (make_first_column_positive A) $$ (i+1,j+1)"
            by (simp add: A'_def M_def False True non_zero_positions_xs_m)
          also have "... = (if A $$ (i+1,0) < 0 then - A $$ (i+1,j+1) else A $$ (i+1,j+1))" 
            unfolding make_first_column_positive.simps using A i1_mn j1n by auto
          also have "... = A $$ (i+1,j+1)" using Ai10 by auto
          also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1 - m,j+1)"
            by (smt A_def A'' A i_ge_m append_rows_def carrier_matD i1_mn index_mat_four_block(1,3)
                index_one_mat(2) index_smult_mat(2) index_zero_mat(2) j1n less_imp_diff_less add_diff_cancel_right')
          finally show ?thesis .
        qed
        also have "... = D * (1\<^sub>m n) $$ ((i+1)-m, j+1)"
          by (rule index_smult_mat, insert i jn1 A'_DR False dr, auto)            
        also have "... = D *(1\<^sub>m (n - 1)) $$ (i-m,j)" using dc dr i j A'_DR i_ge_m
          by (smt Nat.add_diff_assoc2 carrier_matD(1) index_one_mat(1) jn1 less_diff_conv 
              linorder_not_less add_diff_cancel_right' add_diff_cancel_right' add_diff_cancel_left')
        also have "... = (D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i-m,j)"
          by (rule index_smult_mat[symmetric], insert i jn1 A'_DR False dr, auto)
        finally show ?thesis using 1 2 by auto
      next
        case False     
      have "?reduce_below $$ (i+1, j+1) = M $$ (i+1, j+1)"
      proof (unfold non_zero_positions_xs_m M_def,
          rule reduce_below_preserves_case_m[OF M' m0 _ M_M'D mk_A'_not0 m_le_n _ d_xs all_less_m _ _ _ D0])            
        show "j + 1 < n" using jn1 by auto
        show "i + 1 \<notin> set xs" using all_less_m i_ge_m non_zero_positions_xs_m by auto
        show "i + 1 \<noteq> 0" by auto
        show " i + 1 < m + n" using i_ge_m i dr A'_DR by auto
        show " i + 1 \<noteq> m" using i_ge_m by auto
      qed (insert False)
      also have "... = (?M' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n) $$ (i+1, j+1)" unfolding M_def using False M_M'D by argo
      also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ ((i+1)-m, j+1)"
      proof -
        have f1: "1 + j < n"
          by (metis Groups.add_ac(2) jn1 less_diff_conv)
        have f2: "\<forall>n. \<not> n + i < m"
          by (meson i_ge_m linorder_not_less nat_SN.compat not_add_less2)
        have "i < m + (n - 1)"
          by (metis (no_types) A'_DR carrier_matD(1) dr i)
        then have "1 + i < m + n"
          using f1 by linarith
        then show ?thesis
          using f2 f1 by (metis (no_types) Groups.add_ac(2) M' append_rows_def carrier_matD(1) 
              dim_col_mat(1) index_mat_four_block(1) index_one_mat(2) index_smult_mat(2) 
              index_zero_mat(2,3) mat_of_rows_def nat_arith.rule0)
      qed
      also have "... = D * (1\<^sub>m n) $$ ((i+1)-m, j+1)"
        by (rule index_smult_mat, insert i jn1 A'_DR False dr, auto)            
      also have "... = D *(1\<^sub>m (n - 1)) $$ (i-m,j)" using dc dr i j A'_DR i_ge_m
        by (smt Nat.add_diff_assoc2 carrier_matD(1) index_one_mat(1) jn1 less_diff_conv 
            linorder_not_less add_diff_cancel_right' add_diff_cancel_left')
      also have "... = (D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i-m,j)"
        by (rule index_smult_mat[symmetric], insert i jn1 A'_DR False dr, auto)
      finally have 3: "?reduce_below $$ (i+1,j+1) = (D \<cdot>\<^sub>m 1\<^sub>m (n - 1)) $$ (i-m,j)" .            
      show ?thesis using 1 2 3 by presburger
    qed              
  qed
qed
  let ?A'_DR_n = "mat_of_rows (n - 1) (map (Matrix.row A'_DR) [0..<n - 1])"
  have hyp: "\<exists>P. P\<in>carrier_mat (m + (n-1)) (m + (n-1)) \<and> invertible_mat P \<and> sub_PreHNF = P * A'_DR 
  \<and> echelon_form_JNF sub_PreHNF" 
  proof (cases "2 \<le> n - 1")
    case True
    show ?thesis
      by (unfold sub_PreHNF_def, rule "1.hyps"[OF _ _ _ non_zero_positions_def A'_def _ _ _ _ _])
         (insert A n D0 m_le_n True A'DR_A'DR_m_D A A'_split False, auto)
  next
    case False
    have "\<exists>P. P\<in>carrier_mat (m + (n-1)) (m + (n-1)) \<and> invertible_mat P \<and> sub_PreHNF = P * A'_DR"
      by (unfold sub_PreHNF_def, rule FindPreHNF_invertible_mat_mx2
          [OF A'DR_A'DR_m_D A'_DR_m _ _ D0 _])
          (insert False m_le_n n0 m0 "1"(4), auto)
    moreover have "echelon_form_JNF sub_PreHNF" unfolding sub_PreHNF_def 
      by (rule FindPreHNF_echelon_form_mx1[OF A'DR_A'DR_m_D A'_DR_m _ D0 _],
          insert False n0 m_le_n, auto) 
    ultimately show ?thesis by simp
  qed  
  from this obtain P where P: "P \<in> carrier_mat (m + (n - 1)) (m + (n - 1))"
    and inv_P: "invertible_mat P" and sub_PreHNF_P_A'_DR: "sub_PreHNF = P * A'_DR" by blast
  define P' where "P' = (four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (m+(n-1))) (0\<^sub>m (m+(n-1)) 1) P)"
  have P': "P' \<in> carrier_mat (m+n) (m+n)" 
  proof -
    have "P' \<in> carrier_mat (1 + (m+(n-1))) (1 + (m+(n-1))) "
      unfolding P'_def by (rule four_block_carrier_mat[OF _ P], simp) 
    thus ?thesis using n by auto
  qed
  have inv_P': "invertible_mat P'" 
    unfolding P'_def by (rule invertible_mat_four_block_mat_lower_right[OF P inv_P])
  have dr_A2: "dim_row A \<ge> 2" using A m0 n by auto
  have dc_A2: "dim_col A \<ge> 2" using n A by blast
  have *: "(dim_col A = 0) = False" using dc_A2 by auto
  have FindPreHNF_as_fbm: "FindPreHNF abs_flag D A = four_block_mat A'_UL A'_UR A'_DL sub_PreHNF" 
    unfolding FindPreHNF.simps[of abs_flag D A] using A'_split mn n A dr_A2 dc_A2 False
    unfolding Let_def sub_PreHNF_def M_def A'_def non_zero_positions_def *    
    by (smt (z3) linorder_not_less split_conv)
  also have "... = P' * (reduce_below 0 non_zero_positions D M)"
  proof -
    have "P' * (reduce_below 0 non_zero_positions D M) 
      = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (m + (n - 1))) (0\<^sub>m (m + (n - 1)) 1) P 
      * four_block_mat A'_UL A'_UR A'_DL A'_DR"
      unfolding P'_def fbm_R[unfolded M_def[symmetric], symmetric] ..
    also have "... = four_block_mat 
            ((1\<^sub>m 1) * A'_UL + (0\<^sub>m 1 (m + (n - 1)) * A'_DL)) 
            ((1\<^sub>m 1) * A'_UR + (0\<^sub>m 1 (m + (n - 1))) * A'_DR) 
            ((0\<^sub>m (m + (n - 1)) 1) * A'_UL + P * A'_DL) 
            ((0\<^sub>m (m + (n - 1)) 1) * A'_UR + P * A'_DR)" 
      by (rule mult_four_block_mat[OF _ _ _ P A'_UL A'_UR A'_DL A'_DR], auto)
    also have "... = four_block_mat A'_UL A'_UR (P * A'_DL) (P * A'_DR)"
      by (rule cong_four_block_mat, insert A'_UL A'_UR A'_DL A'_DR P, auto)
    also have "... = four_block_mat A'_UL A'_UR (0\<^sub>m (m + (n - 1)) 1) sub_PreHNF"
      unfolding A'_DL0 sub_PreHNF_P_A'_DR using P by simp
    also have "... = four_block_mat A'_UL A'_UR A'_DL sub_PreHNF"
      unfolding A'_DL0 by simp
    finally show ?thesis ..
  qed
  finally have Find_P'_reduceM: "FindPreHNF abs_flag D A =  P' * (reduce_below 0 non_zero_positions D M)" .
  have "\<exists>Q. invertible_mat Q \<and> Q \<in> carrier_mat (m + n) (m + n) 
    \<and> reduce_below 0 (xs @ [m]) D M = Q * M"
  proof (cases "xs = []")
    case True note xs_empty = True
    have rw: "reduce_below 0 (xs @ [m]) D M = reduce 0 m D M" using True by auto
    obtain p q u v d where pquvd: "(p, q, u, v, d) = euclid_ext2 (M $$ (0, 0)) (M $$ (m, 0))"
      by (simp add: euclid_ext2_def)
    have "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (m + n) (m + n) \<and> reduce 0 m D M = P * M"  
    proof (rule reduce_invertible_mat_case_m[OF _ _ m0 _ _ _ _ m_le_n n0 pquvd])
          show "M $$ (0, 0) \<noteq> 0" 
            using M_def mk_A'_not0 by blast
          define M' where  "M' = mat_of_rows n (map (Matrix.row M) [0..<m])"
          define M'' where "M'' = mat_of_rows n (map (Matrix.row M) [m..<m+n])"
          define A2 where "A2 = Matrix.mat (dim_row M) (dim_col M)
          (\<lambda>(i, k). if i = 0 then p * M $$ (0, k) + q * M $$ (m, k) 
                    else if i = m then u * M $$ (0, k) + v * M $$ (m, k)
                    else M $$ (i, k))"
          show M_M'_M'': "M = M' @\<^sub>r M''" unfolding M'_def M''_def            
            by (metis M append_rows_split carrier_matD le_add1)
          show M': "M' \<in> carrier_mat m n" unfolding M'_def by fastforce
          show M'': "M'' \<in> carrier_mat n n" unfolding M''_def by fastforce
          show "0 \<noteq> m" using m0 by simp
          show "A2 = Matrix.mat (dim_row M) (dim_col M)
          (\<lambda>(i, k). if i = 0 then p * M $$ (0, k) + q * M $$ (m, k) 
                    else if i = m then u * M $$ (0, k) + v * M $$ (m, k)
                    else M $$ (i, k))"
            (is "_ = ?rhs") using A A2_def by auto
          define xs' where "xs' = [1..<n]"
          define ys' where  "ys' = [1..<n]"
          show "xs' = [1..<n]" unfolding xs'_def by auto
          show "ys' = [1..<n]" unfolding ys'_def by auto
          have M''D: "(M'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. M'' $$ (j, j') = 0)"
            if jn: "j<n" and j0: "j>0" for j
          proof -
            have Ajm0: "A $$ (j+m,0) = 0"
            proof -
              have "A $$ (j+m,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j+m-m,0)"
                by (smt "1"(2) "1"(3) M M' M'' M_M'_M'' add.commute append_rows_def carrier_matD
                    diff_add_inverse2 index_mat_four_block index_one_mat(2) index_smult_mat(2)
                    le_add2 less_diff_conv2 n0 not_add_less2 that(1))
              also have "... = 0" using jn j0 by auto
              finally show ?thesis .
            qed
            have "M'' $$ (j, i) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)" if i_n: "i<n" for i
            proof (cases "A$$(0,0) = 0")
              case True 
              have "M'' $$ (j, i) = make_first_column_positive (swaprows 0 m A) $$ (j+m,i)"                
                by (smt A'_def Groups.add_ac(2) M' M'' M_M'_M'' M_def True append.simps(1) 
                    append_rows_nth3 diff_add_inverse2 jn le_add2 local.non_zero_positions_xs_m
                    nat_add_left_cancel_less nth_Cons_0 that xs_empty)
              also have "... = A $$ (j+m,i)" using A jn j0 i_n Ajm0 by auto
              also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)"
                by (smt A Groups.add_ac(2) add_mono_thms_linordered_field(1) append_rows_def A_def A'' i_n
                    carrier_matD index_mat_four_block(1,2) add_diff_cancel_right' not_add_less2 jn trans_less_add1)
              finally show ?thesis .            
            next
              case False
              have "A' = A" unfolding A'_def non_zero_positions_xs_m using False True by auto
              hence "M'' $$ (j, i) = make_first_column_positive A $$ (j+m,i)"                
                by (smt m_le_n M' M'' M_M'_M'' M_def append_rows_nth2 jn nat_SN.compat that)                
              also have "... = A $$ (j+m,i)" using A jn j0 i_n Ajm0 by auto
              also have "... = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (j,i)"
                by (smt A Groups.add_ac(2) add_mono_thms_linordered_field(1) append_rows_def A_def A'' i_n
                    carrier_matD index_mat_four_block(1,2) add_diff_cancel_right' not_add_less2 jn trans_less_add1)
              finally show ?thesis .
            qed                           
            thus ?thesis using jn j0 by auto
          qed
          have Am0D: "A$$(m,0) = D"
          proof -
            have "A$$(m,0) = (D \<cdot>\<^sub>m 1\<^sub>m n) $$ (m-m,0)"
              by (smt "1"(2) "1"(3) M M' M'' M_M'_M'' append_rows_def carrier_matD
                  diff_less_mono2 diff_self_eq_0 index_mat_four_block index_one_mat(2) 
                  index_smult_mat(2) less_add_same_cancel1 n0 semiring_norm(137))
            also have "... = D" using m0 n0 by auto
            finally show ?thesis .
          qed
          hence S00D: "(swaprows 0 m A) $$ (0,0) = D" using n0 m0 A by auto
          have Sm00: "(swaprows 0 m A) $$ (m,0) = A$$(0,0)" using n0 m0 A by auto
          have M00D: "M $$ (0, 0) = D" if A00: "A$$(0,0) = 0"
          proof -
            have "M $$ (0,0) = (make_first_column_positive (swaprows 0 m A)) $$ (0,0)"
              unfolding M_def A'_def using A00
              by (simp add: True non_zero_positions_xs_m)
            also have "... = (if (swaprows 0 m A) $$ (0,0) < 0 then - (swaprows 0 m A) $$(0,0)
                              else (swaprows 0 m A) $$(0,0))"
              unfolding make_first_column_positive.simps using m0 n0 A by auto
            also have "... = (swaprows 0 m A) $$(0,0)" using S00D D0 by auto
            also have "... = D" using S00D by auto
            finally show ?thesis .
          qed
          have Mm00: "M $$ (m, 0) = 0" if A00: "A$$(0,0) = 0"
          proof -
            have "M $$ (m,0) = (make_first_column_positive (swaprows 0 m A)) $$ (m,0)"
              unfolding M_def A'_def using A00
              by (simp add: True non_zero_positions_xs_m)
            also have "... = (if (swaprows 0 m A) $$ (m,0) < 0 then - (swaprows 0 m A) $$(m,0)
                              else (swaprows 0 m A) $$(m,0))"
              unfolding make_first_column_positive.simps using m0 n0 A by auto
            also have "... = (swaprows 0 m A) $$(m,0)" using Sm00 A00 D0 by auto
            also have "... = 0" using Sm00 A00 by auto
            finally show ?thesis .
          qed
          have M000: "M $$ (0, 0) = abs (A$$(0,0))" if A00: "A$$(0,0) \<noteq> 0"
          proof -
            have "M $$ (0,0) = (make_first_column_positive A) $$ (0,0)"
              unfolding M_def A'_def using A00
              by (simp add: True non_zero_positions_xs_m)
            also have "... = (if A $$ (0,0) < 0 then - A $$(0,0)
                              else A $$(0,0))"
              unfolding make_first_column_positive.simps using m0 n0 A by auto
            also have "... = abs (A$$(0,0))" using Sm00 A00 by auto
            finally show ?thesis .
          qed
          have Mm0D: "M $$ (m, 0) = D" if A00: "A $$ (0,0) \<noteq> 0"
          proof -
            have "M $$ (m,0) = (make_first_column_positive A) $$ (m,0)"
              unfolding M_def A'_def using A00
              by (simp add: True non_zero_positions_xs_m)
            also have "... = (if A $$ (m,0) < 0 then - A $$(m,0)
                              else A $$(m,0))"
              unfolding make_first_column_positive.simps using m0 n0 A by auto
            also have "... = A $$(m,0)" using S00D D0 Am0D by auto
            also have "... = D" using Am0D D0 by auto
            finally show ?thesis .
          qed
          have "0 \<notin> set xs'"
          proof -
            have "A2 $$ (0,0) = p * M $$ (0, 0) + q * M $$ (m, 0)" 
              using A A2_def n0 M by auto
            also have "... = gcd (M $$ (0, 0)) (M $$ (m, 0))"
              by (metis euclid_ext2_works(1,2) pquvd)
            also have "abs ... \<le> D" using M00D Mm00 M000 Mm0D using gcd_0_int D0 by fastforce
            finally have "abs (A2 $$ (0,0)) \<le> D" .
            thus ?thesis unfolding xs'_def using D0 by auto
          qed
          thus "\<forall>j\<in>set xs'. j<n \<and> (M'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. M'' $$ (j, j') = 0)"  
            using M''D xs'_def by auto
          have "0 \<notin> set ys'"
          proof -
            have "A2 $$ (m,0) = u * M $$ (0, 0) + v * M $$ (m, 0)"
              using A A2_def n0 m0 M by auto
            also have "... = - M $$ (m, 0) div gcd (M $$ (0, 0)) (M $$ (m, 0)) * M $$ (0, 0) 
                + M $$ (0, 0) div gcd (M $$ (0, 0)) (M $$ (m, 0)) * M $$ (m, 0) "
              by (simp add: euclid_ext2_works[OF pquvd[symmetric]])
            also have "... = 0" using M00D Mm00 M000 Mm0D
              by (smt dvd_div_mult_self euclid_ext2_works(3) euclid_ext2_works(5)
                  more_arith_simps(11) mult.commute mult_minus_left pquvd semiring_gcd_class.gcd_dvd1)
            finally have "A2 $$ (m,0) = 0" .
            thus ?thesis unfolding ys'_def using D0 by auto
          qed
          thus "\<forall>j\<in>set ys'. j<n \<and> (M'' $$ (j, j) = D) \<and> (\<forall>j'\<in>{0..<n}-{j}. M'' $$ (j, j') = 0)"
            using M''D ys'_def by auto   
          show "M $$ (m, 0) \<in> {0,D}" using Mm00 Mm0D by blast
          show " M $$ (m, 0) = 0 \<longrightarrow> M $$ (0, 0) = D"  using Mm00 Mm0D D_not0 M00D by blast          
        qed (insert D0)
        then show ?thesis using rw by auto
  next
    case False
    show ?thesis
      by (unfold M_def, rule reduce_below_invertible_mat_case_m[OF M' m0 n0 M_M'D[OF False] 
          mk_A'_not0 m_le_n d_xs all_less_m D0])
  qed
   
  from this obtain Q where inv_Q: "invertible_mat Q" and Q: "Q \<in> carrier_mat (m + n) (m + n)"
    and reduce_QM: "reduce_below 0 (xs @ [m]) D M = Q * M" by blast
  have "\<exists>R. invertible_mat R 
    \<and> R \<in> carrier_mat (dim_row A') (dim_row A') \<and> M = R * A'"
    by (unfold M_def, rule make_first_column_positive_invertible)
  from this obtain R where inv_R: "invertible_mat R"
    and R: "R \<in> carrier_mat (dim_row A') (dim_row A')" and M_RA': "M = R * A'" by blast
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> A' = P * A" 
    by (rule A'_swaprows_invertible_mat[OF A A'_def non_zero_positions_def],
        insert non_zero_positions_xs_m n m0, auto)
  from this obtain S where inv_S: "invertible_mat S"
   and S: "S \<in> carrier_mat (dim_row A) (dim_row A)" and A'_SA: "A' = S * A" 
    using A by auto
  have "(P'*Q*R*S) \<in> carrier_mat (m+n) (m+n)" using P' Q R S A' A by auto
  moreover have "FindPreHNF abs_flag D A = (P'*Q*R*S) * A" using Find_P'_reduceM reduce_QM 
    unfolding  M_RA' A'_SA M_def
    by (smt A' A'_SA P' Q R S assoc_mult_mat carrier_matD carrier_mat_triv index_mult_mat(2,3) 
        non_zero_positions_xs_m)
  moreover have "invertible_mat (P'*Q*R*S)" using inv_P' inv_Q inv_R inv_S using P' Q R S A' A 
    by (metis carrier_matD carrier_mat_triv index_mult_mat(2,3) invertible_mult_JNF)
  ultimately have exists_inv: "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P 
    \<and> FindPreHNF abs_flag D A = P * A" by blast
  moreover have "echelon_form_JNF (FindPreHNF abs_flag D A)" 
  proof (rule echelon_form_four_block_mat[OF A'_UL A'_UR sub_PreHNF'   ])
    show "FindPreHNF abs_flag D A = four_block_mat A'_UL A'_UR (0\<^sub>m (m + n - 1) 1) sub_PreHNF" 
      using A'_DL0 FindPreHNF_as_fbm sub_PreHNF sub_PreHNF' by auto
    have "A'_UL $$ (0, 0) = ?R $$ (0,0)"
      by (metis (mono_tags, lifting) A A'_DR A'_UL Find_P'_reduceM M_def 
          \<open>FindPreHNF abs_flag D A = P' * Q * R * S * A\<close> add_Suc_right add_sign_intros(2) carrier_matD fbm_R
          index_mat_four_block(1,3) index_mult_mat(3) m0 n0 plus_1_eq_Suc
          zero_less_one_class.zero_less_one)
    also have "... \<noteq> 0"
    proof (cases "xs=[]")
      case True
      have "?R $$ (0,0) = reduce 0 m D M $$ (0,0)"
        unfolding non_zero_positions_xs_m True M_def by simp
      also have "... \<noteq> 0"
        by (metis D_not0 M M_def add_pos_pos less_add_same_cancel1 m0 mk_A'_not0 n0 reduce_not0)
      finally show ?thesis .
    next
      case False
      show ?thesis
        by (unfold non_zero_positions_xs_m,
          rule reduce_below_not0_case_m[OF M' m0 n0 M_M'D[OF False] mk_A'_not0 m_le_n all_less_m D_not0])     
    qed       
    finally show "A'_UL $$ (0, 0) \<noteq> 0" .
  qed (insert mn n hyp, auto)
  ultimately show ?thesis by blast
qed
qed

lemma
  assumes A_def: "A = A'' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
  and A'': "A'' \<in> carrier_mat m n" and "n\<ge>2" and m_le_n: "m\<ge>n" and "D>0"
shows FindPreHNF_invertible_mat_n_ge2: "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> FindPreHNF abs_flag D A = P * A"
and FindPreHNF_echelon_form_n_ge2: "echelon_form_JNF (FindPreHNF abs_flag D A)"
  using FindPreHNF_works_n_ge2[OF assms] by blast+

lemma FindPreHNF_invertible_mat:
  assumes A_def: "A = A'' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
    and A'': "A'' \<in> carrier_mat m n" and n0: "0<n" and mn: "m\<ge>n" and D: "D>0"
  shows "\<exists>P. P \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat P \<and> FindPreHNF abs_flag D A = P * A"
proof -
  have A: "A \<in> carrier_mat (m+n) n" using A_def A'' by auto
  show ?thesis
  proof (cases "m+n<2")
    case True
    show ?thesis by (rule FindPreHNF_invertible_mat_2xn[OF A True])
  next
    case False note m_ge2 = False
    show ?thesis
    proof (cases "n<2")
      case True
      show ?thesis by (rule FindPreHNF_invertible_mat_mx2[OF A_def A'' True n0 D mn])
    next
      case False
      show ?thesis 
        by (rule FindPreHNF_invertible_mat_n_ge2[OF A_def A'' _ mn D], insert False, auto)
    qed  
  qed
qed


lemma FindPreHNF_echelon_form:
  assumes A_def: "A = A'' @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n"
    and A'': "A'' \<in> carrier_mat m n" and mn: "m\<ge>n" and D: "D>0"
  shows "echelon_form_JNF (FindPreHNF abs_flag D A)"
proof -
  have A: "A \<in> carrier_mat (m+n) n" using A_def A'' by auto
  have FindPreHNF: "(FindPreHNF abs_flag D A) \<in> carrier_mat (m+n) n" by (rule FindPreHNF[OF A])
  show ?thesis
  proof (cases "m+n<2")
    case True
    show ?thesis by (rule echelon_form_JNF_1xn[OF FindPreHNF True])
  next
    case False note m_ge2 = False
    show ?thesis
    proof (cases "n<2")
      case True
      show ?thesis by (rule FindPreHNF_echelon_form_mx1[OF A_def A'' True D mn])
    next
      case False
      show ?thesis 
        by (rule FindPreHNF_echelon_form_n_ge2[OF A_def A'' _ mn D], insert False, auto)
    qed  
  qed
qed
end

text \<open>We connect the algorithm developed in the Hermite AFP entry with ours. This would permit
to reuse many existing results and prove easily the soundness.\<close>

(*In HOL Analysis*)
thm Hermite.Hermite_reduce_above.simps
thm Hermite.Hermite_of_row_i_def
thm Hermite.Hermite_of_upt_row_i_def
thm Hermite.Hermite_of_def

(*In JNF*)
thm Hermite_reduce_above.simps
thm Hermite_of_row_i_def
thm Hermite_of_list_of_rows.simps
thm mod_operation.Hermite_mod_det_def

(*Connecting Hermite.Hermite_reduce_above and Hermite_reduce_above*)
thm Hermite.Hermite_reduce_above.simps Hermite_reduce_above.simps

context includes lifting_syntax
begin

definition "res_int = (\<lambda>b n::int. n mod b)"

lemma res_function_res_int: 
  "res_function res_int"
  using res_function_euclidean2 unfolding res_int_def by auto

lemma HMA_Hermite_reduce_above[transfer_rule]: 
  assumes "n<CARD('m)"
  shows "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> int ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) 
    ===> (Mod_Type_Connect.HMA_I) ===> (Mod_Type_Connect.HMA_I) ===> (Mod_Type_Connect.HMA_M)) 
  (\<lambda>A i j. Hermite_reduce_above A n i j)
  (\<lambda>A i j. Hermite.Hermite_reduce_above A n i j res_int)"
proof (intro rel_funI, goal_cases)
  case (1 A A' i i' j j')
  then show ?case using assms
  proof (induct n arbitrary: A A')
    case 0
    then show ?case by auto
  next
    case (Suc n)
    note AA'[transfer_rule] = "Suc.prems"(1)
    note ii'[transfer_rule] = "Suc.prems"(2)
    note jj'[transfer_rule] = "Suc.prems"(3)
    note Suc_n_less_m = "Suc.prems"(4)

    let ?H_JNF = "HNF_Mod_Det_Algorithm.Hermite_reduce_above"
    let ?H_HMA = "Hermite.Hermite_reduce_above"
    let ?from_nat_rows = "mod_type_class.from_nat :: _ \<Rightarrow> 'm"
    have nn[transfer_rule]: "Mod_Type_Connect.HMA_I n (?from_nat_rows n)" 
      unfolding Mod_Type_Connect.HMA_I_def
      by (simp add: Suc_lessD Suc_n_less_m mod_type_class.from_nat_to_nat)

    have Anj: "A' $h (?from_nat_rows n) $h j' = A $$ (n,j)" 
      by (unfold index_hma_def[symmetric], transfer, simp)
    have Aij: "A' $h i' $h j' = A $$ (i,j)" by (unfold index_hma_def[symmetric], transfer, simp)
    let ?s = "(- (A $$ (n, j) div A $$ (i, j)))"
    let ?s' = "((res_int (A' $h i' $h j') (A' $h ?from_nat_rows n $h j') 
      - A' $h ?from_nat_rows n $h j') div A' $h i' $h j')"
    have ss'[transfer_rule]: "?s = ?s'" unfolding res_int_def Anj Aij
      by (metis (no_types, hide_lams) Groups.add_ac(2) add_diff_cancel_left' div_by_0 
          minus_div_mult_eq_mod more_arith_simps(7) nat_arith.rule0 nonzero_mult_div_cancel_right
          uminus_add_conv_diff)
    have H_JNF_eq: "?H_JNF A (Suc n) i j = ?H_JNF (addrow (- (A $$ (n, j) div A $$ (i, j))) n i A) n i j"
      by auto
    have H_HMA_eq: "?H_HMA A' (Suc n) i' j' res_int = ?H_HMA (row_add A' (?from_nat_rows n) i' ?s') n i' j' res_int"
      by (auto simp add: Let_def)
    have "Mod_Type_Connect.HMA_M (?H_JNF (addrow ?s n i A) n i j) 
      (?H_HMA (row_add A' (?from_nat_rows n) i' ?s') n i' j' res_int)" 
      by (rule "Suc.hyps"[OF _ ii' jj'], transfer_prover, insert Suc_n_less_m, simp)
    thus ?case using H_JNF_eq H_HMA_eq by auto
  qed
qed


corollary HMA_Hermite_reduce_above': 
  assumes "n<CARD('m)"
  and "Mod_Type_Connect.HMA_M A (A':: int ^ 'n :: mod_type ^ 'm :: mod_type)"
  and "Mod_Type_Connect.HMA_I i i'" and "Mod_Type_Connect.HMA_I j j'"
  shows"Mod_Type_Connect.HMA_M (Hermite_reduce_above A n i j) (Hermite.Hermite_reduce_above A' n i' j' res_int)"
  using HMA_Hermite_reduce_above assms unfolding rel_fun_def by metis


lemma HMA_Hermite_of_row_i[transfer_rule]: 
  assumes upt_A: "upper_triangular' A"
  and AA': "Mod_Type_Connect.HMA_M A (A':: int ^ 'n :: mod_type ^ 'm :: mod_type)"
  and ii': "Mod_Type_Connect.HMA_I i i'"
  shows "Mod_Type_Connect.HMA_M (Hermite_of_row_i A i)
  (Hermite.Hermite_of_row_i ass_function_euclidean res_int A' i')"
proof -
  note AA'[transfer_rule]
  note ii'[transfer_rule]
  have i: "i<dim_row A"
    by (metis (full_types) AA' ii' Mod_Type_Connect.HMA_I_def 
        Mod_Type_Connect.dim_row_transfer_rule mod_type_class.to_nat_less_card)  
  show ?thesis
  proof (cases "is_zero_row i' A'")
    case True
    hence "is_zero_row_JNF i A" by (transfer, simp)
    hence "find_fst_non0_in_row i A = None" using find_fst_non0_in_row_None[OF _ upt_A i] by auto
    thus ?thesis using True AA' unfolding Hermite.Hermite_of_row_i_def Hermite_of_row_i_def by auto
  next
    case False
    have nz_iA: "\<not> is_zero_row_JNF i A" using False by transfer
    hence "find_fst_non0_in_row i A \<noteq> None" using find_fst_non0_in_row_None[OF _ upt_A i] by auto
    from this obtain j where j: "find_fst_non0_in_row i A = Some j" by blast
    have j_eq: "j = (LEAST n. A $$ (i,n) \<noteq> 0)"
      by (rule find_fst_non0_in_row_LEAST[OF _ upt_A j i], auto)
    have H_JNF_rw: "(Hermite_of_row_i A i) = 
    (if A $$ (i, j) < 0 then Hermite_reduce_above (multrow i (- 1) A) i i j
     else Hermite_reduce_above A i i j)" unfolding Hermite_of_row_i_def using j by auto
    let ?H_HMA = "Hermite.Hermite_of_row_i"
    let ?j' = "(LEAST n. A' $h i' $h n \<noteq> 0)"
    have ii'2: "(mod_type_class.to_nat i') = i" using ii'
      by (simp add: Mod_Type_Connect.HMA_I_def)                                            
    have jj'[transfer_rule]: "Mod_Type_Connect.HMA_I j ?j'"
      unfolding j_eq index_hma_def[symmetric] by (rule HMA_LEAST[OF AA' ii' nz_iA])
    have Aij: "A $$ (i, j) = A' $h i' $h (LEAST n. A' $h i' $h n \<noteq> 0)"
      by (subst index_hma_def[symmetric], transfer', simp)
    have H_HMA_rw: "?H_HMA ass_function_euclidean res_int A' i' = 
    Hermite.Hermite_reduce_above (mult_row A' i' (\<bar>A' $h i' $h ?j'\<bar> 
      div A' $h i' $h ?j'))
     (mod_type_class.to_nat i') i' ?j' res_int" 
      unfolding Hermite.Hermite_of_row_i_def Let_def ass_function_euclidean_def
      by (auto simp add: False)
    have im: "i < CARD('m)" using ii' unfolding Mod_Type_Connect.HMA_I_def
      using mod_type_class.to_nat_less_card by blast
    show ?thesis
    proof (cases "A $$ (i, j) < 0")
      case True
      have A'i'j'_le_0: "A' $h i' $h ?j' < 0" using Aij True by auto
      hence 1: "(\<bar>A' $h i' $h ?j'\<bar> div A' $h i' $h ?j') 
          = -1" using div_pos_neg_trivial by auto
      have [transfer_rule]: "Mod_Type_Connect.HMA_M (multrow i (- 1) A) 
      (mult_row A' i' (\<bar>A' $h i' $h ?j'\<bar> 
      div A' $h i' $h ?j'))" unfolding 1 by transfer_prover      
      have H_HMA_rw2: "Hermite_of_row_i A i = Hermite_reduce_above (multrow i (- 1) A) i i j"
        using True H_JNF_rw by auto
      have *: "Mod_Type_Connect.HMA_M (Hermite_reduce_above (multrow i (- 1) A) i i j) 
        (Hermite.Hermite_reduce_above (mult_row A' i' (\<bar>A' $h i' $h ?j'\<bar> 
        div A' $h i' $h ?j'))
        (mod_type_class.to_nat i') i' ?j' res_int) "
        unfolding 1 ii'2
        by (rule HMA_Hermite_reduce_above'[OF im _ ii' jj'], transfer_prover)
       show ?thesis unfolding H_JNF_rw H_HMA_rw unfolding H_HMA_rw2 using True * by auto
    next
      case False
      have Aij_not0: "A $$ (i, j) \<noteq> 0" using j_eq nz_iA
        by (metis (mono_tags) LeastI is_zero_row_JNF_def)
      have A'i'j'_le_0: "A' $h i' $h ?j' > 0" using False Aij_not0 Aij by auto
      hence 1: "(\<bar>A' $h i' $h ?j'\<bar> div A' $h i' $h ?j') = 1" by auto
      have H_HMA_rw2: "Hermite_of_row_i A i = Hermite_reduce_above A i i j"
        using False H_JNF_rw by auto
      have *: "?H_HMA ass_function_euclidean res_int A' i' = 
      (Hermite.Hermite_reduce_above A' (mod_type_class.to_nat i') i' ?j' res_int)"
        using H_HMA_rw unfolding 1 unfolding mult_row_1_id by simp
      have "Mod_Type_Connect.HMA_M (Hermite_reduce_above A i i j) 
        (Hermite.Hermite_reduce_above A' (mod_type_class.to_nat i') i' ?j' res_int)"
        unfolding 1 ii'2
        by (rule HMA_Hermite_reduce_above'[OF im AA' ii' jj'])
      then show ?thesis using H_HMA_rw * H_HMA_rw2 by presburger
    qed        
  qed
qed


lemma Hermite_of_list_of_rows_append:
"Hermite_of_list_of_rows A (xs @ [x]) = Hermite_of_row_i (Hermite_of_list_of_rows A xs) x"
  by (induct xs arbitrary: A, auto)


lemma Hermite_reduce_above[simp]: "Hermite_reduce_above A n i j \<in> carrier_mat (dim_row A) (dim_col A)"  
proof (induct n arbitrary: A)
  case 0
  then show ?case by auto
next
  case (Suc n)    
  let ?A = "(addrow (- (A $$ (n, j) div A $$ (i, j))) n i A)"  
  have "Hermite_reduce_above A (Suc n) i j = Hermite_reduce_above ?A n i j"
    by (auto simp add: Let_def)
  also have "... \<in> carrier_mat (dim_row ?A) (dim_col ?A)" by(rule Suc.hyps)
  finally show ?case by auto  
qed                           


lemma Hermite_of_row_i: "Hermite_of_row_i A i \<in> carrier_mat (dim_row A) (dim_col A)" 
proof -
  have "Hermite_reduce_above (multrow i (- 1) A) i i a 
    \<in> carrier_mat (dim_row (multrow i (- 1) A)) (dim_col (multrow i (- 1) A))" 
    for a by (rule Hermite_reduce_above)
  thus ?thesis
    unfolding Hermite_of_row_i_def using Hermite_reduce_above 
    by (cases "find_fst_non0_in_row i A", auto)
qed

end


text \<open>We now move more lemmas from HOL Analysis (with mod-type restrictions) to the JNF matrix
representation.\<close>

(*thm echelon_form_Hermite_of_row will be transferred from HOL Analysis to JNF*)

context
begin

private lemma echelon_form_Hermite_of_row_mod_type:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('m::mod_type) CARD('n::mod_type)"
  assumes eA: "echelon_form_JNF A"
  and i: "i<CARD('m)"
  shows "echelon_form_JNF (Hermite_of_row_i A i)"
proof -
  have uA: "upper_triangular' A" by (rule echelon_form_JNF_imp_upper_triangular[OF eA])
  define A' where "A' = (Mod_Type_Connect.to_hma\<^sub>m A :: int ^'n :: mod_type ^'m :: mod_type)"
  define i' where "i' = (Mod_Type.from_nat i :: 'm)"
  have AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'"
    unfolding Mod_Type_Connect.HMA_M_def using assms A'_def by auto
  have ii'[transfer_rule]: "Mod_Type_Connect.HMA_I i i'"
    unfolding Mod_Type_Connect.HMA_I_def i'_def using assms
    using from_nat_not_eq order.strict_trans by blast 
  have eA'[transfer_rule]: "echelon_form A'" using eA by transfer
  have [transfer_rule]: "Mod_Type_Connect.HMA_M 
    (HNF_Mod_Det_Algorithm.Hermite_of_row_i A i) 
    (Hermite.Hermite_of_row_i ass_function_euclidean res_int A' i')"
    by (rule HMA_Hermite_of_row_i[OF uA AA' ii'])
  have "echelon_form (Hermite.Hermite_of_row_i ass_function_euclidean res_int A' i')"
    by (rule echelon_form_Hermite_of_row[OF ass_function_euclidean res_function_res_int eA'])    
  thus ?thesis by (transfer, simp)
qed 


private lemma echelon_form_Hermite_of_row_nontriv_mod_ring:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('m::nontriv mod_ring) CARD('n::nontriv mod_ring)"
  assumes eA: "echelon_form_JNF A"
  and "i<CARD('m)"
  shows "echelon_form_JNF (Hermite_of_row_i A i)"
using assms echelon_form_Hermite_of_row_mod_type by (smt CARD_mod_ring) 

(*We internalize both sort constraints in one step*)
lemmas echelon_form_Hermite_of_row_nontriv_mod_ring_internalized = 
  echelon_form_Hermite_of_row_nontriv_mod_ring[unfolded CARD_mod_ring, 
      internalize_sort "'m::nontriv", internalize_sort "'b::nontriv"]

context
  fixes m::nat and n::nat
  assumes local_typedef1: "\<exists>(Rep :: ('b \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<m :: int}"
  assumes local_typedef2: "\<exists>(Rep :: ('c \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<n :: int}"
  and m: "m>1"
  and n: "n>1"
begin

lemma echelon_form_Hermite_of_row_nontriv_mod_ring_aux:
 fixes A::"int mat"
  assumes "A \<in> carrier_mat m n"
  assumes eA: "echelon_form_JNF A"
  and "i<m"
shows "echelon_form_JNF (Hermite_of_row_i A i)"  
  using echelon_form_Hermite_of_row_nontriv_mod_ring_internalized
    [OF type_to_set2(1)[OF local_typedef1 local_typedef2] 
        type_to_set1(1)[OF local_typedef1 local_typedef2]]
  using assms 
  using type_to_set1(2) local_typedef1 local_typedef2 n m by metis 

end

(*Canceling the first local type definitions*)
context
begin

(*Canceling the first*)

private lemma echelon_form_Hermite_of_row_i_cancelled_first:
"\<exists>Rep Abs. type_definition Rep Abs {0..<int n} \<Longrightarrow> 1 < m \<Longrightarrow> 1 < n 
  \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> echelon_form_JNF A \<Longrightarrow> i < m 
  \<Longrightarrow> echelon_form_JNF (HNF_Mod_Det_Algorithm.Hermite_of_row_i A i)"
  using echelon_form_Hermite_of_row_nontriv_mod_ring_aux[cancel_type_definition, of m n A i]
  by auto  

(*Canceling the second*)
private lemma echelon_form_Hermite_of_row_i_cancelled_both:
"1 < m \<Longrightarrow> 1 < n \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> echelon_form_JNF A \<Longrightarrow> i < m 
  \<Longrightarrow> echelon_form_JNF (HNF_Mod_Det_Algorithm.Hermite_of_row_i A i)"
  using echelon_form_Hermite_of_row_i_cancelled_first[cancel_type_definition, of n m A i] by simp

(*The final results in JNF*)

lemma echelon_form_JNF_Hermite_of_row_i':
 fixes A::"int mat"
  assumes "A \<in> carrier_mat m n"
  assumes eA: "echelon_form_JNF A"
  and "i<m"
  and "1 < m" and "1 < n" (*Required from the mod_type restrictions*)
shows "echelon_form_JNF (Hermite_of_row_i A i)"  
  using echelon_form_Hermite_of_row_i_cancelled_both assms by auto


corollary echelon_form_JNF_Hermite_of_row_i:
  fixes A::"int mat"
  assumes eA: "echelon_form_JNF A"
    and i: "i<dim_row A"
  shows "echelon_form_JNF (Hermite_of_row_i A i)"  
proof (cases "dim_row A < 2")
  case True
  show ?thesis 
    by (rule echelon_form_JNF_1xn[OF Hermite_of_row_i True])
next
  case False note m_ge2 = False
  show ?thesis
  proof (cases "1<dim_col A")
    case True
    show ?thesis by (rule echelon_form_JNF_Hermite_of_row_i'[OF _ eA i _ True], insert m_ge2, auto)
  next
    case False
    hence dc_01: "dim_col A \<in> {0,1}" by auto
    show ?thesis
    proof (cases "dim_col A = 0")
      case True
      have H: "Hermite_of_row_i A i \<in> carrier_mat (dim_row A) (dim_col A)"
        using Hermite_of_row_i by blast
      show ?thesis by (rule echelon_form_mx0, insert True H, auto)
    next
      case False
      hence dc_1: "dim_col A = 1" using dc_01 by simp
      then show ?thesis     
      proof (cases "i=0")
        case True      
        have eA': "echelon_form_JNF (multrow 0 (- 1) A)"
          by (rule echelon_form_JNF_multrow[OF _ _ eA], insert m_ge2, auto)
        show ?thesis using True unfolding Hermite_of_row_i_def
          by (cases "find_fst_non0_in_row 0 A", insert eA eA', auto)
      next
        case False  
        have all_zero: "(\<forall>j\<in>{i..<dim_col A}. A $$ (i, j) = 0)" unfolding dc_1 using False by auto
        hence "find_fst_non0_in_row i A = None" using find_fst_non0_in_row_None'[OF _ i] by blast
        hence "Hermite_of_row_i A i = A" unfolding Hermite_of_row_i_def by auto
        then show ?thesis using eA by auto
      qed  
    qed  
  qed
qed



lemma Hermite_of_list_of_rows:
 "(Hermite_of_list_of_rows A xs) \<in> carrier_mat (dim_row A) (dim_col A)"
proof (induct xs arbitrary: A rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  let ?A = "(Hermite_of_list_of_rows A xs)"
  have hyp: "(Hermite_of_list_of_rows A xs) \<in> carrier_mat (dim_row A) (dim_col A)" by (rule snoc.hyps)
  have "Hermite_of_list_of_rows A (xs @ [x]) = Hermite_of_row_i ?A x"
    using Hermite_of_list_of_rows_append by auto
  also have "... \<in> carrier_mat (dim_row ?A) (dim_col ?A)" using Hermite_of_row_i by auto
  finally show ?case using hyp by auto  
qed

lemma echelon_form_JNF_Hermite_of_list_of_rows:
  assumes "A\<in>carrier_mat m n"
 and "\<forall>x\<in>set xs. x < m"
  and "echelon_form_JNF A"
shows "echelon_form_JNF (Hermite_of_list_of_rows A xs)"
  using assms
proof (induct xs arbitrary: A rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  have hyp: "echelon_form_JNF (Hermite_of_list_of_rows A xs)"
    by (rule snoc.hyps, insert snoc.prems, auto)
  have H_Axs: "(Hermite_of_list_of_rows A xs) \<in> carrier_mat (dim_row A) (dim_col A)" 
    by (rule Hermite_of_list_of_rows)
  have "(Hermite_of_list_of_rows A (xs @ [x])) = Hermite_of_row_i (Hermite_of_list_of_rows A xs) x"
    using Hermite_of_list_of_rows_append by simp
  also have "echelon_form_JNF ..."
  proof (rule echelon_form_JNF_Hermite_of_row_i[OF hyp])
    show "x < dim_row (Hermite_of_list_of_rows A xs)" using snoc.prems H_Axs by auto
  qed
  finally show ?case .
qed




lemma HMA_Hermite_of_upt_row_i[transfer_rule]: 
  assumes "xs = [0..<i]"
    and "\<forall>x\<in>set xs. x < CARD('m)"
  assumes "Mod_Type_Connect.HMA_M A (A':: int ^ 'n :: mod_type ^ 'm :: mod_type)" 
    and "echelon_form_JNF A"
  shows "Mod_Type_Connect.HMA_M (Hermite_of_list_of_rows A xs)
  (Hermite.Hermite_of_upt_row_i A' i ass_function_euclidean res_int)"
  using assms
proof (induct xs arbitrary: A A' i rule: rev_induct)
  case Nil
  have "i=0" using Nil by (metis le_0_eq upt_eq_Nil_conv)
  then show ?case using Nil unfolding Hermite_of_upt_row_i_def by auto
next
  case (snoc x xs)
  note xs_x_eq = snoc.prems(1)
  note all_xm = snoc.prems(2)
  note AA' = snoc.prems(3)
  note upt_A = snoc.prems(4)
  let ?x' = "(mod_type_class.from_nat x::'m)"
  have xm: "x < CARD('m)" using all_xm by auto
  have xx'[transfer_rule]: "Mod_Type_Connect.HMA_I x ?x'"
    unfolding Mod_Type_Connect.HMA_I_def using from_nat_not_eq xm by blast
  have last_i1: "last [0..<i] = i-1"
    by (metis append_is_Nil_conv last_upt list.simps(3) neq0_conv xs_x_eq upt.simps(1))
  have "last (xs @ [x]) = i-1" using xs_x_eq last_i1 by auto
  hence x_i1: "x = i-1" by auto
  have xs_eq: "xs = [0..<x]" using xs_x_eq x_i1
    by (metis add_diff_inverse_nat append_is_Nil_conv append_same_eq less_one list.simps(3)
        plus_1_eq_Suc upt_Suc upt_eq_Nil_conv)
  have list_rw: "[0..<i] = 0 #[1..<i]" 
    by (auto, metis append_is_Nil_conv list.distinct(2) upt_rec xs_x_eq)
  have 1: "Hermite_of_list_of_rows A (xs @ [x]) = Hermite_of_row_i (Hermite_of_list_of_rows A xs) x"
    unfolding Hermite_of_list_of_rows_append by auto
  let ?H_upt_HA = "Hermite.Hermite_of_upt_row_i"
  let ?H_HA = "Hermite.Hermite_of_row_i ass_function_euclidean res_int"
  have "(Hermite_of_upt_row_i A' i ass_function_euclidean res_int) = 
    foldl ?H_HA A' (map mod_type_class.from_nat [0..<i])"
    unfolding Hermite_of_upt_row_i_def by auto
  also have "... = foldl ?H_HA A' ((map mod_type_class.from_nat [0..<i-1])@[?x'])"
    by (metis list.simps(8) list.simps(9) map_append x_i1 xs_eq xs_x_eq)
  also have "... = foldl ?H_HA (?H_upt_HA A' (i - 1) ass_function_euclidean res_int) [?x']"
    unfolding foldl_append unfolding Hermite_of_upt_row_i_def[symmetric] by auto
  also have "... = ?H_HA (Hermite_of_upt_row_i A' (i - 1) ass_function_euclidean res_int) ?x'" by auto
  finally have 2: "?H_upt_HA A' i ass_function_euclidean res_int =
    ?H_HA (Hermite_of_upt_row_i A' (i - 1) ass_function_euclidean res_int) ?x'" .

  have hyp[transfer_rule]: "Mod_Type_Connect.HMA_M (Hermite_of_list_of_rows A xs)
              (Hermite_of_upt_row_i A' (i - 1) ass_function_euclidean res_int)"
    by (rule snoc.hyps[OF _ _ AA' upt_A], insert xs_eq x_i1 xm, auto)

  have upt_H_Axs:"upper_triangular' (Hermite_of_list_of_rows A xs)"
  proof (rule echelon_form_JNF_imp_upper_triangular, 
      rule echelon_form_JNF_Hermite_of_list_of_rows[OF _ _ upt_A])
    show "A\<in>carrier_mat (CARD('m)) (CARD('n))"
      using Mod_Type_Connect.dim_col_transfer_rule
        Mod_Type_Connect.dim_row_transfer_rule snoc(4) by blast
    show "\<forall>x\<in>set xs. x < CARD('m)" using all_xm by auto
  qed
  show ?case unfolding 1 2 
  by (rule HMA_Hermite_of_row_i[OF upt_H_Axs hyp xx'])
qed

(*This is the lemma that I will transfer to JNF to get the soundness*)
lemma Hermite_Hermite_of_upt_row_i:
  assumes a: "ass_function ass"
    and r: "res_function res"
    and eA: "echelon_form A"
  shows "Hermite (range ass) (\<lambda>c. range (res c)) (Hermite_of_upt_row_i A (nrows A) ass res)" 
proof -
  let ?H = "(Hermite_of_upt_row_i A (nrows A) ass res)"  
  show ?thesis
  proof (rule Hermite_intro, auto)
    show "Complete_set_non_associates (range ass)"
      by (simp add: ass_function_Complete_set_non_associates a)
    show "Complete_set_residues (\<lambda>c. range (res c))"
      by (simp add: r res_function_Complete_set_residues)
    show "echelon_form ?H"
      by (rule echelon_form_Hermite_of_upt_row_i[OF eA a r])  
    fix i
    assume i: "\<not> is_zero_row i ?H" 
    show "?H $ i $ (LEAST n. ?H $ i $ n \<noteq> 0) \<in> range ass"
    proof -
      have non_zero_i_eA: "\<not> is_zero_row i A"
        using Hermite_of_upt_row_preserves_zero_rows[OF _ _ a r] i eA by blast   
      have least: "(LEAST n. ?H $h i $h n \<noteq> 0) = (LEAST n. A $h i $h n \<noteq> 0)"
        by (rule Hermite_of_upt_row_i_Least[OF non_zero_i_eA eA a r], simp)
      have "?H $ i $ (LEAST n. A $ i $ n \<noteq> 0) \<in> range ass"
        by (rule Hermite_of_upt_row_i_in_range[OF non_zero_i_eA eA a r], auto)
      thus ?thesis unfolding least by auto
    qed
  next
    fix i j assume i: "\<not> is_zero_row i ?H" and j: "j < i"
    show "?H $ j $ (LEAST n. ?H $ i $ n \<noteq> 0)
    \<in> range (res (?H $ i $ (LEAST n. ?H $ i $ n \<noteq> 0)))"
    proof -
      have non_zero_i_eA: "\<not> is_zero_row i A"
        using Hermite_of_upt_row_preserves_zero_rows[OF _ _ a r] i eA by blast   
      have least: "(LEAST n. ?H $h i $h n \<noteq> 0) = (LEAST n. A $h i $h n \<noteq> 0)"
        by (rule Hermite_of_upt_row_i_Least[OF non_zero_i_eA eA a r], simp)
      have "?H $ j $ (LEAST n. A $ i $ n \<noteq> 0) \<in> range (res (?H $ i $ (LEAST n. A $ i $ n \<noteq> 0)))"
        by (rule Hermite_of_upt_row_i_in_range_res[OF non_zero_i_eA eA a r _ _ j], auto)
      thus ?thesis unfolding least by auto
    qed
  qed
qed


lemma Hermite_of_row_i_0:
  "Hermite_of_row_i A 0 = A \<or> Hermite_of_row_i A 0 = multrow 0 (- 1) A"
    by (cases "find_fst_non0_in_row 0 A", unfold Hermite_of_row_i_def, auto)

lemma Hermite_JNF_intro:
assumes 
"Complete_set_non_associates associates" "(Complete_set_residues res)" "echelon_form_JNF A"
 "(\<forall>i<dim_row A. \<not> is_zero_row_JNF i A \<longrightarrow> A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0) \<in> associates)"
 "(\<forall>i<dim_row A. \<not> is_zero_row_JNF i A \<longrightarrow> (\<forall>j. j<i \<longrightarrow> A $$ (j, (LEAST n. A $$ (i, n) \<noteq> 0)) 
     \<in> res (A $$ (i,(LEAST n. A $$ (i,n) \<noteq> 0)))))"
shows "Hermite_JNF associates res A"
  using assms unfolding Hermite_JNF_def by auto

lemma least_multrow:
  assumes "A \<in> carrier_mat m n" and "i<m" and eA: "echelon_form_JNF A"
  assumes ia: "ia < dim_row A" and nz_ia_mrA: "\<not> is_zero_row_JNF ia (multrow i (- 1) A)"
  shows "(LEAST n. multrow i (- 1) A $$ (ia, n) \<noteq> 0) = (LEAST n. A $$ (ia, n) \<noteq> 0)"
proof (rule Least_equality)
  have nz_ia_A: "\<not> is_zero_row_JNF ia A" using nz_ia_mrA ia by auto
  have Least_Aian_n: "(LEAST n. A $$ (ia, n) \<noteq> 0) < dim_col A"
    by (smt dual_order.strict_trans is_zero_row_JNF_def not_less_Least not_less_iff_gr_or_eq nz_ia_A)
  show "multrow i (- 1) A $$ (ia, LEAST n. A $$ (ia, n) \<noteq> 0) \<noteq> 0"
    by (smt LeastI Least_Aian_n class_cring.cring_simprules(22) equation_minus_iff ia
        index_mat_multrow(1) is_zero_row_JNF_def mult_minus1 nz_ia_A)
  show " \<And>y. multrow i (- 1) A $$ (ia, y) \<noteq> 0 \<Longrightarrow> (LEAST n. A $$ (ia, n) \<noteq> 0) \<le> y"
    by (metis (mono_tags, lifting) Least_Aian_n class_cring.cring_simprules(22) ia 
        index_mat_multrow(1) leI mult_minus1 order.strict_trans wellorder_Least_lemma(2))
qed


lemma Hermite_Hermite_of_row_i:
  assumes A: "A \<in> carrier_mat 1 n"
  shows "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (Hermite_of_row_i A 0)"
proof (rule Hermite_JNF_intro)
  show "Complete_set_non_associates (range ass_function_euclidean)"   
    using ass_function_Complete_set_non_associates ass_function_euclidean by blast
  show "Complete_set_residues (\<lambda>c. range (res_int c))"
    using res_function_Complete_set_residues res_function_res_int by blast
  show "echelon_form_JNF (HNF_Mod_Det_Algorithm.Hermite_of_row_i A 0)"
    by (metis (full_types) assms carrier_matD(1) echelon_form_JNF_Hermite_of_row_i
        echelon_form_JNF_def less_one not_less_zero)
  let ?H = "Hermite_of_row_i A 0"
  show "\<forall>i<dim_row ?H. \<not> is_zero_row_JNF i ?H 
      \<longrightarrow> ?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0) \<in> range ass_function_euclidean"
  proof (auto)
    fix i assume i: "i<dim_row ?H" and nz_iH: "\<not> is_zero_row_JNF i ?H"
    have nz_iA: "\<not> is_zero_row_JNF i A"
      by (metis (full_types) Hermite_of_row_i Hermite_of_row_i_0 carrier_matD(1)
          i is_zero_row_JNF_multrow nz_iH)
    have "?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0) \<ge> 0"
    proof (cases "find_fst_non0_in_row 0 A")
      case None
       then show ?thesis using nz_iH unfolding Hermite_of_row_i_def
         by (smt HNF_Mod_Det_Algorithm.Hermite_of_row_i_def upper_triangular'_def assms 
             carrier_matD(1) find_fst_non0_in_row_None i less_one not_less_zero option.simps(4))
    next
      case (Some a)
      have upA: "upper_triangular' A" using A unfolding upper_triangular'_def by auto
      have eA: "echelon_form_JNF A" by (metis A Suc_1 echelon_form_JNF_1xn lessI)
      have i0: "i=0" using Hermite_of_row_i[of A 0] A i by auto        
      have Aia: "A $$ (i,a) \<noteq> 0" and a0: "0 \<le> a" and an: "a<n"
        using i0 Some assms find_fst_non0_in_row by auto+
      have l: "(LEAST n. A $$ (i, n) \<noteq> 0) = (LEAST n.  multrow 0 (- 1) A $$ (i, n) \<noteq> 0)"
        by (rule least_multrow[symmetric, OF A _ eA _], insert nz_iA i A i0, auto)
      have a1: "a = (LEAST n. A $$ (i, n) \<noteq> 0)"
        by (rule find_fst_non0_in_row_LEAST[OF A upA], insert Some i0, auto)
      hence a2: "a = (LEAST n.  multrow 0 (- 1) A $$ (i, n) \<noteq> 0)" unfolding l by simp
      have m1: "multrow 0 (- 1) A $$ (i, LEAST n. multrow 0 (- 1) A $$ (i, n) \<noteq> 0) 
          = (- 1) * A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0)"
        by (metis Hermite_of_row_i_0 a1 a2 an assms carrier_matD(2) i i0 index_mat_multrow(1,4))
      then show ?thesis using nz_iH Some a1 Aia a2 i0 unfolding Hermite_of_row_i_def by auto 
    qed
    thus "?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0) \<in> range ass_function_euclidean"
      using ass_function_int ass_function_int_UNIV by auto
    qed
    show "\<forall>i<dim_row ?H. \<not> is_zero_row_JNF i ?H \<longrightarrow> (\<forall>j<i. ?H $$ (j, LEAST n. ?H $$ (i, n) \<noteq> 0)
    \<in> range (res_int (?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0))))"
      using Hermite_of_row_i[of A 0] A by auto
  qed
  
lemma Hermite_of_row_i_0_eq_0:
  assumes A: "A\<in>carrier_mat m n" and i: "i>0" and eA: "echelon_form_JNF A" and im: "i<m"
    and n0: "0<n"
  shows "Hermite_of_row_i A 0 $$ (i, 0) = 0"
proof -
  have Ai0: "A $$ (i, 0) = 0" by (rule echelon_form_JNF_first_column_0[OF eA A i im n0]) 
  show ?thesis
  proof (cases "find_fst_non0_in_row 0 A")
    case None  
    thus ?thesis using Ai0 unfolding Hermite_of_row_i_def by auto 
  next
    case (Some a)
    have "A $$ (0, a) \<noteq> 0"  and a0: "0 \<le> a" and an: "a<n"
      using find_fst_non0_in_row[OF A Some] A by auto
    then show ?thesis using Some Ai0 A an a0 im unfolding Hermite_of_row_i_def mat_multrow_def by auto
  qed
qed

  

lemma Hermite_Hermite_of_row_i_mx1:
  assumes A: "A \<in> carrier_mat m 1" and eA: "echelon_form_JNF A"
  shows "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (Hermite_of_row_i A 0)"
proof (rule Hermite_JNF_intro)
  show "Complete_set_non_associates (range ass_function_euclidean)"   
    using ass_function_Complete_set_non_associates ass_function_euclidean by blast
  show "Complete_set_residues (\<lambda>c. range (res_int c))"
    using res_function_Complete_set_residues res_function_res_int by blast
  have H: "Hermite_of_row_i A 0 : carrier_mat m 1" using A Hermite_of_row_i[of A] by auto
  have upA: "upper_triangular' A"
    by (simp add: eA echelon_form_JNF_imp_upper_triangular)
  show eH: "echelon_form_JNF (Hermite_of_row_i A 0)"
  proof (rule echelon_form_JNF_mx1[OF H])
    show "\<forall>i\<in>{1..<m}. HNF_Mod_Det_Algorithm.Hermite_of_row_i A 0 $$ (i, 0) = 0"
      using Hermite_of_row_i_0_eq_0 assms by auto
  qed (simp)
  let ?H = "Hermite_of_row_i A 0"
  show "\<forall>i<dim_row ?H. \<not> is_zero_row_JNF i ?H 
      \<longrightarrow> ?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0) \<in> range ass_function_euclidean"
  proof (auto)
    fix i assume i: "i<dim_row ?H" and nz_iH: "\<not> is_zero_row_JNF i ?H"
    have nz_iA: "\<not> is_zero_row_JNF i A"
      by (metis (full_types) Hermite_of_row_i Hermite_of_row_i_0 carrier_matD(1)
          i is_zero_row_JNF_multrow nz_iH)    
    have "?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0) \<ge> 0"
    proof (cases "find_fst_non0_in_row 0 A")
      case None
      have "is_zero_row_JNF i A"
        by (metis H upper_triangular'_def None assms(1) carrier_matD find_fst_non0_in_row_None
            i is_zero_row_JNF_def less_one linorder_neqE_nat not_less0 upA)
       then show ?thesis using nz_iH None unfolding Hermite_of_row_i_def by auto
     next
      case (Some a)
      have Aia: "A $$ (0,a) \<noteq> 0" and a0: "0 \<le> a" and an: "a<1"
        using find_fst_non0_in_row[OF A Some] A by auto  
      have nz_j_mA: "is_zero_row_JNF j (multrow 0 (- 1) A)" if j0: "j>0" and jm: "j<m" for j 
        unfolding is_zero_row_JNF_def using A j0 jm upA by auto
      show ?thesis
      proof (cases "i=0")
        case True
        then show ?thesis
          using nz_iH Some nz_j_mA A H i Aia an unfolding Hermite_of_row_i_def by auto
      next
        case False
        have nz_iA: "is_zero_row_JNF i A"
          by (metis False H Hermite_of_row_i_0 carrier_matD(1) i is_zero_row_JNF_multrow not_gr0 nz_iH nz_j_mA)
        hence "is_zero_row_JNF i (multrow 0 (- 1) A)" using A H i by auto
        then show ?thesis using nz_iH Some nz_j_mA False nz_iA 
          unfolding Hermite_of_row_i_def by fastforce
      qed
    qed
    thus "?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0) \<in> range ass_function_euclidean"
      using ass_function_int ass_function_int_UNIV by auto
    qed
    show "\<forall>i<dim_row ?H. \<not> is_zero_row_JNF i ?H \<longrightarrow> (\<forall>j<i. ?H $$ (j, LEAST n. ?H $$ (i, n) \<noteq> 0)
    \<in> range (res_int (?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0))))"
    proof auto
      fix i j assume i: "i<dim_row ?H" and nz_iH: "\<not> is_zero_row_JNF i ?H" and ji: "j<i"
      have "i=0"
        by (metis H upper_triangular'_def One_nat_def nz_iH eH i carrier_matD(2) nat_neq_iff
            echelon_form_JNF_imp_upper_triangular is_zero_row_JNF_def less_Suc0 not_less_zero)
      thus "?H $$ (j, LEAST n. ?H $$ (i, n) \<noteq> 0)
           \<in> range (res_int (?H $$ (i, LEAST n. ?H $$ (i, n) \<noteq> 0)))" using ji by auto
    qed
qed


lemma Hermite_of_list_of_rows_1xn:
  assumes A: "A \<in> carrier_mat 1 n"
    and eA: "echelon_form_JNF A" 
    and x: "\<forall>x \<in> set xs. x < 1" and xs: "xs\<noteq>[]"
  shows "Hermite_JNF (range ass_function_euclidean) 
  (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A xs)"
  using x xs
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  have x0: "x=0" using snoc.prems by auto
  show ?case 
  proof (cases "xs = []")
    case True    
    have "Hermite_of_list_of_rows A (xs @ [x]) = Hermite_of_row_i A 0"
      unfolding Hermite_of_list_of_rows_append x0 using True by auto
    then show ?thesis using Hermite_Hermite_of_row_i[OF A] by auto
  next
    case False
    have x0: "x=0" using snoc.prems by auto
    have hyp: "Hermite_JNF (range ass_function_euclidean) 
      (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A xs)"
        by (rule snoc.hyps, insert snoc.prems False, auto)
    have "Hermite_of_list_of_rows A (xs @ [x]) = Hermite_of_row_i (Hermite_of_list_of_rows A xs) 0"
      unfolding Hermite_of_list_of_rows_append hyp x0 ..
    thus ?thesis
      by (metis A Hermite_Hermite_of_row_i Hermite_of_list_of_rows carrier_matD(1))
  qed
qed


lemma Hermite_of_row_i_id_mx1:
  assumes H': "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) A"
    and x: "x<dim_row A" and A: "A\<in>carrier_mat m 1"
shows "Hermite_of_row_i A x = A"  
proof (cases "find_fst_non0_in_row x A")
  case None
  then show ?thesis unfolding Hermite_of_row_i_def by auto
next
  case (Some a)
  have eH: "echelon_form_JNF A" using H' unfolding Hermite_JNF_def by simp
  have ut_A: "upper_triangular' A" by (simp add: eH echelon_form_JNF_imp_upper_triangular)
  have a_least: "a = (LEAST n. A $$ (x,n) \<noteq> 0)" 
    by (rule find_fst_non0_in_row_LEAST[OF _ ut_A Some], insert x, auto)
  have Axa: "A $$ (x, a) \<noteq> 0" and xa: "x\<le>a" and a: "a<dim_col A"
    using find_fst_non0_in_row[OF A Some] unfolding a_least by auto
  have nz_xA: "\<not> is_zero_row_JNF x A" using Axa xa x a unfolding is_zero_row_JNF_def by blast
  have a0: "a = 0" using a A by auto
  have x0: "x=0" using echelon_form_JNF_first_column_0[OF eH A] Axa a0 xa by blast  
  have "A $$ (x, a) \<in> (range ass_function_euclidean)" 
    using nz_xA H' x unfolding a_least unfolding Hermite_JNF_def by auto
  hence "A $$ (x, a) > 0" using Axa unfolding image_def ass_function_euclidean_def by auto
  then show ?thesis unfolding Hermite_of_row_i_def using Some x0 by auto
qed

lemma Hermite_of_row_i_id_mx1':
  assumes eA: "echelon_form_JNF A"
    and x: "x<dim_row A" and A: "A\<in>carrier_mat m 1"
shows "Hermite_of_row_i A x = A \<or> Hermite_of_row_i A x = multrow 0 (- 1) A" 
proof (cases "find_fst_non0_in_row x A")
  case None
  then show ?thesis unfolding Hermite_of_row_i_def by auto
next
  case (Some a)
  have ut_A: "upper_triangular' A" by (simp add: eA echelon_form_JNF_imp_upper_triangular)
  have a_least: "a = (LEAST n. A $$ (x,n) \<noteq> 0)" 
    by (rule find_fst_non0_in_row_LEAST[OF _ ut_A Some], insert x, auto)
  have Axa: "A $$ (x, a) \<noteq> 0" and xa: "x\<le>a" and a: "a<dim_col A"
    using find_fst_non0_in_row[OF A Some] unfolding a_least by auto
  have nz_xA: "\<not> is_zero_row_JNF x A" using Axa xa x a unfolding is_zero_row_JNF_def by blast
  have a0: "a = 0" using a A by auto
  have x0: "x=0" using echelon_form_JNF_first_column_0[OF eA A] Axa a0 xa by blast
  show ?thesis by (cases "A $$(x,a)>0", unfold Hermite_of_row_i_def, insert Some x0, auto)
qed


lemma Hermite_of_list_of_rows_mx1:
  assumes A: "A \<in> carrier_mat m 1"
    and eA: "echelon_form_JNF A" 
    and x: "\<forall>x \<in> set xs. x < m" and xs: "xs=[0..<i]" and i: "i>0"
  shows "Hermite_JNF (range ass_function_euclidean) 
  (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A xs)"
  using x xs i
proof (induct xs arbitrary: i rule: rev_induct)
  case Nil
  then show ?case by (metis neq0_conv not_less upt_eq_Nil_conv)
next
  case (snoc x xs)
  note all_n_xs_x = snoc.prems(1)
  note xs_x = snoc.prems(2)
  note i0 = snoc.prems(3)
  have i_list_rw:"[0..<i] = [0..<i-1] @ [i-1]" using i0 less_imp_Suc_add by fastforce
  hence xs: "xs = [0..<i-1]" using xs_x by force
  hence x: "x=i-1" using i_list_rw xs_x by auto
  have H: "Hermite_of_list_of_rows A xs \<in> carrier_mat m 1"
    using A Hermite_of_list_of_rows[of A xs] by auto
  show ?case
  proof (cases "i-1=0")
    case True
    hence xs_empty: "xs = []" using xs by auto
    have *: "Hermite_of_list_of_rows A (xs @ [x]) = Hermite_of_row_i A 0"
      unfolding Hermite_of_list_of_rows_append xs_empty x True by simp    
    show ?thesis unfolding * by (rule Hermite_Hermite_of_row_i_mx1[OF A eA])
  next
    case False          
    have hyp: "Hermite_JNF (range ass_function_euclidean) 
      (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A xs)"
      by (rule snoc.hyps[OF _ xs], insert False all_n_xs_x, auto)
    have "Hermite_of_list_of_rows A (xs @ [x]) 
        = Hermite_of_row_i (Hermite_of_list_of_rows A xs) x" 
      unfolding Hermite_of_list_of_rows_append ..
    also have "... = (Hermite_of_list_of_rows A xs)"
      by (rule Hermite_of_row_i_id_mx1[OF hyp _ H], insert snoc.prems H x, auto)
    finally show ?thesis using hyp by auto
  qed
qed



lemma invertible_Hermite_of_list_of_rows_1xn:
  assumes "A \<in> carrier_mat 1 n"
  shows "\<exists>P. P \<in> carrier_mat 1 1 \<and> invertible_mat P \<and> Hermite_of_list_of_rows A [0..<1] = P * A"
proof -
  let ?H = "Hermite_of_list_of_rows A [0..<1]"
  have "?H = Hermite_of_row_i A 0" by auto 
  hence H_or: "?H = A \<or> ?H = multrow 0 (- 1) A"
    using Hermite_of_row_i_0 by simp
  show ?thesis
  proof (cases "?H = A")
    case True
    then show ?thesis
      by (metis assms invertible_mat_one left_mult_one_mat one_carrier_mat)
  next
    case False
    hence H_mr: "?H = multrow 0 (- 1) A" using H_or by simp
    let ?M = "multrow_mat 1 0 (-1)::int mat"
    show ?thesis
    proof (rule exI[of _ "?M"])
      have "?M \<in> carrier_mat 1 1" by auto
      moreover have "invertible_mat ?M"
        by (metis calculation det_multrow_mat det_one dvd_mult_right invertible_iff_is_unit_JNF
            invertible_mat_one one_carrier_mat square_eq_1_iff zero_less_one_class.zero_less_one)
      moreover have "?H= ?M * A"
        by (metis H_mr assms multrow_mat)      
      ultimately show "?M \<in> carrier_mat 1 1 \<and> invertible_mat (?M) 
  \<and> Hermite_of_list_of_rows A [0..<1] = ?M * A" by blast
    qed
  qed
qed



lemma invertible_Hermite_of_list_of_rows_mx1':
  assumes A: "A \<in> carrier_mat m 1" and eA: "echelon_form_JNF A"
    and xs_i: "xs = [0..<i]" and xs_m: "\<forall>x\<in>set xs. x < m" and i: "i>0"
  shows "\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> Hermite_of_list_of_rows A xs = P * A"
  using xs_i xs_m i
proof (induct xs arbitrary: i rule: rev_induct)
  case Nil
  then show ?case by (metis diff_zero length_upt list.size(3) zero_order(3))
next
  case (snoc x xs)
  note all_n_xs_x = snoc.prems(2)
  note xs_x = snoc.prems(1)
  note i0 = snoc.prems(3)
  have i_list_rw:"[0..<i] = [0..<i-1] @ [i-1]" using i0 less_imp_Suc_add by fastforce
  hence xs: "xs = [0..<i-1]" using xs_x by force
  hence x: "x=i-1" using i_list_rw xs_x by auto
  have H: "Hermite_of_list_of_rows A xs \<in> carrier_mat m 1"
    using A Hermite_of_list_of_rows[of A xs] by auto
  show ?case
  proof (cases "i-1=0")
    case True
    hence xs_empty: "xs = []" using xs by auto
    let ?H = "Hermite_of_list_of_rows A (xs @ [x])"
    have *: "Hermite_of_list_of_rows A (xs @ [x]) = Hermite_of_row_i A 0"
      unfolding Hermite_of_list_of_rows_append xs_empty x True by simp  
    hence H_or: "?H = A \<or> ?H = multrow 0 (- 1) A" using Hermite_of_row_i_0 by simp
    thus ?thesis
    proof (cases "?H=A")
      case True
      then show ?thesis unfolding * 
        by (metis A invertible_mat_one left_mult_one_mat one_carrier_mat)
    next
      case False
      hence H_mr: "?H = multrow 0 (- 1) A" using H_or by simp    
      let ?M = "multrow_mat m 0 (-1)::int mat"
    show ?thesis 
    proof (rule exI[of _ "?M"])
      have "?M \<in> carrier_mat m m" by auto
      moreover have "invertible_mat ?M"
        by (metis (full_types) det_multrow_mat dvd_mult_right invertible_iff_is_unit_JNF
            invertible_mat_zero more_arith_simps(10) mult_minus1_right multrow_mat_carrier neq0_conv)
      moreover have "?H = ?M * A" unfolding H_mr using A multrow_mat by blast            
      ultimately show "?M \<in> carrier_mat m m \<and> invertible_mat ?M \<and> ?H = ?M * A" by blast
    qed
  qed
  next
    case False
    let ?A = "(Hermite_of_list_of_rows A xs)"
    have A': "?A \<in> carrier_mat m 1" using A Hermite_of_list_of_rows[of A xs] by simp
    have hyp: "\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> Hermite_of_list_of_rows A xs = P * A"
      by (rule snoc.hyps[OF xs], insert False all_n_xs_x, auto)
    have rw: "Hermite_of_list_of_rows A (xs @ [x]) 
        = Hermite_of_row_i (Hermite_of_list_of_rows A xs) x" 
      unfolding Hermite_of_list_of_rows_append ..
    have *: "Hermite_of_row_i ?A x = ?A \<or> Hermite_of_row_i ?A x = multrow 0 (- 1) ?A"
    proof (rule Hermite_of_row_i_id_mx1'[OF _ _ A'])
      show "echelon_form_JNF ?A"
        using A eA echelon_form_JNF_Hermite_of_list_of_rows snoc(3) by auto
      show "x < dim_row ?A" using A' x i A by (simp add: snoc(3))
    qed
    show ?thesis
    proof (cases "Hermite_of_row_i ?A x = ?A")
    case True
      then show ?thesis 
        by (simp add: hyp rw)
    next
      case False
      let ?M = "multrow_mat m 0 (-1)::int mat"
      obtain P where P: "P \<in> carrier_mat m m" 
        and inv_P: "invertible_mat P" and H_PA: "Hermite_of_list_of_rows A xs = P * A"
        using hyp by auto
      have M: "?M \<in> carrier_mat m m" by auto
      have inv_M: "invertible_mat ?M"
        by (metis (full_types) det_multrow_mat dvd_mult_right invertible_iff_is_unit_JNF
            invertible_mat_zero more_arith_simps(10) mult_minus1_right multrow_mat_carrier neq0_conv)
      have H_MA': "Hermite_of_row_i ?A x = ?M * ?A" using False * H multrow_mat by metis
      have inv_MP: "invertible_mat (?M*P)" using M inv_M P inv_P invertible_mult_JNF by blast
      moreover have MP: "(?M*P) \<in> carrier_mat m m" using M P by fastforce
      moreover have "Hermite_of_list_of_rows A (xs @ [x]) = (?M*P) * A"
        by (metis A H_MA' H_PA M P assoc_mult_mat rw)  
      ultimately show ?thesis by blast
    qed  
  qed
qed


corollary invertible_Hermite_of_list_of_rows_mx1:
  assumes "A \<in> carrier_mat m 1" and eA: "echelon_form_JNF A"
  shows "\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> Hermite_of_list_of_rows A [0..<m] = P * A"
proof (cases "m=0")
  case True
  then show ?thesis 
    by (auto, metis assms(1) invertible_mat_one left_mult_one_mat one_carrier_mat)
next
  case False
  then show ?thesis using invertible_Hermite_of_list_of_rows_mx1' assms by simp
qed
  

lemma Hermite_of_list_of_rows_mx0:
  assumes A: "A \<in> carrier_mat m 0"
  and xs: "xs = [0..<i]" and x: "\<forall>x\<in> set xs. x < m"
shows "Hermite_of_list_of_rows A xs = A"
  using xs x
proof (induct xs arbitrary: i rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)    
  note all_n_xs_x = snoc.prems(2)
  note xs_x = snoc.prems(1)
  have i0: "i>0" using neq0_conv snoc(2) by fastforce
  have i_list_rw:"[0..<i] = [0..<i-1] @ [i-1]" using i0 less_imp_Suc_add by fastforce
  hence xs: "xs = [0..<i-1]" using xs_x by force
  hence x: "x=i-1" using i_list_rw xs_x by auto
  have H: "Hermite_of_list_of_rows A xs \<in> carrier_mat m 0"
    using A Hermite_of_list_of_rows[of A xs] by auto
  define A' where "A' = (Hermite_of_list_of_rows A xs)"
  have A'A: "A' = A" by (unfold A'_def, rule snoc.hyps, insert snoc.prems xs, auto)
  have "Hermite_of_list_of_rows A (xs @ [x]) = Hermite_of_row_i A' x"
    using Hermite_of_list_of_rows_append A'_def by auto
  also have "... = A"
  proof (cases "find_fst_non0_in_row x A'")
    case None
    then show ?thesis unfolding Hermite_of_row_i_def using A'A by auto
    next
      case (Some a)
    then show ?thesis
      by (metis (full_types) A'A A carrier_matD(2) find_fst_non0_in_row(3) zero_order(3))
  qed
  finally show ?case .
qed


text \<open>Again, we move more lemmas from HOL Analysis (with mod-type restrictions) to the JNF matrix
representation.\<close>

(*
The following lemmas will be transferred from HOL Analysis to JNF:
thm Hermite_Hermite_of_upt_row_i
thm invertible_Hermite_of_upt_row_i
*)

context
begin

private lemma Hermite_Hermite_of_list_of_rows_mod_type:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('m::mod_type) CARD('n::mod_type)"
  assumes eA: "echelon_form_JNF A"
shows "Hermite_JNF (range ass_function_euclidean) 
  (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A [0..<CARD('m)])"
proof -
  define A' where "A' = (Mod_Type_Connect.to_hma\<^sub>m A :: int ^'n :: mod_type ^'m :: mod_type)"
  have AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'"
    unfolding Mod_Type_Connect.HMA_M_def using assms A'_def by auto 
  have eA'[transfer_rule]: "echelon_form A'" using eA by transfer
  have [transfer_rule]: "Mod_Type_Connect.HMA_M (Hermite_of_list_of_rows A [0..<CARD('m)]) 
  (Hermite_of_upt_row_i A' (CARD('m)) ass_function_euclidean res_int)"
    by (rule HMA_Hermite_of_upt_row_i[OF _ _ AA' eA], auto)
  have [transfer_rule]: " (range ass_function_euclidean) =  (range ass_function_euclidean)" ..
  have [transfer_rule]: "(\<lambda>c. range (res_int c)) = (\<lambda>c. range (res_int c))" ..
  have n: "CARD('m) = nrows A'" using AA' unfolding nrows_def by auto
  have "Hermite (range ass_function_euclidean) (\<lambda>c. range (res_int c)) 
  (Hermite_of_upt_row_i A' (CARD('m)) ass_function_euclidean res_int)"
    by (unfold n, rule Hermite_Hermite_of_upt_row_i[OF ass_function_euclidean res_function_res_int eA'])    
  thus ?thesis by transfer
qed 

private lemma invertible_Hermite_of_list_of_rows_mod_type:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('m::mod_type) CARD('n::mod_type)"
  assumes eA: "echelon_form_JNF A"
  shows "\<exists>P. P \<in> carrier_mat CARD('m) CARD('m) \<and> 
    invertible_mat P \<and> Hermite_of_list_of_rows A [0..<CARD('m)] = P * A"
proof -
  define A' where "A' = (Mod_Type_Connect.to_hma\<^sub>m A :: int ^'n :: mod_type ^'m :: mod_type)"
  have AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'"
    unfolding Mod_Type_Connect.HMA_M_def using assms A'_def by auto 
  have eA'[transfer_rule]: "echelon_form A'" using eA by transfer
  have [transfer_rule]: "Mod_Type_Connect.HMA_M (Hermite_of_list_of_rows A [0..<CARD('m)]) 
  (Hermite_of_upt_row_i A' (CARD('m)) ass_function_euclidean res_int)"
    by (rule HMA_Hermite_of_upt_row_i[OF _ _ AA' eA], auto)
  have [transfer_rule]: " (range ass_function_euclidean) =  (range ass_function_euclidean)" ..
  have [transfer_rule]: "(\<lambda>c. range (res_int c)) = (\<lambda>c. range (res_int c))" ..
  have n: "CARD('m) = nrows A'" using AA' unfolding nrows_def by auto
  have "\<exists>P. invertible P \<and> Hermite_of_upt_row_i A' (CARD('m)) ass_function_euclidean res_int 
      = P ** A'" by (rule invertible_Hermite_of_upt_row_i[OF ass_function_euclidean])
  thus ?thesis by (transfer, auto)
qed


private lemma Hermite_Hermite_of_list_of_rows_nontriv_mod_ring:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('m::nontriv mod_ring) CARD('n::nontriv mod_ring)"
  assumes eA: "echelon_form_JNF A"
shows "Hermite_JNF (range ass_function_euclidean) 
  (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A [0..<CARD('m)])"
using assms Hermite_Hermite_of_list_of_rows_mod_type by (smt CARD_mod_ring) 

private lemma invertible_Hermite_of_list_of_rows_nontriv_mod_ring:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('m::nontriv mod_ring) CARD('n::nontriv mod_ring)"
  assumes eA: "echelon_form_JNF A"
  shows "\<exists>P. P \<in> carrier_mat CARD('m) CARD('m) \<and> 
    invertible_mat P \<and> Hermite_of_list_of_rows A [0..<CARD('m)] = P * A"
using assms invertible_Hermite_of_list_of_rows_mod_type by (smt CARD_mod_ring) 


(*We internalize both sort constraints in one step*)
lemmas Hermite_Hermite_of_list_of_rows_nontriv_mod_ring_internalized = 
  Hermite_Hermite_of_list_of_rows_nontriv_mod_ring[unfolded CARD_mod_ring, 
      internalize_sort "'m::nontriv", internalize_sort "'b::nontriv"]

lemmas invertible_Hermite_of_list_of_rows_nontriv_mod_ring_internalized = 
  invertible_Hermite_of_list_of_rows_nontriv_mod_ring[unfolded CARD_mod_ring, 
      internalize_sort "'m::nontriv", internalize_sort "'b::nontriv"]


context
  fixes m::nat and n::nat
  assumes local_typedef1: "\<exists>(Rep :: ('b \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<m :: int}"
  assumes local_typedef2: "\<exists>(Rep :: ('c \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<n :: int}"
  and m: "m>1"
  and n: "n>1"
begin

lemma Hermite_Hermite_of_list_of_rows_nontriv_mod_ring_aux:
 fixes A::"int mat"
   assumes "A \<in> carrier_mat m n"
  assumes eA: "echelon_form_JNF A"
shows "Hermite_JNF (range ass_function_euclidean) 
  (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A [0..<m])"
  using Hermite_Hermite_of_list_of_rows_nontriv_mod_ring_internalized
    [OF type_to_set2(1)[OF local_typedef1 local_typedef2] 
        type_to_set1(1)[OF local_typedef1 local_typedef2]]
  using assms 
  using type_to_set1(2) local_typedef1 local_typedef2 n m by metis 



lemma invertible_Hermite_of_list_of_rows_nontriv_mod_ring_aux:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat m n"
  assumes eA: "echelon_form_JNF A"
  shows "\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> Hermite_of_list_of_rows A [0..<m] = P * A"
using invertible_Hermite_of_list_of_rows_nontriv_mod_ring_internalized
    [OF type_to_set2(1)[OF local_typedef1 local_typedef2] 
        type_to_set1(1)[OF local_typedef1 local_typedef2]]
  using assms 
  using type_to_set1(2) local_typedef1 local_typedef2 n m by metis 
end


(*Canceling the first local type definitions*)
context
begin

(*Canceling the first*)
private lemma invertible_Hermite_of_list_of_rows_cancelled_first:
  "\<exists>Rep Abs. type_definition Rep Abs {0..<int n} 
  \<Longrightarrow> 1 < m \<Longrightarrow> 1 < n \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> echelon_form_JNF A 
  \<Longrightarrow> \<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> Hermite_of_list_of_rows A [0..<m] = P * A"
  using invertible_Hermite_of_list_of_rows_nontriv_mod_ring_aux[cancel_type_definition, of m n A]
  by auto  

(*Canceling the second*)
private lemma invertible_Hermite_of_list_of_rows_cancelled_both:
  "1 < m \<Longrightarrow> 1 < n \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> echelon_form_JNF A 
  \<Longrightarrow> \<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> Hermite_of_list_of_rows A [0..<m] = P * A"
  using invertible_Hermite_of_list_of_rows_cancelled_first[cancel_type_definition, of n m A] by simp


(*Canceling the first*)

private lemma Hermite_Hermite_of_list_of_rows_cancelled_first:
"\<exists>Rep Abs. type_definition Rep Abs {0..<int n} \<Longrightarrow>
  1 < m \<Longrightarrow>
  1 < n \<Longrightarrow>
  A \<in> carrier_mat m n \<Longrightarrow>
  echelon_form_JNF A 
  \<Longrightarrow> Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A [0..<m])"
  using Hermite_Hermite_of_list_of_rows_nontriv_mod_ring_aux[cancel_type_definition, of m n A]
  by auto  

(*Canceling the second*)
private lemma Hermite_Hermite_of_list_of_rows_cancelled_both:
"1 < m \<Longrightarrow>
  1 < n \<Longrightarrow>
  A \<in> carrier_mat m n \<Longrightarrow>
  echelon_form_JNF A 
  \<Longrightarrow> Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A [0..<m])"
  using Hermite_Hermite_of_list_of_rows_cancelled_first[cancel_type_definition, of n m A] by simp


(*The final results in JNF*)

lemma Hermite_Hermite_of_list_of_rows':
 fixes A::"int mat"
  assumes "A \<in> carrier_mat m n"
    and "echelon_form_JNF A"  
  and "1 < m" and "1 < n" (*Required from the mod_type restrictions*)
shows "Hermite_JNF (range ass_function_euclidean) 
  (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A [0..<m])"  
  using Hermite_Hermite_of_list_of_rows_cancelled_both assms by auto

corollary Hermite_Hermite_of_list_of_rows:
 fixes A::"int mat"
  assumes A: "A \<in> carrier_mat m n"
    and eA: "echelon_form_JNF A"  
shows "Hermite_JNF (range ass_function_euclidean) 
  (\<lambda>c. range (res_int c)) (Hermite_of_list_of_rows A [0..<m])"
proof (cases "m=0 \<or> n=0")
  case True
  then show ?thesis 
    by (auto, metis Hermite_Hermite_of_row_i Hermite_JNF_def A eA carrier_matD(1) one_carrier_mat zero_order(3))   
     (metis Hermite_Hermite_of_row_i Hermite_JNF_def Hermite_of_list_of_rows A carrier_matD(2) 
       echelon_form_mx0 is_zero_row_JNF_def mat_carrier zero_order(3))
next
  case False note not_m0_or_n0 = False
  show ?thesis
  proof (cases "m=1 \<or> n=1")
    case True
    then show ?thesis
      by (metis False Hermite_of_list_of_rows_1xn Hermite_of_list_of_rows_mx1 A eA 
          atLeastLessThan_iff linorder_not_less neq0_conv set_upt upt_eq_Nil_conv)
  next
    case False
    show ?thesis
      by (rule Hermite_Hermite_of_list_of_rows'[OF A eA], insert not_m0_or_n0 False, auto)
  qed
qed

lemma invertible_Hermite_of_list_of_rows:
  assumes A: "A \<in> carrier_mat m n"
  and eA: "echelon_form_JNF A"
shows "\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> Hermite_of_list_of_rows A [0..<m] = P * A"
proof (cases "m=0 \<or> n=0")
  case True
  have *: "Hermite_of_list_of_rows A [0..<m] = A" if n: "n=0"
    by (rule Hermite_of_list_of_rows_mx0, insert A n, auto)
  show ?thesis using True
    by (auto, metis assms(1) invertible_mat_one left_mult_one_mat one_carrier_mat)
       (metis (full_types) "*" assms(1) invertible_mat_one left_mult_one_mat one_carrier_mat)
next
  case False note mn = False
  show ?thesis
  proof (cases "m=1 \<or> n=1")
    case True
    then show ?thesis 
      using A eA invertible_Hermite_of_list_of_rows_1xn invertible_Hermite_of_list_of_rows_mx1 by blast
  next
    case False
    then show ?thesis 
      using invertible_Hermite_of_list_of_rows_cancelled_both[OF _ _ A eA] False mn by auto
  qed  
qed
end
end
end
end


text \<open>Now we have all the required stuff to prove the soundness of the algorithm.\<close>

context proper_mod_operation
begin

(*
thm invertible_Hermite_of_list_of_rows
thm Hermite_Hermite_of_list_of_rows
thm LLL_with_assms.Hermite_append_det_id
thm FindPreHNF_invertible_mat
thm FindPreHNF_echelon_form
*)

lemma Hermite_mod_det_mx0:
  assumes "A \<in> carrier_mat m 0"
  shows "Hermite_mod_det abs_flag A = A"
  unfolding Hermite_mod_det_def Let_def using assms by auto

lemma Hermite_JNF_mx0:
  assumes A: "A \<in> carrier_mat m 0"
  shows "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) A"
  unfolding Hermite_JNF_def using A echelon_form_mx0 unfolding is_zero_row_JNF_def 
  using ass_function_Complete_set_non_associates[OF ass_function_euclidean]
  using res_function_Complete_set_residues[OF res_function_res_int] by auto
  

lemma Hermite_mod_det_soundness_mx0:
  assumes  A: "A \<in> carrier_mat m n"
  and n0: "n=0"
shows "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (Hermite_mod_det abs_flag A)" 
and "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> (Hermite_mod_det abs_flag A) = P * A)"
proof -
  have A: "A \<in> carrier_mat m 0" using A n0 by blast
  then show "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (Hermite_mod_det abs_flag A)"
    using Hermite_JNF_mx0[OF A] Hermite_mod_det_mx0[OF A] by auto
  show "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> (Hermite_mod_det abs_flag A) = P * A)"
    by (metis A Hermite_mod_det_mx0 invertible_mat_one left_mult_one_mat one_carrier_mat)
qed


lemma Hermite_mod_det_soundness_mxn:
  assumes mn: "m = n"
  and A: "A \<in> carrier_mat m n"
  and n0: "0<n"
  and inv_RAT_A: "invertible_mat (map_mat rat_of_int A)"
shows "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (Hermite_mod_det abs_flag A)" 
  and "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> (Hermite_mod_det abs_flag A) = P * A)"
proof -
  define D A' E H H' where D_def: "D = \<bar>Determinant.det A\<bar>"
  and A'_def: "A' = A @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n" and E_def: "E = FindPreHNF abs_flag D A'"
  and H_def: "H = Hermite_of_list_of_rows E [0..<m+n]"
  and H'_def: "H' = mat_of_rows n (map (Matrix.row H) [0..<m])"
  have A': "A' \<in> carrier_mat (m+n) n" using A A A'_def by auto
  let ?RAT = "of_int_hom.mat_hom :: int mat \<Rightarrow> rat mat"
  have RAT_A: "?RAT A \<in> carrier_mat n n"
    using A map_carrier_mat mat_of_rows_carrier(1) mn by auto 
  have det_RAT_fs_init: "det (?RAT A) \<noteq> 0"
    using inv_RAT_A unfolding invertible_iff_is_unit_JNF[OF RAT_A] by auto
  moreover have "mat_of_rows n (map (Matrix.row A') [0..<n]) = A"
  proof
    let ?A' = "mat_of_rows n (map (Matrix.row A') [0..<n])"    
    show dr: "dim_row ?A' = dim_row A" and dc: "dim_col ?A' = dim_col A" using A mn by auto
    fix i j assume i: "i < dim_row A" and j: "j < dim_col A"
    have D: "D \<cdot>\<^sub>m 1\<^sub>m n \<in> carrier_mat n n" using mn by auto
    have "?A' $$ (i,j) =  (map (Matrix.row A') [0..<n]) ! i $v j"
      by (rule mat_of_rows_index, insert i j dr dc A, auto) 
    also have "... = A' $$ (i,j)" using A' mn i j A by auto
    also have "... = A $$ (i,j)" unfolding A'_def using i append_rows_nth[OF A D] mn j A by auto
    finally show "?A' $$ (i, j) = A $$ (i, j)" .
  qed
  ultimately have inv_RAT_A'n: 
    "invertible_mat (map_mat rat_of_int (mat_of_rows n (map (Matrix.row A') [0..<n])))" 
    using inv_RAT_A by auto
  have eE: "echelon_form_JNF E"
    by (unfold E_def, rule FindPreHNF_echelon_form[OF A'_def A _ _],
        insert mn D_def det_RAT_fs_init, auto)
  have E: "E \<in> carrier_mat (m+n) n" unfolding E_def by (rule FindPreHNF[OF A'])
  have "\<exists>P. P \<in> carrier_mat (m + n) (m + n) \<and> invertible_mat P \<and> E = P * A'"
  by (unfold E_def, rule FindPreHNF_invertible_mat[OF A'_def A n0 _ _],
      insert mn D_def det_RAT_fs_init, auto)
  from this obtain P where P: "P \<in> carrier_mat (m + n) (m + n)"
    and inv_P: "invertible_mat P" and E_PA': "E = P * A'"
    by blast
  have "\<exists>Q. Q \<in> carrier_mat (m+n) (m+n) \<and> invertible_mat Q \<and> H = Q * E"
    by (unfold H_def, rule invertible_Hermite_of_list_of_rows[OF E eE])  
  from this obtain Q where Q: "Q \<in> carrier_mat (m+n) (m+n)"
    and inv_Q: "invertible_mat Q" and H_QE: "H = Q * E" by blast
  let ?ass ="(range ass_function_euclidean)"
  let ?res = "(\<lambda>c. range (res_int c))"
  have Hermite_H: "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) H"
    by (unfold H_def, rule Hermite_Hermite_of_list_of_rows[OF E eE])
  hence eH: "echelon_form_JNF H" unfolding Hermite_JNF_def by auto
  have H': "H' \<in> carrier_mat m n" using H'_def by auto
  have H_H'0: "H = H' @\<^sub>r 0\<^sub>m m n"
  proof (unfold H'_def, rule upper_triangular_append_zero)
    show "upper_triangular' H" using eH by (rule echelon_form_JNF_imp_upper_triangular)
    show "H \<in> carrier_mat (m + m) n"
      unfolding H_def using Hermite_of_list_of_rows[of E] E mn by auto
  qed (insert mn, simp)
  obtain P' where PP': "inverts_mat P P'"
    and P'P: "inverts_mat P' P" and P': "P' \<in> carrier_mat (m+n) (m+n)"         
    using P inv_P obtain_inverse_matrix by blast
  obtain Q' where QQ': "inverts_mat Q Q'"
    and Q'Q: "inverts_mat Q' Q" and Q': "Q' \<in> carrier_mat (m+n) (m+n)"         
    using Q inv_Q obtain_inverse_matrix by blast
  have P'Q': "(P'*Q') \<in> carrier_mat (m + m) (m + m)" using P' Q' mn by simp
  have A'_P'Q'H: "A' = P' * Q' * H"
  proof -
    have QP: "Q * P \<in> carrier_mat (m + m) (m + m)" using Q P mn by auto
    have "H = Q * (P * A')" using H_QE E_PA' by auto
    also have "... = (Q * P) * A'" using A' P Q by auto
    also have "(P' * Q') * ... = ((P' * Q') * (Q * P)) * A'" using A' P'Q' QP mn by auto
    also have "... =  (P' * (Q' * Q) * P) * A'"
      by (smt P P' P'Q' Q Q' assms(1) assoc_mult_mat)
    also have "... = (P'*P) * A'" 
      by (metis P' Q' Q'Q carrier_matD(1) inverts_mat_def right_mult_one_mat)
    also have "... = A'"
      by (metis A' P' P'P carrier_matD(1) inverts_mat_def left_mult_one_mat)
    finally show "A' = P' * Q' * H" ..
  qed
  have inv_P'Q': "invertible_mat (P' * Q')"
    by (metis P' P'P PP' Q' Q'Q QQ' carrier_matD(1) carrier_matD(2) invertible_mat_def
        invertible_mult_JNF square_mat.simps)
  interpret vec_module "TYPE(int)" .
  interpret B: cof_vec_space n "TYPE(rat)" .
  interpret A: LLL_with_assms n m "(Matrix.rows A)" "4/3"
  proof       
    show "length (rows A) = m " using A unfolding Matrix.rows_def by simp
    have s: "set (map of_int_hom.vec_hom (rows A)) \<subseteq> carrier_vec n"
      using A unfolding Matrix.rows_def by auto
    have rw: "(map of_int_hom.vec_hom (rows A)) = (rows (?RAT A))" 
      by (metis A s carrier_matD(2) mat_of_rows_map mat_of_rows_rows rows_mat_of_rows set_rows_carrier subsetI)
    have "B.lin_indpt (set (map of_int_hom.vec_hom (rows A)))"
      unfolding rw by (rule B.det_not_0_imp_lin_indpt_rows[OF RAT_A det_RAT_fs_init])
    moreover have "distinct (map of_int_hom.vec_hom (rows A)::rat Matrix.vec list)"
    proof (rule ccontr)
      assume " \<not> distinct (map of_int_hom.vec_hom (rows A)::rat Matrix.vec list)"
      from this obtain i j where "row (?RAT A) i = row (?RAT A) j" and "i \<noteq> j" and "i < n" and "j < n"
        unfolding rw
        by (metis Determinant.det_transpose RAT_A add_0 cols_transpose det_RAT_fs_init 
            not_add_less2 transpose_carrier_mat vec_space.det_rank_iff vec_space.non_distinct_low_rank)
      thus False using Determinant.det_identical_rows[OF RAT_A] using det_RAT_fs_init RAT_A by auto      
    qed      
    ultimately show "B.lin_indpt_list (map of_int_hom.vec_hom (rows A))"
      using s unfolding B.lin_indpt_list_def by auto
  qed (simp)
  have A_eq: "mat_of_rows n (Matrix.rows A) = A" using A mat_of_rows_rows by blast
  have D_A: "D = \<bar>det (mat_of_rows n (rows A))\<bar>" using D_def A_eq by auto
  have Hermite_H': "Hermite_JNF ?ass ?res H'"
    by (rule A.Hermite_append_det_id(1)[OF _ mn _ H' H_H'0 P'Q' inv_P'Q' A'_P'Q'H Hermite_H],
         insert D_def A'_def mn A inv_RAT_A D_A A_eq, auto) 
  have dc: "dim_row A = m" and dr: "dim_col A = n" using A by auto
  have Hermite_mod_det_H': "Hermite_mod_det abs_flag A = H'" 
    unfolding Hermite_mod_det_def Let_def H'_def H_def E_def A'_def D_def dc dr det_int by blast
  show "Hermite_JNF ?ass ?res (Hermite_mod_det abs_flag A)" using Hermite_mod_det_H' Hermite_H' by simp
  have "\<exists>R. invertible_mat R \<and> R \<in> carrier_mat m m \<and> A = R * H'"
    by (subst A_eq[symmetric], 
        rule A.Hermite_append_det_id(2)[OF _ mn _ H' H_H'0 P'Q' inv_P'Q' A'_P'Q'H Hermite_H],
        insert D_def A'_def mn A inv_RAT_A D_A A_eq, auto)
  from this obtain R where inv_R: "invertible_mat R" 
    and R: "R \<in> carrier_mat m m" and A_RH': "A = R * H'"
    by blast
  obtain R' where inverts_R: "inverts_mat R R'" and R': "R' \<in> carrier_mat m m"    
    by (meson R inv_R obtain_inverse_matrix)
  have inv_R': "invertible_mat R'" using inverts_R unfolding invertible_mat_def inverts_mat_def
    using R R' mat_mult_left_right_inverse by auto
  moreover have "H' = R' * A"
  proof -
    have "R' * A = R' * (R * H')" using A_RH' by auto
    also have "... = (R'*R) * H'" using H' R R' by auto
    also have "... = H'"
      by (metis H' R R' mat_mult_left_right_inverse carrier_matD(1) 
          inverts_R inverts_mat_def left_mult_one_mat)
    finally show ?thesis ..
  qed
  ultimately show "\<exists>S. invertible_mat S \<and> S \<in> carrier_mat m m \<and> Hermite_mod_det abs_flag A = S * A" 
    using R' Hermite_mod_det_H' by blast
qed


lemma Hermite_mod_det_soundness:
  assumes mn: "m = n"
  and A_def: "A \<in> carrier_mat m n"
  and i: "invertible_mat (map_mat rat_of_int A)"
shows "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (Hermite_mod_det abs_flag A)" 
  and "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> (Hermite_mod_det abs_flag A) = P * A)" 
  using A_def Hermite_mod_det_soundness_mx0(1) Hermite_mod_det_soundness_mxn(1) mn i 
  by blast (insert Hermite_mod_det_soundness_mx0(2) Hermite_mod_det_soundness_mxn(2) assms, blast)


text \<open>We can even move the whole echelon form algorithm @{text "echelon_form_of"} from HOL Analysis 
to JNF and then we can combine it with @{text "Hermite_of_list_of_rows"} to have another 
HNF algorithm which is not efficient, but valid for arbitrary matrices.\<close>

lemma reduce_D0:
"reduce a b 0 A = (let Aaj = A$$(a,0); Abj = A $$ (b,0)     
  in
  if Aaj = 0 then A else
  case euclid_ext2 Aaj Abj of (p,q,u,v,d) \<Rightarrow> 
       Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then  (p*A$$(a,k) + q*A$$(b,k))
                   else if i = b then  u * A$$(a,k) + v * A$$(b,k)
                   else A$$(i,k)
            )
  )" (is "?lhs = ?rhs")
proof 
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A $$ (a, 0)) (A $$ (b, 0))"
    by (simp add: euclid_ext2_def) 
  have *:" Matrix.mat (dim_row A) (dim_col A)
        (\<lambda>(i, k).
            if i = a then let r = p * A $$ (a, k) + q * A $$ (b, k) in if 0 < \<bar>r\<bar> then 
                                  if k = 0 \<and> 0 dvd r then 0 else r mod 0 else r
            else if i = b then let r = u * A $$ (a, k) + v * A $$ (b, k) in 
                              if 0 < \<bar>r\<bar> then r mod 0 else r else A $$ (i, k)) 
        = Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then  (p*A$$(a,k) + q*A$$(b,k))
                   else if i = b then  u * A$$(a,k) + v * A$$(b,k)
                   else A$$(i,k) 
            )" 
    by (rule eq_matI, auto simp add: Let_def)
  show "dim_row ?lhs = dim_row ?rhs" 
    unfolding reduce.simps Let_def by (smt dim_row_mat(1) pquvd prod.simps(2))
  show "dim_col ?lhs = dim_col ?rhs"
    unfolding reduce.simps Let_def by (smt dim_col_mat(1) pquvd prod.simps(2))
  fix i j assume i: "i<dim_row ?rhs" and j: "j<dim_col ?rhs"
  show "?lhs $$ (i,j) = ?rhs $$ (i,j)"
    by (cases " A $$ (a, 0) = 0", insert * pquvd i j, auto simp add: case_prod_beta Let_def)
qed



lemma bezout_matrix_JNF_mult_eq':
  assumes A': "A' \<in> carrier_mat m n" and a: "a<m"  and b: "b<m" and ab: "a \<noteq> b" 
  and A_def: "A = A' @\<^sub>r B" and B: "B \<in> carrier_mat t n"
  assumes pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,j)) (A$$(b,j))"
  shows "Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(b,k))
                   else if i = b then u * A$$(a,k) + v * A$$(b,k)
                   else A$$(i,k)
            ) = (bezout_matrix_JNF A a b j euclid_ext2) * A" (is "?A = ?BM * A")
proof (rule eq_matI) 
  have A: "A \<in> carrier_mat (m+t) n" using A_def A' B by simp
  hence A_carrier: "?A \<in> carrier_mat (m+t) n" by auto  
  show dr: "dim_row ?A = dim_row (?BM * A)" and dc: "dim_col ?A = dim_col (?BM * A)"
    unfolding bezout_matrix_JNF_def by auto
  fix i ja assume i: "i < dim_row  (?BM * A)" and ja: "ja < dim_col (?BM * A)"
  let ?f = "\<lambda>ia. (bezout_matrix_JNF A a b j euclid_ext2) $$ (i,ia) * A $$ (ia,ja)"
  have dv: "dim_vec (col A ja) = m+t" using A by auto
  have i_dr: "i<dim_row A" using i A unfolding bezout_matrix_JNF_def by auto
  have a_dr: "a<dim_row A" using A a ja by auto
  have b_dr: "b<dim_row A" using A b ja by auto
  show "?A $$ (i,ja) = (?BM * A) $$ (i,ja)"
  proof -
    have "(?BM * A) $$ (i,ja) = Matrix.row ?BM i \<bullet> col A ja"
      by (rule index_mult_mat, insert i ja, auto)
    also have "... = (\<Sum>ia = 0..<dim_vec (col A ja). 
          Matrix.row (bezout_matrix_JNF A a b j euclid_ext2) i $v ia * col A ja $v ia)"
      by (simp add: scalar_prod_def)
    also have "... = (\<Sum>ia = 0..<m+t. ?f ia)"
      by (rule sum.cong, insert A i dr dc, auto) (smt bezout_matrix_JNF_def carrier_matD(1) 
          dim_col_mat(1) index_col index_mult_mat(3) index_row(1) ja)
    also have "... = (\<Sum>ia \<in> ({a,b} \<union> ({0..<m+t} - {a,b})). ?f ia)"
      by (rule sum.cong, insert a a_dr b A ja, auto)
    also have "... = sum ?f {a,b} + sum ?f ({0..<m+t} - {a,b})" 
      by (rule sum.union_disjoint, auto)
    finally have BM_A_ija_eq: "(?BM * A) $$ (i,ja) = sum ?f {a,b} + sum ?f ({0..<m+t} - {a,b})" by auto
    show ?thesis
    proof (cases "i = a")
      case True
      have sum0: "sum ?f ({0..<m+t} - {a,b}) = 0"
      proof (rule sum.neutral, rule)
        fix x assume x: "x \<in> {0..<m + t} - {a, b}"
        hence xm: "x < m+t" by auto
        have x_not_i: "x \<noteq> i" using True x by blast
        have x_dr: "x < dim_row A" using x A by auto
        have "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) = 0"
          unfolding bezout_matrix_JNF_def 
          unfolding index_mat(1)[OF i_dr x_dr] using x_not_i x by auto
        thus "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) * A $$ (x, ja) = 0" by auto
      qed
      have fa: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, a) = p" 
        unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr a_dr] using True pquvd 
        by (auto, metis split_conv)
      have fb: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, b) = q"
        unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr b_dr] using True pquvd ab
        by (auto, metis split_conv)
      have "sum ?f {a,b} + sum ?f ({0..<m+t} - {a,b}) = ?f a + ?f b" using sum0 by (simp add: ab)
      also have "... = p * A $$ (a, ja) + q * A $$ (b, ja)" unfolding fa fb by simp
      also have "... = ?A $$ (i,ja)" using A True dr i ja by auto
      finally show ?thesis using BM_A_ija_eq by simp
    next
      case False note i_not_a = False
      show ?thesis
      proof (cases "i=b")
        case True
        have sum0: "sum ?f ({0..<m+t} - {a,b}) = 0"
        proof (rule sum.neutral, rule)
          fix x assume x: "x \<in> {0..<m + t} - {a, b}"
          hence xm: "x < m+t" by auto
          have x_not_i: "x \<noteq> i" using True x by blast
          have x_dr: "x < dim_row A" using x A by auto
          have "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) = 0"
            unfolding bezout_matrix_JNF_def 
            unfolding index_mat(1)[OF i_dr x_dr] using x_not_i x by auto
          thus "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) * A $$ (x, ja) = 0" by auto
        qed
        have fa: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, a) = u" 
          unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr a_dr] using True i_not_a pquvd 
          by (auto, metis split_conv)
        have fb: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, b) = v"
          unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr b_dr] using True i_not_a pquvd ab
          by (auto, metis split_conv)
        have "sum ?f {a,b} + sum ?f ({0..<m+t} - {a,b}) = ?f a + ?f b" using sum0 by (simp add: ab)
        also have "... = u * A $$ (a, ja) + v * A $$ (b, ja)" unfolding fa fb by simp
        also have "... = ?A $$ (i,ja)" using A True i_not_a dr i ja by auto
        finally show ?thesis using BM_A_ija_eq by simp
      next
        case False note i_not_b = False
        have sum0: "sum ?f ({0..<m+t} - {a,b} - {i}) = 0" 
        proof (rule sum.neutral, rule)
          fix x assume x: "x \<in> {0..<m + t} - {a, b} - {i}"
          hence xm: "x < m+t" by auto
          have x_not_i: "x \<noteq> i" using x by blast
          have x_dr: "x < dim_row A" using x A by auto
          have "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) = 0"
            unfolding bezout_matrix_JNF_def 
            unfolding index_mat(1)[OF i_dr x_dr] using x_not_i x by auto
          thus "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, x) * A $$ (x, ja) = 0" by auto
        qed
        have fa: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, a) = 0" 
          unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr a_dr] using False i_not_a pquvd 
          by auto
        have fb: "bezout_matrix_JNF A a b j euclid_ext2 $$ (i, b) = 0" 
          unfolding bezout_matrix_JNF_def index_mat(1)[OF i_dr b_dr] using False i_not_a pquvd 
          by auto
        have "sum ?f ({0..<m+t} - {a,b}) = sum ?f (insert i ({0..<m+t} - {a,b} - {i}))"
          by (rule sum.cong, insert i_dr A i_not_a i_not_b, auto)
        also have "... = ?f i + sum ?f ({0..<m+t} - {a,b} - {i})" by (rule sum.insert, auto)
        also have "... = ?f i" using sum0 by simp
        also have "... = ?A $$ (i,ja)"
          unfolding bezout_matrix_JNF_def using i_not_a i_not_b  A dr i ja by fastforce
        finally show ?thesis unfolding BM_A_ija_eq by (simp add: ab fa fb)
      qed    
    qed
  qed
qed



lemma bezout_matrix_JNF_mult_eq2:
  assumes A: "A \<in> carrier_mat m n" and a: "a<m"  and b: "b<m" and ab: "a \<noteq> b" 
  assumes pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,j)) (A$$(b,j))"
  shows "Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then (p*A$$(a,k) + q*A$$(b,k))
                   else if i = b then u * A$$(a,k) + v * A$$(b,k)
                   else A$$(i,k)
            ) = (bezout_matrix_JNF A a b j euclid_ext2) * A" (is "?A = ?BM * A")
proof (rule bezout_matrix_JNF_mult_eq'[OF A a b ab _ _ pquvd])
  show "A = A @\<^sub>r (0\<^sub>m 0 n)" by (rule eq_matI, unfold append_rows_def, auto)
  show "(0\<^sub>m 0 n) \<in> carrier_mat 0 n" by auto
qed


lemma reduce_invertible_mat_D0_BM:
  assumes A: "A \<in> carrier_mat m n"
  and a: "a < m"
  and b: "b < m"
  and ab: "a \<noteq> b"
  and Aa0: "A$$(a,0) \<noteq> 0"
  shows "reduce a b 0 A = (bezout_matrix_JNF A a b 0 euclid_ext2) * A"
proof -
 obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(b,0))"
    by (simp add: euclid_ext2_def)
  let ?BM = "bezout_matrix_JNF A a b 0 euclid_ext2"
  let ?A = "Matrix.mat (dim_row A) (dim_col A)
          (\<lambda>(i,k). if i = a then  (p*A$$(a,k) + q*A$$(b,k))
                   else if i = b then  u * A$$(a,k) + v * A$$(b,k)
                   else A$$(i,k))"
  have A'_BZ_A: "?A = ?BM * A"
    by (rule bezout_matrix_JNF_mult_eq2[OF A _ _ ab pquvd], insert a b, auto)  
  moreover have "?A = reduce a b 0 A" using pquvd Aa0 unfolding reduce_D0 Let_def
    by (metis (no_types, lifting) split_conv)
  ultimately show ?thesis by simp
qed


lemma reduce_invertible_mat_D0:
  assumes A: "A \<in> carrier_mat m n"
  and a: "a < m"
  and b: "b < m"
  and n0: "0<n"
  and ab: "a \<noteq> b"
  and a_less_b: "a<b"
  shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> reduce a b 0 A = P * A"
proof (cases "A$$(a,0) = 0")
  case True
  then show ?thesis
    by (smt A invertible_mat_one left_mult_one_mat one_carrier_mat reduce.simps)
next
  case False
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(b,0))"
    by (simp add: euclid_ext2_def)
  let ?BM = "bezout_matrix_JNF A a b 0 euclid_ext2"
  have "reduce a b 0 A = ?BM * A"  by (rule reduce_invertible_mat_D0_BM[OF A a b ab False])
  moreover have invertible_bezout: "invertible_mat ?BM"
    by (rule invertible_bezout_matrix_JNF[OF A is_bezout_ext_euclid_ext2 a_less_b _ n0 False],
        insert a_less_b b, auto)      
  moreover have BM: "?BM \<in> carrier_mat m m" unfolding bezout_matrix_JNF_def using A by auto
  ultimately show ?thesis by blast
qed

lemma reduce_below_invertible_mat_D0:
  assumes A': "A \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
  and "D=0"
shows "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> reduce_below a xs D A = P * A)"
  using assms
proof (induct a xs D A arbitrary: A rule: reduce_below.induct)
  case (1 a D A)
  then show ?case
    by (auto, metis invertible_mat_one left_mult_one_mat one_carrier_mat)
next
  case (2 a x xs D A)
  note A = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note d = "2.prems"(4)
  note x_xs = "2.prems"(5)
  note D0 = "2.prems"(6)
  have xm: "x < m" using "2.prems" by auto
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat m n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have h: "(\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m
    \<and> reduce_below a xs D (reduce a x D A) = P * reduce a x D A)"
    by (rule "2.hyps"[OF _ a j _ _ ],insert  d x_xs  D0 reduce_ax, auto)   
  from this obtain P where inv_P: "invertible_mat P" and P: "P \<in> carrier_mat m m"
    and rb_Pr: "reduce_below a xs D (reduce a x D A) = P * reduce a x D A" by blast
  have *: "reduce_below a (x # xs) D A = reduce_below a xs D (reduce a x D A)" by simp
  have "\<exists>Q. invertible_mat Q \<and> Q \<in> carrier_mat m m \<and> (reduce a x D A) = Q * A"
    by (unfold D0, rule reduce_invertible_mat_D0[OF A a xm j], insert "2.prems", auto)
  from this obtain Q where inv_Q: "invertible_mat Q" and Q: "Q \<in> carrier_mat m m"
    and r_QA: "reduce a x D A = Q * A" by blast
  have "invertible_mat (P*Q)" using inv_P inv_Q P Q invertible_mult_JNF by blast
  moreover have "P * Q \<in> carrier_mat m m" using P Q by auto
  moreover have "reduce_below a (x # xs) D A = (P*Q) * A" 
    by (smt P Q * assoc_mult_mat carrier_matD(1) carrier_mat_triv index_mult_mat(2) 
        r_QA rb_Pr reduce_preserves_dimensions(1))
  ultimately show ?case by blast
qed


(*This lemma permits to get rid of one assumption in reduce_not0*)
lemma reduce_not0':
  assumes A: "A \<in> carrier_mat m n" and a: "a<m" and a_less_b: "a<b" and j: "0<n" and b: "b<m"
    and Aaj: "A $$ (a,0) \<noteq> 0"
  shows "reduce a b 0 A $$ (a, 0) \<noteq> 0" (is "?reduce_ab $$ (a,0) \<noteq> _")
proof -
  have "?reduce_ab $$ (a,0) = (let r = gcd (A $$ (a, 0)) (A $$ (b, 0)) in if 0 dvd r then 0 else r)" 
    by (rule reduce_gcd[OF A _ j Aaj], insert a, simp)
  also have "... \<noteq> 0" unfolding Let_def
    by (simp add: assms(6))
  finally show ?thesis .
qed


lemma reduce_below_preserves_D0:
  assumes A': "A \<in> carrier_mat m n" and a: "a<m" and j: "j<n"
    and Aaj: "A $$ (a,0) \<noteq> 0"
  assumes "i \<notin> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
    and "i\<noteq>a" and "i<m"
  and "D=0"
  shows "reduce_below a xs D A $$ (i,j) = A $$ (i,j)"
  using assms
proof (induct a xs D A arbitrary: A i rule: reduce_below.induct)
  case (1 a D A)
  then show ?case by auto
next
  case (2 a x xs D A)
  note A = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note Aaj = "2.prems"(4)
  note i_set_xxs = "2.prems"(5)
  note d = "2.prems"(6)
  note xxs_less_m = "2.prems"(7)
  note ia = "2.prems"(8)
  note im = "2.prems"(9)
  note D0 = "2.prems"(10)
  have xm: "x < m"  using "2.prems" by auto
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "(reduce a x D A)"
  have reduce_ax: "?reduce_ax \<in> carrier_mat m n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  have "reduce_below a (x # xs) D A $$ (i, j) = reduce_below a xs D (reduce a x D A) $$ (i, j)"
    by auto
  also have "... = reduce a x D A $$ (i, j)"
  proof (rule "2.hyps"[OF _ a j _ _ ])   
    show "i \<notin> set xs" using i_set_xxs by auto
    show "distinct xs" using d by auto
    show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
    show "reduce a x D A $$ (a, 0) \<noteq> 0"
      by (unfold D0, rule reduce_not0'[OF A _ _ _ _ Aaj], insert "2.prems", auto)
    show "reduce a x D A \<in> carrier_mat m n" using reduce_ax by linarith
  qed (insert "2.prems", auto)
  also have "... = A $$ (i,j)" by (rule reduce_preserves[OF A j Aaj], insert "2.prems", auto)
  finally show ?case .
qed



lemma reduce_below_0_D0:
  assumes A: "A \<in> carrier_mat m n" and a: "a<m" and j: "0<n"
    and Aaj: "A $$ (a,0) \<noteq> 0"
  assumes "i \<in> set xs" and "distinct xs" and "\<forall>x \<in> set xs. x < m \<and> a < x"
  and "D=0"
  shows "reduce_below a xs D A $$ (i,0) = 0"
  using assms
proof (induct a xs D A arbitrary: A i rule: reduce_below.induct)
  case (1 a D A)
  then show ?case by auto 
next
  case (2 a x xs D A)
  note A = "2.prems"(1)
  note a = "2.prems"(2)
  note j = "2.prems"(3)
  note Aaj = "2.prems"(4)
  note i_set_xxs = "2.prems"(5)
  note d = "2.prems"(6)
  note xxs_less_m = "2.prems"(7)
  note D0 = "2.prems"(8)
  have xm: "x < m"  using "2.prems" by auto
  obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 (A$$(a,0)) (A$$(x,0))"
    by (metis prod_cases5)
  let ?reduce_ax = "reduce a x D A"
  have reduce_ax: "?reduce_ax \<in> carrier_mat m n"
    by (metis (no_types, lifting) "2" add.comm_neutral append_rows_def 
        carrier_matD carrier_mat_triv index_mat_four_block(2,3)
        index_one_mat(2) index_smult_mat(2) index_zero_mat(2,3) reduce_preserves_dimensions)
  show ?case
  proof (cases "i=x")
    case True
    have "reduce_below a (x # xs) D A $$ (i, 0) = reduce_below a xs D (reduce a x D A) $$ (i, 0)"
      by auto
    also have "... = (reduce a x D A) $$ (i, 0)"
    proof (rule reduce_below_preserves_D0[OF _ a j _ _ ])
      show "reduce a x D A \<in> carrier_mat m n" using reduce_ax by linarith
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce a x D A $$ (a, 0) \<noteq> 0"
        by (unfold D0, rule reduce_not0'[OF A _ _ j _ Aaj], insert "2.prems", auto)
      show "i \<notin> set xs" using True d by auto
      show "i \<noteq> a" using "2.prems" by blast
      show "i < m" by (simp add: True trans_less_add1 xm)
    qed (insert D0)
    also have "... = 0" unfolding True by (rule reduce_0[OF A _ j _ _ Aaj], insert "2.prems", auto)
    finally show ?thesis .
  next
    case False note i_not_x = False    
    have h: "reduce_below a xs D (reduce a x D A) $$ (i, 0) = 0 "
    proof (rule "2.hyps"[OF _ a j _ _ ])
      show "reduce a x D A \<in> carrier_mat m n" using reduce_ax by linarith
      show "i \<in> set xs" using i_set_xxs i_not_x by auto
      show "distinct xs" using d by auto
      show "\<forall>x\<in>set xs. x < m \<and> a < x" using xxs_less_m by auto
      show "reduce a x D A $$ (a, 0) \<noteq> 0"
        by (unfold D0, rule reduce_not0'[OF A _ _ j _ Aaj], insert "2.prems", auto)
    qed (insert D0)
    have "reduce_below a (x # xs) D A $$ (i, 0) = reduce_below a xs D (reduce a x D A) $$ (i, 0)"
      by auto
    also have "... = 0" using h .
    finally show ?thesis .
  qed
qed

end

text \<open>Definition of the echelon form algorithm in JNF\<close>

primrec bezout_iterate_JNF
where "bezout_iterate_JNF A 0 i j bezout = A"
    | "bezout_iterate_JNF A (Suc n) i j bezout = 
        (if (Suc n) \<le> i then A else 
              bezout_iterate_JNF (bezout_matrix_JNF A i ((Suc n)) j bezout * A) n i j bezout)"

definition 
  "echelon_form_of_column_k_JNF bezout A' k = 
    (let (A, i) = A' 
     in if (i = dim_row A) \<or> (\<forall>m \<in> {i..<dim_row A}. A $$ (m, k) = 0) then (A, i) else 
        if (\<forall>m\<in>{i+1..<dim_row A}. A $$ (m,k) = 0) then (A, i + 1) else
            let n = (LEAST n. A $$ (n,k) \<noteq> 0 \<and> i \<le> n); 
                interchange_A = swaprows i n A
           in
            (bezout_iterate_JNF (interchange_A) (dim_row A - 1) i k bezout, i + 1) )"


definition "echelon_form_of_upt_k_JNF A k bezout = (fst (foldl (echelon_form_of_column_k_JNF bezout) (A,0) [0..<Suc k]))"
definition "echelon_form_of_JNF A bezout = echelon_form_of_upt_k_JNF A (dim_col A - 1) bezout"


context includes lifting_syntax
begin

lemma HMA_bezout_iterate[transfer_rule]: 
  assumes "n<CARD('m)"
  shows "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> int ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) 
     ===> (Mod_Type_Connect.HMA_I) ===> (Mod_Type_Connect.HMA_I) ===> (=) ===> (Mod_Type_Connect.HMA_M)) 
  (\<lambda>A i j bezout. bezout_iterate_JNF A n i j bezout)  
  (\<lambda>A i j bezout. bezout_iterate A n i j bezout)
  "
proof (intro rel_funI, goal_cases)
  case (1 A A' i i' j j' bezout bezout')
  then show ?case using assms
  proof (induct n arbitrary: A A')
    case 0
    then show ?case by auto
  next
    case (Suc n)
    note AA'[transfer_rule] = "Suc.prems"(1)
    note ii'[transfer_rule] = "Suc.prems"(2)
    note jj'[transfer_rule] = "Suc.prems"(3)
    note bb'[transfer_rule] = "Suc.prems"(4)
    note Suc_n_less_m = "Suc.prems"(5)
    let ?BI_JNF = "bezout_iterate_JNF"
    let ?BI_HMA = "bezout_iterate"
    let ?from_nat_rows = "mod_type_class.from_nat :: _ \<Rightarrow> 'm"
    have Sucn[transfer_rule]: "Mod_Type_Connect.HMA_I (Suc n) (?from_nat_rows (Suc n))"
      unfolding Mod_Type_Connect.HMA_I_def
      by (simp add: Suc_lessD Suc_n_less_m mod_type_class.from_nat_to_nat)
    have n: " n < CARD('m)" using Suc_n_less_m by simp
    have [transfer_rule]: 
      "Mod_Type_Connect.HMA_M (?BI_JNF (bezout_matrix_JNF A i (Suc n) j bezout * A) n i j bezout)
     (?BI_HMA (bezout_matrix A' i' (?from_nat_rows (Suc n)) j' bezout' ** A') n i' j' bezout')"    
      by (rule Suc.hyps[OF _ ii' jj' bb' n], transfer_prover)
    moreover have "Suc n \<le> i \<Longrightarrow>  Suc n \<le> mod_type_class.to_nat i'"
      and "Suc n > i \<Longrightarrow> Suc n > mod_type_class.to_nat i'" 
      by (metis "1"(2) Mod_Type_Connect.HMA_I_def)+
    ultimately show ?case using AA' by auto
  qed
qed


corollary HMA_bezout_iterate'[transfer_rule]: 
  fixes A'::"int ^ 'n :: mod_type ^ 'm :: mod_type"
  assumes n: "n<CARD('m)"
  and "Mod_Type_Connect.HMA_M A A'"
   and "Mod_Type_Connect.HMA_I i i'" and "Mod_Type_Connect.HMA_I j j'" 
 shows "Mod_Type_Connect.HMA_M (bezout_iterate_JNF A n i j bezout) (bezout_iterate A' n i' j' bezout)"
  using assms HMA_bezout_iterate[OF n] unfolding rel_fun_def by force



lemma snd_echelon_form_of_column_k_JNF_le_dim_row:
  assumes "i<dim_row A"
  shows "snd (echelon_form_of_column_k_JNF bezout (A,i) k ) \<le> dim_row A"   
  using assms unfolding echelon_form_of_column_k_JNF_def by auto



lemma HMA_echelon_form_of_column_k[transfer_rule]: 
  assumes k: "k<CARD('n)"
  shows "((=) ===> rel_prod (Mod_Type_Connect.HMA_M :: _ \<Rightarrow> int ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) (\<lambda>a b. a=b \<and> a\<le>CARD('m))
    ===> (rel_prod (Mod_Type_Connect.HMA_M) (\<lambda>a b. a=b \<and> a\<le>CARD('m)))) 
  (\<lambda>bezout A. echelon_form_of_column_k_JNF bezout A k)  
  (\<lambda>bezout A. echelon_form_of_column_k bezout A k)
  "
proof (intro rel_funI, goal_cases)
  case (1 bezout bezout' xa ya )
  obtain A i where xa: "xa = (A,i)" using surjective_pairing by blast
  obtain A' i' where ya: "ya = (A',i')" using surjective_pairing by blast
  have ii'[transfer_rule]: "i=i'" using "1"(2) xa ya by auto
  have i_le_m: "i\<le>CARD('m)"  using "1"(2) xa ya by auto
  have AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'" using "1"(2) xa ya by auto
  have bb'[transfer_rule]: "bezout=bezout'" using "1" by auto
  let ?from_nat_rows = "mod_type_class.from_nat :: _ \<Rightarrow> 'm"
  let ?from_nat_cols = "mod_type_class.from_nat :: _ \<Rightarrow> 'n"
  have kk'[transfer_rule]: "Mod_Type_Connect.HMA_I k (?from_nat_cols k)"
    by (simp add: Mod_Type_Connect.HMA_I_def assms mod_type_class.to_nat_from_nat_id)
  have c1_eq: "(i = dim_row A) = (i = nrows A')"
    by (metis AA' Mod_Type_Connect.dim_row_transfer_rule nrows_def)
  have c2_eq: "(\<forall>m \<in> {i..<dim_row A}. A $$ (m, k) = 0) 
      = (\<forall>m\<ge>?from_nat_rows i. A' $ m $ ?from_nat_cols k = 0)" (is "?lhs = ?rhs") if i_not: "i\<noteq>dim_row A" 
  proof 
    assume lhs: "?lhs"
    show "?rhs"
    proof (rule+)    
      fix m 
      assume im: "?from_nat_rows i \<le> m"
      have im': "i<CARD('m)" using i_le_m i_not
        by (simp add: c1_eq dual_order.order_iff_strict nrows_def)
      let ?m' = "mod_type_class.to_nat m"
      have mm'[transfer_rule]: "Mod_Type_Connect.HMA_I ?m' m" 
        by (simp add: Mod_Type_Connect.HMA_I_def)
      from im have "mod_type_class.to_nat (?from_nat_rows i) \<le> ?m'"
        by (simp add: to_nat_mono')
      hence "?m' >= i" using im im' by (simp add: mod_type_class.to_nat_from_nat_id)
      hence "?m' \<in> {i..<dim_row A}"
        using AA' Mod_Type_Connect.dim_row_transfer_rule mod_type_class.to_nat_less_card by fastforce
      hence "A $$ (?m', k) = 0" using lhs by auto
      moreover have "A $$ (?m', k) = A' $h m $h ?from_nat_cols k" unfolding index_hma_def[symmetric] by transfer_prover
      ultimately show "A' $h m $h ?from_nat_cols k = 0" by simp
    qed
  next
    assume rhs: "?rhs"
    show "?lhs"
    proof (rule)
      fix m assume m: "m \<in> {i..<dim_row A}"
      let ?m = "?from_nat_rows m"
      have mm'[transfer_rule]: "Mod_Type_Connect.HMA_I m ?m" 
        by (metis AA' Mod_Type_Connect.HMA_I_def Mod_Type_Connect.dim_row_transfer_rule
            atLeastLessThan_iff m mod_type_class.from_nat_to_nat)
      have m_ge_i: "?m\<ge>?from_nat_rows i"
        using AA' Mod_Type_Connect.dim_row_transfer_rule from_nat_mono' m by fastforce
      hence "A' $h ?m $h ?from_nat_cols k = 0" using rhs by auto
      moreover have "A $$ (m, k) = A' $h ?m $h ?from_nat_cols k"
        unfolding index_hma_def[symmetric] by transfer_prover
      ultimately show "A $$ (m, k) = 0" by simp
    qed
  qed
  show ?case 
  proof (cases "(i = dim_row A) \<or> (\<forall>m \<in> {i..<dim_row A}. A $$ (m, k) = 0)")
    case True   
    hence *: "(\<forall>m\<ge>?from_nat_rows i. A' $ m $ ?from_nat_cols k = 0) \<or> (i = nrows A')"
      using c1_eq c2_eq by auto
    have "echelon_form_of_column_k_JNF bezout xa k = (A,i)" 
      unfolding echelon_form_of_column_k_JNF_def using True xa by auto
    moreover have "echelon_form_of_column_k bezout ya k = (A',i')"
      unfolding echelon_form_of_column_k_def Let_def using * ya ii' by simp
    ultimately show ?thesis unfolding xa ya rel_prod.simps using AA' ii' bb' i_le_m by blast    
  next
    case False note not_c1 = False
    hence im': "i<CARD('m)"
      by (metis c1_eq dual_order.order_iff_strict i_le_m nrows_def)
    have *: "(\<forall>m\<in>{i+1..<dim_row A}. A $$ (m,k) = 0) 
      = (\<forall>m>?from_nat_rows i. A' $ m $ ?from_nat_cols k = 0)" (is "?lhs = ?rhs")
    proof 
      assume lhs: "?lhs"
      show "?rhs"
      proof (rule+)    
        fix m 
        assume im: "?from_nat_rows i < m"     
        let ?m' = "mod_type_class.to_nat m"
        have mm'[transfer_rule]: "Mod_Type_Connect.HMA_I ?m' m" 
          by (simp add: Mod_Type_Connect.HMA_I_def)
        from im have "mod_type_class.to_nat (?from_nat_rows i) < ?m'"
          by (simp add: to_nat_mono)
        hence "?m' > i" using im im' by (simp add: mod_type_class.to_nat_from_nat_id)
        hence "?m' \<in> {i+1..<dim_row A}"
          using AA' Mod_Type_Connect.dim_row_transfer_rule mod_type_class.to_nat_less_card by fastforce
        hence "A $$ (?m', k) = 0" using lhs by auto
        moreover have "A $$ (?m', k) = A' $h m $h ?from_nat_cols k" unfolding index_hma_def[symmetric] by transfer_prover
        ultimately show "A' $h m $h ?from_nat_cols k = 0" by simp
      qed
    next
      assume rhs: "?rhs"
      show "?lhs"
      proof (rule)
        fix m assume m: "m \<in> {i+1..<dim_row A}"
        let ?m = "?from_nat_rows m"
        have mm'[transfer_rule]: "Mod_Type_Connect.HMA_I m ?m" 
          by (metis AA' Mod_Type_Connect.HMA_I_def Mod_Type_Connect.dim_row_transfer_rule
              atLeastLessThan_iff m mod_type_class.from_nat_to_nat)
        have m_ge_i: "?m>?from_nat_rows i"
          by (metis Mod_Type_Connect.HMA_I_def One_nat_def add_Suc_right atLeastLessThan_iff from_nat_mono
              le_simps(3) m mm' mod_type_class.to_nat_less_card nat_arith.rule0)
        hence "A' $h ?m $h ?from_nat_cols k = 0" using rhs by auto
        moreover have "A $$ (m, k) = A' $h ?m $h ?from_nat_cols k"
          unfolding index_hma_def[symmetric] by transfer_prover
        ultimately show "A $$ (m, k) = 0" by simp
      qed
    qed
    show ?thesis
    proof (cases "(\<forall>m\<in>{i+1..<dim_row A}. A $$ (m,k) = 0)")
      case True
      have "echelon_form_of_column_k_JNF bezout xa k = (A,i+1)" 
        unfolding echelon_form_of_column_k_JNF_def using True xa not_c1 by auto
      moreover have "echelon_form_of_column_k bezout ya k = (A',i'+1)"
        unfolding echelon_form_of_column_k_def Let_def using ya ii' * True c1_eq c2_eq not_c1 by auto
      ultimately show ?thesis unfolding xa ya rel_prod.simps using AA' ii' bb' i_le_m
        by (metis Mod_Type_Connect.dim_row_transfer_rule le_neq_implies_less le_simps(3) not_c1 semiring_norm(175))      
    next
      case False
      hence *: "\<not> (\<forall>m>?from_nat_rows i. A' $ m $ ?from_nat_cols k = 0)" using * by auto
      have **: "\<not> ((\<forall>m\<ge>?from_nat_rows i. A' $h m $h ?from_nat_cols k = 0) \<or> i = nrows A')"
        using c1_eq c2_eq not_c1 by auto
      define n where "n=(LEAST n. A $$ (n,k) \<noteq> 0 \<and> i \<le> n)"
      define n' where "n'=(LEAST n. A' $ n $ ?from_nat_cols k \<noteq> 0 \<and> ?from_nat_rows i \<le> n)"
      let ?interchange_A = "swaprows i n A"
      let ?interchange_A' = "interchange_rows A' (?from_nat_rows i') n'"      
      have nn'[transfer_rule]: "Mod_Type_Connect.HMA_I n n'"
      proof -
        let ?n' = "mod_type_class.to_nat n'"
        have exist: "\<exists>n. A' $ n $ ?from_nat_cols k \<noteq> 0 \<and> ?from_nat_rows i \<le> n"
          using * by auto
        from this obtain a where c: "A' $ a $ ?from_nat_cols k \<noteq> 0 \<and> ?from_nat_rows i \<le> a" by blast        
        have "n = ?n'"
        proof (unfold n_def, rule Least_equality)
          have n'n'[transfer_rule]: "Mod_Type_Connect.HMA_I ?n' n'"
            by (simp add: Mod_Type_Connect.HMA_I_def)
          have e: "(A' $ n' $ ?from_nat_cols k \<noteq> 0 \<and> ?from_nat_rows i \<le> n')"
            by (metis (mono_tags, lifting) LeastI c2_eq n'_def not_c1) 
          hence  "i \<le> mod_type_class.to_nat n'" 
            using im' mod_type_class.from_nat_to_nat to_nat_mono' by fastforce       
          moreover have "A' $ n' $ ?from_nat_cols k = A $$ (?n', k)" 
            unfolding index_hma_def[symmetric] by (transfer', auto)
          ultimately show "A $$ (?n', k) \<noteq> 0 \<and> i \<le> ?n'"
            using e by auto
          show " \<And>y. A $$ (y, k) \<noteq> 0 \<and> i \<le> y \<Longrightarrow> mod_type_class.to_nat n' \<le> y"
            by (smt AA' Mod_Type_Connect.HMA_M_def Mod_Type_Connect.from_hma\<^sub>m_def assms from_nat_mono
                from_nat_mono' index_mat(1) linorder_not_less mod_type_class.from_nat_to_nat_id
                mod_type_class.to_nat_less_card n'_def order.strict_trans prod.simps(2) wellorder_Least_lemma(2))
        qed
        thus ?thesis unfolding Mod_Type_Connect.HMA_I_def by auto
      qed
      have dr1[transfer_rule]: "(nrows A' - 1) = (dim_row A - 1)" unfolding nrows_def
        using AA' Mod_Type_Connect.dim_row_transfer_rule by force
      have ii'2[transfer_rule]: "Mod_Type_Connect.HMA_I i (?from_nat_rows i')"
        by (metis "**" Mod_Type_Connect.HMA_I_def i_le_m ii' le_neq_implies_less
            mod_type_class.to_nat_from_nat_id nrows_def)
      have ii'3[transfer_rule]: "Mod_Type_Connect.HMA_I i' (?from_nat_rows i')" 
        using ii' ii'2 by blast
      let ?BI_JNF = "(bezout_iterate_JNF (?interchange_A) (dim_row A - 1) i k bezout)"
      let ?BI_HA = "(bezout_iterate (?interchange_A') (nrows A' - 1) (?from_nat_rows i) (?from_nat_cols k) bezout)"
      have e_rw: "echelon_form_of_column_k_JNF bezout xa k = (?BI_JNF,i+1)"
        unfolding echelon_form_of_column_k_JNF_def n_def using False xa not_c1 by auto
      have e_rw2: "echelon_form_of_column_k bezout ya k = (?BI_HA,i+1)"
        unfolding echelon_form_of_column_k_def Let_def n'_def using * ya ** ii' by auto
      have s[transfer_rule]: "Mod_Type_Connect.HMA_M (swaprows i' n A) (interchange_rows A' (?from_nat_rows i') n')" 
        by transfer_prover
      have n_CARD: "(nrows A' - 1) < CARD('m)" unfolding nrows_def by auto
      note a[transfer_rule] = HMA_bezout_iterate[OF n_CARD]
      have BI[transfer_rule]:"Mod_Type_Connect.HMA_M ?BI_JNF ?BI_HA" unfolding ii' dr1 
        by (rule HMA_bezout_iterate'[OF _ s ii'3 kk'], insert n_CARD, transfer', simp)
      thus ?thesis using e_rw e_rw2 bb'
        by (metis (mono_tags, lifting) AA' False Mod_Type_Connect.dim_row_transfer_rule 
            atLeastLessThan_iff dual_order.trans order_less_imp_le rel_prod_inject)
    qed
  qed
qed

corollary HMA_echelon_form_of_column_k'[transfer_rule]: 
  assumes k: "k<CARD('n)" and "i\<le>CARD('m)"
  and "(Mod_Type_Connect.HMA_M :: _ \<Rightarrow> int ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) A A'"
  shows "(rel_prod (Mod_Type_Connect.HMA_M) (\<lambda>a b. a=b \<and> a\<le>CARD('m))) 
  (echelon_form_of_column_k_JNF bezout (A,i) k)  
  (echelon_form_of_column_k bezout (A',i) k)"
  using assms HMA_echelon_form_of_column_k[OF k] unfolding rel_fun_def by force

lemma HMA_foldl_echelon_form_of_column_k:
  assumes k: "k\<le>CARD('n)"
  shows "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> int ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) ===> (=)
    ===> (rel_prod (Mod_Type_Connect.HMA_M) (\<lambda>a b. a=b \<and> a\<le>CARD('m)))) 
  (\<lambda>A bezout. (foldl (echelon_form_of_column_k_JNF bezout) (A,0) [0..<k]))  
  (\<lambda>A bezout. (foldl (echelon_form_of_column_k bezout) (A,0) [0..<k]))"
proof (intro rel_funI, goal_cases)
  case (1 A A' bezout bezout')
  then show ?case using assms
  proof (induct k arbitrary: A A' )
    case 0
    then show ?case by auto
  next
     case (Suc k)
    note AA'[transfer_rule] = "Suc.prems"(1)
    note bb'[transfer_rule] = "Suc.prems"(2)
    note Suc_k_less_m = "Suc.prems"(3)
    let ?foldl_JNF = "foldl (echelon_form_of_column_k_JNF bezout) (A,0)"
    let ?foldl_HA = "foldl (echelon_form_of_column_k bezout') (A',0)"
    have set_rw: "[0..<Suc k] = [0..<k] @ [k]" by auto
    have f_JNF: "?foldl_JNF [0..<Suc k] = echelon_form_of_column_k_JNF bezout (?foldl_JNF [0..<k]) k" 
      by auto
    have f_HA: "?foldl_HA [0..<Suc k] = echelon_form_of_column_k bezout' (?foldl_HA [0..<k]) k" 
      by auto
    have hyp[transfer_rule]: "rel_prod Mod_Type_Connect.HMA_M (\<lambda>a b. a=b \<and> a\<le>CARD('m)) (?foldl_JNF [0..<k]) (?foldl_HA [0..<k])"
      by (rule Suc.hyps[OF AA'], insert Suc.prems, auto)
    show ?case unfolding f_JNF unfolding f_HA bb' using HMA_echelon_form_of_column_k'
      by (smt "1"(2) Suc_k_less_m Suc_le_lessD hyp rel_prod.cases)
  qed
qed



lemma HMA_echelon_form_of_upt_k[transfer_rule]:
  assumes k: "k<CARD('n)"
  shows "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> int ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) ===> (=)
    ===> (Mod_Type_Connect.HMA_M)) 
  (\<lambda>A bezout. echelon_form_of_upt_k_JNF A k bezout)  
  (\<lambda>A bezout. echelon_form_of_upt_k A k bezout)
  "
proof (intro rel_funI, goal_cases)
  case (1 A A' bezout bezout')
  have k': "Suc k \<le> CARD('n)" using k by auto
  have rel_foldl: "(rel_prod (Mod_Type_Connect.HMA_M) (\<lambda>a b. a=b \<and> a\<le>CARD('m))) 
  (foldl (echelon_form_of_column_k_JNF bezout) (A,0) [0..<Suc k])  
  (foldl (echelon_form_of_column_k bezout) (A',0) [0..<Suc k])"
    using HMA_foldl_echelon_form_of_column_k[OF k'] by (smt "1"(1) rel_fun_def)
  then show ?case using assms unfolding echelon_form_of_upt_k_JNF_def echelon_form_of_upt_k_def    
    by (metis (no_types, lifting) "1"(2) prod.collapse rel_prod_inject)
qed
 

lemma HMA_echelon_form_of[transfer_rule]:
  shows "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> int ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) ===> (=)
    ===> (Mod_Type_Connect.HMA_M)) 
  (\<lambda>A bezout. echelon_form_of_JNF A bezout)  
  (\<lambda>A bezout. echelon_form_of A bezout)
  "
proof (intro rel_funI, goal_cases)
  case (1 A A' bezout bezout')
  note AA'[transfer_rule] = 1(1)
  note bb'[transfer_rule] = 1(2)
  have *: "(dim_col A - 1) < CARD('n)" using 1
    using Mod_Type_Connect.dim_col_transfer_rule by force
  note **[transfer_rule] = HMA_echelon_form_of_upt_k[OF *]
  have [transfer_rule]: "(ncols A' - 1) = (dim_col A - 1)"
    by (metis "1"(1) Mod_Type_Connect.dim_col_transfer_rule ncols_def)
  have [transfer_rule]: "(dim_col A - 1) = (dim_col A - 1)" ..
  show ?case unfolding echelon_form_of_def echelon_form_of_JNF_def bb'
    by (metis (mono_tags) "**" "1"(1) \<open>ncols A' - 1 = dim_col A - 1\<close> rel_fun_def)
qed
end


context
begin

private lemma echelon_form_of_euclidean_invertible_mod_type:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('m::mod_type) CARD('n::mod_type)"
  shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (CARD('m::mod_type)) (CARD('m::mod_type)) 
    \<and> P * A = echelon_form_of_JNF A euclid_ext2 
    \<and> echelon_form_JNF (echelon_form_of_JNF A euclid_ext2)"
proof -
  define A' where "A' = (Mod_Type_Connect.to_hma\<^sub>m A :: int ^'n :: mod_type ^'m :: mod_type)"
  have AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'"
    unfolding Mod_Type_Connect.HMA_M_def using assms A'_def by auto   
  have [transfer_rule]: "Mod_Type_Connect.HMA_M 
    (echelon_form_of_JNF A euclid_ext2) (echelon_form_of A' euclid_ext2)" 
    by transfer_prover  
  have "\<exists>P. invertible P \<and> P**A' = (echelon_form_of A' euclid_ext2) 
         \<and> echelon_form (echelon_form_of A' euclid_ext2)"
    by (rule echelon_form_of_euclidean_invertible)    
  thus ?thesis by (transfer, auto)
qed 


private lemma echelon_form_of_euclidean_invertible_nontriv_mod_ring:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('m::nontriv mod_ring) CARD('n::nontriv mod_ring)"
  shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat (CARD('m)) (CARD('m)) 
    \<and> P * A = echelon_form_of_JNF A euclid_ext2 
    \<and> echelon_form_JNF (echelon_form_of_JNF A euclid_ext2)"
  using assms echelon_form_of_euclidean_invertible_mod_type by (smt CARD_mod_ring)

(*We internalize both sort constraints in one step*)
lemmas echelon_form_of_euclidean_invertible_nontriv_mod_ring_internalized = 
  echelon_form_of_euclidean_invertible_nontriv_mod_ring[unfolded CARD_mod_ring, 
      internalize_sort "'m::nontriv", internalize_sort "'b::nontriv"]

context
  fixes m::nat and n::nat
  assumes local_typedef1: "\<exists>(Rep :: ('b \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<m :: int}"
  assumes local_typedef2: "\<exists>(Rep :: ('c \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<n :: int}"
  and m: "m>1"
  and n: "n>1"
begin

lemma echelon_form_of_euclidean_invertible_nontriv_mod_ring_aux:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat m n"
  shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m
    \<and> P * A = echelon_form_of_JNF A euclid_ext2 
    \<and> echelon_form_JNF (echelon_form_of_JNF A euclid_ext2)"
 using echelon_form_of_euclidean_invertible_nontriv_mod_ring_internalized
    [OF type_to_set2(1)[OF local_typedef1 local_typedef2] 
        type_to_set1(1)[OF local_typedef1 local_typedef2]]
  using assms 
  using type_to_set1(2) local_typedef1 local_typedef2 n m by metis 

end


(*Canceling the first local type definitions*)
context
begin

(*Canceling the first*)

private lemma echelon_form_of_euclidean_invertible_cancelled_first:
"\<exists>Rep Abs. type_definition Rep Abs {0..<int n} \<Longrightarrow> 1 < m \<Longrightarrow> 1 < n \<Longrightarrow>
  A \<in> carrier_mat m n \<Longrightarrow> \<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m
  \<and> P * (A::int mat) = echelon_form_of_JNF A euclid_ext2 \<and> echelon_form_JNF (echelon_form_of_JNF A euclid_ext2)"
  using echelon_form_of_euclidean_invertible_nontriv_mod_ring_aux[cancel_type_definition, of m n A]
  by force  

(*Canceling the second*)
private lemma echelon_form_of_euclidean_invertible_cancelled_both:
"1 < m \<Longrightarrow> 1 < n \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow> \<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m 
  \<and> P * (A::int mat) = echelon_form_of_JNF A euclid_ext2 \<and> echelon_form_JNF (echelon_form_of_JNF A euclid_ext2)"
  using echelon_form_of_euclidean_invertible_cancelled_first[cancel_type_definition, of n m A]
  by force

(*The final result in JNF*)

lemma echelon_form_of_euclidean_invertible':
 fixes A::"int mat"
  assumes "A \<in> carrier_mat m n" 
  and "1 < m" and "1 < n" (*Required from the mod_type restrictions*)
  shows "\<exists>P. invertible_mat P \<and>
        P \<in> carrier_mat m m \<and> P * A = echelon_form_of_JNF A euclid_ext2 
        \<and> echelon_form_JNF (echelon_form_of_JNF A euclid_ext2)"  
  using echelon_form_of_euclidean_invertible_cancelled_both assms by auto
end
end

context mod_operation
begin

definition "FindPreHNF_rectangular A 
  =   (let m = dim_row A; n = dim_col A in 
  if m < 2 \<or> n = 0 then A else \<comment> \<open> No operations are carried out if m = 1 \<close>
  if n = 1 then 
        let non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A] in
        if non_zero_positions = [] then A
        else let A' = (if A$$(0,0) \<noteq> 0 then A else let i = non_zero_positions ! 0 in swaprows 0 i A)
            in reduce_below_impl 0 non_zero_positions 0 A'
  else (echelon_form_of_JNF A euclid_ext2))"

text \<open>This is the (non-efficient) HNF algorithm obtained from the echelon form and Hermite normal 
form AFP entries\<close>

definition "HNF_algorithm_from_HA A 
            = Hermite_of_list_of_rows (FindPreHNF_rectangular A) [0..<(dim_row A)]"

(*
  Now we can combine FindPreHNF_rectangular, FindPreHNF and Hermite_of_list_of_rows to get
  an algorithm to compute the HNF of any matrix (if it is square and invertible, then the HNF is
  computed reducing entries modulo D)
*)

text \<open>Now we can combine @{text"FindPreHNF_rectangular"}, @{text"FindPreHNF"}
  and @{text"Hermite_of_list_of_rows"} to get an algorithm to compute the HNF of any matrix
  (if it is square and invertible, then the HNF is computed reducing entries modulo D)\<close>

definition "HNF_algorithm abs_flag A = 
  (let m = dim_row A; n = dim_col A in
  if m \<noteq> n then Hermite_of_list_of_rows (FindPreHNF_rectangular A) [0..<m]
  else
    let D = abs (det_int A) in
    if D = 0 then Hermite_of_list_of_rows (FindPreHNF_rectangular A) [0..<m]
    else 
      let A' = A @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n;
          E = FindPreHNF abs_flag D A';
          H = Hermite_of_list_of_rows E [0..<m+n]
      in mat_of_rows n (map (Matrix.row H) [0..<m]))"

end

declare mod_operation.FindPreHNF_rectangular_def[code]
declare mod_operation.HNF_algorithm_from_HA_def[code]
declare mod_operation.HNF_algorithm_def[code]

context proper_mod_operation
begin

(*With some work, we could get this lemma for matrices whose elements belong to a Bézout domain*)
lemma FindPreHNF_rectangular_soundness:
  fixes A::"int mat"
  assumes A: "A \<in> carrier_mat m n" 
  shows "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> P * A = FindPreHNF_rectangular A 
    \<and> echelon_form_JNF (FindPreHNF_rectangular A)"  
proof (cases "m < 2 \<or> n = 0")
  case True
  then show ?thesis
    by (smt A FindPreHNF_rectangular_def carrier_matD echelon_form_JNF_1xn echelon_form_mx0
        invertible_mat_one left_mult_one_mat one_carrier_mat)
next
  case False 
  have m1: "m>1" using False by auto
  have n0: "n>0" using False by auto
  show ?thesis
  proof (cases "n=1")
    case True note n1 = True
    let ?nz = "filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A]" 
    let ?A' = "(if A$$(0,0) \<noteq> 0 then A else let i = ?nz ! 0 in swaprows 0 i A)"
    have A': "?A' \<in> carrier_mat m n" using A by auto
    have A'00: "?A' $$ (0,0) \<noteq> 0" if "?nz \<noteq> []" 
      by (smt True assms carrier_matD index_mat_swaprows(1) length_greater_0_conv m1
          mem_Collect_eq nat_SN.gt_trans nth_mem set_filter that zero_less_one_class.zero_less_one)
    have e_r: "echelon_form_JNF (reduce_below 0 ?nz 0 ?A')" if nz_not_empty: "?nz \<noteq> []" 
    proof (rule echelon_form_JNF_mx1)
      show "(reduce_below 0 ?nz 0 ?A') \<in> carrier_mat m n"  using A reduce_below by auto
      have "(reduce_below 0 ?nz 0 ?A') $$ (i,0) = 0" if i: "i \<in> {1..<m}" for i
      proof (cases "i \<in> set ?nz")
        case True
        show ?thesis
          by (rule reduce_below_0_D0[OF A' _ _ A'00 True], insert m1 n0 True A nz_not_empty, auto)
      next
        case False
        have "(reduce_below 0 ?nz 0 ?A') $$ (i,0) = ?A' $$ (i,0)" 
          by (rule reduce_below_preserves_D0[OF A' _ _ A'00 False], insert m1 n0 True A i nz_not_empty, auto)
        also have "... = 0" using False n1 assms that by auto
        finally show ?thesis .
      qed
      thus "\<forall>i \<in> {1..<m}. (reduce_below 0 ?nz 0 ?A') $$ (i,0) = 0"
        by simp
    qed (insert True, simp)
    have "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> reduce_below 0 ?nz 0 ?A' = P * ?A'" 
      by (rule reduce_below_invertible_mat_D0[OF A'], insert m1 n0 True A, auto)
    moreover have "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> ?A' = P * A"   if "?nz \<noteq> []"
      using A A'_swaprows_invertible_mat m1 that by blast 
    ultimately have e_inv: "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> reduce_below 0 ?nz 0 ?A' = P * A"
      if "?nz \<noteq> []"
      by (smt that A assoc_mult_mat invertible_mult_JNF mult_carrier_mat)
    have e_r1: "echelon_form_JNF A" if nz_empty: "?nz = []" 
    proof (rule echelon_form_JNF_mx1[OF A])
      show "\<forall>i\<in>{1..<m}. A $$ (i, 0) = 0 " using nz_empty
        by (metis (mono_tags, lifting) A carrier_matD(1) empty_filter_conv set_upt)
    qed (insert n1, simp)
    have e_inv1: "\<exists>P. invertible_mat P \<and> P \<in> carrier_mat m m \<and> A = P * A"
      by (metis A invertible_mat_one left_mult_one_mat one_carrier_mat)
    have "FindPreHNF_rectangular A = (if ?nz = [] then A else reduce_below_impl 0 ?nz 0 ?A')"
      unfolding FindPreHNF_rectangular_def Let_def using m1 n1 A True by auto
    also have "reduce_below_impl 0 ?nz 0 ?A' = reduce_below 0 ?nz 0 ?A'"
      by (rule reduce_below_impl[OF _ _ _ _ A'], insert m1 n0 A, auto)
    finally show ?thesis using e_inv e_r e_r1 e_inv1 by metis
  next
    case False
    have f_rw: "FindPreHNF_rectangular A = echelon_form_of_JNF A euclid_ext2"
      unfolding FindPreHNF_rectangular_def Let_def using m1 n0 A False by auto
    show ?thesis unfolding f_rw 
      by (rule echelon_form_of_euclidean_invertible'[OF A], insert False n0 m1, auto)
  qed
qed

lemma HNF_algorithm_from_HA_soundness:
  assumes A: "A \<in> carrier_mat m n"
  shows "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (HNF_algorithm_from_HA A)
    \<and> (\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> (HNF_algorithm_from_HA A) = P * A)"
proof -
  have m: "dim_row A = m" using A by auto
  have "(\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> (HNF_algorithm_from_HA A) = P * (FindPreHNF_rectangular A))"
    unfolding HNF_algorithm_from_HA_def m
  proof (rule invertible_Hermite_of_list_of_rows)
    show "FindPreHNF_rectangular A \<in> carrier_mat m n"
      by (smt A FindPreHNF_rectangular_soundness mult_carrier_mat)
    show "echelon_form_JNF (FindPreHNF_rectangular A)" 
      using FindPreHNF_rectangular_soundness by blast
  qed
  moreover have "(\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> (FindPreHNF_rectangular A) = P * A)"    
    by (metis A FindPreHNF_rectangular_soundness)
  ultimately have "(\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> (HNF_algorithm_from_HA A) = P * A)"
    by (smt assms assoc_mult_mat invertible_mult_JNF mult_carrier_mat)
  moreover have "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (HNF_algorithm_from_HA A)"
    by (metis A FindPreHNF_rectangular_soundness HNF_algorithm_from_HA_def m 
        Hermite_Hermite_of_list_of_rows mult_carrier_mat)
  ultimately show ?thesis by simp
qed


text \<open>Soundness theorem for any matrix\<close>
lemma HNF_algorithm_soundness:
  assumes A: "A \<in> carrier_mat m n"
  shows "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (HNF_algorithm abs_flag A)
    \<and> (\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> (HNF_algorithm abs_flag A) = P * A)"
proof (cases "m\<noteq>n \<or> Determinant.det A = 0")
  case True
  have H_rw: "HNF_algorithm abs_flag A = Hermite_of_list_of_rows (FindPreHNF_rectangular A) [0..<m]"
    using True A unfolding HNF_algorithm_def Let_def by auto
  have "(\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> (HNF_algorithm abs_flag A) = P * (FindPreHNF_rectangular A))"
    unfolding H_rw
  proof (rule invertible_Hermite_of_list_of_rows)
    show "FindPreHNF_rectangular A \<in> carrier_mat m n"
      by (smt A FindPreHNF_rectangular_soundness mult_carrier_mat)
    show "echelon_form_JNF (FindPreHNF_rectangular A)" 
      using FindPreHNF_rectangular_soundness by blast
  qed
  moreover have "(\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> (FindPreHNF_rectangular A) = P * A)"    
    by (metis A FindPreHNF_rectangular_soundness)
  ultimately have "(\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> (HNF_algorithm abs_flag A) = P * A)"
    by (smt assms assoc_mult_mat invertible_mult_JNF mult_carrier_mat)
  moreover have "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (HNF_algorithm abs_flag A)"
    by (metis A FindPreHNF_rectangular_soundness H_rw Hermite_Hermite_of_list_of_rows mult_carrier_mat)
  ultimately show ?thesis by simp
next
  case False
  hence mn: "m=n" and det_A_not0:"(Determinant.det A) \<noteq> 0" by auto
  have inv_RAT_A: "invertible_mat (map_mat rat_of_int A)"
  proof -
    have "det (map_mat rat_of_int A) \<noteq> 0" using det_A_not0 by auto
    thus ?thesis 
      by (metis False assms dvd_field_iff invertible_iff_is_unit_JNF map_carrier_mat)
  qed
  have "HNF_algorithm abs_flag A = Hermite_mod_det abs_flag A"
    unfolding HNF_algorithm_def Hermite_mod_det_def Let_def using False A by simp    
  then show ?thesis using Hermite_mod_det_soundness[OF mn A inv_RAT_A] by auto
qed
end


text \<open>New predicate of soundness of a HNF algorithm, without providing explicitly the transformation matrix.\<close>

definition "is_sound_HNF' algorithm associates res 
    = (\<forall>A. let H = algorithm A; m = dim_row A; n = dim_col A in Hermite_JNF associates res H 
        \<and> H \<in> carrier_mat m n \<and> (\<exists>P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> A = P * H))"

lemma is_sound_HNF_conv:
  assumes s: "is_sound_HNF' algorithm associates res"
  shows "is_sound_HNF (\<lambda>A. let H = algorithm A in (SOME P. P \<in> carrier_mat (dim_row A) (dim_row A)
    \<and> invertible_mat P \<and> A = P * H, H)) associates res"
proof (unfold is_sound_HNF_def Let_def prod.case, rule allI)
  fix A::"'a mat"
  define m where "m = dim_row A"
  obtain P where P: "P \<in> carrier_mat m m \<and> invertible_mat P \<and> A = P * (algorithm A)" 
    using s unfolding is_sound_HNF'_def Let_def m_def by auto
  let ?some_P = "(SOME P. P \<in> carrier_mat m m \<and> invertible_mat P \<and> A = P * algorithm A)"
  have some_P: "?some_P \<in> carrier_mat m m \<and> invertible_mat ?some_P \<and> A = ?some_P * algorithm A"
    by (smt P verit_sko_ex_indirect)
  moreover have "algorithm A \<in> carrier_mat (dim_row A) (dim_col A)"
    and  "Hermite_JNF associates res (algorithm A)" using s unfolding is_sound_HNF'_def Let_def by auto    
  ultimately show "?some_P \<in> carrier_mat m m \<and> algorithm A \<in> carrier_mat m (dim_col A) 
    \<and> invertible_mat ?some_P \<and> A = ?some_P * algorithm A \<and> Hermite_JNF associates res (algorithm A)"
    unfolding is_sound_HNF_def Let_def m_def by (auto split: prod.split)
qed

context proper_mod_operation
begin
corollary is_sound_HNF'_HNF_algorithm:
   "is_sound_HNF' (HNF_algorithm abs_flag) (range ass_function_euclidean) (\<lambda>c. range (res_int c))"  
proof -
  have "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (HNF_algorithm abs_flag A)" for A
    using HNF_algorithm_soundness by blast
  moreover have "HNF_algorithm abs_flag A \<in> carrier_mat (dim_row A) (dim_col A)" for A
    by (metis HNF_algorithm_soundness carrier_matI mult_carrier_mat)
  moreover have "\<exists>P. P \<in> carrier_mat (dim_row A) (dim_row A) \<and> invertible_mat P \<and> A = P * HNF_algorithm abs_flag A" for A 
  proof -
    have "\<exists>P. P \<in> carrier_mat (dim_row A) (dim_row A) \<and> invertible_mat P \<and> HNF_algorithm abs_flag A = P *  A"
      using HNF_algorithm_soundness by blast
    from this obtain P where P: "P \<in> carrier_mat (dim_row A) (dim_row A)" and inv_P: "invertible_mat P"
      and H_PA: "HNF_algorithm abs_flag A = P *  A" by blast
    obtain P' where PP': "inverts_mat P P'" and P'P: "inverts_mat P' P"
      using inv_P unfolding invertible_mat_def by auto
    have P': "P' \<in> carrier_mat (dim_row A) (dim_row A) "
      by (metis P PP' P'P carrier_matD carrier_mat_triv index_mult_mat(3) index_one_mat(3) inverts_mat_def)
    moreover have inv_P': "invertible_mat P'"
      by (metis P' P'P PP' carrier_matD(1) carrier_matD(2) invertible_mat_def square_mat.simps)
    moreover have "A = P' * HNF_algorithm abs_flag A"
      by (smt H_PA P P'P assoc_mult_mat calculation(1) carrier_matD(1) carrier_matI inverts_mat_def left_mult_one_mat')
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis
    unfolding is_sound_HNF'_def Let_def by auto
qed


corollary is_sound_HNF'_HNF_algorithm_from_HA:
   "is_sound_HNF' (HNF_algorithm_from_HA) (range ass_function_euclidean) (\<lambda>c. range (res_int c))"  
proof -
  have "Hermite_JNF (range ass_function_euclidean) (\<lambda>c. range (res_int c)) (HNF_algorithm_from_HA A)" for A
    using HNF_algorithm_from_HA_soundness by blast
  moreover have "HNF_algorithm_from_HA A \<in> carrier_mat (dim_row A) (dim_col A)" for A
    by (metis HNF_algorithm_from_HA_soundness carrier_matI mult_carrier_mat)
  moreover have "\<exists>P. P \<in> carrier_mat (dim_row A) (dim_row A) \<and> invertible_mat P \<and> A = P * HNF_algorithm_from_HA A" for A 
  proof -
    have "\<exists>P. P \<in> carrier_mat (dim_row A) (dim_row A) \<and> invertible_mat P \<and> HNF_algorithm_from_HA A = P *  A"
      using HNF_algorithm_from_HA_soundness by blast
    from this obtain P where P: "P \<in> carrier_mat (dim_row A) (dim_row A)" and inv_P: "invertible_mat P"
      and H_PA: "HNF_algorithm_from_HA A = P *  A" by blast
    obtain P' where PP': "inverts_mat P P'" and P'P: "inverts_mat P' P"
      using inv_P unfolding invertible_mat_def by auto
    have P': "P' \<in> carrier_mat (dim_row A) (dim_row A) "
      by (metis P PP' P'P carrier_matD carrier_mat_triv index_mult_mat(3) index_one_mat(3) inverts_mat_def)
    moreover have inv_P': "invertible_mat P'"
      by (metis P' P'P PP' carrier_matD(1) carrier_matD(2) invertible_mat_def square_mat.simps)
    moreover have "A = P' * HNF_algorithm_from_HA A"
      by (smt H_PA P P'P assoc_mult_mat calculation(1) carrier_matD(1) carrier_matI inverts_mat_def left_mult_one_mat')
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis
    unfolding is_sound_HNF'_def Let_def by auto
qed
end

text \<open>Some work to make the algorithm executable\<close>

definition find_non0' :: "nat \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1 mat \<Rightarrow> nat option" where
  "find_non0' i k A = (let is = [i ..< dim_row A];
    Ais = filter (\<lambda>j. A $$ (j, k) \<noteq> 0) is
    in case Ais of [] \<Rightarrow> None | _ \<Rightarrow> Some (Ais!0))"

lemma find_non0': 
  assumes A: "A \<in> carrier_mat m n"
  and res: "find_non0' i k A = Some j"
  shows "A $$ (j,k) \<noteq> 0" "i \<le> j" "j < dim_row A"
proof -
  let ?xs = "filter (\<lambda>j. A $$ (j,k) \<noteq> 0) [i ..< dim_row A]"
  from res[unfolded find_non0'_def Let_def]
  have xs: "?xs \<noteq> []" by (cases ?xs, auto)
  have j_in_xs: "j \<in> set ?xs" using res unfolding find_non0'_def Let_def
    by (metis (no_types, lifting) length_greater_0_conv list.case(2) list.exhaust nth_mem option.simps(1) xs)
  show "A $$ (j,k) \<noteq> 0" "i \<le> j" "j < dim_row A" using j_in_xs by auto+  
qed


lemma find_non0'_w_zero_before: 
  assumes A: "A \<in> carrier_mat m n"
  and res: "find_non0' i k A = Some j"
  shows "\<forall>j'\<in>{i..<j}. A $$ (j',k) = 0"
proof -
  let ?xs = "filter (\<lambda>j. A $$ (j, k) \<noteq> 0) [i ..< dim_row A]"
  from res[unfolded find_non0'_def Let_def]
  have xs: "?xs \<noteq> []" by (cases ?xs, auto)
  have j_in_xs: "j \<in> set ?xs" using res unfolding find_non0'_def Let_def
    by (metis (no_types, lifting) length_greater_0_conv list.case(2) list.exhaust nth_mem option.simps(1) xs)
  have j_xs0: "j = ?xs ! 0"
    by (smt res[unfolded find_non0'_def Let_def] list.case(2) list.exhaust option.inject xs)
  show "\<forall>j'\<in>{i..<j}. A $$ (j',k) = 0"
  proof (rule+, rule ccontr)
    fix j' assume j': "j' : {i..<j}" and Alj': "A $$ (j',k) \<noteq> 0"
    have j'j: "j'<j" using j' by auto
    have j'_in_xs: "j' \<in> set ?xs" 
      by (metis (mono_tags, lifting) A Alj' Set.member_filter atLeastLessThan_iff filter_set
          find_non0'(3) j' nat_SN.gt_trans res set_upt)
    have l_rw: "[i..<dim_row A] = [i ..<j] @[j..<dim_row A]"
      using assms(1) assms(2) find_non0'(3) j' upt_append 
      by (metis atLeastLessThan_iff le_trans linorder_not_le) 
    have xs_rw: "?xs = filter (\<lambda>j. A $$ (j,k) \<noteq> 0) ([i ..<j] @[j..<dim_row A])"
      using l_rw by auto
    hence "filter (\<lambda>j. A $$ (j,k) \<noteq> 0) [i ..<j] = []" using j_xs0 
      by (metis (no_types, lifting) Set.member_filter atLeastLessThan_iff filter_append filter_set
          length_greater_0_conv nth_append nth_mem order_less_irrefl set_upt)
    thus False using j_xs0 j' j_xs0 
      by (metis Set.member_filter filter_empty_conv filter_set j'_in_xs set_upt)
  qed
qed


lemma find_non0'_LEAST: 
  assumes A: "A \<in> carrier_mat m n"
  and res: "find_non0' i k A = Some j"
shows "j = (LEAST n. A $$ (n,k) \<noteq> 0 \<and> i\<le>n)"
proof (rule Least_equality[symmetric])
  show " A $$ (j, k) \<noteq> 0 \<and> i \<le> j" 
    using A res find_non0'[OF A] by auto
  show " \<And>y. A $$ (y, k) \<noteq> 0 \<and> i \<le> y \<Longrightarrow> j \<le> y"
    by (meson A res atLeastLessThan_iff find_non0'_w_zero_before linorder_not_le)
qed

lemma echelon_form_of_column_k_JNF_code[code]:
  "echelon_form_of_column_k_JNF bezout (A,i) k = 
    (if (i = dim_row A) \<or> (\<forall>m \<in> {i..<dim_row A}. A $$ (m, k) = 0) then (A, i) else 
        if (\<forall>m\<in>{i+1..<dim_row A}. A $$ (m,k) = 0) then (A, i + 1) else
            let n = the (find_non0' i k A); 
                interchange_A = swaprows i n A
           in
            (bezout_iterate_JNF (interchange_A) (dim_row A - 1) i k bezout, i + 1))"
proof (cases "\<not> ((i = dim_row A) \<or> (\<forall>m \<in> {i..<dim_row A}. A $$ (m, k) = 0)) 
            \<and> \<not> (\<forall>m\<in>{i+1..<dim_row A}. A $$ (m,k) = 0)")
  case True
  let ?n = "the (find_non0' i k A)"
  let ?interchange_A = "swaprows i ?n A"
  have f_rw: "(the (find_non0' i k A)) = (LEAST n. A $$ (n, k) \<noteq> 0 \<and> i \<le> n)"
  proof (rule find_non0'_LEAST)
    have "find_non0' i k A \<noteq> None" using True unfolding find_non0'_def Let_def
      by (auto split: list.split)
         (metis (mono_tags, lifting) atLeastLessThan_iff atLeastLessThan_upt empty_filter_conv)
    thus "find_non0' i k A = Some (the (find_non0' i k A))" by auto
  qed (auto)
  show ?thesis unfolding echelon_form_of_column_k_JNF_def Let_def f_rw using True by auto
next
  case False
  then show ?thesis unfolding echelon_form_of_column_k_JNF_def by auto
qed


subsection \<open>Instantiation of the HNF-algorithm with modulo-operation\<close>

text \<open>We currently use a Boolean flag to indicate whether standard-mod or symmetric modulo
  should be used.\<close>

lemma sym_mod: "proper_mod_operation sym_mod sym_div" 
  by (unfold_locales, auto simp: sym_mod_sym_div)

lemma standard_mod: "proper_mod_operation (mod) (div)" 
  by (unfold_locales, auto, intro HOL.nitpick_unfold(7))

definition HNF_algorithm :: "bool \<Rightarrow> int mat \<Rightarrow> int mat" where
  "HNF_algorithm use_sym_mod = (if use_sym_mod 
    then mod_operation.HNF_algorithm sym_mod False else mod_operation.HNF_algorithm (mod) True)" 

definition HNF_algorithm_from_HA :: "bool \<Rightarrow> int mat \<Rightarrow> int mat" where
  "HNF_algorithm_from_HA use_sym_mod = (if use_sym_mod 
    then mod_operation.HNF_algorithm_from_HA sym_mod else mod_operation.HNF_algorithm_from_HA (mod))"


corollary is_sound_HNF'_HNF_algorithm:
   "is_sound_HNF' (HNF_algorithm use_sym_mod) (range ass_function_euclidean) (\<lambda>c. range (res_int c))"  
  using proper_mod_operation.is_sound_HNF'_HNF_algorithm[OF sym_mod]
    proper_mod_operation.is_sound_HNF'_HNF_algorithm[OF standard_mod]
  unfolding HNF_algorithm_def by (cases use_sym_mod, auto)

corollary is_sound_HNF'_HNF_algorithm_from_HA:
   "is_sound_HNF' (HNF_algorithm_from_HA use_sym_mod) (range ass_function_euclidean) (\<lambda>c. range (res_int c))"  
  using proper_mod_operation.is_sound_HNF'_HNF_algorithm_from_HA[OF sym_mod]
    proper_mod_operation.is_sound_HNF'_HNF_algorithm_from_HA[OF standard_mod]
  unfolding HNF_algorithm_from_HA_def by (cases use_sym_mod, auto)


(*Examples:*)
(*Rectangular matrix (6x4)*)
value [code]"let A = mat_of_rows_list 4 (
  [[0,3,1,4],
   [7,1,0,0],
   [8,0,19,16],
   [2,0,0,3::int],
   [9,-3,2,5],
   [6,3,2,4]]) in
  show (HNF_algorithm True A)"

(*Rectangular matrix (4x6)*)

value [code]"let A = mat_of_rows_list 6 (
  [[0,3,1,4,8,7],
   [7,1,0,0,4,1],
   [8,0,19,16,33,5],
   [2,0,0,3::int,-5,8]]) in
  show (HNF_algorithm False A)"

(*Singular matrix*)
value [code]"let A = mat_of_rows_list 6 (
  [[0,3,1,4,8,7],
   [7,1,0,0,4,1],
   [8,0,19,16,33,5],
   [0,3,1,4,8,7],
   [2,0,0,3::int,-5,8],
   [2,4,6,8,10,12]]) in
  show (Determinant.det A, HNF_algorithm True A)"

(*Invertible matrix*)
value [code]"let A = mat_of_rows_list 6 (
  [[0,3,1,4,8,7],
   [7,1,0,0,4,1],
   [8,0,19,16,33,5],
   [5,6,1,2,8,7],
   [2,0,0,3::int,-5,8],
   [2,4,6,8,10,12]]) in
  show (Determinant.det A, HNF_algorithm True A)"

end