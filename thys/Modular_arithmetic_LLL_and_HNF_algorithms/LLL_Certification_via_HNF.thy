section \<open>LLL certification via Hermite normal forms\<close>

text \<open>In this file, we define the new certified approach and prove its soundness.\<close>

theory LLL_Certification_via_HNF
  imports 
   LLL_Basis_Reduction.LLL_Certification
   Jordan_Normal_Form.DL_Rank
   HNF_Mod_Det_Soundness
begin


context LLL_with_assms
begin

lemma m_le_n: "m\<le>n"
proof -
  have "gs.lin_indpt (set (RAT fs_init))"
    using cof_vec_space.lin_indpt_list_def lin_dep by blast
  moreover have "gs.dim = n"
    by (simp add: gs.dim_is_n)
  moreover have "card (set (RAT fs_init)) = m"
    using LLL_invD(2) LLL_inv_initial_state cof_vec_space.lin_indpt_list_def distinct_card lin_dep
    by blast
  ultimately show ?thesis using gs.li_le_dim 
    by (metis cof_vec_space.lin_indpt_list_def gs.fin_dim lin_dep)
qed

end

text \<open>This lemma is a generalization of the theorem named @{text "HNF_A_eq_HNF_PA"}, using
the new uniqueness statement of the HNF. We provide two versions, one
assuming the existence and the other one obtained from a sound algorithm.\<close>

lemma HNF_A_eq_HNF_PA'_exist:
  fixes A::"int mat"
  assumes A: "A \<in> carrier_mat n n" and inv_A: "invertible_mat (map_mat rat_of_int A)" 
    and inv_P: "invertible_mat P" and P: "P \<in> carrier_mat n n"
    and HNF_H1: "Hermite_JNF associates res H1"
    and H1: "H1 \<in> carrier_mat n n"
    and HNF_H2: "Hermite_JNF associates res H2"
    and H2: "H2 \<in> carrier_mat n n"
    and sound_HNF1: "\<exists>P1. P1 \<in> carrier_mat n n \<and> invertible_mat P1 \<and> (P * A) = P1 * H1"
    and sound_HNF2: "\<exists>P2. P2 \<in> carrier_mat n n \<and> invertible_mat P2 \<and> A = P2 * H2"
  shows "H1 = H2"
proof -
  obtain inv_P where P_inv_P: "inverts_mat P inv_P" and inv_P_P: "inverts_mat inv_P P"
    and inv_P: "inv_P \<in> carrier_mat n n"
    using P inv_P obtain_inverse_matrix by blast
  obtain P1 where P1: "P1 \<in> carrier_mat n n" and inv_P1: "invertible_mat P1" and P1_H1: "P* A = P1 * H1"
    using sound_HNF1 by auto
  obtain P2 where P2: "P2 \<in> carrier_mat n n" and inv_P2: "invertible_mat P2" and P2_H2: "A = P2 * H2"
    using sound_HNF2 by auto
  have invertible_inv_P: "invertible_mat inv_P"
      using P_inv_P inv_P inv_P_P invertible_mat_def square_mat.simps by blast
  have P_A_P1_H1: "P * A = P1 * H1" using P1_H1 P2_H2 unfolding is_sound_HNF_def Let_def
    by (metis (mono_tags, lifting) case_prod_conv)
  hence "A = inv_P * (P1 * H1)"
    by (smt A P inv_P_P inv_P assoc_mult_mat carrier_matD(1) inverts_mat_def left_mult_one_mat)
  hence A_inv_P_P1_H1: "A = (inv_P * P1) * H1" using P P1_H1 assoc_mult_mat inv_P H1 P1 by auto
  have invertible_inv_P_P1: "invertible_mat (inv_P * P1)"
    by (rule invertible_mult_JNF[OF inv_P P1 invertible_inv_P inv_P1])   
  show ?thesis
  proof (rule HNF_unique_generalized_JNF[OF A _ H1 P2 H2 A_inv_P_P1_H1 P2_H2 
        inv_A invertible_inv_P_P1 inv_P2 HNF_H1 HNF_H2])
    show "inv_P * P1 \<in> carrier_mat n n"
      by (metis carrier_matD(1) carrier_matI index_mult_mat(2) inv_P
          invertible_inv_P_P1 invertible_mat_def square_mat.simps)    
  qed
qed


corollary HNF_A_eq_HNF_PA':
  fixes A::"int mat"
  assumes A: "A \<in> carrier_mat n n" and inv_A: "invertible_mat (map_mat rat_of_int A)" 
    and inv_P: "invertible_mat P" and P: "P \<in> carrier_mat n n"
    and sound_HNF: "is_sound_HNF HNF associates res"
    and P1_H1: "(P1,H1) = HNF (P*A)"
    and P2_H2: "(P2,H2) = HNF A"
  shows "H1 = H2" 
proof -
  have H1: "H1 \<in> carrier_mat n n"
    by (smt P1_H1 A P carrier_matD index_mult_mat is_sound_HNF_def prod.sel(2) sound_HNF split_beta)
  have H2: "H2 \<in> carrier_mat n n"
    by (smt P2_H2 A carrier_matD index_mult_mat is_sound_HNF_def prod.sel(2) sound_HNF split_beta)
  have HNF_H1: "Hermite_JNF associates res H1" 
    by (smt P1_H1 is_sound_HNF_def prod.sel(2) sound_HNF split_beta)
  have HNF_H2: "Hermite_JNF associates res H2"
    by (smt P2_H2 is_sound_HNF_def prod.sel(2) sound_HNF split_beta)
  have sound_HNF1: "\<exists>P1. P1 \<in> carrier_mat n n \<and> invertible_mat P1 \<and> (P * A) = P1 * H1"
    using sound_HNF P1_H1 unfolding is_sound_HNF_def Let_def
    by (metis (mono_tags, lifting) P carrier_matD(1) index_mult_mat(2) old.prod.simps(2))
  have sound_HNF2: "\<exists>P2. P2 \<in> carrier_mat n n \<and> invertible_mat P2 \<and> A = P2 * H2"
    using sound_HNF P1_H1 unfolding is_sound_HNF_def Let_def
    by (metis (mono_tags, lifting) A P2_H2 carrier_matD(1) old.prod.simps(2))
  show ?thesis 
    by (rule HNF_A_eq_HNF_PA'_exist[OF A inv_A inv_P P HNF_H1 H1 HNF_H2 H2 sound_HNF1 sound_HNF2])
qed


context LLL_with_assms
begin


lemma certification_via_eq_HNF2_exist:
  assumes HNF_H1: "Hermite_JNF associates res H1"
    and H1: "H1 \<in> carrier_mat n n"
    and HNF_H2: "Hermite_JNF associates res H2"
    and H2: "H2 \<in> carrier_mat n n"
    and sound_HNF1: "\<exists>P1. P1 \<in> carrier_mat n n \<and> invertible_mat P1 \<and> (mat_of_rows n fs_init) = P1 * H1"
    and sound_HNF2: "\<exists>P2. P2 \<in> carrier_mat n n \<and> invertible_mat P2 \<and> (mat_of_rows n gs) = P2 * H2"
    and gs: "set gs \<subseteq> carrier_vec n" 
    and l: "lattice_of fs_init = lattice_of gs"
    and mn: "m = n" and len_gs: "length gs = n" (*For the moment, only for square matrices*)
  shows "H1 = H2"
proof -
  have "\<exists>P \<in> carrier_mat n n. invertible_mat P \<and> mat_of_rows n fs_init = P * mat_of_rows n gs"    
    by (rule eq_lattice_imp_mat_mult_invertible_rows[OF fs_init gs lin_dep len[unfolded mn] len_gs l])
  from this obtain P where P: "P \<in> carrier_mat n n" and inv_P: "invertible_mat P"
    and fs_P_gs: "mat_of_rows n fs_init = P * mat_of_rows n gs" by auto
   obtain P1 where P1: "P1 \<in> carrier_mat n n" and inv_P1: "invertible_mat P1" and P1_H1: "(mat_of_rows n fs_init) = P1 * H1"
    using sound_HNF1 by auto
  obtain P2 where P2: "P2 \<in> carrier_mat n n" and inv_P2: "invertible_mat P2" and P2_H2: "(mat_of_rows n gs) = P2 * H2"
    using sound_HNF2 by auto
  have P1_H1_2: "P * mat_of_rows n gs = P1 * H1"
    using P1_H1 fs_P_gs by auto
  have gs_carrier: "mat_of_rows n gs \<in> carrier_mat n n" by (simp add: len_gs carrier_matI)
  show ?thesis
  proof (rule HNF_A_eq_HNF_PA'_exist[OF gs_carrier _ inv_P P HNF_H1 H1 HNF_H2 H2 _ sound_HNF2])
    from inv_P obtain P' where PP': "inverts_mat P P'" and P'P: "inverts_mat P' P"
      using invertible_mat_def by blast
    let ?RAT = "of_int_hom.mat_hom :: int mat \<Rightarrow> rat mat"
    have det_RAT_fs_init: "det (?RAT (mat_of_rows n fs_init)) \<noteq> 0"
    proof (rule gs.lin_indpt_rows_imp_det_not_0)
      show "?RAT (mat_of_rows n fs_init) \<in> carrier_mat n n"
        using len map_carrier_mat mat_of_rows_carrier(1) mn by blast
      have rw: "Matrix.rows (?RAT (mat_of_rows n fs_init)) = RAT fs_init"
        by (metis cof_vec_space.lin_indpt_list_def fs_init lin_dep mat_of_rows_map rows_mat_of_rows)
      thus "gs.lin_indpt (set (Matrix.rows (?RAT (mat_of_rows n fs_init))))" 
        by (insert lin_dep, simp add: cof_vec_space.lin_indpt_list_def)
      show "distinct (Matrix.rows (?RAT (mat_of_rows n fs_init)))"
        using rw cof_vec_space.lin_indpt_list_def lin_dep by auto
    qed
    hence d: "det (?RAT (mat_of_rows n fs_init)) dvd 1" using dvd_field_iff by blast
    hence inv_RAT_fs_init: "invertible_mat (?RAT (mat_of_rows n fs_init))"
      using invertible_iff_is_unit_JNF by (metis mn len map_carrier_mat mat_of_rows_carrier(1))
    have "invertible_mat (?RAT P)"
      by (metis P dvd_field_iff inv_P invertible_iff_is_unit_JNF map_carrier_mat 
          not_is_unit_0 of_int_hom.hom_0 of_int_hom.hom_det)
    have "det (?RAT (mat_of_rows n fs_init)) = det (?RAT P) * det (?RAT (mat_of_rows n gs))"
      by (metis Determinant.det_mult P fs_P_gs gs_carrier of_int_hom.hom_det of_int_hom.hom_mult)
    hence "det (?RAT (mat_of_rows n gs)) \<noteq> 0" using d by auto 
    thus "invertible_mat (?RAT (mat_of_rows n gs))"
      by (meson dvd_field_iff gs_carrier invertible_iff_is_unit_JNF map_carrier_mat)
    show "\<exists>P1. P1 \<in> carrier_mat n n \<and> invertible_mat P1 \<and> P * mat_of_rows n gs = P1 * H1"
      using P1 P1_H1_2 inv_P1 by blast
  qed
qed

lemma certification_via_eq_HNF2:
  assumes sound_HNF: "is_sound_HNF HNF associates res"
    and P1_H1: "(P1,H1) = HNF (mat_of_rows n fs_init)"
    and P2_H2: "(P2,H2) = HNF (mat_of_rows n gs)"    
    and gs: "set gs \<subseteq> carrier_vec n" 
    and l: "lattice_of fs_init = lattice_of gs"
    and mn: "m = n" and len_gs: "length gs = n" (*For the moment, only for square matrices*)
  shows "H1 = H2"
proof -
  have "\<exists>P \<in> carrier_mat n n. invertible_mat P \<and> mat_of_rows n fs_init = P * mat_of_rows n gs"    
    by (rule eq_lattice_imp_mat_mult_invertible_rows[OF fs_init gs lin_dep len[unfolded mn] len_gs l])
  from this obtain P where P: "P \<in> carrier_mat n n" and inv_P: "invertible_mat P"
    and fs_P_gs: "mat_of_rows n fs_init = P * mat_of_rows n gs" by auto
  have P1_H1_2: "(P1,H1) = HNF (P * mat_of_rows n gs)" using fs_P_gs P1_H1 by auto  
  have gs_carrier: "mat_of_rows n gs \<in> carrier_mat n n" by (simp add: len_gs carrier_matI)
  show ?thesis
  proof (rule HNF_A_eq_HNF_PA'[OF gs_carrier _ inv_P P sound_HNF P1_H1_2 P2_H2])
    from inv_P obtain P' where PP': "inverts_mat P P'" and P'P: "inverts_mat P' P"
      using invertible_mat_def by blast
    let ?RAT = "of_int_hom.mat_hom :: int mat \<Rightarrow> rat mat"
    have det_RAT_fs_init: "det (?RAT (mat_of_rows n fs_init)) \<noteq> 0"
    proof (rule gs.lin_indpt_rows_imp_det_not_0)
      show "?RAT (mat_of_rows n fs_init) \<in> carrier_mat n n"
        using len map_carrier_mat mat_of_rows_carrier(1) mn by blast
      have rw: "Matrix.rows (?RAT (mat_of_rows n fs_init)) = RAT fs_init"
        by (metis cof_vec_space.lin_indpt_list_def fs_init lin_dep mat_of_rows_map rows_mat_of_rows)
      thus "gs.lin_indpt (set (Matrix.rows (?RAT (mat_of_rows n fs_init))))" 
        by (insert lin_dep, simp add: cof_vec_space.lin_indpt_list_def)
      show "distinct (Matrix.rows (?RAT (mat_of_rows n fs_init)))"
        using rw cof_vec_space.lin_indpt_list_def lin_dep by auto
    qed
    hence d: "det (?RAT (mat_of_rows n fs_init)) dvd 1" using dvd_field_iff by blast
    hence inv_RAT_fs_init: "invertible_mat (?RAT (mat_of_rows n fs_init))"
      using invertible_iff_is_unit_JNF by (metis mn len map_carrier_mat mat_of_rows_carrier(1))
    have "invertible_mat (?RAT P)"
      by (metis P dvd_field_iff inv_P invertible_iff_is_unit_JNF map_carrier_mat 
          not_is_unit_0 of_int_hom.hom_0 of_int_hom.hom_det)
    have "det (?RAT (mat_of_rows n fs_init)) = det (?RAT P) * det (?RAT (mat_of_rows n gs))"
      by (metis Determinant.det_mult P fs_P_gs gs_carrier of_int_hom.hom_det of_int_hom.hom_mult)
    hence "det (?RAT (mat_of_rows n gs)) \<noteq> 0" using d by auto 
    thus "invertible_mat (?RAT (mat_of_rows n gs))"
      by (meson dvd_field_iff gs_carrier invertible_iff_is_unit_JNF map_carrier_mat)
  qed
qed


corollary lattice_of_eq_via_HNF:
  assumes sound_HNF: "is_sound_HNF HNF associates res"
    and P1_H1: "(P1,H1) = HNF (mat_of_rows n fs_init)"
    and P2_H2: "(P2,H2) = HNF (mat_of_rows n gs)"    
    and gs: "set gs \<subseteq> carrier_vec n"     
    and mn: "m = n" and len_gs: "length gs = n"
  shows "(H1 = H2) \<longleftrightarrow> (lattice_of fs_init = lattice_of gs)"
  using certification_via_eq_HNF certification_via_eq_HNF2 assms by metis
end



context
begin

interpretation vec_module "TYPE(int)" n .

lemma lattice_of_eq_via_HNF_paper:
  fixes F G :: "int mat" and HNF :: "int mat \<Rightarrow> int mat"
  assumes sound_HNF': "is_sound_HNF' HNF \<A> \<R>" (* HNF is a sound algorithm *)  
    and inv_F_Q: "invertible_mat (map_mat rat_of_int F)" (* invertible over Q *)
    and FG: "{F,G} \<subseteq> carrier_mat n n"
  shows "(HNF F = HNF G) \<longleftrightarrow> (lattice_of (rows F) = lattice_of (rows G))"
proof -
  define HNF' 
    where "HNF' = (\<lambda>A. let H = HNF A 
    in (SOME P. P \<in> carrier_mat (dim_row A) (dim_row A) \<and> invertible_mat P \<and> A = P * H, H))"
  have sound_HNF': "is_sound_HNF HNF' \<A> \<R>" by (unfold HNF'_def, rule is_sound_HNF_conv[OF sound_HNF'])
  have F_eq: "F = mat_of_rows n (rows F)" and G_eq: "G = mat_of_rows n (rows G)"
    using FG by auto
  interpret L: LLL_with_assms n n "(rows F)" "4/3"
  proof 
    interpret gs: cof_vec_space n "TYPE(rat)" .
    thm gs.upper_triangular_imp_lin_indpt_rows
  let ?RAT ="map_mat rat_of_int"
    have m_rw: "(map (map_vec rat_of_int) (rows F)) = rows (?RAT F)"
      unfolding Matrix.rows_def by auto
    show "gs.lin_indpt_list (map (map_vec rat_of_int) (rows F))"
    proof -
      have det_RAT_F: "det (?RAT F) \<noteq> 0"         
        by (metis inv_F_Q carrier_mat_triv invertible_iff_is_unit_JNF 
            invertible_mat_def not_is_unit_0 square_mat.simps)
      have d_RAT_F: "distinct (rows (?RAT F))"
      proof (rule ccontr)
        assume "\<not> distinct (rows (?RAT F))" 
        from this obtain i j 
          where ij: "row (?RAT F) i = row (?RAT F) j"
            and i: "i<dim_row (?RAT F)" and j: "j<dim_row (?RAT F)" 
            and i_not_j: "i\<noteq>j"
          unfolding Matrix.rows_def distinct_conv_nth by auto
        have "det (?RAT F) = 0" using ij i j i_not_j
          by (metis Determinant.det_def Determinant.det_identical_rows carrier_mat_triv)
        thus False using inv_F_Q
          by (metis carrier_mat_triv invertible_iff_is_unit_JNF invertible_mat_def 
              not_is_unit_0 square_mat.simps)
      qed     
      moreover have "\<not> gs.lin_dep (set (rows (?RAT F)))"
        using gs.det_not_0_imp_lin_indpt_rows[OF _ det_RAT_F] using FG by auto
      ultimately show ?thesis
        unfolding gs.lin_indpt_list_def m_rw using FG unfolding Matrix.rows_def by auto      
    qed 
  qed (insert FG F_eq, auto)
  show ?thesis 
  proof (rule L.lattice_of_eq_via_HNF[OF sound_HNF'])
    show "(fst (HNF' F), HNF F) = HNF' (mat_of_rows n (rows F))" 
      unfolding HNF'_def Let_def using F_eq by auto
    show "(fst (HNF' G), HNF G) = HNF' (mat_of_rows n (rows G))" 
      unfolding HNF'_def Let_def using G_eq by auto
    show "length (rows G) = n " using FG by auto
    show "set (rows G) \<subseteq> carrier_vec n" using FG
      by (metis G_eq mat_of_rows_carrier(3) rows_carrier)
  qed (simp)
qed
end

text \<open>We define a new const similar to @{text "external_lll_solver"},
but now it only returns the reduced matrix.\<close>

consts external_lll_solver' :: "integer \<times> integer \<Rightarrow> integer list list \<Rightarrow> integer list list" 

hide_type (open) Finite_Cartesian_Product.vec


text \<open>The following definition is an adaptation of @{text "reduce_basis_external"}\<close>

definition reduce_basis_external' :: "(int mat \<Rightarrow> int mat) \<Rightarrow> rat \<Rightarrow> int vec list \<Rightarrow> int vec list" where
  "reduce_basis_external' HNF \<alpha> fs = (case fs of Nil \<Rightarrow> [] | Cons f _ \<Rightarrow> (let 
    rb = reduce_basis \<alpha>;
    fsi = map (map integer_of_int o list_of_vec) fs;
    n = dim_vec f;
    m = length fs;
    gsi = external_lll_solver' (map_prod integer_of_int integer_of_int (quotient_of \<alpha>)) fsi;
    gs = (map (vec_of_list o map int_of_integer) gsi) in
    if \<not> (length gs = m \<and> (\<forall> gi \<in> set gs. dim_vec gi = n)) then
      Code.abort (STR ''error in external LLL invocation: dimensions of reduced basis do not fit\<newline>input to external solver: ''
        + String.implode (show fs) + STR ''\<newline>\<newline>'') (\<lambda> _. rb fs)
     else 
      let Fs = mat_of_rows n fs;
          Gs = mat_of_rows n gs;
          H1 = HNF Fs;
          H2 = HNF Gs in 
           if (H1 = H2) then rb gs 
          else Code.abort (STR ''the reduced matrix does not span the same lattice\<newline>f,g,P1,P2,H1,H2 are as follows\<newline>''
            + String.implode (show Fs) + STR ''\<newline>\<newline>''
            + String.implode (show Gs) + STR ''\<newline>\<newline>''
            + String.implode (show H1) + STR ''\<newline>\<newline>''
            + String.implode (show H2) + STR ''\<newline>\<newline>''
            ) (\<lambda> _. rb fs))
    )" 

locale certification = LLL_with_assms +
  fixes HNF::"int mat \<Rightarrow> int mat" and associates res (*HNF operation without explicit transformation matrix*)
  assumes sound_HNF': "is_sound_HNF' HNF associates res"
begin

lemma reduce_basis_external': assumes res: "reduce_basis_external' HNF \<alpha> fs_init = fs" 
  shows "reduced fs m" "LLL_invariant True m fs" 
proof (atomize(full), goal_cases)
  case 1
  show ?case
  proof (cases "LLL_Impl.reduce_basis \<alpha> fs_init = fs")
    case True   
    from reduce_basis[OF this] show ?thesis by simp
  next
    case False note a = False
    show ?thesis
    proof (cases fs_init)
      case Nil
      with res have "fs = []" unfolding reduce_basis_external'_def by auto
      with False Nil have False by (simp add: LLL_Impl.reduce_basis_def)
      thus ?thesis ..
    next
      case (Cons f rest) 
      from Cons fs_init len have dim_fs_n: "dim_vec f = n" by auto
      let ?ext = "external_lll_solver' (map_prod integer_of_int integer_of_int (quotient_of \<alpha>)) 
        (map (map integer_of_int \<circ> list_of_vec) fs_init)" 
      note res = res[unfolded reduce_basis_external'_def Cons Let_def list.case Code.abort_def dim_fs_n,
          folded Cons]
      define gs where "gs = map (vec_of_list o map int_of_integer) ?ext" 
      define Fs where "Fs = mat_of_rows n fs_init"
      define Gs where "Gs = mat_of_rows n gs"
      define H1 where "H1 = HNF Fs"
      define H2 where "H2 = HNF Gs"
      note res = res[unfolded ext option.simps split len dim_fs_n, folded gs_def]
      from res False have not: "(\<not> (length gs = m \<and> (\<forall>gi\<in>set gs. dim_vec gi = n))) = False" 
        by (auto split: if_splits)
      note res = res[unfolded this if_False]
      from not have gs: "set gs \<subseteq> carrier_vec n" 
        and len_gs: "length gs = m" by auto
      show ?thesis
      proof (cases "H1 = H2")
        case True
        hence H1_eq_H2: "H1 = H2" by auto
        let ?HNF = "(\<lambda>A. let H = HNF A in (SOME P. P \<in> carrier_mat (dim_row A) (dim_row A) \<and> invertible_mat P \<and> A = P * H, H))"
        obtain P1 where P1_H1: "(P1,H1) = ?HNF Fs" by (metis H1_def)
        obtain P2 where P2_H2: "(P2,H2) = ?HNF Gs" by (metis H2_def)
        have sound_HNF: "is_sound_HNF ?HNF associates res"
          by (rule is_sound_HNF_conv[OF sound_HNF'])
        have laticce_gs_fs_init: "lattice_of gs = lattice_of fs_init" 
          and gs_assms: "LLL_with_assms n m gs \<alpha>"
          by (rule certification_via_eq_HNF[OF sound_HNF P1_H1[unfolded Fs_def] 
                P2_H2[unfolded Gs_def] H1_eq_H2 gs len_gs])+
        from res a True   
        have gs_fs:  "LLL_Impl.reduce_basis \<alpha> gs = fs"  by (auto split:  prod.split) 
        have lattice_gs_fs: "lattice_of gs = lattice_of fs" 
          and "gram_schmidt_fs.reduced n (map of_int_hom.vec_hom fs) \<alpha> m" 
          and "gs.lin_indpt_list (map of_int_hom.vec_hom fs)"
          and "length fs = length gs" 
          using LLL_with_assms.reduce_basis gs_fs gs_assms laticce_gs_fs_init gs_assms 
          using LLL_with_assms_def len_gs unfolding LLL.L_def by fast+             
        from this show ?thesis
          using laticce_gs_fs_init gs_assms LLL_with_assms_def lattice_gs_fs
          unfolding LLL_invariant_def L_def by auto               
      next
        case False
        then show ?thesis 
          using a Fs_def Gs_def res H1_def H2_def by auto
      qed
    qed
  qed
qed
end

context LLL_with_assms
begin

text \<open>We interpret the certification context using our formalized @{text "HNF_algorithm"}\<close>

interpretation efficient_cert: certification n m fs_init \<alpha> "HNF_algorithm use_sym_mod" "range ass_function_euclidean" "\<lambda>c. range (res_int c)"  
  by (unfold_locales, rule is_sound_HNF'_HNF_algorithm)

(*We get the final lemma for our algorithm. It works for any matrix, but it only applies operations
modulo determinant for non-singular matrices.*)
thm efficient_cert.reduce_basis_external' 

text \<open>Same, but applying the naive HNF algorithm, moved to JNF library from the echelon form 
  and Hermite normal form AFP entries\<close>

interpretation cert: certification n m fs_init \<alpha> "HNF_algorithm_from_HA use_sym_mod" "range ass_function_euclidean" "\<lambda>c. range (res_int c)"  
  by (unfold_locales, rule is_sound_HNF'_HNF_algorithm_from_HA)
thm cert.reduce_basis_external'

(*Explicit versions for paper-presentation:*)
lemma RBE_HNF_algorithm_efficient:
  assumes "reduce_basis_external' (HNF_algorithm use_sym_mod) \<alpha> fs_init = fs"
  shows "gram_schmidt_fs.reduced n (map of_int_hom.vec_hom fs) \<alpha> m"
    and "LLL_invariant True m fs" using efficient_cert.reduce_basis_external' assms by blast+

lemma RBE_HNF_algorithm_naive:
  assumes "reduce_basis_external' (HNF_algorithm_from_HA use_sym_mod) \<alpha> fs_init = fs"
  shows "gram_schmidt_fs.reduced n (map of_int_hom.vec_hom fs) \<alpha> m"
    and "LLL_invariant True m fs" using cert.reduce_basis_external' assms by blast+

end

lemma external_lll_solver'_code[code]: 
  "external_lll_solver' = Code.abort (STR ''require proper implementation of external_lll_solver'') (\<lambda> _. external_lll_solver')" 
  by simp
end
