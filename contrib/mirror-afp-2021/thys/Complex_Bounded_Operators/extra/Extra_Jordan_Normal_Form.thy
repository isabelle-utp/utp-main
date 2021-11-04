section \<open>\<open>Extra_Jordan_Normal_Form\<close> -- Additional results for \<^session>\<open>Jordan_Normal_Form\<close>\<close>
(*
Authors: 
  Dominique Unruh, University of Tartu, unruh@ut.ee      
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)                 

theory Extra_Jordan_Normal_Form
  imports
    Jordan_Normal_Form.Matrix Jordan_Normal_Form.Schur_Decomposition
begin

text \<open>We define bundles to activate/deactivate the notation from \<^session>\<open>Jordan_Normal_Form\<close>.
                                                                         
Reactivate the notation locally via "@{theory_text \<open>includes jnf_notation\<close>}" in a lemma statement.
(Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle jnf_notation ... unbundle no_jnf_notation\<close>}.)
\<close>

bundle jnf_notation begin
notation transpose_mat ("(_\<^sup>T)" [1000])
notation cscalar_prod (infix "\<bullet>c" 70)
notation vec_index (infixl "$" 100)
notation smult_vec (infixl "\<cdot>\<^sub>v" 70)
notation scalar_prod (infix "\<bullet>" 70)
notation index_mat (infixl "$$" 100)
notation smult_mat (infixl "\<cdot>\<^sub>m" 70)
notation mult_mat_vec (infixl "*\<^sub>v" 70)
notation pow_mat (infixr "^\<^sub>m" 75)
notation append_vec (infixr "@\<^sub>v" 65)
notation append_rows (infixr "@\<^sub>r" 65)
end


bundle no_jnf_notation begin
no_notation transpose_mat ("(_\<^sup>T)" [1000])
no_notation cscalar_prod (infix "\<bullet>c" 70)
no_notation vec_index (infixl "$" 100)
no_notation smult_vec (infixl "\<cdot>\<^sub>v" 70)
no_notation scalar_prod (infix "\<bullet>" 70)
no_notation index_mat (infixl "$$" 100)
no_notation smult_mat (infixl "\<cdot>\<^sub>m" 70)
no_notation mult_mat_vec (infixl "*\<^sub>v" 70)
no_notation pow_mat (infixr "^\<^sub>m" 75)
no_notation append_vec (infixr "@\<^sub>v" 65)
no_notation append_rows (infixr "@\<^sub>r" 65)
end

unbundle jnf_notation


lemma mat_entry_explicit:
  fixes M :: "'a::field mat"
  assumes "M \<in> carrier_mat m n" and "i < m" and "j < n"
  shows   "vec_index (M *\<^sub>v unit_vec n j) i = M $$ (i,j)"
  using assms by auto


lemma mat_adjoint_def': "mat_adjoint M = transpose_mat (map_mat conjugate M)"
  apply (rule mat_eq_iff[THEN iffD2])
  apply (auto simp: mat_adjoint_def transpose_mat_def)
  apply (subst mat_of_rows_index)
  by auto

lemma mat_adjoint_swap:
  fixes M ::"complex mat"
  assumes "M \<in> carrier_mat nB nA" and "iA < dim_row M" and "iB < dim_col M"
  shows "(mat_adjoint M)$$(iB,iA) = cnj (M$$(iA,iB))"
  unfolding transpose_mat_def map_mat_def
  by (simp add: assms(2) assms(3) mat_adjoint_def')

lemma cscalar_prod_adjoint:
  fixes M:: "complex mat"
  assumes "M \<in> carrier_mat nB nA" 
    and "dim_vec v = nA"
    and "dim_vec u = nB"
  shows "v \<bullet>c ((mat_adjoint M) *\<^sub>v u) = (M *\<^sub>v v) \<bullet>c u"
  unfolding mat_adjoint_def using assms(1) assms(2,3)[symmetric]
  apply (simp add: scalar_prod_def sum_distrib_left field_simps)
  by (intro sum.swap)

lemma scaleC_minus1_left_vec: "-1 \<cdot>\<^sub>v v = - v" for v :: "_::ring_1 vec"
  unfolding smult_vec_def uminus_vec_def by auto

lemma square_nneg_complex:
  fixes x :: complex
  assumes "x \<in> \<real>" shows "x^2 \<ge> 0"
  apply (cases x) using assms unfolding Reals_def by auto

definition "vec_is_zero n v = (\<forall>i<n. v $ i = 0)"

lemma vec_is_zero: "dim_vec v = n \<Longrightarrow> vec_is_zero n v \<longleftrightarrow> v = 0\<^sub>v n"
  unfolding vec_is_zero_def apply auto
  by (metis index_zero_vec(1))

fun gram_schmidt_sub0
  where "gram_schmidt_sub0 n us [] = us"
  | "gram_schmidt_sub0 n us (w # ws) =
     (let w' = adjuster n w us + w in
      if vec_is_zero n w' then gram_schmidt_sub0 n us ws
                          else gram_schmidt_sub0 n (w' # us) ws)"

lemma (in cof_vec_space) adjuster_already_in_span:
  assumes "w \<in> carrier_vec n"
  assumes us_carrier: "set us \<subseteq> carrier_vec n"
  assumes "corthogonal us"
  assumes "w \<in> span (set us)"
  shows "adjuster n w us + w = 0\<^sub>v n"
proof -
  define v U where "v = adjuster n w us + w" and "U = set us"
  have span: "v \<in> span U"
    unfolding v_def U_def
    apply (rule adjust_preserves_span[THEN iffD1])
    using assms corthogonal_distinct by simp_all
  have v_carrier: "v \<in> carrier_vec n"
    by (simp add: v_def assms corthogonal_distinct)
  have "v \<bullet>c us!i = 0" if "i < length us" for i
    unfolding v_def
    apply (rule adjust_zero)
    using that assms by simp_all
  hence "v \<bullet>c u = 0" if "u \<in> U" for u
    by (metis assms(3) U_def corthogonal_distinct distinct_Ex1 that)
  hence ortho: "u \<bullet>c v = 0" if "u \<in> U" for u
    apply (subst conjugate_zero_iff[symmetric])
    apply (subst conjugate_vec_sprod_comm)
    using that us_carrier v_carrier apply (auto simp: U_def)[2]
    apply (subst conjugate_conjugate_sprod)
    using that us_carrier v_carrier by (auto simp: U_def)
  from span obtain a where v: "lincomb a U = v"
    apply atomize_elim apply (rule finite_in_span[simplified])
    unfolding U_def using us_carrier by auto
  have "v \<bullet>c v = (\<Sum>u\<in>U. (a u \<cdot>\<^sub>v u) \<bullet>c v)"
    apply (subst v[symmetric])
    unfolding lincomb_def
    apply (subst finsum_scalar_prod_sum)
    using U_def span us_carrier by auto
  also have "\<dots> = (\<Sum>u\<in>U. a u * (u \<bullet>c v))"
    using U_def assms(1) in_mono us_carrier v_def by fastforce
  also have "\<dots> = (\<Sum>u\<in>U. a u * conjugate 0)"
    apply (rule sum.cong, simp)
    using span span_closed U_def us_carrier ortho by auto
  also have "\<dots> = 0"
    by auto
  finally have "v \<bullet>c v = 0"
    by -
  thus "v = 0\<^sub>v n"
    using U_def conjugate_square_eq_0_vec span span_closed us_carrier by blast
qed


lemma (in cof_vec_space) gram_schmidt_sub0_result:
  assumes "gram_schmidt_sub0 n us ws = us'"
    and "set ws \<subseteq> carrier_vec n"
    and "set us \<subseteq> carrier_vec n"
    and "distinct us"
    and "~ lin_dep (set us)"
    and "corthogonal us"
  shows "set us' \<subseteq> carrier_vec n \<and>
         distinct us' \<and>
         corthogonal us' \<and>
         span (set (us @ ws)) = span (set us')"  
  using assms
proof (induct ws arbitrary: us us')
  case (Cons w ws)
  show ?case
  proof (cases "w \<in> span (set us)")
    case False
    let ?v = "adjuster n w us"
    have wW[simp]: "set (w#ws) \<subseteq> carrier_vec n" using Cons by simp
    hence W[simp]: "set ws \<subseteq> carrier_vec n"
      and w[simp]: "w : carrier_vec n" by auto
    have U[simp]: "set us \<subseteq> carrier_vec n" using Cons by simp
    have UW: "set (us@ws) \<subseteq> carrier_vec n" by simp
    have wU: "set (w#us) \<subseteq> carrier_vec n" by simp
    have dist_U: "distinct us" using Cons by simp
    have w_U: "w \<notin> set us" using False using span_mem by auto
    have ind_U: "~ lin_dep (set us)"
      using Cons by simp
    have ind_wU: "~ lin_dep (insert w (set us))"
      apply (subst lin_dep_iff_in_span[simplified, symmetric])
      using w_U ind_U False by auto
    thm lin_dep_iff_in_span[simplified, symmetric]
    have corth: "corthogonal us" using Cons by simp
    have "?v + w \<noteq> 0\<^sub>v n"
      by (simp add: False adjust_nonzero dist_U)
    hence "\<not> vec_is_zero n (?v + w)"
      by (simp add: vec_is_zero)
    hence U'def: "gram_schmidt_sub0 n ((?v + w)#us) ws = us'" 
      using Cons by simp
    have v: "?v : carrier_vec n" using dist_U by auto
    hence vw: "?v + w : carrier_vec n" by auto
    hence vwU: "set ((?v + w) # us) \<subseteq> carrier_vec n" by auto
    have vsU: "?v : span (set us)" 
      apply (rule adjuster_in_span[OF w])
      using Cons by simp_all
    hence vsUW: "?v : span (set (us @ ws))"
      using span_is_monotone[of "set us" "set (us@ws)"] by auto
    have wsU: "w \<notin> span (set us)"
      using lin_dep_iff_in_span[OF U ind_U w w_U] ind_wU by auto
    hence vwU: "?v + w \<notin> span (set us)" using adjust_not_in_span[OF w U dist_U] by auto

    have span: "?v + w \<notin> span (set us)" 
      apply (subst span_add[symmetric])
      by (simp_all add: False vsU)
    hence vwUS: "?v + w \<notin> set us" using span_mem by auto

    have vwU: "set ((?v + w) # us) \<subseteq> carrier_vec n" 
      using U w vw by simp
    have dist2: "distinct (((?v + w) # us))" 
      using vwUS
      by (simp add: dist_U)

    have orth2: "corthogonal ((adjuster n w us + w) # us)"
      using adjust_orthogonal[OF U corth w wsU].

    have ind_vwU: "~ lin_dep (set ((adjuster n w us + w) # us))"
      apply simp
      apply (subst lin_dep_iff_in_span[simplified, symmetric])
      by (simp_all add: ind_U vw vwUS span)

    have span_UwW_U': "span (set (us @ w # ws)) = span (set us')"
      using Cons(1)[OF U'def W vwU dist2 ind_vwU orth2] 
      using span_Un[OF vwU wU gram_schmidt_sub_span[OF w U dist_U] W W refl]
      by simp

    show ?thesis
      apply (intro conjI)
      using Cons(1)[OF U'def W vwU dist2 ind_vwU orth2] span_UwW_U' by simp_all
  next
    case True

    let ?v = "adjuster n w us"
    have "?v + w = 0\<^sub>v n"
      apply (rule adjuster_already_in_span)
      using True Cons by auto
    hence "vec_is_zero n (?v + w)"
      by (simp add: vec_is_zero)
    hence U'_def: "us' = gram_schmidt_sub0 n us ws"
      using Cons by simp
    have span: "span (set (us @ w # ws)) = span (set us')"
    proof -
      have wU_U: "span (set (w # us)) = span (set us)"
        apply (subst already_in_span[OF _ True, simplified])
        using Cons by auto
      have "span (set (us @ w # ws)) = span (set (w # us) \<union> set ws)"
        by simp
      also have "\<dots> = span (set us \<union> set ws)"
        apply (rule span_Un) using wU_U Cons by auto
      also have "\<dots> = local.span (set us')"
        using Cons U'_def by auto
      finally show ?thesis
        by -
    qed
    moreover have "set us' \<subseteq> carrier_vec n \<and> distinct us' \<and> corthogonal us'"
      unfolding U'_def using Cons by simp
    ultimately show ?thesis
      by auto
  qed
qed simp

text \<open>This is a variant of \<^term>\<open>Gram_Schmidt.gram_schmidt\<close> that does not require the input vectors
  \<^term>\<open>ws\<close> to be distinct or orthogonal. (In comparison to \<^term>\<open>Gram_Schmidt.gram_schmidt\<close>,
  our version also returns the result in reversed order.)\<close>
definition "gram_schmidt0 n ws = gram_schmidt_sub0 n [] ws"

lemma (in cof_vec_space) gram_schmidt0_result:
  fixes ws
  defines "us' \<equiv> gram_schmidt0 n ws"
  assumes ws: "set ws \<subseteq> carrier_vec n"
  shows "set us' \<subseteq> carrier_vec n"        (is ?thesis1)
    and "distinct us'"                    (is ?thesis2)
    and "corthogonal us'"                 (is ?thesis3)
    and "span (set ws) = span (set us')"  (is ?thesis4)
proof -
  have carrier_empty: "set [] \<subseteq> carrier_vec n" by auto
  have distinct_empty: "distinct []" by simp
  have indep_empty: "lin_indpt (set [])"
    using basis_def subset_li_is_li unit_vecs_basis by auto
  have ortho_empty: "corthogonal []" by auto
  note gram_schmidt_sub0_result' = gram_schmidt_sub0_result
    [OF us'_def[symmetric, THEN meta_eq_to_obj_eq, unfolded gram_schmidt0_def] ws
      carrier_empty distinct_empty indep_empty ortho_empty]
  thus ?thesis1 ?thesis2 ?thesis3 ?thesis4
    by auto
qed

locale complex_vec_space = cof_vec_space n "TYPE(complex)" for n :: nat

lemma gram_schmidt0_corthogonal:
  assumes a1: "corthogonal R" 
    and a2: "\<And>x. x \<in> set R \<Longrightarrow> dim_vec x = d"
  shows "gram_schmidt0 d R = rev R"
proof -
  have "gram_schmidt_sub0 d U R = rev R @ U"
    if "corthogonal ((rev U) @ R)"
      and "\<And>x. x \<in> set U \<union> set R \<Longrightarrow> dim_vec x = d" for U
  proof (insert that, induction R arbitrary: U)
    case Nil
    show ?case 
      by auto
  next
    case (Cons a R)
    have "a \<in> set (rev U @ a # R)"
      by simp      
    moreover have uar: "corthogonal (rev U @ a # R)"
      by (simp add: Cons.prems(1))      
    ultimately have \<open>a \<noteq> 0\<^sub>v d\<close>
      unfolding corthogonal_def
      by (metis conjugate_zero_vec in_set_conv_nth scalar_prod_right_zero zero_carrier_vec)
    then have nonzero_a: "\<not> vec_is_zero d a"
      by (simp add: Cons.prems(2) vec_is_zero)
    define T where "T = rev U @ a # R"
    have "T ! length (rev U) = a"
      unfolding T_def
      by (meson nth_append_length) 
    moreover have "(T ! i \<bullet>c T ! j = 0) = (i \<noteq> j)"
      if "i<length T"
        and "j<length T"
      for i j
      using uar 
      unfolding corthogonal_def T_def
      apply auto
      using T_def that(2) apply auto[1]
      using T_def that(1) that(2) by auto     
    moreover have "length (rev U) < length T"
      by (simp add: T_def)
    ultimately have "(T ! (length (rev U)) \<bullet>c T ! j = 0) = (length (rev U) \<noteq> j)"
      if "j<length T"
      for j
      using that by blast    
    hence "T ! (length (rev U)) \<bullet>c T ! j = 0"
      if  "j<length T"
        and "j \<noteq> length (rev U)"
      for j
      using that(1) that(2) by blast
    hence "a \<bullet>c T ! j = 0"
      if   "j < length (rev U)"
      for j
      using \<open>T ! length (rev U) = a\<close> that(1)
        \<open>length (rev U) < length T\<close> dual_order.strict_trans by blast
    moreover have "T ! j = (rev U) ! j"
      if   "j < length (rev U)"
      for j
      by (smt T_def \<open>length (rev U) < length T\<close> dual_order.strict_trans list_update_append1
          list_update_id nth_list_update_eq that)
    ultimately have "a \<bullet>c u = 0"
      if "u \<in> set (rev U)"
      for u
      by (metis in_set_conv_nth that)
    hence "a \<bullet>c u = 0"
      if "u \<in> set U"
      for u
      by (simp add: that)
    moreover have "\<And>x. x \<in> set U \<Longrightarrow> dim_vec x = d"
      by (simp add: Cons.prems(2))      
    ultimately have "adjuster d a U = 0\<^sub>v d"
    proof(induction U)
      case Nil
      then show ?case by simp
    next
      case (Cons u U)
      moreover have "0 \<cdot>\<^sub>v u + 0\<^sub>v d = 0\<^sub>v d"
      proof-
        have "dim_vec u = d"
          by (simp add: calculation(3))          
        thus ?thesis
          by auto 
      qed
      ultimately show ?case by auto
    qed
    hence adjuster_a: "adjuster d a U + a = a"
      by (simp add: Cons.prems(2) carrier_vecI)      
    have "gram_schmidt_sub0 d U (a # R) = gram_schmidt_sub0 d (a # U) R"
      by (simp add: adjuster_a nonzero_a)
    also have "\<dots> = rev (a # R) @ U"
      apply (subst Cons.IH)
      using Cons.prems by simp_all
    finally show ?case
      by -
  qed
  from this[where U="[]"] show ?thesis
    unfolding gram_schmidt0_def using assms by auto
qed

lemma adjuster_carrier': (* Like adjuster_carrier but with one assm less *)
  assumes w: "(w :: 'a::conjugatable_field vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
  shows "adjuster n w us \<in> carrier_vec n"
  by (insert us, induction us, auto)

lemma eq_mat_on_vecI:
  fixes M N :: \<open>'a::field mat\<close>
  assumes eq: \<open>\<And>v. v\<in>carrier_vec nA \<Longrightarrow> M *\<^sub>v v = N *\<^sub>v v\<close>
  assumes [simp]: \<open>M \<in> carrier_mat nB nA\<close> \<open>N \<in> carrier_mat nB nA\<close>
  shows \<open>M = N\<close>
proof (rule eq_matI)
  show [simp]: \<open>dim_row M = dim_row N\<close> \<open>dim_col M = dim_col N\<close>
    using assms(2) assms(3) by blast+
  fix i j
  assume [simp]: \<open>i < dim_row N\<close> \<open>j < dim_col N\<close>
  show \<open>M $$ (i, j) = N $$ (i, j)\<close>
    thm mat_entry_explicit[where M=M]
    apply (subst mat_entry_explicit[symmetric])
    using assms apply auto[3]
    apply (subst mat_entry_explicit[symmetric])
    using assms apply auto[3]
    apply (subst eq)
     apply auto using assms(3) unit_vec_carrier by blast
qed

lemma list_of_vec_plus:
  fixes v1 v2 :: \<open>complex vec\<close>
  assumes \<open>dim_vec v1 = dim_vec v2\<close>
  shows \<open>list_of_vec (v1 + v2) = map2 (+) (list_of_vec v1) (list_of_vec v2)\<close>
proof-
  have \<open>i < dim_vec v1 \<Longrightarrow> (list_of_vec (v1 + v2)) ! i = (map2 (+) (list_of_vec v1) (list_of_vec v2)) ! i\<close>
    for i
    by (simp add: assms)
  thus ?thesis
    by (metis assms index_add_vec(2) length_list_of_vec length_map map_fst_zip nth_equalityI) 
qed

lemma list_of_vec_mult:
  fixes v :: \<open>complex vec\<close>
  shows \<open>list_of_vec (c \<cdot>\<^sub>v v) = map ((*) c) (list_of_vec v)\<close>
  by (metis (mono_tags, lifting) index_smult_vec(1) index_smult_vec(2) length_list_of_vec length_map nth_equalityI nth_list_of_vec nth_map)



unbundle no_jnf_notation


end
