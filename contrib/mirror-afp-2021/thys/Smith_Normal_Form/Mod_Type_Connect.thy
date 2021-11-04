(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>A new bridge to convert theorems from JNF to HOL Analysis and vice-versa, 
based on the @{text "mod_type"} class\<close>

theory Mod_Type_Connect
  imports 
          Perron_Frobenius.HMA_Connect
          Rank_Nullity_Theorem.Mod_Type
          Gauss_Jordan.Elementary_Operations
begin

text \<open>Some lemmas on @{text "Mod_Type.to_nat"} and @{text "Mod_Type.from_nat"} are added to have 
them with the same names as the analogous ones for @{text "Bij_Nat.to_nat"} 
and @{text "Bij_Nat.to_nat"}.\<close>

lemma inj_to_nat: "inj to_nat" by (simp add: inj_on_def)
lemmas from_nat_inj = from_nat_eq_imp_eq
lemma range_to_nat: "range (to_nat :: 'a :: mod_type \<Rightarrow> nat) = {0 ..< CARD('a)}"
  by (simp add: bij_betw_imp_surj_on mod_type_class.bij_to_nat)


text \<open>This theory is an adaptation of the one presented in @{text "Perron_Frobenius.HMA_Connect"},
  but for matrices and vectors where indexes have the @{text "mod_type"} class restriction.

  It is worth noting that some definitions still use the old abbreviation for HOL Analysis 
  (HMA, from HOL Multivariate Analysis) instead of HA. This is done to be consistent with 
  the existing names in the Perron-Frobenius development\<close>

context includes vec.lifting 
begin
end

definition from_hma\<^sub>v :: "'a ^ 'n :: mod_type \<Rightarrow> 'a Matrix.vec" where
  "from_hma\<^sub>v v = Matrix.vec CARD('n) (\<lambda> i. v $h from_nat i)"

definition from_hma\<^sub>m :: "'a ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> 'a Matrix.mat" where
  "from_hma\<^sub>m a = Matrix.mat CARD('nr) CARD('nc) (\<lambda> (i,j). a $h from_nat i $h from_nat j)"

definition to_hma\<^sub>v :: "'a Matrix.vec \<Rightarrow> 'a ^ 'n :: mod_type" where
  "to_hma\<^sub>v v = (\<chi> i. v $v to_nat i)"

definition to_hma\<^sub>m :: "'a Matrix.mat \<Rightarrow> 'a ^ 'nc :: mod_type ^ 'nr :: mod_type " where
  "to_hma\<^sub>m a = (\<chi> i j. a $$ (to_nat i, to_nat j))"

lemma to_hma_from_hma\<^sub>v[simp]: "to_hma\<^sub>v (from_hma\<^sub>v v) = v"
  by (auto simp: to_hma\<^sub>v_def from_hma\<^sub>v_def to_nat_less_card)

lemma to_hma_from_hma\<^sub>m[simp]: "to_hma\<^sub>m (from_hma\<^sub>m v) = v"
  by (auto simp: to_hma\<^sub>m_def from_hma\<^sub>m_def to_nat_less_card)

lemma from_hma_to_hma\<^sub>v[simp]:
  "v \<in> carrier_vec (CARD('n)) \<Longrightarrow> from_hma\<^sub>v (to_hma\<^sub>v v :: 'a ^ 'n :: mod_type) = v"
  by (auto simp: to_hma\<^sub>v_def from_hma\<^sub>v_def to_nat_from_nat_id)

lemma from_hma_to_hma\<^sub>m[simp]:
  "A \<in> carrier_mat (CARD('nr)) (CARD('nc)) \<Longrightarrow> from_hma\<^sub>m (to_hma\<^sub>m A :: 'a ^ 'nc :: mod_type  ^ 'nr :: mod_type) = A"
  by (auto simp: to_hma\<^sub>m_def from_hma\<^sub>m_def to_nat_from_nat_id)

lemma from_hma\<^sub>v_inj[simp]: "from_hma\<^sub>v x = from_hma\<^sub>v y \<longleftrightarrow> x = y"
  by (intro iffI, insert to_hma_from_hma\<^sub>v[of x], auto)

lemma from_hma\<^sub>m_inj[simp]: "from_hma\<^sub>m x = from_hma\<^sub>m y \<longleftrightarrow> x = y"
  by(intro iffI, insert to_hma_from_hma\<^sub>m[of x], auto)

definition HMA_V :: "'a Matrix.vec \<Rightarrow> 'a ^ 'n :: mod_type \<Rightarrow> bool" where 
  "HMA_V = (\<lambda> v w. v = from_hma\<^sub>v w)"

definition HMA_M :: "'a Matrix.mat \<Rightarrow> 'a ^ 'nc :: mod_type ^ 'nr :: mod_type  \<Rightarrow> bool" where 
  "HMA_M = (\<lambda> a b. a = from_hma\<^sub>m b)"

definition HMA_I :: "nat \<Rightarrow> 'n :: mod_type \<Rightarrow> bool" where
  "HMA_I = (\<lambda> i a. i = to_nat a)"



context includes lifting_syntax
begin

lemma Domainp_HMA_V [transfer_domain_rule]: 
  "Domainp (HMA_V :: 'a Matrix.vec \<Rightarrow> 'a ^ 'n :: mod_type \<Rightarrow> bool) = (\<lambda> v. v \<in> carrier_vec (CARD('n )))"
  by(intro ext iffI, insert from_hma_to_hma\<^sub>v[symmetric], auto simp: from_hma\<^sub>v_def HMA_V_def)

lemma Domainp_HMA_M [transfer_domain_rule]: 
  "Domainp (HMA_M :: 'a Matrix.mat \<Rightarrow> 'a ^ 'nc :: mod_type  ^ 'nr :: mod_type \<Rightarrow> bool) 
  = (\<lambda> A. A \<in> carrier_mat CARD('nr) CARD('nc))"
  by (intro ext iffI, insert from_hma_to_hma\<^sub>m[symmetric], auto simp: from_hma\<^sub>m_def HMA_M_def)

lemma Domainp_HMA_I [transfer_domain_rule]: 
  "Domainp (HMA_I :: nat \<Rightarrow> 'n :: mod_type \<Rightarrow> bool) = (\<lambda> i. i < CARD('n))" (is "?l = ?r")
proof (intro ext)
  fix i :: nat
  show "?l i = ?r i"
    unfolding HMA_I_def Domainp_iff
    by (auto intro: exI[of _ "from_nat i"] simp: to_nat_from_nat_id to_nat_less_card)
qed

lemma bi_unique_HMA_V [transfer_rule]: "bi_unique HMA_V" "left_unique HMA_V" "right_unique HMA_V"
  unfolding HMA_V_def bi_unique_def left_unique_def right_unique_def by auto

lemma bi_unique_HMA_M [transfer_rule]: "bi_unique HMA_M" "left_unique HMA_M" "right_unique HMA_M"
  unfolding HMA_M_def bi_unique_def left_unique_def right_unique_def by auto

lemma bi_unique_HMA_I [transfer_rule]: "bi_unique HMA_I" "left_unique HMA_I" "right_unique HMA_I"
  unfolding HMA_I_def bi_unique_def left_unique_def right_unique_def by auto

lemma right_total_HMA_V [transfer_rule]: "right_total HMA_V"
  unfolding HMA_V_def right_total_def by simp

lemma right_total_HMA_M [transfer_rule]: "right_total HMA_M"
  unfolding HMA_M_def right_total_def by simp

lemma right_total_HMA_I [transfer_rule]: "right_total HMA_I"
  unfolding HMA_I_def right_total_def by simp

lemma HMA_V_index [transfer_rule]: "(HMA_V ===> HMA_I ===> (=)) ($v) ($h)"
  unfolding rel_fun_def HMA_V_def HMA_I_def from_hma\<^sub>v_def
  by (auto simp: to_nat_less_card)


lemma HMA_M_index [transfer_rule]:
  "(HMA_M ===> HMA_I ===> HMA_I ===> (=)) (\<lambda> A i j. A $$ (i,j)) index_hma"
  by (intro rel_funI, simp add: index_hma_def to_nat_less_card HMA_M_def HMA_I_def from_hma\<^sub>m_def)  


lemma HMA_V_0 [transfer_rule]: "HMA_V (0\<^sub>v CARD('n)) (0 :: 'a :: zero ^ 'n:: mod_type)"
  unfolding HMA_V_def from_hma\<^sub>v_def by auto

lemma HMA_M_0 [transfer_rule]: 
  "HMA_M (0\<^sub>m CARD('nr) CARD('nc)) (0 :: 'a :: zero ^ 'nc:: mod_type  ^ 'nr :: mod_type)"
  unfolding HMA_M_def from_hma\<^sub>m_def by auto

lemma HMA_M_1[transfer_rule]:
  "HMA_M (1\<^sub>m (CARD('n))) (mat 1 :: 'a::{zero,one}^'n:: mod_type^'n:: mod_type)"
  unfolding HMA_M_def
  by (auto simp add: mat_def from_hma\<^sub>m_def from_nat_inj)
 

lemma from_hma\<^sub>v_add: "from_hma\<^sub>v v + from_hma\<^sub>v w = from_hma\<^sub>v (v + w)"
  unfolding from_hma\<^sub>v_def by auto

lemma HMA_V_add [transfer_rule]: "(HMA_V ===> HMA_V ===> HMA_V) (+) (+) "
  unfolding rel_fun_def HMA_V_def
  by (auto simp: from_hma\<^sub>v_add)

lemma from_hma\<^sub>v_diff: "from_hma\<^sub>v v - from_hma\<^sub>v w = from_hma\<^sub>v (v - w)"
  unfolding from_hma\<^sub>v_def by auto

lemma HMA_V_diff [transfer_rule]: "(HMA_V ===> HMA_V ===> HMA_V) (-) (-)"
  unfolding rel_fun_def HMA_V_def
  by (auto simp: from_hma\<^sub>v_diff)

lemma from_hma\<^sub>m_add: "from_hma\<^sub>m a + from_hma\<^sub>m b = from_hma\<^sub>m (a + b)"
  unfolding from_hma\<^sub>m_def by auto

lemma HMA_M_add [transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) (+) (+) "
  unfolding rel_fun_def HMA_M_def
  by (auto simp: from_hma\<^sub>m_add)

lemma from_hma\<^sub>m_diff: "from_hma\<^sub>m a - from_hma\<^sub>m b = from_hma\<^sub>m (a - b)"
  unfolding from_hma\<^sub>m_def by auto

lemma HMA_M_diff [transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) (-) (-) "
  unfolding rel_fun_def HMA_M_def
  by (auto simp: from_hma\<^sub>m_diff)

lemma scalar_product: fixes v :: "'a :: semiring_1 ^ 'n :: mod_type"
  shows "scalar_prod (from_hma\<^sub>v v) (from_hma\<^sub>v w) = scalar_product v w"
  unfolding scalar_product_def scalar_prod_def from_hma\<^sub>v_def dim_vec
  by (simp add: sum.reindex[OF inj_to_nat, unfolded range_to_nat])

lemma [simp]:
  "from_hma\<^sub>m (y :: 'a ^ 'nc :: mod_type ^ 'nr:: mod_type) \<in> carrier_mat (CARD('nr)) (CARD('nc))"
  "dim_row (from_hma\<^sub>m (y :: 'a ^ 'nc:: mod_type  ^ 'nr :: mod_type)) = CARD('nr)"
  "dim_col (from_hma\<^sub>m (y :: 'a ^ 'nc :: mod_type ^ 'nr:: mod_type )) = CARD('nc)"
  unfolding from_hma\<^sub>m_def by simp_all

lemma [simp]:
  "from_hma\<^sub>v (y :: 'a ^ 'n:: mod_type) \<in> carrier_vec (CARD('n))"
  "dim_vec (from_hma\<^sub>v (y :: 'a ^ 'n:: mod_type)) = CARD('n)"
  unfolding from_hma\<^sub>v_def by simp_all

lemma HMA_scalar_prod [transfer_rule]:
  "(HMA_V ===> HMA_V ===> (=)) scalar_prod scalar_product" 
  by (auto simp: HMA_V_def scalar_product)

lemma HMA_row [transfer_rule]: "(HMA_I ===> HMA_M ===> HMA_V) (\<lambda> i a. Matrix.row a i) row"
  unfolding HMA_M_def HMA_I_def HMA_V_def
  by (auto simp: from_hma\<^sub>m_def from_hma\<^sub>v_def to_nat_less_card row_def)

lemma HMA_col [transfer_rule]: "(HMA_I ===> HMA_M ===> HMA_V) (\<lambda> i a. col a i) column"
  unfolding HMA_M_def HMA_I_def HMA_V_def
  by (auto simp: from_hma\<^sub>m_def from_hma\<^sub>v_def to_nat_less_card column_def)


lemma HMA_M_mk_mat[transfer_rule]: "((HMA_I ===> HMA_I ===> (=)) ===> HMA_M) 
  (\<lambda> f. Matrix.mat (CARD('nr)) (CARD('nc)) (\<lambda> (i,j). f i j)) 
  (mk_mat :: (('nr \<Rightarrow> 'nc \<Rightarrow> 'a) \<Rightarrow> 'a^'nc:: mod_type^'nr:: mod_type))"
proof-
  {
    fix x y i j
    assume id: "\<forall> (ya :: 'nr) (yb :: 'nc). (x (to_nat ya) (to_nat yb) :: 'a) = y ya yb"
       and i: "i < CARD('nr)" and j: "j < CARD('nc)"
    from to_nat_from_nat_id[OF i] to_nat_from_nat_id[OF j] id[rule_format, of "from_nat i" "from_nat j"]
    have "x i j = y (from_nat i) (from_nat j)" by auto
  }
  thus ?thesis
    unfolding rel_fun_def mk_mat_def HMA_M_def HMA_I_def from_hma\<^sub>m_def by auto
qed

lemma HMA_M_mk_vec[transfer_rule]: "((HMA_I ===> (=)) ===> HMA_V) 
  (\<lambda> f. Matrix.vec (CARD('n)) (\<lambda> i. f i)) 
  (mk_vec :: (('n \<Rightarrow> 'a) \<Rightarrow> 'a^'n:: mod_type))"
proof-
  {
    fix x y i
    assume id: "\<forall> (ya :: 'n). (x (to_nat ya) :: 'a) = y ya"
       and i: "i < CARD('n)" 
    from to_nat_from_nat_id[OF i] id[rule_format, of "from_nat i"]
    have "x i = y (from_nat i)" by auto
  }
  thus ?thesis
    unfolding rel_fun_def mk_vec_def HMA_V_def HMA_I_def from_hma\<^sub>v_def by auto
qed


lemma mat_mult_scalar: "A ** B = mk_mat (\<lambda> i j. scalar_product (row i A) (column j B))"
  unfolding vec_eq_iff matrix_matrix_mult_def scalar_product_def mk_mat_def
  by (auto simp: row_def column_def)

lemma mult_mat_vec_scalar: "A *v v = mk_vec (\<lambda> i. scalar_product (row i A) v)"
  unfolding vec_eq_iff matrix_vector_mult_def scalar_product_def mk_mat_def mk_vec_def
  by (auto simp: row_def column_def)

lemma dim_row_transfer_rule: 
  "HMA_M A (A' :: 'a ^ 'nc:: mod_type ^ 'nr:: mod_type) \<Longrightarrow> (=) (dim_row A) (CARD('nr))"
  unfolding HMA_M_def by auto

lemma dim_col_transfer_rule: 
  "HMA_M A (A' :: 'a ^ 'nc:: mod_type ^ 'nr:: mod_type) \<Longrightarrow> (=) (dim_col A) (CARD('nc))"
  unfolding HMA_M_def by auto


lemma HMA_M_mult [transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) (*) (**)"
proof -
  {
    fix A B :: "'a :: semiring_1 mat" and A' :: "'a ^ 'n :: mod_type ^ 'nr:: mod_type" 
      and B' :: "'a ^ 'nc :: mod_type ^ 'n:: mod_type"
    assume 1[transfer_rule]: "HMA_M A A'" "HMA_M B B'"
    note [transfer_rule] = dim_row_transfer_rule[OF 1(1)] dim_col_transfer_rule[OF 1(2)]
    have "HMA_M (A * B) (A' ** B')"
      unfolding times_mat_def mat_mult_scalar
      by (transfer_prover_start, transfer_step+, transfer, auto)
  }
  thus ?thesis by blast
qed
      

lemma HMA_V_smult [transfer_rule]: "((=) ===> HMA_V ===> HMA_V) (\<cdot>\<^sub>v) (*s)"
  unfolding smult_vec_def 
  unfolding rel_fun_def HMA_V_def from_hma\<^sub>v_def
  by auto

lemma HMA_M_mult_vec [transfer_rule]: "(HMA_M ===> HMA_V ===> HMA_V) (*\<^sub>v) (*v)"
proof -
  {
    fix A :: "'a :: semiring_1 mat" and v :: "'a Matrix.vec"
      and A' :: "'a ^ 'nc :: mod_type ^ 'nr :: mod_type" and v' :: "'a ^ 'nc :: mod_type"
    assume 1[transfer_rule]: "HMA_M A A'" "HMA_V v v'"
    note [transfer_rule] = dim_row_transfer_rule
    have "HMA_V (A *\<^sub>v v) (A' *v v')"
      unfolding mult_mat_vec_def mult_mat_vec_scalar
      by (transfer_prover_start, transfer_step+, transfer, auto)
  }
  thus ?thesis by blast  
qed


lemma HMA_det [transfer_rule]: "(HMA_M ===> (=)) Determinant.det 
  (det :: 'a :: comm_ring_1 ^ 'n :: mod_type ^ 'n :: mod_type \<Rightarrow> 'a)"
proof -
  {
    fix a :: "'a ^ 'n :: mod_type^ 'n:: mod_type"
    let ?tn = "to_nat :: 'n :: mod_type \<Rightarrow> nat"
    let ?fn = "from_nat :: nat \<Rightarrow> 'n"
    let ?zn = "{0..< CARD('n)}"
    let ?U = "UNIV :: 'n set"
    let ?p1 = "{p. p permutes ?zn}"
    let ?p2 = "{p. p permutes ?U}"  
    let ?f= "\<lambda> p i. if i \<in> ?U then ?fn (p (?tn i)) else i"
    let ?g = "\<lambda> p i. ?fn (p (?tn i))"
    have fg: "\<And> a b c. (if a \<in> ?U then b else c) = b" by auto
    have "?p2 = ?f ` ?p1" 
      by (rule permutes_bij', auto simp: to_nat_less_card to_nat_from_nat_id)
    hence id: "?p2 = ?g ` ?p1" by simp
    have inj_g: "inj_on ?g ?p1"
      unfolding inj_on_def
    proof (intro ballI impI ext, auto)
      fix p q i
      assume p: "p permutes ?zn" and q: "q permutes ?zn"
        and id: "(\<lambda> i. ?fn (p (?tn i))) = (\<lambda> i. ?fn (q (?tn i)))"
      {
        fix i
        from permutes_in_image[OF p] have pi: "p (?tn i) < CARD('n)" by (simp add: to_nat_less_card)
        from permutes_in_image[OF q] have qi: "q (?tn i) < CARD('n)" by (simp add: to_nat_less_card)
        from fun_cong[OF id] have "?fn (p (?tn i))  = from_nat (q (?tn i))" .
        from arg_cong[OF this, of ?tn] have "p (?tn i) = q (?tn i)"
          by (simp add: to_nat_from_nat_id pi qi)
      } note id = this             
      show "p i = q i"
      proof (cases "i < CARD('n)")
        case True
        hence "?tn (?fn i) = i" by (simp add: to_nat_from_nat_id)
        from id[of "?fn i", unfolded this] show ?thesis .
      next
        case False
        thus ?thesis using p q unfolding permutes_def by simp
      qed
    qed
    have mult_cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by simp
    have "sum (\<lambda> p. 
      signof p * (\<Prod>i\<in>?zn. a $h ?fn i $h ?fn (p i))) ?p1
      = sum (\<lambda> p. of_int (sign p) * (\<Prod>i\<in>UNIV. a $h i $h p i)) ?p2"
      unfolding id sum.reindex[OF inj_g]
    proof (rule sum.cong[OF refl], unfold mem_Collect_eq o_def, rule mult_cong)
      fix p
      assume p: "p permutes ?zn"
      let ?q = "\<lambda> i. ?fn (p (?tn i))"
      from id p have q: "?q permutes ?U" by auto
      from p have pp: "permutation p" unfolding permutation_permutes by auto
      let ?ft = "\<lambda> p i. ?fn (p (?tn i))"
      have fin: "finite ?zn" by simp
      have "sign p = sign ?q \<and> p permutes ?zn"
      proof (induct rule: permutes_induct[OF fin _ _ p])    
        case 1 
        show ?case by (auto simp: sign_id[unfolded id_def] permutes_id[unfolded id_def])
      next
        case (2 a b p)
        let ?sab = "Fun.swap a b id"
        let ?sfab = "Fun.swap (?fn a) (?fn b) id"
        have p_sab: "permutation ?sab" by (rule permutation_swap_id)
        have p_sfab: "permutation ?sfab" by (rule permutation_swap_id)
        from 2(3) have IH1: "p permutes ?zn" and IH2: "sign p = sign (?ft p)" by auto
        have sab_perm: "?sab permutes ?zn" using 2(1-2) by (rule permutes_swap_id)
        from permutes_compose[OF IH1 this] have perm1: "?sab o p permutes ?zn" .
        from IH1 have p_p1: "p \<in> ?p1" by simp
        hence "?ft p \<in> ?ft ` ?p1" by (rule imageI)
        from this[folded id] have "?ft p permutes ?U" by simp
        hence p_ftp: "permutation (?ft p)" unfolding permutation_permutes by auto
        {
          fix a b
          assume a: "a \<in> ?zn" and b: "b \<in> ?zn" 
          hence "(?fn a = ?fn b) = (a = b)" using 2(1-2)
            by (auto simp add: from_nat_eq_imp_eq)
        } note inj = this
        from inj[OF 2(1-2)] have id2: "sign ?sfab = sign ?sab" unfolding sign_swap_id by simp
        have id: "?ft (Fun.swap a b id \<circ> p) = Fun.swap (?fn a) (?fn b) id \<circ> ?ft p"
        proof
          fix c 
          show "?ft (Fun.swap a b id \<circ> p) c = (Fun.swap (?fn a) (?fn b) id \<circ> ?ft p) c"
          proof (cases "p (?tn c) = a \<or> p (?tn c) = b")
            case True
            thus ?thesis by (cases, auto simp add: o_def swap_def)
          next
            case False
            hence neq: "p (?tn c) \<noteq> a" "p (?tn c) \<noteq> b" by auto
            have pc: "p (?tn c) \<in> ?zn" unfolding permutes_in_image[OF IH1] 
              by (simp add: to_nat_less_card)
            from neq[folded inj[OF pc 2(1)] inj[OF pc 2(2)]]
            have "?fn (p (?tn c)) \<noteq> ?fn a" "?fn (p (?tn c)) \<noteq> ?fn b" .
            with neq show ?thesis by (auto simp: o_def swap_def)
          qed
        qed
        show ?case unfolding IH2 id sign_compose[OF p_sab 2(5)] sign_compose[OF p_sfab p_ftp] id2 
          by (rule conjI[OF refl perm1])
      qed
      thus "signof p = of_int (sign ?q)" unfolding signof_def sign_def by auto
      show "(\<Prod>i = 0..<CARD('n). a $h ?fn i $h ?fn (p i)) =
           (\<Prod>i\<in>UNIV. a $h i $h ?q i)" unfolding 
           range_to_nat[symmetric] prod.reindex[OF inj_to_nat]
            by (rule prod.cong[OF refl], unfold o_def, simp)
    qed   
  }
  thus ?thesis unfolding HMA_M_def 
    by (auto simp: from_hma\<^sub>m_def Determinant.det_def det_def)
qed

lemma HMA_mat[transfer_rule]: "((=) ===> HMA_M) (\<lambda> k. k \<cdot>\<^sub>m 1\<^sub>m CARD('n)) 
  (Finite_Cartesian_Product.mat :: 'a::semiring_1 \<Rightarrow> 'a^'n :: mod_type^'n :: mod_type)"
  unfolding Finite_Cartesian_Product.mat_def[abs_def] rel_fun_def HMA_M_def
  by (auto simp: from_hma\<^sub>m_def from_nat_inj)


lemma HMA_mat_minus[transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) 
  (\<lambda> A B. A + map_mat uminus B) ((-) :: 'a :: group_add ^'nc:: mod_type^'nr:: mod_type 
  \<Rightarrow> 'a^'nc:: mod_type^'nr:: mod_type \<Rightarrow> 'a^'nc:: mod_type^'nr:: mod_type)"
  unfolding rel_fun_def HMA_M_def from_hma\<^sub>m_def by auto

lemma HMA_transpose_matrix [transfer_rule]: 
  "(HMA_M ===> HMA_M) transpose_mat transpose"
  unfolding transpose_mat_def transpose_def HMA_M_def from_hma\<^sub>m_def by auto


lemma HMA_invertible_matrix_mod_type[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'n :: mod_type ^ 'n :: mod_type 
      \<Rightarrow> _) ===> (=)) invertible_mat invertible" 
proof (intro rel_funI, goal_cases)
  case (1 x y)
  note rel_xy[transfer_rule] = "1"
  have eq_dim: "dim_col x = dim_row x"
    using Mod_Type_Connect.dim_col_transfer_rule Mod_Type_Connect.dim_row_transfer_rule rel_xy 
    by fastforce    
  moreover have "\<exists>A'. y ** A' = mat 1 \<and> A' ** y = mat 1" 
    if xB: "x * B = 1\<^sub>m (dim_row x)" and Bx: "B * x = 1\<^sub>m (dim_row B)" for B
  proof -
    let ?A' = "Mod_Type_Connect.to_hma\<^sub>m B:: 'a :: comm_ring_1 ^ 'n :: mod_type^ 'n :: mod_type" 
    have rel_BA[transfer_rule]: "Mod_Type_Connect.HMA_M B ?A'"
      by (metis (no_types, lifting) Bx Mod_Type_Connect.HMA_M_def eq_dim carrier_mat_triv dim_col_mat(1)
          Mod_Type_Connect.from_hma\<^sub>m_def Mod_Type_Connect.from_hma_to_hma\<^sub>m index_mult_mat(3) 
          index_one_mat(3) rel_xy xB)
    have [simp]: "dim_row B = CARD('n)" using Mod_Type_Connect.dim_row_transfer_rule rel_BA by blast
    have [simp]: "dim_row x = CARD('n)" using Mod_Type_Connect.dim_row_transfer_rule rel_xy by blast
    have "y ** ?A' = mat 1" using xB by (transfer, simp)
    moreover have "?A' ** y  = mat 1" using Bx by (transfer, simp)
    ultimately show ?thesis by blast
  qed
  moreover have "\<exists>B. x * B = 1\<^sub>m (dim_row x) \<and> B * x = 1\<^sub>m (dim_row B)"
    if yA: "y ** A' = mat 1" and Ay: "A' ** y = mat 1" for A'
  proof -
    let ?B = "(Mod_Type_Connect.from_hma\<^sub>m A')"
    have [simp]: "dim_row x = CARD('n)" using rel_xy Mod_Type_Connect.dim_row_transfer_rule by blast
    have [transfer_rule]: "Mod_Type_Connect.HMA_M ?B A'" by (simp add: Mod_Type_Connect.HMA_M_def)
    hence [simp]: "dim_row ?B = CARD('n)" using dim_row_transfer_rule by auto
    have "x * ?B = 1\<^sub>m (dim_row x)" using yA by (transfer', auto)
    moreover have "?B * x = 1\<^sub>m (dim_row ?B)" using Ay by (transfer', auto)
    ultimately show ?thesis by auto
  qed
  ultimately show ?case unfolding invertible_mat_def invertible_def inverts_mat_def by auto
qed


end


text \<open>Some transfer rules for relating the elementary operations are also proved.\<close>

context
  includes lifting_syntax
begin

lemma HMA_swaprows[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> _)
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nr :: mod_type \<Rightarrow> _ )
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nr :: mod_type \<Rightarrow> _ )     
    ===> Mod_Type_Connect.HMA_M) 
    (\<lambda>A a b. swaprows a b A) interchange_rows" 
  by (intro rel_funI, goal_cases, auto simp add: Mod_Type_Connect.HMA_M_def interchange_rows_def)
     (rule eq_matI, auto simp add: Mod_Type_Connect.from_hma\<^sub>m_def Mod_Type_Connect.HMA_I_def 
      to_nat_less_card to_nat_from_nat_id)

lemma HMA_swapcols[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> _)
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nc :: mod_type \<Rightarrow> _ )
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nc :: mod_type \<Rightarrow> _ )     
    ===> Mod_Type_Connect.HMA_M) 
    (\<lambda>A a b. swapcols a b A) interchange_columns" 
  by (intro rel_funI, goal_cases, auto simp add: Mod_Type_Connect.HMA_M_def interchange_columns_def)
     (rule eq_matI, auto simp add: Mod_Type_Connect.from_hma\<^sub>m_def Mod_Type_Connect.HMA_I_def 
      to_nat_less_card to_nat_from_nat_id)

lemma HMA_addrow[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> _) 
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nr :: mod_type \<Rightarrow> _ )
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nr :: mod_type \<Rightarrow> _ ) 
    ===> (=)
    ===> Mod_Type_Connect.HMA_M) 
    (\<lambda>A a b q. addrow q a b A) row_add"
  by (intro rel_funI, goal_cases, auto simp add: Mod_Type_Connect.HMA_M_def row_add_def)
     (rule eq_matI, auto simp add: Mod_Type_Connect.from_hma\<^sub>m_def Mod_Type_Connect.HMA_I_def 
      to_nat_less_card to_nat_from_nat_id)

lemma HMA_addcol[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> _) 
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nc :: mod_type \<Rightarrow> _ )
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nc :: mod_type \<Rightarrow> _ ) 
    ===> (=)
    ===> Mod_Type_Connect.HMA_M) 
    (\<lambda>A a b q. addcol q a b A) column_add"
  by (intro rel_funI, goal_cases, auto simp add: Mod_Type_Connect.HMA_M_def column_add_def)
     (rule eq_matI, auto simp add: Mod_Type_Connect.from_hma\<^sub>m_def Mod_Type_Connect.HMA_I_def 
      to_nat_less_card to_nat_from_nat_id)

lemma HMA_multrow[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> _)
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nr :: mod_type \<Rightarrow> _ )
    ===> (=)     
    ===> Mod_Type_Connect.HMA_M) 
    (\<lambda>A i q. multrow i q A) mult_row"
  by (intro rel_funI, goal_cases, auto simp add: Mod_Type_Connect.HMA_M_def mult_row_def)
     (rule eq_matI, auto simp add: Mod_Type_Connect.from_hma\<^sub>m_def Mod_Type_Connect.HMA_I_def 
      to_nat_less_card to_nat_from_nat_id)

lemma HMA_multcol[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> _)
    ===> (Mod_Type_Connect.HMA_I :: _ \<Rightarrow>'nc :: mod_type \<Rightarrow> _ )
    ===> (=)     
    ===> Mod_Type_Connect.HMA_M) 
    (\<lambda>A i q. multcol i q A) mult_column"
  by (intro rel_funI, goal_cases, auto simp add: Mod_Type_Connect.HMA_M_def mult_column_def)
     (rule eq_matI, auto simp add: Mod_Type_Connect.from_hma\<^sub>m_def Mod_Type_Connect.HMA_I_def 
      to_nat_less_card to_nat_from_nat_id)

end

fun HMA_M3 where
  "HMA_M3 (P,A,Q) 
  (P' :: 'a :: comm_ring_1 ^ 'nr :: mod_type ^ 'nr :: mod_type,
   A' :: 'a ^ 'nc :: mod_type ^ 'nr :: mod_type,
   Q' :: 'a ^ 'nc :: mod_type ^ 'nc :: mod_type) = 
  (Mod_Type_Connect.HMA_M P P' \<and> Mod_Type_Connect.HMA_M A A' \<and> Mod_Type_Connect.HMA_M Q Q')"

lemma HMA_M3_def: 
  "HMA_M3 A B = (Mod_Type_Connect.HMA_M (fst A) (fst B) 
  \<and> Mod_Type_Connect.HMA_M (fst (snd A)) (fst (snd B)) 
  \<and> Mod_Type_Connect.HMA_M (snd (snd A)) (snd (snd B)))"  
  by (smt HMA_M3.simps prod.collapse)


context 
  includes lifting_syntax
begin

lemma Domainp_HMA_M3 [transfer_domain_rule]: 
 "Domainp (HMA_M3 :: _\<Rightarrow>(_\<times>('a::comm_ring_1^'nc::mod_type^'nr::mod_type)\<times>_)\<Rightarrow>_) 
 = (\<lambda>(P,A,Q). P \<in> carrier_mat CARD('nr) CARD('nr) \<and> A \<in> carrier_mat CARD('nr) CARD('nc) 
  \<and> Q \<in> carrier_mat CARD('nc) CARD('nc))"
proof -
  let ?HMA_M3 = "HMA_M3::_\<Rightarrow>(_\<times>('a::comm_ring_1^'nc::mod_type^'nr::mod_type)\<times>_)\<Rightarrow>_"
  have 1: "P \<in> carrier_mat CARD('nr) CARD('nr) \<and>
         A \<in> carrier_mat CARD('nr) CARD('nc) \<and> Q \<in> carrier_mat CARD('nc) CARD('nc)"
    if "Domainp ?HMA_M3 (P,A,Q)" for P A Q
      using that unfolding Domainp_iff by (auto simp add: Mod_Type_Connect.HMA_M_def)  
  have 2: "Domainp ?HMA_M3 (P,A,Q)" if PAQ: "P \<in> carrier_mat CARD('nr) CARD('nr)
   \<and> A \<in> carrier_mat CARD('nr) CARD('nc) \<and>Q \<in> carrier_mat CARD('nc) CARD('nc)" for P A Q
  proof -
     let ?P = "Mod_Type_Connect.to_hma\<^sub>m P::'a^'nr::mod_type^'nr::mod_type"
     let ?A = "Mod_Type_Connect.to_hma\<^sub>m A::'a^'nc::mod_type^'nr::mod_type"
     let ?Q = "Mod_Type_Connect.to_hma\<^sub>m Q::'a^'nc::mod_type^'nc::mod_type"
     have "HMA_M3 (P,A,Q) (?P,?A,?Q)"
       by (auto simp add: Mod_Type_Connect.HMA_M_def PAQ)  
     thus ?thesis unfolding Domainp_iff by auto
   qed  
   have "fst x \<in> carrier_mat CARD('nr) CARD('nr) \<and> fst (snd x) \<in> carrier_mat CARD('nr) CARD('nc) 
      \<and> (snd (snd x)) \<in> carrier_mat CARD('nc) CARD('nc)"
    if "Domainp ?HMA_M3 x" for x using 1
    by (metis (full_types) surjective_pairing that)
  moreover have "Domainp ?HMA_M3 x" 
    if "fst x \<in> carrier_mat CARD('nr) CARD('nr) \<and> fst (snd x) \<in> carrier_mat CARD('nr) CARD('nc) 
      \<and> (snd (snd x)) \<in> carrier_mat CARD('nc) CARD('nc)" for x 
    using 2
    by (metis (full_types) surjective_pairing that)
  ultimately show ?thesis by (intro ext iffI, unfold split_beta, metis+) 
qed

lemma bi_unique_HMA_M3 [transfer_rule]: "bi_unique HMA_M3" "left_unique HMA_M3" "right_unique HMA_M3"
  unfolding HMA_M3_def bi_unique_def left_unique_def right_unique_def
  by (auto simp add: Mod_Type_Connect.HMA_M_def)

lemma right_total_HMA_M3 [transfer_rule]: "right_total HMA_M3"
  unfolding HMA_M_def right_total_def
  by (simp add: Mod_Type_Connect.HMA_M_def)

end

(*
  TODO: add more theorems to connect everything from HA to JNF in this setting.
*)
end
