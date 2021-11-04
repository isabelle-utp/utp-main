section \<open>Storjohann's basis reduction algorithm (abstract version)\<close>

text \<open>This theory contains the soundness proofs of Storjohann's basis
  reduction algorithms, both for the normal and the improved-swap-order variant.

  The implementation of Storjohann's version of LLL uses modular operations throughout.
  It is an abstract implementation that is already quite close to what the actual implementation will be.
   In particular, the swap operation here is derived from the computation lemma for the swap
   operation in the old, integer-only formalization of LLL.\<close>

theory Storjohann
  imports 
    Storjohann_Mod_Operation
    LLL_Basis_Reduction.LLL_Number_Bounds
    Sqrt_Babylonian.NthRoot_Impl
begin

subsection \<open>Definition of algorithm\<close>

text \<open>In the definition of the algorithm, the first-flag determines, whether only the first vector
  of the reduced basis should be computed, i.e., a short vector. Then the modulus can be slightly
  decreased in comparison to the required modulus for computing the whole reduced matrix.\<close>

fun max_list_rats_with_index :: "(int * int * nat) list \<Rightarrow> (int * int * nat)" where
  "max_list_rats_with_index [x] = x" |
  "max_list_rats_with_index ((n1,d1,i1) # (n2,d2,i2) # xs) 
     = max_list_rats_with_index ((if n1 * d2 \<le> n2 * d1 then (n2,d2,i2) else (n1,d1,i1)) # xs)"

context LLL
begin

definition "log_base = (10 :: int)" 

definition bound_number :: "bool \<Rightarrow> nat" where
  "bound_number first = (if first \<and> m \<noteq> 0 then 1 else m)" 

definition compute_mod_of_max_gso_norm :: "bool \<Rightarrow> rat \<Rightarrow> int" where
  "compute_mod_of_max_gso_norm first mn = log_base ^ (log_ceiling log_base (max 2 (
     root_rat_ceiling 2 (mn * (rat_of_nat (bound_number first) + 3)) + 1)))"

definition g_bnd_mode :: "bool \<Rightarrow> rat \<Rightarrow> int vec list \<Rightarrow> bool" where 
  "g_bnd_mode first b fs = (if first \<and> m \<noteq> 0 then sq_norm (gso fs 0) \<le> b else g_bnd b fs)" 

definition d_of where "d_of dmu i = (if i = 0 then 1 :: int else dmu $$ (i - 1, i - 1))"

definition compute_max_gso_norm :: "bool \<Rightarrow> int mat \<Rightarrow> rat \<times> nat" where
  "compute_max_gso_norm first dmu = (if m = 0 then (0,0) else 
      case max_list_rats_with_index (map (\<lambda> i. (d_of dmu (Suc i), d_of dmu i, i)) [0 ..< (if first then 1 else m)])
      of (num, denom, i) \<Rightarrow> (of_int num / of_int denom, i))"


context
  fixes p :: int \<comment> \<open>the modulus\<close>
    and first :: bool \<comment> \<open>only compute first vector of reduced basis\<close>
begin

definition basis_reduction_mod_add_row :: 
  "int vec list \<Rightarrow> int mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (int vec list \<times> int mat)"  where
  "basis_reduction_mod_add_row mfs dmu i j = 
    (let c = round_num_denom (dmu $$ (i,j)) (d_of dmu (Suc j)) in
      (if c = 0 then (mfs, dmu) 
        else (mfs[ i := (map_vec (\<lambda> x. x symmod p)) (mfs ! i - c \<cdot>\<^sub>v mfs ! j)], 
             mat m m (\<lambda>(i',j'). (if (i' = i \<and> j' \<le> j) 
                then (if j'=j then (dmu $$ (i,j') - c * dmu $$ (j,j')) 
                      else (dmu $$ (i,j') - c * dmu $$ (j,j')) 
                            symmod (p * d_of dmu j' * d_of dmu (Suc j')))
                else (dmu $$ (i',j')))))))"

fun basis_reduction_mod_add_rows_loop where
  "basis_reduction_mod_add_rows_loop mfs dmu i 0 = (mfs, dmu)"
| "basis_reduction_mod_add_rows_loop mfs dmu i (Suc j) = (
     let (mfs', dmu') = basis_reduction_mod_add_row mfs dmu i j
      in basis_reduction_mod_add_rows_loop mfs' dmu' i j)" 

definition basis_reduction_mod_swap_dmu_mod :: "int mat \<Rightarrow> nat \<Rightarrow> int mat" where
  "basis_reduction_mod_swap_dmu_mod dmu k = mat m m (\<lambda>(i, j). (
    if j < i \<and> (j = k \<or> j = k - 1) then 
        dmu $$ (i, j) symmod (p * d_of dmu j * d_of dmu (Suc j))
    else dmu $$ (i, j)))"

definition basis_reduction_mod_swap where
  "basis_reduction_mod_swap mfs dmu k = 
     (mfs[k := mfs ! (k - 1), k - 1 := mfs ! k],
      basis_reduction_mod_swap_dmu_mod (mat m m (\<lambda>(i,j). (
      if j < i then
        if i = k - 1 then 
           dmu $$ (k, j)
        else if i = k \<and> j \<noteq> k - 1 then 
             dmu $$ (k - 1, j)
        else if i > k \<and> j = k then
           ((d_of dmu (Suc k)) * dmu $$ (i, k - 1) - dmu $$ (k, k - 1) * dmu $$ (i, j)) 
              div (d_of dmu k)
        else if i > k \<and> j = k - 1 then
           (dmu $$ (k, k - 1) * dmu $$ (i, j) + dmu $$ (i, k) * (d_of dmu (k-1)))
              div (d_of dmu k)
        else dmu $$ (i, j)
      else if i = j then 
        if i = k - 1 then 
          ((d_of dmu (Suc k)) * (d_of dmu (k-1)) + dmu $$ (k, k - 1) * dmu $$ (k, k - 1)) 
            div (d_of dmu k)
        else (d_of dmu (Suc i))
      else dmu $$ (i, j))
    )) k)" 

fun basis_reduction_adjust_mod where
  "basis_reduction_adjust_mod mfs dmu = 
    (let (b,g_idx) = compute_max_gso_norm first dmu;
         p' = compute_mod_of_max_gso_norm first b
        in if p' < p then 
           let mfs' = map (map_vec (\<lambda>x. x symmod p')) mfs;
               d_vec = vec (Suc m) (\<lambda> i. d_of dmu i);
               dmu' = mat m m (\<lambda> (i,j). if j < i then dmu $$ (i,j) 
                 symmod (p' * d_vec $ j * d_vec $ (Suc j)) else
                 dmu $$ (i,j))
             in (p', mfs', dmu', g_idx)
           else (p, mfs, dmu, g_idx))" 

definition basis_reduction_adjust_swap_add_step where
  "basis_reduction_adjust_swap_add_step mfs dmu g_idx i = (
    let i1 = i - 1; 
        (mfs1, dmu1) = basis_reduction_mod_add_row mfs dmu i i1;
        (mfs2, dmu2) = basis_reduction_mod_swap mfs1 dmu1 i
      in if i1 = g_idx then basis_reduction_adjust_mod mfs2 dmu2
         else (p, mfs2, dmu2, g_idx))"


definition basis_reduction_mod_step where
  "basis_reduction_mod_step mfs dmu g_idx i (j :: int) = (if i = 0 then (p, mfs, dmu, g_idx, Suc i, j)
     else let di = d_of dmu i;
              (num, denom) = quotient_of \<alpha>
      in if di * di * denom \<le> num * d_of dmu (i - 1) * d_of dmu (Suc i) then
          (p, mfs, dmu, g_idx, Suc i, j)
      else let (p', mfs', dmu', g_idx') = basis_reduction_adjust_swap_add_step mfs dmu g_idx i
          in (p', mfs', dmu', g_idx', i - 1, j + 1))" 

primrec basis_reduction_mod_add_rows_outer_loop where
  "basis_reduction_mod_add_rows_outer_loop mfs dmu 0 = (mfs, dmu)" |
  "basis_reduction_mod_add_rows_outer_loop mfs dmu (Suc i) = 
    (let (mfs', dmu') = basis_reduction_mod_add_rows_outer_loop mfs dmu i in
      basis_reduction_mod_add_rows_loop mfs' dmu' (Suc i) (Suc i))"
end

text \<open>the main loop of the normal Storjohann algorithm\<close>
partial_function (tailrec) basis_reduction_mod_main where
  "basis_reduction_mod_main p first mfs dmu g_idx i (j :: int) = (
    (if i < m 
       then 
         case basis_reduction_mod_step p first mfs dmu g_idx i j
         of (p', mfs', dmu', g_idx', i', j') \<Rightarrow>  
           basis_reduction_mod_main p' first mfs' dmu' g_idx' i' j'
       else
         (p, mfs, dmu)))"

definition compute_max_gso_quot:: "int mat \<Rightarrow> (int * int * nat)" where
  "compute_max_gso_quot dmu = max_list_rats_with_index 
    (map (\<lambda>i. ((d_of dmu (i+1)) * (d_of dmu (i+1)), (d_of dmu (i+2)) * (d_of dmu i), Suc i)) [0..<(m-1)])"

text \<open>the main loop of Storjohann's algorithm with improved swap order\<close>
partial_function (tailrec) basis_reduction_iso_main where
  "basis_reduction_iso_main p first mfs dmu g_idx (j :: int) = (
    (if m > 1 then
      (let (max_gso_num, max_gso_denum, indx) = compute_max_gso_quot dmu;
        (num, denum) = quotient_of \<alpha> in
        (if (max_gso_num * denum  > num * max_gso_denum) then
            case basis_reduction_adjust_swap_add_step p first mfs dmu g_idx indx of
              (p', mfs', dmu', g_idx') \<Rightarrow>
          basis_reduction_iso_main p' first mfs' dmu' g_idx' (j + 1) 
         else
           (p, mfs, dmu)))
     else (p, mfs, dmu)))"

definition compute_initial_mfs where
  "compute_initial_mfs p = map (map_vec (\<lambda>x. x symmod p)) fs_init"

definition compute_initial_dmu where
  "compute_initial_dmu p dmu = mat m m (\<lambda>(i',j'). if j' < i' 
        then dmu $$ (i', j') symmod (p * d_of dmu j' * d_of dmu (Suc j')) 
        else dmu $$ (i', j'))"

definition "dmu_initial = (let dmu = d\<mu>_impl fs_init
   in mat m m (\<lambda> (i,j). 
   if j \<le> i then d\<mu>_impl fs_init !! i !! j else 0))"

definition "compute_initial_state first = 
  (let dmu = dmu_initial;
       (b, g_idx) = compute_max_gso_norm first dmu;
       p = compute_mod_of_max_gso_norm first b
     in (p, compute_initial_mfs p, compute_initial_dmu p dmu, g_idx))" 

text \<open>Storjohann's algorithm\<close>
definition reduce_basis_mod :: "int vec list" where
  "reduce_basis_mod = (
     let first = False;
         (p0, mfs0, dmu0, g_idx) = compute_initial_state first;
         (p', mfs', dmu') = basis_reduction_mod_main p0 first mfs0 dmu0 g_idx 0 0;
         (mfs'', dmu'') = basis_reduction_mod_add_rows_outer_loop p' mfs' dmu' (m-1)
      in mfs'')"

text \<open>Storjohann's algorithm with improved swap order\<close>
definition reduce_basis_iso :: "int vec list" where
  "reduce_basis_iso = (
     let first = False; 
         (p0, mfs0, dmu0, g_idx) = compute_initial_state first;
         (p', mfs', dmu') = basis_reduction_iso_main p0 first mfs0 dmu0 g_idx 0;
         (mfs'', dmu'') = basis_reduction_mod_add_rows_outer_loop p' mfs' dmu' (m-1)
      in mfs'')"

text \<open>Storjohann's algorithm for computing a short vector\<close>
definition 
  "short_vector_mod = (
     let first = True;
         (p0, mfs0, dmu0, g_idx) = compute_initial_state first;
         (p', mfs', dmu') = basis_reduction_mod_main p0 first mfs0 dmu0 g_idx 0 0
      in hd mfs')"

text \<open>Storjohann's algorithm (iso-variant) for computing a short vector\<close>
definition 
  "short_vector_iso = (
     let first = True; 
         (p0, mfs0, dmu0, g_idx) = compute_initial_state first;
         (p', mfs', dmu') = basis_reduction_iso_main p0 first mfs0 dmu0 g_idx 0
      in hd mfs')"
end

subsection \<open>Towards soundness of Storjohann's algorithm\<close>

lemma max_list_rats_with_index_in_set: 
  assumes max: "max_list_rats_with_index xs = (nm, dm, im)"
  and len: "length xs \<ge> 1"
shows "(nm, dm, im) \<in> set xs"
  using assms
proof (induct xs rule: max_list_rats_with_index.induct)
  case (2 n1 d1 i1 n2 d2 i2 xs)
  have "1 \<le> length ((if n1 * d2 \<le> n2 * d1 then (n2, d2, i2) else (n1, d1, i1)) # xs)" by simp
  moreover have "max_list_rats_with_index ((if n1 * d2 \<le> n2 * d1 then (n2, d2, i2) else (n1, d1, i1)) # xs)
              = (nm, dm, im)" using 2 by simp
  moreover have "(if n1 * d2 \<le> n2 * d1 then (n2, d2, i2) else (n1, d1, i1)) \<in>
        set ((n1, d1, i1) # (n2, d2, i2) # xs)" by simp
  moreover then have "set ((if n1 * d2 \<le> n2 * d1 then (n2, d2, i2) else (n1, d1, i1)) # xs) \<subseteq>
        set ((n1, d1, i1) # (n2, d2, i2) # xs)" by auto
  ultimately show ?case using 2(1) by auto
qed auto

lemma max_list_rats_with_index: assumes "\<And> n d i. (n,d,i) \<in> set xs \<Longrightarrow> d > 0" 
  and max: "max_list_rats_with_index xs = (nm, dm, im)" 
  and "(n,d,i) \<in> set xs" 
shows "rat_of_int n / of_int d \<le> of_int nm / of_int dm" 
  using assms
proof (induct xs arbitrary: n d i rule: max_list_rats_with_index.induct)
  case (2 n1 d1 i1 n2 d2 i2 xs n d i)
  let ?r = "rat_of_int" 
  from 2(2) have "d1 > 0" "d2 > 0" by auto
  hence d: "?r d1 > 0" "?r d2 > 0" by auto
  have "(n1 * d2 \<le> n2 * d1) = (?r n1 * ?r d2 \<le> ?r n2 * ?r d1)" 
    unfolding of_int_mult[symmetric] by presburger
  also have "\<dots> = (?r n1 / ?r d1 \<le> ?r n2 / ?r d2)" using d 
    by (smt divide_strict_right_mono leD le_less_linear mult.commute nonzero_mult_div_cancel_left 
        not_less_iff_gr_or_eq times_divide_eq_right)
  finally have id: "(n1 * d2 \<le> n2 * d1) = (?r n1 / ?r d1 \<le> ?r n2 / ?r d2)" .
  obtain n' d' i' where new: "(if n1 * d2 \<le> n2 * d1 then (n2, d2, i2) else (n1, d1, i1)) = (n',d',i')" 
    by force  
  have nd': "(n',d',i') \<in> {(n1,d1,i1), (n2, d2, i2)}" using new[symmetric] by auto
  from 2(3) have res: "max_list_rats_with_index ((n',d',i') # xs) = (nm, dm, im)" using new by auto
  note 2 = 2[unfolded new]
  show ?case 
  proof (cases "(n,d,i) \<in> set xs")
    case True
    show ?thesis 
      by (rule 2(1)[of n d, OF 2(2) res], insert True nd', force+)
  next
    case False
    with 2(4) have "n = n1 \<and> d = d1 \<or> n = n2 \<and> d = d2" by auto
    hence "?r n / ?r d \<le> ?r n' / ?r d'" using new[unfolded id]
      by (metis linear prod.inject)
    also have "?r n' / ?r d' \<le> ?r nm / ?r dm" 
      by (rule 2(1)[of n' d', OF 2(2) res], insert nd', force+)
    finally show ?thesis .
  qed
qed auto

context LLL
begin

lemma log_base: "log_base \<ge> 2" unfolding log_base_def by auto

definition LLL_invariant_weak' :: "nat \<Rightarrow> int vec list \<Rightarrow> bool" where 
  "LLL_invariant_weak' i fs = ( 
    gs.lin_indpt_list (RAT fs) \<and> 
    lattice_of fs = L \<and>
    weakly_reduced fs i \<and>
    i \<le> m \<and> 
    length fs = m    
  )" 

lemma LLL_invD_weak: assumes "LLL_invariant_weak' i fs"
  shows 
  "lin_indep fs" 
  "length (RAT fs) = m" 
  "set fs \<subseteq> carrier_vec n"
  "\<And> i. i < m \<Longrightarrow> fs ! i \<in> carrier_vec n" 
  "\<And> i. i < m \<Longrightarrow> gso fs i \<in> carrier_vec n" 
  "length fs = m"
  "lattice_of fs = L" 
  "weakly_reduced fs i"
  "i \<le> m"
proof (atomize (full), goal_cases)
  case 1
  interpret gs': gram_schmidt_fs_lin_indpt n "RAT fs"
    by (standard) (use assms LLL_invariant_weak'_def gs.lin_indpt_list_def in auto)
  show ?case
    using assms gs'.fs_carrier gs'.f_carrier gs'.gso_carrier
    by (auto simp add: LLL_invariant_weak'_def gram_schmidt_fs.reduced_def)
qed

lemma LLL_invI_weak: assumes  
  "set fs \<subseteq> carrier_vec n"
  "length fs = m"
  "lattice_of fs = L" 
  "i \<le> m"
  "lin_indep fs" 
  "weakly_reduced fs i" 
shows "LLL_invariant_weak' i fs" 
  unfolding LLL_invariant_weak'_def Let_def using assms by auto

lemma LLL_invw'_imp_w: "LLL_invariant_weak' i fs \<Longrightarrow> LLL_invariant_weak fs" 
  unfolding LLL_invariant_weak'_def LLL_invariant_weak_def by auto
  
lemma basis_reduction_add_row_weak: 
  assumes Linvw: "LLL_invariant_weak' i fs"
  and i: "i < m"  and j: "j < i" 
  and fs': "fs' = fs[ i := fs ! i - c \<cdot>\<^sub>v fs ! j]" 
shows "LLL_invariant_weak' i fs'"
  "g_bnd B fs \<Longrightarrow> g_bnd B fs'" 
proof (atomize(full), goal_cases)
  case 1
  note Linv = LLL_invw'_imp_w[OF Linvw]
  note main = basis_reduction_add_row_main[OF Linv i j fs']
  have bnd: "g_bnd B fs \<Longrightarrow> g_bnd B fs'" using main(6) unfolding g_bnd_def by auto
  note new = LLL_inv_wD[OF main(1)]
  note old = LLL_invD_weak[OF Linvw]
  have red: "weakly_reduced fs' i" using \<open>weakly_reduced fs i\<close> main(6) \<open>i < m\<close>
    unfolding gram_schmidt_fs.weakly_reduced_def by auto
  have inv: "LLL_invariant_weak' i fs'" using LLL_inv_wD[OF main(1)] \<open>i < m\<close>
    by (intro LLL_invI_weak, auto intro: red)
  show ?case using inv red main bnd by auto
qed

lemma LLL_inv_weak_m_impl_i:
  assumes inv: "LLL_invariant_weak' m fs"
  and i: "i \<le> m"
shows "LLL_invariant_weak' i fs"
proof -
  have "weakly_reduced fs i" using LLL_invD_weak(8)[OF inv]
    by (meson assms(2) gram_schmidt_fs.weakly_reduced_def le_trans less_imp_le_nat linorder_not_less)
  then show ?thesis
    using LLL_invI_weak[of fs i, OF LLL_invD_weak(3,6,7)[OF inv] _ LLL_invD_weak(1)[OF inv]] 
      LLL_invD_weak(2,4,5,8-)[OF inv] i by simp
qed
 
definition mod_invariant where 
  "mod_invariant b p first = (b \<le> rat_of_int (p - 1)^2 / (rat_of_nat (bound_number first) + 3)
     \<and> (\<exists> e. p = log_base ^ e))"  

lemma compute_mod_of_max_gso_norm: assumes mn: "mn \<ge> 0"
  and m: "m = 0 \<Longrightarrow> mn = 0" 
  and p: "p = compute_mod_of_max_gso_norm first mn" 
shows  
  "p > 1" 
  "mod_invariant mn p first" 
proof -
  let ?m = "bound_number first" 
  define p' where "p' = root_rat_ceiling 2 (mn * (rat_of_nat ?m + 3)) + 1" 
  define p'' where "p'' = max 2 p'" 
  define q where "q = real_of_rat (mn * (rat_of_nat ?m + 3))" 
  have *: "-1 < (0 :: real)" by simp
  also have "0 \<le> root 2 (real_of_rat (mn * (rat_of_nat ?m + 3)))" using mn by auto
  finally have "p' \<ge> 0 + 1" unfolding p'_def
    by (intro plus_left_mono, simp)
  hence p': "p' > 0" by auto
  have p'': "p'' > 1" unfolding p''_def by auto
  have pp'': "p \<ge> p''" unfolding compute_mod_of_max_gso_norm_def p  p'_def[symmetric] p''_def[symmetric]
    using log_base p'' log_ceiling_sound by auto
  hence pp': "p \<ge> p'" unfolding p''_def by auto    
  show "p > 1" using pp'' p'' by auto

  have q0: "q \<ge> 0" unfolding q_def using mn m by auto
  have "(mn \<le> rat_of_int (p' - 1)^2 / (rat_of_nat ?m + 3)) 
    = (real_of_rat mn \<le> real_of_rat (rat_of_int (p' - 1)^2 / (rat_of_nat ?m + 3)))" using of_rat_less_eq by blast
  also have "\<dots> = (real_of_rat mn \<le> real_of_rat (rat_of_int (p' - 1)^2) / real_of_rat (rat_of_nat ?m + 3))" by (simp add: of_rat_divide)
  also have "\<dots> = (real_of_rat mn \<le> ((real_of_int (p' - 1))^2) / real_of_rat (rat_of_nat ?m + 3))" 
    by (metis of_rat_of_int_eq of_rat_power)
  also have "\<dots> = (real_of_rat mn \<le> (real_of_int \<lceil>sqrt q\<rceil>)^2 / real_of_rat (rat_of_nat ?m + 3))" 
    unfolding p'_def sqrt_def q_def by simp
  also have "\<dots>" 
  proof -
    have "real_of_rat mn \<le> q / real_of_rat (rat_of_nat ?m + 3)" unfolding q_def using m
      by (auto simp: of_rat_mult)
    also have "\<dots> \<le> (real_of_int \<lceil>sqrt q\<rceil>)^2 / real_of_rat (rat_of_nat ?m + 3)" 
    proof (rule divide_right_mono)
      have "q = (sqrt q)^2" using q0 by simp
      also have "\<dots> \<le> (real_of_int \<lceil>sqrt q\<rceil>)^2" 
        by (rule power_mono, auto simp: q0)
      finally show "q \<le> (real_of_int \<lceil>sqrt q\<rceil>)^2" .
    qed auto
    finally show ?thesis .
  qed
  finally have "mn \<le> rat_of_int (p' - 1)^2 / (rat_of_nat ?m + 3)" .
  also have "\<dots> \<le> rat_of_int (p - 1)^2 / (rat_of_nat ?m + 3)"
    unfolding power2_eq_square
    by (intro divide_right_mono mult_mono, insert p' pp', auto) 
  finally have "mn \<le> rat_of_int (p - 1)^2 / (rat_of_nat ?m + 3)" .
  moreover have "\<exists> e. p = log_base ^ e" unfolding p compute_mod_of_max_gso_norm_def by auto
  ultimately show "mod_invariant mn p first" unfolding mod_invariant_def by auto
qed

lemma g_bnd_mode_cong: assumes "\<And> i. i < m \<Longrightarrow> gso fs i = gso fs' i"
  shows "g_bnd_mode first b fs = g_bnd_mode first b fs'"
  using assms unfolding g_bnd_mode_def g_bnd_def by auto

definition LLL_invariant_mod :: "int vec list \<Rightarrow> int vec list \<Rightarrow> int mat \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> bool" where 
  "LLL_invariant_mod fs mfs dmu p first b i = ( 
    length fs = m \<and>
    length mfs = m \<and>
    i \<le> m \<and>
    lattice_of fs = L \<and>
    gs.lin_indpt_list (RAT fs) \<and>
    weakly_reduced fs i \<and>
    (map (map_vec (\<lambda>x. x symmod p)) fs = mfs) \<and>
    (\<forall>i' < m. \<forall> j' < i'. \<bar>d\<mu> fs i' j'\<bar> < p * d fs j' * d fs (Suc j')) \<and>
    (\<forall>i' < m. \<forall>j' < m. d\<mu> fs i' j' = dmu $$ (i',j')) \<and>
    p > 1 \<and>
    g_bnd_mode first b fs \<and>
    mod_invariant b p first
)"

lemma LLL_invD_mod: assumes "LLL_invariant_mod fs mfs dmu p first b i"
shows 
  "length mfs = m"
  "i \<le> m"
  "length fs = m"
  "lattice_of fs = L"
  "gs.lin_indpt_list (RAT fs)"
  "weakly_reduced fs i"
  "(map (map_vec (\<lambda>x. x symmod p)) fs = mfs)"
  "(\<forall>i' < m. \<forall>j' < i'. \<bar>d\<mu> fs i' j'\<bar> < p * d fs j' * d fs (Suc j'))"
  "(\<forall>i' < m. \<forall>j' < m. d\<mu> fs i' j' = dmu $$ (i',j'))"
  "\<And> i. i < m \<Longrightarrow> fs ! i \<in> carrier_vec n" 
  "set fs \<subseteq> carrier_vec n"
  "\<And> i. i < m \<Longrightarrow> gso fs i \<in> carrier_vec n" 
  "\<And> i. i < m \<Longrightarrow> mfs ! i \<in> carrier_vec n"
  "set mfs \<subseteq> carrier_vec n"
  "p > 1"
  "g_bnd_mode first b fs"
  "mod_invariant b p first"
proof (atomize (full), goal_cases)
  case 1
  interpret gs': gram_schmidt_fs_lin_indpt n "RAT fs"
    using assms LLL_invariant_mod_def gs.lin_indpt_list_def 
    by (meson gram_schmidt_fs_Rn.intro gram_schmidt_fs_lin_indpt.intro gram_schmidt_fs_lin_indpt_axioms.intro)
  have allfs: "\<forall>i < m. fs ! i \<in> carrier_vec n" using assms gs'.f_carrier 
    by (simp add: LLL.LLL_invariant_mod_def)
  then have setfs: "set fs \<subseteq> carrier_vec n" by (metis LLL_invariant_mod_def assms in_set_conv_nth subsetI)
  have allgso: "(\<forall>i < m. gso fs i \<in> carrier_vec n)" using assms gs'.gso_carrier
    by (simp add: LLL.LLL_invariant_mod_def)
  show ?case
    using assms gs'.fs_carrier gs'.f_carrier gs'.gso_carrier allfs allgso 
      LLL_invariant_mod_def gram_schmidt_fs.reduced_def in_set_conv_nth setfs by fastforce
qed

lemma LLL_invI_mod: assumes 
  "length mfs = m"
  "i \<le> m"
  "length fs = m"
  "lattice_of fs = L"
  "gs.lin_indpt_list (RAT fs)"
  "weakly_reduced fs i"
  "map (map_vec (\<lambda>x. x symmod p)) fs = mfs"
  "(\<forall>i' < m. \<forall>j' < i'. \<bar>d\<mu> fs i' j'\<bar> < p * d fs j' * d fs (Suc j'))"
  "(\<forall>i' < m. \<forall>j' < m. d\<mu> fs i' j' = dmu $$ (i',j'))"
  "p > 1"
  "g_bnd_mode first b fs"
  "mod_invariant b p first"
shows "LLL_invariant_mod fs mfs dmu p first b i" 
  unfolding LLL_invariant_mod_def using assms by blast

definition LLL_invariant_mod_weak :: "int vec list \<Rightarrow> int vec list \<Rightarrow> int mat \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> rat \<Rightarrow> bool" where 
  "LLL_invariant_mod_weak fs mfs dmu p first b = ( 
    length fs = m \<and>
    length mfs = m \<and>
    lattice_of fs = L \<and>
    gs.lin_indpt_list (RAT fs) \<and>
    (map (map_vec (\<lambda>x. x symmod p)) fs = mfs) \<and>
    (\<forall>i' < m. \<forall> j' < i'. \<bar>d\<mu> fs i' j'\<bar> < p * d fs j' * d fs (Suc j')) \<and>
    (\<forall>i' < m. \<forall>j' < m. d\<mu> fs i' j' = dmu $$ (i',j')) \<and>
    p > 1 \<and>
    g_bnd_mode first b fs \<and>
    mod_invariant b p first
)"

lemma LLL_invD_modw: assumes "LLL_invariant_mod_weak fs mfs dmu p first b"
shows 
  "length mfs = m"
  "length fs = m"
  "lattice_of fs = L"
  "gs.lin_indpt_list (RAT fs)"
  "(map (map_vec (\<lambda>x. x symmod p)) fs = mfs)"
  "(\<forall>i' < m. \<forall>j' < i'. \<bar>d\<mu> fs i' j'\<bar> < p * d fs j' * d fs (Suc j'))"
  "(\<forall>i' < m. \<forall>j' < m. d\<mu> fs i' j' = dmu $$ (i',j'))"
  "\<And> i. i < m \<Longrightarrow> fs ! i \<in> carrier_vec n" 
  "set fs \<subseteq> carrier_vec n"
  "\<And> i. i < m \<Longrightarrow> gso fs i \<in> carrier_vec n" 
  "\<And> i. i < m \<Longrightarrow> mfs ! i \<in> carrier_vec n"
  "set mfs \<subseteq> carrier_vec n"
  "p > 1"
  "g_bnd_mode first b fs"
  "mod_invariant b p first"
proof (atomize (full), goal_cases)
  case 1
  interpret gs': gram_schmidt_fs_lin_indpt n "RAT fs"
    using assms LLL_invariant_mod_weak_def gs.lin_indpt_list_def 
    by (meson gram_schmidt_fs_Rn.intro gram_schmidt_fs_lin_indpt.intro gram_schmidt_fs_lin_indpt_axioms.intro)
  have allfs: "\<forall>i < m. fs ! i \<in> carrier_vec n" using assms gs'.f_carrier 
    by (simp add: LLL.LLL_invariant_mod_weak_def)
  then have setfs: "set fs \<subseteq> carrier_vec n" by (metis LLL_invariant_mod_weak_def assms in_set_conv_nth subsetI)
  have allgso: "(\<forall>i < m. gso fs i \<in> carrier_vec n)" using assms gs'.gso_carrier
    by (simp add: LLL.LLL_invariant_mod_weak_def)
  show ?case
    using assms gs'.fs_carrier gs'.f_carrier gs'.gso_carrier allfs allgso 
      LLL_invariant_mod_weak_def gram_schmidt_fs.reduced_def in_set_conv_nth setfs by fastforce
qed

lemma LLL_invI_modw: assumes 
  "length mfs = m"
  "length fs = m"
  "lattice_of fs = L"
  "gs.lin_indpt_list (RAT fs)"
  "map (map_vec (\<lambda>x. x symmod p)) fs = mfs"
  "(\<forall>i' < m. \<forall>j' < i'. \<bar>d\<mu> fs i' j'\<bar> < p * d fs j' * d fs (Suc j'))"
  "(\<forall>i' < m. \<forall>j' < m. d\<mu> fs i' j' = dmu $$ (i',j'))"
  "p > 1"
  "g_bnd_mode first b fs"
  "mod_invariant b p first"
shows "LLL_invariant_mod_weak fs mfs dmu p first b" 
  unfolding LLL_invariant_mod_weak_def using assms by blast

lemma dd\<mu>:
  assumes i: "i < m"
  shows "d fs (Suc i) = d\<mu> fs i i"
proof-
  have "\<mu> fs i i = 1" using i by (simp add: gram_schmidt_fs.\<mu>.simps)
  then show ?thesis using d\<mu>_def by simp
qed

lemma d_of_main: assumes "(\<forall>i' < m. d\<mu> fs i' i' = dmu $$ (i',i'))"
  and "i \<le> m"
shows "d_of dmu i = d fs i" 
proof (cases "i = 0")
  case False
  with assms have "i - 1 < m" by auto
  from assms(1)[rule_format, OF this] dd\<mu>[OF this, of fs] False
  show ?thesis by (simp add: d_of_def)
next
  case True
  thus ?thesis unfolding d_of_def True d_def by simp
qed

lemma d_of: assumes inv: "LLL_invariant_mod fs mfs dmu p b first j"
  and "i \<le> m" 
shows "d_of dmu i = d fs i" 
  by (rule d_of_main[OF _ assms(2)], insert LLL_invD_mod(9)[OF inv], auto)

lemma d_of_weak: assumes inv: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and "i \<le> m" 
shows "d_of dmu i = d fs i" 
  by (rule d_of_main[OF _ assms(2)], insert LLL_invD_modw(7)[OF inv], auto)

lemma compute_max_gso_norm: assumes dmu: "(\<forall>i' < m. d\<mu> fs i' i' = dmu $$ (i',i'))" 
  and Linv: "LLL_invariant_weak fs" 
shows "g_bnd_mode first (fst (compute_max_gso_norm first dmu)) fs" 
  "fst (compute_max_gso_norm first dmu) \<ge> 0" 
  "m = 0 \<Longrightarrow> fst (compute_max_gso_norm first dmu) = 0" 
proof -
  show gbnd: "g_bnd_mode first (fst (compute_max_gso_norm first dmu)) fs" 
  proof (cases "first \<and> m \<noteq> 0")
    case False
    have "?thesis = (g_bnd (fst (compute_max_gso_norm first dmu)) fs)" unfolding g_bnd_mode_def using False by auto
    also have \<dots> unfolding g_bnd_def
    proof (intro allI impI)
      fix i
      assume i: "i < m" 
      have id: "(if first then 1 else m) = m" using False i by auto
      define list where "list = map (\<lambda> i. (d_of dmu (Suc i), d_of dmu i, i)) [0 ..< m ]" 
      obtain num denom j where ml: "max_list_rats_with_index list = (num, denom, j)" 
        by (metis prod_cases3)
      have dpos: "d fs i > 0" using LLL_d_pos[OF Linv, of i]  i by auto
      have pos: "(n, d, i) \<in> set list \<Longrightarrow> 0 < d" for n d i 
        using LLL_d_pos[OF Linv] unfolding list_def using d_of_main[OF dmu] by auto
      from i have "list ! i \<in> set list" using i unfolding list_def by auto
      also have "list ! i = (d_of dmu (Suc i), d_of dmu i, i)" unfolding list_def using i by auto
      also have "\<dots> = (d fs (Suc i), d fs i, i)" using d_of_main[OF dmu] i by auto
      finally have "(d fs (Suc i), d fs i, i) \<in> set list" . 
      from max_list_rats_with_index[OF pos ml this] 
      have "of_int (d fs (Suc i)) / of_int (d fs i) \<le> fst (compute_max_gso_norm first dmu)" 
        unfolding compute_max_gso_norm_def list_def[symmetric] ml id split using i by auto
      also have "of_int (d fs (Suc i)) / of_int (d fs i) = sq_norm (gso fs i)" 
        using LLL_d_Suc[OF Linv i] dpos by auto
      finally show "sq_norm (gso fs i) \<le> fst (compute_max_gso_norm first dmu)" .
    qed
    finally show ?thesis .
  next
    case True
    thus ?thesis unfolding g_bnd_mode_def compute_max_gso_norm_def using d_of_main[OF dmu] 
      LLL_d_Suc[OF Linv, of 0] LLL_d_pos[OF Linv, of 0] LLL_d_pos[OF Linv, of 1] by auto
  qed
  show "fst (compute_max_gso_norm first dmu) \<ge> 0" 
  proof (cases "m = 0")
    case True
    thus ?thesis unfolding compute_max_gso_norm_def by simp
  next
    case False
    hence 0: "0 < m" by simp
    have "0 \<le> sq_norm (gso fs 0)" by blast
    also have "\<dots> \<le> fst (compute_max_gso_norm first dmu)" 
      using gbnd[unfolded g_bnd_mode_def g_bnd_def] using 0 by metis
    finally show ?thesis .
  qed
qed (auto simp: LLL.compute_max_gso_norm_def)


lemma increase_i_mod:
  assumes Linv: "LLL_invariant_mod fs mfs dmu p first b i"
  and i: "i < m" 
  and red_i: "i \<noteq> 0 \<Longrightarrow> sq_norm (gso fs (i - 1)) \<le> \<alpha> * sq_norm (gso fs i)"
shows "LLL_invariant_mod fs mfs dmu p first b (Suc i)" "LLL_measure i fs > LLL_measure (Suc i) fs" 
proof -
  note inv = LLL_invD_mod[OF Linv]
  from inv have red: "weakly_reduced fs i"  by (auto)
  from red red_i i have red: "weakly_reduced fs (Suc i)" 
    unfolding gram_schmidt_fs.weakly_reduced_def
    by (intro allI impI, rename_tac ii, case_tac "Suc ii = i", auto)
  show "LLL_invariant_mod fs mfs dmu p first b (Suc i)"
    by (intro LLL_invI_mod, insert inv red i, auto)
  show "LLL_measure i fs > LLL_measure (Suc i) fs" unfolding LLL_measure_def using i by auto
qed

lemma basis_reduction_mod_add_row_main:
  assumes Linvmw: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and i: "i < m"  and j: "j < i" 
  and c: "c = round (\<mu> fs i j)"
  and mfs': "mfs' = mfs[ i := (map_vec (\<lambda> x. x symmod p)) (mfs ! i - c \<cdot>\<^sub>v mfs ! j)]"
  and dmu': "dmu' = mat m m (\<lambda>(i',j'). (if (i' = i \<and> j' \<le> j) 
        then (if j'=j then (dmu $$ (i,j') - c * dmu $$ (j,j')) 
              else (dmu $$ (i,j') - c * dmu $$ (j,j')) 
                    symmod (p * (d_of dmu j') * (d_of dmu (Suc j'))))
        else (dmu $$ (i',j'))))"
shows "(\<exists>fs'. LLL_invariant_mod_weak fs' mfs' dmu' p first b \<and>
        LLL_measure i fs' = LLL_measure i fs
        \<and> (\<mu>_small_row i fs (Suc j) \<longrightarrow> \<mu>_small_row i fs' j) 
        \<and> (\<forall>k < m. gso fs' k = gso fs k)
        \<and> (\<forall>ii \<le> m. d fs' ii = d fs ii)
        \<and> \<bar>\<mu> fs' i j\<bar> \<le> 1 / 2
        \<and> (\<forall>i' j'. i' < i \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs' i' j' = \<mu> fs i' j')
        \<and> (LLL_invariant_mod fs mfs dmu p first b i \<longrightarrow> LLL_invariant_mod fs' mfs' dmu' p first b i))"
proof -
  define fs' where "fs' = fs[ i := fs ! i - c \<cdot>\<^sub>v fs ! j]"
  from LLL_invD_modw[OF Linvmw] have gbnd: "g_bnd_mode first b fs" and p1: "p > 1" and pgtz: "p > 0" by auto
  have Linvww: "LLL_invariant_weak fs" using LLL_invD_modw[OF Linvmw] LLL_invariant_weak_def by simp
  have 
    Linvw': "LLL_invariant_weak fs'" and
    01: "c = round (\<mu> fs i j) \<Longrightarrow> \<mu>_small_row i fs (Suc j) \<Longrightarrow> \<mu>_small_row i fs' j" and
    02: "LLL_measure i fs' = LLL_measure i fs" and
    03: "\<And> i. i < m \<Longrightarrow> gso fs' i = gso fs i" and
    04: "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> 
      \<mu> fs' i' j' = (if i' = i \<and> j' \<le> j then \<mu> fs i j' - of_int c * \<mu> fs j j' else \<mu> fs i' j')" and
    05: "\<And> ii. ii \<le> m \<Longrightarrow> d fs' ii = d fs ii" and 
    06: "\<bar>\<mu> fs' i j\<bar> \<le> 1 / 2" and
    061: "(\<forall>i' j'. i' < i \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs i' j' = \<mu> fs' i' j')"
    using basis_reduction_add_row_main[OF Linvww i j fs'_def] c i by auto
  have 07: "lin_indep fs'" and 
    08: "length fs' = m" and 
    09: "lattice_of fs' = L" using LLL_inv_wD Linvw' by auto
  have 091: "fs_int_indpt n fs'" using 07 using Gram_Schmidt_2.fs_int_indpt.intro by simp
  define I where "I = {(i',j'). i' = i \<and> j' < j}"
  have 10: "I \<subseteq> {(i',j'). i' < m \<and> j' < i'}" "(i,j)\<notin> I" "\<forall>j' \<ge> j. (i,j') \<notin> I" using I_def i j by auto
  obtain fs'' where 
    11: "lattice_of fs'' = L" and
    12: "map (map_vec (\<lambda> x. x symmod p)) fs'' = map (map_vec (\<lambda> x. x symmod p)) fs'" and
    13: "lin_indep fs''" and
    14: "length fs'' = m" and
    15: "(\<forall> k < m. gso fs'' k = gso fs' k)" and
    16: "(\<forall> k \<le> m. d fs'' k = d fs' k)" and
    17: "(\<forall> i' < m. \<forall> j' < m. d\<mu> fs'' i' j' = 
      (if (i',j') \<in> I then d\<mu> fs' i' j' symmod (p * d fs' j' * d fs' (Suc j')) else d\<mu> fs' i' j'))"
    using mod_finite_set[OF 07 08 10(1) 09 pgtz] by blast
  have 171: "(\<forall>i' j'. i' < i \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs'' i' j' = \<mu> fs' i' j')"
  proof -
    {
      fix i' j'
      assume i'j': "i' < i" "j' \<le> i'"
      have "rat_of_int (d\<mu> fs'' i' j') = rat_of_int (d\<mu> fs' i' j')" using "17" I_def i i'j' by auto
      then have "rat_of_int (int_of_rat (rat_of_int (d fs'' (Suc j')) * \<mu> fs'' i' j')) = 
        rat_of_int (int_of_rat (rat_of_int (d fs' (Suc j')) * \<mu> fs' i' j'))"
        using d\<mu>_def i'j' j by auto
      then have "rat_of_int (d fs'' (Suc j')) * \<mu> fs'' i' j' = 
        rat_of_int (d fs' (Suc j')) * \<mu> fs' i' j'" 
        by (smt "08" "091" "13" "14" d_def dual_order.strict_trans fs_int.d_def 
            fs_int_indpt.fs_int_mu_d_Z fs_int_indpt.intro i i'j'(1) i'j'(2) int_of_rat(2))
      then have "\<mu> fs'' i' j' = \<mu> fs' i' j'" by (smt "16" 
            LLL_d_pos[OF Linvw'] Suc_leI int_of_rat(1)
            dual_order.strict_trans fs'_def i i'j' j 
            le_neq_implies_less nonzero_mult_div_cancel_left of_int_hom.hom_zero)
    }
    then show ?thesis by simp
  qed
  then have 172: "(\<forall>i' j'. i' < i \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs'' i' j' = \<mu> fs i' j')" using 061 by simp (* goal *)
  have 18: "LLL_measure i fs'' = LLL_measure i fs'" using 16 LLL_measure_def logD_def D_def by simp
  have 19: "(\<forall>k < m. gso fs'' k = gso fs k)" using 03 15 by simp
  have "\<forall>j' \<in> {j..(m-1)}. j' < m" using j i by auto
  then have 20: "\<forall>j' \<in> {j..(m-1)}. d\<mu> fs'' i j' = d\<mu> fs' i j'" 
    using 10(3) 17 Suc_lessD less_trans_Suc by (meson atLeastAtMost_iff i)
  have 21: "\<forall>j' \<in> {j..(m-1)}. \<mu> fs'' i j' = \<mu> fs' i j'" 
  proof -
    {
      fix j'
      assume j': "j' \<in> {j..(m-1)}"
      define \<mu>'' :: rat where "\<mu>'' = \<mu> fs'' i j'"
      define \<mu>' :: rat where "\<mu>' = \<mu> fs' i j'"
      have "rat_of_int (d\<mu> fs'' i j') = rat_of_int (d\<mu> fs' i j')" using 20 j' by simp
      moreover have "j' < length fs'" using i j' 08 by auto
      ultimately have "rat_of_int (d fs' (Suc j')) * gram_schmidt_fs.\<mu> n (map of_int_hom.vec_hom fs') i j'
        = rat_of_int (d fs'' (Suc j')) * gram_schmidt_fs.\<mu> n (map of_int_hom.vec_hom fs'') i j'"
        using 20 08 091 13 14 fs_int_indpt.d\<mu>_def fs_int.d_def fs_int_indpt.d\<mu> d\<mu>_def d_def i fs_int_indpt.intro j'
        by metis
      then have "rat_of_int (d fs' (Suc j')) * \<mu>'' = rat_of_int (d fs' (Suc j')) * \<mu>'" 
        using 16 i j' \<mu>'_def \<mu>''_def unfolding d\<mu>_def by auto
      moreover have "0 < d fs' (Suc j')" using LLL_d_pos[OF Linvw', of "Suc j'"] i j' by auto
      ultimately have "\<mu> fs'' i j' = \<mu> fs' i j'" using \<mu>'_def \<mu>''_def by simp
    }
    then show ?thesis by simp
  qed
  then have 22: "\<mu> fs'' i j = \<mu> fs' i j" using i j by simp
  then have 23: "\<bar>\<mu> fs'' i j\<bar> \<le> 1 / 2" using 06 by simp (* goal *)
  have 24: "LLL_measure i fs'' = LLL_measure i fs" using 02 18 by simp (* goal *)
  have 25: "(\<forall> k \<le> m. d fs'' k = d fs k)" using 16 05 by simp (* goal *)
  have 26: "(\<forall> k < m. gso fs'' k = gso fs k)" using 15 03 by simp (* goal *)
  have 27: "\<mu>_small_row i fs (Suc j) \<Longrightarrow> \<mu>_small_row i fs'' j"
    using 21 01 \<mu>_small_row_def i j c by auto (* goal *)
  have 28: "length fs = m" "length mfs = m" using LLL_invD_modw[OF Linvmw] by auto
  have 29: "map (map_vec (\<lambda>x. x symmod p)) fs = mfs" using assms LLL_invD_modw by simp
  have 30: "\<And> i. i < m \<Longrightarrow> fs ! i \<in> carrier_vec n" "\<And> i. i < m \<Longrightarrow> mfs ! i \<in> carrier_vec n"
    using LLL_invD_modw[OF Linvmw] by auto
  have 31: "\<And> i. i < m \<Longrightarrow> fs' ! i \<in> carrier_vec n" using fs'_def 30(1) 
    using "08" "091" fs_int_indpt.f_carrier by blast
  have 32: "\<And> i. i < m \<Longrightarrow> mfs' ! i \<in> carrier_vec n" unfolding mfs' using 30(2) 28(2) 
    by (metis (no_types, lifting) Suc_lessD j less_trans_Suc map_carrier_vec minus_carrier_vec 
        nth_list_update_eq nth_list_update_neq smult_closed)
  have 33: "length mfs' = m" using 28(2) mfs' by simp (* invariant goal *)
  then have 34: "map (map_vec (\<lambda>x. x symmod p)) fs' = mfs'"
  proof -
    {
      fix i' j'
      have j2: "j < m" using j i by auto
      assume i': "i' < m"
      assume j': "j' < n"
      then have fsij: "(fs ! i' $ j') symmod p = mfs ! i' $ j'" using 30 i' j' 28 29 by fastforce
      have "mfs' ! i $ j' = (mfs ! i $ j'- (c \<cdot>\<^sub>v mfs ! j) $ j') symmod p"
        unfolding mfs' using 30(2) j' 28 j2 
        by (metis (no_types, lifting) carrier_vecD i index_map_vec(1) index_minus_vec(1) 
            index_minus_vec(2) index_smult_vec(2) nth_list_update_eq)
      then have mfs'ij: "mfs' ! i $ j' = (mfs ! i $ j'- c * mfs ! j $ j') symmod p" 
        unfolding mfs' using 30(2) i' j' 28 j2 by fastforce
      have "(fs' ! i' $ j') symmod p = mfs' ! i' $ j'"
      proof(cases "i' = i")
        case True
        show ?thesis using fs'_def mfs' True 28 fsij 
        proof -
          have "fs' ! i' $ j' = (fs ! i' - c \<cdot>\<^sub>v fs ! j) $ j'" using fs'_def True i' j' 28(1) by simp
          also have "\<dots> = fs ! i' $ j' - (c \<cdot>\<^sub>v fs ! j) $ j'" using i' j' 30(1)
            by (metis Suc_lessD carrier_vecD i index_minus_vec(1) index_smult_vec(2) j less_trans_Suc)
          finally have "fs' ! i' $ j' = fs ! i' $ j' - (c \<cdot>\<^sub>v fs ! j) $ j'" by auto
          then have "(fs' ! i' $ j') symmod p = (fs ! i' $ j' - (c \<cdot>\<^sub>v fs ! j) $ j') symmod p" by auto
          also have "\<dots> = ((fs ! i' $ j') symmod p - ((c \<cdot>\<^sub>v fs ! j) $ j') symmod p) symmod p"
            by (simp add: sym_mod_diff_eq)
          also have "(c \<cdot>\<^sub>v fs ! j) $ j' = c * (fs ! j $ j')" 
            using i' j' True 28 30(1) j
            by (metis Suc_lessD carrier_vecD index_smult_vec(1) less_trans_Suc)
          also have "((fs ! i' $ j') symmod p - (c * (fs ! j $ j')) symmod p) symmod p = 
            ((fs ! i' $ j') symmod p - c * ((fs ! j $ j') symmod p)) symmod p" 
            using i' j' True 28 30(1) j by (metis sym_mod_diff_right_eq sym_mod_mult_right_eq)
          also have "((fs ! j $ j') symmod p) = mfs ! j $ j'" using 30 i' j' 28 29 j2 by fastforce
          also have "((fs ! i' $ j') symmod p - c * mfs ! j $ j') symmod p = 
            (mfs ! i' $ j' - c * mfs ! j $ j') symmod p" using fsij by simp
          finally show ?thesis using mfs'ij by (simp add: True)
        qed
      next
        case False
        show ?thesis using fs'_def mfs' False 28 fsij by simp
      qed
    }
    then have "\<forall>i' < m. (map_vec (\<lambda>x. x symmod p)) (fs' ! i') = mfs' ! i'"
      using 31 32 33 08 by fastforce
    then show ?thesis using 31 32 33 08 by (simp add: map_nth_eq_conv)
  qed
  then have 35: "map (map_vec (\<lambda>x. x symmod p)) fs'' = mfs'" using 12 by simp (* invariant req. *)
  have 36: "lin_indep fs''"  using 13 by simp (* invariant req. *)
  have Linvw'': "LLL_invariant_weak fs''" using LLL_invariant_weak_def 11 13 14 by simp
  have 39: "(\<forall>i' < m. \<forall>j' < i'. \<bar>d\<mu> fs'' i' j'\<bar> < p * d fs'' j' * d fs'' (Suc j'))" (* invariant req. *)
  proof -
    {
      fix i' j'
      assume i': "i' < m"
      assume j': "j' < i'"
      define pdd where "pdd = (p * d fs'' j' * d fs'' (Suc j'))"
      then have pddgtz: "pdd > 0" 
        using pgtz j' LLL_d_pos[OF Linvw', of "Suc j'"] LLL_d_pos[OF Linvw', of j'] j' i' 16 by simp
      have "\<bar>d\<mu> fs'' i' j'\<bar> < p * d fs'' j' * d fs'' (Suc j')"
      proof(cases "i' = i")
        case i'i: True
        then show ?thesis
        proof (cases "j' < j")
          case True
          then have eq'': "d\<mu> fs'' i' j' = d\<mu> fs' i' j' symmod (p * d fs'' j' * d fs'' (Suc j'))"
            using 16 17 10 I_def True i' j' i'i by simp
          have "0 < pdd" using pddgtz by simp
          then show ?thesis unfolding eq'' unfolding pdd_def[symmetric] using sym_mod_abs by blast
        next
          case fls: False
          then have "(i',j') \<notin> I" using I_def i'i by simp
          then have dmufs''fs': "d\<mu> fs'' i' j' = d\<mu> fs' i' j'" using 17 i' j' by simp
          show ?thesis
          proof (cases "j' = j")
            case True
            define \<mu>'' where "\<mu>'' = \<mu> fs'' i' j'" 
            define d'' where "d'' = d fs'' (Suc j')"
            have pge1: "p \<ge> 1" using pgtz by simp
            have lh: "\<bar>\<mu>''\<bar> \<le> 1 / 2" using 23 True i'i \<mu>''_def by simp
            moreover have eq: "d\<mu> fs'' i' j' = \<mu>'' * d''" using d\<mu>_def i' j' \<mu>''_def d''_def 
              by (smt "14" "36" LLL.d_def Suc_lessD fs_int.d_def fs_int_indpt.d\<mu> fs_int_indpt.intro 
                  int_of_rat(1) less_trans_Suc mult_of_int_commute of_rat_mult of_rat_of_int_eq)
            moreover have Sj': "Suc j' \<le> m" "j' \<le> m" using True j' i i' by auto
            moreover then have gtz: "0 < d''" using LLL_d_pos[OF Linvw''] d''_def by simp
            moreover have "rat_of_int \<bar>d\<mu> fs'' i' j'\<bar> = \<bar>\<mu>'' * (rat_of_int d'')\<bar>" 
              using eq by (metis of_int_abs of_rat_hom.injectivity of_rat_mult of_rat_of_int_eq)
            moreover then have "\<bar>\<mu>'' * rat_of_int d'' \<bar> =  \<bar>\<mu>''\<bar> * rat_of_int \<bar>d''\<bar>"
              by (metis (mono_tags, hide_lams) abs_mult of_int_abs)
            moreover have "\<dots> = \<bar>\<mu>''\<bar> * rat_of_int d'' " using gtz by simp
            moreover have "\<dots> < rat_of_int d''" using lh gtz by simp
            ultimately have "rat_of_int \<bar>d\<mu> fs'' i' j'\<bar> < rat_of_int d''" by simp
            then have "\<bar>d\<mu> fs'' i' j'\<bar> <  d fs'' (Suc j')" using d''_def by simp
            then have "\<bar>d\<mu> fs'' i' j'\<bar> < p * d fs'' (Suc j')" using pge1
              by (smt mult_less_cancel_right2)
            then show ?thesis using pge1 LLL_d_pos[OF Linvw'' Sj'(2)] gtz unfolding d''_def
              by (smt mult_less_cancel_left2 mult_right_less_imp_less)
          next
            case False
            have "j' < m" using i' j' by simp
            moreover have "j' > j" using False fls by simp
            ultimately have "\<mu> fs' i' j' = \<mu> fs i' j'" using i' 04 i by simp
            then have "d\<mu> fs' i' j' = d\<mu> fs i' j'" using d\<mu>_def i' j' 05 by simp
            then have "d\<mu> fs'' i' j' = d\<mu> fs i' j'" using dmufs''fs' by simp
            then show ?thesis using LLL_invD_modw[OF Linvmw] i' j' 25 by simp
          qed
        qed
      next
        case False
        then have "(i',j') \<notin> I" using I_def by simp
        then have dmufs''fs': "d\<mu> fs'' i' j' = d\<mu> fs' i' j'" using 17 i' j' by simp
        have "\<mu> fs' i' j' = \<mu> fs i' j'" using i' 04 j' False by simp
        then have "d\<mu> fs' i' j' = d\<mu> fs i' j'" using d\<mu>_def i' j' 05 by simp
        moreover then have "d\<mu> fs'' i' j' = d\<mu> fs i' j'" using dmufs''fs' by simp
        then show ?thesis using LLL_invD_modw[OF Linvmw] i' j' 25 by simp
      qed
    }
    then show ?thesis by simp
  qed
  have 40: "(\<forall>i' < m. \<forall>j' < m. i' \<noteq> i \<or> j' > j \<longrightarrow> d\<mu> fs' i' j' = dmu $$ (i',j'))"
  proof -
    {
      fix i' j'
      assume i': "i' < m" and j': "j' < m"
      assume assm: "i' \<noteq> i \<or> j' > j"
      have "d\<mu> fs' i' j' = dmu $$ (i',j')"
      proof (cases "i' \<noteq> i")
        case True
        then show ?thesis using fs'_def LLL_invD_modw[OF Linvmw] d\<mu>_def i i' j j'
          04 28(1) LLL_invI_weak basis_reduction_add_row_main(8)[OF Linvww] by auto
      next
        case False
        then show ?thesis 
          using 05 LLL_invD_modw[OF Linvmw] d\<mu>_def i j j' 04 assm by simp
      qed
    }
    then show ?thesis by simp
  qed
  have 41: "\<forall>j' \<le> j. d\<mu> fs' i j' = dmu $$ (i,j') - c * dmu $$ (j,j')"
  proof -
    {
      let ?oi = "of_int :: _ \<Rightarrow> rat" 
      fix j'
      assume j': "j' \<le> j"
      define dj' \<mu>i \<mu>j where "dj' = d fs (Suc j')" and "\<mu>i = \<mu> fs i j'" and "\<mu>j = \<mu> fs j j'"
      have "?oi (d\<mu> fs' i j') = ?oi (d fs (Suc j')) * (\<mu> fs i j' - ?oi c * \<mu> fs j j')"
        using j' 04 d\<mu>_def 
        by (smt "05" "08" "091" Suc_leI d_def diff_diff_cancel fs_int.d_def 
            fs_int_indpt.fs_int_mu_d_Z i int_of_rat(2) j less_imp_diff_less less_imp_le_nat)
      also have "\<dots> = (?oi dj') * (\<mu>i - of_int c * \<mu>j)" 
        using dj'_def \<mu>i_def \<mu>j_def by (simp add: of_rat_mult)
      also have "\<dots> = (rat_of_int dj') * \<mu>i - of_int c * (rat_of_int dj') * \<mu>j" by algebra
      also have "\<dots> = rat_of_int (d\<mu> fs i j') - ?oi c * rat_of_int (d\<mu> fs j j')" unfolding dj'_def \<mu>i_def \<mu>j_def
        using i j j' d\<mu>_def
        using "28"(1) LLL.LLL_invD_modw(4) Linvmw d_def fs_int.d_def fs_int_indpt.fs_int_mu_d_Z fs_int_indpt.intro by auto
      also have "\<dots> = rat_of_int (dmu $$ (i,j')) - ?oi c * rat_of_int (dmu $$ (j,j'))" 
        using LLL_invD_modw(7)[OF Linvmw] d\<mu>_def j' i j by auto
      finally have "?oi (d\<mu> fs' i j') = rat_of_int (dmu $$ (i,j')) - ?oi c * rat_of_int (dmu $$ (j,j'))" by simp
      then have "d\<mu> fs' i j' = dmu $$ (i,j') - c * dmu $$ (j,j')"
        using of_int_eq_iff by fastforce
    }
    then show ?thesis by simp
  qed
  have 42: "(\<forall>i' < m. \<forall>j' < m. d\<mu> fs'' i' j' = dmu' $$ (i',j'))"
  proof -
    {
      fix i' j'
      assume i': "i' < m" and j': "j' < m"
      have "d\<mu> fs'' i' j' = dmu' $$ (i',j')" 
      proof (cases "i' = i")
        case i'i: True
        then show ?thesis
        proof (cases "j' > j")
          case True
          then have "(i',j')\<notin>I" using I_def by simp
          moreover then have "d\<mu> fs' i' j' = d\<mu> fs i' j'" using "04" "05" True Suc_leI d\<mu>_def i' j' by simp
          moreover have "dmu' $$ (i',j') = dmu $$ (i',j')" using dmu' True i' j' by simp
          ultimately show ?thesis using "17" "40" True i' j' by auto
        next
          case False
          then have j'lej: "j' \<le> j" by simp
          then have eq': "d\<mu> fs' i j' = dmu $$ (i,j') - c * dmu $$ (j,j')" using 41 by simp
          have id: "d_of dmu j' = d fs j'" "d_of dmu (Suc j') = d fs (Suc j')" 
            using d_of_weak[OF Linvmw] \<open>j' < m\<close> by auto
          show ?thesis
          proof (cases "j' \<noteq> j")
            case True
            then have j'ltj: "j' < j" using True False by simp
            then have "(i',j') \<in> I" using I_def True i'i by simp
            then have "d\<mu> fs'' i' j' = 
              (dmu $$ (i,j') - c * dmu $$ (j,j')) symmod (p * d fs' j' * d fs' (Suc j'))"
              using 17 i' 41 j'lej by (simp add: j' i'i)
            also have "\<dots> = (dmu $$ (i,j') - c * dmu $$ (j,j')) symmod (p * d fs j' * d fs (Suc j'))"
              using 05 i j'ltj j by simp
            also have "\<dots> = dmu' $$ (i,j')" 
              unfolding dmu' index_mat(1)[OF \<open>i < m\<close> \<open>j' < m\<close>] split id using j'lej True by auto
            finally show ?thesis using i'i by simp
          next
            case False
            then have j'j: "j' = j" by simp
            then have "d\<mu> fs'' i j' = d\<mu> fs' i j'" using 20 j' by simp
            also have "\<dots> = dmu $$ (i,j') - c * dmu $$ (j,j')" using eq' by simp
            also have "\<dots> = dmu' $$ (i,j')" using dmu' j'j i j' by simp
            finally show ?thesis using i'i by simp
          qed
        qed
      next
        case False
        then have "(i',j')\<notin>I" using I_def by simp
        moreover then have "d\<mu> fs' i' j' = d\<mu> fs i' j'" by (simp add: "04" "05" False Suc_leI d\<mu>_def i' j')
        moreover then have "dmu' $$ (i',j') = dmu $$ (i',j')" using dmu' False i' j' by simp
        ultimately show ?thesis using "17" "40" False i' j' by auto
      qed
    }
    then show ?thesis by simp
  qed
  from gbnd 26 have gbnd: "g_bnd_mode first b fs''" using g_bnd_mode_cong[of fs'' fs] by simp
  {
    assume Linv: "LLL_invariant_mod fs mfs dmu p first b i"
    have Linvw: "LLL_invariant_weak' i fs" using Linv LLL_invD_mod LLL_invI_weak by simp
    note Linvww = LLL_invw'_imp_w[OF Linvw]
    have 00: "LLL_invariant_weak' i fs'" using Linvw basis_reduction_add_row_weak[OF Linvw i j fs'_def] by auto
    have 37: "weakly_reduced fs'' i" using 15 LLL_invD_weak(8)[OF 00] gram_schmidt_fs.weakly_reduced_def 
      by (smt Suc_lessD i less_trans_Suc) (* invariant req. *)
    have 38: "LLL_invariant_weak' i fs''"
      using 00 11 14 36 37 i 31 12  LLL_invariant_weak'_def by blast
    have "LLL_invariant_mod fs'' mfs' dmu' p first b i"
      using LLL_invI_mod[OF 33 _ 14 11 13 37 35 39 42 p1 gbnd LLL_invD_mod(17)[OF Linv]] i by simp
  }
  moreover have "LLL_invariant_mod_weak fs'' mfs' dmu' p first b"
    using LLL_invI_modw[OF 33 14 11 13 35 39 42 p1 gbnd LLL_invD_modw(15)[OF Linvmw]] by simp
  ultimately show ?thesis using 27 23 24 25 26 172 by auto
qed

definition D_mod :: "int mat \<Rightarrow> nat" where "D_mod dmu = nat (\<Prod> i < m. d_of dmu i)"

definition logD_mod :: "int mat \<Rightarrow> nat"
  where "logD_mod dmu = (if \<alpha> = 4/3 then (D_mod dmu) else nat (floor (log (1 / of_rat reduction) (D_mod dmu))))" 
end

locale fs_int'_mod = 
  fixes n m fs_init \<alpha> i fs mfs dmu p first b 
  assumes LLL_inv_mod: "LLL.LLL_invariant_mod n m fs_init \<alpha> fs mfs dmu p first b i"

context LLL_with_assms
begin

lemma basis_reduction_swap_weak': assumes Linvw: "LLL_invariant_weak' i fs"
  and i: "i < m"
  and i0: "i \<noteq> 0"
  and mu_F1_i: "\<bar>\<mu> fs i (i-1)\<bar> \<le> 1 / 2"
  and norm_ineq: "sq_norm (gso fs (i - 1)) > \<alpha> * sq_norm (gso fs i)" 
  and fs'_def: "fs' = fs[i := fs ! (i - 1), i - 1 := fs ! i]" 
shows "LLL_invariant_weak' (i - 1) fs'" 
proof -
  note inv = LLL_invD_weak[OF Linvw]
  note invw = LLL_invw'_imp_w[OF Linvw]
  note main = basis_reduction_swap_main[OF invw disjI2[OF mu_F1_i] i i0 norm_ineq fs'_def]
  note inv' = LLL_inv_wD[OF main(1)]
  from \<open>weakly_reduced fs i\<close> have "weakly_reduced fs (i - 1)" 
    unfolding gram_schmidt_fs.weakly_reduced_def by auto
  also have "weakly_reduced fs (i - 1) = weakly_reduced fs' (i - 1)" 
    unfolding gram_schmidt_fs.weakly_reduced_def 
    by (intro all_cong, insert i0 i main(5), auto)
  finally have red: "weakly_reduced fs' (i - 1)" .
  show "LLL_invariant_weak' (i - 1) fs'" using i
    by (intro LLL_invI_weak red inv', auto)
qed

lemma basis_reduction_add_row_done_weak: 
  assumes Linv: "LLL_invariant_weak' i fs"
  and i: "i < m" 
  and mu_small: "\<mu>_small_row i fs 0" 
shows "\<mu>_small fs i"
proof -
  note inv = LLL_invD_weak[OF Linv]
  from mu_small 
  have mu_small: "\<mu>_small fs i" unfolding \<mu>_small_row_def \<mu>_small_def by auto
  show ?thesis
    using i mu_small LLL_invI_weak[OF inv(3,6,7,9,1)] by auto
qed     

lemma LLL_invariant_mod_to_weak_m_to_i: assumes
  inv: "LLL_invariant_mod fs mfs dmu p first b m"
  and i: "i \<le> m"
shows "LLL_invariant_mod fs mfs dmu p first b i"
  "LLL_invariant_weak' m fs"
  "LLL_invariant_weak' i fs"
proof -
  show "LLL_invariant_mod fs mfs dmu p first b i" 
  proof -
    have "LLL_invariant_weak' m fs" using LLL_invD_mod[OF inv] LLL_invI_weak by simp
    then have "LLL_invariant_weak' i fs" using LLL_inv_weak_m_impl_i i by simp
    then have "weakly_reduced fs i" using i LLL_invD_weak(8) by simp
    then show ?thesis using LLL_invD_mod[OF inv] LLL_invI_mod i by simp
  qed
  then show fsinvwi: "LLL_invariant_weak' i fs" using LLL_invD_mod LLL_invI_weak by simp
  show "LLL_invariant_weak' m fs" using LLL_invD_mod[OF inv] LLL_invI_weak by simp
qed

lemma basis_reduction_mod_swap_main: 
  assumes Linvmw: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and k: "k < m"
  and k0: "k \<noteq> 0"
  and mu_F1_i: "\<bar>\<mu> fs k (k-1)\<bar> \<le> 1 / 2"
  and norm_ineq: "sq_norm (gso fs (k - 1)) > \<alpha> * sq_norm (gso fs k)" 
  and mfs'_def: "mfs' = mfs[k := mfs ! (k - 1), k - 1 := mfs ! k]"
  and dmu'_def: "dmu' = (mat m m (\<lambda>(i,j). (
      if j < i then
        if i = k - 1 then 
           dmu $$ (k, j)
        else if i = k \<and> j \<noteq> k - 1 then 
             dmu $$ (k - 1, j)
        else if i > k \<and> j = k then
           ((d_of dmu (Suc k)) * dmu $$ (i, k - 1) - dmu $$ (k, k - 1) * dmu $$ (i, j)) 
              div (d_of dmu k)
        else if i > k \<and> j = k - 1 then
           (dmu $$ (k, k - 1) * dmu $$ (i, j) + dmu $$ (i, k) * (d_of dmu (k-1)))
              div (d_of dmu k)
        else dmu $$ (i, j)
      else if i = j then 
        if i = k - 1 then 
          ((d_of dmu (Suc k)) * (d_of dmu (k-1)) + dmu $$ (k, k - 1) * dmu $$ (k, k - 1)) 
            div (d_of dmu k)
        else (d_of dmu (Suc i))
      else dmu $$ (i, j))
    ))"
  and dmu'_mod_def: "dmu'_mod = mat m m (\<lambda>(i, j). (
        if j < i \<and> (j = k \<or> j = k - 1) then 
          dmu' $$ (i, j) symmod (p * (d_of dmu' j) * (d_of dmu' (Suc j)))
        else dmu' $$ (i, j)))"
shows "(\<exists>fs'. LLL_invariant_mod_weak fs' mfs' dmu'_mod p first b \<and>
        LLL_measure (k-1) fs' < LLL_measure k fs \<and>
        (LLL_invariant_mod fs mfs dmu p first b k \<longrightarrow> LLL_invariant_mod fs' mfs' dmu'_mod p first b (k-1)))" 
proof - 
  define fs' where "fs' = fs[k := fs ! (k - 1), k - 1 := fs ! k]"
  have pgtz: "p > 0" and p1: "p > 1" using LLL_invD_modw[OF Linvmw] by auto
  have invw: "LLL_invariant_weak fs" using LLL_invD_modw[OF Linvmw] LLL_invariant_weak_def by simp
  note swap_main = basis_reduction_swap_main(3-)[OF invw disjI2[OF mu_F1_i] k k0 norm_ineq fs'_def]
  note dd\<mu>_swap = d_d\<mu>_swap[OF invw disjI2[OF mu_F1_i] k k0 norm_ineq fs'_def]
  have invw': "LLL_invariant_weak fs'" using fs'_def assms invw basis_reduction_swap_main(1) by simp
  have 02: "LLL_measure k fs > LLL_measure (k - 1) fs'" by fact
  have 03: "\<And> i j. i < m \<Longrightarrow> j < i \<Longrightarrow> 
          d\<mu> fs' i j = (
        if i = k - 1 then 
           d\<mu> fs k j
        else if i = k \<and> j \<noteq> k - 1 then 
             d\<mu> fs (k - 1) j
        else if i > k \<and> j = k then
           (d fs (Suc k) * d\<mu> fs i (k - 1) - d\<mu> fs k (k - 1) * d\<mu> fs i j) div d fs k
        else if i > k \<and> j = k - 1 then 
           (d\<mu> fs k (k - 1) * d\<mu> fs i j + d\<mu> fs i k * d fs (k - 1)) div d fs k
        else d\<mu> fs i j)"
    using dd\<mu>_swap by auto
  have 031: "\<And>i. i < k-1 \<Longrightarrow> gso fs' i = gso fs i" 
    using swap_main(2) k k0 by auto
  have 032: "\<And> ii. ii \<le> m \<Longrightarrow> of_int (d fs' ii) = (if ii = k then 
           sq_norm (gso fs' (k - 1)) / sq_norm (gso fs (k - 1)) * of_int (d fs k)
           else of_int (d fs ii))" 
    by fact 
  have gbnd: "g_bnd_mode first b fs'"
  proof (cases "first \<and> m \<noteq> 0")
    case True
    have "sq_norm (gso fs' 0) \<le> sq_norm (gso fs 0)" 
    proof (cases "k - 1 = 0")
      case False
      thus ?thesis using 031[of 0] by simp
    next
      case *: True
      have k_1: "k - 1 < m" using k by auto
      from * k0 have k1: "k = 1" by simp
      (* this is a copy of what is done in LLL.swap-main, should be made accessible in swap-main *)
      have "sq_norm (gso fs' 0) \<le> abs (sq_norm (gso fs' 0))" by simp
      also have "\<dots> = abs (sq_norm (gso fs 1) + \<mu> fs 1 0 * \<mu> fs 1 0 * sq_norm (gso fs 0))" 
        by (subst swap_main(3)[OF k_1, unfolded *], auto simp: k1)
      also have "\<dots> \<le> sq_norm (gso fs 1) + abs (\<mu> fs 1 0) * abs (\<mu> fs 1 0) * sq_norm (gso fs 0)"
        by (simp add: sq_norm_vec_ge_0)
      also have "\<dots> \<le> sq_norm (gso fs 1) + (1 / 2) * (1 / 2) * sq_norm (gso fs 0)" 
        using mu_F1_i[unfolded k1] 
        by (intro plus_right_mono mult_mono, auto)
      also have "\<dots> < 1 / \<alpha> * sq_norm (gso fs 0) + (1 / 2) * (1 / 2) * sq_norm (gso fs 0)" 
        by (intro add_strict_right_mono, insert norm_ineq[unfolded mult.commute[of \<alpha>],
          THEN mult_imp_less_div_pos[OF \<alpha>0(1)]] k1, auto)
      also have "\<dots> = reduction * sq_norm (gso fs 0)" unfolding reduction_def
        using \<alpha>0 by (simp add: ring_distribs add_divide_distrib)
      also have "\<dots> \<le> 1 * sq_norm (gso fs 0)" using reduction(2)
        by (intro mult_right_mono, auto)
      finally show ?thesis by simp
    qed
    thus ?thesis using LLL_invD_modw(14)[OF Linvmw] True
      unfolding g_bnd_mode_def by auto
  next
    case False
    from LLL_invD_modw(14)[OF Linvmw] False have "g_bnd b fs" unfolding g_bnd_mode_def by auto
    hence "g_bnd b fs'" using g_bnd_swap[OF k k0 invw mu_F1_i norm_ineq fs'_def] by simp
    thus ?thesis using False unfolding g_bnd_mode_def by auto
  qed
  note d_of = d_of_weak[OF Linvmw]
  have 033: "\<And> i. i < m \<Longrightarrow> d\<mu> fs' i i = (
            if i = k - 1 then 
             ((d_of dmu (Suc k)) * (d_of dmu (k-1)) + dmu $$ (k, k - 1) * dmu $$ (k, k - 1)) 
                div (d_of dmu k)
            else (d_of dmu (Suc i)))"  
  proof -
    fix i
    assume i: "i < m"
    have "d\<mu> fs' i i = d fs' (Suc i)" using dd\<mu> i by simp
    also have "\<dots> = (if i = k - 1 then 
          (d fs (Suc k) * d fs (k - 1) + d\<mu> fs k (k - 1) * d\<mu> fs k (k - 1)) div d fs k 
        else d fs (Suc i))"
      by (subst dd\<mu>_swap, insert dd\<mu> k0 i, auto)
    also have "\<dots> = (if i = k - 1 then 
        ((d_of dmu (Suc k)) * (d_of dmu (k-1)) + dmu $$ (k, k - 1) * dmu $$ (k, k - 1)) 
          div (d_of dmu k)
       else (d_of dmu (Suc i)))" (is "_ = ?r") 
      using d_of i k LLL_invD_modw(7)[OF Linvmw] by auto
    finally show "d\<mu> fs' i i = ?r" .
  qed
  have 04: "lin_indep fs'" "length fs' = m" "lattice_of fs' = L" using LLL_inv_wD[OF invw'] by auto
  define I where "I = {(i, j). i < m \<and> j < i \<and> (j = k \<or> j = k - 1)}"
  then have Isubs: "I \<subseteq> {(i,j). i < m \<and> j < i}" using k k0 by auto
  obtain fs'' where 
    05: "lattice_of fs'' = L" and
    06: "map (map_vec (\<lambda> x. x symmod p)) fs'' = map (map_vec (\<lambda> x. x symmod p)) fs'" and
    07: "lin_indep fs''" and
    08: "length fs'' = m" and
    09: "(\<forall> k < m. gso fs'' k = gso fs' k)" and
    10: "(\<forall> k \<le> m. d fs'' k = d fs' k)" and
    11: "(\<forall> i' < m. \<forall> j' < m. d\<mu> fs'' i' j' = 
           (if (i',j') \<in> I then d\<mu> fs' i' j' symmod (p * d fs' j' * d fs' (Suc j')) else d\<mu> fs' i' j'))"
    using mod_finite_set[OF 04(1) 04(2) Isubs 04(3) pgtz] by blast
  have 13: "length mfs' = m" using mfs'_def LLL_invD_modw(1)[OF Linvmw] by simp (* invariant requirement *)
  have 14: "map (map_vec (\<lambda> x. x symmod p)) fs'' = mfs'"  (* invariant requirement *)
    using 06 fs'_def k k0 04(2) LLL_invD_modw(5)[OF Linvmw]
    by (metis (no_types, lifting) length_list_update less_imp_diff_less map_update mfs'_def nth_map)
  have "LLL_measure (k - 1) fs'' = LLL_measure (k - 1) fs'" using 10 LLL_measure_def logD_def D_def by simp
  then have 15: "LLL_measure (k - 1) fs'' < LLL_measure k fs" using 02 by simp (* goal *)
  {
    fix i' j'
    assume i'j': "i'<m" "j'<i'" 
      and neq: "j' \<noteq> k" "j' \<noteq> k - 1"
    hence j'k: "j' \<noteq> k" "Suc j' \<noteq> k" using k0 by auto
    hence "d fs'' j' = d fs j'" "d fs'' (Suc j') = d fs (Suc j')" 
      using \<open>k < m\<close> i'j' k0
        10[rule_format, of j'] 032[rule_format, of j']
        10[rule_format, of "Suc j'"] 032[rule_format, of "Suc j'"] 
      by auto
  } note d_id = this

  have 16: "\<forall>i'<m. \<forall>j'<i'. \<bar>d\<mu> fs'' i' j'\<bar> < p * d fs'' j' * d fs'' (Suc j')" (* invariant requirement *)
  proof -
    {
      fix i' j'
      assume i'j': "i'<m" "j'<i'"
      have "\<bar>d\<mu> fs'' i' j'\<bar> < p * d fs'' j' * d fs'' (Suc j')"
      proof (cases "(i',j') \<in> I")
        case True
        define pdd where "pdd = (p * d fs' j' * d fs' (Suc j'))"
        have pdd_pos: "pdd > 0" using pgtz i'j' LLL_d_pos[OF invw'] pdd_def by simp
        have "d\<mu> fs'' i' j' = d\<mu> fs' i' j' symmod pdd" using True 11 i'j' pdd_def by simp
        then have "\<bar>d\<mu> fs'' i' j'\<bar> < pdd" using True 11 i'j' pdd_pos sym_mod_abs by simp
        then show ?thesis unfolding pdd_def using 10 i'j' by simp
      next
        case False
        from False[unfolded I_def] i'j' have neg: "j' \<noteq> k" "j' \<noteq> k - 1" by auto
        
        consider (1) "i' = k - 1 \<or> i' = k" | (2) "\<not> (i' = k - 1 \<or> i' = k)"  
          using False i'j' unfolding I_def by linarith
        thus ?thesis
        proof cases
          case **: 1
          let ?i'' = "if i' = k - 1 then k else k -1" 
          from ** neg i'j' have i'': "?i'' < m" "j' < ?i''" using k0 k by auto
          have "d\<mu> fs'' i' j' = d\<mu> fs' i' j'" using 11 False i'j' by simp
          also have "\<dots> = d\<mu> fs ?i'' j'" unfolding 03[OF \<open>i' < m\<close> \<open>j' < i'\<close>]
            using ** neg by auto
          finally show ?thesis using LLL_invD_modw(6)[OF Linvmw, rule_format, OF i''] unfolding d_id[OF i'j' neg] by auto
        next
          case **: 2
          hence neq: "j' \<noteq> k" "j' \<noteq> k - 1" using False k k0 i'j' unfolding I_def by auto
          have "d\<mu> fs'' i' j' = d\<mu> fs' i' j'" using 11 False i'j' by simp
          also have "\<dots> = d\<mu> fs i' j'" unfolding 03[OF \<open>i' < m\<close> \<open>j' < i'\<close>] using ** neq by auto
          finally show ?thesis using LLL_invD_modw(6)[OF Linvmw, rule_format, OF i'j'] using d_id[OF i'j' neq] by auto
        qed
      qed
    }
    then show ?thesis by simp
  qed
  have 17: "\<forall>i'<m. \<forall>j'<m. d\<mu> fs'' i' j' = dmu'_mod $$ (i', j')" (* invariant requirement *)
  proof -
    {
      fix i' j'
      assume i'j': "i'<m" "j'<i'"
      have d'dmu': "\<forall>j' < m. d fs' (Suc j') = dmu' $$ (j', j')" using dd\<mu> dmu'_def 033 by simp
      have eq': "d\<mu> fs' i' j' = dmu' $$ (i', j')"
      proof -
        have t00: "d\<mu> fs k j' = dmu $$ (k, j')" and
          t01: "d\<mu> fs (k - 1) j' =  dmu $$ (k - 1, j')" and
          t04: "d\<mu> fs k (k - 1) = dmu $$ (k, k - 1)" and
          t05: "d\<mu> fs i' k = dmu $$ (i', k)"
          using LLL_invD_modw(7)[OF Linvmw] i'j' k dd\<mu> k0 by auto 
        have t03: "d fs k = d\<mu> fs (k-1) (k-1)" using k0 k by (metis LLL.dd\<mu> Suc_diff_1 lessI not_gr_zero)
        have t06: "d fs (k - 1) = (d_of dmu (k-1))" using d_of k by auto
        have t07: "d fs k = (d_of dmu k)" using d_of k by auto
        have j': "j' < m" using i'j' by simp
        have "d\<mu> fs' i' j' = (if i' = k - 1 then 
                   dmu $$ (k, j')
                else if i' = k \<and> j' \<noteq> k - 1 then 
                   dmu $$ (k - 1, j')
                else if i' > k \<and> j' = k then
                   (dmu $$ (k, k) * dmu $$ (i', k - 1) - dmu $$ (k, k - 1) * dmu $$ (i', j')) div (d_of dmu k)
                else if i' > k \<and> j' = k - 1 then 
                   (dmu $$ (k, k - 1) * dmu $$ (i', j') + dmu $$ (i', k) * d fs (k - 1)) div (d_of dmu k)
                else dmu $$ (i', j'))"
          using dd\<mu> k t00 t01 t03 LLL_invD_modw(7)[OF Linvmw] k i'j' j' 03 t07 by simp
        then show ?thesis using dmu'_def i'j' j' t06 t07 by (simp add: d_of_def)
      qed
      have "d\<mu> fs'' i' j' = dmu'_mod $$ (i', j')"
      proof (cases "(i',j') \<in> I")
        case i'j'I: True
        have j': "j' < m" using i'j' by simp
        show ?thesis
        proof -
          have "dmu'_mod $$ (i',j') = dmu' $$ (i',j') 
                  symmod (p * (d_of dmu' j') * (d_of dmu' (Suc j')))"
            using dmu'_mod_def i'j' i'j'I I_def by simp
          also have "d_of dmu' j' = d fs' j'" 
            using j' d'dmu' d_def Suc_diff_1 less_imp_diff_less unfolding d_of_def 
            by (cases j', auto)
          finally have "dmu'_mod $$ (i',j') = dmu' $$ (i',j') symmod (p * d fs' j' * d fs' (Suc j'))"
            using dd\<mu>[OF j'] d'dmu' j' by (auto simp: d_of_def)
          then show ?thesis using i'j'I 11 i'j' eq' by simp
        qed
      next
        case False
        have "d\<mu> fs'' i' j' = d\<mu> fs' i' j'" using False 11 i'j' by simp
        also have "\<dots> = dmu' $$ (i', j')" unfolding eq' ..
        finally show ?thesis unfolding dmu'_mod_def using False[unfolded I_def] i'j' by auto
      qed
    }
    moreover have "\<forall>i' j'. i' < m \<longrightarrow> j' < m \<longrightarrow> i' = j' \<longrightarrow> d\<mu> fs'' i' j' = dmu'_mod $$ (i', j')" 
      using dd\<mu> dmu'_def 033 10 dmu'_mod_def 11 I_def by simp
    moreover {
      fix i' j'
      assume i'j'': "i' < m" "j' < m" "i' < j'"
      then have \<mu>z: "\<mu> fs'' i' j' = 0" by (simp add: gram_schmidt_fs.\<mu>.simps)
      have "dmu'_mod $$ (i',j') = dmu' $$ (i',j')" using dmu'_mod_def i'j'' by auto
      also have "\<dots> = d\<mu> fs i' j'" using LLL_invD_modw(7)[OF Linvmw] i'j'' dmu'_def by simp
      also have "\<dots> = 0" using d\<mu>_def i'j'' by (simp add: gram_schmidt_fs.\<mu>.simps)
      finally have "d\<mu> fs'' i' j' =  dmu'_mod $$ (i',j')" using \<mu>z d_def i'j'' d\<mu>_def by simp
    }
    ultimately show ?thesis by (meson nat_neq_iff)
  qed
  from gbnd 09 have g_bnd: "g_bnd_mode first b fs''" using g_bnd_mode_cong[of fs' fs''] by auto
  {
    assume Linv: "LLL_invariant_mod fs mfs dmu p first b k"
    have 00: "LLL_invariant_weak' k fs" using LLL_invD_mod[OF Linv] LLL_invI_weak by simp
    note swap_weak' = basis_reduction_swap_weak'[OF 00 k k0 mu_F1_i norm_ineq fs'_def]
    have 01: "LLL_invariant_weak' (k - 1) fs'" by fact
    have 12: "weakly_reduced fs'' (k-1)" (* invariant requirement *)
      using 031 09 k LLL_invD_weak(8)[OF 00] unfolding gram_schmidt_fs.weakly_reduced_def by simp
    have "LLL_invariant_mod fs'' mfs' dmu'_mod p first b (k-1)" 
      using LLL_invI_mod[OF 13 _ 08 05 07 12 14 16 17 p1 g_bnd LLL_invD_mod(17)[OF Linv]] k by simp
  }
  moreover have "LLL_invariant_mod_weak fs'' mfs' dmu'_mod p first b"
    using LLL_invI_modw[OF 13 08 05 07 14 16 17 p1 g_bnd LLL_invD_modw(15)[OF Linvmw]] by simp
  ultimately show ?thesis using 15 by auto
qed

lemma dmu_quot_is_round_of_\<mu>:
  assumes Linv: "LLL_invariant_mod fs mfs dmu p first b i'"
    and c: "c = round_num_denom (dmu $$ (i,j)) (d_of dmu (Suc j))" 
    and i: "i < m"
    and j: "j < i"
  shows "c = round(\<mu> fs i j)" 
proof -
  have Linvw: "LLL_invariant_weak' i' fs" using LLL_invD_mod[OF Linv] LLL_invI_weak by simp
  have j2: "j < m" using i j by simp
  then have j3: "Suc j \<le> m" by simp
  have \<mu>1: "\<mu> fs j j = 1" using i j by (meson gram_schmidt_fs.\<mu>.elims less_irrefl_nat)
  have inZ: "rat_of_int (d fs (Suc j)) * \<mu> fs i j \<in> \<int>" using fs_int_indpt.fs_int_mu_d_Z_m_m i j
      LLL_invD_mod(5)[OF Linv] LLL_invD_weak(2) Linvw d_def fs_int.d_def fs_int_indpt.intro by auto
  have "c = round(rat_of_int (d\<mu> fs i j) / rat_of_int (d\<mu> fs j j))" using LLL_invD_mod(9) Linv i j c 
    by (simp add: round_num_denom d_of_def)
  then show ?thesis using LLL_d_pos[OF LLL_invw'_imp_w[OF Linvw] j3] j i inZ d\<mu>_def \<mu>1 by simp
qed

lemma dmu_quot_is_round_of_\<mu>_weak:
  assumes Linv: "LLL_invariant_mod_weak fs mfs dmu p first b"
    and c: "c = round_num_denom (dmu $$ (i,j)) (d_of dmu (Suc j))" 
    and i: "i < m"
    and j: "j < i"
  shows "c = round(\<mu> fs i j)" 
proof -
  have Linvww: "LLL_invariant_weak fs" using LLL_invD_modw[OF Linv] LLL_invariant_weak_def by simp
  have j2: "j < m" using i j by simp
  then have j3: "Suc j \<le> m" by simp
  have \<mu>1: "\<mu> fs j j = 1" using i j by (meson gram_schmidt_fs.\<mu>.elims less_irrefl_nat)
  have inZ: "rat_of_int (d fs (Suc j)) * \<mu> fs i j \<in> \<int>" using fs_int_indpt.fs_int_mu_d_Z_m_m i j
      LLL_invD_modw[OF Linv] d_def fs_int.d_def fs_int_indpt.intro by auto
  have "c = round(rat_of_int (d\<mu> fs i j) / rat_of_int (d\<mu> fs j j))" using LLL_invD_modw(7) Linv i j c 
    by (simp add: round_num_denom d_of_def)
  then show ?thesis using LLL_d_pos[OF Linvww j3] j i inZ d\<mu>_def \<mu>1 by simp
qed  

lemma basis_reduction_mod_add_row: assumes 
  Linv: "LLL_invariant_mod_weak fs mfs dmu p first b" 
  and res: "basis_reduction_mod_add_row p mfs dmu i j = (mfs', dmu')" 
  and i: "i < m"
  and j: "j < i"
  and igtz: "i \<noteq> 0"
shows "(\<exists>fs'. LLL_invariant_mod_weak fs' mfs' dmu' p first b \<and>
        LLL_measure i fs' = LLL_measure i fs \<and>
        (\<mu>_small_row i fs (Suc j) \<longrightarrow> \<mu>_small_row i fs' j) \<and>
        \<bar>\<mu> fs' i j\<bar> \<le> 1 / 2 \<and>
        (\<forall>i' j'. i' < i \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs' i' j' = \<mu> fs i' j') \<and>
        (LLL_invariant_mod fs mfs dmu p first b i \<longrightarrow> LLL_invariant_mod fs' mfs' dmu' p first b i) \<and>
        (\<forall>ii \<le> m. d fs' ii = d fs ii))"
proof -
  define c where "c = round_num_denom (dmu $$ (i,j)) (d_of dmu (Suc j))" 
  then have c: "c = round(\<mu> fs i j)" using dmu_quot_is_round_of_\<mu>_weak[OF Linv c_def i j] by simp
  show ?thesis
  proof (cases "c = 0")
    case True
    then have pair_id: "(mfs', dmu') = (mfs, dmu)" 
      using res c_def unfolding basis_reduction_mod_add_row_def Let_def by auto
    moreover have "\<bar>\<mu> fs i j\<bar> \<le> inverse 2" using c[symmetric, unfolded True] 
      by (simp add: round_def, linarith)
    moreover then have "(\<mu>_small_row i fs (Suc j) \<longrightarrow> \<mu>_small_row i fs j)" 
      unfolding \<mu>_small_row_def using Suc_leI le_neq_implies_less by blast
    ultimately show ?thesis using Linv pair_id by auto
  next
    case False
    then have pair_id: "(mfs', dmu') = (mfs[i := map_vec (\<lambda>x. x symmod p) (mfs ! i - c \<cdot>\<^sub>v mfs ! j)],
                mat m m (\<lambda>(i', j'). if i' = i \<and> j' \<le> j
                  then if j' = j then dmu $$ (i, j') - c * dmu $$ (j, j')
                       else (dmu $$ (i,j') - c * dmu $$ (j,j')) 
                              symmod (p * (d_of dmu j') * (d_of dmu (Suc j')))
                  else dmu $$ (i', j')))" 
      using res c_def unfolding basis_reduction_mod_add_row_def Let_def by auto
    then have mfs': "mfs' = mfs[i := map_vec (\<lambda>x. x symmod p) (mfs ! i - c \<cdot>\<^sub>v mfs ! j)]"
      and dmu': "dmu' = mat m m (\<lambda>(i', j'). if i' = i \<and> j' \<le> j
                  then if j' = j then dmu $$ (i, j') - c * dmu $$ (j, j')
                       else (dmu $$ (i,j') - c * dmu $$ (j,j')) 
                              symmod (p * (d_of dmu j') * (d_of dmu (Suc j')))
                  else dmu $$ (i', j'))" by auto
    show ?thesis using basis_reduction_mod_add_row_main[OF Linv i j c mfs' dmu'] by blast
  qed
qed

lemma basis_reduction_mod_swap: assumes
  Linv: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and mu: "\<bar>\<mu> fs k (k-1)\<bar> \<le> 1 / 2"
  and res: "basis_reduction_mod_swap p mfs dmu k = (mfs', dmu'_mod)" 
  and cond: "sq_norm (gso fs (k - 1)) > \<alpha> * sq_norm (gso fs k)"
  and i: "k < m" "k \<noteq> 0" 
shows "(\<exists>fs'. LLL_invariant_mod_weak fs' mfs' dmu'_mod p first b \<and>
        LLL_measure (k - 1) fs' < LLL_measure k fs \<and>
        (LLL_invariant_mod fs mfs dmu p first b k \<longrightarrow> LLL_invariant_mod fs' mfs' dmu'_mod p first b (k-1)))"
  using res[unfolded basis_reduction_mod_swap_def basis_reduction_mod_swap_dmu_mod_def] 
    basis_reduction_mod_swap_main[OF Linv i mu cond] by blast

lemma basis_reduction_adjust_mod: assumes 
  Linv: "LLL_invariant_mod_weak fs mfs dmu p first b" 
  and res: "basis_reduction_adjust_mod p first mfs dmu = (p', mfs', dmu', g_idx')" 
shows "(\<exists>fs' b'. (LLL_invariant_mod fs mfs dmu p first b i \<longrightarrow> LLL_invariant_mod fs' mfs' dmu' p' first b' i) \<and>
       LLL_invariant_mod_weak fs' mfs' dmu' p' first b' \<and>
       LLL_measure i fs' = LLL_measure i fs)"
proof (cases "\<exists> g_idx. basis_reduction_adjust_mod p first mfs dmu = (p, mfs, dmu, g_idx)")
  case True
  thus ?thesis using res Linv by auto
next
  case False
  obtain b' g_idx where norm: "compute_max_gso_norm first dmu = (b', g_idx)" by force
  define p'' where "p'' = compute_mod_of_max_gso_norm first b'" 
  define d_vec where "d_vec = vec (Suc m) (\<lambda>i. d_of dmu i)" 
  define mfs'' where "mfs'' = map (map_vec (\<lambda>x. x symmod p'')) mfs"  
  define dmu'' where "dmu'' = mat m m (\<lambda>(i, j).
                   if j < i then dmu $$ (i, j) symmod (p'' * d_vec $ j * d_vec $ Suc j)
                   else dmu $$ (i, j))" 
  note res = res False
  note res = res[unfolded basis_reduction_adjust_mod.simps Let_def norm split, 
      folded p''_def, folded d_vec_def mfs''_def, folded dmu''_def]
  from res have pp': "p'' < p" and id: "dmu' = dmu''" "mfs' = mfs''" "p' = p''" "g_idx' = g_idx"
    by (auto split: if_splits)
  define I where "I = {(i',j'). i' < m \<and> j' < i'}"
  note inv = LLL_invD_modw[OF Linv]
  from inv(4) have lin: "gs.lin_indpt_list (RAT fs)" .
  from inv(3) have lat: "lattice_of fs = L" .
  from inv(2) have len: "length fs = m" .
  have weak: "LLL_invariant_weak fs" using Linv
    by (auto simp: LLL_invariant_mod_weak_def LLL_invariant_weak_def)
  from compute_max_gso_norm[OF _ weak, of dmu first, unfolded norm] inv(7)
  have bnd: "g_bnd_mode first b' fs" and b': "b' \<ge> 0" "m = 0 \<Longrightarrow> b' = 0" by auto
  from compute_mod_of_max_gso_norm[OF b' p''_def] 
  have p'': "0 < p''" "1 < p''" "mod_invariant b' p'' first" 
    by auto
  obtain fs' where 
    01: "lattice_of fs' = L" and
    02: "map (map_vec (\<lambda> x. x symmod p'')) fs' = map (map_vec (\<lambda> x. x symmod p'')) fs" and
    03: "lin_indep fs'" and
    04: "length fs' = m" and
    05: "(\<forall> k < m. gso fs' k = gso fs k)" and
    06: "(\<forall> k \<le> m. d fs' k = d fs k)" and
    07: "(\<forall> i' < m. \<forall> j' < m. d\<mu> fs' i' j' = 
      (if (i',j') \<in> I then d\<mu> fs i' j' symmod (p'' * d fs j' * d fs (Suc j')) else d\<mu> fs i' j'))"
    using mod_finite_set[OF lin len _ lat, of I] I_def p'' by blast
  from bnd 05 have bnd: "g_bnd_mode first b' fs'" using g_bnd_mode_cong[of fs fs'] by auto
  have D: "D fs = D fs'" unfolding D_def using 06 by auto  


  have Linv': "LLL_invariant_mod_weak fs' mfs'' dmu'' p'' first b'"
  proof (intro LLL_invI_modw p'' 04 03 01 bnd)
    {
      have "mfs'' = map (map_vec (\<lambda>x. x symmod p'')) mfs" by fact
      also have "\<dots> = map (map_vec (\<lambda>x. x symmod p'')) (map (map_vec (\<lambda>x. x symmod p)) fs)" 
        using inv by simp
      also have "\<dots> = map (map_vec (\<lambda>x. x symmod p symmod p'')) fs" by auto
      also have "(\<lambda> x. x symmod p symmod p'') = (\<lambda> x. x symmod p'')" 
      proof (intro ext)
        fix x
        from \<open>mod_invariant b p first\<close>[unfolded mod_invariant_def] obtain e where 
          p: "p = log_base ^ e" by auto
        from p''[unfolded mod_invariant_def] obtain e' where
          p'': "p'' = log_base ^ e'" by auto
        from pp'[unfolded p p''] log_base have "e' \<le> e" by simp
        hence dvd: "p'' dvd p" unfolding p p'' using log_base by (metis le_imp_power_dvd)
        thus "x symmod p symmod p'' = x symmod p''"  
          by (intro sym_mod_sym_mod_cancel)
      qed
      finally show "map (map_vec (\<lambda>x. x symmod p'')) fs' = mfs''" unfolding 02 ..
    }
    thus "length mfs'' = m" using 04 by auto
    show "\<forall>i'<m. \<forall>j'<i'. \<bar>d\<mu> fs' i' j'\<bar> < p'' * d fs' j' * d fs' (Suc j')"
    proof -
      {
        fix i' j'
        assume i'j': "i' < m" "j' < i'"
        then have "d\<mu> fs' i' j' = d\<mu> fs i' j' symmod (p'' * d fs' j' * d fs' (Suc j'))"
          using 07 06 unfolding I_def by simp
        then have "\<bar>d\<mu> fs' i' j'\<bar> < p'' * d fs' j' * d fs' (Suc j')" 
          using sym_mod_abs p'' LLL_d_pos[OF weak] mult_pos_pos
          by (smt "06" i'j' less_imp_le_nat less_trans_Suc nat_SN.gt_trans)
      }
      then show ?thesis by simp
    qed
    from inv(7) have dmu: "i' < m \<Longrightarrow> j' < m \<Longrightarrow> dmu $$ (i', j') = d\<mu> fs i' j'" for i' j'
      by auto
    note d_of = d_of_weak[OF Linv]
    have dvec: "i \<le> m \<Longrightarrow> d_vec $ i = d fs i" for i unfolding d_vec_def using d_of by auto
    show "\<forall>i'<m. \<forall>j'<m. d\<mu> fs' i' j' = dmu'' $$ (i', j')" 
      using 07 unfolding dmu''_def I_def 
      by (auto simp: dmu dvec)
  qed

  moreover 
  {
    assume linv: "LLL_invariant_mod fs mfs dmu p first b i" 
    note inv = LLL_invD_mod[OF linv]
    hence i: "i \<le> m" by auto
    have norm: "j < m \<Longrightarrow> \<parallel>gso fs j\<parallel>\<^sup>2 = \<parallel>gso fs' j\<parallel>\<^sup>2" for j
      using 05 by auto
    have "weakly_reduced fs i = weakly_reduced fs' i" 
      unfolding gram_schmidt_fs.weakly_reduced_def using i
      by (intro all_cong arg_cong2[where f = "(\<le>)"] arg_cong[where f = "\<lambda> x. _ * x"] norm, auto)
    with inv have "weakly_reduced fs' i" by auto
    hence "LLL_invariant_mod fs' mfs'' dmu'' p'' first b' i" using inv         
      by (intro LLL_invI_mod LLL_invD_modw[OF Linv'])
  }

  moreover have "LLL_measure i fs' = LLL_measure i fs" 
    unfolding LLL_measure_def logD_def D ..
  ultimately show ?thesis unfolding id by blast
qed

lemma alpha_comparison: assumes 
  Linv: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and alph: "quotient_of \<alpha> = (num, denom)" 
  and i: "i < m" 
  and i0: "i \<noteq> 0" 
shows "(d_of dmu i * d_of dmu i * denom \<le> num * d_of dmu (i - 1) * d_of dmu (Suc i))
  = (sq_norm (gso fs (i - 1)) \<le> \<alpha> * sq_norm (gso fs i))" 
proof - 
  note inv = LLL_invD_modw[OF Linv]
  interpret fs_indep: fs_int_indpt n fs
    by (unfold_locales, insert inv, auto)
  from inv(2) i have ifs: "i < length fs" by auto
  note d_of_fs = d_of_weak[OF Linv]
  show ?thesis 
    unfolding fs_indep.d_sq_norm_comparison[OF alph ifs i0, symmetric]
    by (subst (1 2 3 4) d_of_fs, use i d_def fs_indep.d_def in auto)
qed

lemma basis_reduction_adjust_swap_add_step: assumes 
  Linv: "LLL_invariant_mod_weak fs mfs dmu p first b" 
  and res: "basis_reduction_adjust_swap_add_step p first mfs dmu g_idx i = (p', mfs', dmu', g_idx')" 
  and alph: "quotient_of \<alpha> = (num, denom)" 
  and ineq: "\<not> (d_of dmu i * d_of dmu i * denom
              \<le> num * d_of dmu (i - 1) * d_of dmu (Suc i))" 
  and i: "i < m" 
  and i0: "i \<noteq> 0" 
shows "\<exists>fs' b'. LLL_invariant_mod_weak fs' mfs' dmu' p' first b' \<and>
        LLL_measure (i - 1) fs' < LLL_measure i fs \<and>
        LLL_measure (m - 1) fs' < LLL_measure (m - 1) fs \<and>
        (LLL_invariant_mod fs mfs dmu p first b i \<longrightarrow> 
         LLL_invariant_mod fs' mfs' dmu' p' first b' (i - 1))"
proof -
  obtain mfs0 dmu0 where add: "basis_reduction_mod_add_row p mfs dmu i (i-1) = (mfs0, dmu0)" by force
  obtain mfs1 dmu1 where swap: "basis_reduction_mod_swap p mfs0 dmu0 i = (mfs1, dmu1)" by force
  note res = res[unfolded basis_reduction_adjust_swap_add_step_def Let_def add split swap]
  from i0 have ii: "i - 1 < i" by auto
  from basis_reduction_mod_add_row[OF Linv add i ii i0]
  obtain fs0 where Linv0: "LLL_invariant_mod_weak fs0 mfs0 dmu0 p first b" 
    and meas0: "LLL_measure i fs0 = LLL_measure i fs" 
    and small: "\<bar>\<mu> fs0 i (i - 1)\<bar> \<le> 1 / 2" 
    and Linv0': "LLL_invariant_mod fs mfs dmu p first b i \<Longrightarrow> LLL_invariant_mod fs0 mfs0 dmu0 p first b i" 
    by blast
  {
    have id: "d_of dmu0 i = d_of dmu i" "d_of dmu0 (i - 1) = d_of dmu (i - 1)"
      "d_of dmu0 (Suc i) = d_of dmu (Suc i)"
      using i i0 add[unfolded basis_reduction_mod_add_row_def Let_def]
      by (auto split: if_splits simp: d_of_def)
    from ineq[folded id, unfolded alpha_comparison[OF Linv0 alph i i0]]
    have "\<parallel>gso fs0 (i - 1)\<parallel>\<^sup>2 > \<alpha> * \<parallel>gso fs0 i\<parallel>\<^sup>2" by simp
  } note ineq = this
  from Linv have "LLL_invariant_weak fs" 
    by (auto simp: LLL_invariant_weak_def LLL_invariant_mod_weak_def)
  from basis_reduction_mod_swap[OF Linv0 small swap ineq i i0, unfolded meas0] Linv0'
  obtain fs1 where Linv1: "LLL_invariant_mod_weak fs1 mfs1 dmu1 p first b"
    and meas1: "LLL_measure (i - 1) fs1 < LLL_measure i fs" 
    and Linv1': "LLL_invariant_mod fs mfs dmu p first b i \<Longrightarrow> LLL_invariant_mod fs1 mfs1 dmu1 p first b (i - 1)" 
    by auto
  show ?thesis
  proof (cases "i - 1 = g_idx")
    case False
    with res have id: "p' = p" "mfs' = mfs1" "dmu' = dmu1" "g_idx' = g_idx" by auto
    show ?thesis unfolding id using Linv1' meas1 Linv1 by (intro exI[of _ fs1] exI[of _ b], auto simp: LLL_measure_def)
  next
    case True
    with res have adjust: "basis_reduction_adjust_mod p first mfs1 dmu1 = (p', mfs', dmu', g_idx')" by simp
    from basis_reduction_adjust_mod[OF Linv1 adjust, of "i - 1"] Linv1'
    obtain fs' b' where Linvw: "LLL_invariant_mod_weak fs' mfs' dmu' p' first b'"
      and Linv: "LLL_invariant_mod fs mfs dmu p first b i \<Longrightarrow> LLL_invariant_mod fs' mfs' dmu' p' first b' (i - 1)"
      and meas: "LLL_measure (i - 1) fs' = LLL_measure (i - 1) fs1" 
      by blast
    note meas = meas1[folded meas]
    from meas have meas': "LLL_measure (m - 1) fs' < LLL_measure (m - 1) fs" 
      unfolding LLL_measure_def using i by auto
    show ?thesis
      by (intro exI conjI impI, rule Linvw, rule meas, rule meas', rule Linv) 
  qed
qed


lemma basis_reduction_mod_step: assumes 
  Linv: "LLL_invariant_mod fs mfs dmu p first b i" 
  and res: "basis_reduction_mod_step p first mfs dmu g_idx i j = (p', mfs', dmu', g_idx', i', j')" 
  and i: "i < m" 
shows "\<exists>fs' b'. LLL_measure i' fs' < LLL_measure i fs \<and> LLL_invariant_mod fs' mfs' dmu' p' first b' i'"
proof -
  note res = res[unfolded basis_reduction_mod_step_def Let_def]
  from Linv have Linvw: "LLL_invariant_mod_weak fs mfs dmu p first b" 
    by (auto simp: LLL_invariant_mod_weak_def LLL_invariant_mod_def)
  show ?thesis
  proof (cases "i = 0")
    case True
    then have ids: "mfs' = mfs" "dmu' = dmu" "i' = Suc i" "p' = p" using res by auto
    have "LLL_measure i' fs < LLL_measure i fs \<and> LLL_invariant_mod fs mfs' dmu' p first b i'"
      using increase_i_mod[OF Linv i] True res ids inv by simp
    then show ?thesis using res ids inv by auto
  next
    case False
    hence id: "(i = 0) = False" by auto
    obtain num denom where alph: "quotient_of \<alpha> = (num, denom)" by force
    note res = res[unfolded id if_False alph split]
    let ?comp = "d_of dmu i * d_of dmu i * denom \<le> num * d_of dmu (i - 1) * d_of dmu (Suc i)" 
    show ?thesis
    proof (cases ?comp)
      case False
      hence id: "?comp = False" by simp
      note res = res[unfolded id if_False]
      let ?step = "basis_reduction_adjust_swap_add_step p first mfs dmu g_idx i" 
      from res have step: "?step = (p', mfs', dmu', g_idx')" 
        and i': "i' = i - 1" 
        by (cases ?step, auto)+
      from basis_reduction_adjust_swap_add_step[OF Linvw step alph False i \<open>i \<noteq> 0\<close>] Linv
      show ?thesis unfolding i' by blast
    next
      case True
      hence id: "?comp = True" by simp
      note res = res[unfolded id if_True]
      from res have ids: "p' = p" "mfs' = mfs" "dmu' = dmu" "i' = Suc i" by auto
      from True alpha_comparison[OF Linvw alph i False]
      have ineq: "sq_norm (gso fs (i - 1)) \<le> \<alpha> * sq_norm (gso fs i)" by simp
      from increase_i_mod[OF Linv i ineq]
      show ?thesis unfolding ids by auto
    qed
  qed
qed

lemma basis_reduction_mod_main: assumes "LLL_invariant_mod fs mfs dmu p first b i" 
  and res: "basis_reduction_mod_main p first mfs dmu g_idx i j = (p', mfs', dmu')" 
shows "\<exists>fs' b'. LLL_invariant_mod fs' mfs' dmu' p' first b' m" 
  using assms
proof (induct "LLL_measure i fs" arbitrary: i mfs dmu j p b fs g_idx rule: less_induct)
  case (less i fs mfs dmu j p b g_idx)
  hence fsinv: "LLL_invariant_mod fs mfs dmu p first b i" by auto
  note res = less(3)[unfolded basis_reduction_mod_main.simps[of p first mfs dmu g_idx i j]]
  note inv = less(2)
  note IH = less(1)
  show ?case
  proof (cases "i < m")
    case i: True
    obtain p' mfs' dmu' g_idx' i' j' where step: "basis_reduction_mod_step p first mfs dmu g_idx i j = (p', mfs', dmu', g_idx', i', j')" 
      (is "?step = _") by (cases ?step, auto)
    then obtain fs' b' where Linv: "LLL_invariant_mod fs' mfs' dmu' p' first b' i'" 
      and decr: "LLL_measure i' fs' < LLL_measure i fs"
      using basis_reduction_mod_step[OF fsinv step i] i fsinv by blast 
    note res = res[unfolded step split]
    from res i show ?thesis using IH[OF decr Linv] by auto
  next
    case False
    with LLL_invD_mod[OF fsinv] res have i: "i = m" "p' = p" by auto
    then obtain fs' b' where "LLL_invariant_mod fs' mfs' dmu' p first b' m" using False res fsinv by simp
    then show ?thesis using i by auto
  qed
qed

lemma compute_max_gso_quot_alpha: 
  assumes inv: "LLL_invariant_mod_weak fs mfs dmu p first b" 
  and max: "compute_max_gso_quot dmu = (msq_num, msq_denum, idx)"
  and alph: "quotient_of \<alpha> = (num, denum)" 
  and cmp: "(msq_num * denum  > num * msq_denum) = cmp" 
  and m: "m > 1" 
shows "cmp \<Longrightarrow> idx \<noteq> 0 \<and> idx < m \<and> \<not> (d_of dmu idx * d_of dmu idx * denum
              \<le> num * d_of dmu (idx - 1) * d_of dmu (Suc idx))" 
  and "\<not> cmp \<Longrightarrow> LLL_invariant_mod fs mfs dmu p first b m" 
proof -
  from inv
  have fsinv: "LLL_invariant_weak fs" 
    by (simp add: LLL_invariant_mod_weak_def LLL_invariant_weak_def)
  define qt where "qt = (\<lambda>i. ((d_of dmu (i + 1)) * (d_of dmu (i + 1)),
            (d_of dmu (i + 2)) * (d_of dmu i), Suc i))"
  define lst where "lst = (map (\<lambda>i. qt i) [0..<(m-1)])"
  have msqlst: "(msq_num, msq_denum, idx) = max_list_rats_with_index lst"
    using max lst_def qt_def unfolding compute_max_gso_quot_def by simp
  have nz: "\<And>n d i. (n, d, i) \<in> set lst \<Longrightarrow> d > 0"
    unfolding lst_def qt_def using d_of_weak[OF inv] LLL_d_pos[OF fsinv] by auto
  have geq: "\<forall>(n, d, i) \<in> set lst. rat_of_int msq_num / of_int msq_denum \<ge> rat_of_int n / of_int d"
    using max_list_rats_with_index[of lst] nz msqlst by (metis (no_types, lifting) case_prodI2)
  have len: "length lst \<ge> 1" using m unfolding lst_def by simp
  have inset: "(msq_num, msq_denum, idx) \<in> set lst"
    using max_list_rats_with_index_in_set[OF msqlst[symmetric] len] nz by simp
  then have idxm: "idx \<in> {1..<m}" using lst_def[unfolded qt_def] by auto
  then have idx0: "idx \<noteq> 0" and idx: "idx < m" by auto
  have 00: "(msq_num, msq_denum, idx)  = qt (idx - 1)" using lst_def inset qt_def by auto
  then have id_qt: "msq_num = d_of dmu idx * d_of dmu idx" "msq_denum = d_of dmu (Suc idx) * d_of dmu (idx - 1)" 
    unfolding qt_def by auto
  have "msq_denum = (d_of dmu (idx + 1)) * (d_of dmu (idx - 1))"
    using 00 unfolding qt_def by simp
  then have dengt0: "msq_denum > 0" using d_of_weak[OF inv] idxm LLL_d_pos[OF fsinv] by auto
  have \<alpha>dengt0: "denum > 0" using alph by (metis quotient_of_denom_pos)
  from cmp[unfolded id_qt]
  have cmp: "cmp = (\<not> (d_of dmu idx * d_of dmu idx * denum \<le> num * d_of dmu (idx - 1) * d_of dmu (Suc idx)))" 
    by (auto simp: ac_simps)
  {
    assume cmp    
    from this[unfolded cmp] 
    show "idx \<noteq> 0 \<and> idx < m \<and> \<not> (d_of dmu idx * d_of dmu idx * denum
              \<le> num * d_of dmu (idx - 1) * d_of dmu (Suc idx))" using idx0 idx by auto
  }
  {
    assume "\<not> cmp" 
    from this[unfolded cmp] have small: "d_of dmu idx * d_of dmu idx * denum \<le> num * d_of dmu (idx - 1) * d_of dmu (Suc idx)" by auto
    note d_pos = LLL_d_pos[OF fsinv]
    have gso: "k < m \<Longrightarrow> sq_norm (gso fs k) = of_int (d fs (Suc k)) / of_int (d fs k)" for k using 
        LLL_d_Suc[OF fsinv, of k] d_pos[of k] by simp
    have gso_pos: "k < m \<Longrightarrow> sq_norm (gso fs k) > 0" for k 
      using gso[of k] d_pos[of k] d_pos[of "Suc k"] by auto
    from small[unfolded alpha_comparison[OF inv alph idx idx0]]
    have alph: "sq_norm (gso fs (idx - 1)) \<le> \<alpha> * sq_norm (gso fs idx)" .
    with gso_pos[OF idx] have alph: "sq_norm (gso fs (idx - 1)) / sq_norm (gso fs idx) \<le> \<alpha>" 
      by (metis mult_imp_div_pos_le)
    have weak: "weakly_reduced fs m" unfolding gram_schmidt_fs.weakly_reduced_def
    proof (intro allI impI, goal_cases)
      case (1 i)
      from idx have idx1: "idx - 1 < m" by auto
      from geq[unfolded lst_def]
      have mem: "(d_of dmu (Suc i) * d_of dmu (Suc i),
            d_of dmu (Suc (Suc i)) * d_of dmu i, Suc i) \<in> set lst" 
        unfolding lst_def qt_def using 1 by auto
      have "sq_norm (gso fs i) / sq_norm (gso fs (Suc i)) = 
        of_int (d_of dmu (Suc i) * d_of dmu (Suc i)) / of_int (d_of dmu (Suc (Suc i)) * d_of dmu i)" 
        using gso idx0 d_of_weak[OF inv] 1 by auto
      also have "\<dots> \<le> rat_of_int msq_num / rat_of_int msq_denum" 
        using geq[rule_format, OF mem, unfolded split] by auto
      also have "\<dots> = sq_norm (gso fs (idx - 1)) / sq_norm (gso fs idx)" 
        unfolding id_qt gso[OF idx] gso[OF idx1] using idx0 d_of_weak[OF inv] idx by auto
      also have "\<dots> \<le> \<alpha>" by fact
      finally show "sq_norm (gso fs i) \<le> \<alpha> * sq_norm (gso fs (Suc i))" using gso_pos[OF 1]
        using pos_divide_le_eq by blast
    qed
    with inv show "LLL_invariant_mod fs mfs dmu p first b m" 
      by (auto simp: LLL_invariant_mod_weak_def LLL_invariant_mod_def)
  }
qed
  

lemma small_m: 
  assumes inv: "LLL_invariant_mod_weak fs mfs dmu p first b" 
  and m: "m \<le> 1" 
shows "LLL_invariant_mod fs mfs dmu p first b m" 
proof -
  have weak: "weakly_reduced fs m" unfolding gram_schmidt_fs.weakly_reduced_def using m
    by auto
  with inv show "LLL_invariant_mod fs mfs dmu p first b m" 
    by (auto simp: LLL_invariant_mod_weak_def LLL_invariant_mod_def)
qed

lemma basis_reduction_iso_main: assumes "LLL_invariant_mod_weak fs mfs dmu p first b"
  and res: "basis_reduction_iso_main p first mfs dmu g_idx j = (p', mfs', dmu')" 
shows "\<exists>fs' b'. LLL_invariant_mod fs' mfs' dmu' p' first b' m" 
  using assms
proof (induct "LLL_measure (m-1) fs" arbitrary: fs mfs dmu j p b g_idx rule: less_induct)
  case (less fs mfs dmu j p b g_idx)
  have inv: "LLL_invariant_mod_weak fs mfs dmu p first b" using less by auto
  hence fsinv: "LLL_invariant_weak fs" 
    by (simp add: LLL_invariant_mod_weak_def LLL_invariant_weak_def)
  note res = less(3)[unfolded basis_reduction_iso_main.simps[of p first mfs dmu g_idx j]]
  note IH = less(1)
  obtain msq_num msq_denum idx where max: "compute_max_gso_quot dmu = (msq_num, msq_denum, idx)" 
    by (metis prod_cases3)
  obtain num denum where alph: "quotient_of \<alpha> = (num, denum)" by force
  note res = res[unfolded max alph Let_def split]
  consider (small) "m \<le> 1" | (final) "m > 1" "\<not> (num * msq_denum < msq_num * denum)" | (step) "m > 1" "num * msq_denum < msq_num * denum" 
    by linarith
  thus ?case
  proof cases
    case *: step
    obtain p1 mfs1 dmu1 g_idx1 where step: "basis_reduction_adjust_swap_add_step p first mfs dmu g_idx idx = (p1, mfs1, dmu1, g_idx1)"
      by (metis prod_cases4)
    from res[unfolded step split] * have res: "basis_reduction_iso_main p1 first mfs1 dmu1 g_idx1 (j + 1) = (p', mfs', dmu')" by auto
    from compute_max_gso_quot_alpha(1)[OF inv max alph refl *]
    have idx0: "idx \<noteq> 0" and idx: "idx < m" and cmp: "\<not> d_of dmu idx * d_of dmu idx * denum \<le> num * d_of dmu (idx - 1) * d_of dmu (Suc idx)" by auto
    from basis_reduction_adjust_swap_add_step[OF inv step alph cmp idx idx0] obtain fs1 b1 
      where inv1: "LLL_invariant_mod_weak fs1 mfs1 dmu1 p1 first b1" and meas: "LLL_measure (m - 1) fs1 < LLL_measure (m - 1) fs" 
      by auto
    from IH[OF meas inv1 res] show ?thesis .
  next
    case small
    with res small_m[OF inv] show ?thesis by auto
  next
    case final 
    from compute_max_gso_quot_alpha(2)[OF inv max alph refl final]
      final show ?thesis using res by auto
  qed
qed

lemma basis_reduction_mod_add_rows_loop_inv': assumes 
  fsinv: "LLL_invariant_mod fs mfs dmu p first b m" 
  and res: "basis_reduction_mod_add_rows_loop p mfs dmu i i = (mfs', dmu')" 
  and i: "i < m" 
shows "\<exists>fs'. LLL_invariant_mod fs' mfs' dmu' p first b m \<and>
        (\<forall>i' j'. i' < i \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs i' j' = \<mu> fs' i' j') \<and>
        \<mu>_small fs' i"
proof -
  {
    fix j
    assume j: "j \<le> i" and mu_small: "\<mu>_small_row i fs j" 
      and resj: "basis_reduction_mod_add_rows_loop p mfs dmu i j = (mfs', dmu')"
    have "\<exists>fs'. LLL_invariant_mod fs' mfs' dmu' p first b m \<and>
        (\<forall>i' j'. i' < i \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs i' j' = \<mu> fs' i' j') \<and>
        (\<mu>_small fs' i)"
    proof (insert fsinv mu_small resj i j, induct j arbitrary: fs mfs dmu mfs' dmu')
      case (0 fs)
      then have "(mfs', dmu') = (mfs, dmu)" by simp
      then show ?case 
        using LLL_invariant_mod_to_weak_m_to_i(3) basis_reduction_add_row_done_weak 0 by auto
    next
      case (Suc j)
      hence j: "j < i" by auto
      have in0: "i \<noteq> 0" using Suc(6) by simp
      define c where "c = round_num_denom (dmu $$ (i,j)) (d_of dmu (Suc j))"
      have c2: "c = round (\<mu> fs i j)" using dmu_quot_is_round_of_\<mu>[OF _ _ i j] c_def Suc by simp
        define mfs'' where "mfs'' = (if c=0 then mfs else mfs[ i := (map_vec (\<lambda> x. x symmod p)) (mfs ! i - c \<cdot>\<^sub>v mfs ! j)])"
        define dmu'' where "dmu'' = (if c=0 then dmu else mat m m (\<lambda>(i',j'). (if (i' = i \<and> j' \<le> j) 
        then (if j'=j then (dmu $$ (i,j') - c * dmu $$ (j,j')) 
              else (dmu $$ (i,j') - c * dmu $$ (j,j')) symmod (p * (d_of dmu j') * (d_of dmu (Suc j'))))
        else (dmu $$ (i',j')))))"
        have 00: "basis_reduction_mod_add_row p mfs dmu i j = (mfs'', dmu'')" 
          using mfs''_def dmu''_def unfolding basis_reduction_mod_add_row_def c_def[symmetric] by simp
        then have 01: "basis_reduction_mod_add_rows_loop p mfs'' dmu'' i j = (mfs', dmu')" 
          using basis_reduction_mod_add_rows_loop.simps(2)[of p mfs dmu i j] Suc by simp
        have fsinvi: "LLL_invariant_mod fs mfs dmu p first b i" using LLL_invariant_mod_to_weak_m_to_i[OF Suc(2)] i by simp
        then have fsinvmw: "LLL_invariant_mod_weak fs mfs dmu p first b" using LLL_invD_mod LLL_invI_modw by simp
        obtain fs'' where fs''invi: "LLL_invariant_mod fs'' mfs'' dmu'' p first b i" and
          \<mu>_small': "(\<mu>_small_row i fs (Suc j) \<longrightarrow> \<mu>_small_row i fs'' j)" and
          \<mu>s: "(\<forall>i' j'. i' < i \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs'' i' j' = \<mu> fs i' j')"
          using Suc basis_reduction_mod_add_row[OF fsinvmw 00 i j] fsinvi by auto
        moreover then have \<mu>sm: "\<mu>_small_row i fs'' j" using Suc by simp
        have fs''invwi: "LLL_invariant_weak' i fs''" using LLL_invD_mod[OF fs''invi] LLL_invI_weak by simp
        have fsinvwi: "LLL_invariant_weak' i fs" using LLL_invD_mod[OF fsinvi] LLL_invI_weak by simp
        note invw = LLL_invw'_imp_w[OF fsinvwi]
        note invw'' = LLL_invw'_imp_w[OF fs''invwi]
        have "LLL_invariant_mod fs'' mfs'' dmu'' p first b m"
        proof -
          have "(\<forall> l. Suc l < m \<longrightarrow> sq_norm (gso fs'' l) \<le> \<alpha> * sq_norm (gso fs'' (Suc l)))"
          proof -
            {
              fix l
              assume l: "Suc l < m"
              have "sq_norm (gso fs'' l) \<le> \<alpha> * sq_norm (gso fs'' (Suc l))"
              proof (cases "i \<le> Suc l")
                case True
                have deq: "\<And>k. k < m \<Longrightarrow> d fs (Suc k) = d fs'' (Suc k)" 
                  using dd\<mu> LLL_invD_mod(9)[OF fs''invi] LLL_invD_mod(9)[OF Suc(2)] dmu''_def j by simp
                {
                  fix k
                  assume k: "k < m"
                  then have "d fs (Suc k) = d fs'' (Suc k)" 
                    using dd\<mu> LLL_invD_mod(9)[OF fs''invi] LLL_invD_mod(9)[OF Suc(2)] dmu''_def j by simp
                  have "d fs 0 = 1" "d fs'' 0 = 1" using d_def by auto
                  moreover have sqid: "sq_norm (gso fs'' k) = rat_of_int (d fs'' (Suc k)) / rat_of_int (d fs'' k)"
                    using LLL_d_Suc[OF invw''] LLL_d_pos[OF invw''] k
                    by (smt One_nat_def Suc_less_eq Suc_pred le_imp_less_Suc mult_eq_0_iff less_imp_le_nat
                        nonzero_mult_div_cancel_right of_int_0_less_iff of_int_hom.hom_zero)
                  moreover have "sq_norm (gso fs k) = rat_of_int (d fs (Suc k)) / rat_of_int (d fs k)"
                    using LLL_d_Suc[OF invw] LLL_d_pos[OF invw] k
                    by (smt One_nat_def Suc_less_eq Suc_pred le_imp_less_Suc mult_eq_0_iff less_imp_le_nat
                        nonzero_mult_div_cancel_right of_int_0_less_iff of_int_hom.hom_zero)
                  ultimately have "sq_norm (gso fs k) = sq_norm (gso fs'' k)" using k deq 
                      LLL_d_pos[OF invw] LLL_d_pos[OF invw'']
                    by (metis (no_types, lifting) Nat.lessE Suc_lessD old.nat.inject zero_less_Suc)
                }
                then show ?thesis using LLL_invD_mod(6)[OF Suc(2)] by (simp add: gram_schmidt_fs.weakly_reduced_def l)
              next
                case False
                then show ?thesis using LLL_invD_mod(6)[OF fs''invi] gram_schmidt_fs.weakly_reduced_def
                  by (metis less_or_eq_imp_le nat_neq_iff)
              qed
            }
            then show ?thesis by simp
          qed
          then have "weakly_reduced fs'' m" using gram_schmidt_fs.weakly_reduced_def by blast
          then show ?thesis using LLL_invD_mod[OF fs''invi] LLL_invI_mod by simp
        qed
        then show ?case using "01" Suc.hyps i j less_imp_le_nat \<mu>sm \<mu>s by metis
    qed
  }
  then show ?thesis using \<mu>_small_row_refl res by auto
qed

lemma basis_reduction_mod_add_rows_outer_loop_inv:
  assumes inv: "LLL_invariant_mod fs mfs dmu p first b m"
  and "(mfs', dmu') = basis_reduction_mod_add_rows_outer_loop p mfs dmu i"
  and i: "i < m"
shows "(\<exists>fs'. LLL_invariant_mod fs' mfs' dmu' p first b m \<and> 
  (\<forall>j. j \<le> i \<longrightarrow> \<mu>_small fs' j))"
proof(insert assms, induct i arbitrary: fs mfs dmu mfs' dmu')
  case (0 fs)
  then show ?case using \<mu>_small_def by auto
next
  case (Suc i fs mfs dmu mfs' dmu')
  obtain mfs'' dmu'' where mfs''dmu'': "(mfs'', dmu'')
    = basis_reduction_mod_add_rows_outer_loop p mfs dmu i" by (metis surj_pair)
  then obtain fs'' where fs'': "LLL_invariant_mod fs'' mfs'' dmu'' p first b m" 
    and 00: "(\<forall>j. j \<le> i \<longrightarrow> \<mu>_small fs'' j)" using Suc by fastforce
  have "(mfs', dmu') = basis_reduction_mod_add_rows_loop p mfs'' dmu'' (Suc i) (Suc i)"
    using Suc(3,4) mfs''dmu'' by (smt basis_reduction_mod_add_rows_outer_loop.simps(2) case_prod_conv)
  then obtain fs' where 01: "LLL_invariant_mod fs' mfs' dmu' p first b m" 
    and 02: "\<forall>i' j'. i' < (Suc i) \<longrightarrow> j' \<le> i' \<longrightarrow> \<mu> fs'' i' j' = \<mu> fs' i' j'" and 03: "\<mu>_small fs' (Suc i)"
    using fs'' basis_reduction_mod_add_rows_loop_inv' Suc by metis
  moreover have "\<forall>j. j \<le> (Suc i) \<longrightarrow> \<mu>_small fs' j" using 02 00 03 \<mu>_small_def by (simp add: le_Suc_eq)
  ultimately show ?case by blast
qed

lemma basis_reduction_mod_fs_bound:
  assumes Linv: "LLL_invariant_mod fs mfs dmu p first b k"
  and mu_small: "\<mu>_small fs i"
  and i: "i < m"
  and nFirst: "\<not> first" 
shows "fs ! i = mfs ! i"
proof -
  from LLL_invD_mod(16-17)[OF Linv] nFirst g_bnd_mode_def
  have gbnd: "g_bnd b fs" and bp: "b \<le> (rat_of_int (p - 1))\<^sup>2 / (rat_of_nat m + 3)" 
    by (auto simp: mod_invariant_def bound_number_def)
  have Linvw: "LLL_invariant_weak' k fs" using LLL_invD_mod[OF Linv] LLL_invI_weak by simp
  have "fs_int_indpt n fs" using LLL_invD_mod(5)[OF Linv] Gram_Schmidt_2.fs_int_indpt.intro by simp
  then interpret fs: fs_int_indpt n fs
    using fs_int_indpt.sq_norm_fs_via_sum_mu_gso by simp
  have "\<parallel>gso fs 0\<parallel>\<^sup>2 \<le> b" using gbnd i unfolding g_bnd_def by blast
  then have b0: "0 \<le> b" using sq_norm_vec_ge_0 dual_order.trans by auto
  have 00: "of_int \<parallel>fs ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<Suc i]. (\<mu> fs i j)\<^sup>2 * \<parallel>gso fs j\<parallel>\<^sup>2)" 
    using fs.sq_norm_fs_via_sum_mu_gso LLL_invD_mod[OF Linv] Gram_Schmidt_2.fs_int_indpt.intro i by simp 
  have 01: "\<forall>j < i. (\<mu> fs i j)\<^sup>2 * \<parallel>gso fs j\<parallel>\<^sup>2 \<le> (1 / rat_of_int 4) * \<parallel>gso fs j\<parallel>\<^sup>2"
  proof -
    {
      fix j
      assume j: "j < i"
      then have "\<bar>fs.gs.\<mu> i j\<bar> \<le> 1 / (rat_of_int 2)" 
        using mu_small Power.linordered_idom_class.abs_square_le_1 j unfolding \<mu>_small_def by simp
      moreover have "\<bar>\<mu> fs i j\<bar> \<ge> 0" by simp
      ultimately have "\<bar>\<mu> fs i j\<bar>\<^sup>2 \<le> (1 / rat_of_int 2)\<^sup>2" 
        using Power.linordered_idom_class.abs_le_square_iff by fastforce
      also have "\<dots> = 1 / (rat_of_int 4)" by (simp add: field_simps)
      finally have "\<bar>\<mu> fs i j\<bar>\<^sup>2 \<le> 1 / rat_of_int 4" by simp
    }
    then show ?thesis using fs.gs.\<mu>.simps by (metis mult_right_mono power2_abs sq_norm_vec_ge_0)
  qed
  then have 0111: "\<And>j. j \<in> set [0..<i] \<Longrightarrow> (\<mu> fs i j)\<^sup>2 * \<parallel>gso fs j\<parallel>\<^sup>2 \<le> (1 / rat_of_int 4) * \<parallel>gso fs j\<parallel>\<^sup>2"
    by simp
  {
    fix j
    assume j: "j < n" 
    have 011: "(\<mu> fs i i)\<^sup>2 * \<parallel>gso fs i\<parallel>\<^sup>2 = 1 * \<parallel>gso fs i\<parallel>\<^sup>2"
      using fs.gs.\<mu>.simps by simp
    have 02: "\<forall>j < Suc i. \<parallel>gso fs j\<parallel>\<^sup>2 \<le> b"
      using gbnd i unfolding g_bnd_def by simp
    have 03: "length [0..<Suc i] = (Suc i)" by simp
    have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 = (\<Sum>j\<leftarrow>[0..<i]. (\<mu> fs i j)\<^sup>2 * \<parallel>gso fs j\<parallel>\<^sup>2) + \<parallel>gso fs i\<parallel>\<^sup>2"
      unfolding 00 using 011 by simp
    also have "(\<Sum>j\<leftarrow>[0..<i]. (\<mu> fs i j)\<^sup>2 * \<parallel>gso fs j\<parallel>\<^sup>2) \<le> (\<Sum>j\<leftarrow>[0..<i]. ((1 / rat_of_int 4) * \<parallel>gso fs j\<parallel>\<^sup>2))"
      using Groups_List.sum_list_mono[OF 0111] by fast
    finally have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 \<le> (\<Sum>j\<leftarrow>[0..<i]. ((1 / rat_of_int 4) * \<parallel>gso fs j\<parallel>\<^sup>2)) + \<parallel>gso fs i\<parallel>\<^sup>2"
      by simp
    also have "(\<Sum>j\<leftarrow>[0..<i]. ((1 / rat_of_int 4) * \<parallel>gso fs j\<parallel>\<^sup>2)) \<le> (\<Sum>j\<leftarrow>[0..<i]. (1 / rat_of_int 4) * b)" 
      by (intro sum_list_mono, insert 02, auto)
    also have " \<parallel>gso fs i\<parallel>\<^sup>2 \<le> b" using 02 by simp
    finally have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 \<le> (\<Sum>j\<leftarrow>[0..<i]. (1 / rat_of_int 4) * b) + b" by simp
    also have "\<dots> = (rat_of_nat i) * ((1 / rat_of_int 4) *  b) + b" 
      using 03 sum_list_triv[of "(1 / rat_of_int 4) * b" "[0..<i]"] by simp
    also have "\<dots> = (rat_of_nat i) / 4 * b + b" by simp
    also have "\<dots> = ((rat_of_nat i) / 4 + 1)* b" by algebra
    also have "\<dots> = (rat_of_nat i + 4) / 4 * b" by simp
    finally have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 \<le> (rat_of_nat i + 4) / 4 * b" by simp
    also have "\<dots> \<le> (rat_of_nat (m + 3)) / 4 * b" using i b0 times_left_mono by fastforce
    finally have "of_int \<parallel>fs ! i\<parallel>\<^sup>2 \<le> rat_of_nat (m+3) / 4 * b" by simp
    moreover have "\<bar>fs ! i $ j\<bar>\<^sup>2 \<le> \<parallel>fs ! i\<parallel>\<^sup>2" using vec_le_sq_norm LLL_invD_mod(10)[OF Linv] i j by blast
    ultimately have 04: "of_int (\<bar>fs ! i $ j\<bar>\<^sup>2) \<le> rat_of_nat (m+3) / 4 * b" using ge_trans i by linarith
    then have 05: "real_of_int (\<bar>fs ! i $ j\<bar>\<^sup>2) \<le> real_of_rat (rat_of_nat (m+3) / 4 * b)" 
    proof -
      from j have "rat_of_int (\<bar>fs ! i $ j\<bar>\<^sup>2) \<le> rat_of_nat (m+3) / 4 * b" using 04 by simp
      then have "real_of_int (\<bar>fs ! i $ j\<bar>\<^sup>2) \<le> real_of_rat (rat_of_nat (m+3) / 4 * b)" 
        using j of_rat_less_eq by (metis of_rat_of_int_eq)
      then show ?thesis by simp
    qed
    define rhs where "rhs = real_of_rat (rat_of_nat (m+3) / 4 * b)"
    have rhs0: "rhs \<ge> 0" using b0 i rhs_def by simp
    have fsij: "real_of_int \<bar>fs ! i $ j\<bar> \<ge> 0" by simp
    have "real_of_int (\<bar>fs ! i $ j\<bar>\<^sup>2) = (real_of_int \<bar>fs ! i $ j\<bar>)\<^sup>2" by simp
    then have "(real_of_int \<bar>fs ! i $ j\<bar>)\<^sup>2 \<le> rhs" using 05 j rhs_def by simp
    then have g1: "real_of_int \<bar>fs ! i $ j\<bar> \<le> sqrt rhs" using NthRoot.real_le_rsqrt by simp
    have pbnd: "2 * \<bar>fs ! i $ j\<bar> < p"
    proof -
      have "rat_of_nat (m+3) / 4 * b \<le> (rat_of_nat (m +3) / 4) * (rat_of_int (p - 1))\<^sup>2 / (rat_of_nat m+3)"
        using bp b0 i times_left_mono SN_Orders.of_nat_ge_zero gs.m_comm times_divide_eq_right 
        by (smt gs.l_null le_divide_eq_numeral1(1))
      also have "\<dots> = (rat_of_int (p - 1))\<^sup>2 / 4 * (rat_of_nat (m + 3) / rat_of_nat (m + 3))"
        by (metis (no_types, lifting) gs.m_comm of_nat_add of_nat_numeral times_divide_eq_left)
      finally have "rat_of_nat (m+3) / 4 * b \<le> (rat_of_int (p - 1))\<^sup>2 / 4" by simp
      then have "sqrt rhs \<le> sqrt (real_of_rat ((rat_of_int (p - 1))\<^sup>2 / 4))"
        unfolding rhs_def using of_rat_less_eq by fastforce
      then have two_ineq: 
        "2 * \<bar>fs ! i $ j\<bar> \<le> 2 * sqrt (real_of_rat ((rat_of_int (p - 1))\<^sup>2 / 4))"
        using g1 by linarith
      have "2 * sqrt (real_of_rat ((rat_of_int (p - 1))\<^sup>2 / 4)) =
      sqrt (real_of_rat (4 * ((rat_of_int (p - 1))\<^sup>2 / 4)))"
        by (metis (no_types, hide_lams) real_sqrt_mult of_int_numeral of_rat_hom.hom_mult 
            of_rat_of_int_eq real_sqrt_four times_divide_eq_right)
      also have "\<dots> = sqrt (real_of_rat ((rat_of_int (p - 1))\<^sup>2))" using i by simp
      also have "(real_of_rat ((rat_of_int (p - 1))\<^sup>2)) = (real_of_rat (rat_of_int (p - 1)))\<^sup>2"
        using Rat.of_rat_power by blast
      also have "sqrt ((real_of_rat (rat_of_int (p - 1)))\<^sup>2) = real_of_rat (rat_of_int (p - 1))"
        using LLL_invD_mod(15)[OF Linv] by simp
      finally have "2 * sqrt (real_of_rat ((rat_of_int (p - 1))\<^sup>2 / 4)) =
      real_of_rat (rat_of_int (p - 1))" by simp
      then have "2 * \<bar>fs ! i $ j\<bar> \<le> real_of_rat (rat_of_int (p - 1))"
        using two_ineq by simp
      then show ?thesis by (metis of_int_le_iff of_rat_of_int_eq zle_diff1_eq)
    qed
    have p1: "p > 1" using LLL_invD_mod[OF Linv] by blast
    interpret pm: poly_mod_2 p
      by (unfold_locales, rule p1)
    from LLL_invD_mod[OF Linv] have len: "length fs = m" and fs: "set fs \<subseteq> carrier_vec n" by auto
    from pm.inv_M_rev[OF pbnd, unfolded pm.M_def] have "pm.inv_M (fs ! i $ j mod p) = fs ! i $ j" .
    also have "pm.inv_M (fs ! i $ j mod p) = mfs ! i $ j" unfolding LLL_invD_mod(7)[OF Linv, symmetric] sym_mod_def
      using i j len fs by auto
    finally have "fs ! i $ j = mfs ! i $ j" ..
  }
  thus "fs ! i = mfs ! i" using LLL_invD_mod(10,13)[OF Linv i] by auto
qed

lemma basis_reduction_mod_fs_bound_first:
  assumes Linv: "LLL_invariant_mod fs mfs dmu p first b k"
  and m0: "m > 0"
  and first: "first" 
shows "fs ! 0 = mfs ! 0"
proof -
  from LLL_invD_mod(16-17)[OF Linv] first g_bnd_mode_def m0
  have gbnd: "sq_norm (gso fs 0) \<le> b" and bp: "b \<le> (rat_of_int (p - 1))\<^sup>2 / 4" 
    by (auto simp: mod_invariant_def bound_number_def)
  from LLL_invD_mod[OF Linv] have p1: "p > 1" by blast
  have Linvw: "LLL_invariant_weak' k fs" using LLL_invD_mod[OF Linv] LLL_invI_weak by simp
  have "fs_int_indpt n fs" using LLL_invD_mod(5)[OF Linv] Gram_Schmidt_2.fs_int_indpt.intro by simp
  then interpret fs: fs_int_indpt n fs
    using fs_int_indpt.sq_norm_fs_via_sum_mu_gso by simp
  from gbnd have b0: "0 \<le> b" using sq_norm_vec_ge_0 dual_order.trans by auto
  have "of_int \<parallel>fs ! 0\<parallel>\<^sup>2 = (\<mu> fs 0 0)\<^sup>2 * \<parallel>gso fs 0\<parallel>\<^sup>2" 
    using fs.sq_norm_fs_via_sum_mu_gso LLL_invD_mod[OF Linv] Gram_Schmidt_2.fs_int_indpt.intro m0 by simp 
  also have "\<dots> = \<parallel>gso fs 0\<parallel>\<^sup>2" unfolding fs.gs.\<mu>.simps by (simp add: gs.\<mu>.simps)
  also have "\<dots> \<le> (rat_of_int (p - 1))\<^sup>2 / 4" using gbnd bp by auto
  finally have one: "of_int (sq_norm (fs ! 0)) \<le> (rat_of_int (p - 1))\<^sup>2 / 4" .
  {
    fix j
    assume j: "j < n" 
    have leq: "\<bar>fs ! 0 $ j\<bar>\<^sup>2 \<le> \<parallel>fs ! 0\<parallel>\<^sup>2" using vec_le_sq_norm LLL_invD_mod(10)[OF Linv] m0 j by blast
    have "rat_of_int ((2 * \<bar>fs ! 0 $ j\<bar>)^2) = rat_of_int (4 * \<bar>fs ! 0 $ j\<bar>\<^sup>2)" by simp
    also have "\<dots> \<le> 4 * of_int \<parallel>fs ! 0\<parallel>\<^sup>2" using leq by simp
    also have "\<dots> \<le> 4 * (rat_of_int (p - 1))\<^sup>2 / 4" using one by simp
    also have "\<dots> = (rat_of_int (p - 1))\<^sup>2" by simp
    also have "\<dots> = rat_of_int ((p - 1)\<^sup>2)" by simp
    finally have "(2 * \<bar>fs ! 0 $ j\<bar>)^2 \<le> (p - 1)\<^sup>2" by linarith
    hence "2 * \<bar>fs ! 0 $ j\<bar> \<le> p - 1" using p1 
      by (smt power_mono_iff zero_less_numeral)
    hence pbnd: "2 * \<bar>fs ! 0 $ j\<bar> < p" by simp
    interpret pm: poly_mod_2 p
      by (unfold_locales, rule p1)
    from LLL_invD_mod[OF Linv] m0 have len: "length fs = m" "length mfs = m" 
      and fs: "fs ! 0 \<in> carrier_vec n" "mfs ! 0 \<in> carrier_vec n" by auto
    from pm.inv_M_rev[OF pbnd, unfolded pm.M_def] have "pm.inv_M (fs ! 0 $ j mod p) = fs ! 0 $ j" .
    also have "pm.inv_M (fs ! 0 $ j mod p) = mfs ! 0 $ j" unfolding LLL_invD_mod(7)[OF Linv, symmetric] sym_mod_def
      using m0 j len fs by auto
    finally have "mfs ! 0 $ j = fs ! 0 $ j" . 
  }
  thus "fs ! 0 = mfs ! 0" using LLL_invD_mod(10,13)[OF Linv m0] by auto
qed

lemma dmu_initial: "dmu_initial = mat m m (\<lambda> (i,j). d\<mu> fs_init i j)"
proof -
  interpret fs: fs_int_indpt n fs_init
    by (unfold_locales, intro lin_dep)
  show ?thesis unfolding dmu_initial_def Let_def
  proof (intro cong_mat refl refl, unfold split, goal_cases)
    case (1 i j)
    show ?case
    proof (cases "j \<le> i")
      case False
      thus ?thesis by (auto simp: d\<mu>_def gs.\<mu>.simps)
    next
      case True
      hence id: "d\<mu>_impl fs_init !! i !! j = fs.d\<mu> i j" unfolding fs.d\<mu>_impl
        by (subst of_fun_nth, use 1 len in force, subst of_fun_nth, insert True, auto)
      also have "\<dots> = d\<mu> fs_init i j" unfolding fs.d\<mu>_def d\<mu>_def fs.d_def d_def by simp
      finally show ?thesis using True by auto
    qed
  qed
qed

lemma LLL_initial_invariant_mod: assumes res: "compute_initial_state first = (p, mfs, dmu', g_idx)" 
shows "\<exists>fs b. LLL_invariant_mod fs mfs dmu' p first b 0" 
proof -
  from dmu_initial have dmu: "(\<forall>i' < m. \<forall>j' < m. d\<mu> fs_init i' j' = dmu_initial $$ (i',j'))" by auto
  obtain b g_idx where norm: "compute_max_gso_norm first dmu_initial = (b,g_idx)" by force
  note res = res[unfolded compute_initial_state_def Let_def norm split]
  from res have p: "p = compute_mod_of_max_gso_norm first b" by auto
  then have p0: "p > 0" unfolding compute_mod_of_max_gso_norm_def using log_base by simp
  then have p1: "p \<ge> 1" by simp
  note res = res[folded p]
  from res[unfolded compute_initial_mfs_def]
  have mfs: "mfs = map (map_vec (\<lambda>x. x symmod p)) fs_init" by auto
  from res[unfolded compute_initial_dmu_def]
  have dmu': "dmu' = mat m m (\<lambda>(i',j'). if j' < i' 
              then dmu_initial $$ (i', j') symmod (p * d_of dmu_initial j' * d_of dmu_initial (Suc j')) 
              else dmu_initial $$ (i',j'))" by auto
  have lat: "lattice_of fs_init = L" by (auto simp: L_def)
  define I where "I = {(i',j'). i' < m \<and> j' < i'}"
  obtain fs where 
    01: "lattice_of fs = L" and
    02: "map (map_vec (\<lambda> x. x symmod p)) fs = map (map_vec (\<lambda> x. x symmod p)) fs_init" and
    03: "lin_indep fs" and
    04: "length fs = m" and
    05: "(\<forall> k < m. gso fs k = gso fs_init k)" and
    06: "(\<forall> k \<le> m. d fs k = d fs_init k)" and
    07: "(\<forall> i' < m. \<forall> j' < m. d\<mu> fs i' j' = 
      (if (i',j') \<in> I then d\<mu> fs_init i' j' symmod (p * d fs_init j' * d fs_init (Suc j')) else d\<mu> fs_init i' j'))"
    using mod_finite_set[OF lin_dep len _ lat p0, of I] I_def by blast
  have inv: "LLL_invariant_weak fs_init"
    by (intro LLL_inv_wI lat len lin_dep fs_init)
  have "\<forall>i'<m. d\<mu> fs_init i' i' = dmu_initial $$ (i', i')" unfolding dmu_initial by auto
  from compute_max_gso_norm[OF this inv, of first, unfolded norm] have gbnd: "g_bnd_mode first b fs_init" 
    and b0: "0 \<le> b" and mb0: "m = 0 \<Longrightarrow> b = 0" by auto
  from gbnd 05 have gbnd: "g_bnd_mode first b fs" using g_bnd_mode_cong[of fs fs_init] by auto
  have d\<mu>dmu': "\<forall>i'<m. \<forall>j'<m. d\<mu> fs i' j' = dmu' $$ (i', j')" using 07 dmu d_of_main[of fs_init dmu_initial]
    unfolding I_def dmu' by simp
  have wred: "weakly_reduced fs 0" by (simp add: gram_schmidt_fs.weakly_reduced_def)
  have fs_carr: "set fs \<subseteq> carrier_vec n" using 03 unfolding gs.lin_indpt_list_def by force
  have m0: "m \<ge> 0" using len by auto 
  have Linv: "LLL_invariant_weak' 0 fs"
    by (intro LLL_invI_weak 03 04 01 wred fs_carr m0)
  note Linvw = LLL_invw'_imp_w[OF Linv]
  from compute_mod_of_max_gso_norm[OF b0 mb0 p]
  have p: "mod_invariant b p first" "p > 1" by auto
  from len mfs have len': "length mfs = m" by auto
  have modbnd: "\<forall>i'<m. \<forall>j'<i'. \<bar>d\<mu> fs i' j'\<bar> < p * d fs j' * d fs (Suc j')"
  proof -
    have "\<forall> i' < m. \<forall> j' < i'. d\<mu> fs i' j' = d\<mu> fs i' j' symmod (p * d fs j' * d fs (Suc j'))"
      using I_def 07 06 by simp
    moreover have "\<forall>j' < m. p * d fs j' * d fs (Suc j') > 0" using p(2) LLL_d_pos[OF Linvw] by simp
    ultimately show ?thesis using sym_mod_abs
      by (smt Euclidean_Division.pos_mod_bound Euclidean_Division.pos_mod_sign less_trans)
  qed
  have "LLL_invariant_mod fs mfs dmu' p first b 0" 
    using LLL_invI_mod[OF len' m0 04 01 03 wred _ modbnd d\<mu>dmu' p(2) gbnd p(1)] 02 mfs by simp
  then show ?thesis by auto
qed

subsection \<open>Soundness of Storjohann's algorithm\<close>

text \<open>For all of these abstract algorithms, we actually formulate their soundness proofs by linking
  to the LLL-invariant (which implies that @{term fs} is reduced (@{term "LLL_invariant True m fs"})
  or that the first vector of @{term fs} is short (@{term "LLL_invariant_weak fs \<and> weakly_reduced fs m"}).\<close>

text \<open>Soundness of Storjohann's algorithm\<close>
lemma reduce_basis_mod_inv: assumes res: "reduce_basis_mod = fs"    
  shows "LLL_invariant True m fs" 
proof (cases "m = 0")
  case True
  from True have *: "fs_init = []" using len by simp
  moreover have "fs = []" using res basis_reduction_mod_add_rows_outer_loop.simps(1)
    unfolding reduce_basis_mod_def Let_def basis_reduction_mod_main.simps[of _ _ _ _ _ 0] 
      compute_initial_mfs_def compute_initial_state_def compute_initial_dmu_def 
    unfolding True * by (auto split: prod.splits)
  ultimately show ?thesis using True LLL_inv_initial_state by blast
next
  case False
  let ?first = False
  obtain p mfs0 dmu0 g_idx0 where init: "compute_initial_state ?first = (p, mfs0, dmu0, g_idx0)" by (metis prod_cases4)
  from LLL_initial_invariant_mod[OF init]
  obtain fs0 b where fs0: "LLL_invariant_mod fs0 mfs0 dmu0 p ?first b 0" by blast
  note res = res[unfolded reduce_basis_mod_def init Let_def split]
  obtain p1 mfs1 dmu1 where mfs1dmu1: "(p1, mfs1, dmu1) = basis_reduction_mod_main p ?first mfs0 dmu0 g_idx0 0 0"
    by (metis prod.exhaust)
  obtain fs1 b1 where Linv1: "LLL_invariant_mod fs1 mfs1 dmu1 p1 ?first b1 m"
    using basis_reduction_mod_main[OF fs0 mfs1dmu1[symmetric]] by auto
  obtain mfs2 dmu2 where mfs2dmu2:
    "(mfs2, dmu2) = basis_reduction_mod_add_rows_outer_loop p1 mfs1 dmu1 (m-1)" by (metis old.prod.exhaust)
  obtain fs2 where fs2: "LLL_invariant_mod fs2 mfs2 dmu2 p1 ?first b1 m" 
    and \<mu>s: "((\<forall>j. j < m \<longrightarrow> \<mu>_small fs2 j))"
    using basis_reduction_mod_add_rows_outer_loop_inv[OF _ mfs2dmu2, of fs1 ?first b1] Linv1 False by auto
  have rbd: "LLL_invariant_weak' m fs2" "\<forall>j < m. \<mu>_small fs2 j"
    using LLL_invD_mod[OF fs2] LLL_invI_weak \<mu>s by auto
  have redfs2: "reduced fs2 m" using rbd LLL_invD_weak(8) gram_schmidt_fs.reduced_def \<mu>_small_def by blast
  have fs: "fs = mfs2" 
    using res[folded mfs1dmu1, unfolded Let_def split, folded mfs2dmu2, unfolded split] .. 
  have "\<forall>i < m. fs2 ! i = fs ! i"
  proof (intro allI impI)
    fix i
    assume i: "i < m"
    then have fs2i: "LLL_invariant_mod fs2 mfs2 dmu2 p1 ?first b1 i"
      using fs2 LLL_invariant_mod_to_weak_m_to_i by simp
    have \<mu>si: "\<mu>_small fs2 i" using \<mu>s i by simp
    show "fs2 ! i = fs ! i" 
      using basis_reduction_mod_fs_bound(1)[OF fs2i \<mu>si i] fs by simp
  qed
  then have "fs2 = fs"
    using LLL_invD_mod(1,3,10,13)[OF fs2] fs by (metis nth_equalityI)
  then show ?thesis using redfs2 fs rbd(1) reduce_basis_def res LLL_invD_weak 
      LLL_invariant_def by simp
qed

text \<open>Soundness of Storjohann's algorithm for computing a short vector.\<close>
lemma short_vector_mod_inv: assumes res: "short_vector_mod = v"    
  and m: "m > 0" 
  shows "\<exists> fs. LLL_invariant_weak fs \<and> weakly_reduced fs m \<and> v = hd fs" 
proof -
  let ?first = True
  obtain p mfs0 dmu0 g_idx0 where init: "compute_initial_state ?first = (p, mfs0, dmu0, g_idx0)" by (metis prod_cases4)
  from LLL_initial_invariant_mod[OF init]
  obtain fs0 b where fs0: "LLL_invariant_mod fs0 mfs0 dmu0 p ?first b 0" by blast
  obtain p1 mfs1 dmu1 where main: "basis_reduction_mod_main p ?first mfs0 dmu0 g_idx0 0 0 = (p1, mfs1, dmu1)"
    by (metis prod.exhaust)
  obtain fs1 b1 where Linv1: "LLL_invariant_mod fs1 mfs1 dmu1 p1 ?first b1 m"
    using basis_reduction_mod_main[OF fs0 main] by auto
  have "v = hd mfs1" using res[unfolded short_vector_mod_def Let_def init split main] ..
  with basis_reduction_mod_fs_bound_first[OF Linv1 m] LLL_invD_mod(1,3)[OF Linv1] m
  have v: "v = hd fs1" by (cases fs1; cases mfs1; auto)
  from Linv1 have Linv1: "LLL_invariant_weak fs1" and red: "weakly_reduced fs1 m" 
    unfolding LLL_invariant_mod_def LLL_invariant_weak_def by auto
  show ?thesis  
    by (intro exI[of _ fs1] conjI Linv1 red v)
qed

text \<open>Soundness of Storjohann's algorithm with improved swap order\<close>
lemma reduce_basis_iso_inv: assumes res: "reduce_basis_iso = fs"
  shows "LLL_invariant True m fs" 
proof (cases "m = 0")
  case True
  then have *: "fs_init = []" using len by simp
  moreover have "fs = []" using res basis_reduction_mod_add_rows_outer_loop.simps(1)
    unfolding reduce_basis_iso_def Let_def basis_reduction_iso_main.simps[of _ _ _ _ _ 0] 
      compute_initial_mfs_def compute_initial_state_def compute_initial_dmu_def
    unfolding True * by (auto split: prod.splits)
  ultimately show ?thesis using True LLL_inv_initial_state by blast
next
  case False
  let ?first = False
  obtain p mfs0 dmu0 g_idx0 where init: "compute_initial_state ?first = (p, mfs0, dmu0, g_idx0)" by (metis prod_cases4)
  from LLL_initial_invariant_mod[OF init]
  obtain fs0 b where fs0: "LLL_invariant_mod fs0 mfs0 dmu0 p ?first b 0" by blast
  have fs0w: "LLL_invariant_mod_weak fs0 mfs0 dmu0 p ?first b" using LLL_invD_mod[OF fs0] LLL_invI_modw by simp 
  note res = res[unfolded reduce_basis_iso_def init Let_def split]
  obtain p1 mfs1 dmu1 where mfs1dmu1: "(p1, mfs1, dmu1) = basis_reduction_iso_main p ?first mfs0 dmu0 g_idx0 0"
    by (metis prod.exhaust)
  obtain fs1 b1 where Linv1: "LLL_invariant_mod fs1 mfs1 dmu1 p1 ?first b1 m"
    using basis_reduction_iso_main[OF fs0w mfs1dmu1[symmetric]] by auto
  obtain mfs2 dmu2 where mfs2dmu2:
    "(mfs2, dmu2) = basis_reduction_mod_add_rows_outer_loop p1 mfs1 dmu1 (m-1)" by (metis old.prod.exhaust)
  obtain fs2 where fs2: "LLL_invariant_mod fs2 mfs2 dmu2 p1 ?first b1 m" 
    and \<mu>s: "((\<forall>j. j < m \<longrightarrow> \<mu>_small fs2 j))"
    using basis_reduction_mod_add_rows_outer_loop_inv[OF _ mfs2dmu2, of fs1 ?first b1] Linv1 False by auto
  have rbd: "LLL_invariant_weak' m fs2" "\<forall>j < m. \<mu>_small fs2 j"
    using LLL_invD_mod[OF fs2] LLL_invI_weak \<mu>s by auto
  have redfs2: "reduced fs2 m" using rbd LLL_invD_weak(8) gram_schmidt_fs.reduced_def \<mu>_small_def by blast
  have fs: "fs = mfs2" 
    using res[folded mfs1dmu1, unfolded Let_def split, folded mfs2dmu2, unfolded split] .. 
  have "\<forall>i < m. fs2 ! i = fs ! i"
  proof (intro allI impI)
    fix i
    assume i: "i < m"
    then have fs2i: "LLL_invariant_mod fs2 mfs2 dmu2 p1 ?first b1 i"
      using fs2 LLL_invariant_mod_to_weak_m_to_i by simp
    have \<mu>si: "\<mu>_small fs2 i" using \<mu>s i by simp
    show "fs2 ! i = fs ! i" 
      using basis_reduction_mod_fs_bound(1)[OF fs2i \<mu>si i] fs by simp
  qed
  then have "fs2 = fs"
    using LLL_invD_mod(1,3,10,13)[OF fs2] fs by (metis nth_equalityI)
  then show ?thesis using redfs2 fs rbd(1) reduce_basis_def res LLL_invD_weak 
      LLL_invariant_def by simp
qed

text \<open>Soundness of Storjohann's algorithm to compute short vectors with improved swap order\<close>
lemma short_vector_iso_inv: assumes res: "short_vector_iso = v"    
  and m: "m > 0" 
  shows "\<exists> fs. LLL_invariant_weak fs \<and> weakly_reduced fs m \<and> v = hd fs" 
proof -
  let ?first = True
  obtain p mfs0 dmu0 g_idx0 where init: "compute_initial_state ?first = (p, mfs0, dmu0, g_idx0)" by (metis prod_cases4)
  from LLL_initial_invariant_mod[OF init]
  obtain fs0 b where fs0: "LLL_invariant_mod fs0 mfs0 dmu0 p ?first b 0" by blast
  have fs0w: "LLL_invariant_mod_weak fs0 mfs0 dmu0 p ?first b" using LLL_invD_mod[OF fs0] LLL_invI_modw by simp 
  obtain p1 mfs1 dmu1 where main: "basis_reduction_iso_main p ?first mfs0 dmu0 g_idx0 0 = (p1, mfs1, dmu1)"
    by (metis prod.exhaust)
  obtain fs1 b1 where Linv1: "LLL_invariant_mod fs1 mfs1 dmu1 p1 ?first b1 m"
    using basis_reduction_iso_main[OF fs0w main] by auto
  have "v = hd mfs1" using res[unfolded short_vector_iso_def Let_def init split main] ..
  with basis_reduction_mod_fs_bound_first[OF Linv1 m] LLL_invD_mod(1,3)[OF Linv1] m
  have v: "v = hd fs1" by (cases fs1; cases mfs1; auto)
  from Linv1 have Linv1: "LLL_invariant_weak fs1" and red: "weakly_reduced fs1 m" 
    unfolding LLL_invariant_mod_def LLL_invariant_weak_def by auto
  show ?thesis  
    by (intro exI[of _ fs1] conjI Linv1 red v)
qed

end

text \<open>From the soundness results of these abstract versions of the algorithms, 
  one just needs to derive actual implementations that may integrate low-level
  optimizations.\<close>

end
