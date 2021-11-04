section \<open>Storjohann's basis reduction algorithm (concrete implementation)\<close>

text \<open>We refine the abstract algorithm into a more efficient executable one.\<close>

theory Storjohann_Impl
  imports 
    Storjohann
begin

subsection \<open>Implementation\<close>

text \<open>We basically store four components:
  \<^item> The $f$-basis (as list, all values taken modulo $p$)
  \<^item> The $d\mu$-matrix (as nested arrays, all values taken modulo $d_id_{i+1}p$)
  \<^item> The $d$-values (as array)
  \<^item> The modulo-values $d_id_{i+1}p$ (as array)
\<close>

type_synonym state_impl = "int vec list \<times> int iarray iarray \<times> int iarray \<times> int iarray" 

fun di_of :: "state_impl \<Rightarrow> int iarray" where
  "di_of (mfsi, dmui, di, mods) = di" 

context LLL
begin

fun state_impl_inv :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> state_impl \<Rightarrow> bool" where 
  "state_impl_inv p mfs dmu (mfsi, dmui, di, mods) = (mfsi = mfs \<and> di = IArray.of_fun (d_of dmu) (Suc m)
     \<and> dmui = IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. dmu $$ (i,j)) i) m
     \<and> mods = IArray.of_fun (\<lambda> j. p * di !! j * di !! (Suc j)) (m - 1))" 

definition state_iso_inv :: "(int \<times> int) iarray \<Rightarrow> int iarray \<Rightarrow> bool" where
  "state_iso_inv prods di = (prods = IArray.of_fun 
           (\<lambda> i. (di !! (i+1) * di !! (i+1), di !! (i+2) * di !! i)) (m - 1))" 

definition perform_add_row :: "int \<Rightarrow> state_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int iarray \<Rightarrow> int \<Rightarrow> int \<Rightarrow> state_impl" where
  "perform_add_row p state i j c rowi muij dij1 = (let
     (mfsi, dmui, di, mods) = state;
       fsj = mfsi ! j;
        rowj = dmui !! j
      in 
      (case split_at i mfsi of (start, fsi # end) \<Rightarrow> start @ vec n (\<lambda> k. (fsi $ k - c * fsj $ k) symmod p) # end,
        IArray.of_fun (\<lambda> ii. if i = ii then 
         IArray.of_fun (\<lambda> jj. if jj < j then 
              (rowi !! jj - c * rowj !! jj) symmod (mods !! jj)
            else if jj = j then muij - c * dij1 
            else rowi !! jj) i
        else dmui !! ii) m, 
      di, mods))" 

definition LLL_add_row :: "int \<Rightarrow> state_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state_impl" where
  "LLL_add_row p state i j = (let
     (_, dmui, di, _) = state;
     rowi = dmui !! i;
     dij1 = di !! (Suc j);
     muij = rowi !! j;
     c = round_num_denom muij dij1
     in if c = 0 then state
      else perform_add_row p state i j c rowi muij dij1)"     


definition LLL_swap_row :: "int \<Rightarrow> state_impl \<Rightarrow> nat \<Rightarrow> state_impl" where
  "LLL_swap_row p state k = (case state of (mfsi, dmui, di, mods) \<Rightarrow> let 
        k1 = k - 1;
        kS1 = Suc k;
        muk = dmui !! k; 
        muk1 = dmui !! k1;
        mukk1 = muk !! k1;
        dk1 = di !! k1;
        dkS1 = di !! kS1;
        dk = di !! k;
        dk' = (dkS1 * dk1 + mukk1 * mukk1) div dk;
        mod1 = p * dk1 * dk';
        modk = p * dk' * dkS1
      in 
      (case split_at k1 mfsi
        of (start, fsk1 # fsk # end) \<Rightarrow> start @ fsk # fsk1 # end,
        IArray.of_fun (\<lambda> i. 
          if i < k1 then dmui !! i
          else if i > k then 
             let row_i = dmui !! i; muik = row_i !! k; muik1 = row_i !! k1 in IArray.of_fun 
                 (\<lambda> j. if j = k1 then ((mukk1 * muik1 + muik * dk1) div dk) symmod mod1 
                        else if j = k then ((dkS1 * muik1 - mukk1 * muik) div dk) symmod modk  
                        else row_i !! j) i
          else if i = k then IArray.of_fun (\<lambda> j. if j = k1 then mukk1 symmod mod1 else muk1 !! j) i
          else IArray.of_fun ((!!) muk) i 
          ) m, 
       IArray.of_fun (\<lambda> i. if i = k then dk' else di !! i) (Suc m), 
       IArray.of_fun (\<lambda> j. if j = k1 then mod1 else if j = k then modk else mods !! j) (m - 1)))"

definition perform_swap_add where "perform_swap_add p state k k1 c row_k mukk1 dk = 
(let (fs, dmu, dd, mods) = state; 
     row_k1 = dmu !! k1; 
     kS1 = Suc k;
     mukk1' = mukk1 - c * dk;
     dk1 = dd !! k1; 
     dkS1 = dd !! kS1; 
     dk' = (dkS1 * dk1 + mukk1' * mukk1') div dk; 
     mod1 = p * dk1 * dk'; 
     modk = p * dk' * dkS1
 in 
      (case split_at k1 fs of (start, fsk1 # fsk # end) \<Rightarrow> 
         start @ vec n (\<lambda>k. (fsk $ k - c * fsk1 $ k) symmod p) # fsk1 # end,
       IArray.of_fun
        (\<lambda>i. if i < k1
              then dmu !! i
              else if k < i
                   then let row_i = dmu !! i;
                            muik1 = row_i !! k1;
                            muik = row_i !! k
                        in IArray.of_fun
                            (\<lambda>j. if j = k1 then (mukk1' * muik1 + muik * dk1) div dk symmod mod1
                                 else if j = k then (dkS1 * muik1 - mukk1' * muik) div dk symmod modk 
                                 else row_i !! j)
                            i
                   else if i = k then IArray.of_fun (\<lambda>j. if j = k1 then mukk1' symmod mod1 else row_k1 !! j) k 
                   else IArray.of_fun (\<lambda>j. (row_k !! j - c * row_k1 !! j) symmod mods !! j) i)
        m,
       IArray.of_fun (\<lambda>i. if i = k then dk' else dd !! i) (Suc m), 
       IArray.of_fun (\<lambda>j. if j = k1 then mod1 else if j = k then modk else mods !! j) (m - 1)))" 


definition LLL_swap_add where
  "LLL_swap_add p state i = (let
     i1 = i - 1;
     (_, dmui, di, _) = state;
     rowi = dmui !! i;
     dii = di !! i;
     muij = rowi !! i1;
     c = round_num_denom muij dii
     in if c = 0 then LLL_swap_row p state i
      else perform_swap_add p state i i1 c rowi muij dii)"

definition LLL_max_gso_norm_di :: "bool \<Rightarrow> int iarray \<Rightarrow> rat \<times> nat" where
  "LLL_max_gso_norm_di first di = 
      (if first then (of_int (di !! 1), 0) 
       else case max_list_rats_with_index (map (\<lambda> i. (di !! (Suc i), di !! i, i)) [0 ..< m ])
      of (num, denom, i) \<Rightarrow> (of_int num / of_int denom, i))" 

definition LLL_max_gso_quot:: "(int * int) iarray \<Rightarrow> (int * int * nat)" where
  "LLL_max_gso_quot di_prods = max_list_rats_with_index 
    (map (\<lambda>i. case di_prods !! i of (l,r) \<Rightarrow> (l, r, Suc i)) [0..<(m-1)])"


definition LLL_max_gso_norm :: "bool \<Rightarrow> state_impl \<Rightarrow> rat \<times> nat" where
  "LLL_max_gso_norm first state = (case state of (_, _, di, mods) \<Rightarrow> LLL_max_gso_norm_di first di)" 

definition perform_adjust_mod :: "int \<Rightarrow> state_impl \<Rightarrow> state_impl" where
  "perform_adjust_mod p state = (case state of (mfsi, dmui, di, _) \<Rightarrow> 
          let mfsi' = map (map_vec (\<lambda>x. x symmod p)) mfsi;
              mods = IArray.of_fun (\<lambda> j. p * di !! j * di !! (Suc j)) (m - 1);
              dmui' = IArray.of_fun (\<lambda> i. let row = dmui !! i in IArray.of_fun (\<lambda> j. row !! j symmod (mods !! j)) i) m
        in 
          ((mfsi', dmui', di, mods)))" 

definition mod_of_gso_norm :: "bool \<Rightarrow> rat \<Rightarrow> int" where
  "mod_of_gso_norm first mn = log_base ^ (log_ceiling log_base (max 2 (
     root_rat_ceiling 2 (mn * (rat_of_nat (if first then 4 else m + 3))) + 1)))"

definition LLL_adjust_mod :: "int \<Rightarrow> bool \<Rightarrow> state_impl \<Rightarrow> int \<times> state_impl \<times> nat" where
  "LLL_adjust_mod p first state = ( 
     let (b', g_idx) = LLL_max_gso_norm first state;
       p' = mod_of_gso_norm first b'
      in if p' < p then (p', perform_adjust_mod p' state, g_idx)
          else (p, state, g_idx) 
      )" 

definition LLL_adjust_swap_add where
  "LLL_adjust_swap_add p first state g_idx i = (
      let state1 = LLL_swap_add p state i
      in if i - 1 = g_idx then
      LLL_adjust_mod p first state1 else (p, state1, g_idx))" 


definition LLL_step :: "int \<Rightarrow> bool \<Rightarrow> state_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> (int \<times> state_impl \<times> nat) \<times> nat \<times> int" where
  "LLL_step p first state g_idx i j = (if i = 0 then ((p, state, g_idx), Suc i, j)
     else let 
        i1 = i - 1; 
        iS = Suc i;
        (_, _, di, _) = state;
        (num, denom) = quotient_of \<alpha>;
        d_i = di !! i;
        d_i1 = di !! i1;
        d_Si = di !! iS
       in if d_i * d_i * denom \<le> num * d_i1 * d_Si then
          ((p, state, g_idx), iS, j) 
        else (LLL_adjust_swap_add p first state g_idx i, i1, j + 1))" 

partial_function (tailrec) LLL_main :: "int \<Rightarrow> bool \<Rightarrow> state_impl \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<times> state_impl"
  where
  "LLL_main p first state g_idx i (j :: int) = (
    (if i < m 
     then case LLL_step p first state g_idx i j of
         ((p', state', g_idx'), i', j') \<Rightarrow> 
         LLL_main p' first state' g_idx' i' j'
       else
         (p, state)))"

partial_function (tailrec) LLL_iso_main_inner where
  "LLL_iso_main_inner p first state di_prods g_idx (j :: int) = (
      case state of (_, _, di, _) \<Rightarrow>
    (
      (let (max_gso_num, max_gso_denum, indx) = LLL_max_gso_quot di_prods;
        (num, denum) = quotient_of \<alpha> in
        (if max_gso_num * denum  > num * max_gso_denum then
           case LLL_adjust_swap_add p first state g_idx indx of 
              (p', state', g_idx') \<Rightarrow> case state' of (_, _, di', _) \<Rightarrow> 
              let di_prods' = IArray.of_fun (\<lambda> i. case di_prods !! i of lr \<Rightarrow> 
                    if i > indx \<or> i + 2 < indx then lr
                     else case lr of (l,r) 
                  \<Rightarrow> if i + 1 = indx then let d_idx = di' !! indx in (d_idx * d_idx, r) else (l, di' !! (i + 2) * di' !! i)) (m - 1)
                in LLL_iso_main_inner p' first state' di_prods' g_idx' (j + 1)
         else
           (p, state)))))"

definition LLL_iso_main where
  "LLL_iso_main p first state g_idx j = (if m > 1 then 
     case state of (_, _, di, _) \<Rightarrow>
     let di_prods = IArray.of_fun (\<lambda> i. (di !! (i+1) * di !! (i+1), di !! (i+2) * di !! i)) (m - 1)
      in LLL_iso_main_inner p first state di_prods g_idx j else (p,state))" 


definition LLL_initial :: "bool \<Rightarrow> int \<times> state_impl \<times> nat" where
  "LLL_initial first = (let init = d\<mu>_impl fs_init;
      di = IArray.of_fun (\<lambda> i. if i = 0 then 1 else let i1 = i - 1 in init !! i1 !! i1) (Suc m);
      (b,g_idx) = LLL_max_gso_norm_di first di;
      p = mod_of_gso_norm first b;
      mods = IArray.of_fun (\<lambda> j. p * di !! j * di !! (Suc j)) (m - 1);
      dmui = IArray.of_fun (\<lambda> i. let row = init !! i in IArray.of_fun (\<lambda> j. row !! j symmod (mods !! j)) i) m
      in (p, (compute_initial_mfs p, dmui, di, mods), g_idx))" 

fun LLL_add_rows_loop where
  "LLL_add_rows_loop p state i 0 = state"
| "LLL_add_rows_loop p state i (Suc j) = (
     let state' = LLL_add_row p state i j
      in LLL_add_rows_loop p state' i j)" 

primrec LLL_add_rows_outer_loop where
  "LLL_add_rows_outer_loop p state 0 = state" |
  "LLL_add_rows_outer_loop p state (Suc i) = 
    (let state' = LLL_add_rows_outer_loop p state i in
      LLL_add_rows_loop p state' (Suc i) (Suc i))"

definition 
  "LLL_reduce_basis = (if m = 0 then [] else
     let first = False;
         (p0, state0, g_idx0) = LLL_initial first;
         (p, state) = LLL_main p0 first state0 g_idx0 0 0;
         (mfs,_,_,_) = LLL_add_rows_outer_loop p state (m - 1)
      in mfs)"

definition 
  "LLL_reduce_basis_iso = (if m = 0 then [] else
     let first = False;
         (p0, state0, g_idx0) = LLL_initial first;
         (p, state) = LLL_iso_main p0 first state0 g_idx0 0;
         (mfs,_,_,_) = LLL_add_rows_outer_loop p state (m - 1)
      in mfs)"

definition 
  "LLL_short_vector = (
     let first = True;
         (p0, state0, g_idx0) = LLL_initial first;
         (p, (mfs,_,_,_)) = LLL_main p0 first state0 g_idx0 0 0
      in hd mfs)"

definition 
  "LLL_short_vector_iso = (
     let first = True;
         (p0, state0, g_idx0) = LLL_initial first;
         (p, (mfs,_,_,_)) = LLL_iso_main p0 first state0 g_idx0 0         
      in hd mfs)"

end

declare LLL.LLL_short_vector_def[code]
declare LLL.LLL_short_vector_iso_def[code]
declare LLL.LLL_reduce_basis_def[code]
declare LLL.LLL_reduce_basis_iso_def[code]
declare LLL.LLL_iso_main_def[code]
declare LLL.LLL_iso_main_inner.simps[code]
declare LLL.LLL_add_rows_outer_loop.simps[code]
declare LLL.LLL_add_rows_loop.simps[code]
declare LLL.LLL_initial_def[code]
declare LLL.LLL_main.simps[code]
declare LLL.LLL_adjust_mod_def[code]
declare LLL.LLL_max_gso_norm_def[code]
declare LLL.perform_adjust_mod_def[code]
declare LLL.LLL_max_gso_norm_di_def[code]
declare LLL.LLL_max_gso_quot_def[code]
declare LLL.LLL_step_def[code]
declare LLL.LLL_add_row_def[code]
declare LLL.perform_add_row_def[code]
declare LLL.LLL_swap_row_def[code]
declare LLL.LLL_swap_add_def[code]
declare LLL.LLL_adjust_swap_add_def[code]
declare LLL.perform_swap_add_def[code]
declare LLL.mod_of_gso_norm_def[code]
declare LLL.compute_initial_mfs_def[code]
declare LLL.log_base_def[code]


subsection \<open>Towards soundness proof of implementation\<close>

context LLL
begin
lemma perform_swap_add: assumes k: "k \<noteq> 0" "k < m" and fs: "length fs = m"
  shows "LLL_swap_row p (perform_add_row p (fs, dmu, di, mods) k (k - 1) c (dmu !! k) (dmu !! k !! (k - 1)) (di !! k)) k
    = perform_swap_add p (fs, dmu, di, mods) k (k - 1) c (dmu !! k) (dmu !! k !! (k - 1)) (di !! k)"
proof -
  from k[folded fs] 
  have drop: "drop k fs = fs ! k # drop (Suc k) fs"
    by (simp add: Cons_nth_drop_Suc)
  obtain v where v: "vec n (\<lambda>ka. (fs ! k $ ka - c * fs ! (k - 1) $ ka) symmod p) = v" by auto
  from k[folded fs] 
  have drop1: "drop (k - 1) (take k fs @ v # drop (Suc k) fs) = fs ! (k - 1) # v # drop (Suc k) fs" 
    by (simp add: Cons_nth_drop_Suc) 
      (smt Cons_nth_drop_Suc Suc_diff_Suc Suc_less_eq Suc_pred diff_Suc_less diff_self_eq_0 drop_take less_SucI take_Suc_Cons take_eq_Nil)
  from k[folded fs]
  have drop2: "drop (k - 1) fs = fs ! (k - 1) # fs ! k # drop (Suc k) fs" 
    by (metis Cons_nth_drop_Suc One_nat_def Suc_less_eq Suc_pred less_SucI neq0_conv)
  have take: "take (k - 1) (take k fs @ xs) = take (k - 1) fs" for xs using k[folded fs] by auto
  obtain rowk where rowk: "IArray.of_fun
                             (\<lambda>jj. if jj < k - 1 then (dmu !! k !! jj - c * dmu !! (k - 1) !! jj) symmod mods !! jj
                else if jj = k - 1 then dmu !! k !! (k - 1) - c * di !! k else dmu !! k !! jj) k = rowk" 
    by auto
  obtain mukk1' where mukk1': "(di !! Suc k * di !! (k - 1) + rowk !! (k - 1) * rowk !! (k - 1)) div di !! k = mukk1'" 
    by auto
  have kk1: "k - 1 < k" using k by auto
  have mukk1'': "(di !! Suc k * di !! (k - 1) +
             (dmu !! k !! (k - 1) - c * di !! k) * (dmu !! k !! (k - 1) - c * di !! k)) div
            di !! k = mukk1'"
    unfolding mukk1'[symmetric] rowk[symmetric] IArray.of_fun_nth[OF kk1] by auto
  have id: "(k = k) = True" by simp
  have rowk1: "dmu !! k !! (k - 1) - c * di !! k = rowk !! (k - 1)" 
    unfolding rowk[symmetric] IArray.of_fun_nth[OF kk1] by simp
  show ?thesis 
    unfolding perform_swap_add_def split perform_add_row_def Let_def split LLL_swap_row_def split_at_def
    unfolding drop list.simps v drop1 take prod.inject drop2 rowk IArray.of_fun_nth[OF \<open>k < m\<close>] id if_True
    unfolding rowk1
  proof (intro conjI refl iarray_cong, unfold rowk1[symmetric], goal_cases)    
    case i: (1 i)
    show ?case unfolding IArray.of_fun_nth[OF i] IArray.of_fun_nth[OF \<open>k < m\<close>] id if_True mukk1' mukk1''
      rowk1[symmetric]
    proof (intro if_cong[OF refl], force, goal_cases)
      case 3
      hence i: "i = k - 1" by auto
      show ?case unfolding i by (intro iarray_cong[OF refl], unfold rowk[symmetric],
          subst IArray.of_fun_nth, insert k, auto)
    next
      case ki: 1 (* k < i *)
      hence id: "(k = i) = False" by auto 
      show ?case unfolding id if_False rowk
        by (intro iarray_cong if_cong refl)
    next
      case 2 (* k = i *)
      show ?case unfolding 2 
        by (intro iarray_cong if_cong refl, subst IArray.of_fun_nth, insert k, auto)
    qed
  qed
qed
        

lemma LLL_swap_add_eq: assumes i: "i \<noteq> 0" "i < m" and fs: "length fs = m" 
  shows "LLL_swap_add p (fs,dmu,di,mods) i = (LLL_swap_row p (LLL_add_row p (fs,dmu,di,mods) i (i - 1)) i)" 
proof -
  define c where "c = round_num_denom (dmu !! i !! (i - 1)) (di !! i)"
  from i have si1: "Suc (i - 1) = i" by auto
  note res1 = LLL_swap_add_def[of p "(fs,dmu,di,mods)" i, unfolded split Let_def c_def[symmetric]]
  show ?thesis
  proof (cases "c = 0")
    case True
    thus ?thesis using i unfolding res1 LLL_add_row_def split id c_def Let_def by auto
  next
    case False
    hence c: "(c = 0) = False" by simp
    have add: "LLL_add_row p (fs, dmu, di, mods) i (i - 1) = 
       perform_add_row p (fs, dmu, di, mods) i (i - 1) c (dmu !! i) (dmu !! i !! (i - 1)) (di !! i)" 
      unfolding LLL_add_row_def Let_def split si1 c_def[symmetric] c by auto 
    show ?thesis unfolding res1 c if_False add 
      by (subst perform_swap_add[OF assms]) simp
  qed
qed
end


context LLL_with_assms
begin

lemma LLL_mod_inv_to_weak: "LLL_invariant_mod fs mfs dmu p first b i \<Longrightarrow> LLL_invariant_mod_weak fs mfs dmu p first b" 
  unfolding LLL_invariant_mod_def LLL_invariant_mod_weak_def by auto

declare IArray.of_fun_def[simp del]

lemma LLL_swap_row: assumes impl: "state_impl_inv p mfs dmu state" 
  and Linv: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and res: "basis_reduction_mod_swap p mfs dmu k = (mfs', dmu')" 
  and res': "LLL_swap_row p state k = state'" 
  and k: "k < m" "k \<noteq> 0" 
shows "state_impl_inv p mfs' dmu' state'" 
proof -
  note inv = LLL_invD_modw[OF Linv]
  obtain fsi dmui di mods where state: "state = (fsi, dmui, di, mods)" by (cases state, auto)
  obtain fsi' dmui' di' mods' where state': "state' = (fsi', dmui', di', mods')" by (cases state', auto)
  from impl[unfolded state, simplified]
  have id: "fsi = mfs" 
    "di = IArray.of_fun (d_of dmu) (Suc m)" 
    "dmui = IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. dmu $$ (i, j)) i) m" 
    "mods = IArray.of_fun (\<lambda>j. p * di !! j * di !! Suc j) (m - 1)"
    by auto
  have kk1: "dmui !! k !! (k - 1) = dmu $$ (k, k - 1)" using k unfolding id 
      IArray.of_fun_nth[OF k(1)]
    by (subst IArray.of_fun_nth, auto)
  have di: "i \<le> m \<Longrightarrow> di !! i = d_of dmu i" for i
    unfolding id by (subst IArray.of_fun_nth, auto)
  have dS1: "di !! Suc k = d_of dmu (Suc k)" using di k by auto
  have d1: "di !! (k - 1) = d_of dmu (k - 1)" using di k by auto
  have dk: "di !! k = d_of dmu k" using di k by auto
  define dk' where "dk' = (d_of dmu (Suc k) * d_of dmu (k - 1) + dmu $$ (k, k - 1) * dmu $$ (k, k - 1)) div d_of dmu k" 
  define mod1 where "mod1 = p * d_of dmu (k - 1) * dk'" 
  define modk where "modk = p * dk' * d_of dmu (Suc k)" 
  define dmu'' where "dmu'' = (mat m m
      (\<lambda>(i, j).
          if j < i
          then if i = k - 1 then dmu $$ (k, j)
               else if i = k \<and> j \<noteq> k - 1 then dmu $$ (k - 1, j)
                    else if k < i \<and> j = k then (d_of dmu (Suc k) * dmu $$ (i, k - 1) - dmu $$ (k, k - 1) * dmu $$ (i, j)) div d_of dmu k
                         else if k < i \<and> j = k - 1 then (dmu $$ (k, k - 1) * dmu $$ (i, j) + dmu $$ (i, k) * d_of dmu (k - 1)) div d_of dmu k else dmu $$ (i, j)
          else if i = j then if i = k - 1 then (d_of dmu (Suc k) * d_of dmu (k - 1) + dmu $$ (k, k - 1) * dmu $$ (k, k - 1)) div d_of dmu k else d_of dmu (Suc i)
               else dmu $$ (i, j)))" 
  have drop: "drop (k - 1) fsi = mfs ! (k - 1) # mfs ! k # drop (Suc k) mfs" unfolding id using \<open>length mfs = m\<close> k
    by (metis Cons_nth_drop_Suc One_nat_def Suc_less_eq Suc_pred less_SucI linorder_neqE_nat not_less0)
  have dk': "dk' = d_of dmu'' k" unfolding dk'_def d_of_def dmu''_def using k by auto
  have mod1: "mod1 = p * d_of dmu'' (k - 1) * d_of dmu'' k" unfolding mod1_def dk' using k
    by (auto simp: dmu''_def d_of_def)
  have modk: "modk = p * d_of dmu'' k * d_of dmu'' (Suc k)" unfolding modk_def dk' using k
    by (auto simp: dmu''_def d_of_def)
  note res = res[unfolded basis_reduction_mod_swap_def, folded dmu''_def, symmetric]
  note res' = res'[unfolded state state' split_at_def drop list.simps split LLL_swap_row_def Let_def kk1 dS1 d1 dk, 
      folded dk'_def mod1_def modk_def, symmetric]
  from res' have fsi': "fsi' = take (k - 1) mfs @ mfs ! k # mfs ! (k - 1) # drop (Suc k) mfs" unfolding id by simp
  from res' have di': "di' = IArray.of_fun (\<lambda>ii. if ii = k then dk' else di !! ii) (Suc m)" by simp
  from res' have dmui': "dmui' = IArray.of_fun
    (\<lambda>i. if i < k - 1 then dmui !! i
         else if k < i then IArray.of_fun
                    (\<lambda>j. if j = k - 1
                         then (dmu $$ (k, k - 1) * dmui !! i !! (k - 1) + dmui !! i !! k * d_of dmu (k - 1)) 
                                 div d_of dmu k symmod mod1
                         else if j = k
                              then (d_of dmu (Suc k) * dmui !! i !! (k - 1) - dmu $$ (k, k - 1) * dmui !! i !! k) 
                                 div d_of dmu k symmod modk                                   
                              else dmui !! i !! j)
                    i
              else if i = k then IArray.of_fun (\<lambda>j. if j = k - 1 then dmu $$ (k, k - 1) symmod mod1 
        else dmui !! (k - 1) !! j) i else IArray.of_fun ((!!) (dmui !! k)) i)
    m" by auto
  from res' have mods': "mods' = IArray.of_fun (\<lambda>jj. if jj = k - 1 then mod1 else if jj = k then modk else mods !! jj) (m - 1)"
    by auto
  from res have dmu': "dmu' = basis_reduction_mod_swap_dmu_mod p dmu'' k" by auto
  show ?thesis unfolding state' state_impl_inv.simps
  proof (intro conjI)
    from res have mfs': "mfs' = mfs[k := mfs ! (k - 1), k - 1 := mfs ! k]" by simp
    show "fsi' = mfs'" unfolding fsi' mfs' using \<open>length mfs = m\<close> k 
    proof (intro nth_equalityI, force, goal_cases)
      case (1 j)
      have choice: "j = k - 1 \<or> j = k \<or> j < k - 1 \<or> j > k" by linarith
      have "min (length mfs) (k - 1) = k - 1" using 1 by auto
      with 1 choice show ?case by (auto simp: nth_append)
    qed
    show "di' = IArray.of_fun (d_of dmu') (Suc m)" unfolding di' 
    proof (intro iarray_cong refl, goal_cases)
      case i: (1 i)
      hence "d_of dmu' i = d_of dmu'' i" unfolding dmu' basis_reduction_mod_swap_dmu_mod_def d_of_def
        by (intro if_cong, auto)
      also have "\<dots> = ((if i = k then dk' else di !! i))" 
      proof (cases "i = k")
        case False
        hence "d_of dmu'' i = d_of dmu i" unfolding dmu''_def d_of_def using i k
          by (intro if_cong refl, auto)
        thus ?thesis using False i k unfolding id by (metis iarray_of_fun_sub)
      next
        case True
        thus ?thesis using dk' by auto
      qed
      finally show ?case by simp
    qed
    have dkS1: "d_of dmu (Suc k) = d_of dmu'' (Suc k)" 
      unfolding dmu''_def d_of_def using k by auto
    have dk1: "d_of dmu (k - 1) = d_of dmu'' (k - 1)" 
      unfolding dmu''_def d_of_def using k by auto
    show "dmui' = IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. dmu' $$ (i, j)) i) m" 
      unfolding dmui'
    proof (intro iarray_cong refl, goal_cases)
      case i: (1 i)
      consider (1) "i < k - 1" | (2) "i = k - 1" | (3) "i = k" | (4) "i > k" by linarith
      thus ?case
      proof (cases)
        case 1
        hence *: "(i < k - 1) = True" by simp
        show ?thesis unfolding * if_True id IArray.of_fun_nth[OF i] using i k 1
          by (intro iarray_cong refl, auto simp: dmu' basis_reduction_mod_swap_dmu_mod_def, auto simp: dmu''_def)
      next
        case 2
        hence *: "(i < k - 1) = False" "(k < i) = False" "(i = k) = False" using k by auto
        show ?thesis unfolding * if_False id using i k 2 unfolding IArray.of_fun_nth[OF k(1)]
          by (intro iarray_cong refl, subst IArray.of_fun_nth, auto simp: dmu' basis_reduction_mod_swap_dmu_mod_def dmu''_def)
      next
        case 3
        hence *: "(i < k - 1) = False" "(k < i) = False" "(i = k) = True" using k by auto
        show ?thesis unfolding * if_False if_True id IArray.of_fun_nth[OF k(1)]
        proof (intro iarray_cong refl, goal_cases)
          case j: (1 j)
          show ?case
          proof (cases "j = k - 1")
            case False
            hence *: "(j = k - 1) = False" by auto
            show ?thesis unfolding * if_False using False j k i 3
              by (subst IArray.of_fun_nth, force, subst IArray.of_fun_nth, force, auto simp: dmu' basis_reduction_mod_swap_dmu_mod_def dmu''_def)
          next
            case True
            hence *: "(j = k - 1) = True" by auto
            show ?thesis unfolding * if_True unfolding True 3 using k
              by (auto simp: basis_reduction_mod_swap_dmu_mod_def dmu' dk' mod1 dmu''_def)
          qed
        qed
      next
        case 4
        hence *: "(i < k - 1) = False" "(k < i) = True" using k by auto
        show ?thesis unfolding * if_False if_True id IArray.of_fun_nth[OF k(1)] IArray.of_fun_nth[OF \<open>i < m\<close>]
        proof (intro iarray_cong refl, goal_cases)
          case j: (1 j)
          from 4 have k1: "k - 1 < i" by auto
          show ?case unfolding IArray.of_fun_nth[OF j] IArray.of_fun_nth[OF 4] IArray.of_fun_nth[OF k1]
            unfolding mod1 modk dmu' basis_reduction_mod_swap_dmu_mod_def using i j 4 k
            by (auto intro!: arg_cong[of _ _ "\<lambda> x. x symmod _"], auto simp: dmu''_def)
        qed
      qed
    qed
    show "mods' = IArray.of_fun (\<lambda>j. p * di' !! j * di' !! Suc j) (m - 1)" 
      unfolding mods' di' dk' mod1 modk
    proof (intro iarray_cong refl, goal_cases)
      case (1 j)
      hence j: "j < Suc m" "Suc j < Suc m" by auto
      show ?case unfolding  
        IArray.of_fun_nth[OF 1]
        IArray.of_fun_nth[OF j(1)]
        IArray.of_fun_nth[OF j(2)] id(4) using k di dk1 dkS1
        by auto
    qed
  qed
qed


lemma LLL_add_row: assumes impl: "state_impl_inv p mfs dmu state" 
  and Linv: "LLL_invariant_mod_weak fs mfs dmu p first b" 
  and res: "basis_reduction_mod_add_row p mfs dmu i j = (mfs', dmu')" 
  and res': "LLL_add_row p state i j = state'" 
  and i: "i < m"
  and j: "j < i"
shows "state_impl_inv p mfs' dmu' state'"
proof - 
  note inv = LLL_invD_modw[OF Linv]
  obtain fsi dmui di mods where state: "state = (fsi, dmui, di, mods)" by (cases state, auto)
  obtain fsi' dmui' di' mods' where state': "state' = (fsi', dmui', di', mods')" by (cases state', auto)
  from impl[unfolded state, simplified]
  have id: "fsi = mfs" 
    "di = IArray.of_fun (d_of dmu) (Suc m)" 
    "dmui = IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. dmu $$ (i, j)) i) m"
    "mods = IArray.of_fun (\<lambda>j. p * di !! j * di !! Suc j) (m - 1)" 
    by auto
  let ?c = "round_num_denom (dmu $$ (i, j)) (d_of dmu (Suc j))" 
  let ?c' = "round_num_denom (dmui !! i !! j) (di !! Suc j)" 
  obtain c where c: "?c = c" by auto
  have c': "?c' = c" unfolding id c[symmetric] using i j
    by (subst (1 2) IArray.of_fun_nth, (force+)[2],
      subst IArray.of_fun_nth, force+)
  have drop: "drop i fsi = mfs ! i # drop (Suc i) mfs" unfolding id using \<open>length mfs = m\<close> i
    by (metis Cons_nth_drop_Suc)
  note res = res[unfolded basis_reduction_mod_add_row_def Let_def c, symmetric]
  note res' = res'[unfolded state state' split LLL_add_row_def Let_def c', symmetric]
  show ?thesis 
  proof (cases "c = 0")
    case True
    from res[unfolded True] res'[unfolded True] show ?thesis unfolding state' using id by auto
  next
    case False
    hence False: "(c = 0) = False" by simp
    note res = res[unfolded Let_def False if_False]
    from res have mfs': "mfs' = mfs[i := map_vec (\<lambda>x. x symmod p) (mfs ! i - c \<cdot>\<^sub>v mfs ! j)]" by auto
    from res have dmu': "dmu' = mat m m (\<lambda>(i', j').
        if i' = i \<and> j' \<le> j
        then if j' = j then dmu $$ (i, j') - c * dmu $$ (j, j')
             else (dmu $$ (i, j') - c * dmu $$ (j, j')) symmod (p * d_of dmu j' * d_of dmu (Suc j'))
        else dmu $$ (i', j'))" by auto
    note res' = res'[unfolded Let_def False if_False perform_add_row_def drop list.simps split_at_def split]
    from res' have fsi': "fsi' = take i fsi @ vec n (\<lambda>k. (mfs ! i $ k - c * mfs ! j $ k) symmod p) # drop (Suc i) mfs" 
      by (auto simp: id)
    from res' have di': "di' = di" and mods': "mods' = mods" by auto
    from res' have dmui': "dmui' = IArray.of_fun (\<lambda>ii. if i = ii
          then IArray.of_fun
                (\<lambda>jj. if jj < j then (dmui !! i !! jj - c * dmui !! j !! jj) symmod (mods !! jj)
                      else if jj = j then dmui !! i !! j - c * di !! (Suc j) else dmui !! i !! jj)
                i
          else dmui !! ii) m" by auto
    show ?thesis unfolding state' state_impl_inv.simps
    proof (intro conjI)
      from inv(11) i j have vec: "mfs ! i \<in> carrier_vec n" "mfs ! j \<in> carrier_vec n" by auto
      hence id': "map_vec (\<lambda>x. x symmod p) (mfs ! i - c \<cdot>\<^sub>v mfs ! j) = vec n (\<lambda>k. (mfs ! i $ k - c * mfs ! j $ k) symmod p)" 
        by (intro eq_vecI, auto)
      show "mods' = IArray.of_fun (\<lambda>j. p * di' !! j * di' !! Suc j) (m - 1)" using id unfolding mods' di' by auto
      show "fsi' = mfs'" unfolding fsi' mfs' id unfolding id' using \<open>length mfs = m\<close> i
        by (simp add: upd_conv_take_nth_drop)
      show "di' = IArray.of_fun (d_of dmu') (Suc m)" 
        unfolding dmu' di' id d_of_def
        by (intro iarray_cong if_cong refl, insert i j, auto)
      show "dmui' = IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. dmu' $$ (i, j)) i) m" 
        unfolding dmui'
      proof (intro iarray_cong refl)
        fix ii
        assume ii: "ii < m" 
        show "(if i = ii
           then IArray.of_fun
                 (\<lambda>jj. if jj < j then (dmui !! i !! jj - c * dmui !! j !! jj) symmod (mods !! jj)
                       else if jj = j then dmui !! i !! j - c * di !! (Suc j) else dmui !! i !! jj)
                 i
           else dmui !! ii) =
          IArray.of_fun (\<lambda>j. dmu' $$ (ii, j)) ii" 
        proof (cases "i = ii")
          case False
          hence *: "(i = ii) = False" by auto
          show ?thesis unfolding * if_False id dmu' using False i j ii
            unfolding IArray.of_fun_nth[OF ii]
            by (intro iarray_cong refl, auto)
        next
          case True
          hence *: "(i = ii) = True" by auto         
          from i j have "j < m" by simp
          show ?thesis unfolding * if_True dmu' id IArray.of_fun_nth[OF i] IArray.of_fun_nth[OF \<open>j < m\<close>]
            unfolding True[symmetric]
          proof (intro iarray_cong refl, goal_cases)
            case jj: (1 jj)
            consider (1) "jj < j" | (2) "jj = j" | (3) "jj > j" by linarith
            thus ?case 
            proof cases
              case 1
              thus ?thesis using jj i j unfolding id(4)
                by (subst (1 2 3 4 5 6) IArray.of_fun_nth, auto)
            next
              case 2
              thus ?thesis using jj i j
                by (subst (5 6) IArray.of_fun_nth, auto simp: d_of_def)
            next
              case 3
              thus ?thesis using jj i j
                by (subst (7) IArray.of_fun_nth, auto simp: d_of_def)
            qed
          qed
        qed
      qed
    qed
  qed
qed


lemma LLL_max_gso_norm_di: assumes di: "di = IArray.of_fun (d_of dmu) (Suc m)"
  and m: "m \<noteq> 0" 
shows "LLL_max_gso_norm_di first di = compute_max_gso_norm first dmu"
proof -
  have di: "j \<le> m \<Longrightarrow> di !! j = d_of dmu j" for j unfolding di
    by (subst IArray.of_fun_nth, auto)
  have id: "(m = 0) = False" using m by auto
  show ?thesis
  proof (cases first)
    case False
    hence id': "first = False" by auto
    show ?thesis unfolding LLL_max_gso_norm_di_def compute_max_gso_norm_def id id' if_False
      by (intro if_cong refl arg_cong[of _ _ "\<lambda> xs. case max_list_rats_with_index xs of (num, denom, i) \<Rightarrow> (rat_of_int num / rat_of_int denom, i)"], 
          unfold map_eq_conv, intro ballI, subst (1 2) di, auto)
  next
    case True
    hence id': "first = True" by auto
    show ?thesis unfolding LLL_max_gso_norm_di_def compute_max_gso_norm_def id id' if_False if_True
      using m di[of 1]
      by (simp add: d_of_def)
  qed
qed

lemma LLL_max_gso_quot: assumes di: "di = IArray.of_fun (d_of dmu) (Suc m)"
  and prods: "state_iso_inv di_prods di" 
shows "LLL_max_gso_quot di_prods = compute_max_gso_quot dmu"
proof -
  have di: "j \<le> m \<Longrightarrow> di !! j = d_of dmu j" for j unfolding di
    by (subst IArray.of_fun_nth, auto)
  show ?thesis unfolding LLL_max_gso_quot_def compute_max_gso_quot_def prods[unfolded state_iso_inv_def]
    by (intro if_cong refl arg_cong[of _ _ max_list_rats_with_index], unfold map_eq_conv Let_def, intro ballI,
     subst IArray.of_fun_nth, force, unfold split,
     subst (1 2 3 4) di, auto)
qed

lemma LLL_max_gso_norm: assumes impl: "state_impl_inv p mfs dmu state" 
  and m: "m \<noteq> 0" 
shows "LLL_max_gso_norm first state = compute_max_gso_norm first dmu"
proof -
  obtain mfsi dmui di mods where state: "state = (mfsi, dmui, di,mods)" 
    by (metis prod_cases3)
  from impl[unfolded state state_impl_inv.simps]
  have di: "di = IArray.of_fun (d_of dmu) (Suc m)" by auto
  show ?thesis using LLL_max_gso_norm_di[OF di m] unfolding LLL_max_gso_norm_def state split .
qed

lemma mod_of_gso_norm: "m \<noteq> 0 \<Longrightarrow> mod_of_gso_norm first mn =
  compute_mod_of_max_gso_norm first mn" 
  unfolding mod_of_gso_norm_def compute_mod_of_max_gso_norm_def bound_number_def
  by auto

lemma LLL_adjust_mod: assumes impl: "state_impl_inv p mfs dmu state" 
  and res: "basis_reduction_adjust_mod p first mfs dmu = (p', mfs', dmu', g_idx)" 
  and res': "LLL_adjust_mod p first state = (p'', state', g_idx')" 
  and m: "m \<noteq> 0" 
shows "state_impl_inv p' mfs' dmu' state' \<and> p'' = p' \<and> g_idx' = g_idx"
proof -
  from LLL_max_gso_norm[OF impl m] 
  have id: "LLL_max_gso_norm first state = compute_max_gso_norm first dmu" by auto
  obtain b gi where norm: "compute_max_gso_norm first dmu = (b, gi)" by force
  obtain P where P: "compute_mod_of_max_gso_norm first b = P" by auto
  note res = res[unfolded basis_reduction_adjust_mod.simps Let_def P norm split]
  note res' = res'[unfolded LLL_adjust_mod_def id Let_def P norm split mod_of_gso_norm[OF m]]
  show ?thesis
  proof (cases "P < p")
    case False
    thus ?thesis using res res' impl by (auto split: if_splits)
  next
    case True
    hence id: "(P < p) = True" by auto
    obtain fsi dmui di mods where state: "state = (fsi, dmui, di, mods)" by (metis prod_cases3)
    from impl[unfolded state state_impl_inv.simps]
    have impl: "fsi = mfs" "di = IArray.of_fun (d_of dmu) (Suc m)" "dmui = IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. dmu $$ (i, j)) i) m" by auto
    note res = res[unfolded id if_True]
    from res have mfs': "mfs' = map (map_vec (\<lambda>x. x symmod P)) mfs" 
       and p': "p' = P" 
       and dmu': "dmu' = mat m m (\<lambda>(i, j). if j < i then dmu $$ (i, j) symmod (P * vec (Suc m) (d_of dmu) $ j * vec (Suc m) (d_of dmu) $ Suc j) else dmu $$ (i, j))" 
       and gidx: "g_idx = gi" 
      by auto
    let ?mods = "IArray.of_fun (\<lambda>j. P * di !! j * di !! Suc j) (m - 1)" 
    let ?dmu = "IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. dmui !! i !! j symmod ?mods !! j) i) m" 
    note res' = res'[unfolded id if_True state split impl(1) perform_adjust_mod_def Let_def]
    from res' have p'': "p'' = P" and state': "state' = (map (map_vec (\<lambda>x. x symmod P)) mfs, ?dmu, di, ?mods)" 
       and gidx': "g_idx' = gi" by auto
    show ?thesis unfolding state' state_impl_inv.simps mfs' p'' p' gidx gidx'
    proof (intro conjI refl)
      show "di = IArray.of_fun (d_of dmu') (Suc m)" unfolding impl
        by (intro iarray_cong refl, auto simp: dmu' d_of_def)
      show "?dmu = IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. dmu' $$ (i, j)) i) m" 
      proof (intro iarray_cong refl, goal_cases)
        case (1 i j)
        hence "j < m" "Suc j < Suc m" "j < Suc m" "j < m - 1" by auto
        show ?case unfolding dmu' impl IArray.of_fun_nth[OF \<open>i < m\<close>] IArray.of_fun_nth[OF \<open>j < i\<close>]
            IArray.of_fun_nth[OF \<open>j < m\<close>] IArray.of_fun_nth[OF \<open>Suc j < Suc m\<close>]
            IArray.of_fun_nth[OF \<open>j < Suc m\<close>] IArray.of_fun_nth[OF \<open>j < m - 1\<close>] using 1 by auto
      qed
    qed
  qed
qed

lemma LLL_adjust_swap_add: assumes impl: "state_impl_inv p mfs dmu state" 
  and Linv: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and res: "basis_reduction_adjust_swap_add_step p first mfs dmu g_idx k = (p', mfs', dmu', g_idx')" 
  and res': "LLL_adjust_swap_add p first state g_idx k = (p'',state', G_idx')" 
  and k: "k < m" and k0: "k \<noteq> 0" 
shows "state_impl_inv p' mfs' dmu' state'" "p'' = p'" "G_idx' = g_idx'" 
  "i \<le> m \<Longrightarrow> i \<noteq> k \<Longrightarrow> di_of state' !! i = di_of state !! i" 
proof (atomize(full), goal_cases)
  case 1
  from k have m: "m \<noteq> 0" by auto
  obtain mfsi dmui di mods where state: "state = (mfsi, dmui, di, mods)" 
    by (metis prod_cases3)
  obtain state'' where add': "LLL_add_row p state k (k - 1) = state''" by blast
  obtain mfs'' dmu'' where add: "basis_reduction_mod_add_row p mfs dmu k (k - 1) = (mfs'', dmu'')" by force
  obtain mfs3 dmu3 where swap: "basis_reduction_mod_swap p mfs'' dmu'' k = (mfs3, dmu3)" by force
  obtain state3 where swap': "LLL_swap_row p state'' k = state3" by blast
  obtain mfsi2 dmui2 di2 mods2 where state2: "state'' = (mfsi2, dmui2, di2, mods2)" by (cases state'', auto)
  obtain mfsi3 dmui3 di3 mods3 where state3: "state3 = (mfsi3, dmui3, di3, mods3)" by (cases state3, auto)
  have "length mfsi = m" using impl[unfolded state state_impl_inv.simps] LLL_invD_modw[OF Linv] by auto
  note res' = res'[unfolded state LLL_adjust_swap_add_def LLL_swap_add_eq[OF k0 k this], folded state, unfolded add' swap' Let_def]
  note res = res[unfolded basis_reduction_adjust_swap_add_step_def Let_def add split swap]
  from LLL_add_row[OF impl Linv add add' k] k0
  have impl': "state_impl_inv p mfs'' dmu'' state''" by auto
  from basis_reduction_mod_add_row[OF Linv add k _ k0] k0
  obtain fs'' where Linv': "LLL_invariant_mod_weak fs'' mfs'' dmu'' p first b" by auto
  from LLL_swap_row[OF impl' Linv' swap swap' k k0] 
  have impl3: "state_impl_inv p mfs3 dmu3 state3" .
  have di2: "di2 = di" using add'[unfolded state LLL_add_row_def Let_def split perform_add_row_def state2]
    by (auto split: if_splits)
  have di3: "di3 = IArray.of_fun (\<lambda>i. if i = k then (di2 !! Suc k * di2 !! (k - 1) + dmui2 !! k !! (k - 1) * dmui2 !! k !! (k - 1)) div di2 !! k else di2 !! i) (Suc m)" 
    using swap'[unfolded state2 state3] 
    unfolding LLL_swap_row_def Let_def by simp 
  have di3: "i \<le> m \<Longrightarrow> i \<noteq> k \<Longrightarrow> di3 !! i = di !! i"
    unfolding di2[symmetric] di3 
    by (subst IArray.of_fun_nth, auto)
  show ?case
  proof (cases "k - 1 = g_idx")
    case True
    hence id: "(k - 1 = g_idx) = True" by simp
    note res = res[unfolded id if_True]
    note res' = res'[unfolded id if_True]
    obtain mfsi4 dmui4 di4 mods4 where state': "state' = (mfsi4, dmui4, di4, mods4)" by (cases state', auto)
    from res'[unfolded state3 state' LLL_adjust_mod_def Let_def perform_adjust_mod_def] have di4: "di4 = di3" 
      by (auto split: if_splits prod.splits)
    from LLL_adjust_mod[OF impl3 res res' m] di3 state state' di4 res'
    show ?thesis by auto
  next
    case False
    hence id: "(k - 1 = g_idx) = False" by simp
    note res = res[unfolded id if_False]
    note res' = res'[unfolded id if_False]
    from impl3 res res' di3 state state3 show ?thesis by auto
  qed
qed
  


lemma LLL_step: assumes impl: "state_impl_inv p mfs dmu state" 
  and Linv: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and res: "basis_reduction_mod_step p first mfs dmu g_idx k j = (p', mfs', dmu', g_idx', k', j')" 
  and res': "LLL_step p first state g_idx k j = ((p'',state', g_idx''), k'', j'')" 
  and k: "k < m" 
shows "state_impl_inv p' mfs' dmu' state' \<and> k'' = k' \<and> p'' = p' \<and> j'' = j' \<and> g_idx'' = g_idx'"
proof (cases "k = 0")
  case True
  thus ?thesis using res res' impl unfolding LLL_step_def basis_reduction_mod_step_def by auto
next
  case k0: False
  hence id: "(k = 0) = False" by simp
  note res = res[unfolded basis_reduction_mod_step_def id if_False]
  obtain num denom where alph: "quotient_of \<alpha> = (num,denom)" by force
  obtain mfsi dmui di mods where state: "state = (mfsi, dmui, di, mods)" 
    by (metis prod_cases3)
  note res' = res'[unfolded LLL_step_def id if_False Let_def state split alph, folded state]
  from k0 have kk1: "k - 1 < k" by auto
  note res = res[unfolded Let_def alph split]
  obtain state'' where addi: "LLL_swap_add p state k = state''" by auto
  from impl[unfolded state state_impl_inv.simps] 
  have di: "di = IArray.of_fun (d_of dmu) (Suc m)" by auto
  have id: "di !! k = d_of dmu k" 
    "di !! (Suc k) = d_of dmu (Suc k)" 
    "di !! (k - 1) = d_of dmu (k - 1)" 
    unfolding di using k
    by (subst IArray.of_fun_nth, force, force)+
  have "length mfsi = m" using impl[unfolded state state_impl_inv.simps] LLL_invD_modw[OF Linv] by auto
  note res' = res'[unfolded id]
  let ?cond = "d_of dmu k * d_of dmu k * denom \<le> num * d_of dmu (k - 1) * d_of dmu (Suc k)" 
  show ?thesis
  proof (cases ?cond)
    case True
    from True res res' state show ?thesis using impl by auto
  next
    case False
    hence cond: "?cond = False" by simp
    note res = res[unfolded cond if_False]
    note res' = res'[unfolded cond if_False]
    let ?step = "basis_reduction_adjust_swap_add_step p first mfs dmu g_idx k" 
    let ?step' = "LLL_adjust_swap_add p first state g_idx k" 
    from res have step: "?step = (p', mfs', dmu', g_idx')" by (cases ?step, auto)
    note res = res[unfolded step split]
    from res' have step': "?step' = (p'',state', g_idx'')" by auto
    note res' = res'[unfolded step']
    from LLL_adjust_swap_add[OF impl Linv step step' k k0] 
    show ?thesis using res res' by auto
  qed
qed


lemma LLL_main: assumes impl: "state_impl_inv p mfs dmu state" 
  and Linv: "LLL_invariant_mod fs mfs dmu p first b i"
  and res: "basis_reduction_mod_main p first mfs dmu g_idx i k = (p', mfs', dmu')" 
  and res': "LLL_main p first state g_idx i k = (pi', state')" 
shows "state_impl_inv p' mfs' dmu' state' \<and> pi' = p'"
  using assms
proof (induct "LLL_measure i fs" arbitrary: mfs dmu state fs p b k i g_idx rule: less_induct)
  case (less fs i mfs dmu state p b k g_idx)
  note impl = less(2)
  note Linv = less(3)
  note res = less(4)
  note res' = less(5)
  note IH = less(1)
  note res = res[unfolded basis_reduction_mod_main.simps[of _ _ _ _ _ _ k]]
  note res' = res'[unfolded LLL_main.simps[of _ _ _ _ _ k]]
  note Linvw = LLL_mod_inv_to_weak[OF Linv]
  show ?case
  proof (cases "i < m")
    case False
    thus ?thesis using res res' impl by auto
  next 
    case i: True
    hence id: "(i < m) = True" by simp
    obtain P'' state'' I'' K'' G_idx'' where step': "LLL_step p first state g_idx i k = ((P'', state'', G_idx''), I'', K'')" 
      by (metis prod_cases3)
    obtain p'' mfs'' dmu'' i'' k'' g_idx'' where step: "basis_reduction_mod_step p first mfs dmu g_idx i k = (p'', mfs'', dmu'', g_idx'', i'', k'')" 
      by (metis prod_cases3)
    from LLL_step[OF impl Linvw step step' i]
    have impl'': "state_impl_inv p'' mfs'' dmu'' state''" and ID: "I'' = i''" "K'' = k''" "P'' = p''" "G_idx'' = g_idx''" by auto
    from basis_reduction_mod_step[OF Linv step i] obtain
       fs'' b'' where 
       Linv'': "LLL_invariant_mod fs'' mfs'' dmu'' p'' first b'' i''" and 
       decr: "LLL_measure i'' fs'' < LLL_measure i fs" by auto
    note res = res[unfolded id if_True step split]
    note res' = res'[unfolded id if_True step' split ID]
    show ?thesis
      by (rule IH[OF decr impl'' Linv'' res res'])
  qed
qed

lemma LLL_iso_main_inner: assumes impl: "state_impl_inv p mfs dmu state" 
  and di_prods: "state_iso_inv di_prods (di_of state)" 
  and Linv: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and res: "basis_reduction_iso_main p first mfs dmu g_idx k = (p', mfs', dmu')" 
  and res': "LLL_iso_main_inner p first state di_prods g_idx k = (pi', state')" 
  and m: "m > 1" 
shows "state_impl_inv p' mfs' dmu' state' \<and> pi' = p'"
  using assms(1-5)
proof (induct "LLL_measure (m - 1) fs" arbitrary: mfs dmu state fs p b k di_prods g_idx rule: less_induct)
  case (less fs mfs dmu state p b k di_prods g_idx)
  note impl = less(2)
  note di_prods  = less(3)
  note Linv = less(4)
  note res = less(5)
  note res' = less(6)
  note IH = less(1)
  obtain mfsi dmui di mods where state: "state = (mfsi, dmui, di, mods)" 
    by (metis prod_cases4)
  from di_prods state have di_prods: "state_iso_inv di_prods di" by auto
  obtain num denom idx where quot': "LLL_max_gso_quot di_prods = (num, denom, idx)" 
    by (metis prod_cases3)
  note inv = LLL_invD_modw[OF Linv]
  obtain na da where alph: "quotient_of \<alpha> = (na,da)" by force
  from impl[unfolded state] have di: "di = IArray.of_fun (d_of dmu) (Suc m)" by auto
  from LLL_max_gso_quot[OF di di_prods] have quot: "compute_max_gso_quot dmu = LLL_max_gso_quot di_prods" ..
  obtain cmp where cmp: "(na * denom < num * da) = cmp" by force
  have "(m > 1) = True" using m by auto
  note res = res[unfolded basis_reduction_iso_main.simps[of _ _ _ _ _ k] this if_True Let_def quot quot' split alph cmp]
  note res' = res'[unfolded LLL_iso_main_inner.simps[of _ _ _ _ _ k] state split Let_def quot' alph cmp, folded state]
  note cmp = compute_max_gso_quot_alpha[OF Linv quot[unfolded quot'] alph cmp m]
  show ?case
  proof (cases cmp)
    case False
    thus ?thesis using res res' impl by auto
  next 
    case True
    hence id: "cmp = True" by simp 
    note cmp = cmp(1)[OF True]
    obtain state'' P'' G_idx'' where step': "LLL_adjust_swap_add p first state g_idx idx = (P'',state'', G_idx'')" 
      by (metis prod.exhaust)
    obtain mfs'' dmu'' p'' g_idx'' where step: "basis_reduction_adjust_swap_add_step p first mfs dmu g_idx idx = (p'', mfs'', dmu'', g_idx'')" 
      by (metis prod_cases3)
    obtain mfsi2 dmui2 di2 mods2 where state2: "state'' = (mfsi2, dmui2, di2, mods2)" by (cases state'', auto)
    note res = res[unfolded id if_True step split]
    note res' = res'[unfolded id if_True step' state2 split, folded state2]
    from cmp have idx0: "idx \<noteq> 0" and idx: "idx < m" and ineq: "\<not> d_of dmu idx * d_of dmu idx * da \<le> na * d_of dmu (idx - 1) * d_of dmu (Suc idx)" 
      by auto
    from basis_reduction_adjust_swap_add_step[OF Linv step alph ineq idx idx0]
    obtain fs'' b'' where Linv'': "LLL_invariant_mod_weak fs'' mfs'' dmu'' p'' first b''" and
       meas: "LLL_measure (m - 1) fs'' < LLL_measure (m - 1) fs" by auto
    from LLL_adjust_swap_add[OF impl Linv step step' idx idx0]
    have impl'': "state_impl_inv p'' mfs'' dmu'' state''" and P'': "P'' = p''" "G_idx'' = g_idx''" 
      and di_prod_upd: "\<And> i. i \<le> m \<Longrightarrow> i \<noteq> idx \<Longrightarrow> di2 !! i = di !! i" 
      using state state2 by auto
    have di_prods: "state_iso_inv (IArray.of_fun
       (\<lambda>i. if idx < i \<or> i + 2 < idx then di_prods !! i
            else case di_prods !! i of (l, r) \<Rightarrow> if i + 1 = idx then (di2 !! idx * di2 !! idx, r) else (l, di2 !! (i + 2) * di2 !! i))
       (m - 1)) di2" unfolding state_iso_inv_def
      by (intro iarray_cong', insert di_prod_upd, unfold di_prods[unfolded state_iso_inv_def],
        subst (1 2) IArray.of_fun_nth, auto)
    show ?thesis 
      by (rule IH[OF meas impl'' _ Linv'' res res'[unfolded step' P'']], insert di_prods state2, auto)
  qed
qed

lemma LLL_iso_main: assumes impl: "state_impl_inv p mfs dmu state" 
  and Linv: "LLL_invariant_mod_weak fs mfs dmu p first b"
  and res: "basis_reduction_iso_main p first mfs dmu g_idx k = (p', mfs', dmu')" 
  and res': "LLL_iso_main p first state g_idx k = (pi', state')" 
shows "state_impl_inv p' mfs' dmu' state' \<and> pi' = p'"
proof (cases "m > 1")
  case True
  from LLL_iso_main_inner[OF impl _ Linv res _ True, unfolded state_iso_inv_def, OF refl, of pi' state'] res' True
  show ?thesis unfolding LLL_iso_main_def by (cases state, auto)
next
  case False
  thus ?thesis using res res' impl unfolding LLL_iso_main_def
    basis_reduction_iso_main.simps[of _ _ _ _ _ k] by auto
qed

lemma LLL_initial: assumes res: "compute_initial_state first = (p, mfs, dmu, g_idx)" 
  and res': "LLL_initial first = (p', state, g_idx')" 
  and m: "m \<noteq> 0" 
shows "state_impl_inv p mfs dmu state \<and> p' = p \<and> g_idx' = g_idx"
proof -
  obtain b gi where norm: "compute_max_gso_norm first dmu_initial = (b,gi)" by force
  obtain P where P: "compute_mod_of_max_gso_norm first b = P" by auto
  define di where "di = IArray.of_fun (\<lambda>i. if i = 0 then 1 else d\<mu>_impl fs_init !! (i - 1) !! (i - 1)) (Suc m)" 
  note res = res[unfolded compute_initial_state_def Let_def P norm split]
  have di: "di = IArray.of_fun (d_of dmu_initial) (Suc m)" 
    unfolding di_def dmu_initial_def Let_def d_of_def
    by (intro iarray_cong refl if_cong, auto)  
  note norm' = LLL_max_gso_norm_di[OF di m, of first, unfolded norm]
  note res' = res'[unfolded LLL_initial_def Let_def, folded di_def, unfolded norm' P split mod_of_gso_norm[OF m]]
  from res have p: "p = P" and mfs: "mfs = compute_initial_mfs p" and dmu: "dmu = compute_initial_dmu P dmu_initial" 
    and g_idx: "g_idx = gi" 
     by auto
  let ?mods = "IArray.of_fun (\<lambda>j. P * di !! j * di !! Suc j) (m - 1)" 
  have di': "di = IArray.of_fun (d_of (compute_initial_dmu P dmu_initial)) (Suc m)" 
    unfolding di
    by (intro iarray_cong refl, auto simp: compute_initial_dmu_def d_of_def)
  from res' have p': "p' = P" and g_idx': "g_idx' = gi" and state: 
    "state = (compute_initial_mfs P, IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. d\<mu>_impl fs_init !! i !! j symmod ?mods !! j) i) m, di, ?mods)" 
    by auto
  show ?thesis unfolding mfs p state p' dmu state_impl_inv.simps g_idx' g_idx
  proof (intro conjI refl di' iarray_cong, goal_cases)
    case (1 i j)
    hence "j < m" "Suc j < Suc m" "j < Suc m" "j < m - 1" by auto
    thus ?case unfolding compute_initial_dmu_def di 
        IArray.of_fun_nth[OF \<open>j < m\<close>]
        IArray.of_fun_nth[OF \<open>Suc j < Suc m\<close>]
        IArray.of_fun_nth[OF \<open>j < Suc m\<close>]
        IArray.of_fun_nth[OF \<open>j < m - 1\<close>]
      unfolding dmu_initial_def Let_def using 1 by auto
  qed
qed 

lemma LLL_add_rows_loop: assumes impl: "state_impl_inv p mfs dmu state" 
  and Linv: "LLL_invariant_mod fs mfs dmu p b first i"
  and res: "basis_reduction_mod_add_rows_loop p mfs dmu i j = (mfs', dmu')" 
  and res': "LLL_add_rows_loop p state i j = state'" 
  and j: "j \<le> i" 
  and i: "i < m" 
shows "state_impl_inv p mfs' dmu' state'"
  using assms(1-5)
proof (induct j arbitrary: fs mfs dmu state)
  case (Suc j)
  note impl = Suc(2)
  note Linv = Suc(3)
  note res = Suc(4)
  note res' = Suc(5)
  note IH = Suc(1)
  from Suc have j: "j < i" and ji: "j \<le> i" by auto
  obtain mfs1 dmu1 where add: "basis_reduction_mod_add_row p mfs dmu i j = (mfs1, dmu1)" by force
  note res = res[unfolded basis_reduction_mod_add_rows_loop.simps Let_def add split]
  obtain state1 where add': "LLL_add_row p state i j = state1" by auto
  note res' = res'[unfolded LLL_add_rows_loop.simps Let_def add']
  note Linvw = LLL_mod_inv_to_weak[OF Linv]
  from LLL_add_row[OF impl Linvw add add' i j]
  have impl1: "state_impl_inv p mfs1 dmu1 state1" .
  from basis_reduction_mod_add_row[OF Linvw add i j] Linv j 
  obtain fs1 where Linv1: "LLL_invariant_mod fs1 mfs1 dmu1 p b first i" by auto
  show ?case using IH[OF impl1 Linv1 res res' ji] .
qed auto

lemma LLL_add_rows_outer_loop: assumes impl: "state_impl_inv p mfs dmu state" 
  and Linv: "LLL_invariant_mod fs mfs dmu p first b m"
  and res: "basis_reduction_mod_add_rows_outer_loop p mfs dmu i = (mfs', dmu')" 
  and res': "LLL_add_rows_outer_loop p state i = state'" 
  and i: "i \<le> m - 1" 
shows "state_impl_inv p mfs' dmu' state'"
  using assms
proof (induct i arbitrary: fs mfs dmu state mfs' dmu' state')
  case (Suc i)
  note impl = Suc(2)
  note Linv = Suc(3)
  note res = Suc(4)
  note res' = Suc(5)
  note i = Suc(6)
  note IH = Suc(1)
  from i have im: "i < m" "i \<le> m - 1" "Suc i < m" by auto
  obtain mfs1 dmu1 where add: "basis_reduction_mod_add_rows_outer_loop p mfs dmu i = (mfs1, dmu1)" by force
  note res = res[unfolded basis_reduction_mod_add_rows_outer_loop.simps Let_def add split]
  obtain state1 where add': "LLL_add_rows_outer_loop p state i = state1" by auto
  note res' = res'[unfolded LLL_add_rows_outer_loop.simps Let_def add']
  from IH[OF impl Linv add add' im(2)] 
  have impl1: "state_impl_inv p mfs1 dmu1 state1" .
  from basis_reduction_mod_add_rows_outer_loop_inv[OF Linv add[symmetric] im(1)]
  obtain fs1 where Linv1: "LLL_invariant_mod fs1 mfs1 dmu1 p first b m" by auto
  from basis_reduction_mod_add_rows_loop_inv'[OF Linv1 res im(3)] obtain fs' where 
    Linv': "LLL_invariant_mod fs' mfs' dmu' p first b m" by auto
  from LLL_add_rows_loop[OF impl1 LLL_invariant_mod_to_weak_m_to_i(1)[OF Linv1] res res' le_refl im(3)] i
  show ?case by auto
qed auto

subsection \<open>Soundness of implementation\<close>

text \<open>We just prove that the concrete implementations have the same input-output-behaviour as
  the abstract versions of Storjohann's algorithms.\<close>

lemma LLL_reduce_basis: "LLL_reduce_basis = reduce_basis_mod" 
proof (cases "m = 0")
  case True
  from LLL_invD[OF reduce_basis_mod_inv[OF refl]] True 
  have "reduce_basis_mod = []" by auto
  thus ?thesis using True unfolding LLL_reduce_basis_def by auto
next
  case False
  hence idm: "(m = 0) = False" by auto
  let ?first = False
  obtain p1 mfs1 dmu1 g_idx1 where init: "compute_initial_state ?first = (p1, mfs1, dmu1,g_idx1)" 
    by (metis prod_cases3)
  obtain p1' state1 g_idx1' where init': "LLL_initial ?first = (p1', state1, g_idx1')" 
    by (metis prod.exhaust)
  from LLL_initial[OF init init' False]
  have impl1: "state_impl_inv p1 mfs1 dmu1 state1" and id: "p1' = p1" "g_idx1' = g_idx1" by auto
  from LLL_initial_invariant_mod[OF init] obtain fs1 b1 where 
    inv1: "LLL_invariant_mod fs1 mfs1 dmu1 p1 ?first b1 0" by auto
  obtain p2 mfs2 dmu2 where main: "basis_reduction_mod_main p1 ?first mfs1 dmu1 g_idx1 0 0 = (p2, mfs2, dmu2)" 
    by (metis prod_cases3)
  from basis_reduction_mod_main[OF inv1 main] obtain fs2 b2 where 
    inv2: " LLL_invariant_mod fs2 mfs2 dmu2 p2 ?first b2 m" by auto  
  obtain p2' state2 where main': "LLL_main p1 ?first state1 g_idx1 0 0 = (p2', state2)" 
    by (metis prod.exhaust)
  from LLL_main[OF impl1 inv1 main, unfolded id, OF main']
  have impl2: "state_impl_inv p2 mfs2 dmu2 state2" and p2: "p2' = p2" by auto
  obtain mfs3 dmu3 where outer: "basis_reduction_mod_add_rows_outer_loop p2 mfs2 dmu2 (m - 1) = (mfs3, dmu3)" by force
  obtain mfsi3 dmui3 di3 mods3 where outer': "LLL_add_rows_outer_loop p2 state2 (m - 1) = (mfsi3, dmui3, di3, mods3)" 
    by (metis prod_cases4)
  from LLL_add_rows_outer_loop[OF impl2 inv2 outer outer' le_refl] 
  have "state_impl_inv p2 mfs3 dmu3 (mfsi3, dmui3, di3, mods3)" .
  hence identity: "mfs3 = mfsi3" unfolding state_impl_inv.simps by auto
  note res = reduce_basis_mod_def[unfolded init main split Let_def outer]
  note res' = LLL_reduce_basis_def[unfolded init' Let_def main' id split p2 outer' idm if_False]
  show ?thesis unfolding res res' identity ..
qed

lemma LLL_reduce_basis_iso: "LLL_reduce_basis_iso = reduce_basis_iso" 
proof (cases "m = 0")
  case True
  from LLL_invD[OF reduce_basis_iso_inv[OF refl]] True 
  have "reduce_basis_iso = []" by auto
  thus ?thesis using True unfolding LLL_reduce_basis_iso_def by auto
next
  case False
  hence idm: "(m = 0) = False" by auto
  let ?first = False
  obtain p1 mfs1 dmu1 g_idx1 where init: "compute_initial_state ?first = (p1, mfs1, dmu1, g_idx1)" 
    by (metis prod_cases3)
  obtain p1' state1 g_idx1' where init': "LLL_initial ?first = (p1', state1, g_idx1')" 
    by (metis prod.exhaust)
  from LLL_initial[OF init init' False]
  have impl1: "state_impl_inv p1 mfs1 dmu1 state1" and id: "p1' = p1" "g_idx1' = g_idx1" by auto
  from LLL_initial_invariant_mod[OF init] obtain fs1 b1 where 
    inv1: "LLL_invariant_mod_weak fs1 mfs1 dmu1 p1 ?first b1" 
    by (auto simp: LLL_invariant_mod_weak_def LLL_invariant_mod_def)
  obtain p2 mfs2 dmu2 where main: "basis_reduction_iso_main p1 ?first mfs1 dmu1 g_idx1 0 = (p2, mfs2, dmu2)" 
    by (metis prod_cases3)
  from basis_reduction_iso_main[OF inv1 main] obtain fs2 b2 where 
    inv2: " LLL_invariant_mod fs2 mfs2 dmu2 p2 ?first b2 m" by auto  
  obtain p2' state2 where main': "LLL_iso_main p1 ?first state1 g_idx1 0 = (p2', state2)" 
    by (metis prod.exhaust)
  from LLL_iso_main[OF impl1 inv1 main, unfolded id, OF main']
  have impl2: "state_impl_inv p2 mfs2 dmu2 state2" and p2: "p2' = p2" by auto
  obtain mfs3 dmu3 where outer: "basis_reduction_mod_add_rows_outer_loop p2 mfs2 dmu2 (m - 1) = (mfs3, dmu3)" by force
  obtain mfsi3 dmui3 di3 mods3 where outer': "LLL_add_rows_outer_loop p2 state2 (m - 1) = (mfsi3, dmui3, di3, mods3)" 
    by (metis prod_cases4)
  from LLL_add_rows_outer_loop[OF impl2 inv2 outer outer' le_refl] 
  have "state_impl_inv p2 mfs3 dmu3 (mfsi3, dmui3, di3, mods3)" .
  hence identity: "mfs3 = mfsi3" unfolding state_impl_inv.simps by auto
  note res = reduce_basis_iso_def[unfolded init main split Let_def outer]
  note res' = LLL_reduce_basis_iso_def[unfolded init' Let_def main' id split p2 outer' idm if_False]
  show ?thesis unfolding res res' identity ..
qed

lemma LLL_short_vector: assumes m: "m \<noteq> 0" 
  shows "LLL_short_vector = short_vector_mod" 
proof -
  let ?first = True
  obtain p1 mfs1 dmu1 g_idx1 where init: "compute_initial_state ?first = (p1, mfs1, dmu1,g_idx1)" 
    by (metis prod_cases3)
  obtain p1' state1 g_idx1' where init': "LLL_initial ?first = (p1', state1, g_idx1')" 
    by (metis prod.exhaust)
  from LLL_initial[OF init init' m]
  have impl1: "state_impl_inv p1 mfs1 dmu1 state1" and id: "p1' = p1" "g_idx1' = g_idx1" by auto
  from LLL_initial_invariant_mod[OF init] obtain fs1 b1 where 
    inv1: "LLL_invariant_mod fs1 mfs1 dmu1 p1 ?first b1 0" by auto
  obtain p2 mfs2 dmu2 where main: "basis_reduction_mod_main p1 ?first mfs1 dmu1 g_idx1 0 0 = (p2, mfs2, dmu2)" 
    by (metis prod_cases3)
  from basis_reduction_mod_main[OF inv1 main] obtain fs2 b2 where 
    inv2: " LLL_invariant_mod fs2 mfs2 dmu2 p2 ?first b2 m" by auto  
  obtain p2' mfsi2 dmui2 di2 mods2 where main': "LLL_main p1 ?first state1 g_idx1 0 0 = (p2', (mfsi2, dmui2, di2, mods2))" 
    by (metis prod.exhaust)
  from LLL_main[OF impl1 inv1 main, unfolded id, OF main']
  have impl2: "state_impl_inv p2 mfs2 dmu2 (mfsi2, dmui2, di2, mods2)" and p2: "p2' = p2" by auto
  hence identity: "mfs2 = mfsi2" unfolding state_impl_inv.simps by auto
  note res = short_vector_mod_def[unfolded init main split Let_def]
  note res' = LLL_short_vector_def[unfolded init' Let_def main' id split p2]
  show ?thesis unfolding res res' identity ..
qed

lemma LLL_short_vector_iso: assumes m: "m \<noteq> 0" 
  shows "LLL_short_vector_iso = short_vector_iso" 
proof -
  let ?first = True
  obtain p1 mfs1 dmu1 g_idx1 where init: "compute_initial_state ?first = (p1, mfs1, dmu1,g_idx1)" 
    by (metis prod_cases3)
  obtain p1' state1 g_idx1' where init': "LLL_initial ?first = (p1', state1, g_idx1')" 
    by (metis prod.exhaust)
  from LLL_initial[OF init init' m]
  have impl1: "state_impl_inv p1 mfs1 dmu1 state1" and id: "p1' = p1" "g_idx1' = g_idx1" by auto
  from LLL_initial_invariant_mod[OF init] obtain fs1 b1 where 
    inv1: "LLL_invariant_mod_weak fs1 mfs1 dmu1 p1 ?first b1" 
    by (auto simp: LLL_invariant_mod_weak_def LLL_invariant_mod_def)
  obtain p2 mfs2 dmu2 where main: "basis_reduction_iso_main p1 ?first mfs1 dmu1 g_idx1 0 = (p2, mfs2, dmu2)" 
    by (metis prod_cases3)
  from basis_reduction_iso_main[OF inv1 main] obtain fs2 b2 where 
    inv2: " LLL_invariant_mod fs2 mfs2 dmu2 p2 ?first b2 m" by auto  
  obtain p2' mfsi2 dmui2 di2 mods2 where main': "LLL_iso_main p1 ?first state1 g_idx1 0 = (p2', (mfsi2, dmui2, di2, mods2))" 
    by (metis prod.exhaust)
  from LLL_iso_main[OF impl1 inv1 main, unfolded id, OF main']
  have impl2: "state_impl_inv p2 mfs2 dmu2 (mfsi2, dmui2, di2, mods2)" and p2: "p2' = p2" by auto
  hence identity: "mfs2 = mfsi2" unfolding state_impl_inv.simps by auto
  note res = short_vector_iso_def[unfolded init main split Let_def]
  note res' = LLL_short_vector_iso_def[unfolded init' Let_def main' id split p2]
  show ?thesis unfolding res res' identity ..
qed

end

end