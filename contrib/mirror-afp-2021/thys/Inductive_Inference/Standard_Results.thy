theory Standard_Results
  imports Universal
begin

section \<open>Kleene normal form and the number of $\mu$-operations\<close>

text \<open>Kleene's original normal form theorem~\cite{Kleene43} states that
every partial recursive $f$ can be expressed as $f(x) = u(\mu y[t(i, x, y) =
0]$ for some $i$, where $u$ and $t$ are specially crafted primitive recursive
functions tied to Kleene's definition of partial recursive functions.
Rogers~\cite[p.~29f.]{Rogers87} relaxes the theorem by allowing $u$ and $t$
to be any primitive recursive functions of arity one and three, respectively.
Both versions require a separate $t$-predicate for every arity. We will show
a unified version for all arities by treating $x$ as an encoded list of
arguments.

Our universal function @{thm[display,names_short] "r_univ_def"} can represent
all partial recursive functions (see theorem @{thm[source] r_univ}). Moreover
@{term "r_result"}, @{term "r_dec"}, and @{term "r_not"} are primitive
recursive. As such @{term r_univ} could almost serve as the right-hand side
$u(\mu y[t(i, x, y) = 0]$. Its only flaw is that the outer function, the
composition of @{term r_dec} and @{term r_result}, is ternary rather than
unary.\<close>

lemma r_univ_almost_kleene_nf:
  "r_univ \<simeq>
   (let u = Cn 3 r_dec [r_result];
        t = Cn 3 r_not [r_result]
    in Cn 2 u [Mn 2 t, Id 2 0, Id 2 1])"
  unfolding r_univ_def by (rule exteqI) simp_all

text \<open>We can remedy the wrong arity with some encoding and
projecting.\<close>

definition r_nf_t :: recf where
  "r_nf_t \<equiv> Cn 3 r_and
    [Cn 3 r_eq [Cn 3 r_pdec2 [Id 3 0], Cn 3 r_prod_encode [Id 3 1, Id 3 2]],
     Cn 3 r_not
      [Cn 3 r_result
        [Cn 3 r_pdec1 [Id 3 0],
         Cn 3 r_pdec12 [Id 3 0],
         Cn 3 r_pdec22 [Id 3 0]]]]"

lemma r_nf_t_prim: "prim_recfn 3 r_nf_t"
  unfolding r_nf_t_def by simp

definition r_nf_u :: recf where
  "r_nf_u \<equiv> Cn 1 r_dec [Cn 1 r_result [r_pdec1, r_pdec12, r_pdec22]]"

lemma r_nf_u_prim: "prim_recfn 1 r_nf_u"
  unfolding r_nf_u_def by simp

lemma r_nf_t_0:
  assumes "eval r_result [pdec1 y, pdec12 y, pdec22 y] \<down>\<noteq> 0"
    and "pdec2 y = prod_encode (i, x)"
  shows "eval r_nf_t [y, i, x] \<down>= 0"
  unfolding r_nf_t_def using assms by auto

lemma r_nf_t_1:
  assumes "eval r_result [pdec1 y, pdec12 y, pdec22 y] \<down>= 0 \<or> pdec2 y \<noteq> prod_encode (i, x)"
  shows "eval r_nf_t [y, i, x] \<down>= 1"
  unfolding r_nf_t_def using assms r_result_total by auto

text \<open>The next function is just as universal as @{term r_univ}, but
satisfies the conditions of the Kleene normal form theorem because the
outer funtion @{term r_nf_u} is unary.\<close>

definition "r_normal_form \<equiv> Cn 2 r_nf_u [Mn 2 r_nf_t]"

lemma r_normal_form_recfn: "recfn 2 r_normal_form"
  unfolding r_normal_form_def using r_nf_u_prim r_nf_t_prim by simp

lemma r_univ_exteq_r_normal_form: "r_univ \<simeq> r_normal_form"
proof (rule exteqI)
  show arity: "arity r_univ = arity r_normal_form"
    using r_normal_form_recfn by simp
  show "eval r_univ xs = eval r_normal_form xs" if "length xs = arity r_univ" for xs
  proof -
    have "length xs = 2"
      using that by simp
    then obtain i x where ix: "[i, x] = xs"
      by (smt Suc_length_conv length_0_conv numeral_2_eq_2)
    have "eval r_univ [i, x] = eval r_normal_form [i, x]"
    proof (cases "\<forall>t. eval r_result [t, i, x] \<down>= 0")
      case True
      then have "eval r_univ [i, x] \<up>"
        unfolding r_univ_def by simp
      moreover have "eval r_normal_form [i, x] \<up>"
      proof -
        have "eval r_nf_t [y, i, x] \<down>= 1" for y
          using True r_nf_t_1[of y i x] by fastforce
        then show ?thesis
          unfolding r_normal_form_def using r_nf_u_prim r_nf_t_prim by simp
      qed
      ultimately show ?thesis by simp
    next
      case False
      then have "\<exists>t. eval r_result [t, i, x] \<down>\<noteq> 0"
        by (simp add: r_result_total)
      then obtain t where "eval r_result [t, i, x] \<down>\<noteq> 0"
        by auto
      then have "eval r_nf_t [triple_encode t i x, i, x] \<down>= 0"
        using r_nf_t_0 by simp
      then obtain y where y: "eval (Mn 2 r_nf_t) [i, x] \<down>= y"
        using r_nf_t_prim Mn_free_imp_total by fastforce
      then have "eval r_nf_t [y, i, x] \<down>= 0"
        using r_nf_t_prim Mn_free_imp_total eval_Mn_convergE(2)[of 2 r_nf_t "[i, x]" y]
        by simp
      then have r_result: "eval r_result [pdec1 y, pdec12 y, pdec22 y] \<down>\<noteq> 0"
        and pdec2: "pdec2 y = prod_encode (i, x)"
        using r_nf_t_0[of y i x] r_nf_t_1[of y i x] r_result_total by auto
      then have "eval r_result [pdec1 y, i, x] \<down>\<noteq> 0"
        by simp
      then obtain v where v:
          "eval r_univ [pdec12 y, pdec22 y] \<down>= v"
          "eval r_result [pdec1 y, pdec12 y, pdec22 y] \<down>= Suc v"
        using r_result r_result_bivalent'[of "pdec12 y" "pdec22 y" _ "pdec1 y"]
          r_result_diverg'[of "pdec12 y" "pdec22 y" "pdec1 y"]
        by auto
      
      have "eval r_normal_form [i, x] = eval r_nf_u [y]"
        unfolding r_normal_form_def using y r_nf_t_prim r_nf_u_prim by simp
      also have "... = eval r_dec [the (eval (Cn 1 r_result [r_pdec1, r_pdec12, r_pdec22]) [y])]"
        unfolding r_nf_u_def using r_result by simp
      also have "... = eval r_dec [Suc v]"
        using v by simp
      also have "... \<down>= v"
        by simp
      finally have "eval r_normal_form [i, x] \<down>= v" .
      moreover have "eval r_univ [i, x] \<down>= v"
        using v(1) pdec2 by simp
      ultimately show ?thesis by simp
    qed
    with ix show ?thesis by simp
  qed
qed

theorem normal_form:
  assumes "recfn n f"
  obtains i where "\<forall>x. e_length x = n \<longrightarrow> eval r_normal_form [i, x] = eval f (list_decode x)"
proof -
  have "eval r_normal_form [encode f, x] = eval f (list_decode x)" if "e_length x = n" for x
    using r_univ_exteq_r_normal_form assms that exteq_def r_univ' by auto
  then show ?thesis using that by auto
qed

text \<open>As a consequence of the normal form theorem every partial
recursive function can be represented with exactly one application of the
$\mu$-operator.\<close>

fun count_Mn :: "recf \<Rightarrow> nat" where
  "count_Mn Z = 0"
| "count_Mn S = 0"
| "count_Mn (Id m n) = 0"
| "count_Mn (Cn n f gs) = count_Mn f + sum_list (map count_Mn gs)"
| "count_Mn (Pr n f g) = count_Mn f + count_Mn g"
| "count_Mn (Mn n f) = Suc (count_Mn f)"

lemma count_Mn_zero_iff_prim: "count_Mn f = 0 \<longleftrightarrow> Mn_free f"
  by (induction f) auto

text \<open>The normal form has only one $\mu$-recursion.\<close>

lemma count_Mn_normal_form: "count_Mn r_normal_form = 1"
  unfolding r_normal_form_def r_nf_u_def r_nf_t_def using count_Mn_zero_iff_prim by simp

lemma one_Mn_suffices:
  assumes "recfn n f"
  shows "\<exists>g. count_Mn g = 1 \<and> g \<simeq> f"
proof -
  have "n > 0"
    using assms wellf_arity_nonzero by auto
  obtain i where i:
    "\<forall>x. e_length x = n \<longrightarrow> eval r_normal_form [i, x] = eval f (list_decode x)"
    using normal_form[OF assms(1)] by auto
  define g where "g \<equiv> Cn n r_normal_form [r_constn (n - 1) i, r_list_encode (n - 1)]"
  then have "recfn n g"
    using r_normal_form_recfn \<open>n > 0\<close> by simp
  then have "g \<simeq> f"
    using g_def r_list_encode i assms by (intro exteqI) simp_all
  moreover have "count_Mn g = 1"
    unfolding g_def using count_Mn_normal_form count_Mn_zero_iff_prim by simp
  ultimately show ?thesis by auto
qed

text \<open>The previous lemma could have been obtained without @{term
"r_normal_form"} directly from @{term "r_univ"}.\<close>


section \<open>The $s$-$m$-$n$ theorem\<close>

text \<open>For all $m, n > 0$ there is an $(m + 1)$-ary primitive recursive
function $s^m_n$ with
\[
  \varphi_p^{(m + n)}(c_1, \dots,c_m, x_1, \dots, x_n) =
  \varphi_{s^m_n(p, c_1, \dots,c_m)}^{(n)}(x_1, \dots, x_n)
\]
for all $p, c_1, \ldots, c_m, x_1, \ldots, x_n$. Here, $\varphi^{(n)}$ is a
function universal for $n$-ary partial recursive functions, which we will
represent by @{term "r_universal n"}\<close>

text \<open>The $s^m_n$ functions compute codes of functions. We start simple:
computing codes of the unary constant functions.\<close>

fun code_const1 :: "nat \<Rightarrow> nat" where
  "code_const1 0 = 0"
| "code_const1 (Suc c) = quad_encode 3 1 1 (singleton_encode (code_const1 c))"

lemma code_const1: "code_const1 c = encode (r_const c)"
  by (induction c) simp_all

definition "r_code_const1_aux \<equiv>
  Cn 3 r_prod_encode
    [r_constn 2 3,
      Cn 3 r_prod_encode
        [r_constn 2 1,
          Cn 3 r_prod_encode
            [r_constn 2 1, Cn 3 r_singleton_encode [Id 3 1]]]]"

lemma r_code_const1_aux_prim: "prim_recfn 3 r_code_const1_aux"
  by (simp_all add: r_code_const1_aux_def)

lemma r_code_const1_aux:
  "eval r_code_const1_aux [i, r, c] \<down>= quad_encode 3 1 1 (singleton_encode r)"
  by (simp add: r_code_const1_aux_def)

definition "r_code_const1 \<equiv> r_shrink (Pr 1 Z r_code_const1_aux)"

lemma r_code_const1_prim: "prim_recfn 1 r_code_const1"
  by (simp_all add: r_code_const1_def r_code_const1_aux_prim)

lemma r_code_const1: "eval r_code_const1 [c] \<down>= code_const1 c"
proof -
  let ?h = "Pr 1 Z r_code_const1_aux"
  have "eval ?h [c, x] \<down>= code_const1 c" for x
    using r_code_const1_aux r_code_const1_def
    by (induction c) (simp_all add: r_code_const1_aux_prim)
  then show ?thesis by (simp add: r_code_const1_def r_code_const1_aux_prim)
qed

text \<open>Functions that compute codes of higher-arity constant functions:\<close>

definition code_constn :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "code_constn n c \<equiv>
    if n = 1 then code_const1 c
    else quad_encode 3 n (code_const1 c) (singleton_encode (triple_encode 2 n 0))"

lemma code_constn: "code_constn (Suc n) c = encode (r_constn n c)"
  unfolding code_constn_def using code_const1 r_constn_def
  by (cases "n = 0") simp_all

definition r_code_constn :: "nat \<Rightarrow> recf" where
  "r_code_constn n \<equiv>
     if n = 1 then r_code_const1
     else
       Cn 1 r_prod_encode
        [r_const 3,
         Cn 1 r_prod_encode
          [r_const n,
           Cn 1 r_prod_encode
            [r_code_const1,
             Cn 1 r_singleton_encode
              [Cn 1 r_prod_encode
                [r_const 2, Cn 1 r_prod_encode [r_const n, Z]]]]]]"

lemma r_code_constn_prim: "prim_recfn 1 (r_code_constn n)"
  by (simp_all add: r_code_constn_def r_code_const1_prim)

lemma r_code_constn: "eval (r_code_constn n) [c] \<down>= code_constn n c"
  by (auto simp add: r_code_constn_def r_code_const1 code_constn_def r_code_const1_prim)

text \<open>Computing codes of $m$-ary projections:\<close>

definition code_id :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "code_id m n \<equiv> triple_encode 2 m n"

lemma code_id: "encode (Id m n) = code_id m n"
  unfolding code_id_def by simp

text \<open>The functions $s^m_n$ are represented by the following function.
The value $m$ corresponds to the length of @{term "cs"}.\<close>

definition smn :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "smn n p cs \<equiv> quad_encode
     3
     n
     (encode (r_universal (n + length cs)))
     (list_encode (code_constn n p # map (code_constn n) cs @ map (code_id n) [0..<n]))"

lemma smn:
  assumes "n > 0"
  shows "smn n p cs = encode
   (Cn n
     (r_universal (n + length cs))
     (r_constn (n - 1) p # map (r_constn (n - 1)) cs @ (map (Id n) [0..<n])))"
proof -
  let ?p = "r_constn (n - 1) p"
  let ?gs1 = "map (r_constn (n - 1)) cs"
  let ?gs2 = "map (Id n) [0..<n]"
  let ?gs = "?p # ?gs1 @ ?gs2"
  have "map encode ?gs1 = map (code_constn n) cs"
    by (intro nth_equalityI; auto; metis code_constn assms Suc_pred)
  moreover have "map encode ?gs2 = map (code_id n) [0..<n]"
    by (rule nth_equalityI) (auto simp add: code_id_def)
  moreover have "encode ?p = code_constn n p"
    using assms code_constn[of "n - 1" p] by simp
  ultimately have "map encode ?gs =
      code_constn n p # map (code_constn n) cs @ map (code_id n) [0..<n]"
    by simp
  then show ?thesis
    unfolding smn_def using assms encode.simps(4) by presburger
qed

text \<open>The next function is to help us define @{typ recf}s corresponding
to the $s^m_n$ functions. It maps $m + 1$ arguments $p, c_1, \ldots, c_m$ to
an encoded list of length $m + n + 1$. The list comprises the $m + 1$ codes
of the $n$-ary constants $p, c_1, \ldots, c_m$ and the $n$ codes for all
$n$-ary projections.\<close>

definition r_smn_aux :: "nat \<Rightarrow> nat \<Rightarrow> recf" where
  "r_smn_aux n m \<equiv>
     Cn (Suc m)
      (r_list_encode (m + n))
      (map (\<lambda>i. Cn (Suc m) (r_code_constn n) [Id (Suc m) i]) [0..<Suc m] @
       map (\<lambda>i. r_constn m (code_id n i)) [0..<n])"

lemma r_smn_aux_prim: "n > 0 \<Longrightarrow> prim_recfn (Suc m) (r_smn_aux n m)"
  by (auto simp add: r_smn_aux_def r_code_constn_prim)

lemma r_smn_aux:
  assumes "n > 0" and "length cs = m"
  shows "eval (r_smn_aux n m) (p # cs) \<down>=
    list_encode (map (code_constn n) (p # cs) @ map (code_id n) [0..<n])"
proof -
  let ?xs = "map (\<lambda>i. Cn (Suc m) (r_code_constn n) [Id (Suc m) i]) [0..<Suc m]"
  let ?ys = "map (\<lambda>i. r_constn m (code_id n i)) [0..<n]"
  have len_xs: "length ?xs = Suc m" by simp

  have map_xs: "map (\<lambda>g. eval g (p # cs)) ?xs = map Some (map (code_constn n) (p # cs))"
  proof (intro nth_equalityI)
    show len: "length (map (\<lambda>g. eval g (p # cs)) ?xs) =
        length (map Some (map (code_constn n) (p # cs)))"
      by (simp add: assms(2))

    have "map (\<lambda>g. eval g (p # cs)) ?xs ! i = map Some (map (code_constn n) (p # cs)) ! i"
        if "i < Suc m" for i
    proof -
      have "map (\<lambda>g. eval g (p # cs)) ?xs ! i = (\<lambda>g. eval g (p # cs)) (?xs ! i)"
        using len_xs that by (metis nth_map)
      also have "... = eval (Cn (Suc m) (r_code_constn n) [Id (Suc m) i]) (p # cs)"
        using that len_xs
        by (metis (no_types, lifting) add.left_neutral length_map nth_map nth_upt)
      also have "... = eval (r_code_constn n) [the (eval (Id (Suc m) i) (p # cs))]"
        using r_code_constn_prim assms(2) that by simp
      also have "... = eval (r_code_constn n) [(p # cs) ! i]"
        using len that by simp
      finally have "map (\<lambda>g. eval g (p # cs)) ?xs ! i \<down>= code_constn n ((p # cs) ! i)"
        using r_code_constn by simp
      then show ?thesis
        using len_xs len that by (metis length_map nth_map)
    qed
    moreover have "length (map (\<lambda>g. eval g (p # cs)) ?xs) = Suc m" by simp
    ultimately show "\<And>i. i < length (map (\<lambda>g. eval g (p # cs)) ?xs) \<Longrightarrow>
        map (\<lambda>g. eval g (p # cs)) ?xs ! i =
        map Some (map (code_constn n) (p # cs)) ! i"
      by simp
  qed
  moreover have "map (\<lambda>g. eval g (p # cs)) ?ys = map Some (map (code_id n) [0..<n])"
    using assms(2) by (intro nth_equalityI; auto)
  ultimately have "map (\<lambda>g. eval g (p # cs)) (?xs @ ?ys) =
      map Some (map (code_constn n) (p # cs) @ map (code_id n) [0..<n])"
    by (metis map_append)
  moreover have "map (\<lambda>x. the (eval x (p # cs))) (?xs @ ?ys) =
      map the (map (\<lambda>x. eval x (p # cs)) (?xs @ ?ys))"
    by simp
  ultimately have *: "map (\<lambda>g. the (eval g (p # cs))) (?xs @ ?ys) =
      (map (code_constn n) (p # cs) @ map (code_id n) [0..<n])"
    by simp

  have "\<forall>i<length ?xs. eval (?xs ! i) (p # cs) = map (\<lambda>g. eval g (p # cs)) ?xs ! i"
    by (metis nth_map)
  then have
    "\<forall>i<length ?xs. eval (?xs ! i) (p # cs) = map Some (map (code_constn n) (p # cs)) ! i"
    using map_xs by simp
  then have "\<forall>i<length ?xs. eval (?xs ! i) (p # cs) \<down>"
    using assms map_xs by (metis length_map nth_map option.simps(3))
  then have xs_converg: "\<forall>z\<in>set ?xs. eval z (p # cs) \<down>"
    by (metis in_set_conv_nth)

  have "\<forall>i<length ?ys. eval (?ys ! i) (p # cs) = map (\<lambda>x. eval x (p # cs)) ?ys ! i"
    by simp
  then have
    "\<forall>i<length ?ys. eval (?ys ! i) (p # cs) = map Some (map (code_id n) [0..<n]) ! i"
    using assms(2) by simp
  then have "\<forall>i<length ?ys. eval (?ys ! i) (p # cs) \<down>"
    by simp
  then have "\<forall>z\<in>set (?xs @ ?ys). eval z (p # cs) \<down>"
    using xs_converg by auto
  moreover have "recfn (length (p # cs)) (Cn (Suc m) (r_list_encode (m + n)) (?xs @ ?ys))"
    using assms r_code_constn_prim by auto
  ultimately have "eval (r_smn_aux n m) (p # cs) =
      eval (r_list_encode (m + n)) (map (\<lambda>g. the (eval g (p # cs))) (?xs @ ?ys))"
    unfolding r_smn_aux_def using assms by simp
  then have "eval (r_smn_aux n m) (p # cs) =
      eval (r_list_encode (m + n)) (map (code_constn n) (p # cs) @ map (code_id n) [0..<n])"
    using * by metis
  moreover have "length (?xs @ ?ys) = Suc (m + n)" by simp
  ultimately show ?thesis
    using r_list_encode * assms(1) by (metis (no_types, lifting) length_map)
qed

text \<open>For all $m, n > 0$, the @{typ recf} corresponding to $s^m_n$ is
given by the next function.\<close>

definition r_smn :: "nat \<Rightarrow> nat \<Rightarrow> recf" where
 "r_smn n m \<equiv>
    Cn (Suc m) r_prod_encode
     [r_constn m 3,
      Cn (Suc m) r_prod_encode
       [r_constn m n,
        Cn (Suc m) r_prod_encode
          [r_constn m (encode (r_universal (n + m))), r_smn_aux n m]]]"

lemma r_smn_prim [simp]: "n > 0 \<Longrightarrow> prim_recfn (Suc m) (r_smn n m)"
  by (simp_all add: r_smn_def r_smn_aux_prim)

lemma r_smn:
  assumes "n > 0" and "length cs = m"
  shows "eval (r_smn n m) (p # cs) \<down>= smn n p cs"
  using assms r_smn_def r_smn_aux smn_def r_smn_aux_prim by simp

lemma map_eval_Some_the:
  assumes "map (\<lambda>g. eval g xs) gs = map Some ys"
  shows "map (\<lambda>g. the (eval g xs)) gs = ys"
  using assms
  by (metis (no_types, lifting) length_map nth_equalityI nth_map option.sel)

text \<open>The essential part of the $s$-$m$-$n$ theorem: For all $m, n > 0$
the function $s^m_n$ satisfies
\[
  \varphi_p^{(m + n)}(c_1, \dots,c_m, x_1, \dots, x_n) =
  \varphi_{s^m_n(p, c_1, \dots,c_m)}^{(n)}(x_1, \dots, x_n)
\] for all $p, c_i, x_j$.\<close>

lemma smn_lemma:
  assumes "n > 0" and len_cs: "length cs = m" and len_xs: "length xs = n"
  shows "eval (r_universal (m + n)) (p # cs @ xs) =
    eval (r_universal n) ((the (eval (r_smn n m) (p # cs))) # xs)"
proof -
  let ?s = "r_smn n m"
  let ?f = "Cn n
    (r_universal (n + length cs))
    (r_constn (n - 1) p # map (r_constn (n - 1)) cs @ (map (Id n) [0..<n]))"
  have "eval ?s (p # cs) \<down>= smn n p cs"
    using assms r_smn by simp
  then have eval_s: "eval ?s (p # cs) \<down>= encode ?f"
    by (simp add: assms(1) smn)

  have "recfn n ?f"
    using len_cs assms by auto
  then have *: "eval (r_universal n) ((encode ?f) # xs) = eval ?f xs"
    using r_universal[of ?f n, OF _ len_xs] by simp

  let ?gs = "r_constn (n - 1) p # map (r_constn (n - 1)) cs @ map (Id n) [0..<n]"
  have "\<forall>g\<in>set ?gs. eval g xs \<down>"
    using len_cs len_xs assms by auto
  then have "eval ?f xs =
      eval (r_universal (n + length cs)) (map (\<lambda>g. the (eval g xs)) ?gs)"
    using len_cs len_xs assms \<open>recfn n ?f\<close> by simp
  then have "eval ?f xs = eval (r_universal (m + n)) (map (\<lambda>g. the (eval g xs)) ?gs)"
    by (simp add: len_cs add.commute)
  then have "eval (r_universal n) ((the (eval ?s (p # cs))) # xs) =
      eval (r_universal (m + n)) (map (\<lambda>g. the (eval g xs)) ?gs)"
    using eval_s * by simp
  moreover have "map (\<lambda>g. the (eval g xs)) ?gs = p # cs @ xs"
  proof (intro nth_equalityI)
    show "length (map (\<lambda>g. the (eval g xs)) ?gs) = length (p # cs @ xs)"
      by (simp add: len_xs)
    have len: "length (map (\<lambda>g. the (eval g xs)) ?gs) = Suc (m + n)"
      by (simp add: len_cs)
    moreover have "map (\<lambda>g. the (eval g xs)) ?gs ! i = (p # cs @ xs) ! i"
      if "i < Suc (m + n)" for i
    proof -
      from that consider "i = 0" | "i > 0 \<and> i < Suc m" | "Suc m \<le> i \<and> i < Suc (m + n)"
        using not_le_imp_less by auto
      then show ?thesis
      proof (cases)
        case 1
        then show ?thesis using assms(1) len_xs by simp
      next
        case 2
        then have "?gs ! i = (map (r_constn (n - 1)) cs) ! (i - 1)"
          using len_cs
          by (metis One_nat_def Suc_less_eq Suc_pred length_map
            less_numeral_extra(3) nth_Cons' nth_append)
        then have "map (\<lambda>g. the (eval g xs)) ?gs ! i =
            (\<lambda>g. the (eval g xs)) ((map (r_constn (n - 1)) cs) ! (i - 1))"
          using len by (metis length_map nth_map that)
        also have "... = the (eval ((r_constn (n - 1) (cs ! (i - 1)))) xs)"
          using 2 len_cs by auto
        also have "... = cs ! (i - 1)"
          using r_constn len_xs assms(1) by simp
        also have "... = (p # cs @ xs) ! i"
          using 2 len_cs
          by (metis diff_Suc_1 less_Suc_eq_0_disj less_numeral_extra(3) nth_Cons' nth_append)
        finally show ?thesis .
      next
        case 3
        then have "?gs ! i = (map (Id n) [0..<n]) ! (i - Suc m)"
          using len_cs 
          by (simp; metis (no_types, lifting) One_nat_def Suc_less_eq add_leE
            plus_1_eq_Suc diff_diff_left length_map not_le nth_append
            ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
        then have "map (\<lambda>g. the (eval g xs)) ?gs ! i =
            (\<lambda>g. the (eval g xs)) ((map (Id n) [0..<n]) ! (i - Suc m))"
          using len by (metis length_map nth_map that)
        also have "... = the (eval ((Id n (i - Suc m))) xs)"
          using 3 len_cs by auto
        also have "... = xs ! (i - Suc m)"
          using len_xs 3 by auto
        also have "... = (p # cs @ xs) ! i"
          using len_cs len_xs 3
          by (metis diff_Suc_1 diff_diff_left less_Suc_eq_0_disj not_le nth_Cons'
            nth_append plus_1_eq_Suc)
        finally show ?thesis .
      qed
    qed
    ultimately show "map (\<lambda>g. the (eval g xs)) ?gs ! i = (p # cs @ xs) ! i"
        if "i < length (map (\<lambda>g. the (eval g xs)) ?gs)" for i
      using that by simp
  qed
  ultimately show ?thesis by simp
qed

theorem smn_theorem:
  assumes "n > 0"
  shows "\<exists>s. prim_recfn (Suc m) s \<and>
    (\<forall>p cs xs. length cs = m \<and> length xs = n \<longrightarrow>
        eval (r_universal (m + n)) (p # cs @ xs) =
        eval (r_universal n) ((the (eval s (p # cs))) # xs))"
  using smn_lemma exI[of _ "r_smn n m"] assms by simp

text \<open>For every numbering, that is, binary partial recursive function,
$\psi$ there is a total recursive function $c$ that translates $\psi$-indices
into $\varphi$-indices.\<close>

lemma numbering_translation:
  assumes "recfn 2 psi"
  obtains c where
    "recfn 1 c"
    "total c"
    "\<forall>i x. eval psi [i, x] = eval r_phi [the (eval c [i]), x]"
proof -
  let ?p = "encode psi"
  define c where "c = Cn 1 (r_smn 1 1) [r_const ?p, Id 1 0]"
  then have "prim_recfn 1 c" by simp
  moreover from this have "total c"
    by auto
  moreover have "eval r_phi [the (eval c [i]), x] = eval psi [i, x]" for i x
  proof -
    have "eval c [i] = eval (r_smn 1 1) [?p, i]"
      using c_def by simp
    then have "eval (r_universal 1) [the (eval c [i]), x] =
        eval (r_universal 1) [the (eval (r_smn 1 1) [?p, i]), x]"
      by simp
    also have "... = eval (r_universal (1 + 1)) (?p # [i] @ [x])"
      using smn_lemma[of 1 "[i]" 1 "[x]" ?p] by simp
    also have "... = eval (r_universal 2) [?p, i, x]"
      by (metis append_eq_Cons_conv nat_1_add_1)
    also have "... = eval psi [i, x]"
      using r_universal[OF assms, of "[i, x]"] by simp
    finally have "eval (r_universal 1) [the (eval c [i]), x] = eval psi [i, x]" .
    then show ?thesis using r_phi_def by simp
  qed
  ultimately show ?thesis using that by auto
qed


section \<open>Fixed-point theorems\<close>

text \<open>Fixed-point theorems (also known as recursion theorems) come in
many shapes. We prove the minimum we need for Chapter~\ref{c:iirf}.\<close>


subsection \<open>Rogers's fixed-point theorem\<close>

text \<open>In this section we prove a theorem that Rogers~\cite{Rogers87}
credits to Kleene, but admits that it is a special case and not the original
formulation. We follow Wikipedia~\cite{wiki-krt} and call it the Rogers's
fixed-point theorem.\<close>

lemma s11_inj: "inj (\<lambda>x. smn 1 p [x])"
proof
  fix x\<^sub>1 x\<^sub>2 :: nat
  assume "smn 1 p [x\<^sub>1] = smn 1 p [x\<^sub>2]"
  then have "list_encode [code_constn 1 p, code_constn 1 x\<^sub>1, code_id 1 0] =
      list_encode [code_constn 1 p, code_constn 1 x\<^sub>2, code_id 1 0]"
    using smn_def by (simp add: prod_encode_eq)
  then have "[code_constn 1 p, code_constn 1 x\<^sub>1, code_id 1 0] =
      [code_constn 1 p, code_constn 1 x\<^sub>2, code_id 1 0]"
    using list_decode_encode by metis
  then have "code_constn 1 x\<^sub>1 = code_constn 1 x\<^sub>2" by simp
  then show "x\<^sub>1 = x\<^sub>2"
    using code_const1 code_constn code_constn_def encode_injective r_constn
    by (metis One_nat_def length_Cons list.size(3) option.simps(1))
qed

definition "r_univuniv \<equiv> Cn 2 r_phi [Cn 2 r_phi [Id 2 0, Id 2 0], Id 2 1]"

lemma r_univuniv_recfn: "recfn 2 r_univuniv"
  by (simp add: r_univuniv_def)

lemma r_univuniv_converg:
  assumes "eval r_phi [x, x] \<down>"
  shows "eval r_univuniv [x, y] = eval r_phi [the (eval r_phi [x, x]), y]"
  unfolding r_univuniv_def using assms r_univuniv_recfn r_phi_recfn by simp

text \<open>Strictly speaking this is a generalization of Rogers's theorem in
that it shows the existence of infinitely many fixed-points. In conventional
terms it says that for every total recursive $f$ and $k \in \mathbb{N}$ there is
an $n \geq k$ with $\varphi_n = \varphi_{f(n)}$.\<close>

theorem rogers_fixed_point_theorem:
  fixes k :: nat
  assumes "recfn 1 f" and "total f"
  shows "\<exists>n\<ge>k. \<forall>x. eval r_phi [n, x] = eval r_phi [the (eval f [n]), x]"
proof -
  let ?p = "encode r_univuniv"
  define h where "h = Cn 1 (r_smn 1 1) [r_const ?p, Id 1 0]"
  then have "prim_recfn 1 h"
    by simp
  then have "total h"
    by blast
  have "eval h [x] = eval (Cn 1 (r_smn 1 1) [r_const ?p, Id 1 0]) [x]" for x
    unfolding h_def by simp
  then have h: "the (eval h [x]) = smn 1 ?p [x]" for x
    by (simp add: r_smn)

  have "eval r_phi [the (eval h [x]), y] = eval r_univuniv [x, y]" for x y
  proof -
    have "eval r_phi [the (eval h [x]), y] = eval r_phi [smn 1 ?p [x], y]"
      using h by simp
    also have "... = eval r_phi [the (eval (r_smn 1 1) [?p, x]), y]"
      by (simp add: r_smn)
    also have "... = eval (r_universal 2) [?p, x, y]"
      using r_phi_def smn_lemma[of 1 "[x]" 1 "[y]" ?p]
      by (metis Cons_eq_append_conv One_nat_def Suc_1 length_Cons
        less_numeral_extra(1) list.size(3) plus_1_eq_Suc)
    finally show "eval r_phi [the (eval h [x]), y] = eval r_univuniv [x, y]"
      using r_universal r_univuniv_recfn by simp
  qed
  then have *: "eval r_phi [the (eval h [x]), y] = eval r_phi [the (eval r_phi [x, x]), y]"
      if "eval r_phi [x, x] \<down>" for x y
    using r_univuniv_converg that by simp

  let ?fh = "Cn 1 f [h]"
  have "recfn 1 ?fh"
    using \<open>prim_recfn 1 h\<close> assms by simp
  then have "infinite {r. recfn 1 r \<and> r \<simeq> ?fh}"
    using exteq_infinite[of ?fh 1] by simp
  then have "infinite (encode ` {r. recfn 1 r \<and> r \<simeq> ?fh})" (is "infinite ?E")
    using encode_injective by (meson finite_imageD inj_onI)
  then have "infinite ((\<lambda>x. smn 1 ?p [x]) ` ?E)"
    using s11_inj[of ?p] by (simp add: finite_image_iff inj_on_subset)
  moreover have "(\<lambda>x. smn 1 ?p [x]) ` ?E = {smn 1 ?p [encode r] |r. recfn 1 r \<and> r \<simeq> ?fh}"
    by auto
  ultimately have "infinite {smn 1 ?p [encode r] |r. recfn 1 r \<and> r \<simeq> ?fh}"
    by simp
  then obtain n where "n \<ge> k" "n \<in> {smn 1 ?p [encode r] |r. recfn 1 r \<and> r \<simeq> ?fh}"
    by (meson finite_nat_set_iff_bounded_le le_cases)
  then obtain r where r: "recfn 1 r" "n = smn 1 ?p [encode r]" "recfn 1 r \<and> r \<simeq> ?fh"
    by auto
  then have eval_r: "eval r [encode r] = eval ?fh [encode r]"
    by (simp add: exteq_def)
  then have eval_r': "eval r [encode r] = eval f [the (eval h [encode r])]"
    using assms \<open>total h\<close> \<open>prim_recfn 1 h\<close> by simp
  then have "eval r [encode r] \<down>"
    using  \<open>prim_recfn 1 h\<close> assms(1,2) by simp
  then have "eval r_phi [encode r, encode r] \<down>"
    by (simp add: \<open>recfn 1 r\<close> r_phi)
  then have "eval r_phi [the (eval h [encode r]), y] =
      eval r_phi [(the (eval r_phi [encode r, encode r])), y]"
      for y
    using * by simp
  then have "eval r_phi [the (eval h [encode r]), y] =
      eval r_phi [(the (eval r [encode r])), y]"
      for y
    by (simp add: \<open>recfn 1 r\<close> r_phi)
  moreover have "n = the (eval h [encode r])" by (simp add: h r(2))
  ultimately have "eval r_phi [n, y] = eval r_phi [the (eval r [encode r]), y]" for y
    by simp
  then have "eval r_phi [n, y] = eval r_phi [the (eval ?fh [encode r]), y]" for y
    using r by (simp add: eval_r)
  moreover have "eval ?fh [encode r] = eval f [n]"
    using eval_r eval_r' \<open>n = the (eval h [encode r])\<close> by auto 
  ultimately have "eval r_phi [n, y] = eval r_phi [the (eval f [n]), y]" for y
    by simp
  with \<open>n \<ge> k\<close> show ?thesis by auto
qed


subsection \<open>Kleene's fixed-point theorem\<close>

text \<open>The next theorem is what Rogers~\cite[p.~214]{Rogers87} calls
Kleene's version of what we call Rogers's fixed-point theorem. More precisely
this would be Kleene's \emph{second} fixed-point theorem, but since we do not
cover the first one, we leave out the number.\<close>

theorem kleene_fixed_point_theorem:
  fixes k :: nat
  assumes "recfn 2 psi"
  shows "\<exists>n\<ge>k. \<forall>x. eval r_phi [n, x] = eval psi [n, x]"
proof -
  from numbering_translation[OF assms] obtain c where c:
    "recfn 1 c"
    "total c"
    "\<forall>i x. eval psi [i, x] = eval r_phi [the (eval c [i]), x]"
    by auto
  then obtain n where "n \<ge> k" and "\<forall>x. eval r_phi [n, x] = eval r_phi [the (eval c [n]), x]"
    using rogers_fixed_point_theorem by blast
  with c(3) have "\<forall>x. eval r_phi [n, x] = eval psi [n, x]"
    by simp
  with \<open>n \<ge> k\<close> show ?thesis by auto
qed

text \<open>Kleene's fixed-point theorem can be generalized to arbitrary
arities. But we need to generalize it only to binary functions in order to
show Smullyan's double fixed-point theorem in
Section~\ref{s:smullyan}.\<close>

definition "r_univuniv2 \<equiv>
  Cn 3 r_phi [Cn 3 (r_universal 2) [Id 3 0, Id 3 0, Id 3 1], Id 3 2]"

lemma r_univuniv2_recfn: "recfn 3 r_univuniv2"
  by (simp add: r_univuniv2_def)

lemma r_univuniv2_converg:
  assumes "eval (r_universal 2) [u, u, x] \<down>"
  shows "eval r_univuniv2 [u, x, y] = eval r_phi [the (eval (r_universal 2) [u, u, x]), y]"
  unfolding r_univuniv2_def using assms r_univuniv2_recfn by simp

theorem kleene_fixed_point_theorem_2:
  assumes "recfn 2 f" and "total f"
  shows "\<exists>n.
    recfn 1 n \<and>
    total n \<and>
    (\<forall>x y. eval r_phi [(the (eval n [x])), y] = eval r_phi [(the (eval f [the (eval n [x]), x])), y])"
proof -
  let ?p = "encode r_univuniv2"
  let ?s = "r_smn 1 2"
  define h where "h = Cn 2 ?s [r_dummy 1 (r_const ?p), Id 2 0, Id 2 1]"
  then have [simp]: "prim_recfn 2 h" by simp
  {
    fix u x y
    have "eval h [u, x] = eval (Cn 2 ?s [r_dummy 1 (r_const ?p), Id 2 0, Id 2 1]) [u, x]"
      using h_def by simp
    then have "the (eval h [u, x]) = smn 1 ?p [u, x]"
      by (simp add: r_smn)
    then have "eval r_phi [the (eval h [u, x]), y] = eval r_phi [smn 1 ?p [u, x], y]"
      by simp
    also have "... =
      eval r_phi
        [encode (Cn 1 (r_universal 3) (r_constn 0 ?p # r_constn 0 u # r_constn 0 x # [Id 1 0])),
         y]"
      using smn[of 1 ?p "[u, x]"] by (simp add: numeral_3_eq_3)
    also have "... =
      eval r_phi
        [encode (Cn 1 (r_universal 3) (r_const ?p # r_const u # r_const x # [Id 1 0])), y]"
        (is "_ = eval r_phi [encode ?f, y]")
      by (simp add: r_constn_def)
    also have "... = eval ?f [y]"
      using r_phi'[of ?f] by auto
    also have "... = eval (r_universal 3) [?p, u, x, y]"
      using r_univuniv2_recfn r_universal r_phi by auto
    also have "... = eval r_univuniv2 [u, x, y]"
      using r_universal
      by (simp add: r_universal r_univuniv2_recfn) 
    finally have "eval r_phi [the (eval h [u, x]), y] =  eval r_univuniv2 [u, x, y]" .
  }
  then have *: "eval r_phi [the (eval h [u, x]), y] =
      eval r_phi [the (eval (r_universal 2) [u, u, x]), y]"
      if "eval (r_universal 2) [u, u, x] \<down>" for u x y
    using r_univuniv2_converg that by simp

  let ?fh = "Cn 2 f [h, Id 2 1]"
  let ?e = "encode ?fh"
  have "recfn 2 ?fh"
    using assms by simp
  have "total h"
    by auto
  then have "total ?fh"
    using assms Cn_total totalI2[of ?fh] by fastforce

  let ?n = "Cn 1 h [r_const ?e, Id 1 0]"
  have "recfn 1 ?n"
    using assms by simp
  moreover have "total ?n"
    using \<open>total h\<close> totalI1[of ?n] by simp
  moreover {
    fix x y
    have "eval r_phi [(the (eval ?n [x])), y] = eval r_phi [(the (eval h [?e, x])), y]"
      by simp
    also have "... = eval r_phi [the (eval (r_universal 2) [?e, ?e, x]), y]"
      using * r_universal[of _ 2] totalE[of ?fh 2] \<open>total ?fh\<close> \<open>recfn 2 ?fh\<close> 
      by (metis length_Cons list.size(3) numeral_2_eq_2)
    also have "... = eval r_phi [the (eval f [the (eval h [?e, x]), x]), y]"
    proof -
      have "eval (r_universal 2) [?e, ?e, x] \<down>"
        using totalE[OF \<open>total ?fh\<close>] \<open>recfn 2 ?fh\<close> r_universal
        by (metis length_Cons list.size(3) numeral_2_eq_2)
      moreover have "eval (r_universal 2) [?e, ?e, x] = eval ?fh [?e, x]"
        by (metis \<open>recfn 2 ?fh\<close> length_Cons list.size(3) numeral_2_eq_2 r_universal)
      then show ?thesis using assms \<open>total h\<close> by simp
    qed
    also have "... =  eval r_phi [(the (eval f [the (eval ?n [x]), x])), y]"
      by simp
    finally have "eval r_phi [(the (eval ?n [x])), y] =
      eval r_phi [(the (eval f [the (eval ?n [x]), x])), y]" .
  }
  ultimately show ?thesis by blast
qed


subsection \<open>Smullyan's double fixed-point theorem\label{s:smullyan}\<close>

theorem smullyan_double_fixed_point_theorem:
  assumes "recfn 2 g" and "total g" and "recfn 2 h" and "total h"
  shows "\<exists>m n.
    (\<forall>x. eval r_phi [m, x] = eval r_phi [the (eval g [m, n]), x]) \<and>
    (\<forall>x. eval r_phi [n, x] = eval r_phi [the (eval h [m, n]), x])"
proof -
  obtain m where
    "recfn 1 m" and
    "total m" and
    m: "\<forall>x y. eval r_phi [the (eval m [x]), y] =
      eval r_phi [the (eval g [the (eval m [x]), x]), y]"
    using kleene_fixed_point_theorem_2[of g] assms(1,2) by auto
  define k where "k = Cn 1 h [m, Id 1 0]"
  then have "recfn 1 k"
    using \<open>recfn 1 m\<close> assms(3) by simp
  have "total (Id 1 0)"
    by (simp add: Mn_free_imp_total)
  then have "total k"
    using \<open>total m\<close> assms(4) Cn_total k_def \<open>recfn 1 k\<close> by simp
  obtain n where n: "\<forall>x. eval r_phi [n, x] = eval r_phi [the (eval k [n]), x]"
    using rogers_fixed_point_theorem[of k] \<open>recfn 1 k\<close> \<open>total k\<close> by blast
  obtain mm where mm: "eval m [n] \<down>= mm"
    using \<open>total m\<close> \<open>recfn 1 m\<close> by fastforce
  then have "\<forall>x. eval r_phi [mm, x] = eval r_phi [the (eval g [mm, n]), x]"
    by (metis m option.sel)
  moreover have "\<forall>x. eval r_phi [n, x] = eval r_phi [the (eval h [mm, n]), x]"
    using k_def assms(3) \<open>total m\<close> \<open>recfn 1 m\<close> mm n by simp
  ultimately show ?thesis by blast
qed


section \<open>Decidable and recursively enumerable sets\label{s:decidable}\<close>

text \<open>We defined @{term decidable} already back in
Section~\ref{s:halting}: @{thm[display] decidable_def}\<close>

text \<open>The next theorem is adapted from @{thm[source]
halting_problem_undecidable}.\<close>

theorem halting_problem_phi_undecidable: "\<not> decidable {x. eval r_phi [x, x] \<down>}"
  (is "\<not> decidable ?K")
proof
  assume "decidable ?K"
  then obtain f where "recfn 1 f" and f: "\<forall>x. eval f [x] \<down>= (if x \<in> ?K then 1 else 0)"
    using decidable_def by auto
  define g where "g \<equiv> Cn 1 r_ifeq_else_diverg [f, Z, Z]"
  then have "recfn 1 g"
    using \<open>recfn 1 f\<close> r_ifeq_else_diverg_recfn by simp
  then obtain i where i: "eval r_phi [i, x] = eval g [x]" for x
    using r_phi' by auto
  from g_def have "eval g [x] = (if x \<notin> ?K then Some 0 else None)" for x
    using r_ifeq_else_diverg_recfn \<open>recfn 1 f\<close> f by simp
  then have "eval g [i] \<down> \<longleftrightarrow> i \<notin> ?K" by simp
  also have "... \<longleftrightarrow> eval r_phi [i, i] \<up>" by simp
  also have "... \<longleftrightarrow> eval g [i] \<up>"
    using i by simp
  finally have "eval g [i] \<down> \<longleftrightarrow> eval g [i] \<up>" .
  then show False by auto
qed

lemma decidable_complement: "decidable X \<Longrightarrow> decidable (- X)"
proof -
  assume "decidable X"
  then obtain f where f: "recfn 1 f" "\<forall>x. eval f [x] \<down>= (if x \<in> X then 1 else 0)"
    using decidable_def by auto
  define g where "g = Cn 1 r_not [f]"
  then have "recfn 1 g"
    by (simp add: f(1))
  moreover have "eval g [x] \<down>= (if x \<in> X then 0 else 1)" for x
    by (simp add: g_def f)
  ultimately show ?thesis using decidable_def by auto
qed

text \<open>Finite sets are decidable.\<close>

fun r_contains :: "nat list \<Rightarrow> recf" where
  "r_contains [] = Z"
| "r_contains (x # xs) = Cn 1 r_ifeq [Id 1 0, r_const x, r_const 1, r_contains xs]"

lemma r_contains_prim: "prim_recfn 1 (r_contains xs)"
  by (induction xs) auto

lemma r_contains: "eval (r_contains xs) [x] \<down>= (if x \<in> set xs then 1 else 0)"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have "eval (r_contains (a # xs)) [x] = eval r_ifeq [x, a, 1, the (eval (r_contains xs) [x])]"
    using r_contains_prim prim_recfn_total by simp
  also have "... \<down>= (if x = a then 1 else if x \<in> set xs then 1 else 0)"
    using Cons.IH by simp
  also have "... \<down>= (if x = a \<or> x \<in> set xs then 1 else 0)"
    by simp
  finally show ?case by simp
qed

lemma finite_set_decidable: "finite X \<Longrightarrow> decidable X"
proof -
  fix X :: "nat set"
  assume "finite X"
  then obtain xs where "X = set xs"
    using finite_list by auto
  then have "\<forall>x. eval (r_contains xs) [x] \<down>= (if x \<in> X then 1 else 0)"
    using r_contains by simp
  then show "decidable X"
    using decidable_def r_contains_prim by blast
qed

definition semidecidable :: "nat set \<Rightarrow> bool" where
  "semidecidable X \<equiv> (\<exists>f. recfn 1 f \<and> (\<forall>x. eval f [x] = (if x \<in> X then Some 1 else None)))"

text \<open>The semidecidable sets are the domains of partial recursive functions.\<close>

lemma semidecidable_iff_domain:
  "semidecidable X \<longleftrightarrow> (\<exists>f. recfn 1 f \<and> (\<forall>x. eval f [x] \<down> \<longleftrightarrow> x \<in> X))"
proof
  show "semidecidable X \<Longrightarrow> \<exists>f. recfn 1 f \<and> (\<forall>x. (eval f [x] \<down>) = (x \<in> X))"
    using semidecidable_def by (metis option.distinct(1))
  show "semidecidable X" if "\<exists>f. recfn 1 f \<and> (\<forall>x. (eval f [x] \<down>) = (x \<in> X))" for X
  proof -
    from that obtain f where f: "recfn 1 f" "\<forall>x. (eval f [x] \<down>) = (x \<in> X)"
      by auto
    let ?g = "Cn 1 (r_const 1) [f]"
    have "recfn 1 ?g"
      using f(1) by simp
    moreover have "\<forall>x. eval ?g [x] = (if x \<in> X then Some 1 else None)"
      using f by simp
    ultimately show "semidecidable X"
      using semidecidable_def by blast
  qed
qed

lemma decidable_imp_semidecidable: "decidable X \<Longrightarrow> semidecidable X"
proof -
  assume "decidable X"
  then obtain f where f: "recfn 1 f" "\<forall>x. eval f [x] \<down>= (if x \<in> X then 1 else 0)"
    using decidable_def by auto
  define g where "g = Cn 1 r_ifeq_else_diverg [f, r_const 1, r_const 1]"
  then have "recfn 1 g"
    by (simp add: f(1))
  have "eval g [x] = eval r_ifeq_else_diverg [if x \<in> X then 1 else 0, 1, 1]" for x
    by (simp add: g_def f)
  then have "\<And>x. x \<in> X \<Longrightarrow> eval g [x] \<down>= 1" and "\<And>x. x \<notin> X \<Longrightarrow> eval g [x] \<up>"
    by simp_all
  then show ?thesis
    using \<open>recfn 1 g\<close> semidecidable_def by auto
qed

text \<open>A set is recursively enumerable if it is empty or the image of a
total recursive function.\<close>

definition recursively_enumerable :: "nat set \<Rightarrow> bool" where
  "recursively_enumerable X \<equiv>
     X = {} \<or> (\<exists>f. recfn 1 f \<and> total f \<and> X = {the (eval f [x]) |x. x \<in> UNIV})"

theorem recursively_enumerable_iff_semidecidable:
  "recursively_enumerable X \<longleftrightarrow> semidecidable X"
proof
  show "semidecidable X" if "recursively_enumerable X" for X
  proof (cases)
    assume "X = {}"
    then show ?thesis
      using finite_set_decidable decidable_imp_semidecidable
        recursively_enumerable_def semidecidable_def
      by blast
  next
    assume "X \<noteq> {}"
    with that obtain f where f: "recfn 1 f" "total f" "X = {the (eval f [x]) |x. x \<in> UNIV}"
      using recursively_enumerable_def by blast
    define h where "h = Cn 2 r_eq [Cn 2 f [Id 2 0], Id 2 1]"
    then have "recfn 2 h"
      using f(1) by simp
    from h_def have h: "eval h [x, y] \<down>= 0 \<longleftrightarrow> the (eval f [x]) = y" for x y
      using f(1,2) by simp
    from h_def \<open>recfn 2 h\<close> totalI2 f(2) have "total h" by simp
    define g where "g = Mn 1 h"
    then have "recfn 1 g"
      using h_def f(1) by simp
    then have "eval g [y] =
      (if (\<exists>x. eval h [x, y] \<down>= 0 \<and> (\<forall>x'<x. eval h [x', y] \<down>))
       then Some (LEAST x. eval h [x, y] \<down>= 0)
       else None)" for y
      using g_def \<open>total h\<close> f(2) by simp
    then have "eval g [y] =
      (if \<exists>x. eval h [x, y] \<down>= 0
       then Some (LEAST x. eval h [x, y] \<down>= 0)
       else None)" for y
      using \<open>total h\<close> \<open>recfn 2 h\<close> by simp
    then have "eval g [y] \<down> \<longleftrightarrow> (\<exists>x. eval h [x, y] \<down>= 0)" for y
      by simp
    with h have "eval g [y] \<down> \<longleftrightarrow> (\<exists>x. the (eval f [x]) = y)" for y
      by simp
    with f(3) have "eval g [y] \<down> \<longleftrightarrow> y \<in> X" for y
      by auto
    with \<open>recfn 1 g\<close> semidecidable_iff_domain show ?thesis by auto
  qed

  show "recursively_enumerable X" if "semidecidable X" for X
  proof (cases)
    assume "X = {}"
    then show ?thesis using recursively_enumerable_def by simp
  next
    assume "X \<noteq> {}"
    then obtain x\<^sub>0 where "x\<^sub>0 \<in> X" by auto
    from that semidecidable_iff_domain obtain f where f: "recfn 1 f" "\<forall>x. eval f [x] \<down> \<longleftrightarrow> x \<in> X"
      by auto
    let ?i = "encode f"
    have i: "\<And>x. eval f [x] = eval r_phi [?i, x]"
      using r_phi' f(1) by simp
    with \<open>x\<^sub>0 \<in> X\<close> f(2) have "eval r_phi [?i, x\<^sub>0] \<down>" by simp
    then obtain g where g: "recfn 1 g" "total g" "\<forall>x. eval r_phi [?i, x] \<down> = (\<exists>y. eval g [y] \<down>= x)"
      using f(1) nonempty_domain_enumerable by blast
    with f(2) i have "\<forall>x. x \<in> X = (\<exists>y. eval g [y] \<down>= x)"
      by simp
    then have "\<forall>x. x \<in> X = (\<exists>y. the (eval g [y]) = x)"
      using totalE[OF g(2) g(1)]
      by (metis One_nat_def length_Cons list.size(3) option.collapse option.sel)
    then have "X = {the (eval g [y]) |y. y \<in> UNIV}"
      by auto
    with g(1,2) show ?thesis using recursively_enumerable_def by auto
  qed
qed

text \<open>The next goal is to show that a set is decidable iff. it and its
complement are semidecidable. For this we use the concurrent evaluation
function.\<close>

lemma semidecidable_decidable:
  assumes "semidecidable X" and "semidecidable (- X)"
  shows "decidable X"
proof -
  obtain f where f: "recfn 1 f \<and> (\<forall>x. eval f [x] \<down> \<longleftrightarrow> x \<in> X)"
    using assms(1) semidecidable_iff_domain by auto
  let ?i = "encode f"
  obtain g where g: "recfn 1 g \<and> (\<forall>x. eval g [x] \<down> \<longleftrightarrow> x \<in> (- X))"
    using assms(2) semidecidable_iff_domain by auto
  let ?j = "encode g"
  define d where "d = Cn 1 r_pdec1 [Cn 1 r_parallel [r_const ?j, r_const ?i, Id 1 0]]"
  then have "recfn 1 d"
    by (simp add: d_def)
  have *: "\<And>x. eval r_phi [?i, x] = eval f [x]" "\<And>x. eval r_phi [?j, x] = eval g [x]"
    using f g r_phi' by simp_all
  have "eval d [x] \<down>= 1" if "x \<in> X" for x
  proof -
    have "eval f [x] \<down>"
      using f that by simp
    moreover have "eval g [x] \<up>"
      using g that by blast
    ultimately have "eval r_parallel [?j, ?i, x] \<down>= prod_encode (1, the (eval f [x]))"
      using * r_parallel(3) by simp
    with d_def show ?thesis by simp
  qed
  moreover have "eval d [x] \<down>= 0" if "x \<notin> X" for x
  proof -
    have "eval g [x] \<down>"
      using g that by simp
    moreover have "eval f [x] \<up>"
      using f that by blast
    ultimately have "eval r_parallel [?j, ?i, x] \<down>= prod_encode (0, the (eval g [x]))"
      using * r_parallel(2) by blast
    with d_def show ?thesis by simp
  qed
  ultimately show ?thesis
    using decidable_def \<open>recfn 1 d\<close> by auto
qed

theorem decidable_iff_semidecidable_complement:
  "decidable X \<longleftrightarrow> semidecidable X \<and> semidecidable (- X)"
  using semidecidable_decidable decidable_imp_semidecidable decidable_complement
  by blast


section \<open>Rice's theorem\<close>

definition index_set :: "nat set \<Rightarrow> bool" where
  "index_set I \<equiv> \<forall>i j. i \<in> I \<and> (\<forall>x. eval r_phi [i, x] = eval r_phi [j, x]) \<longrightarrow> j \<in> I"

lemma index_set_closed_in:
  assumes "index_set I" and "i \<in> I" and "\<forall>x. eval r_phi [i, x] = eval r_phi [j, x]"
  shows "j \<in> I"
  using index_set_def assms by simp

lemma index_set_closed_not_in:
  assumes "index_set I" and "i \<notin> I" and "\<forall>x. eval r_phi [i, x] = eval r_phi [j, x]"
  shows "j \<notin> I"
  using index_set_def assms by metis

theorem rice_theorem:
  assumes "index_set I" and "I \<noteq> UNIV" and "I \<noteq> {}"
  shows "\<not> decidable I"
proof
  assume "decidable I"
  then obtain d where d: "recfn 1 d" "\<forall>i. eval d [i] \<down>= (if i \<in> I then 1 else 0)"
    using decidable_def by auto
  obtain j\<^sub>1 j\<^sub>2 where "j\<^sub>1 \<notin> I" and "j\<^sub>2 \<in> I"
    using assms(2,3) by auto
  let ?if = "Cn 2 r_ifz [Cn 2 d [Id 2 0], r_dummy 1 (r_const j\<^sub>2), r_dummy 1 (r_const j\<^sub>1)]"
  define psi where "psi = Cn 2 r_phi [?if, Id 2 1] "
  then have "recfn 2 psi"
    by (simp add: d)
  have "eval ?if [x, y] = Some (if x \<in> I then j\<^sub>1 else j\<^sub>2)" for x y
    by (simp add: d)
  moreover have "eval psi [x, y] = eval (Cn 2 r_phi [?if, Id 2 1]) [x, y]" for x y
    using psi_def by simp
  ultimately have psi: "eval psi [x, y] = eval r_phi [if x \<in> I then j\<^sub>1 else j\<^sub>2, y]" for x y
    by (simp add: d)
  then have in_I: "eval psi [x, y] = eval r_phi [j\<^sub>1, y]" if "x \<in> I" for x y
    by (simp add: that)
  have not_in_I: "eval psi [x, y] = eval r_phi [j\<^sub>2, y]" if "x \<notin> I" for x y
    by (simp add: psi that)
  obtain n where n: "\<forall>x. eval r_phi [n, x] = eval psi [n, x]"
    using kleene_fixed_point_theorem[OF \<open>recfn 2 psi\<close>] by auto
  show False
  proof cases
    assume "n \<in> I"
    then have "\<forall>x. eval r_phi [n, x] = eval r_phi [j\<^sub>1, x]"
      using n in_I by simp
    then have "n \<notin> I"
      using \<open>j\<^sub>1 \<notin> I\<close> index_set_closed_not_in[OF assms(1)] by simp
    with \<open>n \<in> I\<close> show False by simp
  next
    assume "n \<notin> I"
    then have "\<forall>x. eval r_phi [n, x] = eval r_phi [j\<^sub>2, x]"
      using n not_in_I by simp
    then have "n \<in> I"
      using \<open>j\<^sub>2 \<in> I\<close> index_set_closed_in[OF assms(1)] by simp
    with \<open>n \<notin> I\<close> show False by simp
  qed
qed


section \<open>Partial recursive functions as actual functions\label{s:alternative}\<close>

text \<open>A well-formed @{typ recf} describes an algorithm. Usually,
however, partial recursive functions are considered to be partial functions,
that is, right-unique binary relations. This distinction did not matter much
until now, because we were mostly concerned with the \emph{existence} of
partial recursive functions, which is equivalent to the existence of
algorithms. Whenever it did matter, we could use the extensional equivalence
@{term "exteq"}. In Chapter~\ref{c:iirf}, however, we will deal with sets of
functions and sets of sets of functions.

For illustration consider the singleton set containing only the unary zero
function. It could be expressed by @{term "{Z}"}, but this would not contain
@{term[names_short] "Cn 1 (Id 1 0) [Z]"}, which computes the same function.
The alternative representation as @{term "{f. f \<simeq> Z}"} is not a
singleton set. Another alternative would be to identify partial recursive
functions with the equivalence classes of @{term "exteq"}. This would work
for all arities. But since we will only need unary and binary functions, we
can go for the less general but simpler alternative of regarding partial
recursive functions as certain functions of types @{typ "nat \<Rightarrow>
nat option"} and @{typ "nat \<Rightarrow> nat \<Rightarrow> nat option"}.
With this notation we can represent the aforementioned set by @{term
"{\<lambda>_. Some (0::nat)}"} and express that the function @{term "\<lambda>_.
Some (0::nat)"} is total recursive.

In addition terms get shorter, for instance, @{term "eval r_func [i, x]"}
becomes @{term "func i x"}.\<close>


subsection \<open>The definitions\<close>

type_synonym partial1 = "nat \<Rightarrow> nat option"

type_synonym partial2 = "nat \<Rightarrow> nat \<Rightarrow> nat option"

definition total1 :: "partial1 \<Rightarrow> bool" where
  "total1 f \<equiv> \<forall>x. f x \<down>"

definition total2 :: "partial2 \<Rightarrow> bool" where
  "total2 f \<equiv> \<forall>x y. f x y \<down>"

lemma total1I [intro]: "(\<And>x. f x \<down>) \<Longrightarrow> total1 f"
  using total1_def by simp

lemma total2I [intro]: "(\<And>x y. f x y \<down>) \<Longrightarrow> total2 f"
  using total2_def by simp

lemma total1E [dest, simp]: "total1 f \<Longrightarrow> f x \<down>"
  using total1_def by simp

lemma total2E [dest, simp]: "total2 f \<Longrightarrow> f x y \<down>"
  using total2_def by simp

definition P1 :: "partial1 set" ("\<P>") where
  "\<P> \<equiv> {\<lambda>x. eval r [x] |r. recfn 1 r}"

definition P2 :: "partial2 set" ("\<P>\<^sup>2") where
  "\<P>\<^sup>2 \<equiv> {\<lambda>x y. eval r [x, y] |r. recfn 2 r}"

definition R1 :: "partial1 set" ("\<R>") where
  "\<R> \<equiv> {\<lambda>x. eval r [x] |r. recfn 1 r \<and> total r}"

definition R2 :: "partial2 set" ("\<R>\<^sup>2") where
  "\<R>\<^sup>2 \<equiv> {\<lambda>x y. eval r [x, y] |r. recfn 2 r \<and> total r}"

definition Prim1 :: "partial1 set" where
  "Prim1 \<equiv> {\<lambda>x. eval r [x] |r. prim_recfn 1 r}"

definition Prim2 :: "partial2 set" where
  "Prim2 \<equiv> {\<lambda>x y. eval r [x, y] |r. prim_recfn 2 r}"

lemma R1_imp_P1 [simp, elim]: "f \<in> \<R> \<Longrightarrow> f \<in> \<P>"
  using R1_def P1_def by auto

lemma R2_imp_P2 [simp, elim]: "f \<in> \<R>\<^sup>2 \<Longrightarrow> f \<in> \<P>\<^sup>2"
  using R2_def P2_def by auto

lemma Prim1_imp_R1 [simp, elim]: "f \<in> Prim1 \<Longrightarrow> f \<in> \<R>"
  unfolding Prim1_def R1_def by auto

lemma Prim2_imp_R2 [simp, elim]: "f \<in> Prim2 \<Longrightarrow> f \<in> \<R>\<^sup>2"
  unfolding Prim2_def R2_def by auto

lemma P1E [elim]:
  assumes "f \<in> \<P>"
  obtains r where "recfn 1 r" and "\<forall>x. eval r [x] = f x"
  using assms P1_def by force

lemma P2E [elim]:
  assumes "f \<in> \<P>\<^sup>2"
  obtains r where "recfn 2 r" and "\<forall>x y. eval r [x, y] = f x y"
  using assms P2_def by force

lemma P1I [intro]:
  assumes "recfn 1 r" and "(\<lambda>x. eval r [x]) = f"
  shows "f \<in> \<P>"
  using assms P1_def by auto

lemma P2I [intro]:
  assumes "recfn 2 r" and "\<And>x y. eval r [x, y] = f x y"
  shows "f \<in> \<P>\<^sup>2"
proof -
  have "(\<lambda>x y. eval r [x, y]) = f"
    using assms(2) by simp
  then show ?thesis
    using assms(1) P2_def by auto
qed

lemma R1I [intro]:
  assumes "recfn 1 r" and "total r" and "\<And>x. eval r [x] = f x"
  shows "f \<in> \<R>"
  unfolding R1_def
  using CollectI[of "\<lambda>f. \<exists>r. f = (\<lambda>x. eval r [x]) \<and> recfn 1 r \<and> total r" f] assms
  by metis

lemma R1E [elim]:
  assumes "f \<in> \<R>"
  obtains r where "recfn 1 r" and "total r" and "f = (\<lambda>x. eval r [x])"
  using assms R1_def by auto

lemma R2I [intro]:
  assumes "recfn 2 r" and "total r" and "\<And>x y. eval r [x, y] = f x y"
  shows "f \<in> \<R>\<^sup>2"
  unfolding R2_def
  using CollectI[of "\<lambda>f. \<exists>r. f = (\<lambda>x y. eval r [x, y]) \<and> recfn 2 r \<and> total r" f] assms
  by metis

lemma R1_SOME:
  assumes "f \<in> \<R>"
    and "r = (SOME r'. recfn 1 r' \<and>  total r' \<and> f = (\<lambda>x. eval r' [x]))"
      (is "r = (SOME r'. ?P r')")
  shows "recfn 1 r"
    and "\<And>x. eval r [x] \<down>"
    and "\<And>x. f x = eval r [x]"
    and "f = (\<lambda>x. eval r [x])"
proof -
  obtain r' where "?P r'"
    using R1E[OF assms(1)] by auto
  then show "recfn 1 r" "\<And>b. eval r [b] \<down>" "\<And>x. f x = eval r [x]"
    using someI[of ?P r'] assms(2) totalE[of r] by (auto, metis)
  then show "f = (\<lambda>x. eval r [x])" by auto
qed

lemma R2E [elim]:
  assumes "f \<in> \<R>\<^sup>2"
  obtains r where "recfn 2 r" and "total r" and "f = (\<lambda>x\<^sub>1 x\<^sub>2. eval r [x\<^sub>1, x\<^sub>2])"
  using assms R2_def by auto

lemma R1_imp_total1 [simp]: "f \<in> \<R> \<Longrightarrow> total1 f"
  using total1I by fastforce

lemma R2_imp_total2 [simp]: "f \<in> \<R>\<^sup>2 \<Longrightarrow> total2 f"
  using totalE by fastforce

lemma Prim1I [intro]:
  assumes "prim_recfn 1 r" and "\<And>x. f x = eval r [x]"
  shows "f \<in> Prim1"
  using assms Prim1_def by blast

lemma Prim2I [intro]:
  assumes "prim_recfn 2 r" and "\<And>x y. f x y = eval r [x, y]"
  shows "f \<in> Prim2"
  using assms Prim2_def by blast

lemma P1_total_imp_R1 [intro]:
  assumes "f \<in> \<P>" and "total1 f"
  shows "f \<in> \<R>"
  using assms totalI1 by force

lemma P2_total_imp_R2 [intro]:
  assumes "f \<in> \<P>\<^sup>2 " and "total2 f"
  shows "f \<in> \<R>\<^sup>2"
  using assms totalI2 by force


subsection \<open>Some simple properties\<close>

text \<open>In order to show that a @{typ partial1} or @{typ partial2}
function is in @{term "\<P>"}, @{term "\<P>\<^sup>2"}, @{term "\<R>"}, @{term
"\<R>\<^sup>2"}, @{term "Prim1"}, or @{term "Prim2"} we will usually have to
find a suitable @{typ recf}. But for some simple or frequent cases this
section provides shortcuts.\<close>

lemma identity_in_R1: "Some \<in> \<R>"
proof -
  have "\<forall>x. eval (Id 1 0) [x] \<down>= x" by simp
  moreover have "recfn 1 (Id 1 0)" by simp
  moreover have "total (Id 1 0)"
    by (simp add: totalI1)
  ultimately show ?thesis by blast
qed

lemma P2_proj_P1 [simp, elim]:
  assumes "\<psi> \<in> \<P>\<^sup>2"
  shows "\<psi> i \<in> \<P>"
proof -
  from assms obtain u where u: "recfn 2 u" "(\<lambda>x\<^sub>1 x\<^sub>2. eval u [x\<^sub>1, x\<^sub>2]) = \<psi>"
    by auto
  define v where "v \<equiv> Cn 1 u [r_const i, Id 1 0]"
  then have "recfn 1 v" "(\<lambda>x. eval v [x]) = \<psi> i"
    using u by auto
  then show ?thesis by auto
qed

lemma R2_proj_R1 [simp, elim]:
  assumes "\<psi> \<in> \<R>\<^sup>2"
  shows "\<psi> i \<in> \<R>"
proof -
  from assms have "\<psi> \<in> \<P>\<^sup>2" by simp
  then have "\<psi> i \<in> \<P>" by auto
  moreover have "total1 (\<psi> i)"
    using assms by (simp add: total1I)
  ultimately show ?thesis by auto
qed

lemma const_in_Prim1: "(\<lambda>_. Some c) \<in> Prim1"
proof -
  define r where "r = r_const c"
  then have "\<And>x. eval r [x] = Some c" by simp
  moreover have "recfn 1 r" "Mn_free r"
    using r_def by simp_all
  ultimately show ?thesis by auto
qed

lemma concat_P1_P1:
  assumes "f \<in> \<P>" and "g \<in> \<P>"
  shows "(\<lambda>x. if g x \<down> \<and> f (the (g x)) \<down> then Some (the (f (the (g x)))) else None) \<in> \<P>"
    (is "?h \<in> \<P>")
proof -
  obtain rf where rf: "recfn 1 rf" "\<forall>x. eval rf [x] = f x"
    using assms(1) by auto
  obtain rg where rg: "recfn 1 rg" "\<forall>x. eval rg [x] = g x"
    using assms(2) by auto
  let ?rh = "Cn 1 rf [rg]"
  have "recfn 1 ?rh"
    using rf(1) rg(1) by simp
  moreover have "eval ?rh [x] = ?h x" for x
    using rf rg by simp
  ultimately show ?thesis by blast
qed

lemma P1_update_P1:
  assumes "f \<in> \<P>"
  shows "f(x:=z) \<in> \<P>"
proof (cases z)
  case None
  define re where "re \<equiv> Mn 1 (r_constn 1 1)"
  from assms obtain r where r: "recfn 1 r" "(\<lambda>u. eval r [u]) = f"
    by auto
  define r' where "r' = Cn 1 (r_lifz re r) [Cn 1 r_eq [Id 1 0, r_const x], Id 1 0]"
  have "recfn 1 r'"
    using r(1) r'_def re_def by simp
  then have "eval r' [u] = eval (r_lifz re r) [if u = x then 0 else 1, u]" for u
    using r'_def by simp
  with r(1) have "eval r' [u] = (if u = x then None else eval r [u])" for u
    using re_def re_def by simp
  with r(2) have "eval r' [u] = (f(x:=None)) u" for u
    by auto
  then have "(\<lambda>u. eval r' [u]) = f(x:=None)"
    by auto
  with None \<open>recfn 1 r'\<close> show ?thesis by auto
next
  case (Some y)
  from assms obtain r where r: "recfn 1 r" "(\<lambda>u. eval r [u]) = f"
    by auto
  define r' where
    "r' \<equiv> Cn 1 (r_lifz (r_const y) r) [Cn 1 r_eq [Id 1 0, r_const x], Id 1 0]"
  have "recfn 1 r'"
    using r(1) r'_def by simp
  then have "eval r' [u] = eval (r_lifz (r_const y) r) [if u = x then 0 else 1, u]" for u
    using r'_def by simp
  with r(1) have "eval r' [u] = (if u = x then Some y else eval r [u])" for u
    by simp
  with r(2) have "eval r' [u] = (f(x:=Some y)) u" for u
    by auto
  then have "(\<lambda>u. eval r' [u]) = f(x:=Some y)"
    by auto
  with Some \<open>recfn 1 r'\<close> show ?thesis by auto
qed

lemma swap_P2:
  assumes "f \<in> \<P>\<^sup>2"
  shows "(\<lambda>x y. f y x) \<in> \<P>\<^sup>2"
proof -
  obtain r where r: "recfn 2 r" "\<And>x y. eval r [x, y] = f x y"
    using assms by auto
  then have "eval (r_swap r) [x, y] = f y x" for x y
    by simp
  moreover have "recfn 2 (r_swap r)"
    using r_swap_recfn r(1) by simp
  ultimately show ?thesis by auto
qed

lemma swap_R2:
  assumes "f \<in> \<R>\<^sup>2"
  shows "(\<lambda>x y. f y x) \<in> \<R>\<^sup>2"
  using swap_P2[of f] assms
  by (meson P2_total_imp_R2 R2_imp_P2 R2_imp_total2 total2E total2I)

lemma skip_P1:
  assumes "f \<in> \<P>"
  shows "(\<lambda>x. f (x + n)) \<in> \<P>"
proof -
  obtain r where r: "recfn 1 r" "\<And>x. eval r [x] = f x"
    using assms by auto
  let ?s = "Cn 1 r [Cn 1 r_add [Id 1 0, r_const n]]"
  have "recfn 1 ?s"
    using r by simp
  have "eval ?s [x] = eval r [x + n]" for x
    using r by simp
  with r have "eval ?s [x] = f (x + n)" for x
    by simp
  with \<open>recfn 1 ?s\<close> show ?thesis by blast
qed

lemma skip_R1:
  assumes "f \<in> \<R>"
  shows "(\<lambda>x. f (x + n)) \<in> \<R>"
  using assms skip_P1 R1_imp_total1 total1_def by auto


subsection \<open>The Gödel numbering @{term \<phi>}\label{s:goedel_numbering}\<close>

text \<open>While the term \emph{Gödel numbering} is often used generically for
mappings between natural numbers and mathematical concepts, the inductive
inference literature uses it in a more specific sense. There it is equivalent
to the notion of acceptable numbering~\cite{Rogers87}: For every numbering
there is a recursive function mapping the numbering's indices to equivalent
ones of a Gödel numbering.\<close>

definition goedel_numbering :: "partial2 \<Rightarrow> bool" where
  "goedel_numbering \<psi> \<equiv> \<psi> \<in> \<P>\<^sup>2 \<and> (\<forall>\<chi>\<in>\<P>\<^sup>2. \<exists>c\<in>\<R>. \<forall>i. \<chi> i = \<psi> (the (c i)))"

lemma goedel_numbering_P2:
  assumes "goedel_numbering \<psi>"
  shows "\<psi> \<in> \<P>\<^sup>2"
  using goedel_numbering_def assms by simp

lemma goedel_numberingE:
  assumes "goedel_numbering \<psi>" and "\<chi> \<in> \<P>\<^sup>2"
  obtains c where "c \<in> \<R>" and "\<forall>i. \<chi> i = \<psi> (the (c i))"
  using assms goedel_numbering_def by blast

lemma goedel_numbering_universal:
  assumes "goedel_numbering \<psi>" and "f \<in> \<P>"
  shows "\<exists>i. \<psi> i = f"
proof -
  define \<chi> :: partial2 where "\<chi> = (\<lambda>i. f)"
  have "\<chi> \<in> \<P>\<^sup>2"
  proof -
    obtain rf where rf: "recfn 1 rf" "\<And>x. eval rf [x] = f x"
      using assms(2) by auto
    define r where "r = Cn 2 rf [Id 2 1]"
    then have r: "recfn 2 r" "\<And>i x. eval r [i, x] = eval rf [x]"
      using rf(1) by simp_all
    with rf(2) have "\<And>i x. eval r [i, x] = f x" by simp
    with r(1) show ?thesis using \<chi>_def by auto
  qed
  then obtain c where "c \<in> \<R>" and "\<forall>i. \<chi> i = \<psi> (the (c i))"
    using goedel_numbering_def assms(1) by auto
  with \<chi>_def show ?thesis by auto
qed

text \<open>Our standard Gödel numbering is based on @{term r_phi}:\<close>

definition phi :: partial2 ("\<phi>") where
  "\<phi> i x \<equiv> eval r_phi [i, x]"

lemma phi_in_P2: "\<phi> \<in> \<P>\<^sup>2"
  unfolding phi_def using r_phi_recfn by blast

text \<open>Indices of any numbering can be translated into equivalent indices
of @{term phi}, which thus is a Gödel numbering.\<close>

lemma numbering_translation_for_phi:
  assumes "\<psi> \<in> \<P>\<^sup>2"
  shows "\<exists>c\<in>\<R>. \<forall>i. \<psi> i = \<phi> (the (c i))"
proof -
  obtain psi where psi: "recfn 2 psi" "\<And>i x. eval psi [i, x] = \<psi> i x"
    using assms by auto
  with numbering_translation obtain b where
    "recfn 1 b" "total b" "\<forall>i x. eval psi [i, x] = eval r_phi [the (eval b [i]), x]"
    by blast
  moreover from this obtain c where c: "c \<in> \<R>" "\<forall>i. c i = eval b [i]"
    by fast
  ultimately have "\<psi> i x = \<phi> (the (c i)) x" for i x
    using phi_def psi(2) by presburger
  then have "\<psi> i = \<phi> (the (c i))" for i
    by auto
  then show ?thesis using c(1) by blast
qed

corollary goedel_numbering_phi: "goedel_numbering \<phi>"
  unfolding goedel_numbering_def using numbering_translation_for_phi phi_in_P2 by simp

corollary phi_universal:
  assumes "f \<in> \<P>"
  obtains i where "\<phi> i = f"
  using goedel_numbering_universal[OF goedel_numbering_phi assms] by auto


subsection \<open>Fixed-point theorems\<close>

text \<open>The fixed-point theorems look somewhat cleaner in the new
notation. We will only need the following ones in the next chapter.\<close>

theorem kleene_fixed_point:
  fixes k :: nat
  assumes "\<psi> \<in> \<P>\<^sup>2"
  obtains i where "i \<ge> k" and "\<phi> i = \<psi> i"
proof -
  obtain r_psi where r_psi: "recfn 2 r_psi" "\<And>i x. eval r_psi [i, x] = \<psi> i x"
    using assms by auto
  then obtain i where i: "i \<ge> k" "\<forall>x. eval r_phi [i, x] = eval r_psi [i, x]"
    using kleene_fixed_point_theorem by blast
  then have "\<forall>x. \<phi> i x = \<psi> i x"
    using phi_def r_psi by simp
  then show ?thesis using i that by blast
qed

theorem smullyan_double_fixed_point:
  assumes "g \<in> \<R>\<^sup>2" and "h \<in> \<R>\<^sup>2"
  obtains m n where "\<phi> m = \<phi> (the (g m n))" and "\<phi> n = \<phi> (the (h m n))"
proof -
  obtain rg where rg: "recfn 2 rg" "total rg" "g = (\<lambda>x y. eval rg [x, y])"
    using R2E[OF assms(1)] by auto
  moreover obtain rh where rh: "recfn 2 rh" "total rh" "h = (\<lambda>x y. eval rh [x, y])"
    using R2E[OF assms(2)] by auto
  ultimately obtain m n where
    "\<forall>x. eval r_phi [m, x] = eval r_phi [the (eval rg [m, n]), x]"
    "\<forall>x. eval r_phi [n, x] = eval r_phi [the (eval rh [m, n]), x]"
    using smullyan_double_fixed_point_theorem[of rg rh] by blast
  then have "\<phi> m = \<phi> (the (g m n))" and "\<phi> n = \<phi> (the (h m n))"
    using phi_def rg rh by auto
  then show ?thesis using that by simp
qed

end