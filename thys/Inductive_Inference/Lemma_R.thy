section \<open>Lemma R\label{s:lemma_r}\<close>

theory Lemma_R
  imports Inductive_Inference_Basics
begin

text \<open>A common technique for constructing a class that cannot be
learned is diagonalization against all strategies (see, for instance,
Section~\ref{s:lim_bc}). Similarly, the typical way of proving that a class
cannot be learned is by assuming there is a strategy and deriving a
contradiction. Both techniques are easier to carry out if one has to consider
only \emph{total} recursive strategies. This is not possible in general,
since after all the definitions of the inference types admit strictly partial
strategies. However, for many inference types one can show that for every
strategy there is a total strategy with at least the same ``learning power''.
Results to that effect are called Lemma~R.

Lemma~R comes in different strengths depending on how general the
construction of the total recursive strategy is. CONS is the only inference
type considered here for which not even a weak form of Lemma~R holds.\<close>


subsection \<open>Strong Lemma R for LIM, FIN, and BC\<close>

text \<open>In its strong form Lemma~R says that for any strategy $S$, there
is a total strategy $T$ that learns all classes $S$ learns regardless of
hypothesis space. The strategy $T$ can be derived from $S$ by a delayed
simulation of $S$. More precisely, for input $f^n$, $T$ simulates $S$ for
prefixes $f^0, f^1, \ldots, f^n$ for at most $n$ steps. If $S$ halts on none
of the prefixes, $T$ outputs an arbitrary hypothesis. Otherwise let $k \leq
n$ be maximal such that $S$ halts on $f^k$ in at most $n$ steps. Then $T$
outputs $S(f^k)$. \<close>

text \<open>We reformulate some lemmas for @{term r_result1} to make it easier
to use them with @{term "\<phi>"}.\<close>

lemma r_result1_converg_phi:
  assumes "\<phi> i x \<down>= v"
  shows "\<exists>t.
    (\<forall>t'\<ge>t. eval r_result1 [t', i, x] \<down>= Suc v) \<and> 
    (\<forall>t'<t. eval r_result1 [t', i, x] \<down>= 0)"
  using assms r_result1_converg' phi_def by simp_all

lemma r_result1_bivalent':
  assumes "eval r_phi [i, x] \<down>= v"
  shows "eval r_result1 [t, i, x] \<down>= Suc v \<or> eval r_result1 [t, i, x] \<down>= 0"
  using assms r_result1 r_result_bivalent' r_phi'' by simp

lemma r_result1_bivalent_phi:
  assumes "\<phi> i x \<down>= v"
  shows "eval r_result1 [t, i, x] \<down>= Suc v \<or> eval r_result1 [t, i, x] \<down>= 0"
  using assms r_result1_bivalent' phi_def by simp_all

lemma r_result1_diverg_phi:
  assumes "\<phi> i x \<up>"
  shows "eval r_result1 [t, i, x] \<down>= 0"
  using assms phi_def r_result1_diverg' by simp

lemma r_result1_some_phi:
  assumes "eval r_result1 [t, i, x] \<down>= Suc v"
  shows "\<phi> i x \<down>= v"
  using assms phi_def r_result1_Some' by simp

lemma r_result1_saturating':
  assumes "eval r_result1 [t, i, x] \<down>= Suc v"
  shows "eval r_result1 [t + d, i, x] \<down>= Suc v"
  using assms r_result1 r_result_saturating r_phi'' by simp

lemma r_result1_saturating_the:
  assumes "the (eval r_result1 [t, i, x]) > 0" and "t' \<ge> t"
  shows "the (eval r_result1 [t', i, x]) > 0"
proof -
  from assms(1) obtain v where "eval r_result1 [t, i, x] \<down>= Suc v"
    using r_result1_bivalent_phi r_result1_diverg_phi
    by (metis inc_induct le_0_eq not_less_zero option.discI option.expand option.sel)
  with assms have "eval r_result1 [t', i, x] \<down>= Suc v"
    using r_result1_saturating' le_Suc_ex by blast
  then show ?thesis by simp
qed

lemma Greatest_bounded_Suc:
  fixes P :: "nat \<Rightarrow> nat"
  shows "(if P n > 0 then Suc n
          else if \<exists>j<n. P j > 0 then Suc (GREATEST j. j < n \<and> P j > 0) else 0) =
    (if \<exists>j<Suc n. P j > 0 then Suc (GREATEST j. j < Suc n \<and> P j > 0) else 0)"
      (is "?lhs = ?rhs")
proof (cases "\<exists>j<Suc n. P j > 0")
  case 1: True
  show ?thesis
  proof (cases "P n > 0")
    case True
    then have "(GREATEST j. j < Suc n \<and> P j > 0) = n"
      using Greatest_equality[of "\<lambda>j. j < Suc n \<and> P j > 0"] by simp
    moreover have "?rhs = Suc (GREATEST j. j < Suc n \<and> P j > 0)"
      using 1 by simp
    ultimately have "?rhs = Suc n" by simp
    then show ?thesis using True by simp
  next
    case False
    then have "?lhs = Suc (GREATEST j. j < n \<and> P j > 0)"
      using 1 by (metis less_SucE)
    moreover have "?rhs = Suc (GREATEST j. j < Suc n \<and> P j > 0)"
      using 1 by simp
    moreover have "(GREATEST j. j < n \<and> P j > 0) =
        (GREATEST j. j < Suc n \<and> P j > 0)"
      using 1 False by (metis less_SucI less_Suc_eq)
    ultimately show ?thesis by simp
  qed
next
  case False
  then show ?thesis by auto
qed

text \<open>For $n$, $i$, $x$, the next function simulates $\varphi_i$ on all
non-empty prefixes of at most length $n$ of the list $x$ for at most $n$
steps. It returns the length of the longest such prefix for which $\varphi_i$
halts, or zero if $\varphi_i$ does not halt for any prefix.\<close>

definition "r_delay_aux \<equiv>
  Pr 2 (r_constn 1 0)
    (Cn 4 r_ifz
      [Cn 4 r_result1
        [Cn 4 r_length [Id 4 3], Id 4 2,
         Cn 4 r_take [Cn 4 S [Id 4 0], Id 4 3]],
       Id 4 1, Cn 4 S [Id 4 0]])"

lemma r_delay_aux_prim: "prim_recfn 3 r_delay_aux"
  unfolding r_delay_aux_def by simp_all

lemma r_delay_aux_total: "total r_delay_aux"
  using  prim_recfn_total[OF r_delay_aux_prim] .

lemma r_delay_aux:
  assumes "n \<le> e_length x"
  shows "eval r_delay_aux [n, i, x] \<down>=
   (if \<exists>j<n. the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0
    then Suc (GREATEST j.
                 j < n \<and>
                 the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0)
    else 0)"
proof -
  define z where "z \<equiv>
    Cn 4 r_result1
      [Cn 4 r_length [Id 4 3], Id 4 2, Cn 4 r_take [Cn 4 S [Id 4 0], Id 4 3]]"
  then have z_recfn: "recfn 4 z" by simp
  have z: "eval z [j, r, i, x] = eval r_result1 [e_length x, i, e_take (Suc j) x]"
      if "j < e_length x" for j r i x
    unfolding z_def using that by simp

  define g where "g \<equiv> Cn 4 r_ifz [z, Id 4 1, Cn 4 S [Id 4 0]]"
  then have g: "eval g [j, r, i, x] \<down>=
      (if the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0 then Suc j else r)"
      if "j < e_length x" for j r i x
    using that z prim_recfn_total z_recfn by simp

  show ?thesis
    using assms
  proof (induction n)
    case 0
    moreover have "eval r_delay_aux [0, i, x] \<down>= 0"
      using eval_Pr_0 r_delay_aux_def r_delay_aux_prim r_constn
      by (simp add: r_delay_aux_def)
    ultimately show ?case by simp
  next
    case (Suc n)
    let ?P = "\<lambda>j. the (eval r_result1 [e_length x, i, e_take (Suc j) x])"
    have "eval r_delay_aux [n, i, x] \<down>"
      using Suc by simp
    moreover have "eval r_delay_aux [Suc n, i, x] =
        eval (Pr 2 (r_constn 1 0) g) [Suc n, i, x]"
      unfolding r_delay_aux_def g_def z_def by simp
    ultimately have "eval r_delay_aux [Suc n, i, x] =
        eval g [n, the (eval r_delay_aux [n, i, x]), i, x]"
      using r_delay_aux_prim Suc eval_Pr_converg_Suc
      by (simp add: r_delay_aux_def g_def z_def numeral_3_eq_3)
    then have "eval r_delay_aux [Suc n, i, x] \<down>=
        (if ?P n > 0 then Suc n
         else if \<exists>j<n. ?P j > 0 then Suc (GREATEST j. j < n \<and> ?P j > 0) else 0)"
      using g Suc by simp
    then have "eval r_delay_aux [Suc n, i, x] \<down>=
        (if \<exists>j<Suc n. ?P j > 0 then Suc (GREATEST j. j < Suc n \<and> ?P j > 0) else 0)"
      using Greatest_bounded_Suc[where ?P="?P"] by simp
    then show ?case by simp
  qed
qed

text \<open>The next function simulates $\varphi_i$ on all non-empty prefixes
of a list $x$ of length $n$ for at most $n$ steps and outputs the length of
the longest prefix for which $\varphi_i$ halts, or zero if $\varphi_i$ does
not halt for any such prefix.\<close>

definition "r_delay \<equiv> Cn 2 r_delay_aux [Cn 2 r_length [Id 2 1], Id 2 0, Id 2 1]"

lemma r_delay_recfn [simp]: "recfn 2 r_delay"
  unfolding r_delay_def by (simp add: r_delay_aux_prim)

lemma r_delay:
  "eval r_delay [i, x] \<down>=
    (if \<exists>j<e_length x. the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0
     then Suc (GREATEST j.
        j < e_length x \<and> the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0)
     else 0)"
  unfolding r_delay_def using r_delay_aux r_delay_aux_prim by simp

definition "delay i x \<equiv> Some
 (if \<exists>j<e_length x. the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0
  then Suc (GREATEST j.
    j < e_length x \<and> the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0)
  else 0)"

lemma delay_in_R2: "delay \<in> \<R>\<^sup>2"
  using r_delay totalI2 R2I delay_def r_delay_recfn
  by (metis (no_types, lifting) numeral_2_eq_2 option.simps(3))

lemma delay_le_length: "the (delay i x) \<le> e_length x"
proof (cases "\<exists>j<e_length x. the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0")
  case True
  let ?P = "\<lambda>j. j < e_length x \<and> the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0"
  from True have "\<exists>j. ?P j" by simp
  moreover have "\<And>y. ?P y \<Longrightarrow> y \<le> e_length x" by simp
  ultimately have "?P (Greatest ?P)"
    using GreatestI_ex_nat[where ?P="?P"] by blast
  then have "Greatest ?P < e_length x" by simp
  moreover have "delay i x \<down>= Suc (Greatest ?P)"
    using delay_def True by simp
  ultimately show ?thesis by auto
next
  case False
  then show ?thesis using delay_def by auto
qed

lemma e_take_delay_init:
  assumes "f \<in> \<R>" and "the (delay i (f \<triangleright> n)) > 0"
  shows "e_take (the (delay i (f \<triangleright> n))) (f \<triangleright> n) = f \<triangleright> (the (delay i (f \<triangleright> n)) - 1)"
  using assms e_take_init[of f _ n] length_init[of f n] delay_le_length[of i "f \<triangleright> n"]
  by (metis One_nat_def Suc_le_lessD Suc_pred)

lemma delay_gr0_converg:
  assumes "the (delay i x) > 0"
  shows "\<phi> i (e_take (the (delay i x)) x) \<down>"
proof -
  let ?P = "\<lambda>j. j < e_length x \<and> the (eval r_result1 [e_length x, i, e_take (Suc j) x]) > 0"
  have "\<exists>j. ?P j"
  proof (rule ccontr)
    assume "\<not> (\<exists>j. ?P j)"
    then have "delay i x \<down>= 0"
      using delay_def by simp
    with assms show False by simp
  qed
  then have d: "the (delay i x) = Suc (Greatest ?P)"
    using delay_def by simp
  moreover have "\<And>y. ?P y \<Longrightarrow> y \<le> e_length x" by simp
  ultimately have "?P (Greatest ?P)"
    using \<open>\<exists>j. ?P j\<close> GreatestI_ex_nat[where ?P="?P"] by blast
  then have "the (eval r_result1 [e_length x, i, e_take (Suc (Greatest ?P)) x]) > 0"
    by simp
  then have "the (eval r_result1 [e_length x, i, e_take (the (delay i x)) x]) > 0"
    using d by simp
  then show ?thesis using r_result1_diverg_phi by fastforce
qed

lemma delay_unbounded:
  fixes n :: nat
  assumes "f \<in> \<R>" and "\<forall>n. \<phi> i (f \<triangleright> n) \<down>"
  shows "\<exists>m. the (delay i (f \<triangleright> m)) > n"
proof -
  from assms have "\<exists>t. the (eval r_result1 [t, i, f \<triangleright> n]) > 0"
    using r_result1_converg_phi
    by (metis le_refl option.exhaust_sel option.sel zero_less_Suc)
  then obtain t where t: "the (eval r_result1 [t, i, f \<triangleright> n]) > 0"
    by auto
  let ?m = "max n t"
  have "Suc ?m \<ge> t" by simp
  have m: "the (eval r_result1 [Suc ?m, i, f \<triangleright> n]) > 0"
  proof -
    let ?w = "eval r_result1 [t, i, f \<triangleright> n]"
    obtain v where v: "?w \<down>= Suc v"
      using t assms(2) r_result1_bivalent_phi by fastforce
    have "eval r_result1 [Suc ?m, i, f \<triangleright> n] = ?w"
      using v t r_result1_saturating' \<open>Suc ?m \<ge> t\<close> le_Suc_ex by fastforce
    then show ?thesis using t by simp
  qed
  let ?x = "f \<triangleright> ?m"
  have "the (delay i ?x) > n"
  proof -
    let ?P = "\<lambda>j. j < e_length ?x \<and> the (eval r_result1 [e_length ?x, i, e_take (Suc j) ?x]) > 0"
    have "e_length ?x = Suc ?m" by simp
    moreover have "e_take (Suc n) ?x = f \<triangleright> n"
      using assms(1) e_take_init by auto
    ultimately have "?P n"
      using m by simp
    have "\<And>y. ?P y \<Longrightarrow> y \<le> e_length ?x" by simp
    with \<open>?P n\<close> have "n \<le> (Greatest ?P)"
      using Greatest_le_nat[of ?P n "e_length ?x"] by simp
    moreover have "the (delay i ?x) = Suc (Greatest ?P)"
      using delay_def \<open>?P n\<close> by auto
    ultimately show ?thesis by simp
  qed
  then show ?thesis by auto
qed

lemma delay_monotone:
  assumes "f \<in> \<R>" and "n\<^sub>1 \<le> n\<^sub>2"
  shows "the (delay i (f \<triangleright> n\<^sub>1)) \<le> the (delay i (f \<triangleright> n\<^sub>2))"
    (is "the (delay i ?x1) \<le> the (delay i ?x2)")
proof (cases "the (delay i (f \<triangleright> n\<^sub>1)) = 0")
  case True
  then show ?thesis by simp
next
  case False
  let ?P1 = "\<lambda>j. j < e_length ?x1 \<and> the (eval r_result1 [e_length ?x1, i, e_take (Suc j) ?x1]) > 0"
  let ?P2 = "\<lambda>j. j < e_length ?x2 \<and> the (eval r_result1 [e_length ?x2, i, e_take (Suc j) ?x2]) > 0"
  from False have d1: "the (delay i ?x1) = Suc (Greatest ?P1)" "\<exists>j. ?P1 j"
    using delay_def option.collapse by fastforce+
  moreover have "\<And>y. ?P1 y \<Longrightarrow> y \<le> e_length ?x1" by simp
  ultimately have *: "?P1 (Greatest ?P1)" using GreatestI_ex_nat[of ?P1] by blast
  let ?j = "Greatest ?P1"
  from * have "?j < e_length ?x1" by auto
  then have 1: "e_take (Suc ?j) ?x1 = e_take (Suc ?j) ?x2"
    using assms e_take_init by auto
  from * have 2: "?j < e_length ?x2" using assms(2) by auto
  with 1 * have "the (eval r_result1 [e_length ?x1, i, e_take (Suc ?j) ?x2]) > 0"
    by simp
  moreover have "e_length ?x1 \<le> e_length ?x2"
    using assms(2) by auto
  ultimately have "the (eval r_result1 [e_length ?x2, i, e_take (Suc ?j) ?x2]) > 0"
    using r_result1_saturating_the by simp
  with 2 have "?P2 ?j" by simp
  then have d2: "the (delay i ?x2) = Suc (Greatest ?P2)"
    using delay_def by auto
  have "\<And>y. ?P2 y \<Longrightarrow> y \<le> e_length ?x2" by simp
  with \<open>?P2 ?j\<close> have "?j \<le> (Greatest ?P2)" using Greatest_le_nat[of ?P2] by blast
  with d1 d2 show ?thesis by simp
qed

lemma delay_unbounded_monotone:
  fixes n :: nat
  assumes "f \<in> \<R>" and "\<forall>n. \<phi> i (f \<triangleright> n) \<down>"
  shows "\<exists>m\<^sub>0. \<forall>m\<ge>m\<^sub>0. the (delay i (f \<triangleright> m)) > n"
proof -
  from assms delay_unbounded obtain m\<^sub>0 where "the (delay i (f \<triangleright> m\<^sub>0)) > n"
    by blast
  then have "\<forall>m\<ge>m\<^sub>0. the (delay i (f \<triangleright> m)) > n"
    using assms(1) delay_monotone order.strict_trans2 by blast
  then show ?thesis by auto
qed

text \<open>Now we can define a function that simulates an arbitrary strategy
$\varphi_i$ in a delayed way. The parameter $d$ is the default hypothesis for
when $\varphi_i$ does not halt within the time bound for any prefix.\<close>

definition r_totalizer :: "nat \<Rightarrow> recf" where
  "r_totalizer d \<equiv>
     Cn 2
      (r_lifz
        (r_constn 1 d)
        (Cn 2 r_phi
          [Id 2 0, Cn 2 r_take [Cn 2 r_delay [Id 2 0, Id 2 1], Id 2 1]]))
      [Cn 2 r_delay [Id 2 0, Id 2 1], Id 2 0, Id 2 1]"

lemma r_totalizer_recfn: "recfn 2 (r_totalizer d)"
  unfolding r_totalizer_def by simp

lemma r_totalizer:
  "eval (r_totalizer d) [i, x] =
    (if the (delay i x) = 0 then Some d else \<phi> i (e_take (the (delay i x)) x))"
proof -
  let ?i = "Cn 2 r_delay [Id 2 0, Id 2 1]"
  have "eval ?i [i, x] = eval r_delay [i, x]" for i x
    using r_delay_recfn by simp
  then have i: "eval ?i [i, x] = delay i x" for i x
    using r_delay by (simp add: delay_def)
  let ?t = "r_constn 1 d"
  have t: "eval ?t [i, x] \<down>= d" for i x by simp
  let ?e1 = "Cn 2 r_take [?i, Id 2 1]"
  let ?e = "Cn 2 r_phi [Id 2 0, ?e1]"
  have "eval ?e1 [i, x] = eval r_take [the (delay i x), x]" for i x
    using r_delay i delay_def by simp
  then have "eval ?e1 [i, x] \<down>= e_take (the (delay i x)) x" for i x
    using delay_le_length by simp
  then have e: "eval ?e [i, x] = \<phi> i (e_take (the (delay i x)) x)"
    using phi_def by simp
  let ?z = "r_lifz ?t ?e"
  have recfn_te: "recfn 2 ?t" "recfn 2 ?e"
    by simp_all
  then have "eval (r_totalizer d) [i, x] = eval (r_lifz ?t ?e) [the (delay i x), i, x]"
      for i x
    unfolding r_totalizer_def using i r_totalizer_recfn delay_def by simp
  then have "eval (r_totalizer d) [i, x] =
      (if the (delay i x) = 0 then eval ?t [i, x] else eval ?e [i, x])"
      for i x
    using recfn_te by simp
  then show ?thesis using t e by simp
qed

lemma r_totalizer_total: "total (r_totalizer d)"
proof (rule totalI2)
  show "recfn 2 (r_totalizer d)" using r_totalizer_recfn by simp
  show "\<And>x y. eval (r_totalizer d) [x, y] \<down>"
    using r_totalizer delay_gr0_converg by simp
qed

definition totalizer :: "nat \<Rightarrow> partial2" where
  "totalizer d i x \<equiv>
     if the (delay i x) = 0 then Some d else \<phi> i (e_take (the (delay i x)) x)"

lemma totalizer_init:
  assumes "f \<in> \<R>"
  shows "totalizer d i (f \<triangleright> n) =
    (if the (delay i (f \<triangleright> n)) = 0 then Some d
     else \<phi> i (f \<triangleright> (the (delay i (f \<triangleright> n)) - 1)))"
  using assms e_take_delay_init by (simp add: totalizer_def)

lemma totalizer_in_R2: "totalizer d \<in> \<R>\<^sup>2"
  using totalizer_def r_totalizer r_totalizer_total R2I r_totalizer_recfn
  by metis

text \<open>For LIM, @{term totalizer} works with every default hypothesis
$d$.\<close>

lemma lemma_R_for_Lim:
  assumes "learn_lim \<psi> U (\<phi> i)"
  shows "learn_lim \<psi> U (totalizer d i)"
proof (rule learn_limI)
  show env: "environment \<psi> U (totalizer d i)"
    using assms learn_limE(1) totalizer_in_R2 by auto
  show "\<exists>j. \<psi> j = f \<and> (\<forall>\<^sup>\<infinity>n. totalizer d i (f \<triangleright> n) \<down>= j)" if "f \<in> U" for f
  proof -
    have "f \<in> \<R>"
      using assms env that by auto
    from assms learn_limE obtain j n\<^sub>0 where
      j: "\<psi> j = f" and
      n0: "\<forall>n\<ge>n\<^sub>0. (\<phi> i) (f \<triangleright> n) \<down>= j"
      using \<open>f \<in> U\<close> by metis
    obtain m\<^sub>0 where m0: "\<forall>m\<ge>m\<^sub>0. the (delay i (f \<triangleright> m)) > n\<^sub>0"
      using delay_unbounded_monotone \<open>f \<in> \<R>\<close> \<open>f \<in> U\<close> assms learn_limE(1)
      by blast
    then have "\<forall>m\<ge>m\<^sub>0. totalizer d i (f \<triangleright> m) = \<phi> i (e_take (the (delay i (f \<triangleright> m))) (f \<triangleright> m))"
      using totalizer_def by auto
    then have "\<forall>m\<ge>m\<^sub>0. totalizer d i (f \<triangleright> m) = \<phi> i (f \<triangleright> (the (delay i (f \<triangleright> m)) - 1))"
      using e_take_delay_init m0 \<open>f \<in> \<R>\<close> by auto
    with m0 n0 have "\<forall>m\<ge>m\<^sub>0. totalizer d i (f \<triangleright> m) \<down>= j"
      by auto
    with j show ?thesis by auto
  qed
qed

text \<open>The effective version of Lemma~R for LIM states that there is a
total recursive function computing Gödel numbers of total strategies
from those of arbitrary strategies.\<close>

lemma lemma_R_for_Lim_effective:
  "\<exists>g\<in>\<R>. \<forall>i.
     \<phi> (the (g i)) \<in> \<R> \<and>
     (\<forall>U \<psi>. learn_lim \<psi> U (\<phi> i) \<longrightarrow> learn_lim \<psi> U (\<phi> (the (g i))))"
proof -
  have "totalizer 0 \<in> \<P>\<^sup>2" using totalizer_in_R2 by auto
  then obtain g where g: "g \<in> \<R>" "\<forall>i. (totalizer 0) i = \<phi> (the (g i))"
    using numbering_translation_for_phi by blast
  with totalizer_in_R2 have "\<forall>i. \<phi> (the (g i)) \<in> \<R>"
    by (metis R2_proj_R1)
  moreover from g(2) lemma_R_for_Lim[where ?d=0] have
    "\<forall>i U \<psi>. learn_lim \<psi> U (\<phi> i) \<longrightarrow> learn_lim \<psi> U (\<phi> (the (g i)))"
    by simp
  ultimately show ?thesis using g(1) by blast
qed

text \<open>In order for us to use the previous lemma, we need a function
that performs the actual computation:\<close>

definition "r_limr \<equiv>
 SOME g.
   recfn 1 g \<and>
   total g \<and>
   (\<forall>i. \<phi> (the (eval g [i])) \<in> \<R> \<and>
      (\<forall>U \<psi>. learn_lim \<psi> U (\<phi> i) \<longrightarrow> learn_lim \<psi> U (\<phi> (the (eval g [i])))))"

lemma r_limr_recfn: "recfn 1 r_limr"
  and r_limr_total: "total r_limr"
  and r_limr:
    "\<phi> (the (eval r_limr [i])) \<in> \<R>"
    "learn_lim \<psi> U (\<phi> i) \<Longrightarrow> learn_lim \<psi> U (\<phi> (the (eval r_limr [i])))"
proof -
  let ?P = "\<lambda>g.
    g \<in> \<R> \<and>
    (\<forall>i. \<phi> (the (g i)) \<in> \<R> \<and> (\<forall>U \<psi>. learn_lim \<psi> U (\<phi> i) \<longrightarrow> learn_lim \<psi> U (\<phi> (the (g i)))))"
  let ?Q = "\<lambda>g.
    recfn 1 g \<and>
    total g \<and>
    (\<forall>i. \<phi> (the (eval g [i])) \<in> \<R> \<and> 
       (\<forall>U \<psi>. learn_lim \<psi> U (\<phi> i) \<longrightarrow> learn_lim \<psi> U (\<phi> (the (eval g [i])))))"
  have "\<exists>g. ?P g" using lemma_R_for_Lim_effective by auto
  then obtain g where "?P g" by auto
  then obtain g' where g': "recfn 1 g'" "total g'" "\<forall>i. eval g' [i] = g i"
    by blast
  with \<open>?P g\<close> have "?Q g'" by simp
  with r_limr_def someI_ex[of ?Q] show
    "recfn 1 r_limr"
    "total r_limr"
    "\<phi> (the (eval r_limr [i])) \<in> \<R>"
    "learn_lim \<psi> U (\<phi> i) \<Longrightarrow> learn_lim \<psi> U (\<phi> (the (eval r_limr [i])))"
    by auto
qed

text \<open>For BC, too, @{term totalizer} works with every default
hypothesis $d$.\<close>

lemma lemma_R_for_BC:
  assumes "learn_bc \<psi> U (\<phi> i)"
  shows "learn_bc \<psi> U (totalizer d i)"
proof (rule learn_bcI)
  show env: "environment \<psi> U (totalizer d i)"
    using assms learn_bcE(1) totalizer_in_R2 by auto
  show "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. \<psi> (the (totalizer d i (f \<triangleright> n))) = f" if "f \<in> U" for f
  proof -
    have "f \<in> \<R>"
      using assms env that by auto
    obtain n\<^sub>0 where n0: "\<forall>n\<ge>n\<^sub>0. \<psi> (the ((\<phi> i) (f \<triangleright> n))) = f"
      using assms learn_bcE \<open>f \<in> U\<close> by metis
    obtain m\<^sub>0 where m0: "\<forall>m\<ge>m\<^sub>0. the (delay i (f \<triangleright> m)) > n\<^sub>0"
      using delay_unbounded_monotone \<open>f \<in> \<R>\<close> \<open>f \<in> U\<close> assms learn_bcE(1)
      by blast
    then have "\<forall>m\<ge>m\<^sub>0. totalizer d i (f \<triangleright> m) = \<phi> i (e_take (the (delay i (f \<triangleright> m))) (f \<triangleright> m))"
      using totalizer_def by auto
    then have "\<forall>m\<ge>m\<^sub>0. totalizer d i (f \<triangleright> m) = \<phi> i (f \<triangleright> (the (delay i (f \<triangleright> m)) - 1))"
      using e_take_delay_init m0 \<open>f \<in> \<R>\<close> by auto
    with m0 n0 have "\<forall>m\<ge>m\<^sub>0. \<psi> (the (totalizer d i (f \<triangleright> m))) = f"
      by auto
    then show ?thesis by auto
  qed
qed

corollary lemma_R_for_BC_simple:
  assumes "learn_bc \<psi> U s"
  shows "\<exists>s'\<in>\<R>. learn_bc \<psi> U s'"
  using assms lemma_R_for_BC totalizer_in_R2 learn_bcE
  by (metis R2_proj_R1 learn_bcE(1) phi_universal)


text \<open>For FIN the default hypothesis of @{term totalizer} must be
zero, signalling ``don't know yet''.\<close>

lemma lemma_R_for_FIN:
  assumes "learn_fin \<psi> U (\<phi> i)"
  shows "learn_fin \<psi> U (totalizer 0 i)"
proof (rule learn_finI)
  show env: "environment \<psi> U (totalizer 0 i)"
    using assms learn_finE(1) totalizer_in_R2 by auto
  show "\<exists>j n\<^sub>0. \<psi> j = f \<and>
           (\<forall>n<n\<^sub>0. totalizer 0 i (f \<triangleright> n) \<down>= 0) \<and>
           (\<forall>n\<ge>n\<^sub>0. totalizer 0 i (f \<triangleright> n) \<down>= Suc j)"
      if "f \<in> U" for f
  proof -
    have "f \<in> \<R>"
      using assms env that by auto
    from assms learn_finE[of \<psi> U "\<phi> i"] obtain j where
      j: "\<psi> j = f" and
      ex_n0: "\<exists>n\<^sub>0. (\<forall>n<n\<^sub>0. (\<phi> i) (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. (\<phi> i) (f \<triangleright> n) \<down>= Suc j)"
      using \<open>f \<in> U\<close> by blast
    let ?Q = "\<lambda>n\<^sub>0. (\<forall>n<n\<^sub>0. (\<phi> i) (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. (\<phi> i) (f \<triangleright> n) \<down>= Suc j)"
    define n\<^sub>0 where "n\<^sub>0 = Least ?Q"
    with ex_n0 have n0: "?Q n\<^sub>0" "\<forall>n<n\<^sub>0. \<not> ?Q n"
      using LeastI_ex[of ?Q] not_less_Least[of _ ?Q] by blast+
    define m\<^sub>0 where "m\<^sub>0 = (LEAST m\<^sub>0. \<forall>m\<ge>m\<^sub>0. the (delay i (f \<triangleright> m)) > n\<^sub>0)"
      (is "m\<^sub>0 = Least ?P")
    moreover have "\<exists>m\<^sub>0. \<forall>m\<ge>m\<^sub>0. the (delay i (f \<triangleright> m)) > n\<^sub>0"
      using delay_unbounded_monotone \<open>f\<in>\<R>\<close> \<open>f \<in> U\<close> assms learn_finE(1)
      by simp
    ultimately have m0: "?P m\<^sub>0" "\<forall>m<m\<^sub>0. \<not> ?P m"
      using LeastI_ex[of ?P] not_less_Least[of _ ?P] by blast+
    then have "\<forall>m\<ge>m\<^sub>0. totalizer 0 i (f \<triangleright> m) = \<phi> i (e_take (the (delay i (f \<triangleright> m))) (f \<triangleright> m))"
      using totalizer_def by auto
    then have "\<forall>m\<ge>m\<^sub>0. totalizer 0 i (f \<triangleright> m) = \<phi> i (f \<triangleright> (the (delay i (f \<triangleright> m)) - 1))"
      using e_take_delay_init m0 \<open>f\<in>\<R>\<close> by auto
    with m0 n0 have "\<forall>m\<ge>m\<^sub>0. totalizer 0 i (f \<triangleright> m) \<down>= Suc j"
      by auto
    moreover have "totalizer 0 i (f \<triangleright> m) \<down>= 0" if "m < m\<^sub>0" for m
    proof (cases "the (delay i (f \<triangleright> m)) = 0")
      case True
      then show ?thesis by (simp add: totalizer_def)
    next
      case False
      then have "the (delay i (f \<triangleright> m)) \<le> n\<^sub>0"
        using m0 that \<open>f \<in> \<R>\<close> delay_monotone by (meson leI order.strict_trans2)
      then show ?thesis
        using \<open>f \<in> \<R>\<close> n0(1) totalizer_init by (simp add: Suc_le_lessD)
    qed
    ultimately show ?thesis using j by auto
  qed
qed


subsection \<open>Weaker Lemma R for CP and TOTAL\<close>

text \<open>For TOTAL the default hypothesis used by @{term totalizer}
depends on the hypothesis space, because it must refer to a total function in
that space. Consequently the total strategy depends on the hypothesis space,
which makes this form of Lemma~R weaker than the ones in the previous
section.\<close>

lemma lemma_R_for_TOTAL:
  fixes \<psi> :: partial2
  shows "\<exists>d. \<forall>U. \<forall>i. learn_total \<psi> U (\<phi> i) \<longrightarrow>  learn_total \<psi> U (totalizer d i)"
proof (cases "\<exists>d. \<psi> d \<in> \<R>")
  case True
  then obtain d where "\<psi> d \<in> \<R>" by auto
  have "learn_total \<psi> U (totalizer d i)" if "learn_total \<psi> U (\<phi> i)" for U i
  proof (rule learn_totalI)
    show env: "environment \<psi> U (totalizer d i)"
      using that learn_totalE(1) totalizer_in_R2 by auto
    show "\<And>f. f \<in> U \<Longrightarrow> \<exists>j. \<psi> j = f \<and> (\<forall>\<^sup>\<infinity>n. totalizer d i (f \<triangleright> n) \<down>= j)"
      using that learn_total_def lemma_R_for_Lim[where ?d=d] learn_limE(2) by metis
    show "\<psi> (the (totalizer d i (f \<triangleright> n))) \<in> \<R>" if "f \<in> U" for f n
    proof (cases "the (delay i (f \<triangleright> n)) = 0")
      case True
      then show ?thesis using totalizer_def \<open>\<psi> d \<in> \<R>\<close> by simp
    next
      case False
      have "f \<in> \<R>"
        using that env by auto
      then show ?thesis
        using False that \<open>learn_total \<psi> U (\<phi> i)\<close> totalizer_init learn_totalE(3)
        by simp
    qed
  qed
  then show ?thesis by auto
next
  case False
  then show ?thesis using learn_total_def lemma_R_for_Lim by auto
qed

corollary lemma_R_for_TOTAL_simple:
  assumes "learn_total \<psi> U s"
  shows "\<exists>s'\<in>\<R>. learn_total \<psi> U s'"
  using assms lemma_R_for_TOTAL totalizer_in_R2
  by (metis R2_proj_R1 learn_totalE(1) phi_universal)

text \<open>For CP the default hypothesis used by @{term totalizer} depends
on both the hypothesis space and the class. Therefore the total strategy
depends on both the the hypothesis space and the class, which makes Lemma~R
for CP even weaker than the one for TOTAL.\<close>

lemma lemma_R_for_CP:
  fixes \<psi> :: partial2 and U :: "partial1 set"
  assumes "learn_cp \<psi> U (\<phi> i)"
  shows "\<exists>d. learn_cp \<psi> U (totalizer d i)"
proof (cases "U = {}")
  case True
  then show ?thesis using assms learn_cp_def lemma_R_for_Lim by auto
next
  case False
  then obtain f where "f \<in> U" by auto
  from \<open>f \<in> U\<close> obtain d where "\<psi> d = f"
    using learn_cpE(2)[OF assms] by auto
  with \<open>f \<in> U\<close> have "\<psi> d \<in> U" by simp
  have "learn_cp \<psi> U (totalizer d i)"
  proof (rule learn_cpI)
    show env: "environment \<psi> U (totalizer d i)"
      using assms learn_cpE(1) totalizer_in_R2 by auto
    show "\<And>f. f \<in> U \<Longrightarrow> \<exists>j. \<psi> j = f \<and> (\<forall>\<^sup>\<infinity>n. totalizer d i (f \<triangleright> n) \<down>= j)"
      using assms learn_cp_def lemma_R_for_Lim[where ?d=d] learn_limE(2) by metis
    show "\<psi> (the (totalizer d i (f \<triangleright> n))) \<in> U" if "f \<in> U" for f n
    proof (cases "the (delay i (f \<triangleright> n)) = 0")
      case True
      then show ?thesis using totalizer_def \<open>\<psi> d \<in> U\<close> by simp
    next
      case False
      then show ?thesis
        using that env assms totalizer_init learn_cpE(3) by auto
    qed
  qed
  then show ?thesis by auto
qed


subsection \<open>No Lemma R for CONS\<close>

text \<open>This section demonstrates that the class $V_{01}$ of all total
recursive functions $f$ where $f(0)$ or $f(1)$ is a Gödel number of $f$ can
be consistently learned in the limit, but not by a total strategy. This implies
that Lemma~R does not hold for CONS.\<close>

definition V01 :: "partial1 set" ("V\<^sub>0\<^sub>1") where
  "V\<^sub>0\<^sub>1 = {f. f \<in> \<R> \<and> (\<phi> (the (f 0)) = f \<or> \<phi> (the (f 1)) = f)}"


subsubsection \<open>No total CONS strategy for @{term "V\<^sub>0\<^sub>1"}\label{s:v01_not_total}\<close>

text \<open>In order to show that no total strategy can learn @{term
"V\<^sub>0\<^sub>1"} we construct, for each total strategy $S$, one or two
functions in @{term "V\<^sub>0\<^sub>1"} such that $S$ fails for at least one
of them. At the core of this construction is a process that given a total
recursive strategy $S$ and numbers $z, i, j \in \mathbb{N}$ builds a function
$f$ as follows: Set $f(0) = i$ and $f(1) = j$. For $x\geq1$:
\begin{enumerate}
\item[(a)] Check whether $S$ changes its hypothesis when $f^x$ is
  extended by 0, that is, if $S(f^x) \neq S(f^x0)$. If so, set $f(x+1) = 0$.
\item[(b)] Otherwise check if $S$ changes its hypothesis when $f^x$ is extended
  by $1$, that is, if $S(f^x) \neq S(f^x1)$. If so, set $f(x+1) = 1$.
\item[(c)] If neither happens, set $f(x+1) = z$.
\end{enumerate}
In other words, as long as we can force $S$ to change its hypothesis by
extending the function by 0 or 1, we do just that. Now there are two
cases:
\begin{enumerate}
\item[Case 1.] For all $x\geq1$ either (a) or (b) occurs; then $S$
  changes its hypothesis on $f$ all the time and thus does not learn $f$ in
  the limit (not to mention consistently). The value of $z$ makes no
  difference in this case.
\item[Case 2.] For some minimal $x$, (c) occurs, that is,
  there is an $f^x$ such that $h := S(f^x) = S(f^x0) = S(f^x1)$. But the
  hypothesis $h$ cannot be consistent with both prefixes $f^x0$ and $f^x1$.
  Running the process once with $z = 0$ and once with $z = 1$ yields two
  functions starting with $f^x0$ and $f^x1$, respectively, such that $S$
  outputs the same hypothesis, $h$, on both prefixes and thus cannot be
  consistent for both functions.
\end{enumerate}
This process is computable because $S$ is total. The construction does not
work if we only assume $S$ to be a CONS strategy for $V_{01}$, because we
need to be able to apply $S$ to prefixes not in $V_{01}$.

The parameters $i$ and $j$ provide flexibility to find functions built by the
above process that are actually in $V_{01}$. To this end we will use
Smullyan's double fixed-point theorem.\<close>

context
  fixes s :: partial1
  assumes s_in_R1 [simp, intro]: "s \<in> \<R>"
begin

text \<open>The function @{term prefixes} constructs prefixes according to the
aforementioned process.\<close>

fun prefixes :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "prefixes z i j 0 = [i]"
| "prefixes z i j (Suc x) = prefixes z i j x @
    [if x = 0 then j
     else if s (list_encode (prefixes z i j x @ [0])) \<noteq> s (list_encode (prefixes z i j x))
          then 0
          else if s (list_encode (prefixes z i j x @ [1])) \<noteq> s (list_encode (prefixes z i j x))
               then 1
               else z]"

lemma prefixes_length: "length (prefixes z i j x) = Suc x"
  by (induction x) simp_all

text \<open>The functions @{term[names_short] "adverse z i j"} are the
functions constructed by @{term[names_short] "prefixes"}.\<close>

definition adverse :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "adverse z i j x \<equiv> Some (last (prefixes z i j x))"

lemma init_adverse_eq_prefixes: "(adverse z i j) \<triangleright> n = list_encode (prefixes z i j n)"
proof -
  have "prefix (adverse z i j) n = prefixes z i j n"
  proof (induction n)
    case 0
    then show ?case using adverse_def prefixes_length prefixI' by fastforce
  next
    case (Suc n)
    then show ?case using adverse_def by (simp add: prefix_Suc)
  qed
  then show ?thesis by (simp add: init_def)
qed

lemma adverse_at_01:
  "adverse z i j 0 \<down>= i"
  "adverse z i j 1 \<down>= j"
  by (auto simp add: adverse_def)

text \<open>Had we introduced ternary partial recursive functions, the
@{term[names_short] "adverse z"} functions would be among them.\<close>

lemma adverse_in_R3: "\<exists>r. recfn 3 r \<and> total r \<and> (\<lambda>i j x. eval r [i, j, x]) = adverse z"
proof -
  obtain rs where rs: "recfn 1 rs" "total rs" "(\<lambda>x. eval rs [x]) = s"
    using R1E by auto
  have s_total: "\<And>x. s x \<down>" by simp

  define f where "f = Cn 2 r_singleton_encode [Id 2 0]"
  then have "recfn 2 f" by simp
  have f: "\<And>i j. eval f [i, j] \<down>= list_encode [i]"
    unfolding f_def by simp

  define ch1 where "ch1 = Cn 4 r_ifeq
    [Cn 4 rs [Cn 4 r_snoc [Id 4 1, r_constn 3 1]],
     Cn 4 rs [Id 4 1],
     r_dummy 3 (r_const z),
     r_constn 3 1]"
  then have ch1: "recfn 4 ch1" "total ch1"
    using Cn_total prim_recfn_total rs by auto

  define ch0 where "ch0 = Cn 4 r_ifeq
    [Cn 4 rs [Cn 4 r_snoc [Id 4 1, r_constn 3 0]],
     Cn 4 rs [Id 4 1],
     ch1,
     r_constn 3 0]"
  then have ch0_total: "total ch0" "recfn 4 ch0"
    using Cn_total prim_recfn_total rs ch1 by auto

  have "eval ch1 [l, v, i, j] \<down>= (if s (e_snoc v 1) = s v then z else 1)" for l v i j
  proof -
    have "eval ch1 [l, v, i, j] = eval r_ifeq [the (s (e_snoc v 1)), the (s v), z, 1]"
      unfolding ch1_def using rs by auto
    then show ?thesis by (simp add: s_total option.expand)
  qed
  moreover have "eval ch0 [l, v, i, j] \<down>=
    (if s (e_snoc v 0) = s v then the (eval ch1 [l, v, i, j]) else 0)" for l v i j
  proof -
    have "eval ch0 [l, v, i, j] =
        eval r_ifeq [the (s (e_snoc v 0)), the (s v), the (eval ch1 [l, v, i, j]), 0]"
      unfolding ch0_def using rs ch1 by auto
    then show ?thesis by (simp add: s_total option.expand)
  qed
  ultimately have ch0: "\<And>l v i j. eval ch0 [l, v, i, j] \<down>=
    (if s (e_snoc v 0) \<noteq> s v then 0
     else if s (e_snoc v 1) \<noteq> s v then 1 else z)"
    by simp

  define app where "app = Cn 4 r_ifz [Id 4 0, Id 4 3, ch0]"
  then have "recfn 4 app" "total app"
    using ch0_total totalI4 by auto
  have "eval app [l, v, i, j] \<down>= (if l = 0 then j else the (eval ch0 [l, v, i, j]))" for l v i j
    unfolding app_def using ch0_total by simp
  with ch0 have app: "\<And>l v i j. eval app [l, v, i, j] \<down>=
    (if l = 0 then j
     else if s (e_snoc v 0) \<noteq> s v then 0
     else if s (e_snoc v 1) \<noteq> s v then 1 else z)"
    by simp

  define g where "g = Cn 4 r_snoc [Id 4 1, app]"
  with app have g: "\<And>l v i j. eval g [l, v, i, j] \<down>= e_snoc v
    (if l = 0 then j
     else if s (e_snoc v 0) \<noteq> s v then 0
     else if s (e_snoc v 1) \<noteq> s v then 1 else z)"
    using \<open>recfn 4 app\<close> by auto
  from g_def have "recfn 4 g" "total g"
    using \<open>recfn 4 app\<close> \<open>total app\<close> Cn_total Mn_free_imp_total by auto

  define b where "b = Pr 2 f g"
  then have "recfn 3 b"
    using \<open>recfn 2 f\<close> \<open>recfn 4 g\<close> by simp
  have b: "eval b [x, i, j] \<down>= list_encode (prefixes z i j x)" for x i j
  proof (induction x)
    case 0
    then show ?case
      unfolding b_def using f \<open>recfn 2 f\<close> \<open>recfn 4 g\<close> by simp
  next
    case (Suc x)
    then have "eval b [Suc x, i, j] = eval g [x, the (eval b [x, i, j]), i, j]"
      using b_def \<open>recfn 3 b\<close> by simp
    also have "... \<down>=
     (let v = list_encode (prefixes z i j x)
      in e_snoc v
        (if x = 0 then j
         else if s (e_snoc v 0) \<noteq> s v then 0
              else if s (e_snoc v 1) \<noteq> s v then 1 else z))"
      using g Suc by simp
    also have "... \<down>=
     (let v = list_encode (prefixes z i j x)
      in e_snoc v
        (if x = 0 then j
         else if s (list_encode (prefixes z i j x @ [0])) \<noteq> s v then 0
              else if s (list_encode (prefixes z i j x @ [1])) \<noteq> s v then 1 else z))"
      using list_decode_encode by presburger
    finally show ?case by simp
  qed

  define b' where "b' = Cn 3 b [Id 3 2, Id 3 0, Id 3 1]"
  then have "recfn 3 b'"
    using \<open>recfn 3 b\<close> by simp
  with b have b': "\<And>i j x. eval b' [i, j, x] \<down>= list_encode (prefixes z i j x)"
    using b'_def by simp

  define r where "r = Cn 3 r_last [b']"
  then have "recfn 3 r"
    using \<open>recfn 3 b'\<close> by simp
  with b' have "\<And>i j x. eval r [i, j, x] \<down>= last (prefixes z i j x)"
    using r_def prefixes_length by auto
  moreover from this have "total r"
    using totalI3 \<open>recfn 3 r\<close> by simp
  ultimately have "(\<lambda>i j x. eval r [i, j, x]) = adverse z"
    unfolding adverse_def by simp
  with \<open>recfn 3 r\<close> \<open>total r\<close> show ?thesis by auto
qed

lemma adverse_in_R1: "adverse z i j \<in> \<R>"
proof -
  from adverse_in_R3 obtain r where
    r: "recfn 3 r" "total r" "(\<lambda>i j x. eval r [i, j, x]) = adverse z"
    by blast
  define rij where "rij = Cn 1 r [r_const i, r_const j, Id 1 0]"
  then have "recfn 1 rij" "total rij"
    using r(1,2) Cn_total Mn_free_imp_total by auto
  from rij_def have "\<And>x. eval rij [x] = eval r [i, j, x]"
    using r(1) by auto
  with r(3) have "\<And>x. eval rij [x] = adverse z i j x"
    by metis
  with \<open>recfn 1 rij\<close> \<open>total rij\<close> show ?thesis by auto
qed

text \<open>Next we show that for every $z$ there are $i$, $j$ such that
@{term[names_short] "adverse z i j \<in> V\<^sub>0\<^sub>1"}. The first step is to show that for every
$z$, Gödel numbers for @{term[names_short] "adverse z i j"} can be computed
uniformly from $i$ and $j$.\<close>

lemma phi_translate_adverse: "\<exists>f\<in>\<R>\<^sup>2.\<forall>i j. \<phi> (the (f i j)) = adverse z i j"
proof -
  obtain r where r: "recfn 3 r" "total r" "(\<lambda>i j x. eval r [i, j, x]) = adverse z"
    using adverse_in_R3 by blast
  let ?p = "encode r"
  define rf where "rf = Cn 2 (r_smn 1 2) [r_dummy 1 (r_const ?p), Id 2 0, Id 2 1]"
  then have "recfn 2 rf" and "total rf"
    using Mn_free_imp_total by simp_all
  define f where "f \<equiv> \<lambda>i j. eval rf [i, j]"
  with \<open>recfn 2 rf\<close> \<open>total rf\<close> have "f \<in> \<R>\<^sup>2" by auto
  have rf: "eval rf [i, j] = eval (r_smn 1 2) [?p, i, j]" for i j
    unfolding rf_def by simp
  {
    fix i j x
    have "\<phi> (the (f i j)) x = eval r_phi [the (f i j), x]"
      using phi_def by simp
    also have "... = eval r_phi [the (eval rf [i, j]), x]"
      using f_def by simp
    also have "... = eval (r_universal 1) [the (eval (r_smn 1 2) [?p, i, j]), x]"
      using rf r_phi_def by simp
    also have "... = eval (r_universal (2 + 1)) (?p # [i, j] @ [x])" 
      using smn_lemma[of 1 "[i, j]" 2 "[x]"] by simp
    also have "... = eval (r_universal 3) [?p, i, j, x]" 
      by simp
    also have "... = eval r [i, j, x]" 
      using r_universal r by force
    also have "... = adverse z i j x" 
      using r(3) by metis
    finally have "\<phi> (the (f i j)) x = adverse z i j x" .
  }
  with \<open>f \<in> \<R>\<^sup>2\<close> show ?thesis by blast
qed

text \<open>The second, and final, step is to apply Smullyan's double
fixed-point theorem to show the existence of @{term[names_short] adverse}
functions in @{term "V\<^sub>0\<^sub>1"}.\<close>

lemma adverse_in_V01: "\<exists>m n. adverse 0 m n \<in> V\<^sub>0\<^sub>1 \<and> adverse 1 m n \<in> V\<^sub>0\<^sub>1"
proof -
  obtain f\<^sub>0 where f0: "f\<^sub>0 \<in> \<R>\<^sup>2" "\<forall>i j. \<phi> (the (f\<^sub>0 i j)) = adverse 0 i j"
    using phi_translate_adverse[of 0] by auto
  obtain f\<^sub>1 where f1: "f\<^sub>1 \<in> \<R>\<^sup>2" "\<forall>i j. \<phi> (the (f\<^sub>1 i j)) = adverse 1 i j"
    using phi_translate_adverse[of 1] by auto
  obtain m n where "\<phi> m = \<phi> (the (f\<^sub>0 m n))" and "\<phi> n = \<phi> (the (f\<^sub>1 m n))"
    using smullyan_double_fixed_point[OF f0(1) f1(1)] by blast
  with f0(2) f1(2) have "\<phi> m = adverse 0 m n" and "\<phi> n = adverse 1 m n"
    by simp_all
  moreover have "the (adverse 0 m n 0) = m" and "the (adverse 1 m n 1) = n"
    using adverse_at_01 by simp_all
  ultimately have
    "\<phi> (the (adverse 0 m n 0)) = adverse 0 m n"
    "\<phi> (the (adverse 1 m n 1)) = adverse 1 m n"
    by simp_all
  moreover have "adverse 0 m n \<in> \<R>" and "adverse 1 m n \<in> \<R>"
    using adverse_in_R1 by simp_all
  ultimately show ?thesis using V01_def by auto
qed

text \<open>Before we prove the main result of this section we need some
lemmas regarding the shape of the @{term[names_short] adverse} functions and
hypothesis changes of the strategy.\<close>

lemma adverse_Suc:
  assumes "x > 0"
  shows "adverse z i j (Suc x) \<down>=
    (if s (e_snoc ((adverse z i j) \<triangleright> x) 0) \<noteq> s ((adverse z i j) \<triangleright> x)
     then 0
     else if s (e_snoc ((adverse z i j) \<triangleright> x) 1) \<noteq> s ((adverse z i j) \<triangleright> x)
          then 1 else z)"
proof -
  have "adverse z i j (Suc x) \<down>=
    (if s (list_encode (prefixes z i j x @ [0])) \<noteq> s (list_encode (prefixes z i j x))
     then 0
     else if s (list_encode (prefixes z i j x @ [1])) \<noteq> s (list_encode (prefixes z i j x))
          then 1 else z)"
    using assms adverse_def by simp
  then show ?thesis by (simp add: init_adverse_eq_prefixes)
qed

text \<open>The process in the proof sketch (page~\pageref{s:v01_not_total})
consists of steps (a), (b), and (c). The next abbreviation is true iff.\ step
(a) or (b) applies.\<close>

abbreviation "hyp_change z i j x \<equiv>
  s (e_snoc ((adverse z i j) \<triangleright> x) 0) \<noteq> s ((adverse z i j) \<triangleright> x) \<or>
  s (e_snoc ((adverse z i j) \<triangleright> x) 1) \<noteq> s ((adverse z i j) \<triangleright> x)"

text \<open>If step (c) applies, the process appends $z$.\<close>

lemma adverse_Suc_not_hyp_change:
  assumes "x > 0" and "\<not> hyp_change z i j x"
  shows "adverse z i j (Suc x) \<down>= z"
  using assms adverse_Suc by simp

text \<open>While (a) or (b) applies, the process appends a value that
forces $S$ to change its hypothesis.\<close>

lemma while_hyp_change:
  assumes "\<forall>x\<le>n. x > 0 \<longrightarrow> hyp_change z i j x"
  shows "\<forall>x\<le>Suc n. adverse z i j x = adverse z' i j x"
  using assms
proof (induction n)
  case 0
  then show ?case by (simp add: adverse_def le_Suc_eq)
next
  case (Suc n)
  then have "\<forall>x\<le>n. x > 0 \<longrightarrow> hyp_change z i j x" by simp
  with Suc have "\<forall>x\<le>Suc n. x > 0 \<longrightarrow> adverse z i j x = adverse z' i j x"
    by simp
  moreover have "adverse z i j 0 = adverse z' i j 0"
    using adverse_at_01 by simp
  ultimately have zz': "\<forall>x\<le>Suc n. adverse z i j x = adverse z' i j x"
    by auto
  moreover have "adverse z i j \<in> \<R>" "adverse z' i j \<in> \<R>"
    using adverse_in_R1 by simp_all
  ultimately have init_zz': "(adverse z i j) \<triangleright> (Suc n) = (adverse z' i j) \<triangleright> (Suc n)"
    using init_eqI by blast

  have "adverse z i j (Suc (Suc n)) = adverse z' i j (Suc (Suc n))"
  proof (cases "s (e_snoc ((adverse z i j) \<triangleright> (Suc n)) 0) \<noteq> s ((adverse z i j) \<triangleright> (Suc n))")
    case True
    then have "s (e_snoc ((adverse z' i j) \<triangleright> (Suc n)) 0) \<noteq> s ((adverse z' i j) \<triangleright> (Suc n))"
      using init_zz' by simp
    then have "adverse z' i j (Suc (Suc n)) \<down>= 0"
      by (simp add: adverse_Suc)
    moreover have "adverse z i j (Suc (Suc n)) \<down>= 0"
      using True by (simp add: adverse_Suc)
    ultimately show ?thesis by simp
  next
    case False
    then have "s (e_snoc ((adverse z' i j) \<triangleright> (Suc n)) 0) = s ((adverse z' i j) \<triangleright> (Suc n))"
      using init_zz' by simp
    then have "adverse z' i j (Suc (Suc n)) \<down>= 1"
      using init_zz' Suc.prems adverse_Suc by (smt le_refl zero_less_Suc)
    moreover have "adverse z i j (Suc (Suc n)) \<down>= 1"
      using False Suc.prems adverse_Suc by auto
    ultimately show ?thesis by simp
  qed
  with zz' show ?case using le_SucE by blast
qed

text \<open>The next result corresponds to Case~1 from the proof sketch.\<close>

lemma always_hyp_change_no_lim:
  assumes "\<forall>x>0. hyp_change z i j x"
  shows "\<not> learn_lim \<phi> {adverse z i j} s"
proof (rule infinite_hyp_changes_not_Lim[of "adverse z i j"])
  show "adverse z i j \<in> {adverse z i j}" by simp
  show "\<forall>n. \<exists>m\<^sub>1>n. \<exists>m\<^sub>2>n. s (adverse z i j \<triangleright> m\<^sub>1) \<noteq> s (adverse z i j \<triangleright> m\<^sub>2)"
  proof
    fix n
    from assms obtain m\<^sub>1 where m1: "m\<^sub>1 > n" "hyp_change z i j m\<^sub>1"
      by auto
    have "s (adverse z i j \<triangleright> m\<^sub>1) \<noteq> s (adverse z i j \<triangleright> (Suc m\<^sub>1))"
    proof (cases "s (e_snoc ((adverse z i j) \<triangleright> m\<^sub>1) 0) \<noteq> s ((adverse z i j) \<triangleright> m\<^sub>1)")
      case True
      then have "adverse z i j (Suc m\<^sub>1) \<down>= 0"
        using m1 adverse_Suc by simp
      then have "(adverse z i j) \<triangleright> (Suc m\<^sub>1) = e_snoc ((adverse z i j) \<triangleright> m\<^sub>1) 0"
        by (simp add: init_Suc_snoc)
      with True show ?thesis by simp
    next
      case False
      then have "adverse z i j (Suc m\<^sub>1) \<down>= 1"
        using m1 adverse_Suc by simp
      then have "(adverse z i j) \<triangleright> (Suc m\<^sub>1) = e_snoc ((adverse z i j) \<triangleright> m\<^sub>1) 1"
        by (simp add: init_Suc_snoc)
      with False m1(2) show ?thesis by simp
    qed
    then show "\<exists>m\<^sub>1>n. \<exists>m\<^sub>2>n. s (adverse z i j \<triangleright> m\<^sub>1) \<noteq> s (adverse z i j \<triangleright> m\<^sub>2)"
      using less_SucI m1(1) by blast
  qed
qed

text \<open>The next result corresponds to Case~2 from the proof sketch.\<close>

lemma no_hyp_change_no_cons:
  assumes "x > 0" and "\<not> hyp_change z i j x"
  shows "\<not> learn_cons \<phi> {adverse 0 i j, adverse 1 i j} s"
proof -
  let ?P = "\<lambda>x. x > 0 \<and> \<not> hyp_change z i j x"
  define xmin where "xmin = Least ?P"
  with assms have xmin:
    "?P xmin"
    "\<And>x. x < xmin \<Longrightarrow> \<not> ?P x"
    using LeastI[of ?P] not_less_Least[of _ ?P] by simp_all
  then have "xmin > 0" by simp

  have "\<forall>x\<le>xmin - 1. x > 0 \<longrightarrow> hyp_change z i j x"
    using xmin by (metis One_nat_def Suc_pred le_imp_less_Suc)
  then have
    "\<forall>x\<le>xmin. adverse z i j x = adverse 0 i j x"
    "\<forall>x\<le>xmin. adverse z i j x = adverse 1 i j x"
    using while_hyp_change[of "xmin - 1" z i j 0]
    using while_hyp_change[of "xmin - 1" z i j 1]
    by simp_all
  then have
    init_z0: "(adverse z i j) \<triangleright> xmin = (adverse 0 i j) \<triangleright> xmin" and
    init_z1: "(adverse z i j) \<triangleright> xmin = (adverse 1 i j) \<triangleright> xmin"
    using adverse_in_R1 init_eqI by blast+
  then have
    a0: "adverse 0 i j (Suc xmin) \<down>= 0" and
    a1: "adverse 1 i j (Suc xmin) \<down>= 1"
    using adverse_Suc_not_hyp_change xmin(1) init_z1
    by metis+
  then have
    i0: "(adverse 0 i j) \<triangleright> (Suc xmin) = e_snoc ((adverse z i j) \<triangleright> xmin) 0" and
    i1: "(adverse 1 i j) \<triangleright> (Suc xmin) = e_snoc ((adverse z i j) \<triangleright> xmin) 1"
    using init_z0 init_z1 by (simp_all add: init_Suc_snoc)
  moreover have
    "s (e_snoc ((adverse z i j) \<triangleright> xmin) 0) = s ((adverse z i j) \<triangleright> xmin)"
    "s (e_snoc ((adverse z i j) \<triangleright> xmin) 1) = s ((adverse z i j) \<triangleright> xmin)"
    using xmin by simp_all
  ultimately have
    "s ((adverse 0 i j) \<triangleright> (Suc xmin)) = s ((adverse z i j) \<triangleright> xmin)"
    "s ((adverse 1 i j) \<triangleright> (Suc xmin)) = s ((adverse z i j) \<triangleright> xmin)"
    by simp_all
  then have
    "s ((adverse 0 i j) \<triangleright> (Suc xmin)) = s ((adverse 1 i j) \<triangleright> (Suc xmin))"
    by simp
  moreover have "(adverse 0 i j) \<triangleright> (Suc xmin) \<noteq> (adverse 1 i j) \<triangleright> (Suc xmin)"
    using a0 a1 i0 i1 by (metis append1_eq_conv list_decode_encode zero_neq_one)
  ultimately show "\<not> learn_cons \<phi> {adverse 0 i j, adverse 1 i j} s"
    using same_hyp_different_init_not_cons by blast
qed

text \<open>Combining the previous two lemmas shows that @{term
"V\<^sub>0\<^sub>1"} cannot be learned consistently in the limit by the total
strategy $S$.\<close>

lemma V01_not_in_R_cons: "\<not> learn_cons \<phi> V\<^sub>0\<^sub>1 s"
proof -
  obtain m n where
    mn0: "adverse 0 m n \<in> V\<^sub>0\<^sub>1" and
    mn1: "adverse 1 m n \<in> V\<^sub>0\<^sub>1"
    using adverse_in_V01 by auto
  show "\<not> learn_cons \<phi> V\<^sub>0\<^sub>1 s"
  proof (cases "\<forall>x>0. hyp_change 0 m n x")
    case True
    then have "\<not> learn_lim \<phi> {adverse 0 m n} s"
      using always_hyp_change_no_lim by simp
    with mn0 show ?thesis
      using learn_cons_def learn_lim_closed_subseteq by auto
  next
    case False
    then obtain x where x: "x > 0" "\<not> hyp_change 0 m n x" by auto
    then have "\<not> learn_cons \<phi> {adverse 0 m n, adverse 1 m n} s"
      using no_hyp_change_no_cons[OF x] by simp
    with mn0 mn1 show ?thesis using learn_cons_closed_subseteq by auto
  qed
qed

end


subsubsection \<open>@{term "V\<^sub>0\<^sub>1"} is in CONS\<close>

text \<open>At first glance, consistently learning @{term "V\<^sub>0\<^sub>1"} looks fairly
easy. After all every @{term "f \<in> V\<^sub>0\<^sub>1"} provides a Gödel number of itself
either at argument 0 or 1. A strategy only has to figure out which one is
right. However, the strategy $S$ we are going to devise does not always
converge to $f(0)$ or $f(1)$. Instead it uses a technique called
``amalgamation''. The amalgamation of two Gödel numbers $i$ and $j$ is a
function whose value at $x$ is determined by simulating $\varphi_i(x)$ and
$\varphi_j(x)$ in parallel and outputting the value of the first one to halt.
If neither halts the value is undefined. There is a function
$a\in\mathcal{R}^2$ such that $\varphi_{a(i,j)}$ is the amalgamation of $i$
and $j$.

If @{term "f \<in> V\<^sub>0\<^sub>1"} then $\varphi_{a(f(0), f(1))}$ is
total because by definition of @{term "V\<^sub>0\<^sub>1"} we have
$\varphi_{f(0)} = f$ or $\varphi_{f(1)} = f$ and $f$ is total.

Given a prefix $f^n$ of an @{term "f \<in> V\<^sub>0\<^sub>1"} the strategy
$S$ first computes $\varphi_{a(f(0), f(1))}(x)$ for $x = 0, \ldots, n$. For
the resulting prefix $\varphi^n_{a(f(0), f(1))}$ there are two cases:
\begin{enumerate}
\item[Case 1.] It differs from $f^n$, say at minimum index $x$. Then for
  either $z = 0$ or $z = 1$ we have $\varphi_{f(z)}(x) \neq f(x)$ by
  definition of amalgamation. This
  implies $\varphi_{f(z)} \neq f$, and thus $\varphi_{f(1-z)} = f$ by
  definition of @{term "V\<^sub>0\<^sub>1"}. We set $S(f^n) = f(1 - z)$. This
  hypothesis is correct and hence consistent.
\item[Case 2.] It equals $f^n$. Then we set $S(f^n) = a(f(0), f(1))$. This
  hypothesis is consistent by definition of this case.
\end{enumerate}

In both cases the hypothesis is consistent. If Case~1 holds for some $n$, the
same $x$ and $z$ will be found also for all larger values of $n$. Therefore
$S$ converges to the correct hypothesis $f(1 - z)$. If Case~2 holds for all
$n$, then $S$ always outputs the same hypothesis $a(f(0), f(1))$ and thus
also converges.

The above discussion tacitly assumes $n \geq 1$, such that both $f(0)$ and
$f(1)$ are available to $S$. For $n = 0$ the strategy outputs an arbitrary
consistent hypothesis.\<close>

text \<open>Amalgamation uses the concurrent simulation of functions.\<close>

definition parallel :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "parallel i j x \<equiv> eval r_parallel [i, j, x]"

lemma r_parallel': "eval r_parallel [i, j, x] = parallel i j x"
  using parallel_def by simp

lemma r_parallel'':
  shows "eval r_phi [i, x] \<up> \<and> eval r_phi [j, x] \<up> \<Longrightarrow> eval r_parallel [i, j, x] \<up>"
    and "eval r_phi [i, x] \<down> \<and> eval r_phi [j, x] \<up> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval r_phi [i, x]))"
    and "eval r_phi [j, x] \<down> \<and> eval r_phi [i, x] \<up> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval r_phi [j, x]))"
    and "eval r_phi [i, x] \<down> \<and> eval r_phi [j, x] \<down> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval r_phi [i, x])) \<or>
      eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval r_phi [j, x]))"
proof -
  let ?f = "Cn 1 r_phi [r_const i, Id 1 0]"
  let ?g = "Cn 1 r_phi [r_const j, Id 1 0]"
  have *: "\<And>x. eval r_phi [i, x] = eval ?f [x]" "\<And>x. eval r_phi [j, x] = eval ?g [x]"
    by simp_all
  show "eval r_phi [i, x] \<up> \<and> eval r_phi [j, x] \<up> \<Longrightarrow> eval r_parallel [i, j, x] \<up>"
    and "eval r_phi [i, x] \<down> \<and> eval r_phi [j, x] \<up> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval r_phi [i, x]))"
    and "eval r_phi [j, x] \<down> \<and> eval r_phi [i, x] \<up> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval r_phi [j, x]))"
    and "eval r_phi [i, x] \<down> \<and> eval r_phi [j, x] \<down> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval r_phi [i, x])) \<or>
      eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval r_phi [j, x]))"
    using r_parallel[OF *] by simp_all
qed

lemma parallel:
  "\<phi> i x \<up> \<and> \<phi> j x \<up> \<Longrightarrow> parallel i j x \<up>"
  "\<phi> i x \<down> \<and> \<phi> j x \<up> \<Longrightarrow> parallel i j x \<down>= prod_encode (0, the (\<phi> i x))"
  "\<phi> j x \<down> \<and> \<phi> i x \<up> \<Longrightarrow> parallel i j x \<down>= prod_encode (1, the (\<phi> j x))"
  "\<phi> i x \<down> \<and> \<phi> j x \<down> \<Longrightarrow>
     parallel i j x \<down>= prod_encode (0, the (\<phi> i x)) \<or>
     parallel i j x \<down>= prod_encode (1, the (\<phi> j x))"
  using phi_def r_parallel'' r_parallel parallel_def by simp_all

lemma parallel_converg_pdec1_0_or_1:
  assumes "parallel i j x \<down>"
  shows "pdec1 (the (parallel i j x)) = 0 \<or> pdec1 (the (parallel i j x)) = 1"
  using assms parallel[of i x j] parallel(3)[of j x i]
  by (metis fst_eqD option.sel prod_encode_inverse)

lemma parallel_converg_either: "(\<phi> i x \<down> \<or> \<phi> j x \<down>) = (parallel i j x \<down>)"
  using parallel by (metis option.simps(3))

lemma parallel_0:
  assumes "parallel i j x \<down>= prod_encode (0, v)"
  shows "\<phi> i x \<down>= v"
  using parallel assms
  by (smt option.collapse option.sel option.simps(3) prod.inject prod_encode_eq zero_neq_one)

lemma parallel_1:
  assumes "parallel i j x \<down>= prod_encode (1, v)"
  shows "\<phi> j x \<down>= v"
  using parallel assms
  by (smt option.collapse option.sel option.simps(3) prod.inject prod_encode_eq zero_neq_one)

lemma parallel_converg_V01:
  assumes "f \<in> V\<^sub>0\<^sub>1"
  shows "parallel (the (f 0)) (the (f 1)) x \<down>"
proof -
  have "f \<in> \<R> \<and> (\<phi> (the (f 0)) = f \<or> \<phi> (the (f 1)) = f)"
    using assms V01_def by auto
  then have "\<phi> (the (f 0)) \<in> \<R> \<or> \<phi> (the (f 1)) \<in> \<R>"
    by auto
  then have "\<phi> (the (f 0)) x \<down> \<or> \<phi> (the (f 1)) x \<down>"
    using R1_imp_total1 by auto
  then show ?thesis using parallel_converg_either by simp
qed

text \<open>The amalgamation of two Gödel numbers can then be described
in terms of @{term "parallel"}.\<close>

definition amalgamation :: "nat \<Rightarrow> nat \<Rightarrow> partial1" where
  "amalgamation i j x \<equiv>
     if parallel i j x \<up> then None else Some (pdec2 (the (parallel i j x)))"

lemma amalgamation_diverg: "amalgamation i j x \<up> \<longleftrightarrow> \<phi> i x \<up> \<and> \<phi> j x \<up>"
  using amalgamation_def parallel by (metis option.simps(3))

lemma amalgamation_total:
  assumes "total1 (\<phi> i) \<or> total1 (\<phi> j)"
  shows "total1 (amalgamation i j)"
  using assms amalgamation_diverg[of i j] total_def by auto

lemma amalgamation_V01_total:
  assumes "f \<in> V\<^sub>0\<^sub>1"
  shows "total1 (amalgamation (the (f 0)) (the (f 1)))"
  using assms V01_def amalgamation_total R1_imp_total1 total1_def
  by (metis (mono_tags, lifting) mem_Collect_eq)

definition "r_amalgamation \<equiv> Cn 3 r_pdec2 [r_parallel]"

lemma r_amalgamation_recfn: "recfn 3 r_amalgamation"
  unfolding r_amalgamation_def by simp

lemma r_amalgamation: "eval r_amalgamation [i, j, x] = amalgamation i j x"
proof (cases "parallel i j x \<up>")
  case True
  then have "eval r_parallel [i, j, x] \<up>"
    by (simp add: r_parallel')
  then have "eval r_amalgamation [i, j, x] \<up>"
    unfolding r_amalgamation_def by simp
  moreover from True have "amalgamation i j x \<up>"
    using amalgamation_def by simp
  ultimately show ?thesis by simp
next
  case False
  then have "eval r_parallel [i, j, x] \<down>"
    by (simp add: r_parallel')
  then have "eval r_amalgamation [i, j, x] = eval r_pdec2 [the (eval r_parallel [i, j, x])]"
    unfolding r_amalgamation_def by simp
  also have "... \<down>= pdec2 (the (eval r_parallel [i, j, x]))"
    by simp
  finally show ?thesis by (simp add: False amalgamation_def r_parallel')
qed

text \<open>The function @{term "amalgamate"} computes Gödel numbers of
amalgamations. It corresponds to the function $a$ from the proof sketch.\<close>

definition amalgamate :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "amalgamate i j \<equiv> smn 1 (encode r_amalgamation) [i, j]"

lemma amalgamate: "\<phi> (amalgamate i j) = amalgamation i j"
proof
  fix x
  have "\<phi> (amalgamate i j) x = eval r_phi [amalgamate i j, x]"
    by (simp add: phi_def)
  also have "... = eval r_phi [smn 1 (encode r_amalgamation) [i, j], x]"
    using amalgamate_def by simp
  also have "... = eval r_phi
     [encode (Cn 1 (r_universal 3)
      (r_constn 0 (encode r_amalgamation) # map (r_constn 0) [i, j] @ map (Id 1) [0])), x]"
    using smn[of 1 "encode r_amalgamation" "[i, j]"] by (simp add: numeral_3_eq_3)
  also have "... = eval r_phi
     [encode (Cn 1 (r_universal 3)
      (r_const (encode r_amalgamation) # [r_const i, r_const j, Id 1 0])), x]"
     (is "... = eval r_phi [encode ?f, x]")
    by (simp add: r_constn_def)
  finally have "\<phi> (amalgamate i j) x = eval r_phi
     [encode (Cn 1 (r_universal 3)
      (r_const (encode r_amalgamation) # [r_const i, r_const j, Id 1 0])), x]" .
  then have "\<phi> (amalgamate i j) x = eval (r_universal 3) [encode r_amalgamation, i, j, x]"
    unfolding r_phi_def using r_universal[of ?f 1] r_amalgamation_recfn by simp
  then show "\<phi> (amalgamate i j) x = amalgamation i j x"
    using r_amalgamation by (simp add: r_amalgamation_recfn r_universal)
qed

lemma amalgamation_in_P1: "amalgamation i j \<in> \<P>"
  using amalgamate by (metis P2_proj_P1 phi_in_P2)

lemma amalgamation_V01_R1:
  assumes "f \<in> V\<^sub>0\<^sub>1"
  shows "amalgamation (the (f 0)) (the (f 1)) \<in> \<R>"
  using assms amalgamation_V01_total amalgamation_in_P1
  by (simp add: P1_total_imp_R1)

definition "r_amalgamate \<equiv>
  Cn 2 (r_smn 1 2) [r_dummy 1 (r_const (encode r_amalgamation)), Id 2 0, Id 2 1]"

lemma r_amalgamate_recfn: "recfn 2 r_amalgamate"
  unfolding r_amalgamate_def by simp

lemma r_amalgamate: "eval r_amalgamate [i, j] \<down>= amalgamate i j"
proof -
  let ?p = "encode r_amalgamation"
  have rs21: "eval (r_smn 1 2) [?p, i, j] \<down>= smn 1 ?p [i, j]"
    using r_smn by simp
  moreover have "eval r_amalgamate [i, j] = eval (r_smn 1 2) [?p, i, j]"
    unfolding r_amalgamate_def by auto
  ultimately have "eval r_amalgamate [i, j] \<down>= smn 1 ?p [i, j]"
    by simp
  then show ?thesis using amalgamate_def by simp
qed

text \<open>The strategy $S$ distinguishes the two cases from the proof
sketch with the help of the next function, which checks if a hypothesis
$\varphi_i$ is inconsistent with a prefix $e$. If so, it returns the least $x
< |e|$ witnessing the inconsistency; otherwise it returns the length $|e|$.
If $\varphi_i$ diverges for some $x < |e|$, so does the function.\<close>

definition inconsist :: partial2 where
  "inconsist i e \<equiv>
    (if \<exists>x<e_length e. \<phi> i x \<up> then None
     else if \<exists>x<e_length e. \<phi> i x \<down>\<noteq> e_nth e x
          then Some (LEAST x. x < e_length e \<and> \<phi> i x \<down>\<noteq> e_nth e x)
          else Some (e_length e))"

lemma inconsist_converg:
  assumes "inconsist i e \<down>"
  shows "inconsist i e =
    (if \<exists>x<e_length e. \<phi> i x \<down>\<noteq> e_nth e x
     then Some (LEAST x. x < e_length e \<and> \<phi> i x \<down>\<noteq> e_nth e x)
     else Some (e_length e))"
    and "\<forall>x<e_length e. \<phi> i x \<down>"
  using inconsist_def assms by (presburger, meson)

lemma inconsist_bounded:
  assumes "inconsist i e \<down>"
  shows "the (inconsist i e) \<le> e_length e"
proof (cases "\<exists>x<e_length e. \<phi> i x \<down>\<noteq> e_nth e x")
  case True
  then show ?thesis
    using inconsist_converg[OF assms]
    by (smt Least_le dual_order.strict_implies_order dual_order.strict_trans2 option.sel)
next
  case False
  then show ?thesis using inconsist_converg[OF assms] by auto
qed

lemma inconsist_consistent:
  assumes "inconsist i e \<down>"
  shows "inconsist i e \<down>= e_length e \<longleftrightarrow> (\<forall>x<e_length e. \<phi> i x \<down>= e_nth e x)"
proof
  show "\<forall>x<e_length e. \<phi> i x \<down>= e_nth e x" if "inconsist i e \<down>= e_length e"
  proof (cases "\<exists>x<e_length e. \<phi> i x \<down>\<noteq> e_nth e x")
    case True
    then show ?thesis
      using that inconsist_converg[OF assms]
      by (metis (mono_tags, lifting) not_less_Least option.inject)
  next
    case False
    then show ?thesis
      using that inconsist_converg[OF assms] by simp
  qed
  show "\<forall>x<e_length e. \<phi> i x \<down>= e_nth e x \<Longrightarrow> inconsist i e \<down>= e_length e"
    unfolding inconsist_def using assms by auto
qed

lemma inconsist_converg_eq:
  assumes "inconsist i e \<down>= e_length e"
  shows "\<forall>x<e_length e. \<phi> i x \<down>= e_nth e x"
  using assms inconsist_consistent by auto

lemma inconsist_converg_less:
  assumes "inconsist i e \<down>" and "the (inconsist i e) < e_length e"
  shows "\<exists>x<e_length e. \<phi> i x \<down>\<noteq> e_nth e x"
    and "inconsist i e \<down>= (LEAST x. x < e_length e \<and> \<phi> i x \<down>\<noteq> e_nth e x)"
proof -
  show "\<exists>x<e_length e. \<phi> i x \<down>\<noteq> e_nth e x"
    using assms by (metis (no_types, lifting) inconsist_converg(1) nat_neq_iff option.sel)
  then show "inconsist i e \<down>= (LEAST x. x < e_length e \<and> \<phi> i x \<down>\<noteq> e_nth e x)"
    using assms inconsist_converg by presburger
qed

lemma least_bounded_Suc:
  assumes "\<exists>x. x < upper \<and> P x"
  shows "(LEAST x. x < upper \<and> P x) = (LEAST x. x < Suc upper \<and> P x)"
proof -
  let ?Q = "\<lambda>x. x < upper \<and> P x"
  let ?x = "Least ?Q"
  from assms have "?x < upper \<and> P ?x"
    using LeastI_ex[of ?Q] by simp
  then have 1: "?x < Suc upper \<and> P ?x" by simp
  from assms have 2: "\<forall>y<?x. \<not> P y"
    using Least_le[of ?Q] not_less_Least by fastforce
  have "(LEAST x. x < Suc upper \<and> P x) = ?x"
  proof (rule Least_equality)
    show "?x < Suc upper \<and> P ?x" using 1 2 by blast
    show "\<And>y. y < Suc upper \<and> P y \<Longrightarrow> ?x \<le> y"
      using 1 2 leI by blast
  qed
  then show ?thesis ..
qed

lemma least_bounded_gr:
  fixes P :: "nat \<Rightarrow> bool" and m :: nat
  assumes "\<exists>x. x < upper \<and> P x"
  shows "(LEAST x. x < upper \<and> P x) = (LEAST x. x < upper + m \<and> P x)"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  moreover have "\<exists>x. x < upper + m \<and> P x"
    using assms trans_less_add1 by blast
  ultimately show ?case using least_bounded_Suc by simp
qed

lemma inconsist_init_converg_less:
  assumes "f \<in> \<R>"
    and "\<phi> i \<in> \<R>"
    and "inconsist i (f \<triangleright> n) \<down>"
    and "the (inconsist i (f \<triangleright> n)) < Suc n"
  shows "inconsist i (f \<triangleright> (n + m)) = inconsist i (f \<triangleright> n)"
proof -
  have phi_i_total: "\<phi> i x \<down>" for x
    using assms by simp
  moreover have f_nth: "f x \<down>= e_nth (f \<triangleright> n) x" if "x < Suc n" for x n
    using that assms(1) by simp
  ultimately have "(\<phi> i x \<noteq> f x) = (\<phi> i x \<down>\<noteq> e_nth (f \<triangleright> n) x)" if "x < Suc n" for x n
    using that by simp
  then have cond: "(x < Suc n \<and> \<phi> i x \<noteq> f x) =
      (x < e_length (f \<triangleright> n) \<and> \<phi> i x \<down>\<noteq> e_nth (f \<triangleright> n) x)" for x n
    using length_init by metis
  then have
    1: "\<exists>x<Suc n. \<phi> i x \<noteq> f x" and
    2: "inconsist i (f \<triangleright> n) \<down>= (LEAST x. x < Suc n \<and> \<phi> i x \<noteq> f x)"
    using assms(3,4) inconsist_converg_less[of i "f \<triangleright> n"] by simp_all
  then have 3: "\<exists>x<Suc (n + m). \<phi> i x \<noteq> f x"
    using not_add_less1 by fastforce
  then have "\<exists>x<Suc (n + m). \<phi> i x \<down>\<noteq> e_nth (f \<triangleright> (n + m)) x"
    using cond by blast
  then have "\<exists>x<e_length (f \<triangleright> (n + m)). \<phi> i x \<down>\<noteq> e_nth (f \<triangleright> (n + m)) x"
    by simp
  moreover have 4: "inconsist i (f \<triangleright> (n + m)) \<down>"
    using assms(2) R1_imp_total1 inconsist_def by simp
  ultimately have "inconsist i (f \<triangleright> (n + m)) \<down>=
      (LEAST x. x < e_length (f \<triangleright> (n + m)) \<and> \<phi> i x \<down>\<noteq> e_nth (f \<triangleright> (n + m)) x)"
    using inconsist_converg[OF 4] by simp
  then have 5: "inconsist i (f \<triangleright> (n + m)) \<down>= (LEAST x. x < Suc (n + m) \<and> \<phi> i x \<noteq> f x)"
    using cond[of _ "n + m"] by simp
  then have "(LEAST x. x < Suc n \<and> \<phi> i x \<noteq> f x) =
      (LEAST x. x < Suc n + m \<and> \<phi> i x \<noteq> f x)"
    using least_bounded_gr[where ?upper="Suc n"] 1 3 by simp
  then show ?thesis using 2 5 by simp
qed

definition "r_inconsist \<equiv>
  let
    f = Cn 2 r_length [Id 2 1];
    g = Cn 4 r_ifless
      [Id 4 1,
       Cn 4 r_length [Id 4 3],
       Id 4 1,
       Cn 4 r_ifeq
        [Cn 4 r_phi [Id 4 2, Id 4 0],
         Cn 4 r_nth [Id 4 3, Id 4 0],
         Id 4 1,
         Id 4 0]]
   in Cn 2 (Pr 2 f g) [Cn 2 r_length [Id 2 1], Id 2 0, Id 2 1]"

lemma r_inconsist_recfn: "recfn 2 r_inconsist"
  unfolding r_inconsist_def by simp

lemma r_inconsist: "eval r_inconsist [i, e] = inconsist i e"
proof -
  define f where "f = Cn 2 r_length [Id 2 1]"
  define len where "len = Cn 4 r_length [Id 4 3]"
  define nth where "nth = Cn 4 r_nth [Id 4 3, Id 4 0]"
  define ph where "ph = Cn 4 r_phi [Id 4 2, Id 4 0]"
  define g where
    "g = Cn 4 r_ifless [Id 4 1, len, Id 4 1, Cn 4 r_ifeq [ph, nth, Id 4 1, Id 4 0]]"
  have "recfn 2 f"
    unfolding f_def by simp
  have f: "eval f [i, e] \<down>= e_length e"
    unfolding f_def by simp
  have "recfn 4 len"
    unfolding len_def by simp
  have len: "eval len [j, v, i, e] \<down>= e_length e" for j v
    unfolding len_def by simp
  have "recfn 4 nth"
    unfolding nth_def by simp
  have nth: "eval nth [j, v, i, e] \<down>= e_nth e j" for j v
    unfolding nth_def by simp
  have "recfn 4 ph"
    unfolding ph_def by simp
  have ph: "eval ph [j, v, i, e] = \<phi> i j" for j v
    unfolding ph_def using phi_def by simp
  have "recfn 4 g"
    unfolding g_def using \<open>recfn 4 nth\<close> \<open>recfn 4 ph\<close> \<open>recfn 4 len\<close> by simp
  have g_diverg: "eval g [j, v, i, e] \<up>" if "eval ph [j, v, i, e] \<up>" for j v
    unfolding g_def using that \<open>recfn 4 nth\<close> \<open>recfn 4 ph\<close> \<open>recfn 4 len\<close> by simp
  have g_converg: "eval g [j, v, i, e] \<down>=
      (if v < e_length e then v else if \<phi> i j \<down>= e_nth e j then v else j)"
      if "eval ph [j, v, i, e] \<down>" for j v
    unfolding g_def using that \<open>recfn 4 nth\<close> \<open>recfn 4 ph\<close> \<open>recfn 4 len\<close> len nth ph
    by auto
  define h where "h \<equiv> Pr 2 f g"
  then have "recfn 3 h"
    by (simp add: \<open>recfn 2 f\<close> \<open>recfn 4 g\<close>)

  let ?invariant = "\<lambda>j i e.
    (if \<exists>x<j. \<phi> i x \<up> then None
     else if \<exists>x<j. \<phi> i x \<down>\<noteq> e_nth e x
          then Some (LEAST x. x < j \<and> \<phi> i x \<down>\<noteq> e_nth e x)
          else Some (e_length e))"

  have "eval h [j, i, e] = ?invariant j i e" if "j \<le> e_length e" for j
    using that
  proof (induction j)
    case 0
    then show ?case unfolding h_def using \<open>recfn 2 f\<close> f \<open>recfn 4 g\<close> by simp
  next
    case (Suc j)
    then have j_less: "j < e_length e" by simp
    then have j_le: "j \<le> e_length e" by simp
    show ?case
    proof (cases "eval h [j, i, e] \<up>")
      case True
      then have "\<exists>x<j. \<phi> i x \<up>"
        using j_le Suc.IH by (metis option.simps(3))
      then have "\<exists>x<Suc j. \<phi> i x \<up>"
        using less_SucI by blast
      moreover have h: "eval h [Suc j, i, e] \<up>"
        using True h_def \<open>recfn 3 h\<close> by simp
      ultimately show ?thesis by simp
    next
      case False
      with Suc.IH j_le have h_j: "eval h [j, i, e] =
        (if \<exists>x<j. \<phi> i x \<down>\<noteq> e_nth e x
         then Some (LEAST x. x < j \<and> \<phi> i x \<down>\<noteq> e_nth e x)
         else Some (e_length e))"
        by presburger
      then have the_h_j: "the (eval h [j, i, e]) =
        (if \<exists>x<j. \<phi> i x \<down>\<noteq> e_nth e x
         then LEAST x. x < j \<and> \<phi> i x \<down>\<noteq> e_nth e x
         else e_length e)"
         (is "_ = ?v")
        by auto
      have h_Suc: "eval h [Suc j, i, e] = eval g [j, the (eval h [j, i, e]), i, e]"
        using False h_def \<open>recfn 4 g\<close> \<open>recfn 2 f\<close> by auto
      show ?thesis
      proof (cases "\<phi> i j \<up>")
        case True
        with ph g_diverg h_Suc show ?thesis by auto
      next
        case False
        with h_Suc have "eval h [Suc j, i, e] \<down>=
          (if ?v < e_length e then ?v
           else if \<phi> i j \<down>= e_nth e j then ?v else j)"
          (is "_ \<down>= ?lhs")
          using g_converg ph the_h_j by simp
        moreover have "?invariant (Suc j) i e \<down>=
          (if \<exists>x<Suc j. \<phi> i x \<down>\<noteq> e_nth e x
           then LEAST x. x < Suc j \<and> \<phi> i x \<down>\<noteq> e_nth e x
           else e_length e)"
          (is "_ \<down>= ?rhs")
        proof -
          from False have "\<phi> i j \<down>" by simp
          moreover have "\<not> (\<exists>x<j. \<phi> i x \<up>)"
            by (metis (no_types, lifting) Suc.IH h_j j_le option.simps(3))
          ultimately have "\<not> (\<exists>x<Suc j. \<phi> i x \<up>)"
            using less_Suc_eq by auto
          then show ?thesis by auto
        qed
        moreover have "?lhs = ?rhs"
        proof (cases "?v < e_length e")
          case True
          then have
            ex_j: "\<exists>x<j. \<phi> i x \<down>\<noteq> e_nth e x" and
            v_eq: "?v = (LEAST x. x < j \<and> \<phi> i x \<down>\<noteq> e_nth e x)"
            by presburger+
          with True have "?lhs = ?v" by simp
          from ex_j have "\<exists>x<Suc j. \<phi> i x \<down>\<noteq> e_nth e x"
            using less_SucI by blast
          then have "?rhs = (LEAST x. x < Suc j \<and> \<phi> i x \<down>\<noteq> e_nth e x)" by simp
          with True v_eq ex_j show ?thesis
            using least_bounded_Suc[of j "\<lambda>x. \<phi> i x \<down>\<noteq> e_nth e x"] by simp
        next
          case False
          then have not_ex: "\<not> (\<exists>x<j. \<phi> i x \<down>\<noteq> e_nth e x)"
            using Least_le[of "\<lambda>x. x < j \<and> \<phi> i x \<down>\<noteq> e_nth e x"] j_le
            by (smt leD le_less_linear le_trans)
          then have "?v = e_length e" by argo
          with False have lhs: "?lhs = (if \<phi> i j \<down>= e_nth e j then e_length e else j)"
            by simp
          show ?thesis
          proof (cases "\<phi> i j \<down>= e_nth e j")
            case True
            then have "\<not> (\<exists>x<Suc j. \<phi> i x \<down>\<noteq> e_nth e x)"
              using less_SucE not_ex by blast
            then have "?rhs = e_length e" by argo
            moreover from True have "?lhs = e_length e"
              using lhs by simp
            ultimately show ?thesis by simp
          next case False
            then have "\<phi> i j \<down>\<noteq> e_nth e j"
              using \<open>\<phi> i j \<down>\<close> by simp
            with not_ex have "(LEAST x. x<Suc j \<and> \<phi> i x \<down>\<noteq> e_nth e x) = j"
              using LeastI[of "\<lambda>x. x<Suc j \<and> \<phi> i x \<down>\<noteq> e_nth e x" j] less_Suc_eq
              by blast
            then have "?rhs = j"
              using \<open>\<phi> i j \<down>\<noteq> e_nth e j\<close> by (meson lessI)
            moreover from False lhs have "?lhs = j" by simp
            ultimately show ?thesis by simp
          qed
        qed
        ultimately show ?thesis by simp
      qed
    qed
  qed
  then have "eval h [e_length e, i, e] = ?invariant (e_length e) i e"
    by auto
  then have "eval h [e_length e, i, e] = inconsist i e"
    using inconsist_def by simp
  moreover have "eval (Cn 2 (Pr 2 f g) [Cn 2 r_length [Id 2 1], Id 2 0, Id 2 1]) [i, e] =
      eval h [e_length e, i, e]"
    using \<open>recfn 4 g\<close> \<open>recfn 2 f\<close> h_def by auto
  ultimately show ?thesis
    unfolding r_inconsist_def by (simp add: f_def g_def len_def nth_def ph_def)
qed

lemma inconsist_for_total:
  assumes "total1 (\<phi> i)"
  shows "inconsist i e \<down>=
    (if \<exists>x<e_length e. \<phi> i x \<down>\<noteq> e_nth e x
     then LEAST x. x < e_length e \<and> \<phi> i x \<down>\<noteq> e_nth e x
     else e_length e)"
  unfolding inconsist_def using assms total1_def by (auto; blast)

lemma inconsist_for_V01:
  assumes "f \<in> V\<^sub>0\<^sub>1" and "k = amalgamate (the (f 0)) (the (f 1))"
  shows "inconsist k e \<down>=
    (if \<exists>x<e_length e. \<phi> k x \<down>\<noteq> e_nth e x
     then LEAST x. x < e_length e \<and> \<phi> k x \<down>\<noteq> e_nth e x
     else e_length e)"
proof -
  have "\<phi> k \<in> \<R>"
    using amalgamation_V01_R1[OF assms(1)] assms(2) amalgamate by simp
  then have "total1 (\<phi> k)" by simp
  with inconsist_for_total[of k] show ?thesis by simp
qed

text \<open>The next function computes Gödel numbers of functions consistent
with a given prefix. The strategy will use these as consistent auxiliary
hypotheses when receiving a prefix of length one.\<close>

definition "r_auxhyp \<equiv> Cn 1 (r_smn 1 1) [r_const (encode r_prenum), Id 1 0]"

lemma r_auxhyp_prim: "prim_recfn 1 r_auxhyp"
  unfolding r_auxhyp_def by simp

lemma r_auxhyp: "\<phi> (the (eval r_auxhyp [e])) = prenum e"
proof
  fix x
  let ?p = "encode r_prenum"
  let ?p = "encode r_prenum"
  have "eval r_auxhyp [e] = eval (r_smn 1 1) [?p, e]"
    unfolding r_auxhyp_def by simp
  then have "eval r_auxhyp [e] \<down>= smn 1 ?p [e]"
    by (simp add: r_smn)
  also have "... \<down>= encode (Cn 1 (r_universal (1 + length [e]))
      (r_constn (1 - 1) ?p #
       map (r_constn (1 - 1)) [e] @ map (recf.Id 1) [0..<1]))"
    using smn[of 1 ?p "[e]"] by simp
  also have "... \<down>= encode (Cn 1 (r_universal (1 + 1))
      (r_constn 0 ?p # map (r_constn 0) [e] @ [Id 1 0]))"
    by simp
  also have "... \<down>= encode (Cn 1 (r_universal 2)
      (r_constn 0 ?p # map (r_constn 0) [e] @ [Id 1 0]))"
    by (metis one_add_one)
  also have "... \<down>= encode (Cn 1 (r_universal 2) [r_constn 0 ?p, r_constn 0 e, Id 1 0])"
    by simp
  also have "... \<down>= encode (Cn 1 (r_universal 2) [r_const ?p, r_const e, Id 1 0])"
    using r_constn_def by simp
  finally have "eval r_auxhyp [e] \<down>=
    encode (Cn 1 (r_universal 2) [r_const ?p, r_const e, Id 1 0])" .
  moreover have "\<phi> (the (eval r_auxhyp [e])) x = eval r_phi [the (eval r_auxhyp [e]), x]"
    by (simp add: phi_def)
  ultimately have "\<phi> (the (eval r_auxhyp [e])) x =
      eval r_phi [encode (Cn 1 (r_universal 2) [r_const ?p, r_const e, Id 1 0]), x]"
      (is "_ = eval r_phi [encode ?f, x]")
    by simp
  then have "\<phi> (the (eval r_auxhyp [e])) x =
      eval (Cn 1 (r_universal 2) [r_const ?p, r_const e, Id 1 0]) [x]"
    using r_phi_def r_universal[of ?f 1 "[x]"] by simp
  then have "\<phi> (the (eval r_auxhyp [e])) x = eval (r_universal 2) [?p, e, x]"
    by simp
  then have "\<phi> (the (eval r_auxhyp [e])) x = eval r_prenum [e, x]"
    using r_universal by simp
  then show "\<phi> (the (eval r_auxhyp [e])) x = prenum e x" by simp
qed

definition auxhyp :: partial1 where
  "auxhyp e \<equiv> eval r_auxhyp [e]"

lemma auxhyp_prenum: "\<phi> (the (auxhyp e)) = prenum e"
  using auxhyp_def r_auxhyp by metis

lemma auxhyp_in_R1: "auxhyp \<in> \<R>"
  using auxhyp_def Mn_free_imp_total R1I r_auxhyp_prim by metis

text \<open>Now we can define our consistent learning strategy for @{term "V\<^sub>0\<^sub>1"}.\<close>

definition "r_sv01 \<equiv>
  let
    at0 = Cn 1 r_nth [Id 1 0, Z];
    at1 = Cn 1 r_nth [Id 1 0, r_const 1];
    m = Cn 1 r_amalgamate [at0, at1];
    c = Cn 1 r_inconsist [m, Id 1 0];
    p = Cn 1 r_pdec1 [Cn 1 r_parallel [at0, at1, c]];
    g = Cn 1 r_ifeq [c, r_length, m, Cn 1 r_ifz [p, at1, at0]]
  in Cn 1 (r_lifz r_auxhyp g) [Cn 1 r_eq [r_length, r_const 1], Id 1 0]"

lemma r_sv01_recfn: "recfn 1 r_sv01"
  unfolding r_sv01_def using r_auxhyp_prim r_inconsist_recfn r_amalgamate_recfn
  by (simp add: Let_def)

definition sv01 :: partial1 ("s\<^bsub>01\<^esub>")where
  "sv01 e \<equiv> eval r_sv01 [e]"

lemma sv01_in_P1: "s\<^bsub>01\<^esub> \<in> \<P>"
  using sv01_def r_sv01_recfn P1I by presburger

text \<open>We are interested in the behavior of @{term "s\<^bsub>01\<^esub>"} only on
prefixes of functions in @{term "V\<^sub>0\<^sub>1"}. This behavior is linked
to the amalgamation of $f(0)$ and $f(1)$, where $f$ is the function
to be learned.\<close>

abbreviation amalg01 :: "partial1 \<Rightarrow> nat" where
  "amalg01 f \<equiv> amalgamate (the (f 0)) (the (f 1))"

lemma sv01:
  assumes "f \<in> V\<^sub>0\<^sub>1"
  shows "s\<^bsub>01\<^esub> (f \<triangleright> 0) = auxhyp (f \<triangleright> 0)"
    and "n \<noteq> 0 \<Longrightarrow>
      inconsist (amalg01 f) (f \<triangleright> n) \<down>= Suc n \<Longrightarrow>
      s\<^bsub>01\<^esub> (f \<triangleright> n) \<down>= amalg01 f"
    and "n \<noteq> 0 \<Longrightarrow>
      the (inconsist (amalg01 f) (f \<triangleright> n)) < Suc n \<Longrightarrow>
      pdec1 (the (parallel (the (f 0)) (the (f 1)) (the (inconsist (amalg01 f) (f \<triangleright> n))))) = 0 \<Longrightarrow>
      s\<^bsub>01\<^esub> (f \<triangleright> n) = f 1"
    and "n \<noteq> 0 \<Longrightarrow>
      the (inconsist (amalg01 f) (f \<triangleright> n)) < Suc n \<Longrightarrow>
      pdec1 (the (parallel (the (f 0)) (the (f 1)) (the (inconsist (amalg01 f) (f \<triangleright> n))))) \<noteq> 0 \<Longrightarrow>
      s\<^bsub>01\<^esub> (f \<triangleright> n) = f 0"
proof -
  have f_total: "\<And>x. f x \<down>"
    using assms V01_def R1_imp_total1 by blast
  define at0 where "at0 = Cn 1 r_nth [Id 1 0, Z]"
  define at1 where "at1 = Cn 1 r_nth [Id 1 0, r_const 1]"
  define m where  "m = Cn 1 r_amalgamate [at0, at1]"
  define c where "c = Cn 1 r_inconsist [m, Id 1 0]"
  define p where "p = Cn 1 r_pdec1 [Cn 1 r_parallel [at0, at1, c]]"
  define g where "g = Cn 1 r_ifeq [c, r_length, m, Cn 1 r_ifz [p, at1, at0]]"
  have "recfn 1 g"
    unfolding g_def p_def c_def m_def at1_def at0_def
    using r_auxhyp_prim r_inconsist_recfn r_amalgamate_recfn
    by simp
  have "eval (Cn 1 r_eq [r_length, r_const 1]) [f \<triangleright> 0] \<down>= 0"
    by simp
  then have "eval r_sv01 [f \<triangleright> 0] = eval r_auxhyp [f \<triangleright> 0]"
    unfolding r_sv01_def using \<open>recfn 1 g\<close> c_def g_def m_def p_def r_auxhyp_prim
    by (auto simp add: Let_def)
  then show "s\<^bsub>01\<^esub> (f \<triangleright> 0) = auxhyp (f \<triangleright> 0)"
    by (simp add: auxhyp_def sv01_def)

  have sv01: "s\<^bsub>01\<^esub> (f \<triangleright> n) = eval g [f \<triangleright> n]" if "n \<noteq> 0"
  proof -
    have *: "eval (Cn 1 r_eq [r_length, r_const 1]) [f \<triangleright> n] \<down>\<noteq> 0"
      (is "?r_eq \<down>\<noteq> 0")
      using that by simp
    moreover have "recfn 2 (r_lifz r_auxhyp g)"
      using \<open>recfn 1 g\<close> r_auxhyp_prim by simp
    moreover have "eval r_sv01 [f \<triangleright> n] =
        eval (Cn 1 (r_lifz r_auxhyp g) [Cn 1 r_eq [r_length, r_const 1], Id 1 0]) [f \<triangleright> n]"
      using r_sv01_def by (metis at0_def at1_def c_def g_def m_def p_def)
    ultimately have "eval r_sv01 [f \<triangleright> n] = eval (r_lifz r_auxhyp g) [the ?r_eq, f \<triangleright> n]"
      by simp
    then have "eval r_sv01 [f \<triangleright> n] = eval g [f \<triangleright> n]"
      using "*" \<open>recfn 1 g\<close> r_auxhyp_prim by auto
    then show ?thesis by (simp add: sv01_def that)
  qed

  have "recfn 1 at0"
    unfolding at0_def by simp
  have at0: "eval at0 [f \<triangleright> n] \<down>= the (f 0)"
    unfolding at0_def by simp
  have "recfn 1 at1"
    unfolding at1_def by simp
  have at1: "n \<noteq> 0 \<Longrightarrow> eval at1 [f \<triangleright> n] \<down>= the (f 1)"
    unfolding at1_def by simp
  have "recfn 1 m"
    unfolding m_def at0_def at1_def using r_amalgamate_recfn by simp
  have m: "n \<noteq> 0 \<Longrightarrow> eval m [f \<triangleright> n] \<down>= amalg01 f"
      (is "_ \<Longrightarrow> _ \<down>= ?m")
    unfolding m_def at0_def at1_def
    using at0 at1 amalgamate r_amalgamate r_amalgamate_recfn by simp
  then have c: "n \<noteq> 0 \<Longrightarrow> eval c [f \<triangleright> n] = inconsist (amalg01 f) (f \<triangleright> n)"
      (is "_ \<Longrightarrow> _ = ?c")
    unfolding c_def using r_inconsist_recfn \<open>recfn 1 m\<close> r_inconsist by auto
  then have c_converg: "n \<noteq> 0 \<Longrightarrow> eval c [f \<triangleright> n] \<down>"
    using inconsist_for_V01[OF assms] by simp
  have "recfn 1 c"
    unfolding c_def using \<open>recfn 1 m\<close> r_inconsist_recfn by simp

  have par: "n \<noteq> 0 \<Longrightarrow>
      eval (Cn 1 r_parallel [at0, at1, c]) [f \<triangleright> n] = parallel (the (f 0)) (the (f 1)) (the ?c)"
      (is "_ \<Longrightarrow> _ = ?par")
    using at0 at1 c c_converg m r_parallel' \<open>recfn 1 at0\<close> \<open>recfn 1 at1\<close> \<open>recfn 1 c\<close>
    by simp
  with parallel_converg_V01[OF assms] have
      par_converg: "n \<noteq> 0 \<Longrightarrow> eval (Cn 1 r_parallel [at0, at1, c]) [f \<triangleright> n] \<down>"
    by simp
  then have p_converg: "n \<noteq> 0 \<Longrightarrow> eval p [f \<triangleright> n] \<down>"
    unfolding p_def using at0 at1 c_converg \<open>recfn 1 at0\<close> \<open>recfn 1 at1\<close> \<open>recfn 1 c\<close>
    by simp
  have p: "n \<noteq> 0 \<Longrightarrow> eval p [f \<triangleright> n] \<down>= pdec1 (the ?par)"
    unfolding p_def
    using at0 at1 c_converg \<open>recfn 1 at0\<close> \<open>recfn 1 at1\<close> \<open>recfn 1 c\<close> par par_converg
    by simp
  have "recfn 1 p"
    unfolding p_def using \<open>recfn 1 at0\<close> \<open>recfn 1 at1\<close> \<open>recfn 1 m\<close> \<open>recfn 1 c\<close>
    by simp

  let ?r = "Cn 1 r_ifz [p, at1, at0]"
  have r: "n \<noteq> 0 \<Longrightarrow> eval ?r [f \<triangleright> n] = (if pdec1 (the ?par) = 0 then f 1 else f 0)"
    using at0 at1 c_converg \<open>recfn 1 at0\<close> \<open>recfn 1 at1\<close> \<open>recfn 1 c\<close>
      \<open>recfn 1 m\<close> \<open>recfn 1 p\<close> p f_total
    by fastforce

  have g: "n \<noteq> 0 \<Longrightarrow>
      eval g [f \<triangleright> n] \<down>=
        (if the ?c = e_length (f \<triangleright> n)
         then ?m else the (eval (Cn 1 r_ifz [p, at1, at0]) [f \<triangleright> n]))"
    unfolding g_def
    using \<open>recfn 1 p\<close> \<open>recfn 1 at0\<close> \<open>recfn 1 at1\<close> \<open>recfn 1 c\<close> \<open>recfn 1 m\<close>
      p_converg at1 at0 c c_converg m
    by simp
  {
    assume "n \<noteq> 0" and "?c \<down>= Suc n"
    moreover have "e_length (f \<triangleright> n) = Suc n" by simp
    ultimately have "eval g [f \<triangleright> n] \<down>= ?m" using g by simp
    then show "s\<^bsub>01\<^esub> (f \<triangleright> n) \<down>= amalg01 f"
      using sv01[OF \<open>n \<noteq> 0\<close>] by simp
  next
    assume "n \<noteq> 0" and "the ?c < Suc n" and "pdec1 (the ?par) = 0"
    with g r f_total have "eval g [f \<triangleright> n] = f 1" by simp
    then show "s\<^bsub>01\<^esub> (f \<triangleright> n) = f 1"
      using sv01[OF \<open>n \<noteq> 0\<close>] by simp
  next
    assume "n \<noteq> 0" and "the ?c < Suc n" and "pdec1 (the ?par) \<noteq> 0"
    with g r f_total have "eval g [f \<triangleright> n] = f 0" by simp
    then show "s\<^bsub>01\<^esub> (f \<triangleright> n) = f 0"
      using sv01[OF \<open>n \<noteq> 0\<close>] by simp
  }
qed

text \<open>Part of the correctness of @{term sv01} is convergence on
prefixes of functions in @{term "V\<^sub>0\<^sub>1"}.\<close>

lemma sv01_converg_V01:
  assumes "f \<in> V\<^sub>0\<^sub>1"
  shows "s\<^bsub>01\<^esub> (f \<triangleright> n) \<down>"
proof (cases "n = 0")
  case True
  then show ?thesis
    using assms sv01 R1_imp_total1 auxhyp_in_R1 by simp
next
  case n_gr_0: False
  show ?thesis
  proof (cases "inconsist (amalg01 f) (f \<triangleright> n) \<down>= Suc n")
    case True
    then show ?thesis
    using n_gr_0 assms sv01 by simp
  next
    case False
    then have "the (inconsist (amalg01 f) (f \<triangleright> n)) < Suc n"
      using assms inconsist_bounded inconsist_for_V01 length_init
      by (metis (no_types, lifting) le_neq_implies_less option.collapse option.simps(3))
    then show ?thesis
      using n_gr_0 assms sv01 R1_imp_total1 total1E V01_def
      by (metis (no_types, lifting) mem_Collect_eq)
  qed
qed

text \<open>Another part of the correctness of @{term sv01} is its hypotheses
being consistent on prefixes of functions in @{term "V\<^sub>0\<^sub>1"}.\<close>

lemma sv01_consistent_V01:
  assumes "f \<in> V\<^sub>0\<^sub>1"
  shows "\<forall>x\<le>n. \<phi> (the (s\<^bsub>01\<^esub> (f \<triangleright> n))) x = f x"
proof (cases "n = 0")
  case True
  then have "s\<^bsub>01\<^esub> (f \<triangleright> n) = auxhyp (f \<triangleright> n)"
    using sv01[OF assms] by simp
  then have "\<phi> (the (s\<^bsub>01\<^esub> (f \<triangleright> n))) = prenum (f \<triangleright> n)"
    using auxhyp_prenum by simp
  then show ?thesis
    using R1_imp_total1 total1E assms by (simp add: V01_def)
next
  case n_gr_0: False
  let ?m = "amalg01 f"
  let ?e = "f \<triangleright> n"
  let ?c = "the (inconsist ?m ?e)"
  have c: "inconsist ?m ?e \<down>"
    using assms inconsist_for_V01 by blast
  show ?thesis
  proof (cases "inconsist ?m ?e \<down>= Suc n")
    case True
    then show ?thesis
      using assms n_gr_0 sv01 R1_imp_total1 total1E V01_def is_init_of_def
        inconsist_consistent not_initial_imp_not_eq length_init inconsist_converg_eq 
      by (metis (no_types, lifting) le_imp_less_Suc mem_Collect_eq option.sel)
  next
    case False
    then have less: "the (inconsist ?m ?e) < Suc n"
      using c assms inconsist_bounded inconsist_for_V01 length_init
      by (metis le_neq_implies_less option.collapse)
    then have "the (inconsist ?m ?e) < e_length ?e"
      by auto
    then have
      "\<exists>x<e_length ?e. \<phi> ?m x \<down>\<noteq> e_nth ?e x"
      "inconsist ?m ?e \<down>= (LEAST x. x < e_length ?e \<and> \<phi> ?m x \<down>\<noteq> e_nth ?e x)"
      (is "_ \<down>= Least ?P")
      using inconsist_converg_less[OF c] by simp_all
    then have "?P ?c" and "\<And>x. x < ?c \<Longrightarrow> \<not> ?P x"
      using LeastI_ex[of ?P] not_less_Least[of _ ?P] by (auto simp del: e_nth)
    then have "\<phi> ?m ?c \<noteq> f ?c" by auto
    then have "amalgamation (the (f 0)) (the (f 1)) ?c \<noteq> f ?c"
      using amalgamate by simp
    then have *: "Some (pdec2 (the (parallel (the (f 0)) (the (f 1)) ?c))) \<noteq> f ?c"
      using amalgamation_def by (metis assms parallel_converg_V01)
    let ?p = "parallel (the (f 0)) (the (f 1)) ?c"
    show ?thesis
    proof (cases "pdec1 (the ?p) = 0")
      case True
      then have "\<phi> (the (f 0)) ?c \<down>= pdec2 (the ?p)"
        using assms parallel_0 parallel_converg_V01
        by (metis option.collapse prod.collapse prod_decode_inverse)
      then have "\<phi> (the (f 0)) ?c \<noteq> f ?c"
        using * by simp
      then have "\<phi> (the (f 0)) \<noteq> f" by auto
      then have "\<phi> (the (f 1)) = f"
        using assms V01_def by auto
      moreover have "s\<^bsub>01\<^esub> (f \<triangleright> n) = f 1"
        using True less n_gr_0 sv01 assms by simp
      ultimately show ?thesis by simp
    next
      case False
      then have "pdec1 (the ?p) = 1"
        by (meson assms parallel_converg_V01 parallel_converg_pdec1_0_or_1)
      then have "\<phi> (the (f 1)) ?c \<down>= pdec2 (the ?p)"
        using assms parallel_1 parallel_converg_V01
        by (metis option.collapse prod.collapse prod_decode_inverse)
      then have "\<phi> (the (f 1)) ?c \<noteq> f ?c"
        using * by simp
      then have "\<phi> (the (f 1)) \<noteq> f" by auto
      then have "\<phi> (the (f 0)) = f"
        using assms V01_def by auto
      moreover from False less n_gr_0 sv01 assms have "s\<^bsub>01\<^esub> (f \<triangleright> n) = f 0"
        by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

text \<open>The final part of the correctness is @{term "sv01"} converging
for all functions in @{term "V\<^sub>0\<^sub>1"}.\<close>

lemma sv01_limit_V01:
 assumes "f \<in> V\<^sub>0\<^sub>1"
 shows "\<exists>i. \<forall>\<^sup>\<infinity>n. s\<^bsub>01\<^esub> (f \<triangleright> n) \<down>= i"
proof (cases "\<forall>n>0. s\<^bsub>01\<^esub> (f \<triangleright> n) \<down>= amalgamate (the (f 0)) (the (f 1))")
  case True
  then show ?thesis by (meson less_le_trans zero_less_one)
next
  case False
  then obtain n\<^sub>0 where n0:
    "n\<^sub>0 \<noteq> 0"
    "s\<^bsub>01\<^esub> (f \<triangleright> n\<^sub>0) \<down>\<noteq> amalg01 f"
    using \<open>f \<in> V\<^sub>0\<^sub>1\<close> sv01_converg_V01 by blast
  then have *: "the (inconsist (amalg01 f) (f \<triangleright> n\<^sub>0)) < Suc n\<^sub>0"
      (is "the (inconsist ?m (f \<triangleright> n\<^sub>0)) < Suc n\<^sub>0")
    using assms \<open>n\<^sub>0 \<noteq> 0\<close> sv01(2) inconsist_bounded inconsist_for_V01 length_init
    by (metis (no_types, lifting) le_neq_implies_less option.collapse option.simps(3))
  moreover have "f \<in> \<R>"
    using assms V01_def by auto
  moreover have "\<phi> ?m \<in> \<R>"
    using amalgamate amalgamation_V01_R1 assms by auto
  moreover have "inconsist ?m (f \<triangleright> n\<^sub>0) \<down>"
    using inconsist_for_V01 assms by blast
  ultimately have **: "inconsist ?m (f \<triangleright> (n\<^sub>0 + m)) = inconsist ?m (f \<triangleright> n\<^sub>0)" for m
    using inconsist_init_converg_less[of f ?m] by simp
  then have "the (inconsist ?m (f \<triangleright> (n\<^sub>0 + m))) < Suc n\<^sub>0 + m" for m
    using * by auto
  moreover have
    "pdec1 (the (parallel (the (f 0)) (the (f 1)) (the (inconsist ?m (f \<triangleright> (n\<^sub>0 + m)))))) =
      pdec1 (the (parallel (the (f 0)) (the (f 1)) (the (inconsist ?m (f \<triangleright> n\<^sub>0)))))"
    for m
    using ** by auto
  moreover have "n\<^sub>0 + m \<noteq> 0" for m
    using \<open>n\<^sub>0 \<noteq> 0\<close> by simp
  ultimately have "s\<^bsub>01\<^esub> (f \<triangleright> (n\<^sub>0 + m)) = s\<^bsub>01\<^esub> (f \<triangleright> n\<^sub>0)" for m
    using assms sv01 * \<open>n\<^sub>0 \<noteq> 0\<close> by (metis add_Suc)
  moreover define i where "i = s\<^bsub>01\<^esub> (f \<triangleright> n\<^sub>0)"
  ultimately have "\<forall>n\<ge>n\<^sub>0. s\<^bsub>01\<^esub> (f \<triangleright> n) = i"
    using nat_le_iff_add by auto
  then have "\<forall>n\<ge>n\<^sub>0. s\<^bsub>01\<^esub> (f \<triangleright> n) \<down>= the i"
    using n0(2) by simp
  then show ?thesis by auto
qed

lemma V01_learn_cons: "learn_cons \<phi> V\<^sub>0\<^sub>1 s\<^bsub>01\<^esub>"
proof (rule learn_consI2)
  show "environment \<phi> V\<^sub>0\<^sub>1 s\<^bsub>01\<^esub>"
    by (simp add: Collect_mono V01_def phi_in_P2 sv01_in_P1 sv01_converg_V01)
  show "\<And>f n. f \<in> V\<^sub>0\<^sub>1 \<Longrightarrow> \<forall>k\<le>n. \<phi> (the (s\<^bsub>01\<^esub> (f \<triangleright> n))) k = f k"
    using sv01_consistent_V01 .
  show "\<exists>i n\<^sub>0. \<forall>n\<ge>n\<^sub>0. s\<^bsub>01\<^esub> (f \<triangleright> n) \<down>= i" if "f \<in> V\<^sub>0\<^sub>1" for f
    using sv01_limit_V01 that by simp
qed

corollary V01_in_CONS: "V\<^sub>0\<^sub>1 \<in> CONS"
  using V01_learn_cons CONS_def by auto

text \<open>Now we can show the main result of this section, namely that
there is a consistently learnable class that cannot be learned consistently
by a total strategy. In other words, there is no Lemma~R for CONS.\<close>

lemma no_lemma_R_for_CONS: "\<exists>U. U \<in> CONS \<and> (\<not> (\<exists>s. s \<in> \<R> \<and> learn_cons \<phi> U s))"
  using V01_in_CONS V01_not_in_R_cons by auto

end