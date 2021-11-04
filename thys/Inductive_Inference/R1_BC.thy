section \<open>@{term "\<R>"} is not in BC\label{s:r1_bc}\<close>

theory R1_BC
  imports Lemma_R
    CP_FIN_NUM  (* for V0 *)
begin

text \<open>We show that @{term "U\<^sub>0 \<union> V\<^sub>0"} is not in BC,
which implies @{term "\<R> \<notin> BC"}.

The proof is by contradiction. Assume there is a strategy $S$ learning @{term
"U\<^sub>0 \<union> V\<^sub>0"} behaviorally correct in the limit with respect to our
standard Gödel numbering $\varphi$. Thanks to Lemma~R for BC we can assume
$S$ to be total. Then we construct a function in @{term "U\<^sub>0 \<union> V\<^sub>0"} for
which $S$ fails.

As usual, there is a computable process building prefixes of functions
$\psi_j$. For every $j$ it starts with the singleton prefix $b = [j]$ and
computes the next prefix from a given prefix $b$ as follows:

\begin{enumerate}
\item Simulate $\varphi_{S(b0^k)}(|b| + k)$ for increasing $k$ for an
  increasing number of steps.
\item Once a $k$ with $\varphi_{S(b0^k)}(|b| + k) = 0$ is found, extend the
  prefix by $0^k1$.
\end{enumerate}

There is always such a $k$ because by assumption $S$ learns $b0^\infty \in
U_0$ and thus outputs a hypothesis for $b0^\infty$ on almost all of its
prefixes. Therefore for almost all prefixes of the form $b0^k$, we have
$\varphi_{S(b0^k)} = b0^\infty$ and hence $\varphi_{S(b0^k)}(|b| + k) = 0$.
But Step~2 constructs $\psi_j$ such that $\psi_j(|b| + k) = 1$. Therefore $S$
does not hypothesize $\psi_j$ on the prefix $b0^k$ of $\psi_j$. And since the
process runs forever, $S$ outputs infinitely many incorrect hypotheses for
$\psi_j$ and thus does not learn $\psi_j$.

Applying Kleene's fixed-point theorem to @{term "\<psi> \<in> \<R>\<^sup>2"}
yields a $j$ with $\varphi_j = \psi_j$ and thus $\psi_j \in V_0$. But $S$
does not learn any $\psi_j$, contradicting our assumption.

The result @{prop "\<R> \<notin> BC"} can be obtained more directly by
running the process with the empty prefix, thereby constructing only one
function instead of a numbering. This function is in @{term R1}, and $S$
fails to learn it by the same reasoning as above. The stronger statement
about @{term "U\<^sub>0 \<union> V\<^sub>0"} will be exploited in
Section~\ref{s:union}.

In the following locale the assumption that $S$ learns @{term "U\<^sub>0"}
suffices for analyzing the process. However, in order to arrive at the
desired contradiction this assumption is too weak because the functions built
by the process are not in @{term "U\<^sub>0"}.\<close>

locale r1_bc =
  fixes s :: partial1
  assumes s_in_R1: "s \<in> \<R>" and s_learn_U0: "learn_bc \<phi> U\<^sub>0 s"
begin

lemma s_learn_prenum: "\<And>b. learn_bc \<phi> {prenum b} s"
  using s_learn_U0 U0_altdef learn_bc_closed_subseteq by blast

text \<open>A @{typ recf} for the strategy:\<close>

definition r_s :: recf where
  "r_s \<equiv> SOME rs. recfn 1 rs \<and>  total rs \<and> s = (\<lambda>x. eval rs [x])"

lemma r_s_recfn [simp]: "recfn 1 r_s"
  and r_s_total: "\<And>x. eval r_s [x] \<down>"
  and eval_r_s: "\<And>x. s x = eval r_s [x]"
  using r_s_def R1_SOME[OF s_in_R1, of r_s] by simp_all

text \<open>We begin with the function that finds the $k$ from Step~1 of the
construction of $\psi$.\<close>

definition "r_find_k \<equiv>
  let k = Cn 2 r_pdec1 [Id 2 0];
      r = Cn 2 r_result1
        [Cn 2 r_pdec2 [Id 2 0],
        Cn 2 r_s [Cn 2 r_append_zeros [Id 2 1, k]],
        Cn 2 r_add [Cn 2 r_length [Id 2 1], k]]
  in Cn 1 r_pdec1 [Mn 1 (Cn 2 r_eq [r, r_constn 1 1])]"

lemma r_find_k_recfn [simp]: "recfn 1 r_find_k"
  unfolding r_find_k_def by (simp add: Let_def)

text \<open>There is always a suitable $k$, since the strategy learns
$b0^\infty$ for all $b$.\<close>

lemma learn_bc_prenum_eventually_zero:
  "\<exists>k. \<phi> (the (s (e_append_zeros b k))) (e_length b + k) \<down>= 0"
proof -
  let ?f = "prenum b"
  have "\<exists>n\<ge>e_length b. \<phi> (the (s (?f \<triangleright> n))) = ?f"
    using learn_bcE s_learn_prenum by (meson le_cases singletonI)
  then obtain n where n: "n \<ge> e_length b" "\<phi> (the (s (?f \<triangleright> n))) = ?f"
    by auto
  define k where "k = Suc n - e_length b"
  let ?e = "e_append_zeros b k"
  have len: "e_length ?e = Suc n"
    using k_def n e_append_zeros_length by simp
  have "?f \<triangleright> n = ?e"
  proof -
    have "e_length ?e > 0"
      using len n(1) by simp
    moreover have "?f x \<down>= e_nth ?e x" for x
    proof (cases "x < e_length b")
      case True
      then show ?thesis using e_nth_append_zeros by simp
    next
      case False
      then have "?f x \<down>= 0" by simp
      moreover from False have "e_nth ?e x = 0"
        using e_nth_append_zeros_big by simp
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis using initI[of "?e"] len by simp
  qed
  with n(2) have "\<phi> (the (s ?e)) = ?f" by simp
  then have "\<phi> (the (s ?e)) (e_length ?e) \<down>= 0"
    using len n(1) by auto
  then show ?thesis using e_append_zeros_length by auto
qed

lemma if_eq_eq: "(if v = 1 then (0 :: nat) else 1) = 0 \<Longrightarrow> v = 1"
  by presburger

lemma r_find_k:
  shows "eval r_find_k [b] \<down>"
    and "let k = the (eval r_find_k [b])
           in \<phi> (the (s (e_append_zeros b k))) (e_length b + k) \<down>= 0"
proof -
  let ?k = "Cn 2 r_pdec1 [Id 2 0]"
  let ?argt = "Cn 2 r_pdec2 [Id 2 0]"
  let ?argi = "Cn 2 r_s [Cn 2 r_append_zeros [Id 2 1, ?k]]"
  let ?argx = "Cn 2 r_add [Cn 2 r_length [Id 2 1], ?k]"
  let ?r = "Cn 2 r_result1 [?argt, ?argi, ?argx]"
  define f where "f \<equiv>
    let k = Cn 2 r_pdec1 [Id 2 0];
        r = Cn 2 r_result1
             [Cn 2 r_pdec2 [Id 2 0],
              Cn 2 r_s [Cn 2 r_append_zeros [Id 2 1, k]],
              Cn 2 r_add [Cn 2 r_length [Id 2 1], k]]
    in Cn 2 r_eq [r, r_constn 1 1]"
  then have "recfn 2 f" by (simp add: Let_def)
  have "total r_s"
    by (simp add: r_s_total totalI1)
  then have "total f"
    unfolding f_def using Cn_total Mn_free_imp_total by (simp add: Let_def)

  have "eval ?argi [z, b] = s (e_append_zeros b (pdec1 z))" for z
    using r_append_zeros \<open>recfn 2 f\<close> eval_r_s by auto
  then have "eval ?argi [z, b] \<down>= the (s (e_append_zeros b (pdec1 z)))" for z
    using eval_r_s r_s_total by simp
  moreover have "recfn 2 ?r" using \<open>recfn 2 f\<close> by auto
  ultimately have r: "eval ?r [z, b] =
      eval r_result1 [pdec2 z, the (s (e_append_zeros b (pdec1 z))), e_length b + pdec1 z]"
      for z
    by simp
  then have f: "eval f [z, b] \<down>= (if the (eval ?r [z, b]) = 1 then 0 else 1)" for z
    using f_def \<open>recfn 2 f\<close> prim_recfn_total by (auto simp add: Let_def)

  have "\<exists>k. \<phi> (the (s (e_append_zeros b k))) (e_length b + k) \<down>= 0"
    using s_learn_prenum learn_bc_prenum_eventually_zero by auto
  then obtain k where "\<phi> (the (s (e_append_zeros b k))) (e_length b + k) \<down>= 0"
    by auto
  then obtain t where "eval r_result1 [t, the (s (e_append_zeros b k)), e_length b + k] \<down>= Suc 0"
    using r_result1_converg_phi(1) by blast
  then have t: "eval r_result1 [t, the (s (e_append_zeros b k)), e_length b + k] \<down>= Suc 0"
    by simp

  let ?z = "prod_encode (k, t)"
  have "eval ?r [?z, b] \<down>= Suc 0"
    using t r by (metis fst_conv prod_encode_inverse snd_conv)
  with f have fzb: "eval f [?z, b] \<down>= 0" by simp
  moreover have "eval (Mn 1 f) [b] =
    (if (\<exists>z. eval f ([z, b]) \<down>= 0)
     then Some (LEAST z. eval f [z, b] \<down>= 0)
     else None)"
    using eval_Mn_total[of 1 f "[b]"] \<open>total f\<close> \<open>recfn 2 f\<close> by simp
  ultimately have mn1f: "eval (Mn 1 f) [b] \<down>= (LEAST z. eval f [z, b] \<down>= 0)"
    by auto
  with fzb have "eval f [the (eval (Mn 1 f) [b]), b] \<down>= 0" (is "eval f [?zz, b] \<down>= 0")
    using \<open>total f\<close> \<open>recfn 2 f\<close> LeastI_ex[of "%z. eval f [z, b] \<down>= 0"] by auto
  moreover have "eval f [?zz, b] \<down>= (if the (eval ?r [?zz, b]) = 1 then 0 else 1)"
    using f by simp
  ultimately have "(if the (eval ?r [?zz, b]) = 1 then (0 :: nat) else 1) = 0" by auto
  then have "the (eval ?r [?zz, b]) = 1"
    using if_eq_eq[of "the (eval ?r [?zz, b])"] by simp
  then have
     "eval r_result1
        [pdec2 ?zz, the (s (e_append_zeros b (pdec1 ?zz))), e_length b + pdec1 ?zz] \<down>=
      1"
    using r r_result1_total r_result1_prim totalE
    by (metis length_Cons list.size(3) numeral_3_eq_3 option.collapse)
  then have *: "\<phi> (the (s (e_append_zeros b (pdec1 ?zz)))) (e_length b + pdec1 ?zz) \<down>= 0"
    by (simp add: r_result1_some_phi)

  define Mn1f where "Mn1f = Mn 1 f"
  then have "eval Mn1f [b] \<down>= ?zz"
    using mn1f by auto
  moreover have "recfn 1 (Cn 1 r_pdec1 [Mn1f])"
    using \<open>recfn 2 f\<close> Mn1f_def by simp
  ultimately have "eval (Cn 1 r_pdec1 [Mn1f]) [b] = eval r_pdec1 [the (eval (Mn1f) [b])]"
    by auto
  then have "eval (Cn 1 r_pdec1 [Mn1f]) [b] = eval r_pdec1 [?zz]"
    using Mn1f_def by blast
  then have 1: "eval (Cn 1 r_pdec1 [Mn1f]) [b] \<down>= pdec1 ?zz"
    by simp
  moreover have "recfn 1 (Cn 1 S [Cn 1 r_pdec1 [Mn1f]])"
    using \<open>recfn 2 f\<close> Mn1f_def by simp
  ultimately have "eval (Cn 1 S [Cn 1 r_pdec1 [Mn1f]]) [b] =
      eval S [the (eval (Cn 1 r_pdec1 [Mn1f]) [b])]"
    by simp
  then have "eval (Cn 1 S [Cn 1 r_pdec1 [Mn1f]]) [b] = eval S [pdec1 ?zz]"
    using 1 by simp
  then have "eval (Cn 1 S [Cn 1 r_pdec1 [Mn1f]]) [b] \<down>= Suc (pdec1 ?zz)"
    by simp
  moreover have "eval r_find_k [b] = eval (Cn 1 r_pdec1 [Mn1f]) [b]"
    unfolding r_find_k_def Mn1f_def f_def by metis
  ultimately have r_find_ksb: "eval r_find_k [b] \<down>= pdec1 ?zz"
    using 1 by simp
  then show "eval r_find_k [b] \<down>" by simp_all

  from r_find_ksb have "the (eval r_find_k [b]) = pdec1 ?zz"
    by simp
  moreover have "\<phi> (the (s (e_append_zeros b (pdec1 ?zz)))) (e_length b + pdec1 ?zz) \<down>= 0"
    using * by simp
  ultimately show "let k = the (eval r_find_k [b])
      in \<phi> (the (s (e_append_zeros b k))) (e_length b + k) \<down>= 0"
    by simp
qed

lemma r_find_k_total: "total r_find_k"
  by (simp add: s_learn_prenum r_find_k(1) totalI1)

text \<open>The following function represents one iteration of the
process.\<close>

abbreviation "r_next \<equiv>
  Cn 3 r_snoc [Cn 3 r_append_zeros [Id 3 1, Cn 3 r_find_k [Id 3 1]], r_constn 2 1]"

text \<open>Using @{term r_next} we define the function @{term r_prefixes}
that computes the prefix after every iteration of the process.\<close>

definition r_prefixes :: recf where
  "r_prefixes \<equiv> Pr 1 r_singleton_encode r_next"

lemma r_prefixes_recfn: "recfn 2 r_prefixes"
  unfolding r_prefixes_def by simp

lemma r_prefixes_total: "total r_prefixes"
proof -
  have "recfn 3 r_next" by simp
  then have "total r_next"
    using \<open>recfn 3 r_next\<close> r_find_k_total Cn_total Mn_free_imp_total by auto
  then show ?thesis
    by (simp add: Mn_free_imp_total Pr_total r_prefixes_def)
qed

lemma r_prefixes_0: "eval r_prefixes [0, j] \<down>= list_encode [j]"
  unfolding r_prefixes_def by simp

lemma r_prefixes_Suc:
  "eval r_prefixes [Suc n, j] \<down>=
    (let b = the (eval r_prefixes [n, j])
     in e_snoc (e_append_zeros b (the (eval r_find_k [b]))) 1)"
proof -
  have "recfn 3 r_next" by simp
  then have "total r_next"
    using \<open>recfn 3 r_next\<close> r_find_k_total Cn_total Mn_free_imp_total by auto
  have eval_next: "eval r_next [t, v, j] \<down>=
      e_snoc (e_append_zeros v (the (eval r_find_k [v]))) 1"
      for t v j
    using r_find_k_total \<open>recfn 3 r_next\<close> r_append_zeros by simp
  then have "eval r_prefixes [Suc n, j] = eval r_next [n, the (eval r_prefixes [n, j]), j]"
    using r_prefixes_total by (simp add: r_prefixes_def)
  then show "eval r_prefixes [Suc n, j] \<down>=
    (let b = the (eval r_prefixes [n, j])
     in e_snoc (e_append_zeros b (the (eval r_find_k [b]))) 1)"
    using eval_next by metis
qed

text \<open>Since @{term r_prefixes} is total, we can get away with
introducing a total function.\<close>

definition prefixes :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "prefixes j t \<equiv> the (eval r_prefixes [t, j])"

lemma prefixes_Suc:
  "prefixes j (Suc t) =
    e_snoc (e_append_zeros (prefixes j t) (the (eval r_find_k [prefixes j t]))) 1"
  unfolding prefixes_def using r_prefixes_Suc by (simp_all add: Let_def)

lemma prefixes_Suc_length:
  "e_length (prefixes j (Suc t)) =
    Suc (e_length (prefixes j t) + the (eval r_find_k [prefixes j t]))"
  using e_append_zeros_length prefixes_Suc by simp

lemma prefixes_length_mono: "e_length (prefixes j t) < e_length (prefixes j (Suc t))"
  using prefixes_Suc_length by simp

lemma prefixes_length_mono': "e_length (prefixes j t) \<le> e_length (prefixes j (t + d))"
proof (induction d)
  case 0
  then show ?case by simp
next
  case (Suc d)
  then show ?case using prefixes_length_mono le_less_trans by fastforce
qed

lemma prefixes_length_lower_bound: "e_length (prefixes j t) \<ge> Suc t"
proof (induction t)
  case 0
  then show ?case by (simp add: prefixes_def r_prefixes_0)
next
  case (Suc t)
  moreover have "Suc (e_length (prefixes j t)) \<le> e_length (prefixes j (Suc t))"
    using prefixes_length_mono by (simp add: Suc_leI)
  ultimately show ?case by simp
qed

lemma prefixes_Suc_nth:
  assumes "x < e_length (prefixes j t)"
  shows "e_nth (prefixes j t) x = e_nth (prefixes j (Suc t)) x"
proof -
  define k where "k = the (eval r_find_k [prefixes j t])"
  let ?u = "e_append_zeros (prefixes j t) k"
  have "prefixes j (Suc t) =
      e_snoc (e_append_zeros (prefixes j t) (the (eval r_find_k [prefixes j t]))) 1"
    using prefixes_Suc by simp
  with k_def have "prefixes j (Suc t) = e_snoc ?u 1"
    by simp
  then have "e_nth (prefixes j (Suc t)) x = e_nth (e_snoc ?u 1) x"
    by simp
  moreover have "x < e_length ?u"
    using assms e_append_zeros_length by auto
  ultimately have "e_nth (prefixes j (Suc t)) x = e_nth ?u x"
    using e_nth_snoc_small by simp
  moreover have "e_nth ?u x = e_nth (prefixes j t) x"
    using assms e_nth_append_zeros by simp
  ultimately show "e_nth (prefixes j t) x = e_nth (prefixes j (Suc t)) x"
    by simp
qed

lemma prefixes_Suc_last: "e_nth (prefixes j (Suc t)) (e_length (prefixes j (Suc t)) - 1) = 1"
  using prefixes_Suc by simp

lemma prefixes_le_nth:
  assumes "x < e_length (prefixes j t)"
  shows "e_nth (prefixes j t) x = e_nth (prefixes j (t + d)) x"
proof (induction d)
  case 0
  then show ?case by simp
next
  case (Suc d)
  have "x < e_length (prefixes j (t + d))"
    using s_learn_prenum assms prefixes_length_mono'
    by (simp add: less_eq_Suc_le order_trans_rules(23))
  then have "e_nth (prefixes j (t + d)) x = e_nth (prefixes j (t + Suc d)) x"
    using prefixes_Suc_nth by simp
  with Suc show ?case by simp
qed

text \<open>The numbering $\psi$ is defined via @{term[names_short] prefixes}.\<close>

definition psi :: partial2 ("\<psi>") where
  "\<psi> j x \<equiv> Some (e_nth (prefixes j (Suc x)) x)"

lemma psi_in_R2: "\<psi> \<in> \<R>\<^sup>2"
proof
  define r where "r \<equiv>  Cn 2 r_nth [Cn 2 r_prefixes [Cn 2 S [Id 2 1], Id 2 0], Id 2 1]"
  then have "recfn 2 r"
    using r_prefixes_recfn by simp
  then have "eval r [j, x] \<down>= e_nth (prefixes j (Suc x)) x" for j x
    unfolding r_def prefixes_def using r_prefixes_total r_prefixes_recfn e_nth by simp
  then have "eval r [j, x] = \<psi> j x" for j x
    unfolding psi_def by simp
  then show "\<psi> \<in> \<P>\<^sup>2"
    using \<open>recfn 2 r\<close> by auto
  show "total2 \<psi>"
    unfolding psi_def by auto
qed

lemma psi_eq_nth_prefixes:
  assumes "x < e_length (prefixes j t)"
  shows "\<psi> j x \<down>= e_nth (prefixes j t) x"
proof (cases "Suc x < t")
  case True
  have "x \<le> e_length (prefixes j x)"
    using prefixes_length_lower_bound by (simp add: Suc_leD)
  also have "... < e_length (prefixes j (Suc x))"
    using prefixes_length_mono s_learn_prenum by simp
  finally have "x < e_length (prefixes j (Suc x))" .
  with True have "e_nth (prefixes j (Suc x)) x = e_nth (prefixes j t) x"
    using prefixes_le_nth[of x j "Suc x" "t - Suc x"] by simp
  then show ?thesis using psi_def by simp
next
  case False
  then have "e_nth (prefixes j (Suc x)) x = e_nth (prefixes j t) x"
    using prefixes_le_nth[of x j t "Suc x - t"] assms by simp
  then show ?thesis using psi_def by simp
qed

lemma psi_at_0: "\<psi> j 0 \<down>= j"
  using psi_eq_nth_prefixes[of 0 j 0] prefixes_length_lower_bound[of 0 j]
  by (simp add: prefixes_def r_prefixes_0)

text \<open>The prefixes output by the process @{term[names_short] "prefixes j"} are
indeed prefixes of $\psi_j$.\<close>

lemma prefixes_init_psi: "\<psi> j \<triangleright> (e_length (prefixes j (Suc t)) - 1) = prefixes j (Suc t)"
proof (rule initI[of "prefixes j (Suc t)"])
  let ?e = "prefixes j (Suc t)"
  show "e_length ?e > 0"
    using prefixes_length_lower_bound[of "Suc t" j] by auto
  show "\<And>x. x < e_length ?e \<Longrightarrow> \<psi> j x \<down>= e_nth ?e x"
    using prefixes_Suc_nth psi_eq_nth_prefixes by simp
qed

text \<open>Every prefix of $\psi_j$ generated by the process
@{term[names_short] "prefixes j"} (except for the initial one) is of the form
$b0^k1$. But $k$ is chosen such that $\varphi_{S(b0^k)}(|b|+k) = 0 \neq 1 =
b0^k1_{|b|+k}$. Therefore the hypothesis $S(b0^k)$ is incorrect for
$\psi_j$.\<close>

lemma hyp_wrong_at_last:
  "\<phi> (the (s (e_butlast (prefixes j (Suc t))))) (e_length (prefixes j (Suc t)) - 1) \<noteq>
   \<psi> j (e_length (prefixes j (Suc t)) - 1)"
  (is "?lhs \<noteq> ?rhs")
proof -
  let ?b = "prefixes j t"
  let ?k = "the (eval r_find_k [?b])"
  let ?x = "e_length (prefixes j (Suc t)) - 1"
  have "e_butlast (prefixes j (Suc t)) = e_append_zeros ?b ?k"
    using s_learn_prenum prefixes_Suc by simp
  then have "?lhs = \<phi> (the (s (e_append_zeros ?b ?k))) ?x"
    by simp
  moreover have "?x = e_length ?b + ?k"
    using prefixes_Suc_length by simp
  ultimately have "?lhs = \<phi> (the (s (e_append_zeros ?b ?k))) (e_length ?b + ?k)"
    by simp
  then have "?lhs \<down>= 0"
    using r_find_k(2) r_s_total s_learn_prenum by metis
  moreover have "?x < e_length (prefixes j (Suc t))"
    using prefixes_length_lower_bound le_less_trans linorder_not_le s_learn_prenum
    by fastforce
  ultimately have "?rhs \<down>= e_nth (prefixes j (Suc t)) ?x"
    using psi_eq_nth_prefixes[of ?x j "Suc t"] by simp
  moreover have "e_nth (prefixes j (Suc t)) ?x = 1"
    using prefixes_Suc prefixes_Suc_last by simp
  ultimately have "?rhs \<down>= 1" by simp
  with \<open>?lhs \<down>= 0\<close> show ?thesis by simp
qed

corollary hyp_wrong: "\<phi> (the (s (e_butlast (prefixes j (Suc t))))) \<noteq> \<psi> j"
  using hyp_wrong_at_last[of j t] by auto

text \<open>For all $j$, the strategy $S$ outputs infinitely many wrong hypotheses for
$\psi_j$\<close>

lemma infinite_hyp_wrong: "\<exists>m>n. \<phi> (the (s (\<psi> j \<triangleright> m))) \<noteq> \<psi> j"
proof -
  let ?b = "prefixes j (Suc (Suc n))"
  let ?bb = "e_butlast ?b"
  have len_b: "e_length ?b > Suc (Suc n)"
    using prefixes_length_lower_bound by (simp add: Suc_le_lessD)
  then have len_bb: "e_length ?bb > Suc n" by simp
  define m where "m = e_length ?bb - 1"
  with len_bb have "m > n" by simp
  have "\<psi> j \<triangleright> m = ?bb"
  proof -
    have "\<psi> j \<triangleright> (e_length ?b - 1) = ?b"
      using prefixes_init_psi by simp
    then have "\<psi> j \<triangleright> (e_length ?b - 2) = ?bb"
      using init_butlast_init psi_in_R2 R2_proj_R1 R1_imp_total1 len_bb length_init
      by (metis Suc_1 diff_diff_left length_butlast length_greater_0_conv
        list.size(3) list_decode_encode not_less0 plus_1_eq_Suc)
    then show ?thesis by (metis diff_Suc_1 length_init m_def)
  qed
  moreover have "\<phi> (the (s ?bb)) \<noteq> \<psi> j"
    using hyp_wrong by simp
  ultimately have "\<phi> (the (s (\<psi> j \<triangleright> m))) \<noteq> \<psi> j"
    by simp
  with \<open>m > n\<close> show ?thesis by auto
qed

lemma U0_V0_not_learn_bc: "\<not> learn_bc \<phi> (U\<^sub>0 \<union> V\<^sub>0) s"
proof -
  obtain j where j: "\<phi> j = \<psi> j"
    using R2_imp_P2 kleene_fixed_point psi_in_R2 by blast
  moreover have "\<exists>m>n. \<phi> (the (s ((\<psi> j) \<triangleright> m))) \<noteq> \<psi> j" for n
    using infinite_hyp_wrong[of _ j] by simp
  ultimately have "\<not> learn_bc \<phi> {\<psi> j} s"
    using infinite_hyp_wrong_not_BC by simp
  moreover have "\<psi> j \<in> V\<^sub>0"
  proof -
    have "\<psi> j \<in> \<R>" (is "?f \<in> \<R>")
      using psi_in_R2 by simp
    moreover have "\<phi> (the (?f 0)) = ?f"
      using j psi_at_0[of j] by simp
    ultimately show ?thesis by (simp add: V0_def)
  qed
  ultimately show "\<not> learn_bc \<phi> (U\<^sub>0 \<union> V\<^sub>0) s"
    using learn_bc_closed_subseteq by auto
qed

end

lemma U0_V0_not_in_BC: "U\<^sub>0 \<union> V\<^sub>0 \<notin> BC"
proof
  assume in_BC: "U\<^sub>0 \<union> V\<^sub>0 \<in> BC"
  then have "U\<^sub>0 \<union> V\<^sub>0 \<in> BC_wrt \<phi>"
    using BC_wrt_phi_eq_BC by simp
  then obtain s where "learn_bc \<phi> (U\<^sub>0 \<union> V\<^sub>0) s"
    using BC_wrt_def by auto
  then obtain s' where s': "s' \<in> \<R>" "learn_bc \<phi> (U\<^sub>0 \<union> V\<^sub>0) s'"
    using lemma_R_for_BC_simple by blast
  then have learn_U0: "learn_bc \<phi> U\<^sub>0 s'"
    using learn_bc_closed_subseteq[of \<phi> "U\<^sub>0 \<union> V\<^sub>0" "s'"] by simp
  then interpret r1_bc s'
    by (simp add: r1_bc_def s'(1))
  have "\<not> learn_bc \<phi> (U\<^sub>0 \<union> V\<^sub>0) s'"
    using learn_bc_closed_subseteq U0_V0_not_learn_bc by simp
  with s'(2) show False by simp
qed

theorem R1_not_in_BC: "\<R> \<notin> BC"
proof -
  have "U\<^sub>0 \<union> V\<^sub>0 \<subseteq> \<R>"
    using V0_def U0_in_NUM by auto
  then show ?thesis
    using U0_V0_not_in_BC BC_closed_subseteq by auto
qed

end