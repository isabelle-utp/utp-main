section \<open>CONS is a proper subset of LIM\label{s:cons_lim}\<close>

theory CONS_LIM
  imports Inductive_Inference_Basics
begin

text \<open>That there are classes in @{term "LIM - CONS"} was noted by
Barzdin~\cite{b-iiafp-74,b-iiafp-77} and Blum and Blum~\cite{bb-tmtii-75}. It
was proven by Wiehagen~\cite{w-lerfss-76} (see also Wiehagen and
Zeugmann~\cite{wz-idmowle-94}). The proof uses this class:\<close>

definition U_LIMCONS :: "partial1 set" ("U\<^bsub>LIM-CONS\<^esub>") where
  "U\<^bsub>LIM-CONS\<^esub> \<equiv> {vs @ [j] \<odot> p| vs j p. j \<ge> 2 \<and> p \<in> \<R>\<^sub>0\<^sub>1 \<and> \<phi> j = vs @ [j] \<odot> p}"

text \<open>Every function in @{term "U\<^bsub>LIM-CONS\<^esub>"} carries a Gödel number
greater or equal two of itself, after which only zeros and ones occur.
Thus, a strategy that always outputs the rightmost value greater or equal two
in the given prefix will converge to this Gödel number.

The next function searches an encoded list for the rightmost element
greater or equal two.\<close>

definition rmge2 :: partial1 where
  "rmge2 e \<equiv>
    if \<forall>i<e_length e. e_nth e i < 2 then Some 0
    else Some (e_nth e (GREATEST i. i < e_length e \<and> e_nth e i \<ge> 2))"

lemma rmge2:
  assumes "xs = list_decode e"
  shows "rmge2 e =
   (if \<forall>i<length xs. xs ! i < 2 then Some 0
    else Some (xs ! (GREATEST i. i < length xs \<and> xs ! i \<ge> 2)))"
proof -
  have "(i < e_length e \<and> e_nth e i \<ge> 2) = (i < length xs \<and> xs ! i \<ge> 2)" for i
    using assms by simp
  then have "(GREATEST i. i < e_length e \<and> e_nth e i \<ge> 2) =
      (GREATEST i. i < length xs \<and> xs ! i \<ge> 2)"
    by simp
  moreover have "(\<forall>i<length xs. xs ! i < 2) = (\<forall>i<e_length e. e_nth e i < 2)"
    using assms by simp
  moreover have "(GREATEST i. i < length xs \<and> xs ! i \<ge> 2) < length xs" (is "Greatest ?P < _")
      if "\<not> (\<forall>i<length xs. xs ! i < 2)"
    using that GreatestI_ex_nat[of ?P] le_less_linear order.asym by blast
  ultimately show ?thesis using rmge2_def assms by auto
qed

lemma rmge2_init:
  "rmge2 (f \<triangleright> n) =
   (if \<forall>i<Suc n. the (f i) < 2 then Some 0
    else Some (the (f (GREATEST i. i < Suc n \<and> the (f i) \<ge> 2))))"
proof -
  let ?xs = "prefix f n"
  have "f \<triangleright> n = list_encode ?xs" by (simp add: init_def)
  moreover have "(\<forall>i<Suc n. the (f i) < 2) = (\<forall>i<length ?xs. ?xs ! i < 2)"
    by simp
  moreover have "(GREATEST i. i < Suc n \<and> the (f i) \<ge> 2) =
      (GREATEST i. i < length ?xs \<and> ?xs ! i \<ge> 2)"
    using length_prefix[of f n] prefix_nth[of _ n f] by metis
  moreover have "(GREATEST i. i < Suc n \<and> the (f i) \<ge> 2) < Suc n"
      if "\<not> (\<forall>i<Suc n. the (f i) < 2)"
    using that GreatestI_ex_nat[of "\<lambda>i. i<Suc n \<and> the (f i) \<ge> 2" n] by fastforce
  ultimately show ?thesis using rmge2 by auto
qed

corollary rmge2_init_total:
  assumes "total1 f"
  shows "rmge2 (f \<triangleright> n) =
   (if \<forall>i<Suc n. the (f i) < 2 then Some 0
    else f (GREATEST i. i < Suc n \<and> the (f i) \<ge> 2))"
  using assms total1_def rmge2_init by auto

lemma rmge2_in_R1: "rmge2 \<in> \<R>"
proof -
  define g where
    "g = Cn 3 r_ifle [r_constn 2 2, Cn 3 r_nth [Id 3 2, Id 3 0], Cn 3 r_nth [Id 3 2, Id 3 0], Id 3 1]"
  then have "recfn 3 g" by simp
  then have g: "eval g [j, r, e] \<down>= (if 2 \<le> e_nth e j then e_nth e j else r)" for j r e
    using g_def by simp

  let ?h = "Pr 1 Z g"
  have "recfn 2 ?h"
    by (simp add: \<open>recfn 3 g\<close>)
  have h: "eval ?h [j, e] =
   (if \<forall>i<j. e_nth e i < 2 then Some 0
    else Some (e_nth e (GREATEST i. i < j \<and> e_nth e i \<ge> 2)))" for j e
  proof (induction j)
    case 0
    then show ?case using \<open>recfn 2 ?h\<close> by auto
  next
    case (Suc j)
    then have "eval ?h [Suc j, e] = eval g [j, the (eval ?h [j, e]), e]"
      using \<open>recfn 2 ?h\<close> by auto
    then have *: "eval ?h [Suc j, e] \<down>=
      (if 2 \<le> e_nth e j then e_nth e j
       else if \<forall>i<j. e_nth e i < 2 then 0
            else (e_nth e (GREATEST i. i < j \<and> e_nth e i \<ge> 2)))"
      using g Suc by auto
    show ?case
    proof (cases "\<forall>i<Suc j. e_nth e i < 2")
      case True
      then show ?thesis using * by auto
    next
      case ex: False
      show ?thesis
      proof (cases "2 \<le> e_nth e j")
        case True
        then have "eval ?h [Suc j, e] \<down>= e_nth e j"
          using * by simp
        moreover have "(GREATEST i. i < Suc j \<and> e_nth e i \<ge> 2) = j"
          using ex True Greatest_equality[of "\<lambda>i.  i < Suc j \<and> e_nth e i \<ge> 2"]
          by simp
        ultimately show ?thesis using ex by auto
      next
        case False
        then have "\<exists>i<j. e_nth e i \<ge> 2"
          using ex leI less_Suc_eq by blast
        with * have "eval ?h [Suc j, e] \<down>= e_nth e (GREATEST i. i < j \<and> e_nth e i \<ge> 2)"
          using False by (smt leD)
        moreover have "(GREATEST i. i < Suc j \<and> e_nth e i \<ge> 2) =
            (GREATEST i. i < j \<and> e_nth e i \<ge> 2)"
          using False ex by (metis less_SucI less_Suc_eq less_antisym numeral_2_eq_2)
        ultimately show ?thesis using ex by metis
      qed
    qed
  qed

  let ?hh = "Cn 1 ?h [Cn 1 r_length [Id 1 0], Id 1 0]"
  have "recfn 1 ?hh"
    using \<open>recfn 2 ?h\<close> by simp
  with h have hh: "eval ?hh [e] \<down>=
    (if \<forall>i<e_length e. e_nth e i < 2 then 0
     else e_nth e (GREATEST i. i < e_length e \<and> e_nth e i \<ge> 2))" for e
    by auto
  then have "eval ?hh [e] = rmge2 e" for e
    unfolding rmge2_def by auto
  moreover have "total ?hh"
    using hh totalI1 \<open>recfn 1 ?hh\<close> by simp
  ultimately show ?thesis using \<open>recfn 1 ?hh\<close> by blast
qed

text \<open>The first part of the main result is that @{term "U\<^bsub>LIM-CONS\<^esub> \<in> LIM"}.\<close>

lemma U_LIMCONS_in_Lim: "U\<^bsub>LIM-CONS\<^esub> \<in> LIM"
proof -
  have "U\<^bsub>LIM-CONS\<^esub> \<subseteq> \<R>"
    unfolding U_LIMCONS_def using prepend_in_R1 RPred1_subseteq_R1 by blast
  have "learn_lim \<phi> U\<^bsub>LIM-CONS\<^esub> rmge2"
  proof (rule learn_limI)
    show "environment \<phi> U\<^bsub>LIM-CONS\<^esub> rmge2"
      using \<open>U_LIMCONS \<subseteq> \<R>\<close> phi_in_P2 rmge2_def rmge2_in_R1 by simp
    show "\<exists>i. \<phi> i = f \<and> (\<forall>\<^sup>\<infinity>n. rmge2 (f \<triangleright> n) \<down>= i)" if "f \<in> U\<^bsub>LIM-CONS\<^esub>" for f
    proof -
      from that obtain vs j p where
        j: "j \<ge> 2"
        and p: "p \<in> \<R>\<^sub>0\<^sub>1"
        and s: "\<phi> j = vs @ [j] \<odot> p"
        and f: "f = vs @ [j] \<odot> p"
        unfolding U_LIMCONS_def by auto
      then have "\<phi> j = f" by simp
      from that have "total1 f"
        using \<open>U\<^bsub>LIM-CONS\<^esub> \<subseteq> \<R>\<close> R1_imp_total1 total1_def by auto
      define n\<^sub>0 where "n\<^sub>0 = length vs"
      have f_gr_n0: "f n \<down>= 0 \<or> f n \<down>= 1" if "n > n\<^sub>0" for n
      proof -
        have "f n = p (n - n\<^sub>0 - 1)"
          using that n\<^sub>0_def f by simp
        with RPred1_def p show ?thesis by auto
      qed
      have "rmge2 (f \<triangleright> n) \<down>= j" if "n \<ge> n\<^sub>0" for n
      proof -
        have n0_greatest: "(GREATEST i. i < Suc n \<and> the (f i) \<ge> 2) = n\<^sub>0"
        proof (rule Greatest_equality)
          show "n\<^sub>0 < Suc n \<and> the (f n\<^sub>0) \<ge> 2"
            using n\<^sub>0_def f that j by simp
          show "\<And>y. y < Suc n \<and> the (f y) \<ge> 2 \<Longrightarrow> y \<le> n\<^sub>0"
          proof -
            fix y assume "y < Suc n \<and> 2 \<le> the (f y)"
            moreover have "p \<in> \<R> \<and> (\<forall>n. p n \<down>= 0 \<or> p n \<down>= 1)"
              using RPred1_def p by blast
            ultimately show "y \<le> n\<^sub>0"
              using f_gr_n0
              by (metis Suc_1 Suc_n_not_le_n Zero_neq_Suc le_less_linear le_zero_eq option.sel)
          qed
        qed
        have "f n\<^sub>0 \<down>= j"
          using n\<^sub>0_def f by simp
        then have "\<not> (\<forall>i<Suc n. the (f i) < 2)"
          using j that less_Suc_eq_le by auto
        then have "rmge2 (f \<triangleright> n) = f (GREATEST i. i < Suc n \<and> the (f i) \<ge> 2)"
          using rmge2_init_total \<open>total1 f\<close> by auto
        with n0_greatest \<open>f n\<^sub>0 \<down>= j\<close> show ?thesis by simp
      qed
      with \<open>\<phi> j = f\<close> show ?thesis by auto
    qed
  qed
  then show ?thesis using Lim_def by auto
qed

text \<open>The class @{term "U_LIMCONS"} is \emph{prefix-complete}, which
means that every non-empty list is the prefix of some function in @{term
"U_LIMCONS"}. To show this we use an auxiliary lemma: For every $f \in
\mathcal{R}$ and $k \in \mathbb{N}$ the value of $f$ at $k$ can be replaced
by a Gödel number of the function resulting from the replacement.\<close>

lemma goedel_at:
  fixes m :: nat and k :: nat
  assumes "f \<in> \<R>"
  shows "\<exists>n\<ge>m. \<phi> n = (\<lambda>x. if x = k then Some n else f x)"
proof -
  define psi :: "partial1 \<Rightarrow> nat \<Rightarrow> partial2" where
    "psi = (\<lambda>f k i x. (if x = k then Some i else f x))"
  have "psi f k \<in> \<R>\<^sup>2"
  proof -
    obtain r where r: "recfn 1 r" "total r" "eval r [x] = f x" for x
      using assms by auto
    define r_psi where
      "r_psi = Cn 2 r_ifeq [Id 2 1, r_dummy 1 (r_const k), Id 2 0, Cn 2 r [Id 2 1]]"
    show ?thesis
    proof (rule R2I[of r_psi])
      from r_psi_def show "recfn 2 r_psi"
        using r(1) by simp
      have "eval r_psi [i, x] = (if x = k then Some i else f x)" for i x
      proof -
        have "eval (Cn 2 r [Id 2 1]) [i, x] = f x"
          using r by simp
        then have "eval r_psi [i, x] = eval r_ifeq [x, k, i, the (f x)]"
          unfolding r_psi_def using \<open>recfn 2 r_psi\<close> r R1_imp_total1[OF assms]
          by simp
        then show ?thesis using assms by simp
      qed
      then show "\<And>x y. eval r_psi [x, y] = psi f k x y"
        unfolding psi_def by simp
      then show "total r_psi"
        using totalI2[of r_psi] \<open>recfn 2 r_psi\<close> assms psi_def by fastforce
    qed
  qed
  then obtain n where "n \<ge> m" "\<phi> n = psi f k n"
    using assms kleene_fixed_point[of "psi f k" m] by auto
  then show ?thesis unfolding psi_def by auto
qed

lemma U_LIMCONS_prefix_complete:
  assumes "length vs > 0"
  shows "\<exists>f\<in>U\<^bsub>LIM-CONS\<^esub>. prefix f (length vs - 1) = vs"
proof -
  let ?p = "\<lambda>_. Some 0"
  let ?f = "vs @ [0] \<odot> ?p"
  have "?f \<in> \<R>"
    using prepend_in_R1 RPred1_subseteq_R1 const0_in_RPred1 by blast
  with goedel_at[of ?f 2 "length vs"] obtain j where
    j: "j \<ge> 2" "\<phi> j = (\<lambda>x. if x = length vs then Some j else ?f x)" (is "_ = ?g")
    by auto
  moreover have g: "?g x = (vs @ [j] \<odot> ?p) x" for x
    by (simp add: nth_append)
  ultimately have "?g \<in> U\<^bsub>LIM-CONS\<^esub>"
    unfolding U_LIMCONS_def using const0_in_RPred1 by fastforce
  moreover have "prefix ?g (length vs - 1) = vs"
    using g assms prefixI prepend_associative by auto
  ultimately show ?thesis by auto
qed

text \<open>Roughly speaking, a strategy learning a prefix-complete class
must be total because it must be defined for every prefix in
the class. Technically, however, the empty list is not a prefix, and thus a
strategy may diverge on input 0. We can work around this by
showing that if there is a strategy learning a prefix-complete class then
there is also a total strategy learning this class. We need the result only
for consistent learning.\<close>

lemma U_prefix_complete_imp_total_strategy:
  assumes "\<And>vs. length vs > 0 \<Longrightarrow> \<exists>f\<in>U. prefix f (length vs - 1) = vs"
    and "learn_cons \<psi> U s"
  shows "\<exists>t. total1 t \<and> learn_cons \<psi> U t"
proof -
  define t where "t = (\<lambda>e. if e = 0 then Some 0 else s e)"
  have "s e \<down>" if "e > 0" for e
  proof -
    from that have "list_decode e \<noteq> []" (is "?vs \<noteq> _")
      using list_encode_0 list_encode_decode by (metis less_imp_neq)
    then have "length ?vs > 0" by simp
    with assms(1) obtain f where f: "f \<in> U" "prefix f (length ?vs - 1) = ?vs"
      by auto
    with learn_cons_def learn_limE have "s (f \<triangleright> (length ?vs - 1)) \<down>"
      using assms(2) by auto
    then show "s e \<down>"
      using f(2) init_def by auto
  qed
  then have "total1 t"
    using t_def by auto
  have "t \<in> \<P>"
  proof -
    from assms(2) have "s \<in> \<P>"
      using learn_consE by simp
    then obtain rs where rs: "recfn 1 rs" "eval rs [x] = s x" for x
      by auto
    define rt where "rt = Cn 1 (r_lifz Z rs) [Id 1 0, Id 1 0]"
    then have "recfn 1 rt"
      using rs by auto
    moreover have "eval rt [x] = t x" for x
      using rs rt_def t_def by simp
    ultimately show ?thesis by blast
  qed
  have "s (f \<triangleright> n) = t (f \<triangleright> n)" if "f \<in> U" for f n
    unfolding t_def by (simp add: init_neq_zero)
  then have "learn_cons \<psi> U t"
    using \<open>t \<in> \<P>\<close> assms(2) learn_consE[of \<psi> U s] learn_consI[of \<psi> U t] by simp
  with \<open>total1 t\<close> show ?thesis by auto
qed

text \<open>The proof of @{prop "U\<^bsub>LIM-CONS\<^esub> \<notin> CONS"} is by contradiction.
Assume there is a consistent learning strategy $S$. By the previous
lemma $S$ can be assumed to be total. Moreover it outputs a consistent
hypothesis for every prefix. Thus for every $e \in \mathbb{N}^+$, $S(e) \neq
S(e0)$ or $S(e) \neq S(e1)$ because $S(e)$ cannot be consistent with both
$e0$ and $e1$. We use this property of $S$ to construct a function in @{term
"U\<^bsub>LIM-CONS\<^esub>"} for which $S$ fails as a learning strategy. To
this end we define a numbering $\psi \in \mathcal{R}^2$ with $\psi_i(0) = i$
and
\[
\psi_i(x + 1) = \left\{\begin{array}{ll}
    0 & \mbox{if } S(\psi_i^x0) \neq S(\psi_i^x),\\
    1 & \mbox{otherwise}.
\end{array}\right.
\]
This numbering is recursive because $S$ is total. The ``otherwise'' case is
equivalent to $S(\psi_i^x1) \neq S(\psi_i^x)$ because $S(\psi_i^x)$ cannot be
consistent with both $\psi_i^x0$ and $\psi_i^x1$. Therefore every prefix
$\psi_i^x$ is extended in such a way that $S$ changes its hypothesis. Hence
$S$ does not learn $\psi_i$ in the limit. Kleene's fixed-point theorem
ensures that for some $j \geq 2$, $\varphi_j = \psi_j$. This $\psi_j$ is the
sought function in @{term "U\<^bsub>LIM-CONS\<^esub>"}.

The following locale formalizes the construction of $\psi$ for a total
strategy $S$.\<close>

locale cons_lim =
  fixes s :: partial1
  assumes s_in_R1: "s \<in> \<R>"
begin

text \<open>A @{typ recf} computing the strategy:\<close>

definition r_s :: recf where
  "r_s \<equiv> SOME r_s. recfn 1 r_s \<and>  total r_s \<and> s = (\<lambda>x. eval r_s [x])"

lemma r_s_recfn [simp]: "recfn 1 r_s"
  and r_s_total [simp]: "\<And>x. eval r_s [x] \<down>"
  and eval_r_s: "s = (\<lambda>x. eval r_s [x])"
  using r_s_def R1_SOME[OF s_in_R1, of r_s] by simp_all

text \<open>The next function represents the prefixes of $\psi_i$.\<close>

fun prefixes :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "prefixes i 0 = [i]"
| "prefixes i (Suc x) = (prefixes i x) @
    [if s (e_snoc (list_encode (prefixes i x)) 0) = s (list_encode (prefixes i x))
     then 1 else 0]"

definition "r_prefixes_aux \<equiv>
  Cn 3 r_ifeq
   [Cn 3 r_s [Cn 3 r_snoc [Id 3 1, r_constn 2 0]],
    Cn 3 r_s [Id 3 1],
    Cn 3 r_snoc [Id 3 1, r_constn 2 1],
    Cn 3 r_snoc [Id 3 1, r_constn 2 0]]"

lemma r_prefixes_aux_recfn: "recfn 3 r_prefixes_aux"
  unfolding r_prefixes_aux_def by simp

lemma r_prefixes_aux:
  "eval r_prefixes_aux [j, v, i] \<down>=
    e_snoc v (if eval r_s [e_snoc v 0] = eval r_s [v] then 1 else 0)"
  unfolding r_prefixes_aux_def by auto

definition "r_prefixes \<equiv> r_swap (Pr 1 r_singleton_encode r_prefixes_aux)"

lemma r_prefixes_recfn: "recfn 2 r_prefixes"
  unfolding r_prefixes_def r_prefixes_aux_def by simp

lemma r_prefixes: "eval r_prefixes [i, n] \<down>= list_encode (prefixes i n)"
proof -
  let ?h = "Pr 1 r_singleton_encode r_prefixes_aux"
  have "eval ?h [n, i] \<down>= list_encode (prefixes i n)"
  proof (induction n)
    case 0
    then show ?case
      using r_prefixes_def r_prefixes_aux_recfn r_singleton_encode by simp
  next
    case (Suc n)
    then show ?case
      using r_prefixes_aux_recfn r_prefixes_aux eval_r_s
      by auto metis+
  qed
  moreover have "eval ?h [n, i] = eval r_prefixes [i, n]" for i n
    unfolding r_prefixes_def by (simp add: r_prefixes_aux_recfn)
  ultimately show ?thesis by simp
qed

lemma prefixes_neq_nil: "length (prefixes i x) > 0"
  by (induction x) auto

text \<open>The actual numbering can then be defined via @{term prefixes}.\<close>

definition psi :: "partial2" ("\<psi>") where
  "\<psi> i x \<equiv> Some (last (prefixes i x))"

lemma psi_in_R2: "\<psi> \<in> \<R>\<^sup>2"
proof
  define r_psi where "r_psi \<equiv> Cn 2 r_last [r_prefixes]"
  have "recfn 2 r_psi"
    unfolding r_psi_def by (simp add: r_prefixes_recfn)
  then have "eval r_psi [i, n] \<down>= last (prefixes i n)" for n i
    unfolding r_psi_def using r_prefixes r_prefixes_recfn prefixes_neq_nil by simp
  then have "(\<lambda>i x. Some (last (prefixes i x))) \<in> \<P>\<^sup>2"
    using \<open>recfn 2 r_psi\<close> P2I[of "r_psi"] by simp
  with psi_def show "\<psi> \<in> \<P>\<^sup>2" by presburger
  moreover show "total2 psi"
    unfolding psi_def by auto
qed

lemma psi_0_or_1:
  assumes "n > 0"
  shows "\<psi> i n \<down>= 0 \<or> \<psi> i n \<down>= 1"
proof -
  from assms obtain m where "n = Suc m"
    using gr0_implies_Suc by blast
  then have "last (prefixes i (Suc m)) = 0 \<or> last (prefixes i (Suc m)) = 1"
    by simp
  then show ?thesis using \<open>n = Suc m\<close> psi_def by simp
qed

text \<open>The function @{term "prefixes"} does indeed provide the prefixes
for @{term "\<psi>"}.\<close>

lemma psi_init: "(\<psi> i) \<triangleright> x = list_encode (prefixes i x)"
proof -
  have "prefix (\<psi> i) x = prefixes i x"
    unfolding psi_def
    by (induction x) (simp_all add: prefix_0 prefix_Suc)
  with init_def show ?thesis by simp
qed

text \<open>One of the functions $\psi_i$ is in @{term "U\<^bsub>LIM-CONS\<^esub>"}.\<close>

lemma ex_psi_in_U: "\<exists>j. \<psi> j \<in> U\<^bsub>LIM-CONS\<^esub>"
proof -
  obtain j where j: "j \<ge> 2" "\<psi> j = \<phi> j"
    using kleene_fixed_point[of \<psi>] psi_in_R2 R2_imp_P2 by metis
  then have "\<psi> j \<in> \<P>" by (simp add: phi_in_P2)
  define p where "p = (\<lambda>x. \<psi> j (x + 1))"
  have "p \<in> \<R>\<^sub>0\<^sub>1"
  proof -
    from p_def \<open>\<psi> j \<in> \<P>\<close> skip_P1 have "p \<in> \<P>" by blast
    from psi_in_R2 have "total1 (\<psi> j)" by simp
    with p_def have "total1 p"
      by (simp add: total1_def)
    with psi_0_or_1 have "p n \<down>= 0 \<or> p n \<down>= 1" for n
      using psi_def p_def by simp
    then show ?thesis
      by (simp add: RPred1_def P1_total_imp_R1 \<open>p \<in> \<P>\<close> \<open>total1 p\<close>)
  qed
  moreover have "\<psi> j = [j] \<odot> p"
  proof
    fix x
    show "\<psi> j x = ([j] \<odot> p) x"
    proof (cases "x = 0")
      case True
      then show ?thesis using psi_def psi_def prepend_at_less by simp
    next
      case False
      then show ?thesis using p_def by simp
    qed
  qed
  ultimately have "\<psi> j \<in> U\<^bsub>LIM-CONS\<^esub>"
    using j U_LIMCONS_def by (metis (mono_tags, lifting) append_Nil mem_Collect_eq)
  then show ?thesis by auto
qed

text \<open>The strategy fails to learn @{term U_LIMCONS} because it changes
its hypothesis all the time on functions $\psi_j \in V_0$.\<close>

lemma U_LIMCONS_not_learn_cons: "\<not> learn_cons \<phi> U\<^bsub>LIM-CONS\<^esub> s"
proof
  assume learn: "learn_cons \<phi> U\<^bsub>LIM-CONS\<^esub> s"
  have "s (list_encode (vs @ [0])) \<noteq> s (list_encode (vs @ [1]))" for vs
  proof -
    obtain f\<^sub>0 where f0: "f\<^sub>0 \<in> U\<^bsub>LIM-CONS\<^esub>" "prefix f\<^sub>0 (length vs) = vs @ [0]"
      using U_LIMCONS_prefix_complete[of "vs @ [0]"] by auto
    obtain f\<^sub>1 where f1: "f\<^sub>1 \<in> U\<^bsub>LIM-CONS\<^esub>" "prefix f\<^sub>1 (length vs) = vs @ [1]"
      using U_LIMCONS_prefix_complete[of "vs @ [1]"] by auto
    have "f\<^sub>0 (length vs) \<noteq> f\<^sub>1 (length vs)"
      using f0 f1 by (metis lessI nth_append_length prefix_nth zero_neq_one)
    moreover have "\<phi> (the (s (f\<^sub>0 \<triangleright> length vs))) (length vs) = f\<^sub>0 (length vs)"
      using learn_consE(3)[of \<phi> U_LIMCONS s, OF learn, of f\<^sub>0 "length vs", OF f0(1)]
      by simp
    moreover have "\<phi> (the (s (f\<^sub>1 \<triangleright> length vs))) (length vs) = f\<^sub>1 (length vs)"
      using learn_consE(3)[of \<phi> U_LIMCONS s, OF learn, of f\<^sub>1 "length vs", OF f1(1)]
      by simp
    ultimately have "the (s (f\<^sub>0 \<triangleright> length vs)) \<noteq> the (s (f\<^sub>1 \<triangleright> length vs))"
      by auto
    then have "s (f\<^sub>0 \<triangleright> length vs) \<noteq> s (f\<^sub>1 \<triangleright> length vs)"
      by auto
    with f0(2) f1(2) show ?thesis by (simp add: init_def)
  qed
  then have "s (list_encode (vs @ [0])) \<noteq> s (list_encode vs) \<or>
      s (list_encode (vs @ [1])) \<noteq> s (list_encode vs)"
      for vs
    by metis
  then have "s (list_encode (prefixes i (Suc x))) \<noteq> s (list_encode (prefixes i x))" for i x
    by simp
  then have "\<not> learn_lim \<phi> {\<psi> i} s" for i
    using psi_def psi_init always_hyp_change_not_Lim by simp
  then have "\<not> learn_lim \<phi> U_LIMCONS s"
    using ex_psi_in_U learn_lim_closed_subseteq by blast
  then show False
    using learn learn_cons_def by simp
qed

end

text \<open>With the locale we can now show the second part of the main
result:\<close>

lemma U_LIMCONS_not_in_CONS: "U\<^bsub>LIM-CONS\<^esub> \<notin> CONS"
proof
  assume "U\<^bsub>LIM-CONS\<^esub> \<in> CONS"
  then have "U\<^bsub>LIM-CONS\<^esub> \<in> CONS_wrt \<phi>"
    by (simp add: CONS_wrt_phi_eq_CONS)
  then obtain almost_s where "learn_cons \<phi> U\<^bsub>LIM-CONS\<^esub> almost_s"
    using CONS_wrt_def by auto
  then obtain s where s: "total1 s" "learn_cons \<phi> U\<^bsub>LIM-CONS\<^esub> s"
    using U_LIMCONS_prefix_complete U_prefix_complete_imp_total_strategy by blast
  then have "s \<in> \<R>"
    using learn_consE(1) P1_total_imp_R1 by blast
  with cons_lim_def interpret cons_lim s by simp
  show False
    using s(2) U_LIMCONS_not_learn_cons by simp
qed

text \<open>The main result of this section:\<close>

theorem CONS_subset_Lim: "CONS \<subset> LIM"
  using U_LIMCONS_in_Lim U_LIMCONS_not_in_CONS CONS_subseteq_Lim by auto

end