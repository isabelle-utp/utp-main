section \<open>TOTAL is a proper subset of CONS\label{s:total_cons}\<close>

theory TOTAL_CONS
  imports Lemma_R  (* for r_auxhyp *)
    CP_FIN_NUM  (* for r_consistent *)
    CONS_LIM  (* for rmge2, goedel_at *)
begin

text \<open>We first show that TOTAL is a subset of CONS. Then we present a
separating class.\<close>


subsection \<open>TOTAL is a subset of CONS\<close>

text \<open>A TOTAL strategy hypothesizes only total functions, for which the
consistency with the input prefix is decidable. A CONS strategy can thus run
a TOTAL strategy and check if its hypothesis is consistent. If so, it
outputs this hypothesis, otherwise some arbitrary consistent one. Since the
TOTAL strategy converges to a correct hypothesis, which is consistent, the
CONS strategy will converge to the same hypothesis.\<close>

text \<open>Without loss of generality we can assume that learning takes place
with respect to our Gödel numbering $\varphi$. So we need to decide
consistency only for this numbering.\<close>

abbreviation r_consist_phi where
  "r_consist_phi \<equiv> r_consistent r_phi"

lemma r_consist_phi_recfn [simp]: "recfn 2 r_consist_phi"
  by simp

lemma r_consist_phi:
  assumes "\<forall>k<e_length e. \<phi> i k \<down>"
  shows "eval r_consist_phi [i, e] \<down>=
    (if \<forall>k<e_length e. \<phi> i k \<down>= e_nth e k then 0 else 1)"
proof -
  have "\<forall>k<e_length e. eval r_phi [i, k] \<down>"
    using assms phi_def by simp
  moreover have "recfn 2 r_phi" by simp
  ultimately have "eval (r_consistent r_phi) [i, e] \<down>=
     (if \<forall>k<e_length e. eval r_phi [i, k] \<down>= e_nth e k then 0 else 1)"
    using r_consistent_converg assms by simp
  then show ?thesis using phi_def by simp
qed

lemma r_consist_phi_init:
  assumes "f \<in> \<R>" and "\<phi> i \<in> \<R>"
  shows "eval r_consist_phi [i, f \<triangleright> n] \<down>= (if \<forall>k\<le>n. \<phi> i k = f k then 0 else 1)"
  using assms r_consist_phi R1_imp_total1 total1E by (simp add: r_consist_phi)

lemma TOTAL_subseteq_CONS: "TOTAL \<subseteq> CONS"
proof
  fix U assume "U \<in> TOTAL"
  then have "U \<in> TOTAL_wrt \<phi>"
    using TOTAL_wrt_phi_eq_TOTAL by blast
  then obtain t' where t': "learn_total \<phi> U t'"
    using TOTAL_wrt_def by auto
  then obtain t where t: "recfn 1 t" "\<And>x. eval t [x] = t' x"
    using learn_totalE(1) P1E by blast
  then have t_converg: "eval t [f \<triangleright> n] \<down>" if "f \<in> U" for f n
    using t' learn_totalE(1) that by auto

  define s where "s \<equiv> Cn 1 r_ifz [Cn 1 r_consist_phi [t, Id 1 0], t, r_auxhyp]"
  then have "recfn 1 s"
    using r_consist_phi_recfn r_auxhyp_prim t(1) by simp

  have consist: "eval r_consist_phi [the (eval t [f \<triangleright> n]), f \<triangleright> n] \<down>=
     (if \<forall>k\<le>n. \<phi> (the (eval t [f \<triangleright> n])) k = f k then 0 else 1)"
    if "f \<in> U" for f n
  proof -
    have "eval r_consist_phi [the (eval t [f \<triangleright> n]), f \<triangleright> n] =
        eval (Cn 1 r_consist_phi [t, Id 1 0]) [f \<triangleright> n]"
      using that t_converg t(1) by simp
    also have "... \<down>= (if \<forall>k\<le>n. \<phi> (the (eval t [f \<triangleright> n])) k = f k then 0 else 1)"
    proof -
      from that have "f \<in> \<R>"
        using learn_totalE(1) t' by blast
      moreover have "\<phi> (the (eval t [f \<triangleright> n])) \<in> \<R>"
        using t' t learn_totalE t_converg that by simp
      ultimately show ?thesis
        using r_consist_phi_init t_converg t(1) that by simp
    qed
    finally show ?thesis .
  qed

  have s_eq_t: "eval s [f \<triangleright> n] = eval t [f \<triangleright> n]"
    if "\<forall>k\<le>n. \<phi> (the (eval t [f \<triangleright> n])) k = f k" and "f \<in> U" for f n
    using that consist s_def t r_auxhyp_prim prim_recfn_total
    by simp

  have s_eq_aux: "eval s [f \<triangleright> n] = eval r_auxhyp [f \<triangleright> n]"
    if "\<not> (\<forall>k\<le>n. \<phi> (the (eval t [f \<triangleright> n])) k = f k)" and "f \<in> U" for f n
  proof -
    from that have "eval r_consist_phi [the (eval t [f \<triangleright> n]), f \<triangleright> n] \<down>= 1"
      using consist by simp
    moreover have "t' (f \<triangleright> n) \<down>" using t' learn_totalE(1) that(2) by blast
    ultimately show ?thesis
      using s_def t r_auxhyp_prim t' learn_totalE by simp
  qed

  have "learn_cons \<phi> U (\<lambda>e. eval s [e])"
  proof (rule learn_consI)
    have "eval s [f \<triangleright> n] \<down>" if "f \<in> U" for f n
      using that t_converg[OF that, of n] s_eq_t[of n f] prim_recfn_total[of r_auxhyp 1]
        r_auxhyp_prim s_eq_aux[OF _ that, of n] totalE
      by fastforce
    then show "environment \<phi> U (\<lambda>e. eval s [e])"
      using t' \<open>recfn 1 s\<close> learn_totalE(1) by blast
    show "\<exists>i. \<phi> i = f \<and> (\<forall>\<^sup>\<infinity>n. eval s [f \<triangleright> n] \<down>= i)" if "f \<in> U" for f
    proof -
      from that t' t learn_totalE obtain i n\<^sub>0 where
        i_n0: "\<phi> i = f \<and> (\<forall>n\<ge>n\<^sub>0. eval t [f \<triangleright> n] \<down>= i)"
        by metis
      then have "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> \<forall>k\<le>n. \<phi> (the (eval t [f \<triangleright> n])) k = f k"
        by simp
      with s_eq_t have "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> eval s [f \<triangleright> n] = eval t [f \<triangleright> n]"
        using that by simp
      with i_n0 have "\<And>n. n \<ge> n\<^sub>0 \<Longrightarrow> eval s [f \<triangleright> n] \<down>= i"
        by auto
      with i_n0 show ?thesis by auto
    qed
    show "\<forall>k\<le>n. \<phi> (the (eval s [f \<triangleright> n])) k = f k" if "f \<in> U" for f n
    proof (cases "\<forall>k\<le>n. \<phi> (the (eval t [f \<triangleright> n])) k = f k")
      case True
      with that s_eq_t show ?thesis by simp
    next
      case False
      then have "eval s [f \<triangleright> n] = eval r_auxhyp [f \<triangleright> n]"
        using that s_eq_aux by simp
      moreover have "f \<in> \<R>"
        using learn_totalE(1)[OF t'] that by auto
      ultimately show ?thesis using r_auxhyp by simp
    qed
  qed
  then show "U \<in> CONS" using CONS_def by auto
qed


subsection \<open>The separating class\<close>


subsubsection \<open>Definition of the class\<close>

text \<open>The class that will be shown to be in @{term "CONS - TOTAL"} is
the union of the following two classes.\<close>

definition V_constotal_1 :: "partial1 set" where
  "V_constotal_1 \<equiv> {f. \<exists>j p. f = [j] \<odot> p \<and> j \<ge> 2 \<and> p \<in> \<R>\<^sub>0\<^sub>1 \<and> \<phi> j = f}"

definition V_constotal_2 :: "partial1 set" where
  "V_constotal_2 \<equiv>
     {f. \<exists>j a k.
            f = j # a @ [k] \<odot> 0\<^sup>\<infinity> \<and>
            j \<ge> 2 \<and>
            (\<forall>i<length a. a ! i \<le> 1) \<and>
            k \<ge> 2 \<and>
            \<phi> j = j # a \<odot> \<up>\<^sup>\<infinity> \<and>
            \<phi> k = f}"

definition V_constotal :: "partial1 set" where
  "V_constotal \<equiv> V_constotal_1 \<union> V_constotal_2"

lemma V_constotal_2I:
  assumes "f = j # a @ [k] \<odot> 0\<^sup>\<infinity>"
    and "j \<ge> 2"
    and "\<forall>i<length a. a ! i \<le> 1"
    and "k \<ge> 2"
    and "\<phi> j = j # a \<odot> \<up>\<^sup>\<infinity>"
    and "\<phi> k = f"
  shows "f \<in> V_constotal_2"
  using assms V_constotal_2_def by blast

lemma V_subseteq_R1: "V_constotal \<subseteq> \<R>"
proof
  fix f assume "f \<in> V_constotal"
  then have "f \<in> V_constotal_1 \<or> f \<in> V_constotal_2"
    using V_constotal_def by auto
  then show "f \<in> \<R>"
  proof
    assume "f \<in> V_constotal_1"
    then obtain j p where "f = [j] \<odot> p" "p \<in> \<R>\<^sub>0\<^sub>1"
      using V_constotal_1_def by blast
    then show ?thesis using prepend_in_R1 RPred1_subseteq_R1 by auto
  next
    assume "f \<in> V_constotal_2"
    then obtain j a k where "f = j # a @ [k] \<odot> 0\<^sup>\<infinity>"
      using V_constotal_2_def by blast
    then show ?thesis using almost0_in_R1 by auto
  qed
qed


subsubsection \<open>The class is in CONS\<close>

text \<open>The class can be learned by the strategy @{term rmge2}, which
outputs the rightmost value greater or equal two in the input $f^n$. If $f$
is from $V_1$ then the strategy is correct right from the start. If $f$ is
from $V_2$ the strategy outputs the consistent hypothesis $j$ until it
encounters the correct hypothesis $k$, to which it converges.\<close>

lemma V_in_CONS: "learn_cons \<phi> V_constotal rmge2"
proof (rule learn_consI)
  show "environment \<phi> V_constotal rmge2"
    using V_subseteq_R1 rmge2_in_R1 R1_imp_total1 phi_in_P2 by simp
  have "(\<exists>i. \<phi> i = f \<and> (\<forall>\<^sup>\<infinity>n. rmge2 (f \<triangleright> n) \<down>= i)) \<and>
      (\<forall>n. \<forall>k\<le>n. \<phi> (the (rmge2 (f \<triangleright> n))) k = f k)"
    if "f \<in> V_constotal" for f
  proof (cases "f \<in> V_constotal_1")
    case True
    then obtain j p where
      f: "f = [j] \<odot> p" and
      j: "j \<ge> 2" and
      p: "p \<in> \<R>\<^sub>0\<^sub>1" and
      phi_j: "\<phi> j = f"
      using V_constotal_1_def by blast
    then have "f 0 \<down>= j" by (simp add: prepend_at_less)
    then have f_at_0: "the (f 0) \<ge> 2" by (simp add: j)
    have f_at_gr0: "the (f x) \<le> 1" if "x > 0" for x
      using that f p by (simp add: RPred1_altdef Suc_leI prepend_at_ge)
    have "total1 f"
      using V_subseteq_R1 that R1_imp_total1 total1_def by auto
    have "rmge2 (f \<triangleright> n) \<down>= j" for n
    proof -
      let ?P = "\<lambda>i. i < Suc n \<and> the (f i) \<ge> 2"
      have "Greatest ?P = 0"
      proof (rule Greatest_equality)
        show "0 < Suc n \<and> 2 \<le> the (f 0)"
          using f_at_0 by simp
        show "\<And>y. y < Suc n \<and> 2 \<le> the (f y) \<Longrightarrow> y \<le> 0"
          using f_at_gr0 by fastforce
      qed
      then have "rmge2 (f \<triangleright> n) = f 0"
        using f_at_0 rmge2_init_total[of f n, OF \<open>total1 f\<close>] by auto
      then show "rmge2 (f \<triangleright> n) \<down>= j"
        by (simp add: \<open>f 0 \<down>= j\<close>)
    qed
    then show ?thesis using phi_j by auto
  next
    case False
    then have "f \<in> V_constotal_2"
      using V_constotal_def that by auto
    then obtain j a k where jak:
      "f = j # a @ [k] \<odot> 0\<^sup>\<infinity>"
      "j \<ge> 2"
      "\<forall>i<length a. a ! i \<le> 1"
      "k \<ge> 2"
      "\<phi> j = j # a \<odot> \<up>\<^sup>\<infinity> "
      "\<phi> k = f"
      using V_constotal_2_def by blast
    then have f_at_0: "f 0 \<down>= j" by simp
    have f_eq_a: "f x \<down>= a ! (x - 1)" if "0 < x \<and> x < Suc (length a)" for x
    proof -
      have "x - 1 < length a"
        using that by auto
      then show ?thesis
        by (simp add: jak(1) less_SucI nth_append that)
    qed
    then have f_at_a: "the (f x) \<le> 1" if "0 < x \<and> x < Suc (length a)" for x
      using jak(3) that by auto
    from jak have f_k: "f (Suc (length a)) \<down>= k" by auto
    from jak have f_at_big: "f x \<down>= 0" if "x > Suc (length a)" for x
      using that by simp
    let ?P = "\<lambda>n i. i < Suc n \<and> the (f i) \<ge> 2"
    have rmge2: "rmge2 (f \<triangleright> n) = f (Greatest (?P n))" for n
    proof -
      have "\<not> (\<forall>i<Suc n. the (f i) < 2)" for n
        using jak(2) f_at_0 by auto
      moreover have "total1 f"
        using V_subseteq_R1 R1_imp_total1 that total1_def by auto
      ultimately show ?thesis using rmge2_init_total[of f n] by auto
    qed
    have "Greatest (?P n) = 0" if "n < Suc (length a)" for n
    proof (rule Greatest_equality)
      show "0 < Suc n \<and> 2 \<le> the (f 0)"
        using that by (simp add: jak(2) f_at_0)
      show "\<And>y. y < Suc n \<and> 2 \<le> the (f y) \<Longrightarrow> y \<le> 0"
        using that f_at_a
        by (metis Suc_1 dual_order.strict_trans leI less_Suc_eq not_less_eq_eq)
    qed
    with rmge2 f_at_0 have rmge2_small:
      "rmge2 (f \<triangleright> n) \<down>= j" if "n < Suc (length a)" for n
      using that by simp
    have "Greatest (?P n) = Suc (length a)" if "n \<ge> Suc (length a)" for n
    proof (rule Greatest_equality)
      show "Suc (length a) < Suc n \<and> 2 \<le> the (f (Suc (length a)))"
        using that f_k by (simp add: jak(4) less_Suc_eq_le)
      show "\<And>y. y < Suc n \<and> 2 \<le> the (f y) \<Longrightarrow> y \<le> Suc (length a)"
        using that f_at_big by (metis leI le_SucI not_less_eq_eq numeral_2_eq_2 option.sel)
    qed
    with rmge2 f_at_big f_k have rmge2_big:
      "rmge2 (f \<triangleright> n) \<down>= k" if "n \<ge> Suc (length a)" for n
      using that by simp
    then have "\<exists>i n\<^sub>0. \<phi> i = f \<and> (\<forall>n\<ge>n\<^sub>0. rmge2 (f \<triangleright> n) \<down>= i)"
      using jak(6) by auto
    moreover have "\<forall>k\<le>n. \<phi> (the (rmge2 (f \<triangleright> n))) k = f k" for n
    proof (cases "n < Suc (length a)")
      case True
      then have "rmge2 (f \<triangleright> n) \<down>= j"
        using rmge2_small by simp
      then have "\<phi> (the (rmge2 (f \<triangleright> n))) = \<phi> j" by simp
      with True show ?thesis
        using rmge2_small f_at_0 f_eq_a jak(5) prepend_at_less
        by (metis le_less_trans le_zero_eq length_Cons not_le_imp_less nth_Cons_0 nth_Cons_pos)
    next
      case False
      then show ?thesis using rmge2_big jak by simp
    qed
    ultimately show ?thesis by simp
  qed
  then show "\<And>f. f \<in> V_constotal \<Longrightarrow> \<exists>i. \<phi> i = f \<and> (\<forall>\<^sup>\<infinity>n. rmge2 (f \<triangleright> n) \<down>= i)"
    and "\<And>f n. f \<in> V_constotal \<Longrightarrow> \<forall>k\<le>n. \<phi> (the (rmge2 (f \<triangleright> n))) k = f k"
    by simp_all
qed


subsubsection \<open>The class is not in TOTAL\<close>

text \<open>Recall that $V$ is the union of $V_1 = \{jp \mid j\geq2 \land p \in
\mathcal{R}_{01} \land \varphi_j = jp\}$ and $V_2 = \{jak0^\infty \mid j\geq 2 \land a
\in \{0, 1\}^* \land k\geq 2 \land \varphi_j = ja\uparrow^\infty \land\ 
\varphi_k = jak0^\infty\}$.\<close>

text \<open>The proof is adapted from a proof of a stronger result by
Freivalds, Kinber, and Wiehagen~\cite[Theorem~27]{fkw-iisde-95} concerning an
inference type not defined here.

The proof is by contradiction. If $V$ was in TOTAL, there would be
a strategy $S$ learning $V$ in our standard Gödel numbering $\varphi$.
By Lemma R for TOTAL we can assume $S$ to be total.

In order to construct a function $f\in V$ for which $S$ fails we employ a
computable process iteratively building function prefixes. For every $j$ the
process builds a function $\psi_j$. The initial prefix is the singleton
$[j]$. Given a prefix $b$, the next prefix is determined as follows:
\begin{enumerate}
\item Search for a $y \geq |b|$ with $\varphi_{S(b)}(y) \downarrow= v$ for
some $v$.
\item Set the new prefix $b0^{y - |b|}\bar{v}$, where $\bar v = 1 - v$.
\end{enumerate}

Step~1 can diverge, for example, if $\varphi_{S(b)}$ is the empty function.
In this case $\psi_j$ will only be defined for a finite prefix. If, however,
Step~2 is reached, the prefix $b$ is extended to a $b'$ such that
$\varphi_{S(b)}(y) \neq b'_y$, which implies $S(b)$ is a wrong hypothesis for
every function starting with $b'$, in particular for $\psi_j$. Since $\bar v
\in \{0, 1\}$, Step~2 only appends zeros and ones, which is important for
showing membership in $V$.

This process defines a numbering $\psi \in \mathcal{P}^2$, and by Kleene's
fixed-point theorem there is a $j \geq 2$ with $\varphi_j = \psi_j$. For this
$j$ there are two cases:
\begin{enumerate}
\item[Case 1.] Step~1 always succeeds. Then $\psi_j$ is total and
  $\psi_j \in V_1$. But $S$ outputs wrong hypotheses on infinitely many
  prefixes of $\psi_j$ (namely every prefix constructed by the process).

\item[Case 2.] Step~1 diverges at some iteration, say when the state is $b = ja$
  for some $a \in \{0, 1\}^*$.
  Then $\psi_j$ has the form $ja\uparrow^\infty$. The numbering $\chi$ with $\chi_k =
  jak0^\infty$ is in $\mathcal{P}^2$, and by Kleene's fixed-point theorem there is a
  $k\geq 2$ with $\varphi_k = \chi_k = jak0^\infty$. This $jak0^\infty$ is in
  $V_2$ and has the prefix $ja$. But Step~1 diverged on this prefix, which
  means there is no $y \geq |ja|$ with $\varphi_{S(ja)}(y)\downarrow$. In
  other words $S$ hypothesizes a non-total function.
\end{enumerate}

Thus, in both cases there is a function in $V$ where $S$ does not behave like
a TOTAL strategy. This is the desired contradiction.

The following locale formalizes this proof sketch.\<close>

locale total_cons =
  fixes s :: partial1
  assumes s_in_R1: "s \<in> \<R>"
begin

definition r_s :: recf where
  "r_s \<equiv> SOME r_s. recfn 1 r_s \<and>  total r_s \<and> s = (\<lambda>x. eval r_s [x])"

lemma rs_recfn [simp]: "recfn 1 r_s"
  and rs_total [simp]: "\<And>x. eval r_s [x] \<down>"
  and eval_rs: "\<And>x. s x = eval r_s [x]"
  using r_s_def R1_SOME[OF s_in_R1, of r_s] by simp_all

text \<open>Performing Step~1 means enumerating the domain of
$\varphi_{S(b)}$ until a $y \geq |b|$ is found. The next function enumerates
all domain values and checks the condition for them.\<close>

definition "r_search_enum \<equiv>
  Cn 2 r_le [Cn 2 r_length [Id 2 1], Cn 2 r_enumdom [Cn 2 r_s [Id 2 1], Id 2 0]]"

lemma r_search_enum_recfn [simp]: "recfn 2 r_search_enum"
  by (simp add: r_search_enum_def Let_def)

abbreviation search_enum :: partial2 where
  "search_enum x b \<equiv> eval r_search_enum [x, b]"

abbreviation enumdom :: partial2 where
  "enumdom i y \<equiv> eval r_enumdom [i, y]"

lemma enumdom_empty_domain:
  assumes "\<And>x. \<phi> i x \<up>"
  shows "\<And>y. enumdom i y \<up>"
  using assms r_enumdom_empty_domain by (simp add: phi_def)

lemma enumdom_nonempty_domain:
  assumes "\<phi> i x\<^sub>0 \<down>"
  shows "\<And>y. enumdom i y \<down>"
   and "\<And>x. \<phi> i x \<down> \<longleftrightarrow> (\<exists>y. enumdom i y \<down>= x)"
  using assms r_enumdom_nonempty_domain phi_def by metis+

text \<open>Enumerating the empty domain yields the empty function.\<close>

lemma search_enum_empty:
  fixes b :: nat
  assumes "s b \<down>= i" and "\<And>x. \<phi> i x \<up>"
  shows "\<And>x. search_enum x b \<up>"
  using assms r_search_enum_def enumdom_empty_domain eval_rs by simp

text \<open>Enumerating a non-empty domain yields a total function.\<close>

lemma search_enum_nonempty:
  fixes b y0 :: nat
  assumes "s b \<down>= i" and "\<phi> i y\<^sub>0 \<down>" and "e = the (enumdom i x)"
  shows "search_enum x b \<down>= (if e_length b \<le> e then 0 else 1)"
proof -
  let ?e = "\<lambda>x. the (enumdom i x)"
  let ?y = "Cn 2 r_enumdom [Cn 2 r_s [Id 2 1], Id 2 0]"
  have "recfn 2 ?y" using assms(1) by simp
  moreover have "\<And>x. eval ?y [x, b] = enumdom i x"
    using assms(1,2) eval_rs by auto
  moreover from this have "\<And>x. eval ?y [x, b] \<down>"
    using enumdom_nonempty_domain(1)[OF assms(2)] by simp
  ultimately have "eval (Cn 2 r_le [Cn 2 r_length [Id 2 1], ?y]) [x, b] \<down>=
      (if e_length b \<le> ?e x then 0 else 1)"
    by simp
  then show ?thesis using assms by (simp add: r_search_enum_def)
qed

text \<open>If there is a $y$ as desired, the enumeration will eventually return
zero (representing ``true'').\<close>

lemma search_enum_nonempty_eq0:
  fixes b y :: nat
  assumes "s b \<down>= i" and "\<phi> i y \<down>" and "y \<ge> e_length b"
  shows "\<exists>x. search_enum x b \<down>= 0"
proof -
  obtain x where x: "enumdom i x \<down>= y"
    using enumdom_nonempty_domain(2)[OF assms(2)] assms(2) by auto
  from assms(2) have "\<phi> i y \<down>" by simp
  with x have "search_enum x b \<down>= 0"
    using search_enum_nonempty[where ?e=y] assms by auto
  then show ?thesis by auto
qed

text \<open>If there is no $y$ as desired, the enumeration will never return
zero.\<close>

lemma search_enum_nonempty_neq0:
  fixes b y0 :: nat
  assumes "s b \<down>= i"
    and "\<phi> i y\<^sub>0 \<down>"
    and "\<not> (\<exists>y. \<phi> i y \<down> \<and> y \<ge> e_length b)"
  shows "\<not> (\<exists>x. search_enum x b \<down>= 0)"
proof
  assume "\<exists>x. search_enum x b \<down>= 0"
  then obtain x where x: "search_enum x b \<down>= 0"
    by auto
  obtain y where y: "enumdom i x \<down>= y"
    using enumdom_nonempty_domain[OF assms(2)] by blast
  then have "search_enum x b \<down>= (if e_length b \<le> y then 0 else 1)"
    using assms(1-2) search_enum_nonempty by simp
  with x have "e_length b \<le> y"
    using option.inject by fastforce
  moreover have "\<phi> i y \<down>"
    using assms(2) enumdom_nonempty_domain(2) y by blast
  ultimately show False using assms(3) by force
qed

text \<open>The next function corresponds to Step~1. Given a prefix $b$ it
computes a $y \geq |b|$ with $\varphi_{S(b)}(y)\downarrow$ if such a $y$
exists; otherwise it diverges.\<close>

definition "r_search \<equiv> Cn 1 r_enumdom [r_s, Mn 1 r_search_enum]"

lemma r_search_recfn [simp]: "recfn 1 r_search"
  using r_search_def by simp

abbreviation search :: partial1 where
  "search b \<equiv> eval r_search [b]"

text \<open>If $\varphi_{S(b)}$ is the empty function, the search process
diverges because already the enumeration of the domain diverges.\<close>

lemma search_empty:
  assumes "s b \<down>= i" and "\<And>x. \<phi> i x \<up>"
  shows "search b \<up>"
proof -
  have "\<And>x. search_enum x b \<up>"
    using search_enum_empty[OF assms] by simp
  then have "eval (Mn 1 r_search_enum) [b] \<up>" by simp
  then show "search b \<up>" unfolding r_search_def by simp
qed

text \<open>If $\varphi_{S(b)}$ is non-empty, but there is no $y$ with the
desired properties, the search process diverges.\<close>

lemma search_nonempty_neq0:
  fixes b y0 :: nat
  assumes "s b \<down>= i"
    and "\<phi> i y\<^sub>0 \<down>"
    and "\<not> (\<exists>y. \<phi> i y \<down> \<and> y \<ge> e_length b)"
  shows "search b \<up>"
proof -
  have "\<not> (\<exists>x. search_enum x b \<down>= 0)"
    using assms search_enum_nonempty_neq0 by simp
  moreover have "recfn 1 (Mn 1 r_search_enum)"
    by (simp add: assms(1))
  ultimately have "eval (Mn 1 r_search_enum) [b] \<up>" by simp
  then show ?thesis using r_search_def by auto
qed

text \<open>If there is a $y$ as desired, the search process will return
one such $y$.\<close>

lemma search_nonempty_eq0:
  fixes b y :: nat
  assumes "s b \<down>= i" and "\<phi> i y \<down>" and "y \<ge> e_length b"
  shows "search b \<down>"
    and "\<phi> i (the (search b)) \<down>"
    and "the (search b) \<ge> e_length b"
proof -
  have "\<exists>x. search_enum x b \<down>= 0"
    using assms search_enum_nonempty_eq0 by simp
  moreover have "\<forall>x. search_enum x b \<down>"
    using assms search_enum_nonempty by simp
  moreover have "recfn 1 (Mn 1 r_search_enum)"
    by simp
  ultimately have
    1: "search_enum (the (eval (Mn 1 r_search_enum) [b])) b \<down>= 0" and
    2: "eval (Mn 1 r_search_enum) [b] \<down>"
    using eval_Mn_diverg eval_Mn_convergE[of 1 "r_search_enum" "[b]"]
    by (metis (no_types, lifting) One_nat_def length_Cons list.size(3) option.collapse,
      metis (no_types, lifting) One_nat_def length_Cons list.size(3))
  let ?x = "the (eval (Mn 1 r_search_enum) [b])"
  have "search b = eval (Cn 1 r_enumdom [r_s, Mn 1 r_search_enum]) [b]"
    unfolding r_search_def by simp
  then have 3: "search b = enumdom i ?x"
    using assms 2 eval_rs by simp
  then have "the (search b) = the (enumdom i ?x)" (is "?y = _")
    by simp
  then have 4: "search_enum ?x b \<down>= (if e_length b \<le> ?y then 0 else 1)"
    using search_enum_nonempty assms by simp
  from 3 have "\<phi> i ?y \<down>"
    using enumdom_nonempty_domain assms(2) by (metis option.collapse)
  then show "\<phi> i ?y \<down>"
    using phi_def by simp
  then show "?y \<ge> e_length b"
    using assms 4 1 option.inject by fastforce
  show "search b \<down>"
    using 3 assms(2) enumdom_nonempty_domain(1) by auto
qed

text \<open>The converse of the previous lemma states that whenever
the search process returns a value it will be one with the
desired properties.\<close>

lemma search_converg:
  assumes "s b \<down>= i" and "search b \<down>" (is "?y \<down>")
  shows "\<phi> i (the ?y) \<down>"
    and "the ?y \<ge> e_length b"
proof -
  have "\<exists>y. \<phi> i y \<down>"
    using assms search_empty by meson
  then have "\<exists>y. y \<ge> e_length b \<and> \<phi> i y \<down>"
    using search_nonempty_neq0 assms by meson
  then obtain y where y: "y \<ge> e_length b \<and> \<phi> i y \<down>" by auto
  then have "\<phi> i y \<down>"
    using phi_def by simp
  then show "\<phi> i (the (search b)) \<down>"
    and "(the (search b)) \<ge> e_length b"
    using y assms search_nonempty_eq0[OF assms(1) \<open>\<phi> i y \<down>\<close>] by simp_all
qed

text \<open>Likewise, if the search diverges, there is no appropriate $y$.\<close>

lemma search_diverg:
  assumes "s b \<down>= i" and "search b \<up>"
  shows "\<not> (\<exists>y. \<phi> i y \<down> \<and> y \<ge> e_length b)"
proof
  assume "\<exists>y. \<phi> i y \<down> \<and> y \<ge> e_length b"
  then obtain y where y: "\<phi> i y \<down>" "y \<ge> e_length b"
    by auto
  from y(1) have "\<phi> i y \<down>"
    by (simp add: phi_def)
  with y(2) search_nonempty_eq0 have "search b \<down>"
    using assms by blast
  with assms(2) show False by simp
qed

text \<open>Step~2 extends the prefix by a block of the shape $0^n\bar v$.
The next function constructs such a block for given $n$ and $v$.\<close>

definition "r_badblock \<equiv>
  let f = Cn 1 r_singleton_encode [r_not];
      g = Cn 3 r_cons [r_constn 2 0, Id 3 1]
  in Pr 1 f g"

lemma r_badblock_prim [simp]: "recfn 2 r_badblock"
  unfolding r_badblock_def by simp

lemma r_badblock: "eval r_badblock [n, v] \<down>= list_encode (replicate n 0 @ [1 - v])"
proof (induction n)
  case 0
  let ?f = "Cn 1 r_singleton_encode [r_not]"
  have "eval r_badblock [0, v] = eval ?f [v]"
    unfolding r_badblock_def by simp
  also have "... = eval r_singleton_encode [the (eval r_not [v])]"
    by simp
  also have "... \<down>= list_encode [1 - v]"
    by simp
  finally show ?case by simp
next
  case (Suc n)
  let ?g = "Cn 3 r_cons [r_constn 2 0, Id 3 1]"
  have "recfn 3 ?g" by simp
  have "eval r_badblock [(Suc n), v] = eval ?g [n, the (eval r_badblock [n , v]), v]"
    using \<open>recfn 3 ?g\<close> Suc by (simp add: r_badblock_def)
  also have "... = eval ?g [n, list_encode (replicate n 0 @ [1 - v]), v]"
    using Suc by simp
  also have "... = eval r_cons [0, list_encode (replicate n 0 @ [1 - v])]"
    by simp
  also have "... \<down>= e_cons 0 (list_encode (replicate n 0 @ [1 - v]))"
    by simp
  also have "... \<down>= list_encode (0 # (replicate n 0 @ [1 - v]))"
    by simp
  also have "... \<down>= list_encode (replicate (Suc n) 0 @ [1 - v])"
    by simp
  finally show ?case by simp
qed

lemma r_badblock_only_01: "e_nth (the (eval r_badblock [n, v])) i \<le> 1"
  using r_badblock by (simp add: nth_append)

lemma r_badblock_last: "e_nth (the (eval r_badblock [n, v])) n = 1 - v"
  using r_badblock by (simp add: nth_append)

text \<open>The following function computes the next prefix from the current
one. In other words, it performs Steps~1 and~2.\<close>

definition "r_next \<equiv>
  Cn 1 r_append
   [Id 1 0,
    Cn 1 r_badblock
     [Cn 1 r_sub [r_search, r_length],
      Cn 1 r_phi [r_s, r_search]]]"

lemma r_next_recfn [simp]: "recfn 1 r_next"
  unfolding r_next_def by simp

text \<open>The name @{text next} is unavailable, so we go for @{term nxt}.\<close>

abbreviation nxt :: partial1 where
  "nxt b \<equiv> eval r_next [b]"

lemma nxt_diverg:
  assumes "search b \<up>"
  shows "nxt b \<up>"
  unfolding r_next_def using assms by (simp add: Let_def)

lemma nxt_converg:
  assumes "search b \<down>= y"
  shows "nxt b \<down>=
     e_append b (list_encode (replicate (y - e_length b) 0 @ [1 - the (\<phi> (the (s b)) y)]))"
  unfolding r_next_def using assms r_badblock search_converg phi_def eval_rs
  by fastforce

lemma nxt_search_diverg:
  assumes "nxt b \<up>"
  shows "search b \<up>"
proof (rule ccontr)
  assume "search b \<down>"
  then obtain y where "search b \<down>= y" by auto
  then show False
    using nxt_converg assms by simp
qed

text \<open>If Step~1 finds a $y$, the hypothesis $S(b)$ is incorrect for
the new prefix.\<close>

lemma nxt_wrong_hyp:
  assumes "nxt b \<down>= b'" and "s b \<down>= i"
  shows "\<exists>y<e_length b'. \<phi> i y \<down>\<noteq> e_nth b' y"
proof -
  obtain y where y: "search b \<down>= y"
    using assms nxt_diverg by fastforce
  then have y_len: "y \<ge> e_length b"
    using assms search_converg(2) by fastforce
  then have b': "b' =
      (e_append b (list_encode (replicate (y - e_length b) 0 @ [1 - the (\<phi> i y)])))"
    using y assms nxt_converg by simp
  then have "e_nth b' y = 1 - the (\<phi> i y)"
    using y_len e_nth_append_big r_badblock r_badblock_last by auto
  moreover have "\<phi> i y \<down>"
    using search_converg y y_len assms(2) by fastforce
  ultimately have "\<phi> i y \<down>\<noteq> e_nth b' y"
    by (metis gr_zeroI less_numeral_extra(4) less_one option.sel zero_less_diff)
  moreover have "e_length b' = Suc y"
    using y_len e_length_append b' by auto
  ultimately show ?thesis by auto
qed

text \<open>If Step~1 diverges, the hypothesis $S(b)$ refers to a non-total
function.\<close>

lemma nxt_nontotal_hyp:
  assumes "nxt b \<up>" and "s b \<down>= i"
  shows "\<exists>x. \<phi> i x \<up>"
  using nxt_search_diverg[OF assms(1)] search_diverg[OF assms(2)] by auto

text \<open>The process only ever extends the given prefix.\<close>

lemma nxt_stable:
  assumes "nxt b \<down>= b'"
  shows "\<forall>x<e_length b. e_nth b x = e_nth b' x"
proof -
  obtain y where y: "search b \<down>= y"
    using assms nxt_diverg by fastforce
  then have "y \<ge> e_length b"
    using search_converg(2) eval_rs rs_total by fastforce
  show ?thesis
  proof (rule allI, rule impI)
    fix x assume "x < e_length b"
    let ?i = "the (s b)"
    have b': "b' =
        (e_append b (list_encode (replicate (y - e_length b) 0 @ [1 - the (\<phi> ?i y)])))"
      using assms nxt_converg[OF y] by auto
    then show "e_nth b x = e_nth b' x"
      using e_nth_append_small \<open>x < e_length b\<close> by auto
  qed
qed

text \<open>The following properties of @{term r_next} will be
used to show that some of the constructed functions are in the class
$V$.\<close>

lemma nxt_append_01:
  assumes "nxt b \<down>= b'"
  shows "\<forall>x. x \<ge> e_length b \<and> x < e_length b' \<longrightarrow>  e_nth b' x = 0 \<or> e_nth b' x = 1"
proof -
  obtain y where y: "search b \<down>= y"
    using assms nxt_diverg by fastforce
  let ?i = "the (s b)"
  have b': "b' = (e_append b (list_encode (replicate (y - e_length b) 0 @ [1 - the (\<phi> ?i y)])))"
    (is "b' = (e_append b ?z)")
    using assms y  nxt_converg prod_encode_eq by auto
  show ?thesis
  proof (rule allI, rule impI)
    fix x assume x: "e_length b \<le> x \<and> x < e_length b'"
    then have "e_nth b' x = e_nth ?z (x - e_length b)"
      using b' e_nth_append_big by blast
    then show "e_nth b' x = 0 \<or> e_nth b' x = 1"
      by (metis less_one nat_less_le option.sel r_badblock r_badblock_only_01)
  qed
qed

lemma nxt_monotone:
  assumes "nxt b \<down>= b'"
  shows "e_length b < e_length b'"
proof -
  obtain y where y: "search b \<down>= y"
    using assms nxt_diverg by fastforce
  let ?i = "the (s b)"
  have b': "b' =
      (e_append b (list_encode (replicate (y - e_length b) 0 @ [1 - the (\<phi> ?i y)])))"
    using assms y nxt_converg prod_encode_eq by auto
  then show ?thesis using e_length_append by auto
qed

text \<open>The next function computes the prefixes after each iteration of
the process @{term r_next} when started with the list $[j]$.\<close>

definition r_prefixes :: recf where
  "r_prefixes \<equiv> Pr 1 r_singleton_encode (Cn 3 r_next [Id 3 1])"

lemma r_prefixes_recfn [simp]: "recfn 2 r_prefixes"
  unfolding r_prefixes_def by (simp add: Let_def)

abbreviation prefixes :: partial2 where
  "prefixes t j \<equiv> eval r_prefixes [t, j]"

lemma prefixes_at_0: "prefixes 0 j \<down>= list_encode [j]"
  unfolding r_prefixes_def by simp

lemma prefixes_at_Suc:
  assumes "prefixes t j \<down>" (is "?b \<down>")
  shows "prefixes (Suc t) j = nxt (the ?b)"
  using r_prefixes_def assms by auto

lemma prefixes_at_Suc':
  assumes "prefixes t j \<down>= b"
  shows "prefixes (Suc t) j = nxt b"
  using r_prefixes_def assms by auto

lemma prefixes_prod_encode:
  assumes "prefixes t j \<down>"
  obtains b where "prefixes t j \<down>= b"
  using assms surj_prod_encode by force

lemma prefixes_converg_le:
  assumes "prefixes t j \<down>" and "t' \<le> t"
  shows "prefixes t' j \<down>"
  using r_prefixes_def assms eval_Pr_converg_le[of 1 _ _ "[j]"]
  by simp

lemma prefixes_diverg_add:
  assumes "prefixes t j \<up>"
  shows "prefixes (t + d) j \<up>"
  using r_prefixes_def assms eval_Pr_diverg_add[of 1 _ _ "[j]"]
  by simp

text \<open>Many properties of @{term r_prefixes} can be derived from similar
properties of @{term r_next}.\<close>

lemma prefixes_length:
  assumes "prefixes t j \<down>= b"
  shows "e_length b > t"
proof (insert assms, induction t arbitrary: b)
  case 0
  then show ?case using prefixes_at_0 prod_encode_eq by auto
next
  case (Suc t)
  then have "prefixes t j \<down>"
    using prefixes_converg_le Suc_n_not_le_n nat_le_linear by blast
  then obtain b' where b': "prefixes t j \<down>= b'"
    using prefixes_prod_encode by blast
  with Suc have "e_length b' > t" by simp
  have "prefixes (Suc t) j = nxt b'"
    using b' prefixes_at_Suc' by simp
  with Suc have "nxt b' \<down>= b" by simp
  then have "e_length b' < e_length b"
    using nxt_monotone by simp
  then show ?case using \<open>e_length b' > t\<close> by simp
qed

lemma prefixes_monotone:
  assumes "prefixes t j \<down>= b" and "prefixes (t + d) j \<down>= b'"
  shows "e_length b \<le> e_length b'"
proof (insert assms, induction d arbitrary: b')
  case 0
  then show ?case using prod_encode_eq by simp
next
  case (Suc d)
  moreover have "t + d \<le> t + Suc d" by simp
  ultimately have "prefixes (t + d) j \<down>"
    using prefixes_converg_le by blast
  then obtain b'' where b'': "prefixes (t + d) j \<down>= b''"
    using prefixes_prod_encode by blast
  with Suc have "prefixes (t + Suc d) j = nxt b''"
    by (simp add: prefixes_at_Suc')
  with Suc have "nxt b'' \<down>= b'" by simp
  then show ?case using nxt_monotone Suc b'' by fastforce
qed

lemma prefixes_stable:
  assumes "prefixes t j \<down>= b" and "prefixes (t + d) j \<down>= b'"
  shows "\<forall>x<e_length b. e_nth b x = e_nth b' x"
proof (insert assms, induction d arbitrary: b')
  case 0
  then show ?case using prod_encode_eq by simp
next
  case (Suc d)
  moreover have "t + d \<le> t + Suc d" by simp
  ultimately have "prefixes (t + d) j \<down>"
    using prefixes_converg_le by blast
  then obtain b'' where b'': "prefixes (t + d) j \<down>= b''"
    using prefixes_prod_encode by blast
  with Suc have "prefixes (t + Suc d) j = nxt b''"
    by (simp add: prefixes_at_Suc')
  with Suc have b': "nxt b'' \<down>= b'" by simp
  show "\<forall>x<e_length b. e_nth b x = e_nth b' x"
  proof (rule allI, rule impI)
    fix x assume x: "x < e_length b"
    then have "e_nth b x = e_nth b'' x"
      using Suc b'' by simp
    moreover have "x \<le> e_length b''"
      using x prefixes_monotone b'' Suc by fastforce
    ultimately show "e_nth b x = e_nth b' x"
      using b'' nxt_stable Suc b' prefixes_monotone x
      by (metis leD le_neq_implies_less)
  qed
qed

lemma prefixes_tl_only_01:
  assumes "prefixes t j \<down>= b"
  shows "\<forall>x>0. e_nth b x = 0 \<or> e_nth b x = 1"
proof (insert assms, induction t arbitrary: b)
  case 0
  then show ?case using prefixes_at_0 prod_encode_eq by auto
next
  case (Suc t)
  then have "prefixes t j \<down>"
    using prefixes_converg_le Suc_n_not_le_n nat_le_linear by blast
  then obtain b' where b': "prefixes t j \<down>= b'"
    using prefixes_prod_encode by blast
  show "\<forall>x>0. e_nth b x = 0 \<or> e_nth b x = 1"
  proof (rule allI, rule impI)
    fix x :: nat
    assume x: "x > 0"
    show "e_nth b x = 0 \<or> e_nth b x = 1"
    proof (cases "x < e_length b'")
      case True
      then show ?thesis
        using Suc b' prefixes_at_Suc' nxt_stable x by metis
    next
      case False
      then show ?thesis
        using Suc.prems b' prefixes_at_Suc' nxt_append_01 by auto
    qed
  qed
qed

lemma prefixes_hd:
  assumes "prefixes t j \<down>= b"
  shows "e_nth b 0 = j"
proof -
  obtain b' where b': "prefixes 0 j \<down>= b'"
    by (simp add: prefixes_at_0)
  then have "b' = list_encode [j]"
    by (simp add: prod_encode_eq prefixes_at_0)
  then have "e_nth b' 0 = j" by simp
  then show "e_nth b 0 = j"
    using assms prefixes_stable[OF b', of t b] prefixes_length[OF b'] by simp
qed

lemma prefixes_nontotal_hyp:
  assumes "prefixes t j \<down>= b"
    and "prefixes (Suc t) j \<up>"
    and "s b \<down>= i"
  shows "\<exists>x. \<phi> i x \<up>"
  using nxt_nontotal_hyp[OF _ assms(3)] assms(2) prefixes_at_Suc'[OF assms(1)] by simp

text \<open>We now consider the two cases from the proof sketch.\<close>

abbreviation "case_two j \<equiv> \<exists>t. prefixes t j \<up>"

abbreviation "case_one j \<equiv> \<not> case_two j"

text \<open>In Case~2 there is a maximum convergent iteration because
iteration 0 converges.\<close>

lemma case_two:
  assumes "case_two j"
  shows "\<exists>t. (\<forall>t'\<le>t. prefixes t' j \<down>) \<and> (\<forall>t'>t. prefixes t' j \<up>)"
proof -
  let ?P = "\<lambda>t. prefixes t j \<up>"
  define t\<^sub>0 where "t\<^sub>0 = Least ?P"
  then have "?P t\<^sub>0"
    using assms LeastI_ex[of ?P] by simp
  then have diverg: "?P t" if "t \<ge> t\<^sub>0" for t
    using prefixes_converg_le that by blast
  from t\<^sub>0_def have converg: "\<not> ?P t" if "t < t\<^sub>0" for t
    using Least_le[of ?P] that not_less by blast
  have "t\<^sub>0 > 0"
  proof (rule ccontr)
    assume "\<not> 0 < t\<^sub>0"
    then have "t\<^sub>0 = 0" by simp
    with \<open>?P t\<^sub>0\<close> prefixes_at_0 show False by simp
  qed
  let ?t = "t\<^sub>0 - 1"
  have "\<forall>t'\<le>?t. prefixes t' j \<down>"
    using converg \<open>0 < t\<^sub>0\<close> by auto
  moreover have "\<forall>t'>?t. prefixes t' j \<up>"
    using diverg by simp
  ultimately show ?thesis by auto
qed

text \<open>Having completed the modelling of the process, we can now define
the functions $\psi_j$ it computes. The value $\psi_j(x)$ is computed by
running @{term r_prefixes} until the prefix is longer than $x$ and then
taking the $x$-th element of the prefix.\<close>

definition "r_psi \<equiv>
  let f = Cn 3 r_less [Id 3 2, Cn 3 r_length [Cn 3 r_prefixes [Id 3 0, Id 3 1]]]
  in Cn 2 r_nth [Cn 2 r_prefixes [Mn 2 f, Id 2 0], Id 2 1]"

lemma r_psi_recfn: "recfn 2 r_psi"
  unfolding r_psi_def by simp

abbreviation psi :: partial2 ("\<psi>") where
  "\<psi> j x \<equiv> eval r_psi [j, x]"

lemma psi_in_P2: "\<psi> \<in> \<P>\<^sup>2"
  using r_psi_recfn by auto

text \<open>The values of @{term "\<psi>"} can be read off the prefixes.\<close>

lemma psi_eq_nth_prefix:
  assumes "prefixes t j \<down>= b" and "e_length b > x"
  shows "\<psi> j x \<down>= e_nth b x"
proof -
  let ?f = "Cn 3 r_less [Id 3 2, Cn 3 r_length [Cn 3 r_prefixes [Id 3 0, Id 3 1]]]"
  let ?P = "\<lambda>t. prefixes t j \<down> \<and> e_length (the (prefixes t j)) > x"
  from assms have ex_t: "\<exists>t. ?P t" by auto
  define t\<^sub>0 where "t\<^sub>0 = Least ?P"
  then have "?P t\<^sub>0"
    using LeastI_ex[OF ex_t] by simp
  from ex_t have not_P: "\<not> ?P t" if "t < t\<^sub>0" for t
    using ex_t that Least_le[of ?P] not_le t\<^sub>0_def by auto

  have "?P t" using assms by simp
  with not_P have "t\<^sub>0 \<le> t" using leI by blast
  then obtain b\<^sub>0 where b0: "prefixes t\<^sub>0 j \<down>= b\<^sub>0"
    using assms(1) prefixes_converg_le by blast

  have "eval ?f [t\<^sub>0, j, x] \<down>= 0"
  proof -
    have "eval (Cn 3 r_prefixes [Id 3 0, Id 3 1]) [t\<^sub>0, j, x] \<down>= b\<^sub>0"
      using b0 by simp
    then show ?thesis using \<open>?P t\<^sub>0\<close> by simp
  qed
  moreover have "eval ?f [t, j, x] \<down>\<noteq> 0" if "t < t\<^sub>0" for t
  proof -
    obtain bt where bt: "prefixes t j \<down>= bt"
      using prefixes_converg_le[of t\<^sub>0 j t] b0 \<open>t < t\<^sub>0\<close> by auto
    moreover have "\<not> ?P t"
      using that not_P by simp
    ultimately have "e_length bt \<le> x" by simp
    moreover have "eval (Cn 3 r_prefixes [Id 3 0, Id 3 1]) [t, j, x] \<down>= bt"
      using bt by simp
    ultimately show ?thesis by simp
  qed
  ultimately have "eval (Mn 2 ?f) [j, x] \<down>= t\<^sub>0"
    using eval_Mn_convergI[of 2 ?f "[j, x]" t\<^sub>0] by simp
  then have "\<psi> j x \<down>= e_nth b\<^sub>0 x"
    unfolding r_psi_def using b0 by simp
  then show ?thesis
    using \<open>t\<^sub>0 \<le> t\<close> assms(1) prefixes_stable[of t\<^sub>0 j b\<^sub>0 "t - t\<^sub>0" b] b0 \<open>?P t\<^sub>0\<close>
    by simp
qed

lemma psi_converg_imp_prefix:
  assumes "\<psi> j x \<down>"
  shows "\<exists>t b. prefixes t j \<down>= b \<and> e_length b > x"
proof -
  let ?f = "Cn 3 r_less [Id 3 2, Cn 3 r_length [Cn 3 r_prefixes [Id 3 0, Id 3 1]]]"
  have "eval (Mn 2 ?f) [j, x] \<down>"
  proof (rule ccontr)
    assume "\<not> eval (Mn 2 ?f) [j, x] \<down>"
    then have "eval (Mn 2 ?f) [j, x] \<up>" by simp
    then have "\<psi> j x \<up>"
      unfolding r_psi_def by simp
    then show False
      using assms by simp
  qed
  then obtain t where t: "eval (Mn 2 ?f) [j, x] \<down>= t"
    by blast
  have "recfn 2 (Mn 2 ?f)" by simp
  then have f_zero: "eval ?f [t, j, x] \<down>= 0"
    using eval_Mn_convergE[OF _ t]
    by (metis (no_types, lifting) One_nat_def Suc_1 length_Cons list.size(3))
  have "prefixes t j \<down>"
  proof (rule ccontr)
    assume "\<not> prefixes t j \<down>"
    then have "prefixes t j \<up>" by simp
    then have "eval ?f [t, j, x] \<up>" by simp
    with f_zero show False by simp
  qed
  then obtain b' where b': "prefixes t j \<down>= b'" by auto
  moreover have "e_length b' > x"
  proof (rule ccontr)
    assume "\<not> e_length b' > x"
    then have "eval ?f [t, j, x] \<down>= 1"
      using b' by simp
    with f_zero show False by simp
  qed
  ultimately show ?thesis by auto
qed

lemma psi_converg_imp_prefix':
  assumes "\<psi> j x \<down>"
  shows "\<exists>t b. prefixes t j \<down>= b \<and> e_length b > x \<and> \<psi> j x \<down>= e_nth b x"
  using psi_converg_imp_prefix[OF assms] psi_eq_nth_prefix by blast

text \<open>In both Case~1 and~2, $\psi_j$ starts with $j$.\<close>

lemma psi_at_0: "\<psi> j 0 \<down>= j"
  using prefixes_hd prefixes_length psi_eq_nth_prefix prefixes_at_0 by fastforce

text \<open>In Case~1, $\psi_j$ is total and made up of $j$ followed by zeros
and ones, just as required by the definition of $V_1$.\<close>

lemma case_one_psi_total:
  assumes "case_one j" and "x > 0"
  shows "\<psi> j x \<down>= 0 \<or> \<psi> j x \<down>= 1"
proof -
  obtain b where b: "prefixes x j \<down>= b"
    using assms(1) by auto
  then have "e_length b > x"
    using prefixes_length by simp
  then have "\<psi> j x \<down>= e_nth b x"
    using b psi_eq_nth_prefix by simp
  moreover have "e_nth b x = 0 \<or> e_nth b x = 1"
    using prefixes_tl_only_01[OF b] assms(2) by simp
  ultimately show "\<psi> j x \<down>= 0 \<or> \<psi> j x \<down>= 1"
    by simp
qed

text \<open>In Case~2, $\psi_j$ is defined only for a prefix starting with
$j$ and continuing with zeros and ones. This prefix corresponds to $ja$ from
the definition of $V_2$.\<close>

lemma case_two_psi_only_prefix:
  assumes "case_two j"
  shows "\<exists>y. (\<forall>x. 0 < x \<and> x < y \<longrightarrow> \<psi> j x \<down>= 0 \<or> \<psi> j x \<down>= 1) \<and>
                (\<forall>x \<ge> y. \<psi> j x \<up>)"
proof -
  obtain t where
    t_le: "\<forall>t'\<le>t. prefixes t' j \<down>" and
    t_gr: "\<forall>t'>t. prefixes t' j \<up>"
    using assms case_two by blast
  then obtain b where b: "prefixes t j \<down>= b"
    by auto
  let ?y = "e_length b"
  have "\<psi> j x \<down>= 0 \<or> \<psi> j x \<down>= 1" if "x > 0 \<and> x < ?y" for x
    using t_le b that by (metis prefixes_tl_only_01 psi_eq_nth_prefix)
  moreover have "\<psi> j x \<up>" if "x \<ge> ?y" for x
  proof (rule ccontr)
    assume "\<psi> j x \<down>"
    then obtain t' b' where t': "prefixes t' j \<down>= b'" and "e_length b' > x"
      using psi_converg_imp_prefix by blast
    then have "e_length b' > ?y"
      using that by simp
    with t' have "t' > t"
      using prefixes_monotone b by (metis add_diff_inverse_nat leD)
    with t' t_gr show False by simp
  qed
  ultimately show ?thesis by auto
qed

definition longest_prefix :: "nat \<Rightarrow> nat" where
  "longest_prefix j \<equiv> THE y. (\<forall>x<y. \<psi> j x \<down>) \<and> (\<forall>x\<ge>y. \<psi> j x \<up>)"

lemma longest_prefix:
  assumes "case_two j" and "z = longest_prefix j"
  shows "(\<forall>x<z. \<psi> j x \<down>) \<and> (\<forall>x\<ge>z. \<psi> j x \<up>)"
proof -
  let ?P = "\<lambda>z. (\<forall>x<z. \<psi> j x \<down>) \<and> (\<forall>x\<ge>z. \<psi> j x \<up>)"
  obtain y where y:
    "\<forall>x. 0 < x \<and> x < y \<longrightarrow> \<psi> j x \<down>= 0 \<or> \<psi> j x \<down>= 1"
    "\<forall>x\<ge>y. \<psi> j x \<up>"
    using case_two_psi_only_prefix[OF assms(1)] by auto
  have "?P (THE z. ?P z)"
  proof (rule theI[of ?P y])
    show "?P y"
    proof
      show "\<forall>x<y. \<psi> j x \<down>"
      proof (rule allI, rule impI)
        fix x assume "x < y"
        show "\<psi> j x \<down>"
        proof (cases "x = 0")
          case True
          then show ?thesis using psi_at_0 by simp
        next
          case False
          then show ?thesis using y(1) \<open>x < y\<close> by auto
        qed
      qed
      show "\<forall>x\<ge>y. \<psi> j x \<up>" using y(2) by simp
    qed
    show "z = y" if "?P z" for z
    proof (rule ccontr, cases "z < y")
      case True
      moreover assume "z \<noteq> y"
      ultimately show False
        using that \<open>?P y\<close> by auto
    next
      case False
      moreover assume "z \<noteq> y"
      then show False
        using that \<open>?P y\<close> y(2) by (meson linorder_cases order_refl)
    qed
  qed
  then have "(\<forall>x<(THE z. ?P z). \<psi> j x \<down>) \<and> (\<forall>x\<ge>(THE z. ?P z). \<psi> j x \<up>)"
    by blast
  moreover have "longest_prefix j = (THE z. ?P z)"
    unfolding longest_prefix_def by simp
  ultimately show ?thesis using assms(2) by metis
qed

lemma case_two_psi_longest_prefix:
  assumes "case_two j" and "y = longest_prefix j"
  shows "(\<forall>x. 0 < x \<and> x < y \<longrightarrow> \<psi> j x \<down>= 0 \<or> \<psi> j x \<down>= 1) \<and>
    (\<forall>x \<ge> y. \<psi> j x \<up>)"
  using assms longest_prefix case_two_psi_only_prefix
  by (metis prefixes_tl_only_01 psi_converg_imp_prefix')

text \<open>The prefix cannot be empty because the process starts with prefix $[j]$.\<close>

lemma longest_prefix_gr_0:
  assumes "case_two j"
  shows "longest_prefix j > 0"
  using assms case_two_psi_longest_prefix psi_at_0 by force

lemma psi_not_divergent_init:
  assumes "prefixes t j \<down>= b"
  shows "(\<psi> j) \<triangleright> (e_length b - 1) = b"
proof (intro initI)
  show "0 < e_length b"
    using assms prefixes_length by fastforce
  show "\<psi> j x \<down>= e_nth b x" if "x < e_length b" for x
    using that assms psi_eq_nth_prefix by simp
qed

text \<open>In Case~2, the strategy $S$ outputs a non-total hypothesis on
some prefix of $\psi_j$.\<close>

lemma case_two_nontotal_hyp:
  assumes "case_two j"
  shows "\<exists>n<longest_prefix j. \<not> total1 (\<phi> (the (s ((\<psi> j) \<triangleright> n))))"
proof -
  obtain t where "\<forall>t'\<le>t. prefixes t' j \<down>" and t_gr: "\<forall>t'>t. prefixes t' j \<up>"
    using assms case_two by blast
  then obtain b where b: "prefixes t j \<down>= b"
    by auto
  moreover obtain i where i: "s b \<down>= i"
    using eval_rs by fastforce
  moreover have div: "prefixes (Suc t) j \<up>"
    using t_gr by simp
  ultimately have "\<exists>x. \<phi> i x \<up>"
    using prefixes_nontotal_hyp by simp
  then obtain x where "\<phi> i x \<up>" by auto
  moreover have init: "\<psi> j \<triangleright> (e_length b - 1) = b" (is "_ \<triangleright> ?n = b")
    using psi_not_divergent_init[OF b] by simp
  ultimately have "\<phi> (the (s (\<psi> j \<triangleright> ?n))) x \<up>"
    using i by simp
  then have "\<not> total1 (\<phi> (the (s (\<psi> j \<triangleright> ?n))))"
    by auto
  moreover have "?n < longest_prefix j"
    using case_two_psi_longest_prefix init b div psi_eq_nth_prefix
    by (metis length_init lessI not_le_imp_less option.simps(3))
  ultimately show ?thesis by auto
qed

text \<open>Consequently, in Case~2 the strategy does not TOTAL-learn
any function starting with the longest prefix of $\psi_j$.\<close>

lemma case_two_not_learn:
  assumes "case_two j"
    and "f \<in> \<R>"
    and "\<And>x. x < longest_prefix j \<Longrightarrow> f x = \<psi> j x"
  shows "\<not> learn_total \<phi> {f} s"
proof -
  obtain n where n:
    "n < longest_prefix j"
    "\<not> total1 (\<phi> (the (s (\<psi> j \<triangleright> n))))"
    using case_two_nontotal_hyp[OF assms(1)] by auto
  have "f \<triangleright> n = \<psi> j \<triangleright> n"
    using assms(3) n(1) by (intro init_eqI) auto
  with n(2) show ?thesis by (metis R1_imp_total1 learn_totalE(3) singletonI)
qed

text \<open>In Case~1 the strategy outputs a wrong hypothesis
on infinitely many prefixes of $\psi_j$ and thus does not
learn $\psi_j$ in the limit, much less in the sense of TOTAL.\<close>

lemma case_one_wrong_hyp:
  assumes "case_one j"
  shows "\<exists>n>k. \<phi> (the (s ((\<psi> j) \<triangleright> n))) \<noteq> \<psi> j"
proof -
  have all_t: "\<forall>t. prefixes t j \<down>"
    using assms by simp
  then obtain b where b: "prefixes (Suc k) j \<down>= b"
    by auto
  then have length: "e_length b > Suc k"
    using prefixes_length by simp
  then have init: "\<psi> j \<triangleright> (e_length b - 1) = b"
    using psi_not_divergent_init b by simp
  obtain i where i: "s b \<down>= i"
    using eval_rs by fastforce
  from all_t obtain b' where b': "prefixes (Suc (Suc k)) j \<down>= b'"
    by auto
  then have "\<psi> j \<triangleright> (e_length b' - 1) = b'"
    using psi_not_divergent_init by simp
  moreover have "\<exists>y<e_length b'. \<phi> i y \<down>\<noteq> e_nth b' y"
    using nxt_wrong_hyp b b' i prefixes_at_Suc by auto
  ultimately have "\<exists>y<e_length b'. \<phi> i y \<noteq> \<psi> j y"
    using b' psi_eq_nth_prefix by auto
  then have "\<phi> i \<noteq> \<psi> j" by auto
  then show ?thesis
    using init length i by (metis Suc_less_eq length_init option.sel)
qed

lemma case_one_not_learn:
  assumes "case_one j"
  shows "\<not> learn_lim \<phi> {\<psi> j} s"
proof (rule infinite_hyp_wrong_not_Lim[of "\<psi> j"])
  show "\<psi> j \<in> {\<psi> j}" by simp
  show "\<forall>n. \<exists>m>n. \<phi> (the (s (\<psi> j \<triangleright> m))) \<noteq> \<psi> j"
    using case_one_wrong_hyp[OF assms] by simp
qed

lemma case_one_not_learn_V:
  assumes "case_one j" and "j \<ge> 2" and "\<phi> j = \<psi> j"
  shows "\<not> learn_lim \<phi> V_constotal s"
proof -
  have "\<psi> j \<in> V_constotal_1"
  proof -
    define p where "p = (\<lambda>x. (\<psi> j) (x + 1))"
    have "p \<in> \<R>\<^sub>0\<^sub>1"
    proof -
      from p_def have "p \<in> \<P>"
        using skip_P1[of "\<psi> j" 1] psi_in_P2 P2_proj_P1 by blast
      moreover have "p x \<down>= 0 \<or> p x \<down>= 1" for x
        using p_def assms(1) case_one_psi_total by auto
      moreover from this have "total1 p" by fast
      ultimately show ?thesis using RPred1_def by auto
    qed
    moreover have "\<psi> j = [j] \<odot> p"
      by (intro prepend_eqI, simp add: psi_at_0, simp add: p_def)
    ultimately show ?thesis using assms(2,3) V_constotal_1_def by blast
  qed
  then have "\<psi> j \<in> V_constotal" using V_constotal_def by auto
  moreover have "\<not> learn_lim \<phi> {\<psi> j} s"
    using case_one_not_learn assms(1) by simp
  ultimately show ?thesis using learn_lim_closed_subseteq by auto
qed

text \<open>The next lemma embodies the construction of $\chi$ followed by
the application of Kleene's fixed-point theorem as described in the
proof sketch.\<close>

lemma goedel_after_prefixes:
  fixes vs :: "nat list" and m :: nat
  shows "\<exists>n\<ge>m. \<phi> n = vs @ [n] \<odot> 0\<^sup>\<infinity>"
proof -
  define f :: partial1 where "f \<equiv> vs \<odot> 0\<^sup>\<infinity>"
  then have "f \<in> \<R>"
    using almost0_in_R1 by auto
  then obtain n where n:
    "n \<ge> m"
    "\<phi> n = (\<lambda>x. if x = length vs then Some n else f x)"
    using goedel_at[of f m "length vs"] by auto
  moreover have "\<phi> n x = (vs @ [n] \<odot> 0\<^sup>\<infinity>) x" for x
  proof -
    consider "x < length vs" | "x = length vs" | "x > length vs"
      by linarith
    then show ?thesis
      using n f_def by (cases) (auto simp add: prepend_associative)
  qed
  ultimately show ?thesis by blast
qed

text \<open>If Case~2 holds for a $j\geq 2$ with $\varphi_j = \psi_j$, that
is, if $\psi_j\in V_1$, then there is a function in $V$, namely $\psi_j$, on
which $S$ fails. Therefore $S$ does not learn $V$.\<close>

lemma case_two_not_learn_V:
  assumes "case_two j" and "j \<ge> 2" and "\<phi> j = \<psi> j"
  shows "\<not> learn_total \<phi> V_constotal s"
proof -
  define z where "z = longest_prefix j"
  then have "z > 0"
    using longest_prefix_gr_0[OF assms(1)] by simp
  define vs where "vs = prefix (\<psi> j) (z - 1)"
  then have "vs ! 0 = j"
    using psi_at_0 \<open>z > 0\<close> by simp
  define a where "a = tl vs"
  then have vs: "vs = j # a"
    using vs_def \<open>vs ! 0 = j\<close>
    by (metis length_Suc_conv length_prefix list.sel(3) nth_Cons_0)
  obtain k where k: "k \<ge> 2" and phi_k: "\<phi> k = j # a @ [k] \<odot> 0\<^sup>\<infinity>"
    using goedel_after_prefixes[of 2 "j # a"] by auto
  have phi_j: "\<phi> j = j # a \<odot> \<up>\<^sup>\<infinity> "
  proof (rule prepend_eqI)
    show "\<And>x. x < length (j # a) \<Longrightarrow> \<phi> j x \<down>= (j # a) ! x"
      using assms(1,3) vs vs_def \<open>0 < z\<close>
        length_prefix[of "\<psi> j" "z - 1"]
        prefix_nth[of _ _ "\<psi> j"]
        psi_at_0[of j]
        case_two_psi_longest_prefix[OF _ z_def]
        longest_prefix[OF _ z_def]
      by (metis One_nat_def Suc_pred option.collapse)
    show "\<And>x. \<phi> j (length (j # a) + x) \<up>"
      using assms(3) vs_def
      by (simp add: vs assms(1) case_two_psi_longest_prefix z_def)
  qed
  moreover have "\<phi> k \<in> V_constotal_2"
  proof (intro V_constotal_2I[of _ j a k])
    show "\<phi> k = j # a @ [k] \<odot> 0\<^sup>\<infinity>"
      using phi_k .
    show "2 \<le> j"
      using \<open>2 \<le> j\<close> .
    show "2 \<le> k"
      using \<open>2 \<le> k\<close> .
    show "\<forall>i<length a. a ! i \<le> 1"
    proof (rule allI, rule impI)
      fix i assume i: "i < length a"
      then have "Suc i < z"
        using z_def vs_def length_prefix \<open>0 < z\<close> vs
        by (metis One_nat_def Suc_mono Suc_pred length_Cons)
      have "a ! i = vs ! (Suc i)"
        using vs by simp
      also have "... = the (\<psi> j (Suc i))"
        using vs_def vs i length_Cons length_prefix prefix_nth
        by (metis Suc_mono)
      finally show "a ! i \<le> 1"
        using case_two_psi_longest_prefix \<open>Suc i < z\<close> z_def
        by (metis assms(1) less_or_eq_imp_le not_le_imp_less not_one_less_zero
          option.sel zero_less_Suc)
    qed
  qed (auto simp add: phi_j)
  then have "\<phi> k \<in> V_constotal"
    using V_constotal_def by auto
  moreover have "\<not> learn_total \<phi> {\<phi> k} s"
  proof -
    have "\<phi> k \<in> \<R>"
      by (simp add: phi_k almost0_in_R1)
    moreover have "\<And>x. x < longest_prefix j \<Longrightarrow> \<phi> k x = \<psi> j x"
      using phi_k vs_def z_def length_prefix phi_j prepend_associative prepend_at_less
      by (metis One_nat_def Suc_pred \<open>0 < z\<close> \<open>vs = j # a\<close> append_Cons assms(3))
    ultimately show ?thesis
      using case_two_not_learn[OF assms(1)] by simp
  qed
  ultimately show "\<not> learn_total \<phi> V_constotal s"
    using learn_total_closed_subseteq by auto
qed

text \<open>The strategy $S$ does not learn $V$ in either case.\<close>

lemma not_learn_total_V: "\<not> learn_total \<phi> V_constotal s"
proof -
  obtain j where "j \<ge> 2" "\<phi> j = \<psi> j"
    using kleene_fixed_point psi_in_P2 by auto
  then show ?thesis
    using case_one_not_learn_V learn_total_def case_two_not_learn_V
    by (cases "case_two j") auto
qed

end


lemma V_not_in_TOTAL: "V_constotal \<notin> TOTAL"
proof (rule ccontr)
  assume "\<not> V_constotal \<notin> TOTAL"
  then have "V_constotal \<in> TOTAL" by simp
  then have "V_constotal \<in> TOTAL_wrt \<phi>"
    by (simp add: TOTAL_wrt_phi_eq_TOTAL)
  then obtain s where "learn_total \<phi> V_constotal s"
    using TOTAL_wrt_def by auto
  then obtain s' where s': "s' \<in> \<R>" "learn_total \<phi> V_constotal s'"
    using lemma_R_for_TOTAL_simple by blast
  then interpret total_cons s'
    by (simp add: total_cons_def)
  have "\<not> learn_total \<phi> V_constotal s'"
    by (simp add: not_learn_total_V)
  with s'(2) show False by simp
qed

lemma TOTAL_neq_CONS: "TOTAL \<noteq> CONS"
  using V_not_in_TOTAL V_in_CONS CONS_def by auto

text \<open>The main result of this section:\<close>

theorem TOTAL_subset_CONS: "TOTAL \<subset> CONS"
  using TOTAL_subseteq_CONS TOTAL_neq_CONS by simp

end