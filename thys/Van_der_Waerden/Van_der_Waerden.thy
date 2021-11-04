theory Van_der_Waerden
  imports Main "HOL-Library.FuncSet" Digits
begin

section \<open>Van der Waerden's Theorem\<close>

text \<open>In combinatorics, Van der Waerden's Theorem is about arithmetic progressions of a certain
length of the same colour in a colouring of an interval. In order to state the theorem and to
prove it, we need to formally introduce arithmetic progressions. We will express $k$-colourings as
functions mapping an integer interval to the set $\{0,\dots , k-1 \}$ of colours.\<close>

subsection \<open>Arithmetic progressions\<close>

text \<open>A sequence of integer numbers with the same step size is called an arithmetic progression.
 We say an  $m$-fold arithmetic progression is an arithmetic progression with multiple step 
lengths.\<close>

text \<open> Arithmetic progressions are defined in the following using the variables:

\begin{tabular}{lcp{8cm}}
$start$:& \<open>int\<close>& starting value\\
$step$:&  \<open>nat\<close>& positive integer for step length\\
$i$:&     \<open>nat\<close>& $i$-th value in the arithmetic progression \\
\end{tabular}\<close>

definition arith_prog :: "int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int"
  where "arith_prog start step i = start + int (i * step)"

text \<open> An $m$-fold arithmetic progression (which we will also call a multi-arithmetic progression)
is defined in the following using the variables:

\begin{tabular}{lcp{8cm}}
$dims$:&   \<open>nat\<close>& number of dimensions/step directions of $m$-fold arithmetic progression\\
$start$:&  \<open>int\<close>& starting value\\
$steps$:&  \<open>nat \<Rightarrow> nat\<close>& function of steps, returns step in $i$-th dimension for $i\in[0..<dims]$\\
$c$:&      \<open>nat \<Rightarrow> nat\<close>& function of coefficients, returns coefficient in $i$-th dimension for 
           $i\in[0..<dims]$ \\
\end{tabular}\<close>

definition multi_arith_prog :: 
    "nat \<Rightarrow> int \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> int"
  where "multi_arith_prog dims start steps c = 
           start + int (\<Sum>i<dims. c i * steps i)"

text \<open>An $m$-fold arithmetic progression of dimension $1$ is also an arithmetic progression and 
  vice versa. This is shown in the following lemmas.\<close>
lemma multi_to_arith_prog: 
  "multi_arith_prog 1 start steps c = 
    arith_prog start (steps 0) (c 0)"
  unfolding multi_arith_prog_def arith_prog_def by auto

lemma arith_prog_to_multi: 
  "arith_prog start step c = 
    multi_arith_prog 1 start (\<lambda>_. step) (\<lambda>_. c)"
  unfolding multi_arith_prog_def arith_prog_def by auto

text \<open>To show that an arithmetic progression is well-defined, we introduce the following predicate.
It assures that \<open>arith_prog start step ` [0..<l]\<close> is contained in the integer interval $[a..b]$.\<close>
definition is_arith_prog_on :: 
    "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" 
  where "is_arith_prog_on l start step a b \<longleftrightarrow>
    (start \<ge> a \<and> arith_prog start step (l-1) \<le> b)"

text \<open>Furthermore, we have monotonicity for arithmetic progressions.\<close>
lemma arith_prog_mono: 
  assumes "c \<le> c'"
  shows   "arith_prog start step c \<le> arith_prog start step c'"
  using assms unfolding arith_prog_def by (auto intro: mult_mono)

text \<open>Now, we state the well-definedness of an arithmetic progression of length $l$ in an integer
interval $[a..b]$. 
Indeed, \<open>is_arith_prog_on\<close> guarantees that every element of \<open>arith_prog start step\<close> of length $l$ 
  lies in $[a..b]$.\<close>
lemma is_arith_prog_onD:
  assumes "is_arith_prog_on l start step a b"
  assumes "c \<in> {0..<l}"
  shows   "arith_prog start step c \<in> {a..b}"
proof -
  have "arith_prog start step 0 \<le> arith_prog start step c"
    by (rule arith_prog_mono) auto
  hence "arith_prog start step c \<ge> a"
    using assms by (simp add: arith_prog_def is_arith_prog_on_def 
                      add_increasing2)
  moreover have "arith_prog start step (l-1) \<ge> 
                   arith_prog start step c"
    by (rule arith_prog_mono) (use assms(2) in auto)
  hence "arith_prog start step c \<le> b"
    using assms unfolding arith_prog_def is_arith_prog_on_def 
    by linarith
  ultimately show ?thesis
    by auto
qed

text \<open>We also need a predicate for an $m$-fold arithmetic progression to be well-defined. 
It assures that \<open>multi_arith_prog start step ` [0..<l]^m\<close> is contained in $[a..b]$.\<close>
definition is_multi_arith_prog_on :: 
    "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" 
  where "is_multi_arith_prog_on l m start steps a b \<longleftrightarrow>
     (start \<ge> a \<and> multi_arith_prog m start steps (\<lambda>_. l-1) \<le> b)"

text \<open>Moreover, we have monotonicity for $m$-fold arithmetic progressions as well.\<close>
lemma multi_arith_prog_mono:
  assumes "\<And>i. i < m \<Longrightarrow> c i \<le> c' i"
  shows   "multi_arith_prog m start steps c \<le> 
            multi_arith_prog m start steps c'"
  using assms unfolding multi_arith_prog_def 
  by (auto intro!: sum_mono intro: mult_right_mono)

text \<open>Finally, we get the well-definedness for $m$-fold arithmetic progressions of length $l$.
Here, \<open>is_multi_arith_prog_on\<close> guarantees that every element of \<open>multi_arith_prog start step\<close> 
  of length $l$ lies in $[a..b]$.\<close>
lemma is_multi_arith_prog_onD:
  assumes "is_multi_arith_prog_on l m start steps a b"
  assumes "c \<in> {0..<m} \<rightarrow> {0..<l}"
  shows   "multi_arith_prog m start steps c \<in> {a..b}"
proof -
  have "multi_arith_prog m start steps (\<lambda>_. 0) \<le> 
          multi_arith_prog m start steps c"
    by (rule multi_arith_prog_mono) auto
  hence "multi_arith_prog m start steps c \<ge> a"
    using assms by (simp add: multi_arith_prog_def 
       is_multi_arith_prog_on_def)
  moreover have "multi_arith_prog m start steps (\<lambda>_. l-1) \<ge> 
                   multi_arith_prog m start steps c"
    by (rule multi_arith_prog_mono) (use assms in force)
  hence "multi_arith_prog m start steps c \<le> b"
    using assms by (simp add: multi_arith_prog_def 
        is_multi_arith_prog_on_def)
  ultimately show ?thesis
    by auto
qed


subsection \<open>Van der Waerden's Theorem\<close>

text \<open>The property for a number $n$ to fulfill Van der Waerden's theorem is the following:\\
For a $k$-colouring col of $[a..b]$ there exist
\begin{itemize}
\item $start$: starting value of an arithmetic progression
\item $step$:  step length of an arithmetic progression
\item $j$: colour 
\end{itemize}
such that \<open>arith_prog start step\<close> is a valid arithmetic progression of length $l$ lying 
in $[a..b]$ of the same colour $j$.

The following variables will be used:\\
\begin{tabular}{lcp{8cm}}
$k$:& \<open>nat\<close>& number of colours in segment colouring on $[a..b]$\\
$l$:& \<open>nat\<close>& length of arithmetic progression\\
$n$:& \<open>nat\<close>& number fulfilling Van der Waerden's Theorem\\
\end{tabular}
\<close>
definition vdw :: 
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" 
  where "vdw k l n \<longleftrightarrow>
     (\<forall>a b col. b + 1 \<ge> a + int n \<and> col \<in> {a..b} \<rightarrow> {..<k} \<longrightarrow>
       (\<exists>j start step. j < k \<and> step > 0 \<and> 
        is_arith_prog_on l start step a b \<and>
        arith_prog start step ` {..<l} \<subseteq> col -` {j} \<inter> {a..b}))"

text \<open>To better work with the property of Van der Waerden's theorem, we introduce an 
  elimination rule.\<close>
lemma vdwE:
  assumes "vdw k l n"
          "b + 1 \<ge> a + int n" 
          "col \<in> {a..b} \<rightarrow> {..<k}"
  obtains j start step where
    "j < k" "step > 0" 
    "is_arith_prog_on l start step a b"
    "arith_prog start step ` {..<l} \<subseteq> col -` {j} \<inter> {a..b}"
  using assms that unfolding vdw_def by metis

text \<open>Van der Waerden's theorem implies that the number fulfilling it is positive. This is show 
in the following lemma.\<close>
lemma vdw_imp_pos:
  assumes "vdw k l n" 
          "l > 0"
  shows "n > 0"
proof (rule Nat.gr0I)
  assume [simp]: "n = 0"
  show False
    using assms 
    by (elim vdwE[where a = 1 and b = 0 and col = "\<lambda>_. 0"]) 
       (auto simp: lessThan_empty_iff)
qed

text \<open>Van der Waerden's Theorem is trivial for a non-existent colouring. 
It also makes no sense for arithmetic progressions of length 0.\<close>
lemma vdw_0_left [simp, intro]: "n>0 \<Longrightarrow> vdw 0 l n"
  by (auto simp: vdw_def)

text \<open>In the case of $k=1$, Van der Waerden's Theorem holds. Then every number has the same colour,
hence also the arithmetic progression. A possible choice for the number fulfilling Van der 
Waerden Theorem is $l$.\<close>
lemma vdw_1_left: 
  assumes "l>0" 
  shows "vdw 1 l l"
unfolding vdw_def
proof (safe, goal_cases)
  case (1 a b col)
  have "arith_prog a 1 ` {..<l} \<subseteq> {a..b}"
    using 1(1) by (auto simp: arith_prog_def)
  also have "{a..b} = col -` {0} \<inter> {a..b}"
    using 1(2) by auto
  finally have "arith_prog a 1 ` {..<l} \<subseteq> col -` {0} \<inter> {a..b}"
    by auto
  moreover have "is_arith_prog_on l a 1 a b" 
    unfolding is_arith_prog_on_def arith_prog_def using 1 assms 
    by auto
  ultimately show "\<exists>j start step. j < 1 \<and> 0 < step \<and> 
        is_arith_prog_on l start step a b \<and>
        arith_prog start step ` {..<l} \<subseteq> col -` {j} \<inter> {a..b}"
    by auto
qed

text \<open>In the case $l=1$, Van der Waerden's Theorem holds. As the length of the arithmetic 
progression is $1$, it consists of just one element. Thus every nonempty integer interval fulfills 
the Van der Waerden property. We can prove $N_{k,1}$ to be $1$.\<close>
lemma vdw_1_right: "vdw k 1 1"
unfolding vdw_def 
proof safe
  fix a b :: int and col :: "int \<Rightarrow> nat"
  assume *: "a + int 1 \<le> b + 1" "col \<in> {a..b} \<rightarrow> {..<k}"
  have "col a < k" using * by auto
  have "arith_prog a 1 ` {..<1} = {a}"
    using *(1) by (auto simp: arith_prog_def)
  also have "{a} \<subseteq> col -` {col a} \<inter> {a..b}"
    using * by auto
  finally have "arith_prog a 1 ` {..<1} \<subseteq> col -` {col a} \<inter> {a..b}"
    by auto
  moreover have "is_arith_prog_on 1 a 1 a b" 
    unfolding is_arith_prog_on_def arith_prog_def
    using * by auto
  ultimately show  "\<exists>j start step.
          j < k \<and> 0 < step \<and> is_arith_prog_on 1 start step a b \<and>
          arith_prog start step ` {..<1} \<subseteq> col -` {j} \<inter> {a..b}"
    using \<open>col a <k\<close> by blast
qed

text \<open>In the case $l=2$, Van der Waerden's Theorem holds as well. Here, any two distinct numbers 
form an arithmetic progression of length $2$. Thus we only have to find two numbers with the same 
colour.
Using the pigeonhole principle on $k+1$ values, we can find two integers with the same colour.\<close>
lemma vdw_2_right: "vdw k 2 (k+1)"
unfolding vdw_def 
proof safe
  fix a b :: int and col :: "int \<Rightarrow> nat"
  assume *: "a + int (k + 1) \<le> b + 1" "col \<in> {a..b} \<rightarrow> {..<k}"

  have "col ` {a..b} \<subseteq> {..<k}" using *(2) by auto
  moreover have "k+1 \<le> card {a..b}" using *(1) by auto
  ultimately have "card (col ` {a..b}) < card {a..b}" using * 
    by (metis card_lessThan card_mono finite_lessThan le_less_trans 
        less_add_one not_le)
  then have "\<not> inj_on col {a..b}" using pigeonhole[of col "{a..b}"]
    by auto
  then obtain start start_step 
    where pigeon: "col start = col start_step" 
      "start < start_step"
      "start \<in> {a..b}" 
      "start_step \<in> {a..b}" 
    using inj_onI[of "{a..b}" col] 
    by (metis not_less_iff_gr_or_eq)

  define step where "step = nat (start_step - start)"
  define j where "j = col start"

  have "j < k" unfolding j_def using *(2) pigeon(3) by auto 
  moreover have "0 < step" unfolding step_def using pigeon(2) by auto
  moreover have "is_arith_prog_on 2 start step a b" 
    unfolding is_arith_prog_on_def arith_prog_def step_def 
    using pigeon by auto
  moreover {
  have "arith_prog start step i \<in> {start, start_step}" if "i<2" for i
    using that arith_prog_def step_def by (auto simp: less_2_cases_iff)
  also have "\<dots> \<subseteq> col -` {j} \<inter> {a..b}" 
    using pigeon unfolding j_def by auto
  finally have "arith_prog start step ` {..<2} \<subseteq> col -` {j} \<inter> {a..b}" 
    by auto
  }
  ultimately show "\<exists>j start step.
          j < k \<and>
          0 < step \<and>
          is_arith_prog_on 2 start step a b \<and>
          arith_prog start step ` {..<2} \<subseteq> col -` {j} \<inter> {a..b}" by blast
qed

text \<open>In order to prove Van der Waerden's Theorem, we first prove a slightly different lemma.
The statement goes as follows:\\
For a $k$-colouring $col$ on $[a..b]$ there exist
\begin{itemize}
\item  $start$: starting value of an arithmetic progression
\item  $steps$: step length of an arithmetic progression
\end{itemize}
such that \<open>f = multi_arith_prog m start step\<close> is a valid $m$-fold arithmetic progression of 
length $l$ lying in $[a..b]$ such that for every $s<m$ have: if $c j < l$ for all $j\leq s$ then
$f(c_0, c_1, \dots, c_{m-1})$ and $f(0,\dots,0, c_{s+1},\dots, c_{m-1})$ have the same colour.

The property of the lemma uses the following variables:\\
\begin{tabular}{lcp{8cm}}
$k$:& \<open>nat\<close>& number of colours in segment colouring of $[a..b]$\\
$m$:& \<open>nat\<close>& dimension of $m$-fold arithmetic progression\\
$l$:& \<open>nat\<close>& $l+1$ is length of $m$-fold arithmetic progression\\
$n$:& \<open>nat\<close>& number fulfilling \<open>vdw_lemma\<close>\\
\end{tabular}
\<close>
definition vdw_lemma :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "vdw_lemma k m l n \<longleftrightarrow>
     (\<forall>a b col. b + 1 \<ge> a + int n \<and> col \<in> {a..b} \<rightarrow> {..<k} \<longrightarrow>
       (\<exists>start steps. (\<forall>i<m. steps i > 0) \<and> 
        is_multi_arith_prog_on (l+1) m start steps a b \<and> (
           let f = multi_arith_prog m start steps
           in  (\<forall>c \<in> {0..<m} \<rightarrow> {0..l}. \<forall>s<m. (\<forall> j \<le> s. c j < l) \<longrightarrow>
                  col (f c) = col (f (\<lambda>i. if i \<le> s then 0 else c i))))))"

text \<open>To better work with this property, we introduce an elimination rule for \<open>vdw_lemma\<close>.\<close>
lemma vdw_lemmaE:
  fixes a b :: int
  assumes "vdw_lemma k m l n"
    "b + 1 \<ge> a + int n" "col \<in> {a..b} \<rightarrow> {..<k}"
  obtains start steps where
    "\<And>i. i < m \<Longrightarrow> steps i > 0"
    "is_multi_arith_prog_on (l+1) m start steps a b"
    "let f = multi_arith_prog m start steps
     in  \<forall>c \<in> {0..<m} \<rightarrow> {0..l}. \<forall>s<m. (\<forall> j \<le> s. c j < l) \<longrightarrow>
            col (f c) = col (f (\<lambda>i. if i \<le> s then 0 else c i))"
  using assms that unfolding vdw_lemma_def by blast

text \<open>To simplify the following proof, we show the following formula.\<close>
lemma sum_mod_poly: 
  assumes "(k::nat)>0" 
  shows "(k - 1) * (\<Sum> n\<in>{..<q}. k^n) < k^q "
proof -
  have "int ((k - 1) * (\<Sum>n<q. k ^ n)) = 
        (int k - 1) * (\<Sum>n<q. int k ^ n)"
    using assms by (simp add: of_nat_diff)
  also have "\<dots> = int k ^ q - 1"
    by (induction q) (auto simp: algebra_simps)
  also have "\<dots> < int (k ^ q)"
    by simp
  finally show ?thesis by linarith
qed

text \<open>The proof of Van der Waerden's Theorem now proceeds in three steps:\\
\begin{itemize}
\item Firstly, we show that the \<open>vdw\<close> property for all $k$ proves the \<open>vdw_lemma\<close> for fixed $l$ but 
arbitrary $k$ and $m$. This is done by induction over $m$.
\item Secondly, we show that \<open>vdw_lemma\<close> implies the induction step of \<open>vdw\<close> using the pigeonhole 
principle.
\item Lastly, we combine the previous steps in an induction over $l$ to show Van der Waerden's 
Theorem in the general setting.
\end{itemize}\<close>

text \<open>Firstly, we need to show that \<open>vdw\<close> for arbitrary $k$ implies \<open>vdw_lemma\<close> for fixed $l$.
As mentioned earlier, we use induction over $m$.\<close>
lemma vdw_imp_vdw_lemma:
  fixes l
  assumes vdw_assms: "\<And>k'. k'>0 \<Longrightarrow> \<exists>n_k'. vdw k' l n_k'"
    and "l \<ge> 2"
    and "m > 0"
    and "k > 0"
  shows   "\<exists>N. vdw_lemma k m l N"
using \<open>m>0\<close> \<open>k>0\<close> proof (induction m rule: less_induct)
  case (less m)
  consider  "m=1" | "m>1" using less.prems by linarith
  then show ?case 
  proof cases
    text \<open> Case $m=1$: Show \<open>vdw_lemma\<close> for arithmetic progression, Induction start. \<close>
    assume "m = 1"

    obtain n where vdw: "vdw k l n" using vdw_assms \<open>k>0\<close> by blast
    define N where "N = 2*n"
    have "l>0" and "l>1" using \<open>l\<ge>2\<close> by auto

    have "vdw_lemma k m l N"
      unfolding vdw_lemma_def
    proof (safe, goal_cases)
      case (1 a b col)
      text \<open> Divide $[a..b]$ in two intervals $I_1$, $I_2$ of same length and obtain arithmetic 
        progression of length $l$ in $I_1$. \<close>
      have col_restr: "col \<in> {a..a + int n - 1} \<rightarrow> {..<k}"
        using 1 by (auto simp: N_def)
      then obtain j start step where prog:
        "j < k" "step > 0" 
        "is_arith_prog_on l start step a (a + int n -1)"
        "arith_prog start step ` {..<l} \<subseteq> 
          col -` {j} \<inter> {a..a + int n - 1}"
        using vdw 1 unfolding N_def by (elim vdwE)(auto simp:is_arith_prog_on_def)
      have range_prog_lessThan_l: 
        "arith_prog start step i \<in> {a..a + int n -1}" if "i < l" for i
        using that prog by auto

      have "{a..a + int n-1}\<subseteq>{a..b}" using N_def "1"(1) by auto 
      then have "a + 2* int n - 1 \<le> b" using 1(1) unfolding N_def 
        by auto

      text \<open> Show that \<open>arith_prog start step\<close> is an arithmetic progression of length $l+1$
         in $[a..b]$. \<close>
      have prog_in_ivl: "arith_prog start step i \<in> {a..b}" 
        if "i \<le> l" for i
      proof (cases "i=l")
        case False
        have "i<l" using that False by auto
        then show ?thesis 
          using range_prog_lessThan_l \<open>{a..a + int n-1}\<subseteq>{a..b}\<close> by force
      next
        case True
        text \<open> Show $\<open>step\<close>\leq |I_1|$ then have \<open>arith_prog start step (l+1)\<in>[a..b]\<close> as 
           \<open>arith_prog start step (l+1) = arith_prog start step l + step\<close> \<close>
        have "start \<in> {a..a + int n -1}" 
          using range_prog_lessThan_l[of 0] 
          unfolding arith_prog_def by (simp add: \<open>0 < l\<close>)
        moreover have "start + int step \<in> {a..a + int n -1}" 
          using range_prog_lessThan_l[of 1] 
          unfolding arith_prog_def by (metis \<open>1 < l\<close> mult.left_neutral)
        ultimately have "step \<le> n" by auto
        have "arith_prog start step (l-1) \<in> {a..a + int n -1}" 
          using range_prog_lessThan_l[of "l-1"] unfolding arith_prog_def
          using \<open>0 < l\<close> diff_less less_numeral_extra(1) by blast
        moreover have "arith_prog start step l = 
                        arith_prog start step (l-1) + int step"
          unfolding arith_prog_def using \<open>0 < l\<close> mult_eq_if by force
        ultimately have "arith_prog start step l \<in> {a..b}" 
          using \<open>step\<le>n\<close> N_def \<open>a + 2* int n -1 \<le> b\<close> by auto
        then show ?thesis using range_prog_lessThan_l using True 
          by force
      qed

      have col_prog_eq: "col (arith_prog start step k) = j" 
        if "k < l" for k
        using prog that by blast
      
      define steps :: "nat \<Rightarrow> nat" where steps_def: "steps = (\<lambda>i. step)"
      define f where "f = multi_arith_prog 1 start steps"
      
      have rel_prop_1: 
        "col (f c) = col (f (\<lambda>i. if i < s then 0 else c i))"
        if "c \<in> {0..<1} \<rightarrow> {0..l}" "s<1" "\<forall>j\<le>s. c j < l" for c s 
        using that by auto

      have arith_prog_on: 
        "is_multi_arith_prog_on (l+1) m start steps a b"
        using prog(3) unfolding is_arith_prog_on_def is_multi_arith_prog_on_def
        using \<open>m=1\<close> arith_prog_to_multi steps_def prog_in_ivl by auto
      
      show ?case
        by (rule exI[of _ start], rule exI[of _ steps])
           (use rel_prop_1 \<open>step > 0\<close> \<open>m = 1\<close> arith_prog_on col_prog_eq
             multi_to_arith_prog in \<open>auto simp: f_def Let_def steps_def\<close>)
    qed
    then show ?case ..

  next
    text \<open> Case $m>1$: Show \<open>vdw_lemma\<close> for $m$-fold arithmetic progression, 
          Induction step $(m-1) \longrightarrow m$. \<close>
    assume "m>1"

    obtain q where vdw_lemma_IH:"vdw_lemma k (m-1) l q" 
      using \<open>1 < m\<close> less by force
    have "k^q>0" using \<open>k>0\<close> by auto
    obtain n_kq where vdw: "vdw (k^q) l n_kq" 
      using vdw_assms \<open>k^q>0\<close> by blast
    define N where "N = q + 2 * n_kq"

    text \<open>Idea: $[a..b] = I_1 \cup I_2$ where $|I_1| = 2*n_{k,q}$ and $|I_2| = q$.
                Divide $I_1$ into blocks of length $q$ and define a new colouring on the set of 
                $q$-blocks where the colour of the block is the $k$-basis representation where 
                the $i$-th digit corresponds to the colour of the $i$-th element in the block. 
                Get an arithmetic progression of $q$-blocks of length $l+1$ in $I_1$, such that
                the first $l$ $q$-blocks have the same colour. 
                The step of the block-arithmetic progression is going to be the additional 
                step in the induction over $m$. \<close>

    have "vdw_lemma k m l N"
      unfolding vdw_lemma_def
    proof (safe, goal_cases)
      case (1 a b col)
      have "n_kq>0" using vdw_imp_pos vdw \<open>l\<ge>2\<close> by auto
      then have "N>0" by (simp add:N_def)
      then have "a\<le>b" using 1 by auto
      then have "k>0" using 1 by (intro Nat.gr0I) force
      have "l>0" and "l>1" using \<open>l\<ge>2\<close> by auto
      interpret digits k by (simp add: \<open>0 < k\<close> digits_def)
      define col1 where "col1 = (\<lambda> x. from_digits q (\<lambda>y. col (x + y)))" 
      have range_col1: "col1\<in>{a..a + int n_kq - 1} \<rightarrow> {..<k^q}" 
      unfolding Pi_def
      proof safe
        fix x assume "x\<in>{a..a + int n_kq - 1}"
        then have col_xn:"col (x + int n)\<in>{..<k}" if "n<q" for n :: nat
          using that 1 PiE N_def by auto
        have col_xn_upper_bound:"col (x + int n) \<le> k - 1" 
          if "n<q" for n ::nat
          using that col_xn[of n] \<open>k>0\<close> by (auto)
        have "(\<Sum>n<q. col (x + int n) * k ^ n)\<le> 
               (\<Sum>n<q. (k-1) *  k ^ n)"
          using col_xn_upper_bound by (intro sum_mono mult_right_mono) 
            auto
        also have "\<dots> = (k-1) * (\<Sum>n<q. k ^ n)"
          by (rule sum_distrib_left[symmetric])
        also have "\<dots> < k^q" using sum_mod_poly \<open>k>0\<close> by auto        
        finally show "col1 x <k^q" unfolding col1_def from_digits_altdef 
          by auto 
      qed

      obtain j start step where prog:
        "j < k^q" "step > 0" 
        "is_arith_prog_on l start step a (a + int n_kq - 1)"
        "arith_prog start step ` {..<l} \<subseteq> 
          col1 -` {j} \<inter> {a..a + int n_kq -1}"
        using vdw range_col1 by (elim vdwE) (auto simp: \<open>k>0\<close>) 

      have range_prog_lessThan_l: 
        "arith_prog start step i \<in> {a..a + int n_kq -1}" 
        if "i < l" for i
        using that prog by auto

      have prog_in_ivl: 
        "arith_prog start step i \<in> {a..a + 2 * int n_kq -1}" 
        if "i \<le> l" for i
      proof (cases "i=l")
        case False
        then have "i<l" using that by auto
        then show ?thesis using prog by auto
      next
        case True
        have "start \<in> {a..a + int n_kq -1}" 
          using range_prog_lessThan_l[of 0] unfolding arith_prog_def 
          by (simp add: \<open>0 < l\<close>)
        moreover have "start + step \<in> {a..a + int n_kq -1}" 
          using range_prog_lessThan_l[of 1] unfolding arith_prog_def 
          by (metis \<open>1 < l\<close> mult.left_neutral)
        ultimately have "step \<le> n_kq" by auto
        have "arith_prog start step (l-1) \<in> {a..a + int n_kq -1}" 
          using range_prog_lessThan_l[of "l-1"] unfolding arith_prog_def
          using \<open>0 < l\<close> diff_less less_numeral_extra(1) by blast
        moreover have "arith_prog start step l = 
            arith_prog start step (l-1) + step"
          unfolding arith_prog_def using \<open>0 < l\<close> mult_eq_if by force
        ultimately have "arith_prog start step l \<in> 
            {a..a + 2 * int n_kq - 1}" 
          using \<open>step\<le>n_kq\<close> by auto
        then show ?thesis using range_prog_lessThan_l using True 
          by force
      qed

      have col_prog_eq: "col1 (arith_prog start step k) = j" 
        if "k < l" for k
        using prog that by blast

      have digit_col1:"digit (col1 x) y = col (x+int y)" 
        if "x\<in>{a..<a + 2*int n_kq}" "y\<in>{..<q}" 
        for x::int and y::nat unfolding col1_def using that
      proof -
        have "\<And>j'. j'<q \<Longrightarrow> x+j'\<in>{a..b}" 
          using "1"(1) N_def that(1) by force
        then have "\<And>j'. j'<q \<Longrightarrow> (\<lambda>y. col (x+int y)) j' < k" 
          using 1 that by auto
        then show "digit (from_digits q (\<lambda>xa. col (x + int xa))) y = 
                    col (x + int y)" 
          using digit_from_digits that 1 by auto
      qed

      text \<open> Impact on the colour when taking the block-step. \<close>
      have one_step_more:
        "col (arith_prog start' step i) = digit j (nat (start'-start))" 
        if "start'\<in>{start..<start+q}" "i\<in>{..<l}" for start' i
      proof -
        have "start \<le> start'" using that by simp
        have shift_arith_prog:
          "arith_prog start step i + (start' - start) = 
            arith_prog start' step i" 
          unfolding arith_prog_def by simp
        define diff where "diff = nat (start'-start)"
        have "diff \<in>{..<q}" using that unfolding diff_def by auto
        have "col (arith_prog start step i + int diff) = digit j diff"
        proof -
          have "col1 (arith_prog start step i) = j" 
            using col1_def prog that by blast
          moreover have " arith_prog start step i\<in>{a..a + 2 * int n_kq-1}"
            using prog(4) that by auto
          ultimately show ?thesis 
            using digit_col1[where x = "arith_prog start step i" 
                and y = "diff"] 
              prog 1 \<open>diff \<in>{..<q}\<close> by auto
        qed
        then show ?thesis unfolding diff_def 1
          by (auto simp: \<open>start\<le>start'\<close> shift_arith_prog) 
      qed

      have one_step_more': "col (arith_prog start' step i) =
        col (arith_prog start' step 0)"
        if "start'\<in>{start..<start+q}" "i\<in>{..<l}" for start' i
        using that one_step_more[of start' 0] 
          one_step_more[of start' i] by auto

      have start_q: "start + int q \<le> start + int q - 1 + 1" by linarith
      have "{start..start + int q-1} \<subseteq> {a..b}"
        using prog N_def 1(1) by (force simp: arith_prog_def is_arith_prog_on_def)  
      then have col': "col \<in> {start..start + int q-1} \<rightarrow> {..<k}"
        using 1 prog(4) by auto

      text \<open> Obtain an $(m-1)$-fold arithmetic progression in the starting $q$-bolck of the 
             block arithmetic progression. \<close>
      obtain start_m steps_m where
        step_m_pos: "\<And>i. i < m - 1 \<Longrightarrow> 0 < steps_m i" and
        is_multi_arith_prog: "is_multi_arith_prog_on (l+1) (m - 1) 
          start_m steps_m start (start + int q - 1)" and
        g_aux: "let g = multi_arith_prog (m - 1) start_m steps_m
          in  \<forall>c\<in>{0..<m - 1} \<rightarrow> {0..l}. \<forall>s<m - 1. (\<forall>j\<le>s. c j < l) \<longrightarrow>
          col (g c) = col (g (\<lambda>i. if i \<le> s then 0 else c i))"
        by (rule vdw_lemmaE[OF vdw_lemma_IH start_q col']) blast
        
      define g where "g = multi_arith_prog (m-1) start_m steps_m"
      have g: "col (g c) = col (g (\<lambda>i. if i \<le> s then 0 else c i))"
        if "c \<in> {0..<(m-1)} \<rightarrow> {0..l}" "s < m - 1" "\<forall>j \<le> s. c j < l"
        for c s using g_aux that unfolding g_def Let_def by blast

      have range_g: "g c \<in> {start..start + int q - 1}"
        if "c \<in> {0..<m - 1} \<rightarrow> {0..<(l+1)}" for c
        using is_multi_arith_prog_onD[OF is_multi_arith_prog that] 
        by (auto simp: g_def)

      text \<open>Obtain an $m$-fold arithmetic progression by adding the block-step.\<close>
      define steps :: "nat \<Rightarrow> nat" where steps_def: 
        "steps = (\<lambda>i.  (if i=0 then step else steps_m (i-1)))"
      define f where "f = multi_arith_prog m start_m steps"
      have f_step_g: "f c = int (c 0*step) + g (c \<circ> Suc)" for c
      proof -
        have "f c = start_m + int (\<Sum>i<Suc (m-1). c i * steps i)"
          using f_def unfolding multi_arith_prog_def 
          using less.prems by auto 
        also have "\<dots> = start_m + int (c 0 * steps 0) + 
                       int (\<Sum>i<m-1. c (Suc i) * steps (Suc i))"
          using sum.lessThan_Suc_shift[where n = "m-1"] by auto
        also have "\<dots> = start_m + int (c 0 * step) + 
                       int (\<Sum>i<m-1. c (Suc i) * steps_m i)"
          using steps_def by (auto split:if_splits)
        finally show ?thesis unfolding multi_arith_prog_def g_def 
          by simp
      qed

      text \<open> Show that this $m$-fold arithmetic progression fulfills all needed properties. \<close>
      have steps_gr_0: "\<forall>i<m. 0 < steps i" 
        unfolding steps_def using step_m_pos prog by auto

      have is_multi_on_f: 
        "is_multi_arith_prog_on (l+1) m start_m steps a b"
      proof -
        have "a \<le> start_m" using is_multi_arith_prog 
          unfolding is_multi_arith_prog_on_def
          using is_arith_prog_on_def prog(3) by force
        moreover {
          have "f (\<lambda>_. l) = arith_prog (g ((\<lambda>_. l) \<circ> Suc)) step l" 
            using f_step_g unfolding arith_prog_def by auto
          also have "g ((\<lambda>_. l) \<circ> Suc) \<le> start + q" 
            using range_g[of "(\<lambda>_. l) \<circ> Suc"] by auto
          then have "arith_prog (g ((\<lambda>_. l) \<circ> Suc)) step l \<le> 
            arith_prog start step l + q"
            unfolding arith_prog_def by auto
          also have "\<dots>\<le> b" using prog_in_ivl[of l]
            using is_multi_arith_prog unfolding is_multi_arith_prog_on_def
            using "1"(1) N_def by auto
          finally have "f (\<lambda>_. l) \<le> b" by auto
         }
         ultimately show ?thesis 
           unfolding is_multi_arith_prog_on_def f_def by auto
      qed

      text \<open> Show the relational property for all $s$. \<close>
      have rel_prop_1: 
        "col (f c) = col (f (\<lambda>i. if i \<le> s then 0 else c i))"
        if "c \<in> {0..<m} \<rightarrow> {0..l}" "s<m" "\<forall>j\<le>s. c j < l" for c s 
      proof (cases "s = 0")
        case True
        have "c 0 < l" using that(3) True by auto
        have range_c_Suc: "c \<circ> Suc \<in> {0..<m-1} \<rightarrow> {0..l}" 
          using that(1) by auto
        have "f c = arith_prog (g (c \<circ> Suc)) step (c 0)" 
          using f_step_g unfolding arith_prog_def by auto
        then have "col (f c) = col (arith_prog (g (c \<circ> Suc)) step 0)"
          using one_step_more'[of "g (c \<circ> Suc)" "c 0"] \<open>c 0 < l\<close>
            range_g[of "c \<circ> Suc"] range_c_Suc 
            atLeastLessThanSuc_atLeastAtMost by auto
        also {
          have "(\<Sum>x<m - 1. int (c (Suc x)) * int (steps_m x)) =
                   (\<Sum>x=1..<m. int(c x) * int (steps x))"
            by(rule sum.reindex_bij_witness[of _ "(\<lambda>x. x-1)" "Suc"]) 
              (auto simp: steps_def split:if_splits) 
          also have "\<dots> = (\<Sum>x<m. int (if x = 0 then 0 else c x) * 
            int (steps x))" 
            by (rule sum.mono_neutral_cong_left) auto
          finally have "arith_prog (g (c \<circ> Suc)) step 0 = 
            f (\<lambda>i. if i \<le> s then 0 else c i)" 
            unfolding f_def g_def multi_arith_prog_def arith_prog_def
            using True by auto
      }
        finally show ?thesis by auto
      next 
        case False
        hence s_greater_0: "s > 0" by auto
        have range_c_Suc: "c \<circ> Suc \<in> {0..<m-1} \<rightarrow> {0..l}" 
          using that(1) by auto
        have "c 0 < l" using \<open>s>0\<close> that by auto
        have g_IH:
          "col (g c') = col (g (\<lambda>i. if i \<le> s' then 0 else c' i))" 
          if "c' \<in> {0..<m-1} \<rightarrow> {0..l}" "s'<m-1" "\<forall>j\<le>s'. c' j < l" 
          for c' s' 
          using g_aux that unfolding multi_arith_prog_def g_def
          by (auto simp: Let_def)
        have g_shift_IH: "col (g (c \<circ> Suc)) = 
          col (g ((\<lambda>i. if i\<in>{1..t} then 0 else c i) \<circ> Suc))" 
          if "c \<in> {1..<m} \<rightarrow> {0..l}" "t\<in>{1..<m}" "\<forall>j\<in>{1..t}. c j < l"
          for c t
        proof -
          have "(\<lambda>i. (if i \<le> t - 1 then 0 else (c \<circ> Suc) i)) =
                (\<lambda>i. (if i \<in> {1..t} then 0 else c i)) \<circ> Suc"
            using that by (auto split: if_splits simp:fun_eq_iff)
          then have right: 
            "g (\<lambda>i. if i \<le> (t-1) then 0 else (c \<circ> Suc) i) = 
             g ((\<lambda>i. if i\<in>{1..t} then 0 else c i) \<circ> Suc)" by auto
          have "(c \<circ> Suc)\<in> {0..<m-1} \<rightarrow> {0..l}" using that(1) by auto
          moreover have "t-1<m-1" using that(2) by auto
          moreover have"\<forall>j\<le>t-1. (c \<circ> Suc) j < l" using that by auto
          ultimately have "col (g (c \<circ> Suc)) = 
            col (g (\<lambda>i. (if i \<le> t-1 then 0 else (c \<circ> Suc) i)))"
            using g_IH[of "(c \<circ> Suc)" "t-1"] by auto
          with right show ?thesis by auto
        qed

        have "col (f c) = col (int (c 0 * step) + g (c \<circ> Suc))" 
          using f_step_g by simp
        also have "int (c 0 * step) + g (c \<circ> Suc) = 
          arith_prog (g (c \<circ> Suc)) step (c 0)"
          by (simp add: arith_prog_def)
        also have "col \<dots> = col (arith_prog (g (c \<circ> Suc)) step 0)" 
          using one_step_more'[of "g (c \<circ> Suc)" "c 0"] \<open>c 0 < l\<close> 
            range_g[of "c \<circ> Suc"] range_c_Suc 
            atLeastLessThanSuc_atLeastAtMost by auto
        also have "\<dots> = col (g (c \<circ> Suc))"
          unfolding arith_prog_def by auto
        also have "\<dots> = col (g ((\<lambda>i. if  i\<in>{1..s} then 0 else c i) \<circ>
          Suc))" using g_shift_IH[of "c" s] \<open>s>0\<close> that by force
        also have "\<dots> = col ((\<lambda>c. int (c 0 * step) + 
          g (c \<circ> Suc))(\<lambda>i. if i\<le>s then 0 else c i))" 
          by (auto simp: g_def multi_arith_prog_def)
        also have "\<dots> = col (f (\<lambda>i. if i \<le> s then 0 else c i))" 
          unfolding f_step_g by auto
        finally show ?thesis by simp
      qed

      show ?case
        by (rule exI[of _ start_m], rule exI[of _ steps])
           (use steps_gr_0 is_multi_on_f rel_prop_1 in 
             \<open>auto simp: f_def Let_def steps_def\<close>)
    qed
    then show ?case ..
  qed
qed




text \<open> Secondly, we show that \<open>vdw_lemma\<close> implies the induction step of Van der Waerden's Theorem
using the pigeonhole principle. \<close>
lemma vdw_lemma_imp_vdw:
  assumes "vdw_lemma k k l N"
  shows   "vdw k (Suc l) N"
unfolding vdw_def proof (safe, goal_cases)
text \<open>Idea: Proof uses pigeonhole principle to guarantee the existence of an arithmetic 
            progression of length $l+1$ with the same colour. \<close>
  case (1 a b col)
  obtain start steps where prog:
    "\<And>i. i < k \<Longrightarrow> steps i > 0"
    "is_multi_arith_prog_on (l+1) k start steps a b"
    "let f = multi_arith_prog k start steps
     in  \<forall>c \<in> {0..<k} \<rightarrow> {0..l}. \<forall>s<k. (\<forall> j \<le> s. c j < l) \<longrightarrow>
            col (f c) = col (f (\<lambda>i. if i \<le> s then 0 else c i))"
    using assms 1 
    by (elim vdw_lemmaE[where a=a and b=b and col=col and m=k 
          and k=k and l=l and n=N]) auto

  text \<open> Obtain a $k$-fold arithmetic progression $f$ of length $l$ from assumptions. \<close>
  define f where "f = multi_arith_prog k start steps" 
  have rel_propE: "col (f c) = col (f (\<lambda>i. if i \<le> s then 0 else c i))"
    if "c \<in> {0..<k} \<rightarrow> {0..l}" "s<k" "\<forall> j \<le> s. c j < l"
    for c s
    using prog(3) that unfolding f_def Let_def by auto

  text \<open>There are $k+1$ values $a_r = f(0,\dots,0,l,\dots,l)$ with $0\leq r\leq k$ zeros.\<close>
  define a_r where "a_r = (\<lambda>r. f (\<lambda>i. (if i<r then 0 else l)))"
  have range_col_a_r: "col (a_r x) < k" if "x < k+1" for x 
  proof -
    have "a_r x \<in> {a..b}" unfolding a_r_def f_def 
      by (intro is_multi_arith_prog_onD[OF prog(2)]) auto
    thus ?thesis using 1 by blast
  qed
  then have "(col \<circ> a_r) ` {..<k + 1} \<subseteq> {..<k}" using 1(2) by auto
  then have "card ((col \<circ> a_r) ` {..<k + 1}) \<le> card {..<k}"
    by (intro card_mono) auto
  then have "\<not> inj_on (col \<circ> a_r) {..<k+1}" 
    using pigeonhole[of "col \<circ> a_r" "{..<k+1}"] by auto
  text \<open>Using the pigeonhole principle get $r_1$ and $r_2$ where $a_{r_1}$ and $a_{r_2}$ have the 
    same colour.\<close>
  then obtain r1 r2 where pigeon_cols:
      "r1\<in>{..<k+1}" 
      "r2\<in>{..<k+1}" 
      "r1 < r2" 
      "(col \<circ> a_r) r1 = (col \<circ> a_r) r2"
    by (metis (mono_tags, lifting) linear linorder_inj_onI)
  text \<open> Show that the following function $h$ is an arithmetic progression which fulfills all
         properties for Van der Waerden's Theorem. \<close>
  define h where 
    "h = (\<lambda>x. f (\<lambda>i. (if i<r1 then 0 else (if i<r2 then x else l))))"
  have "h 0 = a_r r2" unfolding h_def a_r_def using \<open>r1<r2\<close> 
    by (intro arg_cong[where f = f]) auto
  moreover have "h l = a_r r1"  unfolding h_def a_r_def using \<open>r1<r2\<close>
    by (metis le_eq_less_or_eq less_le_trans)
  ultimately have "col (h 0) = col (h l)" using pigeon_cols(4) by auto
  have h_col: "col (h 0) = col (h i)" if "i\<in>{..<l+1}" for i
  proof (cases "i=l")
    case True
    then show ?thesis using \<open>col (h 0) = col (h l)\<close> by auto
  next
    case False
    then have "i<l" using that by auto
    let ?c = "(\<lambda>idx. if idx < r1 then 0 else if idx < r2 then i else l)"
    have "?c\<in>{0..<k} \<rightarrow> {0..l}" 
      using that by auto
    moreover have "(\<forall>j\<le>r2-1. ?c j < l)" 
      using \<open>i<l\<close> pigeon_cols(3) by force
    ultimately have "col (f ?c) = 
      col (f (\<lambda>i. if i \<le> r2-1 then 0 else ?c i))"
      using rel_propE[of ?c "r2-1"] pigeon_cols by simp
    then show ?thesis unfolding h_def f_def 
      by (smt (z3) Nat.lessE One_nat_def add_diff_cancel_left' 
          le_less less_Suc_eq_le multi_arith_prog_mono plus_1_eq_Suc)
  qed

  define h_start where "h_start = start + l*(\<Sum>i\<in>{r2..<k}. steps i)"
  define h_step where "h_step = (\<Sum>i\<in>{r1..<r2}. steps i)"
  have h_arith_prog: "h = arith_prog h_start h_step" 
  proof -
    have "(\<Sum>x<k. int (if x < r1 then 0 else if x < r2 then y else l)
        * int (steps x)) =
      int l * (\<Sum>x = r2..<k. int (steps x)) + 
        int y * (\<Sum>x = r1..<r2. int (steps x))"
      for y 
    proof (cases "r2 = k")
      case True
      then have "r1<k" using pigeon_cols by auto
      with True have 
        "(\<Sum>x<k. int (if x < r1 then 0 else if x < r2 then y else l)
           * int (steps x)) =
         (\<Sum>x<k. int (if x < r1 then 0 else y) * int (steps x))"
        by (intro sum.cong) auto
      also have "\<dots> = (\<Sum>x<r1. int (if x < r1 then 0 else y) *
          int (steps x)) + (\<Sum>x=r1..<k. int (if x < r1 then 0 else y)
          * int (steps x))"
        using split_sum_mid_less[of r1 k 
            "(\<lambda>x. int (if x < r1 then 0 else y) * int (steps x))"] 
            \<open>r1<k\<close> by auto
      also have "\<dots> = (\<Sum>x=r1..<k. int y * int (steps x))" by auto
      also have "\<dots> = int y * (\<Sum>x=r1..<k. int (steps x))" 
        by (auto simp: sum_distrib_left[of "int y"])
      finally show ?thesis using True by auto
    next
      case False
      then have "r2<k" using pigeon_cols by auto
      define aux_left where "aux_left = 
        (\<lambda>x. int (if x < r1 then 0 else if x < r2 then y else l)
          * int (steps x))"
      have "(\<Sum>x<k. aux_left x) = (\<Sum>x=r1..<k. aux_left x)"
        by (intro sum.mono_neutral_right) (auto simp: aux_left_def)
      also have "{r1..<k} = {r1..<r2} \<union> {r2..<k}"
        using \<open>r1 < r2\<close> \<open>r2 < k\<close> by auto
      also have "(\<Sum>x\<in>\<dots>. aux_left x) = (\<Sum>x=r1..<r2. aux_left x) + 
        (\<Sum>x=r2..<k. aux_left x)"
        by (intro sum.union_disjoint) auto
      also have "(\<Sum>x=r1..<r2. aux_left x) =
        (\<Sum>x=r1..<r2. int y * int (steps x))"
        by (intro sum.cong) (auto simp: aux_left_def)
      also have "(\<Sum>x=r2..<k. aux_left x) = 
        (\<Sum>x=r2..<k. int l * int (steps x))"
        using \<open>r1 < r2\<close> by (intro sum.cong) (auto simp: aux_left_def)
      finally show ?thesis
        by (simp add: aux_left_def sum_distrib_left)
    qed
    then show ?thesis
      unfolding arith_prog_def h_start_def h_step_def h_def f_def
        multi_arith_prog_def by (auto split:if_splits)
  qed

  define j where "j = col (h 0)"
  have case_j: "j<k" using 1 range_col_a_r \<open>col (h 0) = col (h l)\<close> 
      \<open>h l = a_r r1\<close> j_def pigeon_cols(1) by auto
  have case_step: "h_step > 0" unfolding h_step_def
    using pigeon_cols by (intro sum_pos prog(1)) auto

  have range_h: "h i \<in> {a..b}" if "i < l + 1" for i
    unfolding h_def f_def by (rule is_multi_arith_prog_onD[OF prog(2)])
      (use that in auto)

  have case_on: "is_arith_prog_on (l+1) h_start h_step a b"
    unfolding is_arith_prog_on_def h_arith_prog 
    using range_h[of 0] range_h[of l]
    by (auto simp: Max_ge[of "{a..b}"] Min_le[of "{a..b}"] 
        h_arith_prog arith_prog_def)

  have case_col: "h ` {..<Suc l} \<subseteq> col -` {j} \<inter> {a..b}" 
    using h_col range_h unfolding j_def by auto

  show ?case using case_j case_step case_on case_col 
    by (auto simp: h_arith_prog) 
qed

text \<open> Lastly, we assemble all lemmas to finally prove Van der Waerden's Theorem by induction on 
$l$. The cases $l=1$ and the induction start $l=2$ are treated separately and have been shown 
earlier.\<close>
theorem van_der_Waerden: assumes "l>0" "k>0" shows "\<exists>n. vdw k l n"
using assms proof (induction l arbitrary: k rule: less_induct)
  case (less l)
  consider  "l=1" | "l=2" | "l>2" using less.prems by linarith
  then show ?case
  proof (cases)
    assume "l=1"
    then show ?thesis using vdw_1_right by auto
  next
    assume "l=2"
    then show ?thesis using vdw_2_right by auto
  next
    assume "l > 2"
    then have "2\<le>l-1" by auto
    from less.IH[of "l-1"] \<open>l>2\<close> 
    have "\<And>k'. k'>0 \<Longrightarrow> \<exists>n. vdw k' (l-1) n" by auto
    with vdw_imp_vdw_lemma[of "l-1" k k] \<open>l-1\<ge>2\<close> \<open>k>0\<close> 
      obtain N where "vdw_lemma k k (l-1) N" by auto
    then have "vdw k l N" using vdw_lemma_imp_vdw[of k "l-1" N]
      by (simp add: less.prems(1))
    then show ?thesis by auto
  qed
qed

end
