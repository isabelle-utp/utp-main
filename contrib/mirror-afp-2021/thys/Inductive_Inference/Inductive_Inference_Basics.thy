chapter \<open>Inductive inference of recursive functions\label{c:iirf}\<close>

theory Inductive_Inference_Basics
  imports Standard_Results
begin

text \<open>Inductive inference originates from work by
Solomonoff~\cite{s-ftiip1-64,s-ftiip2-64} and Gold~\cite{g-lil-67,g-lr-65}
and comes in many variations. The common theme is to infer additional
information about objects, such as formal languages or functions, from incomplete
data, such as finitely many words contained in the language or argument-value
pairs of the function. Oftentimes ``additional information'' means complete
information, such that the task becomes identification of the object.

The basic setting in inductive inference of recursive functions is as follows.
Let us denote, for a total function $f$, by $f^n$ the code of the list
$[f(0), ..., f(n)]$. Let $U$ be a set (called \emph{class}) of total
recursive functions, and $\psi$ a binary partial recursive function
(called \emph{hypothesis space}).
A partial recursive function $S$ (called \emph{strategy})
is said to \emph{learn $U$ in the limit with respect to $\psi$} if
for all $f \in U$,
\begin{itemize}
  \item the value $S(f^n)$ is defined for all $n\in\mathbb{N}$,
  \item the sequence $S(f^0), S(f^1), \ldots$ converges to an
    $i\in\mathbb{N}$ with $\psi_i = f$.
\end{itemize}

Both the output $S(f^n)$ of the strategy and its interpretation
as a function $\psi_{S(f^n)}$ are called \emph{hypothesis}. The set
of all classes learnable in the limit by $S$ with respect to $\psi$ is
denoted by $\mathrm{LIM}_\psi(S)$. Moreover we set $\mathrm{LIM}_\psi =
\bigcup_{S\in\mathcal{P}} \mathrm{LIM}_\psi(S)$ and $\mathrm{LIM} =
\bigcup_{\psi\in\mathcal{P}^2} \mathrm{LIM}_\psi$. We call the latter set the
\emph{inference type} $\mathrm{LIM}$.

Many aspects of this setting can be varied. We shall consider:
\begin{itemize}
  \item Intermediate hypotheses: $\psi_{S(f^n)}$ can be required to be total or
    to be in the class $U$, or to coincide with $f$ on arguments up to $n$, or
    a myriad of other conditions or combinations thereof.
  \item Convergence of hypotheses:
  \begin{itemize}
    \item The strategy can be required to output not a sequence but a single
      hypothesis, which must be correct.
    \item The strategy can be required to converge to a \emph{function} rather
      than an index.
  \end{itemize}
\end{itemize}

We formalize five kinds of results (\<open>\<I>\<close> and \<open>\<I>'\<close> stand for
inference types):
\begin{itemize}
  \item Comparison of learning power: results of the form @{prop "\<I>
    \<subset> \<I>'"}, in particular showing that the inclusion is proper
    (Sections~\ref{s:fin_cp}, \ref{s:num_fin}, \ref{s:num_cp},
    \ref{s:num_total}, \ref{s:cons_lim}, \ref{s:lim_bc}, \ref{s:total_cons},
    \ref{s:r1_bc}).
  \item Whether \<open>\<I>\<close> is closed under the subset relation: @{prop "U
    \<in> \<I> \<and> V \<subseteq> U \<Longrightarrow> V \<in> \<I>"}.
  \item Whether \<open>\<I>\<close> is closed under union: @{prop "U \<in> \<I> \<and>
    V \<in> \<I> \<Longrightarrow> U \<union> V \<in> \<I>"} (Section~\ref{s:union}).
  \item Whether every class in \<open>\<I>\<close> can be learned with respect to a
    Gödel numbering as hypothesis space (Section~\ref{s:inference_types}).
  \item Whether every class in \<open>\<I>\<close> can be learned by a \emph{total}
    recursive strategy (Section~\ref{s:lemma_r}).
\end{itemize}

The bulk of this chapter is devoted to the first category of results. Most
results that we are going to formalize have been called ``classical'' by
Jantke and Beick~\cite{jb-cpnii-81}, who compare a large number of inference
types. Another comparison is by Case and Smith~\cite{cs-cicmii-83}. Angluin
and Smith~\cite{as-ii-87} give an overview of various forms of inductive
inference.

All (interesting) proofs herein are based on my lecture notes of the
\emph{Induktive Inferenz} lectures by Rolf Wiehagen from 1999/2000 and
2000/2001 at the University of Kaiserslautern. I have given references to the
original proofs whenever I was able to find them. For the other proofs, as
well as for those that I had to contort beyond recognition, I provide proof
sketches.\<close>


section \<open>Preliminaries\<close>

text \<open>Throughout the chapter, in particular in proof sketches, we use
the following notation.

Let $b\in\mathbb{N}^*$ be a list of numbers. We write $|b|$ for its length
and $b_i$ for the $i$-th element ($i=0,\dots, |b| - 1$). Concatenation of
numbers and lists works in the obvious way; for instance, $jbk$ with
$j,k\in\mathbb{N}$, $b\in\mathbb{N}^*$ refers to the list $jb_0\dots
b_{|b|-1}k$. For $0 \leq i < |b|$, the term $b_{i:=v}$ denotes the list
$b_0\dots b_{i-1}vb_{i+1}\dots b_{|b|-1}$. The notation $b_{<i}$ refers to
$b_0\dots b_{i-1}$ for $0 < i \leq |b|$. Moreover, $v^n$ is short for the
list consisting of $n$ times the value $v \in \mathbb{N}$.

Unary partial functions can be regarded as infinite sequences consisting of
numbers and the symbol~$\uparrow$ denoting undefinedness. We abbreviate the
empty function by $\uparrow^\infty$ and the constant zero function by
$0^\infty$. A function can be written as a list concatenated with a partial
function. For example, $jb\uparrow^\infty$ is the function
\[
x \mapsto \left\{\begin{array}{ll}
  j        & \mbox{if } x = 0,\\
  b_{x-1}  & \mbox{if } 0 < x \leq |b|,\\
  \uparrow & \mbox{otherwise,}
\end{array}\right.
\]
and $jp$, where $p$ is a function, means
\[
x \mapsto \left\{\begin{array}{ll}
  j      & \mbox{if } x = 0,\\
  p(x-1) & \mbox{otherwise.}
\end{array}\right.
\]

A \emph{numbering} is a function $\psi \in \mathcal{P}^2$.\<close>


subsection \<open>The prefixes of a function\<close>

text \<open>A \emph{prefix}, also called \emph{initial segment}, is a list of
initial values of a function.\<close>

definition prefix :: "partial1 \<Rightarrow> nat \<Rightarrow> nat list" where
  "prefix f n \<equiv> map (\<lambda>x. the (f x)) [0..<Suc n]"

lemma length_prefix [simp]: "length (prefix f n) = Suc n"
  unfolding prefix_def by simp

lemma prefix_nth [simp]:
  assumes "k < Suc n"
  shows "prefix f n ! k = the (f k)"
  unfolding prefix_def using assms nth_map_upt[of k "Suc n" 0 "\<lambda>x. the (f x)"] by simp

lemma prefixI:
  assumes "length vs > 0" and "\<And>x. x < length vs \<Longrightarrow> f x \<down>= vs ! x"
  shows "prefix f (length vs - 1) = vs"
  using assms nth_equalityI[of "prefix f (length vs - 1)" vs] by simp

lemma prefixI':
  assumes "length vs = Suc n" and "\<And>x. x < Suc n \<Longrightarrow> f x \<down>= vs ! x"
  shows "prefix f n = vs"
  using assms nth_equalityI[of "prefix f (length vs - 1)" vs] by simp

lemma prefixE:
  assumes "prefix f (length vs - 1) = vs"
    and "f \<in> \<R>"
    and "length vs > 0"
    and "x < length vs"
  shows "f x \<down>= vs ! x"
  using assms length_prefix prefix_nth[of x "length vs - 1" f] by simp

lemma prefix_eqI:
  assumes "\<And>x. x \<le> n \<Longrightarrow> f x = g x"
  shows "prefix f n = prefix g n"
  using assms prefix_def by simp

lemma prefix_0: "prefix f 0 = [the (f 0)]"
  using prefix_def by simp

lemma prefix_Suc: "prefix f (Suc n) = prefix f n @ [the (f (Suc n))]"
  unfolding prefix_def by simp

lemma take_prefix:
  assumes "f \<in> \<R>" and "k \<le> n"
  shows "prefix f k = take (Suc k) (prefix f n)"
proof -
  let ?vs = "take (Suc k) (prefix f n)"
  have "length ?vs = Suc k"
    using assms(2) by simp
  then have "\<And>x. x < length ?vs \<Longrightarrow> f x \<down>= ?vs ! x"
    using assms by auto
  then show ?thesis
    using prefixI[where ?vs="?vs"] \<open>length ?vs = Suc k\<close> by simp
qed

text \<open>Strategies receive prefixes in the form of encoded lists. The
term ``prefix'' refers to both encoded and unencoded lists. We use the
notation @{text "f \<triangleright> n"} for the prefix $f^n$.\<close>

definition init :: "partial1 \<Rightarrow> nat \<Rightarrow> nat" (infix "\<triangleright>" 110) where
  "f \<triangleright> n \<equiv> list_encode (prefix f n)"

lemma init_neq_zero: "f \<triangleright> n \<noteq> 0"
  unfolding init_def prefix_def using list_encode_0 by fastforce

lemma init_prefixE [elim]: "prefix f n = prefix g n \<Longrightarrow> f \<triangleright> n = g \<triangleright> n"
  unfolding init_def by simp

lemma init_eqI:
  assumes "\<And>x. x \<le> n \<Longrightarrow> f x = g x"
  shows "f \<triangleright> n = g \<triangleright> n"
  unfolding init_def using prefix_eqI[OF assms] by simp

lemma initI:
  assumes "e_length e > 0" and "\<And>x. x < e_length e \<Longrightarrow> f x \<down>= e_nth e x"
  shows "f \<triangleright> (e_length e - 1) = e"
  unfolding init_def using assms prefixI by simp

lemma initI':
  assumes "e_length e = Suc n" and "\<And>x. x <  Suc n \<Longrightarrow> f x \<down>= e_nth e x"
  shows "f \<triangleright> n = e"
  unfolding init_def using assms prefixI' by simp

lemma init_iff_list_eq_upto:
  assumes "f \<in> \<R>" and "e_length vs > 0"
  shows "(\<forall>x<e_length vs. f x \<down>= e_nth vs x) \<longleftrightarrow> prefix f (e_length vs - 1) = list_decode vs"
  using prefixI[OF assms(2)] prefixE[OF _ assms] by auto

lemma length_init [simp]: "e_length (f \<triangleright> n) = Suc n"
  unfolding init_def by simp

lemma init_Suc_snoc: "f \<triangleright> (Suc n) = e_snoc (f \<triangleright> n) (the (f (Suc n)))"
  unfolding init_def by (simp add: prefix_Suc)

lemma nth_init: "i < Suc n \<Longrightarrow> e_nth (f \<triangleright> n) i = the (f i)"
  unfolding init_def using prefix_nth by auto

lemma hd_init [simp]: "e_hd (f \<triangleright> n) = the (f 0)"
  unfolding init_def using init_neq_zero by (simp add: e_hd_nth0)

lemma list_decode_init [simp]: "list_decode (f \<triangleright> n) = prefix f n"
  unfolding init_def by simp

lemma init_eq_iff_eq_upto:
  assumes "g \<in> \<R>" and "f \<in> \<R>"
  shows "(\<forall>j<Suc n. g j = f j) \<longleftrightarrow> g \<triangleright> n = f \<triangleright> n"
  using assms initI' init_iff_list_eq_upto length_init list_decode_init
  by (metis diff_Suc_1 zero_less_Suc)

definition is_init_of :: "nat \<Rightarrow> partial1 \<Rightarrow> bool" where
  "is_init_of t f \<equiv> \<forall>i<e_length t. f i \<down>= e_nth t i"

lemma not_initial_imp_not_eq:
  assumes "\<And>x. x < Suc n \<Longrightarrow> f x \<down>" and "\<not> (is_init_of (f \<triangleright> n) g)"
  shows "f \<noteq> g"
  using is_init_of_def assms by auto

lemma all_init_eq_imp_fun_eq:
  assumes "f \<in> \<R>" and "g \<in> \<R>" and "\<And>n. f \<triangleright> n = g \<triangleright> n"
  shows "f = g"
proof
  fix n
  from assms have "prefix f n = prefix g n"
    by (metis init_def list_decode_encode)
  then have "the (f n) = the (g n)"
    unfolding init_def prefix_def by simp
  then show "f n = g n"
    using assms(1,2) by (meson R1_imp_total1 option.expand total1E)
qed

corollary neq_fun_neq_init:
  assumes "f \<in> \<R>" and "g \<in> \<R>" and "f \<noteq> g"
  shows "\<exists>n. f \<triangleright> n \<noteq> g \<triangleright> n"
  using assms all_init_eq_imp_fun_eq by auto

lemma eq_init_forall_le:
  assumes "f \<triangleright> n = g \<triangleright> n" and "m \<le> n"
  shows "f \<triangleright> m = g \<triangleright> m"
proof -
  from assms(1) have "prefix f n = prefix g n"
    by (metis init_def list_decode_encode)
  then have "the (f k) = the (g k)" if "k \<le> n" for k
    using prefix_def that by auto
  then have "the (f k) = the (g k)" if "k \<le> m" for k
    using assms(2) that by simp
  then have "prefix f m = prefix g m"
    using prefix_def by simp
  then show ?thesis by (simp add: init_def)
qed

corollary neq_init_forall_ge:
  assumes "f \<triangleright> n \<noteq> g \<triangleright> n" and "m \<ge> n"
  shows "f \<triangleright> m \<noteq> g \<triangleright> m"
  using eq_init_forall_le assms by blast

lemma e_take_init:
  assumes "f \<in> \<R>" and "k < Suc n"
  shows "e_take (Suc k) (f \<triangleright> n) = f \<triangleright> k"
  using assms take_prefix by (simp add: init_def less_Suc_eq_le)

lemma init_butlast_init:
  assumes "total1 f" and "f \<triangleright> n = e" and "n > 0"
  shows "f \<triangleright> (n - 1) = e_butlast e"
proof -
  let ?e = "e_butlast e"
  have "e_length e = Suc n"
    using assms(2) by auto
  then have len: "e_length ?e = n"
    by simp
  have "f \<triangleright> (e_length ?e - 1) = ?e"
  proof (rule initI)
    show "0 < e_length ?e"
      using assms(3) len by simp
    have "\<And>x. x < e_length e \<Longrightarrow> f x \<down>= e_nth e x"
      using assms(1,2) total1_def \<open>e_length e = Suc n\<close> by auto
    then show "\<And>x. x < e_length ?e \<Longrightarrow> f x \<down>= e_nth ?e x"
      by (simp add: butlast_conv_take)
  qed
  with len show ?thesis by simp
qed

text \<open>Some definitions make use of recursive predicates, that is,
$01$-valued functions.\<close>

definition RPred1 :: "partial1 set" ("\<R>\<^sub>0\<^sub>1") where
  "\<R>\<^sub>0\<^sub>1 \<equiv> {f. f \<in> \<R> \<and> (\<forall>x. f x \<down>= 0 \<or> f x \<down>= 1)}"

lemma RPred1_subseteq_R1: "\<R>\<^sub>0\<^sub>1 \<subseteq> \<R>"
  unfolding RPred1_def by auto

lemma const0_in_RPred1: "(\<lambda>_. Some 0) \<in> \<R>\<^sub>0\<^sub>1"
  using RPred1_def const_in_Prim1 by fast

lemma RPred1_altdef: "\<R>\<^sub>0\<^sub>1 = {f. f \<in> \<R> \<and> (\<forall>x. the (f x) \<le> 1)}"
  (is "\<R>\<^sub>0\<^sub>1 = ?S")
proof
  show "\<R>\<^sub>0\<^sub>1 \<subseteq> ?S"
  proof
    fix f
    assume f: "f \<in> \<R>\<^sub>0\<^sub>1"
    with RPred1_def have "f \<in> \<R>" by auto
    from f have "\<forall>x. f x \<down>= 0 \<or> f x \<down>= 1"
      by (simp add: RPred1_def)
    then have "\<forall>x. the (f x) \<le> 1"
      by (metis eq_refl less_Suc_eq_le zero_less_Suc option.sel)
    with \<open>f \<in> \<R>\<close> show "f \<in> ?S" by simp
  qed
  show "?S \<subseteq> \<R>\<^sub>0\<^sub>1"
  proof
    fix f
    assume f: "f \<in> ?S"
    then have "f \<in> \<R>" by simp
    then have total: "\<And>x. f x \<down>" by auto
    from f have "\<forall>x. the (f x) = 0 \<or> the (f x) = 1"
      by (simp add: le_eq_less_or_eq)
    with total have "\<forall>x. f x \<down>= 0 \<or> f x \<down>= 1"
      by (metis option.collapse)
    then show "f \<in> \<R>\<^sub>0\<^sub>1"
      using \<open>f \<in> \<R>\<close> RPred1_def by auto
  qed
qed

subsection \<open>NUM\<close>

text \<open>A class of recursive functions is in NUM if it can be
embedded in a total numbering. Thus, for learning such classes there is
always a total hypothesis space available.\<close>

definition NUM :: "partial1 set set" where
  "NUM \<equiv> {U. \<exists>\<psi>\<in>\<R>\<^sup>2. \<forall>f\<in>U. \<exists>i. \<psi> i = f}"

definition NUM_wrt :: "partial2 \<Rightarrow> partial1 set set" where
  "\<psi> \<in> \<R>\<^sup>2 \<Longrightarrow> NUM_wrt \<psi> \<equiv> {U. \<forall>f\<in>U. \<exists>i. \<psi> i = f}"

lemma NUM_I [intro]:
  assumes "\<psi> \<in> \<R>\<^sup>2" and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i. \<psi> i = f"
  shows "U \<in> NUM"
  using assms NUM_def by blast

lemma NUM_E [dest]:
  assumes "U \<in> NUM"
  shows "U \<subseteq> \<R>"
    and "\<exists>\<psi>\<in>\<R>\<^sup>2. \<forall>f\<in>U. \<exists>i. \<psi> i = f"
  using NUM_def assms by (force, auto)

lemma NUM_closed_subseteq:
  assumes "U \<in> NUM" and "V \<subseteq> U"
  shows "V \<in> NUM"
  using assms subset_eq[of V U] NUM_I by auto

text \<open>This is the classical diagonalization proof showing that there is
no total numbering containing all total recursive functions.\<close>

lemma R1_not_in_NUM: "\<R> \<notin> NUM"
proof
  assume "\<R> \<in> NUM"
  then obtain \<psi> where num: "\<psi> \<in> \<R>\<^sup>2" "\<forall>f\<in>\<R>. \<exists>i. \<psi> i = f"
    by auto
  then obtain psi where psi: "recfn 2 psi" "total psi" "eval psi [i, x] = \<psi> i x" for i x
    by auto
  define d where "d = Cn 1 S [Cn 1 psi [Id 1 0, Id 1 0]]"
  then have "recfn 1 d"
    using psi(1) by simp
  moreover have d: "eval d [x] \<down>= Suc (the (\<psi> x x))" for x
    unfolding d_def using num psi by simp
  ultimately have "(\<lambda>x. eval d [x]) \<in> \<R>"
    using R1I by blast
  then obtain i where "\<psi> i = (\<lambda>x. eval d [x])"
    using num(2) by auto
  then have "\<psi> i i = eval d [i]" by simp
  with d have "\<psi> i i \<down>= Suc (the (\<psi> i i))" by simp
  then show False
    using option.sel[of "Suc (the (\<psi> i i))"] by simp
qed

text \<open>A hypothesis space that contains a function for every prefix will
come in handy. The following is a total numbering with this property.\<close>

definition "r_prenum \<equiv>
  Cn 2 r_ifless [Id 2 1, Cn 2 r_length [Id 2 0], Cn 2 r_nth [Id 2 0, Id 2 1], r_constn 1 0]"

lemma r_prenum_prim [simp]: "prim_recfn 2 r_prenum"
  unfolding r_prenum_def by simp_all

lemma r_prenum [simp]:
  "eval r_prenum [e, x] \<down>= (if x < e_length e then e_nth e x else 0)"
  by (simp add: r_prenum_def)

definition prenum :: partial2 where
  "prenum e x \<equiv> Some (if x < e_length e then e_nth e x else 0)"

lemma prenum_in_R2: "prenum \<in> \<R>\<^sup>2"
  using prenum_def Prim2I[OF r_prenum_prim, of prenum] by simp

lemma prenum [simp]: "prenum e x \<down>= (if x < e_length e then e_nth e x else 0)"
  unfolding prenum_def ..

lemma prenum_encode:
  "prenum (list_encode vs) x \<down>= (if x < length vs then vs ! x else 0)"
  using prenum_def by (cases "x < length vs") simp_all

text \<open>Prepending a list of numbers to a function:\<close>

definition prepend :: "nat list \<Rightarrow> partial1 \<Rightarrow> partial1" (infixr "\<odot>" 64) where
  "vs \<odot> f \<equiv> \<lambda>x. if x < length vs then Some (vs ! x) else f (x - length vs)"

lemma prepend [simp]:
  "(vs \<odot> f) x = (if x < length vs then Some (vs ! x) else f (x - length vs))"
  unfolding prepend_def ..

lemma prepend_total: "total1 f \<Longrightarrow> total1 (vs \<odot> f)"
  unfolding total1_def by simp

lemma prepend_at_less:
  assumes "n < length vs"
  shows "(vs \<odot> f) n \<down>= vs ! n"
  using assms by simp

lemma prepend_at_ge:
  assumes "n \<ge> length vs"
  shows "(vs \<odot> f) n = f (n - length vs)"
  using assms by simp

lemma prefix_prepend_less:
  assumes "n < length vs"
  shows "prefix (vs \<odot> f) n = take (Suc n) vs"
  using assms length_prefix by (intro nth_equalityI) simp_all

lemma prepend_eqI:
  assumes "\<And>x. x < length vs \<Longrightarrow> g x \<down>= vs ! x"
    and "\<And>x. g (length vs + x) = f x"
  shows "g = vs \<odot> f"
proof
  fix x
  show "g x = (vs \<odot> f) x"
  proof (cases "x < length vs")
    case True
    then show ?thesis using assms by simp
  next
    case False
    then show ?thesis
      using assms prepend by (metis add_diff_inverse_nat)
  qed
qed

fun r_prepend :: "nat list \<Rightarrow> recf \<Rightarrow> recf" where
  "r_prepend [] r = r"
| "r_prepend (v # vs) r =
     Cn 1 (r_lifz (r_const v) (Cn 1 (r_prepend vs r) [r_dec])) [Id 1 0, Id 1 0]"

lemma r_prepend_recfn:
  assumes "recfn 1 r"
  shows "recfn 1 (r_prepend vs r)"
  using assms by (induction vs) simp_all

lemma r_prepend:
  assumes "recfn 1 r"
  shows "eval (r_prepend vs r) [x] =
    (if x < length vs then Some (vs ! x) else eval r [x - length vs])"
proof (induction vs arbitrary: x)
  case Nil
  then show ?case using assms by simp
next
  case (Cons v vs)
  show ?case
    using assms Cons by (cases "x = 0") (auto simp add: r_prepend_recfn)
qed

lemma r_prepend_total:
  assumes "recfn 1 r" and "total r"
  shows "eval (r_prepend vs r) [x] \<down>=
    (if x < length vs then vs ! x else the (eval r [x - length vs]))"
proof (induction vs arbitrary: x)
  case Nil
  then show ?case using assms by simp
next
  case (Cons v vs)
  show ?case
    using assms Cons by (cases "x = 0") (auto simp add: r_prepend_recfn)
qed

lemma prepend_in_P1:
  assumes "f \<in> \<P>"
  shows "vs \<odot> f \<in> \<P>"
proof -
  obtain r where r: "recfn 1 r"  "\<And>x. eval r [x] = f x"
    using assms by auto
  moreover have "recfn 1 (r_prepend vs r)"
    using r r_prepend_recfn by simp
  moreover have "eval (r_prepend vs r) [x] = (vs \<odot> f) x" for x
    using r r_prepend by simp
  ultimately show ?thesis by blast
qed

lemma prepend_in_R1:
  assumes "f \<in> \<R>"
  shows "vs \<odot> f \<in> \<R>"
proof -
  obtain r where r: "recfn 1 r" "total r" "\<And>x. eval r [x] = f x"
    using assms by auto
  then have "total1 f"
    using R1_imp_total1[OF assms] by simp
  have "total (r_prepend vs r)"
    using r r_prepend_total r_prepend_recfn totalI1[of "r_prepend vs r"] by simp
  with r have "total (r_prepend vs r)" by simp
  moreover have "recfn 1 (r_prepend vs r)"
    using r r_prepend_recfn by simp
  moreover have "eval (r_prepend vs r) [x] = (vs \<odot> f) x" for x
    using r r_prepend \<open>total1 f\<close> total1E by simp
  ultimately show ?thesis by auto
qed

lemma prepend_associative: "(us @ vs) \<odot> f = us \<odot> vs \<odot> f" (is "?lhs = ?rhs")
proof
  fix x
  consider
      "x < length us"
    | "x \<ge> length us \<and> x < length (us @ vs)"
    | "x \<ge> length (us @ vs)"
    by linarith
  then show "?lhs x = ?rhs x"
  proof (cases)
    case 1
    then show ?thesis
      by (metis le_add1 length_append less_le_trans nth_append prepend_at_less)
  next
    case 2
    then show ?thesis
      by (smt add_diff_inverse_nat add_less_cancel_left length_append nth_append prepend)
  next
    case 3
    then show ?thesis
      using prepend_at_ge by auto
  qed
qed

abbreviation constant_divergent :: partial1 ("\<up>\<^sup>\<infinity>") where
  "\<up>\<^sup>\<infinity> \<equiv> \<lambda>_. None"

abbreviation constant_zero :: partial1 ("0\<^sup>\<infinity>") where
  "0\<^sup>\<infinity> \<equiv> \<lambda>_. Some 0"

lemma almost0_in_R1: "vs \<odot> 0\<^sup>\<infinity> \<in> \<R>"
  using RPred1_subseteq_R1 const0_in_RPred1 prepend_in_R1 by auto

text \<open>The class $U_0$ of all total recursive functions that are almost
everywhere zero will be used several times to construct
(counter-)examples.\<close>

definition U0 :: "partial1 set" ("U\<^sub>0") where
  "U\<^sub>0 \<equiv> {vs \<odot> 0\<^sup>\<infinity> |vs. vs \<in> UNIV}"

text \<open>The class @{term U0} contains exactly the functions in the
numbering @{term prenum}.\<close>

lemma U0_altdef: "U\<^sub>0 = {prenum e| e. e \<in> UNIV}" (is "U\<^sub>0 = ?W")
proof
  show "U\<^sub>0 \<subseteq> ?W"
  proof
    fix f
    assume "f \<in> U\<^sub>0"
    with U0_def obtain vs where "f = vs \<odot> 0\<^sup>\<infinity>"
      by auto
    then have "f = prenum (list_encode vs)"
      using prenum_encode by auto
    then show "f \<in> ?W" by auto
  qed
  show "?W \<subseteq> U\<^sub>0"
    unfolding U0_def by fastforce
qed

lemma U0_in_NUM: "U\<^sub>0 \<in> NUM"
  using prenum_in_R2 U0_altdef by (intro NUM_I[of prenum]; force)

text \<open>Every almost-zero function can be represented by $v0^\infty$ for
a list $v$ not ending in zero.\<close>

lemma almost0_canonical:
  assumes "f = vs \<odot> 0\<^sup>\<infinity>" and "f \<noteq> 0\<^sup>\<infinity>"
  obtains ws where "length ws > 0" and "last ws \<noteq> 0" and "f = ws \<odot> 0\<^sup>\<infinity>"
proof -
  let ?P = "\<lambda>k. k < length vs \<and> vs ! k \<noteq> 0"
  from assms have "vs \<noteq> []"
    by auto
  then have ex: "\<exists>k<length vs. vs ! k \<noteq> 0"
    using assms by auto
  define m where "m = Greatest ?P"
  moreover have le: "\<forall>y. ?P y \<longrightarrow> y \<le> length vs"
    by simp
  ultimately have "?P m"
    using ex GreatestI_ex_nat[of ?P "length vs"] by simp
  have not_gr: "\<not> ?P k" if "k > m" for k
    using Greatest_le_nat[of ?P _ "length vs"] m_def ex le not_less that by blast
  let ?ws = "take (Suc m) vs"
  have "vs \<odot> 0\<^sup>\<infinity> = ?ws \<odot> 0\<^sup>\<infinity>"
  proof
    fix x
    show "(vs \<odot> 0\<^sup>\<infinity>) x = (?ws \<odot> 0\<^sup>\<infinity>) x"
    proof (cases "x < Suc m")
      case True
      then show ?thesis using \<open>?P m\<close> by simp
    next
      case False
      moreover from this have "(?ws \<odot> 0\<^sup>\<infinity>) x \<down>= 0"
        by simp
      ultimately show ?thesis
        using not_gr by (cases "x < length vs") simp_all
    qed
  qed
  then have "f = ?ws \<odot> 0\<^sup>\<infinity>"
    using assms(1) by simp
  moreover have "length ?ws > 0"
    by (simp add: \<open>vs \<noteq> []\<close>)
  moreover have "last ?ws \<noteq> 0"
    by (simp add: \<open>?P m\<close> take_Suc_conv_app_nth)
  ultimately show ?thesis using that by blast
qed


section \<open>Types of inference\label{s:inference_types}\<close>

text \<open>This section introduces all inference types that we are going to
consider together with some of their simple properties. All these inference
types share the following condition, which essentially says that everything
must be computable:\<close>

abbreviation environment :: "partial2 \<Rightarrow> (partial1 set) \<Rightarrow> partial1 \<Rightarrow> bool" where
  "environment \<psi> U s \<equiv> \<psi> \<in> \<P>\<^sup>2 \<and> U \<subseteq> \<R> \<and> s \<in> \<P> \<and> (\<forall>f\<in>U. \<forall>n. s (f \<triangleright> n) \<down>)"


subsection \<open>LIM: Learning in the limit\<close>

text \<open>A strategy $S$ learns a class $U$ in the limit with respect to a
hypothesis space @{term "\<psi> \<in> \<P>\<^sup>2"} if for all $f\in U$, the
sequence $(S(f^n))_{n\in\mathbb{N}}$ converges to an $i$ with $\psi_i = f$.
Convergence for a sequence of natural numbers means that almost all elements
are the same. We express this with the following notation.\<close>

abbreviation Almost_All :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<^sup>\<infinity>" 10) where
  "\<forall>\<^sup>\<infinity>n. P n \<equiv> \<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. P n"

definition learn_lim :: "partial2 \<Rightarrow> (partial1 set) \<Rightarrow> partial1 \<Rightarrow> bool" where
  "learn_lim \<psi> U s \<equiv>
     environment \<psi> U s \<and>
     (\<forall>f\<in>U. \<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i))"

lemma learn_limE:
  assumes "learn_lim \<psi> U s"
  shows "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i)"
  using assms learn_lim_def by auto

lemma learn_limI:
  assumes "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i)"
  shows "learn_lim \<psi> U s"
  using assms learn_lim_def by auto

definition LIM_wrt :: "partial2 \<Rightarrow> partial1 set set" where
  "LIM_wrt \<psi> \<equiv> {U. \<exists>s. learn_lim \<psi> U s}"

definition Lim :: "partial1 set set" ("LIM") where
  "LIM \<equiv> {U. \<exists>\<psi> s. learn_lim \<psi> U s}"

text \<open>LIM is closed under the the subset relation.\<close>

lemma learn_lim_closed_subseteq:
  assumes "learn_lim \<psi> U s" and "V \<subseteq> U"
  shows "learn_lim \<psi> V s"
  using assms learn_lim_def by auto

corollary LIM_closed_subseteq:
  assumes "U \<in> LIM" and "V \<subseteq> U"
  shows "V \<in> LIM"
  using assms learn_lim_closed_subseteq by (smt Lim_def mem_Collect_eq)

text \<open>Changing the hypothesis infinitely often precludes learning in
the limit.\<close>

lemma infinite_hyp_changes_not_Lim:
  assumes "f \<in> U" and "\<forall>n. \<exists>m\<^sub>1>n. \<exists>m\<^sub>2>n. s (f \<triangleright> m\<^sub>1) \<noteq> s (f \<triangleright> m\<^sub>2)"
  shows "\<not> learn_lim \<psi> U s"
  using assms learn_lim_def by (metis less_imp_le)

lemma always_hyp_change_not_Lim:
  assumes "\<And>x. s (f \<triangleright> (Suc x)) \<noteq> s (f \<triangleright> x)"
  shows "\<not> learn_lim \<psi> {f} s"
  using assms learn_limE by (metis le_SucI order_refl singletonI)

text \<open>Guessing a wrong hypothesis infinitely often precludes learning
in the limit.\<close>

lemma infinite_hyp_wrong_not_Lim:
  assumes "f \<in> U" and "\<forall>n. \<exists>m>n. \<psi> (the (s (f \<triangleright> m))) \<noteq> f"
  shows "\<not> learn_lim \<psi> U s"
  using assms learn_limE by (metis less_imp_le option.sel)

text \<open>Converging to the same hypothesis on two functions precludes
learning in the limit.\<close>

lemma same_hyp_for_two_not_Lim:
  assumes "f\<^sub>1 \<in> U"
    and "f\<^sub>2 \<in> U"
    and "f\<^sub>1 \<noteq> f\<^sub>2"
    and "\<forall>n\<ge>n\<^sub>1. s (f\<^sub>1 \<triangleright> n) = h"
    and "\<forall>n\<ge>n\<^sub>2. s (f\<^sub>2 \<triangleright> n) = h"
  shows "\<not> learn_lim \<psi> U s"
  using assms learn_limE by (metis le_cases option.sel)

text \<open>Every class that can be learned in the limit can be learned in
the limit with respect to any Gödel numbering. We prove a generalization in
which hypotheses may have to satisfy an extra condition, so we can re-use it
for other inference types later.\<close>

lemma learn_lim_extra_wrt_goedel:
  fixes extra :: "(partial1 set) \<Rightarrow> partial1 \<Rightarrow> nat \<Rightarrow> partial1 \<Rightarrow> bool"
  assumes "goedel_numbering \<chi>"
    and "learn_lim \<psi> U s"
    and "\<And>f n. f \<in> U \<Longrightarrow> extra U f n (\<psi> (the (s (f \<triangleright> n))))"
  shows "\<exists>t. learn_lim \<chi> U t \<and> (\<forall>f\<in>U. \<forall>n. extra U f n (\<chi> (the (t (f \<triangleright> n)))))"
proof -
  have env: "environment \<psi> U s"
    and lim: "learn_lim \<psi> U s"
    and extra: "\<forall>f\<in>U. \<forall>n. extra U f n (\<psi> (the (s (f \<triangleright> n))))"
    using assms learn_limE by auto
  obtain c where c: "c \<in> \<R>" "\<forall>i. \<psi> i = \<chi> (the (c i))"
    using env goedel_numberingE[OF assms(1), of \<psi>] by auto
  define t where "t \<equiv>
    (\<lambda>x. if s x \<down> \<and> c (the (s x)) \<down> then Some (the (c (the (s x)))) else None)"
  have "t \<in> \<P>"
    unfolding t_def using env c concat_P1_P1[of c s] by auto
  have "t x = (if s x \<down> then Some (the (c (the (s x)))) else None)" for x
    using t_def c(1) R1_imp_total1 by auto
  then have t: "t (f \<triangleright> n) \<down>= the (c (the (s (f \<triangleright> n))))" if "f \<in> U" for f n
    using lim learn_limE that by simp
  have "learn_lim \<chi> U t"
  proof (rule learn_limI)
    show "environment \<chi> U t"
      using t by (simp add: \<open>t \<in> \<P>\<close> env goedel_numbering_P2[OF assms(1)])
    show "\<exists>i. \<chi> i = f \<and> (\<forall>\<^sup>\<infinity>n. t (f \<triangleright> n) \<down>= i)" if "f \<in> U" for f
    proof -
      from lim learn_limE(2) obtain i n\<^sub>0 where
        i: "\<psi> i = f \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= i)"
        using \<open>f \<in> U\<close> by blast
      let ?j = "the (c i)"
      have "\<chi> ?j = f"
        using c(2) i by simp
      moreover have "t (f \<triangleright> n) \<down>= ?j" if "n \<ge> n\<^sub>0" for n
        by (simp add: \<open>f \<in> U\<close> i t that)
      ultimately show ?thesis by auto
    qed
  qed
  moreover have "extra U f n (\<chi> (the (t (f \<triangleright> n))))" if "f \<in> U" for f n
  proof -
    from t have "the (t (f \<triangleright> n)) = the (c (the (s (f \<triangleright> n))))"
      by (simp add: that)
    then have "\<chi> (the (t (f \<triangleright> n))) = \<psi> (the (s (f \<triangleright> n)))"
      using c(2) by simp
    with extra show ?thesis using that by simp
  qed
  ultimately show ?thesis by auto
qed

lemma learn_lim_wrt_goedel:
  assumes "goedel_numbering \<chi>" and "learn_lim \<psi> U s"
  shows "\<exists>t. learn_lim \<chi> U t"
  using assms learn_lim_extra_wrt_goedel[where ?extra="\<lambda>U f n h. True"]
  by simp

lemma LIM_wrt_phi_eq_Lim: "LIM_wrt \<phi> = LIM"
  using LIM_wrt_def Lim_def learn_lim_wrt_goedel[OF goedel_numbering_phi]
  by blast


subsection \<open>BC: Behaviorally correct learning in the limit\<close>

text \<open>Behaviorally correct learning in the limit relaxes LIM by
requiring that the strategy almost always output an index for the target
function, but not necessarily the same index. In other words convergence of
$(S(f^n))_{n\in\mathbb{N}}$ is replaced by convergence of
$(\psi_{S(f^n)})_{n\in\mathbb{N}}$.\<close>

definition learn_bc :: "partial2 \<Rightarrow> (partial1 set) \<Rightarrow> partial1 \<Rightarrow> bool" where
  "learn_bc \<psi> U s \<equiv> 
     environment \<psi> U s \<and>
     (\<forall>f\<in>U. \<forall>\<^sup>\<infinity>n. \<psi> (the (s (f \<triangleright> n))) = f)"

lemma learn_bcE:
  assumes "learn_bc \<psi> U s"
  shows "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<forall>\<^sup>\<infinity>n. \<psi> (the (s (f \<triangleright> n))) = f"
  using assms learn_bc_def by auto

lemma learn_bcI:
  assumes "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<forall>\<^sup>\<infinity>n. \<psi> (the (s (f \<triangleright> n))) = f"
  shows "learn_bc \<psi> U s"
  using assms learn_bc_def by auto

definition BC_wrt :: "partial2 \<Rightarrow> partial1 set set" where
  "BC_wrt \<psi> \<equiv> {U. \<exists>s. learn_bc \<psi> U s}"

definition BC :: "partial1 set set" where
  "BC \<equiv> {U. \<exists>\<psi> s. learn_bc \<psi> U s}"

text \<open>BC is a superset of LIM and closed under the subset relation.\<close>

lemma learn_lim_imp_BC: "learn_lim \<psi> U s \<Longrightarrow> learn_bc \<psi> U s"
  using learn_limE learn_bcI[of \<psi> U s] by fastforce

lemma Lim_subseteq_BC: "LIM \<subseteq> BC"
  using learn_lim_imp_BC Lim_def BC_def by blast

lemma learn_bc_closed_subseteq:
  assumes "learn_bc \<psi> U s" and "V \<subseteq> U"
  shows "learn_bc \<psi> V s"
  using assms learn_bc_def by auto

corollary BC_closed_subseteq:
  assumes "U \<in> BC" and "V \<subseteq> U"
  shows "V \<in> BC"
  using assms by (smt BC_def learn_bc_closed_subseteq mem_Collect_eq)

text \<open>Just like with LIM, guessing a wrong hypothesis infinitely often
precludes BC-style learning.\<close>

lemma infinite_hyp_wrong_not_BC:
  assumes "f \<in> U" and "\<forall>n. \<exists>m>n. \<psi> (the (s (f \<triangleright> m))) \<noteq> f"
  shows "\<not> learn_bc \<psi> U s"
proof
  assume "learn_bc \<psi> U s"
  then obtain n\<^sub>0 where "\<forall>n\<ge>n\<^sub>0. \<psi> (the (s (f \<triangleright> n))) = f"
    using learn_bcE assms(1) by metis
  with assms(2) show False using less_imp_le by blast
qed

text \<open>The proof that Gödel numberings suffice as hypothesis spaces for
BC is similar to the one for @{thm[source] learn_lim_extra_wrt_goedel}. We do
not need the @{term extra} part for BC, but we get it for free.\<close>

lemma learn_bc_extra_wrt_goedel:
  fixes extra :: "(partial1 set) \<Rightarrow> partial1 \<Rightarrow> nat \<Rightarrow> partial1 \<Rightarrow> bool"
  assumes "goedel_numbering \<chi>"
    and "learn_bc \<psi> U s"
    and "\<And>f n. f \<in> U \<Longrightarrow> extra U f n (\<psi> (the (s (f \<triangleright> n))))"
  shows "\<exists>t. learn_bc \<chi> U t \<and> (\<forall>f\<in>U. \<forall>n. extra U f n (\<chi> (the (t (f \<triangleright> n)))))"
proof -
  have env: "environment \<psi> U s"
    and lim: "learn_bc \<psi> U s"
    and extra: "\<forall>f\<in>U. \<forall>n. extra U f n (\<psi> (the (s (f \<triangleright> n))))"
    using assms learn_bc_def by auto
  obtain c where c: "c \<in> \<R>" "\<forall>i. \<psi> i = \<chi> (the (c i))"
    using env goedel_numberingE[OF assms(1), of \<psi>] by auto
  define t where
    "t = (\<lambda>x. if s x \<down> \<and> c (the (s x)) \<down> then Some (the (c (the (s x)))) else None)"
  have "t \<in> \<P>"
    unfolding t_def using env c concat_P1_P1[of c s] by auto
  have "t x = (if s x \<down> then Some (the (c (the (s x)))) else None)" for x
    using t_def c(1) R1_imp_total1 by auto
  then have t: "t (f \<triangleright> n) \<down>= the (c (the (s (f \<triangleright> n))))" if "f \<in> U" for f n
    using lim learn_bcE(1) that by simp
  have "learn_bc \<chi> U t"
  proof (rule learn_bcI)
    show "environment \<chi> U t"
      using t by (simp add: \<open>t \<in> \<P>\<close> env goedel_numbering_P2[OF assms(1)])
    show "\<forall>\<^sup>\<infinity>n. \<chi> (the (t (f \<triangleright> n))) = f" if "f \<in> U" for f
    proof -
      obtain n\<^sub>0 where "\<forall>n\<ge>n\<^sub>0. \<psi> (the (s (f \<triangleright> n))) = f"
        using lim learn_bcE(2) \<open>f \<in> U\<close> by blast
      then show ?thesis using that t c(2) by auto
    qed
  qed
  moreover have "extra U f n (\<chi> (the (t (f \<triangleright> n))))" if "f \<in> U" for f n
  proof -
    from t have "the (t (f \<triangleright> n)) = the (c (the (s (f \<triangleright> n))))"
      by (simp add: that)
    then have "\<chi> (the (t (f \<triangleright> n))) = \<psi> (the (s (f \<triangleright> n)))"
      using c(2) by simp
    with extra show ?thesis using that by simp
  qed
  ultimately show ?thesis by auto
qed

corollary learn_bc_wrt_goedel:
  assumes "goedel_numbering \<chi>" and "learn_bc \<psi> U s"
  shows "\<exists>t. learn_bc \<chi> U t"
  using assms learn_bc_extra_wrt_goedel[where ?extra="\<lambda>_ _ _ _. True"] by simp

corollary BC_wrt_phi_eq_BC: "BC_wrt \<phi> = BC"
  using learn_bc_wrt_goedel goedel_numbering_phi BC_def BC_wrt_def by blast


subsection \<open>CONS: Learning in the limit with consistent hypotheses\<close>

text \<open>A hypothesis is \emph{consistent} if it matches all values in the
prefix given to the strategy. Consistent learning in the limit requires the
strategy to output only consistent hypotheses for prefixes from the class.\<close>

definition learn_cons :: "partial2 \<Rightarrow> (partial1 set) \<Rightarrow> partial1 \<Rightarrow> bool" where
  "learn_cons \<psi> U s \<equiv>
     learn_lim \<psi> U s \<and>
     (\<forall>f\<in>U. \<forall>n. \<forall>k\<le>n. \<psi> (the (s (f \<triangleright> n))) k = f k)"

definition CONS_wrt :: "partial2 \<Rightarrow> partial1 set set" where
  "CONS_wrt \<psi> \<equiv> {U. \<exists>s. learn_cons \<psi> U s}"

definition CONS :: "partial1 set set" where
  "CONS \<equiv> {U. \<exists>\<psi> s. learn_cons \<psi> U s}"

lemma CONS_subseteq_Lim: "CONS \<subseteq> LIM"
  using CONS_def Lim_def learn_cons_def by blast

lemma learn_consI:
  assumes "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i)"
    and "\<And>f n. f \<in> U \<Longrightarrow> \<forall>k\<le>n. \<psi> (the (s (f \<triangleright> n))) k = f k"
  shows "learn_cons \<psi> U s"
  using assms learn_lim_def learn_cons_def by simp

text \<open>If a consistent strategy converges, it automatically converges to
a correct hypothesis. Thus we can remove @{term "\<psi> i = f"} from the second
assumption in the previous lemma.\<close>

lemma learn_consI2:
  assumes "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i. \<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i"
    and "\<And>f n. f \<in> U \<Longrightarrow> \<forall>k\<le>n. \<psi> (the (s (f \<triangleright> n))) k = f k"
  shows "learn_cons \<psi> U s"
proof (rule learn_consI)
  show "environment \<psi> U s"
    and cons: "\<And>f n. f \<in> U \<Longrightarrow> \<forall>k\<le>n. \<psi> (the (s (f \<triangleright> n))) k = f k"
    using assms by simp_all
  show "\<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i)" if "f \<in> U" for f
  proof -
    from that assms(2) obtain i n\<^sub>0 where i_n0: "\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= i"
      by blast
    have "\<psi> i x = f x" for x
    proof (cases "x \<le> n\<^sub>0")
      case True
      then show ?thesis
        using i_n0 cons that by fastforce
    next
      case False
      moreover have "\<forall>k\<le>x. \<psi> (the (s (f \<triangleright> x))) k = f k"
        using cons that by simp
      ultimately show ?thesis using i_n0 by simp
    qed
    with i_n0 show ?thesis by auto
  qed
qed

lemma learn_consE:
  assumes "learn_cons \<psi> U s"
  shows "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= i)"
    and "\<And>f n. f \<in> U \<Longrightarrow> \<forall>k\<le>n. \<psi> (the (s (f \<triangleright> n))) k = f k"
  using assms learn_cons_def learn_lim_def by auto

lemma learn_cons_wrt_goedel:
  assumes "goedel_numbering \<chi>" and "learn_cons \<psi> U s"
  shows "\<exists>t. learn_cons \<chi> U t"
  using learn_cons_def assms
    learn_lim_extra_wrt_goedel[where ?extra="\<lambda>U f n h. \<forall>k\<le>n. h k = f k"]
  by auto

lemma CONS_wrt_phi_eq_CONS: "CONS_wrt \<phi> = CONS"
  using CONS_wrt_def CONS_def learn_cons_wrt_goedel goedel_numbering_phi
  by blast

lemma learn_cons_closed_subseteq:
  assumes "learn_cons \<psi> U s" and "V \<subseteq> U"
  shows "learn_cons \<psi> V s"
  using assms learn_cons_def learn_lim_closed_subseteq by auto

lemma CONS_closed_subseteq:
  assumes "U \<in> CONS" and "V \<subseteq> U"
  shows "V \<in> CONS"
  using assms learn_cons_closed_subseteq by (smt CONS_def mem_Collect_eq)

text \<open>A consistent strategy cannot output the same hypothesis for two
different prefixes from the class to be learned.\<close>

lemma same_hyp_different_init_not_cons:
  assumes "f \<in> U"
    and "g \<in> U"
    and "f \<triangleright> n \<noteq> g \<triangleright> n"
    and "s (f \<triangleright> n) = s (g \<triangleright> n)"
  shows "\<not> learn_cons \<phi> U s"
  unfolding learn_cons_def by (auto, metis assms init_eqI)


subsection \<open>TOTAL: Learning in the limit with total hypotheses\<close>

text \<open>Total learning in the limit requires the strategy to hypothesize
only total functions for prefixes from the class.\<close>

definition learn_total :: "partial2 \<Rightarrow> (partial1 set) \<Rightarrow> partial1 \<Rightarrow> bool" where
  "learn_total \<psi> U s \<equiv>
     learn_lim \<psi> U s \<and>
     (\<forall>f\<in>U. \<forall>n. \<psi> (the (s (f \<triangleright> n))) \<in> \<R>)"

definition TOTAL_wrt :: "partial2 \<Rightarrow> partial1 set set" where
  "TOTAL_wrt \<psi> \<equiv> {U. \<exists>s. learn_total \<psi> U s}"

definition TOTAL :: "partial1 set set" where
  "TOTAL \<equiv> {U. \<exists>\<psi> s. learn_total \<psi> U s}"

lemma TOTAL_subseteq_LIM: "TOTAL \<subseteq> LIM"
  unfolding TOTAL_def Lim_def using learn_total_def by auto

lemma learn_totalI:
  assumes "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i)"
    and "\<And>f n. f \<in> U \<Longrightarrow> \<psi> (the (s (f \<triangleright> n))) \<in> \<R>"
  shows "learn_total \<psi> U s"
  using assms learn_lim_def learn_total_def by auto

lemma learn_totalE:
  assumes "learn_total \<psi> U s"
  shows "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= i)"
    and "\<And>f n. f \<in> U \<Longrightarrow> \<psi> (the (s (f \<triangleright> n))) \<in> \<R>"
  using assms learn_lim_def learn_total_def by auto

lemma learn_total_wrt_goedel:
  assumes "goedel_numbering \<chi>" and "learn_total \<psi> U s"
  shows "\<exists>t. learn_total \<chi> U t"
  using learn_total_def assms learn_lim_extra_wrt_goedel[where ?extra="\<lambda>U f n h. h \<in> \<R>"]
  by auto

lemma TOTAL_wrt_phi_eq_TOTAL: "TOTAL_wrt \<phi> = TOTAL"
  using TOTAL_wrt_def TOTAL_def learn_total_wrt_goedel goedel_numbering_phi
  by blast

lemma learn_total_closed_subseteq:
  assumes "learn_total \<psi> U s" and "V \<subseteq> U"
  shows "learn_total \<psi> V s"
  using assms learn_total_def learn_lim_closed_subseteq by auto

lemma TOTAL_closed_subseteq:
  assumes "U \<in> TOTAL" and "V \<subseteq> U"
  shows "V \<in> TOTAL"
  using assms learn_total_closed_subseteq by (smt TOTAL_def mem_Collect_eq)


subsection \<open>CP: Learning in the limit with class-preserving hypotheses\<close>

text \<open>Class-preserving learning in the limit requires all hypotheses
for prefixes from the class to be functions from the class.\<close>

definition learn_cp :: "partial2 \<Rightarrow> (partial1 set) \<Rightarrow> partial1 \<Rightarrow> bool" where
  "learn_cp \<psi> U s \<equiv>
     learn_lim \<psi> U s \<and>
     (\<forall>f\<in>U. \<forall>n. \<psi> (the (s (f \<triangleright> n))) \<in> U)"

definition CP_wrt :: "partial2 \<Rightarrow> partial1 set set" where
  "CP_wrt \<psi> \<equiv> {U. \<exists>s. learn_cp \<psi> U s}"

definition CP :: "partial1 set set" where
  "CP \<equiv> {U. \<exists>\<psi> s. learn_cp \<psi> U s}"

lemma learn_cp_wrt_goedel:
  assumes "goedel_numbering \<chi>" and "learn_cp \<psi> U s"
  shows "\<exists>t. learn_cp \<chi> U t"
  using learn_cp_def assms learn_lim_extra_wrt_goedel[where ?extra="\<lambda>U f n h. h \<in> U"]
  by auto

corollary CP_wrt_phi: "CP = CP_wrt \<phi>"
  using learn_cp_wrt_goedel[OF goedel_numbering_phi]
  by (smt CP_def CP_wrt_def Collect_cong)

lemma learn_cpI:
  assumes "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow> \<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i)"
    and "\<And>f n. f \<in> U \<Longrightarrow> \<psi> (the (s (f \<triangleright> n))) \<in> U"
  shows "learn_cp \<psi> U s"
  using assms learn_cp_def learn_lim_def by auto

lemma learn_cpE:
  assumes "learn_cp \<psi> U s"
  shows "environment \<psi> U s"
    and "\<And>f. f \<in>  U \<Longrightarrow> \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= i)"
    and "\<And>f n. f \<in> U \<Longrightarrow> \<psi> (the (s (f \<triangleright> n))) \<in> U"
  using assms learn_lim_def learn_cp_def by auto

text \<open>Since classes contain only total functions, a CP strategy is also
a TOTAL strategy.\<close>

lemma learn_cp_imp_total: "learn_cp \<psi> U s \<Longrightarrow> learn_total \<psi> U s"
  using learn_cp_def learn_total_def learn_lim_def by auto

lemma CP_subseteq_TOTAL: "CP \<subseteq> TOTAL"
  using learn_cp_imp_total CP_def TOTAL_def by blast


subsection \<open>FIN: Finite learning\<close>

text \<open>In general it is undecidable whether a LIM strategy has reached
its final hypothesis. By contrast, in finite learning (also called ``one-shot
learning'') the strategy signals when it is ready to output a hypothesis. Up
until then it outputs a ``don't know yet'' value. This value is represented
by zero and the actual hypothesis $i$ by $i + 1$.\<close>

definition learn_fin :: "partial2 \<Rightarrow> partial1 set \<Rightarrow> partial1 \<Rightarrow> bool" where
  "learn_fin \<psi> U s \<equiv>
     environment \<psi> U s \<and>
     (\<forall>f \<in> U. \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i))"

definition FIN_wrt :: "partial2 \<Rightarrow> partial1 set set" where
  "FIN_wrt \<psi> \<equiv> {U. \<exists>s. learn_fin \<psi> U s}"

definition FIN :: "partial1 set set" where
  "FIN \<equiv> {U. \<exists>\<psi> s. learn_fin \<psi> U s}"

lemma learn_finI:
  assumes "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow>
      \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i)"
  shows "learn_fin \<psi> U s"
  using assms learn_fin_def by auto

lemma learn_finE:
  assumes "learn_fin \<psi> U s"
  shows "environment \<psi> U s"
    and "\<And>f. f \<in> U \<Longrightarrow>
      \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i)"
  using assms learn_fin_def by auto

lemma learn_fin_closed_subseteq:
  assumes "learn_fin \<psi> U s" and "V \<subseteq> U"
  shows "learn_fin \<psi> V s"
  using assms learn_fin_def by auto

lemma learn_fin_wrt_goedel:
  assumes "goedel_numbering \<chi>" and "learn_fin \<psi> U s"
  shows "\<exists>t. learn_fin \<chi> U t"
proof -
  have env: "environment \<psi> U s"
    and fin: "\<And>f. f \<in> U \<Longrightarrow>
      \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i)"
    using assms(2) learn_finE by auto
  obtain c where c: "c \<in> \<R>" "\<forall>i. \<psi> i = \<chi> (the (c i))"
    using env goedel_numberingE[OF assms(1), of \<psi>] by auto
  define t where "t \<equiv>
    \<lambda>x. if s x \<up> then None
         else if s x = Some 0 then Some 0
              else Some (Suc (the (c (the (s x) - 1))))"
  have "t \<in> \<P>"
  proof -
    from c obtain rc where rc:
      "recfn 1 rc"
      "total rc"
      "\<forall>x. c x = eval rc [x]"
      by auto
    from env obtain rs where rs: "recfn 1 rs" "\<forall>x. s x = eval rs [x]"
      by auto
    then have "eval rs [f \<triangleright> n] \<down>" if "f \<in> U" for f n
      using env that by simp
    define rt where "rt = Cn 1 r_ifz [rs, Z, Cn 1 S [Cn 1 rc [Cn 1 r_dec [rs]]]]"
    then have "recfn 1 rt"
      using rc(1) rs(1) by simp
    have "eval rt [x] \<up>" if "eval rs [x] \<up>" for x
      using rc(1) rs(1) rt_def that by auto
    moreover have "eval rt [x] \<down>= 0" if "eval rs [x] \<down>= 0" for x
      using rt_def that rc(1,2) rs(1) by simp
    moreover have "eval rt [x] \<down>= Suc (the (c (the (s x) - 1)))" if "eval rs [x] \<down>\<noteq> 0" for x
      using rt_def that rc rs by auto
    ultimately have "eval rt [x] = t x" for x
      by (simp add: rs(2) t_def)
    with \<open>recfn 1 rt\<close> show ?thesis by auto
  qed
  have t: "t (f \<triangleright> n) \<down>=
      (if s (f \<triangleright> n) = Some 0 then 0 else Suc (the (c (the (s (f \<triangleright> n)) - 1))))"
    if "f \<in> U" for f n
    using that env by (simp add: t_def)
  have "learn_fin \<chi> U t"
  proof (rule learn_finI)
    show "environment \<chi> U t"
      using t by (simp add: \<open>t \<in> \<P>\<close> env goedel_numbering_P2[OF assms(1)])
    show "\<exists>i n\<^sub>0. \<chi> i = f \<and> (\<forall>n<n\<^sub>0. t (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. t (f \<triangleright> n) \<down>= Suc i)"
      if "f \<in> U" for f
    proof -
      from fin obtain i n\<^sub>0 where
        i: "\<psi> i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i)"
        using \<open>f \<in> U\<close> by blast
      let ?j = "the (c i)"
      have "\<chi> ?j = f"
        using c(2) i by simp
      moreover have "\<forall>n<n\<^sub>0. t (f \<triangleright> n) \<down>= 0"
        using t[OF that] i by simp
      moreover have "t (f \<triangleright> n) \<down>= Suc ?j" if "n \<ge> n\<^sub>0" for n
        using that i t[OF \<open>f \<in> U\<close>] by simp
      ultimately show ?thesis by auto
    qed
  qed
  then show ?thesis by auto
qed

end