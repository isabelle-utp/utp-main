theory Kleene_Fixed_Point
  imports Complete_Relations
begin


section \<open>Iterative Fixed Point Theorem\<close>

text \<open>Kleene's fixed-point theorem states that,
for a pointed directed complete partial order $\tp{A,\SLE}$
and a Scott-continuous map $f: A \to A$,
the supremum of $\set{f^n(\bot) \mid n\in\Nat}$ exists in $A$ and is a least 
fixed point.
Mashburn \cite{mashburn83} generalized the result so that
$\tp{A,\SLE}$ is a $\omega$-complete partial order
and $f$ is $\omega$-continuous.

In this section we further generalize the result and show that
for $\omega$-complete relation $\tp{A,\SLE}$
and for every bottom element $\bot \in A$,
the set $\set{f^n(\bot) \mid n\in\Nat}$ has suprema (not necessarily unique, of 
course) and, 
they are quasi-fixed points.
Moreover, if $(\SLE)$ is attractive, then the suprema are precisely the least 
quasi-fixed points.\<close>

subsection \<open>Scott Continuity, $\omega$-Completeness, $\omega$-Continuity\<close>

text \<open>In this Section, we formalize $\omega$-completeness, Scott continuity and $\omega$-continuity.
We then prove that a Scott continuous map is $\omega$-continuous and that an $\omega$-continuous 
map is ``nearly'' monotone.\<close>

context
  fixes A :: "'a set" and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

definition "omega_continuous f \<equiv>
  f ` A \<subseteq> A \<and>
  (\<forall>c :: nat \<Rightarrow> 'a. \<forall> b \<in> A.
  range c \<subseteq> A \<longrightarrow>
  monotone (\<le>) (\<sqsubseteq>) c \<longrightarrow>
  extreme_bound A (\<sqsubseteq>) (range c) b \<longrightarrow> extreme_bound A (\<sqsubseteq>) (f ` range c) (f b))"

lemmas omega_continuousI[intro?] =
  omega_continuous_def[unfolded atomize_eq, THEN iffD2, unfolded conj_imp_eq_imp_imp, rule_format]

lemmas omega_continuousDdom =
  omega_continuous_def[unfolded atomize_eq, THEN iffD1, unfolded conj_imp_eq_imp_imp, THEN conjunct1]

lemmas omega_continuousD =
  omega_continuous_def[unfolded atomize_eq, THEN iffD1, unfolded conj_imp_eq_imp_imp, THEN conjunct2, rule_format]

lemmas omega_continuousE[elim] =
  omega_continuous_def[unfolded atomize_eq, THEN iffD1, elim_format, unfolded conj_imp_eq_imp_imp, rule_format]

lemma omega_continuous_imp_mono_refl:
  assumes cont: "omega_continuous f"
    and x: "x \<in> A" and y: "y \<in> A"
    and xy: "x \<sqsubseteq> y" and xx: "x \<sqsubseteq> x" and yy: "y \<sqsubseteq> y"
  shows "f x \<sqsubseteq> f y"
proof-
  define c :: "nat \<Rightarrow> 'a" where "c \<equiv> \<lambda>i. if i = 0 then x else y"
  from x y xx xy yy have c: "range c \<subseteq> A" "monotone (\<le>) (\<sqsubseteq>) c"
    by (auto simp: c_def intro!: monotoneI)
  have "extreme_bound A (\<sqsubseteq>) (range c) y" using xy yy x y by (auto simp: c_def)
  then have fboy: "extreme_bound A (\<sqsubseteq>) (f ` range c) (f y)" using c cont y by auto
  then show "f x \<sqsubseteq> f y" by (auto simp: c_def)
qed

definition "scott_continuous f \<equiv>
  f ` A \<subseteq> A \<and>
  (\<forall>X s. X \<subseteq> A \<longrightarrow> directed X (\<sqsubseteq>) \<longrightarrow> X \<noteq> {} \<longrightarrow> extreme_bound A (\<sqsubseteq>) X s \<longrightarrow> extreme_bound A (\<sqsubseteq>) (f ` X) (f s))"

lemmas scott_continuousI[intro?] =
  scott_continuous_def[unfolded atomize_eq, THEN iffD2, unfolded conj_imp_eq_imp_imp, rule_format]

lemmas scott_continuousE =
  scott_continuous_def[unfolded atomize_eq, THEN iffD1, elim_format, unfolded conj_imp_eq_imp_imp, rule_format]

lemma scott_continuous_imp_mono_refl:
  assumes scott: "scott_continuous f"
    and x: "x \<in> A" and y: "y \<in> A" and xy: "x \<sqsubseteq> y" and yy: "y \<sqsubseteq> y"
  shows "f x \<sqsubseteq> f y"
proof-
  define D where "D \<equiv> {x,y}"
  from x y xy yy have dir_D: "D \<subseteq> A" "directed D (\<sqsubseteq>)" "D \<noteq> {}"
    by (auto simp: D_def intro!: bexI[of _ y] directedI)
  have "extreme_bound A (\<sqsubseteq>) D y" using xy yy x y by (auto simp: D_def)
  then have fboy: "extreme_bound A (\<sqsubseteq>) (f ` D) (f y)" using dir_D scott by (auto elim!: scott_continuousE)
  then show "f x \<sqsubseteq> f y" by (auto simp: D_def)
qed

lemma scott_continuous_imp_omega_continuous:
  assumes scott: "scott_continuous f" shows "omega_continuous f"
proof
  from scott show "f ` A \<subseteq> A" by (auto elim!: scott_continuousE)
  fix c :: "nat \<Rightarrow> 'a"
  assume mono: "monotone (\<le>) (\<sqsubseteq>) c" and c: "range c \<subseteq> A"
  from monotone_directed_image[OF mono[folded monotone_on_UNIV] order.directed] scott c
  show "extreme_bound A (\<sqsubseteq>) (range c) b \<Longrightarrow> extreme_bound A (\<sqsubseteq>) (f ` range c) (f b)" for b
    by (auto elim!: scott_continuousE)
qed

end

subsection \<open>Existence of Iterative Fixed Points\<close>

text \<open>The first part of Kleene's theorem demands to prove that the set 
$\set{f^n(\bot) \mid n \in \Nat}$ has a supremum and 
that all such are quasi-fixed points. We prove this claim without assuming 
anything on the relation $\SLE$ besides $\omega$-completeness and one bottom element.\<close>

(*
no_notation power (infixr "^" 80)
*)
notation compower ("_^_"[1000,1000]1000)

lemma mono_funpow: assumes f: "f ` A \<subseteq> A" and mono: "monotone_on A r r f"
  shows "monotone_on A r r (f^n)"
proof (induct n)
  case 0
  show ?case using monotone_on_id by (auto simp: id_def)
next
  case (Suc n)
  with funpow_dom[OF f] show ?case
    by (auto intro!: monotone_onI monotone_onD[OF mono] elim!:monotone_onE)
qed

no_notation bot ("\<bottom>")

context
  fixes A and less_eq (infix "\<sqsubseteq>" 50) and bot ("\<bottom>") and f
  assumes bot: "\<bottom> \<in> A" "\<forall>q \<in> A. \<bottom> \<sqsubseteq> q"
  assumes cont: "omega_continuous A (\<sqsubseteq>) f"
begin

interpretation less_eq_notations.

private lemma f: "f ` A \<subseteq> A" using cont by auto

private abbreviation(input) "Fn \<equiv> {f^n \<bottom> |. n :: nat}"

private lemma fn_ref: "f^n \<bottom> \<sqsubseteq> f^n \<bottom>" and fnA: "f^n \<bottom> \<in> A"
proof (atomize(full), induct n)
  case 0
  from bot show ?case by simp
next
  case (Suc n)
  then have fn: "f^n \<bottom> \<in> A" and fnfn: "f^n \<bottom> \<sqsubseteq> f^n \<bottom>" by auto
  from f fn omega_continuous_imp_mono_refl[OF cont fn fn fnfn fnfn fnfn]
  show ?case by auto
qed

private lemma FnA: "Fn \<subseteq> A" using fnA by auto

private lemma fn_monotone: "monotone (\<le>) (\<sqsubseteq>) (\<lambda>n. f^n \<bottom>)"
proof
  fix n m :: nat
  assume "n \<le> m"
  from le_Suc_ex[OF this] obtain k where m: "m = n + k" by auto
  from bot fn_ref fnA omega_continuous_imp_mono_refl[OF cont]
  show "f^n \<bottom> \<sqsubseteq> f^m \<bottom>" by (unfold m, induct n, auto)
qed

private lemma Fn: "Fn = range (\<lambda>n. f^n \<bottom>)" by auto

theorem kleene_qfp:
  assumes q: "extreme_bound A (\<sqsubseteq>) Fn q"
  shows "f q \<sim> q"
proof
  have fq: "extreme_bound A (\<sqsubseteq>) (f ` Fn) (f q)"
    apply (unfold Fn)
    apply (rule omega_continuousD[OF cont])
    using FnA fn_monotone q by (unfold Fn, auto)
  with bot have nq: "f^n \<bottom> \<sqsubseteq> f q" for n
    by(induct n, auto simp: extreme_bound_iff)
  then show "q \<sqsubseteq> f q" using f q by blast
  have "f (f^n \<bottom>) \<in> Fn" for n by (auto intro!: exI[of _ "Suc n"])
  then have "f ` Fn \<subseteq> Fn" by auto
  from extreme_bound_mono[OF this fq q]
  show "f q \<sqsubseteq> q".
qed

lemma ex_kleene_qfp:
  assumes comp: "omega_complete A (\<sqsubseteq>)"
  shows "\<exists>p. extreme_bound A (\<sqsubseteq>) Fn p" 
  using fn_monotone
  apply (intro comp[unfolded omega_complete_def, THEN completeD, OF FnA])
  by fast

subsection \<open>Iterative Fixed Points are Least.\<close>
text \<open>Kleene's theorem also states that the quasi-fixed point found this way is a least one.
Again, attractivity is needed to prove this statement.\<close>

lemma kleene_qfp_is_least:
  assumes attract: "\<forall>q \<in> A. \<forall>x \<in> A. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
  assumes q: "extreme_bound A (\<sqsubseteq>) Fn q"
  shows "extreme {s \<in> A. f s \<sim> s} (\<sqsupseteq>) q"
proof(safe intro!: extremeI kleene_qfp[OF q])
  from q
  show "q \<in> A" by auto
  fix c assume c: "c \<in> A" and cqfp: "f c \<sim> c"
  {
    fix n::nat
    have "f^n \<bottom> \<sqsubseteq> c"
    proof(induct n)
      case 0
      show ?case using bot c by auto
    next
      case IH: (Suc n)
      have "c \<sqsubseteq> c" using attract cqfp c by auto
      with IH have "f^(Suc n) \<bottom> \<sqsubseteq> f c"
        using omega_continuous_imp_mono_refl[OF cont] fn_ref fnA c by auto
      then show ?case using attract cqfp c fnA by blast
    qed
  }
  then show "q \<sqsubseteq> c" using q c by auto
qed

lemma kleene_qfp_iff_least:
  assumes comp: "omega_complete A (\<sqsubseteq>)"
  assumes attract: "\<forall>q \<in> A. \<forall>x \<in> A. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
  assumes dual_attract: "\<forall>p \<in> A. \<forall>q \<in> A. \<forall>x \<in> A. p \<sim> q \<longrightarrow> q \<sqsubseteq> x \<longrightarrow> p \<sqsubseteq> x"
  shows "extreme_bound A (\<sqsubseteq>) Fn = extreme {s \<in> A. f s \<sim> s} (\<sqsupseteq>)"
proof (intro ext iffI kleene_qfp_is_least[OF attract])
  fix q
  assume q: "extreme {s \<in> A. f s \<sim> s} (\<sqsupseteq>) q"
  from q have qA: "q \<in> A" by auto
  from q have qq: "q \<sqsubseteq> q" by auto
  from q have fqq: "f q \<sim> q" by auto
  from ex_kleene_qfp[OF comp]
  obtain k where k: "extreme_bound A (\<sqsubseteq>) Fn k" by auto
  have qk: "q \<sim> k"
  proof
    from kleene_qfp[OF k] q k
    show "q \<sqsubseteq> k" by auto
    from kleene_qfp_is_least[OF _ k] q attract
    show "k \<sqsubseteq> q" by blast
  qed
  show "extreme_bound A (\<sqsubseteq>) Fn q"
  proof (intro extreme_boundI,safe)
    fix n
    show "f^n \<bottom> \<sqsubseteq> q"
    proof (induct n)
      case 0
      from bot q show ?case by auto 
    next
      case S:(Suc n)
      from fnA f have fsnbA: "f (f^n \<bottom>) \<in> A" by auto
      have fnfn: "f^n \<bottom> \<sqsubseteq> f^n \<bottom>" using fn_ref by auto
      have "f (f^n \<bottom>) \<sqsubseteq> f q"
        using omega_continuous_imp_mono_refl[OF cont fnA qA S fnfn qq] by auto
      then show ?case using fsnbA qA attract fqq by auto
    qed
  next
    fix x
    assume "bound Fn (\<sqsubseteq>) x" and x: "x \<in> A"
    with k have kx: "k \<sqsubseteq> x" by auto
    with dual_attract[rule_format, OF _ _ x qk] q k
    show "q \<sqsubseteq> x" by auto
  next
    from q show "q \<in> A" by auto
  qed
qed

end

context attractive begin

interpretation less_eq_notations.

theorem kleene_qfp_is_dual_extreme:
  assumes comp: "omega_complete A (\<sqsubseteq>)"
    and cont: "omega_continuous A (\<sqsubseteq>) f" and bA: "b \<in> A" and bot: "\<forall>x \<in> A. b \<sqsubseteq> x"
  shows "extreme_bound A (\<sqsubseteq>) {f^n b |. n :: nat} = extreme {s \<in> A. f s \<sim> s} (\<sqsupseteq>)"
  apply (rule kleene_qfp_iff_least[OF bA bot cont comp])
  using cont[THEN omega_continuousDdom]
  by (auto dest: sym_order_trans order_sym_trans)

end

corollary(in antisymmetric) kleene_fp:
  assumes cont: "omega_continuous A (\<sqsubseteq>) f"
    and b: "b \<in> A" "\<forall>x \<in> A. b \<sqsubseteq> x"
    and p: "extreme_bound A (\<sqsubseteq>) {f^n b |. n :: nat} p"
  shows "f p = p"
  using kleene_qfp[OF b cont] p cont[THEN omega_continuousDdom]
  by (auto 2 3 intro!:antisym)

no_notation compower ("_^_"[1000,1000]1000)

end