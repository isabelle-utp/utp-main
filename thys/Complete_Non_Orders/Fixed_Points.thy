(*
Author:  Jérémy Dubut (2019-2021)
Author:  Akihisa Yamada (2019-2021)
License: LGPL (see file COPYING.LESSER)
*)

theory Fixed_Points
  imports Complete_Relations
begin

section \<open>Existence of Fixed Points in Complete Related Sets\<close>
text \<open>\label{sec:qfp-exists}\<close>

text \<open>The following proof is simplified and generalized from
  Stouti--Maaden \cite{SM13}. We construct some set whose extreme bounds 
  -- if they exist, typically when the underlying related set is complete -- 
  are fixed points of a monotone or inflationary function on any 
  related set. When the related set is attractive, those are actually the least fixed points.
  This generalizes \cite{SM13}, relaxing reflexivity and antisymmetry.\<close>

locale fixed_point_proof = related_set +
  fixes f
  assumes f: "f ` A \<subseteq> A"
begin

sublocale less_eq_notations.

definition AA where "AA \<equiv>
  {X. X \<subseteq> A \<and> f ` X \<subseteq> X \<and> (\<forall>Y s. Y \<subseteq> X \<longrightarrow> extreme_bound A (\<sqsubseteq>) Y s \<longrightarrow> s \<in> X)}"

lemma AA_I:
  "X \<subseteq> A \<Longrightarrow> f ` X \<subseteq> X \<Longrightarrow> (\<And>Y s. Y \<subseteq> X \<Longrightarrow> extreme_bound A (\<sqsubseteq>) Y s \<Longrightarrow> s \<in> X) \<Longrightarrow> X \<in> AA"
  by (unfold AA_def, safe)

lemma AA_E:
  "X \<in> AA \<Longrightarrow>
   (X \<subseteq> A \<Longrightarrow> f ` X \<subseteq> X \<Longrightarrow> (\<And>Y s. Y \<subseteq> X \<Longrightarrow> extreme_bound A (\<sqsubseteq>) Y s \<Longrightarrow> s \<in> X) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: AA_def)

definition C where "C \<equiv> \<Inter> AA"

lemma A_AA: "A \<in> AA" by (auto intro!:AA_I f)

lemma C_AA: "C \<in> AA"
proof (intro AA_I)
  show "C \<subseteq> A" using C_def A_AA f by auto
  show "f ` C \<subseteq> C" unfolding C_def AA_def by auto
  fix B b assume B: "B \<subseteq> C" "extreme_bound A (\<sqsubseteq>) B b"
  { fix X assume X: "X \<in> AA"
    with B have "B \<subseteq> X" by (auto simp: C_def)
    with X B have "b\<in>X" by (auto elim!: AA_E)
  }
  then show "b \<in> C" by (auto simp: C_def AA_def)
qed

lemma CA: "C \<subseteq> A" using A_AA by (auto simp: C_def)

lemma fC: "f ` C \<subseteq> C" using C_AA by (auto elim!: AA_E)

context
  fixes c assumes Cc: "extreme_bound A (\<sqsubseteq>) C c"
begin

private lemma cA: "c \<in> A" using Cc by auto
private lemma cC: "c \<in> C" using Cc C_AA by (blast elim!:AA_E) 
private lemma fcC: "f c \<in> C" using cC AA_def C_AA by auto
private lemma fcA: "f c \<in> A" using fcC CA by auto

lemma qfp_as_extreme_bound:
  assumes infl_mono: "\<forall>x \<in> A. x \<sqsubseteq> f x \<or> (\<forall>y \<in> A. y \<sqsubseteq> x \<longrightarrow> f y \<sqsubseteq> f x)"
  shows "f c \<sim> c"
proof (intro conjI bexI sympartpI)
  show "f c \<sqsubseteq> c" using fcC Cc by auto
  from infl_mono[rule_format, OF cA]
  show "c \<sqsubseteq> f c"
  proof (safe)
    text \<open>Monotone case:\<close>
    assume mono: "\<forall>b\<in>A. b \<sqsubseteq> c \<longrightarrow> f b \<sqsubseteq> f c"
    define D where "D \<equiv> {x \<in> C. x \<sqsubseteq> f c}"
    have "D \<in> AA"
    proof (intro AA_I)
      show "D \<subseteq> A" unfolding D_def C_def using A_AA f by auto
      have fxC: "x \<in> C \<Longrightarrow> x \<sqsubseteq> f c \<Longrightarrow> f x \<in> C" for x using C_AA by (auto simp: AA_def)
      show "f ` D \<subseteq> D"
      proof (unfold D_def, safe intro!: fxC)
        fix x assume xC: "x \<in> C"
        have "x \<sqsubseteq> c" "x \<in> A" using Cc xC CA by auto
        then show "f x \<sqsubseteq> f c" using mono by (auto dest:monotoneD)
      qed
      have DC: "D \<subseteq> C" unfolding D_def by auto
      fix B b assume BD: "B \<subseteq> D" and Bb: "extreme_bound A (\<sqsubseteq>) B b"
      have "B \<subseteq> C" using DC BD by auto
      then have bC: "b \<in> C" using C_AA Bb BD by (auto elim!: AA_E)
      have bfc: "\<forall>a\<in>B. a \<sqsubseteq> f c" using BD unfolding D_def by auto
      with f cA Bb
      have "b \<sqsubseteq> f c" by (auto simp: extreme_def image_subset_iff)
      with bC show "b \<in> D" unfolding D_def by auto
    qed
    then have "C \<subseteq> D" unfolding C_def by auto
    then show "c \<sqsubseteq> f c" using cC unfolding D_def by auto
  qed
qed

lemma extreme_qfp:
  assumes attract: "\<forall>q \<in> A. \<forall>x \<in> A. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
    and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "extreme {q \<in> A. f q \<sim> q \<or> f q = q} (\<sqsupseteq>) c"
proof-
  have fcc: "f c \<sim> c"
    apply (rule qfp_as_extreme_bound)
    using mono by (auto elim!: monotone_onE)
  define L where [simp]: "L \<equiv> {a \<in> A. \<forall>s \<in> A. (f s \<sim> s \<or> f s = s) \<longrightarrow> a \<sqsubseteq> s}"
  have "L \<in> AA"
  proof (unfold AA_def, intro CollectI conjI allI impI)
    show XA: "L \<subseteq> A" by auto  
    show "f ` L \<subseteq> L"
    proof safe
      fix x assume xL: "x \<in> L"
      show "f x \<in> L"
      proof (unfold L_def, safe)
        have xA: "x \<in> A" using xL by auto 
        then show fxA: "f x \<in> A" using f by auto
        { fix s assume sA: "s \<in> A" and sf: "f s \<sim> s \<or> f s = s"
          then have "x \<sqsubseteq> s" using xL sA sf by auto
          then have "f x \<sqsubseteq> f s" using mono fxA sA xA by (auto elim!:monotone_onE)}
        note fxfs = this
        { fix s assume sA: "s \<in> A" and sf: "f s \<sim> s"
          then show "f x \<sqsubseteq> s" using fxfs attract mono sf fxA sA xA by (auto elim!:monotone_onE)
        }
        { fix s assume sA: "s \<in> A" and sf: "f s = s"
          with fxfs[OF sA] show "f x \<sqsubseteq> s" by simp}
      qed 
    qed
    fix B b assume BL: "B \<subseteq> L" and b: "extreme_bound A (\<sqsubseteq>) B b"
    then have BA: "B \<subseteq> A" by auto
    with BL b have bA: "b \<in> A" by auto
    show "b \<in> L"
    proof (unfold L_def, safe intro!: bA)
      { fix s assume sA: "s \<in> A" and sf: "f s \<sim> s \<or> f s = s"
        have "bound B (\<sqsubseteq>) s" using sA BL b sf by auto
      }
      note Bs = this
      { fix s assume sA: "s \<in> A" and sf: "f s \<sim> s"
        with b sA Bs show "b \<sqsubseteq> s" by auto
      }
      { fix s assume sA: "s \<in> A" and sf: "f s = s"
        with b sA Bs show "b \<sqsubseteq> s" by auto
      }
    qed
  qed
  then have "C \<subseteq> L" by (simp add: C_def Inf_lower)
  with cC have "c \<in> L" by auto
  with L_def fcc
  show ?thesis by auto
qed

end

lemma ex_qfp:
  assumes comp: "CC-complete A (\<sqsubseteq>)" and C: "C \<in> CC"
    and infl_mono: "\<forall>a \<in> A. a \<sqsubseteq> f a \<or> (\<forall>b \<in> A. b \<sqsubseteq> a \<longrightarrow> f b \<sqsubseteq> f a)"
  shows "\<exists>s \<in> A. f s \<sim> s"
  using qfp_as_extreme_bound[OF _  infl_mono] completeD[OF comp CA C] by auto

lemma ex_extreme_qfp_fp:
  assumes comp: "CC-complete A (\<sqsubseteq>)" and C: "C \<in> CC"
    and attract: "\<forall>q \<in> A. \<forall>x \<in> A. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
    and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "\<exists>c. extreme {q \<in> A. f q \<sim> q \<or> f q = q} (\<sqsupseteq>) c"
  using extreme_qfp[OF _ attract mono] completeD[OF comp CA C] by auto

lemma ex_extreme_qfp:
  assumes comp: "CC-complete A (\<sqsubseteq>)" and C: "C \<in> CC"
    and attract: "\<forall>q \<in> A. \<forall>x \<in> A. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
    and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "\<exists>c. extreme {q \<in> A. f q \<sim> q} (\<sqsupseteq>) c"
proof-
  from completeD[OF comp CA C]
  obtain c where Cc: "extreme_bound A (\<sqsubseteq>) C c" by auto
  from extreme_qfp[OF Cc attract mono]
  have Qc: "bound {q \<in> A. f q \<sim> q} (\<sqsupseteq>) c" by auto
  have fcc: "f c \<sim> c"
    apply (rule qfp_as_extreme_bound[OF Cc])
    using mono by (auto simp: monotone_onD)
  from Cc CA have cA: "c \<in> A" by auto
  from Qc fcc cA show ?thesis by (auto intro!: exI[of _ c])
qed

end

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) and A :: "'a set" and f
  assumes f: "f ` A \<subseteq> A"
begin

interpretation less_eq_notations.
interpretation fixed_point_proof A "(\<sqsubseteq>)" f using f by unfold_locales

theorem complete_infl_mono_imp_ex_qfp:
  assumes comp: "UNIV-complete A (\<sqsubseteq>)" and infl_mono: "\<forall>a\<in>A. a \<sqsubseteq> f a \<or> (\<forall>b\<in>A. b \<sqsubseteq> a \<longrightarrow> f b \<sqsubseteq> f a)"
  shows "\<exists>s\<in>A. f s \<sim> s"
  apply (rule ex_qfp[OF comp _ infl_mono]) by auto

end

corollary (in antisymmetric) complete_infl_mono_imp_ex_fp:
  assumes comp: "UNIV-complete A (\<sqsubseteq>)" and f: "f ` A \<subseteq> A"
    and infl_mono: "\<forall>a\<in>A. a \<sqsubseteq> f a \<or> (\<forall>b\<in>A. b \<sqsubseteq> a \<longrightarrow> f b \<sqsubseteq> f a)"
  shows "\<exists>s \<in> A. f s = s"
proof-
  interpret less_eq_notations.
  from complete_infl_mono_imp_ex_qfp[OF f comp infl_mono]
  obtain s where sA: "s \<in> A" and fss: "f s \<sim> s" by auto
  from f sA have fsA: "f s \<in> A" by auto
  have "f s = s" using antisym fsA sA fss by auto
  with sA show ?thesis by auto
qed

context semiattractive begin

interpretation less_eq_notations.

theorem complete_mono_imp_ex_extreme_qfp:
  assumes comp: "UNIV-complete A (\<sqsubseteq>)" and f: "f ` A \<subseteq> A"
    and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "\<exists>s. extreme {p \<in> A. f p \<sim> p} (\<sqsubseteq>) s"
proof-
  interpret dual: fixed_point_proof A "(\<sqsupseteq>)" rewrites "dual.sym = (\<sim>)"
    using f by unfold_locales (auto intro!:ext)
  show ?thesis
    apply (rule dual.ex_extreme_qfp[OF complete_dual[OF comp] _ _ monotone_on_dual[OF mono]])
    apply simp
    using f sym_order_trans by blast
qed

end

corollary (in antisymmetric) complete_mono_imp_ex_extreme_fp:
  assumes comp: "UNIV-complete A (\<sqsubseteq>)" and f: "f ` A \<subseteq> A"
    and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "\<exists>s. extreme {s \<in> A. f s = s} (\<sqsubseteq>)\<^sup>- s"
proof-
  interpret less_eq_notations.
  interpret fixed_point_proof A "(\<sqsubseteq>)" f using f by unfold_locales
  have "\<exists>c. extreme {q \<in> A. f q \<sim> q \<or> f q = q} (\<sqsupseteq>) c"
    apply (rule ex_extreme_qfp_fp[OF comp _ _ mono])
    using antisym f by (auto dest: order_sym_trans)
  then obtain c where c: "extreme {q \<in> A. f q \<sim> q \<or> f q = q} (\<sqsupseteq>) c" by auto
  then have "f c = c" using antisym f by blast
  with c have "extreme {q \<in> A. f q = q} (\<sqsupseteq>) c" by auto
  then show ?thesis by auto
qed

section \<open>Fixed Points in Well-Complete Antisymmetric Sets\<close>
text \<open>\label{sec:well-complete}\<close>

text \<open>In this section, we prove that an
inflationary or monotone map over a well-complete antisymmetric set
has a fixed point.

In order to formalize such a theorem in Isabelle,
we followed Grall's~\cite{grall10} elementary proof for Bourbaki--Witt and Markowsky's theorems.
His idea is to consider well-founded derivation trees over $A$,
where from a set $C \subseteq A$ of premises
one can derive $f\:(\bigsqcup C)$ if $C$ is a chain.
The main observation is as follows:
Let $D$ be the set of all the derivable elements; that is,
for each $d \in D$ there exists a well-founded derivation
whose root is $d$.
It is shown that $D$ is a chain,
and hence one can build a derivation yielding $f\:(\bigsqcup D)$,
and $f\:(\bigsqcup D)$ is shown to be a fixed point.\<close>

lemma bound_monotone_on:
  assumes mono: "monotone_on A r s f" and XA: "X \<subseteq> A" and aA: "a \<in> A" and rXa: "bound X r a"
  shows "bound (f`X) s (f a)"
proof (safe)
  fix x assume xX: "x \<in> X" 
  from rXa xX have "r x a" by auto
  with xX XA mono aA show "s (f x) (f a)" by (auto elim!:monotone_onE)
qed

context fixed_point_proof begin

text \<open>To avoid the usage of the axiom of choice, we carefully define derivations so that any derivable element
determines its lower set. This led to the following definition:\<close>

definition "derivation X \<equiv> X \<subseteq> A \<and> well_ordered_set X (\<sqsubseteq>) \<and>
  (\<forall>x \<in> X. let Y = {y \<in> X. y \<sqsubset> x} in
    (\<exists>y. extreme Y (\<sqsubseteq>) y \<and> x = f y) \<or>
    f ` Y \<subseteq> Y \<and> extreme_bound A (\<sqsubseteq>) Y x)"

lemma assumes "derivation P"
  shows derivation_A: "P \<subseteq> A" and derivation_well_ordered: "well_ordered_set P (\<sqsubseteq>)"
  using assms by (auto simp: derivation_def)

lemma derivation_cases[consumes 2, case_names suc lim]:
  assumes "derivation X" and "x \<in> X"
    and "\<And>Y y. Y = {y \<in> X. y \<sqsubset> x} \<Longrightarrow> extreme Y (\<sqsubseteq>) y \<Longrightarrow> x = f y \<Longrightarrow> thesis"
    and "\<And>Y. Y = {y \<in> X. y \<sqsubset> x} \<Longrightarrow> f ` Y \<subseteq> Y \<Longrightarrow> extreme_bound A (\<sqsubseteq>) Y x \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding derivation_def Let_def by auto

definition "derivable x \<equiv> \<exists>X. derivation X \<and> x \<in> X"

lemma derivableI[intro?]: "derivation X \<Longrightarrow> x \<in> X \<Longrightarrow> derivable x" by (auto simp: derivable_def)
lemma derivableE: "derivable x \<Longrightarrow> (\<And>P. derivation P \<Longrightarrow> x \<in> P \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: derivable_def)

lemma derivable_A: "derivable x \<Longrightarrow> x \<in> A" by (auto elim: derivableE dest:derivation_A)

lemma UN_derivations_eq_derivable: "(\<Union>{P. derivation P}) = {x. derivable x}"
  by (auto simp: derivable_def)

context
  assumes ord: "antisymmetric A (\<sqsubseteq>)"
begin

interpretation antisymmetric using ord.

lemma derivation_lim:
  assumes P: "derivation P" and fP: "f ` P \<subseteq> P" and Pp: "extreme_bound A (\<sqsubseteq>) P p"
  shows "derivation (P \<union> {p})"
proof (cases "p \<in> P")
  case True
  with P show ?thesis by (auto simp: insert_absorb)
next
  case pP: False
  interpret P: well_ordered_set P "(\<sqsubseteq>)" using derivation_well_ordered[OF P].
  have PA: "P \<subseteq> A" using derivation_A[OF P].
  from Pp have pA: "p \<in> A" by auto
  have bp: "bound P (\<sqsubseteq>) p" using Pp by auto
  then have pp: "p \<sqsubseteq> p" using Pp by auto
  have 1: "y \<in> P \<longrightarrow> {x. (x = p \<or> x \<in> P) \<and> x \<sqsubset> y} = {x \<in> P. x \<sqsubset> y}" for y
    using Pp by (auto dest:extreme_bound_bound)
  { fix x assume xP: "x \<in> P" and px: "p \<sqsubseteq> x"
    from xP Pp have "x \<sqsubseteq> p" by auto
    with px have "p = x" using xP PA pA by (auto intro!: antisym)
    with xP pP
    have "False" by auto
  }
  note 2 = this
  then have 3: "{x. (x = p \<or> x \<in> P) \<and> x \<sqsubset> p} = P" using Pp by (auto intro!: asympartpI)
  have wr: "well_ordered_set (P \<union> {p}) (\<sqsubseteq>)"
    apply (rule well_order_extend[OF P.well_ordered_set_axioms])
    using pp bp pP 2 by auto
  from P fP Pp
  show "derivation (P \<union> {p})" by (auto simp: derivation_def pA wr[simplified] 1 3)
qed

context
  assumes derivation_infl: "\<forall>X x y. derivation X \<longrightarrow> x \<in> X \<longrightarrow> y \<in> X \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> x \<sqsubseteq> f y"
    and derivation_f_refl: "\<forall>X x. derivation X \<longrightarrow> x \<in> X \<longrightarrow> f x \<sqsubseteq> f x"
begin

lemma derivation_suc:
  assumes P: "derivation P" and Pp: "extreme P (\<sqsubseteq>) p" shows "derivation (P \<union> {f p})"
proof (cases "f p \<in> P")
  case True
  with P show ?thesis by (auto simp: insert_absorb)
next
  case fpP: False
  interpret P: well_ordered_set P "(\<sqsubseteq>)" using derivation_well_ordered[OF P].
  have PA: "P \<subseteq> A" using derivation_A[OF P].
  with Pp have pP: "p \<in> P" and pA: "p \<in> A" by auto
  with f have fpA: "f p \<in> A" by auto 
  from pP have pp: "p \<sqsubseteq> p" by auto
  from derivation_infl[rule_format, OF P pP pP pp] have "p \<sqsubseteq> f p".
  { fix x assume xP: "x \<in> P"
    then have xA: "x \<in> A" using PA by auto
    have xp: "x \<sqsubseteq> p" using xP Pp by auto
    from derivation_infl[rule_format, OF P xP pP this]
    have "x \<sqsubseteq> f p".
  }
  note Pfp = this
  then have bfp: "bound P (\<sqsubseteq>) (f p)" by auto
  { fix y assume yP: "y \<in> P"
    note yfp = Pfp[OF yP]
    { assume fpy: "f p \<sqsubseteq> y"
      with yfp have "f p = y" using yP PA pA fpA antisym by auto
      with yP fpP have "False" by auto
    }
    with Pfp yP have "y \<sqsubset> f p" by auto
  }
  note Pfp = this
  have 1: "\<And>y. y \<in> P \<longrightarrow> {x. (x = f p \<or> x \<in> P) \<and> x \<sqsubset> y} = {x \<in> P. x \<sqsubset> y}"
   and 2: "{x. (x = f p \<or> x \<in> P) \<and> x \<sqsubset> f p} = P" using Pfp by auto
  have wr: "well_ordered_set (P \<union> {f p}) (\<sqsubseteq>)"
    apply (rule well_order_extend[OF P.well_ordered_set_axioms singleton_well_ordered])
    using Pfp derivation_f_refl[rule_format, OF P pP] by auto
  from P Pp
  show "derivation (P \<union> {f p})" by (auto simp: derivation_def wr[simplified] 1 2 fpA)
qed

lemma derivable_closed:
  assumes x: "derivable x" shows "derivable (f x)"
proof (insert x, elim derivableE)
  fix P
  assume P: "derivation P" and xP: "x \<in> P"
  note PA = derivation_A[OF P]
  then have xA: "x \<in> A" using xP by auto
  interpret P: well_ordered_set P "(\<sqsubseteq>)" using derivation_well_ordered[OF P].
  interpret P.asympartp: transitive P "(\<sqsubset>)" using P.asympartp_transitive.
  define Px where "Px \<equiv> {y. y \<in> P \<and> y \<sqsubset> x} \<union> {x}"
  then have PxP: "Px \<subseteq> P" using xP by auto
  have "x \<sqsubseteq> x" using xP by auto
  then have Pxx: "extreme Px (\<sqsubseteq>) x" using xP PA by (auto simp: Px_def)
  have wr: "well_ordered_set Px (\<sqsubseteq>)" using P.well_ordered_subset[OF PxP].
  { fix z y assume zPx: "z \<in> Px" and yP: "y \<in> P" and yz: "y \<sqsubset> z"
    then have zP: "z \<in> P" using PxP by auto
    have "y \<sqsubset> x"
    proof (cases "z = x")
      case True
      then show ?thesis using yz by auto
    next
      case False
      then have zx: "z \<sqsubset> x" using zPx by (auto simp: Px_def)
      from P.asympartp.trans[OF yz zx yP zP xP] show ?thesis.
    qed
  }
  then have 1: "\<And>z. z \<in> Px \<longrightarrow> {y \<in> Px. y \<sqsubset> z} = {y \<in> P. y \<sqsubset> z}" using Px_def by blast
  have Px: "derivation Px" using PxP PA P by (auto simp: wr derivation_def 1)
  from derivation_suc[OF Px Pxx]
  show ?thesis by (auto intro!: derivableI)
qed

text \<open>The following lemma is derived from Grall’s proof. We simplify the claim so that we
consider two elements from one derivation, instead of two derivations.\<close>

lemma derivation_useful:
  assumes X: "derivation X" and xX: "x \<in> X" and yX: "y \<in> X" and xy: "x \<sqsubset> y"
  shows "f x \<sqsubseteq> y"
proof-
  interpret X: well_ordered_set X "(\<sqsubseteq>)" using derivation_well_ordered[OF X].
  note XA = derivation_A[OF X]
  { fix x y assume xX: "x \<in> X" and yX: "y \<in> X"
    from xX yX have "(x \<sqsubset> y \<longrightarrow> f x \<sqsubseteq> y \<and> f x \<in> X) \<and> (y \<sqsubset> x \<longrightarrow> f y \<sqsubseteq> x \<and> f y \<in> X)"
    proof (induct x arbitrary: y)
      case (less x)
      note xX = \<open>x \<in> X\<close> and IHx = this(2)
      with XA have xA: "x \<in> A" by auto
      from \<open>y \<in> X\<close> show ?case
      proof (induct y)
        case (less y)
        note yX = \<open>y \<in> X\<close> and IHy = this(2)
        with XA have yA: "y \<in> A" by auto
        show ?case
        proof (rule conjI; intro impI)
          assume xy: "x \<sqsubset> y"
          from X yX
          show "f x \<sqsubseteq> y \<and> f x \<in> X"
          proof (cases rule:derivation_cases)
            case (suc Z z)
            with XA have zX: "z \<in> X" and zA: "z \<in> A" and zy: "z \<sqsubset> y" and yfz: "y = f z" by auto
            from xX zX show ?thesis
            proof (cases rule: X.comparable_three_cases)
              case xz: less
              with IHy[OF zX zy] have fxz: "f x \<sqsubseteq> z" and fxX: "f x \<in> X" by auto
              from derivation_infl[rule_format, OF X fxX zX fxz] have "f x \<sqsubseteq> y" by (auto simp: yfz)
              with fxX show ?thesis by auto
            next
              case eq
              with xX zX have "x = z" by auto
              with yX yfz show ?thesis by auto
            next
              case zx: greater
              with IHy[OF zX zy] yfz xy have False by auto
              then show ?thesis by auto
            qed
          next
            case (lim Z)
            note Z = \<open>Z = {z \<in> X. z \<sqsubset> y}\<close> and fZ = \<open>f ` Z \<subseteq> Z\<close>
            from xX xy have "x \<in> Z" by (auto simp: Z)
            with fZ have "f x \<in> Z" by auto
            then have "f x \<sqsubset> y" and "f x \<in> X" by (auto simp: Z)
            then show ?thesis by auto
          qed
        next
          assume yx: "y \<sqsubset> x"
          from X xX
          show "f y \<sqsubseteq> x \<and> f y \<in> X"
          proof (cases rule:derivation_cases)
            case (suc Z z)
            with XA have zX: "z \<in> X" and zA: "z \<in> A" and zx: "z \<sqsubset> x" and xfz: "x = f z" by auto
            from yX zX show ?thesis
            proof (cases rule: X.comparable_three_cases)
              case yz: less
              with IHx[OF zX zx yX] have fyz: "f y \<sqsubseteq> z" and fyX: "f y \<in> X" by auto
              from derivation_infl[rule_format, OF X fyX zX fyz] have "f y \<sqsubseteq> x" by (auto simp: xfz)
              with fyX show ?thesis by auto
            next
              case eq
              with yX zX have "y = z" by auto
              with xX xfz show ?thesis by auto
            next
              case greater
              with IHx[OF zX zx yX] xfz yx have False by auto
              then show ?thesis by auto
            qed
          next
            case (lim Z)
            note Z = \<open>Z = {z \<in> X. z \<sqsubset> x}\<close> and fZ = \<open>f ` Z \<subseteq> Z\<close>
            from yX yx have "y \<in> Z" by (auto simp: Z)
            with fZ have "f y \<in> Z" by auto
            then have "f y \<sqsubset> x" and "f y \<in> X" by (auto simp: Z)
            then show ?thesis by auto
          qed
        qed
      qed
    qed
  }
  with assms show "f x \<sqsubseteq> y" by auto
qed

text \<open>Next one is the main lemma of this section, stating that elements from two possibly different 
derivations are comparable, and moreover the lower one is in the derivation of the upper one. 
The latter claim, not found in Grall’s proof, is crucial in proving that the union of all 
derivations is well-related.\<close>

lemma derivations_cross_compare:
  assumes X: "derivation X" and Y: "derivation Y" and xX: "x \<in> X" and yY: "y \<in> Y"
  shows "(x \<sqsubset> y \<and> x \<in> Y) \<or> x = y \<or> (y \<sqsubset> x \<and> y \<in> X)" 
proof-
  { fix X Y x y
    assume X: "derivation X" and Y: "derivation Y" and xX: "x \<in> X" and yY: "y \<in> Y"
    interpret X: well_ordered_set X "(\<sqsubseteq>)" using derivation_well_ordered[OF X].
    interpret X.asympartp: transitive X "(\<sqsubset>)" using X.asympartp_transitive.
    interpret Y: well_ordered_set Y "(\<sqsubseteq>)" using derivation_well_ordered[OF Y].
    have XA: "X \<subseteq> A" using derivation_A[OF X].
    then have xA: "x \<in> A" using xX by auto
    with f have fxA: "f x \<in> A" by auto
    have YA: "Y \<subseteq> A" using derivation_A[OF Y].
    then have yA: "y \<in> A" using yY by auto
    with f have fyA: "f y \<in> A" by auto
    { fix Z
      assume Z: "Z = {z \<in> X. z \<sqsubset> x}"
        and fZ: "f ` Z \<subseteq> Z"
        and Zx: "extreme_bound A (\<sqsubseteq>) Z x"
        and IHx: "\<forall>z \<in> X. z \<sqsubset> x \<longrightarrow> (z \<sqsubset> y \<and> z \<in> Y) \<or> z = y \<or> (y \<sqsubset> z \<and> y \<in> X)"
      have "(y \<sqsubset> x \<and> y \<in> X) \<or> x \<sqsubseteq> y"
      proof (cases "\<exists>z \<in> Z. y \<sqsubset> z")
        case True
        then obtain z where zZ: "z \<in> Z" and yz: "y \<sqsubset> z" by auto
        from zZ Z have zX: "z \<in> X" and zx: "z \<sqsubset> x" by auto
        from IHx[rule_format, OF zX zx] yz have yX: "y \<in> X" by auto
        from X.asympartp.trans[OF yz zx yX zX xX] have "y \<sqsubset> x".
        with yX show ?thesis by auto
      next
        case False
        have "bound Z (\<sqsubseteq>) y"
        proof
          fix z assume "z \<in> Z"
          then have zX: "z \<in> X" and zx: "z \<sqsubset> x" and nyz: "\<not> y \<sqsubset> z" using Z False by auto
          with IHx[rule_format, OF zX zx] X show "z \<sqsubseteq> y" by auto
        qed
        with yA Zx have xy: "x \<sqsubseteq> y" by auto
        then show ?thesis by auto
      qed
    }
    note lim_any = this
    { fix z Z
      assume Z: "Z = {z \<in> X. z \<sqsubset> x}"
        and Zz: "extreme Z (\<sqsubseteq>) z"
        and xfz: "x = f z"
        and IHx: "(z \<sqsubset> y \<and> z \<in> Y) \<or> z = y \<or> (y \<sqsubset> z \<and> y \<in> X)"
      have zX: "z \<in> X" and zx: "z \<sqsubset> x" using Zz Z by (auto simp: extreme_def)
      then have zA: "z \<in> A" using XA by auto
      from IHx have "(y \<sqsubset> x \<and> y \<in> X) \<or> x \<sqsubseteq> y"
      proof (elim disjE conjE)
        assume zy: "z \<sqsubset> y" and zY: "z \<in> Y"
        from derivation_useful[OF Y zY yY zy] xfz have xy: "x \<sqsubseteq> y" by auto
        then show ?thesis by auto
      next
        assume zy: "z = y"
        then have "y \<sqsubset> x" using zx by auto
        with zy zX show ?thesis by auto
      next
        assume yz: "y \<sqsubset> z" and yX: "y \<in> X"
        from X.asympartp.trans[OF yz zx yX zX xX] have "y \<sqsubset> x".
        with yX show ?thesis by auto
      qed
    }
    note lim_any this
  }
  note lim_any = this(1) and suc_any = this(2)
  interpret X: well_ordered_set X "(\<sqsubseteq>)" using derivation_well_ordered[OF X].
  interpret Y: well_ordered_set Y "(\<sqsubseteq>)" using derivation_well_ordered[OF Y].
  have XA: "X \<subseteq> A" using derivation_A[OF X].
  have YA: "Y \<subseteq> A" using derivation_A[OF Y].
  from xX yY show ?thesis
  proof (induct x arbitrary: y)
    case (less x)
    note xX = \<open>x \<in> X\<close> and IHx = this(2)
    from xX XA f have xA: "x \<in> A" and fxA: "f x \<in> A" by auto
    from \<open>y \<in> Y\<close>
    show ?case
    proof (induct y)
      case (less y)
      note yY = \<open>y \<in> Y\<close> and IHy = less(2)
      from yY YA f have yA: "y \<in> A" and fyA: "f y \<in> A" by auto
      from X xX show ?case
      proof (cases rule: derivation_cases)
        case (suc Z z)
        note Z = \<open>Z = {z \<in> X. z \<sqsubset> x}\<close> and Zz = \<open>extreme Z (\<sqsubseteq>) z\<close> and xfz = \<open>x = f z\<close>
        then have zx: "z \<sqsubset> x" and zX: "z \<in> X" by auto
        note IHz = IHx[OF zX zx yY]
        have 1: "y \<sqsubset> x \<and> y \<in> X \<or> x \<sqsubseteq> y" using suc_any[OF X Y xX yY Z Zz xfz IHz] IHy by auto
        from Y yY show ?thesis
        proof (cases rule: derivation_cases)
          case (suc W w)
          note W = \<open>W = {w \<in> Y. w \<sqsubset> y}\<close> and Ww = \<open>extreme W (\<sqsubseteq>) w\<close> and yfw = \<open>y = f w\<close> 
          then have wY: "w \<in> Y" and wy: "w \<sqsubset> y" by auto
          have IHw: "w \<sqsubset> x \<and> w \<in> X \<or> w = x  \<or> x \<sqsubset> w \<and> x \<in> Y" using IHy[OF wY wy] by auto
          have "x \<sqsubset> y \<and> x \<in> Y \<or> y \<sqsubseteq> x" using suc_any[OF Y X yY xX W Ww yfw IHw] by auto
          with 1 show ?thesis using antisym xA yA by auto
        next
          case (lim W)
          note W = \<open>W = {w \<in> Y. w \<sqsubset> y}\<close> and fW = \<open>f ` W \<subseteq> W\<close> and Wy = \<open>extreme_bound A (\<sqsubseteq>) W y\<close>
          have "x \<sqsubset> y \<and> x \<in> Y \<or> y \<sqsubseteq> x" using lim_any[OF Y X yY xX W fW Wy] IHy by auto
          with 1 show ?thesis using antisym xA yA by auto
        qed
      next
        case (lim Z)
        note Z = \<open>Z = {z \<in> X. z \<sqsubset> x}\<close> and fZ = \<open>f ` Z \<subseteq> Z\<close> and Zx = \<open>extreme_bound A (\<sqsubseteq>) Z x\<close>
        have 1: "y \<sqsubset> x \<and> y \<in> X \<or> x \<sqsubseteq> y" using lim_any[OF X Y xX yY Z fZ Zx] IHx[OF _ _ yY] by auto
        from Y yY show ?thesis
        proof (cases rule: derivation_cases)
          case (suc W w)
          note W = \<open>W = {w \<in> Y. w \<sqsubset> y}\<close> and Ww = \<open>extreme W (\<sqsubseteq>) w\<close> and yfw = \<open>y = f w\<close>
          then have wY: "w \<in> Y" and wy: "w \<sqsubset> y" by auto
          have IHw: "w \<sqsubset> x \<and> w \<in> X \<or>  w = x  \<or>  x \<sqsubset> w \<and> x \<in> Y" using IHy[OF wY wy] by auto
          have "x \<sqsubset> y \<and> x \<in> Y \<or> y \<sqsubseteq> x" using suc_any[OF Y X yY xX W Ww yfw IHw] by auto
          with 1 show ?thesis using antisym xA yA by auto
        next
          case (lim W)
          note W = \<open>W = {w \<in> Y. w \<sqsubset> y}\<close> and fW = \<open>f ` W \<subseteq> W\<close> and Wy = \<open>extreme_bound A (\<sqsubseteq>) W y\<close>
          have "x \<sqsubset> y \<and> x \<in> Y \<or> y \<sqsubseteq> x" using lim_any[OF Y X yY xX W fW Wy] IHy by auto
          with 1 show ?thesis using antisym xA yA by auto
        qed
      qed
    qed
  qed
qed

interpretation derivable: well_ordered_set "{x. derivable x}" "(\<sqsubseteq>)"
proof (rule well_ordered_set.intro)
  show "antisymmetric {x. derivable x} (\<sqsubseteq>)"
    apply unfold_locales by (auto dest: derivable_A antisym)
  show "well_related_set {x. derivable x} (\<sqsubseteq>)"
  apply (fold UN_derivations_eq_derivable)
  apply (rule closed_UN_well_related)
  by (auto dest: derivation_well_ordered derivations_cross_compare well_ordered_set.axioms)
qed

lemmas derivable_well_ordered = derivable.well_ordered_set_axioms
lemmas derivable_total_ordered = derivable.total_ordered_set_axioms
lemmas derivable_well_related = derivable.well_related_set_axioms

lemma pred_unique:
  assumes X: "derivation X" and xX: "x \<in> X"
  shows "{z \<in> X. z \<sqsubset> x} = {z. derivable z \<and> z \<sqsubset> x}"
proof
  { fix z assume "z \<in> X" and "z \<sqsubset> x"
    then have "derivable z \<and> z \<sqsubset> x" using X by (auto simp: derivable_def)
  }
  then show "{z \<in> X. z \<sqsubset> x} \<subseteq> {z. derivable z \<and> z \<sqsubset> x}" by auto
  { fix z assume "derivable z" and zx: "z \<sqsubset> x"
    then obtain Y where Y: "derivation Y" and zY: "z \<in> Y" by (auto simp: derivable_def)
    then have "z \<in> X" using derivations_cross_compare[OF X Y xX zY] zx by auto
  }
  then show "{z \<in> X. z \<sqsubset> x} \<supseteq> {z. derivable z \<and> z \<sqsubset> x}" by auto
qed

text \<open>The set of all derivable elements is itself a derivation.\<close>

lemma derivation_derivable: "derivation {x. derivable x}"
  apply (unfold derivation_def)
  apply (safe intro!: derivable_A derivable.well_ordered_set_axioms elim!: derivableE)
  apply (unfold mem_Collect_eq pred_unique[symmetric])
  by (auto simp: derivation_def)

text \<open>Finally, if the set of all derivable elements admits a supremum, then it is a fixed point.\<close>

lemma
  assumes p: "extreme_bound A (\<sqsubseteq>) {x. derivable x} p"
  shows sup_derivable_qfp: "f p \<sim> p" and sup_derivable_fp: "f p = p"
proof (intro antisym sympartpI)
  define P where "P \<equiv> {x. derivable x}"
  have pA: "p \<in> A" using p by auto
  have P: "derivation P" using derivation_derivable by (simp add: P_def)
  from derivable_closed have fP: "f ` P \<subseteq> P" by (auto simp: P_def)
  from derivation_lim[OF P fP] p
  have pP: "p \<in> P" by (auto simp: P_def intro:derivableI)
  with fP have "f p \<in> P" by auto
  with p show fpp: "f p \<sqsubseteq> p" by (auto simp: P_def)
  show pfp: "p \<sqsubseteq> f p" apply (rule derivation_infl[rule_format, OF P]) using pP by (auto simp: P_def)
  from fpp pfp p f show "f p = p" by (auto intro!: antisym)
qed

end

text "The assumptions are satisfied by monotone functions."

context
  assumes mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
begin

lemma mono_imp_derivation_infl:
  "\<forall>X x y. derivation X \<longrightarrow> x \<in> X \<longrightarrow> y \<in> X \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> x \<sqsubseteq> f y"
proof (intro allI impI)
  fix X x y
  assume X: "derivation X" and xX: "x \<in> X" and yX: "y \<in> X" and xy: "x \<sqsubseteq> y"
  interpret X: well_ordered_set X "(\<sqsubseteq>)" using derivation_well_ordered[OF X].
  note XA = derivation_A[OF X]
  from xX yX xy show "x \<sqsubseteq> f y"
  proof (induct x)
    case (less x)
    note IH = this(2) and xX = \<open>x \<in> X\<close> and yX = \<open>y \<in> X\<close> and xy = \<open>x \<sqsubseteq> y\<close>
    from xX yX XA have xA: "x \<in> A" and yA: "y \<in> A" by auto
    from X xX show ?case
    proof (cases rule: derivation_cases)
      case (suc Z z)
      then have zX: "z \<in> X" and zsx: "z \<sqsubset> x" and xfz: "x = f z" by auto
      then have zx: "z \<sqsubseteq> x" by auto
      from X.trans[OF zx xy zX xX yX] have zy: "z \<sqsubseteq> y".
      from zX XA have zA: "z \<in> A" by auto
      from zy monotone_onD[OF mono] zA yA xfz show "x \<sqsubseteq> f y" by auto
    next
      case (lim Z)
      note Z = \<open>Z = {z \<in> X. z \<sqsubset> x}\<close> and Zx = \<open>extreme_bound A (\<sqsubseteq>) Z x\<close>
      from f yA have fyA: "f y \<in> A" by auto
      have "bound Z (\<sqsubseteq>) (f y)"
      proof
        fix z assume zZ: "z \<in> Z"
        with Z xX have zsx: "z \<sqsubset> x" and zX: "z \<in> X" by auto
        then have zx: "z \<sqsubseteq> x" by auto
        from X.trans[OF zx xy zX xX yX] have zy: "z \<sqsubseteq> y".
        from IH[OF zX zsx yX] zy show "z \<sqsubseteq> f y" by auto
      qed
      with Zx fyA show ?thesis by auto
    qed
  qed
qed

lemma mono_imp_derivation_f_refl:
  "\<forall>X x. derivation X \<longrightarrow> x \<in> X \<longrightarrow> f x \<sqsubseteq> f x"
proof (intro allI impI)
  fix X x
  assume X: "derivation X" and xX: "x \<in> X"
  interpret X: well_ordered_set X "(\<sqsubseteq>)" using derivation_well_ordered[OF X].
  note XA = derivation_A[OF X]
  from xX have "x \<sqsubseteq> x" by auto
  from monotone_onD[OF mono this] xX XA show "f x \<sqsubseteq> f x" by auto
qed

corollary mono_imp_sup_derivable_fp:
  assumes p: "extreme_bound A (\<sqsubseteq>) {x. derivable x} p"
  shows "f p = p"
  by (simp add: sup_derivable_fp[OF mono_imp_derivation_infl mono_imp_derivation_f_refl p])

lemma mono_imp_sup_derivable_lfp:
  assumes p: "extreme_bound A (\<sqsubseteq>) {x. derivable x} p"
  shows "extreme {q \<in> A. f q = q} (\<sqsupseteq>) p"
proof (safe intro!: extremeI)
  from p show "p \<in> A" by auto
  from sup_derivable_fp[OF mono_imp_derivation_infl mono_imp_derivation_f_refl p]
  show "f p = p".
  fix q assume qA: "q \<in> A" and fqq: "f q = q"
  have "bound {x. derivable x} (\<sqsubseteq>) q"
  proof (safe intro!: boundI elim!:derivableE)
    fix x X
    assume X: "derivation X" and xX: "x \<in> X"
    from X interpret well_ordered_set X "(\<sqsubseteq>)" by (rule derivation_well_ordered)
    from xX show "x \<sqsubseteq> q"
    proof (induct x)
      case (less x)
      note xP = this(1) and IH = this(2)
      with X show ?case
      proof (cases rule: derivation_cases)
        case (suc Z z)
        with IH[of z] have zq: "z \<sqsubseteq> q" and zX: "z \<in> X" by auto
        from monotone_onD[OF mono zq] zX qA derivation_A[OF X]
        show ?thesis by (auto simp: fqq suc)
      next
        case lim
        with IH have "bound {z \<in> X. z \<sqsubset> x} (\<sqsubseteq>) q" by auto
        with lim qA show ?thesis by auto
      qed
    qed
  qed
  with p qA show "p \<sqsubseteq> q" by auto
qed

lemma mono_imp_ex_least_fp:
  assumes comp: "well_complete A (\<sqsubseteq>)"
  shows "\<exists>p. extreme {q \<in> A. f q = q} (\<sqsupseteq>) p"
proof-
  interpret fixed_point_proof using f by unfold_locales
  note as = antisymmetric_axioms
  note infl = mono_imp_derivation_infl
  note refl = mono_imp_derivation_f_refl
  have wr: "well_related_set {x. derivable x} (\<sqsubseteq>)"
    using derivable_well_related[OF infl refl].
  have "\<exists>p. extreme_bound A (\<sqsubseteq>) {x. derivable x} p"
    apply (rule completeD[OF comp])
    using derivable_A wr by auto
  then obtain p where p: "extreme_bound A (\<sqsubseteq>) {x. derivable x} p" by auto
  from p mono_imp_sup_derivable_lfp[OF p] sup_derivable_qfp[OF infl refl p]
  show ?thesis by auto
qed

end

end

end

text \<open>Bourbaki-Witt Theorem on well-complete pseudo-ordered set:\<close>
theorem (in pseudo_ordered_set) well_complete_infl_imp_ex_fp:
  assumes comp: "well_complete A (\<sqsubseteq>)"
    and f: "f ` A \<subseteq> A" and infl: "\<forall>x \<in> A. \<forall>y \<in> A. x \<sqsubseteq> y \<longrightarrow> x \<sqsubseteq> f y"
  shows "\<exists>p \<in> A. f p = p"
proof-
  note as = antisymmetric_axioms
  interpret fixed_point_proof using f by unfold_locales
  have dinfl: "\<forall>X x y. derivation X \<longrightarrow> x \<in> X \<longrightarrow> y \<in> X \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> x \<sqsubseteq> f y"
    using infl by (auto dest!:derivation_A)
  have drefl: "\<forall>X x. derivation X \<longrightarrow> x \<in> X \<longrightarrow> f x \<sqsubseteq> f x" using f by (auto dest!: derivation_A)
  have "\<exists>p. extreme_bound A (\<sqsubseteq>) {x. derivable x} p"
    apply (rule completeD[OF comp])
    using derivable_well_related[OF as dinfl drefl] derivable_A by auto
  with sup_derivable_fp[OF as dinfl drefl]
  show ?thesis by auto
qed


section \<open>Completeness of (Quasi-)Fixed Points\<close>

text \<open>We now prove that, under attractivity, the set of quasi-fixed points is complete.\<close>

definition setwise where "setwise r X Y \<equiv> \<forall>x\<in>X. \<forall>y\<in>Y. r x y"

lemmas setwiseI[intro] = setwise_def[unfolded atomize_eq, THEN iffD2, rule_format]
lemmas setwiseE[elim] = setwise_def[unfolded atomize_eq, THEN iffD1, elim_format, rule_format]

context fixed_point_proof begin

abbreviation setwise_less_eq (infix "\<sqsubseteq>\<^sup>s" 50) where "(\<sqsubseteq>\<^sup>s) \<equiv> setwise (\<sqsubseteq>)"

subsection \<open>Least Quasi-Fixed Points for Attractive Relations.\<close>

lemma attract_mono_imp_least_qfp:
  assumes attract: "attractive A (\<sqsubseteq>)"
    and comp: "well_complete A (\<sqsubseteq>)"
    and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "\<exists>c. extreme {p \<in> A. f p \<sim> p \<or> f p = p} (\<sqsupseteq>) c \<and> f c \<sim> c"
proof-
  interpret attractive using attract by auto
  interpret sym: transitive A "(\<sim>)" using sym_transitive.
  define ecl ("[_]\<^sub>\<sim>") where "[x]\<^sub>\<sim> \<equiv> {y \<in> A. x \<sim> y} \<union> {x}" for x
  define Q where "Q \<equiv> {[x]\<^sub>\<sim> |. x \<in> A}"
  { fix X x assume XQ: "X \<in> Q" and xX: "x \<in> X"
    then have XA: "X \<subseteq> A" by (auto simp: Q_def ecl_def)
    then have xA: "x \<in> A" using xX by auto
    obtain q where qA: "q \<in> A" and X: "X = [q]\<^sub>\<sim>" using XQ by (auto simp: Q_def)
    have xqqx: "x \<sim> q \<or> x = q" using X xX by (auto simp: ecl_def)
    {fix y assume yX: "y \<in> X"
      then have yA: "y \<in> A" using XA by auto
      have "y \<sim> q \<or> y = q" using yX X by (auto simp: ecl_def)
      then have "x \<sim> y \<or> y = x" using sym_order_trans xqqx xA qA yA by blast
    }
    then have 1: "X \<subseteq> [x]\<^sub>\<sim>" using X qA by (auto simp: ecl_def)
    { fix y assume "y \<in> A" and "x \<sim> y \<or> y = x"
      then have "q \<sim> y \<or> y = q" using sym_order_trans xqqx xA qA by blast
    }
    then have 2: "X \<supseteq> [x]\<^sub>\<sim>" using X xX by (auto simp: ecl_def)
    from 1 2 have "X = [x]\<^sub>\<sim>" by auto
  }
  then have XQx: "\<forall>X \<in> Q. \<forall>x \<in> X. X = [x]\<^sub>\<sim>" by auto
  have RSLE_eq: "X \<in> Q \<Longrightarrow> Y \<in> Q \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> X \<sqsubseteq>\<^sup>s Y" for X Y x y
  proof-
    assume XQ: "X \<in> Q" and YQ: "Y \<in> Q" and xX: "x \<in> X" and yY: "y \<in> Y" and xy: "x \<sqsubseteq> y"
    then have XA: "X \<subseteq> A" and YA: "Y \<subseteq> A" by (auto simp: Q_def ecl_def)
    then have xA: "x \<in> A" and yA: "y \<in> A" using xX yY by auto
    { fix xp yp assume xpX: "xp \<in> X" and ypY: "yp \<in> Y"
      then have xpA: "xp \<in> A" and ypA: "yp \<in> A" using XA YA by auto
      then have "xp \<sim> x \<or> xp = x" using xpX XQx xX XQ by (auto simp: ecl_def)
      then have xpy: "xp \<sqsubseteq> y" using attract[OF _ _ xy xpA xA yA] xy by blast
      have "yp \<sim> y \<or> yp = y" using ypY XQx yY YQ by (auto simp: ecl_def)
      then have "xp \<sqsubseteq> yp" using dual.attract[OF _ _ xpy ypA yA xpA] xpy by blast
    }
    then show "X \<sqsubseteq>\<^sup>s Y" using XQ YQ XA YA by auto
  qed
  have compQ: "well_complete Q (\<sqsubseteq>\<^sup>s)"
  proof (intro completeI, safe)
    fix XX assume XXQ: "XX \<subseteq> Q" and XX: "well_related_set XX (\<sqsubseteq>\<^sup>s)"
    have BA: "\<Union>XX \<subseteq> A" using XXQ by (auto simp: Q_def ecl_def)
    from XX interpret XX: well_related_set XX "(\<sqsubseteq>\<^sup>s)".
    interpret UXX: semiattractive "\<Union>XX" "(\<sqsubseteq>)" by (rule semiattractive_subset[OF BA])
    have "well_related_set (\<Union>XX) (\<sqsubseteq>)"
    proof(unfold_locales)
      fix Y assume YXX: "Y \<subseteq> \<Union>XX" and Y0: "Y \<noteq> {}"
      have "{X \<in> XX. X \<inter> Y \<noteq> {}} \<noteq> {}" using YXX Y0 by auto
      from XX.nonempty_imp_ex_extreme[OF _ this]
      obtain E where E: "extreme {X \<in> XX. X \<inter> Y \<noteq> {}} (\<sqsubseteq>\<^sup>s)\<^sup>- E" by auto
      then have "E \<inter> Y \<noteq> {}" by auto
      then obtain e where eE: "e \<in> E" and eX: "e \<in> Y" by auto
      have "extreme Y (\<sqsupseteq>) e"
      proof (intro extremeI eX)
        fix x assume xY: "x \<in> Y"
        with YXX obtain X where XXX: "X \<in> XX" and xX: "x \<in> X" by auto
        with xY E XXX have "E \<sqsubseteq>\<^sup>s X" by auto
        with eE xX show "e \<sqsubseteq> x" by auto
      qed
      then show "\<exists>e. extreme Y (\<sqsupseteq>) e" by auto
    qed
    with completeD[OF comp BA]
    obtain b where extb: "extreme_bound A (\<sqsubseteq>) (\<Union>XX) b" by auto
    then have bb: "b \<sqsubseteq> b" using extreme_def bound_def by auto
    have bA: "b \<in> A" using extb extreme_def by auto
    then have XQ: "[b]\<^sub>\<sim> \<in> Q" using Q_def bA by auto
    have bX: "b \<in> [b]\<^sub>\<sim>" by (auto simp: ecl_def)
    have "extreme_bound Q (\<sqsubseteq>\<^sup>s) XX [b]\<^sub>\<sim>"
    proof(intro extreme_boundI)
      show "[b]\<^sub>\<sim> \<in> Q" using XQ.
    next
      fix Y assume YXX: "Y \<in> XX"
      then have YQ: "Y \<in> Q" using XXQ by auto
      then obtain y where yA: "y \<in> A" and Yy: "Y = [y]\<^sub>\<sim>" by (auto simp: Q_def)
      then have yY: "y \<in> Y" by (auto simp: ecl_def)
      then have "y \<in> \<Union>XX" using yY YXX by auto
      then have "y \<sqsubseteq> b" using extb by auto
      then show "Y \<sqsubseteq>\<^sup>s [b]\<^sub>\<sim>" using RSLE_eq[OF YQ XQ yY bX] by auto
    next
      fix Z assume boundZ: "bound XX (\<sqsubseteq>\<^sup>s) Z" and ZQ: "Z \<in> Q"
      then obtain z where zA: "z \<in> A" and Zz: "Z = [z]\<^sub>\<sim>" by (auto simp: Q_def)
      then have zZ: "z \<in> Z" by (auto simp: ecl_def)
      { fix y assume "y \<in> \<Union>XX"
        then obtain Y where yY: "y \<in> Y" and YXX: "Y \<in> XX" by auto
        then have YA: "Y \<subseteq> A" using XXQ Q_def by (auto simp: ecl_def)
        then have "Y \<sqsubseteq>\<^sup>s Z" using YXX boundZ bound_def by auto
        then have "y \<sqsubseteq> z" using yY zZ by auto
      }
      then have "bound (\<Union>XX) (\<sqsubseteq>) z" by auto
      then have "b \<sqsubseteq> z" using extb zA by auto
      then show "[b]\<^sub>\<sim> \<sqsubseteq>\<^sup>s Z" using RSLE_eq[OF XQ ZQ bX zZ] by auto
    qed
    then show "Ex (extreme_bound Q (\<sqsubseteq>\<^sup>s) XX)" by auto
  qed
  interpret Q: antisymmetric Q "(\<sqsubseteq>\<^sup>s)"
  proof
    fix X Y assume XY: "X \<sqsubseteq>\<^sup>s Y" and YX: "Y \<sqsubseteq>\<^sup>s X" and XQ: "X \<in> Q" and YQ: "Y \<in> Q"
    then obtain q where qA: "q \<in> A" and X: "X = [q]\<^sub>\<sim>" using Q_def by auto
    then have qX: "q \<in> X" using X by (auto simp: ecl_def)
    then obtain p where pA: "p \<in> A" and Y: "Y = [p]\<^sub>\<sim>" using YQ Q_def by auto
    then have pY: "p \<in> Y" using X by (auto simp: ecl_def)
    have pq: "p \<sqsubseteq> q" using  XQ YQ YX qX pY by auto
    have "q \<sqsubseteq> p" using XQ YQ XY qX pY by auto
    then have "p \<in> X" using pq X pA by (auto simp: ecl_def)
    then have "X = [p]\<^sub>\<sim>" using XQ XQx by auto
    then show "X = Y" using Y by (auto simp: ecl_def)
  qed
  define F where "F X \<equiv> {y \<in> A. \<exists>x \<in> X. y \<sim> f x} \<union> f ` X" for X
  have XQFXQ: "\<And>X. X \<in> Q \<Longrightarrow> F X \<in> Q"
  proof-
    fix X assume XQ: "X \<in> Q"
    then obtain x where xA: "x \<in> A" and X: "X = [x]\<^sub>\<sim>" using Q_def by auto
    then have xX: "x \<in> X" by (auto simp: ecl_def)
    have fxA: "f x \<in> A" using xA f by auto
    have FXA: "F X \<subseteq> A" using f fxA X by (auto simp: F_def ecl_def)
    have "F X = [f x]\<^sub>\<sim>"
    proof (unfold X, intro equalityI subsetI)
      fix z assume zFX: "z \<in> F [x]\<^sub>\<sim>"
      then obtain y where yX: "y \<in> [x]\<^sub>\<sim>" and zfy: "z \<sim> f y \<or> z = f y" by (auto simp: F_def)
      have yA: "y \<in> A" using yX xA by (auto simp: ecl_def)
      with f have fyA: "f y \<in> A" by auto
      have zA: "z \<in> A" using zFX FXA by (auto simp: X)
      have "y \<sim> x \<or> y = x" using X yX by (auto simp: ecl_def)
      then have "f y \<sim> f x \<or> f y = f x" using mono xA yA by (auto simp: monotone_on_def)
      then have "z \<sim> f x \<or> z = f x" using zfy sym.trans[OF _ _ zA fyA fxA] by (auto simp:)
      with zA show "z \<in> [f x]\<^sub>\<sim>" by (auto simp: ecl_def)
    qed (auto simp: xX F_def ecl_def)
    with FXA show "F X \<in> Q" by (auto simp: Q_def ecl_def)
  qed
  then have F: "F ` Q \<subseteq> Q" by auto
  then interpret Q: fixed_point_proof Q "(\<sqsubseteq>\<^sup>s)" F by unfold_locales
  have monoQ: "monotone_on Q (\<sqsubseteq>\<^sup>s) (\<sqsubseteq>\<^sup>s) F" 
  proof (intro monotone_onI)
    fix X Y assume XQ: "X \<in> Q" and YQ: "Y \<in> Q" and XY: "X \<sqsubseteq>\<^sup>s Y"
    then obtain x y where xX: "x \<in> X" and yY: "y \<in> Y" using Q_def by (auto simp: ecl_def)
    then have xA: "x \<in> A" and yA: "y \<in> A" using XQ YQ by (auto simp: Q_def ecl_def)
    have "x \<sqsubseteq> y" using XY xX yY by auto
    then have fxfy: "f x \<sqsubseteq> f y" using monotone_on_def[of A "(\<sqsubseteq>)" "(\<sqsubseteq>)" f] xA yA mono by auto
    have fxgX: "f x \<in> F X" using xX F_def by blast
    have fygY: "f y \<in> F Y" using yY F_def by blast
    show "F X \<sqsubseteq>\<^sup>s F Y" using RSLE_eq[OF XQFXQ[OF XQ] XQFXQ[OF YQ] fxgX fygY fxfy].
  qed
  have QdA: "{x. Q.derivable x} \<subseteq> Q" using Q.derivable_A by auto
  note asQ = Q.antisymmetric_axioms
  note infl = Q.mono_imp_derivation_infl[OF asQ monoQ]
  note f_refl = Q.mono_imp_derivation_f_refl[OF asQ monoQ]
  from Q.mono_imp_ex_least_fp[OF asQ monoQ compQ]
  obtain P where P: "extreme {q \<in> Q. F q = q} (\<sqsubseteq>\<^sup>s)\<^sup>- P" by auto
  then have PQ: "P \<in> Q" by (auto simp: extreme_def)
  from P have FPP: "F P = P" using PQ by auto
  with P have PP: "P \<sqsubseteq>\<^sup>s P" by auto
  from P obtain p where pA: "p \<in> A" and Pp: "P = [p]\<^sub>\<sim>" using Q_def by auto
  then have pP: "p \<in> P" by (auto simp: ecl_def)
  then have fpA: "f p \<in> A" using pA f by auto
  have "f p \<in> F P" using pP F_def fpA by auto
  then have "F P = [f p]\<^sub>\<sim>" using XQx XQFXQ[OF PQ] by auto
  then have fp: "f p \<sim> p \<or> f p = p" using pP FPP by (auto simp: ecl_def)
  have "p \<sqsubseteq> p" using PP pP by auto
  with fp have fpp: "f p \<sim> p" by auto
  have e: "extreme {p \<in> A. f p \<sim> p \<or> f p = p} (\<sqsupseteq>) p"
  proof (intro extremeI CollectI conjI pA fp, elim CollectE conjE)
    fix q assume qA: "q \<in> A" and fq: "f q \<sim> q \<or> f q = q"
    define Z where "Z \<equiv> {z \<in> A. q \<sim> z}\<union>{q}"
    then have qZ: "q \<in> Z" using qA by auto
    then have ZQ: "Z \<in> Q" using qA by (auto simp: Z_def Q_def ecl_def)
    have fqA: "f q \<in> A" using qA f by auto
    then have "f q \<in> Z" using fq by (auto simp: Z_def)
    then have 1: "Z = [f q]\<^sub>\<sim>" using XQx ZQ by auto
    then have "f q \<in> F Z" using qZ fqA by (auto simp: F_def)
    then have "F Z = [f q]\<^sub>\<sim>" using XQx XQFXQ[OF ZQ] by auto
    with 1 have "Z = F Z" by auto
    then have "P \<sqsubseteq>\<^sup>s Z" using P ZQ by auto
    then show "p \<sqsubseteq> q" using pP qZ by auto
  qed
  with fpp show ?thesis using e by auto
qed

subsection \<open>General Completeness\<close>

lemma attract_mono_imp_fp_qfp_complete:
  assumes attract: "attractive A (\<sqsubseteq>)"
    and comp: "CC-complete A (\<sqsubseteq>)"
    and wr_CC: "\<forall>C \<subseteq> A. well_related_set C (\<sqsubseteq>) \<longrightarrow> C \<in> CC"
    and extend: "\<forall>X \<in> CC. \<forall>Y \<in> CC. X \<sqsubseteq>\<^sup>s Y \<longrightarrow> X \<union> Y \<in> CC"
    and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
    and P: "P \<subseteq> {x \<in> A. f x = x}"
  shows "CC-complete ({q \<in> A. f q \<sim> q} \<union> P) (\<sqsubseteq>)"
proof (intro completeI)
  interpret attractive using attract.
  fix X assume Xfix: "X \<subseteq> {q \<in> A. f q \<sim> q} \<union> P" and XCC: "X \<in> CC"
  with P have XA: "X \<subseteq> A" by auto
  define B where "B \<equiv> {b \<in> A. \<forall>a \<in> X. a \<sqsubseteq> b}"
  { fix s a assume sA: "s \<in> A" and as: "\<forall>a \<in> X. a \<sqsubseteq> s" and aX: "a \<in> X"
    then have aA: "a \<in> A" using XA by auto
    then have fafs: "f a \<sqsubseteq> f s" using mono f aX sA as by (auto elim!: monotone_onE)
    have "a \<sqsubseteq> f s"
    proof (cases "f a = a")
      case True
      then show ?thesis using fafs by auto
    next
      case False
      then have "a \<sim> f a" using P aX Xfix by auto
      also from fafs have "f a \<sqsubseteq> f s" by auto
      finally show ?thesis using f aA sA by auto
    qed
  }
  with f have fBB: "f ` B \<subseteq> B" unfolding B_def by auto
  have BA: "B \<subseteq> A" by (auto simp: B_def)
  have compB: "CC-complete B (\<sqsubseteq>)"
  proof (unfold complete_def, intro allI impI)
    fix Y assume YS: "Y \<subseteq> B" and YCC: "Y \<in> CC"
    with BA have YA: "Y \<subseteq> A" by auto
    define C where "C \<equiv> X\<union>Y"
    then have CA: "C \<subseteq> A" using XA YA C_def by auto
    have XY: "X \<sqsubseteq>\<^sup>s Y" using B_def YS by auto
    then have CCC: "C \<in> CC" using extend XA YA XCC YCC C_def by auto
    then obtain s where s: "extreme_bound A (\<sqsubseteq>) C s"
      using completeD[OF comp CA CCC] by auto
    then have sA: "s \<in> A" by auto
    show "Ex (extreme_bound B (\<sqsubseteq>) Y)"
    proof (intro exI extreme_boundI)
      { fix x assume "x \<in> X"
        then have "x \<sqsubseteq> s" using s C_def by auto
      }
      then show "s \<in> B" using sA B_def by auto
    next
      fix y assume "y \<in> Y"
      then show "y \<sqsubseteq> s" using s C_def using extremeD by auto
    next
      fix c assume cS: "c \<in> B" and "bound Y (\<sqsubseteq>) c"
      then have "bound C (\<sqsubseteq>) c" using C_def B_def by auto
      then show "s \<sqsubseteq> c" using s BA cS by auto
    qed
  qed
  from fBB interpret B: fixed_point_proof B "(\<sqsubseteq>)" f by unfold_locales
  from BA have *: "{x \<in> A. f x \<sim> x} \<inter> B = {x \<in> B. f x \<sim> x}" by auto
  have asB: "attractive B (\<sqsubseteq>)" using attractive_subset[OF BA] by auto
  have monoB: "monotone_on B (\<sqsubseteq>) (\<sqsubseteq>) f" using monotone_on_cmono[OF BA] mono by (auto dest!: le_funD)
  have compB: "well_complete B (\<sqsubseteq>)"
    using wr_CC compB BA by (simp add: complete_def) 
  from B.attract_mono_imp_least_qfp[OF asB compB monoB]
  obtain l where "extreme {p \<in> B. f p \<sim> p \<or> f p = p} (\<sqsupseteq>) l" and fll: "f l \<sim> l" by auto
  with P have l: "extreme ({p \<in> B. f p \<sim> p} \<union> P \<inter> B) (\<sqsupseteq>) l" by auto
  show "Ex (extreme_bound ({q \<in> A. f q \<sim> q} \<union> P) (\<sqsubseteq>) X)"
  proof (intro exI extreme_boundI)
    show "l \<in> {q \<in> A. f q \<sim> q} \<union> P" using l BA by auto
    fix a assume "a \<in> X"
    with l show "a \<sqsubseteq> l" by (auto simp: B_def)
  next
    fix c assume c: "bound X (\<sqsubseteq>) c" and cfix: "c \<in> {q \<in> A. f q \<sim> q} \<union> P"
    with P have cA: "c \<in> A" by auto
    with c have "c \<in> B" by (auto simp: B_def)
    with cfix l show "l \<sqsubseteq> c" by auto
  qed
qed

lemma attract_mono_imp_qfp_complete:
  assumes "attractive A (\<sqsubseteq>)"
    and "CC-complete A (\<sqsubseteq>)"
    and "\<forall>C \<subseteq> A. well_related_set C (\<sqsubseteq>) \<longrightarrow> C \<in> CC"
    and "\<forall>X \<in> CC. \<forall>Y \<in> CC. X \<sqsubseteq>\<^sup>s Y \<longrightarrow> X \<union> Y \<in> CC"
    and "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "CC-complete {p \<in> A. f p \<sim> p} (\<sqsubseteq>)"
  using attract_mono_imp_fp_qfp_complete[OF assms, of "{}"] by simp

lemma antisym_mono_imp_fp_complete:
  assumes anti: "antisymmetric A (\<sqsubseteq>)"
    and comp: "CC-complete A (\<sqsubseteq>)"
    and wr_CC: "\<forall>C \<subseteq> A. well_related_set C (\<sqsubseteq>) \<longrightarrow> C \<in> CC"
    and extend: "\<forall>X \<in> CC. \<forall>Y \<in> CC. X \<sqsubseteq>\<^sup>s Y \<longrightarrow> X \<union> Y \<in> CC"
    and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "CC-complete {p \<in> A. f p = p} (\<sqsubseteq>)"
proof-
  interpret antisymmetric using anti.
  have *: "{q \<in> A. f q \<sim> q} \<subseteq> {p \<in> A. f p = p}" using f by (auto intro!: antisym)
  from * attract_mono_imp_fp_qfp_complete[OF attractive_axioms comp wr_CC extend mono, of "{p\<in>A. f p = p}"]
  show ?thesis by (auto simp: subset_Un_eq)
qed

end

subsection \<open>Instances\<close>

subsubsection \<open>Instances under attractivity\<close>

context attractive begin

interpretation less_eq_notations.

text \<open>Full completeness\<close>
theorem mono_imp_qfp_UNIV_complete:
  assumes comp: "UNIV-complete A (\<sqsubseteq>)" and f: "f ` A \<subseteq> A" and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "UNIV-complete {p \<in> A. f p \<sim> p} (\<sqsubseteq>)"
  apply (intro fixed_point_proof.attract_mono_imp_qfp_complete comp mono)
    apply unfold_locales
  by (auto simp: f)

text \<open>Connex completeness\<close>
theorem mono_imp_qfp_connex_complete:
  assumes comp: "{X. connex X (\<sqsubseteq>)}-complete A (\<sqsubseteq>)"
    and f: "f ` A \<subseteq> A" and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "{X. connex X (\<sqsubseteq>)}-complete {p \<in> A. f p \<sim> p} (\<sqsubseteq>)"
  apply (intro fixed_point_proof.attract_mono_imp_qfp_complete mono comp)
    apply unfold_locales
  by (auto simp: f intro: connex_union well_related_set.connex_axioms)

text \<open>Directed completeness\<close>
theorem mono_imp_qfp_directed_complete:
  assumes comp: "{X. directed X (\<sqsubseteq>)}-complete A (\<sqsubseteq>)"
    and f: "f ` A \<subseteq> A" and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "{X. directed X (\<sqsubseteq>)}-complete {p \<in> A. f p \<sim> p} (\<sqsubseteq>)"
  apply (intro fixed_point_proof.attract_mono_imp_qfp_complete mono comp)
    apply unfold_locales
  by (auto simp: f intro!: directed_extend intro: well_related_set.connex_axioms connex.directed)

text \<open>Well Completeness\<close>
theorem mono_imp_qfp_well_complete:
  assumes comp: "well_complete A (\<sqsubseteq>)"
    and f: "f ` A \<subseteq> A" and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "well_complete {p \<in> A. f p \<sim> p} (\<sqsubseteq>)"
  apply (intro fixed_point_proof.attract_mono_imp_qfp_complete mono comp)
    apply unfold_locales
  by (auto simp: f well_related_extend)

end

subsubsection \<open>Usual instances under antisymmetry \<close>

context antisymmetric begin

text \<open>Knaster--Tarski\<close>
theorem mono_imp_fp_complete:
  assumes comp: "UNIV-complete A (\<sqsubseteq>)"
    and f: "f ` A \<subseteq> A" and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "UNIV-complete {p \<in> A. f p = p} (\<sqsubseteq>)"
proof-
  interpret fixed_point_proof using f by unfold_locales
  show ?thesis
    apply (intro antisym_mono_imp_fp_complete mono antisymmetric_axioms comp)
    by auto
qed

text \<open>Markowsky 1976\<close>
theorem mono_imp_fp_connex_complete:
  assumes comp: "{X. connex X (\<sqsubseteq>)}-complete A (\<sqsubseteq>)"
    and f: "f ` A \<subseteq> A" and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "{X. connex X (\<sqsubseteq>)}-complete {p \<in> A. f p = p} (\<sqsubseteq>)"
proof-
  interpret fixed_point_proof using f by unfold_locales
  show ?thesis
    apply (intro antisym_mono_imp_fp_complete antisymmetric_axioms mono comp)
    by (auto intro: connex_union well_related_set.connex_axioms)
qed

text \<open>Pataraia\<close>
theorem mono_imp_fp_directed_complete:
  assumes comp: "{X. directed X (\<sqsubseteq>)}-complete A (\<sqsubseteq>)"
    and f: "f ` A \<subseteq> A" and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "{X. directed X (\<sqsubseteq>)}-complete {p \<in> A. f p = p} (\<sqsubseteq>)"
proof-
  interpret fixed_point_proof using f by unfold_locales
  show ?thesis
    apply (intro antisym_mono_imp_fp_complete mono antisymmetric_axioms comp)
     by (auto intro: directed_extend connex.directed well_related_set.connex_axioms)
qed

text \<open>Bhatta \& George 2011\<close>
theorem mono_imp_fp_well_complete:
  assumes comp: "well_complete A (\<sqsubseteq>)"
    and f: "f ` A \<subseteq> A" and mono: "monotone_on A (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "well_complete {p \<in> A. f p = p} (\<sqsubseteq>)"
proof-
  interpret fixed_point_proof using f by unfold_locales
  show ?thesis
    apply (intro antisym_mono_imp_fp_complete mono antisymmetric_axioms comp)
    by (auto intro!: antisym well_related_extend)
qed

end

end
