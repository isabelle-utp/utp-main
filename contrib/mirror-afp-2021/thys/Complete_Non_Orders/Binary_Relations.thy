(*
Author:  Akihisa Yamada (2018-2021)
License: LGPL (see file COPYING.LESSER)
*)
section \<open>Binary Relations\<close>

text \<open>We start with basic properties of binary relations.\<close>

theory Binary_Relations
  imports
(* To verify that we don't use the axiom of choice, import
    HOL.Complete_Partial_Order HOL.Wellfounded
   instead of *) Main
begin

lemma conj_imp_eq_imp_imp: "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)"
  by standard simp_all

lemma tranclp_trancl: "r\<^sup>+\<^sup>+ = (\<lambda>x y. (x,y) \<in> {(a,b). r a b}\<^sup>+)"
  by (auto simp: tranclp_trancl_eq[symmetric])

lemma tranclp_id[simp]: "transp r \<Longrightarrow> tranclp r = r"
  using trancl_id[of "{(x,y). r x y}", folded transp_trans] by (auto simp:tranclp_trancl)

lemma transp_tranclp[simp]: "transp (tranclp r)" by (auto simp: tranclp_trancl transp_trans)

lemma funpow_dom: "f ` A \<subseteq> A \<Longrightarrow> (f^^n) ` A \<subseteq> A" by (induct n, auto)

text \<open>Below we introduce an Isabelle-notation for $\{ \ldots x\ldots \mid x \in X \}$.\<close>

syntax
  "_range" :: "'a \<Rightarrow> idts \<Rightarrow> 'a set" ("(1{_ /|./ _})")
  "_image" :: "'a \<Rightarrow> pttrn \<Rightarrow> 'a set \<Rightarrow> 'a set"  ("(1{_ /|./ (_/ \<in> _)})")
translations
  "{e |. p}" \<rightleftharpoons> "{e | p. CONST True}"
  "{e |. p \<in> A}" \<rightleftharpoons> "CONST image (\<lambda>p. e) A"

lemma image_constant:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i = y"
  shows "f ` I = (if I = {} then {} else {y})"
  using assms by auto


subsection \<open>Various Definitions\<close>

text \<open>Here we introduce various definitions for binary relations.
The first one is our abbreviation for the dual of a relation.\<close>

abbreviation(input) dual ("(_\<^sup>-)" [1000] 1000) where "r\<^sup>- x y \<equiv> r y x"

lemma conversep_is_dual[simp]: "conversep = dual" by auto

text \<open>Monotonicity is already defined in the library, but we want one restricted to a domain.\<close>

definition "monotone_on X r s f \<equiv> \<forall>x y. x \<in> X \<longrightarrow> y \<in> X \<longrightarrow> r x y \<longrightarrow> s (f x) (f y)"

lemmas monotone_onI = monotone_on_def[unfolded atomize_eq, THEN iffD2, rule_format]
lemma monotone_onD: "monotone_on X r s f \<Longrightarrow> r x y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> s (f x) (f y)"
  by (auto simp: monotone_on_def)

lemmas monotone_onE = monotone_on_def[unfolded atomize_eq, THEN iffD1, elim_format, rule_format]

lemma monotone_on_UNIV[simp]: "monotone_on UNIV = monotone"
  by (intro ext, auto simp: monotone_on_def monotone_def)

lemma monotone_on_dual: "monotone_on X r s f \<Longrightarrow> monotone_on X r\<^sup>- s\<^sup>- f"
  by (auto simp: monotone_on_def)

lemma monotone_on_id: "monotone_on X r r id"
  by (auto simp: monotone_on_def)

lemma monotone_on_cmono: "A \<subseteq> B \<Longrightarrow> monotone_on B \<le> monotone_on A"
   by (intro le_funI, auto simp: monotone_on_def)

text \<open>Here we define the following notions in a standard manner\<close>

text \<open>The symmetric part of a relation:\<close>

definition sympartp where "sympartp r x y \<equiv> r x y \<and> r y x"

lemma sympartpI[intro]:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes "x \<sqsubseteq> y" and "y \<sqsubseteq> x" shows "sympartp (\<sqsubseteq>) x y"
  using assms by (auto simp: sympartp_def)

lemma sympartpE[elim]:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes "sympartp (\<sqsubseteq>) x y" and "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: sympartp_def)

lemma sympartp_dual: "sympartp r\<^sup>- = sympartp r"
  by (auto intro!:ext simp: sympartp_def)

lemma sympartp_eq[simp]: "sympartp (=) = (=)" by auto

lemma reflclp_sympartp[simp]: "(sympartp r)\<^sup>=\<^sup>= = sympartp r\<^sup>=\<^sup>=" by auto

definition "equivpartp r x y \<equiv> x = y \<or> r x y \<and> r y x"

lemma sympartp_reflclp_equivp[simp]: "sympartp r\<^sup>=\<^sup>= = equivpartp r" by (auto intro!:ext simp: equivpartp_def)

lemma equivpartI[simp]: "equivpartp r x x"
  and sympartp_equivpartpI: "sympartp r x y \<Longrightarrow> equivpartp r x y"
  and equivpartpCI[intro]: "(x \<noteq> y \<Longrightarrow> sympartp r x y) \<Longrightarrow> equivpartp r x y"
  by (auto simp:equivpartp_def)

lemma equivpartpE[elim]:
  assumes "equivpartp r x y"
    and "x = y \<Longrightarrow> thesis"
    and "r x y \<Longrightarrow> r y x \<Longrightarrow> thesis"
  shows "thesis"
  using assms by (auto simp: equivpartp_def)

lemma equivpartp_eq[simp]: "equivpartp (=) = (=)" by auto

lemma sympartp_equivpartp[simp]: "sympartp (equivpartp r) = (equivpartp r)"
  and equivpartp_equivpartp[simp]: "equivpartp (equivpartp r) = (equivpartp r)"
  and equivpartp_sympartp[simp]: "equivpartp (sympartp r) = (equivpartp r)"
  by (auto 0 5 intro!:ext)

lemma equivpartp_dual: "equivpartp r\<^sup>- = equivpartp r"
  by (auto intro!:ext simp: equivpartp_def)

text \<open>The asymmetric part:\<close>

definition "asympartp r x y \<equiv> r x y \<and> \<not> r y x"

lemma asympartpE[elim]:
  fixes r (infix "\<sqsubseteq>" 50)
  shows "asympartp (\<sqsubseteq>) x y \<Longrightarrow> (x \<sqsubseteq> y \<Longrightarrow> \<not>y \<sqsubseteq> x \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: asympartp_def)

lemmas asympartpI[intro] = asympartp_def[unfolded atomize_eq, THEN iffD2, unfolded conj_imp_eq_imp_imp, rule_format] 

lemma asympartp_eq[simp]: "asympartp (=) = bot" by auto

lemma asympartp_sympartp [simp]: "asympartp (sympartp r) = bot"
  and sympartp_asympartp [simp]: "sympartp (asympartp r) = bot"
  by (auto intro!: ext)

text \<open>Restriction to a set:\<close>

definition Restrp (infixl "\<restriction>" 60) where "(r \<restriction> A) a b \<equiv> a \<in> A \<and> b \<in> A \<and> r a b"

lemmas RestrpI[intro!] = Restrp_def[unfolded atomize_eq, THEN iffD2, unfolded conj_imp_eq_imp_imp]
lemmas RestrpE[elim!] = Restrp_def[unfolded atomize_eq, THEN iffD1, elim_format, unfolded conj_imp_eq_imp_imp]

lemma Restrp_UNIV[simp]: "r \<restriction> UNIV \<equiv> r" by (auto simp: atomize_eq)

lemma Restrp_Restrp[simp]: "r \<restriction> A \<restriction> B \<equiv> r \<restriction> A \<inter> B" by (auto simp: atomize_eq Restrp_def)

lemma sympartp_Restrp[simp]: "sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
  by (auto simp: atomize_eq)

text \<open>Relational images:\<close>
definition Imagep (infixr "```" 59) where "r ``` A \<equiv> {b. \<exists>a \<in> A. r a b}"

lemma Imagep_Image: "r ``` A = {(a,b). r a b} `` A"
  by (auto simp: Imagep_def)

lemma in_Imagep: "b \<in> r ``` A \<longleftrightarrow> (\<exists>a \<in> A. r a b)" by (auto simp: Imagep_def)

lemma ImagepI: "a \<in> A \<Longrightarrow> r a b \<Longrightarrow> b \<in> r ``` A" by (auto simp: in_Imagep)

lemma subset_Imagep: "B \<subseteq> r ``` A \<longleftrightarrow> (\<forall>b\<in>B. \<exists>a\<in>A. r a b)"
  by (auto simp: Imagep_def)

text \<open>Bounds of a set:\<close>
definition "bound X r b \<equiv> \<forall>x \<in> X. r x b"

lemma
  fixes r (infix "\<sqsubseteq>" 50)
  shows boundI[intro!]: "(\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> bound X (\<sqsubseteq>) b"
    and boundE[elim]: "bound X (\<sqsubseteq>) b \<Longrightarrow> ((\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: bound_def)

lemma bound_empty: "bound {} = (\<lambda>r x. True)" by auto

lemma bound_insert[simp]:
  fixes r (infix "\<sqsubseteq>" 50)
  shows "bound (insert x X) (\<sqsubseteq>) b \<longleftrightarrow> x \<sqsubseteq> b \<and> bound X (\<sqsubseteq>) b" by auto

text \<open>Extreme (greatest) elements in a set:\<close>
definition "extreme X r e \<equiv> e \<in> X \<and> (\<forall>x \<in> X. r x e)"

lemma
  fixes r (infix "\<sqsubseteq>" 50)
  shows extremeI[intro]: "e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e) \<Longrightarrow> extreme X (\<sqsubseteq>) e"
    and extremeD: "extreme X (\<sqsubseteq>) e \<Longrightarrow> e \<in> X" "extreme X (\<sqsubseteq>) e \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e)"
    and extremeE[elim]: "extreme X (\<sqsubseteq>) e \<Longrightarrow> (e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: extreme_def)

lemma
  fixes r (infix "\<sqsubseteq>" 50)
  shows extreme_UNIV[simp]: "extreme UNIV (\<sqsubseteq>) t \<longleftrightarrow> (\<forall>x. x \<sqsubseteq> t)" by auto

lemma extremes_equiv: "extreme X r b \<Longrightarrow> extreme X r c \<Longrightarrow> sympartp r b c" by blast

lemma bound_cmono: assumes "X \<subseteq> Y" shows "bound Y \<le> bound X"
  using assms by auto

lemma sympartp_sympartp[simp]: "sympartp (sympartp r) = sympartp r" by (auto intro!:ext)

text \<open>Now suprema and infima are given uniformly as follows.
  The definition is restricted to a given set.
\<close>
context
  fixes A :: "'a set" and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

abbreviation "extreme_bound X \<equiv> extreme {b \<in> A. bound X (\<sqsubseteq>) b} (\<lambda>x y. y \<sqsubseteq> x)"

lemma extreme_boundI[intro]:
  assumes "\<And>b. bound X (\<sqsubseteq>) b \<Longrightarrow> b \<in> A \<Longrightarrow> s \<sqsubseteq> b" and "\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> s" and "s \<in> A"
  shows "extreme_bound X s"
  using assms by auto

lemma extreme_bound_bound: "extreme_bound X y \<Longrightarrow> x \<in> X \<Longrightarrow> x \<sqsubseteq> y" by auto

lemma extreme_bound_mono:
  assumes XY: "X \<subseteq> Y"
    and sX: "extreme_bound X sX"
    and sY: "extreme_bound Y sY"
  shows "sX \<sqsubseteq> sY"
proof-
  have "bound X (\<sqsubseteq>) sY" using XY sY by force
  with sX sY show ?thesis by (auto 0 4)
qed

lemma extreme_bound_iff:
  shows "extreme_bound X s \<longleftrightarrow> s \<in> A \<and> (\<forall>c \<in> A. (\<forall>x \<in> X. x \<sqsubseteq> c) \<longrightarrow> s \<sqsubseteq> c) \<and> (\<forall>x \<in> X. x \<sqsubseteq> s)"
  by (auto simp: extreme_def)

lemma extreme_bound_singleton_refl[simp]:
  "extreme_bound {x} x \<longleftrightarrow> x \<in> A \<and> x \<sqsubseteq> x" by auto

lemma extreme_bound_image_const:
  "x \<sqsubseteq> x \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> f i = x) \<Longrightarrow> x \<in> A \<Longrightarrow> extreme_bound (f ` I) x"
  by (auto simp: image_constant)

lemma extreme_bound_UN_const:
  "x \<sqsubseteq> x \<Longrightarrow> I \<noteq> {} \<Longrightarrow> (\<And>i y. i \<in> I \<Longrightarrow> P i y \<longleftrightarrow> x = y) \<Longrightarrow> x \<in> A \<Longrightarrow>
  extreme_bound (\<Union>i\<in>I. {y. P i y}) x"
  by auto

end

context
  fixes ir :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<preceq>" 50)
    and r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
    and f and A and e and I
  assumes fIA: "f ` I \<subseteq> A"
    and mono: "monotone_on I (\<preceq>) (\<sqsubseteq>) f"
    and e: "extreme I (\<preceq>) e"
begin

lemma monotone_extreme_imp_extreme_bound:
  "extreme_bound A (\<sqsubseteq>) (f ` I) (f e)"
  using monotone_onD[OF mono] e fIA
  by (intro extreme_boundI, auto simp: image_def elim!: extremeE)

lemma monotone_extreme_extreme_boundI:
  "x = f e \<Longrightarrow> extreme_bound A (\<sqsubseteq>) (f ` I) x"
  using monotone_extreme_imp_extreme_bound by auto

end

subsection \<open>Locales for Binary Relations\<close>

text \<open>We now define basic properties of binary relations,
in form of \emph{locales}~\cite{Kammuller00,locale}.\<close>

subsubsection \<open>Syntactic Locales\<close>

text \<open>The following locales do not assume anything, but provide infix notations for
relations.\<close>

locale less_eq_syntax =
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)

locale less_syntax =
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)

locale equivalence_syntax =
  fixes equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sim>" 50)
begin

abbreviation equiv_class ("[_]\<^sub>\<sim>") where "[x]\<^sub>\<sim> \<equiv> { y. x \<sim> y }"

end

text \<open>Next ones introduce abbreviations for dual etc.
To avoid needless constants, one should be careful when declaring them as sublocales.\<close>

locale less_eq_notations = less_eq_syntax
begin

abbreviation (input) greater_eq (infix "\<sqsupseteq>" 50) where "x \<sqsupseteq> y \<equiv> y \<sqsubseteq> x"
abbreviation sym (infix "\<sim>" 50) where "(\<sim>) \<equiv> sympartp (\<sqsubseteq>)"
abbreviation less (infix "\<sqsubset>" 50) where "(\<sqsubset>) \<equiv> asympartp (\<sqsubseteq>)"
abbreviation greater (infix "\<sqsupset>" 50) where "(\<sqsupset>) \<equiv> (\<sqsubset>)\<^sup>-"
abbreviation equiv (infix "(\<simeq>)" 50) where "(\<simeq>) \<equiv> equivpartp (\<sqsubseteq>)"

lemma asym_cases[consumes 1, case_names asym sym]:
  assumes "x \<sqsubseteq> y" and "x \<sqsubset> y \<Longrightarrow> thesis" and "x \<sim> y \<Longrightarrow> thesis"
  shows thesis
  using assms by auto

end

locale less_notations = less_syntax
begin

abbreviation (input) greater (infix "\<sqsupset>" 50) where "x \<sqsupset> y \<equiv> y \<sqsubset> x"

end

locale related_set =
  fixes A :: "'a set" and less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)

subsubsection \<open>Basic Properties of Relations\<close>

text \<open>In the following we define basic properties in form of locales.\<close>

text \<open>Reflexivity restricted on a set:\<close>
locale reflexive = related_set +
  assumes refl[intro]: "x \<in> A \<Longrightarrow> x \<sqsubseteq> x"
begin

lemma eq_implies: "x = y \<Longrightarrow> x \<in> A \<Longrightarrow> x \<sqsubseteq> y" by auto

lemma extreme_singleton[simp]: "x \<in> A \<Longrightarrow> extreme {x} (\<sqsubseteq>) y \<longleftrightarrow> x = y" by auto

lemma extreme_bound_singleton: "x \<in> A \<Longrightarrow> extreme_bound A (\<sqsubseteq>) {x} x" by auto

lemma reflexive_subset: "B \<subseteq> A \<Longrightarrow> reflexive B (\<sqsubseteq>)" apply unfold_locales by auto

end

declare reflexive.intro[intro!]

lemma reflexiveE[elim]:
  assumes "reflexive A r" and "(\<And>x. x \<in> A \<Longrightarrow> r x x) \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: reflexive.refl)

lemma reflexive_cong:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b) \<Longrightarrow> reflexive A r \<longleftrightarrow> reflexive A r'"
  by (simp add: reflexive_def)

locale irreflexive = related_set A "(\<sqsubset>)" for A and less (infix "\<sqsubset>" 50) +
  assumes irrefl: "x \<in> A \<Longrightarrow> \<not> x \<sqsubset> x"
begin

lemma irreflD[simp]: "x \<sqsubset> x \<Longrightarrow> \<not>x \<in> A" by (auto simp: irrefl)

lemma implies_not_eq: "x \<sqsubset> y \<Longrightarrow> x \<in> A \<Longrightarrow> x \<noteq> y" by auto

lemma Restrp_irreflexive: "irreflexive UNIV ((\<sqsubset>)\<restriction>A)"
  apply unfold_locales by auto

lemma irreflexive_subset: "B \<subseteq> A \<Longrightarrow> irreflexive B (\<sqsubset>)" apply unfold_locales by auto

end

declare irreflexive.intro[intro!]

lemma irreflexive_cong:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b) \<Longrightarrow> irreflexive A r \<longleftrightarrow> irreflexive A r'"
  by (simp add: irreflexive_def)

locale transitive = related_set +
  assumes trans[trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubseteq> z"
begin

interpretation less_eq_notations.

lemma Restrp_transitive: "transitive UNIV ((\<sqsubseteq>)\<restriction>A)"
  apply unfold_locales
  by (auto intro: trans)

lemma bound_trans[trans]: "bound X (\<sqsubseteq>) b \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> X \<subseteq> A \<Longrightarrow> b \<in> A \<Longrightarrow> c \<in> A \<Longrightarrow> bound X (\<sqsubseteq>) c"
  by (auto 0 4 dest: trans)

lemma transitive_subset:
  assumes BA: "B \<subseteq> A" shows "transitive B (\<sqsubseteq>)"
  apply unfold_locales
  using trans BA by blast

lemma asympartp_transitive: "transitive A (\<sqsubset>)"
  apply unfold_locales by (auto dest:trans)

lemma reflclp_transitive: "transitive A (\<sqsubseteq>)\<^sup>=\<^sup>="
  apply unfold_locales by (auto dest: trans)

text \<open>The symmetric part is also transitive, but this is done in the later semiattractive locale\<close>

end

declare transitive.intro[intro?]

lemma transitive_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b" shows "transitive A r \<longleftrightarrow> transitive A r'"
proof (intro iffI)
  show "transitive A r \<Longrightarrow> transitive A r'"
    apply (intro transitive.intro)
    apply (unfold r[symmetric])
    using transitive.trans.
  show "transitive A r' \<Longrightarrow> transitive A r"
    apply (intro transitive.intro)
    apply (unfold r)
    using transitive.trans.
qed

lemma tranclp_transitive: "transitive A (tranclp r)"
  using tranclp_trans by unfold_locales

locale symmetric = related_set A "(\<sim>)" for A and equiv (infix "\<sim>" 50) +
  assumes sym[sym]: "x \<sim> y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> y \<sim> x"
begin

lemma sym_iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sim> y \<longleftrightarrow> y \<sim> x"
  by (auto dest: sym)

lemma Restrp_symmetric: "symmetric UNIV ((\<sim>)\<restriction>A)"
  apply unfold_locales by (auto simp: sym_iff)

lemma symmetric_subset: "B \<subseteq> A \<Longrightarrow> symmetric B (\<sim>)"
  apply unfold_locales by (auto dest: sym)

end

declare symmetric.intro[intro]

lemma symmetric_cong:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b) \<Longrightarrow> symmetric A r \<longleftrightarrow> symmetric A r'"
  by (auto simp: symmetric_def)


global_interpretation sympartp: symmetric UNIV "sympartp r"
  rewrites "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  by auto

lemma sympartp_symmetric: "symmetric A (sympartp r)" by auto

locale antisymmetric = related_set +
  assumes antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y"
begin

interpretation less_eq_notations.

lemma sym_iff_eq_refl: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sim> y \<longleftrightarrow> x = y \<and> y \<sqsubseteq> y" by (auto dest: antisym)

lemma equiv_iff_eq[simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<simeq> y \<longleftrightarrow> x = y" by (auto dest: antisym elim: equivpartpE)

lemma extreme_unique: "X \<subseteq> A \<Longrightarrow> extreme X (\<sqsubseteq>) x \<Longrightarrow> extreme X (\<sqsubseteq>) y \<longleftrightarrow> x = y"
  by (elim extremeE, auto dest!: antisym[OF _ _ subsetD])

lemma ex_extreme_iff_ex1:
  "X \<subseteq> A \<Longrightarrow> Ex (extreme X (\<sqsubseteq>)) \<longleftrightarrow> Ex1 (extreme X (\<sqsubseteq>))" by (auto simp: extreme_unique)

lemma ex_extreme_iff_the:
   "X \<subseteq> A \<Longrightarrow> Ex (extreme X (\<sqsubseteq>)) \<longleftrightarrow> extreme X (\<sqsubseteq>) (The (extreme X (\<sqsubseteq>)))"
  apply (rule iffI)
  apply (rule theI')
  using extreme_unique by auto

lemma Restrp_antisymmetric: "antisymmetric UNIV ((\<sqsubseteq>)\<restriction>A)"
   apply unfold_locales
  by (auto dest: antisym)

lemma antisymmetric_subset: "B \<subseteq> A \<Longrightarrow> antisymmetric B (\<sqsubseteq>)"
  apply unfold_locales using antisym by auto

end

declare antisymmetric.intro[intro]

lemma antisymmetric_cong:
  "(\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b) \<Longrightarrow> antisymmetric A r \<longleftrightarrow> antisymmetric A r'"
  by (auto simp: antisymmetric_def)

lemma antisymmetric_union:
  fixes less_eq (infix "\<sqsubseteq>" 50)
  assumes A: "antisymmetric A (\<sqsubseteq>)" and B: "antisymmetric B (\<sqsubseteq>)"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b \<longrightarrow> b \<sqsubseteq> a \<longrightarrow> a = b"
  shows "antisymmetric (A \<union> B) (\<sqsubseteq>)"
proof-
  interpret A: antisymmetric A "(\<sqsubseteq>)" using A.
  interpret B: antisymmetric B "(\<sqsubseteq>)" using B.
  show ?thesis by (auto dest: AB[rule_format] A.antisym B.antisym)
qed

text \<open>The following notion is new, generalizing antisymmetry and transitivity.\<close>

locale semiattractive = related_set +
  assumes attract: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubseteq> z"
begin

interpretation less_eq_notations.

lemma equiv_order_trans[trans]:
  assumes xy: "x \<simeq> y" and yz: "y \<sqsubseteq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubseteq> z"
  using attract[OF _ _ _ x y z] xy yz by (auto elim: equivpartpE)

lemma equiv_transitive: "transitive A (\<simeq>)"
proof unfold_locales
  fix x y z
  assume x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A" and xy: "x \<simeq> y" and yz: "y \<simeq> z"
  show "x \<simeq> z"
    using equiv_order_trans[OF xy _ x y z] attract[OF _ _ _ z y x] xy yz by (auto simp:equivpartp_def)
qed

lemma sym_order_trans[trans]:
  assumes xy: "x \<sim> y" and yz: "y \<sqsubseteq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubseteq> z"
  using attract[OF _ _ _ x y z] xy yz by auto

interpretation sym: transitive A "(\<sim>)"
proof unfold_locales
  fix x y z
  assume x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A" and xy: "x \<sim> y" and yz: "y \<sim> z"
  show "x \<sim> z"
    using sym_order_trans[OF xy _ x y z] attract[OF _ _ _ z y x] xy yz by auto
qed

lemmas sym_transitive = sym.transitive_axioms

lemma extreme_bound_quasi_const:
  assumes C: "C \<subseteq> A" and x: "x \<in> A" and C0: "C \<noteq> {}" and const: "\<forall>y \<in> C. y \<sim> x"
  shows "extreme_bound A (\<sqsubseteq>) C x"
proof (intro extreme_boundI x)
  from C0 obtain c where cC: "c \<in> C" by auto
  with C have c: "c \<in> A" by auto
  from cC const have cx: "c \<sim> x" by auto
  fix b assume b: "b \<in> A" and "bound C (\<sqsubseteq>) b"
  with cC have cb: "c \<sqsubseteq> b" by auto
  from attract[OF _ _ cb x c b] cx show "x \<sqsubseteq> b" by auto
next
  fix c assume "c \<in> C"
  with const show "c \<sqsubseteq> x" by auto
qed

lemma extreme_bound_quasi_const_iff:
  assumes C: "C \<subseteq> A" and x: "x \<in> A" and y: "y \<in> A" and C0: "C \<noteq> {}" and const: "\<forall>z \<in> C. z \<sim> x"
  shows "extreme_bound A (\<sqsubseteq>) C y \<longleftrightarrow> x \<sim> y"
proof (intro iffI)
  assume y: "extreme_bound A (\<sqsubseteq>) C y"
  note x = extreme_bound_quasi_const[OF C x C0 const]
  from extremes_equiv[OF y x]
  show "x \<sim> y" by auto
next
  assume xy: "x \<sim> y"
  with const C sym.trans[OF _ xy _ x y] have Cy: "\<forall>z \<in> C. z \<sim> y" by auto
  show "extreme_bound A (\<sqsubseteq>) C y"
    using extreme_bound_quasi_const[OF C y C0 Cy].
qed

lemma Restrp_semiattractive: "semiattractive UNIV ((\<sqsubseteq>)\<restriction>A)"
  apply unfold_locales
  by (auto dest: attract)

lemma semiattractive_subset: "B \<subseteq> A \<Longrightarrow> semiattractive B (\<sqsubseteq>)"
  apply unfold_locales using attract by blast

end

lemma semiattractive_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "semiattractive A r \<longleftrightarrow> semiattractive A r'" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r"
    apply (intro semiattractive.intro)
    apply (unfold r[symmetric])
    using semiattractive.attract.
  show "?r \<Longrightarrow> ?l"
    apply (intro semiattractive.intro)
    apply (unfold r)
    using semiattractive.attract.
qed

locale attractive = semiattractive +
  assumes "semiattractive A (\<sqsubseteq>)\<^sup>-"
begin

interpretation less_eq_notations.

sublocale dual: semiattractive A "(\<sqsubseteq>)\<^sup>-"
  rewrites "\<And>r. sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
    and "\<And>r. sympartp (sympartp r) \<equiv> sympartp r"
    and "sympartp ((\<sqsubseteq>) \<restriction> A)\<^sup>- \<equiv> (\<sim>) \<restriction> A"
    and "sympartp (\<sqsubseteq>)\<^sup>- \<equiv> (\<sim>)"
    and "equivpartp (\<sqsubseteq>)\<^sup>- \<equiv> (\<simeq>)"
  using attractive_axioms[unfolded attractive_def]
  by (auto intro!: ext simp: attractive_axioms_def atomize_eq equivpartp_def)

lemma order_equiv_trans[trans]:
  assumes xy: "x \<sqsubseteq> y" and yz: "y \<simeq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubseteq> z"
  using dual.attract[OF _ _ _ z y x] xy yz by auto

lemma order_sym_trans[trans]:
  assumes xy: "x \<sqsubseteq> y" and yz: "y \<sim> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubseteq> z"
  using dual.attract[OF _ _ _ z y x] xy yz by auto

interpretation Restrp: semiattractive UNIV "(\<sqsubseteq>)\<restriction>A" using Restrp_semiattractive.
interpretation dual.Restrp: semiattractive UNIV "(\<sqsubseteq>)\<^sup>-\<restriction>A" using dual.Restrp_semiattractive.

lemma Restrp_attractive: "attractive UNIV ((\<sqsubseteq>)\<restriction>A)"
  apply unfold_locales
  using dual.Restrp.attract by auto

lemma attractive_subset: "B \<subseteq> A \<Longrightarrow> attractive B (\<sqsubseteq>)"
  apply (intro attractive.intro attractive_axioms.intro)
  using semiattractive_subset dual.semiattractive_subset by auto

end

lemma attractive_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "attractive A r \<longleftrightarrow> attractive A r'"
  by (simp add: attractive_def attractive_axioms_def r cong: semiattractive_cong)

context antisymmetric begin

sublocale attractive
  apply unfold_locales by (auto dest: antisym)

end

context transitive begin

sublocale attractive
  rewrites "\<And>r. sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
    and "\<And>r. sympartp (sympartp r) \<equiv> sympartp r"
    and "sympartp (\<sqsubseteq>)\<^sup>- \<equiv> sympartp (\<sqsubseteq>)"
    and "(sympartp (\<sqsubseteq>))\<^sup>- \<equiv> sympartp (\<sqsubseteq>)"
    and "(sympartp (\<sqsubseteq>) \<restriction> A)\<^sup>- \<equiv> sympartp (\<sqsubseteq>) \<restriction> A"
    and "asympartp (asympartp (\<sqsubseteq>)) = asympartp (\<sqsubseteq>)"
    and "asympartp (sympartp (\<sqsubseteq>)) = bot"
    and "asympartp (\<sqsubseteq>) \<restriction> A = asympartp ((\<sqsubseteq>) \<restriction> A)"
  apply unfold_locales
  by (auto intro!:ext dest: trans simp: atomize_eq)

end

subsection \<open>Combined Properties\<close>

text \<open>Some combinations of the above basic properties are given names.\<close>

locale asymmetric = related_set A "(\<sqsubset>)" for A and less (infix "\<sqsubset>" 50) +
  assumes asym: "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> False"
begin

sublocale irreflexive
  apply unfold_locales by (auto dest: asym)

lemma antisymmetric_axioms: "antisymmetric A (\<sqsubset>)"
  apply unfold_locales by (auto dest: asym)

lemma Restrp_asymmetric: "asymmetric UNIV ((\<sqsubset>)\<restriction>A)"
  apply unfold_locales
  by (auto dest:asym)

lemma asymmetric_subset: "B \<subseteq> A \<Longrightarrow> asymmetric B (\<sqsubset>)"
  apply unfold_locales using asym by auto

end

lemma asymmetric_iff_irreflexive_antisymmetric:
  fixes less (infix "\<sqsubset>" 50)
  shows "asymmetric A (\<sqsubset>) \<longleftrightarrow> irreflexive A (\<sqsubset>) \<and> antisymmetric A (\<sqsubset>)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  then interpret asymmetric.
  show ?r by (auto dest: asym)
next
  assume ?r
  then interpret irreflexive + antisymmetric A "(\<sqsubset>)" by auto
  show ?l by (auto intro!:asymmetric.intro dest: antisym irrefl)
qed

lemma asymmetric_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "asymmetric A r \<longleftrightarrow> asymmetric A r'"
  by (simp add: asymmetric_iff_irreflexive_antisymmetric r cong: irreflexive_cong antisymmetric_cong)

locale quasi_ordered_set = reflexive + transitive
begin

lemma quasi_ordered_subset: "B \<subseteq> A \<Longrightarrow> quasi_ordered_set B (\<sqsubseteq>)"
  apply intro_locales
  using reflexive_subset transitive_subset by auto

end

lemma quasi_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "quasi_ordered_set A r \<longleftrightarrow> quasi_ordered_set A r'"
  by (simp add: quasi_ordered_set_def r cong: reflexive_cong transitive_cong)

locale near_ordered_set = antisymmetric + transitive
begin

interpretation Restrp: antisymmetric UNIV "(\<sqsubseteq>)\<restriction>A" using Restrp_antisymmetric.
interpretation Restrp: transitive UNIV "(\<sqsubseteq>)\<restriction>A" using Restrp_transitive.

lemma Restrp_near_order: "near_ordered_set UNIV ((\<sqsubseteq>)\<restriction>A)"..

lemma near_ordered_subset: "B \<subseteq> A \<Longrightarrow> near_ordered_set B (\<sqsubseteq>)"
  apply intro_locales
  using antisymmetric_subset transitive_subset by auto

end

lemma near_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "near_ordered_set A r \<longleftrightarrow> near_ordered_set A r'"
  by (simp add: near_ordered_set_def r cong: antisymmetric_cong transitive_cong)

locale pseudo_ordered_set = reflexive + antisymmetric
begin

interpretation less_eq_notations.

lemma sym_eq[simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sim> y \<longleftrightarrow> x = y"
  by (auto simp: refl dest: antisym)

lemma extreme_bound_singleton_eq[simp]: "x \<in> A \<Longrightarrow> extreme_bound A (\<sqsubseteq>) {x} y \<longleftrightarrow> x = y"
  by (auto intro!: antisym)

lemma eq_iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y \<longleftrightarrow> x \<sqsubseteq> y \<and> y \<sqsubseteq> x" by (auto dest: antisym simp:refl)

lemma extreme_order_iff_eq: "e \<in> A \<Longrightarrow> extreme {x \<in> A. x \<sqsubseteq> e} (\<sqsubseteq>) s \<longleftrightarrow> e = s"
  by (auto intro!: antisym)

lemma pseudo_ordered_subset: "B \<subseteq> A \<Longrightarrow> pseudo_ordered_set B (\<sqsubseteq>)"
  apply intro_locales
  using reflexive_subset antisymmetric_subset by auto

end

lemma pseudo_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "pseudo_ordered_set A r \<longleftrightarrow> pseudo_ordered_set A r'"
  by (simp add: pseudo_ordered_set_def r cong: reflexive_cong antisymmetric_cong)

locale partially_ordered_set = reflexive + antisymmetric + transitive
begin

sublocale pseudo_ordered_set + quasi_ordered_set + near_ordered_set ..

lemma partially_ordered_subset: "B \<subseteq> A \<Longrightarrow> partially_ordered_set B (\<sqsubseteq>)"
  apply intro_locales
  using reflexive_subset transitive_subset antisymmetric_subset by auto

end

lemma partially_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "partially_ordered_set A r \<longleftrightarrow> partially_ordered_set A r'"
  by (simp add: partially_ordered_set_def r cong: reflexive_cong antisymmetric_cong transitive_cong)

locale strict_ordered_set = irreflexive + transitive A "(\<sqsubset>)"
begin

sublocale asymmetric
proof
  fix x y
  assume x: "x \<in> A" and y: "y \<in> A"
  assume xy: "x \<sqsubset> y"
  also assume yx: "y \<sqsubset> x"
  finally have "x \<sqsubset> x" using x y by auto
  with x show False by auto
qed

lemma near_ordered_set_axioms: "near_ordered_set A (\<sqsubset>)"
  using antisymmetric_axioms by intro_locales

interpretation Restrp: asymmetric UNIV "(\<sqsubset>)\<restriction>A" using Restrp_asymmetric.
interpretation Restrp: transitive UNIV "(\<sqsubset>)\<restriction>A" using Restrp_transitive.

lemma Restrp_strict_order: "strict_ordered_set UNIV ((\<sqsubset>)\<restriction>A)"..

lemma strict_ordered_subset: "B \<subseteq> A \<Longrightarrow> strict_ordered_set B (\<sqsubset>)"
  apply intro_locales
  using irreflexive_subset transitive_subset by auto

end

lemma strict_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "strict_ordered_set A r \<longleftrightarrow> strict_ordered_set A r'"
  by (simp add: strict_ordered_set_def r cong: irreflexive_cong transitive_cong)

locale tolerance = symmetric + reflexive A "(\<sim>)"
begin

lemma tolerance_subset: "B \<subseteq> A \<Longrightarrow> tolerance B (\<sim>)"
  apply intro_locales
  using symmetric_subset reflexive_subset by auto

end

lemma tolerance_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "tolerance A r \<longleftrightarrow> tolerance A r'"
  by (simp add: tolerance_def r cong: reflexive_cong symmetric_cong)

global_interpretation equiv: tolerance UNIV "equivpartp r"
  rewrites "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  by unfold_locales (auto simp:equivpartp_def)

locale partial_equivalence = symmetric +
  assumes "transitive A (\<sim>)"
begin

sublocale transitive A "(\<sim>)"
  rewrites "sympartp (\<sim>)\<restriction>A \<equiv> (\<sim>)\<restriction>A"
    and "sympartp ((\<sim>)\<restriction>A) \<equiv> (\<sim>)\<restriction>A"
  using partial_equivalence_axioms
  unfolding partial_equivalence_axioms_def partial_equivalence_def
  by (auto simp: atomize_eq sym intro!:ext)

lemma partial_equivalence_subset: "B \<subseteq> A \<Longrightarrow> partial_equivalence B (\<sim>)"
  apply (intro partial_equivalence.intro partial_equivalence_axioms.intro)
  using symmetric_subset transitive_subset by auto

end

lemma partial_equivalence_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "partial_equivalence A r \<longleftrightarrow> partial_equivalence A r'"
  by (simp add: partial_equivalence_def partial_equivalence_axioms_def r
      cong: transitive_cong symmetric_cong)

locale equivalence = symmetric + reflexive A "(\<sim>)" + transitive A "(\<sim>)"
begin

sublocale tolerance + partial_equivalence + quasi_ordered_set A "(\<sim>)"..

lemma equivalence_subset: "B \<subseteq> A \<Longrightarrow> equivalence B (\<sim>)"
  apply (intro equivalence.intro)
  using symmetric_subset transitive_subset by auto

end

lemma equivalence_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "equivalence A r \<longleftrightarrow> equivalence A r'"
  by (simp add: equivalence_def r cong: reflexive_cong transitive_cong symmetric_cong)

text \<open>Some combinations lead to uninteresting relations.\<close>

context
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<bowtie>" 50)
begin

proposition reflexive_irreflexive_is_empty:
  assumes r: "reflexive A (\<bowtie>)" and ir: "irreflexive A (\<bowtie>)"
  shows "A = {}"
proof (rule ccontr)
  interpret irreflexive A "(\<bowtie>)" using ir.
  interpret reflexive A "(\<bowtie>)" using r.
  assume "A \<noteq> {}"
  then obtain a where a: "a \<in> A" by auto
  from a refl have "a \<bowtie> a" by auto
  with irrefl a show False by auto
qed

proposition symmetric_antisymmetric_imp_eq:
  assumes s: "symmetric A (\<bowtie>)" and as: "antisymmetric A (\<bowtie>)"
  shows "(\<bowtie>)\<restriction>A \<le> (=)"
proof-
  interpret symmetric A "(\<bowtie>)" + antisymmetric A "(\<bowtie>)" using assms by auto
  show "?thesis" using antisym by (auto dest: sym)
qed

proposition nontolerance:
  shows "irreflexive A (\<bowtie>) \<and> symmetric A (\<bowtie>) \<longleftrightarrow> tolerance A (\<lambda>x y. \<not> x \<bowtie> y)"
proof (intro iffI conjI, elim conjE)
  assume "irreflexive A (\<bowtie>)" and "symmetric A (\<bowtie>)"
  then interpret irreflexive A "(\<bowtie>)" + symmetric A "(\<bowtie>)".
  show "tolerance A (\<lambda>x y. \<not> x \<bowtie> y)" by (unfold_locales, auto dest: sym irrefl)
next
  assume "tolerance A (\<lambda>x y. \<not> x \<bowtie> y)"
  then interpret tolerance A "\<lambda>x y. \<not> x \<bowtie> y".
  show "irreflexive A (\<bowtie>)" by (auto simp: eq_implies)
  show "symmetric A (\<bowtie>)" using sym by auto
qed

proposition irreflexive_transitive_symmetric_is_empty:
  assumes irr: "irreflexive A (\<bowtie>)" and tr: "transitive A (\<bowtie>)" and sym: "symmetric A (\<bowtie>)"
  shows "(\<bowtie>)\<restriction>A = bot"
proof (intro ext, unfold bot_fun_def bot_bool_def eq_False, rule notI, erule RestrpE)
  interpret strict_ordered_set A "(\<bowtie>)" using assms by (unfold strict_ordered_set_def, auto)
  interpret symmetric A "(\<bowtie>)" using assms by auto
  fix x y assume x: "x \<in> A" and y: "y \<in> A"
  assume xy: "x \<bowtie> y"
  also note sym[OF xy x y]
  finally have "x \<bowtie> x" using x y by auto
  with x show False by auto
qed

end

subsection \<open>Totality\<close>

locale semiconnex = related_set A "(\<sqsubset>)" for A and less (infix "\<sqsubset>" 50) +
  assumes semiconnex: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
begin

lemma cases[consumes 2, case_names less eq greater]:
  assumes "x \<in> A" and "y \<in> A" and "x \<sqsubset> y \<Longrightarrow> P" and "x = y \<Longrightarrow> P" and "y \<sqsubset> x \<Longrightarrow> P"
  shows "P" using semiconnex assms by auto

lemma neqE:
  assumes "x \<in> A" and "y \<in> A"
  shows "x \<noteq> y \<Longrightarrow> (x \<sqsubset> y \<Longrightarrow> P) \<Longrightarrow> (y \<sqsubset> x \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases rule: cases[OF assms], auto)

lemma semiconnex_subset: "B \<subseteq> A \<Longrightarrow> semiconnex B (\<sqsubset>)"
  apply (intro semiconnex.intro)
  using semiconnex by auto

end

declare semiconnex.intro[intro]

text \<open>Totality is negated antisymmetry \cite[Proposition 2.2.4]{Schmidt1993}.\<close>
proposition semiconnex_iff_neg_antisymmetric:
  fixes less (infix "\<sqsubset>" 50)
  shows "semiconnex A (\<sqsubset>) \<longleftrightarrow> antisymmetric A (\<lambda>x y. \<not> x \<sqsubset> y)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI semiconnex.intro antisymmetric.intro)
  assume ?l
  then interpret semiconnex.
  fix x y
  assume "x \<in> A" "y \<in> A" "\<not> x \<sqsubset> y" and "\<not> y \<sqsubset> x"
  then show "x = y" by (cases rule: cases, auto)
next
  assume ?r
  then interpret neg: antisymmetric A "(\<lambda>x y. \<not> x \<sqsubset> y)".
  fix x y
  show "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x" using neg.antisym by auto
qed

lemma semiconnex_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "semiconnex A r \<longleftrightarrow> semiconnex A r'"
  by (simp add: semiconnex_iff_neg_antisymmetric r cong: antisymmetric_cong)

locale semiconnex_irreflexive = semiconnex + irreflexive
begin

lemma neq_iff: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<longleftrightarrow> x \<sqsubset> y \<or> y \<sqsubset> x" by (auto elim:neqE dest: irrefl)

lemma semiconnex_irreflexive_subset: "B \<subseteq> A \<Longrightarrow> semiconnex_irreflexive B (\<sqsubset>)"
  apply (intro semiconnex_irreflexive.intro)
  using semiconnex_subset irreflexive_subset by auto

end

lemma semiconnex_irreflexive_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "semiconnex_irreflexive A r \<longleftrightarrow> semiconnex_irreflexive A r'"
  by (simp add: semiconnex_irreflexive_def r cong: semiconnex_cong irreflexive_cong)

locale connex = related_set +
  assumes comparable: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
begin

interpretation less_eq_notations.

sublocale reflexive apply unfold_locales using comparable by auto

lemma comparable_cases[consumes 2, case_names le ge]:
  assumes "x \<in> A" and "y \<in> A" and "x \<sqsubseteq> y \<Longrightarrow> P" and "y \<sqsubseteq> x \<Longrightarrow> P" shows "P"
  using assms comparable by auto

lemma comparable_three_cases[consumes 2, case_names less eq greater]:
  assumes "x \<in> A" and "y \<in> A" and "x \<sqsubset> y \<Longrightarrow> P" and "x \<sim> y \<Longrightarrow> P" and "y \<sqsubset> x \<Longrightarrow> P" shows "P"
  using assms comparable by auto

lemma
  assumes x: "x \<in> A" and y: "y \<in> A"
  shows not_iff_asym: "\<not>x \<sqsubseteq> y \<longleftrightarrow> y \<sqsubset> x"
    and not_asym_iff[simp]: "\<not>x \<sqsubset> y \<longleftrightarrow> y \<sqsubseteq> x"
  using comparable[OF x y] by auto

lemma connex_subset: "B \<subseteq> A \<Longrightarrow> connex B (\<sqsubseteq>)"
  by (intro connex.intro comparable, auto)

end

lemmas connexE = connex.comparable_cases

lemmas connexI[intro] = connex.intro

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma connex_iff_semiconnex_reflexive: "connex A (\<sqsubseteq>) \<longleftrightarrow> semiconnex A (\<sqsubseteq>) \<and> reflexive A (\<sqsubseteq>)"
  (is "?c \<longleftrightarrow> ?t \<and> ?r")
proof (intro iffI conjI; (elim conjE)?)
  assume ?c then interpret connex.
  show ?t apply unfold_locales using comparable by auto
  show ?r by unfold_locales
next
  assume ?t then interpret semiconnex A "(\<sqsubseteq>)".
  assume ?r then interpret reflexive.
  from semiconnex show ?c by auto
qed

lemma chain_connect: "Complete_Partial_Order.chain r A \<equiv> connex A r"
  by (auto intro!: ext simp: atomize_eq connex_def Complete_Partial_Order.chain_def)

lemma connex_union:
  assumes "connex X (\<sqsubseteq>)" and "connex Y (\<sqsubseteq>)" and "\<forall>x \<in> X. \<forall>y \<in> Y. x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  shows "connex (X\<union>Y) (\<sqsubseteq>)"
  using assms by (auto simp: connex_def)

end

lemma connex_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "connex A r \<longleftrightarrow> connex A r'"
  by (simp add: connex_iff_semiconnex_reflexive r cong: semiconnex_cong reflexive_cong)

locale total_pseudo_ordered_set = connex + antisymmetric
begin

sublocale pseudo_ordered_set ..

lemma not_weak_iff:
  assumes x: "x \<in> A" and y: "y \<in> A" shows "\<not> y \<sqsubseteq> x \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
using x y by (cases rule: comparable_cases, auto intro:antisym)

lemma total_pseudo_ordered_subset: "B \<subseteq> A \<Longrightarrow> total_pseudo_ordered_set B (\<sqsubseteq>)"
  apply (intro_locales)
  using antisymmetric_subset connex_subset by auto

end

lemma total_pseudo_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "total_pseudo_ordered_set A r \<longleftrightarrow> total_pseudo_ordered_set A r'"
  by (simp add: total_pseudo_ordered_set_def r cong: connex_cong antisymmetric_cong)

locale total_quasi_ordered_set = connex + transitive
begin

sublocale quasi_ordered_set ..

lemma total_quasi_ordered_subset: "B \<subseteq> A \<Longrightarrow> total_quasi_ordered_set B (\<sqsubseteq>)"
  using transitive_subset connex_subset by intro_locales

end

lemma total_quasi_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "total_quasi_ordered_set A r \<longleftrightarrow> total_quasi_ordered_set A r'"
  by (simp add: total_quasi_ordered_set_def r cong: connex_cong transitive_cong)

locale total_ordered_set = total_quasi_ordered_set + antisymmetric
begin

sublocale partially_ordered_set + total_pseudo_ordered_set ..

lemma total_ordered_subset: "B \<subseteq> A \<Longrightarrow> total_ordered_set B (\<sqsubseteq>)"
  using total_quasi_ordered_subset antisymmetric_subset by (intro total_ordered_set.intro)

end

lemma total_ordered_set_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
  shows "total_ordered_set A r \<longleftrightarrow> total_ordered_set A r'"
  by (simp add: total_ordered_set_def r cong: total_quasi_ordered_set_cong antisymmetric_cong)

subsection \<open>Well-Foundedness\<close>

locale well_founded = related_set A "(\<sqsubset>)" for A and less (infix "\<sqsubset>" 50) +
  assumes induct[consumes 1, case_names less, induct set]:
    "a \<in> A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
begin

sublocale asymmetric
proof (intro asymmetric.intro notI)
  fix x y
  assume xA: "x \<in> A"
  then show "y \<in> A \<Longrightarrow> x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False"
    by (induct arbitrary: y rule: induct, auto)
qed

lemma prefixed_Imagep_imp_empty:
  assumes a: "X \<subseteq> ((\<sqsubset>) ``` X) \<inter> A" shows "X = {}"
proof -
  from a have XA: "X \<subseteq> A" by auto
  have "x \<in> A \<Longrightarrow> x \<notin> X" for x
  proof (induct x rule: induct)
    case (less x)
    with a show ?case by (auto simp: Imagep_def)
  qed
  with XA show ?thesis by auto
qed

lemma nonempty_imp_ex_extremal:
  assumes QA: "Q \<subseteq> A" and Q: "Q \<noteq> {}"
  shows "\<exists>z \<in> Q. \<forall>y \<in> Q. \<not> y \<sqsubset> z"
  using Q prefixed_Imagep_imp_empty[of Q] QA by (auto simp: Imagep_def)

interpretation Restrp: well_founded UNIV "(\<sqsubset>)\<restriction>A"
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "(\<sqsubset>)\<restriction>A\<restriction>UNIV = (\<sqsubset>)\<restriction>A"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
proof -
  have "(\<And>x. (\<And>y. ((\<sqsubset>) \<restriction> A) y x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a" for a P
    using induct[of a P] by (auto simp: Restrp_def)
  then show "well_founded UNIV ((\<sqsubset>)\<restriction>A)" apply unfold_locales by auto
qed auto

lemmas Restrp_well_founded = Restrp.well_founded_axioms
lemmas Restrp_induct[consumes 0, case_names less] = Restrp.induct

interpretation Restrp.tranclp: well_founded UNIV "((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+"
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+ \<restriction> UNIV = ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+"
    and "(((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+)\<^sup>+\<^sup>+ = ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
proof-
  { fix P x
    assume induct_step: "\<And>x. (\<And>y. ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+ y x \<Longrightarrow> P y) \<Longrightarrow> P x"
    have "P x"
    proof (rule induct_step)
      show "\<And>y. ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+ y x \<Longrightarrow> P y"
      proof (induct x rule: Restrp_induct)
        case (less x)
        from \<open>((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+ y x\<close>
        show ?case
        proof (cases rule: tranclp.cases)
          case r_into_trancl
          with induct_step less show ?thesis by auto
        next
          case (trancl_into_trancl b)
          with less show ?thesis by auto
        qed
      qed
    qed
  }
  then show "well_founded UNIV ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+" by unfold_locales auto
qed auto

lemmas Restrp_tranclp_well_founded = Restrp.tranclp.well_founded_axioms
lemmas Restrp_tranclp_induct[consumes 0, case_names less] = Restrp.tranclp.induct

end

context
  fixes A :: "'a set" and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)
begin

lemma well_foundedI_pf:
  assumes pre: "\<And>X. X \<subseteq> A \<Longrightarrow> X \<subseteq> ((\<sqsubset>) ``` X) \<inter> A \<Longrightarrow> X = {}"
  shows "well_founded A (\<sqsubset>)"
proof
  fix P a assume aA: "a \<in> A" and Ind: "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> P y) \<Longrightarrow> P x"
  from Ind have "{a\<in>A. \<not>P a} \<subseteq> ((\<sqsubset>) ``` {a\<in>A. \<not>P a}) \<inter> A" by (auto simp: Imagep_def)
  from pre[OF _ this] aA
  show "P a" by auto
qed

lemma well_foundedI_extremal:
  assumes a: "\<And>X. X \<subseteq> A \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>x \<in> X. \<forall>y \<in> X. \<not> y \<sqsubset> x"
  shows "well_founded A (\<sqsubset>)"
proof (rule well_foundedI_pf)
  fix X assume XA: "X \<subseteq> A" and pf: "X \<subseteq> ((\<sqsubset>) ``` X) \<inter> A"
  from a[OF XA] pf show "X = {}" by (auto simp: Imagep_def)
qed

lemma well_founded_iff_ex_extremal:
  "well_founded A (\<sqsubset>) \<longleftrightarrow> (\<forall>X \<subseteq> A. X \<noteq> {} \<longrightarrow> (\<exists>x \<in> X. \<forall>z \<in> X. \<not> z \<sqsubset> x))"
  using well_founded.nonempty_imp_ex_extremal well_foundedI_extremal by blast

end

lemma well_founded_cong:
  assumes r: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> r a b \<longleftrightarrow> r' a b"
    and A: "\<And>a b. r' a b \<Longrightarrow> a \<in> A \<longleftrightarrow> a \<in> A'"
    and B: "\<And>a b. r' a b \<Longrightarrow> b \<in> A \<longleftrightarrow> b \<in> A'"
  shows "well_founded A r \<longleftrightarrow> well_founded A' r'"
proof (intro iffI)
  assume wf: "well_founded A r"
  show "well_founded A' r'"
  proof (intro well_foundedI_extremal)
    fix X
    assume X: "X \<subseteq> A'" and X0: "X \<noteq> {}"
    show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> r' y x"
    proof (cases "X \<inter> A = {}")
      case True
      from X0 obtain x where xX: "x \<in> X" by auto
      with True have "x \<notin> A" by auto
      with xX X have "\<forall>y\<in>X. \<not> r' y x" by (auto simp: B)
      with xX show ?thesis by auto
    next
      case False
      from well_founded.nonempty_imp_ex_extremal[OF wf _ this]
      obtain x where x: "x \<in> X \<inter> A" and Ar: "\<And>y. y \<in> X \<Longrightarrow> y \<in> A \<Longrightarrow> \<not> r y x" by auto
      have "\<forall>y \<in> X. \<not> r' y x"
      proof (intro ballI notI)
        fix y assume yX: "y \<in> X" and yx: "r' y x"
        from yX X have yA': "y \<in> A'" by auto
        show False
        proof (cases "y \<in> A")
          case True with x Ar[OF yX] yx r show ?thesis by auto
        next
          case False with yA' x A[OF yx] r X show ?thesis by (auto simp:)
        qed
      qed
      with x show "\<exists>x \<in> X. \<forall>y \<in> X. \<not> r' y x" by auto
    qed
  qed
next
  assume wf: "well_founded A' r'"
  show "well_founded A r"
  proof (intro well_foundedI_extremal)
    fix X
    assume X: "X \<subseteq> A" and X0: "X \<noteq> {}"
    show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> r y x"
    proof (cases "X \<inter> A' = {}")
      case True
      from X0 obtain x where xX: "x \<in> X" by auto
      with True have "x \<notin> A'" by auto
      with xX X B have "\<forall>y\<in>X. \<not> r y x" by (auto simp: r in_mono)
      with xX show ?thesis by auto
    next
      case False
      from well_founded.nonempty_imp_ex_extremal[OF wf _ this]
      obtain x where x: "x \<in> X \<inter> A'" and Ar: "\<And>y. y \<in> X \<Longrightarrow> y \<in> A' \<Longrightarrow> \<not> r' y x" by auto
      have "\<forall>y \<in> X. \<not> r y x"
      proof (intro ballI notI)
        fix y assume yX: "y \<in> X" and yx: "r y x"
        from yX X have y: "y \<in> A" by auto
        show False
        proof (cases "y \<in> A'")
          case True with x Ar[OF yX] yx r X y show ?thesis by auto
        next
          case False with y x A yx r X show ?thesis by auto
        qed
      qed
      with x show "\<exists>x \<in> X. \<forall>y \<in> X. \<not> r y x" by auto
    qed
  qed
qed

lemma wfP_iff_well_founded_UNIV: "wfP r \<longleftrightarrow> well_founded UNIV r"
  by (auto simp: wfP_def wf_def well_founded_def)

lemma well_founded_singleton:
  assumes "\<not>r x x" shows "well_founded {x} r"
  using assms by (auto simp: well_founded_iff_ex_extremal)

lemma well_founded_Restrp[simp]: "well_founded A (r\<restriction>B) \<longleftrightarrow> well_founded (A\<inter>B) r" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI well_foundedI_extremal)
  assume l: ?l
  fix X assume XAB: "X \<subseteq> A \<inter> B" and X0: "X \<noteq> {}"
  with l[THEN well_founded.nonempty_imp_ex_extremal]
  have "\<exists>x\<in>X. \<forall>z\<in>X. \<not> (r \<restriction> B) z x" by auto
  with XAB show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> r y x" by (auto simp: Restrp_def)
next
  assume r: ?r
  fix X assume XA: "X \<subseteq> A" and X0: "X \<noteq> {}"
  show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> (r \<restriction> B) y x"
  proof (cases "X \<subseteq> B")
    case True
    with r[THEN well_founded.nonempty_imp_ex_extremal, of X] XA X0
    have "\<exists>z\<in>X. \<forall>y\<in>X. \<not> r y z" by auto
    then show ?thesis by auto
  next
    case False
    then obtain x where x: "x \<in> X - B" by auto
    then have "\<forall>y\<in>X. \<not> (r \<restriction> B) y x" by auto
    with x show ?thesis by auto
  qed
qed

lemma (in well_founded) well_founded_subset:
  assumes "B \<subseteq> A" shows "well_founded B (\<sqsubset>)"
  using assms well_founded_axioms by (auto simp: well_founded_iff_ex_extremal)

lemma well_founded_extend:
  fixes less (infix "\<sqsubset>" 50)
  assumes A: "well_founded A (\<sqsubset>)"
  assumes B: "well_founded B (\<sqsubset>)"
  assumes AB: "\<forall>a \<in> A. \<forall>b \<in> B. \<not>b \<sqsubset> a"
  shows "well_founded (A \<union> B) (\<sqsubset>)"
proof (intro well_foundedI_extremal)
  interpret A: well_founded A "(\<sqsubset>)" using A.
  interpret B: well_founded B "(\<sqsubset>)" using B.
  fix X assume XAB: "X \<subseteq> A \<union> B" and X0: "X \<noteq> {}"
  show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> y \<sqsubset> x"
  proof (cases "X \<inter> A = {}")
    case True
    with XAB have XB: "X \<subseteq> B" by auto
    from B.nonempty_imp_ex_extremal[OF XB X0] show ?thesis.
  next
    case False
    with A.nonempty_imp_ex_extremal[OF _ this]
    obtain e where XAe: "e \<in> X \<inter> A" "\<forall>y\<in>X \<inter> A. \<not> y \<sqsubset> e" by auto
    then have eX: "e \<in> X" and eA: "e \<in> A" by auto
    { fix x assume xX: "x \<in> X"
      have "\<not>x \<sqsubset> e"
      proof (cases "x \<in> A")
        case True with XAe xX show ?thesis by auto
      next
        case False
        with xX XAB have "x \<in> B" by auto
        with AB eA show ?thesis by auto
      qed
    }
    with eX show ?thesis by auto
  qed
qed

lemma closed_UN_well_founded:
  fixes r (infix "\<sqsubset>" 50)
  assumes XX: "\<forall>X\<in>XX. well_founded X (\<sqsubset>) \<and> (\<forall>x\<in>X. \<forall>y\<in>\<Union>XX. y \<sqsubset> x \<longrightarrow> y \<in> X)"
  shows "well_founded (\<Union>XX) (\<sqsubset>)"
proof (intro well_foundedI_extremal)
  have *: "X \<in> XX \<Longrightarrow> x\<in>X \<Longrightarrow> y \<in> \<Union>XX \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> y \<in> X" for X x y using XX by blast
  fix S
  assume S: "S \<subseteq> \<Union>XX" and S0: "S \<noteq> {}"
  from S0 obtain x where xS: "x \<in> S" by auto
  with S obtain X where X: "X \<in> XX" and xX: "x \<in> X" by auto
  from xS xX have Sx0: "S \<inter> X \<noteq> {}" by auto
  from X XX interpret well_founded X "(\<sqsubset>)" by auto
  from nonempty_imp_ex_extremal[OF _ Sx0]
  obtain z where zS: "z \<in> S" and zX: "z \<in> X" and min: "\<forall>y \<in> S \<inter> X. \<not> y \<sqsubset> z" by auto
  show "\<exists>x\<in>S. \<forall>y\<in>S. \<not> y \<sqsubset> x"
  proof (intro bexI[OF _ zS] ballI notI)
    fix y
    assume yS: "y \<in> S" and yz: "y \<sqsubset> z"
    have yXX: "y \<in> \<Union> XX" using S yS by auto
    from *[OF X zX yXX yz] yS have "y \<in> X \<inter> S" by auto
    with min yz show False by auto
  qed
qed

lemma well_founded_cmono:
  assumes r': "r' \<le> r" and wf: "well_founded A r"
  shows "well_founded A r'"
proof (intro well_foundedI_extremal)
  fix X assume "X \<subseteq> A" and "X \<noteq> {}"
  from well_founded.nonempty_imp_ex_extremal[OF wf this]
  show "\<exists>x\<in>X. \<forall>y\<in>X. \<not> r' y x" using r' by auto
qed

locale well_founded_ordered_set = well_founded + transitive _ "(\<sqsubset>)"
begin

sublocale strict_ordered_set..

interpretation Restrp: strict_ordered_set UNIV "(\<sqsubset>)\<restriction>A" + Restrp: well_founded UNIV "(\<sqsubset>)\<restriction>A"
  using Restrp_strict_order Restrp_well_founded .

lemma Restrp_well_founded_order: "well_founded_ordered_set UNIV ((\<sqsubset>)\<restriction>A)"..

lemma well_founded_ordered_subset: "B \<subseteq> A \<Longrightarrow> well_founded_ordered_set B (\<sqsubset>)"
  apply intro_locales
  using well_founded_subset transitive_subset by auto

end

lemma (in well_founded) Restrp_tranclp_well_founded_ordered: "well_founded_ordered_set UNIV ((\<sqsubset>)\<restriction>A)\<^sup>+\<^sup>+"
  using Restrp_tranclp_well_founded tranclp_transitive by intro_locales

locale well_related_set = related_set +
  assumes nonempty_imp_ex_extreme: "X \<subseteq> A \<Longrightarrow> X \<noteq> {} \<Longrightarrow> \<exists>e. extreme X (\<sqsubseteq>)\<^sup>- e"
begin

sublocale connex
proof
  fix x y assume "x \<in> A" and "y \<in> A"
  with nonempty_imp_ex_extreme[of "{x,y}"] show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by auto 
qed

lemmas connex_axioms = connex_axioms

interpretation less_eq_notations.

sublocale asym: well_founded A "(\<sqsubset>)"
proof (unfold well_founded_iff_ex_extremal, intro allI impI)
  fix X
  assume XA: "X \<subseteq> A" and X0: "X \<noteq> {}"
  from nonempty_imp_ex_extreme[OF XA X0] obtain e where "extreme X (\<sqsubseteq>)\<^sup>- e" by auto
  then show "\<exists>x\<in>X. \<forall>z\<in>X. \<not>z \<sqsubset> x" by (auto intro!: bexI[of _ e])
qed

lemma well_related_subset: "B \<subseteq> A \<Longrightarrow> well_related_set B (\<sqsubseteq>)"
  by (auto intro!: well_related_set.intro nonempty_imp_ex_extreme)

end

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma well_related_iff_neg_well_founded:
  "well_related_set A (\<sqsubseteq>) \<longleftrightarrow> well_founded A (\<lambda>x y. \<not> y \<sqsubseteq> x)"
  by (simp add: well_related_set_def well_founded_iff_ex_extremal extreme_def Bex_def)

lemma well_related_singleton_refl: 
  assumes "x \<sqsubseteq> x" shows "well_related_set {x} (\<sqsubseteq>)"
  by (intro well_related_set.intro exI[of _ x], auto simp: subset_singleton_iff assms)

lemma closed_UN_well_related:
  assumes XX: "\<forall>X\<in>XX. well_related_set X (\<sqsubseteq>) \<and> (\<forall>x\<in>X. \<forall>y\<in>\<Union>XX. \<not>x \<sqsubseteq> y \<longrightarrow> y \<in> X)"
  shows "well_related_set (\<Union>XX) (\<sqsubseteq>)"
  using XX
  apply (unfold well_related_iff_neg_well_founded)
  using closed_UN_well_founded[of _ "\<lambda>x y. \<not> y \<sqsubseteq> x"].

end

lemma well_related_extend:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes "well_related_set A (\<sqsubseteq>)" and "well_related_set B (\<sqsubseteq>)" and "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b"
  shows "well_related_set (A \<union> B) (\<sqsubseteq>)"
  using well_founded_extend[of _ "\<lambda>x y. \<not> y \<sqsubseteq> x", folded well_related_iff_neg_well_founded]
  using assms by auto

locale pre_well_ordered_set = semiattractive + well_related_set
begin

interpretation less_eq_notations.

sublocale transitive
proof
  fix x y z assume xy: "x \<sqsubseteq> y" and yz: "y \<sqsubseteq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  from x y z have "\<exists>e. extreme {x,y,z} (\<sqsupseteq>) e" (is "\<exists>e. ?P e") by (auto intro!: nonempty_imp_ex_extreme)
  then have "?P x \<or> ?P y \<or> ?P z" by auto
  then show "x \<sqsubseteq> z"
  proof (elim disjE)
    assume "?P x"
    then show ?thesis by auto
  next
    assume "?P y"
    then have "y \<sqsubseteq> x" by auto
    from attract[OF xy this yz] x y z show ?thesis by auto
  next
    assume "?P z"
    then have zx: "z \<sqsubseteq> x" and zy: "z \<sqsubseteq> y" by auto
    from attract[OF yz zy zx] x y z have yx: "y \<sqsubseteq> x" by auto
    from attract[OF xy yx yz] x y z show ?thesis by auto
  qed
qed

sublocale total_quasi_ordered_set..

lemmas connex_axioms = connex_axioms

lemma strict_weak_trans[trans]:
  assumes xy: "x \<sqsubset> y" and yz: "y \<sqsubseteq> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubset> z"
proof (intro asympartpI notI)
  from trans xy yz x y z show "x \<sqsubseteq> z" by auto
  assume "z \<sqsubseteq> x"
  from trans[OF yz this] y z x have "y \<sqsubseteq> x" by auto
  with xy show False by auto
qed

lemma weak_strict_trans[trans]:
  assumes xy: "x \<sqsubseteq> y" and yz: "y \<sqsubset> z" and x: "x \<in> A" and y: "y \<in> A" and z: "z \<in> A"
  shows "x \<sqsubset> z"
proof (intro asympartpI notI)
  from trans xy yz x y z show "x \<sqsubseteq> z" by auto
  assume "z \<sqsubseteq> x"
  from trans[OF this xy] z x y have "z \<sqsubseteq> y" by auto
  with yz show False by auto
qed

end

lemma pre_well_ordered_iff:
  "pre_well_ordered_set A r \<longleftrightarrow> total_quasi_ordered_set A r \<and> well_founded A (asympartp r)"
  (is "?p \<longleftrightarrow> ?t \<and> ?w")
proof safe
  assume ?p
  then interpret pre_well_ordered_set A r.
  show ?t ?w by unfold_locales
next
  assume ?t
  then interpret total_quasi_ordered_set A r.
  assume ?w
  then have "well_founded UNIV (asympartp r \<restriction> A)" by simp
  also have "asympartp r \<restriction> A = (\<lambda>x y. \<not> r y x) \<restriction> A" by (intro ext, auto simp: not_iff_asym)
  finally have "well_related_set A r" by (simp add: well_related_iff_neg_well_founded)
  then show ?p by intro_locales
qed

lemma (in semiattractive) pre_well_ordered_iff_well_related:
  assumes XA: "X \<subseteq> A"
  shows "pre_well_ordered_set X (\<sqsubseteq>) \<longleftrightarrow> well_related_set X (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof
  interpret X: semiattractive X using semiattractive_subset[OF XA].
  { assume ?l
    then interpret X: pre_well_ordered_set X.
    show ?r by unfold_locales
  }
  assume ?r
  then interpret X: well_related_set X.
  show ?l by unfold_locales
qed

lemma semiattractive_extend:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes A: "semiattractive A (\<sqsubseteq>)" and B: "semiattractive B (\<sqsubseteq>)"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b \<and> \<not> b \<sqsubseteq> a"
  shows "semiattractive (A \<union> B) (\<sqsubseteq>)"
proof-
  interpret A: semiattractive A "(\<sqsubseteq>)" using A.
  interpret B: semiattractive B "(\<sqsubseteq>)" using B.
  {
    fix x y z
    assume yB: "y \<in> B" and zA: "z \<in> A" and yz: "y \<sqsubseteq> z"
    have False using AB[rule_format, OF zA yB] yz by auto
  }
  note * = this
  show ?thesis 
    by (auto intro!: semiattractive.intro dest:* AB[rule_format] A.attract B.attract)
qed

lemma pre_well_order_extend:
  fixes r (infix "\<sqsubseteq>" 50)
  assumes A: "pre_well_ordered_set A (\<sqsubseteq>)" and B: "pre_well_ordered_set B (\<sqsubseteq>)"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b \<and> \<not> b \<sqsubseteq> a"
  shows "pre_well_ordered_set (A\<union>B) (\<sqsubseteq>)"
proof-
  interpret A: pre_well_ordered_set A "(\<sqsubseteq>)" using A.
  interpret B: pre_well_ordered_set B "(\<sqsubseteq>)" using B.
  show ?thesis
    apply (intro pre_well_ordered_set.intro well_related_extend semiattractive_extend)
    apply unfold_locales
    by (auto dest: AB[rule_format])
qed

locale well_ordered_set = antisymmetric + well_related_set
begin

sublocale pre_well_ordered_set..

sublocale total_ordered_set..

lemma well_ordered_subset: "B \<subseteq> A \<Longrightarrow> well_ordered_set B (\<sqsubseteq>)"
  using well_related_subset antisymmetric_subset by (intro well_ordered_set.intro)

lemmas connex_axioms = connex_axioms

end

lemma (in antisymmetric) well_ordered_iff_well_related:
  assumes XA: "X \<subseteq> A"
  shows "well_ordered_set X (\<sqsubseteq>) \<longleftrightarrow> well_related_set X (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof
  interpret X: antisymmetric X using antisymmetric_subset[OF XA].
  { assume ?l
    then interpret X: well_ordered_set X.
    show ?r by unfold_locales
  }
  assume ?r
  then interpret X: well_related_set X.
  show ?l by unfold_locales
qed

context
  fixes A and less_eq (infix "\<sqsubseteq>" 50)
  assumes A: "\<forall>a \<in> A. \<forall>b \<in> A. a \<sqsubseteq> b"
begin

interpretation well_related_set A "(\<sqsubseteq>)"
  apply unfold_locales
  using A by blast

lemmas trivial_well_related = well_related_set_axioms

lemma trivial_pre_well_order: "pre_well_ordered_set A (\<sqsubseteq>)"
  apply unfold_locales
  using A by blast

end

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

interpretation less_eq_notations.

lemma well_order_extend:
  assumes A: "well_ordered_set A (\<sqsubseteq>)" and B: "well_ordered_set B (\<sqsubseteq>)"
    and ABa: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b \<longrightarrow> b \<sqsubseteq> a \<longrightarrow> a = b"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b"
  shows "well_ordered_set (A\<union>B) (\<sqsubseteq>)"
proof-
  interpret A: well_ordered_set A "(\<sqsubseteq>)" using A.
  interpret B: well_ordered_set B "(\<sqsubseteq>)" using B.
  show ?thesis
    apply (intro well_ordered_set.intro antisymmetric_union well_related_extend ABa AB)
    by unfold_locales
qed

interpretation singleton: antisymmetric "{a}" "(\<sqsubseteq>)" for a apply unfold_locales by auto

lemmas singleton_antisymmetric[intro!] = singleton.antisymmetric_axioms

lemma singleton_well_ordered[intro!]: "a \<sqsubseteq> a \<Longrightarrow> well_ordered_set {a} (\<sqsubseteq>)"
  apply unfold_locales by auto

lemma closed_UN_well_ordered:
  assumes anti: "antisymmetric (\<Union> XX) (\<sqsubseteq>)"
    and XX: "\<forall>X\<in>XX. well_ordered_set X (\<sqsubseteq>) \<and> (\<forall>x\<in>X. \<forall>y\<in>\<Union>XX. \<not> x \<sqsubseteq> y \<longrightarrow> y \<in> X)"
  shows "well_ordered_set (\<Union>XX) (\<sqsubseteq>)"
  apply (intro well_ordered_set.intro closed_UN_well_related anti)
  using XX well_ordered_set.axioms by fast

end

text \<open>Directed sets:\<close>

definition "directed A r \<equiv> \<forall>x \<in> A. \<forall>y \<in> A. \<exists>z \<in> A. r x z \<and> r y z"

lemmas directedI[intro] = directed_def[unfolded atomize_eq, THEN iffD2, rule_format]

lemmas directedD = directed_def[unfolded atomize_eq, THEN iffD1, rule_format]

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma directedE:
  assumes "directed A (\<sqsubseteq>)" and "x \<in> A" and "y \<in> A"
    and "\<And>z. z \<in> A \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> thesis"
  shows "thesis"
  using assms by (auto dest: directedD)

lemma directed_empty[simp]: "directed {} (\<sqsubseteq>)" by auto

lemma directed_union:
  assumes dX: "directed X (\<sqsubseteq>)" and dY: "directed Y (\<sqsubseteq>)"
    and XY: "\<forall>x\<in>X. \<forall>y\<in>Y. \<exists>z \<in> X \<union> Y. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  shows "directed (X \<union> Y) (\<sqsubseteq>)"
  using directedD[OF dX] directedD[OF dY] XY
  apply (intro directedI) by blast

lemma directed_extend:
  assumes X: "directed X (\<sqsubseteq>)" and Y: "directed Y (\<sqsubseteq>)" and XY: "\<forall>x\<in>X. \<forall>y\<in>Y. x \<sqsubseteq> y"
  shows "directed (X \<union> Y) (\<sqsubseteq>)"
proof -
  { fix x y
    assume xX: "x \<in> X" and yY: "y \<in> Y"
    let ?g = "\<exists>z\<in>X \<union> Y. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
    from directedD[OF Y yY yY] obtain z where zY: "z \<in> Y" and yz: "y \<sqsubseteq> z" by auto
    from xX XY zY yz have ?g by auto
  }
  then show ?thesis by (auto intro!: directed_union[OF X Y])
qed

end

context connex begin

lemma directed: "directed A (\<sqsubseteq>)"
proof
  fix x y
  assume x: "x \<in> A" and y: "y \<in> A"
  then show "\<exists>z\<in>A. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  proof (cases rule: comparable_cases)
    case le
    with refl[OF y] y show ?thesis by (intro bexI[of _ y], auto)
  next
    case ge
    with refl[OF x] x show ?thesis by (intro bexI[of _ x], auto)
  qed
qed

end

context
  fixes ir :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<preceq>" 50)
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma monotone_connex_image:
  assumes mono: "monotone_on I (\<preceq>) (\<sqsubseteq>) f"
  assumes connex: "connex I (\<preceq>)"
  shows "connex (f ` I) (\<sqsubseteq>)"
proof (rule connexI)
  fix x y
  assume "x \<in> f ` I" and "y \<in> f ` I"
  then obtain i j where ij: "i \<in> I" "j \<in> I" and [simp]: "x = f i" "y = f j" by auto
  from connex ij have "i \<preceq> j \<or> j \<preceq> i" by (auto elim: connexE)
  with ij mono show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by (elim disjE, auto dest: monotone_onD) 
qed

lemma monotone_directed_image:
  assumes mono: "monotone_on I (\<preceq>) (\<sqsubseteq>) f"
  assumes dir: "directed I (\<preceq>)" shows "directed (f ` I) (\<sqsubseteq>)"
proof (rule directedI, safe)
  fix x y assume x: "x \<in> I" and y: "y \<in> I"
  with dir obtain z where z: "z \<in> I" and "x \<preceq> z" and "y \<preceq> z" by (auto elim: directedE)
  with mono x y have "f x \<sqsubseteq> f z" and "f y \<sqsubseteq> f z" by (auto dest: monotone_onD)
  with z show "\<exists>fz \<in> f ` I. f x \<sqsubseteq> fz \<and> f y \<sqsubseteq> fz" by auto
qed

end

subsection \<open>Order Pairs\<close>

locale compatible = related_set + related_set A "(\<sqsubset>)" for less (infix "\<sqsubset>" 50) +
  assumes compat_right[trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubset> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubset> z"
  assumes compat_left[trans]: "x \<sqsubset> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubset> z"

locale compatible_ordering = reflexive + irreflexive + compatible +
  assumes strict_implies_weak: "x \<sqsubset> y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<sqsubseteq> y"
begin

text \<open>The strict part is necessarily transitive.\<close>

text \<open>The following sequence of declarations are in order to obtain fact names in a manner
similar to the Isabelle/HOL facts of orders.\<close>

sublocale strict: transitive A "(\<sqsubset>)"
  using compat_right[OF strict_implies_weak] by unfold_locales

sublocale strict_ordered_set A "(\<sqsubset>)" ..

thm strict.trans asym irrefl

lemma strict_implies_not_weak: "x \<sqsubset> y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<not> y \<sqsubseteq> x"
  using irrefl compat_left by blast

end

context transitive begin

interpretation less_eq_notations.

lemma asym_trans[trans]:
  shows "x \<sqsubset> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubset> z"
    and "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubset> z \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> x \<sqsubset> z"
  by (auto 0 3 dest: trans)

end

locale attractive_ordering = compatible_ordering + attractive

locale pseudo_ordering = compatible_ordering + pseudo_ordered_set
begin

sublocale attractive_ordering ..

end

locale quasi_ordering = compatible_ordering + quasi_ordered_set
begin

sublocale attractive_ordering ..

end

locale partial_ordering = compatible_ordering + partially_ordered_set
begin

sublocale pseudo_ordering + quasi_ordering ..

end

locale well_founded_ordering = quasi_ordering + well_founded

locale total_ordering = compatible_ordering + total_ordered_set
begin

sublocale partial_ordering ..

end

locale strict_total_ordering = partial_ordering + semiconnex A "(\<sqsubset>)"
begin

sublocale semiconnex_irreflexive ..

sublocale connex
proof
  fix x y assume x: "x \<in> A" and y: "y \<in> A"
  then show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
    apply (cases rule: cases[OF x y])
    by (auto dest: strict_implies_weak)
qed

sublocale total_ordering ..
(*
sublocale old: ordering "(\<sqsubseteq>)" "(\<sqsubset>)"
proof-
  have "a \<sqsubseteq> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<sqsubset> b" for a b
    by (cases a b rule: cases, auto dest: strict_implies_weak)
  then show "ordering (\<sqsubseteq>) (\<sqsubset>)"
    by (unfold_locales, auto dest:strict_implies_weak trans)
qed
*)

lemma not_weak[simp]:
  assumes "x \<in> A" and "y \<in> A" shows "\<not> x \<sqsubseteq> y \<longleftrightarrow> y \<sqsubset> x"
  using assms by (cases rule:cases, auto simp: strict_implies_not_weak dest: strict_implies_weak)

lemma not_strict[simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> \<not> x \<sqsubset> y \<longleftrightarrow> y \<sqsubseteq> x"
  using not_weak by blast

end

subsection \<open>Relating to Classes\<close>

text \<open>In Isabelle 2020, we should declare sublocales in class before declaring dual
sublocales, since otherwise facts would be prefixed by ``dual.dual.''\<close>

context ord begin

abbreviation least where "least X \<equiv> extreme X (\<lambda>x y. y \<le> x)"

abbreviation greatest where "greatest X \<equiv> extreme X (\<le>)"

abbreviation supremum where "supremum X \<equiv> least (Collect (bound X (\<le>)))"

abbreviation infimum where "infimum X \<equiv> greatest (Collect (bound X (\<lambda>x y. y \<le> x)))"

lemma Least_eq_The_least: "Least P = The (least {x. P x})"
  by (auto simp: Least_def extreme_def[unfolded atomize_eq, THEN ext])

lemma Greatest_eq_The_greatest: "Greatest P = The (greatest {x. P x})"
  by (auto simp: Greatest_def extreme_def[unfolded atomize_eq, THEN ext])

end

lemma Ball_UNIV[simp]: "Ball UNIV = All" by auto
lemma Bex_UNIV[simp]: "Bex UNIV = Ex" by auto

class compat = ord + assumes "compatible_ordering UNIV (\<le>) (<)"
begin

sublocale order: compatible_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  using compat_axioms unfolding class.compat_def by (auto 0 4 simp:atomize_eq)

end

text \<open>We should have imported locale-based facts in classes, e.g.:\<close>
thm order.trans order.strict.trans order.refl order.irrefl order.asym order.extreme_bound_singleton

class attractive_order = ord + assumes "attractive_ordering UNIV (\<le>) (<)"
begin

text \<open>We need to declare subclasses before sublocales in order to preserve facts for superclasses.\<close>

interpretation attractive_ordering UNIV
  using attractive_order_axioms unfolding class.attractive_order_def.

subclass compat ..

sublocale order: attractive_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

thm order.extreme_bound_quasi_const

class psorder = ord + assumes "pseudo_ordering UNIV (\<le>) (<)"
begin

interpretation pseudo_ordering UNIV using psorder_axioms unfolding class.psorder_def.

subclass attractive_order ..

sublocale order: pseudo_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

class qorder = ord + assumes "quasi_ordering UNIV (\<le>) (<)"
begin

interpretation quasi_ordering UNIV using qorder_axioms unfolding class.qorder_def.

subclass attractive_order ..

sublocale order: quasi_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

class porder = ord + assumes "partial_ordering UNIV (\<le>) (<)"
begin

interpretation partial_ordering UNIV
  using porder_axioms unfolding class.porder_def.

subclass psorder ..
subclass qorder ..

sublocale order: partial_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

class wf_qorder = ord + assumes "well_founded_ordering UNIV (\<le>) (<)"
begin

interpretation well_founded_ordering UNIV
  using wf_qorder_axioms unfolding class.wf_qorder_def.

subclass qorder ..

sublocale order: well_founded_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

class totalorder = ord + assumes "total_ordering UNIV (\<le>) (<)"
begin

interpretation total_ordering UNIV
  using totalorder_axioms unfolding class.totalorder_def.

subclass porder ..

sublocale order: total_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

text \<open>Isabelle/HOL's @{class preorder} belongs to @{class qorder}, but not vice versa.\<close>

subclass (in preorder) qorder
  apply unfold_locales
  using order_refl apply assumption
  apply simp
  using le_less_trans apply assumption
  using less_le_trans apply assumption
  using less_imp_le apply assumption
  using  order_trans apply assumption
  done

subclass (in order) porder by (unfold_locales, auto)

subclass (in wellorder) wf_qorder
  apply (unfold_locales)
  using less_induct by auto

text \<open>Isabelle/HOL's @{class linorder} is equivalent to our locale @{locale strict_total_ordering}.\<close>

context linorder begin

interpretation strict_total_ordering UNIV
  apply unfold_locales by auto

subclass totalorder ..

sublocale order: strict_total_ordering UNIV
  rewrites "\<And>x. x \<in> UNIV \<equiv> True"
    and "\<And>X. X \<subseteq> UNIV \<equiv> True"
    and "\<And>r. r \<restriction> UNIV \<equiv> r"
    and "\<And>P. True \<and> P \<equiv> P"
    and "Ball UNIV \<equiv> All"
    and "Bex UNIV \<equiv> Ex"
    and "sympartp (\<le>)\<^sup>- \<equiv> sympartp (\<le>)"
    and "\<And>P1. (True \<Longrightarrow> PROP P1) \<equiv> PROP P1"
    and "\<And>P1. (True \<Longrightarrow> P1) \<equiv> Trueprop P1"
    and "\<And>P1 P2. (True \<Longrightarrow> PROP P1 \<Longrightarrow> PROP P2) \<equiv> (PROP P1 \<Longrightarrow> PROP P2)"
  apply unfold_locales by (auto simp:atomize_eq)

end

text \<open>Tests: facts should be available in the most general classes.\<close>

thm order.strict.trans[where 'a="'a::compat"]
thm order.extreme_bound_quasi_const[where 'a="'a::attractive_order"]
thm order.extreme_bound_singleton_eq[where 'a="'a::psorder"]
thm order.trans[where 'a="'a::qorder"]
thm order.comparable_cases[where 'a="'a::totalorder"]
thm order.cases[where 'a="'a::linorder"]

subsection \<open>Declaring Duals\<close>

sublocale reflexive \<subseteq> sym: reflexive A "sympartp (\<sqsubseteq>)"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- \<equiv> sympartp (\<sqsubseteq>)"
    and "\<And>r. sympartp (sympartp r) \<equiv> sympartp r"
    and "\<And>r. sympartp r \<restriction> A \<equiv> sympartp (r \<restriction> A)"
  by (auto 0 4 simp:atomize_eq)

sublocale quasi_ordered_set \<subseteq> sym: quasi_ordered_set A "sympartp (\<sqsubseteq>)"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
    and "sympartp (sympartp (\<sqsubseteq>)) = sympartp (\<sqsubseteq>)"
   apply unfold_locales by (auto 0 4 dest: trans)
  
text \<open>At this point, we declare dual as sublocales.
In the following, ``rewrites'' eventually cleans up redundant facts.\<close>

sublocale reflexive \<subseteq> dual: reflexive A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- \<equiv> sympartp (\<sqsubseteq>)"
    and "\<And>r. sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
    and "(\<sqsubseteq>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubseteq>) \<restriction> A)\<^sup>-"
  by (auto simp: atomize_eq)

context attractive begin

interpretation less_eq_notations.

sublocale dual: attractive A "(\<sqsupseteq>)"
  rewrites "sympartp (\<sqsupseteq>) = (\<sim>)"
    and "equivpartp (\<sqsupseteq>) \<equiv> (\<simeq>)"
    and "\<And>r. sympartp (r \<restriction> A) \<equiv> sympartp r \<restriction> A"
    and "\<And>r. sympartp (sympartp r) \<equiv> sympartp r"
    and "(\<sqsubseteq>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubseteq>) \<restriction> A)\<^sup>-"
  apply unfold_locales by (auto intro!: ext dest: attract dual.attract simp: atomize_eq)

end

context irreflexive begin

sublocale dual: irreflexive A "(\<sqsubset>)\<^sup>-"
  rewrites "(\<sqsubset>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubset>) \<restriction> A)\<^sup>-"
  apply unfold_locales by (auto dest: irrefl simp: atomize_eq)

end

sublocale transitive \<subseteq> dual: transitive A "(\<sqsubseteq>)\<^sup>-"
  rewrites "(\<sqsubseteq>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubseteq>) \<restriction> A)\<^sup>-"
    and "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
    and "asympartp (\<sqsubseteq>)\<^sup>- = (asympartp (\<sqsubseteq>))\<^sup>-"
  apply unfold_locales by (auto dest: trans simp: atomize_eq intro!:ext)

sublocale antisymmetric \<subseteq> dual: antisymmetric A "(\<sqsubseteq>)\<^sup>-"
  rewrites "(\<sqsubseteq>)\<^sup>- \<restriction> A \<equiv> ((\<sqsubseteq>) \<restriction> A)\<^sup>-"
    and "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by (auto dest: antisym simp: atomize_eq)

sublocale semiconnex \<subseteq> dual: semiconnex A "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubset>)\<^sup>- = sympartp (\<sqsubset>)"
  using semiconnex by auto

sublocale connex \<subseteq> dual: connex A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by (auto intro!: chainI dest:comparable)

sublocale semiconnex_irreflexive \<subseteq> dual: semiconnex_irreflexive A "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubset>)\<^sup>- = sympartp (\<sqsubset>)"
  by unfold_locales auto

sublocale pseudo_ordered_set \<subseteq> dual: pseudo_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

sublocale quasi_ordered_set \<subseteq> dual: quasi_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale partially_ordered_set \<subseteq> dual: partially_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

sublocale total_pseudo_ordered_set \<subseteq> dual: total_pseudo_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

sublocale total_quasi_ordered_set \<subseteq> dual: total_quasi_ordered_set A "(\<sqsubseteq>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale compatible_ordering \<subseteq> dual: compatible_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  apply unfold_locales
  by (auto dest: compat_left compat_right strict_implies_weak)

sublocale attractive_ordering \<subseteq> dual: attractive_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale pseudo_ordering \<subseteq> dual: pseudo_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

sublocale quasi_ordering \<subseteq> dual: quasi_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales auto

sublocale partial_ordering \<subseteq> dual: partial_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

sublocale total_ordering \<subseteq> dual: total_ordering A "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  rewrites "sympartp (\<sqsubseteq>)\<^sup>- = sympartp (\<sqsubseteq>)"
  by unfold_locales (auto 0 4)

lemma(in antisymmetric) monotone_extreme_imp_extreme_bound_iff:
  fixes ir (infix "\<preceq>" 50)
  assumes "f ` C \<subseteq> A" and "monotone_on C (\<preceq>) (\<sqsubseteq>) f" and i: "extreme C (\<preceq>) i"
  shows "extreme_bound A (\<sqsubseteq>) (f ` C) x \<longleftrightarrow> f i = x"
  using dual.extreme_unique monotone_extreme_extreme_boundI[OF assms] by auto


subsection \<open>Instantiations\<close>

text \<open>Finally, we instantiate our classes for sanity check.\<close>

instance nat :: linorder ..

text \<open>Pointwise ordering of functions are compatible only if the weak part is transitive.\<close>

instance "fun" :: (type,qorder) compat
proof (intro_classes, unfold_locales)
  note [simp] = le_fun_def less_fun_def
  fix f g h :: "'a \<Rightarrow> 'b"
  { assume fg: "f \<le> g" and gh: "g < h"
    show "f < h"
    proof (unfold less_fun_def, intro conjI le_funI notI)
      from fg have "f x \<le> g x" for x by auto
      also from gh have "g x \<le> h x" for x by auto
      finally (order.trans) show "f x \<le> h x" for x.
      assume hf: "h \<le> f"
      then have "h x \<le> f x" for x by auto
      also from fg have "f x \<le> g x" for x by auto
      finally have "h \<le> g" by auto
      with gh show False by auto
    qed
  }
  { assume fg: "f < g" and gh: "g \<le> h"
    show "f < h"
    proof (unfold less_fun_def, intro conjI le_funI notI)
      from fg have "f x \<le> g x" for x by auto
      also from gh have "g x \<le> h x" for x by auto
      finally show "f x \<le> h x" for x.
      from gh have "g x \<le> h x" for x by auto
      also assume hf: "h \<le> f"
      then have "h x \<le> f x" for x by auto
      finally have "g \<le> f" by auto
      with fg show False by auto
    qed
  }
  show "f < g \<Longrightarrow> f \<le> g" by auto
  show "\<not>f < f" by auto
  show "f \<le> f" by auto
qed

instance "fun" :: (type,qorder) qorder
  apply intro_classes
  apply unfold_locales
  by (auto simp: le_fun_def dest: order.trans)

instance "fun" :: (type,porder) porder
  apply intro_classes
  apply unfold_locales
proof (intro ext)
  fix f g :: "'a \<Rightarrow> 'b" and x :: 'a
  assume fg: "f \<le> g" and gf: "g \<le> f"
  then have "f x \<le> g x" and "g x \<le> f x" by (auto elim: le_funE)
  from order.antisym[OF this] show "f x = g x" by auto
qed

end
