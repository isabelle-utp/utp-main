(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Action Algebras *}

theory Action_Algebra
imports Kleene_Algebra
begin

text {* Action algebras have been defined and discussed in Vaughan
Pratt's paper on \emph{Action Logic and Pure
Induction}~\cite{pratt90action}. They are expansions of Kleene
algebras by operations of left and right residuation. They are
interesting, first because most models of Kleene algebras, e.g.
relations, traces, paths and languages, possess the residuated
structure, and second because, in this setting, the Kleene star can be
equationally defined.

Action algebras can be based on residuated
semilattices~\cite{galatosjipsenkowalskiono07residuated}, which are
interesting in their own right. Many important properties of action
algebras already arise at this level.

Here we only prove some basic properties of residuated semilattices
and action algebras. A more extensive treatment is left for future
work. There is also an obvious duality between proofs for left and
right residuation which we do not formalise at this stage. *}

class residuated_join_semilattice = join_semilattice + semigroup_mult + residual_l_op + residual_r_op +
  assumes residual_l_galois: "x \<le> z \<leftarrow> y \<longleftrightarrow> x \<cdot> y \<le> z"
  and residual_r_galois: "x \<cdot> y \<le> z \<longleftrightarrow> y \<le> x \<rightarrow> z"
begin

text {* We first prove unit and counit laws for residuals, which are
also known as cancellation laws. *}

lemma galois_unitl: "x \<le> x \<cdot> y \<leftarrow> y"
  by (metis eq_refl residual_l_galois)

lemma galois_counitl: "(y \<leftarrow> x) \<cdot> x \<le> y"
  by (metis eq_refl residual_l_galois)

lemma galois_unitr: "y \<le> x \<rightarrow> x \<cdot> y"
  by (metis eq_refl residual_r_galois)

lemma galois_counitr: "x \<cdot> (x \<rightarrow> y) \<le> y"
  by (metis eq_refl residual_r_galois)

text {* Next we show that distributivity laws hold (in fact, even
distributivity laws for all existing suprema). *}

lemma distl: "x \<cdot> (y + z) = x \<cdot> y + x \<cdot> z"
proof -
  {
    fix w
    have "x \<cdot> (y + z) \<le> w \<longleftrightarrow> y + z \<le> x \<rightarrow> w"
      by (metis residual_r_galois)
    also have "... \<longleftrightarrow> y \<le> x \<rightarrow> w \<and> z \<le> x \<rightarrow> w"
      by (fact add_lub)
    also have "... \<longleftrightarrow> x \<cdot> y \<le> w \<and> x \<cdot> z \<le> w"
      by (metis residual_r_galois)
    ultimately have"x \<cdot> (y + z) \<le> w \<longleftrightarrow> x \<cdot> y + x \<cdot> z \<le> w"
      by (metis add_lub)
  }
  thus ?thesis
    by (metis eq_iff)
qed

lemma distr: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"
proof -
  {
    fix w
    have "(x + y) \<cdot> z \<le> w \<longleftrightarrow> x + y \<le> w \<leftarrow> z"
      by (metis residual_l_galois)
    also have "... \<longleftrightarrow> x \<le> w \<leftarrow> z \<and> y \<le> w \<leftarrow> z"
      by (fact add_lub)
    also have "... \<longleftrightarrow> x \<cdot> z \<le> w \<and> y \<cdot> z \<le> w"
      by (metis residual_l_galois)
    ultimately have"(x + y) \<cdot> z \<le> w \<longleftrightarrow> x \<cdot> z + y \<cdot> z \<le> w"
      by (metis add_lub)
  }
  thus ?thesis
    by (metis eq_iff)
qed

text {* As usual, distributivity implies isotonicity. *}

lemma mult_isol: "x \<le> y \<longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  by (metis distl less_eq_def)

lemma mult_isor: "x \<le> y \<longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  by (metis distr less_eq_def)

text {* Similarly, the residuals as upper adjoints preserve all
existing meets, but we do not assume that any meets exist in
residuated semilattices. However we can show subdistributivity with
respect to residuation. *}

lemma residual_l_subdist_var: "x \<leftarrow> z \<le> (x + y) \<leftarrow> z"
proof -
  {
    fix w
    have "w \<le> x \<leftarrow> z \<longleftrightarrow> w \<cdot> z \<le> x"
      by (metis residual_l_galois)
    also have "... \<longrightarrow> w \<cdot> z \<le> x + y"
      by (metis add_ub1 order_trans)
    ultimately have "w \<le> x \<leftarrow> z \<longrightarrow> w \<le> (x + y) \<leftarrow> z"
      by (metis residual_l_galois)
  }
  thus ?thesis
    by (metis eq_refl)
qed

lemma residual_l_subdist: "(x \<leftarrow> z) + (y \<leftarrow> z) \<le> (x + y) \<leftarrow> z"
  by (metis add_comm add_lub residual_l_subdist_var)

lemma residual_r_subdist_var: "(x \<rightarrow> y) \<le> x \<rightarrow> (y + z)"
  by (metis add_ub1 galois_counitr order_trans residual_r_galois)

lemma residual_r_subdist: "(x \<rightarrow> y) + (x \<rightarrow> z) \<le> x \<rightarrow> (y + z)"
  by (metis add_comm add_lub residual_r_subdist_var)

text {* As usual, subdistributivity implies isotonicity. *}

lemma residual_l_isol: "x \<le> y \<longrightarrow> x \<leftarrow> z \<le> y \<leftarrow> z"
  by (metis less_eq_def residual_l_subdist_var)

lemma residual_r_isor: "x \<le> y \<longrightarrow> z \<rightarrow> x \<le> z \<rightarrow> y"
  by (metis less_eq_def residual_r_subdist_var)

text {* Next, we prove superdistributivity laws for residuation. *}

lemma residual_l_superdist_var: "x \<leftarrow> (y + z) \<le> x \<leftarrow> y"
proof -
  {
    fix w
    have "w \<le> x \<leftarrow> (y + z) \<longleftrightarrow> w \<cdot> (y + z) \<le> x"
      by (metis residual_l_galois)
     also have "... \<longleftrightarrow> w \<cdot> y \<le> x \<and> w \<cdot> z \<le> x"
       by (metis add_lub distl)
     also have "... \<longleftrightarrow> w \<le> x \<leftarrow> y \<and> w \<le> x \<leftarrow> z"
       by (metis residual_l_galois)
    finally have "w \<le> x \<leftarrow> (y + z) \<longrightarrow> w \<le> x \<leftarrow> y"
      by simp
  }
  thus ?thesis
    by (metis eq_refl)
qed

lemma residual_r_superdist_var: "(x + y) \<rightarrow> z \<le> x \<rightarrow> z"
  by (metis add_lub galois_counitr residual_l_galois residual_r_galois)

text {* The previous proof shows, in fact, that @{text "x \<leftarrow> (y + z)"}
is the infimum of @{text "x \<leftarrow> y"} and @{text "x \<leftarrow> z"}; but we have no
operation to express this fact in action algebra. A dual property
holds for right residuation. *}

text {* As usual, superdistributivity implies antitonicity. *}

lemma residual_l_antitoner: "x \<le> y \<longrightarrow> z \<leftarrow> y \<le> z \<leftarrow> x"
  by (metis less_eq_def residual_l_superdist_var)

lemma residual_r_antitonel: "x \<le> y \<longrightarrow> y \<rightarrow> z \<le> x \<rightarrow> z"
  by (metis less_eq_def residual_r_superdist_var)

text {* Finally we prove transitivity laws for residuals. *}

lemma residual_l_trans: "(x \<leftarrow> y) \<cdot> (y \<leftarrow> z) \<le> x \<leftarrow> z"
proof -
  have "(x \<leftarrow> y) \<cdot> y \<le> x"
    by (metis galois_counitl)
  hence "(x \<leftarrow> y) \<cdot> (y \<leftarrow> z) \<cdot> z \<le> x"
    by (metis galois_counitl mult.assoc residual_l_antitoner residual_l_galois)
  thus ?thesis
    by (metis residual_l_galois)
qed

lemma residual_r_trans: "(x \<rightarrow> y) \<cdot> (y \<rightarrow> z) \<le> x \<rightarrow> z"
proof -
  have "y \<cdot> (y \<rightarrow> z)  \<le> z"
    by (metis galois_counitr)
  hence "x \<cdot> (x \<rightarrow> y) \<cdot> (y \<rightarrow> z)  \<le> z"
    by (metis galois_counitr mult.assoc residual_r_antitonel residual_r_galois)
  thus ?thesis
    by (metis mult.assoc residual_r_galois)
qed

end (* residuated_join_semilattice *)

text {* We now present an equivalent equational axiomatisation of
residuated join semilattices, which is essentially derived from an
equational axiomatisation of Galois connections in algebras with
sufficient structure. This equivalence is the basis for establishing
the equivalence of the equational axiomatisation of action algebra and
that based on Galois connections.  *}

class equational_residuated_join_semilattice = join_semilattice + semigroup_mult + residual_l_op + residual_r_op +
  assumes mult_subdist: "z \<cdot> x \<le> z \<cdot> (x + y)"
  and mult_subdistr: "x \<cdot> z \<le> (x+y) \<cdot> z"
  and right_addition: "x \<rightarrow> y \<le> x \<rightarrow> (y + z)"
  and right_galois_counit: "x \<cdot> (x \<rightarrow> y) \<le> y"
  and right_galois_unit: "y \<le> x \<rightarrow> x \<cdot> y"
  and left_addition: "y \<leftarrow> x \<le> (y + z) \<leftarrow> x"
  and left_galois_counit: "(y \<leftarrow> x) \<cdot> x \<le> y"
  and left_galois_unit: "y \<le> y \<cdot> x \<leftarrow> x"
begin

lemma residual_l_galois': "x \<cdot> y \<le> z \<longleftrightarrow> x \<le> z \<leftarrow> y"
proof
  assume "x \<cdot> y \<le> z"
  hence "(x \<cdot> y) \<leftarrow> y \<le> z \<leftarrow> y"
    by (metis less_eq_def left_addition)
  thus "x \<le> z \<leftarrow> y"
    by (metis order_trans left_galois_unit)
next
  assume "x \<le> z \<leftarrow> y"
  hence "x \<cdot> y \<le> (z \<leftarrow> y) \<cdot> y"
    by (metis less_eq_def mult_subdistr)
  thus "x \<cdot> y \<le> z"
    by (metis order_trans left_galois_counit)
qed

lemma residual_r_galois': "x \<cdot> y \<le> z \<longleftrightarrow> y \<le> x \<rightarrow> z"
proof
  assume "x \<cdot> y \<le> z"
  hence "x \<rightarrow> (x \<cdot> y) \<le> x \<rightarrow> z"
    by (metis less_eq_def right_addition)
  thus "y \<le> x \<rightarrow> z"
    by (metis order_trans right_galois_unit)
next
  assume "y \<le> x \<rightarrow> z"
  hence "x \<cdot> y \<le> x \<cdot> (x \<rightarrow> z)"
    by (metis less_eq_def mult_subdist)
  thus "x \<cdot> y \<le> z"
    by (metis order_trans right_galois_counit)
qed

subclass residuated_join_semilattice
  by (unfold_locales, metis residual_l_galois', metis residual_r_galois')

end (* equational_residuated_join_semilattice *)

text {*
Conversely, every residuated join semilattice satisfies the axioms of
equational residuated join semilattices.

Because the subclass relation must be acyclic in Isabelle, we can
only establish this for the corresponding locales.
*}

sublocale residuated_join_semilattice \<subseteq> equational_residuated_join_semilattice
  by (unfold_locales, metis add_ub1 mult_isol, metis add_ub1 mult_isor, metis residual_r_subdist_var, metis galois_counitr, metis galois_unitr, metis residual_l_subdist_var, metis galois_counitl, metis galois_unitl)

text {* We can now define an action algebra as a residuated join
semilattice that is also a dioid. Following Pratt, we also add a star
operation that is axiomatised as a reflexive transitive closure
operation.
*}

class action_algebra = residuated_join_semilattice + dioid_one_zero + star_op +
  assumes star_rtc1: "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
  and star_rtc2: "1 + y \<cdot> y + x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
begin

text {* We first prove a reflexivity property for residuals. *}

lemma residual_r_refl: "1 \<le> x \<rightarrow> x"
proof -
  have "x \<le> x"
    by auto
  thus ?thesis
    by (metis mult_oner residual_r_galois)
qed

lemma residual_l_refl: "1 \<le> x \<leftarrow> x"
proof -
  have "x \<le> x"
    by auto
  thus ?thesis
    by (metis mult_onel residual_l_galois)
qed

text {* We now derive pure induction laws for residuals. *}

lemma residual_l_pure_induction: "(x \<leftarrow> x)\<^sup>\<star> \<le> x \<leftarrow> x"
proof -
  have "1 + (x \<leftarrow> x) \<cdot> (x \<leftarrow> x) + (x \<leftarrow> x) \<le> (x \<leftarrow> x)"
    by (metis add_lub eq_iff residual_l_refl residual_l_trans)
  thus ?thesis
    by (metis star_rtc2)
qed

lemma residual_r_pure_induction: "(x \<rightarrow> x)\<^sup>\<star> \<le> x \<rightarrow> x"
  by (metis add_lub eq_iff residual_r_refl residual_r_trans star_rtc2)

text {* Next we show that every action algebra is a Kleene
algebra. First, we derive the star unfold law and the star induction
laws in action algebra. Then we prove a subclass statement. *}

lemma star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
proof -
  have "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis add_lub mult_isor order_trans star_rtc1)
  thus ?thesis
    by (metis add_lub star_rtc1)
qed

lemma star_mon: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
proof
  assume "x \<le> y"
  hence "x \<le> y\<^sup>\<star>"
    by (metis add_lub order_trans star_rtc1)
  hence "1 + x + y\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> y\<^sup>\<star>"
    by (metis add_lub star_rtc1)
  thus "x\<^sup>\<star> \<le> y\<^sup>\<star>"
    by (metis add.assoc add.commute star_rtc2)
qed

lemma star_subdist': "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  by (metis add_ub1 star_mon)

lemma star_inductl: "z + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
proof
  assume "z + x \<cdot> y \<le> y"
  also have "z \<le> y"
    by (metis add_lub calculation)
  moreover have "x \<cdot> y \<le> y"
    by (metis add_lub calculation)
  hence "x \<le> y \<leftarrow> y"
    by (metis residual_l_galois)
  hence "x\<^sup>\<star> \<le> (y \<leftarrow> y)\<^sup>\<star>"
    by (metis star_mon)
  hence "x\<^sup>\<star> \<le> y \<leftarrow> y"
    by (metis order_trans residual_l_pure_induction)
  hence "x\<^sup>\<star> \<cdot> y \<le> y"
    by (metis residual_l_galois)
  thus "x\<^sup>\<star> \<cdot> z \<le> y"
    by (metis calculation mult_isol order_trans)
qed

lemma star_inductr: "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
proof
  assume "z + y \<cdot> x \<le> y"
  also have "z \<le> y"
    by (metis add_lub calculation)
  moreover have "y \<cdot> x \<le> y"
    by (metis add_lub calculation)
  hence "x \<le> y \<rightarrow> y"
    by (metis residual_r_galois)
  hence "x\<^sup>\<star> \<le> (y \<rightarrow> y)\<^sup>\<star>"
    by (metis star_mon)
  hence "x\<^sup>\<star> \<le> y \<rightarrow> y"
    by (metis order_trans residual_r_pure_induction)
  hence "y \<cdot> x\<^sup>\<star> \<le> y"
    by (metis residual_r_galois)
  thus "z \<cdot> x\<^sup>\<star> \<le> y"
    by (metis calculation mult_isor order_trans)
qed

subclass kleene_algebra
  by (unfold_locales, auto simp add: star_unfoldl star_inductl star_inductr)

end (* action_algebra *)


subsection {* Equational Action Algebras *}

text {* The induction axioms of Kleene algebras are universal Horn
formulas. This is unavoidable, because due to a well known result of
Redko, there is no finite equational axiomatisation for the equational
theory of regular expressions.

Action algebras, in contrast, admit a finite equational
axiomatization, as Pratt has shown. We now formalise this
result. Consequently, the equational action algebra axioms, which
imply those based on Galois connections, which in turn imply those of
Kleene algebras, are complete with respect to the equational theory of
regular expressions. However, this completeness result does not
account for residuation. *}

class equational_action_algebra = equational_residuated_join_semilattice + dioid_one_zero + star_op +
  assumes star_ax: "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
  and star_subdist: "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  and right_pure_induction: "(x \<rightarrow> x)\<^sup>\<star> \<le> x \<rightarrow> x"
begin

text {* We now show that the equational axioms of action algebra
satisfy those based on the Galois connections. Since we can use our
correspondence between the two variants of residuated semilattice, it
remains to derive the second reflexive transitive closure axiom for
the star, essentially copying Pratt's proof step by step. We then
prove a subclass statement. *}

lemma star_rtc_2: "1 + y \<cdot> y + x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
proof
  assume "1 + y \<cdot> y + x \<le> y"
  also have "1 \<le> y"
    by (metis add_lub calculation)
  moreover have "x \<le> y"
    by (metis add_lub calculation)
  moreover have "y \<cdot> y \<le> y"
    by (metis add_lub calculation)
  hence "y \<le> y \<rightarrow> y"
    by (metis residual_r_galois)
  moreover have "x \<le> y \<rightarrow> y"
    by (metis calculation order_trans)
  hence "x\<^sup>\<star> \<le> (y \<rightarrow> y)\<^sup>\<star>"
    by (metis less_eq_def star_subdist)
  hence "x\<^sup>\<star> \<le> y \<rightarrow> y"
    by (metis order_trans right_pure_induction)
  hence "y \<cdot> x\<^sup>\<star> \<le> y"
    by (metis residual_r_galois)
  ultimately show "x\<^sup>\<star> \<le> y"
    by (metis mult_isor mult_onel order_trans)
qed

subclass action_algebra
  by (unfold_locales, metis star_ax, metis star_rtc_2)

end (* equational_action_algebra *)

text {*
Conversely, every action algebra satisfies the equational axioms of
equational action algebras.

Because the subclass relation must be acyclic in Isabelle, we can only
establish this for the corresponding locales. Again this proof is
based on the residuated semilattice result.
*}

sublocale action_algebra \<subseteq> equational_action_algebra
  by (unfold_locales, metis star_rtc1, metis star_subdist, metis residual_r_pure_induction)

subsection {* Another Variant *}

text {* Finally we show that Pratt and Kozen's star axioms generate
precisely the same theory. *}

class action_algebra_var = equational_residuated_join_semilattice + dioid_one_zero + star_op +
  assumes star_unfold': "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_inductl': "z + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and star_inductr': "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star>  \<le> y"
begin

subclass kleene_algebra
  by (unfold_locales, metis star_unfold', metis star_inductl', metis star_inductr')

subclass action_algebra
  by (unfold_locales, metis add.commute less_eq_def order_refl star_ext star_plus_one star_trans_eq, metis add.assoc add.commute star_rtc_least)

end

sublocale action_algebra \<subseteq> action_algebra_var
  by (unfold_locales, metis star_unfoldl, metis star_inductl, metis star_inductr)

end
