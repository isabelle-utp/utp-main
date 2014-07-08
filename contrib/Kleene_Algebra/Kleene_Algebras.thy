(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Kleene Algebras *}

theory Kleene_Algebras
imports Dioid
begin

subsection {* Left Near Kleene Algebras *}

text {* Extending the hierarchy developed in @{theory Dioid} we now
add an operation of Kleene star, finite iteration, or reflexive
transitive closure to variants of Dioids. Since a multiplicative unit
is needed for defining the star we only consider variants with~$1$;
$0$ can be added separately. We consider the left star induction axiom
and the right star induction axiom independently since in some
applications, e.g., Salomaa's axioms, probabilistic Kleene algebras,
or completeness proofs with respect to the equational theoy of regular
expressions and regular languages, the right star induction axiom is
not needed or not valid.

We start with near dioids, then consider pre-dioids and finally
dioids. It turns out that many of the known laws of Kleene algebras
hold already in these more general settings. In fact, all our
equational theorems have been proved within left Kleene algebras, as
expected.

Although most of the proofs in this file could be fully automated by
Sledgehammer and Metis, we display step-wise proofs as they would
appear in a text book. First, this file may then be useful as a
reference manual on Kleene algebra. Second, it is better protected
against changes in the underlying theories and supports easy
translation of proofs into other settings.  *}

class left_near_kleene_algebra = near_dioid_one + star_op +
  assumes star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_inductl: "z + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
begin

text {* First we prove two immediate consequences of the unfold
axiom. The first one states that starred elements are reflexive. *}

lemma star_ref: "1 \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldl)

text {* Reflexivity of starred elements implies, by definition of the
order, that~$1$ is an additive unit for starred elements. *}

lemma star_plus_one [simp]: "1 + x\<^sup>\<star> = x\<^sup>\<star>"
by (metis less_eq_def star_ref)

lemma star_1l: "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis add_lub star_unfoldl)

lemma "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

lemma "x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "2-element counterexample" *)
oops

text {* Next we show that starred elements are transitive. *}

lemma star_trans_eq [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym) -- "this splits an equation into two inequalities"
  have "x\<^sup>\<star> + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis add_lub eq_refl star_1l)
  thus "x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis star_inductl)
  next show "x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    by (metis mult_isor mult_onel star_ref)
qed

lemma star_trans: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis eq_refl star_trans_eq)

text {* We now derive variants of the star induction axiom. *}

lemma star_inductl_var: "x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
proof
  assume "x \<cdot> y \<le> y"
  hence "y + x \<cdot> y \<le> y"
    by (metis add_lub eq_refl)
  thus "x\<^sup>\<star> \<cdot> y \<le> y"
    by (metis star_inductl)
qed

lemma star_inductl_var_equiv: "x \<cdot> y \<le> y \<longleftrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
proof
  assume "x \<cdot> y \<le> y"
  thus "x\<^sup>\<star> \<cdot> y \<le> y"
    by (metis star_inductl_var)
next
  assume "x\<^sup>\<star> \<cdot> y \<le> y"
  hence  "x\<^sup>\<star> \<cdot> y = y"
    by (metis less_def less_le_trans mult_isor mult_onel star_ref)
  also have "x \<cdot> y = x \<cdot> x\<^sup>\<star> \<cdot> y"
    by (metis calculation mult.assoc)
  moreover have "... \<le> x\<^sup>\<star> \<cdot> y"
    by (metis mult_isor star_1l)
  ultimately show "x \<cdot> y \<le> y"
    by auto
qed

lemma star_inductl_var_eq:  "x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
  by (metis eq_iff star_inductl_var)

lemma star_inductl_var_eq2: "y = x \<cdot> y \<longrightarrow> y = x\<^sup>\<star> \<cdot> y"
proof
  assume "y = x \<cdot> y"
  also have "y \<le> x\<^sup>\<star> \<cdot> y"
    by (metis mult_isor mult_onel star_ref)
  thus "y = x\<^sup>\<star> \<cdot> y"
    by (metis calculation eq_iff star_inductl_var_eq)
qed

lemma "y = x \<cdot> y \<longleftrightarrow> y = x\<^sup>\<star> \<cdot> y"
  (* nitpick [expect=genuine] -- "2-element counterexample" *)
oops

lemma "x\<^sup>\<star> \<cdot> z \<le> y \<longrightarrow> z + x \<cdot> y \<le> y"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

lemma star_inductl_one: "1 + x \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
by (metis mult_oner star_inductl)

lemma star_inductl_star: "x \<cdot> y\<^sup>\<star> \<le> y\<^sup>\<star> \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
by (metis add_lub star_inductl_one star_ref)

lemma star_inductl_eq:  "z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  by (metis eq_iff star_inductl)

text {* We now prove two facts related to~$1$. *}

lemma star_subid: "x \<le> 1 \<longrightarrow> x\<^sup>\<star> = 1"
proof
  assume "x \<le> 1"
  hence "1 + x \<cdot> 1 \<le> 1"
    by (metis add_lub eq_refl mult_oner)
  hence "x\<^sup>\<star> \<le> 1"
    by (metis mult_oner star_inductl)
  thus " x\<^sup>\<star> = 1"
    by (metis eq_iff star_ref)
qed

lemma star_one [simp]: "1\<^sup>\<star> = 1"
  by (metis eq_iff star_subid)

text {* We now prove a subdistributivity property for the star (which
is equivalent to isotonicity of star). *}

lemma star_subdist:  "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
proof -
  have "x \<cdot> (x + y)\<^sup>\<star> \<le> (x + y) \<cdot> (x + y)\<^sup>\<star>"
    by (metis add_ub1 mult_isor)
  also have "...  \<le> (x + y)\<^sup>\<star>"
    by (metis star_1l)
  thus ?thesis
    by (metis calculation order_trans star_inductl_star)
qed

lemma star_subdist_var:  "x\<^sup>\<star> + y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  by (metis add.commute add_lub star_subdist)

lemma star_iso: "x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis less_eq_def star_subdist)

text {* We now prove some more simple properties. *}

lemma star_invol [simp]: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  have "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (fact star_trans_eq)
  thus "(x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis order_refl star_inductl_star)
  have"(x\<^sup>\<star>)\<^sup>\<star> \<cdot> (x\<^sup>\<star>)\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
    by (fact star_trans)
  hence "x \<cdot> (x\<^sup>\<star>)\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
    by (metis star_inductl_var_equiv)
  thus "x\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
    by (metis star_inductl_star)
qed

lemma star2 [simp]: "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  show "x\<^sup>\<star> \<le> (1 + x)\<^sup>\<star>"
    by (metis add_comm star_subdist)
  have "x\<^sup>\<star> + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis add_lub eq_refl star_1l)
  hence "(1 + x) \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis mult_onel distrib_right')
  thus "(1 + x)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis star_inductl_star)
qed

lemma "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

lemma "x \<le> x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

lemma "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

lemma "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

lemma "x \<cdot> z \<le> z \<cdot> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> z \<cdot> y\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

text {* The following facts express inductive conditions that are used
to show that @{term "(x + y)\<^sup>\<star>"} is the greatest term that can be built
from~@{term x} and~@{term y}.  *}

lemma sum_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x + y \<le> z\<^sup>\<star>"
  by (metis add_lub)

lemma prod_star_closure: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star> \<longrightarrow> x \<cdot> y \<le> z\<^sup>\<star>"
proof
  assume assm: "x \<le> z\<^sup>\<star> \<and> y \<le> z\<^sup>\<star>"
  hence "y + z\<^sup>\<star> \<cdot> z\<^sup>\<star> \<le> z\<^sup>\<star>"
    by (metis add_lub eq_refl star_trans_eq)
  hence "z\<^sup>\<star> \<cdot> y \<le> z\<^sup>\<star>"
    by (metis star_inductl star_invol)
  also have "x \<cdot> y \<le> z\<^sup>\<star> \<cdot> y"
    by (metis assm mult_isor)
  thus "x \<cdot> y \<le> z\<^sup>\<star>"
    by (metis calculation order_trans)
qed

lemma star_star_closure: "x\<^sup>\<star> \<le> z\<^sup>\<star> \<longrightarrow> (x\<^sup>\<star>)\<^sup>\<star> \<le> z\<^sup>\<star>"
  by (metis star_invol)

lemma star_closed_unfold: "x\<^sup>\<star> = x \<longrightarrow> x = 1 + x \<cdot> x"
  by (metis star_plus_one star_trans_eq)

lemma "x\<^sup>\<star> = x \<longleftrightarrow> x = 1 + x \<cdot> x"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

end (* left_near_kleene_algebra *)


subsection {* Left Pre-Kleene Algebras *}

class left_pre_kleene_algebra = left_near_kleene_algebra + pre_dioid_one
begin

text {* We first prove that the star operation is extensive. *}

lemma star_ext: "x \<le> x\<^sup>\<star>"
proof -
  have "x \<le> x \<cdot> x\<^sup>\<star>"
    by (metis mult_oner mult_isol star_ref)
  thus ?thesis
    by (metis order_trans star_1l)
qed

text {* We now prove a right star unfold law. *}

lemma star_1r: "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
proof -
  have "x + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis add_lub star_1l star_ext)
  thus ?thesis
    by (metis star_inductl)
qed

lemma star_unfoldr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  by (metis add_lub star_1r star_ref)

lemma "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

text {* Next we prove a simulation law for the star.  It is
instrumental in proving further properties. *}

lemma star_sim1: "x \<cdot> z \<le> z \<cdot> y \<longrightarrow> x\<^sup>\<star> \<cdot> z \<le> z \<cdot> y\<^sup>\<star>"
proof
  assume "x \<cdot> z \<le> z \<cdot> y"
  hence "x \<cdot> z \<cdot> y\<^sup>\<star> \<le> z \<cdot> y \<cdot> y\<^sup>\<star>"
    by (metis mult_isor)
  also have "...  \<le> z \<cdot> y\<^sup>\<star>"
    by (metis mult.assoc mult_isol star_1l)
  hence "z + x \<cdot> z \<cdot> y\<^sup>\<star> \<le> z \<cdot> y\<^sup>\<star>"
    by (metis calculation order_trans add_lub mult_isol mult_oner star_ref)
  thus "x\<^sup>\<star> \<cdot> z \<le> z \<cdot> y\<^sup>\<star>"
    by (metis mult.assoc star_inductl)
qed

text {* The next lemma is used in omega algebras to prove, for
instance, Bachmair and Dershowitz's separation of termination
theorem~\cite{bachmair86commutation}. The property at the left-hand
side of the equivalence is known as \emph{quasicommutation}. *}

lemma quasicomm_var: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> \<longleftrightarrow> y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
proof
  assume "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  thus "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    by (metis star_invol star_sim1)
next
  assume "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  thus "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    by (metis mult_isor order_trans star_ext)
qed

lemma star_slide1: "(x \<cdot> y)\<^sup>\<star> \<cdot> x \<le> x \<cdot> (y \<cdot> x)\<^sup>\<star>"
  by (metis eq_iff mult_assoc star_sim1)

lemma "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

lemma star_slide_var1: "x\<^sup>\<star> \<cdot> x \<le> x \<cdot> x\<^sup>\<star>"
  by (metis eq_refl star_sim1)

text {* We now show that the (left) star unfold axiom can be
strengthened to an equality. *}

lemma star_unfoldl_eq [simp]: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (fact star_unfoldl)
  have "1 + x \<cdot> (1 + x \<cdot> x\<^sup>\<star>) \<le> 1 + x \<cdot> x\<^sup>\<star>"
    by (metis add_iso_var eq_refl mult_isol star_unfoldl)
  thus "x\<^sup>\<star> \<le> 1 + x \<cdot> x\<^sup>\<star>"
    by (metis star_inductl_one)
qed

lemma "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

text {* Next we relate the star and the reflexive transitive closure
operation. *}

lemma star_rtc1_eq [simp]: "1 + x + x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof -
  have "1 + x + x\<^sup>\<star> \<cdot> x\<^sup>\<star> = 1 + x + x\<^sup>\<star>"
    by (metis star_trans_eq)
  also have "... = x + x\<^sup>\<star>"
    by (metis add.commute add.left_commute star_plus_one)
  thus ?thesis
    by (metis calculation less_eq_def star_ext)
qed

lemma star_rtc1: "1 + x + x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by (metis eq_refl star_rtc1_eq)

lemma star_rtc2: "1 + x \<cdot> x \<le> x \<longleftrightarrow> x = x\<^sup>\<star>"
  by (metis antisym star_ext star_inductl_one star_plus_one star_trans_eq)

lemma star_rtc3: "1 + x \<cdot> x = x \<longleftrightarrow> x = x\<^sup>\<star>"
  by (metis order_refl star_plus_one star_rtc2 star_trans_eq)

lemma star_rtc_least: "1 + x + y \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
proof
  assume "1 + x + y \<cdot> y \<le> y"
  hence "1 + x \<cdot> y \<le> y"
    by (metis add_lub less_eq_def distrib_right')
  thus "x\<^sup>\<star> \<le> y"
    by (metis star_inductl_one)
qed

lemma star_rtc_least_eq: "1 + x + y \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<le> y"
  by (metis eq_refl star_rtc_least)

lemma "1 + x + y \<cdot> y \<le> y \<longleftrightarrow> x\<^sup>\<star> \<le> y"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

text {* The next lemmas are again related to closure conditions *}

lemma star_subdist_var_1: "x \<le> (x + y)\<^sup>\<star>"
  by (metis add_lub star_ext)

lemma star_subdist_var_2: "x \<cdot> y \<le> (x + y)\<^sup>\<star>"
  by (metis add_lub prod_star_closure star_ext)

lemma star_subdist_var_3: "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  by (metis add_comm prod_star_closure star_subdist)

text {* We now prove variants of sum-elimination laws under a star.
These are also known a denesting laws or as sum-star laws. *}

lemma star_denest [simp]: "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
proof (rule antisym)
  have "x + y \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis add_lub_var mult_isol_var mult_onel mult_oner star_ext star_ref)
  thus "(x + y)\<^sup>\<star> \<le> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
    by (metis star_iso)
  have "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (metis star_subdist_var_3)
  thus "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (metis star_invol star_iso)
qed

lemma star_sum_var [simp]: "(x\<^sup>\<star> + y\<^sup>\<star>)\<^sup>\<star> = (x + y)\<^sup>\<star>"
  by (metis star_denest star_invol)

lemma star_denest_var [simp]: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
proof (rule antisym)
  have "1 \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis add_lub mult_oner star_unfoldl_eq subdistl)
  moreover have "x \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_isor star_1l)
  moreover have "y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_isol_var mult_onel star_1l star_ref)
  hence "1 + (x + y) \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis calculation add_lub_var distrib_right')
  thus "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult.assoc mult_oner star_inductl)
  have "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (y\<^sup>\<star> \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_isor star_ext star_iso)
  moreover have "... = (x + y)\<^sup>\<star>"
    by (metis add.commute star_denest)
  moreover have "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (metis star_subdist)
  thus "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (metis calculation prod_star_closure)
qed

lemma star_denest_var_2: "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var)

lemma star_denest_var_3 [simp]: "x\<^sup>\<star> \<cdot> (y\<^sup>\<star> \<cdot> x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var star_invol)

lemma star_denest_var_4 [simp]: "(y\<^sup>\<star> \<cdot> x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm star_denest)

lemma star_denest_var_5: "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> = y\<^sup>\<star> \<cdot> (x \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm star_denest_var)

(*
lemma "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
  nitpick [expect=genuine] -- "6-element counterexample"
oops
*)

lemma star_denest_var_6 [simp]: "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star> = (x + y)\<^sup>\<star>"
  by (metis mult_assoc star_denest star_denest_var_3)

lemma star_denest_var_7 [simp]: "(x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> = (x + y)\<^sup>\<star>"
proof (rule antisym)
  have "(x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_isol mult_assoc star_ext)
  thus "(x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (metis star_denest star_trans_eq)
  have "1 \<le> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis mult_isol_var mult_oner star_ref)
  moreover have "(x + y) \<cdot> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis mult_isor star_1l)
  moreover have "1 + (x + y) \<cdot> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis add_lub calculation)
  thus "(x + y)\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis mult.assoc star_inductl_one)
qed

lemma star_denest_var_8 [simp]: "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis mult_assoc star_denest_var_2 star_invol)

lemma star_denest_var_9 [simp]: "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis star_denest star_denest_var_7)

text {* The following statements are well known from term
rewriting. They are all variants of the Church-Rosser theorem in
Kleene algebra~\cite{struth06churchrosser}. But first we prove a law
relating two confluence properties. *}

lemma confluence_var: "y \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longleftrightarrow> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
proof
  assume "y \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  thus "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis star_invol star_sim1)
next
  assume "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  thus "y \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis mult_isor order_trans star_ext)
qed

lemma church_rosser: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
proof
  assume "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  hence "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis mult_isol mult_isor mult_assoc)
  also have "... \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis eq_refl mult.assoc star_trans_eq)
  also have "1 \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis add_lub mult_oner star_unfoldl_eq subdistl)
  hence "1 + x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis add_lub_var calculation mult.assoc)
  hence "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>  \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis calculation mult.assoc star_denest_var_9 star_inductl_var_equiv)
  moreover have "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis calculation star_denest)
  thus "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis eq_iff star_subdist_var_3)
qed

lemma church_rosser_var: "y \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis church_rosser confluence_var)

lemma church_rosser_to_confluence: "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longrightarrow> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis add_comm eq_iff star_subdist_var_3)

lemma church_rosser_equiv: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longleftrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis church_rosser church_rosser_to_confluence eq_iff)

lemma confluence_to_local_confluence: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longrightarrow> y \<cdot> x \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis add.commute church_rosser star_subdist_var_2)

(*
lemma "y \<cdot> x \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longrightarrow> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  nitpick [expect=genuine] -- "6-element counterexample"
oops

lemma "y \<cdot> x \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longrightarrow> (x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  nitpick [expect=genuine] -- "6-element counterexample, as expected"
oops

text {*
More variations could easily be proved. The last counterexample shows
that Newman's lemma needs a wellfoundedness assumption. This is well
known.
*}
*)

text {* The next lemmas relate the reflexive transitive closure and
the transitive closure. *}

lemma sup_id_star1: "1 \<le> x \<longrightarrow> x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof
  assume "1 \<le> x"
  hence " x\<^sup>\<star> \<le> x \<cdot> x\<^sup>\<star>"
    by (metis mult_isor mult_onel)
  thus "x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (metis eq_iff star_1l)
qed

lemma sup_id_star2: "1 \<le> x \<longrightarrow> x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  by (metis eq_iff mult_isol mult_oner star_1r)

lemma "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

lemma "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

lemma "x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = 1 + x"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

end (* left_pre_kleene_algebra *)


subsection {* Left Kleene Algebras *}

class left_kleene_algebra = left_pre_kleene_algebra + dioid_one
begin

text {* In left Kleene algebras the non-fact @{prop "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"}
is a good challenge for counterexample generators. A model of left
Kleene algebras in which the right star induction law does not hold
has been given by Kozen~\cite{kozen90kleene}. *}

(*
lemma "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
  nitpick -- "unfortunately, no counterexample found"
oops
*)

text {* We now show that the right unfold law becomes an equality. *}

lemma star_unfoldr_eq [simp]: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
proof (rule antisym)
  show "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
    by (metis star_unfoldr)
  have "1 + x \<cdot> (1 + x\<^sup>\<star> \<cdot> x) = 1 + (1 + x \<cdot> x\<^sup>\<star>) \<cdot> x"
    by (metis distrib_right mult.assoc mult_onel mult_oner distrib_left)
  also have "... = 1 + x\<^sup>\<star> \<cdot> x"
    by (metis star_unfoldl_eq)
  thus "x\<^sup>\<star> \<le> 1 + x\<^sup>\<star> \<cdot> x"
    by (metis calculation eq_refl star_inductl_one)
qed

text {* The following more complex unfold law has been used as an
axiom, called prodstar, by Conway~\cite{conway71regular}. *}

lemma star_prod_unfold [simp]: "1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y = (x \<cdot> y)\<^sup>\<star>"
proof (rule antisym)
  have "(x \<cdot> y)\<^sup>\<star> = 1 + (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y"
    by (metis mult.assoc star_unfoldr_eq)
  thus "(x \<cdot> y)\<^sup>\<star> \<le> 1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
    by (metis add_iso_var mult_isor order_refl star_slide1)
  have "1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<le> 1 + x \<cdot> y \<cdot>  (x \<cdot> y)\<^sup>\<star>"
    by (metis add_iso_var eq_refl mult.assoc mult_isol star_slide1)
  thus "1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<le> (x \<cdot> y)\<^sup>\<star>"
    by (metis star_unfoldl_eq)
qed

text {* The slide laws, which have previously been inequalities, now
become equations. *}

lemma star_slide: "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>"
proof -
  have "x \<cdot> (y \<cdot> x)\<^sup>\<star> = x \<cdot> (1 + y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> x)"
    by (metis star_prod_unfold)
  also have "... = (1 + x \<cdot> y \<cdot> (x \<cdot> y)\<^sup>\<star>) \<cdot> x"
    by (metis distrib_right mult.assoc mult_onel mult_oner distrib_left)
  thus ?thesis
    by (metis calculation star_unfoldl_eq)
qed

lemma star_slide_var: "x\<^sup>\<star> \<cdot> x = x \<cdot> x\<^sup>\<star>"
  by (metis mult_onel mult_oner star_slide)

lemma star_sum_unfold_var [simp]: "1 + x\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star> \<cdot> y\<^sup>\<star> = (x + y)\<^sup>\<star>"
  by (metis star_denest star_denest_var_3 star_denest_var_4 star_plus_one star_slide)

text {* The following law shows how starred sums can be unfolded. *}

lemma star_sum_unfold [simp]: "x\<^sup>\<star> + x\<^sup>\<star> \<cdot> y \<cdot> (x + y)\<^sup>\<star> = (x + y)\<^sup>\<star>"
proof -
  have "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star> )\<^sup>\<star>"
    by (metis star_denest_var)
  also have "... = x\<^sup>\<star> \<cdot> (1 + y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star> )\<^sup>\<star>)"
    by (metis star_unfoldl_eq)
  also have "... = x\<^sup>\<star> \<cdot> (1 + y \<cdot> (x + y)\<^sup>\<star>)"
    by (metis mult.assoc star_denest_var)
  thus ?thesis
    by (metis mult.assoc mult_oner distrib_left calculation)
qed

text {* The following property appears in process algebra. *}

lemma troeger [simp]: "(x + y)\<^sup>\<star> \<cdot> z = x\<^sup>\<star> \<cdot> (y \<cdot> (x+y)\<^sup>\<star> \<cdot> z + z)"
  using [[metis_verbose=false]]
    -- {* Theorem {\em opp\_mult\_def} is not actually required for
          {\em metis} to find a proof, but (interestingly enough) it
          considerably speeds up the proof search. We suppress the
          ``unused theorem'' warning that {\em metis} would generate
          in verbose mode. *}
  by (metis add.commute distrib_left distrib_right mult.assoc mult_onel mult_oner opp_mult_def star_sum_unfold)

text {* The following properties are related to a property from
propositional dynamic logic which has been attributed to Albert
Meyer~\cite{harelkozentiuryn00dynamic}. Here we prove it as a theorem
of Kleene algebra. *}

lemma star_square: "(x \<cdot> x)\<^sup>\<star> \<le> x\<^sup>\<star>"
proof -
  have "x \<cdot> x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis mult.assoc prod_star_closure star_1l star_ext)
  thus ?thesis
    by (metis star_inductl_star)
qed

lemma meyer_1 [simp]: "(1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  have "1 \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis add_lub mult_oner star_unfoldl_eq subdistl)
  also have "x \<cdot>  (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> = x \<cdot> (x \<cdot> x)\<^sup>\<star> + x \<cdot> x \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis distrib_right mult_oner distrib_left)
   moreover have "... \<le> x \<cdot> (x \<cdot> x)\<^sup>\<star> + (x \<cdot> x)\<^sup>\<star>"
    by (metis add_iso_var le_less star_1l)
  moreover have "... \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis add.commute eq_iff distrib_right mult_onel)
  hence "1 + x \<cdot> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis add.commute add_lub_var calculation distrib_right mult.assoc mult_onel)
  thus "x\<^sup>\<star> \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (metis mult.assoc star_inductl_one)
  show "(1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis prod_star_closure star2 star_ext star_square)
qed

text {* The following lemma says that transitive elements are equal to
their transitive closure. *}

lemma tc: "x \<cdot> x \<le> x \<longrightarrow> x\<^sup>\<star> \<cdot> x = x"
proof
  assume "x \<cdot> x \<le> x"
  hence "x + x \<cdot> x \<le> x"
    by (metis add_lub eq_refl)
  hence "x\<^sup>\<star> \<cdot> x \<le> x"
    by (metis star_inductl)
  thus  "x\<^sup>\<star> \<cdot> x = x"
    by (metis mult_isol mult_oner star_ref star_slide_var eq_iff)
qed

lemma tc_eq: "x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> \<cdot> x = x"
  by (metis order_refl tc)


text {* The next fact has been used by Boffa~\cite{boffa90remarque} to
axiomatise the equational theory of regular expressions. *}

lemma boffa_var: "x \<cdot> x \<le> x \<longrightarrow> x\<^sup>\<star> = 1 + x"
proof
  assume "x \<cdot> x \<le> x"
  also have "x\<^sup>\<star> = 1 + x\<^sup>\<star> \<cdot> x"
    by (metis star_unfoldr_eq)
  thus "x\<^sup>\<star> = 1 + x"
    by (metis calculation tc)
qed

lemma boffa: "x \<cdot> x = x \<longrightarrow> x\<^sup>\<star> = 1 + x"
  by (metis boffa_var eq_iff)

(*
text {*
For the following two lemmas, Isabelle could neither find a
counterexample nor a proof automatically.
*}

lemma "z \<cdot> x \<le> y \<cdot> z \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z"
  -- "unfortunately, no counterexample found"
oops

lemma star_sim3: "z \<cdot> x = y \<cdot> z \<longrightarrow> z \<cdot> x\<^sup>\<star> = y\<^sup>\<star> \<cdot> z"
  -- "we conjecture that this is not provable"
oops
*)

end (* left_kleene_algebra *)


subsection {* Left Kleene Algebras with Zero *}

text {*
There are applications where only a left zero is assumed, for instance
in the context of total correctness and for demonic refinement
algebras~\cite{vonwright04refinement}.
*}

class left_kleene_algebra_zerol = left_kleene_algebra + dioid_one_zerol
begin

lemma star_zero [simp]: "0\<^sup>\<star> = 1"
  by (metis add_zerol less_eq_def star_subid)

text {*
In principle,~$1$ could therefore be defined from~$0$ in this setting.
*}

end (* left_kleene_algebra_zerol *)

class left_kleene_algebra_zero = left_kleene_algebra_zerol + dioid_one_zero


subsection {* Pre-Kleene Algebras *}

text {* Pre-Kleene algebras are essentially probabilistic Kleene
algebras~\cite{mciverweber05pka}.  They have a weaker right star
unfold axiom. We are still looking for theorems that could be proved
in this setting.  *}

class pre_kleene_algebra = left_pre_kleene_algebra +
  assumes weak_star_unfoldr: "z + y \<cdot> (x + 1) \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"


subsection {* Kleene Algebras *}

text {* Finally, here come the Kleene algebras \`a~la
Kozen~\cite{kozen04complete}. We only prove quasi-identities in this
section. Since left Kleene algebras are complete with respect to the
equational theory of regular expressions and regular languages, all
identities hold already without the right star induction axiom. *}

class kleene_algebra = left_kleene_algebra_zero +
  assumes star_inductr: "z + y \<cdot> x \<le> y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
begin

text {*
The next lemma shows that opposites of Kleene algebras (i.e., Kleene
algebras with the order of multiplication swapped) are again Kleene
algebras.
*}

lemma dual_kleene_algebra:
  "class.kleene_algebra (op +) (op \<odot>) 1 0 (op \<le>) (op <) star"
proof
  fix x y z :: 'a
  show "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult_assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis opp_mult_def distrib_left)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (fact add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
   show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "x + x = x"
    by (fact add_idem)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "z \<odot> x \<le> z \<odot> (x + y)"
    by (metis mult_isor opp_mult_def order_prop)
  show "1 + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis opp_mult_def order_refl star_slide_var star_unfoldl_eq)
  show "z + x \<odot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<odot> z \<le> y"
    by (metis opp_mult_def star_inductr)
  show "z + y \<odot> x \<le> y \<longrightarrow> z \<odot> x\<^sup>\<star> \<le> y"
    by (metis opp_mult_def star_inductl)
qed

lemma star_inductr_var: "y \<cdot> x \<le> y \<longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (metis add_lub order_refl star_inductr)

lemma star_inductr_var_equiv: "y \<cdot> x \<le> y \<longleftrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (metis order_trans mult_isol star_ext star_inductr_var)

text {*
The following law could be immediate from \emph{star\_sim1} if we had
proper (technical support for) duality for Kleene algebras.
*}

lemma star_sim2: "z \<cdot> x \<le> y \<cdot> z \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z"
proof -
  from dual_kleene_algebra have "class.left_pre_kleene_algebra op+ op\<odot> 1 op\<le> op< star"
    unfolding class.kleene_algebra_def class.left_kleene_algebra_zero_def
      class.left_kleene_algebra_zerol_def class.left_kleene_algebra_def
    by auto
  thus ?thesis
    by (fold opp_mult_def) (erule left_pre_kleene_algebra.star_sim1)
qed

lemma star_sim3: "z \<cdot> x = y \<cdot> z \<longrightarrow> z \<cdot> x\<^sup>\<star> = y\<^sup>\<star> \<cdot> z"
  by (metis eq_iff star_sim1 star_sim2)

lemma star_sim4: "x \<cdot> y \<le>  y \<cdot> x \<longrightarrow> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> x\<^sup>\<star>"
  by (metis star_sim1 star_sim2)

lemma star_inductr_eq: "z + y \<cdot> x = y \<longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
  by (metis eq_iff star_inductr)

lemma star_inductr_var_eq: "y \<cdot> x = y \<longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (metis eq_iff star_inductr_var)

lemma star_inductr_var_eq2: "y \<cdot> x = y \<longrightarrow> y \<cdot> x\<^sup>\<star> = y"
  by (metis mult_onel star_one star_sim3)

lemma bubble_sort: "y \<cdot> x \<le> x \<cdot> y \<longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis church_rosser star_sim4)

text {* Next we prove two independence properties. In relational
Kleene algebras, for instance, \mbox{@{term "x\<cdot>y=0"}} means that
relation~@{term x} does not lead into states where relation~@{term y}
can be executed. *}

lemma independence1: "x \<cdot> y = 0 \<longrightarrow> x\<^sup>\<star> \<cdot> y = y"
proof
  assume "x \<cdot> y = 0"
  also have "x\<^sup>\<star> \<cdot> y = y + x\<^sup>\<star> \<cdot> x \<cdot> y"
    by (metis distrib_right mult_onel star_unfoldr_eq)
  thus "x\<^sup>\<star> \<cdot> y = y"
    by (metis add_zero_r annir calculation mult.assoc)
qed

lemma independence2: "x \<cdot> y = 0 \<longrightarrow> x \<cdot> y\<^sup>\<star> = x"
  by (metis annil mult_onel star_sim3 star_zero)

text {* The following lemma is important for a separation of
termination theorem by Doornbos, Backhouse and van der
Woude~\cite{doornbos97calculational}. The property at the left-hand
side has been baptised lazy commutation by Nachum
Dershowitz~\cite{dershowitz09lazy}. *}

lemma lazycomm_var: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> + y \<longleftrightarrow> y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
proof
  let ?t = "x \<cdot> (x + y)\<^sup>\<star>"
  assume "y \<cdot> x \<le> ?t + y"
  also have "(?t + y) \<cdot> x = ?t \<cdot> x + y \<cdot> x"
    by (metis distrib_right)
  moreover have "... \<le> ?t \<cdot> x + ?t + y"
    by (metis add_iso_var calculation le_less add_assoc)
  moreover have "... \<le> ?t + y"
    by (metis add_iso_var add_lub_var mult.assoc mult_isol order_refl prod_star_closure star_subdist_var_1)
  hence "y + (?t + y) \<cdot> x \<le> ?t + y"
    by (metis add.commute add_lub_var add_ub1 calculation less_eq_def mult.assoc distrib_left star_subdist_var_1 star_trans_eq)
  thus "y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
    by (metis star_inductr)
next
  assume "y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
  thus "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
    by (metis mult_isol order_trans star_ext)
qed

text {* Arden's rule in language theory says that if a language~@{term
X} does not contain the empty word, then the language equation
\mbox{@{term "Y = X\<cdot>Y+Z"}} has the unique solution \mbox{@{term "Y =
X\<^sup>\<star>\<cdot>Z"}}. We prove a variant of this rule, that the Kleene algebra
equation \mbox{@{term "y = x\<cdot>y+z"}} has the unique solution
\mbox{@{term "y = x\<^sup>\<star>\<cdot>z"}}, from a different algebraic
condition~\cite{struth12regeq}. *}

lemma arden_var: "(\<forall>y v. y \<le> x \<cdot> y + v \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> v) \<longrightarrow> z = x \<cdot> z + w \<longrightarrow> z = x\<^sup>\<star> \<cdot> w"
  by (metis add_comm eq_iff star_inductl_eq)

lemma "(\<forall>x y. y \<le> x \<cdot> y \<longrightarrow> y = 0) \<longrightarrow> y \<le> x \<cdot> y + z \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z"
  by (metis eq_refl mult_onel)

(*
lemma "(\<forall>y. y \<le> x \<cdot> y \<longrightarrow> y = 0) \<longrightarrow> y \<le> x \<cdot> y + z \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z"
  -- "no automatic proof, no automatic counterexample"
*)

end (* kleene_algebra *)

text {* We finish with some properties on (multiplicatively)
commutative Kleene algebras. A chapter in Conway's
book~\cite{conway71regular} is devoted to this topic. *}

class commutative_kleene_algebra = kleene_algebra +
  assumes mult_comm: "x \<cdot> y = y \<cdot> x"
begin

lemma conway_c3 [simp]: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis bubble_sort eq_refl mult_comm)

lemma conway_c4 [simp]: "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> = 1 + x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> y"
  by (metis conway_c3 star_denest_var star_prod_unfold)

lemma cka_1: "(x \<cdot> y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis conway_c3 star_invol star_iso star_subdist_var_2)

lemma cka_2 [simp]: "x\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis conway_c3 mult_comm star_denest_var)

lemma conway_c4_var [simp]: "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis conway_c3 star_invol)

lemma conway_c2 [simp]: "(x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
proof (rule antisym)
  show "(x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis cka_1 conway_c3 prod_star_closure star_ext star_sum_var)
  have "x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) = x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + 1 + y \<cdot> y\<^sup>\<star>)"
    by (metis add.commute add.left_commute star_unfoldl_eq)
  also have "... = x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y \<cdot> y\<^sup>\<star>)"
    by (metis add.commute star_plus_one)
  also have "... = (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> x\<^sup>\<star> + (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y \<cdot> y\<^sup>\<star>"
    by (metis distrib_left mult_assoc mult_comm)
  also have "... \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star> + (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y \<cdot> y\<^sup>\<star>"
    by (metis star_1l add_iso mult_isol mult_assoc)
  also have "... \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star> + (x \<cdot> y)\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis add_iso_var conway_c3 mult.assoc mult_comm order_refl prod_star_closure star_subdist_var_1)
  also have "... = (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)"
    by (metis distrib_right mult_comm)
  finally have "x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)" .
  also have "y\<^sup>\<star> \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)"
    by (metis add_lub annir mult_oner star_sim2 star_zero zero_least)
  hence "y\<^sup>\<star> + x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)"
    by (metis add_lub calculation)
  thus "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)"
    by (metis mult.assoc star_inductl)
qed

end (* commutative_kleene_algebra *)

end
