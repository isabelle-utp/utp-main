(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: uref.thy                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

section {* Value Refinement *}

theory uref
imports uval
begin

text {*
  A unified notion of refinement requires again an axiomatisation. Firstly,
  to define refinement for @{class injectable} values, and secondly to assert
  that refinement can be generalised to a partial order on \emph{all} values.
  Right now, I am not certain whether the latter is needed in practice. I am
  fairly confident the axioms are sound, it is essentially a lifting of an
  ordering on HOL values into the universal value type @{type uval}.
*}

subsection {* Axiomatisation *}

axiomatization
-- {* Model Value Refinement *}
  ref_uval :: "uval \<Rightarrow> uval \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>u" 50) where
-- {* Definition of Refinement *}
  ref_uval_def [simp]: "(InjU x) \<sqsubseteq>\<^sub>u (InjU y) \<longleftrightarrow> (x \<le> y)" and
-- {* Global Ordering Axiom *}
  uval_ordering : "ordering (op \<sqsubseteq>\<^sub>u) (\<lambda>x y. x \<sqsubseteq>\<^sub>u y \<and> x \<noteq> y)"

abbreviation ref_uval_neq :: "uval \<Rightarrow> uval \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>u" 50) where
"x \<sqsubset>\<^sub>u y \<equiv> x \<sqsubseteq>\<^sub>u y \<and> x \<noteq> y"

subsection {* Order Instantiation *}

text {*
  For now, we are content with an @{class order} on @{type uval} instead of a
  @{class complete_lattice}. This should already allow us to prove key laws in
  the theory of Higher-Order UTP. If a complete lattice shows to be needed, we
  can easily adapt the current theory in the future.
*}

instantiation uval :: order
begin
definition less_eq_uval :: "uval \<Rightarrow> uval \<Rightarrow> bool" where
"less_eq_uval = ref_uval"

definition less_uval :: "uval \<Rightarrow> uval \<Rightarrow> bool" where
"less_uval = ref_uval_neq"
instance
apply (intro_classes)
apply (unfold less_eq_uval_def less_uval_def)
apply (meson ordering.antisym uval_ordering)
apply (meson ordering.refl uval_ordering)
apply (meson ordering.trans uval_ordering)
apply (meson ordering.antisym uval_ordering)
done
end
end