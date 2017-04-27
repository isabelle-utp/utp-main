(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: LPF.thy                                                              *)
(* Authors: Casper Thule and Frank Zeyda                                      *)
(* Emails: casper.thule@eng.au.dk and frank.zeyda@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 21 Mar 2017 *)

section {* Logic of Partial Functions *}

theory LPF
imports Main Eisbach utp
begin

subsection {* LPF Type *}

text {*
  Below we define a new type to represent values in LPF. Effectively, we encode
  these as @{type option} types where @{const None} will be used to represent
  the undefined value of our LPF logic embedding.
*}

typedef 'a lpf = "UNIV :: 'a option set"
apply(rule UNIV_witness)
done
print_theorems
(* The type synonym below should really go into the VDM.thy theory. *)

(* At a later point we want to introduce a UTP expression type for VDM. *)

type_synonym ('a, '\<alpha>) vexpr = "('a lpf, '\<alpha>) uexpr"

(* With the below, pretty-printing of the type synonym works as well! *)

typ "('a, '\<alpha>) vexpr"

translations (type) "('a, '\<alpha>) vexpr" \<leftharpoondown> (type) "('a lpf, '\<alpha>) uexpr"

typ "('a, '\<alpha>) vexpr"

text {*Two theorems to use in proofs are set up  *}
named_theorems lpf_defs "lpf definitional axioms"
named_theorems lpf_transfer "lpf transfer laws"

lemmas Abs_lpf_inject_sym = sym [OF Abs_lpf_inject]
lemmas Rep_lpf_inject_sym = sym [OF Rep_lpf_inject]

declare Rep_lpf_inverse [lpf_transfer]
declare Abs_lpf_inverse [simplified, lpf_transfer]
declare Rep_lpf_inject_sym [lpf_transfer]
declare Abs_lpf_inject [simplified, lpf_transfer]

text {*The lifting of the type lpf is set up*}
setup_lifting type_definition_lpf

text {*Lifting of a HOL type into a defined lpf value*}
(*TODO: How can one define this as a function e.g. lpf_Some x = Some x*)
lift_definition lpf_Some :: "'a \<Rightarrow> 'a lpf"
is "Some" .
print_theorems

text {* Lpf value for undefined *}
lift_definition lpf_None :: "'a lpf"
is "None" .

text {* Definition of definedness for lpf values*}
definition defined :: "'a lpf \<Rightarrow> bool" ("\<D>'(_')") where
"defined x \<longleftrightarrow> (x \<noteq> lpf_None)"

declare lpf_Some.rep_eq [lpf_transfer]
declare lpf_None.rep_eq [lpf_transfer]
declare defined_def [lpf_defs]

text {*
  The following function checks if an input x satisfies a predicate (belongs to
  a set). If it does then it returns the value backed, wrapped up in the
  @{type lpf} type, otherwise it returns @{const lpf_None}.
*}

definition lpfSat :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a lpf" where
"lpfSat u a = (if a\<in>u then lpf_Some a else lpf_None)"

text {* Overloading definition for monadic bind *}
definition lift1_bind :: "'a lpf \<Rightarrow> ('a \<Rightarrow> 'b lpf) \<Rightarrow> 'b lpf" where
[lpf_defs]: "lift1_bind a f =
  (if \<D>(a) then  (f \<circ> the \<circ> Rep_lpf) a else lpf_None)"

adhoc_overloading
bind lift1_bind

text {* lift1_lpf takes a set which is a predicate on the input values,
  a total HOL function taking one argument and turns  it into a function on
  option types. The resulting value is defined if (1) each input is defined
  and (2) the input satisfies the predicate.
*}

definition lift1_lpf_old :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" where
[lpf_defs]:"lift1_lpf_old u f = (\<lambda>x . (x\<bind>lpfSat u)\<bind> lpf_Some \<circ> f)"

definition lift1_lpf'_old :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" where
[lpf_defs]:"lift1_lpf'_old = lift1_lpf_old UNIV"

lift_definition lift1_lpf :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" is
"(\<lambda> u f x . (x\<bind>lpfSat u)\<bind> lpf_Some \<circ> f)"
done

declare lift1_lpf.transfer [lpf_transfer]
declare lift1_lpf_def [lpf_defs]

lift_definition lift1_lpf' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" is
"(\<lambda> f . lift1_lpf UNIV f)"
done

declare lift1_lpf'.transfer [lpf_transfer]
declare lift1_lpf'_def [lpf_defs]

text {*
  Below we define unary operators on the lpf type
  using the lifting defined above.
*}

(* With instantiation, use the type class syntax for uminus. *)
(*instantiation lpf :: (uminus) uminus
begin
definition uminus_lpf :: "'a lpf \<Rightarrow> 'a lpf" where
"uminus_lpf = lift1_lpf' uminus"
instance ..
end*)

definition uminus_lpf :: "'a::uminus lpf \<Rightarrow> 'a lpf" ("-\<^sub>L _" [81] 80) where
[lpf_defs]: "uminus_lpf = lift1_lpf' uminus"

definition card_lpf :: "'a set lpf \<Rightarrow> nat lpf" where
[lpf_defs]: "card_lpf = lift1_lpf' card"

definition abs_lpf :: "real lpf \<Rightarrow> real lpf" where
[lpf_defs]: "abs_lpf = lift1_lpf' abs"

definition floor_lpf :: "real lpf \<Rightarrow> int lpf" where
[lpf_defs]: "floor_lpf = lift1_lpf' floor"

definition len_lpf :: "'a list lpf \<Rightarrow> nat lpf" where
[lpf_defs]: "len_lpf = lift1_lpf' length"

-- {* \todo{Define the following operators:
  Boolean type: Negation
  Record types: field select and is.
  Set unary operators: dunion, dinter and power.
  Sequence unary operators: hd, tl, elems, inds, reverse, conc and indexing.
  Map unary operators: dom, rng, merge, apply and inverse.  }
*}

lift_definition lift2_lpf ::
  "('a * 'b) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf)" is
  "(\<lambda> u f v1 v2.
  do { x \<leftarrow> v1; y \<leftarrow> v2; lpfSat u (x, y) } \<bind> lpf_Some \<circ> uncurry f)"
done

declare lift2_lpf.transfer [lpf_transfer]
declare lift2_lpf_def [lpf_defs]

lift_definition lift2_lpf' ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf)" is
  "lift2_lpf UNIV"
done

declare lift2_lpf'.transfer [lpf_transfer]
declare lift2_lpf'_def [lpf_defs]

text {*
  Lifts a HOL function with two arguments into a function on the lpf type
*}
definition lift2_lpf_old ::
  "('a * 'b) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf)" where
[lpf_defs]: "lift2_lpf_old u f =
  (\<lambda> v1 v2. do { x \<leftarrow> v1; y \<leftarrow> v2; lpfSat u (x, y) } \<bind> lpf_Some \<circ> uncurry f)"

definition lift2_lpf'_old :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf)" where
[lpf_defs]:"lift2_lpf'_old = lift2_lpf UNIV"

(*TODO: How should this be done? First lift into lpf', and then lift into vexpr?"*)
consts lift1_vdm :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (('a, '\<alpha>) vexpr \<Rightarrow> ('b, '\<alpha>) vexpr)"
(* Open question: do we really need two layers of lifting? *)

declare lift1_lpf'_def [lpf_defs]

method lpf_simp = (simp add: lpf_defs lpf_transfer; clarsimp?)
method lpf_auto = (lpf_simp; auto)
method lpf_blast = (lpf_simp; blast)

lemma "lpf_Some x = lpf_Some y \<longleftrightarrow> x = y"
  by (metis lpf_Some.rep_eq option.inject)

lemma "lpf_Some x = lpf_Some y \<longleftrightarrow> x = y"
apply (lpf_simp)
done

(*How do I prove these?*)
lemma all_lpf_transfer [lpf_transfer]:
"(\<forall>x::'a lpf. P x) = (\<forall>x::'a option. P (Abs_lpf x))"
apply (safe)
-- {* Subgoal 1 *}
apply (drule_tac x = "Abs_lpf x" in spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "Rep_lpf x" in spec)
apply (simp add: Rep_lpf_inverse)
done

thm exI
lemma ex_lpf_transfer [lpf_transfer]:
"(\<exists>x::'a lpf. P x) = (\<exists>x::'a option. P (Abs_lpf x))"
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "Rep_lpf x" in exI)
apply (simp add: Rep_lpf_inverse)
-- {* Subgoal 2 *}
apply (rule_tac x = "Abs_lpf x" in exI)
apply (assumption)
done

lemma meta_lpf_transfer [lpf_transfer]:
"(\<And>x::'a lpf. P x) \<equiv> (\<And>x::'a option. P (Abs_lpf x))"
apply (rule)
-- {* Subgoal 1 *}
apply (drule_tac x = "Abs_lpf x" in meta_spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "Rep_lpf x" in meta_spec)
apply (simp add: Rep_lpf_inverse)
done

lemma lift1_lpf'_example: "lift1_lpf' card lpf_None = lpf_None"
apply (lpf_simp)
done

lemma lift1_lpf'_example: "lift1_lpf' card (lpf_Some {1,2,3}) = lpf_Some 3"
apply (lpf_simp)
(* We need ex_lpf_transfer *)
oops
end