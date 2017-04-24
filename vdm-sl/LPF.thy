(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: LPF.thy                                                              *)
(* Authors: Casper Thule and Frank Zeyda                                      *)
(* Emails: casper.thule@eng.au.dk and frank.zeyda@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 31 Mar 2017 *)

section {* Logic of Partial Functions *}

text {* 
  This theory sets up the prerequisites to reason about partial functions.
  This includes a type definition and lifting functors along with named theorems 
  and tactics.
*}

theory LPF
imports  
  "LPF_Utilities"
  "~~/src/Tools/Adhoc_Overloading"
  "~~/src/HOL/Library/Monad_Syntax" (* Necessary for the bind operator *)
  "~~/src/HOL/Eisbach/Eisbach"
begin

subsection {* Defining the LPF Type and Basic Lifting. *}

text {* 
  In this section we define the lpf type along with basic lifting of HOL values 
  into the lpf type. Furthermore, we give a definition of definedness and set 
  up two theorems: lpf\_defs and lpf\_transfer.
 *}

text {*
  Below we define a new type to represent values in LPF. Effectively, we encode
  these as @{type option} types where @{const None} will be used to represent
  the undefined value of our LPF logic embedding.
*}

typedef 'a lpf = "UNIV :: 'a option set"
by (rule UNIV_witness)

text {*
  The two theorems lpf\_defs and lpf\_transfer are collection of proofs.
  lpf\_defs contains LPF definition aximos, such as a definition of definedness.
  lpf\_transfer contains LPF transfer laws, such as lifting values of HOL 
  types into values of the @{type lpf} type.
*}

named_theorems lpf_defs "lpf definitional axioms"
named_theorems lpf_transfer "lpf transfer laws"

lemmas Abs_lpf_inject_sym = sym [OF Abs_lpf_inject]
lemmas Rep_lpf_inject_sym = sym [OF Rep_lpf_inject]
  
declare Rep_lpf_inverse [lpf_transfer]
declare Abs_lpf_inverse [simplified, lpf_transfer]
declare Rep_lpf_inject_sym [lpf_transfer]
declare Abs_lpf_inject [simplified, lpf_transfer]

text {* Lifting of values into @{type lpf} is set up. *}

setup_lifting type_definition_lpf

text {* Extract the value wrapped in @{type lpf}. *}

lift_definition lpf_the :: "'a lpf \<Rightarrow> 'a" is "(\<lambda>x . (the \<circ> Rep_lpf) x)" .

declare lpf_the.rep_eq [lpf_transfer]

text {* Lift a value into a defined @{type lpf} value. *}

lift_definition lpf_Some :: "'a \<Rightarrow> 'a lpf" is "Some" .

declare lpf_Some.rep_eq [lpf_transfer]

text {* The @{type lpf} value for undefined. *}

lift_definition lpf_None :: "'a lpf" ("\<bottom>\<^sub>L") is "None" .
declare lpf_None.rep_eq [lpf_transfer]

lift_definition lpf_True :: "bool lpf" ("true\<^sub>L") is "lpf_Some(True)" .
declare lpf_True.rep_eq [lpf_transfer]

lift_definition lpf_False :: "bool lpf" ("false\<^sub>L") is "lpf_Some(False)" .
declare lpf_False.rep_eq [lpf_transfer]

text {* 
  Definition of definedness for LPF values. 
  A value of type @{type lpf} is defined if it is not @{const lpf_None}.   
*}

definition defined :: "'a lpf \<Rightarrow> bool" ("\<D>'(_')") where
"defined x \<equiv> (x \<noteq> \<bottom>\<^sub>L)"

declare defined_def [lpf_defs]

subsection {* Lifting of Operators *}
text {* This section introduces lifting of unary, binary and ternary operators 
  into the @{type lpf} type *}

text {*
  The following function checks if an input x satisfies a predicate (belongs to
  a set). If it does belong to the set, then the function returns the value 
  wrapped in the @{type lpf} type. If it does not belong to the set, then the 
  functions returns  @{const lpf_None}.
*}

definition lpfSat :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a lpf" where
"lpfSat u a = (if a\<in>u then lpf_Some a else \<bottom>\<^sub>L)"

declare lpfSat_def [lpf_defs]

text {* Overload of the bind operator for @{type lpf} values. *}

definition lift_bind :: "'a lpf \<Rightarrow> ('a \<Rightarrow> 'b lpf) \<Rightarrow> 'b lpf" where
[lpf_defs]: "lift_bind a f = 
  (if \<D>(a) then  (f \<circ> the \<circ> Rep_lpf) a else \<bottom>\<^sub>L)"

adhoc_overloading
bind lift_bind


subsubsection {* Lifting of Unary Operators *}

text {* lift1\_lpf takes a set, which is a predicate on the input values, 
  a total HOL function taking one argument and turns it into a function on 
  @{type lpf} types. The resulting value is defined if (1) each input is defined
  and (2) the input satisfies the predicate. 
*}

lift_definition lift1_lpf :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" is 
"(\<lambda> u f x . (x\<bind>lpfSat u)\<bind> lpf_Some \<circ> f)" .

declare lift1_lpf.rep_eq [lpf_transfer]

lift_definition lift1_lpf' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" is
"(\<lambda> f . lift1_lpf UNIV f)" .

declare lift1_lpf'.rep_eq [lpf_transfer]

subsubsection {* Lifting of Binary Operators *}

text {* Similar to lift1\_bind. *}

lift_definition lift2_lpf :: 
  "('a * 'b) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf)" is
  "(\<lambda> u f v1 v2. 
  do { x \<leftarrow> v1; y \<leftarrow> v2; lpfSat u (x, y) } \<bind> lpf_Some \<circ> uncurry f)" .

declare lift2_lpf.transfer [lpf_transfer]
declare lift2_lpf_def [lpf_defs]

lift_definition lift2_lpf' :: 
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf)" is 
  "lift2_lpf UNIV" .

declare lift2_lpf'.rep_eq [lpf_transfer]

subsubsection {* Lifting of Ternary Operators. *}

text {* Here we define the lifting functor for ternary operators. *}

lift_definition lift3_lpf :: 
  "('a * 'b * 'c) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf \<Rightarrow> 'd lpf)" is
"(\<lambda> ABC f v1 v2 v3. do { x \<leftarrow> v1; y \<leftarrow> v2; z \<leftarrow> v3; lpfSat ABC (x, y, z) } \<bind> lpf_Some \<circ> (\<lambda> (x,y,z). f x y z))" .

text {*  Three tactics are created for use in proofs. *}

method lpf_simp = (simp add: lpf_defs lpf_transfer; clarsimp?)
method lpf_auto = (lpf_simp; auto)
method lpf_blast = (lpf_simp; blast)
                                                 
subsection {* Proof Examples *}
text {* In this section we illustrate the use of the proof tactics along with 
  proving useful laws *}

lemma "(lpf_Some x = lpf_Some y) \<longleftrightarrow> (x = y)"
by (lpf_simp)

lemma all_lpf_transfer [lpf_transfer]:
"(\<forall>x::'a lpf. P x) = (\<forall>x::'a option. P (Abs_lpf x))" 
apply (safe)
-- {* Subgoal 1 *}
apply (drule_tac x = "Abs_lpf x" in spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "Rep_lpf x" in spec)
by (simp add: Rep_lpf_inverse)

lemma ex_lpf_transfer [lpf_transfer]:
"(\<exists>x::'a lpf. P x) = (\<exists>x::'a option. P (Abs_lpf x))"
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "Rep_lpf x" in exI)
apply (simp add: Rep_lpf_inverse)
-- {* Subgoal 2 *}
apply (rule_tac x = "Abs_lpf x" in exI)
by (assumption)

lemma meta_lpf_transfer [lpf_transfer]:
"(\<And>x::'a lpf. P x) \<equiv> (\<And>x::'a option. P (Abs_lpf x))" 
apply (rule)
-- {* Subgoal 1 *}
apply (drule_tac x = "Abs_lpf x" in meta_spec)
apply (assumption)
-- {* Subgoal 2 *}
apply (drule_tac x = "Rep_lpf x" in meta_spec)
by (simp add: Rep_lpf_inverse)

lemma lifted_card_undefined_example: "lift1_lpf' card \<bottom>\<^sub>L = \<bottom>\<^sub>L"
by (lpf_simp)

lemma lifted_union_undefined_undefined_example: "lift2_lpf' union \<bottom>\<^sub>L \<bottom>\<^sub>L = \<bottom>\<^sub>L"
by (lpf_simp)

lemma lifted_union_defined_undefined_example: "lift2_lpf' union (lpf_Some {True}) \<bottom>\<^sub>L = \<bottom>\<^sub>L"
by (lpf_simp)

lemma lifted_union_defined_defined_example: "lift2_lpf' union (lpf_Some {True}) (lpf_Some {False}) = lpf_Some(union {True} {False} )"
by (lpf_simp)

lemma lifted_card_defined_example: "lift1_lpf' card (lpf_Some ({1,2,3}::nat set)) = lpf_Some 3"
by (lpf_simp)

lemma lpf_The_Some : "lpf_the (lpf_Some a) = a"
apply (simp add: lpf_Some_def)
apply (simp add: lpf_the_def)
by (simp add: Abs_lpf_inverse)

end