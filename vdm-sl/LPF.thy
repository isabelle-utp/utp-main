(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: LPF.thy                                                              *)
(* Authors: Casper Thule and Frank Zeyda                                      *)
(* Emails: casper.thule@eng.au.dk and frank.zeyda@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 22 Mar 2017 *)

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

text {*
  The two theorems lpf_defs and lpf_transfer are collection of proofs.
  lpf_defs contains LPF definition aximos, such as a definition of definedness.
  lpf_transfer contains LPF transfer laws, such as lifting values of HOL types 
  into values of the LPF type
*}

named_theorems lpf_defs "lpf definitional axioms"
named_theorems lpf_transfer "lpf transfer laws"
  
lemmas Abs_lpf_inject_sym = sym [OF Abs_lpf_inject]
lemmas Rep_lpf_inject_sym = sym [OF Rep_lpf_inject]
  
declare Rep_lpf_inverse [lpf_transfer]
declare Abs_lpf_inverse [simplified, lpf_transfer]
declare Rep_lpf_inject_sym [lpf_transfer]
declare Abs_lpf_inject [simplified, lpf_transfer]

text {* The lifting of values into the type @{type lpf} is set up *}
setup_lifting type_definition_lpf

lift_definition lpf_the :: "'a lpf \<Rightarrow> 'a" is "(\<lambda>x . (the \<circ> Rep_lpf) x)" .

text {* Here we define how to lift a value into a defined @{type lpf} value *}

lift_definition lpf_Some :: "'a \<Rightarrow> 'a lpf" is "Some" .

declare lpf_Some.rep_eq [lpf_transfer]

text {* The LPF value for undefined *}

lift_definition lpf_None :: "'a lpf" is "None" .

declare lpf_None.rep_eq [lpf_transfer]

text {* 
  This is a definition of definedness for LPF values.  
  A LPF value is defined if it is not @{const lpf_None}.   
*}
definition defined :: "'a lpf \<Rightarrow> bool" ("\<D>'(_')") where
"defined x \<longleftrightarrow> (x \<noteq> lpf_None)"

declare defined_def [lpf_defs]

subsection {* Lifting of unary operators *}

text {*
  The following function checks if an input x satisfies a predicate (belongs to
  a set). If it does then it returns the value backed, wrapped up in the 
  @{type lpf} type, otherwise it returns @{const lpf_None}.
*}

definition lpfSat :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a lpf" where
"lpfSat u a = (if a\<in>u then lpf_Some a else lpf_None)"

declare lpfSat_def [lpf_defs]

text {* 
  The following function is an overload of the bind operator for the lpf type 
*}

definition lift1_bind :: "'a lpf \<Rightarrow> ('a \<Rightarrow> 'b lpf) \<Rightarrow> 'b lpf" where
[lpf_defs]: "lift1_bind a f = 
  (if \<D>(a) then  (f \<circ> the \<circ> Rep_lpf) a else lpf_None)"

adhoc_overloading
bind lift1_bind

text {* lift1_lpf takes a set, which is a predicate on the input values, 
  a total HOL function taking one argument and turns it into a function on 
  @{type lpf} types. The resulting value is defined if (1) each input is defined
  and (2) the input satisfies the predicate. 
*}

lift_definition lift1_lpf :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" is 
"(\<lambda> u f x . (x\<bind>lpfSat u)\<bind> lpf_Some \<circ> f)" .

declare lift1_lpf.transfer [lpf_transfer]
declare lift1_lpf_def [lpf_defs]

lift_definition lift1_lpf' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" is
"(\<lambda> f . lift1_lpf UNIV f)"
done

declare lift1_lpf'.transfer [lpf_transfer]
declare lift1_lpf'_def [lpf_defs]

subsection {* Lifting of binary operators *}

text {* Lifting of binary operators *}
lift_definition lift2_lpf :: 
  "('a * 'b) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf)" is
  "(\<lambda> u f v1 v2. 
  do { x \<leftarrow> v1; y \<leftarrow> v2; lpfSat u (x, y) } \<bind> lpf_Some \<circ> uncurry f)" .

declare lift2_lpf.transfer [lpf_transfer]
declare lift2_lpf_def [lpf_defs]

lift_definition lift2_lpf' :: 
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf)" is 
  "lift2_lpf UNIV"
done

declare lift2_lpf'.transfer [lpf_transfer]
declare lift2_lpf'_def [lpf_defs]

subsection {* Lifting of ternary operators *}

lift_definition lift3_lpf :: 
  "('a * 'b * 'c) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf \<Rightarrow> 'c lpf \<Rightarrow> 'd lpf)" is
"(\<lambda> ABC f v1 v2 v3. do { x \<leftarrow> v1; y \<leftarrow> v2; z \<leftarrow> v3; lpfSat ABC (x, y, z) } \<bind> lpf_Some \<circ> (\<lambda> (x,y,z). f x y z))" .

text {*  Three tactics are created for use in proofs. *}
method lpf_simp = (simp add: lpf_defs lpf_transfer; clarsimp?)
method lpf_auto = (lpf_simp; auto)
method lpf_blast = (lpf_simp; blast)
                                                                        
subsection {* Examples *}

lemma "lpf_Some x = lpf_Some y \<longleftrightarrow> x = y"
  by (metis lpf_Some.rep_eq option.inject)

lemma "lpf_Some x = lpf_Some y \<longleftrightarrow> x = y"
apply (lpf_simp)
done

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

lemma lifted_card_undefined_example: "lift1_lpf' card lpf_None = lpf_None"
apply (lpf_simp)
done

lemma lifted_card_defined_example: "lift1_lpf' card (lpf_Some ({1,2,3}::nat set)) = lpf_Some 3"
apply (lpf_simp)
done


end