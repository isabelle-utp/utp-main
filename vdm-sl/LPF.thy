section {* Logic of Partial Functions *}

theory LPF
imports Main Eisbach utp
begin

text {* New type 'lpf' corresponding to 'a option *}  
typedef 'a lpf = "UNIV :: 'a option set"
apply(rule Set.UNIV_witness)
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
  
  
text {*The lifting is set up*}
setup_lifting type_definition_lpf

text {*lpf_Some lifts a hol type into a defined lpf type*}
(*TODO: How can one define this as a function e.g. lpf_Some x = Some x*)
lift_definition lpf_Some :: "'a \<Rightarrow> 'a lpf"
is "Some" .

text {* The lpf value for undefined *}
lift_definition lpf_None :: "'a lpf"
is "None" .

text {* Definition that determines whether a lpf value s defined or not  *}
definition defined :: "'a lpf \<Rightarrow> bool" ("\<D>'(_')") where
"defined x \<longleftrightarrow> (x \<noteq> lpf_None)"

declare lpf_Some.rep_eq [lpf_transfer]
declare lpf_None.rep_eq [lpf_transfer]
declare defined_def [lpf_defs]

text {* The following function checks if an input x satisfies a predicate (belongs to a set). If
  it does then it returns the value backed, wrapped up in the option type, otherwise it returns None. *}

definition sat :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a option" where
"sat P x = (if (x \<in> P) then Some x else None)"

definition upfun :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a option \<Rightarrow> 'b option)" where
[upred_defs]: "upfun A f = (\<lambda> x. (x \<bind> sat A) \<bind> Some \<circ> f)" 

(*definition lpfSat :: "'a set \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
"lpfSat u a = 
  (case Rep_lpf a of 
    Some (x) \<Rightarrow> if(x\<in>u) then a else lpf_None | 
    None \<Rightarrow> lpf_None)"

definition applyFunc :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a lpf \<Rightarrow> 'b lpf" where
"applyFunc f = Abs_lpf \<circ> Some \<circ> f \<circ> the \<circ> Rep_lpf"*)

text {* lift1_lpf' takes a set which is a predicate on the input values, a total HOL function and turns
  it into a function on option types. The resulting value is defined if (1) each input is defined
  and (2) the input satisfies the predicate. *}
(*definition lift1_lpf' :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" where
"lift1_lpf' u f = (\<lambda> x. (if ( \<D>(lpfSat u x)) then applyFunc f x else lpf_None))"  *)

definition lpfSat :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a lpf" where
"lpfSat u a = (if a\<in>u then lpf_Some a else lpf_None)"

definition lift1_bind :: "'a lpf \<Rightarrow> ('a \<Rightarrow> 'b lpf) \<Rightarrow> 'b lpf" where
"lift1_bind a f = (if \<D>(a) then  (f \<circ> the \<circ> Rep_lpf) a else lpf_None)"

adhoc_overloading
bind lift1_bind

definition lift1_lpf :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" where
"lift1_lpf u f = (\<lambda>x . (x\<bind>lpfSat u)\<bind> lpf_Some \<circ> f)"

consts lift1_lpf :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)"
(* Perhaps you can define the above lifting functor properly. *)

consts lift1_vdm :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (('a, '\<alpha>) vexpr \<Rightarrow> ('b, '\<alpha>) vexpr)"
(* Open question: do we really need two layers of lifting? *)
  
definition lift1_lpf' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a lpf \<Rightarrow> 'b lpf)" where
"lift1_lpf' = lift1_lpf UNIV"

(* declare lift1_lpf.rep_eq [lpf_transfer] *)
declare lift1_lpf'_def [lpf_defs]

(* Without instantiation, define your own syntax. *)

(* definition uminus_lpf :: "'a::uminus lpf \<Rightarrow> 'a lpf" ("-\<^sub>L _" [81] 80) where
"uminus_lpf = lift1_lpf' uminus" *)

(* Without instantiation, use the type class syntax for uminus. *)

instantiation lpf :: (uminus) uminus
begin
definition uminus_lpf :: "'a lpf \<Rightarrow> 'a lpf" where
"uminus_lpf = lift1_lpf' uminus"
instance ..
end

method lpf_simp = (simp add: lpf_defs lpf_transfer; clarsimp?)
method lpf_auto = (lpf_simp; auto)
method lpf_blast = (lpf_simp; blast)

lemma "lpf_Some x = lpf_Some y \<longleftrightarrow> x = y"
  by (metis lpf_Some.rep_eq option.inject)

lemma "lpf_Some x = lpf_Some y \<longleftrightarrow> x = y"
(* apply (transfer) *)
apply (lpf_simp)
done

lemma all_lpf_transfer [lpf_transfer]:
"(\<forall>x::'a lpf. P x) = (\<forall>x::'a option. P (Abs_lpf x))" sorry

lemma ex_lpf_transfer [lpf_transfer]:
"(\<exists>x::'a lpf. P x) = (\<exists>x::'a option. P (Abs_lpf x))" sorry

lemma meta_lpf_transfer [lpf_transfer]:
"(\<And>x::'a lpf. P x) \<equiv> (\<And>x::'a option. P (Abs_lpf x))" sorry 

thm lpf_transfer
end