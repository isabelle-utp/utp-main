(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: VDM_LPF_Operators.thy                                                *)
(* Authors: Casper Thule, Frank Zeyda and Simon Foster                        *)
(* Emails: casper.thule@eng.au.dk and {frank.zeyda, simon.foster}@york.ac.uk  *) 
(******************************************************************************)
(* LAST REVIEWED: 31 Mar 2017 *)
section {* Operators for the Logic of Partial Functions *}

text {* 
  This theory contains the type used to represent undefinedness and sets up 
  basic lifting functors. Furthermore, tactics and named theorems are created. 
*}

text {* \todo{
  Define the type nat1
  Define the type seq1
  Define the type inmap
  Define numeric operators to take arguments of different types
  Do we need to restrict certain operations to certain types?
  Define infix operators}
*}

theory LPF_Operators
imports LPF Transcendental
begin recall_syntax

text {*
  Below we define unary operators on the @{type lpf} type using the lifting 
  function @{const lift1_lpf'}.
*}
subsection {* Unary Operators *}

-- {* \todo{Define the following operators:
  Sequence unary operators: inds (Define for nat1 type).
  Map unary operators: inverse (Define for type inmap).} 
*}

subsubsection {* Boolean Unary Operators *}

definition not_lpf :: "bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "not_lpf = lift1_lpf' Not"

subsubsection {* Numeric Unary Operators *}

instantiation lpf :: (uminus) uminus
begin
definition uminus_lpf :: "'a lpf \<Rightarrow> 'a lpf" where
[lpf_defs]: "uminus_lpf = lift1_lpf' uminus"
instance ..
end

definition abs_lpf :: "real lpf \<Rightarrow> real lpf" where
[lpf_defs]: "abs_lpf = lift1_lpf' abs"

definition floor_lpf :: "real lpf \<Rightarrow> int lpf" where
[lpf_defs]: "floor_lpf = lift1_lpf' floor"

definition len_lpf :: "'a list lpf \<Rightarrow> nat lpf" where
[lpf_defs]: "len_lpf = lift1_lpf' length"

subsubsection {* Set Unary Operators *}

definition card_lpf :: "'a set lpf \<Rightarrow> nat lpf" where
[lpf_defs]: "card_lpf = lift1_lpf' card"

definition dunion_lpf :: "'a set set lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "dunion_lpf = lift1_lpf' Union"

definition dinter_lpf :: "'a set set lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "dinter_lpf = lift1_lpf' Inter"

definition power_lpf :: "'a set lpf \<Rightarrow> 'a set set lpf" where
[lpf_defs]: "power_lpf = lift1_lpf' Pow"

subsubsection {* Sequence Unary Operators *}

definition hd_lpf :: "'a list lpf \<Rightarrow> 'a lpf" where
[lpf_defs]: "hd_lpf = lift1_lpf {x . x \<noteq> []} hd" 

definition tl_lpf :: "'a list lpf \<Rightarrow> 'a list lpf" where
[lpf_defs]: "tl_lpf = lift1_lpf {x. x \<noteq> []} tl"

definition elems_lpf :: "'a list lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "elems_lpf = lift1_lpf' set"

(*
definition inds_nat1_lpf :: "'a list lpf \<Rightarrow> nat1 set lpf" where
[lpf_defs]: "inds_nat1_lpf = lift1_lpf {x . x \<noteq> []} (\<lambda>x . {1..length x})"
*)

-- {* \todo{Define inds\_lpf for nat1} *}

definition inds_lpf :: "'a list lpf \<Rightarrow> nat set lpf" where
[lpf_defs]: "inds_lpf = lift1_lpf {x . x \<noteq> []} (\<lambda>x . {1..length x})"

definition reverse_lpf :: "'a list lpf \<Rightarrow> 'a list lpf" where
[lpf_defs]: "reverse_lpf = lift1_lpf' rev"

definition conc_lpf :: "'a list list lpf \<Rightarrow> 'a list lpf" where
[lpf_defs]: "conc_lpf = lift1_lpf' concat"

subsubsection {* Map Unary Operators *}

definition dom_lpf :: "('a,'b) map lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "dom_lpf = lift1_lpf' dom"

definition rng_lpf :: "('a,'b) map lpf \<Rightarrow> 'b set lpf" where
[lpf_defs]: "rng_lpf = lift1_lpf' ran"

definition merge_lpf :: "('a, 'b) map set lpf \<Rightarrow> ('a, 'b) map lpf" where
[lpf_defs]: "merge_lpf = lift1_lpf' merge"

subsection {* Binary Operators *}

subsubsection {* Polymorphic Binary Operators  *}

definition equal_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "equal_lpf = lift2_lpf' (op =)"

definition not_equal_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "not_equal_lpf = lift2_lpf' (op \<noteq>)"

subsubsection {* Boolean Binary Operators  *}

definition conj_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "conj_lpf = lift2_lpf' conj"

definition disj_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "disj_lpf = lift2_lpf' disj"

definition implies_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "implies_lpf = lift2_lpf' implies"

definition biimplication_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "biimplication_lpf = lift2_lpf' iff"

subsubsection {* Numeric Binary Operators  *} 

instantiation lpf :: (plus) plus
begin
  definition plus_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [lpf_defs]: "plus_lpf = lift2_lpf' (op +)"
  instance ..
end

instantiation lpf :: (minus) minus
begin
  definition minus_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [lpf_defs]: "minus_lpf = lift2_lpf' (op -)"
  instance ..
end

instantiation lpf :: (times) times
begin
 definition times_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [lpf_defs]: "times_lpf = lift2_lpf' (op *)"
  instance ..
end

instantiation lpf :: ("{zero,divide}") divide
begin
  definition divide_option :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [lpf_defs]: "divide_option = lift2_lpf {(x,y) . y \<noteq> 0} divide"
  instance ..
end

definition div_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where 
[lpf_defs]: "div_lpf = lift2_lpf {(x,y) . y\<noteq>0} (op div)"

definition rem_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where
[lpf_defs]: "rem_lpf = lift2_lpf {(x,y) . y\<noteq>0} (op mod)"

definition mod_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where
[lpf_defs]: "mod_lpf = rem_lpf"

definition power_nat_lpf :: "'a::power lpf \<Rightarrow> nat lpf \<Rightarrow> 'a lpf" where
[lpf_defs]: "power_nat_lpf = lift2_lpf' (op ^) "

-- {* \todo{Define power for int and nat1 exponent} *}

definition power_real_lpf :: "'a::ln lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
[lpf_defs]: "power_real_lpf = lift2_lpf' (op powr) "

consts  power_num_lpf :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"

adhoc_overloading
power_num_lpf power_nat_lpf and
power_num_lpf power_real_lpf

definition slt_lpf :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "slt_lpf = lift2_lpf' (op <)"

definition lte_lpf :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "lte_lpf = lift2_lpf' (op \<le>)"

definition sgt_lpf :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "sgt_lpf = lift2_lpf' (op >)"

definition gte_lpf :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "gte_lpf = lift2_lpf' (op \<ge>)"

subsubsection {* Record Binary Operators *}

-- {* \todo{
  Define field select
  Define is}
*}

subsubsection {* Set Binary Operators *}

definition in_lpf :: "'a lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "in_lpf = lift2_lpf' (op\<in>)"

definition not_in_lpf :: "'a lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "not_in_lpf = lift2_lpf' (op\<notin>)"

definition union_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "union_lpf = lift2_lpf' (op\<union>)"

definition intersect_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "intersect_lpf = lift2_lpf' (op\<inter>)"

definition difference_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "difference_lpf = lift2_lpf' (op -)"

definition subset_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "subset_lpf = lift2_lpf' (op \<subseteq>)"

definition psubset_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "psubset_lpf = lift2_lpf' (op \<subset>)"

subsubsection {* Sequence Binary Operators *}

definition conc_seq_lpf :: "'a list lpf \<Rightarrow> 'a list lpf \<Rightarrow> 'a list lpf" where
[lpf_defs]: "conc_seq_lpf = lift2_lpf' (op @)"

definition seq_mod_lpf :: "'a list lpf \<Rightarrow> (nat, 'a) map lpf \<Rightarrow> 'a list lpf" where
[lpf_defs]: "seq_mod_lpf = lift2_lpf' (\<lambda>ls m.
  [if i \<in> (dom m) then (map_apply m i) else ls!i. i <- [0..<(length ls)]])"

definition seq_index_lpf :: "'a list lpf \<Rightarrow> nat lpf \<Rightarrow> 'a lpf" where
[lpf_defs]: "seq_index_lpf = lift2_lpf {(x,y) . y < (length x) \<and> y > 0} (op !)"


subsubsection {* Comprehensions *}
(*
  First the set must be defined
  Second the predicate of the values of the set must be defined
  Third the function over the values of the set where the predicate is true must be defined
*)

text {* Utility function that converts 'a lpf set to 'a set lpf.
  If any value in the source set is undefined, then the target set is undefined
*}

definition set_sequence_lpf :: "'a lpf set \<Rightarrow> 'a set lpf" where
[lpf_defs]: "set_sequence_lpf xs = (if \<exists>x\<in>xs . \<not>\<D>(x) then lpf_None 
  else lpf_Some {y | x y . y = lpf_the x \<and> x\<in>xs})"

definition set_comprehension_lpf :: "('a \<Rightarrow> 'b lpf) \<Rightarrow> 'a set lpf \<Rightarrow> ('a \<Rightarrow> bool lpf) \<Rightarrow> 'b set lpf" where
[lpf_defs]: "set_comprehension_lpf f xs pred = 
  (if (\<D>(xs) \<and> (\<forall>x\<in>(lpf_the xs) . \<D>(pred x)) \<and> 
    (\<forall>x\<in>(lpf_the xs) . if pred x = lpf_True then \<D>(f x) else True))
  then set_sequence_lpf {y | x y . y = f x \<and> x\<in>(lpf_the xs) \<and> (pred x = lpf_True)}
  else lpf_None)"

text {* Proof that a function returning undefined for values for which the 
  predicate holds makes the comprehension undefined. 
*}

lemma set_comprehension_lpf_undefined_fun: "(set_comprehension_lpf (\<lambda>x . lpf_None) 
  (lpf_Some {1::nat,2,3}) (\<lambda>x . lpf_True)) = lpf_None"
apply(simp add: set_comprehension_lpf_def)
apply(simp add: defined_def)
apply(simp add: lpf_The_Some)
done

text {* Proof that a predicate returning undefined makes the comprehension undefined. *}

lemma set_comprehension_lpf_undefined_pred: "(set_comprehension_lpf (\<lambda>x . lpf_Some x) 
  (lpf_Some {1::nat,2,3}) (\<lambda>x . lpf_None)) = lpf_None"
apply(simp add: set_comprehension_lpf_def)
apply(simp add: defined_def)
apply(simp add: lpf_Some_The)
done

text {* Proof that a an undefined set makes the comprehension undefined. *}

lemma set_comprehension_lpf_undefined_set: "(set_comprehension_lpf (\<lambda>x . lpf_Some x) 
  lpf_None (\<lambda>x . lpf_None)) = lpf_None"
apply(simp add: set_comprehension_lpf_def)
apply(simp add: defined_def)
done

end
