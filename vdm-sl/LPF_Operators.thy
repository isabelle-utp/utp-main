(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: VDM_LPF_Operators.thy                                                *)
(* Authors: Casper Thule, Frank Zeyda and Simon Foster                        *)
(* Emails: casper.thule@eng.au.dk and {frank.zeyda, simon.foster}@york.ac.uk  *) 
(******************************************************************************)
(* LAST REVIEWED: 22 Mar 2017 *)
(* 
  TODO: 
  Define the type nat1
  Define the type seq1
  Define the type inmap
  Define numeric operators to take arguments of different types
  Do we need to restrict certain operations to certain types?
*)

section {* Operators for the Logic of Partial Functions*}

theory LPF_Operators
imports LPF Transcendental
begin recall_syntax

term "x powr y::real"

text {*
  Below we define unary operators on the @{type lpf} type using the lifting 
  function @{const lift1_lpf'}.
*}
subsection {* Unary operators *}
subsubsection {* Boolean unary operators *}

definition not_lpf :: "bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "not_lpf = lift1_lpf' Not"

subsubsection {* Numeric unary operators *}

instantiation lpf :: (uminus) uminus
begin
definition uminus_lpf :: "'a lpf \<Rightarrow> 'a lpf" where
"uminus_lpf = lift1_lpf' uminus"
instance ..
end

definition abs_lpf :: "real lpf \<Rightarrow> real lpf" where
[lpf_defs]: "abs_lpf = lift1_lpf' abs"

definition floor_lpf :: "real lpf \<Rightarrow> int lpf" where
[lpf_defs]: "floor_lpf = lift1_lpf' floor"

definition len_lpf :: "'a list lpf \<Rightarrow> nat lpf" where
[lpf_defs]: "len_lpf = lift1_lpf' length"

subsubsection {* Set unary operators *}

definition card_lpf :: "'a set lpf \<Rightarrow> nat lpf" where
[lpf_defs]: "card_lpf = lift1_lpf' card"

definition dunion_lpf :: "'a set set lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "dunion_lpf = lift1_lpf' Union"

definition dinter_lpf :: "'a set set lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "dinter_lpf = lift1_lpf' Inter"

definition power_lpf :: "'a set lpf \<Rightarrow> 'a set set lpf" where
[lpf_defs]: "power_lpf = lift1_lpf' Pow"

subsubsection {* Sequence unary operators *}

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

(* TODO: Define this for nat1 *)
definition inds_lpf :: "'a list lpf \<Rightarrow> nat set lpf" where
[lpf_defs]: "inds_lpf = lift1_lpf {x . x \<noteq> []} (\<lambda>x . {1..length x})"

definition reverse_lpf :: "'a list lpf \<Rightarrow> 'a list lpf" where
[lpf_defs]: "reverse_lpf = lift1_lpf' rev"

definition conc_lpf :: "'a list list lpf \<Rightarrow> 'a list lpf" where
[lpf_defs]: "conc_lpf = lift1_lpf' concat"

subsubsection {* Map unary operators *}

definition dom_lpf :: "('a,'b) map lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "dom_lpf = lift1_lpf' dom"

definition rng_lpf :: "('a,'b) map lpf \<Rightarrow> 'b set lpf" where
[lpf_defs]: "rng_lpf = lift1_lpf' ran"

definition merge_lpf :: "('a, 'b) map set lpf \<Rightarrow> ('a, 'b) map lpf" where
[lpf_defs]: "merge_lpf = lift1_lpf' merge"

-- {* \todo{Define the following operators: 
  Sequence unary operators: inds(Define for nat1 type).
  Map unary operators: inverse(Define for type inmap).  } 
*}
subsection {* Binary operators *}

subsubsection {* Polymorphic binary operators  *}

definition equal_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "equal_lpf = lift2_lpf' (op =)"

definition not_equal_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "not_equal_lpf = lift2_lpf' (op \<noteq>)"

subsubsection {* Boolean binary operators  *}

definition conj_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "conj_lpf = lift2_lpf' conj"

definition disj_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "disj_lpf = lift2_lpf' disj"

definition implies_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "implies_lpf = lift2_lpf' implies"

definition biimplication_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "biimplication_lpf = lift2_lpf' iff"

subsubsection {* Numeric binary operators  *} 

instantiation lpf :: (plus) plus
begin
  definition plus_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [upred_defs]: "plus_lpf = lift2_lpf' (op +)"
  instance ..
end

instantiation lpf :: (minus) minus
begin
  definition minus_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [upred_defs]: "minus_lpf = lift2_lpf' (op -)"
  instance ..
end

instantiation lpf :: (times) times
begin
 definition times_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [upred_defs]: "times_lpf = lift2_lpf' (op *)"
  instance ..
end

instantiation lpf :: ("{zero,divide}") divide
begin
  definition divide_option :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [lpf_defs]: "divide_option = lift2_lpf {(x,y) . y \<noteq> 0} divide"
  instance ..
end

definition div_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where 
"div_lpf = lift2_lpf {(x,y) . y\<noteq>0} (op div)"

definition rem_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where
"rem_lpf = lift2_lpf {(x,y) . y\<noteq>0} (op mod)"

definition mod_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where
"mod_lpf = rem_lpf"

(* TODO: Define power for int and nat1 exponent *)

definition power_nat_lpf :: "'a::power lpf \<Rightarrow> nat lpf \<Rightarrow> 'a lpf" where
"power_nat_lpf = lift2_lpf' (op ^) "

definition power_real_lpf :: "'a::ln lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
"power_real_lpf = lift2_lpf' (op powr) "

consts  power_num_lpf :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"

adhoc_overloading
power_num_lpf power_nat_lpf and
power_num_lpf power_real_lpf

definition slt_lpf :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
"slt_lpf = lift2_lpf' (op <)"

definition lte_lpf :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
"lte_lpf = lift2_lpf' (op \<le>)"

definition sgt_lpf :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
"sgt_lpf = lift2_lpf' (op >)"

definition gte_lpf :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
"gte_lpf = lift2_lpf' (op \<ge>)"

subsubsection {* Record binary operators *}
(* 
  TODO 
  Define field select
  Define is  
 *)

subsubsection {* Set binary operators *}

definition in_lpf :: "'a lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" where
"in_lpf = lift2_lpf' (op\<in>)"

definition not_in_lpf :: "'a lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" where
"not_in_lpf = lift2_lpf' (op\<notin>)"

definition union_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" where
"union_lpf = lift2_lpf' (op\<union>)"

definition intersect_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" where
"intersect_lpf = lift2_lpf' (op\<inter>)"

definition difference_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" where
"difference_lpf = lift2_lpf' (op -)"

definition subset_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" where
"subset_lpf = lift2_lpf' (op \<subseteq>)"

definition psubset_lpf :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" where
"psubset_lpf = lift2_lpf' (op \<subset>)"

subsubsection {* Sequence binary operators *}

definition conc_seq_lpf :: "'a list lpf \<Rightarrow> 'a list lpf \<Rightarrow> 'a list lpf" where
"conc_seq_lpf = lift2_lpf' (op @)"

declare [[show_types]]

definition seq_mod_lpf :: "'a list lpf \<Rightarrow> (nat, 'a) map lpf \<Rightarrow> 'a list lpf" where
"seq_mod_lpf = lift2_lpf' (\<lambda>ls m.
  [if i \<in> (dom m) then (map_apply m i) else ls!i. i <- [0..<(length ls)]])"

definition seq_index_lpf :: "'a list lpf \<Rightarrow> nat lpf \<Rightarrow> 'a lpf" where
"seq_index_lpf = lift2_lpf {(x,y) . y < (length x) \<and> y > 0} (op !)"

end
