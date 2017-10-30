(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: VDM_LPF_Operators.thy                                                *)
(* Authors: Casper Thule, Frank Zeyda and Simon Foster                        *)
(* Emails: casper.thule@eng.au.dk and {frank.zeyda, simon.foster}@york.ac.uk  *) 
(******************************************************************************)
(* LAST REVIEWED: 31 Mar 2017 *)
section {* Operators for the Logic of Partial Functions *}

text {* \todo{
  Define the type nat1
  Define the type seq1
  Define the type inmap
  Define numeric operators to take arguments of different types
  Do we need to restrict certain operations to certain types?
  Define infix operators}
*}

theory LPF_Operators
imports 
  LPF
  LPF_Logic 
  Transcendental
  "../utils/TotalRecall"
  "../utils/Library_Extra/Map_Extra"
  
begin recall_syntax

text {* 
  This theory implements several operators for the @{type lpf} type. 
  Note: The terms @{term true\<^sub>L} @{term false\<^sub>L}, @{term "\<bottom>\<^sub>L"} and @{term "the\<^sub>L"} 
  are defined in the theory @{theory LPF}.
*}

subsection {* Unary Operators *}
text {*
  In this section we define unary operators on the @{type lpf} type using the lifting 
  function @{const lift1_lpf'}.
*}
-- {* \todo{Define the following operators:
  Sequence unary operators: inds (Define for nat1 type).
  Map unary operators: inverse (Define for type inmap).} 
*}

subsubsection {* Boolean Unary Operators *}

(*TODO: This is defined in LPF, as it is part of the basic LPF logic.
definition not_lpf :: "bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "not_lpf = lift1_lpf' Not"*)

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

definition seq_sequence_lpf :: "'a lpf list \<Rightarrow> 'a list lpf" where
[lpf_defs]: "seq_sequence_lpf xs = (
  if List.find (\<lambda>x. x = \<bottom>\<^sub>L) xs \<noteq> None 
  then \<bottom>\<^sub>L 
  else lpf_Some [the\<^sub>L y . y <- xs])"

definition hd_lpf :: "'a list lpf \<Rightarrow> 'a lpf" where
[lpf_defs]: "hd_lpf = lift1_lpf {x . x \<noteq> []} hd" 

definition tl_lpf :: "'a list lpf \<Rightarrow> 'a list lpf" where
[lpf_defs]: "tl_lpf = lift1_lpf {x. x \<noteq> []} tl"

definition elems_lpf :: "'a list lpf \<Rightarrow> 'a set lpf" where
[lpf_defs]: "elems_lpf = lift1_lpf' set"

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
text {*
  In this section we define binary operators on the @{type lpf} type using the lifting 
  function @{const lift2_lpf}.
*}
subsubsection {* Polymorphic Binary Operators  *}

definition equal_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "equal_lpf = lift2_lpf' (op =)"

definition not_equal_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "not_equal_lpf = lift2_lpf' (op \<noteq>)"

subsubsection {* Boolean Binary Operators  *}
  
text {* This definitions are based on the LPF logic described in
Moddelling systems - Practical Tools and techniques in software development
page 71-73 (Kleene logic)*}
(* TODO: These are defined in LPF, as they are part of the basic logic 
definition conj_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "conj_lpf p q = ( if (p = true\<^sub>L \<and> q = true\<^sub>L)
                              then true\<^sub>L
                              else 
                                if (p = false\<^sub>L \<or> q = false\<^sub>L) 
                                then false\<^sub>L 
                                else \<bottom>\<^sub>L)"

definition disj_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "disj_lpf p q = (if(p = true\<^sub>L \<or> q = true\<^sub>L)
                                then true\<^sub>L
                              else if ((p = false\<^sub>L) \<and> (q = false\<^sub>L))
                                then false\<^sub>L
                              else \<bottom>\<^sub>L)"

definition implies_lpf :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" where
[lpf_defs]: "implies_lpf p q = (if(p = false\<^sub>L \<or> q = true\<^sub>L) 
                                  then true\<^sub>L 
                                else if (p = true\<^sub>L \<or> q = false\<^sub>L)
                                  then false\<^sub>L
                                else \<bottom>\<^sub>L)"
*)
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
  [lpf_defs]: "divide_option = lift2_lpf {(x,y) . y \<noteq> 0} (op div)"
  instance ..
end

text {* \todo{Prove that this is equal to ISO} *}
text {* The right value of a mod operation cannot be 0 according to the standard *}
instantiation lpf :: ("{zero, divide, modulo}") modulo 
begin
  definition modulo_lpf :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
  [lpf_defs]: "modulo_lpf =  lift2_lpf {(x,y) . y \<noteq> 0} (op mod)"
  instance ..
end

(* Covered by typeclass *)
(*definition div_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where 
[lpf_defs]: "div_lpf = lift2_lpf {(x,y) . y\<noteq>0} (op div)"*)

text {* \todo{Prove that this is equal to ISO} *}
definition rem_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where
[lpf_defs]: "rem_lpf = lift2_lpf {(x,y) . y\<noteq>0} 
  (\<lambda>l r . 
    if l > 0 
    then l mod (abs(r)) 
    else l mod -(abs(r)))"

(* By typeclass *)
(*definition mod_lpf :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" where
[lpf_defs]: "mod_lpf = rem_lpf"*)

-- {* \todo{Define power for int and nat1 exponent} *}

definition power_nat_lpf :: "'a::power lpf \<Rightarrow> nat lpf \<Rightarrow> 'a lpf" where
[lpf_defs]: "power_nat_lpf = lift2_lpf' (op ^) "

definition power_real_lpf :: "'a::ln lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" where
[lpf_defs]: "power_real_lpf = lift2_lpf' (op powr)"

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
[lpf_defs]: "set_sequence_lpf xs = (if \<exists>x\<in>xs . \<not>\<D>(x) then \<bottom>\<^sub>L 
  else lpf_Some {y | x y . y = lpf_the x \<and> x\<in>xs})"

definition set_comprehension_lpf :: "('a \<Rightarrow> 'b lpf) \<Rightarrow> 'a set lpf \<Rightarrow> ('a \<Rightarrow> bool lpf) \<Rightarrow> 'b set lpf" where
[lpf_defs]: "set_comprehension_lpf f xs pred = 
  (if (\<D>(xs) \<and> (\<forall>x\<in>(lpf_the xs) . \<D>(pred x)) \<and> 
    (\<forall>x\<in>(lpf_the xs) . if pred x = true\<^sub>L then \<D>(f x) else True))
  then set_sequence_lpf {y | x y . y = f x \<and> x\<in>(lpf_the xs) \<and> (pred x = true\<^sub>L)}
  else \<bottom>\<^sub>L)"

value "List.coset [1..100]"

definition seq_comprehension_lpf :: "('a \<Rightarrow> 'b lpf) \<Rightarrow> 'a::linorder set lpf \<Rightarrow> 'b list lpf" where
[lpf_defs]: "seq_comprehension_lpf f xs = (
  if \<D>(xs) 
  then seq_sequence_lpf (map f (List.linorder_class.sorted_list_of_set.F (lpf_the xs))) 
  else \<bottom>\<^sub>L)"

text {* It is a design decision that lpf types should not be nested to avoid types such as:
  'a list lpf set lpf. This will instead be sequenced into 'a list set lpf. 
  When an element is then extracted from the set, then it will be coerced into the lpf type.
  An interesting case here is the current implementation vs the previous one:
  The previous one had @{text "if \<exists>x . \<not>\<D>(f x) then \<bottom>\<^sub>L else ..."}. 
  However, using this in context with x of type @{type lpf} would always give @{term "\<bottom>\<^sub>L"}.
*}
declare [[show_types]]
(*
definition collect_lpf :: "('a lpf \<Rightarrow> bool lpf) \<Rightarrow> 'a set lpf" where
[lpf_defs]:  "collect_lpf f = (
    if \<exists>x . \<not>\<D>(f x) then \<bottom>\<^sub>L
    else set_sequence_lpf {t . (f t) = true\<^sub>L} )"
*)
definition collect_lpf :: "('a lpf \<Rightarrow> bool lpf) \<Rightarrow> 'a set lpf" where
[lpf_defs]:  "collect_lpf f = (
    if (\<forall>x. \<D>(x) \<longrightarrow> \<D>(f x))
    then set_sequence_lpf {t . (f t) = true\<^sub>L}
    else \<bottom>\<^sub>L )"

subsection {* Structure to single Boolean *}
text {* Bounded Universal Quantification *}
definition Ball_lpf :: "'a set lpf \<Rightarrow> ('a lpf \<Rightarrow> bool lpf) \<Rightarrow> bool lpf" where
[lpf_defs]:  "Ball_lpf A P = (
  if \<D>(A) \<and> (\<forall>x \<in>(the\<^sub>L A) . \<D>(P (lpf_Some x)))
  then lpf_Some (\<forall>x\<in>(the\<^sub>L A) . (P (lpf_Some x)) = true\<^sub>L)
  else \<bottom>\<^sub>L)" 

subsection {* Syntax and Translations for the operators defined above *}

syntax
(* Unary Operators *)
(* Boolean Unary Operators *)
"_lpfnot" :: "bool lpf \<Rightarrow> bool lpf" ("\<not>\<^sub>L _" [40] 40)
(* Numeric Unary Operators *)
"_lpfabs" :: "real lpf \<Rightarrow> real lpf" ("\<bar>_\<bar>\<^sub>L") 
"_lpffloor" :: "real lpf \<Rightarrow> int lpf" ("\<lfloor>_\<rfloor>\<^sub>L") 
"_lpflen" :: "'a list lpf \<Rightarrow> nat lpf" ("len\<^sub>L'(_')")
(* Set Unary Operators *)
"_lpfseq_set" :: "'a lpf set \<Rightarrow> 'a set lpf" ("{_}\<^sub>L")
"_lpfcard" :: "'a set lpf \<Rightarrow> nat lpf" ("card\<^sub>L'(_')")
"_lpfdunion" :: "'a set set lpf \<Rightarrow> 'a set lpf" ("\<Union>\<^sub>L")
"_lpfdinter" :: "'a set set lpf \<Rightarrow> 'a set lpf" ("\<Inter>\<^sub>L")
"_lpfpower" :: "'a set lpf \<Rightarrow> 'a set set lpf" ("Pow\<^sub>L'(_')")
(* Sequence Unary Operators *)
"_lpfseq_seq" :: "'a lpf list \<Rightarrow> 'a list lpf" ("[_]\<^sub>L")
"_lpfhd" :: "'a list lpf \<Rightarrow> 'a lpf" ("hd\<^sub>L'(_')")
"_lpftl" :: "'a list lpf \<Rightarrow> 'a list lpf" ("tl\<^sub>L'(_')")
"_lpfelems" :: "'a list lpf \<Rightarrow> 'a set lpf" ("elem\<^sub>L'(_')")
"_lpfinds" :: "'a list lpf \<Rightarrow> nat set lpf" ("inds\<^sub>L'(_')")
"_lpfreverse" :: "'a list lpf \<Rightarrow> 'a list lpf" ("reverse\<^sub>L'(_')")
"_lpfconc" :: "'a list list lpf \<Rightarrow> 'a list lpf" ("conc\<^sub>L'(_')")
(* Map Unary Operators *)
"_lpfdom" :: "('a,'b) map lpf \<Rightarrow> 'a set lpf" ("dom\<^sub>L'(_')")
"_lpfrng" :: "('a,'b) map lpf \<Rightarrow> 'b set lpf" ("rng\<^sub>L'(_')")
"_lpfmerge" :: "('a, 'b) map set lpf \<Rightarrow> ('a, 'b) map lpf" ("merge\<^sub>L'(_')")
(* Binary Operators *)
(* Polymorphic Binary Operators *)
"_lpfequal" :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" (infix "=\<^sub>L" 50) 
"_lpfnot_equal" :: "'a lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" (infix "\<noteq>\<^sub>L" 50)
(* Boolean Binary Operators  *)
(* TODO: These are defined in LPF, as they are part of the basic logic
"_lpfconj" :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" (infixr "\<and>\<^sub>L" 35)
"_lpfdisj" :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" (infixr "\<or>\<^sub>L" 30)
"_lpfimplies" :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" (infixr "\<Rightarrow>\<^sub>L" 25)
*)
"_lpfbiimplication" :: "bool lpf \<Rightarrow> bool lpf \<Rightarrow> bool lpf" (infixr "\<Leftrightarrow>\<^sub>L" 25)
(* Numeric Binary Operators  *)
"_lpfdiv" :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" (infixl "div\<^sub>L" 70)
"_lpfrem" :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" (infixl "rem\<^sub>L" 70) 
(*"_lpfmod" :: "int lpf \<Rightarrow> int lpf \<Rightarrow> int lpf" (infixl "mod\<^sub>L" 70)*)
"_lpfpower_nat" :: "'a::power lpf \<Rightarrow> nat lpf \<Rightarrow> 'a lpf" (infixr "^\<^sub>L" 80)
"_lpfpower_real" :: "'a::ln lpf \<Rightarrow> 'a lpf \<Rightarrow> 'a lpf" (infixr "powr\<^sub>L" 80)
"_lpfslt" :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" (infix "<\<^sub>L" 50)
"_lpflte" :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" (infix "\<le>\<^sub>L" 50)
"_lpfsgt" :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" (infix ">\<^sub>L" 50) 
"_lpfgte" :: "'a::ord lpf \<Rightarrow> 'a lpf \<Rightarrow> bool lpf" (infix "\<ge>\<^sub>L" 50)
(* Record Binary Operators *)
(* Set Binary Operators *)
"_lpfin" :: "'a lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" (infix "\<in>\<^sub>L" 50)
"_lpfnot_in" :: "'a lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" (infix "\<notin>\<^sub>L" 50)
"_lpfunion" :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" (infixl "\<union>\<^sub>L" 65)
"_lpfintersect" :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" (infixl "\<inter>\<^sub>L" 70)
"_lpfdifference" :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> 'a set lpf" ("\<setminus>\<^sub>L")
"_lpfsubset" :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" (infix "\<subseteq>\<^sub>L" 50)
"_lpfpsubset" :: "'a set lpf \<Rightarrow> 'a set lpf \<Rightarrow> bool lpf" (infix "\<subset>\<^sub>L" 50)
(* Sequence Binary Operators *)
"_lpfconc_seq" :: "'a list lpf \<Rightarrow> 'a list lpf \<Rightarrow> 'a list lpf" ("conc\<^sub>L")
"_lpfseq_mod" :: "'a list lpf \<Rightarrow> (nat, 'a) map lpf \<Rightarrow> 'a list lpf" ("++\<^sub>L")
"_lpfseq_index" :: "'a list lpf \<Rightarrow> nat lpf \<Rightarrow> 'a lpf" ("!\<^sub>L")
(* Comprehensions *)
"_collect_lpf" :: "[pttrn, bool] => 'a set" ("(1{_./ _}\<^sub>L)")
(* Structure to single Boolean *)
(*"_ball_lpf" :: "'a set lpf \<Rightarrow> ('a lpf \<Rightarrow> bool lpf) \<Rightarrow> bool lpf" ("\<forall>\<^sub>L _ \<in>\<^sub>L _ .\<^sub>L _")*)
"_lpfBall"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>\<^sub>L_\<in>_./ _)" [0, 0, 10] 10)

translations
(* Unary Operators *)
(* Boolean Unary Operators *)
(* TODO: This are defined in LPF, as they are part of the basic logic
"\<not>\<^sub>L p" == "CONST not_lpf p" 
*)
(* Numeric Unary Operators *)
"\<bar>x\<bar>\<^sub>L" == "CONST abs_lpf x"
"\<lfloor>x\<rfloor>\<^sub>L" == "CONST floor_lpf x"
"len\<^sub>L(xs)" == "CONST len_lpf xs"
(* Set Unary Operators *)
"{xs}\<^sub>L" == "CONST set_sequence_lpf xs"
"card\<^sub>L(f)" == "CONST card_lpf f"
"\<Union>\<^sub>L A" == "CONST dunion_lpf A"
"\<Inter>\<^sub>L A" == "CONST dinter_lpf A"
"Pow\<^sub>L(A)" == "CONST power_lpf A"
(* Sequence Unary Operators *)
"[xs]\<^sub>L" == "CONST seq_sequence_lpf xs"
"hd\<^sub>L(xs)" == "CONST hd_lpf xs"
"reverse\<^sub>L(xs)" == "CONST reverse_lpf xs"
"tl\<^sub>L(xs)" == "CONST tl_lpf xs"
"elem\<^sub>L(xs)" == "CONST elems_lpf xs"
"inds\<^sub>L(xs)" == "CONST inds_lpf xs"
"conc\<^sub>L(xs)" == "CONST conc_lpf xs"
(* Map Unary Operators *)
"dom\<^sub>L(f)" == "CONST dom_lpf f"
"rng\<^sub>L(f)" == "CONST rng_lpf f"
"merge\<^sub>L(f)" == "CONST merge_lpf f"
(* Binary Operators *)
(* Polymorphic Binary Operators *)
"x =\<^sub>L y" == "CONST equal_lpf x y"
"x \<noteq>\<^sub>L y" == "CONST not_equal_lpf x y"
(* Boolean Binary Operators  *)
(* TODO: These are defined in LPF, as they are part of the basic logic
"p \<and>\<^sub>L q" == "CONST conj_lpf p q"
"p \<or>\<^sub>L q" == "CONST disj_lpf p q"
"p \<Rightarrow>\<^sub>L q" == "CONST implies_lpf p q"
*)
"p \<Leftrightarrow>\<^sub>L q" == "CONST biimplication_lpf p q"
(* Numeric Binary Operators  *)
(*"x div\<^sub>L y" == "CONST div_lpf x y"*) (*by typeclass*)
"x rem\<^sub>L y" == "CONST rem_lpf x y"
(* "x div\<^sub>L y" == "CONST div_lpf x y"*) (*by typeclass*)
"x ^\<^sub>L y" == "CONST power_nat_lpf x y"
"x powr\<^sub>L y" == "CONST power_real_lpf x y"
"x >\<^sub>L y" == "CONST slt_lpf x y"
"x \<ge>\<^sub>L y" == "CONST lte_lpf x y"
"x <\<^sub>L y" == "CONST sgt_lpf x y"
"x \<le>\<^sub>L y" == "CONST gte_lpf x y"
(* Record Binary Operators *)
(* Set Binary Operators *)
"x \<in>\<^sub>L A" == "CONST in_lpf x A"
"x \<notin>\<^sub>L A" == "CONST not_in_lpf x A"
"A \<union>\<^sub>L B" == "CONST union_lpf A B"
"A \<inter>\<^sub>L B" == "CONST intersect_lpf A B"
"A \<setminus>\<^sub>L B" == "CONST difference_lpf A B"
"A \<subset>\<^sub>L B" == "CONST psubset_lpf A B"
"A \<subseteq>\<^sub>L B" == "CONST subset_lpf A B"
(* Sequence Binary Operators *)
"xs conc\<^sub>L ys" == "CONST conc_seq_lpf xs ys"
"xs ++\<^sub>L ys" == "CONST seq_mod_lpf xs ys"
"xs !\<^sub>L x" == "CONST seq_index_lpf xs x"
(* Comprehensions *)
"{x. P}\<^sub>L"      == "CONST collect_lpf (%x. P)"
"\<forall>\<^sub>Lx\<in>A. P" == "CONST Ball_lpf A (\<lambda>x. P)"

  
end
