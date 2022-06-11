(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ranks.thy                                                            *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Type Ranks\<close>

theory ranks
imports Main
  "HOL-Eisbach.Eisbach"
  "../core/uattrib"
begin

default_sort type

text \<open>
  Ranks are used to index HOL types by a natural number. While HOL does not
  support dependent typing, we use type classes as a poor man's dependency
  mechanism to associate each HOL type with a rank. Ranks are used later on
  in the theory @{text uval} to formalise the axioms of the universal value
  model: they determine a (lower bound for) the index @{text "'idx"} of type
  @{text "'idx uval"} into which a HOL type can be injected.
\<close>

subsection \<open>Theorem Attribute\<close>

text \<open>Attribute collecting theorems to facilitate proofs about type ranks.\<close>

named_theorems ranks "rank theorems"

ML \<open>
  structure ranks = Named_Attrib(val name = @{named_theorems ranks});
\<close>

subsection \<open>Rank Class\<close>

text \<open>The class @{text rank} allows us to specify a rank for each HOL type.\<close>

class rank =
  fixes rank :: "'a itself \<Rightarrow> nat"

subsection \<open>Rank Syntax\<close>

text \<open>
  Syntax that lets us write @{text "RANK('t)"} for some HOL type @{text "t"}.
\<close>

syntax "_rank" :: "type \<Rightarrow> nat" ("RANK'(_')")

translations "RANK('a)" \<rightleftharpoons> "(CONST rank) TYPE('a)"

subsection \<open>Instantiations\<close>

text \<open>
  We require a few instantiations of ground types: types that are created
  by type declarations rather than by type definitions. Namely, those types
  are @{type bool}, @{type ind}, @{type fun} and @{type set}. All other HOL
  types are introduced by virtue of type definitions, and for those types we
  automatically obtain instantiations of the @{class rank} class by the type
  interpretation that we configure by virtue of the file @{text "rank.ML"}.
  Correct instantiation of class @{class rank} is crucial for our approach
  to be definitionally sound. All ground types other than @{text uval} have
  a rank of zero, and parametric types obtain their ranks as the maximum of
  their constituent argument types.
\<close>

text \<open>
  An open issue are type declarations as for these we have no mechanism that
  assigns a type rank. I presume that it is safe to assign any rank to them,
  hence such a mechanism might not be required for definitional soundness?!
\<close>

instantiation bool :: rank
begin
definition rank_bool :: "bool itself \<Rightarrow> nat" where
[ranks]: "rank_bool t = 0"
instance ..
end

instantiation ind :: rank
begin
definition rank_ind :: "ind itself \<Rightarrow> nat" where
[ranks]: "rank_ind t = 0"
instance ..
end

(* rank(A \<Rightarrow> B) = rank(A) + 1 according to Burkhart Wolff. *)

(* Citation: Ranked typed systems (see HOL discussion group). *)

(* Work that caused impact / discussion in ITP 2016! *)

instantiation "fun" :: (rank, rank) rank
begin
definition rank_fun :: "('a \<Rightarrow> 'b) itself \<Rightarrow> nat" where
(* [ranks]: "rank_fun t = RANK('a) + 1" *)
[ranks]: "rank_fun t = max RANK('a) RANK('b)"
instance ..
end

instantiation set :: (rank) rank
begin
definition rank_set :: "('a set) itself \<Rightarrow> nat" where
[ranks]: "rank_set t = RANK('a)"
instance ..
end

subsection \<open>Proof Support\<close>

text \<open>
  We next configure a mechanism that instantiates the @{class rank} class
  automatically for any existing or new type definition. This is done via an
  interpretation of @{text typedef}. Correct instantiation is crucial since
  the soundness of the axiomatic UTP value model relies on it. We hence must
  not delegate this task to the user to evade the risk of inconsistencies.
\<close>

text \<open>
  For efficiency reasons, the theorems stored inside the @{attribute ranks}
  attribute are incrementally simplified, evaluating ranks in the RHS of
  definitional theorems `as we go along'. This is necessary since the rank
  terms of subtypes become rapidly large when we evaluate them na\"{i}vely,
  causing such evaluations to become very slow. Additional simplification
  laws are defined below and used to further simplify rank theorems prior to
  inclusion in the @{attribute ranks} attribute.
\<close>

theorem max_cancel_simps :
fixes a :: "nat"
fixes b :: "nat"
fixes c :: "nat"
shows
"max a a = a"
"max (max a b) c = max a (max b c)"
"max a (max b a) = max a b"
"max a (max b (max c a)) = max a (max b c)"
"max a (max a X) = max a X"
"max a (max b (max a X)) = max a (max b X)"
"max a (max b (max c (max a X))) = max a (max b (max c X))"
apply (clarsimp)
apply (auto)
done

ML_file "ranks.ML"

text \<open>
  We lastly configure the @{text Typedef} interpretation. This bootstraps the
  retrospective instantiation of the @{class rank} class for all existing HOL
  types, as well as automatically performs the instantiation of @{class rank}
  for all future type definitions; this is outside the control of the user.
\<close>

setup \<open>
  (Typedef.interpretation
    (Local_Theory.background_theory o Ranks.ensure_rank))
\<close>

text \<open>Automatic tactic to simplify and prove properties of ranks.\<close>

method rank_tac = (auto simp: ranks)

subsection \<open>Dynamic Ranks\<close>

text \<open>
  In order to facilitate the dynamic construction of types with arbitrary
  ranks i.e.~without having to declare a new type for each desired rank, we
  provide two designated types:~type (@{text "r0"}) has a rank of zero and
  (parametric) type (@{text "'a rS"}) increments the rank of @{typ "'a"}.
  In analogy to the construction of natural numbers, composition of the two
  type constructors enable us to create types with any desired rank. Lastly,
  those constructions can also include type parameters, increasing the rank
  of some type @{typ "'a"} by a fixed number.
\<close>

subsubsection \<open>Index Class\<close>

text \<open>
  We use the below to tag types that are used as indices. Note that there is
  currently no mechanism that prevents the user from instantiating other HOL
  types as indices too. While this may not be desirable, I believe that doing
  so does not pose a danger to soundness of the mechanisation. The same is
  true for instantiating the @{class rank} class for declared types added by
  the user. When using the syntax for index types below, sort constraints for
  membership to class @{text index} are imposed automatically on free types.
\<close>

class index = typerep + rank

subsubsection \<open>Index Types\<close>

text \<open>We introduce our two index type constructors as type declarations.\<close>

paragraph \<open>Zero Index\<close>

typedecl r0

instantiation r0 :: typerep
begin
definition typerep_r0 :: "r0 itself \<Rightarrow> typerep" where
[typing]: "typerep_r0 (t :: r0 itself) =
  typerep.Typerep (STR ''ranks.r0'') []"
instance ..
end

instantiation r0 :: index
begin
definition rank_r0 :: "r0 itself \<Rightarrow> nat" where
[ranks]: "rank_r0 t = 0"
instance ..
end

paragraph \<open>Successor Index\<close>

typedecl 'idx(*::index*) rS

instantiation rS :: (typerep) typerep
begin
definition typerep_rS :: "'a rS itself \<Rightarrow> typerep" where
[ranks]: "typerep_rS (t :: 'a rS itself) =
  typerep.Typerep (STR ''ranks.rS'') [TYPEREP('a)]"
instance ..
end

instantiation rS :: (rank) rank
begin
definition rank_rS :: "('a rS) itself \<Rightarrow> nat" where
[ranks]: "rank_rS t = RANK('a) + 1"
instance ..
end

instance rS :: (index) index ..

subsubsection \<open>Index Syntax\<close>

text \<open>
  Lastly, we define a neat syntax for index types. We distinguish open and
  closed index types. Open index types are, for instance, @{text "1>'a"} and
  @{text "2>'a"} for some free type @{text "'a"}. Open types raise the rank
  of the underlying free type. Closed indices are, for instance, @{text "0"},
  @{text "1"}, @{text "2"}, and so one. They are monomorphic types.
\<close>

paragraph \<open>Syntax Definitions\<close>

syntax "_open_idx0" :: "type \<Rightarrow> type" ("0>_")
syntax "_open_idx1" :: "type \<Rightarrow> type" ("1>_")
syntax "_open_idxn" :: "num_const \<Rightarrow> tid \<Rightarrow> type" ("_>_")

syntax "_closed_idx0" :: "type" ("0")
syntax "_closed_idx1" :: "type" ("1")
syntax "_closed_idxn" :: "num_const \<Rightarrow> type" ("_")

paragraph \<open>Syntax Translations\<close>

translations
  (type) "0>'a" \<rightharpoonup> (type) "'a::index"
  (type) "1>'a" \<rightharpoonup> (type) "'a::index rS"

translations
  (type) "0" \<rightharpoonup> (type) "r0"
  (type) "1" \<rightharpoonup> (type) "r0 rS"

paragraph \<open>Parser and Printer\<close>

ML_file "indices.ML"

parse_translation \<open>
  [(@{syntax_const "_open_idxn"}, Idx_Parser.open_idx_tr),
   (@{syntax_const "_closed_idxn"}, Idx_Parser.close_idx_tr)]
\<close>

print_translation \<open>
  [(@{type_syntax "r0"}, Idx_Printer.r0_tr'),
   (@{type_syntax "rS"}, Idx_Printer.rS_tr')]
\<close>

subsection \<open>Experiments\<close>

declare [[show_types=true]]

thm ranks \<comment> \<open>This prints all current rank simplification laws.\<close>

declare [[show_types=false]]

declare [[show_sorts]]

typ "0"
typ "1"
typ "2"
typ "3"

typ "0>'a"
typ "1>'b"
typ "2>'c"
typ "3>'d"

declare [[show_sorts=false]]
end