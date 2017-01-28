(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Typedep.thy                                                          *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 16 Jan 2016 *)

section {* Type Dependency *}

theory Typedep
imports Typerep
  Typerep_ind Named_Attrib
begin

subsection {* Theorem Attribute *}

text {* Attribute collecting theorems to reason about type dependencies. *}

named_theorems typedep "typedep theorems"

ML {*
  structure typedep = Named_Attrib(val name = @{named_theorems typedep});
*}

subsection {* Class @{text typedep} *}

class typedep = typerep +
  fixes typedep :: "'a itself \<Rightarrow> typerep set"

subsection {* Syntax *}

syntax "_TYPEDEP" :: "type \<Rightarrow> logic"  ("(1TYPEDEP/(1'(_')))")

translations "TYPEDEP('a)" \<rightleftharpoons> "(CONST typedep) TYPE('a)"

subsection {* Instantiations *}

text {*
  We require a few instantiations of ground types i.e.~types not created by
  virtue of a @{text typedef}). Namely, these are @{type bool}, @{type ind},
  @{type fun} and @{type set}. All other types in HOL are derived through type
  definitions and hence we obtain instantiations of @{class typedep} by the
  type interpretation that we subsequently configure.
*}

instantiation ind :: typedep
begin
definition typedep_ind :: "ind itself \<Rightarrow> typerep set" where
"typedep_ind t = {TYPEREP(ind)}"
instance by (intro_classes)
end

instantiation bool :: typedep
begin
definition typedep_bool :: "bool itself \<Rightarrow> typerep set" where
"typedep_bool t = {TYPEREP(bool)}"
instance by (intro_classes)
end

instantiation "fun" :: (typedep, typedep) typedep
begin
definition typedep_fun :: "('a \<Rightarrow> 'b) itself \<Rightarrow> typerep set" where
"typedep_fun t = TYPEDEP('a) \<union> TYPEDEP('b)"
instance by (intro_classes)
end

instantiation set :: (typedep) typedep
begin
definition typedep_set :: "'a set itself \<Rightarrow> typerep set" where
"typedep_set t = TYPEDEP('a)"
instance by (intro_classes)
end

subsection {* Proof Support *}

declare typedep_ind_def [typedep]
declare typedep_bool_def [typedep]
declare typedep_fun_def [typedep]
declare typedep_set_def [typedep]

subsection {* Interpretation *}

text {*
  We next configure a mechanism that instantiates the class @{class typedep}
  automatically for any existing or new type definition. This is done via an
  interpretation of a @{text typedef}. Correct instantiation is crucial since
  the soundness of the axiomatic UTP value model relies on it. We hence must
  not delegate this task to the user to avoid any risk of inconsistencies.
*}

text {* The following rewrites could be done generically by a conversion. *}

theorem remove_set_duplicates :
"(insert x (insert x S)) = (insert x S)"
"(insert x (insert a (insert x S))) =
 (insert x (insert a S))"
"(insert x (insert a (insert b (insert x S)))) =
 (insert x (insert a (insert b S)))"
"(insert x (insert a (insert b (insert c (insert x S))))) =
 (insert x (insert a (insert b (insert c S))))"
"(insert x (insert a (insert b (insert c (insert d (insert x S)))))) =
 (insert x (insert a (insert b (insert c (insert d S)))))"
"(insert x (insert a (insert b (insert c (insert d (insert e (insert x S))))))) =
 (insert x (insert a (insert b (insert c (insert d (insert e S))))))"
apply (auto)
done

ML_file "Typedep.ML"

setup {*
  (Typedef.interpretation
    (Local_Theory.background_theory o Typedep.ensure_typedep))
*}

subsection {* Proof Optimisation *}

text {*
  It turns out that instantiation proofs of class @{text injectable} can be
  very slow due to large terms arising if we use the @{text "typedep_..._def"}
  theorems directly. This only became noticeable since Isabelle 2015, which is
  presumably due to a more complex type models for datatypes. To overcome this
  issue, what we store in the @{text typedep} attribute are theorems that have
  in fact already been simplified, expanding @{text "typedep_..._def"} in the
  RHS of the definitional equation and removing duplicates elements in set. We
  note that the theorems in @{text typedep} are not axioms but proved lemmas.
*}

declare [[show_types]]

thm typedep

declare [[show_types=false]]
end