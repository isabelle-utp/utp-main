(******************************************************************************)
(* Title: utp/GLOBAL.thy                                                      *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory GLOBAL
imports "utp_common" "generic/utp_name"
begin

section {* Type Synonyms *}

types 'TYPE VAR = "NAME \<times> 'TYPE"
types 'VAR ALPHABET = "'VAR set"
types ('VAR, 'VALUE) BINDING = "'VAR \<Rightarrow> 'VALUE"
types ('VAR, 'VALUE) BINDING_SET = "('VAR, 'VALUE) BINDING set"
types ('VAR, 'VALUE) BINDING_FUN = "('VAR, 'VALUE) BINDING \<Rightarrow> bool"
types ('VAR, 'VALUE) ALPHA_PREDICATE =
  "('VAR ALPHABET) \<times> ('VAR, 'VALUE) BINDING_SET"

types ('VAR, 'VALUE) ALPHA_FUNCTION =
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"

section {* Global Syntax *}

subsection {* Value Syntax *}

consts type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
consts set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":\<subseteq>" 50)
consts value_ref :: "'VALUE \<Rightarrow> 'VALUE \<Rightarrow> bool" (infix "\<sqsubseteq>v" 50)

subsection {* Predicate Syntax *}

consts BINDING_EQUIV ::
  "('VAR, 'VALUE) BINDING \<Rightarrow>
   ('VAR, 'VALUE) BINDING \<Rightarrow>
   ('VAR ALPHABET) \<Rightarrow> bool"
  ("_ \<cong> _ on _")

consts LiftP ::
  "('VAR ALPHABET) \<Rightarrow>
   (('VAR, 'VALUE) BINDING_FUN) \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"

syntax "LiftP_Syntax" ::
  "'VAR ALPHABET \<Rightarrow> idt \<Rightarrow> bool \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE" ("(1_ \<odot> _ \<bullet>/ _)")

translations
  "a \<odot> b \<bullet> P" == "CONST LiftP a (\<lambda> b . P)"

consts TrueP ::
  "'VAR ALPHABET \<Rightarrow> ('VAR, 'VALUE) ALPHA_PREDICATE" ("true")

consts FalseP ::
  "'VAR ALPHABET \<Rightarrow> ('VAR, 'VALUE) ALPHA_PREDICATE" ("false")

consts TRUE ::
  "('VAR, 'VALUE) ALPHA_PREDICATE" ("TRUE")

consts FALSE ::
  "('VAR, 'VALUE) ALPHA_PREDICATE" ("FALSE")

consts ExtP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> 'VAR ALPHABET \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  (infix "\<oplus>" 200)

consts ResP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> 'VAR ALPHABET \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  (infix "\<ominus>" 200)

consts NotP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  ("\<not>p _" [190] 190)

consts AndP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  (infixr "\<and>p" 180)

consts OrP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  (infixr "\<or>p" 170)

consts ImpliesP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  (infixr "\<Rightarrow>p" 160)

consts IffP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  (infixr "\<Leftrightarrow>p" 150)

consts ExistsResP ::
  "('VAR ALPHABET) \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  ("(\<exists>-p _ ./ _)" [0, 10] 10)

consts ForallResP ::
  "('VAR ALPHABET) \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  ("(\<forall>-p _ ./ _)" [0, 10] 10)

consts ExistsP ::
  "('VAR ALPHABET) \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  ("(\<exists>p _ ./ _)" [0, 10] 10)

consts ForallP ::
  "('VAR ALPHABET) \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  ("(\<forall>p _ ./ _)" [0, 10] 10)

consts ClosureP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  ("[_]")

consts RefP ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE"
  (infix "\<sqsubseteq>p" 100)

consts Tautology ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> bool"
  ("taut _" [50] 50)

consts Contradiction ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> bool"
  ("contra _" [50] 50)

consts Contingency ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> bool"
  ("contg _" [50] 50)

consts Refinement ::
  "('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> bool"
  (infix "\<sqsubseteq>" 50)
end