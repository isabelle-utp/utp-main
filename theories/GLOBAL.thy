(******************************************************************************)
(* Title: utp/GLOBAL.thy                                                      *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory GLOBAL
imports utp_common utp_types
begin

section {* Global Syntax *}

subsection {* Value Syntax *}

consts type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)

consts set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":\<subseteq>" 50)

subsection {* Predicate Syntax *}

consts alphabet ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE ALPHABET)" ("\<alpha>")

consts bindings ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) BINDING_SET" ("\<beta>")

consts binding_equiv ::
  "('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('TYPE ALPHABET) \<Rightarrow> bool"
  ("_ \<cong> _ on _")

consts LiftP ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) BINDING_FUN \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"

syntax "LiftP_Syntax" ::
  "'TYPE ALPHABET \<Rightarrow> idt \<Rightarrow> bool \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("(1_ \<odot> _ \<bullet>/ _)")

translations
  "a \<odot> b \<bullet> P" == "CONST LiftP a (\<lambda> b . P)"

consts TrueP ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("true")

consts FalseP ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("false")

consts TRUE ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE" ("TRUE")

consts FALSE ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE" ("FALSE")

consts ExtP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  (infix "\<oplus>" 200)

consts ResP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  (infix "\<ominus>" 200)

consts NotP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  ("\<not>p _" [190] 190)

consts AndP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  (infixr "\<and>p" 180)

consts OrP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  (infixr "\<or>p" 170)

consts ImpliesP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  (infixr "\<Rightarrow>p" 160)

consts IffP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  (infixr "\<Leftrightarrow>p" 150)

consts ExistsResP ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  ("(\<exists>-p _ ./ _)" [0, 10] 10)

consts ForallResP ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  ("(\<forall>-p _ ./ _)" [0, 10] 10)

consts ExistsP ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  ("(\<exists>p _ ./ _)" [0, 10] 10)

consts ForallP ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  ("(\<forall>p _ ./ _)" [0, 10] 10)

consts ClosureP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  ("[_]")

consts RefP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE"
  (infix "\<sqsubseteq>p" 100)

consts Tautology ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool"
  ("taut _" [50] 50)

consts Contradiction ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool"
  ("contra _" [50] 50)

consts Contingency ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool"
  ("contg _" [50] 50)

consts Refinement ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool"
  (infix "\<sqsubseteq>" 50)
end
