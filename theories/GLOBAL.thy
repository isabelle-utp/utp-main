(******************************************************************************)
(* Title: utp/GLOBAL.thy                                                      *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Global Syntax *}

theory GLOBAL
imports utp_common utp_types
begin

text {* This theory introduces generic definitions for global syntax. *}

subsection {* Value Syntax *}

consts type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)

consts set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":\<subseteq>" 50)

subsection {* Predicate Syntax *}

(*
  We do not use generic operators for the following two. The reason is that
  typing can become a little subtle with generic constants here, namely it is
  not enough to type the operands in order to type the operator. This can lead
  to unexpected behaviours resulting from instantiation with the wrong types.
*)

(*
consts alphabet ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE ALPHABET)" ("\<alpha>")
*)

(*
consts bindings ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) BINDING_SET" ("\<beta>")
*)

consts beta_equiv ::
  "('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('TYPE ALPHABET) \<Rightarrow> bool"
  ("_ \<cong> _ on _")

consts LiftP ::
  "('TYPE ALPHABET) \<Rightarrow> ('VALUE, 'TYPE) BINDING_FUN \<Rightarrow> 'PREDICATE"

syntax "LiftP_Syntax" ::
  "'TYPE ALPHABET \<Rightarrow> idt \<Rightarrow> bool \<Rightarrow> 'PREDICATE" ("(1_ \<odot> _ \<bullet>/ _)")

translations
  "a \<odot> b \<bullet> P" == "CONST LiftP a (\<lambda> b . P)"

consts TrueP ::
  "'TYPE ALPHABET \<Rightarrow>
   'PREDICATE" ("true")

consts FalseP ::
  "'TYPE ALPHABET \<Rightarrow>
   'PREDICATE" ("false")

consts TRUE ::
  "'PREDICATE" ("TRUE")

consts FALSE ::
  "'PREDICATE" ("FALSE")

consts ExtP ::
  "'PREDICATE \<Rightarrow> ('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE"
  (infix "\<oplus>p" 200)

consts ResP ::
  "'PREDICATE \<Rightarrow> ('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE"
  (infix "\<ominus>p" 200)

consts NotP ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("\<not>p _" [190] 190)

consts AndP ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<and>p" 180)

consts OrP ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<or>p" 170)

consts ImpliesP ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<Rightarrow>p" 160)

consts IffP ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<Leftrightarrow>p" 150)

consts ExistsResP ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<exists>-p _ ./ _)" [0, 10] 10)

consts ForallResP ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<forall>-p _ ./ _)" [0, 10] 10)

consts ExistsP ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<exists>p _ ./ _)" [0, 10] 10)

consts ForallP ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<forall>p _ ./ _)" [0, 10] 10)

consts ClosureP ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("[_]")

consts RefP ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infix "\<sqsubseteq>p" 100)

consts Tautology ::
  "'PREDICATE \<Rightarrow> bool"
  ("taut _" [50] 50)

consts Contradiction ::
  "'PREDICATE \<Rightarrow> bool"
  ("contra _" [50] 50)

consts Contingency ::
  "'PREDICATE \<Rightarrow> bool"
  ("cont _" [50] 50)

consts Refinement ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow> bool"
  (infix "\<sqsubseteq>" 50)
end