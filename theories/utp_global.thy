(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_global.thy                                                       *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Global Syntax *}

theory utp_global
imports utp_common "./core/utp_synonyms"
begin

text {* This theory introduces generic constants for global syntax. *}

subsection {* Value Syntax *}

consts global_type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool"
notation global_type_rel (infix ":" 50)

consts global_set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool"
notation global_set_type_rel (infix ":\<subseteq>" 50)

subsection {* Predicate Syntax *}

text {*
  We do not define generic constants for the alphabet and predicate operator.
  The reason for this is that typing can become subtle with generic constants
  here. Namely, it is not enough to type the operands in order to fully type
  the operator. This can lead to unexpected behaviours during parsing; that
  is, for instance, instantiation of the operators with the wrong types.
*}

(*
consts global_alphabet ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE ALPHABET)" ("\<alpha>")

consts global_bindings ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) BINDING_PRED" ("\<beta>")
*)

consts global_binding_equiv ::
  "('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('TYPE ALPHABET) \<Rightarrow> bool"
  ("_ \<cong> _ on _")

consts LiftG ::
  "('TYPE ALPHABET) \<Rightarrow> ('VALUE, 'TYPE) BINDING_PRED \<Rightarrow> 'PREDICATE"

syntax "Lift_Syntax" ::
  "'TYPE ALPHABET \<Rightarrow> idt \<Rightarrow> bool \<Rightarrow> 'PREDICATE" ("(1_ \<odot> _ \<bullet>/ _)")

translations
  "a \<odot> b \<bullet> P" == "CONST LiftG a (\<lambda> b . P)"

consts ExtG ::
  "'PREDICATE \<Rightarrow> ('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE"
  (infix "\<oplus>u" 200)

consts ResG ::
  "'PREDICATE \<Rightarrow> ('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE"
  (infix "\<ominus>u" 200)

consts TrueG ::
  "'TYPE ALPHABET \<Rightarrow>
   'PREDICATE" ("true")

consts FalseG ::
  "'TYPE ALPHABET \<Rightarrow>
   'PREDICATE" ("false")

consts TRUE ::
  "'PREDICATE" ("TRUE")

consts FALSE ::
  "'PREDICATE" ("FALSE")

consts NotG ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("\<not>u _" [190] 190)

consts AndG ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<and>u" 180)

consts OrG ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<or>u" 170)

consts ImpliesG ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<Rightarrow>u" 160)

consts IffG ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<Leftrightarrow>u" 150)

consts ExistsG ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<exists>u _ ./ _)" [0, 10] 10)

consts ForallG ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<forall>u _ ./ _)" [0, 10] 10)

consts ExistsResG ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<exists>-u _ ./ _)" [0, 10] 10)

consts ForallResG ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<forall>-u _ ./ _)" [0, 10] 10)

consts ClosureG ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("[_]u")

consts RefG ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infix "\<sqsubseteq>u" 100)

consts Tautology ::
  "'PREDICATE \<Rightarrow> bool"
  ("taut _" [50] 50)

consts Contradiction ::
  "'PREDICATE \<Rightarrow> bool"
  ("contra _" [50] 50)

consts Refinement ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow> bool"
  (infix "\<sqsubseteq>" 50)

subsection {* Relation Syntax *}

end