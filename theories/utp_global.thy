(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_global.thy                                                       *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Global Syntax *}

theory utp_global
imports utp_common "core/utp_synonyms"
begin

text {* This theory introduces generic constants for global syntax. *}

subsection {* Value Syntax *}

consts global_type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool"
notation global_type_rel (infix ":" 50)

consts global_set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool"
notation global_set_type_rel (infix ":\<subseteq>" 50)

subsection {* Predicate Syntax *}

text {*
  We do not define generic constants for the following two operators. The
  reason for this is that typing can become subtle with generic constants
  here. Namely, it is not enough to type the operand in order to fully type
  the operator. This can lead to unexpected behaviours during parsing; that
  is, for instance, instantiation of the operators with the wrong types.
*}

text {* TODO: I cannot quite follow the above anymore, review this! *}

(*
consts global_alphabet ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE ALPHABET)" ("\<alpha>")

consts global_predicate ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE ("\<pi>")
*)

consts global_binding_equiv ::
  "('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('TYPE ALPHABET) \<Rightarrow> bool"
  ("_ \<cong> _ on _")

consts Lift ::
  "('TYPE ALPHABET) \<Rightarrow> ('VALUE, 'TYPE) BINDING_PRED \<Rightarrow> 'PREDICATE"

syntax Lift_Syntax ::
  "'TYPE ALPHABET \<Rightarrow> idt \<Rightarrow> bool \<Rightarrow> 'PREDICATE" ("(1_ \<odot> _ \<bullet>/ _)")

translations
  "a \<odot> b \<bullet> P" == "CONST Lift a (\<lambda> b . P)"

consts Ext ::
  "'PREDICATE \<Rightarrow> ('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE"
  (infix "\<oplus>u" 200)

consts Res ::
  "'PREDICATE \<Rightarrow> ('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE"
  (infix "\<ominus>u" 200)

consts True ::
  "'TYPE ALPHABET \<Rightarrow>
   'PREDICATE" ("true")
hide_const (open) True

consts False ::
  "'TYPE ALPHABET \<Rightarrow>
   'PREDICATE" ("false")
hide_const (open) False

consts TRUE ::
  "'PREDICATE" ("TRUE")

consts FALSE ::
  "'PREDICATE" ("FALSE")

consts Not ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("\<not>u _" [190] 190)

consts And ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<and>u" 180)

consts Or ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<or>u" 170)

consts Implies ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<Rightarrow>u" 160)

consts Iff ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  (infixr "\<Leftrightarrow>u" 150)

consts Exists ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<exists>u _ ./ _)" [0, 10] 10)

consts Forall ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<forall>u _ ./ _)" [0, 10] 10)

consts ExistsRes ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<exists>-u _ ./ _)" [0, 10] 10)

consts ForallRes ::
  "('TYPE ALPHABET) \<Rightarrow>
   'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("(\<forall>-u _ ./ _)" [0, 10] 10)

consts Closure ::
  "'PREDICATE \<Rightarrow>
   'PREDICATE"
  ("[_]u")

consts Ref ::
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
