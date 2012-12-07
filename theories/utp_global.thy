(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_global.thy                                                       *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Global Syntax *}

theory utp_global
imports utp_common "core/utp_synonyms" "core/utp_value"
begin

subsection {* Global Syntax *}

text {* We introduce generic constants for global syntax. *}

subsubsection {* Value Syntax *}

consts global_type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool"
notation global_type_rel (infix ":" 50)

consts global_set_type_rel :: "'VALUE set \<Rightarrow> 'TYPE \<Rightarrow> bool"
notation global_set_type_rel (infix ":\<subseteq>" 50)

subsubsection {* Predicate Syntax *}

text {*
  We do not define generic constants for the following two operators. The
  reason for this is that typing can become subtle with generic constants
  here. Namely, it is not enough to type the operand in order to fully type
  the operator. This can lead to unexpected behaviours during parsing; that
  is, for instance, instantiation of the operators with wrong types. A
  common solution to this problem is to parametrise the operator in terms of
  the result type using @{type "itself"}. But this might be too cumbersome.
*}

(*
consts global_alphabet ::
  "'PREDICATE \<Rightarrow>
  ('TYPE ALPHABET)" ("\<alpha>")

consts global_predicate ::
  "'PREDICATE1 \<Rightarrow>
  ('VALUE, 'TYPE) PREDICATE2 ("\<pi>")
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

subsubsection {* Relation Syntax *}

subsection {* Global Definitions *}

subsubsection {* Well-formed Values *}

definition WF_VALUE_GLOBAL ::
  "('VALUE\<Rightarrow> 'TYPE \<Rightarrow> bool) \<Rightarrow> 'VALUE set" where
"WF_VALUE_GLOBAL type_rel = {v . \<exists> t . type_rel v t}"

notation WF_VALUE_GLOBAL ("WF'_VALUE[_]")

theorem WF_VALUE_GLOBAL_non_empty :
"VALUE type_rel \<Longrightarrow> WF_VALUE[type_rel] \<noteq> {}"
apply (simp add: WF_VALUE_GLOBAL_def)
apply (simp add: VALUE_def)
apply (drule_tac x = "t" in spec)
apply (clarify)
apply (rule_tac x = "x" in exI)
apply (rule_tac x = "t" in exI)
apply (assumption)
done

theorem WF_VALUE_GLOBAL_member :
"(x \<in> WF_VALUE[type_rel]) \<longleftrightarrow> (\<exists> t . type_rel x t)"
apply (simp add: WF_VALUE_GLOBAL_def)
done

(* The commented out stuff below is probably redundant. Remove! *)

(*
subsubsection {* Carrier Sets *}

definition global_carrier ::
  "('VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool) \<Rightarrow> 'TYPE \<Rightarrow>  ('VALUE set)" where
"global_carrier type_rel t = {x . type_rel x t}"

notation global_carrier ("carrier[_]")

theorem global_carrier_member :
"x \<in> (carrier[type_rel] t) \<longleftrightarrow> (type_rel x t)"
apply (simp add: global_carrier_def)
done

theorem global_equals_local_carrier :
"VALUE type_rel \<Longrightarrow>
 carrier[type_rel] = VALUE.carrier type_rel"
apply (rule ext)
apply (simp add: global_carrier_def)
apply (simp add: VALUE.carrier_def)
done

theorem local_equals_global_carrier :
"VALUE type_rel \<Longrightarrow>
 VALUE.carrier type_rel = carrier[type_rel]"
apply (rule ext)
apply (simp add: VALUE.carrier_def)
apply (simp add: global_carrier_def)
done
*)

(*
subsubsection {* Type Set Carriers *}

definition global_carrier_types ::
  "('VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool) \<Rightarrow> ('TYPE set) \<Rightarrow> ('VALUE set)" where
"global_carrier_types type_rel ts =
 \<Union> {carrier[type_rel] t | t . t \<in> ts}"

notation global_carrier_types ("carrier'_types[_]")

theorem global_carrier_types_member :
"x \<in> (carrier_types[type_rel] ts) \<longleftrightarrow>
 (\<exists> t \<in> ts . x \<in> carrier[type_rel] t)"
apply (simp add: global_carrier_types_def)
apply (safe)
apply (rule_tac x = "t" in bexI)
apply (assumption)+
apply (rule_tac x = "carrier[type_rel] t" in exI)
apply (simp)
apply (rule_tac x = "t" in exI)
apply (simp)
done

theorem global_carrier_types_UNIV :
"type_rel x t \<Longrightarrow> x \<in> (carrier_types[type_rel] UNIV)"
apply (simp add: global_carrier_types_member)
apply (rule_tac x = "t" in exI)
apply (simp add: global_carrier_member)
done

theorem global_carrier_types_monotonic :
"ts1 \<subseteq> ts2 \<Longrightarrow>
 (carrier_types[type_rel] ts1) \<subseteq> (carrier_types[type_rel] ts2)"
apply (simp add: global_carrier_types_def)
apply (clarsimp)
apply (rule_tac x = "carrier[type_rel] t" in exI)
apply (simp)
apply (rule_tac x = "t" in exI)
apply (simp)
apply (auto)
done

theorem WF_VALUE_GLOBAL_carrier_types :
"WF_VALUE[type_rel] = carrier_types[type_rel] UNIV"
apply (simp add: set_eq_iff)
apply (simp add: WF_VALUE_GLOBAL_member)
apply (simp add: global_carrier_types_member)
apply (simp add: global_carrier_member)
done
*)
end