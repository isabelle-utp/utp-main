theory GLOBAL
imports "utp_base" "utp_name"
begin

section {* Global Syntax *}

subsection {* Type Synonyms *}

types 'TYPE VAR = "NAME \<times> 'TYPE"
types 'VAR ALPHABET = "'VAR set"
types ('VAR, 'VAL) BINDING = "'VAR \<Rightarrow> 'VAL"
types ('VAR, 'VAL) BINDING_SET = "('VAR, 'VAL) BINDING set"
types ('VAR, 'VAL) BINDING_FUN = "('VAR, 'VAL) BINDING \<Rightarrow> bool"
types ('VAR, 'VAL) ALPHA_PREDICATE =
  "('VAR ALPHABET) \<times> ('VAR, 'VAL) BINDING_SET"

types ('VAR, 'VAL) ALPHA_FUNCTION =
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"

subsection {* Value Syntax *}

(* Was type_rel was called is_of_type before. *)
consts type_rel :: "'VAL \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
consts set_type_rel :: "'VAL set \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":\<subseteq>" 50)
consts value_ref :: "'VAL \<Rightarrow> 'VAL \<Rightarrow> bool" (infix "\<sqsubseteq>v" 50)

(*
consts MkInt :: "int \<Rightarrow> 'VAL"
consts MkBool :: "bool \<Rightarrow> 'VAL"
consts MkStr :: "string \<Rightarrow> 'VAL"
consts MkPair :: "('VAL \<times> 'VAL) \<Rightarrow> 'VAL"
consts MkSet :: "'TYPE \<Rightarrow> ('VAL set) \<Rightarrow> 'VAL"

consts DestInt :: "'VAL \<Rightarrow> int"
consts DestBool :: "'VAL \<Rightarrow> bool"
consts DestStr :: "'VAL \<Rightarrow> string"
consts DestPair :: "'VAL \<Rightarrow> ('VAL \<times> 'VAL)"
consts DestSet :: "'VAL \<Rightarrow> ('VAL set)"
consts DestSetType :: "'VAL \<Rightarrow> 'TYPE"
*)

(*
subsubsection {* Arithmetic Operators *}

text {* It might be better to suffix the operators with v. *}

class arithmetics =
  fixes uminus :: "'a \<Rightarrow> 'a" ("- _" [81] 80)
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "+" 65)
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-" 65)
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"( infixl "*" 70)
  fixes divide :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "div" 70)
  fixes modulus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "mod" 70)

subsubsection {* Set Operators *}

text {* It might be better to suffix the operators with v. *}

class sets =
  fixes compl :: "'a \<Rightarrow> 'a" ("compl _" [81] 80)
  fixes union :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<union>" 65)
  fixes inter :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<inter>" 70)
  fixes diff :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\\" 75)
  fixes member :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<in> _)" [50, 51] 50)
  fixes not_member :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<notin> _)" [50, 51] 50)
  fixes subset :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<subset> _)" [50, 51] 50)
  fixes subset_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<subseteq> _)" [50, 51] 50)
*)

subsection {* Predicate Syntax *}

consts BINDING_EQUIV ::
  "('VAR, 'VAL) BINDING \<Rightarrow>
   ('VAR, 'VAL) BINDING \<Rightarrow>
   ('VAR ALPHABET) \<Rightarrow> bool"
  ("_ \<cong> _ on _")

consts LiftP ::
  "('VAR ALPHABET) \<Rightarrow>
   (('VAR, 'VAL) BINDING \<Rightarrow> bool) \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"

syntax "LiftP_Syntax" ::
  "'VAR ALPHABET \<Rightarrow> idt \<Rightarrow> bool \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE" ("(1_ \<odot> _ \<bullet>/ _)")

translations
  "a \<odot> b \<bullet> P" == "CONST LiftP a (\<lambda> b . P)"

consts TrueP ::
  "'VAR ALPHABET \<Rightarrow> ('VAR, 'VAL) ALPHA_PREDICATE" ("true")

consts FalseP ::
  "'VAR ALPHABET \<Rightarrow> ('VAR, 'VAL) ALPHA_PREDICATE" ("false")

consts TRUE ::
  "('VAR, 'VAL) ALPHA_PREDICATE" ("TRUE")

consts FALSE ::
  "('VAR, 'VAL) ALPHA_PREDICATE" ("FALSE")

consts ExtP ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow> 'VAR ALPHABET \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  (infix "\<oplus>" 200)

consts ResP ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow> 'VAR ALPHABET \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  (infix "\<ominus>" 200)

consts NotP ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  ("\<not>p _" [190] 190)

consts AndP ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  (infixr "\<and>p" 180)

consts OrP ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  (infixr "\<or>p" 170)

consts ImpliesP ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  (infixr "\<Rightarrow>p" 160)

consts IffP ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  (infixr "\<Leftrightarrow>p" 150)

consts ExistsP ::
  "('VAR ALPHABET) \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  ("(\<exists>p _ ./ _)" [0, 10] 10)

consts ForallP ::
  "('VAR ALPHABET) \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  ("(\<forall>p _ ./ _)" [0, 10] 10)

consts ExistsExtP ::
  "('VAR ALPHABET) \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  ("(\<exists>p+ _ ./ _)" [0, 10] 10)

consts ForallExtP ::
  "('VAR ALPHABET) \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  ("(\<forall>p+ _ ./ _)" [0, 10] 10)

consts ClosureP ::
   "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  ("[_]")

consts RefP ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE"
  (infix "\<sqsubseteq>p" 100)

consts Tautology ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow> bool"
  ("taut _" [50] 50)

consts Contradiction ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow> bool"
  ("contra _" [50] 50)

consts Refinement ::
  "('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow>
   ('VAR, 'VAL) ALPHA_PREDICATE \<Rightarrow> bool"
  (infix "\<sqsubseteq>" 50)
end