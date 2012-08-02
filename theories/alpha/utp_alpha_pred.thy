(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_alpha_pred.thy                                                   *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Alphabetised Predicates *}

theory utp_alpha_pred
imports "../generic/utp_pred"
begin

subsection {* Locale @{text "ALPHA_PRED"} *}

locale ALPHA_PRED =
  PRED "type_rel"
-- {* Typing Relation for Values *}
for type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
begin

subsubsection {* Alphabets *}

definition WF_ALPHABET :: "('TYPE ALPHABET) set" where
"WF_ALPHABET = {vs . finite vs}"

subsubsection {* Bindings *}

definition WF_BINDING_BFUN ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) BINDING_BFUN set" where
"a \<in> WF_ALPHABET \<longrightarrow>
 WF_BINDING_BFUN a = {f . \<forall> b1 b2 . b1 \<cong> b2 on a \<longrightarrow> f b1 = f b2}"

subsubsection {* Predicates *}

abbreviation alphabet ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE ALPHABET)" where
"alphabet p \<equiv> (fst p)"

notation alphabet ("\<alpha>")

abbreviation predicate ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"predicate p \<equiv> (snd p)"

notation predicate ("\<pi>")

definition WF_ALPHA_PREDICATE ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_ALPHA_PREDICATE =
 {p . (\<alpha> p) \<in> WF_ALPHABET \<and> (\<pi> p) \<in> WF_PREDICATE_OVER (\<alpha> p)}"

definition WF_ALPHA_PREDICATE_OVER ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"a \<in> WF_ALPHABET \<longrightarrow>
 WF_ALPHA_PREDICATE_OVER a = {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p = a}"

subsection {* Operators *}

subsubsection {* Shallow Lifting *}

definition LiftA ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) BINDING_BFUN \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 f \<in> WF_BINDING_BFUN a \<longrightarrow>
 LiftA a f = (a, LiftP f)"

subsubsection {* Extension and Restriction *}

definition ExtA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<and>
 a \<in> WF_ALPHABET \<longrightarrow>
 ExtA p a = ((\<alpha> p) \<union> a, \<pi> p)"

notation ExtA (infix "\<oplus>\<alpha>" 200)

definition ResA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<and>
 a \<in> WF_ALPHABET \<longrightarrow>
 ResA p a = ((\<alpha> p) - a, \<exists>p a . \<pi> p)"

notation ResA (infix "\<ominus>\<alpha>" 200)

subsubsection {* True and False *}

definition TrueA ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<longrightarrow>
 TrueA a = (a, true)"

notation TrueA ("true")

definition FalseA ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<longrightarrow>
 FalseA a = (a, false)"

notation FalseA ("false")

subsubsection {* Logical Connectives *}

definition NotA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 NotA p = (\<alpha> p, \<not>p (\<pi> p))"

notation NotA ("\<not>\<alpha> _" [190] 190)

definition AndA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 AndA p1 p2 = ((\<alpha> p1) \<union> (\<alpha> p2), (\<pi> p1) \<and>p (\<pi> p2))"

notation AndA (infixr "\<and>\<alpha>" 180)

definition OrA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 OrA p1 p2 = ((\<alpha> p1) \<union> (\<alpha> p2), (\<pi> p1) \<or>p (\<pi> p2))"

notation OrA (infixr "\<or>\<alpha>" 170)

definition ImpliesA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ImpliesA p1 p2 = ((\<alpha> p1) \<union> (\<alpha> p2), (\<pi> p1) \<Rightarrow>p (\<pi> p2))"

notation ImpliesA (infixr "\<Rightarrow>\<alpha>" 160)

definition IffA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 IffA p1 p2 = ((\<alpha> p1) \<union> (\<alpha> p2), (\<pi> p1) \<Leftrightarrow>p (\<pi> p2))"

notation IffA (infixr "\<Leftrightarrow>\<alpha>" 150)

subsubsection {* Quantifiers *}

definition ExistsA ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ExistsA a p = ((\<alpha> p), \<exists>p a . \<pi> p)"

notation ExistsA ("(\<exists>\<alpha> _ ./ _)" [0, 10] 10)

definition ForallA ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ForallA a p = ((\<alpha> p), \<forall>p a . \<pi> p)"

notation ForallA ("(\<forall>\<alpha> _ ./ _)" [0, 10] 10)

definition ExistsResA ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ExistsResA a p = ((\<alpha> p) - a, \<exists>p a . \<pi> p)"

notation ExistsResA ("(\<exists>-\<alpha> _ ./ _)" [0, 10] 10)

definition ForallResA ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ForallResA a p = ((\<alpha> p) - a, \<forall>p a . \<pi> p)"

notation ForallResA ("(\<forall>-\<alpha> _ ./ _)" [0, 10] 10)

subsubsection {* Universal Closure *}

definition ClosureA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ClosureA p = ({}, [\<pi> p]p)"

notation ClosureA ("[_]\<alpha>")

subsubsection {* Refinement *}

definition RefA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 RefA p1 p2 = [p2 \<Rightarrow>\<alpha> p1]\<alpha>"

notation RefA (infix "\<sqsubseteq>\<alpha>" 100)

subsection {* Meta-logical Operators *}

definition TautologyA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 TautologyA p \<longleftrightarrow> (p = true (\<alpha> p))"

notation TautologyA ("taut _" [50] 50)

definition ContradictionA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ContradictionA p \<longleftrightarrow> (p = false (\<alpha> p))"

notation ContradictionA ("contra _" [50] 50)

definition RefinementA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<and>
 (\<alpha> p1) = (\<alpha> p2) \<longrightarrow>
 RefinementA p1 p2 \<longleftrightarrow> taut (p1 \<sqsubseteq>\<alpha> p2)"

notation RefinementA (infix "\<sqsubseteq>" 50)

subsection {* Theorems *}

subsubsection {* Validation of Soundness *}

theorem TrueA_noteq_FalseA :
"a \<in> WF_ALPHABET \<Longrightarrow> true a \<noteq> false a"
apply (simp add: TrueA_def FalseA_def)
apply (simp add: TrueP_noteq_FalseP)
done
end
end