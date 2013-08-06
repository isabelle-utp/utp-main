(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred.thy                                                         *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Predicates *}

theory utp_pred
imports 
  utp_binding 
  utp_rename
begin

subsection {* Predicates *}

text {* Binding Predicates *}

type_synonym 'VALUE WF_BINDING_PRED = "'VALUE WF_BINDING \<Rightarrow> bool"
type_synonym 'VALUE WF_BINDING_FUN = "'VALUE WF_BINDING \<Rightarrow> 'VALUE"

definition WF_BINDING_PRED ::
  "'VALUE VAR set \<Rightarrow> 'VALUE WF_BINDING_PRED set" where
"WF_BINDING_PRED vs = {f . \<forall> b1 b2 . b1 \<cong> b2 on vs \<longrightarrow> f b1 = f b2}"

definition WF_PREDICATE :: "'VALUE PREDICATE set" where
"WF_PREDICATE = Pow WF_BINDING"

typedef 'VALUE WF_PREDICATE = "UNIV :: 'VALUE WF_BINDING set set"
morphisms destPRED mkPRED
  by (auto)

declare destPRED [simp]
declare destPRED_inverse [simp]
declare mkPRED_inverse [simp]

lemma destPRED_intro [intro!]:
  "destPRED x = destPRED y \<Longrightarrow> x = y"
  by (simp add:destPRED_inject)

lemma destPRED_elim [elim]:
  "\<lbrakk> x = y; destPRED x = destPRED y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

text {* The lifting package allows us to define operators on a typedef
by lifting operators on the underlying type. The following command sets
up the @{term "WF_PREDICATE"} type for lifting. *}

setup_lifting type_definition_WF_PREDICATE

subsection {* Functions *}

type_synonym 'VALUE WF_FUNCTION = "'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE"

subsection {* Operators *}

text {* We define many of these operators by lifting. Each lift
definition requires a name, type, underlying operator and a proof
that the operator is closed under the charateristic set. *}

subsubsection {* Shallow Lifting *}

lift_definition LiftP ::
  "('VALUE WF_BINDING \<Rightarrow> bool) \<Rightarrow>
   'VALUE WF_PREDICATE" is 
  "Collect :: ('VALUE WF_BINDING \<Rightarrow> bool) \<Rightarrow> 'VALUE WF_BINDING set" .

subsubsection {* Equality *}

definition EqualsP ::
  "'VALUE VAR \<Rightarrow> 'VALUE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"EqualsP v x = LiftP (\<lambda> b . \<langle>b\<rangle>\<^sub>bv = x)"

notation EqualsP (infix "=\<^sub>p" 210)

subsubsection {* True and False *}

lift_definition TrueP :: "'VALUE WF_PREDICATE" 
  is "UNIV :: 'VALUE WF_BINDING set" .

setup {*
Adhoc_Overloading.add_variant @{const_name true} @{const_name TrueP}
*}

lift_definition FalseP :: "'VALUE WF_PREDICATE" 
is "{} :: 'VALUE WF_BINDING set" .

setup {*
Adhoc_Overloading.add_variant @{const_name false} @{const_name FalseP}
*}

subsubsection {* Logical Connectives *}

lift_definition NotP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" 
is "uminus" .

notation NotP ("\<not>\<^sub>p _" [190] 190)

lift_definition AndP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" 
is "op \<inter> :: 'VALUE WF_BINDING set \<Rightarrow> 'VALUE WF_BINDING set \<Rightarrow> 'VALUE WF_BINDING set" .

notation AndP (infixr "\<and>\<^sub>p" 180)

lift_definition OrP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" 
is "op \<union> :: 'VALUE WF_BINDING set \<Rightarrow> 'VALUE WF_BINDING set \<Rightarrow> 'VALUE WF_BINDING set" .

notation OrP (infixr "\<or>\<^sub>p" 170)

definition ImpliesP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"ImpliesP p1 p2 = \<not>\<^sub>p p1 \<or>\<^sub>p p2"

notation ImpliesP (infixr "\<Rightarrow>\<^sub>p" 160)

definition IffP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"IffP p1 p2 \<equiv> (p1 \<Rightarrow>\<^sub>p p2) \<and>\<^sub>p (p2 \<Rightarrow>\<^sub>p p1)"

notation IffP (infixr "\<Leftrightarrow>\<^sub>p" 150)

subsubsection {* Quantifiers *}

lift_definition ExistsP ::
  "('VALUE VAR set) \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" is
"\<lambda> vs p. {b1 \<oplus>\<^sub>b b2 on vs | b1 b2. b1 \<in> p}" .

notation ExistsP ("(\<exists>\<^sub>p _ ./ _)" [0, 10] 10)

definition ForallP ::
  "'VALUE VAR set \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"ForallP vs p = \<not>\<^sub>p (\<exists>\<^sub>p vs . \<not>\<^sub>p p)"

notation ForallP ("(\<forall>\<^sub>p _ ./ _)" [0, 10] 10)

text {* Shallow versions of the quantifiers *}

lift_definition ExistsShP :: 
  "('b::type \<Rightarrow> 'a WF_PREDICATE) \<Rightarrow> 'a WF_PREDICATE" is
"\<lambda> P. {b :: 'a WF_BINDING. (\<exists> x. b \<in> P x)}" .

notation ExistsShP (binder "\<exists>\<^sub>s" 10)

lift_definition ForallShP :: 
  "('b::type \<Rightarrow> 'a WF_PREDICATE) \<Rightarrow> 'a WF_PREDICATE" is
"\<lambda> P. {b :: 'a WF_BINDING. (\<forall> x. b \<in> P x)}" .

notation ForallShP (binder "\<forall>\<^sub>s" 10)

subsubsection {* Universal Closure *}

definition ClosureP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"ClosureP p = (\<forall>\<^sub>p VAR . p)"

notation ClosureP ("[_]\<^sub>p")

subsubsection {* Refinement *}

definition RefP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"RefP p1 p2 = [p2 \<Rightarrow>\<^sub>p p1]\<^sub>p"

notation RefP (infix "\<sqsubseteq>\<^sub>p" 100)

subsubsection {* Predicate Permuation *}

lift_definition PermP ::
  "'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" is
"\<lambda> ss p. (RenameB ss) ` p" .

abbreviation RenameP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_PREDICATE" ("_[_]\<^sub>p" [200] 200) where
"RenameP p ss \<equiv> PermP ss p"

setup {*
Adhoc_Overloading.add_variant @{const_name permute} @{const_name PermP}
*}

definition RenamePMap :: 
  "'VALUE  WF_PREDICATE \<Rightarrow> 
   ('VALUE VAR \<rightharpoonup> 'VALUE VAR) \<Rightarrow> 
   'VALUE WF_PREDICATE" ("_\<^bsup>_\<^esup>" [200]) where
"RenamePMap p ss \<equiv> p[MapR ss]\<^sub>p"

subsection {* Meta-logical Operators *}

subsubsection {* Tautologies *}

definition Tautology ::
  "'VALUE WF_PREDICATE \<Rightarrow> bool" where
"Tautology p \<longleftrightarrow> [p]\<^sub>p = true"

declare [[coercion Tautology]]

notation Tautology ("taut _" [50] 50)

definition Contradiction ::
  "'VALUE WF_PREDICATE \<Rightarrow> bool" where
"Contradiction p \<longleftrightarrow> [p]\<^sub>p = false"

notation Contradiction ("contra _" [50] 50)

definition Contingency ::
  "'VALUE WF_PREDICATE \<Rightarrow> bool" where
"Contingency p \<longleftrightarrow> (\<not> taut p) \<and> (\<not> contra p)"

notation Contingency ("contg _" [50] 50)

subsubsection {* Refinement *}

instantiation WF_PREDICATE :: (VALUE) ord
begin

definition less_eq_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> bool" where
"less_eq_WF_PREDICATE p1 p2 \<longleftrightarrow> taut (p2 \<sqsubseteq>\<^sub>p p1)"

definition less_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> bool" where
"less_WF_PREDICATE p1 p2 \<longleftrightarrow> taut (p2 \<sqsubseteq>\<^sub>p p1) \<and> \<not> taut (p1 \<sqsubseteq>\<^sub>p p2)"

instance ..

end

text {* Since we want the refinement operator for several types but don't
        want to conflate it with any partial order, we create a vacuous subclass
        which adds the correct syntax. *}

class refines = ord 

instantiation WF_PREDICATE :: (VALUE) refines begin instance .. end

abbreviation RefinesP :: "'a::refines \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
"p \<sqsubseteq> q \<equiv> q \<le> p"

subsection {* Theorems *}

theorem WF_BINDING_override_on_VAR [simp] :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b1 \<oplus> b2 on VAR = b2"
  by (auto)

subsubsection {* Validation of Soundness *}

theorem TrueP_noteq_FalseP :
"true \<noteq> false"
  by (auto simp add: TrueP.rep_eq FalseP.rep_eq)

end
