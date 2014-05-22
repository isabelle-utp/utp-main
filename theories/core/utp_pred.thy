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

type_synonym 'a binding_pred = "'a binding \<Rightarrow> bool"
type_synonym 'a binding_fun = "'a binding \<Rightarrow> 'a"

definition WF_BINDING_PRED ::
  "'a uvar set \<Rightarrow> 'a binding_pred set" where
"WF_BINDING_PRED vs = {f . \<forall> b1 b2 . b1 \<cong> b2 on vs \<longrightarrow> f b1 = f b2}"

typedef 'a upred = "UNIV :: 'a binding set set"
morphisms destPRED mkPRED
  by (auto)

declare destPRED [simp]
declare destPRED_inverse [simp]
declare mkPRED_inverse [simp]

lemma destPRED_intro [intro]:
  "destPRED x = destPRED y \<Longrightarrow> x = y"
  by (simp add:destPRED_inject)

lemma destPRED_elim [elim]:
  "\<lbrakk> x = y; destPRED x = destPRED y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

text {* The lifting package allows us to define operators on a typedef
by lifting operators on the underlying type. The following command sets
up the @{term "upred"} type for lifting. *}

setup_lifting type_definition_upred

subsection {* Functions *}

type_synonym 'a WF_FUNCTION = "'a upred \<Rightarrow> 'a upred"

subsection {* Operators *}

text {* We define many of these operators by lifting. Each lift
definition requires a name, type, underlying operator and a proof
that the operator is closed under the charateristic set. *}

subsubsection {* Shallow Lifting *}

lift_definition LiftP ::
  "('a binding \<Rightarrow> bool) \<Rightarrow>
   'a upred" is 
  "Collect :: ('a binding \<Rightarrow> bool) \<Rightarrow> 'a binding set" .

subsubsection {* Equality *}

definition EqualsP ::
  "'a uvar \<Rightarrow> 'a \<Rightarrow>
   'a upred" where
"EqualsP v x = LiftP (\<lambda> b . \<langle>b\<rangle>\<^sub>bv = x)"

notation EqualsP (infix "=\<^sub>p" 210)

subsubsection {* True and False *}

lift_definition TrueP :: "'a upred" 
  is "UNIV :: 'a binding set" .

notation TrueP ("true")

lift_definition FalseP :: "'a upred" 
is "{} :: 'a binding set" .

notation FalseP ("false")

subsubsection {* Logical Connectives *}

lift_definition NotP ::
  "'a upred \<Rightarrow>
   'a upred" 
is "uminus" .

notation NotP ("\<not>\<^sub>p _" [190] 190)

lift_definition AndP ::
  "'a upred \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" 
is "op \<inter> :: 'a binding set \<Rightarrow> 'a binding set \<Rightarrow> 'a binding set" .

notation AndP (infixr "\<and>\<^sub>p" 180)

lift_definition OrP ::
  "'a upred \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" 
is "op \<union> :: 'a binding set \<Rightarrow> 'a binding set \<Rightarrow> 'a binding set" .

notation OrP (infixr "\<or>\<^sub>p" 170)

definition ImpliesP ::
  "'a upred \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" where
"ImpliesP p1 p2 = \<not>\<^sub>p p1 \<or>\<^sub>p p2"

notation ImpliesP (infixr "\<Rightarrow>\<^sub>p" 160)

definition IffP ::
  "'a upred \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" where
"IffP p1 p2 \<equiv> (p1 \<Rightarrow>\<^sub>p p2) \<and>\<^sub>p (p2 \<Rightarrow>\<^sub>p p1)"

notation IffP (infixr "\<Leftrightarrow>\<^sub>p" 150)

definition AndDistP :: "'a upred set \<Rightarrow> 'a upred"
where "AndDistP ps = mkPRED (\<Inter> {destPRED p | p. p \<in> ps})"

notation AndDistP ("\<And>\<^sub>p _" [900] 900)

lemma AndDistP_rep_eq: "destPRED (\<And>\<^sub>p ps) = \<Inter> {destPRED p | p. p \<in> ps}"
  by (simp add:AndDistP_def)

definition OrDistP :: "'a upred set \<Rightarrow> 'a upred"
where "OrDistP ps = mkPRED (\<Union> {destPRED p | p. p \<in> ps})"

notation OrDistP ("\<Or>\<^sub>p _" [900] 900)

lemma OrDistP_rep_eq: "destPRED (\<Or>\<^sub>p ps) = \<Union> {destPRED p | p. p \<in> ps}"
  by (simp add:OrDistP_def)

default_sort type

definition ANDI :: "'b set \<Rightarrow> ('b \<Rightarrow> ('a::VALUE) upred) \<Rightarrow> 'a upred" where
"ANDI A f = \<And>\<^sub>p(f ` A)"

definition ORDI :: "'b set \<Rightarrow> ('b \<Rightarrow> ('a::VALUE) upred) \<Rightarrow> 'a upred" where
"ORDI A f = \<Or>\<^sub>p(f ` A)"

syntax
  "_ANDI1" :: "pttrns \<Rightarrow> 'a upred \<Rightarrow> 'a upred" ("(3AND _./ _)" [0, 10] 10)
  "_ANDI"  :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a upred \<Rightarrow> 'a upred"  ("(3AND _:_./ _)" [0, 0, 10] 10)
  "_ORDI1" :: "pttrns \<Rightarrow> 'a upred \<Rightarrow> 'a upred" ("(3OR _./ _)" [0, 10] 10)
  "_ORDI"  :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a upred \<Rightarrow> 'a upred"  ("(3OR _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_ANDI1" :: "pttrns \<Rightarrow> 'a upred \<Rightarrow> 'a upred" ("(3\<And>\<^sub>p_./ _)" [0, 10] 10)
  "_ANDI"  :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a upred \<Rightarrow> 'a upred"  ("(3\<And>\<^sub>p _:_./ _)" [0, 0, 10] 10)
  "_ORDI1" :: "pttrns \<Rightarrow> 'a upred \<Rightarrow> 'a upred" ("(3\<Or>\<^sub>p _./ _)" [0, 10] 10)
  "_ORDI"  :: "pttrn \<Rightarrow> 'b set \<Rightarrow> 'a upred \<Rightarrow> 'a upred"  ("(3\<Or>\<^sub>p _:_./ _)" [0, 0, 10] 10)

translations
  "AND x y. B"  == "AND x. AND y. B"
  "AND x. B"    == "CONST ANDI CONST UNIV (%x. B)"
  "AND x. B"    == "AND x:CONST UNIV. B"
  "AND x:A. B"  == "CONST ANDI A (%x. B)"
  "OR x y. B"   == "OR x. OR y. B"
  "OR x. B"     == "CONST ORDI CONST UNIV (%x. B)"
  "OR x. B"     == "OR x:CONST UNIV. B"
  "OR x:A. B"   == "CONST ORDI A (%x. B)"

default_sort VALUE

subsubsection {* Quantifiers *}

lift_definition ExistsP ::
  "('a uvar set) \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" is
"\<lambda> vs p. {b1 \<oplus>\<^sub>b b2 on vs | b1 b2. b1 \<in> p}" .

notation ExistsP ("(\<exists>\<^sub>p _ ./ _)" [0, 10] 10)

definition ForallP ::
  "'a uvar set \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" where
"ForallP vs p = \<not>\<^sub>p (\<exists>\<^sub>p vs . \<not>\<^sub>p p)"

notation ForallP ("(\<forall>\<^sub>p _ ./ _)" [0, 10] 10)

text {* Shallow versions of the quantifiers *}

lift_definition ExistsShP :: 
  "('b::type \<Rightarrow> 'a upred) \<Rightarrow> 'a upred" is
"\<lambda> P. {b :: 'a binding. (\<exists> x. b \<in> P x)}" .

notation ExistsShP (binder "\<exists>\<^sub>s" 10)

lift_definition ForallShP :: 
  "('b::type \<Rightarrow> 'a upred) \<Rightarrow> 'a upred" is
"\<lambda> P. {b :: 'a binding. (\<forall> x. b \<in> P x)}" .

notation ForallShP (binder "\<forall>\<^sub>s" 10)

subsubsection {* Universal Closure *}

definition ClosureP ::
  "'a upred \<Rightarrow>
   'a upred" where
"ClosureP p = (\<forall>\<^sub>p VAR . p)"

notation ClosureP ("[_]\<^sub>p")

subsubsection {* Refinement *}

definition RefP ::
  "'a upred \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" where
"RefP p1 p2 = [p2 \<Rightarrow>\<^sub>p p1]\<^sub>p"

notation RefP (infix "\<sqsubseteq>\<^sub>p" 100)

subsubsection {* Predicate Permuation *}

lift_definition PermP ::
  "'a VAR_RENAME \<Rightarrow>
   'a upred \<Rightarrow>
   'a upred" is
"\<lambda> ss p. (RenameB ss) ` p" .

abbreviation RenameP ::
  "'a upred \<Rightarrow>
   'a VAR_RENAME \<Rightarrow>
   'a upred" ("_[_]\<^sub>p" [200] 200) where
"RenameP p ss \<equiv> PermP ss p"

adhoc_overloading
  permute PermP

subsection {* Meta-logical Operators *}

subsubsection {* Tautologies *}

definition Tautology ::
  "'a upred \<Rightarrow> bool" where
"Tautology p \<longleftrightarrow> [p]\<^sub>p = true"

declare [[coercion Tautology]]

notation Tautology ("taut _" [50] 50)

definition Contradiction ::
  "'a upred \<Rightarrow> bool" where
"Contradiction p \<longleftrightarrow> [p]\<^sub>p = false"

notation Contradiction ("contra _" [50] 50)

definition Contingency ::
  "'a upred \<Rightarrow> bool" where
"Contingency p \<longleftrightarrow> (\<not> taut p) \<and> (\<not> contra p)"

notation Contingency ("contg _" [50] 50)

subsubsection {* Refinement *}

instantiation upred :: (VALUE) ord
begin

definition less_eq_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> bool" where
"less_eq_upred p1 p2 \<longleftrightarrow> taut (p2 \<sqsubseteq>\<^sub>p p1)"

definition less_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> bool" where
"less_upred p1 p2 \<longleftrightarrow> taut (p2 \<sqsubseteq>\<^sub>p p1) \<and> \<not> taut (p1 \<sqsubseteq>\<^sub>p p2)"

instance ..

end

text {* Since we want the refinement operator for several types but don't
        want to conflate it with any partial order, we create a vacuous subclass
        which adds the correct syntax. *}

class refines = ord 

instantiation upred :: (VALUE) refines begin instance .. end

abbreviation RefinesP :: "'a::refines \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
"p \<sqsubseteq> q \<equiv> q \<le> p"

subsection {* Theorems *}

theorem binding_override_on_VAR [simp] :
"\<lbrakk>b1 \<in> binding;
 b2 \<in> binding\<rbrakk> \<Longrightarrow>
 b1 \<oplus> b2 on VAR = b2"
  by (auto)

subsubsection {* Validation of Soundness *}

theorem TrueP_noteq_FalseP :
"true \<noteq> false"
  by (auto simp add: TrueP.rep_eq FalseP.rep_eq)

subsection {* Predicate to map set *}

definition pred_map_set :: "'a uvar set \<Rightarrow> 'a upred \<Rightarrow> ('a uvar \<rightharpoonup> 'a) set" where
"pred_map_set xs p = binding_map xs ` destPRED p"

lift_definition map_set_pred :: "('a uvar \<rightharpoonup> 'a) set \<Rightarrow> 'a upred" is
"\<lambda> fs. {map_binding f \<oplus>\<^sub>b b on (VAR - dom f) | f b. f \<in> fs}" .

end
