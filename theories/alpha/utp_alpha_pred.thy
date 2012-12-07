(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_pred.thy                                                   *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Predicates *}

theory utp_alpha_pred
imports "../core/utp_pred" "../core/utp_laws" utp_alphabet
begin

subsection {* Locale @{text "ALPHA_PRED"} *}

locale ALPHA_PRED =
  PRED "type_rel"
-- {* Typing Relation for Values *}
for type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
begin

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
   ('VALUE, 'TYPE) BINDING_PRED \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 f \<in> WF_BINDING_PRED a \<longrightarrow>
 LiftA a f = (a, LiftP f)"

subsubsection {* Equality *}

definition EqualsA ::
  "'TYPE VAR \<Rightarrow> 'VALUE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"EqualsA v x = ({v}, v =p x)"

notation EqualsA (infix "=\<alpha>" 210)

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

abbreviation TRUE :: "('VALUE, 'TYPE) ALPHA_PREDICATE" where
"TRUE \<equiv> true {}"

abbreviation FALSE :: "('VALUE, 'TYPE) ALPHA_PREDICATE" where
"FALSE \<equiv> false {}"

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
 ExistsA a p = (\<alpha> p, \<exists>p a . \<pi> p)"

notation ExistsA ("(\<exists>\<alpha> _ ./ _)" [0, 10] 10)

definition ForallA ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ForallA a p = (\<alpha> p, \<forall>p a . \<pi> p)"

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
 RefA p1 p2 = ({}, (\<pi> p1) \<sqsubseteq>p (\<pi> p2))"

notation RefA (infix "\<sqsubseteq>\<alpha>" 100)

subsection {* Meta-logical Operators *}

definition TautologyA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 TautologyA p = (p = true (\<alpha> p))"

notation TautologyA ("taut _" [50] 50)

definition ContradictionA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ContradictionA p = (p = false (\<alpha> p))"

notation ContradictionA ("contra _" [50] 50)

definition RefinementA ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<and>
 (\<alpha> p1) = (\<alpha> p2) \<longrightarrow>
 RefinementA p1 p2 = (taut (p1 \<sqsubseteq>\<alpha> p2))"

notation RefinementA (infix "\<sqsubseteq>" 50)

subsection {* Theorems *}

theorem WF_ALPHA_PREDICATE_WF_ALPHABET [closure] :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> \<alpha> p \<in> WF_ALPHABET"
apply (simp add: WF_ALPHA_PREDICATE_def)
done

theorem WF_ALPHA_PREDICATE_WF_PREDICATE [closure] :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> \<pi> p \<in> WF_PREDICATE"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
done

theorem WF_ALPHA_PREDICATE_UNREST [closure] (* [dest] *) :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> UNREST (VAR - \<alpha> p) (\<pi> p)"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
done

theorem WF_ALPHA_PREDICATE_UNREST_intro [intro] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<subseteq> VAR - (\<alpha> p)\<rbrakk> \<Longrightarrow> UNREST a (\<pi> p)"
apply (insert WF_ALPHA_PREDICATE_UNREST [of "p"])
apply (clarsimp)
apply (erule UNREST_subset)
apply (assumption)
apply (simp add: closure)
done

subsubsection {* Closure Theorems *}

theorem LiftA_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_PRED a\<rbrakk> \<Longrightarrow>
 LiftA a f \<in> WF_ALPHA_PREDICATE"
apply (simp add: LiftA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem EqualsA_closure [closure] :
"v =\<alpha> x \<in> WF_ALPHA_PREDICATE"
apply (simp add: EqualsA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem ExtP_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<oplus>\<alpha> a \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExtA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem ResP_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<ominus>\<alpha> a \<in> WF_ALPHA_PREDICATE"
apply (simp add: ResA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem TrueA_closure [closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 (true a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: TrueA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem FalseA_closure [closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 (false a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: FalseA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem NotA_closure [closure] :
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow>
 \<not>\<alpha> p \<in> WF_ALPHA_PREDICATE"
apply (simp add: NotA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem AndA_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>\<alpha> p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: AndA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem OrA_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>\<alpha> p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: OrA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem ImpliesA_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Rightarrow>\<alpha> p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: ImpliesA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem IffA_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Leftrightarrow>\<alpha> p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: IffA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem ExistsA_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (\<exists>\<alpha> a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExistsA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem ForallA_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (\<forall>\<alpha> a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ForallA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem ExistsResA_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (\<exists>-\<alpha> a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExistsResA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem ForallResA_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (\<forall>-\<alpha> a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ForallResA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem ClosureA_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 [p]\<alpha> \<in> WF_ALPHA_PREDICATE"
apply (simp add: ClosureA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

theorem RefA_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<sqsubseteq>\<alpha> p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: RefA_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (simp add: closure)
apply (auto intro: unrest)
done

subsubsection {* Alphabet Theorems *}

theorem LiftA_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_PRED a\<rbrakk> \<Longrightarrow>
 \<alpha> (LiftA a (\<lambda> b . f b)) = a"
apply (simp add: LiftA_def)
done

theorem EqualsA_alphabet [alphabet] :
"\<alpha> (v =\<alpha> x) = {v}"
apply (simp add: EqualsA_def)
done

theorem TrueA_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (true a) = a"
apply (simp add: TrueA_def)
done

theorem FalseA_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (false a) = a"
apply (simp add: FalseA_def)
done

theorem ExtA_alphabet [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (p \<oplus>\<alpha> a) = (\<alpha> p) \<union> a"
apply (simp add: ExtA_def)
done

theorem ResA_alphabet [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (p \<ominus>\<alpha> a) = (\<alpha> p) - a"
apply (simp add: ResA_def)
done

theorem NotA_alphabet [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<not>\<alpha> p) = (\<alpha> p)"
apply (simp add: NotA_def)
done

theorem AndA_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<and>\<alpha> p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
apply (simp add: AndA_def)
done

theorem OrA_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<or>\<alpha> p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
apply (simp add: OrA_def)
done

theorem ImpliesA_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<Rightarrow>\<alpha> p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
apply (simp add: ImpliesA_def)
done

theorem IffA_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<Leftrightarrow>\<alpha> p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
apply (simp add: IffA_def)
done

theorem ExistsA_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<exists>\<alpha> a . p) = (\<alpha> p)"
apply (simp add: ExistsA_def)
done

theorem ForallA_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<forall>\<alpha> a . p) = (\<alpha> p)"
apply (simp add: ForallA_def)
done

theorem ExistsResA_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<exists>-\<alpha> a . p) = (\<alpha> p) - a"
apply (simp add: ExistsResA_def)
done

theorem ForallResA_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<forall>-\<alpha> a . p) = (\<alpha> p) - a"
apply (simp add: ForallResA_def)
done

theorem ClosureA_alphabet [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> ([p]\<alpha>) = {}"
apply (simp add: ClosureA_def)
done

theorem RefA_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<sqsubseteq>\<alpha> p2) = {}"
apply (simp add: RefA_def alphabet closure)
done

subsubsection {* Validation of Soundness *}

theorem ImpliesA_lemma :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Rightarrow>\<alpha> p2 = \<not>\<alpha> p1 \<or>\<alpha> p2"
apply (simp add: ImpliesA_def)
apply (simp add: ImpliesP_def closure)
apply (simp add: OrA_def closure)
apply (simp add: NotA_def closure)
done

theorem IffA_lemma :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Leftrightarrow>\<alpha> p2 = (p1 \<Rightarrow>\<alpha> p2) \<and>\<alpha> (p2 \<Rightarrow>\<alpha> p1)"
apply (simp add: IffA_def)
apply (simp add: IffP_def closure)
apply (simp add: AndA_def closure)
apply (simp add: ImpliesA_def closure)
apply (auto)
done

theorem ExistsA_lemma :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (\<exists>\<alpha> a . p) = (p \<ominus>\<alpha> a) \<oplus>\<alpha> (\<alpha> p)"
apply (simp add: ExistsA_def)
apply (simp add: ExtA_def closure)
apply (simp add: ResA_def closure)
apply (auto)
done

theorem ForallA_lemma :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (\<forall>\<alpha> a . p) = \<not>\<alpha> (\<exists>\<alpha> a . \<not>\<alpha> p)"
apply (simp add: ForallA_def)
apply (simp add: ForallP_def closure)
apply (subst NotA_def)
apply (simp add: closure)
apply (simp add: ExistsA_def closure)
apply (simp add: NotA_def closure)
done

theorem ExistsResA_lemma :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (\<exists>-\<alpha> a . p) = p \<ominus>\<alpha> a"
apply (simp add: ExistsResA_def)
apply (simp add: ResA_def closure)
done

theorem ForallResA_lemma :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (\<forall>-\<alpha> a . p) = \<not>\<alpha> (\<exists>-\<alpha> a . \<not>\<alpha> p)"
apply (simp add: ForallResA_def)
apply (simp add: ForallP_def closure)
apply (subst NotA_def)
apply (simp add: closure)
apply (simp add: ExistsResA_def closure)
apply (simp add: NotA_def closure)
done

lemma VAR_decomp :
"VAR = vs \<union> (VAR - vs)"
apply (simp add: VAR_def)
done

theorem ClosureA_lemma :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 [p]\<alpha> = (\<forall>-\<alpha> (\<alpha> p) . p)"
apply (simp add: ClosureA_def)
apply (simp add: ClosureP_def closure)
apply (simp add: ForallResA_def closure)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (clarify)
apply (subst VAR_decomp [of "\<alpha> p"])
apply (simp only: ForallP_union)
apply (simp only: ForallP_ident)
done

theorem RefA_lemma :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<sqsubseteq>\<alpha> p2 = [p2 \<Rightarrow>\<alpha> p1]\<alpha>"
apply (simp add: RefA_def)
apply (simp add: RefP_def closure)
apply (simp add: ClosureA_def closure)
apply (simp add: ImpliesA_def closure)
done

theorem TrueA_noteq_FalseA :
"a \<in> WF_ALPHABET \<Longrightarrow> true a \<noteq> false a"
apply (simp add: TrueA_def FalseA_def)
apply (simp add: TrueP_noteq_FalseP)
done
end
end
