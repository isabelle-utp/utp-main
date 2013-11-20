(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_pred.thy                                                   *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Alphabetised Predicates *}

theory utp_alpha_pred
imports 
  "../core/utp_pred" 
  "../laws/utp_pred_laws" 
begin

text {* Theorem Attribute *}

ML {*
  structure evala =
    Named_Thms (val name = @{binding evala} val description = "evala theorems")
*}

setup evala.setup

ML {*
  structure alphabet =
    Named_Thms (val name = @{binding alphabet} val description = "alphabet theorems")
*}

setup alphabet.setup

subsection {* Wellformed alphabetised predicates *}

type_synonym 'VALUE ALPHA_PREDICATE =
  "('VALUE ALPHABET) \<times> 'VALUE WF_PREDICATE"

definition WF_ALPHA_PREDICATE ::
  "'VALUE ALPHA_PREDICATE set" where
"WF_ALPHA_PREDICATE =
 {(a,p) | a p . p \<in> WF_PREDICATE_OVER \<langle>a\<rangle>\<^sub>f}"

typedef 'a WF_ALPHA_PREDICATE = "WF_ALPHA_PREDICATE :: 'a ALPHA_PREDICATE set"
morphisms DestPredA MkPredA
  apply (auto simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (metis UNREST_FalseP prod_caseI)
done

declare DestPredA [simp]
declare DestPredA_inverse [simp]
declare MkPredA_inverse [simp]

lemma DestPredA_intro [intro]:
  "DestPredA x = DestPredA y \<Longrightarrow> x = y"
  by (simp add:DestPredA_inject)

lemma DestPredA_elim [elim]:
  "\<lbrakk> x = y; DestPredA x = DestPredA y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

notation DestPredA ("\<langle>_\<rangle>\<^sub>\<alpha>")

setup_lifting type_definition_WF_ALPHA_PREDICATE

definition pred_alphabet ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE ALPHABET" where
"pred_alphabet p \<equiv> fst \<langle>p\<rangle>\<^sub>\<alpha>"

setup {*
Adhoc_Overloading.add_variant @{const_name alphabet} @{const_name pred_alphabet}
*}

abbreviation predicate ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"predicate p \<equiv> snd \<langle>p\<rangle>\<^sub>\<alpha>"

notation predicate ("\<pi>")

type_synonym 'VALUE ALPHA_FUNCTION =
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE"

definition WF_ALPHA_PREDICATE_OVER ::
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE set" where
"WF_ALPHA_PREDICATE_OVER a = {p . \<alpha> p = a}"

theorem WF_ALPHA_PREDICATE_UNREST [unrest] (* [dest] *) :
"UNREST (VAR - \<langle>\<alpha> p\<rangle>\<^sub>f) (\<pi> p)"
apply (insert DestPredA[of p])
apply (auto simp add: WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def pred_alphabet_def)
done

subsection {* Operators *}

subsubsection {* Shallow Lifting *}

definition LiftA ::
  "'a ALPHABET \<Rightarrow>
   ('a WF_BINDING \<Rightarrow> bool) \<Rightarrow>
   'a WF_ALPHA_PREDICATE" where
"LiftA a f = MkPredA (a, LiftP f)"

subsubsection {* Equality *}

lift_definition EqualsA ::
  "'a VAR \<Rightarrow> 'a \<Rightarrow>
   'a WF_ALPHA_PREDICATE" is "\<lambda> v x. (\<lbrace>v\<rbrace>, v =\<^sub>p x)"
  by (simp add: WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def unrest)
  
notation EqualsA (infix "=\<^sub>\<alpha>" 210)

subsubsection {* Extension and Restriction *}

lift_definition ExtA ::
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a ALPHABET \<Rightarrow>
   'a WF_ALPHA_PREDICATE" is
"\<lambda> p a. ((\<alpha> p) \<union>\<^sub>f a, \<pi> p)"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (auto intro: unrest)
done

notation ExtA (infix "\<oplus>\<^sub>\<alpha>" 200)

lift_definition ResA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> p a. ((\<alpha> p) -\<^sub>f a, \<exists>\<^sub>p \<langle>a\<rangle>\<^sub>f . \<pi> p)"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_PREDICATE_OVER_def)
apply (auto intro: unrest)  
done

notation ResA (infix "\<ominus>\<^sub>\<alpha>" 200)

subsubsection {* True and False *}

definition TrueA ::
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" where
"TrueA a = MkPredA (a, true)"

notation TrueA ("true\<^bsub>_\<^esub>")

definition FalseA ::
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" where
"FalseA a = MkPredA (a, false)"

notation FalseA ("false\<^bsub>_\<^esub>")

abbreviation TRUE :: "'VALUE WF_ALPHA_PREDICATE" where
"TRUE \<equiv> true\<^bsub>\<lbrace>\<rbrace>\<^esub>"

abbreviation FALSE :: "'VALUE WF_ALPHA_PREDICATE" where
"FALSE \<equiv> false\<^bsub>\<lbrace>\<rbrace>\<^esub>"

subsubsection {* Logical Connectives *}

lift_definition NotA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> p. (\<alpha> p, \<not>\<^sub>p (\<pi> p))"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation NotA ("\<not>\<^sub>\<alpha> _" [190] 190)

lift_definition AndA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> p1 p2. ((\<alpha> p1) \<union>\<^sub>f (\<alpha> p2), (\<pi> p1) \<and>\<^sub>p (\<pi> p2))"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation AndA (infixr "\<and>\<^sub>\<alpha>" 180)

lift_definition OrA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> p1 p2 . ((\<alpha> p1) \<union>\<^sub>f (\<alpha> p2), (\<pi> p1) \<or>\<^sub>p (\<pi> p2))"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation OrA (infixr "\<or>\<^sub>\<alpha>" 170)

lift_definition ImpliesA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> p1 p2 . ((\<alpha> p1) \<union>\<^sub>f (\<alpha> p2), (\<pi> p1) \<Rightarrow>\<^sub>p (\<pi> p2))"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation ImpliesA (infixr "\<Rightarrow>\<^sub>\<alpha>" 160)

lift_definition IffA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> p1 p2 . ((\<alpha> p1) \<union>\<^sub>f (\<alpha> p2), (\<pi> p1) \<Leftrightarrow>\<^sub>p (\<pi> p2))"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation IffA (infixr "\<Leftrightarrow>\<^sub>\<alpha>" 150)

subsubsection {* Quantifiers *}

lift_definition ExistsA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> a p . (\<alpha> p, \<exists>\<^sub>p \<langle>a\<rangle>\<^sub>f . \<pi> p)"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation ExistsA ("(\<exists>\<^sub>\<alpha> _ ./ _)" [0, 10] 10)

lift_definition ForallA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> a p. (\<alpha> p, \<forall>\<^sub>p \<langle>a\<rangle>\<^sub>f . \<pi> p)"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation ForallA ("(\<forall>\<^sub>\<alpha> _ ./ _)" [0, 10] 10)

lift_definition ExistsResA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> a p. ((\<alpha> p) -\<^sub>f a, \<exists>\<^sub>p \<langle>a\<rangle>\<^sub>f . \<pi> p)"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation ExistsResA ("(\<exists>-\<^sub>\<alpha> _ ./ _)" [0, 10] 10)

lift_definition ForallResA ::
  "'VALUE ALPHABET \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> a p. ((\<alpha> p) -\<^sub>f a, \<forall>\<^sub>p \<langle>a\<rangle>\<^sub>f . \<pi> p)"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation ForallResA ("(\<forall>-\<^sub>\<alpha> _ ./ _)" [0, 10] 10)

subsubsection {* Universal Closure *}

lift_definition ClosureA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> p. (\<lbrace>\<rbrace>, [\<pi> p]\<^sub>p)"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation ClosureA ("[_]\<^sub>\<alpha>")

subsubsection {* Refinement *}

lift_definition RefA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" is
"\<lambda> p1 p2. (\<lbrace>\<rbrace>, (\<pi> p1) \<sqsubseteq>\<^sub>p (\<pi> p2))"
  by (auto intro:unrest simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)

notation RefA (infix "\<sqsubseteq>\<^sub>\<alpha>" 100)

subsubsection {* Permuation *}

(*
lift_definition alpha_rename_image :: 
  "('VALUE VAR_RENAME) \<Rightarrow> 'VALUE ALPHABET \<Rightarrow> 'VALUE ALPHABET" (infixr "`\<^sub>\<alpha>" 90) is rename_image
  by (simp add:rename_image_def fsets_def)
*)

lift_definition PermA ::
  "'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE \<Rightarrow>
   'VALUE WF_ALPHA_PREDICATE" ("_[_]\<alpha>" [200]) is
"\<lambda> ss p. (\<langle>ss\<rangle>\<^sub>s `\<^sub>f \<alpha> p, ss\<bullet>(\<pi> p))"
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (rule UNREST_RenameP_alt)
  apply (rule WF_ALPHA_PREDICATE_UNREST)
  apply (metis (lifting) Rep_VAR_RENAME_surj VAR_def image_diff_subset)
done

setup {*
Adhoc_Overloading.add_variant @{const_name permute} @{const_name PermA}
*}

subsection {* Meta-logical Operators *}

definition TautologyA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> bool" where
"TautologyA p = (p = true\<^bsub>\<alpha> p\<^esub>)"

notation TautologyA ("taut\<^sub>\<alpha> _" [50] 50)

definition ContradictionA ::
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> bool" where
"ContradictionA p = (p = false\<^bsub>\<alpha> p\<^esub>)"

notation ContradictionA ("contra\<^sub>\<alpha> _" [50] 50)

instantiation WF_ALPHA_PREDICATE :: (VALUE) ord
begin

definition less_eq_WF_ALPHA_PREDICATE :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE \<Rightarrow> bool" where
"less_eq_WF_ALPHA_PREDICATE p2 p1 \<longleftrightarrow> \<alpha> p2 \<subseteq>\<^sub>f \<alpha> p1 \<and> taut\<^sub>\<alpha> (p1 \<sqsubseteq>\<^sub>\<alpha> p2)"

definition less_WF_ALPHA_PREDICATE :: 
  "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a WF_ALPHA_PREDICATE \<Rightarrow> bool" where
"less_WF_ALPHA_PREDICATE p2 p1 \<longleftrightarrow> (\<alpha> p2 \<subseteq>\<^sub>f \<alpha> p1 \<and> taut\<^sub>\<alpha> (p1 \<sqsubseteq>\<^sub>\<alpha> p2)) \<and> \<not> (\<alpha> p1 \<subseteq>\<^sub>f \<alpha> p2 \<and> taut\<^sub>\<alpha> (p2 \<sqsubseteq>\<^sub>\<alpha> p1))"

instance ..

end

instantiation WF_ALPHA_PREDICATE :: (VALUE) refines begin instance .. end

subsection {* Theorems *}

theorem WF_ALPHA_PREDICATE_UNREST_intro [intro] :
"a \<subseteq> VAR - \<langle>\<alpha> p\<rangle>\<^sub>f \<Longrightarrow> UNREST a (\<pi> p)"
apply (insert WF_ALPHA_PREDICATE_UNREST [of "p"])
apply (erule UNREST_subset)
apply (assumption)
done

theorem WF_ALPHA_PREDICATE_intro [intro] :
  "\<lbrakk>\<alpha> p1 = \<alpha> p2; \<pi> p1 = \<pi> p2\<rbrakk> \<Longrightarrow> p1 = p2"
  apply (case_tac p1, case_tac p2)
  apply (simp)
  apply (case_tac y, case_tac ya)
  apply (simp add:pred_alphabet_def)
done

subsubsection {* Closure Theorems *}

theorem LiftA_rep_eq:
  "f \<in> WF_BINDING_PRED \<langle>a\<rangle>\<^sub>f \<Longrightarrow>
   DestPredA (LiftA a f) = (a, LiftP f)"
  apply (subgoal_tac "(a, LiftP f) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:LiftA_def)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def)
  apply (auto intro:unrest)
done

theorem TrueA_rep_eq:
  "DestPredA (TrueA a) = (a, TrueP)"
  apply (subgoal_tac "(a, true) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:TrueA_def)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def unrest)
done

theorem FalseA_rep_eq:
  "DestPredA (FalseA a) = (a, FalseP)"
  apply (subgoal_tac "(a, false) \<in> WF_ALPHA_PREDICATE")
  apply (simp add:FalseA_def)
  apply (simp add:WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def unrest)
done

subsubsection {* Alphabet Theorems *}

declare pred_alphabet_def [simp]

theorem LiftA_alphabet [alphabet] :
"\<lbrakk>f \<in> WF_BINDING_PRED \<langle>a\<rangle>\<^sub>f\<rbrakk> \<Longrightarrow>
 \<alpha> (LiftA a (\<lambda> b . f b)) = a"
  by (simp add: LiftA_rep_eq)

theorem EqualsA_alphabet [alphabet] :
"\<alpha> (v =\<^sub>\<alpha> x) = \<lbrace>v\<rbrace>"
  by (simp add: EqualsA.rep_eq)

theorem TrueA_alphabet [alphabet] :
"\<alpha> (true\<^bsub>a\<^esub>) = a"
  by (simp add: TrueA_rep_eq)

theorem FalseA_alphabet [alphabet] :
"\<alpha> (false\<^bsub>a\<^esub>) = a"
  by (simp add: FalseA_rep_eq)

theorem ExtA_alphabet [alphabet] :
"\<alpha> (p \<oplus>\<^sub>\<alpha> a) = (\<alpha> p) \<union>\<^sub>f a"
  by (simp add: ExtA.rep_eq)

theorem ResA_alphabet [alphabet] :
"\<alpha> (p \<ominus>\<^sub>\<alpha> a) = (\<alpha> p) -\<^sub>f a"
  by (simp add: ResA.rep_eq)

theorem NotA_alphabet [alphabet] :
"\<alpha> (\<not>\<^sub>\<alpha> p) = (\<alpha> p)"
  by (simp add: NotA.rep_eq)

theorem AndA_alphabet [alphabet] :
"\<alpha> (p1 \<and>\<^sub>\<alpha> p2) = (\<alpha> p1) \<union>\<^sub>f (\<alpha> p2)"
  by (simp add: AndA.rep_eq)

theorem OrA_alphabet [alphabet] :
"\<alpha> (p1 \<or>\<^sub>\<alpha> p2) = (\<alpha> p1) \<union>\<^sub>f (\<alpha> p2)"
  by (simp add: OrA.rep_eq)

theorem ImpliesA_alphabet [alphabet] :
"\<alpha> (p1 \<Rightarrow>\<^sub>\<alpha> p2) = (\<alpha> p1) \<union>\<^sub>f (\<alpha> p2)"
  by (simp add: ImpliesA.rep_eq)

theorem IffA_alphabet [alphabet] :
"\<alpha> (p1 \<Leftrightarrow>\<^sub>\<alpha> p2) = (\<alpha> p1) \<union>\<^sub>f (\<alpha> p2)"
  by (simp add: IffA.rep_eq)

theorem ExistsA_alphabet [alphabet] :
"\<alpha> (\<exists>\<^sub>\<alpha> a . p) = (\<alpha> p)"
  by (simp add: ExistsA.rep_eq)

theorem ForallA_alphabet [alphabet] :
"\<alpha> (\<forall>\<^sub>\<alpha> a . p) = (\<alpha> p)"
  by (simp add: ForallA.rep_eq)

theorem ExistsResA_alphabet [alphabet] :
"\<alpha> (\<exists>-\<^sub>\<alpha> a . p) = (\<alpha> p) -\<^sub>f a"
  by (simp add: ExistsResA.rep_eq)

theorem ForallResA_alphabet [alphabet] :
"\<alpha> (\<forall>-\<^sub>\<alpha> a . p) = (\<alpha> p) -\<^sub>f a"
  by (simp add: ForallResA.rep_eq)

theorem ClosureA_alphabet [alphabet] :
"\<alpha> ([p]\<^sub>\<alpha>) = \<lbrace>\<rbrace>"
  by (simp add: ClosureA.rep_eq)

theorem RefA_alphabet [alphabet] :
"\<alpha> (p1 \<sqsubseteq>\<^sub>\<alpha> p2) = \<lbrace>\<rbrace>"
  by (simp add: RefA.rep_eq)

theorem PermA_alphabet [alphabet] :
"\<alpha> (ss\<bullet>p) = \<langle>ss\<rangle>\<^sub>s `\<^sub>f (\<alpha> p)"
  by (simp add:PermA.rep_eq)

subsubsection {* Validation of Soundness *}

theorem ImpliesA_lemma :
"p1 \<Rightarrow>\<^sub>\<alpha> p2 = \<not>\<^sub>\<alpha> p1 \<or>\<^sub>\<alpha> p2"
apply (rule DestPredA_intro)
apply (simp add: ImpliesA.rep_eq OrA.rep_eq NotA.rep_eq)
apply (utp_pred_tac)
done

theorem IffA_lemma :
"p1 \<Leftrightarrow>\<^sub>\<alpha> p2 = (p1 \<Rightarrow>\<^sub>\<alpha> p2) \<and>\<^sub>\<alpha> (p2 \<Rightarrow>\<^sub>\<alpha> p1)"
apply (rule DestPredA_intro)
apply (simp add: IffA.rep_eq AndA.rep_eq NotA.rep_eq ImpliesA.rep_eq)
apply (rule conjI)
apply (force)
apply (utp_pred_auto_tac)
done

theorem ExistsA_lemma :
"(\<exists>\<^sub>\<alpha> a . p) = (p \<ominus>\<^sub>\<alpha> a) \<oplus>\<^sub>\<alpha> (\<alpha> p)"
apply (rule DestPredA_intro)
apply (simp add: ExistsA.rep_eq ExtA.rep_eq ResA.rep_eq)
apply (auto)
done

theorem ForallA_lemma :
"(\<forall>\<^sub>\<alpha> a . p) = \<not>\<^sub>\<alpha> (\<exists>\<^sub>\<alpha> a . \<not>\<^sub>\<alpha> p)"
apply (rule DestPredA_intro)
apply (simp add: ForallA.rep_eq NotA.rep_eq ExistsA.rep_eq)
apply (utp_pred_auto_tac)
done

theorem ExistsResA_lemma :
"(\<exists>-\<^sub>\<alpha> a . p) = p \<ominus>\<^sub>\<alpha> a"
apply (rule DestPredA_intro)
apply (simp add: ExistsResA.rep_eq ResA.rep_eq)
done

theorem ForallResA_lemma :
"(\<forall>-\<^sub>\<alpha> a . p) = \<not>\<^sub>\<alpha> (\<exists>-\<^sub>\<alpha> a . \<not>\<^sub>\<alpha> p)"
apply (rule DestPredA_intro)
apply (simp add: ForallResA.rep_eq ExistsResA.rep_eq ResA.rep_eq NotA.rep_eq)
apply (utp_pred_auto_tac)
done

lemma VAR_decomp :
"VAR = vs \<union> (VAR - vs)"
apply (simp add: VAR_def)
done

theorem ClosureA_lemma :
"[p]\<^sub>\<alpha> = (\<forall>-\<^sub>\<alpha> (\<alpha> p) . p)"
apply (rule DestPredA_intro)
apply (simp add:ClosureA.rep_eq ForallResA.rep_eq)
apply (simp add:ClosureP_def)
apply (subst VAR_decomp [of "\<langle>\<alpha> p\<rangle>\<^sub>f"])
apply (simp only: ForallP_union)
apply (subgoal_tac "UNREST (VAR - \<langle>\<alpha> p\<rangle>\<^sub>f) (\<pi> p)")
apply (auto simp add: ForallP_ident)
done

theorem RefA_lemma :
"p1 \<sqsubseteq>\<^sub>\<alpha> p2 = [p2 \<Rightarrow>\<^sub>\<alpha> p1]\<^sub>\<alpha>"
apply (rule DestPredA_intro)
apply (simp add: RefA.rep_eq ClosureA.rep_eq ImpliesA.rep_eq)
apply (utp_pred_auto_tac)
done

theorem TrueA_noteq_FalseA :
"true\<^bsub>a\<^esub> \<noteq> false\<^bsub>b\<^esub>"
  by (auto simp add: TrueA_rep_eq FalseA_rep_eq TrueP_noteq_FalseP )

(* This lines make many later proofs easier *)
declare pred_alphabet_def [simp del]

lemma WF_ALPHA_PREDICATE_neq_elim [elim]: 
  "\<lbrakk> p \<noteq> q; \<alpha> p \<noteq> \<alpha> q \<Longrightarrow> P; (\<pi> p \<noteq> \<pi> q) \<Longrightarrow> P \<rbrakk>  \<Longrightarrow> P "
  by (auto)

theorem WF_ALPHA_PREDICATE_empty_true_false:
  "\<alpha> p = \<lbrace>\<rbrace> \<Longrightarrow> p = TRUE \<or> p = FALSE"
  apply (auto)
  apply (rule WF_ALPHA_PREDICATE_intro)
  apply (simp add:alphabet)
  apply (erule WF_ALPHA_PREDICATE_neq_elim)
  apply (simp add:TrueA_rep_eq FalseA_rep_eq alphabet)
  apply (simp add:TrueA_rep_eq FalseA_rep_eq alphabet)
  apply (insert WF_ALPHA_PREDICATE_UNREST[of p])
  apply (simp)
  apply (drule UNREST_true_false)
  apply (force)
done

theorem WF_ALPHA_PREDICATE_empty_elim:
  "\<lbrakk> \<alpha> p = \<lbrace>\<rbrace>; p = TRUE \<Longrightarrow> P; p = FALSE \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis WF_ALPHA_PREDICATE_empty_true_false)

lemma WF_ALPHA_PREDICATE_binding_equiv:
  "\<lbrakk> b1 \<in> destPRED (\<pi> p); b1 \<cong> b2 on \<langle>\<alpha> p\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> b2 \<in> destPRED (\<pi> p)"
  apply (insert WF_ALPHA_PREDICATE_UNREST[of "p"])
  apply (auto simp add:UNREST_def)
  apply (smt binding_equiv_comm binding_override_equiv binding_override_simps(10) binding_override_simps(5))
done

lemma WF_ALPHA_PREDICATE_OVER_intro [intro]:
  "\<alpha> p = a \<Longrightarrow> p \<in> WF_ALPHA_PREDICATE_OVER a"
  by (simp add:WF_ALPHA_PREDICATE_OVER_def)

lemma WF_ALPHA_PREDICATE_OVER_alphabet [alphabet]:
  "p \<in> WF_ALPHA_PREDICATE_OVER a \<Longrightarrow> \<alpha> p = a"
  by (auto simp add:WF_ALPHA_PREDICATE_OVER_def)

lemma AndA_WF_ALPHA_PREDICATE_OVER [closure]:
  "\<lbrakk> p \<in> WF_ALPHA_PREDICATE_OVER a; q \<in> WF_ALPHA_PREDICATE_OVER a \<rbrakk> \<Longrightarrow>
   p \<and>\<^sub>\<alpha> q \<in> WF_ALPHA_PREDICATE_OVER a"
  by (auto simp add:alphabet)

lemma OrA_WF_ALPHA_PREDICATE_OVER [closure]:
  "\<lbrakk> p \<in> WF_ALPHA_PREDICATE_OVER a; q \<in> WF_ALPHA_PREDICATE_OVER a \<rbrakk> \<Longrightarrow>
   p \<or>\<^sub>\<alpha> q \<in> WF_ALPHA_PREDICATE_OVER a"
  by (auto simp add:alphabet)

end
