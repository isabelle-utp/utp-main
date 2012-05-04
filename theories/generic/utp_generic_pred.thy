(******************************************************************************)
(* Title: utp/generic/utp_generic_pred.thy                                    *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_generic_pred
imports "../utp_types" utp_var utp_alphabet
begin

section {* Generic Predicates *}

subsection {* Locale @{text "GEN_PRED"} *}

text {*
  For more flexibility needed when instantiating the layered model for higher-
  order predicates, the parametrisation of the locale has changed in a way that
  we specify @{text WF_BINDING} directly rather than the typing relation. This
  allows one to impose more general structural constraints on bindings, i.e.
  here to ensure consistency of higher-order variables between layers.
*}

text {*
  An open issue at the moment is whether despite @{text "WF_BINDING"} we fix
  the notion of typing. An argument for it is that in some cases we require
  typing to specify laws, for instance, involving substitution. It seems that
  there is an implied notion of typing deduced from @{text "WF_BINDING"} but
  using it instead might make matters more complicated than necessary.
*}

locale GEN_PRED = VAR "UNIV :: 'TYPE set" +
-- {* Typing Relation *}
-- {* fixes type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50) *}
-- {* We fix the notion of well-formed bindings. *}
  fixes WF_BINDING :: "('VALUE, 'TYPE) BINDING set"
-- {* There must be at least one well-formed binding. *}
  assumes binding_non_empty [simp] : "WF_BINDING \<noteq> {}"
-- {* Typing Consistency *}
-- {* assumes typing_consistent : *}
-- {*  "x : (type v) \<longleftrightarrow> (\<exists> b \<in> WF_BINDING . x = (b v))" *}
begin

subsection {* Binding Sets *}

text {* We first introduce a notion of binding equivalence. *}

definition binding_equiv ::
  "('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('TYPE ALPHABET) \<Rightarrow> bool" where
"(binding_equiv b1 b2 a) \<longleftrightarrow> (\<forall> x \<in> a . b1 x = b2 x)"

notation binding_equiv ("_ \<cong> _ on _")

text {* Well-formed binding sets are upward-closed w.r.t. an alphabet. *}

definition WF_BINDING_SET ::
  "('TYPE ALPHABET) \<Rightarrow> ('VALUE, 'TYPE) BINDING_SET set" where
"WF_BINDING_SET a =
 {bs . bs \<subseteq> WF_BINDING \<and>
   (\<forall> b1 \<in> bs . \<forall> b2 \<in> WF_BINDING . b1 \<cong> b2 on a \<longrightarrow> b2 \<in> bs)}"

subsection {* Predicate Model *}

abbreviation alphabet ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE ALPHABET)" where
"alphabet p \<equiv> (fst p)"

notation alphabet ("\<alpha>")

abbreviation bindings ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) BINDING_SET" where
"bindings p \<equiv> (snd p)"

notation bindings ("\<beta>")

definition WF_ALPHA_PREDICATE ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_ALPHA_PREDICATE =
 {p . (\<alpha> p) \<in> WF_ALPHABET \<and> (\<beta> p) \<in> WF_BINDING_SET (\<alpha> p)}"

definition WF_ALPHA_PREDICATE_OVER ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"a \<in> WF_ALPHABET \<longrightarrow>
 WF_ALPHA_PREDICATE_OVER a = {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p = a}"

subsection {* Predicate Operators *}

subsubsection {* Shallow Lifting *}

text {* Shallow lifting is defined in terms of well-formed binding functions. *}

definition WF_BINDING_FUN ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) BINDING_FUN set" where
"WF_BINDING_FUN a = {f . \<forall> b1 b2 . b1 \<cong> b2 on a \<longrightarrow> f b1 = f b2}"

definition LiftP ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) BINDING_FUN \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 f \<in> WF_BINDING_FUN a \<longrightarrow>
 LiftP a f = (a, {b \<in> WF_BINDING . f b})"

subsubsection {* Extension and Restriction *}

definition ExtP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<and>
 a \<in> WF_ALPHABET \<longrightarrow>
 ExtP p a = ((\<alpha> p) \<union> a, \<beta> p)"

notation ExtP (infix "\<oplus>" 200)

definition ResP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<and>
 a \<in> WF_ALPHABET \<longrightarrow>
 ResP p a = ((\<alpha> p) - a,
   {b2 \<in> WF_BINDING . (\<exists> b1 \<in> \<beta> p . b1 \<cong> b2 on ((\<alpha> p) - a))})"

notation ResP (infix "\<ominus>" 200)

subsubsection {* True and False *}

definition TrueP ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<longrightarrow>
 TrueP a = (a, WF_BINDING)"

notation TrueP ("true")

definition FalseP ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<longrightarrow>
 FalseP a = (a, {})"

notation FalseP ("false")

abbreviation TRUE :: "('VALUE, 'TYPE) ALPHA_PREDICATE" where
"TRUE \<equiv> TrueP {}"

abbreviation FALSE :: "('VALUE, 'TYPE) ALPHA_PREDICATE" where
"FALSE \<equiv> FalseP {}"

subsubsection {* Logical Connectives *}

definition NotP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 NotP p = (\<alpha> p, WF_BINDING - \<beta> p)"

notation NotP ("\<not>p _" [190] 190)

definition AndP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 AndP p1 p2 = ((\<alpha> p1) \<union> (\<alpha> p2), (\<beta> p1) \<inter> (\<beta> p2))"

notation AndP (infixr "\<and>p" 180)

definition OrP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 OrP p1 p2 = ((\<alpha> p1) \<union> (\<alpha> p2), (\<beta> p1) \<union> (\<beta> p2))"

notation OrP (infixr "\<or>p" 170)

definition ImpliesP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ImpliesP p1 p2 = (\<not>p p1 \<or>p p2)"

notation ImpliesP (infixr "\<Rightarrow>p" 160)

definition IffP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 IffP p1 p2 = (p1 \<Rightarrow>p p2) \<and>p (p2 \<Rightarrow>p p1)"

notation IffP (infixr "\<Leftrightarrow>p" 150)

subsubsection {* Quantifiers *}

(* An open question is whether there is any benefit in requiring a \<subseteq> (\<alpha> p). *)

definition ExistsResP ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ExistsResP a p = p \<ominus> a"

notation ExistsResP ("(\<exists>-p _ ./ _)" [0, 10] 10)

definition ForallResP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ForallResP a p = \<not>p (\<exists>-p a . \<not>p p)"

notation ForallResP ("(\<forall>-p _ ./ _)" [0, 10] 10)

definition ExistsP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ExistsP a p = (\<exists>-p a . p) \<oplus> a"

notation ExistsP ("(\<exists>p _ ./ _)" [0, 10] 10)

definition ForallP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ForallP a p = (\<forall>-p a . p) \<oplus> a"

notation ForallP ("(\<forall>p _ ./ _)" [0, 10] 10)

subsubsection {* Universal Closure *}

definition ClosureP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ClosureP p = (\<forall>-p (\<alpha> p) . p)"

notation ClosureP ("[_]")

subsubsection {* Refinement *}

definition RefP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 RefP p1 p2 = [p2 \<Rightarrow>p p1]"

notation RefP (infix "\<sqsubseteq>p" 100)

subsection {* Meta-logical Operators *}

definition Tautology ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 Tautology p \<longleftrightarrow> (p = true (\<alpha> p))"

notation Tautology ("taut _" [50] 50)

definition Contradiction ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 Contradiction p \<longleftrightarrow> (p = false (\<alpha> p))"

notation Contradiction ("contra _" [50] 50)

definition Contingency ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 Contingency p \<longleftrightarrow> ((\<not> taut p) \<and> (\<not> contra p))"

notation Contingency ("contg _" [50] 50)

definition Refinement ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<and>
 (\<alpha> p1) = (\<alpha> p2) \<longrightarrow>
 Refinement p1 p2 \<longleftrightarrow> taut (p1 \<sqsubseteq>p p2)"

notation Refinement (infix "\<sqsubseteq>" 50)

text {* \newpage *}

subsection {* Theorems *}

subsubsection {* Alphabet Theorems *}

theorem WF_ALPHABET_empty [simp] :
"{} \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_insert [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (insert x a) \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_union [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<union> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_inter [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<inter> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_diff [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 - a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_alphabet :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<alpha> p) \<in> WF_ALPHABET"
apply (simp add: WF_ALPHA_PREDICATE_def)
done

subsubsection {* Binding Theorems *}

text {* Make the following three theorems default simplifications? Examine! *}

theorem WF_BINDING_exists :
"\<exists> b . b \<in> WF_BINDING"
apply (rule_tac x = "(SOME b . b \<in> WF_BINDING)" in exI)
apply (simp)
done

theorem WF_BINDING_member1 :
"\<lbrakk>bs \<subseteq> WF_BINDING;
 b \<in> bs\<rbrakk> \<Longrightarrow>
 b \<in> WF_BINDING"
apply (auto)
done

theorem WF_BINDING_member2 :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 b \<in> \<beta> p\<rbrakk> \<Longrightarrow>
 b \<in> WF_BINDING"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (auto)
done

theorem WF_BINDING_bindings :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<beta> p \<subseteq> WF_BINDING"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

subsubsection {* Binding Equivalence Theorems *}

theorem  binding_equiv_comm :
"b1 \<cong> b2 on a \<longleftrightarrow> b2 \<cong> b1 on a"
apply (simp add: binding_equiv_def)
apply (auto)
done

theorem  binding_equiv_trans :
"\<lbrakk>b1 \<cong> b2 on a; b2 \<cong> b3 on a\<rbrakk> \<Longrightarrow> b1 \<cong> b3 on a"
apply (simp add: binding_equiv_def)
done

theorem binding_equiv_override :
"b1 \<cong> b2 on a \<Longrightarrow> b1 \<oplus> b2 on a = b1"
apply (simp add: binding_equiv_def)
apply (rule ext)
apply (case_tac "x \<in> a")
apply (auto)
done

subsubsection {* Binding Set Theorems *}

theorem  WF_BINDING_SET_ext :
"bs \<in> WF_BINDING_SET a1 \<Longrightarrow>
 bs \<in> WF_BINDING_SET (a1 \<union> a2)"
apply (simp only: WF_BINDING_SET_def)
apply (safe)
apply (drule_tac x = "b1" in bspec, assumption)
apply (drule_tac x = "b2" in bspec, assumption)
apply (simp only: binding_equiv_def)
apply (auto)
done

theorem WF_BINDING_SET_res :
"bs \<in> WF_BINDING_SET a1 \<Longrightarrow>
 {b2 \<in> WF_BINDING .
   (\<exists> b1 \<in> bs . b1 \<cong> b2 on (a1 - a2))} \<in> WF_BINDING_SET (a1 - a2)"
apply (simp only: WF_BINDING_SET_def)
apply (safe)
apply (rule_tac x = "b1a" in bexI)
apply (auto intro: binding_equiv_trans)
done

theorem WF_BINDING_SET_compl :
"bs \<in> WF_BINDING_SET a \<Longrightarrow>
 (WF_BINDING - bs) \<in> WF_BINDING_SET a"
apply (simp only: WF_BINDING_SET_def)
apply (safe)
apply (drule_tac x = "b2" in bspec, assumption)
apply (drule_tac x = "b1" in bspec, assumption)
apply (simp add: binding_equiv_comm)
done

theorem WF_BINDING_SET_inter :
"bs1 \<in> WF_BINDING_SET a1 \<and>
 bs2 \<in> WF_BINDING_SET a2 \<longrightarrow>
 bs1 \<inter> bs2 \<in> WF_BINDING_SET (a1 \<union> a2)"
apply (simp add: WF_BINDING_SET_def)
apply (clarify)
apply (rule conjI)
apply (auto) [1]
apply (safe)
apply (drule_tac x = "b1" in bspec, assumption)
apply (drule_tac x = "b2" in bspec)
back
apply (assumption)
apply (simp add: binding_equiv_def)
apply (drule_tac x = "b1" in bspec)
back
apply (assumption)
apply (drule_tac x = "b2" in bspec)
back
apply (assumption)
apply (simp add: binding_equiv_def)
done

theorem WF_BINDING_SET_union :
"bs1 \<in> WF_BINDING_SET a1 \<and>
 bs2 \<in> WF_BINDING_SET a2 \<longrightarrow>
 bs1 \<union> bs2 \<in> WF_BINDING_SET (a1 \<union> a2)"
apply (simp add: WF_BINDING_SET_def)
apply (safe)
apply (drule_tac x = "b1" in bspec, assumption)
apply (drule_tac x = "b2" in bspec)
back
apply (assumption)
apply (simp add: binding_equiv_def)
apply (drule_tac x = "b1" in bspec)
back
apply (assumption)
apply (drule_tac x = "b2" in bspec)
back
apply (assumption)
apply (simp add: binding_equiv_def)
done

subsubsection {* Binding Function Theorems *}

theorem WF_BINDING_FUN_override [simp] :
"b1 \<in> WF_BINDING \<and>
 b2 \<in> WF_BINDING \<and>
 f \<in> WF_BINDING_FUN a \<longrightarrow>
 f (b1 \<oplus> b2 on -a) = (f b1)"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: binding_equiv_def)
done

subsubsection {* Closure Theorems *}

theorem Coerce_closure [simp] :
"p \<hookrightarrow> WF_ALPHA_PREDICATE \<in> WF_ALPHA_PREDICATE"
apply (rule_tac Coerce_member)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (rule_tac x = "({}, {})" in exI)
apply (simp add: WF_BINDING_SET_def)
done

theorem LiftP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 LiftP a f \<in> WF_ALPHA_PREDICATE"
apply (simp add: LiftP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (simp add: WF_BINDING_FUN_def)
apply (auto)
done

theorem TrueP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (true a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: TrueP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

theorem FalseP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (false a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: FalseP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

theorem ExtP_closure [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<oplus> a \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExtP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_ext)
done

theorem ResP_closure [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<ominus> a \<in> WF_ALPHA_PREDICATE"
apply (simp add: ResP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_res)
done

theorem NotP_closure [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<not>p p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: NotP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_compl)
done

theorem AndP_closure [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: AndP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_inter)
done

theorem OrP_closure [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: OrP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_union)
done

theorem ImpliesP_closure [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Rightarrow>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: ImpliesP_def)
done

theorem IffP_closure [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Leftrightarrow>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: IffP_def)
done

theorem ExistsResP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>-p a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExistsResP_def)
done

theorem ForallResP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>-p a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ForallResP_def)
done

theorem ExistsP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>p a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExistsP_def)
done

theorem ForallP_closure [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>p a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ForallP_def)
done

theorem ClosureP_closure [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 [p] \<in> WF_ALPHA_PREDICATE"
apply (simp add: ClosureP_def)
apply (subgoal_tac "(\<alpha> p) \<in> WF_ALPHABET")
apply (simp)
apply (simp add: WF_ALPHA_PREDICATE_def)
done

theorem RefP_closure [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<sqsubseteq>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: RefP_def)
done

subsubsection {* Alphabet Theorems *}

theorem LiftP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 \<alpha> (LiftP a (\<lambda> b . f b)) = a"
apply (simp add: LiftP_def)
done

theorem TrueP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (true a) = a"
apply (simp add: TrueP_def)
done

theorem FalseP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (false a) = a"
apply (simp add: FalseP_def)
done

theorem ExtP_alphabet [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (p \<oplus> a) = (\<alpha> p) \<union> a"
apply (simp add: ExtP_def)
done

theorem ResP_alphabet [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (p \<ominus> a) = (\<alpha> p) - a"
apply (simp add: ResP_def)
done

theorem NotP_alphabet [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<not>p p) = (\<alpha> p)"
apply (simp add: NotP_def)
done

theorem AndP_alphabet [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<and>p p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
apply (simp add: AndP_def)
done

theorem OrP_alphabet [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<or>p p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
apply (simp add: OrP_def)
done

theorem ImpliesP_alphabet [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<Rightarrow>p p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
apply (simp add: ImpliesP_def)
done

theorem IffP_alphabet [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<Leftrightarrow>p p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
apply (simp add: IffP_def)
apply (auto)
done

theorem ExistsResP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<exists>-p a . p) = (\<alpha> p) - a"
apply (simp add: ExistsResP_def)
done

theorem ForallResP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<forall>-p a . p) = (\<alpha> p) - a"
apply (simp add: ForallResP_def)
done

theorem ExistsP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<exists>p a . p) = (\<alpha> p) \<union> a"
apply (simp add: ExistsP_def)
done

theorem ForallP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<forall>p a . p) = (\<alpha> p) \<union> a"
apply (simp add: ForallP_def)
done

theorem ClosureP_alphabet [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> ([p]) = {}"
apply (simp add: ClosureP_def)
apply (subgoal_tac "(\<alpha> p) \<in> WF_ALPHABET")
apply (simp)
apply (simp add: WF_ALPHA_PREDICATE_def)
done

theorem RefP_alphabet [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<sqsubseteq>p p2) = {}"
apply (simp add: RefP_def)
done
end
end