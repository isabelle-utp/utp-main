theory utp_gen_pred
imports utp_gen_var utp_alphabet
begin

section {* Generic Predicates *}

subsection {* Type Synonyms *}

types 'TYPE VAR = "NAME \<times> 'TYPE"
types 'VAR ALPHABET = "'VAR set"
types ('VAR, 'VALUE) BINDING = "'VAR \<Rightarrow> 'VALUE"
types ('VAR, 'VALUE) BINDING_SET = "('VAR, 'VALUE) BINDING set"
types ('VAR, 'VALUE) BINDING_FUN = "('VAR, 'VALUE) BINDING \<Rightarrow> bool"
types ('VAR, 'VALUE) ALPHA_PREDICATE =
  "('VAR ALPHABET) \<times> ('VAR, 'VALUE) BINDING_SET"

subsection {* Predicate Locale *}

text {*
  For more flexibility in instantiation which we need when creating the model
  for higher-order predicates the parametrisation of the locale has changes in
  a way that we specify the @{text WF_BINDING} directly rather than the typing
  relation. This allows us to impose additional constraints on bindings, i.e.
  here the consistency of the value procedure variables at different levels.
*}

locale GEN_PRED = VAR "UNIV :: 'TYPE set" +
-- {* We fix the notion of a well-formed binding. *}
  fixes WF_BINDING :: "('TYPE VAR, 'VALUE) BINDING set"
-- {* There must be at least one well-formed binding. *}
  assumes binding_non_empty [simp] : "WF_BINDING \<noteq> {}"
-- {* Well-formed bindings must be closed under overriding. *}
  assumes binding_override [simp, intro!] :
  "b1 \<in> WF_BINDING \<and> b2 \<in> WF_BINDING \<longrightarrow> (b1 \<oplus> b2 on a) \<in> WF_BINDING"
begin

subsection {* Binding Sets *}

text {* Well-formed binding sets are upward-closed w.r.t. an alphabet. *}

definition WF_BINDING_SET ::
  "('TYPE VAR ALPHABET) \<Rightarrow> ('TYPE VAR, 'VALUE) BINDING_SET set" where
"WF_BINDING_SET a \<equiv>
 {bs . bs \<subseteq> WF_BINDING \<and>
   (\<forall> b1 \<in> WF_BINDING . \<forall> b2 \<in> bs . (b1 \<oplus> b2 on a) \<in> bs)}"

subsection {* Predicate Model *}

abbreviation alpha ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR ALPHABET)" ("\<alpha>") where
"\<alpha> p \<equiv> (fst p)"

abbreviation binds ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) BINDING_SET" ("\<beta>") where
"\<beta> p \<equiv> (snd p)"

definition WF_ALPHA_PREDICATE ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE set" where
"WF_ALPHA_PREDICATE \<equiv>
 {p . (\<alpha> p) \<in> WF_ALPHABET \<and> (\<beta> p) \<in> WF_BINDING_SET (\<alpha> p)}"

definition WF_ALPHA_PREDICATE_OVER ::
  "'TYPE VAR ALPHABET \<Rightarrow> ('TYPE VAR, 'VALUE) ALPHA_PREDICATE set" where
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 WF_ALPHA_PREDICATE_OVER a \<equiv> {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p = a}"

subsection {* Predicate Operators *}

subsubsection {* Shallow Lifting *}

text {* We first have to define a notion of binding equivalence. *}

definition BINDING_EQUIV ::
  "('TYPE VAR, 'VALUE) BINDING \<Rightarrow>
   ('TYPE VAR, 'VALUE) BINDING \<Rightarrow>
   ('TYPE VAR ALPHABET) \<Rightarrow> bool" where
"(BINDING_EQUIV b1 b2 a) \<longleftrightarrow>
 b1 \<in> WF_BINDING \<and>
 b2 \<in> WF_BINDING \<and>
 (\<forall> x \<in> a . b1 x = b2 x)"

notation BINDING_EQUIV ("_ \<cong> _ on _")

text {* With it we introduce a notion of well-formed binding function. *}

definition WF_BINDING_FUN ::
  "'TYPE VAR ALPHABET \<Rightarrow> ('TYPE VAR, 'VALUE) BINDING_FUN set" where
"WF_BINDING_FUN a \<equiv> {f . \<forall> b1 b2 . b1 \<cong> b2 on a \<longrightarrow> f b1 = f b2}"

text {* Shallow lifting is only defined for well-formed binding functions. *}

definition LiftP ::
  "('TYPE VAR ALPHABET) \<Rightarrow>
   (('TYPE VAR, 'VALUE) BINDING \<Rightarrow> bool) \<Rightarrow>
    ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 f \<in> WF_BINDING_FUN a \<longrightarrow>
 LiftP a f = (a, {b . b \<in> WF_BINDING \<and> f b})"

subsubsection {* Extension and Restriction *}

definition ExtP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> 'TYPE VAR ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<and>
 a \<in> WF_ALPHABET \<longrightarrow>
 ExtP p a = ((\<alpha> p) \<union> a, \<beta> p)"

notation ExtP (infix "\<oplus>" 200)

definition ResP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> 'TYPE VAR ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<and>
 a \<in> WF_ALPHABET \<longrightarrow>
 ResP p a = ((\<alpha> p) - a,
   {b . \<exists> b1 b2 . b1 \<in> \<beta> p \<and> b2 \<in> WF_BINDING \<and> b = b1 \<oplus> b2 on a})"

notation ResP (infix "\<ominus>" 200)

subsubsection {* Logical Connectives *}

definition TrueP ::
  "'TYPE VAR ALPHABET \<Rightarrow> ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<longrightarrow>
 TrueP a = (a, WF_BINDING)"

notation TrueP ("true")

definition FalseP ::
  "'TYPE VAR ALPHABET \<Rightarrow> ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<longrightarrow>
 FalseP a = (a, {})"

notation FalseP ("false")

definition TRUE :: "('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"TRUE = true {}"

definition FALSE :: "('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"FALSE = false {}"

definition NotP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 NotP p = (\<alpha> p, WF_BINDING - \<beta> p)"

notation NotP ("\<not>p _" [190] 190)

definition AndP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 AndP p1 p2 = ((\<alpha> p1) \<union> (\<alpha> p2), (\<beta> p1) \<inter> (\<beta> p2))"

notation AndP (infixr "\<and>p" 180)

definition OrP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 OrP p1 p2 = ((\<alpha> p1) \<union> (\<alpha> p2), (\<beta> p1) \<union> (\<beta> p2))"

notation OrP (infixr "\<or>p" 170)

definition ImpliesP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ImpliesP p1 p2 = (\<not>p p1 \<or>p p2)"

notation ImpliesP (infixr "\<Rightarrow>p" 160)

definition IffP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 IffP p1 p2 = (p1 \<Rightarrow>p p2) \<and>p (p2 \<Rightarrow>p p1)"

notation IffP (infixr "\<Leftrightarrow>p" 150)

subsubsection {* Quantifiers *}

(* An open question is whether there is benefit in requiring a \<subseteq> (\<alpha> p). *)

definition ExistsP ::
  "('TYPE VAR ALPHABET) \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ExistsP a p = p \<ominus> a"

notation ExistsP ("(\<exists>p _ ./ _)" [0, 10] 10)

definition ForallP ::
  "'TYPE VAR ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ForallP a p = \<not>p (\<exists>p a . \<not>p p)"

notation ForallP ("(\<forall>p _ ./ _)" [0, 10] 10)

definition ExistsExtP ::
  "'TYPE VAR ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ExistsExtP a p = (\<exists>p a . p) \<oplus> a"

notation ExistsExtP ("(\<exists>p+ _ ./ _)" [0, 10] 10)

definition ForallExtP ::
  "'TYPE VAR ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ForallExtP a p = (\<forall>p a . p) \<oplus> a"

notation ForallExtP ("(\<forall>p+ _ ./ _)" [0, 10] 10)

subsubsection {* Universal Closure *}

definition ClosureP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ClosureP p = (\<forall>p (\<alpha> p) . p)"

notation ClosureP ("[_]")

subsubsection {* Refinement *}

definition RefP ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 RefP p1 p2 = [p2 \<Rightarrow>p p1]"

notation RefP (infix "\<sqsubseteq>p" 100)

subsection {* Meta-logical Operators *}

subsubsection {* Tautology *}

definition Tautology ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 Tautology p = (p = true (\<alpha> p))"

notation Tautology ("taut _" [50] 50)

definition Contradiction ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 Contradiction p = (p = false (\<alpha> p))"

notation Contradiction ("contra _" [50] 50)

subsubsection {* Refinement *}

text {* Overloaded version of refinement that yields a HOL predicate. *}

definition Refinement ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow> bool" where
"p1 \<in> WF_ALPHA_PREDICATE \<and>
 p2 \<in> WF_ALPHA_PREDICATE \<and>
 (\<alpha> p1) = (\<alpha> p2) \<longrightarrow>
 Refinement p1 p2 \<longleftrightarrow> taut (p1 \<sqsubseteq>p p2)"

notation Refinement (infix "\<sqsubseteq>" 50)

text {* \newpage *}

subsection {* Theorems *}

subsubsection {* Alphabet Theorems *}

theorem empty_alphabet [simp] :
"{} \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem singleton_alphabet [simp] :
"{v} \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

text {* TODO: Add a general theorem for enumerated (finite) sets. *}

theorem union_alphabet [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<union> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem inter_alphabet [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<inter> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem diff_alphabet [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 - a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem alpha_alphabet :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<alpha> p) \<in> WF_ALPHABET"
apply (simp add: WF_ALPHA_PREDICATE_def)
done

subsubsection {* Binding Theorems *}

theorem exists_binding :
"\<exists> b . b \<in> WF_BINDING"
apply (rule_tac x = "(SOME b . b \<in> WF_BINDING)" in exI)
apply (simp)
done

text {* Not sure whether the following two should be default simplifications. *}

theorem member_subset_binding [simp] :
"\<lbrakk>bs \<subseteq> WF_BINDING;
 b \<in> bs\<rbrakk> \<Longrightarrow>
 b \<in> WF_BINDING"
apply (auto)
done

theorem member_binds_binding [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 b \<in> \<beta> p\<rbrakk> \<Longrightarrow>
 b \<in> WF_BINDING"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (auto)
done

theorem binds_subset_binding :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<beta> p \<subseteq> WF_BINDING"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

subsubsection {* Binding Set Theorems *}

theorem binding_set_ext :
"bs \<in> WF_BINDING_SET a1 \<longrightarrow>
 bs \<in> WF_BINDING_SET (a1 \<union> a2)"
apply (simp add: WF_BINDING_SET_def)
apply (clarify)
apply (drule_tac x = "b1 \<oplus> b2 on a2" in bspec)
apply (simp)
apply (drule_tac x = "b2" in bspec)
apply (assumption)
apply (simp)
apply (subgoal_tac "a2 \<union> a1 = a1 \<union> a2")
apply (auto)
done

theorem binding_set_compl :
"a \<in> WF_ALPHABET \<and>
 bs \<in> WF_BINDING_SET a \<longrightarrow>
 (WF_BINDING - bs) \<in> WF_BINDING_SET a"
apply (simp add: WF_BINDING_SET_def)
apply (clarify)
apply (drule_tac x = "b2" in bspec)
apply (assumption)
apply (drule_tac x = "b1 \<oplus> b2 on a" in bspec)
apply (simp_all)
done

theorem binding_set_union :
"bs1 \<in> WF_BINDING_SET a1 \<and>
 bs2 \<in> WF_BINDING_SET a2 \<longrightarrow>
 bs1 \<union> bs2 \<in> WF_BINDING_SET (a1 \<union> a2)"
apply (simp add: WF_BINDING_SET_def)
apply (safe)
apply (drule_tac x = "b1 \<oplus> b2 on a2" in bspec)
apply (simp)
apply (drule_tac x = "b2" in bspec) back
apply (simp)
apply (simp)
apply (subgoal_tac "a2 \<union> a1 = a1 \<union> a2")
apply (simp)
apply (auto) [1]
apply (rule_tac Q = "b1 \<oplus> b2 on a1 \<union> a2 \<in> bs2" in contrapos_np)
apply (assumption)
apply (drule_tac x = "b1 \<oplus> b2 on a1" in bspec) back
apply (simp)
apply (drule_tac x = "b2" in bspec) back
apply (simp)
apply (simp)
done

theorem binding_set_inter :
"bs1 \<in> WF_BINDING_SET a1 \<and>
 bs2 \<in> WF_BINDING_SET a2 \<longrightarrow>
 bs1 \<inter> bs2 \<in> WF_BINDING_SET (a1 \<union> a2)"
apply (simp add: WF_BINDING_SET_def)
apply (clarify)
apply (rule conjI)
apply (auto) [1]
apply (safe)
apply (drule_tac x = "b1 \<oplus> b2 on a2" in bspec)
apply (simp)
apply (drule_tac x = "b2" in bspec) back
apply (simp)
apply (simp)
apply (subgoal_tac "a2 \<union> a1 = a1 \<union> a2")
apply (simp)
apply (auto) [1]
apply (drule_tac x = "b1 \<oplus> b2 on a1" in bspec) back
apply (simp)
apply (drule_tac x = "b2" in bspec) back
apply (simp)
apply (simp)
done

subsubsection {* Binding Function Theorems *}

theorem binding_fun_app_override [simp] :
"b1 \<in> WF_BINDING \<and>
 b2 \<in> WF_BINDING \<and>
 f \<in> WF_BINDING_FUN a \<longrightarrow>
 f (b1 \<oplus> b2 on -a) = (f b1)"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: BINDING_EQUIV_def)
done

subsubsection {* Closure Theorems *}

theorem Coerce_predicate_wf [simp] :
"p \<hookrightarrow> WF_ALPHA_PREDICATE \<in> WF_ALPHA_PREDICATE"
apply (rule_tac Coerce_member)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (rule_tac x = "({}, {})" in exI)
apply (simp add: WF_BINDING_SET_def)
done

theorem LiftP_wf [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 LiftP a f \<in> WF_ALPHA_PREDICATE"
apply (simp add: LiftP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (safe)
apply (subst override_on_comm)
apply (simp add: binding_fun_app_override)
done

theorem TrueP_wf [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (true a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: TrueP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

theorem FalseP_wf [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (false a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: FalseP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

theorem TRUE_wf [simp] :
"TRUE \<in> WF_ALPHA_PREDICATE"
apply (simp add: TRUE_def)
done

theorem FALSE_wf [simp] :
"FALSE \<in> WF_ALPHA_PREDICATE"
apply (simp add: FALSE_def)
done

theorem ExtP_wf [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<oplus> a \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExtP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: binding_set_ext)
done

theorem ResP_wf [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<ominus> a \<in> WF_ALPHA_PREDICATE"
apply (simp add: ResP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (safe)
apply (simp)
apply (simp add: override_on_cancel3)
apply (rule_tac x = "b1 \<oplus> b1a on (\<alpha> p)" in exI)
apply (simp)
apply (rule_tac x = "b1" in exI)
apply (simp)
apply (simp (no_asm) add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem NotP_wf [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<not>p p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: NotP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: binding_set_compl)
done

theorem AndP_wf [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: AndP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: binding_set_inter)
done

theorem OrP_wf [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: OrP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: binding_set_union)
done

theorem ImpliesP_wf [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Rightarrow>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: ImpliesP_def)
done

theorem IffP_wf [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Leftrightarrow>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: IffP_def)
done

theorem ExistsP_wf [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>p a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExistsP_def)
done

theorem ForallP_wf [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>p a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ForallP_def)
done

theorem ExistsExtP_wf [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>p+ a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExistsExtP_def)
done

theorem ForallExtP_wf [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>p+ a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ForallExtP_def)
done

theorem ClosureP_wf [simp] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 [p] \<in> WF_ALPHA_PREDICATE"
apply (simp add: ClosureP_def)
apply (subgoal_tac "(\<alpha> p) \<in> WF_ALPHABET")
apply (simp)
apply (simp add: WF_ALPHA_PREDICATE_def)
done

theorem RefP_wf [simp] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<sqsubseteq>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: RefP_def)
done

subsubsection {* Alpha Theorems *}

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

theorem TRUE_alphabet [simp] :
"\<alpha> TRUE = {}"
apply (simp add: TRUE_def)
done

theorem FALSE_alphabet [simp] :
"\<alpha> FALSE = {}"
apply (simp add: FALSE_def)
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

theorem ExistsP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<exists>p a . p) = (\<alpha> p) - a"
apply (simp add: ExistsP_def)
done

theorem ForallP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<forall>p a . p) = (\<alpha> p) - a"
apply (simp add: ForallP_def)
done

theorem ExistsExtP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<exists>p+ a . p) = (\<alpha> p) \<union> a"
apply (simp add: ExistsExtP_def)
done

theorem ForallExtP_alphabet [simp] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<forall>p+ a . p) = (\<alpha> p) \<union> a"
apply (simp add: ForallExtP_def)
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