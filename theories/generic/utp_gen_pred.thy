(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_gen_pred.thy                                         *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Generic Predicates *}

theory utp_gen_pred
imports "../utp_types" utp_value2 utp_var utp_alphabet
begin

ML {*
  structure BindingThm =
    Named_Thms (val name = @{binding "binding"} val description = "predicate binding rules");
*}

setup {* BindingThm.setup *}

ML {*
  structure ClosureThm =
    Named_Thms (val name = @{binding "closure"} val description = "predicate closure rules");
*}

setup {* ClosureThm.setup *}

subsection {* Locale @{text "GEN_PRED"} *}

locale GEN_PRED =
  VALUE "type_rel" + VAR "UNIV :: 'TYPE set"
-- {* Typing Relation for Values *}
for type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
begin

subsection {* Bindings *}

text {* We require bindings to be well-typed. *}

definition WF_BINDING :: "('VALUE, 'TYPE) BINDING_SET" where
"WF_BINDING = {b . \<forall> v . (b v) : (type v)}"

text {* Binding equivalence class under an alphabet *}

abbreviation binding_upto :: 
"('VALUE, 'TYPE) BINDING set \<Rightarrow> 'TYPE ALPHABET \<Rightarrow> 
 ('VALUE, 'TYPE) BINDING set" (infix "upto" 100)  where
"bs upto a \<equiv> {b2 \<in> WF_BINDING . (\<exists> b1 \<in> bs . b1 \<cong> b2 on a)}"

text {* Binding Sets *}

text {* Well-formed binding sets are upward-closed with respect to an alphabet. *}

definition WF_BINDING_SET ::
  "('TYPE ALPHABET) \<Rightarrow> ('VALUE, 'TYPE) BINDING_SET set" where
"WF_BINDING_SET a =
 {bs . bs \<subseteq> WF_BINDING \<and>
   (\<forall> b1 \<in> bs . \<forall> b2 \<in> WF_BINDING . b1 \<cong> b2 on a \<longrightarrow> b2 \<in> bs)}"

subsection {* Predicates *}

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

subsection {* Operators *}

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

notation ExtP (infix "\<oplus>p" 200)

definition ResP ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> 'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"p \<in> WF_ALPHA_PREDICATE \<and>
 a \<in> WF_ALPHABET \<longrightarrow>
 ResP p a = ((\<alpha> p) - a, \<beta> p upto ((\<alpha> p) - a))"

notation ResP (infix "\<ominus>p" 200)

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

-- {* Open question: is there any benefit in requiring @{text "a \<subseteq> (\<alpha> p)"}. *}

definition ExistsResP ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ExistsResP a p = p \<ominus>p a"

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
 ExistsP a p = (\<exists>-p a . p) \<oplus>p a"

notation ExistsP ("(\<exists>p _ ./ _)" [0, 10] 10)

definition ForallP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"a \<in> WF_ALPHABET \<and>
 p \<in> WF_ALPHA_PREDICATE \<longrightarrow>
 ForallP a p = (\<forall>-p a . p) \<oplus>p a"

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

notation Contingency ("cont _" [50] 50)

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

(* We add some laws from HOL which are useful for proving alphabet lemmas *)
declare image_Un [alphabet]
declare refl [alphabet]
declare image_set_diff [alphabet]

theorem WF_ALPHABET_alphabet [alpha_closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<alpha> p) \<in> WF_ALPHABET"
  by (simp add: WF_ALPHA_PREDICATE_def)

theorem WF_ALPHA_PREDICATE_subset [intro] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE; a \<subseteq> \<alpha> p\<rbrakk> \<Longrightarrow>
 a \<in> WF_ALPHABET"
  by (auto intro:finite_subset simp add: WF_ALPHA_PREDICATE_def WF_ALPHABET_def)

subsubsection {* Binding Theorems *}

declare beta_equiv_refl [binding]

theorem WF_BINDING_exists[binding] :
"\<exists> b . b \<in> WF_BINDING"
apply (rule_tac x = "(\<lambda> v . SOME x . x : (type v))" in exI)
apply (simp add: WF_BINDING_def)
apply (safe)
apply (rule someI2_ex)
apply (simp only: type_non_empty)
apply (assumption)
done

theorem WF_BINDING_non_empty[binding] :
"WF_BINDING \<noteq> {}"
apply (insert WF_BINDING_exists)
apply (auto)
done

theorem WF_BINDING_override [simp,intro,binding] :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b1 \<oplus> b2 on a \<in> WF_BINDING"
apply (simp add: WF_BINDING_def)
apply (safe)
apply (case_tac "v \<in> a")
apply (auto)
done

text {* The following three theorems have to be reviewd. *}

text {* Can we make use of them as default simplifications? *}

theorem WF_BINDING_predicate[binding] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE; b \<in> \<beta> p\<rbrakk> \<Longrightarrow>
 b \<in> WF_BINDING"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (auto)
done

theorem WF_BINDING_bindings[binding] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<beta> p \<subseteq> WF_BINDING"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

theorem bindings_assign[binding] :
"\<lbrakk> v : type x; b \<in> WF_BINDING \<rbrakk> \<Longrightarrow> b(x:=v) \<in> WF_BINDING"
  by (simp add:WF_BINDING_def)

theorem bindings_assign_type[binding] :
"\<lbrakk> b(x:=v) \<in> WF_BINDING \<rbrakk> \<Longrightarrow> v : type x"
  apply (auto simp add:WF_BINDING_def)
  apply (drule_tac x="x" in spec)
  apply (auto)
done

theorem bindings_override[binding] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 b1 \<in> \<beta> p;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 (b1 \<oplus> b2 on - \<alpha> p) \<in> \<beta> p"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (clarify)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (drule_tac x = "b1 \<oplus> b2 on - \<alpha> p" in bspec)
apply (auto) [1]
apply (auto simp: beta_equiv_def)
done

theorem beta_equiv_bindings :
"\<lbrakk>b1 \<cong> b2 on (\<alpha> p);
 p \<in> WF_ALPHA_PREDICATE;
 b1 \<in> \<beta> p; b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b2 \<in> \<beta> p"
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

text {* Binding Set Theorems *}

theorem  WF_BINDING_SET_ext[binding] :
"bs \<in> WF_BINDING_SET a1 \<Longrightarrow>
 bs \<in> WF_BINDING_SET (a1 \<union> a2)"
apply (simp only: WF_BINDING_SET_def)
apply (safe)
apply (drule_tac x = "b1" in bspec, assumption)
apply (drule_tac x = "b2" in bspec, assumption)
apply (simp only: beta_equiv_def)
apply (auto)
done

theorem WF_BINDING_SET_res[binding] :
"bs \<in> WF_BINDING_SET a1 \<Longrightarrow>
 {b2 \<in> WF_BINDING .
   (\<exists> b1 \<in> bs . b1 \<cong> b2 on (a1 - a2))} \<in> WF_BINDING_SET (a1 - a2)"
apply (simp only: WF_BINDING_SET_def)
apply (safe)
apply (rule_tac x = "b1a" in bexI)
apply (auto intro: beta_equiv_trans)
done

theorem WF_BINDING_SET_compl[binding] :
"bs \<in> WF_BINDING_SET a \<Longrightarrow>
 (WF_BINDING - bs) \<in> WF_BINDING_SET a"
apply (simp only: WF_BINDING_SET_def)
apply (safe)
apply (drule_tac x = "b2" in bspec, assumption)
apply (drule_tac x = "b1" in bspec, assumption)
apply (simp add: beta_equiv_comm)
done

theorem WF_BINDING_SET_inter[binding] :
"\<lbrakk>bs1 \<in> WF_BINDING_SET a1;
 bs2 \<in> WF_BINDING_SET a2\<rbrakk> \<Longrightarrow>
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
apply (simp add: beta_equiv_def)
apply (drule_tac x = "b1" in bspec)
back
apply (assumption)
apply (drule_tac x = "b2" in bspec)
back
apply (assumption)
apply (simp add: beta_equiv_def)
done

theorem WF_BINDING_SET_union[binding] :
"\<lbrakk>bs1 \<in> WF_BINDING_SET a1;
 bs2 \<in> WF_BINDING_SET a2\<rbrakk> \<Longrightarrow>
 bs1 \<union> bs2 \<in> WF_BINDING_SET (a1 \<union> a2)"
apply (simp add: WF_BINDING_SET_def)
apply (safe)
apply (drule_tac x = "b1" in bspec, assumption)
apply (drule_tac x = "b2" in bspec)
back
apply (assumption)
apply (simp add: beta_equiv_def)
apply (drule_tac x = "b1" in bspec)
back
apply (assumption)
apply (drule_tac x = "b2" in bspec)
back
apply (assumption)
apply (simp add: beta_equiv_def)
done

(*
theorem WF_BINDING_SET_assign[binding] :
"\<lbrakk> bs \<in> WF_BINDING_SET a; b \<in> bs; x \<in> a; v \<in> {f x | f. f \<in> bs} \<rbrakk> \<Longrightarrow>
 b(x := v) \<in> bs"
  apply(simp add:WF_BINDING_SET_def)
  apply(clarify)
  apply(auto)
*)

text {* Binding Function Theorems *}

theorem WF_BINDING_FUN_override [simp] :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING;
 f \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 f (b1 \<oplus> b2 on -a) = (f b1)"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: beta_equiv_def)
done

subsubsection {* Closure Theorems *}

theorem WF_ALPHA_PREDICATE_OVER_intro [closure]:
"\<lbrakk> a \<in> WF_ALPHABET; p \<in> WF_ALPHA_PREDICATE; \<alpha> p = a\<rbrakk> \<Longrightarrow> p \<in> WF_ALPHA_PREDICATE_OVER a"
  by (simp add:WF_ALPHA_PREDICATE_OVER_def)

theorem WF_ALPHA_PREDICATE_OVER_dest:
"\<lbrakk> a \<in> WF_ALPHABET; p \<in> WF_ALPHA_PREDICATE_OVER a \<rbrakk> \<Longrightarrow> p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p = a"
  by (simp add:WF_ALPHA_PREDICATE_OVER_def)

theorem Coerce_closure [closure] :
"p \<hookrightarrow> WF_ALPHA_PREDICATE \<in> WF_ALPHA_PREDICATE"
apply (rule_tac Coerce_member)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (rule_tac x = "({}, {})" in exI)
apply (simp add: WF_BINDING_SET_def var alpha_closure)
done

theorem LiftP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 LiftP a f \<in> WF_ALPHA_PREDICATE"
apply (simp add: LiftP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (simp add: WF_BINDING_FUN_def)
apply (auto)
done

theorem TrueP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (true a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: TrueP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

theorem FalseP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (false a) \<in> WF_ALPHA_PREDICATE"
apply (simp add: FalseP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
done

theorem ExtP_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<oplus>p a \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExtP_def binding closure alphabet var)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_ext var alpha_closure)
done

theorem ResP_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 p \<ominus>p a \<in> WF_ALPHA_PREDICATE"
apply (simp add: ResP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (auto intro:alpha_closure simp add: WF_BINDING_SET_res var)
done

theorem NotP_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<not>p p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: NotP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_compl)
done

theorem AndP_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: AndP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (auto intro:alpha_closure simp add: WF_BINDING_SET_inter var)
done

theorem OrP_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: OrP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (auto intro:alpha_closure simp add: WF_BINDING_SET_union var)
done

theorem ImpliesP_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Rightarrow>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: ImpliesP_def closure)
done

theorem IffP_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Leftrightarrow>p p2 \<in> WF_ALPHA_PREDICATE"
apply (simp add: IffP_def closure)
done

theorem ExistsResP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>-p a . p) \<in> WF_ALPHA_PREDICATE"
apply (simp add: ExistsResP_def closure)
done

theorem ForallResP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>-p a . p) \<in> WF_ALPHA_PREDICATE"
apply (auto intro:closure simp add: ForallResP_def)
done

theorem ExistsP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>p a . p) \<in> WF_ALPHA_PREDICATE"
apply (auto intro: closure simp add: ExistsP_def)
done

theorem ForallP_closure [closure] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>p a . p) \<in> WF_ALPHA_PREDICATE"
apply (auto intro:closure simp add: ForallP_def)
done

theorem ClosureP_closure [closure] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 [p] \<in> WF_ALPHA_PREDICATE"
apply (simp add: ClosureP_def)
apply (subgoal_tac "(\<alpha> p) \<in> WF_ALPHABET")
apply(blast intro:closure)
apply (simp add: WF_ALPHA_PREDICATE_def closure)
done

theorem RefP_closure [closure] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<sqsubseteq>p p2 \<in> WF_ALPHA_PREDICATE"
  by (auto intro:closure simp add: RefP_def)

subsubsection {* Predicate Alphabets *}

theorem LiftP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 \<alpha> (LiftP a (\<lambda> b . f b)) = a"
  by (simp add: LiftP_def closure)

theorem TrueP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (true a) = a"
  by (simp add: TrueP_def)


theorem FalseP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (false a) = a"
  by (simp add: FalseP_def)

theorem ExtP_alphabet [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (p \<oplus>p a) = (\<alpha> p) \<union> a"
  by (simp add: ExtP_def)


theorem ResP_alphabet [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 \<alpha> (p \<ominus>p a) = (\<alpha> p) - a"
  by (simp add: ResP_def)

theorem NotP_alphabet [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<not>p p) = (\<alpha> p)"
  by (simp add: NotP_def)

theorem AndP_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<and>p p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
  by (simp add: AndP_def)

theorem OrP_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<or>p p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
  by (simp add: OrP_def)

theorem ImpliesP_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<Rightarrow>p p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
  by (simp add: ImpliesP_def alphabet closure)

theorem IffP_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<Leftrightarrow>p p2) = (\<alpha> p1) \<union> (\<alpha> p2)"
  by (auto simp add: IffP_def closure var alphabet)

theorem ExistsResP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<exists>-p a . p) = (\<alpha> p) - a"
  by (simp add: ExistsResP_def alphabet)

theorem ForallResP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<forall>-p a . p) = (\<alpha> p) - a"
  by (simp add:ForallResP_def alphabet closure)

theorem ExistsP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<exists>p a . p) = (\<alpha> p) \<union> a"
  by (simp add: ExistsP_def closure alphabet)

theorem ForallP_alphabet [alphabet] :
"\<lbrakk>a \<in> WF_ALPHABET;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (\<forall>p a . p) = (\<alpha> p) \<union> a"
  by (simp add: ForallP_def closure alphabet)

theorem ClosureP_alphabet [alphabet] :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> ([p]) = {}"
apply (simp add: ClosureP_def)
apply (subgoal_tac "(\<alpha> p) \<in> WF_ALPHABET")
apply (simp add:closure alphabet)
apply (simp add: WF_ALPHA_PREDICATE_def)
done

theorem RefP_alphabet [alphabet] :
"\<lbrakk>p1 \<in> WF_ALPHA_PREDICATE;
 p2 \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<sqsubseteq>p p2) = {}"
apply (simp add: RefP_def closure alphabet)
done

subsubsection {* Soundness Checks *}

theorem TrueP_noteq_FalseP [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow> TrueP a \<noteq> FalseP a"
apply (simp add: TrueP_def FalseP_def)
apply (simp add: WF_BINDING_non_empty)
done

abbreviation "pred_partial_order a \<equiv>
 \<lparr> partial_object.carrier = WF_ALPHA_PREDICATE_OVER a,
   eq = (\<lambda> x y. x = y), 
   le = (\<lambda> x y. x \<sqsubseteq> y) \<rparr>"
end
end
