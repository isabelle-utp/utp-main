(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Predicates *}

theory utp_pred
imports utp_types utp_value utp_var
begin

subsection {* Locale @{text "PRED"} *}

locale PRED =
  VALUE "type_rel" + VAR "UNIV :: 'TYPE set"
-- {* Typing Relation for Values *}
for type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
begin

subsection {* Bindings *}

text {* We require bindings to be well-typed. *}

definition WF_BINDING :: "('VALUE, 'TYPE) BINDING_SET" where
"WF_BINDING = {b . \<forall> v . (b v) : (type v)}"

text {* Binding Equivalence *}

definition binding_equiv ::
  "('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('TYPE VAR set) \<Rightarrow> bool" where
"(binding_equiv b1 b2 a) \<longleftrightarrow> (\<forall> x \<in> a . b1 x = b2 x)"

notation binding_equiv ("_ \<cong> _ on _")

text {* Binding Functions *}

definition WF_BINDING_BFUN ::
  "'TYPE ALPHABET \<Rightarrow> ('VALUE, 'TYPE) BINDING_BFUN set" where
"WF_BINDING_BFUN vs = {f . \<forall> b1 b2 . b1 \<cong> b2 on vs \<longrightarrow> f b1 = f b2}"

subsection {* Predicates *}

definition WF_PREDICATE :: "('VALUE, 'TYPE) PREDICATE set" where
"WF_PREDICATE = {b . b \<subseteq> WF_BINDING}"

subsection {* Functions *}

definition WF_FUNCTION ::
  "(('VALUE, 'TYPE) PREDICATE \<Rightarrow>
    ('VALUE, 'TYPE) PREDICATE) set" where
"WF_FUNCTION = {f . \<forall> p \<in> WF_PREDICATE . f p \<in> WF_PREDICATE}"

subsection {* Operators *}

subsubsection {* Shallow Lifting *}

definition LiftP ::
  "('VALUE, 'TYPE) BINDING_BFUN \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"LiftP f = {b \<in> WF_BINDING . f b}"

subsubsection {* True and False *}

definition TrueP :: "('VALUE, 'TYPE) PREDICATE" where
"TrueP = WF_BINDING"

notation TrueP ("true")

definition FalseP :: "('VALUE, 'TYPE) PREDICATE" where
"FalseP = {}"

notation FalseP ("false")

subsubsection {* Logical Connectives *}

definition NotP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"NotP p = WF_BINDING - p"

notation NotP ("\<not>p _" [190] 190)

definition AndP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 AndP p1 p2 = p1 \<inter> p2"

notation AndP (infixr "\<and>p" 180)

definition OrP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 OrP p1 p2 = p1 \<union> p2"

notation OrP (infixr "\<or>p" 170)

definition ImpliesP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 ImpliesP p1 p2 = (\<not>p p1 \<or>p p2)"

notation ImpliesP (infixr "\<Rightarrow>p" 160)

definition IffP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 IffP p1 p2 = (p1 \<Rightarrow>p p2) \<and>p (p2 \<Rightarrow>p p1)"

notation IffP (infixr "\<Leftrightarrow>p" 150)

subsubsection {* Quantifiers *}

definition ExistsP ::
  "('TYPE VAR set) \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p \<in> WF_PREDICATE \<longrightarrow>
 ExistsP vs p = {b1 \<oplus> b2 on vs | b1 b2 . b1 \<in> p \<and> b2 \<in> WF_BINDING}"

notation ExistsP ("(\<exists>p _ ./ _)" [0, 10] 10)

definition ForallP ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p \<in> WF_PREDICATE \<longrightarrow>
 ForallP vs p = \<not>p (\<exists>p vs . \<not>p p)"

notation ForallP ("(\<forall>p _ ./ _)" [0, 10] 10)

subsubsection {* Universal Closure *}

definition ClosureP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p \<in> WF_PREDICATE \<longrightarrow>
 ClosureP p = (\<forall>p VAR . p)"

notation ClosureP ("[_]p")

subsubsection {* Refinement *}

definition RefP ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 RefP p1 p2 = [p2 \<Rightarrow>p p1]p"

notation RefP (infix "\<sqsubseteq>p" 100)

subsection {* Meta-logical Operators *}

subsubsection {* Tautologies *}

definition Tautology ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow> bool" where
"p \<in> WF_PREDICATE \<longrightarrow>
 Tautology p \<longleftrightarrow> [p]p = true"

notation Tautology ("taut _" [50] 50)

definition Contradiction ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow> bool" where
"p \<in> WF_PREDICATE \<longrightarrow>
 Contradiction p \<longleftrightarrow> [p]p = false"

notation Contradiction ("contra _" [50] 50)

subsubsection {* Refinement *}

definition Refinement ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow> bool" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 Refinement p1 p2 \<longleftrightarrow> taut (p1 \<sqsubseteq>p p2)"

notation Refinement (infix "\<sqsubseteq>" 50)

subsection {* Theorems *}

subsubsection {* Binding Theorems *}

theorem WF_BINDING_exists :
"\<exists> b . b \<in> WF_BINDING"
apply (rule_tac x = "(\<lambda> v . SOME x . x : (type v))" in exI)
apply (simp add: WF_BINDING_def)
apply (safe)
apply (rule someI2_ex)
apply (simp only: type_non_empty)
apply (assumption)
done

theorem WF_BINDING_non_empty :
"WF_BINDING \<noteq> {}"
apply (insert WF_BINDING_exists)
apply (auto)
done

theorem WF_BINDING_app_type [intro] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (b v) : (type v)"
apply (simp add: WF_BINDING_def)
done

theorem WF_BINDING_app_carrier [intro] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (b v) \<in> carrier (type v)"
apply (simp add: WF_BINDING_app_type carrier_def)
done

theorem WF_BINDING_update1 [closure, intro] :
"\<lbrakk>b \<in> WF_BINDING; x : (type v)\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: WF_BINDING_def)
done

theorem WF_BINDING_update2 [closure, intro] :
"\<lbrakk>b \<in> WF_BINDING; x \<in> carrier (type v)\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: carrier_def closure)
done

theorem WF_BINDING_override [closure, intro] :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b1 \<oplus> b2 on vs \<in> WF_BINDING"
apply (simp add: WF_BINDING_def)
apply (safe)
apply (case_tac "v \<in> vs")
apply (auto)
done

theorem WF_BINDING_member [simp, intro] :
"\<lbrakk>b \<in> p;
 p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 b \<in> WF_BINDING"
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem WF_BINDING_override_on_VAR [simp] :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b1 \<oplus> b2 on VAR = b2"
apply (simp add: VAR_def)
apply (auto)
done

subsubsection {* Closure Theorems *}

theorem LiftP_closure [closure] :
"LiftP f \<in> WF_PREDICATE"
apply (simp add: LiftP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem TrueP_closure [closure] :
"true \<in> WF_PREDICATE"
apply (simp add: TrueP_def)
apply (simp add: WF_PREDICATE_def)
done

theorem FalseP_closure [closure] :
"false \<in> WF_PREDICATE"
apply (simp add: FalseP_def)
apply (simp add: WF_PREDICATE_def)
done

theorem NotP_closure [closure, intro!] :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<not>p p) \<in> WF_PREDICATE"
apply (simp add: NotP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem AndP_closure [closure, intro!] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<and>p p2 \<in> WF_PREDICATE"
apply (simp add: AndP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem OrP_closure [closure, intro!] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<or>p p2 \<in> WF_PREDICATE"
apply (simp add: OrP_def)
apply (simp add: WF_PREDICATE_def)
done

theorem ImpliesP_closure [closure, intro!] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Rightarrow>p p2 \<in> WF_PREDICATE"
apply (simp add: ImpliesP_def)
apply (auto)
done

theorem IffP_closure [closure, intro!] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Leftrightarrow>p p2 \<in> WF_PREDICATE"
apply (simp add: IffP_def)
apply (auto)
done

theorem ExistsP_closure [closure, intro!] :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>p vs . p) \<in> WF_PREDICATE"
apply (simp add: ExistsP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem ForallP_closure [closure, intro!] :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>p vs . p) \<in> WF_PREDICATE"
apply (simp add: ForallP_def)
apply (auto)
done

theorem ClosureP_closure [closure, intro!] :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 [p]p \<in> WF_PREDICATE"
apply (simp add: ClosureP_def)
apply (auto)
done

theorem RefP_closure [closure, intro!] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<sqsubseteq>p p2 \<in> WF_PREDICATE"
apply (simp add: RefP_def)
apply (auto)
done

subsubsection {* Validation of Soundness *}

theorem TrueP_noteq_FalseP :
"true \<noteq> false"
apply (simp add: TrueP_def FalseP_def)
apply (simp add: WF_BINDING_non_empty)
done
end
end
