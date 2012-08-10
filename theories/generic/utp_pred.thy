(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
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

subsection {* Unrestricted Variables *}

definition UNREST ::
  "('TYPE VAR) set \<Rightarrow> ('VALUE, 'TYPE) PREDICATE \<Rightarrow> bool" where
"UNREST vs p \<longleftrightarrow> (\<forall> b1 \<in> p . \<forall> b2 \<in> WF_BINDING . b1 \<oplus> b2 on vs \<in> p)"

subsection {* Predicates *}

definition WF_PREDICATE :: "('VALUE, 'TYPE) PREDICATE set" where
"WF_PREDICATE = {b . b \<subseteq> WF_BINDING}"

definition WF_PREDICATE_OVER ::
  "('TYPE VAR) set \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE set" where
"WF_PREDICATE_OVER vs = {p . p \<in> WF_PREDICATE \<and> UNREST (VAR - vs) p}"

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

subsubsection {* @{term UNREST} Theorems *}

theorem UNREST_member [intro] :
"\<lbrakk>p \<in> WF_PREDICATE; b \<in> p; UNREST vs p; b' \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 (b \<oplus> b' on vs) \<in> p"
apply (simp add: UNREST_def)
done

theorem UNREST_empty :
"p \<in> WF_PREDICATE \<Longrightarrow> UNREST {} p"
apply (simp add: UNREST_def)
done

theorem UNREST_subset :
"\<lbrakk>vs2 \<subseteq> vs1;
 p \<in> WF_PREDICATE;
 UNREST vs1 p\<rbrakk> \<Longrightarrow>
 UNREST vs2 p"
apply (simp add: UNREST_def)
apply (clarify)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (drule_tac x = "b2 \<oplus> b1 on (vs1 - vs2)" in bspec)
apply (simp add: closure)
apply (simp)
apply (subgoal_tac "vs1 - (vs1 - vs2) = vs2")
apply (simp)
apply (auto)
done

theorem UNREST_LiftP :
"\<lbrakk>a \<in> WF_ALPHABET;
 f \<in> WF_BINDING_BFUN a\<rbrakk> \<Longrightarrow>
 UNREST (VAR - a) (LiftP f)"
apply (simp add: UNREST_def LiftP_def)
apply (simp add: WF_BINDING_BFUN_def)
apply (safe)
apply (simp add: closure)
apply (drule_tac x = "b1" in spec)
apply (drule_tac x = "b1 \<oplus> b2 on VAR - a" in spec)
apply (simp add: binding_equiv_def)
done

theorem UNREST_TrueP :
"UNREST vs true"
apply (simp add: UNREST_def TrueP_def)
apply (simp add: closure)
done

theorem UNREST_FalseP :
"UNREST vs false"
apply (simp add: UNREST_def FalseP_def)
done

theorem UNREST_NotP :
"\<lbrakk>p \<in> WF_PREDICATE;
 UNREST vs p\<rbrakk> \<Longrightarrow>
 UNREST vs (\<not>p p)"
apply (simp add: UNREST_def NotP_def)
apply (clarify)
apply (simp add: closure)
apply (erule_tac Q = "b1 \<notin> p" in contrapos_pp)
apply (simp)
apply (drule_tac x = "b1 \<oplus> b2 on vs" in bspec)
apply (assumption)
apply (drule_tac x = "b1" in bspec)
apply (assumption)
apply (simp)
done

theorem UNREST_AndP :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<and>p p2)"
apply (simp add: UNREST_def AndP_def)
done

theorem UNREST_OrP :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<or>p p2)"
apply (simp add: UNREST_def OrP_def)
apply (clarify)
apply (drule_tac x = "b1" in bspec)
apply (auto) [1]
apply (drule_tac x = "b2" in bspec) back
apply (assumption)+
done

theorem UNREST_ExistsP :
"\<lbrakk>p \<in> WF_PREDICATE;
 UNREST vs1 p\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<union> vs2) (\<exists>p vs2 . p)"
apply (simp add: UNREST_def ExistsP_def)
apply (clarify)
apply (simp add: override_on_assoc)
apply (subgoal_tac "vs2 \<union> (vs1 \<union> vs2) = (vs1 \<union> vs2)")
apply (simp)
apply (rule_tac x = "b1a \<oplus> b2 on vs1" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
apply (auto)
done

theorem UNREST_ForallP :
"\<lbrakk>p \<in> WF_PREDICATE;
 UNREST vs1 p\<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<union> vs2) (\<forall>p vs2 . p)"
apply (simp add: ForallP_def)
apply (auto intro!: UNREST_ExistsP UNREST_NotP)
done

subsubsection {* Quantifier Normalisation *}

lemma NotP_NotP :
"p \<in> WF_PREDICATE \<Longrightarrow>
 \<not>p \<not>p p = p"
apply (auto simp: NotP_def)
done

theorem ExistsP_empty :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p {} . p) = p"
apply (simp add: ExistsP_def)
apply (auto)
done

theorem ForallP_empty :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<forall>p {} . p) = p"
apply (simp add: ForallP_def)
apply (simp add: ExistsP_empty closure)
apply (simp add: NotP_NotP)
done

theorem ExistsP_single :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p {v} . p) = {b(v := x) | b x . b \<in> p \<and> x : (type v)}"
apply (simp add: ExistsP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "b1" in exI)
apply (rule_tac x = "b2 v" in exI)
apply (simp add: WF_BINDING_def)
apply (simp add: override_on_singleton)
-- {* Subgoal 2 *}
apply (rule_tac x = "b" in exI)
apply (rule_tac x = "b(v := xa)" in exI)
apply (simp add: WF_BINDING_def)
apply (simp add: override_on_singleton)
apply (auto simp add: WF_PREDICATE_def WF_BINDING_def)
done

theorem ExistsP_insert :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p (insert v vs) . p) = (\<exists>p {v} . (\<exists>p vs . p))"
apply (simp add: ExistsP_def [of "(\<exists>p vs . p)"] closure)
apply (simp add: ExistsP_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x = "b1 \<oplus> b2 on vs" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
apply (rule_tac x = "b1" in exI)
apply (rule_tac x = "b2" in exI)
apply (simp)
-- {* Subgoal 2 *}
apply (rule_tac x = "b1a" in exI)
apply (rule_tac x = "b2a \<oplus> b2 on {v}" in exI)
apply (simp)
apply (simp add: override_on_assoc closure)
done

theorem ForallP_insert :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<forall>p (insert v vs) . p) = (\<forall>p {v} . (\<forall>p vs . p))"
apply (simp add: ForallP_def closure)
apply (simp add: NotP_NotP closure)
apply (subst ExistsP_insert)
apply (simp_all add: closure)
done

theorem ExistsP_deatomise :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p (insert x (insert y vs)) . p) =
 (\<exists>p {x} . (\<exists>p (insert y vs) . p))"
apply (auto intro!: ExistsP_insert)
done

theorem ForallP_deatomise :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<forall>p (insert x (insert y vs)) . p) =
 (\<forall>p {x} . (\<forall>p (insert y vs) . p))"
apply (auto intro!: ForallP_insert)
done

theorems QuantP_deatomise =
  ExistsP_deatomise
  ForallP_deatomise

theorem ExistsP_atomise :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p {x} . (\<exists>p (insert y vs) . p)) =
 (\<exists>p (insert x (insert y vs)) . p)"
apply (simp add: ExistsP_deatomise)
done

theorem ForallP_atomise :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<forall>p {x} . (\<forall>p (insert y vs) . p)) =
 (\<forall>p (insert x (insert y vs)) . p)"
apply (simp add: ForallP_deatomise)
done

theorems QuantP_atomise =
  ExistsP_atomise
  ForallP_atomise

subsubsection {* Validation of Soundness *}

theorem TrueP_noteq_FalseP :
"true \<noteq> false"
apply (simp add: TrueP_def FalseP_def)
apply (simp add: WF_BINDING_non_empty)
done

subsection {* Proof Experiments *}

theorem ExistsP_atomise_test :
"p \<in> WF_PREDICATE \<Longrightarrow>
 (\<exists>p {x} . \<exists>p {y} . p) = (\<exists>p {y} . \<exists>p {x} . p)"
apply (simp add: QuantP_atomise)
apply (subgoal_tac "{x, y} = {y, x}")
apply (simp)
apply (auto)
done
end
end