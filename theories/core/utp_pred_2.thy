(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_pred.thy                                                         *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Predicates *}

theory utp_pred_2
imports utp_synonyms utp_value_2 utp_sorts_2 utp_var_2
begin

subsection {* Value Compatibility *}

(* Can the given value be placed into the given variable? *)
definition var_compat :: "'VALUE \<Rightarrow> 'VALUE VAR \<Rightarrow> bool" (infix "\<rhd>" 50) where
"v \<rhd> x \<equiv> v : type x \<and> (control x \<longrightarrow> \<D> v)"

lemma var_compat_intros [simp,intro]:
  "\<lbrakk> v : type x; \<D> v \<rbrakk> \<Longrightarrow> v \<rhd> x"
  "\<lbrakk> v : type x; \<not> control x \<rbrakk> \<Longrightarrow> v \<rhd> x"
  by (simp_all add:var_compat_def)

lemma var_compat_cases [elim]:
  "\<lbrakk> v \<rhd> x; \<lbrakk> v : type x; \<D> v \<rbrakk> \<Longrightarrow> P
          ; \<lbrakk> v : type x; \<not> control x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:var_compat_def)

subsection {* Bindings *}

text {* We require bindings to be well-typed. *}

definition "WF_BINDING \<equiv> {b . \<forall> v. b v \<rhd> v}"

subsubsection {* Binding Theorems *}

theorem WF_BINDING_exists :
"\<exists> b . b \<in> WF_BINDING"
apply (rule_tac x = "(\<lambda> v . SOME x . x : (type v) \<and> \<D> x)" in exI)
apply (auto simp add: WF_BINDING_def)
apply (rule someI2_ex)
apply (rule type_non_empty_elim)
apply (auto)
done

(* Some attempt to convert the above proof into ISAR. *)

(*
theorem WF_BINDING_exists :
"\<exists> b . b \<in> WF_BINDING"
apply (rule_tac x = "(\<lambda> v . SOME x . x : (type v))" in exI)
apply (simp add: WF_BINDING_def)
apply (safe)
apply (rule someI2_ex)
proof -
  fix v
  have lemma1 : "\<exists>a. a : type v"
    apply (simp only: type_non_empty)
  done
  then show ?thesis using lemma1
qed
*)



subsubsection {* Binding theorems *}

theorem WF_BINDING_non_empty :
"WF_BINDING \<noteq> {}"
apply (insert WF_BINDING_exists)
apply (auto)
done

theorem WF_BINDING_app_compat [intro] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (b v) \<rhd> v"
  apply (simp add: WF_BINDING_def)
done

theorem WF_BINDING_app_type [intro] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (b v) : (type v)"
apply (auto simp add: WF_BINDING_def)
done

theorem WF_BINDING_app_carrier [intro] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (b v) \<in> carrier (type v)"
apply (simp add: WF_BINDING_app_type carrier_def)
done

theorem WF_BINDING_update1 [closure] :
"\<lbrakk>b \<in> WF_BINDING; x \<rhd> v\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: WF_BINDING_def)
done

theorem WF_BINDING_update2 [closure] :
"\<lbrakk>b \<in> WF_BINDING; x \<in> carrier (type v); \<not> control v\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: carrier_def closure)
done

theorem WF_BINDING_update2_control [closure] :
"\<lbrakk>b \<in> WF_BINDING; x \<in> carrier (type v); control v; \<D> x\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: carrier_def closure)
done

theorem WF_BINDING_override [closure] :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b1 \<oplus> b2 on vs \<in> WF_BINDING"
apply (simp add: WF_BINDING_def)
apply (safe)
apply (case_tac "v \<in> vs")
apply (auto simp add:override_on_def)
done

theorem WF_BINDING_control_defined [defined]:
"\<lbrakk> b \<in> WF_BINDING; control v \<rbrakk> \<Longrightarrow> \<D> (b v)"
  by (auto simp add:WF_BINDING_def)

typedef (open) 'VALUE WF_BINDING = "WF_BINDING :: 'VALUE BINDING set"
  by (simp add: WF_BINDING_exists)

declare Rep_WF_BINDING [simp]
declare Rep_WF_BINDING_inverse [simp]
declare Abs_WF_BINDING_inverse [simp]

lemma Rep_WF_BINDING_intro [intro]:
  "Rep_WF_BINDING x = Rep_WF_BINDING y \<Longrightarrow> x = y"
  by (simp add:Rep_WF_BINDING_inject)

lemma Rep_WF_BINDING_elim [elim]:
  "\<lbrakk> x = y; Rep_WF_BINDING x = Rep_WF_BINDING y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

notation Rep_WF_BINDING ("\<langle>_\<rangle>\<^sub>b")

text {* Binding Equivalence *}

definition binding_equiv ::
  "'VALUE WF_BINDING \<Rightarrow>
   'VALUE WF_BINDING \<Rightarrow>
   ('VALUE VAR set) \<Rightarrow> bool" where
"(binding_equiv b1 b2 a) \<longleftrightarrow> (\<forall> x \<in> a . \<langle>b1\<rangle>\<^sub>bx = \<langle>b2\<rangle>\<^sub>bx)"

notation binding_equiv ("_ \<cong> _ on _")

setup_lifting type_definition_WF_BINDING

lift_definition binding_override_on ::
  "'VALUE WF_BINDING \<Rightarrow>
   'VALUE WF_BINDING \<Rightarrow>
   'VALUE VAR set \<Rightarrow>
   'VALUE WF_BINDING" ("_ \<oplus>\<^sub>b _ on _" [56, 56, 0] 55) is "override_on"
  apply (simp add: WF_BINDING_def)
  apply (safe)
  apply (case_tac "v \<in> set")
  apply (auto)
done

declare binding_override_on.rep_eq [simp]

definition binding_upd :: 
  "'VALUE WF_BINDING \<Rightarrow>
   'VALUE VAR \<Rightarrow>
   'VALUE \<Rightarrow>
   'VALUE WF_BINDING" where
"binding_upd b x v = Abs_WF_BINDING (fun_upd \<langle>b\<rangle>\<^sub>b x v)"

nonterminal bupdbinds and bupdbind

syntax
  "_bupdbind" :: "['a, 'a] => bupdbind"               ("(2_ :=\<^sub>b/ _)")
  ""         :: "bupdbind => bupdbinds"               ("_")
  "_bupdbinds":: "[bupdbind, bupdbinds] => bupdbinds" ("_,/ _")
  "_BUpdate"  :: "['a, bupdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

translations
  "_BUpdate f (_bupdbinds b bs)" == "_BUpdate (_BUpdate f b) bs"
  "f(x:=\<^sub>by)" == "CONST binding_upd f x y"

lemma binding_type [simp, typing, intro]: "t = type x \<Longrightarrow> \<langle>b\<rangle>\<^sub>bx : t"
  apply (insert Rep_WF_BINDING[of b])
  apply (auto simp add:WF_BINDING_def)
done

lemma binding_compat [simp, intro]: "\<langle>b\<rangle>\<^sub>bx \<rhd> x"
  by auto

lemma binding_value_alt [simp, intro]: 
  "\<lbrakk> type x = type x'; control x = control x' \<rbrakk> \<Longrightarrow> \<langle>b\<rangle>\<^sub>bx \<rhd> x'"
  by (auto simp add:var_compat_def intro: defined)

lemma Rep_WF_BINDING_rep_eq [simp]:
  "\<lbrakk> v \<rhd> x \<rbrakk> \<Longrightarrow> \<langle>binding_upd b x v\<rangle>\<^sub>b = fun_upd \<langle>b\<rangle>\<^sub>b x v"
  apply (simp add:var_compat_def)
  apply (subgoal_tac "\<langle>b\<rangle>\<^sub>b(x := v) \<in> WF_BINDING")
  apply (simp_all add: binding_upd_def WF_BINDING_def)
  apply (auto intro:defined closure)
done

lemma binding_eq_iff: "f = g = (\<forall>x. \<langle>f\<rangle>\<^sub>b x = \<langle>g\<rangle>\<^sub>b x)"
  by (auto)

lemma binding_upd_idem_iff: "y \<rhd> x \<Longrightarrow> (f(x:=\<^sub>by) = f) = (\<langle>f\<rangle>\<^sub>b x = y)"
  by (force simp add: fun_upd_idem_iff var_compat_def)

lemma binding_upd_idem: "\<lbrakk> y \<rhd> x \<rbrakk> \<Longrightarrow> \<langle>f\<rangle>\<^sub>b x = y ==> f(x:=\<^sub>by) = f"
  by (simp add: binding_upd_idem_iff)

lemma binding_upd_triv [iff]: "f(x :=\<^sub>b \<langle>f\<rangle>\<^sub>b x) = f"
  by (simp add: binding_upd_idem)

lemma binding_upd_apply [simp]: "y \<rhd> x \<Longrightarrow> \<langle>f(x:=\<^sub>by)\<rangle>\<^sub>b z = (if z=x then y else \<langle>f\<rangle>\<^sub>b z)"
  by (simp)

lemma binding_upd_upd [simp]: 
  "\<lbrakk> y \<rhd> x; z \<rhd> x \<rbrakk> \<Longrightarrow> f(x:=\<^sub>by,x:=\<^sub>bz) = f(x:=\<^sub>bz)"
  by (simp add: binding_eq_iff)

lemma binding_upd_twist: 
  "\<lbrakk> b \<rhd> a; d \<rhd> c; a ~= c \<rbrakk> \<Longrightarrow> (m(a:=\<^sub>bb))(c:=\<^sub>bd) = (m(c:=\<^sub>bd))(a:=\<^sub>bb)"
  by (force)

theorem binding_override_on_eq :
"f1 \<oplus>\<^sub>b g1 on a = f2 \<oplus>\<^sub>b g2 on a \<longleftrightarrow>
 (\<forall> x . x \<in> a \<longrightarrow> \<langle>g1\<rangle>\<^sub>bx = \<langle>g2\<rangle>\<^sub>bx) \<and>
 (\<forall> x . x \<notin> a \<longrightarrow> \<langle>f1\<rangle>\<^sub>bx = \<langle>f2\<rangle>\<^sub>bx)"
  by (simp add:binding_override_on_def Abs_WF_BINDING_inject closure override_on_eq)

(* Transfer override theorems *)
lemma binding_override_simps [simp]:
  "(f \<oplus>\<^sub>b g on vs1) \<oplus>\<^sub>b g on vs2 = f \<oplus>\<^sub>b g on (vs1 \<union> vs2)"
  "f \<oplus>\<^sub>b f on vs = f"
  "(f \<oplus>\<^sub>b g on vs) \<oplus>\<^sub>b h on vs = f \<oplus>\<^sub>b h on vs"
  "f \<oplus>\<^sub>b (g \<oplus>\<^sub>b h on a) on a = f \<oplus>\<^sub>b h on a"
  "f \<oplus>\<^sub>b (g \<oplus>\<^sub>b f on b) on a = f \<oplus>\<^sub>b g on a - b"
  "f \<oplus>\<^sub>b (f \<oplus>\<^sub>b g on a) on b = f \<oplus>\<^sub>b g on a \<inter> b"
  "f \<oplus>\<^sub>b g on (insert x xs) = f(x :=\<^sub>b \<langle>g\<rangle>\<^sub>bx) \<oplus>\<^sub>b g on xs - {x}"
  "v \<rhd> x \<Longrightarrow> (f \<oplus>\<^sub>b g on a)(x :=\<^sub>b v) = f(x :=\<^sub>b v) \<oplus>\<^sub>b g on (a - {x})"
  "x \<in> vs2 \<Longrightarrow> \<langle>f \<oplus>\<^sub>b g on vs1 - vs2\<rangle>\<^sub>bx = \<langle>f\<rangle>\<^sub>bx"
  "f \<oplus>\<^sub>b g on VAR = g"
  "f \<oplus>\<^sub>b g on {} = f"
  apply (auto simp add:override_on_assoc override_on_singleton override_on_chain)
  apply (auto intro!: Rep_WF_BINDING_intro)
  apply (metis Un_empty_left Un_insert_left insert_Diff_single override_on_chain override_on_singleton)
done

lemma binding_override_singleton:
  "(f \<oplus>\<^sub>b g on {x}) = f(x :=\<^sub>b \<langle>g\<rangle>\<^sub>bx)"
  by (auto)

lemma binding_override_assoc:
  "(f \<oplus>\<^sub>b g on a) \<oplus>\<^sub>b h on b = f \<oplus>\<^sub>b (g \<oplus>\<^sub>b h on b) on (a \<union> b)"
  by (auto simp add:override_on_assoc)

lemma binding_override_subset: 
"\<lbrakk> f = f \<oplus>\<^sub>b g on vs1; vs2 \<subseteq> vs1 \<rbrakk> \<Longrightarrow> f = f \<oplus>\<^sub>b g on vs2"
  by (force simp add:override_on_subset)

lemma binding_override_reorder:
"\<lbrakk> a \<inter> b = {} \<rbrakk> \<Longrightarrow>
 (f \<oplus>\<^sub>b g on a) \<oplus>\<^sub>b h on b = (f \<oplus>\<^sub>b h on b) \<oplus>\<^sub>b g on a"
  apply (rule Rep_WF_BINDING_intro)
  apply (simp)
  apply (drule_tac f="\<langle>f\<rangle>\<^sub>b" and g="\<langle>g\<rangle>\<^sub>b" and h="\<langle>h\<rangle>\<^sub>b" in override_on_reorder)
  apply (simp)
done

lemma binding_override_equiv [simp]:
  "b1 \<cong> b2 on vs \<Longrightarrow> b1 \<oplus>\<^sub>b b2 on vs = b1"
  by (force simp add:override_on_def binding_equiv_def)

lemma binding_override_upd [simp]:
  "\<lbrakk> x \<in> vs; v \<rhd> x \<rbrakk> \<Longrightarrow> b1 \<oplus>\<^sub>b b2(x :=\<^sub>b v) on vs = b1(x :=\<^sub>b v) \<oplus>\<^sub>b b2 on (vs - {x})"
  by (force simp add:override_on_def)

lemma binding_upd_simps [simp]:
  "\<lbrakk> v1 \<rhd> x; v2 \<rhd> x \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v1, x :=\<^sub>b v2) = b(x :=\<^sub>b v2)"
  "b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x) = b"
  by (auto)

text {* Binding Predicates *}

type_synonym 'VALUE WF_BINDING_PRED = "'VALUE WF_BINDING \<Rightarrow> bool"
type_synonym 'VALUE WF_BINDING_FUN = "'VALUE WF_BINDING \<Rightarrow> 'VALUE"

definition WF_BINDING_PRED ::
  "'VALUE VAR set \<Rightarrow> 'VALUE WF_BINDING_PRED set" where
"WF_BINDING_PRED vs = {f . \<forall> b1 b2 . b1 \<cong> b2 on vs \<longrightarrow> f b1 = f b2}"

subsection {* Predicates *}

definition WF_PREDICATE :: "'VALUE PREDICATE set" where
"WF_PREDICATE = Pow WF_BINDING"

typedef (open) 'VALUE WF_PREDICATE = "UNIV :: 'VALUE WF_BINDING set set"
morphisms destPRED mkPRED
  by (auto)

print_theorems


declare destPRED [simp]
declare destPRED_inverse [simp]
declare mkPRED_inverse [simp]

lemma destPRED_intro [intro!]:
  "destPRED x = destPRED y \<Longrightarrow> x = y"
  by (simp add:destPRED_inject)

lemma destPRED_elim [elim]:
  "\<lbrakk> x = y; destPRED x = destPRED y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_WF_PREDICATE

(*
type_synonym 'VALUE WF_PREDICATE = "'VALUE WF_BINDING set"
*)

subsection {* Functions *}

type_synonym 'VALUE WF_FUNCTION = "'VALUE WF_PREDICATE \<Rightarrow> 'VALUE WF_PREDICATE"
(*
definition WF_FUNCTION ::
  "('VALUE WF_PRED \<Rightarrow>
    'VALUE WF_PRED) set" where
"WF_FUNCTION = {f . \<forall> p \<in> WF_PREDICATE . f p \<in> WF_PREDICATE}"
*)

subsection {* Operators *}

subsubsection {* Shallow Lifting *}

lift_definition LiftP ::
  "('VALUE WF_BINDING \<Rightarrow> bool) \<Rightarrow>
   'VALUE WF_PREDICATE" is 
  "Collect :: ('VALUE WF_BINDING \<Rightarrow> bool) \<Rightarrow> 'VALUE WF_BINDING set" done

subsubsection {* Equality *}

definition EqualsP ::
  "'VALUE VAR \<Rightarrow> 'VALUE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"EqualsP v x = LiftP (\<lambda> b . \<langle>b\<rangle>\<^sub>bv = x)"

notation EqualsP (infix "=p" 210)

subsubsection {* True and False *}

lift_definition TrueP :: "'VALUE WF_PREDICATE" 
  is "UNIV :: 'VALUE WF_BINDING set" done

notation TrueP ("true")

lift_definition FalseP :: "'VALUE WF_PREDICATE" 
is "{} :: 'VALUE WF_BINDING set" done

notation FalseP ("false")

subsubsection {* Logical Connectives *}

lift_definition NotP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" 
is "uminus" done

notation NotP ("\<not>p _" [190] 190)

lift_definition AndP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" 
is "op \<inter> :: 'VALUE WF_BINDING set \<Rightarrow> 'VALUE WF_BINDING set \<Rightarrow> 'VALUE WF_BINDING set"
done

notation AndP (infixr "\<and>p" 180)

lift_definition OrP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" 
is "op \<union> :: 'VALUE WF_BINDING set \<Rightarrow> 'VALUE WF_BINDING set \<Rightarrow> 'VALUE WF_BINDING set"
done

notation OrP (infixr "\<or>p" 170)

definition ImpliesP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"ImpliesP p1 p2 = \<not>p p1 \<or>p p2"

notation ImpliesP (infixr "\<Rightarrow>p" 160)

definition IffP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"IffP p1 p2 \<equiv> (p1 \<Rightarrow>p p2) \<and>p (p2 \<Rightarrow>p p1)"

notation IffP (infixr "\<Leftrightarrow>p" 150)

subsubsection {* Quantifiers *}

lift_definition ExistsP ::
  "('VALUE VAR set) \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" is
"\<lambda> vs p. {b1 \<oplus>\<^sub>b b2 on vs | b1 b2. b1 \<in> p}"
done

notation ExistsP ("(\<exists>p _ ./ _)" [0, 10] 10)

definition ForallP ::
  "'VALUE VAR set \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"ForallP vs p = \<not>p (\<exists>p vs . \<not>p p)"

notation ForallP ("(\<forall>p _ ./ _)" [0, 10] 10)

subsubsection {* Universal Closure *}

definition ClosureP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"ClosureP p = (\<forall>p VAR . p)"

notation ClosureP ("[_]p")

subsubsection {* Refinement *}

definition RefP ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"RefP p1 p2 = [p2 \<Rightarrow>p p1]p"

notation RefP (infix "\<sqsubseteq>p" 100)

subsection {* Meta-logical Operators *}

subsubsection {* Tautologies *}

definition Tautology ::
  "'VALUE WF_PREDICATE \<Rightarrow> bool" where
"Tautology p \<longleftrightarrow> [p]p = true"

notation Tautology ("taut _" [50] 50)

definition Contradiction ::
  "'VALUE WF_PREDICATE \<Rightarrow> bool" where
"Contradiction p \<longleftrightarrow> [p]p = false"

notation Contradiction ("contra _" [50] 50)

definition Contingency ::
  "'VALUE WF_PREDICATE \<Rightarrow> bool" where
"Contingency p \<longleftrightarrow> (\<not> taut p) \<and> (\<not> contra p)"

notation Contingency ("contg _" [50] 50)

subsubsection {* Refinement *}

(*
definition Refinement ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow> bool" where
"Refinement p1 p2 \<longleftrightarrow> taut (p1 \<sqsubseteq>p p2)"
*)

instantiation WF_PREDICATE :: (VALUE) ord
begin

definition less_eq_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> bool" where
"less_eq_WF_PREDICATE p1 p2 \<longleftrightarrow> taut (p1 \<sqsubseteq>p p2)"

definition less_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> bool" where
"less_WF_PREDICATE p1 p2 \<longleftrightarrow> taut (p1 \<sqsubseteq>p p2) \<and> \<not> taut (p2 \<sqsubseteq>p p1)"

instance ..

end

notation less_eq (infix "\<sqsubseteq>" 50)

subsection {* Theorems *}


(*
theorem WF_BINDING_member [simp, intro] :
"\<lbrakk>b \<in> p :: 'VALUE WF_PREDICATE;
 p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 b \<in> WF_BINDING"
w'VALUE WF_PREDICATE
apply (simp add: WF_PREDICATE_def)
apply (auto)
done
*)

theorem WF_BINDING_override_on_VAR [simp] :
"\<lbrakk>b1 \<in> WF_BINDING;
 b2 \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 b1 \<oplus> b2 on VAR = b2"
  by (auto)

subsubsection {* Closure Theorems *}

(*
(*
theorem LiftP_closure [closure] :
"LiftP f \<in> WF_PREDICATE"
apply (simp add: LiftP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem EqualsP_closure [closure] :
"v =p x \<in> WF_PREDICATE"
apply (simp add: EqualsP_def)
apply (auto simp: closure)
done
*)

theorem TrueP_closure [closure] :
"true \<in> Pow (Abs_WF_BINDING ` WF_BINDING)"
  apply (simp)
  apply (auto simp add: TrueP_def WF_PREDICATE_def Rep_WF_BINDING )

theorem FalseP_closure [closure] :
"Rep_WF_BINDING ` false \<in> WF_PREDICATE"
  by (simp add: FalseP_def WF_PREDICATE_def)

theorem NotP_closure [closure] :
"Rep_WF_BINDING ` (\<not>p p) \<in> WF_PREDICATE"
apply (simp add: NotP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem AndP_closure [closure] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (p1 \<and>p p2) \<in> WF_PREDICATE"
apply (simp add: AndP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem OrP_closure [closure] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (p1 \<or>p p2) \<in> WF_PREDICATE"
apply (simp add: OrP_def)
apply (simp add: WF_PREDICATE_def)
done

theorem ImpliesP_closure [closure] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (p1 \<Rightarrow>p p2) \<in> WF_PREDICATE"
apply (simp add: ImpliesP_def)
apply (auto simp: closure)
done

theorem IffP_closure [closure] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<Leftrightarrow>p p2 \<in> WF_PREDICATE"
apply (simp add: IffP_def)
apply (auto simp: closure)
done

theorem ExistsP_closure [closure] :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<exists>p vs . p) \<in> WF_PREDICATE"
apply (simp add: ExistsP_def)
apply (simp add: WF_PREDICATE_def)
apply (auto intro!: closure)
done

theorem ForallP_closure [closure] :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (\<forall>p vs . p) \<in> WF_PREDICATE"
apply (simp add: ForallP_def)
apply (auto simp: closure)
done

theorem ClosureP_closure [closure] :
"\<lbrakk>p \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 [p]p \<in> WF_PREDICATE"
apply (simp add: ClosureP_def)
apply (auto simp: closure)
done

theorem RefP_closure [closure] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 \<sqsubseteq>p p2 \<in> WF_PREDICATE"
apply (simp add: RefP_def)
apply (auto simp: closure)
done
*)

subsubsection {* Validation of Soundness *}

theorem TrueP_noteq_FalseP :
"true \<noteq> false"
  by (auto simp add: TrueP.rep_eq FalseP.rep_eq)

end
