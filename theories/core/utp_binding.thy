(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_binding.thy                                                      *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Variable Bindings *}

theory utp_binding
imports
  utp_var
  utp_model
begin

default_sort (*PRE_*)TYPED_MODEL

subsection {* Value Compatibility *}

text {* Can the given value be placed into the given variable? *}

definition var_compat :: "'m uval \<Rightarrow> 'm uvar \<Rightarrow> bool" (infix "\<rhd>" 50) where
"x \<rhd> v \<longleftrightarrow> x : vtype v \<and> (aux v \<longrightarrow> \<D>\<^sub>v x)"

lemma var_compat_intros [intro] :
"\<lbrakk>v : vtype x; \<D>\<^sub>v v\<rbrakk> \<Longrightarrow> v \<rhd> x"
"\<lbrakk>v : vtype x; \<not> aux x\<rbrakk> \<Longrightarrow> v \<rhd> x"
  by (simp_all add: var_compat_def)

lemma var_compat_cases [elim] :
"\<lbrakk>v \<rhd> x; \<lbrakk>v : vtype x; \<D>\<^sub>v v\<rbrakk> \<Longrightarrow> P; \<lbrakk>v : vtype x; \<not> aux x\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp add: var_compat_def)

lemma var_compat_typing [typing]:
"v \<rhd> x \<Longrightarrow> v : vtype x"
  by (auto simp add: var_compat_def)

lemma var_compat_defined [defined]:
"\<lbrakk>v \<rhd> x; aux x\<rbrakk> \<Longrightarrow> \<D>\<^sub>v v"
  by (auto simp add: var_compat_def)

lemma var_compat_default [typing]:
  "default (vtype x) \<rhd> x"
apply (unfold var_compat_def)
apply (simp add: typing defined)
done

lemma var_compat_dash [typing]:
"v \<rhd> x \<Longrightarrow> v \<rhd> x\<acute>"
  by (simp add: var_compat_def)

lemma var_compat_undash [typing]:
"v \<rhd> x \<Longrightarrow> v \<rhd> undash x"
  by (simp add: var_compat_def)

subsection {* Variable coercison *}

definition vcoerce :: "'m uval \<Rightarrow> 'm uvar \<Rightarrow> 'm uval" where
"vcoerce v x = (if (v \<rhd> x) then v else default (vtype x))"

lemma vcoerce_compat [typing] :
"vcoerce v x \<rhd> x"
  by (simp add:vcoerce_def var_compat_default)

lemma vcoerce_reduce1 [simp] :
"v \<rhd> x \<Longrightarrow> vcoerce v x = v"
  by (simp add: vcoerce_def)

lemma vcoerce_reduce2 [simp] :
"\<not> v \<rhd> x \<Longrightarrow> vcoerce v x = default (vtype x)"
  by (simp add: vcoerce_def)

lemma vcoerce_idem [simp] :
"vcoerce (vcoerce v x) x = vcoerce v x"
  by (simp add:vcoerce_def)

subsection {* Bindings *}

text {* We require bindings to be well-typed. *}

definition binding :: "('m::TYPED_MODEL uvar \<Rightarrow> 'm uval) set" where
"binding = {b . \<forall> v . b v \<rhd> v}"

subsubsection {* Binding Theorems *}

theorem binding_exists :
"\<exists> b . b \<in> binding"
apply (rule_tac x = "(\<lambda> v . SOME x . x : (vtype v) \<and> \<D>\<^sub>v x)" in exI)
apply (auto simp add: binding_def)
apply (rule someI2_ex)
apply (rule types_non_empty)
apply (auto)
done

(* Some attempt to convert the above proof into ISAR. *)

(*
theorem binding_exists :
"\<exists> b . b \<in> binding"
apply (rule_tac x = "(\<lambda> v . SOME x . x : (type v))" in exI)
apply (simp add: binding_def)
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

theorem binding_non_empty :
"binding \<noteq> {}"
apply (insert binding_exists)
apply (auto)
done

theorem binding_app_compat [intro] :
"\<lbrakk>b \<in> binding\<rbrakk> \<Longrightarrow> (b v) \<rhd> v"
  apply (simp add: binding_def)
done

theorem binding_app_type [intro] :
"\<lbrakk>b \<in> binding\<rbrakk> \<Longrightarrow> (b v) : (vtype v)"
apply (auto simp add: binding_def)
done

theorem binding_app_carrier [intro] :
"\<lbrakk>b \<in> binding\<rbrakk> \<Longrightarrow> (b v) \<in> carrier (vtype v)"
apply (simp add: binding_app_type carrier_def)
done

theorem binding_update1 [closure] :
"\<lbrakk>b \<in> binding; x \<rhd> v\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> binding"
apply (simp add: binding_def)
done

theorem binding_update2 [closure] :
"\<lbrakk>b \<in> binding; x \<in> carrier (vtype v); \<not> aux v\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> binding"
apply (simp add: carrier_def closure var_compat_intros)
done

theorem binding_update2_aux [closure] :
"\<lbrakk>b \<in> binding; x \<in> carrier (vtype v); aux v; \<D>\<^sub>v x\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> binding"
apply (simp add: carrier_def closure var_compat_intros)
done

theorem binding_override [closure] :
"\<lbrakk>b1 \<in> binding;
 b2 \<in> binding\<rbrakk> \<Longrightarrow>
 b1 \<oplus> b2 on vs \<in> binding"
apply (simp add: binding_def)
apply (safe)
apply (case_tac "v \<in> vs")
apply (auto simp add:override_on_def)
done

theorem binding_aux_defined [defined]:
"\<lbrakk> b \<in> binding; aux v \<rbrakk> \<Longrightarrow> \<D>\<^sub>v (b v)"
  by (auto simp add:binding_def)

subsubsection {* Binding type *}

typedef 'a binding = "binding :: ('a uvar \<Rightarrow> 'a uval)  set"
  by (simp add: binding_exists)

declare Rep_binding [simp]
declare Rep_binding_inverse [simp]
declare Abs_binding_inverse [simp]

lemma Rep_binding_intro [intro]:
  "Rep_binding x = Rep_binding y \<Longrightarrow> x = y"
  by (simp add:Rep_binding_inject)

lemma Rep_binding_elim [elim]:
  "\<lbrakk> x = y; Rep_binding x = Rep_binding y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

notation Rep_binding ("\<langle>_\<rangle>\<^sub>b")

subsubsection {* Binding operators *}

text {* Binding Equivalence *}

definition binding_equiv ::
  "'a binding \<Rightarrow>
   'a binding \<Rightarrow>
   ('a uvar set) \<Rightarrow> bool" where
"(binding_equiv b1 b2 a) \<longleftrightarrow> (\<forall> x \<in> a . \<langle>b1\<rangle>\<^sub>bx = \<langle>b2\<rangle>\<^sub>bx)"

notation binding_equiv ("_ \<cong> _ on _")

text {* The lifting package allows us to define operators on a typedef
by lifting operators on the underlying type. The following command sets
up the @{term "binding"} type for lifting. *}

setup_lifting type_definition_binding

text {* Binding override *}

lift_definition binding_override_on ::
  "'a binding \<Rightarrow>
   'a binding \<Rightarrow>
   'a uvar set \<Rightarrow>
   'a binding" ("_ \<oplus>\<^sub>b _ on _" [56, 0, 57] 55) is "override_on"
  apply (simp add: binding_def)
  apply (safe)
  apply (case_tac "v \<in> set")
  apply (auto)
done

declare binding_override_on.rep_eq [simp]

lemma binding_type [typing, intro]: "t = vtype x \<Longrightarrow> \<langle>b\<rangle>\<^sub>bx : t"
  apply (insert Rep_binding[of b])
  apply (auto simp add:binding_def)
done

lemma binding_stype [typing]:
  "\<lbrakk> t = vtype x; aux x \<rbrakk> \<Longrightarrow> \<langle>b\<rangle>\<^sub>b x :! t"
  by (auto intro:typing simp add:defined)

lemma binding_compat [intro, typing]: "\<langle>b\<rangle>\<^sub>bx \<rhd> x"
  by auto

lemma aux_defined [defined]:
  "aux v \<Longrightarrow> \<D>\<^sub>v (\<langle>b\<rangle>\<^sub>b v)"
  by (metis binding_compat var_compat_def)

lemma binding_value_alt [simp, intro]: 
  "\<lbrakk> vtype x = vtype x'; aux x = aux x' \<rbrakk> \<Longrightarrow> \<langle>b\<rangle>\<^sub>bx \<rhd> x'"
  by (auto simp add:var_compat_def intro: defined)

lemma binding_eq_iff: "f = g = (\<forall>x. \<langle>f\<rangle>\<^sub>b x = \<langle>g\<rangle>\<^sub>b x)"
  by (auto)

text {* Binding update *}

lift_definition binding_upd :: 
  "'m binding \<Rightarrow>
   'm uvar \<Rightarrow>
   'm uval \<Rightarrow>
   'm binding" is
"\<lambda> b x v. (fun_upd b x (vcoerce v x))"
  by (simp add:binding_def typing)

nonterminal bupdbinds and bupdbind

syntax
  "_bupdbind" :: "['a, 'a] => bupdbind"               ("(2_ :=\<^sub>b/ _)")
  ""         :: "bupdbind => bupdbinds"               ("_")
  "_bupdbinds":: "[bupdbind, bupdbinds] => bupdbinds" ("_,/ _")
  "_BUpdate"  :: "['a, bupdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

translations
  "_BUpdate f (_bupdbinds b bs)" == "_BUpdate (_BUpdate f b) bs"
  "f(x:=\<^sub>by)" == "CONST binding_upd f x y"

lemma Rep_binding_rep_eq [simp]:
  "\<lbrakk> v \<rhd> x \<rbrakk> \<Longrightarrow> \<langle>binding_upd b x v\<rangle>\<^sub>b = fun_upd \<langle>b\<rangle>\<^sub>b x v"
  by (simp_all add: binding_upd_def binding_def)

lemma binding_upd_idem_iff: "y \<rhd> x \<Longrightarrow> (f(x:=\<^sub>by) = f) = (\<langle>f\<rangle>\<^sub>b x = y)"
  by (auto simp add: fun_upd_idem_iff var_compat_def)

lemma binding_upd_idem: "\<lbrakk> y \<rhd> x \<rbrakk> \<Longrightarrow> \<langle>f\<rangle>\<^sub>b x = y ==> f(x:=\<^sub>by) = f"
  by (simp add: binding_upd_idem_iff)

lemma binding_upd_triv [iff]: "f(x :=\<^sub>b \<langle>f\<rangle>\<^sub>b x) = f"
  by (simp add: binding_upd_idem)

lemma binding_upd_apply [simp]: "\<langle>f(x:=\<^sub>by)\<rangle>\<^sub>b z = (if z=x then (vcoerce y x) else \<langle>f\<rangle>\<^sub>b z)"
  by (auto simp add:binding_upd.rep_eq)

lemma binding_upd_upd [simp]: 
  "f(x:=\<^sub>by,x:=\<^sub>bz) = f(x:=\<^sub>bz)"
  by (auto simp add:binding_upd.rep_eq)

lemma binding_upd_twist: 
  "\<lbrakk> a ~= c \<rbrakk> \<Longrightarrow> (m(a:=\<^sub>bb))(c:=\<^sub>bd) = (m(c:=\<^sub>bd))(a:=\<^sub>bb)"
  by (force simp add:binding_upd.rep_eq)

theorem binding_override_on_eq :
"f1 \<oplus>\<^sub>b g1 on a = f2 \<oplus>\<^sub>b g2 on a \<longleftrightarrow>
 (\<forall> x . x \<in> a \<longrightarrow> \<langle>g1\<rangle>\<^sub>bx = \<langle>g2\<rangle>\<^sub>bx) \<and>
 (\<forall> x . x \<notin> a \<longrightarrow> \<langle>f1\<rangle>\<^sub>bx = \<langle>f2\<rangle>\<^sub>bx)"
apply (simp add: binding_override_on_def
  Abs_binding_inject closure override_on_eq2)
apply (safe)
done

lemma binding_override_left_eq: 
  "b1 \<cong> b2 on vs2 \<Longrightarrow> b1 \<oplus>\<^sub>b b3 on vs1 \<cong> b2 \<oplus>\<^sub>b b3 on vs1 on vs2"
  by (auto simp add:binding_equiv_def override_on_def)

text {* Transfer override theorems *}

lemma binding_override_simps [simp]:
  "(f \<oplus>\<^sub>b g on vs1) \<oplus>\<^sub>b g on vs2 = f \<oplus>\<^sub>b g on (vs1 \<union> vs2)"
  "f \<oplus>\<^sub>b f on vs = f"
  "(f \<oplus>\<^sub>b g on vs) \<oplus>\<^sub>b h on vs = f \<oplus>\<^sub>b h on vs"
  "f \<oplus>\<^sub>b (g \<oplus>\<^sub>b h on a) on a = f \<oplus>\<^sub>b h on a"
  "f \<oplus>\<^sub>b (g \<oplus>\<^sub>b f on b) on a = f \<oplus>\<^sub>b g on a - b"
  "f \<oplus>\<^sub>b (f \<oplus>\<^sub>b g on a) on b = f \<oplus>\<^sub>b g on a \<inter> b"
  "f \<oplus>\<^sub>b g on (insert x xs) = f(x :=\<^sub>b \<langle>g\<rangle>\<^sub>bx) \<oplus>\<^sub>b g on xs - {x}"
  "(f \<oplus>\<^sub>b g on a)(x :=\<^sub>b v) = f(x :=\<^sub>b v) \<oplus>\<^sub>b g on (a - {x})"
  "x \<in> vs2 \<Longrightarrow> \<langle>f \<oplus>\<^sub>b g on vs1 - vs2\<rangle>\<^sub>bx = \<langle>f\<rangle>\<^sub>bx"
  "f \<oplus>\<^sub>b g on VAR = g"
  "f \<oplus>\<^sub>b g on {} = f"
  apply (auto simp add:override_on_assoc override_on_singleton override_on_chain)
  apply (auto intro!: Rep_binding_intro simp add:binding_upd.rep_eq)
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
  apply (rule Rep_binding_intro)
  apply (simp)
  apply (drule_tac f="\<langle>f\<rangle>\<^sub>b" and g="\<langle>g\<rangle>\<^sub>b" and h="\<langle>h\<rangle>\<^sub>b" in override_on_reorder)
  apply (simp)
done

lemma binding_override_equiv [simp]:
  "b1 \<cong> b2 on vs \<Longrightarrow> b1 \<oplus>\<^sub>b b2 on vs = b1"
  by (force simp add:override_on_def binding_equiv_def)

lemma binding_override_upd [simp]:
  "\<lbrakk> x \<in> vs \<rbrakk> \<Longrightarrow> b1 \<oplus>\<^sub>b b2(x :=\<^sub>b v) on vs = b1(x :=\<^sub>b v) \<oplus>\<^sub>b b2 on (vs - {x})"
  by (force simp add:binding_upd.rep_eq override_on_def)

lemma binding_upd_override [simp]: 
  "\<lbrakk> x \<in> vs \<rbrakk> \<Longrightarrow> (b1(x :=\<^sub>b v)) \<oplus>\<^sub>b b2 on vs = b1 \<oplus>\<^sub>b b2 on vs"
  by (force simp add:override_on_def binding_equiv_def binding_upd.rep_eq)

lemma binding_upd_simps [simp]:
  "b(x :=\<^sub>b v1, x :=\<^sub>b v2) = b(x :=\<^sub>b v2)"
  "b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x) = b"
  by (auto)

lemma binding_value_eq [simp]: 
  "\<lbrakk> v1 \<rhd> x; v2 \<rhd> x \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v1) = b(x :=\<^sub>b v2) \<longleftrightarrow> v1 = v2"
  by (metis binding_upd_apply vcoerce_reduce1)

subsubsection {* Binding Equivalence *}

theorem binding_equiv_empty [simp] :
"b1 \<cong> b2 on {}"
apply (simp add: binding_equiv_def)
done

theorem binding_equiv_insert [simp] :
"b1 \<cong> b2 on (insert x a) \<longleftrightarrow>
 (b1 \<cong> b2 on a) \<and> \<langle>b1\<rangle>\<^sub>b x = \<langle>b2\<rangle>\<^sub>b x"
apply (simp add: binding_equiv_def)
apply (auto)
done

theorem binding_equiv_subset :
"\<lbrakk>b1 \<cong> b2 on a2;
 a1 \<subseteq> a2\<rbrakk> \<Longrightarrow>
 b1 \<cong> b2 on a1"
apply (simp add: binding_equiv_def)
apply (auto)
done

theorem binding_equiv_idem [simp] :
"b \<cong> b on a"
apply (simp add: binding_equiv_def)
done

theorem binding_equiv_comm :
"b1 \<cong> b2 on a \<Longrightarrow> b2 \<cong> b1 on a"
apply (simp add: binding_equiv_def)
done

theorem binding_equiv_trans :
"\<lbrakk>b1 \<cong> b2 on a;
 b2 \<cong> b3 on a\<rbrakk> \<Longrightarrow>
 b1 \<cong> b3 on a"
apply (simp add: binding_equiv_def)
done

theorem binding_equiv_total :
"b1 \<cong> b2 on VAR \<longleftrightarrow> b1 = b2"
apply (simp add: binding_equiv_def)
apply (simp add: VAR_def)
apply (force)
done

lemma binding_equiv_update_drop:
  "\<lbrakk> b1 \<cong> b2 on vs - {x}; vcoerce v1 x = vcoerce v2 x \<rbrakk> 
   \<Longrightarrow> b1(x :=\<^sub>b v1) \<cong> b2(x :=\<^sub>b v2) on vs"
  by (simp add:binding_equiv_def)

lemma binding_override_minus:
  "b1 \<oplus>\<^sub>b b2 on vs = b2 \<oplus>\<^sub>b b1 on - vs"
  by (force simp add:override_on_def)

lemma binding_override_overshadow:
  "(b1 \<oplus>\<^sub>b b2 on vs1 \<union> vs2) \<oplus>\<^sub>b b3 on vs1 = (b1 \<oplus>\<^sub>b b2 on vs2) \<oplus>\<^sub>b b3 on vs1"
  by (force simp add:override_on_def)

lemma binding_override_overshadow2 [simp]:
  "(b1 \<oplus>\<^sub>b b2 on - vs) \<oplus>\<^sub>b b3 on vs = b2 \<oplus>\<^sub>b b3 on vs"
  by (force simp add:override_on_def)

lemma binding_override_overshadow3 [simp]:
  "b1 \<oplus>\<^sub>b (b2 \<oplus>\<^sub>b b3 on - vs) on vs = b1 \<oplus>\<^sub>b b2 on vs"
  by (force simp add:override_on_def)

lemma binding_override_left_subset:
  "vs1 \<subseteq> vs2 \<Longrightarrow> (b1 \<oplus>\<^sub>b b2 on vs1) \<oplus>\<^sub>b b3 on vs2 = b1 \<oplus>\<^sub>b b3 on vs2"
  by (metis binding_override_assoc binding_override_simps(4) sup_absorb2)

lemma binding_override_right_subset:
  "vs1 \<inter> vs2 = {} \<Longrightarrow> b1 \<oplus>\<^sub>b (b2 \<oplus>\<^sub>b b3 on vs1) on vs2 = b1 \<oplus>\<^sub>b b2 on vs2"
  by (force simp add:override_on_def)

lemma binding_override_commute:
  "vs1 \<inter> vs2 = {} \<Longrightarrow> (b1 \<oplus>\<^sub>b b2 on vs1) \<oplus>\<^sub>b b3 on vs2 = (b1 \<oplus>\<^sub>b b3 on vs2) \<oplus>\<^sub>b b2 on vs1"
  by (force simp add:override_on_def)

lemma binding_upd_override2 [simp]:
  "x \<notin> vs \<Longrightarrow> b(x :=\<^sub>b v) \<oplus>\<^sub>b b on vs = b(x :=\<^sub>b v)"
  by (force simp add:override_on_def)

lemma binding_override_subsume1 [simp]: 
  "(b1 \<oplus>\<^sub>b b2 on vs2) \<oplus>\<^sub>b b3 on vs1 \<union> vs2 = b1 \<oplus>\<^sub>b b3 on vs1 \<union> vs2"
  by (force simp add:override_on_def)

lemma binding_override_assoc':
  "b1 \<oplus>\<^sub>b (b2 \<oplus>\<^sub>b b3 on vs1) on vs2 = (b1 \<oplus>\<^sub>b b2 on vs2 - vs1) \<oplus>\<^sub>b b3 on vs1 \<inter> vs2"
  by (force simp add:binding_override_on.rep_eq override_on_def)

lemma binding_override_subsume2 [simp]: 
  "(b1 \<oplus>\<^sub>b b2 on vs1 \<union> vs2) \<oplus>\<^sub>b b3 on vs1 = (b1 \<oplus>\<^sub>b b2 on vs2) \<oplus>\<^sub>b b3 on vs1"
  by (force simp add:binding_override_on.rep_eq override_on_def)


lemma binding_override_equiv1 [simp]:
  "b1 \<oplus>\<^sub>b b2 on vs \<cong> b2 on vs"
  by (force simp add:override_on_def binding_equiv_def)

lemma binding_override_equiv2 [simp]:
  "b1 \<oplus>\<^sub>b b2 on vs \<cong> b1 on - vs"
  by (force simp add:override_on_def binding_equiv_def)

lemma binding_equiv_override:
  "b1 \<cong> b2 on vs \<Longrightarrow> b1 \<oplus>\<^sub>b b3 on - vs = b2 \<oplus>\<^sub>b b3 on - vs"
  by (force simp add:override_on_def binding_equiv_def)

lemma binding_equiv_upd: 
  "b1(x :=\<^sub>b v) \<cong> b1 on vs - {x}"
  by (auto simp add:binding_equiv_def)

lemma binding_equiv_minus: 
  "b1 \<cong> b2 on vs1 \<Longrightarrow> b1 \<cong> b2 on (vs1 - vs2)"
  by (auto simp add:binding_equiv_def)

lemma binding_equiv_override_right_intro [intro]:
  "\<lbrakk> b1 \<cong> b2 on (- vs1 \<inter> vs2); b1 \<cong> b3 on (vs1 \<inter> vs2) \<rbrakk> \<Longrightarrow> 
         b1 \<cong> (b2 \<oplus>\<^sub>b b3 on vs1) on vs2"
  apply (auto simp add:binding_equiv_def)
  apply (case_tac "x \<in> vs1")
  apply (auto)
done

lemma binding_override_eq_intro:
  "\<lbrakk> b1 \<cong> b3 on - vs
   ; b2 \<cong> b4 on vs \<rbrakk> \<Longrightarrow>
  b1 \<oplus>\<^sub>b b2 on vs = b3 \<oplus>\<^sub>b b4 on vs"
  by (metis binding_equiv_override binding_override_minus)

lemma binding_equiv_union_intro:
  "\<lbrakk> b1 \<cong> b2 on vs1; b1 \<cong> b2 on vs2 \<rbrakk> \<Longrightarrow>
     b1 \<cong> b2 on vs1 \<union> vs2" 
  by (auto simp add:binding_equiv_def)

lemma binding_equiv_UNDASHED_overshadow:
  "b1 \<cong> b2 \<oplus>\<^sub>b b3 on UNDASHED on NON_REL_VAR = b1 \<cong> b2 on NON_REL_VAR"
  apply (auto simp add:binding_equiv_def)
  apply (auto simp add:override_on_def)
done

lemma binding_eq_split_equiv:
  "\<lbrakk> b1 \<cong> b2 on D\<^sub>0; b1 \<cong> b2 on D\<^sub>1; b1 \<cong> b2 on NON_REL_VAR \<rbrakk> \<Longrightarrow> b1 = b2"
  apply (auto simp add:binding_equiv_def)
  apply (rule Rep_binding_intro, rule ext)
  apply (case_tac "x \<in> D\<^sub>0", simp_all)
  apply (case_tac "x \<in> D\<^sub>1", simp_all)
  apply (drule_tac x="x" in bspec) back back
  apply (auto simp add:NON_REL_VAR_def)
done

lemma binding_equiv_override_subsume [simp]:
  "(b1 \<oplus>\<^sub>b b2 on vs) \<cong> b3 on vs \<longleftrightarrow> b2 \<cong> b3 on vs"
  by (auto simp add:binding_equiv_def binding_upd.rep_eq)

lemma binding_equiv_update_subsume [simp]:
  "x \<notin> vs \<Longrightarrow> b1(x :=\<^sub>b v) \<cong> b2 on vs \<longleftrightarrow> b1 \<cong> b2 on vs"
  by (auto simp add:binding_equiv_def binding_upd.rep_eq)

lemma binding_equiv_update_subsume' [simp]:
  "x \<notin> vs \<Longrightarrow> b1 \<cong> b2(x :=\<^sub>b v) on vs \<longleftrightarrow> b1 \<cong> b2 on vs"
  by (auto simp add:binding_equiv_def binding_upd.rep_eq)

lemma binding_equiv_update_drop2:
  "b1(x :=\<^sub>b v1) \<cong> b2(x :=\<^sub>b v2) on vs \<Longrightarrow> b1 \<cong> b2 on vs - {x}"
  apply (auto simp add:binding_equiv_def binding_upd.rep_eq)
  apply (drule_tac x="xa" in bspec, auto, metis)
done

lemma binding_equiv_overshadow_left:
  "vs1 \<inter> vs2 = {} \<Longrightarrow> (b1 \<oplus>\<^sub>b b2 on vs1) \<cong> b3 on vs2 \<longleftrightarrow> b1 \<cong> b3 on vs2"
  by (force simp add:override_on_def binding_equiv_def)

lemma binding_equiv_overshadow_right:
  "vs1 \<inter> vs2 = {} \<Longrightarrow> b1 \<cong> (b2 \<oplus>\<^sub>b b3 on vs1) on vs2 \<longleftrightarrow> b1 \<cong> b2 on vs2"
  by (force simp add:override_on_def binding_equiv_def)

lemma binding_override_equiv_subset: 
  "\<lbrakk> b1 \<cong> b2 on vs1; vs2 \<subseteq> vs1 \<rbrakk> \<Longrightarrow> b1 \<oplus>\<^sub>b b2 on vs2 = b1"
  by (metis binding_equiv_subset binding_override_equiv)

text {* The default binding. Every variable maps to the default value. *}

lift_definition default_binding :: 
  "'a binding" ("\<B>") is "(\<lambda> v . SOME x . x : (vtype v) \<and> \<D>\<^sub>v x)" 
  apply (auto simp add: binding_def)
  apply (rule someI2_ex)
  apply (rule types_non_empty)
  apply (auto)
done

lemma default_binding_dash [simp]:
  "\<langle>\<B>\<rangle>\<^sub>b (x\<acute>) = \<langle>\<B>\<rangle>\<^sub>b x"
  by (simp add:default_binding.rep_eq)

text {* Convert a binding to a finite map *}

definition binding_map :: "'a uvar set \<Rightarrow> 'a binding \<Rightarrow> 'a uvar \<rightharpoonup> 'a uval" where
"binding_map xs b = (\<lambda> x. if (x \<in> xs) then Some (\<langle>b\<rangle>\<^sub>b x) else None)"

lemma binding_map_dom: "dom (binding_map xs b) = xs"
  by (simp add: dom_def binding_map_def)

lift_definition map_binding :: "('a uvar \<rightharpoonup> 'a uval) \<Rightarrow> 'a binding"
is "\<lambda> f x. case f x of Some v \<Rightarrow> vcoerce v x | None \<Rightarrow> default (vtype x)"
  apply (auto simp add: binding_def)
  apply (case_tac "fun v")
  apply (simp_all add:typing)
done

lemma map_binding_inv:
  "map_binding (binding_map xs b) \<cong> b on xs"
  by (simp add: binding_map_def map_binding.rep_eq binding_equiv_def)

default_sort type

end
