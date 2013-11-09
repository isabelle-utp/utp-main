(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_binding.thy                                                      *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Variable Bindings *}

theory utp_binding
imports 
  utp_synonyms 
  utp_value 
  utp_sorts 
  utp_var
begin

subsection {* Value Compatibility *}

text {* Can the given value be placed into the given variable? *}

definition var_compat :: "'VALUE \<Rightarrow> 'VALUE VAR \<Rightarrow> bool" (infix "\<rhd>" 50) where
"v \<rhd> x \<equiv> v : vtype x \<and> (aux x \<longrightarrow> \<D> v)"

lemma var_compat_intros [intro]:
  "\<lbrakk> v : vtype x; \<D> v \<rbrakk> \<Longrightarrow> v \<rhd> x"
  "\<lbrakk> v : vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> v \<rhd> x"
  by (simp_all add:var_compat_def)

lemma var_compat_cases [elim]:
  "\<lbrakk> v \<rhd> x; \<lbrakk> v : vtype x; \<D> v \<rbrakk> \<Longrightarrow> P
          ; \<lbrakk> v : vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:var_compat_def)

lemma var_compat_typing [typing]:
  "v \<rhd> x \<Longrightarrow> v : vtype x"
  by (auto simp add:var_compat_def)

lemma var_compat_defined [defined]:
  "\<lbrakk> v \<rhd> x; aux x \<rbrakk> \<Longrightarrow> \<D> v"
  by (auto simp add:var_compat_def)  

lemma var_compat_default [typing]:
  "default (vtype x) \<rhd> x"
  by (auto intro:typing defined)

lemma var_compat_dash [typing]:
  "v \<rhd> x \<Longrightarrow> v \<rhd> x\<acute>"
  by (simp add:var_compat_def)

lemma var_compat_undash [typing]:
  "v \<rhd> x \<Longrightarrow> v \<rhd> undash x"
  by (simp add:var_compat_def)

subsection {* Variable coercison *}

definition vcoerce :: "'a \<Rightarrow> 'a VAR \<Rightarrow> 'a" where
"vcoerce v x = (if (v \<rhd> x) then v else default (vtype x))"

lemma vcoerce_compat [typing]:
  "vcoerce v x \<rhd> x"
  by (simp add:vcoerce_def var_compat_default)

lemma vcoerce_reduce1 [simp]:
  "v \<rhd> x \<Longrightarrow> vcoerce v x = v"
  by (simp add: vcoerce_def)

lemma vcoerce_reduce2 [simp]:
  "\<not> v \<rhd> x \<Longrightarrow> vcoerce v x = default (vtype x)"
  by (simp add: vcoerce_def)

subsection {* Bindings *}

text {* We require bindings to be well-typed. *}

definition "WF_BINDING \<equiv> {b . \<forall> v. b v \<rhd> v}"

subsubsection {* Binding Theorems *}

theorem WF_BINDING_exists :
"\<exists> b . b \<in> WF_BINDING"
apply (rule_tac x = "(\<lambda> v . SOME x . x : (vtype v) \<and> \<D> x)" in exI)
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
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (b v) : (vtype v)"
apply (auto simp add: WF_BINDING_def)
done

theorem WF_BINDING_app_carrier [intro] :
"\<lbrakk>b \<in> WF_BINDING\<rbrakk> \<Longrightarrow> (b v) \<in> carrier (vtype v)"
apply (simp add: WF_BINDING_app_type carrier_def)
done

theorem WF_BINDING_update1 [closure] :
"\<lbrakk>b \<in> WF_BINDING; x \<rhd> v\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: WF_BINDING_def)
done

theorem WF_BINDING_update2 [closure] :
"\<lbrakk>b \<in> WF_BINDING; x \<in> carrier (vtype v); \<not> aux v\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: carrier_def closure var_compat_intros)
done

theorem WF_BINDING_update2_aux [closure] :
"\<lbrakk>b \<in> WF_BINDING; x \<in> carrier (vtype v); aux v; \<D> x\<rbrakk> \<Longrightarrow>
 b(v := x) \<in> WF_BINDING"
apply (simp add: carrier_def closure var_compat_intros)
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

theorem WF_BINDING_aux_defined [defined]:
"\<lbrakk> b \<in> WF_BINDING; aux v \<rbrakk> \<Longrightarrow> \<D> (b v)"
  by (auto simp add:WF_BINDING_def)

subsubsection {* Binding type *}

typedef 'VALUE WF_BINDING = "WF_BINDING :: 'VALUE BINDING set"
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

subsubsection {* Binding operators *}

text {* Binding Equivalence *}

definition binding_equiv ::
  "'VALUE WF_BINDING \<Rightarrow>
   'VALUE WF_BINDING \<Rightarrow>
   ('VALUE VAR set) \<Rightarrow> bool" where
"(binding_equiv b1 b2 a) \<longleftrightarrow> (\<forall> x \<in> a . \<langle>b1\<rangle>\<^sub>bx = \<langle>b2\<rangle>\<^sub>bx)"

notation binding_equiv ("_ \<cong> _ on _")

text {* The lifting package allows us to define operators on a typedef
by lifting operators on the underlying type. The following command sets
up the @{term "WF_BINDING"} type for lifting. *}

setup_lifting type_definition_WF_BINDING

text {* Binding override *}

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

lemma binding_type [simp, typing, intro]: "t = vtype x \<Longrightarrow> \<langle>b\<rangle>\<^sub>bx : t"
  apply (insert Rep_WF_BINDING[of b])
  apply (auto simp add:WF_BINDING_def)
done

lemma binding_stype [typing]:
  "\<lbrakk> t = vtype x; aux x \<rbrakk> \<Longrightarrow> \<langle>b\<rangle>\<^sub>b x :! t"
  by (auto intro:typing simp add:defined)

lemma binding_compat [simp, intro, typing]: "\<langle>b\<rangle>\<^sub>bx \<rhd> x"
  by auto

lemma aux_defined [defined]:
  "aux v \<Longrightarrow> \<D> (\<langle>b\<rangle>\<^sub>b v)"
  by (metis binding_compat var_compat_def)

lemma binding_value_alt [simp, intro]: 
  "\<lbrakk> vtype x = vtype x'; aux x = aux x' \<rbrakk> \<Longrightarrow> \<langle>b\<rangle>\<^sub>bx \<rhd> x'"
  by (auto simp add:var_compat_def intro: defined)

lemma binding_eq_iff: "f = g = (\<forall>x. \<langle>f\<rangle>\<^sub>b x = \<langle>g\<rangle>\<^sub>b x)"
  by (force)

text {* Binding update *}

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

lemma Rep_WF_BINDING_rep_eq [simp]:
  "\<lbrakk> v \<rhd> x \<rbrakk> \<Longrightarrow> \<langle>binding_upd b x v\<rangle>\<^sub>b = fun_upd \<langle>b\<rangle>\<^sub>b x v"
  apply (simp add:var_compat_def)
  apply (subgoal_tac "\<langle>b\<rangle>\<^sub>b(x := v) \<in> WF_BINDING")
  apply (simp_all add: binding_upd_def WF_BINDING_def)
  apply (auto intro:defined closure)
done

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

lemma binding_upd_override [simp]: 
  "\<lbrakk> x \<in> vs; v \<rhd> x \<rbrakk> \<Longrightarrow> (b1(x :=\<^sub>b v)) \<oplus>\<^sub>b b2 on vs = b1 \<oplus>\<^sub>b b2 on vs"
  by (force simp add:override_on_def binding_equiv_def)

lemma binding_upd_simps [simp]:
  "\<lbrakk> v1 \<rhd> x; v2 \<rhd> x \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v1, x :=\<^sub>b v2) = b(x :=\<^sub>b v2)"
  "b(x :=\<^sub>b \<langle>b\<rangle>\<^sub>b x) = b"
  by (auto)

lemma binding_value_eq [simp]: 
  "\<lbrakk> v1 \<rhd> x; v2 \<rhd> x \<rbrakk> \<Longrightarrow> b(x :=\<^sub>b v1) = b(x :=\<^sub>b v2) \<longleftrightarrow> v1 = v2"
  by (metis binding_upd_apply)

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

lemma binding_override_minus:
  "b1 \<oplus>\<^sub>b b2 on vs = b2 \<oplus>\<^sub>b b1 on - vs"
  by (force simp add:override_on_def)

lemma binding_override_overshadow:
  "(b1 \<oplus>\<^sub>b b2 on vs1 \<union> vs2) \<oplus>\<^sub>b b3 on vs1 = (b1 \<oplus>\<^sub>b b2 on vs2) \<oplus>\<^sub>b b3 on vs1"
  by (force simp add:override_on_def)

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
  "v \<rhd> x \<Longrightarrow> b1(x :=\<^sub>b v) \<cong> b1 on vs - {x}"
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

text {* The default binding. Every variable maps to the default value. *}

lift_definition default_binding :: 
  "'VALUE WF_BINDING" ("\<B>") is "(\<lambda> v . SOME x . x : (vtype v) \<and> \<D> x)" 
  apply (auto simp add: WF_BINDING_def)
  apply (rule someI2_ex)
  apply (rule type_non_empty_elim)
  apply (auto)
done

lemma default_binding_dash [simp]:
  "\<langle>\<B>\<rangle>\<^sub>b (x\<acute>) = \<langle>\<B>\<rangle>\<^sub>b x"
  by (simp add:default_binding.rep_eq)

end
