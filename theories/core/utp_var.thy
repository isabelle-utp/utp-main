(******************************************************************************)
(* Project: Unifying Theories of Programming in Isabelle/HOL                  *)
(* File: utp_var.thy                                                          *)
(* Author: Simon Foster & Frank Zeyda, University of York (UK)                *)
(******************************************************************************)
(* LAST REVIEWED: 15 July 2014 *)

header {* UTP Variables *}

theory utp_var
imports utp_name utp_model
begin

default_sort type

subsection {* Variable Model *}

record 'm uvar =
  name :: "uname" ("vname")
  type :: "'m utype" ("vtype")
  strict :: "bool" ("aux")

definition VAR :: "'m uvar set" where
"VAR = UNIV"

abbreviation var_dashes :: "'m uvar \<Rightarrow> nat" ("vdashes") where
"var_dashes v \<equiv> dashes (name v)"

abbreviation var_subscript :: "'m uvar \<Rightarrow> string" ("vsub") where
"var_subscript x \<equiv> subscript (name x)"

subsection {* Countability *}

definition uvar_to_nat ::
  "('m::COUNTABLE_MODEL, 'more::countable) uvar_ext \<Rightarrow> nat" where
"uvar_to_nat v = to_nat (name v, type v, strict v, more v)"

instance uvar_ext :: (COUNTABLE_MODEL, countable) countable
apply (intro_classes)
apply (rule_tac x = "uvar_to_nat" in exI)
apply (rule injI)
apply (unfold uvar_to_nat_def)
apply (erule asmE)
apply (induct_tac x)
apply (induct_tac y)
apply (simp)
done

subsection {* Linear Order *}

text {*
  For now we derive the linear order for variables from the countability of
  model types. That order is, however, not so useful as it cannot effectively
  be evaluated. Future work might consider support for custom orders if this
  proofs to be necessary.
*}

instantiation uvar_ext :: (COUNTABLE_MODEL, linorder) linorder
begin
definition less_eq_uvar_ext ::
  "('m::COUNTABLE_MODEL, 'more::linorder) uvar_ext \<Rightarrow>
   ('m::COUNTABLE_MODEL, 'more::linorder) uvar_ext \<Rightarrow> bool" where
"(less_eq_uvar_ext v1 v2) \<longleftrightarrow>
   (name v1, type v1, strict v1, more v1) \<le>
   (name v2, type v2, strict v2, more v2)"

definition less_uvar_ext ::
  "('m::COUNTABLE_MODEL, 'more::linorder) uvar_ext \<Rightarrow>
   ('m::COUNTABLE_MODEL, 'more::linorder) uvar_ext \<Rightarrow> bool" where
"(less_uvar_ext v1 v2) \<longleftrightarrow> (v1 \<le> v2 \<and> \<not> v2 \<le> v1)"
instance
apply (intro_classes)
apply (simp add: less_uvar_ext_def)
apply (simp add: less_eq_uvar_ext_def)
apply (unfold less_eq_uvar_ext_def)
apply (smt dual_order.trans)
apply (metis eq_iff prod.inject uvar.equality)
apply (metis linear)
done
end

declare less_eq_uvar_ext_def [simp]
declare less_uvar_ext_def [simp]

subsection {* Constructors *}

definition MkVar :: "uname \<Rightarrow> 'm utype \<Rightarrow> bool \<Rightarrow> 'm uvar" where
"MkVar n t b = \<lparr>name = n, type = t, strict = b\<rparr>"

abbreviation MkPlain :: "string \<Rightarrow> 'm utype \<Rightarrow> bool \<Rightarrow> 'm uvar" where
"MkPlain s t d \<equiv> MkVar (bName s) t d"

subsection {* Restrictions *}

definition UNDASHED :: "'m uvar set" where
"UNDASHED = {v . dashes (name v) = 0}"

definition DASHED :: "'m uvar set" where
"DASHED = {v . dashes (name v) = 1}"

definition DASHED_TWICE :: "'m uvar set" where
"DASHED_TWICE = {v . dashes (name v) = 2}"

definition DASHED_THRICE :: "'m uvar set" where
"DASHED_THRICE = {v . dashes (name v) = 3}"

notation
  UNDASHED      ("D\<^sub>0") and
  DASHED        ("D\<^sub>1") and
  DASHED_TWICE  ("D\<^sub>2") and
  DASHED_THRICE ("D\<^sub>3")

definition NOSUB :: "'m uvar set" where
"NOSUB = {v. vsub v = NoSub}"

definition WITHSUB :: "nat \<Rightarrow> 'm uvar set" where
"WITHSUB n = {v. vsub v \<noteq> NoSub}"

definition PLAIN :: "'m uvar set" where
"PLAIN = UNDASHED \<inter> NOSUB"

definition AUX_VAR :: "'m uvar set" where
"AUX_VAR = {v . aux v}"

definition PROGRAM_VAR :: "'m uvar set" where
"PROGRAM_VAR = {v . \<not> aux v}"

abbreviation REL_VAR :: "'m uvar set" where
"REL_VAR \<equiv> UNDASHED \<union> DASHED"

definition NON_REL_VAR :: "'m uvar set" where
"NON_REL_VAR = -REL_VAR"

subsection {* Operators *}

definition dash :: "'m uvar \<Rightarrow> 'm uvar" where
"dash = name_update (dashes_update (\<lambda> d . d + 1))"

adhoc_overloading prime dash

definition undash :: "'m uvar \<Rightarrow> 'm uvar" where
"undash = name_update (dashes_update (\<lambda> d . d - 1))"

adhoc_overloading unprime undash

definition vchsub :: "'m uvar \<Rightarrow> string \<Rightarrow> 'm uvar" where
"vchsub v s = name_update (chsub s) v"

text {* TODO: Do we really need another abberviation here? Ask Simon. *}

abbreviation add_sub :: "string \<Rightarrow> 'm uvar \<Rightarrow> 'm uvar" where
"add_sub s v \<equiv> vchsub v s"

text {* TODO: Move the following into the Theorems subsection? *}

lemma add_sub_inv [simp] :
"add_sub s (add_sub s v) = v"
apply (unfold vchsub_def)
apply (simp)
done

lemma add_sub_bij :
"bij (add_sub s)"
apply (rule Fun.bijI)
apply (rule injI)
apply (metis add_sub_inv)
apply (metis add_sub_inv surj_def)
done

adhoc_overloading subscr vchsub

definition in_vars ::
  "'m uvar set \<Rightarrow>
   'm uvar set" ("in") where
"in vs = vs \<inter> UNDASHED"

definition out_vars ::
  "'m uvar set \<Rightarrow>
   'm uvar set" ("out") where
"out vs = vs \<inter> DASHED"

definition rel_vars ::
  "'m uvar set \<Rightarrow>
   'm uvar set" ("rel") where
"rel vs = vs \<inter> REL_VAR"

definition nrel_vars ::
  "'m uvar set \<Rightarrow>
   'm uvar set" ("nrel") where
"nrel vs = vs \<inter> NON_REL_VAR"

text {* homl and homr construct the left and right homogeneous alphabets. *}

definition homl :: "'m uvar set \<Rightarrow> 'm uvar set" where
"homl vs = in vs \<union> (dash ` in vs) \<union> nrel vs"

definition homr :: "'m uvar set \<Rightarrow> 'm uvar set" where
"homr vs = (undash ` out vs) \<union> out vs \<union> nrel vs"

definition COMPOSABLE ::
  "'m uvar set \<Rightarrow>
   'm uvar set \<Rightarrow> bool" where
"COMPOSABLE a1 a2 \<longleftrightarrow> (out a1) = dash ` (in a2)"

definition HOMOGENEOUS :: "'m uvar set \<Rightarrow> bool" where
"HOMOGENEOUS a \<longleftrightarrow> COMPOSABLE a a"

definition HOM :: "'m uvar set set" where
"HOM = {xs . HOMOGENEOUS xs}"

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

subsection {* Theorems *}

theorems var_defs =
  VAR_def
  PROGRAM_VAR_def
  AUX_VAR_def
  NON_REL_VAR_def
  UNDASHED_def
  DASHED_def
  DASHED_TWICE_def
  DASHED_THRICE_def
  NOSUB_def
  WITHSUB_def
  PLAIN_def
  MkVar_def
  undash_def
  dash_def
  vchsub_def
  in_vars_def
  out_vars_def
  nrel_vars_def
  homl_def
  homr_def
  COMPOSABLE_def
  HOMOGENEOUS_def

theorem VAR_member [simp] :
"x \<in> VAR"
  by (simp add: VAR_def)

theorem AUX_VAR_member [simp] :
"aux x \<Longrightarrow> x \<in> AUX_VAR"
  by (simp add:AUX_VAR_def)

theorem PROGRAM_VAR_member [simp] :
"\<not> aux x \<Longrightarrow> x \<in> PROGRAM_VAR"
  by (simp add:PROGRAM_VAR_def)

theorem VAR_subset [simp]:
"vs \<subseteq> VAR"
  by (simp add:VAR_def)

theorem MkVar_name [simp]:
  "name (MkVar n t s) = n"
  by (simp add:var_defs)

theorem MkVar_vtype [simp]:
  "vtype (MkVar n t s) = t"
  by (simp add:var_defs)

theorem MkVar_aux [simp]:
  "aux (MkVar n t s) = s"
  by (simp add:var_defs)

lemma MkVar_eq_iff[simp]:
  "MkVar n t s = MkVar n' t' s' \<longleftrightarrow> n = n' \<and> t = t' \<and> s = s'"
  by (auto simp add:var_defs)

lemma MkPlain_name [simp]: "name (MkPlain n t a) = bName n"
  by (simp add:var_defs)

lemma MkPlain_vtype [simp]: "vtype (MkPlain n t a) = t"
  by (simp add:var_defs)

lemma MkPlain_vsub [simp]: "vsub (MkPlain n t a) = NoSub"
  by (simp add:var_defs)

lemma MkPlain_aux [simp]: "aux (MkPlain n t a) = a"
  by (simp add:var_defs)

lemma MkPlain_UNDASHED [simp]: "MkPlain n t a \<in> UNDASHED"
  by (simp add:var_defs)

lemma MkPlain_NOSUB [simp]: "MkPlain n t a \<in> NOSUB"
  by (simp add:var_defs)

lemma MkPlain_eq_iff[simp]:
  "MkPlain n t a = MkPlain n' t' a' \<longleftrightarrow> n = n' \<and> t = t' \<and> a = a'"
  by (auto simp add:var_defs)

subsubsection {* Names and Types *}

theorem vtype_dash [simp] :
"vtype (dash x) = vtype x"
  by (simp add: var_defs)

theorem vtype_undash [simp] :
"vtype (undash x) = vtype x"
  by (simp add: var_defs)

theorem vsub_dash [simp] :
"vsub (dash x) = vsub x"
  by (simp add: var_defs)

theorem vsub_undash [simp] :
"vsub (undash x) = vsub x"
  by (simp add: var_defs)

theorem aux_dash [simp] :
"aux (dash x) = aux x"
  by (simp add: var_defs)

theorem aux_undash [simp] :
"aux (undash x) = aux x"
  by (simp add: var_defs)

theorem vtype_sub [simp] :
"vtype (x\<^bsub>n\<^esub>) = vtype x"
apply (case_tac x)
apply (simp add: var_defs)
done

theorem aux_sub [simp] :
"aux (x\<^bsub>n\<^esub>) = aux x"
apply (case_tac x)
apply (simp add: var_defs)
done

subsubsection {* Membership Theorems *}

theorem UNDASHED_not_DASHED :
"x \<in> UNDASHED \<Longrightarrow> \<not> x \<in> DASHED"
  by (simp add: var_defs)

theorem UNDASHED_not_DASHED_TWICE :
"x \<in> UNDASHED \<Longrightarrow> \<not> x \<in> DASHED_TWICE"
  by (simp add: var_defs)

theorem UNDASHED_not_DASHED_THRICE :
"x \<in> UNDASHED \<Longrightarrow> \<not> x \<in> DASHED_THRICE"
  by (simp add: var_defs)

theorem DASHED_not_DASHED_TWICE :
"x \<in> DASHED \<Longrightarrow> \<not> x \<in> DASHED_TWICE"
  by (simp add: var_defs)

theorem DASHED_not_DASHED_THRICE :
"x \<in> DASHED \<Longrightarrow> \<not> x \<in> DASHED_THRICE"
  by (simp add: var_defs)

theorem UNDASHED_dash_DASHED :
"x \<in> UNDASHED \<Longrightarrow> dash x \<in> DASHED"
  by (simp add: var_defs)

theorem UNDASHED_dash_not_UNDASHED :
"x \<in> UNDASHED \<Longrightarrow> x\<acute> \<notin> UNDASHED"
  by (simp add: var_defs)

theorem DASHED_undash_UNDASHED :
"x \<in> DASHED \<Longrightarrow> undash x \<in> UNDASHED"
  by (simp add: var_defs)

theorem DASHED_undash_not_DASHED :
"x \<in> UNDASHED \<Longrightarrow> undash x \<notin> DASHED"
  by (simp add: var_defs)

theorem DASHED_dash_DASHED_TWICE :
"x \<in> DASHED \<Longrightarrow> dash x \<in> DASHED_TWICE"
  by (simp add: var_defs)

theorem DASHED_TWICE_dash_DASHED_THRICE :
"x \<in> DASHED_TWICE \<Longrightarrow> dash x \<in> DASHED_THRICE"
  by (simp add: var_defs)

theorem DASHED_dash_not_DASHED :
"x \<in> DASHED \<Longrightarrow> x\<acute> \<notin> DASHED"
  by (simp add: var_defs)

theorem DASHED_TWICE_undash_DASHED :
"x \<in> DASHED_TWICE \<Longrightarrow> undash x \<in> DASHED"
  by (simp add: var_defs)

theorem DASHED_THRICE_undash_DASHED_TWICE :
"x \<in> DASHED_THRICE \<Longrightarrow> undash x \<in> DASHED_TWICE"
  by (simp add: var_defs)

theorem DASHED_TWICE_undash_not_DASHED_TWICE :
"x \<in> DASHED_TWICE \<Longrightarrow> undash x \<notin> DASHED_TWICE"
  by (simp add: var_defs)

theorem DASHED_THRICE_undash_not_DASHED_THRICE :
"x \<in> DASHED_THRICE \<Longrightarrow> undash x \<notin> DASHED_THRICE"
  by (simp add: var_defs)

lemma DASHED_TWICE_NON_REL_VAR:
  "x \<in> DASHED_TWICE \<Longrightarrow> x \<in> NON_REL_VAR"
  by (simp add:var_defs)

lemma DASHED_THRICE_NON_REL_VAR:
  "x \<in> DASHED_THRICE \<Longrightarrow> x \<in> NON_REL_VAR"
  by (simp add:var_defs)

lemma NON_REL_VAR_dash_NON_REL_VAR:
  "x \<in> NON_REL_VAR \<Longrightarrow> x\<acute> \<in> NON_REL_VAR"
  by (simp add:var_defs)

lemma UNDASHED_not_NON_REL_VAR:
  "x \<in> UNDASHED \<Longrightarrow> x \<notin> NON_REL_VAR"
  by (simp add:var_defs)

lemma DASHED_not_NON_REL_VAR:
  "x \<in> DASHED \<Longrightarrow> x \<notin> NON_REL_VAR"
  by (simp add:var_defs)

lemma NOSUB_dash:
  "x \<in> NOSUB \<Longrightarrow> x\<acute> \<in> NOSUB"
  by (simp add:var_defs)

lemma NOSUB_undash_DASHED:
  "\<lbrakk> x \<in> NOSUB; x \<in> DASHED \<rbrakk> \<Longrightarrow> x~ \<in> NOSUB"
  by (simp add:var_defs)

lemma NOSUB_undash_DASHED_TWICE:
  "\<lbrakk> x \<in> NOSUB; x \<in> DASHED_TWICE \<rbrakk> \<Longrightarrow> x~ \<in> NOSUB"
  by (simp add:var_defs)

lemma WITHSUB_dash:
  "x \<in> WITHSUB(n) \<Longrightarrow> x\<acute> \<in> WITHSUB(n)"
  by (simp add:var_defs)

lemma WITHSUB_undash_DASHED:
  "\<lbrakk> x \<in> WITHSUB(n); x \<in> DASHED \<rbrakk> \<Longrightarrow> x~ \<in> WITHSUB(n)"
  by (simp add:var_defs)

lemma WITHSUB_undash_DASHED_TWICE:
  "\<lbrakk> x \<in> WITHSUB(n); x \<in> DASHED_TWICE \<rbrakk> \<Longrightarrow> x~ \<in> WITHSUB(n)"
  by (simp add:var_defs)

theorem in_UNDASHED :
"in vs \<subseteq> UNDASHED"
  by (simp add: in_vars_def)

theorem out_DASHED :
"out vs \<subseteq> DASHED"
  by (simp add: out_vars_def)

theorem in_of_UNDASHED :
"vs \<subseteq> UNDASHED \<Longrightarrow> in vs = vs"
  by (auto simp add: var_defs)

theorem in_of_DASHED :
"vs \<subseteq> DASHED \<Longrightarrow> in vs = {}"
  by (auto simp add: var_defs)

theorem out_of_UNDASHED :
"vs \<subseteq> UNDASHED \<Longrightarrow> out vs = {}"
  by (auto simp add: var_defs)

theorem out_of_DASHED :
"vs \<subseteq> DASHED \<Longrightarrow> out vs = vs"
  by (auto simp add: var_defs)

lemma homl_REL_VAR:
  "vs \<subseteq> REL_VAR \<Longrightarrow> homl vs \<subseteq> REL_VAR"
  by (auto simp add:var_defs)

lemma homr_REL_VAR:
  "vs \<subseteq> REL_VAR \<Longrightarrow> homr vs \<subseteq> REL_VAR"
  by (auto simp add:var_defs)

theorem not_dash_member_in :
"\<not> dash x \<in> in a"
  by (simp add: var_defs)

theorem not_dash_dash_member_out :
"\<not> dash (dash x) \<in> out a"
  by (simp add: var_defs)

lemma undash_image_member :
  "dash x \<in> xs \<Longrightarrow> x \<in> undash ` xs"
  apply (auto simp add:var_defs)
  apply (rule)
  apply (auto)
done

lemma dash_image_member :
  "\<lbrakk> x \<in> DASHED; undash x \<in> xs \<rbrakk> \<Longrightarrow> x \<in> dash ` xs"
  apply (case_tac x)
  apply (auto simp add:var_defs image_iff)
  apply (rule)
  apply (auto)
done

lemma out_member :
  "\<lbrakk> x \<in> DASHED; x \<in> vs \<rbrakk> \<Longrightarrow> x \<in> out vs"
  by (simp add:var_defs)

lemma in_member :
  "\<lbrakk> x \<in> UNDASHED; x \<in> vs \<rbrakk> \<Longrightarrow> x \<in> in vs"
  by (simp add:var_defs)

theorems var_member =
  UNDASHED_not_DASHED
  UNDASHED_not_DASHED_TWICE
  DASHED_not_DASHED_TWICE
  DASHED_not_DASHED_THRICE
  DASHED_not_DASHED_THRICE
  UNDASHED_dash_DASHED
  UNDASHED_dash_not_UNDASHED
  DASHED_undash_UNDASHED
  DASHED_undash_not_DASHED
  DASHED_dash_DASHED_TWICE
  DASHED_TWICE_dash_DASHED_THRICE
  DASHED_TWICE_undash_DASHED
  DASHED_THRICE_undash_DASHED_TWICE
  DASHED_TWICE_undash_not_DASHED_TWICE
  DASHED_THRICE_undash_not_DASHED_THRICE
  DASHED_TWICE_NON_REL_VAR
  DASHED_THRICE_NON_REL_VAR
  NON_REL_VAR_dash_NON_REL_VAR
  UNDASHED_not_NON_REL_VAR
  DASHED_not_NON_REL_VAR
  NOSUB_dash
  NOSUB_undash_DASHED
  NOSUB_undash_DASHED_TWICE
  WITHSUB_dash
  WITHSUB_undash_DASHED
  WITHSUB_undash_DASHED_TWICE
  in_UNDASHED
  out_DASHED
  in_of_UNDASHED
  in_of_DASHED
  out_of_UNDASHED
  out_of_DASHED
  homl_REL_VAR
  homr_REL_VAR
  not_dash_member_in
  not_dash_dash_member_out
  undash_image_member
  dash_image_member
  out_member
  in_member

declare var_member [intro, simp]

subsubsection {* Contradiction Theorems *}

theorem UNDASHED_DASHED_contra :
"\<lbrakk>x \<in> UNDASHED; x \<in> DASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem UNDASHED_DASHED_TWICE_contra :
"\<lbrakk>x \<in> UNDASHED; x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem DASHED_DASHED_TWICE_contra :
"\<lbrakk>x \<in> DASHED; x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem UNDASHED_DASHED_THRICE_contra :
"\<lbrakk>x \<in> UNDASHED; x \<in> DASHED_THRICE\<rbrakk> \<Longrightarrow> False"
  by (simp add: var_defs)

theorem DASHED_DASHED_THRICE_contra :
"\<lbrakk>x \<in> DASHED; x \<in> DASHED_THRICE\<rbrakk> \<Longrightarrow> False"
  by (simp add: var_defs)

theorem DASHED_TWICE_DASHED_THRICE_contra :
"\<lbrakk>x \<in> DASHED_TWICE; x \<in> DASHED_THRICE\<rbrakk> \<Longrightarrow> False"
  by (simp add: var_defs)

theorem UNDASHED_eq_dash_contra :
"\<lbrakk>x = dash y; x \<in> UNDASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem undash_eq_dash_contra1 :
"\<lbrakk>undash x = dash y; x \<in> DASHED\<rbrakk> \<Longrightarrow> False"
  by (metis DASHED_undash_UNDASHED UNDASHED_eq_dash_contra)

theorem undash_eq_dash_contra2 :
"\<lbrakk>undash x = dash y; x \<in> DASHED_TWICE; y \<in> DASHED\<rbrakk> \<Longrightarrow> False"
  by (metis DASHED_TWICE_undash_DASHED DASHED_dash_not_DASHED)

theorem dash_eq_undash_contra1 :
"\<lbrakk>dash x = undash y; y \<in> DASHED\<rbrakk> \<Longrightarrow> False"
  by (metis undash_eq_dash_contra1)

theorem dash_eq_undash_contra2 :
"\<lbrakk>dash x = undash y; x \<in> DASHED; y \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> False"
  by (metis undash_eq_dash_contra2)

lemma dashed_twice_contras [simp]:
  "x\<acute>\<acute> \<notin> D\<^sub>0" "x\<acute>\<acute> \<notin> D\<^sub>1"
  by (auto simp add:var_defs)

lemma dashed_thrice_contras [simp]:
  "x\<acute>\<acute>\<acute> \<notin> D\<^sub>0" "x\<acute>\<acute>\<acute> \<notin> D\<^sub>1" "x\<acute>\<acute>\<acute> \<notin> D\<^sub>2"
  by (auto simp add:var_defs)

theorems var_contra =
  UNDASHED_DASHED_contra
  UNDASHED_DASHED_TWICE_contra
  DASHED_DASHED_TWICE_contra
  UNDASHED_DASHED_THRICE_contra
  DASHED_DASHED_THRICE_contra
  DASHED_TWICE_DASHED_THRICE_contra
  UNDASHED_eq_dash_contra
  undash_eq_dash_contra1
  undash_eq_dash_contra2
  dash_eq_undash_contra1
  dash_eq_undash_contra2

declare var_contra [dest]

subsubsection {* Simplification Theorems *}


lemma UNDASHED_nempty: "UNDASHED \<noteq> {}"
  apply (auto simp add:var_defs)
  apply (rule_tac x="MkVar (MkName ''x'' 0 NoSub) someType False" in exI)
  apply (simp)
done

lemma DASHED_nempty: "DASHED \<noteq> {}"
  apply (auto simp add:var_defs)
  apply (rule_tac x="MkVar (MkName ''x'' 1 NoSub) someType False" in exI)
  apply (simp)
done

lemma DASHED_TWICE_nempty: "DASHED_TWICE \<noteq> {}"
  apply (auto simp add:var_defs)
  apply (rule_tac x="MkVar (MkName ''x'' 2 NoSub) someType False" in exI)
  apply (simp)
done

lemma dash_neq_reduce:
  "x\<acute> \<noteq> y\<acute> \<longleftrightarrow> x \<noteq> y"
apply (simp add: var_defs)
apply (case_tac x)
apply (case_tac y)
apply (auto)
apply (rename_tac n1 n2)
apply (case_tac n1)
apply (case_tac n2)
apply (simp)
done

theorem dash_uniqs:
"x \<noteq> dash x" "dash x \<noteq> x"
"x \<noteq> dash (dash x)" "dash (dash x) \<noteq> x"
"dash x \<noteq> dash (dash x)" "dash (dash x) \<noteq> dash x"
"x \<noteq> x\<acute>\<acute>\<acute>" "x\<acute>\<acute>\<acute> \<noteq> x"
"x\<acute> \<noteq> x\<acute>\<acute>\<acute>" "x\<acute>\<acute>\<acute> \<noteq> x\<acute>"
"x\<acute>\<acute> \<noteq> x\<acute>\<acute>\<acute>" "x\<acute>\<acute>\<acute> \<noteq> x\<acute>\<acute>"
apply (simp add: var_defs, case_tac x, auto)+
done

text {* I had to add a second assumption to the following lemma. *}

lemma sub_uniqs:
"\<lbrakk>x \<in> NOSUB; n \<noteq> NoSub\<rbrakk> \<Longrightarrow> x\<^bsub>n\<^esub> \<noteq> x"
"\<lbrakk>x \<in> NOSUB; n \<noteq> NoSub\<rbrakk> \<Longrightarrow> x \<noteq> x\<^bsub>n\<^esub>"
apply (simp_all add: var_defs)
apply (unfold chsub_def)
apply (case_tac x)
apply (clarsimp)
apply (case_tac x)
apply (clarsimp)
done

theorem dash_name_str:
  "name_str (name (dash x)) = name_str (name x)"
  by (simp add:var_defs)

theorem dash_dashes:
  "dashes (name (dash x)) = dashes (name x) + 1"
  by (simp add:var_defs)

theorem dash_subscript:
  "subscript (name (dash x)) = subscript (name x)"
  by (simp add:var_defs)

theorem dash_undash_DASHED :
"x \<in> DASHED \<Longrightarrow> dash (undash x) = x"
apply (simp add: var_defs)
done

theorem dash_undash_DASHED_TWICE :
"x \<in> DASHED_TWICE \<Longrightarrow> dash (undash x) = x"
apply (simp add: var_defs)
done

theorem undash_dash :
"undash (dash x) = x"
  by (auto simp add: var_defs)

lemma UNDASHED_undash_elim [elim]:
  "\<lbrakk> x \<in> UNDASHED; \<And> y. \<lbrakk> x = undash y; y \<in> DASHED \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis UNDASHED_dash_DASHED undash_dash)

lemma DASHED_dash_elim [elim]:
  "\<lbrakk> x \<in> DASHED; \<And> y. \<lbrakk> x = dash y; y \<in> UNDASHED \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis DASHED_undash_UNDASHED dash_undash_DASHED)

lemma DASHED_TWICE_dash_elim [elim]:
  "\<lbrakk> x \<in> DASHED_TWICE; \<And> y. \<lbrakk> x = dash y; y \<in> DASHED \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis DASHED_TWICE_undash_DASHED dash_undash_DASHED_TWICE)

lemma dash_DASHED_TWICE_elim [elim]: "\<lbrakk> x\<acute> \<in> DASHED_TWICE; x \<in> DASHED \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:var_defs)

lemma dash_UNDASHED_image:
"dash ` UNDASHED = DASHED"
  by auto

lemma dash_DASHED_image:
"dash ` DASHED = DASHED_TWICE"
  by auto

lemma undash_DASHED_image:
"undash ` DASHED = UNDASHED"
  by auto

lemma undash_DASHED_TWICE_image:
"undash ` DASHED_TWICE = DASHED"
  by (auto)

lemma dash_undash_image:
"vs \<subseteq> DASHED \<Longrightarrow> dash ` undash ` vs = vs"
  by (auto simp add:image_def dash_undash_DASHED, metis dash_undash_DASHED set_mp)

lemma undash_dash_image:
"undash ` dash ` vs = vs"
  by (auto simp add: image_def undash_dash)

theorem undash_image_inter:
  assumes "vs1 \<subseteq> DASHED" "vs2 \<subseteq> DASHED"
  shows "undash ` (vs1 \<inter> vs2) = undash ` vs1 \<inter> undash ` vs2"
  using assms
  by (auto, metis IntI UnI1 Un_absorb1 dash_undash_DASHED imageI)

theorem dash_image_inter:
  shows "dash ` (vs1 \<inter> vs2) = dash ` vs1 \<inter> dash ` vs2"
  apply (auto)
  apply (metis Int_iff imageI undash_dash)
done

lemma dash_inv_into [simp]:
  "x \<in> DASHED \<Longrightarrow> inv_into UNDASHED dash x = undash x"
  by (metis (lifting) dash_UNDASHED_image f_inv_into_f undash_dash)

theorem in_empty :
"in {} = {}"
  by (simp add:var_defs)

theorem out_empty :
"out {} = {}"
  by (simp add:var_defs)

lemma nrel_empty:
  "nrel {} = {}"
  by (auto simp add:var_defs)

theorem in_in :
"in (in vs) = in vs"
  by (auto simp add: var_defs)

theorem out_out :
"out (out vs) = out vs"
  by (auto simp add: var_defs)

lemma nrel_nrel:
  "nrel (nrel vs) = nrel vs"
  by (auto simp add:var_defs)

theorem in_out :
"in (out vs) = {}"
  by (auto simp add: var_defs)

theorem out_in :
"out (in vs) = {}"
  by (auto simp add: var_defs)

lemma nrel_in:
  "nrel (in vs) = {}"
  by (auto simp add:var_defs)

lemma nrel_out:
  "nrel (out vs) = {}"
  by (auto simp add:var_defs)

lemma in_nrel:
  "in (nrel vs) = {}"
  by (auto simp add:var_defs)

lemma out_nrel:
  "out (nrel vs) = {}"
  by (auto simp add:var_defs)

lemma in_dash :
"in (dash ` vs) = {}"
  by (auto simp add: var_defs)

lemma in_undash :
"in (undash ` out vs) = undash ` (out vs)"
  by (auto simp add: var_defs)

lemma out_dash :
"out (dash ` vs) = dash ` (in vs)"
  by (auto simp add: var_defs)

lemma homl_homl:
  "homl (homl vs) = homl vs"
  by (auto simp add:var_defs)

lemma homl_empty:
  "homl {} = {}"
  by (auto simp add:var_defs)

lemma homr_empty:
  "homr {} = {}"
  by (auto simp add:var_defs)

lemma in_homl:
  "in (homl vs) = in vs"
  by (auto simp add:var_defs)

lemma out_homl:
  "out (homl vs) = dash ` in vs"
  by (auto simp add:var_defs)

lemma nrel_homl:
  "nrel (homl vs) = nrel vs"
  by (auto simp add:var_defs)

lemma homl_out:
  "homl (out vs) = {}"
  by (auto simp add:var_defs)

lemma homr_homr:
  "homr (homr vs) = homr vs"
  by (auto simp add:var_defs)

lemma in_homr:
  "in (homr vs) = undash ` out vs"
  by (auto simp add:var_defs)

lemma out_homr:
  "out (homr vs) = out vs"
  by (auto simp add:var_defs)

lemma nrel_homr:
  "nrel (homr vs) = nrel vs"
  by (auto simp add:var_defs)

lemma homr_in:
  "homr (in vs) = {}"
  by (auto simp add:var_defs)

lemma in_out_disj :
"(in vs1) \<inter> (out vs2) = {}"
  by (auto simp add: var_defs)

theorem in_out_union [intro] :
"vs \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow>
 (in vs) \<union> (out vs) = vs"
  by (auto simp add: var_defs)

theorem HOMOGENEOUS_undash_out:
  "HOMOGENEOUS vs \<Longrightarrow> undash ` out vs = in vs"
  by (simp add: HOMOGENEOUS_def COMPOSABLE_def undash_dash_image)

theorem HOMOGENEOUS_dash_in:
  "HOMOGENEOUS vs \<Longrightarrow> dash ` in vs = out vs"
  by (simp add: HOMOGENEOUS_def COMPOSABLE_def)

theorem in_out_UNDASHED_DASHED:
  "in UNDASHED = UNDASHED"
  "out UNDASHED = {}"
  "in DASHED = {}"
  "out DASHED = DASHED"
  by (auto simp add:var_defs)

lemma in_VAR:
  "in VAR = D\<^sub>0"
  by (auto simp add:var_defs)

lemma out_VAR:
  "out VAR = D\<^sub>1"
  by (auto simp add:var_defs)

lemma nrel_VAR:
  "nrel VAR = NON_REL_VAR"
  by (auto simp add:var_defs)

lemma in_NON_REL_VAR:
  "in NON_REL_VAR = {}"
  by (auto simp add:var_defs)

lemma out_NON_REL_VAR:
  "out NON_REL_VAR = {}"
  by (auto simp add:var_defs)

lemma nrel_NON_REL_VAR:
  "nrel NON_REL_VAR = NON_REL_VAR"
  by (auto simp add:var_defs)

theorem UNDASHED_DASHED_inter:
  "UNDASHED \<inter> DASHED = {}"
  "DASHED \<inter> UNDASHED = {}"
  "UNDASHED \<inter> DASHED_TWICE = {}"
  "DASHED_TWICE \<inter> UNDASHED = {}"
  "DASHED \<inter> DASHED_TWICE = {}"
  "DASHED_TWICE \<inter> DASHED = {}"
  "DASHED \<inter> NON_REL_VAR = {}"
  "NON_REL_VAR \<inter> DASHED = {}"
  "UNDASHED \<inter> NON_REL_VAR = {}"
  "NON_REL_VAR \<inter> UNDASHED = {}"
  "(- DASHED) \<inter> NON_REL_VAR = NON_REL_VAR"
  "NON_REL_VAR \<inter> - DASHED = NON_REL_VAR"
  "(- UNDASHED) \<inter> NON_REL_VAR = NON_REL_VAR"
  "NON_REL_VAR \<inter> (- UNDASHED) = NON_REL_VAR"
  "((VAR - UNDASHED) \<inter> (VAR - DASHED)) = NON_REL_VAR"
  "- NON_REL_VAR = REL_VAR"
  by (auto simp add:var_defs)

theorem UNDASHED_DASHED_minus:
  "UNDASHED - DASHED       = UNDASHED"
  "DASHED - UNDASHED       = DASHED"
  "DASHED_TWICE - UNDASHED = DASHED_TWICE"
  "UNDASHED - DASHED_TWICE = UNDASHED"
  "DASHED_TWICE - DASHED   = DASHED_TWICE"
  "DASHED - DASHED_TWICE   = DASHED"
  "UNDASHED - NON_REL_VAR  = UNDASHED"
  "DASHED   - NON_REL_VAR  = DASHED"
  "DASHED_TWICE - NON_REL_VAR = {}"
  "NON_REL_VAR - UNDASHED  = NON_REL_VAR"
  "NON_REL_VAR - DASHED    = NON_REL_VAR"
  "UNDASHED - VAR          = {}"
  "DASHED - VAR            = {}"
  "UNDASHED - VAR          = {}"
  "NON_REL_VAR - VAR       = {}"
  by (auto simp add:var_defs)

lemma var_name_uniq [simp]:
  "name x \<noteq> name y \<Longrightarrow> x \<noteq> y"
  by (auto)

lemma var_type_uniq [simp]:
  "vtype x \<noteq> vtype y \<Longrightarrow> x \<noteq> y"
  by auto

lemma var_aux_uniq [simp]:
  "aux x \<noteq> aux y \<Longrightarrow> x \<noteq> y"
  by auto

lemma inter_not_DASHED:
  "vs \<inter> (- D\<^sub>1) = in vs \<union> nrel vs"
  by (auto simp add:var_defs)

lemma UNDASHED_minus_in:
  "D\<^sub>0 - in vs = D\<^sub>0 - vs"
  by (auto simp add:var_defs)

theorems var_simps =
  UNDASHED_nempty
  DASHED_nempty
  DASHED_TWICE_nempty
  dash_uniqs
  dash_undash_DASHED
  dash_undash_DASHED_TWICE
  dash_dashes
  dash_name_str
  dash_subscript
  undash_dash
  dash_UNDASHED_image
  dash_DASHED_image
  undash_DASHED_image
  undash_DASHED_TWICE_image
  dash_undash_image
  undash_dash_image
  dash_image_inter
  undash_image_inter
  in_empty
  out_empty
  nrel_empty
  in_in
  out_out
  nrel_nrel
  in_out
  out_in
  nrel_in
  nrel_out
  in_nrel
  out_nrel
  in_VAR
  out_VAR
  nrel_VAR
  in_NON_REL_VAR
  out_NON_REL_VAR
  nrel_NON_REL_VAR
  in_dash
  in_undash
  out_dash
  homl_homl
  in_homl
  out_homl
  nrel_homl
  homl_empty
  homr_empty
  homl_out
  homl_out
  homr_homr
  in_homr
  out_homr
  nrel_homr
  homr_in
  in_out_disj
  in_out_union
  in_out_UNDASHED_DASHED
  UNDASHED_DASHED_inter
  UNDASHED_DASHED_minus
  HOMOGENEOUS_undash_out
  HOMOGENEOUS_dash_in
  dash_neq_reduce
  sub_uniqs

declare var_simps [simp]

subsubsection {* Injectivity Theorems *}

theorem dash_inj [simp]:
"inj_on dash vs"
apply (rule inj_onI)
apply (metis dash_neq_reduce)
done

theorem dash_elim [elim] :
  "\<lbrakk>dash x = dash y; x = y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
 by (metis undash_dash)

theorem undash_inj_on [simp]:
"inj_on undash (- UNDASHED)"
apply (rule inj_onI)
apply (simp add: var_defs)
apply (case_tac x)
apply (case_tac y)
apply (clarsimp)
apply (rename_tac n1 n2)
apply (case_tac n1)
apply (case_tac n2)
apply (clarsimp)
apply (rename_tac d1 d2)
apply (metis Suc_pred)
done

theorem undash_inj_on_DASHED [simp]:
"inj_on undash DASHED"
apply (rule inj_onI)
apply (simp add: var_defs)
apply (case_tac x)
apply (case_tac y)
apply (clarsimp)
apply (rename_tac n1 n2)
apply (case_tac n1)
apply (case_tac n2)
apply (clarsimp)
done

theorem undash_inj_on_DASHED_TWICE [simp]:
"inj_on undash DASHED_TWICE"
apply (rule inj_onI)
apply (simp add: var_defs)
apply (case_tac x)
apply (case_tac y)
apply (clarsimp)
apply (rename_tac n1 n2)
apply (case_tac n1)
apply (case_tac n2)
apply (clarsimp)
done

theorem dash_strict_mono [simp]:
"strict_mono dash"
apply (simp add: strict_mono_def)
done

subsubsection {* Distribution Theorems *}

(*
theorem dash_inter_distr :
"dash ` (vs1 \<inter> vs2) = (dash ` vs1) \<inter> (dash ` vs2)"
apply (auto intro!: image_Int dash_inj)
done

theorem dash_union_distr :
"dash ` (vs1 \<union> vs2) = (dash ` vs1) \<union> (dash ` vs2)"
apply (auto intro!: image_Un)
done
*)

theorem override_on_UNIV [simp]:
  "f \<oplus> g on UNIV = g"
  by (simp add:override_on_def)

theorem in_vars_union :
"in (vs1 \<union> vs2) = (in vs1) \<union> (in vs2)"
  by (auto simp add: var_defs)

theorem in_vars_inter :
"in (vs1 \<inter> vs2) = (in vs1) \<inter> (in vs2)"
  by (auto simp add: var_defs)

theorem in_vars_diff :
"in (vs1 - vs2) = (in vs1) - (in vs2)"
  by (auto simp add: var_defs)

theorem in_vars_insert1 :
"v \<in> UNDASHED \<Longrightarrow> in (insert v vs) = insert v (in vs)"
  by (auto simp add: var_defs)

theorem in_vars_insert2 :
"v \<in> DASHED \<Longrightarrow> in (insert v vs) = in vs"
  by (auto simp add: var_defs)

theorem out_vars_union :
"out (vs1 \<union> vs2) = (out vs1) \<union> (out vs2)"
  by (auto simp add: var_defs)

theorem out_vars_inter :
"out (vs1 \<inter> vs2) = (out vs1) \<inter> (out vs2)"
  by (auto simp add: var_defs)

theorem out_vars_diff :
"out (a1 - a2) = (out a1) - (out a2)"
  by (auto simp add: var_defs)

theorem out_vars_insert1 :
"v \<in> DASHED \<Longrightarrow> out (insert v vs) = insert v (out vs)"
  by (auto simp add: var_defs)

theorem out_vars_insert2 :
"v \<in> UNDASHED \<Longrightarrow> out (insert v vs) = out vs"
  by (auto simp add: var_defs)

lemma nrel_vars_uminus:
  "nrel (- vs) = NON_REL_VAR - nrel vs"
  by (auto simp add:var_defs)

lemma nrel_vars_minus:
  "nrel (vs1 - vs2) = nrel vs1 - nrel vs2"
  by (auto simp add:var_defs)

lemma nrel_vars_inter:
  "nrel (vs1 \<inter> vs2) = nrel vs1 \<inter> nrel vs2"
  by (auto simp add:nrel_vars_def)

lemma nrel_vars_union:
  "nrel (vs1 \<union> vs2) = nrel vs1 \<union> nrel vs2"
  by (auto simp add:nrel_vars_def)

lemma nrel_insert_UNDASHED:
  "x \<in> UNDASHED \<Longrightarrow> nrel (insert x xs) = nrel xs"
  by (auto simp add:var_defs)

lemma nrel_insert_DASHED:
  "x \<in> DASHED \<Longrightarrow> nrel (insert x xs) = nrel xs"
  by (auto simp add:var_defs)

lemma nrel_insert_NON_REL_VAR:
  "x \<in> NON_REL_VAR \<Longrightarrow> nrel (insert x xs) = insert x (nrel xs)"
  by (auto simp add:var_defs)

lemma homl_union:
  "homl (xs \<union> ys) = homl xs \<union> homl ys"
  by (auto simp add:homl_def in_vars_union nrel_vars_union)

lemma homr_union:
  "homr (xs \<union> ys) = homr xs \<union> homr ys"
  by (auto simp add:homr_def out_vars_union nrel_vars_union)

lemma homl_inter:
  "homl (xs \<inter> ys) = homl xs \<inter> homl ys"
  apply (auto simp add:homl_def in_vars_inter nrel_vars_inter)
  apply (force simp add:var_defs)+
done

lemma homl_insert_UNDASHED:
  "x \<in> UNDASHED \<Longrightarrow> homl (insert x xs) = insert x (insert x\<acute> (homl xs))"
  by (auto simp add:homl_def out_vars_insert2 nrel_insert_UNDASHED in_vars_insert1)

lemma homl_insert_DASHED:
  "x \<in> DASHED \<Longrightarrow> homl (insert x xs) = homl xs"
  by (simp add:homl_def in_vars_insert2 nrel_insert_DASHED)

lemma homl_insert_NON_REL_VAR:
  "x \<in> NON_REL_VAR \<Longrightarrow> homl (insert x xs) = insert x (homl xs)"
  by (auto simp add:var_defs)

lemma homr_insert_UNDASHED:
  "x \<in> UNDASHED \<Longrightarrow> homr (insert x xs) = homr xs"
  by (simp add:homr_def out_vars_insert2 nrel_insert_UNDASHED)

lemma homr_insert_DASHED:
  "x \<in> DASHED \<Longrightarrow> homr (insert x xs) = insert x~ (insert x (homr xs))"
  by (auto simp add:homr_def out_vars_insert1 nrel_insert_DASHED)

lemma homr_insert_NON_REL_VAR:
  "x \<in> NON_REL_VAR \<Longrightarrow> homr (insert x xs) = insert x (homr xs)"
  by (auto simp add:var_defs)

theorem dash_image_union:
  "dash ` (vs1 \<union> vs2) = dash ` vs1 \<union> dash ` vs2"
  by (auto)

theorem undash_image_union:
  "undash ` (vs1 \<union> vs2) = undash ` vs1 \<union> undash ` vs2"
  by (auto)

theorem dash_image_minus:
  "dash ` (vs1 - vs2) = (dash ` vs1) - (dash ` vs2)"
  by (auto)

theorem undash_image_minus:
 "\<lbrakk> vs1 \<subseteq> DASHED; vs2 \<subseteq> DASHED \<rbrakk> \<Longrightarrow>
  undash ` (vs1 - vs2) = (undash ` vs1) - (undash ` vs2)"
  by (metis dash_image_minus dash_undash_image undash_dash_image)

theorems var_dist =
(* dash_inter_distr
  dash_unsion_distr *)
  in_vars_union
  in_vars_inter
  in_vars_diff
  in_vars_insert1
  in_vars_insert2
  out_vars_union
  out_vars_inter
  out_vars_diff
  out_vars_insert1
  out_vars_insert2
  nrel_vars_union
  nrel_vars_inter
  nrel_vars_uminus
  nrel_vars_minus
  nrel_insert_UNDASHED
  nrel_insert_DASHED
  nrel_insert_NON_REL_VAR
  homl_union
  homr_union
  homl_inter
  homl_insert_UNDASHED
  homl_insert_DASHED
  homl_insert_NON_REL_VAR
  homr_insert_UNDASHED
  homr_insert_DASHED
  homr_insert_NON_REL_VAR
  dash_image_union
  undash_image_union
  dash_image_minus
  undash_image_minus

subsubsection {* Composability Theorems *}

lemma comp_vars_undash [elim]:
  "\<lbrakk> COMPOSABLE vs1 vs2; v \<in> vs2; v \<in> UNDASHED; dash v \<in> vs1 \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (auto simp add:COMPOSABLE_def)
  apply (metis Int_iff imageI in_vars_def out_vars_def)
done

lemma comp_alphabet_dash [elim]:
  "\<lbrakk> COMPOSABLE vs1 vs2; dash v \<in> vs1; v \<in> UNDASHED; v \<in> vs2 \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (auto simp add:COMPOSABLE_def)
  apply (auto simp add: in_vars_def out_vars_def)
done

lemma hom_alphabet_undash [elim]:
  "\<lbrakk> HOMOGENEOUS vs; v \<in> vs; v \<in> UNDASHED; dash v \<in> vs \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:HOMOGENEOUS_def)

lemma hom_alphabet_dash [elim]:
  "\<lbrakk> HOMOGENEOUS vs; dash v \<in> vs; v \<in> UNDASHED; v \<in> vs \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:HOMOGENEOUS_def)

subsubsection {* HOMOGENEOUS variable sets *}

theorem HOMOGENEOUS_empty [simp]:
  "HOMOGENEOUS {}"
  by (simp add: HOMOGENEOUS_def COMPOSABLE_def)

lemma HOMOGENEOUS_REL_VAR [simp]:
  "HOMOGENEOUS (UNDASHED \<union> DASHED)"
  by (simp add:HOMOGENEOUS_def COMPOSABLE_def var_dist)

lemma HOMOGENEOUS_homl [simp]:
  "HOMOGENEOUS (homl vs)"
  apply (unfold HOMOGENEOUS_def COMPOSABLE_def homl_def)
  apply (simp add:var_dist)
done

lemma HOMOGENEOUS_homr [simp]:
  "HOMOGENEOUS (homr vs)"
  apply (unfold HOMOGENEOUS_def COMPOSABLE_def homr_def)
  apply (simp add:var_dist)
  apply (auto simp add: var_defs)
done

lemma HOMOGENEOUS_insert [simp]:
  "\<lbrakk>x \<in> UNDASHED; HOMOGENEOUS vs \<rbrakk> \<Longrightarrow> HOMOGENEOUS (insert x (insert x\<acute> vs))"
  by (simp add: HOMOGENEOUS_def COMPOSABLE_def var_defs)

lemma HOMOGENEOUS_insert' [simp]:
  "\<lbrakk>x \<in> UNDASHED; HOMOGENEOUS vs \<rbrakk> \<Longrightarrow> HOMOGENEOUS (insert x\<acute> (insert x vs))"
  by (simp add: HOMOGENEOUS_def COMPOSABLE_def var_defs)

lemma HOMOGENEOUS_union [simp]:
  "\<lbrakk>HOMOGENEOUS vs1; HOMOGENEOUS vs2\<rbrakk> \<Longrightarrow> HOMOGENEOUS (vs1 \<union> vs2)"
  by (auto simp add: HOMOGENEOUS_def COMPOSABLE_def var_defs)

lemma HOMOGENEOUS_inter [simp]:
  "\<lbrakk>HOMOGENEOUS vs1; HOMOGENEOUS vs2\<rbrakk> \<Longrightarrow> HOMOGENEOUS (vs1 \<inter> vs2)"
  apply (simp add: HOMOGENEOUS_def COMPOSABLE_def)
  apply (simp add: var_dist)
done

lemma HOMOGENEOUS_minus [simp]:
  "\<lbrakk> HOMOGENEOUS vs1; HOMOGENEOUS vs2 \<rbrakk> \<Longrightarrow> HOMOGENEOUS (vs1 - vs2)"
   apply (unfold HOMOGENEOUS_def COMPOSABLE_def)
   apply (simp add:var_dist)
done

lemma HOMOGENEOUS_out_unprimed:
  "\<lbrakk> HOMOGENEOUS xs; x \<in> out(xs) \<rbrakk> \<Longrightarrow> x~ \<in> xs"
  by (metis HOMOGENEOUS_undash_out IntD1 imageI in_vars_def)

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

subsubsection {* Subscript Properties *}

lemma vchsub_vtype [simp] :
  "vtype x\<^bsub>n\<^esub> = vtype x"
apply (case_tac x)
apply (clarsimp)
done

lemma vchsub_vdashes [simp]:
  "vdashes x\<^bsub>n\<^esub> = vdashes x"
apply (case_tac x)
apply (simp add: vchsub_def chsub_def)
done

lemma vsub_aux [simp] :
  "aux x\<^bsub>n\<^esub> = aux x"
apply (case_tac x)
apply (clarsimp)
done

lemma vsub_NOSUB [simp]:
  "x \<in> NOSUB \<Longrightarrow> vsub x\<^bsub>n\<^esub> = n"
apply (case_tac x)
apply (unfold vchsub_def)
apply (clarsimp)
apply (unfold chsub_def)
apply (clarsimp)
apply (simp add: NOSUB_def)
done

subsubsection {* Fresh variables *}

text {* This proof uses the infinitness of @{term "name"} proof to demonstrate
that, given a finite set of variables, we can always generate a fresh variable
with any given type and auxness *}

theorem fresh_var: "\<exists>x::'m uvar. x \<notin> \<langle>xs\<rangle>\<^sub>f \<and> vtype x = t \<and> aux x = s"
proof -

  obtain n where "n \<notin> name ` \<langle>xs\<rangle>\<^sub>f"
    by (force intro!: ex_new_if_finite infinite_uname)
  with assms show ?thesis
    apply (rule_tac x="MkVar n t s" in exI)
    apply (simp)
    apply (metis MkVar_name imageI)
  done
qed
end
