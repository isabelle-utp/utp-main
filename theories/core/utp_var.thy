(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_var.thy                                                          *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Variables *}

theory utp_var
imports utp_names utp_value
begin

text {* A variable constists of a name, type and a flag denoting if it is a auxiliary
variable or not. *}


(* datatype 'VALUE VAR = MkVar NAME "'VALUE UTYPE" bool *)

(*
primrec var_name :: "'VALUE VAR \<Rightarrow> NAME" ("name") where
"var_name (MkVar n t d) = n"

primrec var_type :: "'VALUE VAR \<Rightarrow> 'VALUE UTYPE" ("vtype") where
"var_type (MkVar n t d) = t"

primrec var_aux :: "'VALUE VAR \<Rightarrow> bool" ("aux") where
"var_aux (MkVar n t d) = d"

lemma MkVar_inverse [simp]: 
  "MkVar (name x) (vtype x) (aux x) = x"
  by (case_tac x, simp)

lemma VAR_eq_intro [intro]:
  "\<lbrakk> name x = name y; vtype x = vtype y; aux x = aux y \<rbrakk> \<Longrightarrow> x = y"
  by (case_tac x, case_tac y, simp)

lemma VAR_elim [elim]:
  "\<lbrakk> \<And> n t d. a = MkVar n t d \<Longrightarrow> P a \<rbrakk> \<Longrightarrow> P a"
  by (case_tac a, simp)
*)

(*
instantiation VAR :: (VALUE) linorder
begin

definition less_eq_VAR :: "'a VAR \<Rightarrow> 'a VAR \<Rightarrow> bool" where
"x \<le> y \<longleftrightarrow> name x < name y \<or>
           (name x = name y \<and> to_nat (vtype x) < to_nat (vtype y)) \<or>
           (name x = name y \<and> to_nat (vtype x) = to_nat (vtype y) \<and> aux x \<le> aux y)"

definition less_VAR :: "'a VAR \<Rightarrow> 'a VAR \<Rightarrow> bool" where
"less_VAR x y \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)"

instance 
  apply (intro_classes)
  apply (simp add:less_VAR_def)
  apply (simp_all add:less_eq_VAR_def)
  apply (auto)
done
end
*)

type_synonym 'VALUE VAR =
  "NAME \<times> 'VALUE UTYPE \<times> bool"

definition VAR :: "'VALUE VAR set" where
"VAR = UNIV"

abbreviation var_name :: "'VALUE VAR \<Rightarrow> NAME" ("name") where
"var_name x \<equiv> fst x"

abbreviation var_type :: "'VALUE VAR \<Rightarrow> 'VALUE UTYPE" ("vtype") where 
"var_type x \<equiv> fst (snd x)"

abbreviation var_aux :: "'VALUE VAR \<Rightarrow> bool" ("aux") where 
"var_aux x \<equiv> snd (snd x)"

subsection {* Constructors *}

definition MkVar :: 
  "NAME \<Rightarrow> 'VALUE UTYPE \<Rightarrow> bool \<Rightarrow> 'VALUE VAR" where
"MkVar n t d = (n, t, d)"

definition MkPlain :: "string \<Rightarrow> 'VALUE UTYPE \<Rightarrow> bool \<Rightarrow> 'VALUE VAR" where
"MkPlain s t d = MkVar (MkName s 0 NoSub) t d"

subsection {* Operators *}

definition dash :: "'VALUE VAR \<Rightarrow> 'VALUE VAR" ("_\<acute>" [1000] 1000) where
"dash \<equiv> \<lambda> x. MkVar (MkName (name_str (name x)) (dashes (name x) + 1) (subscript (name x)))
                   (vtype x) (aux x)"

definition undash :: "'VALUE VAR \<Rightarrow> 'VALUE VAR" where
"undash \<equiv> \<lambda> x. MkVar (MkName (name_str (name x)) (dashes (name x)- 1) (subscript (name x)))
                     (vtype x) (aux x)"

subsection {* Recontrolions *}

definition UNDASHED :: "'VALUE VAR set" where
"UNDASHED = {v . dashes (name v) = 0}"

definition DASHED :: "'VALUE VAR set" where
"DASHED = {v . dashes (name v) = 1}"

definition DASHED_TWICE :: "'VALUE VAR set" where
"DASHED_TWICE = {v . dashes (name v) = 2}"

definition PLAIN :: "'VALUE VAR set" where
"PLAIN = {v . v \<in> UNDASHED \<and> subscript (name v) = NoSub}"

definition AUX_VAR :: "'VALUE VAR set" where
"AUX_VAR = {v . aux v}"

definition PROGRAM_VAR :: "'VALUE VAR set" where
"PROGRAM_VAR = {v . \<not> aux v}"

abbreviation "REL_VAR \<equiv> UNDASHED \<union> DASHED"

definition NON_REL_VAR :: "'VALUE VAR set" where
"NON_REL_VAR = - (UNDASHED \<union> DASHED)"

definition in_vars ::
  "'VALUE VAR set \<Rightarrow>
   'VALUE VAR set" ("in") where
"in vs = vs \<inter> UNDASHED"

definition out_vars ::
  "'VALUE VAR set \<Rightarrow>
   'VALUE VAR set" ("out") where
"out vs = vs \<inter> DASHED"

definition COMPOSABLE ::
  "'VALUE VAR set \<Rightarrow>
   'VALUE VAR set \<Rightarrow> bool" where
"COMPOSABLE a1 a2 \<longleftrightarrow> (out a1) = dash ` (in a2)"

definition HOMOGENEOUS :: "'VALUE VAR set \<Rightarrow> bool" where
"HOMOGENEOUS a \<longleftrightarrow> COMPOSABLE a a"

subsection {* Theorems *}

theorems var_defs =
  VAR_def
  PROGRAM_VAR_def
  AUX_VAR_def
  NON_REL_VAR_def
  UNDASHED_def
  DASHED_def
  DASHED_TWICE_def
  PLAIN_def
  MkVar_def
  MkPlain_def
  undash_def
  dash_def
  in_vars_def
  out_vars_def
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

lemma MkPlain_aux [simp]: "aux (MkPlain n t a) = a"
  by (simp add:var_defs)

lemma MkPlain_UNDASHED [simp]: "MkPlain n t a \<in> UNDASHED"
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

theorem aux_dash [simp] :
"aux (dash x) = aux x"
  by (simp add: var_defs)

theorem aux_undash [simp] :
"aux (undash x) = aux x"
  by (simp add: var_defs)

subsubsection {* Membership Theorems *}

theorem UNDASHED_not_DASHED :
"x \<in> UNDASHED \<Longrightarrow> \<not> x \<in> DASHED"
  by (simp add: var_defs)

theorem UNDASHED_not_DASHED_TWICE :
"x \<in> UNDASHED \<Longrightarrow> \<not> x \<in> DASHED_TWICE"
  by (simp add: var_defs)

theorem DASHED_not_DASHED_TWICE :
"x \<in> DASHED \<Longrightarrow> \<not> x \<in> DASHED_TWICE"
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

theorem DASHED_dash_not_DASHED :
"x \<in> DASHED \<Longrightarrow> x\<acute> \<notin> DASHED"
  by (simp add: var_defs)

theorem DASHED_TWICE_undash_DASHED :
"x \<in> DASHED_TWICE \<Longrightarrow> undash x \<in> DASHED"
  by (simp add: var_defs)

theorem DASHED_TWICE_undash_not_DASHED_TWICE :
"x \<in> DASHED_TWICE \<Longrightarrow> undash x \<notin> DASHED_TWICE"
  by (simp add: var_defs)

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
  UNDASHED_dash_DASHED
  UNDASHED_dash_not_UNDASHED
  DASHED_undash_UNDASHED
  DASHED_undash_not_DASHED
  DASHED_dash_DASHED_TWICE
  DASHED_TWICE_undash_DASHED
  DASHED_TWICE_undash_not_DASHED_TWICE
  in_UNDASHED
  out_DASHED
  in_of_UNDASHED
  in_of_DASHED
  out_of_UNDASHED
  out_of_DASHED
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

theorem UNDASHED_eq_dash_contra :
"\<lbrakk>x = dash y; x \<in> UNDASHED\<rbrakk> \<Longrightarrow> False"
apply (simp add: var_defs)
done

theorem undash_eq_dash_contra1 :
"\<lbrakk>undash x = dash y; x \<in> DASHED\<rbrakk> \<Longrightarrow> False"
  by (auto simp add: var_defs)

theorem undash_eq_dash_contra2 :
"\<lbrakk>undash x = dash y; x \<in> DASHED_TWICE; y \<in> DASHED\<rbrakk> \<Longrightarrow> False"
  by (auto simp add: var_defs)

theorem dash_eq_undash_contra1 :
"\<lbrakk>dash x = undash y; y \<in> DASHED\<rbrakk> \<Longrightarrow> False"
  by (auto simp add: var_defs)

theorem dash_eq_undash_contra2 :
"\<lbrakk>dash x = undash y; x \<in> DASHED; y \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> False"
  by (auto simp add: var_defs)

theorems var_contra =
  UNDASHED_DASHED_contra
  UNDASHED_DASHED_TWICE_contra
  DASHED_DASHED_TWICE_contra
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

theorem dash_uniqs:
"x \<noteq> dash x" "dash x \<noteq> x"
"x \<noteq> dash (dash x)" "dash (dash x) \<noteq> x"
"dash x \<noteq> dash (dash x)" "dash (dash x) \<noteq> dash x"
"x \<noteq> x\<acute>\<acute>\<acute>" "x\<acute>\<acute>\<acute> \<noteq> x" 
"x\<acute> \<noteq> x\<acute>\<acute>\<acute>" "x\<acute>\<acute>\<acute> \<noteq> x\<acute>"
"x\<acute>\<acute> \<noteq> x\<acute>\<acute>\<acute>" "x\<acute>\<acute>\<acute> \<noteq> x\<acute>\<acute>"
  by (case_tac x, case_tac a, simp add:var_defs)+

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
apply (atomize (full))
apply (induct_tac x)
apply (auto simp add: var_defs)
done

theorem dash_undash_DASHED_TWICE :
"x \<in> DASHED_TWICE \<Longrightarrow> dash (undash x) = x"
apply (simp add: var_defs)
apply (atomize (full))
apply (induct_tac x)
apply (auto simp add: var_defs)
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

theorem in_empty :
"in {} = {}"
  by (simp add:var_defs)

theorem out_empty :
"out {} = {}"
  by (simp add:var_defs)

theorem in_in :
"in (in vs) = in vs"
  by (auto simp add: var_defs)

theorem out_out :
"out (out vs) = out vs"
  by (auto simp add: var_defs)

theorem in_out :
"in (out vs) = {}"
  by (auto simp add: var_defs)

theorem out_in :
"out (in vs) = {}"
  by (auto simp add: var_defs)

lemma in_dash :
"in (dash ` vs) = {}"
  by (auto simp add: var_defs)

lemma in_undash :
"in (undash ` out vs) = undash ` (out vs)"
  by (auto simp add: var_defs)

lemma out_dash :
"out (dash ` vs) = dash ` (in vs)"
  by (auto simp add: var_defs)

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
  "- NON_REL_VAR = REL_VAR"
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
  in_empty
  out_empty
  in_in
  out_out
  in_out
  out_in
  in_dash
  in_undash
  out_dash
  in_out_disj
  in_out_union
  in_out_UNDASHED_DASHED
  UNDASHED_DASHED_inter
  HOMOGENEOUS_undash_out
  HOMOGENEOUS_dash_in

declare var_simps [simp]

subsubsection {* Injectivity Theorems *}

theorem dash_inj [simp]:
"inj_on dash vs"
apply (rule inj_onI)
apply (force simp add: prod_eq_iff var_defs)
done

theorem dash_elim [elim] :
  "\<lbrakk>dash x = dash y; x = y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
 by (metis undash_dash)

theorem undash_inj_on [simp]:
"inj_on undash (- UNDASHED)"
apply (rule inj_onI)
apply (force simp add: var_defs prod_eq_iff)
done

theorem undash_inj_on_DASHED [simp]:
"inj_on undash DASHED"
apply (rule inj_onI)
apply (force simp add: var_defs prod_eq_iff)
done

theorem undash_inj_on_DASHED_TWICE [simp]:
"inj_on undash DASHED_TWICE"
apply (rule inj_onI)
apply (force simp add: var_defs prod_eq_iff)
done

theorem dash_strict_mono [simp]:
"strict_mono dash"
  apply (auto simp add:strict_mono_def)
  apply (simp add: NAME_less_iff prod_less_def dash_name_str dash_subscript dash_dashes)
  apply (metis (hide_lams, no_types) MkVar_name NAME_less_iff dash_def order_eq_iff order_less_le)
done

subsubsection {* Distribution Theorems *}

theorem dash_inter_distr :
"dash ` (vs1 \<inter> vs2) = (dash ` vs1) \<inter> (dash ` vs2)"
apply (auto intro!: image_Int dash_inj)
done

theorem dash_unsion_distr :
"dash ` (vs1 \<union> vs2) = (dash ` vs1) \<union> (dash ` vs2)"
apply (auto intro!: image_Un)
done

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
  dash_inter_distr
  dash_unsion_distr
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
  apply (auto simp add:  in_vars_def out_vars_def)
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

lemma HOMOGENEOUS_insert [simp]:
  "\<lbrakk>x \<in> UNDASHED; HOMOGENEOUS vs \<rbrakk> \<Longrightarrow> HOMOGENEOUS (insert x (insert (x\<acute>) vs))"
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

subsubsection {* Fresh variables *}

text {* This proof uses the infinitness of @{term "NAME"} proof to demonstrate
that, given a finite set of variables, we can always generate a fresh variable
with any given type and auxness *}

theorem fresh_var: "\<exists>x::'VALUE VAR. x \<notin> \<langle>xs\<rangle>\<^sub>f \<and> vtype x = t \<and> aux x = s"
proof -

  obtain n where "n \<notin> name ` \<langle>xs\<rangle>\<^sub>f"
    by (force intro!: ex_new_if_finite infinite_NAME)
    
  with assms show ?thesis
    apply (rule_tac x="MkVar n t s" in exI)
    apply (simp)
    apply (metis MkVar_name imageI)
  done
qed



end

