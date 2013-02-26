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

type_synonym 'VALUE VAR =
  "NAME \<times> 'VALUE UTYPE \<times> bool"

definition VAR :: "'VALUE VAR set" where
"VAR = UNIV"

abbreviation var_name :: "'VALUE VAR \<Rightarrow> NAME" ("name") where
"var_name x \<equiv> fst x"

abbreviation var_type :: "'VALUE VAR \<Rightarrow> 'VALUE UTYPE" ("type") where 
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

definition dash :: "'VALUE VAR \<Rightarrow> 'VALUE VAR" ("_\<acute>") where
"dash \<equiv> \<lambda> x. ( MkName (name_str (name x)) (dashes (fst x) + 1) (subscript (name x))
             , type x
             , aux x)"

definition undash :: "'VALUE VAR \<Rightarrow> 'VALUE VAR" where
"undash \<equiv> \<lambda> x. ( MkName (name_str (name x)) (dashes (fst x)- 1) (subscript (name x))
               , fst (snd x)
               , snd (snd x))"

subsection {* Recontrolions *}

definition UNDASHED :: "'VALUE VAR set" where
"UNDASHED = {v . dashes (name v) = 0}"

definition DASHED :: "'VALUE VAR set" where
"DASHED = {v . dashes (name v) = 1}"

definition DASHED_TWICE :: "'VALUE VAR set" where
"DASHED_TWICE = {v . dashes (name v) = 2}"

definition PLAIN :: "'VALUE VAR set" where
"PLAIN = {v . v \<in> UNDASHED \<and> subscript (name v) = NoSub}"

definition AUX_VARS :: "'VALUE VAR set" where
"AUX_VARS = {v . aux v}"

definition PROGRAM_VARS :: "'VALUE VAR set" where
"PROGRAM_VARS = {v . \<not> aux v}"

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

theorem MkVar_name [simp]: 
  "name (MkVar n t s) = n" 
  by (simp add:var_defs)

theorem MkVar_type [simp]: 
  "type (MkVar n t s) = t" 
  by (simp add:var_defs)

theorem MkVar_aux [simp]: 
  "aux (MkVar n t s) = s" 
  by (simp add:var_defs)

lemma MkVar_eq_iff[simp]: 
  "MkVar n t s = MkVar n' t' s' \<longleftrightarrow> n = n' \<and> t = t' \<and> s = s'"
  by (simp add:MkVar_def)

subsubsection {* Names and Types *}

theorem type_dash [simp] :
"type (dash x) = type x"
  by (simp add: var_defs)

theorem type_undash [simp] :
"type (undash x) = type x"
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

theorem DASHED_undash_UNDASHED :
"x \<in> DASHED \<Longrightarrow> undash x \<in> UNDASHED"
  by (simp add: var_defs)

theorem DASHED_dash_DASHED_TWICE :
"x \<in> DASHED \<Longrightarrow> dash x \<in> DASHED_TWICE"
  by (simp add: var_defs)

theorem DASHED_TWICE_undash_DASHED :
"x \<in> DASHED_TWICE \<Longrightarrow> undash x \<in> DASHED"
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

theorems var_member =
  UNDASHED_not_DASHED
  UNDASHED_not_DASHED_TWICE
  DASHED_not_DASHED_TWICE
  UNDASHED_dash_DASHED
  DASHED_undash_UNDASHED
  DASHED_dash_DASHED_TWICE
  DASHED_TWICE_undash_DASHED
  in_UNDASHED
  out_DASHED
  in_of_UNDASHED
  in_of_DASHED
  out_of_UNDASHED
  out_of_DASHED
  not_dash_member_in
  not_dash_dash_member_out

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

theorem dash_uniqs:
"x \<noteq> dash x" "dash x \<noteq> x"
"x \<noteq> dash (dash x)" "dash (dash x) \<noteq> x"
"dash x \<noteq> dash (dash x)" "dash (dash x) \<noteq> dash x"
  by (case_tac x, case_tac a, simp add:var_defs)+

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
  by (auto, metis DASHED_dash_DASHED_TWICE imageI undash_dash)

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

theorem in_out_UNDASHED_DASHED:
  "in UNDASHED = UNDASHED"
  "out UNDASHED = {}"
  "in DASHED = {}"
  "out DASHED = DASHED"
  by (auto simp add:var_defs)

theorems var_simps =
  dash_uniqs
  dash_undash_DASHED
  dash_undash_DASHED_TWICE
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

declare var_simps [simp]

subsubsection {* Injectivity Theorems *}

theorem dash_inj :
"inj dash"
apply (rule injI)
apply (force simp add: prod_eq_iff var_defs)
done

theorem dash_elim [elim] :
  "\<lbrakk>dash x = dash y; x = y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
 by (metis undash_dash)

theorem undash_inj_on :
"inj_on undash (- UNDASHED)"
apply (rule inj_onI)
apply (force simp add: var_defs prod_eq_iff)
done

theorem undash_inj_on_DASHED :
"inj_on undash DASHED"
apply (rule inj_onI)
apply (force simp add: var_defs prod_eq_iff)
done

theorem undash_inj_on_DASHED_TWICE :
"inj_on undash DASHED_TWICE"
apply (rule inj_onI)
apply (force simp add: var_defs prod_eq_iff)
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

subsubsection {* Fresh variables *}

text {* This proof uses the infinitness of @{term "NAME"} proof to demonstrate
that, given a finite set of variables, we can always generate a fresh variable
with any given type and auxness *}

theorem fresh_var: "\<exists>x::'VALUE VAR. x \<notin> \<langle>xs\<rangle>\<^sub>f \<and> type x = t \<and> aux x = s"
proof -

  obtain n where "n \<notin> name ` \<langle>xs\<rangle>\<^sub>f"
    by (force intro!: ex_new_if_finite infinite_NAME)
    
  with assms show ?thesis
    apply (rule_tac x="MkVar n t s" in exI)
    apply (simp)
    apply (metis (lifting) MkVar_name assms image_iff)
  done
qed



end

