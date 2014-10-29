(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: ho_type.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 10 September 2014 *)

header {* Higher-Order Types *}

theory ho_type
imports ho_common
  "../core/utp_name"
  "../core/utp_model"
  "../utils/fset"
begin

default_sort type

subsection {* HO Variable Model *}

text {*
  We require an alternative representation of variables to be used in the
  definition of HO types. This is for two reasons. Firstly, variables need
  to be parametrised in terms of their type notion rather than models to
  facilitate a recursive HO type construction. And secondly, a tuple-based
  representation is needed in order to support recursion into variable types
  when defining the HO type notion.
*}

type_synonym 'TYPE ho_var_raw = "uname \<times> 'TYPE \<times> bool"

translations (type) "'TYPE ho_var_raw" \<leftharpoondown> (type) "uname \<times> 'TYPE \<times> bool"

subsubsection {* Constructors *}

abbreviation MkHOVar ::
  "uname \<Rightarrow> 'TYPE \<Rightarrow> bool \<Rightarrow> (uname \<times> 'TYPE \<times> bool)" where
"MkHOVar n t a \<equiv> (n, t, a)"

subsubsection {* Destructors *}

abbreviation ho_var_name :: "'TYPE ho_var_raw \<Rightarrow> uname" ("vname\<^sub>h") where
"ho_var_name \<equiv> (\<lambda> (n, t, a) . n)"

abbreviation ho_var_type :: "'TYPE ho_var_raw \<Rightarrow> 'TYPE" ("vtype\<^sub>h") where
"ho_var_type \<equiv> (\<lambda> (n, t, a) . t)"

abbreviation ho_var_aux :: "'TYPE ho_var_raw \<Rightarrow> bool" ("aux\<^sub>h") where
"ho_var_aux \<equiv> (\<lambda> (n, t, a) . a)"

subsection {* HO Type Model *}

default_sort BASE_MODEL

subsubsection {* Datatype Definition *}

text {* The following does not take into account procedure types yet. *}

datatype_new 'BASE_MODEL ho_type =
  BaseTyp "'BASE_MODEL utype" |
  ProgTyp "'BASE_MODEL ho_type ho_var_raw fset"

text {* Note that @{text "datatype_new_compat ho_type"} does not work. *}

subsubsection {* Type Synonyms *}

paragraph {* HO Variables *}

type_synonym 'BASE_MODEL ho_var = "'BASE_MODEL ho_type ho_var_raw"

translations
  (type) "'BASE_MODEL ho_var" \<leftharpoondown> (type) "'BASE_MODEL ho_type ho_var_raw"

paragraph {* Procedure Types *}

type_synonym 'BASE_MODEL ptype = "'BASE_MODEL ho_var fset"

translations (type) "'MODEL_BASE ptype" \<leftharpoondown> (type) "'MODEL_BASE ho_var fset"

subsubsection {* Destructors *}

text {* The use of @{const id} below is due to a bug in the BNF package. *}

primrec_new BaseTypOf ::
  "'BASE_MODEL ho_type \<Rightarrow> 'BASE_MODEL utype" where
"BaseTypOf (BaseTyp t) = t"

primrec_new ProgTypOf ::
  "'BASE_MODEL ho_type \<Rightarrow> 'BASE_MODEL ho_var fset" where
"ProgTypOf (ProgTyp t) = (id t)"

subsection {* Testing Functions *}

primrec_new IsBaseTyp :: "'BASE_MODEL ho_type \<Rightarrow> bool" where
"IsBaseTyp (BaseTyp _) = True" |
"IsBaseTyp (ProgTyp _) = False"

primrec_new IsProgTyp :: "'BASE_MODEL ho_type \<Rightarrow> bool" where
"IsProgTyp (BaseTyp _) = False" |
"IsProgTyp (ProgTyp _) = True"

subsubsection {* Inverse Theorems *}

theorem BaseTypOf_inverse :
"IsBaseTyp t \<Longrightarrow> BaseTyp (BaseTypOf t) = t"
apply (erule asmE)
apply (induct t)
apply (simp_all)
done

theorem ProgTypOf_inverse :
"IsProgTyp t \<Longrightarrow> ProgTyp (ProgTypOf t) = t"
apply (erule asmE)
apply (induct t)
apply (simp_all)
done

subsection {* Ranks of HO Types *}

function (domintros) Rank :: "'BASE_MODEL ho_type \<Rightarrow> nat" where
"Rank (BaseTyp bt) = 0" |
"Rank (ProgTyp pt) = MaxSet (Rank ` vtype\<^sub>h ` (\<sim>pt)) + 1"
apply (simp_all)
apply (metis ho_type.exhaust)
done
termination Rank
apply (clarify)
apply (induct_tac x)
-- {* Subgoal 1 *}
apply (rule Rank.domintros)
-- {* Subgoal 2 *}
apply (rule Rank.domintros)
apply (unfold fsts_def snds_def)
apply (clarsimp)
apply (metis)
done
end
