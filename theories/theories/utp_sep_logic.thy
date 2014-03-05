theory utp_sep_logic
imports "../utp_base"
begin

default_sort STORE_SORT

abbreviation "heap \<equiv> MkPlainP ''heap'' True TYPE('m STORE) TYPE('m :: STORE_SORT)"

lift_definition AssignS :: "(ADDR, 'm) PVAR \<Rightarrow> 'm WF_EXPRESSION \<Rightarrow> 'm WF_PREDICATE" ("[_] := _" [0, 190] 190) is
"\<lambda> x e. {b. \<langle>b\<rangle>\<^sub>* heap\<acute> = (\<langle>b\<rangle>\<^sub>* heap)(\<langle>b\<rangle>\<^sub>*x :=\<^sub>s \<lbrakk>e\<rbrakk>\<^sub>eb)}" .

term "[x] := v"


(*
definition fv :: "'a WF_ALPHA_PREDICATE \<Rightarrow> 'a VAR fset"
where "fv(P) = pvar_alpha(\<alpha>(P))"

definition prog_vars :: 
  "'a VAR set \<Rightarrow> 
   'a VAR set" ("pvar") where
"pvar vs = vs \<inter> PROGRAM_VAR"

lift_definition pvar_alpha :: 
  "'a ALPHABET \<Rightarrow> 
   'a ALPHABET" ("pvar\<^sub>\<alpha>") is pvar
  by (simp add: fsets_def prog_vars_def)
*)


end