theory utp_sep_logic
imports "../utp_base"
begin

default_sort STORE_SORT

type_synonym ('a, 'm) PTR = "('a PADDR, 'm) PVAR"

abbreviation "heap \<equiv> MkPlainP ''heap'' True TYPE('m STORE) TYPE('m :: STORE_SORT)"

lift_definition AssignSR :: "('a, 'm) PTR \<Rightarrow> ('a, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE" ("[_] :=\<^sub>R _" [0, 190] 190) is
"\<lambda> x e. {b. \<langle>b\<rangle>\<^sub>* heap\<acute> = (\<langle>b\<rangle>\<^sub>* heap)(\<langle>b\<rangle>\<^sub>*x :=\<^sub>& \<lbrakk>e\<rbrakk>\<^sub>*b)}" .

lift_definition DeRefPE :: "('a, 'm) PTR \<Rightarrow> ('a, 'm) WF_PEXPRESSION"
is "\<lambda> x b. \<langle>\<langle>b\<rangle>\<^sub>* heap\<rangle>\<^sub>& (\<langle>b\<rangle>\<^sub>*x)" .

definition scomp_join :: "'m STORE \<Rightarrow> ('m STORE * 'm STORE) \<Rightarrow> bool" (infix "\<oast>" 50)
where "scomp_join = (\<lambda> hp (h1, h2). sdom(h1) \<inter>\<^sub>f sdom(h2) = \<lbrace>\<rbrace> \<and> hp = h1 + h2)"

lemma finter_commute: "x \<inter>\<^sub>f y = y \<inter>\<^sub>f x"
  by auto

lemma sdom_0 [simp]: "sdom(0) = \<lbrace>\<rbrace>"
  by (metis fdom_fmempty sdom.rep_eq zero_STORE.rep_eq)

lemma sran_0 [simp]: "sran(0) = \<lbrace>\<rbrace>"
  by (auto simp add:sran.rep_eq zero_STORE.rep_eq fran.rep_eq zero_fmap.rep_eq)

lemma scomp_join_id: "h \<oast> (h, 0)"
  by (simp add:scomp_join_def)

lemma scomp_join_sym: "h \<oast> (h1, h2) \<Longrightarrow> h \<oast> (h2, h1)"
  apply (simp add:scomp_join_def, clarify)
  apply (rule conjI)
  apply (simp add: finter_commute)
  apply (metis STORE_add_comm)
done

definition
  CompJoinPE :: " ('m STORE, 'm::STORE_SORT) WF_PEXPRESSION 
                \<Rightarrow> ('m STORE, 'm) WF_PEXPRESSION
                \<Rightarrow> ('m STORE, 'm) WF_PEXPRESSION
                \<Rightarrow> 'm WF_PREDICATE" where
"CompJoinPE hp h1 h2 = (PExprP (Op2PE scomp_join hp (ProdPE h1 h2)))"

declare CompJoinPE_def [evalp]

syntax
  "_upred_assignsr"  :: "('a, 'm) PTR \<Rightarrow> pexpr \<Rightarrow> upred" ("[_] := _" [100] 100)
  "_upred_comp_join" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("_ \<oast> '(_, _')" [59,0,0] 60)
  "_pexpr_deref"     :: "('a, 'm) PTR \<Rightarrow> pexpr" ("[_]")

translations
  "_upred_assignsr x e"       == "CONST AssignSR x e"
  "_upred_comp_join hp h1 h2" == "CONST CompJoinPE hp h1 h2"

definition SepAndP :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"SepAndP p q = `\<exists>\<^sub>s h1. \<exists>\<^sub>s h2. ($heap \<oast> (\<guillemotleft>h1\<guillemotright>, \<guillemotleft>h2\<guillemotright>) \<and> p[\<guillemotleft>h1\<guillemotright>/heap] \<and> q[\<guillemotleft>h2\<guillemotright>/heap])`"

declare SepAndP_def [eval, evalpp]

syntax
  "_upred_sep_and"   :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "*" 35)

translations
  "_upred_sep_and p q" == "CONST SepAndP p q"

declare EvalP_ExistsShP [evalpp]
declare EvalP_ForallShP [evalpp]

lemma SepAndP_true: "`p * true` = `p`"
  apply (simp add:SepAndP_def usubst)
  apply (utp_poly_auto_tac)
oops

lemma SepAndP_comm: "`p * q` = `q * p`"
  by (utp_poly_tac, metis scomp_join_sym)


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