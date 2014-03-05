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

lemma scomp_joinE [elim]: "\<lbrakk> h \<oast> (h1,h2); \<lbrakk> sdom(h1) \<inter>\<^sub>f sdom(h2) = \<lbrace>\<rbrace>; h = h1 + h2 \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis (lifting, full_types) scomp_join_def splitD)
  
lemma scomp_join_id [intro]: "h \<oast> (h, 0)"
  by (simp add:scomp_join_def)

lemma scomp_join_sym: "h \<oast> (h1, h2) \<Longrightarrow> h \<oast> (h2, h1)"
  apply (simp add:scomp_join_def, clarify)
  apply (rule conjI)
  apply (simp add: finter_comm)
  apply (metis STORE_add_comm)
done

lemma scomp_assoc_split [intro]: "\<lbrakk> h \<oast> (h1,h2); h2 \<oast> (h2a,h2b) \<rbrakk> \<Longrightarrow> h \<oast> (h1 + h2a,h2b)"
  apply (simp add:scomp_join_def, clarify)
  apply (rule conjI)
  apply (force)
  apply (metis add_assoc)
done

lemma scomp_assoc_split' [intro]: "\<lbrakk> h \<oast> (h1,h2); h1 \<oast> (h1a,h1b) \<rbrakk> \<Longrightarrow> h \<oast> (h1a,h1b + h2)"
  apply (simp add:scomp_join_def, clarify)
  apply (rule conjI)
  apply (force)
  apply (metis add_assoc)
done

lemma scomp_triv [intro]: "sdom(x) \<inter>\<^sub>f sdom(y) = \<lbrace>\<rbrace> \<Longrightarrow> x + y \<oast> (x, y)"
  by (simp add:scomp_join_def)

definition
  CompJoinP :: " ('m STORE, 'm::STORE_SORT) WF_PEXPRESSION 
                \<Rightarrow> ('m STORE, 'm) WF_PEXPRESSION
                \<Rightarrow> ('m STORE, 'm) WF_PEXPRESSION
                \<Rightarrow> 'm WF_PREDICATE" where
"CompJoinP hp h1 h2 = (PExprP (Op2PE scomp_join hp (ProdPE h1 h2)))"

declare CompJoinP_def [evalp]

syntax
  "_upred_assignsr"  :: "('a, 'm) PTR \<Rightarrow> pexpr \<Rightarrow> upred" ("[_] := _" [100] 100)
  "_upred_comp_join" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> upred" ("_ \<oast> '(_, _')" [59,0,0] 60)
  "_pexpr_deref"     :: "('a, 'm) PTR \<Rightarrow> pexpr" ("[_]")

translations
  "_upred_assignsr x e"       == "CONST AssignSR x e"
  "_upred_comp_join hp h1 h2" == "CONST CompJoinP hp h1 h2"

definition SepEmpP :: "'a WF_PREDICATE" where
"SepEmpP = `$heap = \<guillemotleft>0\<guillemotright>`"

lift_definition SepSingleP :: 
  "('a PADDR, 'm) WF_PEXPRESSION \<Rightarrow> ('a, 'm) WF_PEXPRESSION \<Rightarrow> 'm WF_PREDICATE"
is "\<lambda> k v. {b. \<langle>\<langle>b\<rangle>\<^sub>* heap\<rangle>\<^sub>& (\<lbrakk>k\<rbrakk>\<^sub>*b) = \<lbrakk>v\<rbrakk>\<^sub>*b}" .

definition SepAndP :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"SepAndP p q = `\<exists>\<^sub>s h1. \<exists>\<^sub>s h2. ($heap \<oast> (\<guillemotleft>h1\<guillemotright>, \<guillemotleft>h2\<guillemotright>) \<and> p[\<guillemotleft>h1\<guillemotright>/heap] \<and> q[\<guillemotleft>h2\<guillemotright>/heap])`"

declare SepAndP_def [eval, evalpp]
declare SepEmpP_def [eval, evalpp]

syntax
  "_upred_sep_and"   :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "*" 35)
  "_upred_sep_emp"   :: "upred" ("emp")

translations
  "_upred_sep_and p q" == "CONST SepAndP p q"
  "_upred_sep_emp"     == "CONST SepEmpP"

declare EvalP_ExistsShP [evalpp]
declare EvalP_ForallShP [evalpp]

lemma SepAndP_emp: "`p * emp` = `p`"
  by (utp_poly_auto_tac)

lemma SepAndP_false: "`p * false` = `false`"
  by (utp_poly_auto_tac)

lemma SepAndP_comm: "`p * q` = `q * p`"
  by (utp_poly_tac, metis scomp_join_sym)

lemma SepAndP_assoc: "`p * (q * r)` = `(p * q) * r`"
  apply (utp_poly_auto_tac)
  apply (rule_tac x="x + xb" in exI)
  apply (rule_tac x="xc" in exI)
  apply (auto)
  apply (rule_tac x= "x" in exI)
  apply (rule_tac x= "xb" in exI)
  apply (auto)
  apply (erule scomp_joinE)+
  apply (rule)
  apply (simp)
  apply (force)
  apply (rule_tac x= "xb" in exI)
  apply (rule_tac x= "xc + xa" in exI)
  apply (auto)
  apply (rule_tac x="xc" in exI)
  apply (rule_tac x="xa" in exI)
  apply (simp)
  apply (rule scomp_triv)
  apply (erule scomp_joinE)+
  apply (force)
done

lemma SepAnd_dist_disj: "`p * (q \<or> r)` = `(p * q) \<or> (p * r)`"
  by (utp_poly_auto_tac)

lemma SepAnd_dist_conj_ref: "`(p * q) \<and> (p * r)` \<sqsubseteq> `p * (q \<and> r)`"
  by (utp_poly_auto_tac)
  




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