(******************************************************************************)
(* Title: utp/theories/utp_rel.thy                                            *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_rel
imports "../generic/utp_gen_pred"
begin

section {* Theory of Relations *}

context GEN_PRED
begin

subsection {* Restrictions *}

definition WF_RELATION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_RELATION =
 {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p \<subseteq> UNDASHED \<union> DASHED}"

definition WF_CONDITION :: "('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"WF_CONDITION =
 {p . p \<in> WF_RELATION \<and> p = (\<exists>p DASHED . p)}"

subsection {* Substitution *}

text {* The definitions below should probably be in the predicate locale. *}

definition SubstB ::
  "('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) BINDING \<Rightarrow>
   ('VALUE, 'TYPE) BINDING" where
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b = b \<circ> (inv ss)"

definition SubstP ::
  " ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_[_]" [200]) where
"\<lbrakk>ss \<in> VAR_SUBST;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 SubstP p ss = (ss ` (\<alpha> p), (SubstB ss) ` (\<beta> p))"

definition SS1 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS1 v = (
 if dashes (name v) = 1 then (VAR.dash v) else
 if dashes (name v) = 2 then (VAR.undash v) else v)"

definition SS2 :: "'TYPE VAR \<Rightarrow> 'TYPE VAR" where
"SS2 v = (
 if dashes (name v) = 0 then VAR.dash (VAR.dash v) else
 if dashes (name v) = 2 then VAR.undash (VAR.undash v) else v)"

subsection {* Relational Operators *}

definition CondR ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_ \<triangleleft> _ \<triangleright> _") where
"p1 \<in> WF_RELATION \<and>
 p2 \<in> WF_RELATION \<and>
 b \<in> WF_CONDITION \<and>
 \<alpha> p1 = \<alpha> p2 \<and>
 \<alpha> b \<subseteq> \<alpha> p1 \<longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) = (b \<and>p p1) \<or>p (\<not>p b \<and>p p2)"

definition SemiR ::
  "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE" (infixr ";" 140) where
"r1 \<in> WF_RELATION \<and>
 r2 \<in> WF_RELATION \<and>
 COMPOSABLE (\<alpha> r1) (\<alpha> r1) \<longrightarrow>
 r1 ; r2 = (\<exists>-p dash ` (out (\<alpha> r1)) . r1[SS1] \<and>p r2[SS2])"

subsubsection {* Theorems *}

theorem SubstP_closure :
"\<lbrakk>p \<in> WF_ALPHA_PREDICATE;
 ss \<in> VAR_SUBST\<rbrakk> \<Longrightarrow>
 p[ss] \<in> WF_ALPHA_PREDICATE"
apply (simp add: SubstP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (safe)
apply (simp add: WF_ALPHABET_def)
apply (simp add: WF_BINDING_SET_def)
apply (safe)
-- {* To prove this we need consistency of typing w.r.t. WF_BINDING! *}
-- {* This shows that we do need typing to be fixed in the locale. *}
oops

theorem CondR_closure [simp] :
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) \<in> WF_RELATION"
apply (simp add: CondR_def)
apply (simp add: WF_RELATION_def WF_CONDITION_def)
done

theorem CondR_alphabet [simp]:
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<triangleleft> b \<triangleright> p2) = \<alpha> p1"
apply (simp add: CondR_def)
apply (simp add: WF_RELATION_def WF_CONDITION_def)
apply (auto)
done

subsection {* Proof Experiments *}

theorem inj_on_override_on :
"inj_on f a \<and> inj_on g b \<and> (f ` a) \<inter> (g ` b) = {} \<Longrightarrow>
 inj_on (f \<oplus> g on b) a"
apply (simp add: inj_on_def)
apply (safe)
apply (case_tac "x \<in> b")
apply (case_tac "y \<in> b")
apply (simp_all)
apply (rule_tac Q = "(f ` a) \<inter> (g ` b) = {}" in contrapos_pp)
apply (assumption)
apply (simp (no_asm_use) only: non_empty_exists)
apply (rule_tac x = "g x" in exI)
apply (safe)
apply (simp)
apply (thin_tac "g x = f y")
apply (simp)
apply (case_tac "y \<in> b")
apply (simp_all)
apply (rule_tac Q = "(f ` a) \<inter> (g ` b) = {}" in contrapos_pp)
apply (assumption)
apply (simp (no_asm_use) only: non_empty_exists)
apply (rule_tac x = "f x" in exI)
apply (safe)
apply (thin_tac "f x = g y")
apply (simp)
apply (simp)
done

theorem inj_override_on :
"inj_on f (-a) \<and> inj_on g a \<and> f ` (-a) \<inter> (g ` a) = {} \<Longrightarrow>
 inj f \<oplus> g on a"
apply (simp add: inj_on_def)
apply (safe)
apply (case_tac "x \<in> a")
apply (case_tac "y \<in> a")
apply (simp_all)
apply (rule_tac Q = "f ` (- a) \<inter> g ` a = {}" in contrapos_pp)
apply (assumption)
apply (simp (no_asm_use) only: non_empty_exists)
apply (rule_tac x = "g x" in exI)
apply (simp (no_asm_use))
apply (safe)
apply (simp)
apply (thin_tac "g x = f y")
apply (simp)
apply (case_tac "y \<in> a")
apply (simp_all)
apply (rule_tac Q = "f ` (- a) \<inter> g ` a = {}" in contrapos_pp)
apply (assumption)
apply (simp (no_asm_use) only: non_empty_exists)
apply (rule_tac x = "f x" in exI)
apply (simp (no_asm_use))
apply (safe)
apply (thin_tac "f x = g y")
apply (simp)
apply (simp)
done

theorem bij_from_inj_on :
"inj_on f a \<and> a \<inter> f ` a = {} \<longrightarrow>
 bij (id \<oplus> f on a) \<oplus> (inv f) on (f ` a)"
apply (simp only: bij_def)
apply (clarify)
apply (rule conjI)
apply (safe intro!: inj_override_on) [1]
apply (safe intro!: inj_on_override_on) [1]
apply (force)
apply (force)
-- {* TODO: Finish the proof! *}
oops
end
end
