theory utp_rel
imports "../generic/utp_gen_pred"
begin

section {* Theory of Relations *}

context GEN_PRED
begin

subsection {* Semantic Restrictions *}

definition WF_RELATION :: "('TYPE VAR, 'VALUE) ALPHA_PREDICATE set" where
"WF_RELATION \<equiv>
 {p . p \<in> WF_ALPHA_PREDICATE \<and> \<alpha> p \<subseteq> UNDASHED \<union> DASHED}"

definition WF_CONDITION :: "('TYPE VAR, 'VALUE) ALPHA_PREDICATE set" where
"WF_CONDITION \<equiv>
 {p . p \<in> WF_RELATION \<and> p = (\<exists>p DASHED . p) \<oplus> (\<alpha> p)}"

subsection {* Relational Operators *}

definition SubstB ::
  "('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('TYPE VAR, 'VALUE) BINDING \<Rightarrow>
   ('TYPE VAR, 'VALUE) BINDING" where
"\<lbrakk>ss \<in> VAR_SUBST;
 b \<in> WF_BINDING\<rbrakk> \<Longrightarrow>
 SubstB ss b = b \<circ> (inv ss)"

definition SubstP ::
  "('TYPE VAR \<Rightarrow> 'TYPE VAR) \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" ("_\<lbrakk>_\<rbrakk>") where
"\<lbrakk>ss \<in> VAR_SUBST;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 SubstP ss p = (ss ` (\<alpha> p), (SubstB ss) ` (\<beta> p))"

theorem SubstP_wf :
"\<lbrakk>ss \<in> VAR_SUBST;
 p \<in> WF_ALPHA_PREDICATE\<rbrakk> \<Longrightarrow>
 SubstP ss p \<in> WF_ALPHA_PREDICATE"
apply (simp add: SubstP_def)
apply (simp add: WF_ALPHA_PREDICATE_def)
apply (simp add: WF_BINDING_SET_def)
apply (safe)
prefer 3
apply (subgoal_tac "SubstB ss b1 \<in> WF_BINDING")
apply (drule_tac x = "SubstB ss b1" in bspec)
apply (assumption)
apply (drule_tac x = "b2" in bspec)
apply (assumption)
oops

definition Semi ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" (infixr ";" 140) where
"\<lbrakk>r1 \<in> WF_RELATION;
 r2 \<in> WF_RELATION;
 COMPOSABLE (\<alpha> r1) (\<alpha> r1)\<rbrakk> \<Longrightarrow>
 r1 ; r2 = (\<exists>p dash ` (out (\<alpha> r1)) . r1 \<and>p r2)"

definition Cond ::
  "('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE" ("_ \<triangleleft> _ \<triangleright> _") where
"p1 \<in> WF_RELATION \<and>
 p2 \<in> WF_RELATION \<and>
 b \<in> WF_CONDITION \<and>
 \<alpha> p1 = \<alpha> p2 \<and>
 \<alpha> b \<subseteq> \<alpha> p1 \<longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) = (b \<and>p p1) \<or>p (\<not>p b \<and>p p2)"

(* Theorems *)

theorem Cond_wf [simp] :
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 (p1 \<triangleleft> b \<triangleright> p2) \<in> WF_RELATION"
apply (simp add: Cond_def)
apply (simp add: WF_RELATION_def WF_CONDITION_def)
done

theorem Cond_alphabet [simp]:
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION;
 b \<in> WF_CONDITION;
 \<alpha> p1 = \<alpha> p2;
 \<alpha> b \<subseteq> \<alpha> p1\<rbrakk> \<Longrightarrow>
 \<alpha> (p1 \<triangleleft> b \<triangleright> p2) = \<alpha> p1"
apply (simp add: Cond_def)
apply (simp add: WF_RELATION_def WF_CONDITION_def)
apply (auto)
done

(* Proof Experiments *)

theorem non_empty_exists :
"s \<noteq> {} = (\<exists> x . x \<in> s)"
apply (auto)
done

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

theorem
"inj_on f a \<and> a \<inter> f ` a = {} \<longrightarrow>
 bij (id \<oplus> f on a) \<oplus> (inv f) on (f ` a)"
apply (simp only: bij_def)
apply (clarify)
apply (rule conjI)
apply (safe intro!: inj_override_on) [1]
apply (safe intro!: inj_on_override_on) [1]
apply (force)
apply (force)
(* A bit more to do to finish proof! *)
oops
end
end