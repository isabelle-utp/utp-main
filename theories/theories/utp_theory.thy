(******************************************************************************)
(* Title: utp/theories/utp_theory.thy                                         *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)
theory utp_theory
imports "../GLOBAL" "../generic/utp_generic"
begin

section {* UTP Theories *}

record ('VALUE, 'TYPE) UTP_THEORY =
  alphabet::"'TYPE ALPHABET" ("\<alpha>")
  healthconds::"('VALUE, 'TYPE) ALPHA_FUNCTION set" ("\<H>")

context GEN_PRED
begin
definition WF_HEALTH_COND ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION set" where
"a \<in> WF_ALPHABET \<longrightarrow>
 WF_HEALTH_COND a = {hc . hc \<in> IDEMPOTENT_OVER a}"

(* Should we also require hc \<in> WF_ALPHA_FUNCTION_BETWEEN a a ? *)

definition WF_HEALTH_CONDS ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION set set" where
"a \<in> WF_ALPHABET \<longrightarrow>
 WF_HEALTH_CONDS a =
   {hs . finite hs \<and> (\<forall> hc \<in> hs . hc \<in> WF_HEALTH_COND a)}"

definition WF_UTP_THEORY :: "('VALUE, 'TYPE) UTP_THEORY set" where
"WF_UTP_THEORY =
   {th . (\<alpha> th) \<in> WF_ALPHABET \<and> (\<H> th) \<in> WF_HEALTH_CONDS (\<alpha> th)}"

subsection {* Theory Operators *}

definition MakeTheory ::
  "('TYPE ALPHABET) \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION set \<Rightarrow>
   ('VALUE, 'TYPE) UTP_THEORY" where
"a \<in> WF_ALPHABET \<and>
 hs \<in> WF_HEALTH_CONDS a \<longrightarrow>
 MakeTheory a hs = \<lparr>alphabet = a, healthconds = hs\<rparr>"

definition SpecTheory ::
  "('VALUE, 'TYPE) UTP_THEORY \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION set \<Rightarrow>
   ('VALUE, 'TYPE) UTP_THEORY" where
"th \<in> WF_UTP_THEORY \<and>
 hs \<in> WF_HEALTH_CONDS (\<alpha> th) \<longrightarrow>
 SpecTheory th hs = \<lparr>alphabet = (\<alpha> th), healthconds = (\<H> th) \<union> hs\<rparr>"

subsection {* Theory Predicates *}

definition TheoryPreds ::
  "('VALUE, 'TYPE) UTP_THEORY \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"th \<in> WF_UTP_THEORY \<longrightarrow>
 TheoryPreds th =
   {p \<in> WF_ALPHA_PREDICATE_OVER (\<alpha> th) . (\<forall> hc \<in> \<H> th . hc p = p)}"

subsection {* UTP Theory of Predicates *}

definition PredTheory ::
  "'TYPE ALPHABET \<Rightarrow>
   ('VALUE, 'TYPE) UTP_THEORY" where
"a \<in> WF_ALPHABET \<longrightarrow>
 PredTheory a = MakeTheory a {}"
end

subsection {* Theorems *}

context GEN_PRED
begin
theorem WF_HEALTH_CONDS_union :
"\<lbrakk>a \<in> WF_ALPHABET;
 hs1 \<in> WF_HEALTH_CONDS a;
 hs2 \<in> WF_HEALTH_CONDS a\<rbrakk> \<Longrightarrow>
 (hs1 \<union> hs2) \<in> WF_HEALTH_CONDS a"
apply (simp add: WF_HEALTH_CONDS_def)
apply (auto)
done

theorem SpecTheory_closure [simp, intro!] :
"\<lbrakk>th \<in> WF_UTP_THEORY;
 hs \<in> WF_HEALTH_CONDS (\<alpha> th)\<rbrakk> \<Longrightarrow>
 (SpecTheory th hs) \<in> WF_UTP_THEORY"
apply (simp add: SpecTheory_def)
apply (simp add: WF_UTP_THEORY_def)
apply (simp add: WF_HEALTH_CONDS_union)
done

theorem SpecTheory_alphabet [simp] :
"\<lbrakk>th \<in> WF_UTP_THEORY;
 hs \<in> WF_HEALTH_CONDS (\<alpha> th)\<rbrakk> \<Longrightarrow>
 \<alpha> (SpecTheory th hs) = (\<alpha> th)"
apply (simp add: SpecTheory_def)
done

theorem SpecTheory_healthconds [simp] :
"\<lbrakk>th \<in> WF_UTP_THEORY;
 hs \<in> WF_HEALTH_CONDS (\<alpha> th)\<rbrakk> \<Longrightarrow>
 \<H> th \<subseteq> \<H> (SpecTheory th hs)"
apply (simp add: SpecTheory_def)
done

theorem SpecTheory_TheoryPreds :
"\<lbrakk>th \<in> WF_UTP_THEORY;
 hs \<in> WF_HEALTH_CONDS (\<alpha> th)\<rbrakk> \<Longrightarrow>
 TheoryPreds (SpecTheory th hs) \<subseteq> TheoryPreds th"
apply (simp add: TheoryPreds_def)
apply (safe)
apply (drule_tac th = "th" and hs = "hs" in SpecTheory_healthconds)
apply (auto)
done
end
end