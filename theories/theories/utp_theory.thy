(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/theories/utp_theory.thy                                          *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* UTP Theories *}

theory utp_theory
imports "../generic/utp_generic"
begin

record ('VALUE, 'TYPE) UTP_THEORY =
  utp_alphabets::"'TYPE ALPHABET set" ("\<A>")
  healthconds::"('VALUE, 'TYPE) ALPHA_FUNCTION set" ("\<H>")

context GEN_EXPR
begin
definition WF_HEALTH_COND ::
  "('TYPE ALPHABET) set \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION set" where
"A \<subseteq> WF_ALPHABET \<longrightarrow>
 WF_HEALTH_COND A = {hc . (\<forall>a\<in>A. hc \<in> IDEMPOTENT_OVER a)}"

text {* Should we also require @{term "hc \<in> WF_ALPHA_FUNCTION_BETWEEN a a"} ? *}

definition WF_HEALTH_CONDS ::
  "('TYPE ALPHABET) set \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION set set" where
"A \<subseteq> WF_ALPHABET \<longrightarrow>
 WF_HEALTH_CONDS A =
 {hs . finite hs \<and> (\<forall> hc \<in> hs . hc \<in> WF_HEALTH_COND A)}"

definition WF_UTP_THEORY :: "('VALUE, 'TYPE) UTP_THEORY set" where
"WF_UTP_THEORY =
 {th . (\<A> th) \<subseteq> WF_ALPHABET \<and> (\<H> th) \<in> WF_HEALTH_CONDS (\<A> th)}"

subsection {* Theory Operators *}

definition MakeTheory ::
  "('TYPE ALPHABET) set \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION set \<Rightarrow>
   ('VALUE, 'TYPE) UTP_THEORY" where
"A \<subseteq> WF_ALPHABET \<and>
 hs \<in> WF_HEALTH_CONDS A \<longrightarrow>
 MakeTheory A hs = \<lparr>utp_alphabets = A, healthconds = hs\<rparr>"

definition SpecTheory ::
  "('VALUE, 'TYPE) UTP_THEORY \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_FUNCTION set \<Rightarrow>
   ('VALUE, 'TYPE) UTP_THEORY" where
"th \<in> WF_UTP_THEORY \<and>
 hs \<in> WF_HEALTH_CONDS (\<A> th) \<longrightarrow>
 SpecTheory th hs = \<lparr>utp_alphabets = (\<A> th), healthconds = (\<H> th) \<union> hs\<rparr>"

subsection {* Theory Predicates *}

definition TheoryPreds ::
  "('VALUE, 'TYPE) UTP_THEORY \<Rightarrow>
   ('VALUE, 'TYPE) ALPHA_PREDICATE set" where
"th \<in> WF_UTP_THEORY \<longrightarrow>
 TheoryPreds th =
 {p . (\<exists>a\<in>\<A> th. p \<in> WF_ALPHA_PREDICATE_OVER a) \<and> (\<forall> hc \<in> \<H> th . hc p = p)}"

subsection {* UTP Theory of Predicates *}

definition PredTheory ::
  "'TYPE ALPHABET set \<Rightarrow>
   ('VALUE, 'TYPE) UTP_THEORY" where
"A \<subseteq> WF_ALPHABET \<longrightarrow>
 PredTheory A = MakeTheory A {}"

subsection {* Theorems *}

theorem WF_HEALTH_CONDS_union :
"\<lbrakk>A \<subseteq> WF_ALPHABET;
 hs1 \<in> WF_HEALTH_CONDS A;
 hs2 \<in> WF_HEALTH_CONDS A\<rbrakk> \<Longrightarrow>
 (hs1 \<union> hs2) \<in> WF_HEALTH_CONDS A"
apply (simp add: WF_HEALTH_CONDS_def)
apply (auto)
done

theorem SpecTheory_closure [simp, intro!] :
"\<lbrakk>th \<in> WF_UTP_THEORY;
 hs \<in> WF_HEALTH_CONDS (\<A> th)\<rbrakk> \<Longrightarrow>
 (SpecTheory th hs) \<in> WF_UTP_THEORY"
apply (simp add: SpecTheory_def)
apply (simp add: WF_UTP_THEORY_def)
apply (simp add: WF_HEALTH_CONDS_union)
done

theorem SpecTheory_alphabet [simp] :
"\<lbrakk>th \<in> WF_UTP_THEORY;
 hs \<in> WF_HEALTH_CONDS (\<A> th)\<rbrakk> \<Longrightarrow>
 \<A> (SpecTheory th hs) = (\<A> th)"
apply (simp add: SpecTheory_def)
done

theorem SpecTheory_healthconds [simp] :
"\<lbrakk>th \<in> WF_UTP_THEORY;
 hs \<in> WF_HEALTH_CONDS (\<A> th)\<rbrakk> \<Longrightarrow>
 \<H> th \<subseteq> \<H> (SpecTheory th hs)"
apply (simp add: SpecTheory_def)
done

theorem SpecTheory_TheoryPreds :
"\<lbrakk>th \<in> WF_UTP_THEORY;
 hs \<in> WF_HEALTH_CONDS (\<A> th)\<rbrakk> \<Longrightarrow>
 TheoryPreds (SpecTheory th hs) \<subseteq> TheoryPreds th"
apply (simp add: TheoryPreds_def)
apply (safe)
apply (drule_tac th = "th" and hs = "hs" in SpecTheory_healthconds)
apply (auto simp add:closure alpha_closure eval taut binding alphabet)
apply(simp add:SpecTheory_def)
done
end
end
