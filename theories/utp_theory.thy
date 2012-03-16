theory utp_theory
imports GLOBAL "generic/utp_generic"
begin

section {* UTP Theories *}

record ('VAR, 'VALUE) UTP_THEORY =
  theory_alpha::"'VAR ALPHABET" ("\<alpha>")
  healthconds::"('VAR, 'VALUE) ALPHA_FUNCTION set" ("\<H>")

(* Should we also require "hc \<in> WF_ALPHA_FUNCTION_BETWEEN a a" ? *)

context GEN_PRED
begin
definition WF_HEALTH_COND ::
  "('TYPE VAR) ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_FUNCTION set" where
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 WF_HEALTH_COND a \<equiv> {hc . hc \<in> IDEMPOTENT_OVER a}"

definition WF_HEALTH_CONDS ::
  "('TYPE VAR) ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_FUNCTION set set" where
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 WF_HEALTH_CONDS a \<equiv> {hs . finite hs \<and> (\<forall> hc \<in> hs . hc \<in> WF_HEALTH_COND a)}"

definition WF_UTP_THEORY :: "('TYPE VAR, 'VALUE) UTP_THEORY set" where
"WF_UTP_THEORY \<equiv> {th . (\<H> th) \<in> WF_HEALTH_CONDS (\<alpha> th)}"

subsection {* Theory Operators *}

definition MakeTh ::
  "('TYPE VAR) ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_FUNCTION set \<Rightarrow>
   ('TYPE VAR, 'VALUE) UTP_THEORY" where
"\<lbrakk>a \<in> WF_ALPHABET;
  hs \<in> WF_HEALTH_CONDS a\<rbrakk> \<Longrightarrow>
  MakeTh a hs \<equiv> \<lparr>theory_alpha = a, healthconds = hs\<rparr>"

definition SpecTh ::
  "('TYPE VAR, 'VALUE) UTP_THEORY \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_FUNCTION set \<Rightarrow>
   ('TYPE VAR, 'VALUE) UTP_THEORY" where
"\<lbrakk>th \<in> WF_UTP_THEORY;
  hs \<in> WF_HEALTH_CONDS (\<alpha> th)\<rbrakk> \<Longrightarrow>
  SpecTh th hs \<equiv> \<lparr>theory_alpha = (\<alpha> th), healthconds = (\<H> th) \<union> hs\<rparr>"

subsection {* Theory Predicates *}

definition ThPred ::
  "('TYPE VAR, 'VALUE) UTP_THEORY \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_PREDICATE set" where
"\<lbrakk>th \<in> WF_UTP_THEORY\<rbrakk> \<Longrightarrow>
 ThPred th \<equiv> {p \<in> WF_ALPHA_PREDICATE_OVER (\<alpha> th) . (\<forall> hc \<in> \<H> th . hc p = p)}"

subsection {* UTP Theory of Predicates *}

definition PredTheory ::
  "('TYPE VAR) ALPHABET \<Rightarrow>
   ('TYPE VAR, 'VALUE) UTP_THEORY" where
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 PredTheory a \<equiv> MakeTh a {}"
end
end
