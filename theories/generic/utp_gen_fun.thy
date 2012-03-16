theory utp_gen_fun
imports utp_gen_pred
begin

section {* Functions on Alphabetised Predicates *}

context GEN_PRED
begin

types ('a, 'b) ALPHA_FUNCTION =
  "('a, 'b) ALPHA_PREDICATE \<Rightarrow>
   ('a, 'b) ALPHA_PREDICATE"

definition WF_ALPHA_FUNCTION :: "('TYPE VAR, 'VALUE) ALPHA_FUNCTION set" where
"WF_ALPHA_FUNCTION \<equiv>
 {f . \<forall> p \<in> WF_ALPHA_PREDICATE . f p \<in> WF_ALPHA_PREDICATE}"

definition WF_ALPHA_FUNCTION_OVER ::
  "'TYPE VAR ALPHABET \<Rightarrow> ('TYPE VAR, 'VALUE) ALPHA_FUNCTION set" where
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 WF_ALPHA_FUNCTION_OVER a \<equiv>
 {f . \<forall> p \<in> WF_ALPHA_PREDICATE_OVER a . f p \<in> WF_ALPHA_PREDICATE}"

text {* The following might be useful too, this needs to be explored. *}

definition WF_ALPHA_FUNCTION_BETWEEN ::
  "['TYPE VAR ALPHABET, 'TYPE VAR ALPHABET] \<Rightarrow>
   ('TYPE VAR, 'VALUE) ALPHA_FUNCTION set" where
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 WF_ALPHA_FUNCTION_BETWEEN a1 a2 \<equiv>
 {f . \<forall> p \<in> WF_ALPHA_PREDICATE_OVER a1 . f p \<in> WF_ALPHA_PREDICATE_OVER a2}"

section {* Semantic Restrictions *}

definition IDEMPOTENT :: "('TYPE VAR, 'VALUE) ALPHA_FUNCTION set" where
"IDEMPOTENT \<equiv> {f . \<forall> p \<in> WF_ALPHA_PREDICATE . f (f p) = f p}"

definition IDEMPOTENT_OVER ::
  "'TYPE VAR ALPHABET \<Rightarrow> ('TYPE VAR, 'VALUE) ALPHA_FUNCTION set" where
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 IDEMPOTENT_OVER a \<equiv> {f . \<forall> p \<in> WF_ALPHA_PREDICATE_OVER a . f (f p) = f p}"

definition MONOTONIC :: "('TYPE VAR, 'VALUE) ALPHA_FUNCTION set" where
"MONOTONIC \<equiv>
 {f \<in> WF_ALPHA_FUNCTION .
   \<forall> p1 \<in> WF_ALPHA_PREDICATE .
   \<forall> p2 \<in> WF_ALPHA_PREDICATE . p1 \<sqsubseteq> p2 \<longrightarrow> f(p1) \<sqsubseteq> f(p2)}"

definition MONOTONIC_OVER ::
  "'TYPE VAR ALPHABET \<Rightarrow> ('TYPE VAR, 'VALUE) ALPHA_FUNCTION set" where
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 MONOTONIC_OVER a \<equiv>
 {f \<in> WF_ALPHA_FUNCTION_OVER a .
   \<forall> p1 \<in> WF_ALPHA_PREDICATE_OVER a .
   \<forall> p2 \<in> WF_ALPHA_PREDICATE_OVER a . p1 \<sqsubseteq> p2 \<longrightarrow> f(p1) \<sqsubseteq> f(p2)}"
end
end
