theory utp_alphabet
imports utp_gen_var
begin

section {* Alphabets *}

types 'VAR ALPHABET = "'VAR set"

context VAR
begin
subsection {* Well-formed Alphabets *}

definition WF_ALPHABET :: "('TYPE VAR) ALPHABET set" where
"WF_ALPHABET \<equiv> {a . finite a}"

subsection {* Variable Operators *}

definition in_alpha ::
  "('TYPE VAR) ALPHABET \<Rightarrow>
   ('TYPE VAR) ALPHABET" ("in") where
"in a = (a \<inter> UNDASHED)"

definition out_alpha ::
  "('TYPE VAR) ALPHABET \<Rightarrow>
   ('TYPE VAR) ALPHABET" ("out") where
"out a = (a \<inter> DASHED)"

subsection {* Semantic Restrictions *}

definition COMPOSABLE ::
  "('TYPE VAR) ALPHABET \<Rightarrow>
   ('TYPE VAR) ALPHABET \<Rightarrow> bool" where
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 COMPOSABLE a1 a2 \<longleftrightarrow> (out a1) = dash ` (in a2)"
end
end
