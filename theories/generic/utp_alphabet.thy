(******************************************************************************)
(* Title: utp/generic/utp_alphabet.thy                                        *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Alphabets *}

theory utp_alphabet
imports utp_var
begin

types 'TYPE ALPHABET = "'TYPE VAR set"

context VAR
begin

text {* Alphabets are encoded by finite sets of variables. *}

definition WF_ALPHABET :: "'TYPE ALPHABET set" where
"WF_ALPHABET = {a . finite a}"

subsection {* Operators *}

definition in_alphabet ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET" ("in") where
"in a = (a \<inter> UNDASHED)"

definition out_alphabet ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET" ("out") where
"out a = (a \<inter> DASHED)"

subsection {* Restrictions *}

definition COMPOSABLE ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET \<Rightarrow> bool" where
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 COMPOSABLE a1 a2 \<longleftrightarrow> (out a1) = dash ` (in a2)"

subsection {* Theorems *}

theorem WF_ALPHABET_in [simp] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 in a \<in> WF_ALPHABET"
apply (simp add: in_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_out [simp] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 out a \<in> WF_ALPHABET"
apply (simp add: out_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done
end
end