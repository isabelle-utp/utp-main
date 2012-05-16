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

theorem WF_ALPHABET_in [simp,intro] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 in a \<in> WF_ALPHABET"
apply (simp add: in_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_out [simp,intro] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 out a \<in> WF_ALPHABET"
apply (simp add: out_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done

lemma WF_ALPHABET_union [intro] :
"\<lbrakk> a \<in> WF_ALPHABET ; b \<in> WF_ALPHABET \<rbrakk> \<Longrightarrow> a \<union> b \<in> WF_ALPHABET"
  by (simp add:WF_ALPHABET_def)

lemma COMPOSABLE_intro[intro!]: "\<lbrakk> a \<in> WF_ALPHABET ; b \<in> WF_ALPHABET ; out a = dash ` in b \<rbrakk> \<Longrightarrow>
                                COMPOSABLE a b"
  by (simp add:COMPOSABLE_def)

lemma COMPOSABLE_elim[elim]: "\<lbrakk> COMPOSABLE a b ; a \<in> WF_ALPHABET ; b \<in> WF_ALPHABET ; out a = dash ` in b \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:COMPOSABLE_def)  

lemma COMPOSABLE_dest[dest]: "\<lbrakk> COMPOSABLE a b ; a \<in> WF_ALPHABET ; b \<in> WF_ALPHABET \<rbrakk> \<Longrightarrow> out a = dash ` in b"
  by (simp add:COMPOSABLE_def)  

lemma in_alphabet_in[simp]: "in (in a) = in a"
  by (auto simp add: in_alphabet_def)

lemma in_alphabet_out[simp]: "in (out a) = {}"
  by (auto simp add: in_alphabet_def out_alphabet_def DASHED_def UNDASHED_def)

lemma out_alphabet_out[simp]: "out (out a) = out a"
  by (auto simp add: out_alphabet_def)

lemma out_alphabet_in[simp]: "out (in a) = {}"
  by (auto simp add: in_alphabet_def out_alphabet_def DASHED_def UNDASHED_def)

lemma in_alphabet_union[simp]: "in (a \<union> b) = in a \<union> in b"
  by (auto simp add: in_alphabet_def)

lemma out_alphabet_union[simp]: "out (a \<union> b) = out a \<union> out b"
  by (auto simp add: out_alphabet_def)

end
end