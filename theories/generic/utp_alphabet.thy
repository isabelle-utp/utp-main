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

subsection {* Proof Support *}

theorems utp_alphabet_simps =
  UNDASHED_def
  DASHED_def
  DASHED_TWICE_def
  COMPOSABLE_def
  in_alphabet_def
  out_alphabet_def

subsection {* Theorems *}

subsubsection {* Closure Theorems *}

theorem WF_ALPHABET_empty [simp] :
"{} \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_insert [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (insert x a) \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_union [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<union> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_inter [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<inter> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_diff [simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 - a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_subset [intro] :
"\<lbrakk>a \<in> WF_ALPHABET; b \<subseteq> a\<rbrakk> \<Longrightarrow>
 b \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
apply (simp add: finite_subset)
done

theorem WF_ALPHABET_image [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 f ` a \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_in [simp, intro] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 in a \<in> WF_ALPHABET"
apply (simp add: in_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_out [simp, intro] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 out a \<in> WF_ALPHABET"
apply (simp add: out_alphabet_def)
apply (simp add: WF_ALPHABET_def)
done

subsection {* Simon's Theorems *}

theorem COMPOSABLE_intro [intro!] :
"\<lbrakk>a \<in> WF_ALPHABET;
 b \<in> WF_ALPHABET;
 out a = dash ` in b\<rbrakk> \<Longrightarrow>
 COMPOSABLE a b"
apply (auto simp: utp_alphabet_simps)
done

theorem COMPOSABLE_elim [elim] :
"\<lbrakk>COMPOSABLE a b;
 a \<in> WF_ALPHABET;
 b \<in> WF_ALPHABET;
 out a = dash ` in b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (auto simp: utp_alphabet_simps)
done

theorem COMPOSABLE_dest [dest] :
"\<lbrakk>COMPOSABLE a b;
 a \<in> WF_ALPHABET;
 b \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 out a = dash ` in b"
apply (auto simp: utp_alphabet_simps)
done

theorem in_alphabet_in [simp] :
"in (in a) = in a"
apply (auto simp: utp_alphabet_simps)
done

theorem in_alphabet_out [simp] :
"in (out a) = {}"
apply (auto simp: utp_alphabet_simps)
done

theorem out_alphabet_out [simp] :
"out (out a) = out a"
apply (auto simp: utp_alphabet_simps)
done

theorem out_alphabet_in [simp] :
"out (in a) = {}"
apply (auto simp: utp_alphabet_simps)
done

theorem in_alphabet_union [simp] :
"in (a \<union> b) = in a \<union> in b"
apply (auto simp: utp_alphabet_simps)
done

theorem out_alphabet_union [simp] :
"out (a \<union> b) = out a \<union> out b"
apply (auto simp: utp_alphabet_simps)
done
end
end