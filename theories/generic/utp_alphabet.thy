(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_alphabet.thy                                         *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
(******************************************************************************)

header {* Alphabets *}

theory utp_alphabet
imports utp_var
begin

type_synonym 'TYPE ALPHABET = "'TYPE VAR set"

text {* Create a theorem set for alphabets *}

ML {*
  structure AlphabetThm =
    Named_Thms (val name = @{binding "alphabet"} val description = "alphabet theorems");
*}

setup {* AlphabetThm.setup *}

ML {*
  structure AlphaClosureThm =
    Named_Thms (val name = @{binding "alpha_closure"} val description = "alphabet closure theorems");
*}

setup {* AlphaClosureThm.setup *}


context VAR
begin

text {* Alphabets are encoded by finite sets of variables. *}

definition WF_ALPHABET :: "'TYPE ALPHABET set" where
"WF_ALPHABET = {a . finite a (* \<and> (\<forall> x \<in> a. \<forall> y \<in> a. var_name x = var_name y \<longrightarrow> var_type x = var_type y) *)}"

subsection {* Operators *}

definition in_alphabet ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET" ("in") where
"in a = (a \<inter> UNDASHED)"

definition out_alphabet ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET" ("out") where
"out a = (a \<inter> DASHED)"

definition homalph ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET" where
"homalph a = (in a \<union> undash ` out a) \<union> (out a \<union> dash ` in a)"

subsection {* Restrictions *}

definition COMPOSABLE ::
  "'TYPE ALPHABET \<Rightarrow>
   'TYPE ALPHABET \<Rightarrow> bool" where
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 COMPOSABLE a1 a2 \<longleftrightarrow> (out a1) = dash ` (in a2)"

definition HOMOGENEOUS :: "'TYPE ALPHABET \<Rightarrow> bool" where
"HOMOGENEOUS a \<equiv> dash ` in a = out a"

subsection {* Proof Support *}

theorems utp_alphabet_simps =
  UNDASHED_def
  DASHED_def
  DASHED_TWICE_def
  COMPOSABLE_def
  HOMOGENEOUS_def
  in_alphabet_def
  out_alphabet_def

subsection {* Theorems *}

subsubsection {* Closure Theorems *}

theorem WF_ALPHABET_empty [alpha_closure] :
"{} \<in> WF_ALPHABET"
  by (simp add: WF_ALPHABET_def)

theorem WF_ALPHABET_insert [alpha_closure] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (insert x a) \<in> WF_ALPHABET"
  by (simp add: WF_ALPHABET_def)

theorem WF_ALPHABET_union [alpha_closure] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<union> a2 \<in> WF_ALPHABET"
  by (simp add: WF_ALPHABET_def)

theorem WF_ALPHABET_inter [alpha_closure] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<inter> a2 \<in> WF_ALPHABET"
  by (simp add: WF_ALPHABET_def)

theorem WF_ALPHABET_diff [alpha_closure] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 - a2 \<in> WF_ALPHABET"
  by (simp add: WF_ALPHABET_def)

text {* This lemma can really slow down the simplifier, handle with care. *}

theorem WF_ALPHABET_subset [intro]:
"\<lbrakk>a \<in> WF_ALPHABET; b \<subseteq> a\<rbrakk> \<Longrightarrow>
 b \<in> WF_ALPHABET"
  by (simp add: WF_ALPHABET_def finite_subset)

theorem WF_ALPHABET_image [alpha_closure] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 f ` a \<in> WF_ALPHABET"
  by (simp add: WF_ALPHABET_def)

theorem WF_ALPHABET_in [alpha_closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 in a \<in> WF_ALPHABET"
  by (simp add: in_alphabet_def WF_ALPHABET_def)

theorem WF_ALPHABET_out [alpha_closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 out a \<in> WF_ALPHABET"
  by (simp add: out_alphabet_def WF_ALPHABET_def)

theorem WF_ALPHABET_homalph [alpha_closure] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 homalph a \<in> WF_ALPHABET"
  by (auto intro:alpha_closure simp add:homalph_def)

subsection {* Simon's Theorems *}

theorem COMPOSABLE_intro [intro!] :
"\<lbrakk>a \<in> WF_ALPHABET;
 b \<in> WF_ALPHABET;
 out a = dash ` in b\<rbrakk> \<Longrightarrow>
 COMPOSABLE a b"
  by (auto simp: utp_alphabet_simps)

theorem COMPOSABLE_elim [elim] :
"\<lbrakk>COMPOSABLE a b;
 a \<in> WF_ALPHABET;
 b \<in> WF_ALPHABET;
 out a = dash ` in b \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: utp_alphabet_simps)

theorem COMPOSABLE_dest [dest] :
"\<lbrakk>COMPOSABLE a b;
 a \<in> WF_ALPHABET;
 b \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 out a = dash ` in b"
  by (auto simp: utp_alphabet_simps)

theorem in_alphabet_in [var] :
"in (in a) = in a"
  by (auto simp add: in_alphabet_def)

theorem in_alphabet_out [var] :
"in (out a) = {}"
  by (auto simp: utp_alphabet_simps)

theorem out_alphabet_out [var] :
"out (out a) = out a"
  by (auto simp: utp_alphabet_simps)

theorem out_alphabet_in [var] :
"out (in a) = {}"
  by (auto simp: utp_alphabet_simps)

theorem in_alphabet_union [var] :
"in (a \<union> b) = in a \<union> in b"
  by (auto simp: utp_alphabet_simps)

theorem out_alphabet_union [var] :
"out (a \<union> b) = out a \<union> out b"
  by (auto simp: utp_alphabet_simps)

theorem in_alphabet_ndash [var] :
"dash x \<notin> in a"
  by (simp add:utp_alphabet_simps dash_def)

theorem out_alphabet_ndash [var] : 
"x \<in> out a \<Longrightarrow> dash x \<notin> out b"
  by (simp add:utp_alphabet_simps dash_def)

theorem in_undashed [var]:
"in a \<subseteq> UNDASHED"
  by (simp add: UNDASHED_def in_alphabet_def)

theorem out_undashed [var]:
"out a \<subseteq> DASHED"
  by (simp add: DASHED_def out_alphabet_def)

lemma out_undash[var]: "a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> out (undash ` a) = {}"
  by (auto simp add:utp_alphabet_simps image_def undash_def)
 
lemma in_undash[var]:"a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> in (undash ` a) = undash ` a"
  by (auto simp add:utp_alphabet_simps undash_def image_def)

lemma in_dash[var]: "in (dash ` a) = {}"
  by (auto simp add:utp_alphabet_simps dash_def image_def)

lemma out_undash_out[var]: "out (undash ` out a) = {}"
  by (auto simp add:utp_alphabet_simps undash_def image_def)

lemma out_dash_in[var]: "out (dash ` in a) = dash ` in a"
  by (auto simp add:utp_alphabet_simps dash_def image_def)
  
lemma dash_undash_out[var]: "dash ` undash ` out a = out a"
  by (auto simp add:utp_alphabet_simps var image_def)

lemma undash_dash'[var]: "undash ` dash ` a = a"
  by (auto simp add:utp_alphabet_simps var image_def)

lemma in_out_disj[var]: "in a \<inter> out b = {}"
  by (auto simp add:in_alphabet_def var out_alphabet_def DASHED_def UNDASHED_def)

lemma in_out_complete[var]: "a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> in a \<union> out a = a"
  by (auto simp add:utp_alphabet_simps var)

lemma override_out_in: "f \<oplus> (g \<oplus> h on (out a)) on (in b) = f \<oplus> g on (in b)"
  by (metis Diff_triv in_out_disj override_on_cancel4)
  
lemma override_in_out: "f \<oplus> (g \<oplus> h on (in a)) on (out b) = f \<oplus> g on (out b)"
  by (metis Diff_triv in_out_disj inf_commute override_on_cancel4)

lemma homalph_in[var]: "in (homalph a) = in a \<union> undash ` out a"
  by (simp add:var homalph_def)

lemma homalph_out[var]: "out (homalph a) = out a \<union> dash ` in a"
  by (simp add:homalph_def var)

lemma dash_dist_inter[var]: "dash ` (x \<inter> y) = dash ` x \<inter> dash ` y"
  by (metis image_Int dash_inj)

lemma dash_dist_union[var]: "dash ` (x \<union> y) = dash ` x \<union> dash ` y"
  by (metis image_Un)

lemma homalph_homogeneous[var]: "HOMOGENEOUS (homalph a)"
  by (auto simp add:HOMOGENEOUS_def var)
  
lemma homogeneous_homalpha[var]: "\<lbrakk> a \<subseteq> UNDASHED \<union> DASHED ; HOMOGENEOUS a \<rbrakk> \<Longrightarrow> homalph a = a"
  apply(simp add:HOMOGENEOUS_def homalph_def var)
  apply(metis in_out_complete sup_idem undash_dash')
done

lemma homalpha_dashes[var]: "homalph a \<subseteq> UNDASHED \<union> DASHED"
  by (simp add:homalph_def var)

lemma homalpha_subset[var]: "a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> a \<subseteq> homalph a"
proof (simp add:homalph_def)
  assume "a \<subseteq> UNDASHED \<union> DASHED"
  moreover hence "a = in a \<union> out a"
    by (metis in_out_complete)
  ultimately show "a \<subseteq> in a \<union> undash ` out a \<union> (out a \<union> dash ` in a)"
    by auto
qed


lemma homalpha_mono[var]: "a \<subseteq> b \<Longrightarrow> homalph a \<subseteq> homalph b"
  by (auto simp add:homalph_def utp_alphabet_simps var)

end
end


