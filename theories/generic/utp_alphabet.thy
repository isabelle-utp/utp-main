(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/generic/utp_alphabet.thy                                         *)
(* Authors: Frank Zeyda and Simon Foster, University of York                  *)
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

theorem WF_ALPHABET_empty [simp] :
"{} \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_insert [simp] :
"\<lbrakk>a \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 (insert x a) \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_union [intro,simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<union> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_inter [intro,simp] :
"\<lbrakk>a1 \<in> WF_ALPHABET;
 a2 \<in> WF_ALPHABET\<rbrakk> \<Longrightarrow>
 a1 \<inter> a2 \<in> WF_ALPHABET"
apply (simp add: WF_ALPHABET_def)
done

theorem WF_ALPHABET_diff [intro,simp] :
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

theorem WF_ALPHABET_homalph [simp, intro] :
"a \<in> WF_ALPHABET \<Longrightarrow>
 homalph a \<in> WF_ALPHABET"
  by (simp add: homalph_def)

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
by (auto simp: utp_alphabet_simps)

theorem in_alphabet_ndash [simp] :
"dash x \<notin> in a"
by (simp add:utp_alphabet_simps dash_def)

theorem out_alphabet_ndash [simp] : 
"x \<in> out a \<Longrightarrow> dash x \<notin> out b"
by (simp add:utp_alphabet_simps dash_def)

theorem in_undashed [simp]:
"in a \<subseteq> UNDASHED"
  by (simp add: UNDASHED_def in_alphabet_def)

theorem out_undashed [simp]:
"out a \<subseteq> DASHED"
  by (simp add: DASHED_def out_alphabet_def)

theorem dash_undashed [simp]:
"a \<subseteq> UNDASHED \<Longrightarrow> dash ` a \<subseteq> DASHED"
  by (auto simp add: DASHED_def UNDASHED_def dash_def)

theorem dash_dashed [simp]:
"a \<subseteq> DASHED \<Longrightarrow> dash ` a \<subseteq> DASHED_TWICE"
  by (auto simp add: DASHED_def DASHED_TWICE_def dash_def)

theorem undash_dashed [simp]:
"a \<subseteq> DASHED \<Longrightarrow> undash ` a \<subseteq> UNDASHED"
  by (auto simp add: DASHED_def UNDASHED_def undash_def)

theorem undash_dashed_twice [simp]:
"a \<subseteq> DASHED_TWICE \<Longrightarrow> undash ` a \<subseteq> DASHED"
  by (auto simp add: DASHED_def DASHED_TWICE_def undash_def)

lemma out_undash: "a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> out (undash ` a) = {}"
  by (auto simp add:utp_alphabet_simps image_def undash_def)
 
lemma in_undash:"a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> in (undash ` a) = undash ` a"
  by (auto simp add:utp_alphabet_simps undash_def image_def)

lemma in_dash: "in (dash ` a) = {}"
  by (auto simp add:utp_alphabet_simps dash_def image_def)

lemma out_undash_out: "out (undash ` out a) = {}"
  by (auto simp add:utp_alphabet_simps undash_def image_def)

lemma out_dash_in: "out (dash ` in a) = dash ` in a"
  by (auto simp add:utp_alphabet_simps dash_def image_def)

theorem dash_undash[simp]: "dashes (name x) > 0 \<Longrightarrow> dash (undash x) = x"
  apply(auto simp add:dash_def undash_def)
  apply(smt NAME.surjective pair_collapse unit.exhaust)
done

theorem undash_dash[simp]: "undash (dash x) = x"
  apply(auto simp add:dash_def undash_def)
  apply(smt NAME.surjective pair_collapse unit.exhaust)
done
  
lemma dash_undash_out: "dash ` undash ` out a = out a"
  by (auto simp add:utp_alphabet_simps image_def)

lemma undash_dash' : "undash ` dash ` a = a"
  by (auto simp add:utp_alphabet_simps image_def)

lemma in_out_disj[simp]: "in a \<inter> out b = {}"
  by (auto simp add:in_alphabet_def out_alphabet_def DASHED_def UNDASHED_def)

lemma in_out_complete: "a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> in a \<union> out a = a"
  by (auto simp add:utp_alphabet_simps)

lemma override_out_in: "f \<oplus> (g \<oplus> h on (out a)) on (in b) = f \<oplus> g on (in b)"
  by (metis Diff_triv in_out_disj override_on_cancel4)
  
lemma override_in_out: "f \<oplus> (g \<oplus> h on (in a)) on (out b) = f \<oplus> g on (out b)"
  by (metis Diff_triv in_out_disj inf_commute override_on_cancel4)

lemma homalph_in[simp]: "in (homalph a) = in a \<union> undash ` out a"
  apply(simp add:homalph_def)
  apply (smt Un_commute Un_empty_left in_alphabet_def in_dash inf_absorb2 inf_commute le_infI1 order_refl out_alphabet_def undash_dashed)
done

lemma homalph_out[simp]: "out (homalph a) = out a \<union> dash ` in a"
  apply (simp add:homalph_def)
  apply(metis out_dash_in out_undash_out sup_bot_left)
done

lemma dash_dist_inter: "dash ` (x \<inter> y) = dash ` x \<inter> dash ` y"
  by (metis image_Int inj_dash)

lemma dash_dist_union: "dash ` (x \<union> y) = dash ` x \<union> dash ` y"
  by (metis image_Un)

lemma homalph_homogeneous: "HOMOGENEOUS (homalph a)"
  apply(simp add:HOMOGENEOUS_def)
  apply (metis VAR.dash_undash_out image_Un sup_commute)
done
  
lemma homogeneous_homalpha: "\<lbrakk> a \<subseteq> UNDASHED \<union> DASHED ; HOMOGENEOUS a \<rbrakk> \<Longrightarrow> homalph a = a"
apply(simp add:HOMOGENEOUS_def homalph_def)
  by (smt Int_Un_distrib Int_Un_distrib2 Un_absorb in_alphabet_def le_iff_inf out_alphabet_def undash_dash')

lemma homalpha_dashes[simp]: "homalph a \<subseteq> UNDASHED \<union> DASHED"
  by (metis Un_mono homalph_in homalph_out in_undashed out_undashed homalph_def)

lemma homalpha_subset[simp]: "a \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> a \<subseteq> homalph a"
proof (simp add:homalph_def)
  assume "a \<subseteq> UNDASHED \<union> DASHED"
  moreover hence "a = in a \<union> out a"
    by (metis in_out_complete)
  ultimately show "a \<subseteq> in a \<union> undash ` out a \<union> (out a \<union> dash ` in a)"
    by auto
qed


lemma homalpha_mono[simp]: "a \<subseteq> b \<Longrightarrow> homalph a \<subseteq> homalph b"
  by (auto simp add:homalph_def utp_alphabet_simps)

(*
lemma homalph_minus: "homalph (a - b) = homalph a - (b - homalph a)"
proof
  show "homalph (a - b) \<subseteq> homalph a - (b - homalph a)"
    by (metis Diff_disjoint Diff_subset Diff_triv homalpha_mono)
next
  show "homalph a - (b - homalph a) \<subseteq> homalph (a - b)"
    apply(auto)
    apply(simp add:homalph_def)
    apply(auto)
    apply (metis DiffI Int_iff in_alphabet_def)
    apply(simp add:image_def undash_def dash_def utp_alphabet_simps)
    apply(auto)
    apply(force)
    
  apply(clarify)
  apply(fast)


lemma homalpha_in_minus: "b \<subseteq> out a \<Longrightarrow> in (homalph (a - b)) = in (homalph a)"
proof
  assume assm:"b \<subseteq> out a"
  thus "in (homalph (a - b)) \<subseteq> in (homalph a)"
    by (metis Diff_subset VAR.homalpha_mono in_alphabet_def inf_mono set_eq_subset)

next
  assume assm:"b \<subseteq> out a"
  thus "in (homalph a) \<subseteq> in (homalph (a - b))"
    
  
 apply(simp add:homalph_def)
 apply(safe)
*)

end
end


