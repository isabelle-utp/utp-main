(* Title: ETTS/ETTS.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Extension of Types-To-Sets.
*)

section\<open>Isar commands and default settings for the ETTS\<close>
theory ETTS
  imports
    (*order is important*)
    "ETTS_Tools/ETTS_Tools"
    "Conditional_Transfer_Rule.CTR"
    "HOL-Types_To_Sets.Types_To_Sets"
    "HOL-Eisbach.Eisbach"
  keywords "tts_register_sbts" :: thy_goal_stmt
    and "tts_find_sbts" :: diag
    and "tts_theorem" "tts_lemma" "tts_corollary" "tts_proposition" :: 
      thy_goal_stmt
    and "tts_lemmas" :: thy_defn
    and "tts_context" :: thy_decl_block
    and "tts"
    and "to"
    and "sbterms"
    and "substituting"
    and "given"
    and "applying"
    and "rewriting"
    and "eliminating"
    and "through" 
begin



subsection\<open>Prerequisites\<close>


subsubsection\<open>Transfer for local typedef\<close>


text\<open>
The following content was ported from the content of the session 
\<open>Types_To_Sets\<close> in the main library of Isabelle/HOL with minor amendments.
\<close>

context
  fixes Rep Abs A T
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>(x::'a) (y::'b). x = Rep y)"
begin

lemma type_definition_Domainp': 
  "is_equality a \<Longrightarrow> Transfer.Rel a (Domainp T) (\<lambda>x. x \<in> A)"
proof -
  interpret type_definition Rep Abs A by (rule type)
  show "is_equality a \<Longrightarrow> Transfer.Rel a (Domainp T) (\<lambda>x. x \<in> A)"
    unfolding is_equality_def Transfer.Rel_def
    by (elim ssubst, unfold Domainp_iff[abs_def] T_def fun_eq_iff)  
      (metis Abs_inverse Rep)
qed

lemma type_definition_Domainp: "Domainp T = (\<lambda>x. x \<in> A)"
proof -
  interpret type_definition Rep Abs A by (rule type)
  show ?thesis
    unfolding Domainp_iff[abs_def] T_def fun_eq_iff by (metis Abs_inverse Rep)
qed

lemma type_definition_Rangep: "Rangep T = (\<lambda>x. True)"
proof -
  interpret type_definition Rep Abs A by (rule type)
  show ?thesis unfolding T_def by auto
qed

lemma 
  shows rep_in_S[simp]: "Rep x \<in> A" 
    and rep_inverse[simp]: "Abs (Rep x) = x" 
    and Abs_inverse[simp]: "y \<in> A \<Longrightarrow> Rep (Abs y) = y"
  using type unfolding type_definition_def by auto

end

lemmas [transfer_rule] = \<comment>\<open>prefer right-total rules\<close>
  right_total_All_transfer
  right_total_UNIV_transfer
  right_total_Ex_transfer


subsubsection\<open>Auxiliary\<close>

lemma ex_type_definition:   
  fixes A :: "['a, 'b] \<Rightarrow> bool"
  assumes "right_total A" and "bi_unique A"
  shows 
    "\<exists>(Rep::'b \<Rightarrow> 'a) (Abs::'a \<Rightarrow> 'b). 
      type_definition Rep Abs (Collect (Domainp A)) \<and> 
      (\<forall>b b'. A b b' = (b = Rep b'))"
proof(unfold type_definition_def, intro exI conjI; intro allI)
  define Rep :: "'b \<Rightarrow> 'a" where Rep: "Rep = (\<lambda>b'. (SOME b. A b b'))"
  define Abs :: "'a \<Rightarrow> 'b" where Abs: "Abs = (\<lambda>b. (SOME b'. A b b'))"
  have Rep_b: "A (Rep b') b'" for b'
    unfolding Rep by (metis assms(1) right_totalE verit_sko_ex')
  have Abs_a: "b \<in> Collect (Domainp A) \<Longrightarrow> A b (Abs b)" for b
    unfolding Abs by (simp add: assms(1) Domainp_iff someI_ex)
  show "Rep x \<in> Collect (Domainp A)" for x by (auto intro: Rep_b)
  show "Abs (Rep x) = x" for x 
    using assms(2) by (auto dest: bi_uniqueDr intro: Abs_a Rep_b)
  show "y \<in> Collect (Domainp A) \<longrightarrow> Rep (Abs y) = y" for y 
    using assms(2) by (auto dest: bi_uniqueDl intro: Abs_a Rep_b)
  show "A b b' = (b = Rep b')" for b b'
    using assms(2) by (meson Rep_b bi_uniqueDl)
qed

lemma ex_eq: "\<exists>x. x = t" by simp



subsection\<open>Import\<close>

ML_file\<open>ETTS_Tactics.ML\<close>
ML_file\<open>ETTS_Utilities.ML\<close>
ML_file\<open>ETTS_RI.ML\<close>
ML_file\<open>ETTS_Substitution.ML\<close>
ML_file\<open>ETTS_Context.ML\<close>
ML_file\<open>ETTS_Algorithm.ML\<close>
ML_file\<open>ETTS_Active.ML\<close>
ML_file\<open>ETTS_Lemma.ML\<close>
ML_file\<open>ETTS_Lemmas.ML\<close>



subsection\<open>Commands and attributes\<close>

ML \<open>
(* Adopted (with amendments) from the theory Pure.thy *)
ETTS_Lemma.tts_lemma \<^command_keyword>\<open>tts_theorem\<close> "tts theorem";
ETTS_Lemma.tts_lemma \<^command_keyword>\<open>tts_lemma\<close> "tts lemma";
ETTS_Lemma.tts_lemma \<^command_keyword>\<open>tts_corollary\<close> "tts corollary";
ETTS_Lemma.tts_lemma \<^command_keyword>\<open>tts_proposition\<close> "tts proposition";
\<close>



subsection\<open>Default settings\<close>


subsubsection\<open>\<^text>\<open>tts_implicit\<close>\<close>

named_theorems tts_implicit


subsubsection\<open>\<^text>\<open>tts_transfer_rule\<close>\<close>

lemmas [transfer_rule] =
  right_total_UNIV_transfer
  right_total_Collect_transfer
  right_total_Inter_transfer
  right_total_Compl_transfer
  finite_transfer
  image_transfer

end