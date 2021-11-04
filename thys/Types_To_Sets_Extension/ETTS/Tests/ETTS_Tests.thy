(* Title: ETTS/Tests/ETTS_Tests.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

A test suite for the ETTS.
*)

section\<open>A test suite for ETTS\<close>
theory ETTS_Tests
  imports
    "../ETTS_Auxiliary"
    Conditional_Transfer_Rule.IML_UT
begin



subsection\<open>\<open>amend_ctxt_data\<close>\<close>

ML_file\<open>ETTS_TEST_AMEND_CTXT_DATA.ML\<close>

locale test_amend_ctxt_data =
  fixes UA :: "'ao set" and UB :: "'bo set" and UC :: "'co set"
    and le :: "['ao, 'ao] \<Rightarrow> bool" (infix \<open>\<le>\<^sub>o\<^sub>w\<close> 50) 
    and ls :: "['bo, 'bo] \<Rightarrow> bool" (infix \<open><\<^sub>o\<^sub>w\<close> 50)
    and f :: "['ao, 'bo] \<Rightarrow> 'co"
  assumes closed_f: "a \<in> UA \<Longrightarrow> b \<in> UB \<Longrightarrow> f a b \<in> UC"
begin

notation le (\<open>'(\<le>\<^sub>o\<^sub>w')\<close>)
  and le (infix \<open>\<le>\<^sub>o\<^sub>w\<close> 50) 
  and ls (\<open>'(<\<^sub>o\<^sub>w')\<close>) 
  and ls (infix \<open><\<^sub>o\<^sub>w\<close> 50)

tts_register_sbts \<open>(\<le>\<^sub>o\<^sub>w)\<close> | UA
proof-
  assume "Domainp AOA = (\<lambda>x. x \<in> UA)" "bi_unique AOA" "right_total AOA" 
  from tts_AA_eq_transfer[OF this] show ?thesis by auto
qed

tts_register_sbts \<open>(<\<^sub>o\<^sub>w)\<close> | UB
proof-
  assume "Domainp BOA = (\<lambda>x. x \<in> UB)" "bi_unique BOA" "right_total BOA"
  from tts_AA_eq_transfer[OF this] show ?thesis by auto
qed

tts_register_sbts f | UA and UB and UC
proof-
  assume 
    "Domainp AOC = (\<lambda>x. x \<in> UA)" "bi_unique AOC" "right_total AOC"
    "Domainp BOB = (\<lambda>x. x \<in> UB)" "bi_unique BOB" "right_total BOB"
    "Domainp COA = (\<lambda>x. x \<in> UC)" "bi_unique COA" "right_total COA"
  from tts_AB_C_transfer[OF closed_f this] show ?thesis by auto
qed

end

context test_amend_ctxt_data
begin

ML\<open>
val tts_test_amend_ctxt_data_test_results =
  etts_test_amend_ctxt_data.execute_test_suite_amend_context_data @{context}
\<close>
ML\<open>
val _ = tts_test_amend_ctxt_data_test_results
  |> UT_Test_Suite.output_test_results true
\<close>

end



subsection\<open>\<open>tts_algorithm\<close>\<close>


text\<open>
Some of the elements of the content of this section are based on the 
elements of the content of \cite{cain_nine_2019}. 
\<close>

(*the following theorem is restated for forward compatibility*)
lemma exI': "P x \<Longrightarrow> \<exists>x. P x" by auto

class tta_mult =
  fixes tta_mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*\<^sub>t\<^sub>t\<^sub>a" 65)

class tta_semigroup = tta_mult +
  assumes tta_assoc[simp]: "(a *\<^sub>t\<^sub>t\<^sub>a b) *\<^sub>t\<^sub>t\<^sub>a c = a *\<^sub>t\<^sub>t\<^sub>a (b *\<^sub>t\<^sub>t\<^sub>a c)"

definition set_mult :: "'a::tta_mult set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "\<^bold>*\<^sub>t\<^sub>t\<^sub>a" 65) 
  where "set_mult S T = {s *\<^sub>t\<^sub>t\<^sub>a t | s t. s \<in> S \<and> t \<in> T}"

definition left_ideal :: "'a::tta_mult set \<Rightarrow> bool"
  where "left_ideal T \<longleftrightarrow> (\<forall>s. \<forall>t\<in>T. s *\<^sub>t\<^sub>t\<^sub>a t \<in> T)"

lemma left_idealI[intro]:
  assumes "\<And>s t. t \<in> T \<Longrightarrow> s *\<^sub>t\<^sub>t\<^sub>a t \<in> T"
  shows "left_ideal T"
  using assms unfolding left_ideal_def by simp

lemma left_idealE[elim]:
  assumes "left_ideal T"
  obtains "\<And>s t. t \<in> T \<Longrightarrow> s *\<^sub>t\<^sub>t\<^sub>a t \<in> T"
  using assms unfolding left_ideal_def by simp

lemma left_ideal_set_mult_iff: "left_ideal T \<longleftrightarrow> UNIV \<^bold>*\<^sub>t\<^sub>t\<^sub>a T \<subseteq> T"
  unfolding left_ideal_def set_mult_def by auto

ud \<open>set_mult\<close> 
ud \<open>left_ideal\<close>

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule]: "Domainp A = (\<lambda>x. x \<in> U)"
    and [transfer_rule]: "bi_unique A" "right_total A" 
  trp (?'a A)
  in set_mult_ow: set_mult.with_def 
    and left_ideal_ow: left_ideal.with_def 

locale tta_semigroup_hom =
  fixes f :: "'a::tta_semigroup \<Rightarrow> 'b::tta_semigroup"
  assumes hom: "f (a *\<^sub>t\<^sub>t\<^sub>a b) = f a *\<^sub>t\<^sub>t\<^sub>a f b"

context tta_semigroup_hom
begin

lemma tta_left_ideal_closed:
  assumes "left_ideal T" and "surj f"
  shows "left_ideal (f ` T)"
  unfolding left_ideal_def
proof(intro allI ballI)
  fix fs ft assume prems: "ft \<in> f ` T"
  then obtain t where t: "t \<in> T" and ft_def: "ft = f t" by clarsimp
  from assms(2) obtain s where fs_def: "fs = f s" by auto
  from assms have "t \<in> T \<Longrightarrow> s *\<^sub>t\<^sub>t\<^sub>a t \<in> T" for s t by auto
  with t show "fs *\<^sub>t\<^sub>t\<^sub>a ft \<in> f ` T" 
    unfolding ft_def fs_def hom[symmetric] by simp
qed

end

locale semigroup_mult_hom_with = 
  dom: tta_semigroup times_a + cod: tta_semigroup times_b
  for times_a (infixl \<open>*\<^sub>o\<^sub>w\<^sub>.\<^sub>a\<close> 70) and times_b (infixl \<open>*\<^sub>o\<^sub>w\<^sub>.\<^sub>b\<close> 70) +
  fixes f :: "'a \<Rightarrow> 'b"
  assumes f_hom: "f (a *\<^sub>o\<^sub>w\<^sub>.\<^sub>a b) = f a *\<^sub>o\<^sub>w\<^sub>.\<^sub>b f b"

lemma semigroup_mult_hom_with[ud_with]:
  "tta_semigroup_hom = semigroup_mult_hom_with (*\<^sub>t\<^sub>t\<^sub>a) (*\<^sub>t\<^sub>t\<^sub>a)"
  unfolding 
    semigroup_mult_hom_with_def tta_semigroup_hom_def 
    class.tta_semigroup_def semigroup_mult_hom_with_axioms_def
  by auto

locale semigroup_ow = 
  fixes U :: "'ag set" and f :: "['ag, 'ag] \<Rightarrow> 'ag" (infixl \<open>\<^bold>*\<^sub>o\<^sub>w\<close> 70)
  assumes f_closed: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<^bold>*\<^sub>o\<^sub>w b \<in> U"
    and assoc: "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a \<^bold>*\<^sub>o\<^sub>w b \<^bold>*\<^sub>o\<^sub>w c = a \<^bold>*\<^sub>o\<^sub>w (b \<^bold>*\<^sub>o\<^sub>w c)"
begin

notation f (infixl \<open>\<^bold>*\<^sub>o\<^sub>w\<close> 70)

lemma f_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x \<^bold>*\<^sub>o\<^sub>w y \<in> U" by (simp add: f_closed)

tts_register_sbts \<open>(\<^bold>*\<^sub>o\<^sub>w)\<close> | U by (rule tts_AA_A_transfer[OF f_closed])

end

locale times_ow =
  fixes U :: "'ag set" and times :: "['ag, 'ag] \<Rightarrow> 'ag" (infixl \<open>*\<^sub>o\<^sub>w\<close> 70)
  assumes times_closed[simp, intro]: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w b \<in> U"
begin

notation times (infixl \<open>*\<^sub>o\<^sub>w\<close> 70)

lemma times_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x *\<^sub>o\<^sub>w y \<in> U" by simp

tts_register_sbts \<open>(*\<^sub>o\<^sub>w)\<close> | U  by (rule tts_AA_A_transfer[OF times_closed])

end

locale semigroup_mult_ow = times_ow U times 
  for U :: "'ag set" and times +
  assumes mult_assoc: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a *\<^sub>o\<^sub>w b *\<^sub>o\<^sub>w c = a *\<^sub>o\<^sub>w (b *\<^sub>o\<^sub>w c)"
begin

sublocale mult: semigroup_ow U \<open>(*\<^sub>o\<^sub>w)\<close> 
  by unfold_locales (auto simp: times_closed' mult_assoc)

end

locale semigroup_mult_hom_ow = 
  dom: semigroup_mult_ow UA times_a + 
  cod: semigroup_mult_ow UB times_b 
  for UA :: "'a set" 
    and UB :: "'b set" 
    and times_a (infixl \<open>*\<^sub>o\<^sub>w\<^sub>.\<^sub>a\<close> 70) 
    and times_b (infixl \<open>*\<^sub>o\<^sub>w\<^sub>.\<^sub>b\<close> 70) +
  fixes f :: "'a \<Rightarrow> 'b"
  assumes f_closed[simp]: "a \<in> UA \<Longrightarrow> f a \<in> UB"
    and f_hom: "\<lbrakk> a \<in> UA; b \<in> UA \<rbrakk> \<Longrightarrow> f (a *\<^sub>o\<^sub>w\<^sub>.\<^sub>a b) = f a *\<^sub>o\<^sub>w\<^sub>.\<^sub>b f b"
begin

lemma f_closed'[simp]: "f ` UA \<subseteq> UB" by auto

tts_register_sbts f | UA and UB by (rule tts_AB_transfer[OF f_closed'])

end

context semigroup_mult_hom_ow
begin

lemma tta_left_ideal_ow_closed:
  assumes "T \<subseteq> UA"
    and "left_ideal_ow UA (*\<^sub>o\<^sub>w\<^sub>.\<^sub>a) T"
    and "f ` UA = UB"
  shows "left_ideal_ow UB (*\<^sub>o\<^sub>w\<^sub>.\<^sub>b) (f ` T)"
  unfolding left_ideal_ow_def
proof(intro ballI)
  fix fs ft assume ft: "ft \<in> f ` T" and fs: "fs \<in> UB"
  then obtain t where t: "t \<in> T" and ft_def: "ft = f t" by auto
  from assms(3) fs obtain s where fs_def: "fs = f s" and s: "s \<in> UA" by auto
  from assms have "\<lbrakk> s \<in> UA; t \<in> T \<rbrakk> \<Longrightarrow> s *\<^sub>o\<^sub>w\<^sub>.\<^sub>a t \<in> T" for s t 
    unfolding left_ideal_ow_def by simp
  with assms(1) s t fs show "fs *\<^sub>o\<^sub>w\<^sub>.\<^sub>b ft \<in> f ` T" 
    using f_hom[symmetric, OF s] unfolding ft_def fs_def by auto
qed

end

lemma semigroup_mult_ow: "class.tta_semigroup = semigroup_mult_ow UNIV"
  unfolding 
    class.tta_semigroup_def semigroup_mult_ow_def
    semigroup_mult_ow_axioms_def times_ow_def
  by simp

lemma semigroup_mult_hom_ow: 
  "tta_semigroup_hom = semigroup_mult_hom_ow UNIV UNIV (*\<^sub>t\<^sub>t\<^sub>a) (*\<^sub>t\<^sub>t\<^sub>a)"
  unfolding 
    tta_semigroup_hom_def semigroup_mult_hom_ow_axioms_def
    semigroup_mult_hom_ow_def semigroup_mult_ow_def 
    semigroup_mult_ow_axioms_def times_ow_def
  by simp

context
  includes lifting_syntax
begin

lemma semigroup_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=))
      (semigroup_ow (Collect (Domainp A))) semigroup"
proof-
  let ?P = "((A ===> A ===> A) ===> (=))"
  let ?semigroup_ow = "semigroup_ow (Collect (Domainp A))"
  let ?rf_UNIV = 
    "(\<lambda>f::['b, 'b] \<Rightarrow> 'b. (\<forall>x y. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> f x y \<in> UNIV))"
  have "?P ?semigroup_ow (\<lambda>f. ?rf_UNIV f \<and> semigroup f)"
    unfolding semigroup_ow_def semigroup_def
    apply transfer_prover_start
    apply transfer_step+
    by simp
  thus ?thesis by simp
qed

lemma semigroup_mult_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows
    "((A ===> A ===> A) ===> (=))
      (semigroup_mult_ow (Collect (Domainp A)))
      class.tta_semigroup"
proof -
  let ?P = \<open>((A ===> A ===> A) ===> (=))\<close>
    and ?semigroup_mult_ow = 
      \<open>(\<lambda>f. semigroup_mult_ow (Collect (Domainp A)) f)\<close>
    and ?rf_UNIV = 
      \<open>(\<lambda>f::['b, 'b] \<Rightarrow> 'b. (\<forall>x y. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> f x y \<in> UNIV))\<close>
  have "?P ?semigroup_mult_ow (\<lambda>f. ?rf_UNIV f \<and> class.tta_semigroup f)"
    unfolding 
      semigroup_mult_ow_def class.tta_semigroup_def
      semigroup_mult_ow_axioms_def times_ow_def
    apply transfer_prover_start
    apply transfer_step+
    by simp
  thus ?thesis by simp
qed

lemma semigroup_mult_hom_transfer[transfer_rule]:
  assumes [transfer_rule]: 
    "bi_unique A" "right_total A" "bi_unique B" "right_total B" 
  shows
    "((A ===> A ===> A) ===> (B ===> B ===> B) ===> (A ===> B) ===> (=))
      (semigroup_mult_hom_ow (Collect (Domainp A)) (Collect (Domainp B)))
      semigroup_mult_hom_with"
proof-
  let ?PA = "A ===> A ===> A"
    and ?PB = "B ===> B ===> B"
    and ?semigroup_mult_hom_ow = 
      \<open>
        \<lambda>times_a times_b f. semigroup_mult_hom_ow 
          (Collect (Domainp A)) (Collect (Domainp B)) times_a times_b f
      \<close>
  let ?closed = \<open>\<lambda>f::'b\<Rightarrow>'d . \<forall>a. a \<in> UNIV \<longrightarrow> f a \<in> UNIV\<close>
  have
    "(?PA ===> ?PB ===> (A ===> B) ===> (=))
      ?semigroup_mult_hom_ow
      (
        \<lambda>times_a times_b f. 
          ?closed f \<and> semigroup_mult_hom_with times_a times_b f
      )"
    unfolding 
      times_ow_def
      semigroup_mult_hom_ow_def 
      semigroup_mult_hom_ow_axioms_def 
      semigroup_mult_hom_with_def
      semigroup_mult_hom_with_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by blast
  thus ?thesis by simp
qed

end

context semigroup_mult_hom_ow
begin

ML_file\<open>ETTS_TEST_TTS_ALGORITHM.ML\<close>

named_theorems semigroup_mult_hom_ow_test_simps

lemmas [semigroup_mult_hom_ow_test_simps] = 
  ctr_simps_Collect_mem_eq
  ctr_simps_in_iff

tts_context
  tts: (?'a to UA) and (?'b to UB)
  sbterms: (\<open>(*\<^sub>t\<^sub>t\<^sub>a)::[?'a::tta_semigroup, ?'a] \<Rightarrow> ?'a\<close> to \<open>(*\<^sub>o\<^sub>w\<^sub>.\<^sub>a)\<close>)
    and (\<open>(*\<^sub>t\<^sub>t\<^sub>a)::[?'b::tta_semigroup, ?'b] \<Rightarrow> ?'b\<close> to \<open>(*\<^sub>o\<^sub>w\<^sub>.\<^sub>b)\<close>)
    and (\<open>?f::?'a::tta_semigroup \<Rightarrow> ?'b::tta_semigroup\<close> to f)
  rewriting semigroup_mult_hom_ow_test_simps
  substituting semigroup_mult_hom_ow_axioms
    and dom.semigroup_mult_ow_axioms
    and cod.semigroup_mult_ow_axioms
  eliminating \<open>UA \<noteq> {}\<close> and \<open>UB \<noteq> {}\<close> 
    through (auto simp only: left_ideal_ow_def)
begin

ML\<open>
val tts_test_amend_ctxt_data_test_results =
  etts_test_tts_algorithm.execute_test_suite_tts_algorithm @{context}
\<close>
ML\<open>
val _ = tts_test_amend_ctxt_data_test_results
  |> UT_Test_Suite.output_test_results true
\<close>

end

end



subsection\<open>\<open>tts_register_sbts\<close>\<close>

context 
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
    and UA :: "'a set"
begin

ML_file\<open>ETTS_TEST_TTS_REGISTER_SBTS.ML\<close>
ML\<open>
val tts_test_tts_register_sbts_test_results =
  etts_test_tts_register_sbts.execute_test_suite_tts_register_sbts @{context}
\<close>
ML\<open>
val _ = tts_test_tts_register_sbts_test_results
  |> UT_Test_Suite.output_test_results true
\<close>

end

end