(*<*)
theory LTL
imports
  CIMP_pred
  Infinite_Sequences
begin

(*>*)
section\<open> Linear Temporal Logic \label{sec:ltl}\<close>

text\<open>

To talk about liveness we need to consider infinitary behaviour on
sequences. Traditionally future-time linear temporal logic (LTL) is used to do
this @{cite "MannaPnueli:1991" and "OwickiLamport:1982"}.

The following is a straightforward shallow embedding of the
now-traditional anchored semantics of LTL @{cite "MannaPnueli:1988"}. Some of it is adapted
from the sophisticated TLA development in the AFP due to @{cite [cite_macro=citet] "TLA-AFP"}.

Unlike @{cite [cite_macro=citet] "Lamport:2002"}, include the
next operator, which is convenient for stating rules. Sometimes it allows us to
ignore the system, i.e. to state rules as temporally valid
(LTL-valid) rather than just temporally program valid (LTL-cimp-), in Jackson's terminology.

\<close>

definition state_prop :: "('a \<Rightarrow> bool) \<Rightarrow> 'a seq_pred" ("\<lceil>_\<rceil>") where
  "\<lceil>P\<rceil> = (\<lambda>\<sigma>. P (\<sigma> 0))"

definition "next" :: "'a seq_pred \<Rightarrow> 'a seq_pred" ("\<circle>_" [80] 80) where
  "(\<circle>P) = (\<lambda>\<sigma>. P (\<sigma> |\<^sub>s 1))"

definition always :: "'a seq_pred \<Rightarrow> 'a seq_pred" ("\<box>_" [80] 80) where
  "(\<box>P) = (\<lambda>\<sigma>. \<forall>i. P (\<sigma> |\<^sub>s i))"

definition until :: "'a seq_pred \<Rightarrow> 'a seq_pred \<Rightarrow> 'a seq_pred" (infixr "\<U>" 30) where (* FIXME priority, binds tighter than \<^bold>\<longrightarrow> *)
  "(P \<U> Q) = (\<lambda>\<sigma>. \<exists>i. Q (\<sigma> |\<^sub>s i) \<and> (\<forall>k<i. P (\<sigma> |\<^sub>s k)))"

definition eventually :: "'a seq_pred \<Rightarrow> 'a seq_pred" ("\<diamond>_" [80] 80) where (* FIXME priority, consider making an abbreviation *)
  "(\<diamond>P) = (\<langle>True\<rangle> \<U> P)"

definition release :: "'a seq_pred \<Rightarrow> 'a seq_pred \<Rightarrow> 'a seq_pred" (infixr "\<R>" 30) where (* FIXME priority, dual of Until *)
  "(P \<R> Q) = (\<^bold>\<not>(\<^bold>\<not>P \<U> \<^bold>\<not>Q))"

definition unless :: "'a seq_pred \<Rightarrow> 'a seq_pred \<Rightarrow> 'a seq_pred" (infixr "\<W>" 30) where (* FIXME priority, aka weak until *)
  "(P \<W> Q) = ((P \<U> Q) \<^bold>\<or> \<box>P)"

abbreviation (input)
  pred_always_imp_syn :: "'a seq_pred \<Rightarrow> 'a seq_pred \<Rightarrow> 'a seq_pred" (infixr "\<^bold>\<hookrightarrow>" 25) where
  "P \<^bold>\<hookrightarrow> Q \<equiv> \<box>(P \<^bold>\<longrightarrow> Q)"

lemmas defs =
  state_prop_def
  always_def
  eventually_def
  next_def
  release_def
  unless_def
  until_def

lemma suffix_state_prop[simp]:
  shows "\<lceil>P\<rceil> (\<sigma> |\<^sub>s i) = P (\<sigma> i)"
unfolding defs by simp

lemma alwaysI[intro]:
  assumes "\<And>i. P (\<sigma> |\<^sub>s i)"
  shows "(\<box>P) \<sigma>"
unfolding defs using assms by blast

lemma alwaysD:
  assumes "(\<box>P) \<sigma>"
  shows "P (\<sigma> |\<^sub>s i)"
using assms unfolding defs by blast

lemma alwaysE: "\<lbrakk>(\<box>P) \<sigma>; P (\<sigma> |\<^sub>s i) \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding defs by blast

lemma always_induct:
  assumes "P \<sigma>"
  assumes "(\<box>(P \<^bold>\<longrightarrow> \<circle>P)) \<sigma>"
  shows "(\<box>P) \<sigma>"
proof(rule alwaysI)
  fix i from assms show "P (\<sigma> |\<^sub>s i)"
    unfolding defs by (induct i) simp_all
qed

lemma seq_comp:
  fixes \<sigma> :: "'a seq"
  fixes P :: "'b seq_pred"
  fixes f :: "'a \<Rightarrow> 'b"
  shows
    "(\<box>P) (f \<circ> \<sigma>) \<longleftrightarrow> (\<box>(\<lambda>\<sigma>. P (f \<circ> \<sigma>))) \<sigma>"
    "(\<diamond>P) (f \<circ> \<sigma>) \<longleftrightarrow> (\<diamond>(\<lambda>\<sigma>. P (f \<circ> \<sigma>))) \<sigma>"
    "(P \<U> Q) (f \<circ> \<sigma>) \<longleftrightarrow> ((\<lambda>\<sigma>. P (f \<circ> \<sigma>)) \<U> (\<lambda>\<sigma>. Q (f \<circ> \<sigma>))) \<sigma>"
    "(P \<W> Q) (f \<circ> \<sigma>) \<longleftrightarrow> ((\<lambda>\<sigma>. P (f \<circ> \<sigma>)) \<W> (\<lambda>\<sigma>. Q (f \<circ> \<sigma>))) \<sigma>"
unfolding defs by simp_all

lemma nextI[intro]:
  assumes "P (\<sigma> |\<^sub>s Suc 0)"
  shows "(\<circle>P) \<sigma>"
using assms unfolding defs by simp

lemma untilI[intro]:
  assumes "Q (\<sigma> |\<^sub>s i)"
  assumes "\<forall>k<i. P (\<sigma> |\<^sub>s k)"
  shows "(P \<U> Q) \<sigma>"
unfolding defs using assms by blast

lemma untilE:
  assumes "(P \<U> Q) \<sigma>"
  obtains i where "Q (\<sigma> |\<^sub>s i)" and "\<forall>k<i. P (\<sigma> |\<^sub>s k)"
using assms unfolding until_def by blast

lemma eventuallyI[intro]:
  assumes "P (\<sigma> |\<^sub>s i)"
  shows "(\<diamond>P) \<sigma>"
unfolding eventually_def using assms by blast

lemma eventuallyE[elim]:
  assumes "(\<diamond>P) \<sigma>"
  obtains i where "P (\<sigma> |\<^sub>s i)"
using assms unfolding defs by (blast elim: untilE)

lemma unless_alwaysI:
  assumes "(\<box> P) \<sigma>"
  shows "(P \<W> Q) \<sigma>"
using assms unfolding defs by blast

lemma unless_untilI:
  assumes "Q (\<sigma> |\<^sub>s j)"
  assumes "\<And>i. i < j \<Longrightarrow> P (\<sigma> |\<^sub>s i)"
  shows "(P \<W> Q) \<sigma>"
unfolding defs using assms by blast

lemma always_imp_refl[iff]:
  shows "(P \<^bold>\<hookrightarrow> P) \<sigma>"
unfolding defs by blast

lemma always_imp_trans:
  assumes "(P \<^bold>\<hookrightarrow> Q) \<sigma>"
  assumes "(Q \<^bold>\<hookrightarrow> R) \<sigma>"
  shows "(P \<^bold>\<hookrightarrow> R) \<sigma>"
using assms unfolding defs by blast

lemma always_imp_mp:
  assumes "(P \<^bold>\<hookrightarrow> Q) \<sigma>"
  assumes "P \<sigma>"
  shows "Q \<sigma>"
using assms unfolding defs by (metis suffix_zero)

lemma always_imp_mp_suffix:
  assumes "(P \<^bold>\<hookrightarrow> Q) \<sigma>"
  assumes "P (\<sigma> |\<^sub>s i)"
  shows "Q (\<sigma> |\<^sub>s i)"
using assms unfolding defs by metis

text\<open>

Some basic facts and equivalences, mostly sanity.

\<close>

lemma necessitation:
  "(\<And>s. P s) \<Longrightarrow> (\<box>P) \<sigma>"
  "(\<And>s. P s) \<Longrightarrow> (\<diamond>P) \<sigma>"
  "(\<And>s. P s) \<Longrightarrow> (P \<W> Q) \<sigma>"
  "(\<And>s. Q s) \<Longrightarrow> (P \<U> Q) \<sigma>"
unfolding defs by auto

lemma cong:
  "(\<And>s. P s = P' s) \<Longrightarrow> \<lceil>P\<rceil> = \<lceil>P'\<rceil>"
  "(\<And>\<sigma>. P \<sigma> = P' \<sigma>) \<Longrightarrow> (\<box>P) = (\<box>P')"
  "(\<And>\<sigma>. P \<sigma> = P' \<sigma>) \<Longrightarrow> (\<diamond>P) = (\<diamond>P')"
  "(\<And>\<sigma>. P \<sigma> = P' \<sigma>) \<Longrightarrow> (\<circle>P) = (\<circle>P')"
  "\<lbrakk>\<And>\<sigma>. P \<sigma> = P' \<sigma>; \<And>\<sigma>. Q \<sigma> = Q' \<sigma>\<rbrakk> \<Longrightarrow> (P \<U> Q) = (P' \<U> Q')"
  "\<lbrakk>\<And>\<sigma>. P \<sigma> = P' \<sigma>; \<And>\<sigma>. Q \<sigma> = Q' \<sigma>\<rbrakk> \<Longrightarrow> (P \<W> Q) = (P' \<W> Q')"
unfolding defs by auto

lemma norm[simp]:
  "\<lceil>\<langle>False\<rangle>\<rceil> = \<langle>False\<rangle>"
  "\<lceil>\<langle>True\<rangle>\<rceil> = \<langle>True\<rangle>"
  "(\<^bold>\<not>\<lceil>p\<rceil>) = \<lceil>\<^bold>\<not>p\<rceil>"
  "(\<lceil>p\<rceil> \<^bold>\<and> \<lceil>q\<rceil>) = \<lceil>p \<^bold>\<and> q\<rceil>"
  "(\<lceil>p\<rceil> \<^bold>\<or> \<lceil>q\<rceil>) = \<lceil>p \<^bold>\<or> q\<rceil>"
  "(\<lceil>p\<rceil> \<^bold>\<longrightarrow> \<lceil>q\<rceil>) = \<lceil>p \<^bold>\<longrightarrow> q\<rceil>"
  "(\<lceil>p\<rceil> \<sigma> \<and> \<lceil>q\<rceil> \<sigma>) = \<lceil>p \<^bold>\<and> q\<rceil> \<sigma>"
  "(\<lceil>p\<rceil> \<sigma> \<or> \<lceil>q\<rceil> \<sigma>) = \<lceil>p \<^bold>\<or> q\<rceil> \<sigma>"
  "(\<lceil>p\<rceil> \<sigma> \<longrightarrow> \<lceil>q\<rceil> \<sigma>) = \<lceil>p \<^bold>\<longrightarrow> q\<rceil> \<sigma>"

  "(\<circle>\<langle>False\<rangle>) = \<langle>False\<rangle>"
  "(\<circle>\<langle>True\<rangle>) = \<langle>True\<rangle>"

  "(\<box>\<langle>False\<rangle>) = \<langle>False\<rangle>"
  "(\<box>\<langle>True\<rangle>) = \<langle>True\<rangle>"
  "(\<^bold>\<not>\<box> P) \<sigma> = (\<diamond> (\<^bold>\<not> P)) \<sigma>"
  "(\<box>\<box> P) = (\<box> P)"

  "(\<diamond>\<langle>False\<rangle>) = \<langle>False\<rangle>"
  "(\<diamond>\<langle>True\<rangle>) = \<langle>True\<rangle>"
  "(\<^bold>\<not>\<diamond> P) = (\<box> (\<^bold>\<not> P))"
  "(\<diamond>\<diamond> P) = (\<diamond> P)"

  "(P \<W> \<langle>False\<rangle>) = (\<box> P)"

  "(\<^bold>\<not>(P \<U> Q)) \<sigma> = (\<^bold>\<not>P \<R> \<^bold>\<not>Q) \<sigma>"
  "(\<langle>False\<rangle> \<U> P) = P"
  "(P \<U> \<langle>False\<rangle>) = \<langle>False\<rangle>"
  "(P \<U> \<langle>True\<rangle>) = \<langle>True\<rangle>"
  "(\<langle>True\<rangle> \<U> P) = (\<diamond> P)"
  "(P \<U> (P \<U> Q)) = (P \<U> Q)"

  "(\<^bold>\<not>(P \<R> Q)) \<sigma> = (\<^bold>\<not>P \<U> \<^bold>\<not>Q) \<sigma>"
  "(\<langle>False\<rangle> \<R> P) = (\<box>P)"
  "(P \<R> \<langle>False\<rangle>) = \<langle>False\<rangle>"
  "(\<langle>True\<rangle> \<R> P) = P"
  "(P \<R> \<langle>True\<rangle>) = \<langle>True\<rangle>"
(*
  "(P \<U> (P \<U> Q)) \<sigma> = (P \<U> Q) \<sigma>" FIXME for Release
*)
unfolding defs
apply (auto simp: fun_eq_iff)
apply (metis suffix_plus suffix_zero)
apply (metis suffix_plus suffix_zero)
  apply fastforce
  apply force
apply (metis add.commute add_diff_inverse_nat less_diff_conv2 not_le)
apply (metis add.right_neutral not_less0)
  apply force
  apply fastforce
done

lemma always_conj_distrib: "(\<box>(P \<^bold>\<and> Q)) = (\<box>P \<^bold>\<and> \<box>Q)"
unfolding defs by auto

lemma eventually_disj_distrib: "(\<diamond>(P \<^bold>\<or> Q)) = (\<diamond>P \<^bold>\<or> \<diamond>Q)"
unfolding defs by auto

lemma always_eventually[elim!]:
  assumes "(\<box>P) \<sigma>"
  shows "(\<diamond>P) \<sigma>"
using assms unfolding defs by auto

lemma eventually_imp_conv_disj: "(\<diamond>(P \<^bold>\<longrightarrow> Q)) = (\<diamond>(\<^bold>\<not>P) \<^bold>\<or> \<diamond>Q)"
unfolding defs by auto

lemma eventually_imp_distrib:
  "(\<diamond>(P \<^bold>\<longrightarrow> Q)) = (\<box>P \<^bold>\<longrightarrow> \<diamond>Q)"
unfolding defs by auto

lemma unfold:
  "(\<box> P) \<sigma> = (P \<^bold>\<and> \<circle>\<box>P) \<sigma>"
  "(\<diamond> P) \<sigma> = (P \<^bold>\<or> \<circle>\<diamond>P) \<sigma>"
  "(P \<W> Q) \<sigma> = (Q \<^bold>\<or> (P \<^bold>\<and> \<circle>(P \<W> Q))) \<sigma>"
  "(P \<U> Q) \<sigma> = (Q \<^bold>\<or> (P \<^bold>\<and> \<circle>(P \<U> Q))) \<sigma>"
  "(P \<R> Q) \<sigma> = (Q \<^bold>\<and> (P \<^bold>\<or> \<circle>(P \<R> Q))) \<sigma>"
unfolding defs
apply -
apply (metis (full_types) add.commute add_diff_inverse_nat less_one suffix_plus suffix_zero)
apply (metis (full_types) One_nat_def add.right_neutral add_Suc_right lessI less_Suc_eq_0_disj suffix_plus suffix_zero)

apply auto
  apply fastforce
  apply (metis gr0_conv_Suc nat_neq_iff not_less_eq suffix_zero)
  apply (metis suffix_zero)
  apply force
  using less_Suc_eq_0_disj apply fastforce
  apply (metis gr0_conv_Suc nat_neq_iff not_less0 suffix_zero)

  apply fastforce
  apply (case_tac i; auto)
  apply force
  using less_Suc_eq_0_disj apply force

  apply force
  using less_Suc_eq_0_disj apply fastforce
  apply fastforce
  apply (case_tac i; auto)
done

lemma mono:
  "\<lbrakk>(\<box>P) \<sigma>; \<And>\<sigma>. P \<sigma> \<Longrightarrow>  P' \<sigma>\<rbrakk> \<Longrightarrow> (\<box>P') \<sigma>"
  "\<lbrakk>(\<diamond>P) \<sigma>; \<And>\<sigma>. P \<sigma> \<Longrightarrow>  P' \<sigma>\<rbrakk> \<Longrightarrow> (\<diamond>P') \<sigma>"
  "\<lbrakk>(P \<U> Q) \<sigma>; \<And>\<sigma>. P \<sigma> \<Longrightarrow> P' \<sigma>; \<And>\<sigma>. Q \<sigma> \<Longrightarrow> Q' \<sigma>\<rbrakk> \<Longrightarrow> (P' \<U> Q') \<sigma>"
  "\<lbrakk>(P \<W> Q) \<sigma>; \<And>\<sigma>. P \<sigma> \<Longrightarrow> P' \<sigma>; \<And>\<sigma>. Q \<sigma> \<Longrightarrow> Q' \<sigma>\<rbrakk> \<Longrightarrow> (P' \<W> Q') \<sigma>"
unfolding defs by force+

lemma always_imp_mono:
  "\<lbrakk>(\<box>P) \<sigma>; (P \<^bold>\<hookrightarrow> P') \<sigma>\<rbrakk> \<Longrightarrow> (\<box>P') \<sigma>"
  "\<lbrakk>(\<diamond>P) \<sigma>; (P \<^bold>\<hookrightarrow> P') \<sigma>\<rbrakk> \<Longrightarrow> (\<diamond>P') \<sigma>"
  "\<lbrakk>(P \<U> Q) \<sigma>; (P \<^bold>\<hookrightarrow> P') \<sigma>; (Q \<^bold>\<hookrightarrow> Q') \<sigma>\<rbrakk> \<Longrightarrow> (P' \<U> Q') \<sigma>"
  "\<lbrakk>(P \<W> Q) \<sigma>; (P \<^bold>\<hookrightarrow> P') \<sigma>; (Q \<^bold>\<hookrightarrow> Q') \<sigma>\<rbrakk> \<Longrightarrow> (P' \<W> Q') \<sigma>"
unfolding defs by force+

lemma next_conj_distrib:
  "(\<circle>(P \<^bold>\<and> Q)) = (\<circle>P \<^bold>\<and> \<circle>Q)"
unfolding defs by auto

lemma next_disj_distrib:
  "(\<circle>(P \<^bold>\<or> Q)) = (\<circle>P \<^bold>\<or> \<circle>Q)"
unfolding defs by auto

lemma until_next_distrib:
  "(\<circle>(P \<U> Q)) = (\<circle>P \<U> \<circle>Q)"
unfolding defs by (auto simp: fun_eq_iff)

lemma until_imp_eventually:
  "((P \<U> Q) \<^bold>\<longrightarrow> \<diamond>Q) \<sigma>"
unfolding defs by auto

lemma until_until_disj:
  assumes "(P \<U> Q \<U> R) \<sigma>"
  shows "((P \<^bold>\<or> Q) \<U> R) \<sigma>"
using assms unfolding defs
apply clarsimp
apply (metis (full_types) add_diff_inverse_nat nat_add_left_cancel_less)
done

lemma unless_unless_disj:
  assumes "(P \<W> Q \<W> R) \<sigma>"
  shows "((P \<^bold>\<or> Q) \<W> R) \<sigma>"
using assms unfolding defs
apply auto
 apply (metis add.commute add_diff_inverse_nat leI less_diff_conv2)
apply (metis add_diff_inverse_nat)
done

lemma until_conj_distrib:
  "((P \<^bold>\<and> Q) \<U> R) = ((P \<U> R) \<^bold>\<and> (Q \<U> R))"
unfolding defs
apply (auto simp: fun_eq_iff)
apply (metis dual_order.strict_trans nat_neq_iff)
done

lemma until_disj_distrib:
  "(P \<U> (Q \<^bold>\<or> R)) = ((P \<U> Q) \<^bold>\<or> (P \<U> R))"
unfolding defs by (auto simp: fun_eq_iff)

lemma eventually_until:
  "(\<diamond>P) = (\<^bold>\<not>P \<U> P)"
unfolding defs
apply (auto simp: fun_eq_iff)
apply (case_tac "P (x |\<^sub>s 0)")
 apply blast
apply (drule (1) ex_least_nat_less)
apply (metis le_simps(2))
done

lemma eventually_until_eventually:
  "(\<diamond>(P \<U> Q)) = (\<diamond>Q)"
unfolding defs by force

lemma eventually_unless_until:
  "((P \<W> Q) \<^bold>\<and> \<diamond>Q) = (P \<U> Q)"
unfolding defs by force

lemma eventually_always_imp_always_eventually:
  assumes "(\<diamond>\<box>P) \<sigma>"
  shows "(\<box>\<diamond>P) \<sigma>"
using assms unfolding defs by (metis suffix_commute)

lemma eventually_always_next_stable:
  assumes "(\<diamond>P) \<sigma>"
  assumes "(P \<^bold>\<hookrightarrow> \<circle>P) \<sigma>"
  shows "(\<diamond>\<box>P) \<sigma>"
using assms by (metis (no_types) eventuallyI alwaysD always_induct eventuallyE norm(15))

lemma next_stable_imp_eventually_always:
  assumes "(P \<^bold>\<hookrightarrow> \<circle>P) \<sigma>"
  shows "(\<diamond>P \<^bold>\<longrightarrow> \<diamond>\<box>P) \<sigma>"
using assms eventually_always_next_stable by blast

lemma always_eventually_always:
  "\<diamond>\<box>\<diamond>P = \<box>\<diamond>P"
unfolding defs by (clarsimp simp: fun_eq_iff) (metis add.left_commute semiring_normalization_rules(25))

(* FIXME define "stable", develop more rules for it *)
lemma stable_unless:
  assumes "(P \<^bold>\<hookrightarrow> \<circle>(P \<^bold>\<or> Q)) \<sigma>"
  shows "(P \<^bold>\<hookrightarrow> (P \<W> Q)) \<sigma>"
using assms unfolding defs
apply -
apply (rule ccontr)
apply clarsimp
apply (drule (1) ex_least_nat_less[where P="\<lambda>j. \<not>P (\<sigma> |\<^sub>s i + j)" for i, simplified])
apply clarsimp
apply (metis add_Suc_right le_less less_Suc_eq)
done

lemma unless_induct: \<comment>\<open> Rule \texttt{WAIT} from @{cite [cite_macro=citet] \<open>Fig~3.3\<close> "MannaPnueli:1995"}\<close>
  assumes I: "(I \<^bold>\<hookrightarrow> \<circle>(I \<^bold>\<or> R)) \<sigma>"
  assumes P: "(P \<^bold>\<hookrightarrow> I \<^bold>\<or> R) \<sigma>"
  assumes Q: "(I \<^bold>\<hookrightarrow> Q) \<sigma>"
  shows "(P \<^bold>\<hookrightarrow> Q \<W> R) \<sigma>"
apply (intro alwaysI impI)
apply (erule impE[OF alwaysD[OF P]])
apply (erule disjE)
 apply (rule always_imp_mono(4)[where P=I and Q=R])
   apply (erule mp[OF alwaysD[OF stable_unless[OF I]]])
  apply (simp add: Q alwaysD)
 apply blast
apply (simp add: unfold)
done


subsection\<open> Leads-to and leads-to-via \label{sec:leads-to} \<close>

text\<open>

Most of our assertions will be of the form @{term "A \<^bold>\<longrightarrow> \<diamond>C"} (pronounced ``\<open>A\<close> leads to \<open>C\<close>'')
or @{term "A \<^bold>\<longrightarrow> B \<U> C"} (``\<open>A\<close> leads to \<open>C\<close> via \<open>B\<close>'').

Most of these rules are due to @{cite [cite_macro=citet]
"Jackson:1998"} who used leads-to-via in a sequential setting. Others
are due to @{cite [cite_macro=citet] "MannaPnueli:1991"}.

The leads-to-via connective is similar to the ``ensures'' modality of @{cite [cite_macro=citet] \<open>\S3.4.4\<close> "ChandyMisra:1989"}.

\<close>

abbreviation (input)
  leads_to :: "'a seq_pred \<Rightarrow> 'a seq_pred \<Rightarrow> 'a seq_pred" (infixr "\<^bold>\<leadsto>" 25) where (* FIXME priority *)
  "P \<^bold>\<leadsto> Q \<equiv> P \<^bold>\<hookrightarrow> \<diamond>Q"

lemma leads_to_refl:
  shows "(P \<^bold>\<leadsto> P) \<sigma>"
by (metis (no_types, lifting) necessitation(1) unfold(2))

lemma leads_to_trans:
  assumes "(P \<^bold>\<leadsto> Q) \<sigma>"
  assumes "(Q \<^bold>\<leadsto> R) \<sigma>"
  shows "(P \<^bold>\<leadsto> R) \<sigma>"
using assms unfolding defs by clarsimp (metis semiring_normalization_rules(25))

lemma leads_to_eventuallyE:
  assumes "(P \<^bold>\<leadsto> Q) \<sigma>"
  assumes "(\<diamond>P) \<sigma>"
  shows "(\<diamond>Q) \<sigma>"
using assms unfolding defs by auto

lemma leads_to_mono:
  assumes "(P' \<^bold>\<hookrightarrow> P) \<sigma>"
  assumes "(Q \<^bold>\<hookrightarrow> Q') \<sigma>"
  assumes "(P \<^bold>\<leadsto> Q) \<sigma>"
  shows "(P' \<^bold>\<leadsto> Q') \<sigma>"
using assms unfolding defs by clarsimp blast

lemma leads_to_eventually:
  shows "(P \<^bold>\<leadsto> Q \<^bold>\<longrightarrow> \<diamond>P \<^bold>\<longrightarrow> \<diamond>Q) \<sigma>"
by (metis (no_types, lifting) alwaysI unfold(2))

lemma leads_to_disj:
  assumes "(P \<^bold>\<leadsto> R) \<sigma>"
  assumes "(Q \<^bold>\<leadsto> R) \<sigma>"
  shows "((P \<^bold>\<or> Q) \<^bold>\<leadsto> R) \<sigma>"
using assms unfolding defs by simp

lemma leads_to_leads_to_viaE:
  shows "((P \<^bold>\<hookrightarrow> P \<U> Q) \<^bold>\<longrightarrow> P \<^bold>\<leadsto> Q) \<sigma>"
unfolding defs by clarsimp blast

lemma leads_to_via_concl_weaken:
  assumes "(R \<^bold>\<hookrightarrow> R') \<sigma>"
  assumes "(P \<^bold>\<hookrightarrow> Q \<U> R) \<sigma>"
  shows "(P \<^bold>\<hookrightarrow> Q \<U> R') \<sigma>"
using assms unfolding LTL.defs by force

lemma leads_to_via_trans:
  assumes "(A \<^bold>\<hookrightarrow> B \<U> C) \<sigma>"
  assumes "(C \<^bold>\<hookrightarrow> D \<U> E) \<sigma>"
  shows "(A \<^bold>\<hookrightarrow> (B \<^bold>\<or> D) \<U> E) \<sigma>"
proof(rule alwaysI, rule impI)
  fix i assume "A (\<sigma> |\<^sub>s i)" with assms show "((B \<^bold>\<or> D) \<U> E) (\<sigma> |\<^sub>s i)"
    apply -
    apply (erule alwaysE[where i=i])
    apply clarsimp
    apply (erule untilE)
    apply clarsimp (* suffix *)
    apply (drule (1) always_imp_mp_suffix)
    apply (erule untilE)
    apply clarsimp (* suffix *)
    apply (rule_tac i="ia + iaa" in untilI; simp add: ac_simps)
    apply (metis (full_types) add.assoc leI le_Suc_ex nat_add_left_cancel_less) (* arithmetic *)
    done
qed

lemma leads_to_via_disj: \<comment> \<open> useful for case distinctions \<close>
  assumes "(P \<^bold>\<hookrightarrow> Q \<U> R) \<sigma>"
  assumes "(P' \<^bold>\<hookrightarrow> Q' \<U> R) \<sigma>"
  shows "(P \<^bold>\<or> P' \<^bold>\<hookrightarrow> (Q \<^bold>\<or> Q') \<U> R) \<sigma>"
using assms unfolding defs by (auto 10 0)

lemma leads_to_via_disj': \<comment> \<open> more like a chaining rule \<close>
  assumes "(A \<^bold>\<hookrightarrow> B \<U> C) \<sigma>"
  assumes "(C \<^bold>\<hookrightarrow> D \<U> E) \<sigma>"
  shows "(A \<^bold>\<or> C \<^bold>\<hookrightarrow> (B \<^bold>\<or> D) \<U> E) \<sigma>"
proof(rule alwaysI, rule impI, erule disjE)
  fix i assume "A (\<sigma> |\<^sub>s i)" with assms show "((B \<^bold>\<or> D) \<U> E) (\<sigma> |\<^sub>s i)"
    apply -
    apply (erule alwaysE[where i=i])
    apply clarsimp
    apply (erule untilE)
    apply clarsimp (* suffix *)
    apply (drule (1) always_imp_mp_suffix)
    apply (erule untilE)
    apply clarsimp (* suffix *)
    apply (rule_tac i="ia + iaa" in untilI; simp add: ac_simps)
    apply (metis (full_types) add.assoc leI le_Suc_ex nat_add_left_cancel_less) (* arithmetic *)
    done
next
  fix i assume "C (\<sigma> |\<^sub>s i)" with assms(2) show "((B \<^bold>\<or> D) \<U> E) (\<sigma> |\<^sub>s i)"
    apply -
    apply (erule alwaysE[where i=i])
    apply (simp add: mono)
    done
qed

lemma leads_to_via_stable_augmentation:
  assumes stable: "(P \<^bold>\<and> Q \<^bold>\<hookrightarrow> \<circle>Q) \<sigma>"
  assumes U: "(A \<^bold>\<hookrightarrow> P \<U> C) \<sigma>"
  shows "((A \<^bold>\<and> Q) \<^bold>\<hookrightarrow> P \<U> (C \<^bold>\<and> Q)) \<sigma>"
proof(intro alwaysI impI, elim conjE)
  fix i assume AP: "A (\<sigma> |\<^sub>s i)" "Q (\<sigma> |\<^sub>s i)"
  have "Q (\<sigma> |\<^sub>s (j + i))" if "Q (\<sigma> |\<^sub>s i)" and "\<forall>k<j. P (\<sigma> |\<^sub>s (k + i))" for j
    using that stable by (induct j; force simp: defs)
  with U AP show "(P \<U> (\<lambda>\<sigma>. C \<sigma> \<and> Q \<sigma>)) (\<sigma> |\<^sub>s i)"
    unfolding defs by clarsimp (metis (full_types) add.commute)
qed

lemma leads_to_via_wf:
  assumes "wf R"
  assumes indhyp: "\<And>t. (A \<^bold>\<and> \<lceil>\<delta> \<^bold>= \<langle>t\<rangle>\<rceil> \<^bold>\<hookrightarrow> B \<U> (A \<^bold>\<and> \<lceil>\<delta> \<^bold>\<otimes> \<langle>t\<rangle> \<^bold>\<in> \<langle>R\<rangle>\<rceil> \<^bold>\<or> C)) \<sigma>"
  shows "(A \<^bold>\<hookrightarrow> B \<U> C) \<sigma>"
proof(intro alwaysI impI)
  fix i assume "A (\<sigma> |\<^sub>s i)" with \<open>wf R\<close> show "(B \<U> C) (\<sigma> |\<^sub>s i)"
  proof(induct "\<delta> (\<sigma> i)" arbitrary: i)
    case (less i) with indhyp[where t="\<delta> (\<sigma> i)"] show ?case
      apply -
      apply (drule alwaysD[where i=i])
      apply clarsimp
      apply (erule untilE)
      apply (rename_tac j)
       apply (erule disjE; clarsimp)
       apply (drule_tac x="i + j" in meta_spec; clarsimp)
       apply (erule untilE; clarsimp)
       apply (rename_tac j k)
       apply (rule_tac i="j + k" in untilI)
        apply (simp add: add.assoc)
       apply clarsimp
       apply (metis add.assoc add.commute add_diff_inverse_nat less_diff_conv2 not_le)
      apply auto
      done
  qed
qed

text\<open>

The well-founded response rule due to @{cite [cite_macro=citet] \<open>Fig~1.23: \texttt{WELL} (well-founded response)\<close>"MannaPnueli:2010"},
generalised to an arbitrary set of assertions and sequence predicates.
\<^item> \<open>W1\<close> generalised to be contingent.
\<^item> \<open>W2\<close> is a well-founded set of assertions that by \<open>W1\<close> includes \<open>P\<close>

\<close>

(* FIXME: Does \<open>Is\<close> need to be consistent? *)
lemma leads_to_wf:
  fixes Is :: "('a seq_pred \<times> ('a \<Rightarrow> 'b)) set"
  assumes "wf (R :: 'b rel)"
  assumes W1: "(\<box>(\<^bold>\<exists>\<phi>. \<lceil>\<langle>\<phi>\<in>fst ` Is\<rangle>\<rceil> \<^bold>\<and> (P \<^bold>\<longrightarrow> \<phi>))) \<sigma>"
  assumes W2: "\<forall>(\<phi>, \<delta>)\<in>Is. \<exists>(\<phi>', \<delta>')\<in>insert (Q, \<delta>0) Is. \<forall>t. (\<phi> \<^bold>\<and> \<lceil>\<delta> \<^bold>= \<langle>t\<rangle>\<rceil> \<^bold>\<leadsto> \<phi>' \<^bold>\<and> \<lceil>\<delta>' \<^bold>\<otimes> \<langle>t\<rangle> \<^bold>\<in> \<langle>R\<rangle>\<rceil>) \<sigma>"
  shows "(P \<^bold>\<leadsto> Q) \<sigma>"
proof -
  have "(\<phi> \<^bold>\<and> \<lceil>\<delta> \<^bold>= \<langle>t\<rangle>\<rceil> \<^bold>\<leadsto> Q) \<sigma>" if "(\<phi>, \<delta>) \<in> Is" for \<phi> \<delta> t
    using \<open>wf R\<close> that W2
    apply (induct t arbitrary: \<phi> \<delta>)
    unfolding LTL.defs split_def
    apply clarsimp
    apply (metis (no_types, hide_lams) ab_semigroup_add_class.add_ac(1) fst_eqD snd_conv surjective_pairing)
    done
  with W1 show ?thesis
    apply -
    apply (rule alwaysI)
    apply clarsimp
    apply (erule_tac i=i in alwaysE)
    apply clarsimp
    using alwaysD suffix_state_prop apply blast
    done
qed


subsection\<open>Fairness\<close>

text\<open>

A few renderings of weak fairness. @{cite [cite_macro=citet] "vanGlabbeekHofner:2019"} call this
"response to insistence" as a generalisation of weak fairness.

\<close>

definition weakly_fair :: "'a seq_pred \<Rightarrow> 'a seq_pred \<Rightarrow> 'a seq_pred" where
  "weakly_fair enabled taken = (\<box>enabled \<^bold>\<hookrightarrow> \<diamond>taken)"

lemma weakly_fair_def2:
  shows "weakly_fair enabled taken = \<box>(\<^bold>\<not>\<box>(enabled \<^bold>\<and> \<^bold>\<not>taken))"
unfolding weakly_fair_def by (metis (full_types) always_conj_distrib norm(18))

lemma weakly_fair_def3:
  shows "weakly_fair enabled taken = (\<diamond>\<box>enabled \<^bold>\<longrightarrow> \<box>\<diamond>taken)"
unfolding weakly_fair_def2
apply (clarsimp simp: fun_eq_iff)

unfolding defs (* True, but can we get there deductively? *)
apply auto
apply (metis (full_types) add.left_commute semiring_normalization_rules(25))
done

lemma weakly_fair_def4:
  shows "weakly_fair enabled taken = \<box>\<diamond>(enabled \<^bold>\<longrightarrow> taken)"
using weakly_fair_def2 by force

lemma mp_weakly_fair:
  assumes "weakly_fair enabled taken \<sigma>"
  assumes "(\<box>enabled) \<sigma>"
  shows "(\<diamond>taken) \<sigma>"
using assms unfolding weakly_fair_def using always_imp_mp by blast

lemma always_weakly_fair:
  shows "\<box>(weakly_fair enabled taken) = weakly_fair enabled taken"
unfolding weakly_fair_def by simp

lemma eventually_weakly_fair:
  shows "\<diamond>(weakly_fair enabled taken) = weakly_fair enabled taken"
unfolding weakly_fair_def2 by (simp add: always_eventually_always)

lemma weakly_fair_weaken:
  assumes "(enabled' \<^bold>\<hookrightarrow> enabled) \<sigma>"
  assumes "(taken \<^bold>\<hookrightarrow> taken') \<sigma>"
  shows "(weakly_fair enabled taken \<^bold>\<hookrightarrow>  weakly_fair enabled' taken') \<sigma>"
using assms unfolding weakly_fair_def defs by simp blast

lemma weakly_fair_unless_until:
  shows "(weakly_fair enabled taken \<^bold>\<and> (enabled \<^bold>\<hookrightarrow> enabled \<W> taken)) = (enabled \<^bold>\<hookrightarrow> enabled \<U> taken)"
unfolding defs weakly_fair_def
apply (auto simp: fun_eq_iff)
apply (metis add.right_neutral)
done

lemma stable_leads_to_eventually:
  assumes "(enabled \<^bold>\<hookrightarrow> \<circle>(enabled \<^bold>\<or> taken)) \<sigma>"
  shows "(enabled \<^bold>\<hookrightarrow> (\<box>enabled \<^bold>\<or> \<diamond>taken)) \<sigma>"
using assms unfolding defs
apply -
apply (rule ccontr)
apply clarsimp
apply (drule (1) ex_least_nat_less[where P="\<lambda>j. \<not> enabled (\<sigma> |\<^sub>s i + j)" for i, simplified])
apply clarsimp
apply (metis add_Suc_right leI less_irrefl_nat)
done

lemma weakly_fair_stable_leads_to:
  assumes "(weakly_fair enabled taken) \<sigma>"
  assumes "(enabled \<^bold>\<hookrightarrow> \<circle>(enabled \<^bold>\<or> taken)) \<sigma>"
  shows "(enabled \<^bold>\<leadsto> taken) \<sigma>"
using stable_leads_to_eventually[OF assms(2)] assms(1) unfolding defs weakly_fair_def
by (auto simp: fun_eq_iff)

lemma weakly_fair_stable_leads_to_via:
  assumes "(weakly_fair enabled taken) \<sigma>"
  assumes "(enabled \<^bold>\<hookrightarrow> \<circle>(enabled \<^bold>\<or> taken)) \<sigma>"
  shows "(enabled \<^bold>\<hookrightarrow> enabled \<U> taken) \<sigma>"
using stable_unless[OF assms(2)] assms(1) by (metis (mono_tags) weakly_fair_unless_until)

text\<open>

Similarly for strong fairness. @{cite [cite_macro=citet] "vanGlabbeekHofner:2019"} call this
"response to persistence" as a generalisation of strong fairness.

\<close>

definition strongly_fair :: "'a seq_pred \<Rightarrow> 'a seq_pred \<Rightarrow> 'a seq_pred" where
  "strongly_fair enabled taken = (\<box>\<diamond>enabled \<^bold>\<hookrightarrow> \<diamond>taken)"

lemma strongly_fair_def2:
  "strongly_fair enabled taken = \<box>(\<^bold>\<not>\<box>(\<diamond>enabled \<^bold>\<and> \<^bold>\<not>taken))"
unfolding strongly_fair_def by (metis weakly_fair_def weakly_fair_def2)

lemma strongly_fair_def3:
  "strongly_fair enabled taken = (\<box>\<diamond>enabled \<^bold>\<longrightarrow> \<box>\<diamond>taken)"
unfolding strongly_fair_def2 by (metis (full_types) always_eventually_always weakly_fair_def2 weakly_fair_def3)

lemma always_strongly_fair:
  "\<box>(strongly_fair enabled taken) = strongly_fair enabled taken"
unfolding strongly_fair_def by simp

lemma eventually_strongly_fair:
  "\<diamond>(strongly_fair enabled taken) = strongly_fair enabled taken"
unfolding strongly_fair_def2 by (simp add: always_eventually_always)

lemma strongly_fair_disj_distrib: \<comment> \<open>not true for \<open>weakly_fair\<close>\<close>
  "strongly_fair (enabled1 \<^bold>\<or> enabled2) taken = (strongly_fair enabled1 taken \<^bold>\<and> strongly_fair enabled2 taken)"
unfolding strongly_fair_def defs
apply (auto simp: fun_eq_iff)
  apply blast
  apply blast
  apply (metis (full_types) semiring_normalization_rules(25))
done

lemma strongly_fair_imp_weakly_fair:
  assumes "strongly_fair enabled taken \<sigma>"
  shows "weakly_fair enabled taken \<sigma>"
using assms unfolding strongly_fair_def3 weakly_fair_def3 by (simp add: eventually_always_imp_always_eventually)

lemma always_enabled_weakly_fair_strongly_fair:
  assumes "(\<box>enabled) \<sigma>"
  shows "weakly_fair enabled taken \<sigma> = strongly_fair enabled taken \<sigma>"
using assms by (metis strongly_fair_def3 strongly_fair_imp_weakly_fair unfold(2) weakly_fair_def3)


subsection\<open>Safety and liveness \label{sec:ltl-safety-liveness}\<close>

text\<open>

@{cite [cite_macro=citet] "Sistla:1994"} shows some characterisations
of LTL formulas in terms of safety and liveness. Note his @{term
"(\<U>)"} is actually @{term "(\<W>)"}.

See also @{cite [cite_macro=citet] "ChangMannaPnueli:1992"}.

\<close>

lemma safety_state_prop:
  shows "safety \<lceil>P\<rceil>"
unfolding defs by (rule safety_state_prop)

lemma safety_Next:
  assumes "safety P"
  shows "safety (\<circle>P)"
using assms unfolding defs safety_def
apply clarsimp
apply (metis (mono_tags) One_nat_def list.sel(3) nat.simps(3) stake.simps(2))
done

lemma safety_unless:
  assumes "safety P"
  assumes "safety Q"
  shows "safety (P \<W> Q)"
proof(rule safetyI2)
  fix \<sigma> assume X: "\<exists>\<beta>. (P \<W> Q) (stake i \<sigma> @- \<beta>)" for i
  then show "(P \<W> Q) \<sigma>"
  proof(cases "\<forall>i j. \<exists>\<beta>. P (\<sigma>(i \<rightarrow> j) @- \<beta>)")
    case True
    with \<open>safety P\<close> have "\<forall>i. P (\<sigma> |\<^sub>s i)" unfolding safety_def2 by blast
    then show ?thesis by (blast intro: unless_alwaysI)
  next
    case False
    then obtain k k' where "\<forall>\<beta>. \<not> P (\<sigma>(k \<rightarrow> k') @- \<beta>)" by clarsimp
    then have "\<forall>i u. k + k' \<le> i \<longrightarrow> \<not>P ((stake i \<sigma> @- u) |\<^sub>s k)"
      by (metis add.commute diff_add stake_shift_stake_shift stake_suffix_drop suffix_shift)
    then have "\<forall>i u. k + k' \<le> i \<and> (P \<W> Q) (stake i \<sigma> @- u) \<longrightarrow> (\<exists>m\<le>k. Q ((stake i \<sigma> @- u) |\<^sub>s m) \<and> (\<forall>p<m. P ((stake i \<sigma> @- u) |\<^sub>s p)))"
      unfolding defs using leI by blast
    then have "\<forall>i u. k + k' \<le> i \<and> (P \<W> Q) (stake i \<sigma> @- u) \<longrightarrow> (\<exists>m\<le>k. Q (\<sigma>(m \<rightarrow> i - m) @- u) \<and> (\<forall>p<m. P (\<sigma>(p \<rightarrow> i - p) @- u)))"
      by (metis stake_suffix add_leE nat_less_le order_trans)
    then have "\<forall>i. \<exists>n\<ge>i. \<exists>m\<le>k. \<exists>u. Q (\<sigma>(m \<rightarrow> n - m) @- u) \<and> (\<forall>p<m. P (\<sigma>(p \<rightarrow> n - p) @- u))"
      using X by (metis add.commute le_add1)
    then have "\<exists>m\<le>k. \<forall>i. \<exists>n\<ge>i. \<exists>u. Q (\<sigma>(m \<rightarrow> n - m) @- u) \<and> (\<forall>p<m. P (\<sigma>(p \<rightarrow> n - p) @- u))"
      by (simp add: always_eventually_pigeonhole)
    with \<open>safety P\<close> \<open>safety Q\<close> show "(P \<W> Q) \<sigma>"
        unfolding defs by (metis Nat.le_diff_conv2 add_leE safety_always_eventually)
  qed
qed

lemma safety_always:
  assumes "safety P"
  shows "safety (\<box>P)"
using assms by (metis norm(20) safety_def safety_unless)

lemma absolute_liveness_eventually:
  shows "absolute_liveness P \<longleftrightarrow> (\<exists>\<sigma>. P \<sigma>) \<and> P = \<diamond>P"
unfolding absolute_liveness_def defs
by (metis cancel_comm_monoid_add_class.diff_cancel drop_eq_Nil order_refl shift.simps(1) stake_suffix_id suffix_shift suffix_zero)

lemma stable_always:
  shows "stable P \<longleftrightarrow> (\<exists>\<sigma>. P \<sigma>) \<and> P = \<box>P"
unfolding stable_def defs by (metis suffix_zero)

(* FIXME Sistla's examples of stable properties are boring and follow directly from this lemma.
   FIXME the fairness "type of formulas" follow from the above and the fairness def. *)

text\<open>

To show that @{const \<open>weakly_fair\<close>} is a @{const \<open>fairness\<close>} property requires some constraints on \<open>enabled\<close> and \<open>taken\<close>:
\<^item> it is reasonable to assume they are state formulas
\<^item> \<open>taken\<close> must be satisfiable

\<close>

lemma fairness_weakly_fair:
  assumes "\<exists>s. taken s"
  shows "fairness (weakly_fair \<lceil>enabled\<rceil> \<lceil>taken\<rceil>)"
unfolding fairness_def stable_def absolute_liveness_def weakly_fair_def
using assms
apply auto
   apply (rule_tac x="\<lambda>_ .s" in exI)
   apply fastforce
  apply (simp add: alwaysD)
 apply (rule_tac x="\<lambda>_ .s" in exI)
 apply fastforce
apply (metis (full_types) absolute_liveness_def absolute_liveness_eventually eventually_weakly_fair weakly_fair_def)
done

lemma fairness_strongly_fair:
  assumes "\<exists>s. taken s"
  shows "fairness (strongly_fair \<lceil>enabled\<rceil> \<lceil>taken\<rceil>)"
unfolding fairness_def stable_def absolute_liveness_def strongly_fair_def
using assms
apply auto
   apply (rule_tac x="\<lambda>_ .s" in exI)
   apply fastforce
  apply (simp add: alwaysD)
 apply (rule_tac x="\<lambda>_ .s" in exI)
 apply fastforce
apply (metis (full_types) absolute_liveness_def absolute_liveness_eventually eventually_weakly_fair weakly_fair_def)
done

(*<*)

end
(*>*)
