(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus_tutorial_ex.thy                                           *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)

section {* {\Circus} Tutorial *}

theory utp_circus_tutorial_ex
imports "../theories/utp_circus" Transitive_Closure
begin recall_syntax

subsection {* Preliminaries *}

purge_notation nth (infixl "!" 100)

no_translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a\<guillemotright> P"

translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a()\<guillemotright> P"

text \<open>Hints for the tutorial exercise.\<close>

consts COMPLETE :: "'a" ("\<^bold>C\<^bold>O\<^bold>M\<^bold>P\<^bold>L\<^bold>E\<^bold>T\<^bold>E")

paragraph \<open>Additional proof support\<close>

declare list_concat_minus_list_concat [simp]

lemma list_Cons_minus [simp]:
"(x # y) - (x # z) = y - z"
  by (simp add: minus_list_def)

subsection {* Time Types *}

text \<open>Below we define type synonyms for \<open>TIME\<close> and \<open>PERIOD\<close> type.\<close>

type_synonym TIME = "nat"
type_synonym PERIOD = "nat"

subsection {* Channel Declarations *}

datatype timer_evt =
  setT "TIME" |
  updateSS "PERIOD" |
  step "TIME \<times> PERIOD" |
  endc "unit"

abbreviation timer_prefix ::
  "('a, timer_evt) chan \<Rightarrow>
   ('a, timer_evt + 'ext) chan" where
"timer_prefix c \<equiv> Inl o c"

notation timer_prefix ("tm:_" [1000] 1000)

abbreviation "tm_events \<equiv>
  \<epsilon>(tm:step) \<union> \<epsilon>(tm:endc) \<union> \<epsilon>(tm:setT) \<union> \<epsilon>(tm:updateSS)"

subsection {* Process Definition *}

alphabet timer_state =
  currentTime :: "TIME"
  stepSize :: "PERIOD"

type_synonym timer_action =
  "(timer_state, timer_evt) action"

definition [rdes]:
"process Timer(ct::TIME, hc::PERIOD, tN::TIME) \<triangleq> begin
  state(timer_state)
  Step = (
    (tm:setT?(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<^bold>\<rightarrow> currentTime :=\<^sub>C \<guillemotleft>t\<guillemotright>) \<box>
    (tm:updateSS?(ss) \<^bold>\<rightarrow> stepSize :=\<^sub>C \<guillemotleft>ss\<guillemotright>) \<box>
    \<^bold>C\<^bold>O\<^bold>M\<^bold>P\<^bold>L\<^bold>E\<^bold>T\<^bold>E) ;; Step
  \<bullet> \<^bold>C\<^bold>O\<^bold>M\<^bold>P\<^bold>L\<^bold>E\<^bold>T\<^bold>E
end"

text \<open>The same process definition using deep variables.\<close>

definition [rdes]:
"process DvarTimer(ct::TIME, hc::PERIOD, tN::TIME) \<triangleq> begin
  state(vstore)
  Step = (
    (tm:setT?(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<^bold>\<rightarrow> <currentTime> :=\<^sub>C \<guillemotleft>t\<guillemotright>) \<box>
    (tm:updateSS?(ss) \<^bold>\<rightarrow> <stepSize> :=\<^sub>C \<guillemotleft>ss\<guillemotright>) \<box>
    (tm:step!(&<currentTime>)!(&<stepSize>) \<^bold>\<rightarrow>
      <currentTime> :=\<^sub>C min\<^sub>u(&<currentTime> + &<stepSize>, \<guillemotleft>tN\<guillemotright>)) \<box>
    (&<currentTime> =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u tm:endc \<^bold>\<rightarrow> Stop) ;; Step
  \<bullet> (<currentTime>, <stepSize>) :=\<^sub>C (\<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

text \<open>Proof that the @{const Timer} process does not diverge.\<close>

lemma "pre\<^sub>R(Timer(ct, hc, tN)) = true"
-- \<open>TODO: try to complete this prove using the @{method rdes_calc} tactic.\<close>
oops

text \<open>Proof about the initial refusal set of the @{const Timer} process.\<close>

text \<open>
  Simplified encoding of the @{const Timer} process action. The simplification
  does not consider hiding of the state in the process semantics and neither
  uses the extensible event type. The @{const setT} communication is slightly
  more restrictive, requiring \<open>t < tN\<close> rather than \<open>t \<le> tN\<close>.\<close>

definition StepBody :: "TIME \<Rightarrow> timer_action" where
"StepBody tN =
  (setT?(t : \<guillemotleft>t\<guillemotright> <\<^sub>u \<guillemotleft>tN\<guillemotright>) \<^bold>\<rightarrow> currentTime :=\<^sub>C \<guillemotleft>t\<guillemotright>) \<box>
  (updateSS?(ss) \<^bold>\<rightarrow> stepSize :=\<^sub>C \<guillemotleft>ss\<guillemotright>) \<box>
  (step!(&currentTime)!(&stepSize) \<^bold>\<rightarrow>
    currentTime :=\<^sub>C min\<^sub>u(&currentTime + &stepSize, \<guillemotleft>tN\<guillemotright>)) \<box>
  (&currentTime =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u endc \<^bold>\<rightarrow> Stop"

fun MainAction :: "(TIME \<times> PERIOD \<times> TIME) \<Rightarrow> timer_action" where
"MainAction (ct, hc, tN) =
  (currentTime, stepSize) :=\<^sub>C (\<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; (\<mu>\<^sub>C Step \<bullet> StepBody(tN) ;; Step)"

text \<open>Additional lemma needed for the proof below.\<close>

lemma wpR_assign [wp]:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S) wp\<^sub>R pre\<^sub>R P = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> pre\<^sub>R(P)"
apply (simp add: wpR_def unrest rdes assms closure R1_neg_preR usubst)
done

text \<open>Communication on @{const setT} is initially not refused.\<close>

lemma StepBody_muI:
"[true \<turnstile> \<^bold>\<forall> t \<bullet> \<guillemotleft>t\<guillemotright> <\<^sub>u \<guillemotleft>tN\<guillemotright> \<and> \<guillemotleft>trace\<guillemotright> =\<^sub>u \<langle>\<rangle> \<Rightarrow> (setT\<cdot>\<guillemotleft>t\<guillemotright>)\<^sub>u \<notin>\<^sub>u \<guillemotleft>refs\<guillemotright> | false]\<^sub>C
  \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> StepBody tN ;; X)"
apply (unfold StepBody_def)
apply (rule CRD_mu_basic_refine)
-- \<open>TODO: Can you finalise the rest of the proof?\<close>
-- {* Subgoal 1 *}
-- {* Subgoal 2 *}
-- {* Subgoal 3 *}
-- {* Subgoal 4 *}
-- {* Subgoal 5 *}
oops

text \<open>@{const setT} is only enabled when \<open>t < tN\<close>.\<close>

lemma StepBody_muI2:
"[true \<turnstile> \<^bold>\<forall> t \<bullet> \<guillemotleft>trace\<guillemotright> =\<^sub>u \<langle>(setT\<cdot>\<guillemotleft>t\<guillemotright>)\<^sub>u\<rangle> \<Rightarrow> \<guillemotleft>t\<guillemotright> <\<^sub>u \<guillemotleft>tN\<guillemotright> | false]\<^sub>C
  \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> StepBody tN ;; X)"
apply (unfold StepBody_def)
apply (rule CRD_mu_basic_refine)
apply (simp_all add: rdes wp closure unrest usubst alpha)
apply (rel_auto)
apply (simp_all add: zero_list_def) [2]
apply (rel_auto)
apply (metis Prefix_Order.prefix_snoc Prefix_Order.same_prefix_nil append1_eq_conv timer_evt.inject(1) list.discI minus_list_def prefix_concat_minus)
apply (metis Prefix_Order.prefix_snoc Prefix_Order.same_prefix_nil append1_eq_conv timer_evt.distinct(1) list.discI minus_list_def prefix_concat_minus)
apply (metis Prefix_Order.prefix_snoc Prefix_Order.same_prefix_nil append1_eq_conv timer_evt.distinct(3) list.discI minus_list_def prefix_concat_minus)
done

lemma StepBody_muI3:
"[true \<turnstile> \<^bold>\<forall> (ct, ss) \<bullet> \<guillemotleft>ct\<guillemotright> <\<^sub>u \<guillemotleft>tN\<guillemotright> \<and>
    \<guillemotleft>trace\<guillemotright> =\<^sub>u \<langle>(setT\<cdot>\<guillemotleft>ct\<guillemotright>)\<^sub>u, (updateSS\<cdot>\<guillemotleft>ss\<guillemotright>)\<^sub>u\<rangle> \<Rightarrow> (step\<cdot>\<guillemotleft>(ct, ss)\<guillemotright>)\<^sub>u \<notin>\<^sub>u \<guillemotleft>refs\<guillemotright>
 | false]\<^sub>C
 \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> StepBody tN ;; X)"
apply (unfold StepBody_def)
apply (rule CRD_mu_basic_refine)
-- {* Subgoal 1 *}
apply (simp add: closure unrest alpha)
-- {* Subgoal 2 *}
apply (simp add: closure unrest alpha)
-- {* Subgoal 3 *}
apply (simp add: rdes wp closure unrest usubst alpha)
-- {* Subgoal 4 *}
apply (simp add: rdes wp closure unrest usubst alpha)
apply (rel_auto)
apply (simp_all add: zero_list_def) [2]
-- {* Subgoal 5 *}
apply (simp add: rdes wp closure unrest usubst alpha)
apply (rel_auto)
-- {* Subgoal 5.1 *}
apply (erule prefixE)
apply (clarsimp)
defer
-- {* Subgoal 5.1 *}
apply (erule prefixE)
apply (clarsimp)
-- {* Subgoal 5.1 *}
apply (erule prefixE)
apply (clarsimp)
oops

text \<open>Simpler version of the Timer with fewer communications and no recursion.\<close>

definition [rdes]:
"process SimpleTimer(ct::TIME, hc::PERIOD, tN::TIME) \<triangleq> begin
  state(timer_state)
  Step = (
    (step!(&currentTime)!(&stepSize) \<^bold>\<rightarrow>
      currentTime :=\<^sub>C min\<^sub>u(&currentTime + &stepSize, \<guillemotleft>tN\<guillemotright>)) \<box>
    (&currentTime =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u endc \<^bold>\<rightarrow> Stop)
  \<bullet> (currentTime, stepSize) :=\<^sub>C (\<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

lemma
"SimpleTimer(ct, hc, tN) \<sqsubseteq> step!(\<guillemotleft>ct\<guillemotright>)!(\<guillemotleft>hc\<guillemotright>) \<^bold>\<rightarrow> Skip"
apply (unfold SimpleTimer_def)
apply (unfold circus_syntax)
apply (simp add: Let_def)
(* apply (rdes_refine) *)
apply (rule SRD_refine_intro)
-- {* Subgoal 1 *}
apply (simp add: closure)
-- {* Subgoal 2 *}
apply (simp add: closure)
-- {* Subgoal 3 *}
apply (rdes_calc)
-- {* Subgoal 4 *}
apply (rdes_calc)
apply (rel_simp)
apply (erule_tac Q = "endc () \<in> ref\<^sub>v" in contrapos_pp)
apply (simp)
defer
-- {* Subgoal 4 *}
apply (rdes_calc)
apply (rel_simp)
oops

lemma
"ct < tN \<Longrightarrow> SimpleTimer(ct, hc, tN) \<sqsubseteq> step!(\<guillemotleft>ct\<guillemotright>)!(\<guillemotleft>hc\<guillemotright>) \<^bold>\<rightarrow> Skip"
apply (unfold SimpleTimer_def)
apply (unfold circus_syntax)
apply (simp add: Let_def)
apply (rdes_refine)
done

text \<open>Simpler version of the Timer communicating only on channel @{const step}.\<close>

definition [rdes]: -- \<open>@{const Timer} with only @{const step} recursion\<close>
"process SimpleTimer2(ct::TIME, hc::PERIOD, tN::TIME) \<triangleq> begin
  state(timer_state)
  Step = (step!(&currentTime)!(&stepSize) \<^bold>\<rightarrow>
    currentTime :=\<^sub>C min\<^sub>u(&currentTime + &stepSize, \<guillemotleft>tN\<guillemotright>)) ;; Step
  \<bullet> (currentTime, stepSize) :=\<^sub>C (\<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

text \<open>Let us try proving something about @{const step} events.\<close>

lemma "`peri\<^sub>R(SimpleTimer2(ct, hc, tN)) \<and> $tr =\<^sub>u $tr\<acute> \<Rightarrow> \<guillemotleft>step(ct, hc)\<guillemotright> \<notin>\<^sub>u $ref\<acute>`"
apply (rdes_calc)
apply (rel_simp)
apply (erule_tac Q = "step (ct, hc) \<in> ref\<^sub>v" in contrapos_pp; simp)
apply (subgoal_tac "currentTime\<^sub>v' = ct \<and> stepSize\<^sub>v' = hc")
-- {* Subgoal 1 *}
apply (clarsimp)
-- {* Subgoal 2 *}
apply (thin_tac "\<not> step (currentTime\<^sub>v', stepSize\<^sub>v') \<in> ref\<^sub>v")
apply (rename_tac n)
apply (case_tac "n = 0")
-- {* Subgoal 2.1 *}
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (clarify)
apply (erule contrapos_pp; simp)
-- \<open>@{command sledgehammer}\<close>
-- \<open>We need additional lemmas here to make progress..!\<close>
oops

lemma nat_one_induct:
"0 < n \<Longrightarrow> (P 1 \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n)"
apply (induction n)
apply (simp_all)
apply (blast)
done

lemma tr_in_relpow_grows:
"0 < n \<Longrightarrow>
  (\<forall>ok1 ok2 wait1 wait2 (tr1::'\<epsilon> list) (tr2::'\<epsilon> list) (st1::'\<sigma>) (st2::'\<sigma>)
    (ref1::'\<epsilon> set) (ref2::'\<epsilon> set).
    (\<lparr>ok\<^sub>v = ok1, wait\<^sub>v = wait1, tr\<^sub>v = tr1, st\<^sub>v = st1, ref\<^sub>v = ref1\<rparr>,
     \<lparr>ok\<^sub>v = ok2, wait\<^sub>v = wait2, tr\<^sub>v = tr2, st\<^sub>v = st2, ref\<^sub>v = ref2\<rparr>) \<in> r \<longrightarrow>
    tr1 < tr2) \<Longrightarrow>
  (\<forall>ok1 ok2 wait1 wait2 (tr1::'\<epsilon> list) (tr2::'\<epsilon> list) (st1::'\<sigma>) (st2::'\<sigma>)
    (ref1::'\<epsilon> set) (ref2::'\<epsilon> set).
    (\<lparr>ok\<^sub>v = ok1, wait\<^sub>v = wait1, tr\<^sub>v = tr1, st\<^sub>v = st1, ref\<^sub>v = ref1\<rparr>,
     \<lparr>ok\<^sub>v = ok2, wait\<^sub>v = wait2, tr\<^sub>v = tr2, st\<^sub>v = st2, ref\<^sub>v = ref2\<rparr>) \<in> (r ^^ n)
  \<longrightarrow> tr1 < tr2)"
apply (erule nat_one_induct)
apply (simp_all)
apply (clarsimp)
apply (case_tac y)
apply (case_tac more)
apply (case_tac morea)
apply (case_tac moreb)
apply (clarsimp)
using dual_order.strict_trans by (blast)

text \<open>Let us try again with those lemmas.\<close>

lemma empty_trace_neq_relpowI [rule_format]:
"0 < n \<Longrightarrow>
  (\<forall>ok1 ok2 wait1 wait2 (tr1::'\<epsilon> list) (tr2::'\<epsilon> list) (st1::'\<sigma>) (st2::'\<sigma>)
    (ref1::'\<epsilon> set) (ref2::'\<epsilon> set).
    (\<lparr>ok\<^sub>v = ok1, wait\<^sub>v = wait1, tr\<^sub>v = tr1, st\<^sub>v = st1, ref\<^sub>v = ref1\<rparr>,
     \<lparr>ok\<^sub>v = ok2, wait\<^sub>v = wait2, tr\<^sub>v = tr2, st\<^sub>v = st2, ref\<^sub>v = ref2\<rparr>) \<in> r \<longrightarrow>
    tr1 < tr2) \<Longrightarrow>
  (\<forall>ok1 ok2 wait1 wait2 tr st1 st2 ref1 ref2.
    (\<lparr>ok\<^sub>v = ok1, wait\<^sub>v = wait1, tr\<^sub>v = tr, st\<^sub>v = st1, ref\<^sub>v = ref1\<rparr>,
     \<lparr>ok\<^sub>v = ok2, wait\<^sub>v = wait2, tr\<^sub>v = tr, st\<^sub>v = st2, ref\<^sub>v = ref2\<rparr>) \<notin> (r ^^ n))"
apply (drule_tac tr_in_relpow_grows)
apply (assumption)
apply (clarsimp)
apply (subgoal_tac "tr < tr")
apply (clarsimp)
apply (blast)
done

lemma "`peri\<^sub>R(SimpleTimer2(ct, hc, tN)) \<and> $tr =\<^sub>u $tr\<acute> \<Rightarrow> \<guillemotleft>step(ct, hc)\<guillemotright> \<notin>\<^sub>u $ref\<acute>`"
apply (rdes_calc)
apply (rel_simp)
apply (erule_tac Q = "step (ct, hc) \<in> ref\<^sub>v" in contrapos_pp; simp)
apply (subgoal_tac "currentTime\<^sub>v' = ct \<and> stepSize\<^sub>v' = hc")
-- {* Subgoal 1 *}
apply (clarsimp)
-- {* Subgoal 2 *}
apply (thin_tac "\<not> step (currentTime\<^sub>v', stepSize\<^sub>v') \<in> ref\<^sub>v")
apply (rename_tac n)
apply (case_tac "n = 0")
-- {* Subgoal 2.1 *}
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (clarify)
apply (erule contrapos_pp; simp)
apply (erule empty_trace_neq_relpowI)
apply (clarsimp)
apply (simp add: Prefix_Order.strict_prefixI')
done
end