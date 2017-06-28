(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus_tutorial.thy                                              *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section {* {\Circus} Tutorial *}

theory utp_circus_tutorial
imports "../theories/utp_circus" Transitive_Closure
begin recall_syntax

subsection {* Preliminaries *}

declare [[syntax_ambiguity_warning=false]]

purge_notation nth (infixl "!" 100)

no_translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a\<guillemotright> P"

translations
  "a \<^bold>\<rightarrow> P" == "CONST PrefixCSP \<guillemotleft>a()\<guillemotright> P"

text \<open>Below we define type synonyms for \<open>TIME\<close> and \<open>PERIOD\<close> type.\<close>

type_synonym TIME = "nat"
type_synonym PERIOD = "nat"

subsection {* Channel Declarations *}

datatype timer_event =
  setT "TIME" |
  updateSS "PERIOD" |
  step "TIME \<times> PERIOD" |
  endc "unit"

abbreviation timer_prefix ::
  "('a, timer_event) chan \<Rightarrow>
   ('a, timer_event + 'ext) chan" where
"timer_prefix c \<equiv> Inl o c"

notation timer_prefix ("tm:_" [1000] 1000)

abbreviation "tm_events \<equiv>
  \<epsilon>(tm:step) \<union> \<epsilon>(tm:endc) \<union> \<epsilon>(tm:setT) \<union> \<epsilon>(tm:updateSS)"

subsection {* Process Definition *}

definition
"process Timer(ct::TIME, hc::PERIOD, tN::TIME) \<triangleq> begin
  state(vstore)
  Step = (
    (tm:setT?(t : \<guillemotleft>t \<le> tN\<guillemotright>) \<^bold>\<rightarrow> <currentTime> :=\<^sub>C \<guillemotleft>t\<guillemotright>) \<box>
    (tm:updateSS?(ss) \<^bold>\<rightarrow> <stepSize> :=\<^sub>C \<guillemotleft>ss\<guillemotright>) \<box>
    (tm:step!(&<currentTime>)!(&<stepSize>) \<^bold>\<rightarrow>
      <currentTime> :=\<^sub>C min\<^sub>u(&<currentTime> + &<stepSize>, \<guillemotleft>tN\<guillemotright>)) \<box>
    (&<currentTime> =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u tm:endc \<^bold>\<rightarrow> Stop) ;; Step
  \<bullet> (<currentTime>, <stepSize> :=\<^sub>C \<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

lemma "pre\<^sub>R(Timer(ct, hc, tN)) = true"
apply (unfold Timer_def)
apply (unfold circus_syntax)
apply (simp add: Let_def)
apply (rdes_calc)
apply (unfold hide_state_def)
apply (simp add: alpha)
done

definition
"process Timer2(ct::TIME, hc::PERIOD, tN::TIME) \<triangleq> begin
  state(vstore)
  Step = (step!(&<currentTime>)!(&<stepSize>) \<^bold>\<rightarrow>
    <currentTime> :=\<^sub>C min\<^sub>u(&<currentTime> + &<stepSize>, \<guillemotleft>tN\<guillemotright>)) ;; Step
  \<bullet> (<currentTime>, <stepSize> :=\<^sub>C \<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;; Step
end"

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
     \<lparr>ok\<^sub>v = ok2, wait\<^sub>v = wait2, tr\<^sub>v = tr2, st\<^sub>v = st2, ref\<^sub>v = ref2\<rparr>) \<in> (r ^^ n) \<longrightarrow>
    tr1 < tr2)"
apply (erule nat_one_induct)
apply (simp_all)
apply (clarsimp)
apply (case_tac y)
apply (case_tac more)
apply (case_tac morea)
apply (case_tac moreb)
apply (clarsimp)
using dual_order.strict_trans by (blast)

lemma empty_trace_neq_relpowI [rule_format]:
"0 < n \<Longrightarrow>
  (\<forall> ok1 ok2 wait1 wait2 (tr1::'\<epsilon> list) (tr2::'\<epsilon> list) (st1::'\<sigma>) (st2::'\<sigma>)
    (ref1::'\<epsilon> set) (ref2::'\<epsilon> set).
    (\<lparr>ok\<^sub>v = ok1, wait\<^sub>v = wait1, tr\<^sub>v = tr1, st\<^sub>v = st1, ref\<^sub>v = ref1\<rparr>,
     \<lparr>ok\<^sub>v = ok2, wait\<^sub>v = wait2, tr\<^sub>v = tr2, st\<^sub>v = st2, ref\<^sub>v = ref2\<rparr>) \<in> r \<longrightarrow>
    tr1 < tr2) \<Longrightarrow>
  (\<forall> ok1 ok2 wait1 wait2 tr1 st1 st2 ref1 ref2.
    (\<lparr>ok\<^sub>v = ok1, wait\<^sub>v = wait1, tr\<^sub>v = tr1, st\<^sub>v = st1, ref\<^sub>v = ref1\<rparr>,
     \<lparr>ok\<^sub>v = ok2, wait\<^sub>v = wait2, tr\<^sub>v = tr1, st\<^sub>v = st2, ref\<^sub>v = ref2\<rparr>) \<notin> (r ^^ n))"
apply (drule_tac tr_in_relpow_grows)
apply (assumption)
apply (clarsimp)
apply (subgoal_tac "tr1 < tr1")
apply (clarsimp)
apply (blast)
done

lemma "`peri\<^sub>R(Timer2(ct, hc, tN)) \<and> $tr =\<^sub>u $tr\<acute> \<Rightarrow> \<guillemotleft>step(ct, hc)\<guillemotright> \<notin>\<^sub>u $ref\<acute>`"
apply (unfold Timer2_def)
apply (unfold circus_syntax)
apply (simp add: Let_def)
apply (rdes_calc)
apply (unfold hide_state_def)
apply (rel_simp)
apply (erule_tac Q = "step (ct, hc) \<in> ref\<^sub>v" in contrapos_pp; simp)
apply (subgoal_tac "get\<^bsub><currentTime>\<^sub>d\<^esub> st\<^sub>v' = ct \<and> get\<^bsub><stepSize>\<^sub>d\<^esub> st\<^sub>v' = hc")
-- {* Subgoal 1 *}
apply (clarsimp)
-- {* Subgoal 2 *}
apply (thin_tac "\<not> step (get\<^bsub><currentTime>\<^sub>d\<^esub> st\<^sub>v', get\<^bsub><stepSize>\<^sub>d\<^esub> st\<^sub>v') \<in> ref\<^sub>v")
apply (rename_tac n)
apply (case_tac "n = 0")
-- {* Subgoal 2.1 *}
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (clarify)
apply (erule contrapos_pp)
apply (simp)
apply (erule empty_trace_neq_relpowI)
apply (clarsimp)
apply (simp add: Prefix_Order.strict_prefixI')
done
end