section {* UTP Theories *}

theory utp_theory
imports utp_rel
begin

type_synonym '\<alpha> Healthiness_condition = "'\<alpha> upred \<Rightarrow> '\<alpha> upred"

definition 
Healthy::"'\<alpha> upred \<Rightarrow> '\<alpha> Healthiness_condition \<Rightarrow> bool" (infix "is" 30)
where "P is H \<equiv> (P = H P)"

lemma Healthy_def': "P is H \<longleftrightarrow> (H P = P)"
  unfolding Healthy_def by auto

declare Healthy_def' [upred_defs]

(* FIXME: To be reviewed with Simon.
          Considered an attempt at defining Conjunctive/WeakConjunctive & Monotonic
          healthiness conditions. *)

definition "Idempotent(H) \<longleftrightarrow> (\<forall> P. H(H(P)) = H(P))"

definition "Monotonic(H) \<longleftrightarrow> (\<forall> P Q. Q \<sqsubseteq> P \<longrightarrow> (H(Q) \<sqsubseteq> H(P)))"

definition "IMH(H) \<longleftrightarrow> Idempotent(H) \<and> Monotonic(H)"

definition "Antitone(H) \<longleftrightarrow> (\<forall> P Q. Q \<sqsubseteq> P \<longrightarrow> (H(P) \<sqsubseteq> H(Q)))"

definition NM : "NM(P) = (\<not> P \<and> true)"

lemma "Monotonic(NM)"
  apply (simp add:Monotonic_def)
  nitpick (* yes, that fails because it is not monotonic *)
  oops

lemma "Antitone(NM)"
  by (simp add:Antitone_def NM)

definition Conjunctive :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
  "Conjunctive(H) \<longleftrightarrow> (\<exists> Q. \<forall> P. H(P) = (P \<and> Q))"

lemma Conjuctive_Idempotent: 
  "Conjunctive(H) \<Longrightarrow> Idempotent(H)"
  by (auto simp add: Conjunctive_def Idempotent_def)

lemma Conjunctive_Monotonic: 
  "Conjunctive(H) \<Longrightarrow> Monotonic(H)"
  unfolding Conjunctive_def Monotonic_def
  using dual_order.trans by fastforce

lemma Conjunctive_conj:
  assumes "Conjunctive(HC)"
  shows "HC(P \<and> Q) = (HC(P) \<and> Q)"
  using assms unfolding Conjunctive_def
  by (metis utp_pred.inf.assoc utp_pred.inf.commute)

lemma Conjunctive_distr_conj:
  assumes "Conjunctive(HC)"
  shows "HC(P \<and> Q) = (HC(P) \<and> HC(Q))"
  using assms unfolding Conjunctive_def
  by (metis Conjunctive_conj assms utp_pred.inf.assoc utp_pred.inf_right_idem)

lemma Conjunctive_distr_disj:
  assumes "Conjunctive(HC)"
  shows "HC(P \<or> Q) = (HC(P) \<or> HC(Q))"
  using assms unfolding Conjunctive_def
  using utp_pred.inf_sup_distrib2 by fastforce

definition FunctionalConjunctive :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
"FunctionalConjunctive(H) \<longleftrightarrow> (\<exists> F. \<forall> P. H(P) = (P \<and> F(P)) \<and> Monotonic(F))"

definition WeakConjunctive :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
"WeakConjunctive(H) \<longleftrightarrow> (\<forall> P. \<exists> Q. H(P) = (P \<and> Q))"

lemma FunctionalConjunctive_Monotonic:
  "FunctionalConjunctive(H) \<Longrightarrow> Monotonic(H)"
  unfolding FunctionalConjunctive_def by (metis Monotonic_def utp_pred.inf_mono)

lemma WeakConjunctive_Refinement:
  assumes "WeakConjunctive(HC)"
  shows "P \<sqsubseteq> HC(P)"
  using assms unfolding WeakConjunctive_def by (metis utp_pred.inf.cobounded1)

lemma WeakCojunctive_Healthy_Refinement:
  assumes "WeakConjunctive(HC)" and "P is HC"
  shows "HC(P) \<sqsubseteq> P"
  using assms unfolding WeakConjunctive_def Healthy_def by simp

lemma WeakConjunctive_implies_WeakConjunctive:
  "Conjunctive(H) \<Longrightarrow> WeakConjunctive(H)"
  unfolding WeakConjunctive_def Conjunctive_def by pred_tac

end