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

definition Conjunctive :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
"Conjunctive(H) \<longleftrightarrow> (\<exists> Q. \<forall> P. H(P) = (P \<and> Q))"

lemma Conjuctive_Idempotent: 
  "Conjunctive(H) \<Longrightarrow> Idempotent(H)"
  by (auto simp add: Conjunctive_def Idempotent_def)

definition Monotonic :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
"Monotonic(H) \<longleftrightarrow> (\<forall> P Q. `(P \<Rightarrow> Q) \<Rightarrow> (H(P) \<Rightarrow> H(Q))`)"

definition Antitone :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
"Antitone(H) \<longleftrightarrow> (\<forall> P Q. `(P \<Rightarrow> Q) \<Rightarrow> (H(Q) \<Rightarrow> H(P))`)"

definition NM : "NM(P) = (\<not> P \<and> true)"

lemma "Monotonic(NM)"
 apply (simp add:Monotonic_def)
 nitpick (* yes, that fails *)
 oops

lemma "Antitone(NM)"
 apply (simp add:Antitone_def NM)
 by pred_tac

definition WeakConjunctive :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
"WeakConjunctive(H) \<longleftrightarrow> (\<forall> P. \<exists> Q. H(P) = (P \<and> Q)) \<and> Monotonic(H)"

lemma wkConjunctive_Idempotent:
  "WeakConjunctive(H) \<Longrightarrow> Idempotent(H)"
  by (simp add:WeakConjunctive_def Monotonic_def Idempotent_def, pred_tac)

end