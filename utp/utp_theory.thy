section {* UTP Theories *}

theory utp_theory
imports utp_rel
begin

type_synonym '\<alpha> Healthiness_condition = "'\<alpha> upred \<Rightarrow> '\<alpha> upred"

definition 
Healthy::"'\<alpha> upred \<Rightarrow> '\<alpha> Healthiness_condition \<Rightarrow> bool" (infix "is" 30)
where "P is H \<equiv> (H P = P)"

lemma Healthy_def': "P is H \<longleftrightarrow> (H P = P)"
  unfolding Healthy_def by auto

lemma Healthy_if: "P is H \<Longrightarrow> (H P = P)"
  unfolding Healthy_def by auto

declare Healthy_def' [upred_defs]

abbreviation Healthy_carrier :: "'\<alpha> Healthiness_condition \<Rightarrow> '\<alpha> upred set" ("\<lbrakk>_\<rbrakk>\<^sub>H")
where "\<lbrakk>H\<rbrakk>\<^sub>H \<equiv> {P. P is H}"

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

lemma Conjunctive_distr_cond:
  assumes "Conjunctive(HC)"
  shows "HC(P \<triangleleft> b \<triangleright> Q) = (HC(P) \<triangleleft> b \<triangleright> HC(Q))"
  using assms unfolding Conjunctive_def
  by (metis cond_conj_distr utp_pred.inf_commute)

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
  unfolding WeakConjunctive_def Conjunctive_def by pred_auto

declare Conjunctive_def [upred_defs]
declare Monotonic_def [upred_defs]

subsection {* UTP theory hierarchy *}

text {* Unfortunately we can currently only characterise UTP theories of homogeneous relations;
        this is due to restrictions in the instantiation of Isabelle's polymorphic constants. *}

consts
  utp_hcond :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> ('\<alpha> \<times> '\<alpha>) Healthiness_condition" ("\<H>\<index>")
  utp_unit  :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> '\<alpha> hrelation" ("\<I>\<I>\<index>")

definition utp_order :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> '\<alpha> hrelation gorder" where
"utp_order T = \<lparr> carrier = {P. P is \<H>\<^bsub>T\<^esub>}, eq = (op =), le = op \<sqsubseteq> \<rparr>"

locale utp_theory =
  fixes \<T> :: "('\<T> \<times> '\<alpha>) itself" (structure)
  assumes HCond_Idem: "\<H>(\<H>(P)) = \<H>(P)"
begin
  sublocale partial_order "utp_order \<T>"
    by (unfold_locales, simp_all add: utp_order_def)
end

locale utp_theory_lattice = utp_theory \<T> + complete_lattice "utp_order \<T>" for \<T> :: "('\<T> \<times> '\<alpha>) itself" (structure)

locale utp_theory_left_unital = 
  utp_theory +
  assumes Healthy_Left_Unit: "\<I>\<I> is \<H>"
  and Left_Unit: "P is \<H> \<Longrightarrow> (\<I>\<I> ;; P) = P"

locale utp_theory_right_unital = 
  utp_theory +
  assumes Healthy_Right_Unit: "\<I>\<I> is \<H>"
  and Right_Unit: "P is \<H> \<Longrightarrow> (P ;; \<I>\<I>) = P"

locale utp_theory_unital =
  utp_theory +
  assumes Healthy_Unit: "\<I>\<I> is \<H>"
  and Unit_Left: "P is \<H> \<Longrightarrow> (\<I>\<I> ;; P) = P" 
  and Unit_Right: "P is \<H> \<Longrightarrow> (P ;; \<I>\<I>) = P"

sublocale utp_theory_unital \<subseteq> utp_theory_left_unital
  by (simp add: Healthy_Unit Unit_Left utp_theory_axioms utp_theory_left_unital_axioms_def utp_theory_left_unital_def)

sublocale utp_theory_unital \<subseteq> utp_theory_right_unital
  by (simp add: Healthy_Unit Unit_Right utp_theory_axioms utp_theory_right_unital_axioms_def utp_theory_right_unital_def)

typedef REL = "UNIV :: unit set" ..

abbreviation "REL \<equiv> TYPE(REL \<times> '\<alpha>)"

overloading
  rel_hcond == "utp_hcond :: (REL \<times> '\<alpha>) itself \<Rightarrow> ('\<alpha> \<times> '\<alpha>) Healthiness_condition"
  rel_unit == "utp_unit :: (REL \<times> '\<alpha>) itself \<Rightarrow> '\<alpha> hrelation"
begin
  definition rel_hcond :: "(REL \<times> '\<alpha>) itself \<Rightarrow> ('\<alpha> \<times> '\<alpha>) upred \<Rightarrow> ('\<alpha> \<times> '\<alpha>) upred" where
  "rel_hcond T = id"

  definition rel_unit :: "(REL \<times> '\<alpha>) itself \<Rightarrow> '\<alpha> hrelation" where
  "rel_unit T = II"
end

interpretation rel_theory: utp_theory_unital REL
  by (unfold_locales, simp_all add: rel_hcond_def rel_unit_def Healthy_def)

lemma utp_partial_order: "partial_order (utp_order T)"
  by (unfold_locales, simp_all add: utp_order_def)

lemma mono_Monotone_utp_order:
  "mono f \<Longrightarrow> Monotone (utp_order T) f"
  apply (auto simp add: isotone_def)
  apply (metis partial_order_def utp_partial_order)
  apply (simp add: utp_order_def)
  apply (metis monoD)
done

end
