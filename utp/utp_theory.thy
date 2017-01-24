section {* UTP Theories *}

theory utp_theory
imports utp_rel
begin

text {* Closure laws for theories *}

named_theorems closure

subsection {* Complete lattice of predicates *}

definition upred_lattice :: "('\<alpha> upred) gorder" ("\<P>") where
"upred_lattice = \<lparr> carrier = UNIV, eq = (op =), le = op \<sqsubseteq> \<rparr>"

interpretation upred_lattice: complete_lattice \<P>
proof (unfold_locales, simp_all add: upred_lattice_def)
  fix A :: "'\<alpha> upred set"
  show "\<exists>s. is_lub \<lparr>carrier = UNIV, eq = op =, le = op \<sqsubseteq>\<rparr> s A"
    apply (rule_tac x="\<Squnion> A" in exI)
    apply (rule least_UpperI)
    apply (auto intro: Inf_greatest simp add: Inf_lower Upper_def)
  done
  show "\<exists>i. is_glb \<lparr>carrier = UNIV, eq = op =, le = op \<sqsubseteq>\<rparr> i A"
    apply (rule_tac x="\<Sqinter> A" in exI)
    apply (rule greatest_LowerI)
    apply (auto intro: Sup_least simp add: Sup_upper Lower_def)
  done
qed

lemma upred_weak_complete_lattice [simp]: "weak_complete_lattice \<P>"
  by (simp add: upred_lattice.weak.weak_complete_lattice_axioms)

lemma upred_lattice_eq [simp]:
  "op .=\<^bsub>\<P>\<^esub> = op ="
  by (simp add: upred_lattice_def)

lemma upred_lattice_le [simp]:
  "le \<P> P Q = (P \<sqsubseteq> Q)"
  by (simp add: upred_lattice_def)

lemma upred_lattice_carrier [simp]:
  "carrier \<P> = UNIV"
  by (simp add: upred_lattice_def)

subsection {* Healthiness conditions *}

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

lemma Healthy_Idempotent [closure]: 
  "Idempotent H \<Longrightarrow> H(P) is H"
  by (simp add: Healthy_def Idempotent_def)

lemma Idempotent_id [simp]: "Idempotent id"
  by (simp add: Idempotent_def)

lemma Idempotent_comp [intro]:
  "\<lbrakk> Idempotent f; Idempotent g; f \<circ> g = g \<circ> f \<rbrakk> \<Longrightarrow> Idempotent (f \<circ> g)"
  by (auto simp add: Idempotent_def comp_def, metis)

lemma Monotonic_id [simp]: "Monotonic id"
  by (simp add: Monotonic_def)

lemma Monotonic_comp [intro]:
  "\<lbrakk> Monotonic f; Monotonic g \<rbrakk> \<Longrightarrow> Monotonic (f \<circ> g)"
  by (auto simp add: Monotonic_def)

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

lemma Healthy_fixed_points [simp]: "fps \<P> H = \<lbrakk>H\<rbrakk>\<^sub>H"
  by (simp add: fps_def upred_lattice_def Healthy_def)

lemma upred_lattice_Idempotent [simp]: "Idem\<^bsub>\<P>\<^esub> H = Idempotent H"
  using upred_lattice.weak_partial_order_axioms by (auto simp add: idempotent_def Idempotent_def)

lemma upred_lattice_Monotonic [simp]: "Mono\<^bsub>\<P>\<^esub> H = Monotonic H"
  using upred_lattice.weak_partial_order_axioms by (auto simp add: isotone_def Monotonic_def)

subsection {* UTP theory hierarchy *}

text {* Unfortunately we can currently only characterise UTP theories of homogeneous relations;
        this is due to restrictions in the instantiation of Isabelle's polymorphic constants. *}

consts
  utp_hcond :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> ('\<alpha> \<times> '\<alpha>) Healthiness_condition" ("\<H>\<index>")
  utp_unit  :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> '\<alpha> hrelation" ("\<I>\<I>\<index>")

definition utp_order :: "('\<T> \<times> '\<alpha>) itself \<Rightarrow> '\<alpha> hrelation gorder" where
"utp_order T = \<lparr> carrier = {P. P is \<H>\<^bsub>T\<^esub>}, eq = (op =), le = op \<sqsubseteq> \<rparr>"

lemma utp_order_carrier [simp]:
  "carrier (utp_order T) = \<lbrakk>\<H>\<^bsub>T\<^esub>\<rbrakk>\<^sub>H"
  by (simp add: utp_order_def)

lemma utp_order_eq [simp]:
  "eq (utp_order T) = op ="
  by (simp add: utp_order_def)

lemma utp_order_le [simp]:
  "le (utp_order T) = op \<sqsubseteq>"
  by (simp add: utp_order_def)

lemma utp_partial_order: "partial_order (utp_order T)"
  by (unfold_locales, simp_all add: utp_order_def)

lemma utp_weak_partial_order: "weak_partial_order (utp_order T)"
  by (unfold_locales, simp_all add: utp_order_def)

lemma mono_Monotone_utp_order:
  "mono f \<Longrightarrow> Monotone (utp_order T) f"
  apply (auto simp add: isotone_def)
  apply (metis partial_order_def utp_partial_order)
  apply (metis monoD)
done

lemma isotone_utp_orderI: "Monotonic H \<Longrightarrow> isotone (utp_order X) (utp_order Y) H"
  by (auto simp add: Monotonic_def isotone_def utp_weak_partial_order)

text {* UTP order is the fixed point lattice *}

lemma utp_order_fpl: "utp_order T = fpl \<P> (\<H>\<^bsub>T\<^esub>)"
  by (auto simp add: utp_order_def upred_lattice_def fps_def Healthy_def)

locale utp_theory =
  fixes \<T> :: "('\<T> \<times> '\<alpha>) itself" (structure)
  assumes ThTag_def: "TYPE('\<T> \<times> '\<alpha>) = \<T>"
  and HCond_Idem: "\<H>(\<H>(P)) = \<H>(P)"
begin
  lemma HCond_Idempotent [closure,intro]: "Idempotent \<H>"
    by (simp add: Idempotent_def HCond_Idem)

  sublocale partial_order "utp_order \<T>"
    by (unfold_locales, simp_all add: utp_order_def)
end

locale utp_theory_lattice = utp_theory \<T> + complete_lattice "utp_order \<T>" for \<T> :: "('\<T> \<times> '\<alpha>) itself" (structure)
  
abbreviation utp_top ("\<^bold>\<top>\<index>")
where "utp_top \<T> \<equiv> atop (utp_order \<T>)"

abbreviation utp_bottom ("\<^bold>\<bottom>\<index>")
where "utp_bottom \<T> \<equiv> abottom (utp_order \<T>)"

abbreviation utp_join (infixl "\<^bold>\<squnion>\<index>" 65) where
"utp_join \<T> \<equiv> join (utp_order \<T>)"

abbreviation utp_meet (infixl "\<^bold>\<sqinter>\<index>" 70) where
"utp_meet \<T> \<equiv> meet (utp_order \<T>)"

abbreviation utp_gfp ("\<^bold>\<nu>\<index>") where
"utp_gfp \<T> \<equiv> \<nu>\<^bsub>utp_order \<T>\<^esub>"

abbreviation utp_lfp ("\<^bold>\<mu>\<index>") where
"utp_lfp \<T> \<equiv> \<mu>\<^bsub>utp_order \<T>\<^esub>"

context utp_theory_lattice
begin

  lemma LFP_healthy_comp: "\<^bold>\<mu> F = \<^bold>\<mu> (F \<circ> \<H>)"
  proof -
    have "{P. (P is \<H>) \<and> F P \<sqsubseteq> P} = {P. (P is \<H>) \<and> F (\<H> P) \<sqsubseteq> P}"
      by (auto simp add: Healthy_def)
    thus ?thesis
      by (simp add: LFP_def)
  qed

  lemma GFP_healthy_comp: "\<^bold>\<nu> F = \<^bold>\<nu> (F \<circ> \<H>)"
  proof -
    have "{P. (P is \<H>) \<and> P \<sqsubseteq> F P} = {P. (P is \<H>) \<and> P \<sqsubseteq> F (\<H> P)}"
      by (auto simp add: Healthy_def)
    thus ?thesis
      by (simp add: GFP_def)
  qed

  lemma top_healthy [closure]: "\<^bold>\<top> is \<H>"
    using weak.top_closed by auto

  lemma bottom_healthy [closure]: "\<^bold>\<bottom> is \<H>"
    using weak.bottom_closed by auto
    
  lemma utp_top: "P is \<H> \<Longrightarrow> P \<sqsubseteq> \<^bold>\<top>"
    using weak.top_higher by auto

  lemma utp_bottom: "P is \<H> \<Longrightarrow> \<^bold>\<bottom> \<sqsubseteq> P"
    using weak.bottom_lower by auto

end

lemma upred_top: "\<top>\<^bsub>\<P>\<^esub> = false"
  using ball_UNIV greatest_def by fastforce

lemma upred_bottom: "\<bottom>\<^bsub>\<P>\<^esub> = true"
  by fastforce

locale utp_theory_mono = utp_theory + 
  assumes HCond_Mono [closure,intro]: "Monotonic \<H>"

sublocale utp_theory_mono \<subseteq> utp_theory_lattice
proof -
  text {* Use Knaster-Tarski theorem to obtain complete lattice *}

  interpret weak_complete_lattice "fpl \<P> \<H>"
    by (rule Knaster_Tarski, auto simp add: upred_lattice.weak.weak_complete_lattice_axioms)
  
  have "complete_lattice (fpl \<P> \<H>)"
    by (unfold_locales, simp add: fps_def sup_exists, (blast intro: sup_exists inf_exists)+)

  hence "complete_lattice (utp_order \<T>)"
    by (simp add: utp_order_def, simp add: upred_lattice_def)

  thus "utp_theory_lattice \<T>"
    by (simp add: utp_theory_axioms utp_theory_lattice_def)
qed

context utp_theory_mono
begin

  lemma healthy_top: "\<^bold>\<top> = \<H>(false)"
  proof -
    have "\<^bold>\<top> = \<top>\<^bsub>fpl \<P> \<H>\<^esub>"
      by (simp add: utp_order_fpl)
    also have "... = \<H> \<top>\<^bsub>\<P>\<^esub>"
      using Knaster_Tarski_idem_extremes(1)[of \<P> \<H>]  
      by (simp add: HCond_Idempotent HCond_Mono)
    also have "... = \<H> false"
      by (simp add: upred_top)
    finally show ?thesis .
  qed

  lemma healthy_bottom: "\<^bold>\<bottom> = \<H>(true)"
  proof -
    have "\<^bold>\<bottom> = \<bottom>\<^bsub>fpl \<P> \<H>\<^esub>"
      by (simp add: utp_order_fpl)
    also have "... = \<H> \<bottom>\<^bsub>\<P>\<^esub>"
      using Knaster_Tarski_idem_extremes(2)[of \<P> \<H>]  
      by (simp add: HCond_Idempotent HCond_Mono)
    also have "... = \<H> true"
      by (simp add: upred_bottom)
    finally show ?thesis .
  qed

end

locale utp_theory_rel =
  utp_theory +
  assumes Healthy_Sequence [closure]: "\<lbrakk> P is \<H>; Q is \<H> \<rbrakk> \<Longrightarrow> (P ;; Q) is \<H>"

locale utp_theory_left_unital = 
  utp_theory_rel +
  assumes Healthy_Left_Unit [closure]: "\<I>\<I> is \<H>"
  and Left_Unit: "P is \<H> \<Longrightarrow> (\<I>\<I> ;; P) = P"

locale utp_theory_right_unital = 
  utp_theory_rel +
  assumes Healthy_Right_Unit [closure]: "\<I>\<I> is \<H>"
  and Right_Unit: "P is \<H> \<Longrightarrow> (P ;; \<I>\<I>) = P"

locale utp_theory_unital =
  utp_theory_rel +
  assumes Healthy_Unit [closure]: "\<I>\<I> is \<H>"
  and Unit_Left: "P is \<H> \<Longrightarrow> (\<I>\<I> ;; P) = P" 
  and Unit_Right: "P is \<H> \<Longrightarrow> (P ;; \<I>\<I>) = P"

locale utp_theory_mono_unital = utp_theory_mono + utp_theory_unital

definition utp_star ("_\<^bold>\<star>\<index>" [999] 999) where
"utp_star \<T> P = (\<^bold>\<nu>\<^bsub>\<T>\<^esub> (\<lambda> X. (P ;; X) \<^bold>\<sqinter>\<^bsub>\<T>\<^esub> \<I>\<I>\<^bsub>\<T>\<^esub>))"

definition utp_omega ("_\<^bold>\<omega>\<index>" [999] 999) where
"utp_omega \<T> P = (\<mu>\<^bsub>\<T>\<^esub> (\<lambda> X. (P ;; X)))"

locale utp_pre_left_quantale = utp_theory_lattice + utp_theory_left_unital
begin

  lemma star_healthy [closure]: "P\<^bold>\<star> is \<H>"
    by (metis mem_Collect_eq utp_order_carrier utp_star_def weak.GFP_closed)

end

sublocale utp_theory_unital \<subseteq> utp_theory_left_unital
  by (simp add: Healthy_Unit Unit_Left Healthy_Sequence utp_theory_rel_def utp_theory_axioms utp_theory_rel_axioms_def utp_theory_left_unital_axioms_def utp_theory_left_unital_def)

sublocale utp_theory_unital \<subseteq> utp_theory_right_unital
  by (simp add: Healthy_Unit Unit_Right Healthy_Sequence utp_theory_rel_def utp_theory_axioms utp_theory_rel_axioms_def utp_theory_right_unital_axioms_def utp_theory_right_unital_def)

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

interpretation rel_theory: utp_theory_mono_unital REL
  by (unfold_locales, simp_all add: rel_hcond_def rel_unit_def Healthy_def)

lemma REL_top: "\<^bold>\<top>\<^bsub>REL\<^esub> = false"
  by(simp add: rel_hcond_def rel_theory.healthy_top)

lemma REL_bottom: "\<^bold>\<bottom>\<^bsub>REL\<^esub> = true"
  by (simp add: rel_hcond_def rel_theory.healthy_bottom)

subsection {* Theory links *}

definition mk_conn ("_ \<leftarrow>\<langle>_,_\<rangle>\<rightarrow> _" [90,0,0,91] 91) where
"T1 \<leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<rightarrow> T2 \<equiv> \<lparr> orderA = utp_order T1, orderB = utp_order T2, lower = \<H>\<^sub>2, upper = \<H>\<^sub>1 \<rparr>"

lemma mk_conn_orderA [simp]: "\<X>\<^bsub>T1 \<leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<rightarrow> T2\<^esub> = utp_order T1" 
  by (simp add:mk_conn_def)

lemma mk_conn_orderB [simp]: "\<Y>\<^bsub>T1 \<leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<rightarrow> T2\<^esub> = utp_order T2" 
  by (simp add:mk_conn_def)

lemma mk_conn_lower [simp]:  "\<pi>\<^sub>*\<^bsub>T1 \<leftarrow>\<langle>H\<^sub>1,H\<^sub>2\<rangle>\<rightarrow> T2\<^esub> = H\<^sub>1"
  by (simp add: mk_conn_def)

lemma mk_conn_upper [simp]:  "\<pi>\<^sup>*\<^bsub>T1 \<leftarrow>\<langle>H\<^sub>1,H\<^sub>2\<rangle>\<rightarrow> T2\<^esub> = H\<^sub>2"
  by (simp add: mk_conn_def)

lemma galois_comp: "(T\<^sub>2 \<leftarrow>\<langle>\<H>\<^sub>3,\<H>\<^sub>4\<rangle>\<rightarrow> T\<^sub>3) \<circ>\<^sub>g (T\<^sub>1 \<leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<rightarrow> T\<^sub>2) = T\<^sub>1 \<leftarrow>\<langle>\<H>\<^sub>1\<circ>\<H>\<^sub>3,\<H>\<^sub>4\<circ>\<H>\<^sub>2\<rangle>\<rightarrow> T\<^sub>3"
  by (simp add: comp_galcon_def mk_conn_def)

end
