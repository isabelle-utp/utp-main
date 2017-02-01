section {* UTP Theories *}

theory utp_theory
imports utp_rel
begin

text {* Closure laws for theories *}

named_theorems closure

subsection {* Complete lattice of predicates *}

definition upred_lattice :: "('\<alpha> upred) gorder" ("\<P>") where
"upred_lattice = \<lparr> carrier = UNIV, eq = (op =), le = op \<sqsubseteq> \<rparr>"

text {* @{term "\<P>"} is the complete lattice of alphabetised predicates. All other theories will
  be defined relative to it. *}

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

subsection {* Properties of healthiness conditions *}

definition Idempotent :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
  "Idempotent(H) \<longleftrightarrow> (\<forall> P. H(H(P)) = H(P))"

definition Monotonic :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where
  "Monotonic(H) \<longleftrightarrow> (\<forall> P Q. Q \<sqsubseteq> P \<longrightarrow> (H(Q) \<sqsubseteq> H(P)))"

definition IMH :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where
  "IMH(H) \<longleftrightarrow> Idempotent(H) \<and> Monotonic(H)"

definition Antitone :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where
  "Antitone(H) \<longleftrightarrow> (\<forall> P Q. Q \<sqsubseteq> P \<longrightarrow> (H(P) \<sqsubseteq> H(Q)))"

definition Conjunctive :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
  "Conjunctive(H) \<longleftrightarrow> (\<exists> Q. \<forall> P. H(P) = (P \<and> Q))"

definition FunctionalConjunctive :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
  "FunctionalConjunctive(H) \<longleftrightarrow> (\<exists> F. \<forall> P. H(P) = (P \<and> F(P)) \<and> Monotonic(F))"

definition WeakConjunctive :: "'\<alpha> Healthiness_condition \<Rightarrow> bool" where 
  "WeakConjunctive(H) \<longleftrightarrow> (\<forall> P. \<exists> Q. H(P) = (P \<and> Q))"

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

subsection {* UTP theories hierarchy *}

typedef ('\<T>, '\<alpha>) uthy = "UNIV :: unit set"
  by auto

text {* We create a unitary parametric type to represent UTP theories. These are merely tags
  and contain no data other than to help the type-system resolve polymorphic definitions. The
  two parameters denote the name of the UTP theory -- as a unique type -- and the minimal
  alphabet that the UTP theory requires. We will then use Isabelle's ad-hoc overloading
  mechanism to associate theory constructs, like healthiness conditions and units, with
  each of these types. This will allow the type system to retrieve definitions based
  on a particular theory context. *}

definition uthy :: "('a, 'b) uthy" where
"uthy = Abs_uthy ()"

lemma uthy_eq [intro]: 
  fixes x y :: "('a, 'b) uthy"
  shows "x = y"
  by (cases x, cases y, simp)

syntax
  "_UTHY" :: "type \<Rightarrow> type \<Rightarrow> logic" ("UTHY'(_, _')")

translations
  "UTHY('T, '\<alpha>)" == "CONST uthy :: ('T, '\<alpha>) uthy"

text {* We set up polymorphic constants to denote the healthiness conditions associated with
  a UTP theory. Unfortunately we can currently only characterise UTP theories of homogeneous 
  relations; this is due to restrictions in the instantiation of Isabelle's polymorphic constants
  which apparently cannot specialise types in this way. *}

consts
  utp_hcond :: "('\<T>, '\<alpha>) uthy \<Rightarrow> ('\<alpha> \<times> '\<alpha>) Healthiness_condition" ("\<H>\<index>")

definition utp_order :: "('\<alpha> \<times> '\<alpha>) Healthiness_condition \<Rightarrow> '\<alpha> hrelation gorder" where
"utp_order H = \<lparr> carrier = {P. P is H}, eq = (op =), le = op \<sqsubseteq> \<rparr>"

abbreviation "uthy_order T \<equiv> utp_order \<H>\<^bsub>T\<^esub>"

text {* Constant @{term utp_order} obtains the order structure associated with a UTP theory. 
  Its carrier is the set of healthy predicates, equality is HOL equality, and the order is
  refinement. *}

lemma utp_order_carrier [simp]:
  "carrier (utp_order H) = \<lbrakk>H\<rbrakk>\<^sub>H"
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

text {* The UTP order can equivalently be characterised as the fixed point lattice, @{const fpl}. *}

lemma utp_order_fpl: "utp_order H = fpl \<P> H"
  by (auto simp add: utp_order_def upred_lattice_def fps_def Healthy_def)

definition uth_eq :: "('T\<^sub>1, '\<alpha>) uthy \<Rightarrow> ('T\<^sub>2, '\<alpha>) uthy \<Rightarrow> bool" (infix "\<approx>\<^sub>T" 50) where
"T\<^sub>1 \<approx>\<^sub>T T\<^sub>2 \<longleftrightarrow> \<lbrakk>\<H>\<^bsub>T\<^sub>1\<^esub>\<rbrakk>\<^sub>H = \<lbrakk>\<H>\<^bsub>T\<^sub>2\<^esub>\<rbrakk>\<^sub>H"

lemma uth_eq_refl: "T \<approx>\<^sub>T T"
  by (simp add: uth_eq_def)

lemma uth_eq_sym: "T\<^sub>1 \<approx>\<^sub>T T\<^sub>2 \<longleftrightarrow> T\<^sub>2 \<approx>\<^sub>T T\<^sub>1"
  by (auto simp add: uth_eq_def)

lemma uth_eq_trans: "\<lbrakk> T\<^sub>1 \<approx>\<^sub>T T\<^sub>2; T\<^sub>2 \<approx>\<^sub>T T\<^sub>3 \<rbrakk> \<Longrightarrow> T\<^sub>1 \<approx>\<^sub>T T\<^sub>3"
  by (auto simp add: uth_eq_def)

definition uthy_plus :: "('T\<^sub>1, '\<alpha>) uthy \<Rightarrow> ('T\<^sub>2, '\<alpha>) uthy \<Rightarrow> ('T\<^sub>1 \<times> 'T\<^sub>2, '\<alpha>) uthy" (infixl "+\<^sub>T" 65) where
"uthy_plus T\<^sub>1 T\<^sub>2 = uthy"

overloading
  prod_hcond == "utp_hcond :: ('T\<^sub>1 \<times> 'T\<^sub>2, '\<alpha>) uthy \<Rightarrow> ('\<alpha> \<times> '\<alpha>) Healthiness_condition"
begin

  text {* The healthiness condition of a relation is simply identity, since every alphabetised
    relation is healthy. *}

  definition prod_hcond :: "('T\<^sub>1 \<times> 'T\<^sub>2, '\<alpha>) uthy \<Rightarrow> ('\<alpha> \<times> '\<alpha>) upred \<Rightarrow> ('\<alpha> \<times> '\<alpha>) upred" where
  "prod_hcond T = \<H>\<^bsub>UTHY('T\<^sub>1, '\<alpha>)\<^esub> \<circ> \<H>\<^bsub>UTHY('T\<^sub>2, '\<alpha>)\<^esub>"

end

subsection {* UTP theory hierarchy *}

text {* We next define a hierarchy of locales that characterise different classes of UTP theory.
  Minimally we require that a UTP theory's healthiness condition is idempotent. *}

locale utp_theory =
  fixes \<T> :: "('\<T>, '\<alpha>) uthy" (structure)
  assumes HCond_Idem: "\<H>(\<H>(P)) = \<H>(P)"
begin

  lemma uthy_simp:
    "uthy = \<T>"
    by blast

  text {* A UTP theory fixes @{term "\<T>"}, the structural element denoting the UTP theory. All
    constants associated with UTP theories can then be resolved by the type system. *}

  lemma HCond_Idempotent [closure,intro]: "Idempotent \<H>"
    by (simp add: Idempotent_def HCond_Idem)

  sublocale partial_order "uthy_order \<T>"
    by (unfold_locales, simp_all add: utp_order_def)
end

text {* Theory summation is commutative provided the healthiness conditions commute. *}

lemma uthy_plus_comm: 
  assumes "\<H>\<^bsub>T\<^sub>1\<^esub> \<circ> \<H>\<^bsub>T\<^sub>2\<^esub> = \<H>\<^bsub>T\<^sub>2\<^esub> \<circ> \<H>\<^bsub>T\<^sub>1\<^esub>"
  shows "T\<^sub>1 +\<^sub>T T\<^sub>2 \<approx>\<^sub>T T\<^sub>2 +\<^sub>T T\<^sub>1"
proof -
  have "T\<^sub>1 = uthy" "T\<^sub>2 = uthy"
    by blast+
  thus ?thesis
    using assms by (simp add: uth_eq_def prod_hcond_def)
qed

lemma uthy_plus_assoc: "T\<^sub>1 +\<^sub>T (T\<^sub>2 +\<^sub>T T\<^sub>3) \<approx>\<^sub>T (T\<^sub>1 +\<^sub>T T\<^sub>2) +\<^sub>T T\<^sub>3"
  by (simp add: uth_eq_def prod_hcond_def comp_def) 

lemma uthy_plus_idem: "utp_theory T \<Longrightarrow> T +\<^sub>T T \<approx>\<^sub>T T"
  by (simp add: uth_eq_def prod_hcond_def Healthy_def utp_theory.HCond_Idem utp_theory.uthy_simp)

locale utp_theory_lattice = utp_theory \<T> + complete_lattice "uthy_order \<T>" for \<T> :: "('\<T>, '\<alpha>) uthy" (structure)
  
text {* The healthiness conditions of a UTP theory lattice form a complete lattice, and allows us to make
  use of complete lattice results from HOL-Algebra, such as the Knaster-Tarski theorem. We can also 
  retrieve lattice operators as below. *}

abbreviation utp_top ("\<^bold>\<top>\<index>")
where "utp_top \<T> \<equiv> atop (uthy_order \<T>)"

abbreviation utp_bottom ("\<^bold>\<bottom>\<index>")
where "utp_bottom \<T> \<equiv> abottom (uthy_order \<T>)"

abbreviation utp_join (infixl "\<^bold>\<squnion>\<index>" 65) where
"utp_join \<T> \<equiv> join (uthy_order \<T>)"

abbreviation utp_meet (infixl "\<^bold>\<sqinter>\<index>" 70) where
"utp_meet \<T> \<equiv> meet (uthy_order \<T>)"

abbreviation utp_sup ("\<^bold>\<Squnion>\<index>_" [90] 90) where
"utp_sup \<T> \<equiv> asup (uthy_order \<T>)"

abbreviation utp_inf ("\<^bold>\<Sqinter>\<index>_" [90] 90) where
"utp_inf \<T> \<equiv> ainf (uthy_order \<T>)"

abbreviation utp_gfp ("\<^bold>\<nu>\<index>") where
"utp_gfp \<T> \<equiv> \<nu>\<^bsub>uthy_order \<T>\<^esub>"

abbreviation utp_lfp ("\<^bold>\<mu>\<index>") where
"utp_lfp \<T> \<equiv> \<mu>\<^bsub>uthy_order \<T>\<^esub>"

text {* We can then derive a number of properties about these operators, as below. *}

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

text {* One way of obtaining a complete lattice is showing that the healthiness conditions
  are monotone, which the below locale characterises. *}

locale utp_theory_mono = utp_theory + 
  assumes HCond_Mono [closure,intro]: "Monotonic \<H>"

sublocale utp_theory_mono \<subseteq> utp_theory_lattice
proof -
  text {* We can then use the Knaster-Tarski theorem to obtain a complete lattice, and thus
    provide all the usual properties. *}

  interpret weak_complete_lattice "fpl \<P> \<H>"
    by (rule Knaster_Tarski, auto simp add: upred_lattice.weak.weak_complete_lattice_axioms)
  
  have "complete_lattice (fpl \<P> \<H>)"
    by (unfold_locales, simp add: fps_def sup_exists, (blast intro: sup_exists inf_exists)+)

  hence "complete_lattice (uthy_order \<T>)"
    by (simp add: utp_order_def, simp add: upred_lattice_def)

  thus "utp_theory_lattice \<T>"
    by (simp add: utp_theory_axioms utp_theory_lattice_def)
qed

context utp_theory_mono
begin

  text {* In a monotone theory, the top and bottom can always be obtained by applying the healthiness
    condition to the predicate top and bottom, respectively. *}

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

text {* In another direction, we can also characterise UTP theories that are relational. Minimally
  this requires that the healthiness condition is closed under sequential composition. *}

locale utp_theory_rel =
  utp_theory +
  assumes Healthy_Sequence [closure]: "\<lbrakk> P is \<H>; Q is \<H> \<rbrakk> \<Longrightarrow> (P ;; Q) is \<H>"

text {* There also exist UTP theories with units, and the following operator is a theory specific
  operator for them. *}

consts
  utp_unit  :: "('\<T>, '\<alpha>) uthy \<Rightarrow> '\<alpha> hrelation" ("\<I>\<I>\<index>")

text {* Not all theories have both a left and a right unit (e.g. H1-H2 designs) and so we split
  up the locale into two cases. *}

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

subsection {* Theory of relations *}

text {* We can exemplify the creation of a UTP theory with the theory of relations, a trivial theory. *}

typedecl REL
abbreviation "REL \<equiv> UTHY(REL, '\<alpha>)"

text {* We declare the type @{type REL} to be the tag for this theory. We need know nothing about
  this type (other than it's non-empty), since it is merely a name. We also create the corresponding
  constant to refer to the theory. Then we can use it to instantiate the relevant polymorphic
  constants. *}

overloading
  rel_hcond == "utp_hcond :: (REL, '\<alpha>) uthy \<Rightarrow> ('\<alpha> \<times> '\<alpha>) Healthiness_condition"
  rel_unit == "utp_unit :: (REL, '\<alpha>) uthy \<Rightarrow> '\<alpha> hrelation"
begin

  text {* The healthiness condition of a relation is simply identity, since every alphabetised
    relation is healthy. *}

  definition rel_hcond :: "(REL, '\<alpha>) uthy \<Rightarrow> ('\<alpha> \<times> '\<alpha>) upred \<Rightarrow> ('\<alpha> \<times> '\<alpha>) upred" where
  "rel_hcond T = id"

  text {* The unit of the theory is simply the relational unit. *}

  definition rel_unit :: "(REL, '\<alpha>) uthy \<Rightarrow> '\<alpha> hrelation" where
  "rel_unit T = II"
end

text {* Finally we can show that relations are a monotone and unital theory using a locale interpretation,
  which requires that we prove all the relevant properties. It's convenient to rewrite some
  of the theorems so that the provisos are more UTP like; e.g. that the carrier is the
  set of healthy predicates. *}

interpretation rel_theory: utp_theory_mono_unital REL
  rewrites "carrier (uthy_order REL) = \<lbrakk>id\<rbrakk>\<^sub>H"
  by (unfold_locales, simp_all add: rel_hcond_def rel_unit_def Healthy_def)

text {* We can then, for instance, determine what the top and bottom of our new theory is. *}

lemma REL_top: "\<^bold>\<top>\<^bsub>REL\<^esub> = false"
  by (simp add: rel_theory.healthy_top, simp add: rel_hcond_def)

lemma REL_bottom: "\<^bold>\<bottom>\<^bsub>REL\<^esub> = true"
  by (simp add: rel_theory.healthy_bottom, simp add: rel_hcond_def)

text {* A number of theorems have been exported, such at the fixed point unfolding laws. *}

thm rel_theory.GFP_unfold

subsection {* Theory links *}

text {* We can also describe links between theories, such a Galois connections and retractions,
  using the following notation. *}

definition mk_conn ("_ \<Leftarrow>\<langle>_,_\<rangle>\<Rightarrow> _" [90,0,0,91] 91) where
"H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2 \<equiv> \<lparr> orderA = utp_order H1, orderB = utp_order H2, lower = \<H>\<^sub>2, upper = \<H>\<^sub>1 \<rparr>"

abbreviation mk_conn' ("_ \<leftarrow>\<langle>_,_\<rangle>\<rightarrow> _" [90,0,0,91] 91) where
"T1 \<leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<rightarrow> T2 \<equiv> \<H>\<^bsub>T1\<^esub> \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> \<H>\<^bsub>T2\<^esub>"

lemma mk_conn_orderA [simp]: "\<X>\<^bsub>H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2\<^esub> = utp_order H1" 
  by (simp add:mk_conn_def)

lemma mk_conn_orderB [simp]: "\<Y>\<^bsub>H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2\<^esub> = utp_order H2" 
  by (simp add:mk_conn_def)

lemma mk_conn_lower [simp]:  "\<pi>\<^sub>*\<^bsub>H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2\<^esub> = \<H>\<^sub>1"
  by (simp add: mk_conn_def)

lemma mk_conn_upper [simp]:  "\<pi>\<^sup>*\<^bsub>H1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H2\<^esub> = \<H>\<^sub>2"
  by (simp add: mk_conn_def)

lemma galois_comp: "(H\<^sub>2 \<Leftarrow>\<langle>\<H>\<^sub>3,\<H>\<^sub>4\<rangle>\<Rightarrow> H\<^sub>3) \<circ>\<^sub>g (H\<^sub>1 \<Leftarrow>\<langle>\<H>\<^sub>1,\<H>\<^sub>2\<rangle>\<Rightarrow> H\<^sub>2) = H\<^sub>1 \<Leftarrow>\<langle>\<H>\<^sub>1\<circ>\<H>\<^sub>3,\<H>\<^sub>4\<circ>\<H>\<^sub>2\<rangle>\<Rightarrow> H\<^sub>3"
  by (simp add: comp_galcon_def mk_conn_def)

text {* Example Galois connection / retract: Existential quantification *}

lemma Idempotent_ex: "mwb_lens x \<Longrightarrow> Idempotent (ex x)"
  by (simp add: Idempotent_def exists_twice)

lemma Monotonic_ex: "mwb_lens x \<Longrightarrow> Monotonic (ex x)"
  by (simp add: Monotonic_def ex_mono)

lemma ex_closed_unrest:
  "vwb_lens x \<Longrightarrow> \<lbrakk>ex x\<rbrakk>\<^sub>H = {P. x \<sharp> P}"
  by (simp add: Healthy_def unrest_as_exists)

text {* Any theory can be composed with an existential quantification to produce a Galois connection *}

theorem ex_retract:  
  assumes "vwb_lens x" "Idempotent H" "ex x \<circ> H = H \<circ> ex x"
  shows "retract ((ex x \<circ> H) \<Leftarrow>\<langle>ex x, H\<rangle>\<Rightarrow> H)"
proof (unfold_locales, simp_all)
  show "H \<in> \<lbrakk>ex x \<circ> H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>H\<rbrakk>\<^sub>H"
    using Healthy_Idempotent assms by blast
  from assms(1) assms(3)[THEN sym] show "ex x \<in> \<lbrakk>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>ex x \<circ> H\<rbrakk>\<^sub>H"
    by (simp add: Pi_iff Healthy_def fun_eq_iff exists_twice)
  fix P Q
  assume "P is (ex x \<circ> H)" "Q is H"
  thus "(H P \<sqsubseteq> Q) = (P \<sqsubseteq> (\<exists> x \<bullet> Q))"
    by (metis (no_types, lifting) Healthy_Idempotent Healthy_if assms comp_apply dual_order.trans ex_weakens utp_pred.ex_mono vwb_lens_wb)    
next
  fix P
  assume "P is (ex x \<circ> H)"
  thus "(\<exists> x \<bullet> H P) \<sqsubseteq> P"
    by (simp add: Healthy_def)
qed
    
corollary ex_retract_id:
  assumes "vwb_lens x"
  shows "retract (ex x \<Leftarrow>\<langle>ex x, id\<rangle>\<Rightarrow> id)"
  using assms ex_retract[where H="id"] by (auto)  

end
