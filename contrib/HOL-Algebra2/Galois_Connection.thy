theory Galois_Connection
  imports Lattice
begin

section {* Galois connections *}

subsection {* Definition and basic properties *}

record ('a, 'b, 'c, 'd) galcon =
  orderA :: "('a, 'c) gorder_scheme" ("\<X>\<index>")
  orderB :: "('b, 'd) gorder_scheme" ("\<Y>\<index>")
  lower  :: "'a \<Rightarrow> 'b" ("\<pi>\<^sup>*\<index>")
  upper  :: "'b \<Rightarrow> 'a" ("\<pi>\<^sub>*\<index>")

type_synonym ('a, 'b) galois = "('a, 'b, unit, unit) galcon"

abbreviation "inv_galcon G \<equiv> \<lparr> orderA = inv_gorder \<Y>\<^bsub>G\<^esub>, orderB = inv_gorder \<X>\<^bsub>G\<^esub>, lower = upper G, upper = lower G \<rparr>"

definition comp_galcon :: "('b, 'c) galois \<Rightarrow> ('a, 'b) galois \<Rightarrow> ('a, 'c) galois" (infixr "\<circ>\<^sub>g" 85)
where "G \<circ>\<^sub>g F = \<lparr> orderA = orderA F, orderB = orderB G, lower = lower G \<circ> lower F, upper = upper F \<circ> upper G \<rparr>"

lemma funcset_pred: "(f \<in> A \<rightarrow> B) = (\<forall>x. x \<in> A \<longrightarrow> f x \<in> B)"
  by blast

locale galois_connection =
  fixes G (structure)
  assumes is_order_A: "partial_order \<X>"
  and is_order_B: "partial_order \<Y>"
  and lower_closure: "\<pi>\<^sup>* \<in> carrier \<X> \<rightarrow> carrier \<Y>"
  and upper_closure: "\<pi>\<^sub>* \<in> carrier \<Y> \<rightarrow> carrier \<X>"
  and galois_property: "\<lbrakk>\<pi>\<^sup>* x \<in> carrier \<Y>; x \<in> carrier \<X>; y \<in> carrier \<Y>; \<pi>\<^sub>* y \<in> carrier \<X>\<rbrakk> \<Longrightarrow> \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y"
begin

  lemma is_weak_order_A: "weak_partial_order \<X>"
  proof -
    interpret po: partial_order \<X>
      by (metis is_order_A)
    show ?thesis ..
  qed

  lemma is_weak_order_B: "weak_partial_order \<Y>"
  proof -
    interpret po: partial_order \<Y>
      by (metis is_order_B)
    show ?thesis ..
  qed

  lemma right: "\<lbrakk>\<pi>\<^sup>* x \<in> carrier \<Y>; x \<in> carrier \<X>; y \<in> carrier \<Y>; \<pi>\<^sub>* y \<in> carrier \<X>; \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y\<rbrakk> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y"
    by (metis galois_property)

  lemma left: "\<lbrakk>\<pi>\<^sup>* x \<in> carrier \<Y>; x \<in> carrier \<X>; y \<in> carrier \<Y>; \<pi>\<^sub>* y \<in> carrier \<X>; x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y\<rbrakk> \<Longrightarrow> \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y"
    by (metis galois_property)

  lemma deflation: "y \<in> carrier \<Y> \<Longrightarrow> \<pi>\<^sup>* (\<pi>\<^sub>* y) \<sqsubseteq>\<^bsub>\<Y>\<^esub> y"
    by (metis funcset_pred is_weak_order_A left lower_closure upper_closure weak_partial_order.le_refl)

  lemma inflation: "x \<in> carrier \<X> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* (\<pi>\<^sup>* x)"
    by (metis (no_types, lifting) PiE galois_connection.right galois_connection_axioms is_weak_order_B lower_closure upper_closure weak_partial_order.le_refl)

  lemma lower_iso: "isotone \<X> \<Y> \<pi>\<^sup>*"
    apply (auto simp add:isotone_def)
    apply (metis is_weak_order_A)
    apply (metis is_weak_order_B)
    apply (metis (no_types, hide_lams) inflation is_weak_order_A left lower_closure funcset_mem upper_closure weak_partial_order.le_trans)
  done

  lemma upper_iso: "isotone \<Y> \<X> \<pi>\<^sub>*"
    apply (auto simp add:isotone_def)
    apply (metis is_weak_order_B)
    apply (metis is_weak_order_A)
    apply (metis (no_types, hide_lams) deflation is_weak_order_B lower_closure right typed_application upper_closure weak_partial_order.le_trans)
  done

  lemma lower_comp: "x \<in> carrier \<X> \<Longrightarrow> (\<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<circ> \<pi>\<^sup>*) x = \<pi>\<^sup>* x"
  proof -
    assume a1: "x \<in> carrier \<X>"
    have f2: "\<And>x\<^sub>1. \<pi>\<^sup>* x\<^sub>1 \<in> carrier \<Y> \<or> x\<^sub>1 \<notin> carrier \<X>" by (metis lower_closure typed_application)
    hence "\<pi>\<^sub>* (\<pi>\<^sup>* x) \<in> carrier \<X>" using a1 by (metis typed_application upper_closure)
    thus "(\<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<circ> \<pi>\<^sup>*) x = \<pi>\<^sup>* x" using a1 f2 by (metis (no_types) comp_apply deflation inflation is_order_B lower_iso partial_order.le_antisym use_iso2)
  qed

  lemma upper_comp: "y \<in> carrier \<Y> \<Longrightarrow> (\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>*) y = \<pi>\<^sub>* y"
  proof -
    assume a1: "y \<in> carrier \<Y>"
    hence f2: "\<pi>\<^sub>* y \<in> carrier \<X>" by (metis ftype_pred upper_closure)
    have f3: "\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>* \<in> carrier \<Y> \<rightarrow> carrier \<X>" by (metis (no_types) lower_closure typed_composition upper_closure)
    have f4: "\<pi>\<^sup>* (\<pi>\<^sub>* y) \<sqsubseteq>\<^bsub>\<Y>\<^esub> y" using a1 deflation by blast
    have f5: "\<pi>\<^sub>* (\<pi>\<^sup>* (\<pi>\<^sub>* y)) \<in> carrier \<X>" using a1 f3 by (simp add: ftype_pred)
    have "\<pi>\<^sup>* (\<pi>\<^sub>* y) \<in> carrier \<Y>" using f2 by (metis (no_types) ftype_pred lower_closure)
    hence "\<pi>\<^sub>* (\<pi>\<^sup>* (\<pi>\<^sub>* y)) = \<pi>\<^sub>* y" using a1 f2 f4 f5 by (metis inflation is_order_A partial_order.le_antisym upper_iso use_iso2)
    thus "(\<pi>\<^sub>* \<circ> \<pi>\<^sup>* \<circ> \<pi>\<^sub>*) y = \<pi>\<^sub>* y" by simp
  qed

  lemma adjoint_idem1: "idempotent (carrier \<Y>) (\<pi>\<^sup>* \<circ> \<pi>\<^sub>*)"
    by (metis (no_types, hide_lams) comp_apply idempotent_def upper_comp)

  lemma adjoint_idem2: "idempotent (carrier \<X>) (\<pi>\<^sub>* \<circ> \<pi>\<^sup>*)"
    by (metis (mono_tags, hide_lams) comp_apply idempotent_def lower_comp)

  lemma fg_iso: "isotone \<Y> \<Y> (\<pi>\<^sup>* \<circ> \<pi>\<^sub>*)"
    by (metis iso_compose lower_closure lower_iso upper_closure upper_iso)

  lemma gf_iso: "isotone \<X> \<X> (\<pi>\<^sub>* \<circ> \<pi>\<^sup>*)"
    by (metis iso_compose lower_closure lower_iso upper_closure upper_iso)

  lemma semi_inverse1: "x \<in> carrier \<X> \<Longrightarrow> \<pi>\<^sup>* x = \<pi>\<^sup>* (\<pi>\<^sub>* (\<pi>\<^sup>* x))"
    by (metis lower_comp o_eq_dest_lhs)

  lemma semi_inverse2: "x \<in> carrier \<Y> \<Longrightarrow> \<pi>\<^sub>* x = \<pi>\<^sub>* (\<pi>\<^sup>* (\<pi>\<^sub>* x))"
    by (metis o_eq_dest_lhs upper_comp)

end

lemma dual_galois [simp]: " galois_connection \<lparr> orderA = inv_gorder B, orderB = inv_gorder A, lower = f, upper = g \<rparr> 
                          = galois_connection \<lparr> orderA = A, orderB = B, lower = g, upper = f \<rparr>"
  by (auto simp add: galois_connection_def dual_order_iff)

definition lower_adjoint :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "lower_adjoint A B f \<equiv> \<exists>g. galois_connection \<lparr> orderA = A, orderB = B, lower = f, upper = g \<rparr>"

definition upper_adjoint :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "upper_adjoint A B g \<equiv> \<exists>f. galois_connection \<lparr> orderA = A, orderB = B, lower = f, upper = g \<rparr>"

lemma lower_adjoint_dual [simp]: "lower_adjoint (inv_gorder A) (inv_gorder B) f = upper_adjoint B A f"
  by (simp add: lower_adjoint_def upper_adjoint_def)

lemma upper_adjoint_dual [simp]: "upper_adjoint (inv_gorder A) (inv_gorder B) f = lower_adjoint B A f"
  by (simp add: lower_adjoint_def upper_adjoint_def)

lemma lower_type: "lower_adjoint A B f \<Longrightarrow> f \<in> carrier A \<rightarrow> carrier B"
  by (auto dest: galois_connection.lower_closure simp add:lower_adjoint_def)

lemma upper_type: "upper_adjoint A B g \<Longrightarrow> g \<in> carrier B \<rightarrow> carrier A"
  by (auto dest: galois_connection.upper_closure simp add:upper_adjoint_def)

lemma id_galois: "partial_order A \<Longrightarrow> galois_connection \<lparr> orderA = A, orderB = A, lower = id, upper = id \<rparr>"
  by (unfold galois_connection_def, simp add:id_type)

lemma galois_connectionI:
  assumes
    "partial_order A" "partial_order B"
    "L \<in> carrier A \<rightarrow> carrier B" "R \<in> carrier B \<rightarrow> carrier A"
    "isotone A B L" "isotone B A R" 
    " \<lbrakk>L x \<in> carrier B; R x \<in> carrier A; y \<in> carrier B; R y \<in> carrier B\<rbrakk> \<Longrightarrow> \<pi>\<^sup>* x \<sqsubseteq>\<^bsub>\<Y>\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* y"
    "\<forall> X \<in> carrier(B). L(R(X)) \<sqsubseteq>\<^bsub>B\<^esub> X"
    "\<forall> X \<in> carrier(A). X \<sqsubseteq>\<^bsub>A\<^esub> R(L(X))"
  shows "galois_connection \<lparr> orderA = A, orderB = B, lower = L, upper = R \<rparr>"


lemma galois_comp_closed:
  "\<lbrakk> galois_connection G; galois_connection F \<rbrakk> \<Longrightarrow> galois_connection (G \<circ>\<^sub>g F)"
  apply (unfold galois_connection_def)

lemma galois_connectionI':
  assumes
    "partial_order A" "partial_order B"
    "L \<in> carrier A \<rightarrow> carrier B" "R \<in> carrier B \<rightarrow> carrier A"
    "isotone A B L" "isotone B A R" 
    "\<forall> X \<in> carrier(B). L(R(X)) \<sqsubseteq>\<^bsub>B\<^esub> X"
    "\<forall> X \<in> carrier(A). X \<sqsubseteq>\<^bsub>A\<^esub> R(L(X))"
  shows "galois_connection \<lparr> orderA = A, orderB = B, lower = L, upper = R \<rparr>"
  using assms
  by (unfold galois_connection_def,auto, (meson isotone_def typed_application weak_partial_order.le_trans)+)

end
