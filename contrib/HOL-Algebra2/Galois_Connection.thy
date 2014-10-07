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
    by (metis ftype_pred is_weak_order_A left lower_closure upper_closure weak_partial_order.le_refl)

  lemma inflation: "x \<in> carrier \<X> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<X>\<^esub> \<pi>\<^sub>* (\<pi>\<^sup>* x)"
    by (metis (lifting, no_types) ftype_pred is_weak_order_B lower_closure right upper_closure weak_partial_order.le_refl)
   
  lemma lower_iso: "isotone \<X> \<Y> \<pi>\<^sup>*"
    apply (auto simp add:isotone_def)
    apply (metis is_weak_order_A)
    apply (metis is_weak_order_B)
    apply (metis (no_types, hide_lams) inflation is_weak_order_A left lower_closure typed_application upper_closure weak_partial_order.le_trans)
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

(*
lemma galois_ump1: "galois_connection A B f g = (f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A
                                                \<and> isotone A B f \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y)
                                                \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y))"
proof
  assume "galois_connection A B f g"
  thus "f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A \<and> isotone A B f
        \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y)"
    by (smt typed_application galois_connection.deflation galois_connection.galois_property galois_connection.lower_closure galois_connection.lower_iso galois_connection.upper_closure)
next
  assume "f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A \<and> isotone A B f
          \<and> (\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y) \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> g y)"
  thus "galois_connection A B f g"
    by (unfold galois_connection_def, safe, (smt typed_application isotone_def order.order_trans)+)
qed

lemma galois_ump2: "galois_connection A B f g = (f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A
                                                \<and> isotone B A g \<and> (\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x))
                                                \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. x \<sqsubseteq>\<^bsub>A\<^esub> g y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y))"
proof -
  have dual: "galois_connection (B\<sharp>) (A\<sharp>) g f = (g \<in> carrier (B\<sharp>) \<rightarrow> carrier (A\<sharp>) \<and> f \<in> carrier (A\<sharp>) \<rightarrow> carrier (B\<sharp>)
                                                \<and> isotone (B\<sharp>) (A\<sharp>) g \<and> (\<forall>y\<in>carrier (A\<sharp>). g (f y) \<sqsubseteq>\<^bsub>(A\<sharp>)\<^esub> y)
                                                \<and> (\<forall>x\<in>carrier (B\<sharp>). \<forall>y\<in>carrier (A\<sharp>). g x \<sqsubseteq>\<^bsub>(A\<sharp>)\<^esub> y \<longrightarrow> x \<sqsubseteq>\<^bsub>(B\<sharp>)\<^esub> f y))"
    by (metis (no_types) galois_ump1)
  thus ?thesis by (simp, auto)
qed

(* +------------------------------------------------------------------------+
   | Theorem 4.10(a)                                                        |
   +------------------------------------------------------------------------+ *)

lemma ore_galois:
  assumes fclosed: "f \<in> carrier A \<rightarrow> carrier B" and gclosed: "g \<in> carrier B \<rightarrow> carrier A"
  and a: "\<forall>x\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> g (f x)" and b: "\<forall>y\<in>carrier B. f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y"
  and c: "isotone A B f" and d: "isotone B A g"
  shows "galois_connection A B f g"
  by (unfold galois_connection_def, safe, (smt typed_application a b c d gclosed fclosed isotone_def order.order_trans)+)

(* +------------------------------------------------------------------------+
   | Theorems 4.20(a) and 4.20(b)                                           |
   +------------------------------------------------------------------------+ *)

(*
lemma perfect1: "\<lbrakk>galois_connection A B f g; x \<in> carrier A\<rbrakk> \<Longrightarrow> g (f x) = x \<longleftrightarrow> x \<in> range g"
  sledgehammer [timeout = 300]
  by (smt ftype_pred galois_connection.upper_closure image_iff range_eqI semi_inverse2)

lemma perfect2: "\<lbrakk>galois_connection A B f g; x \<in> carrier B\<rbrakk> \<Longrightarrow> f (g x) = x \<longleftrightarrow> x \<in> range f"
  by (metis galois_dual inv_carrier_id perfect1)
*)

(* +------------------------------------------------------------------------+
   | Theorems 4.20(a) and 4.20(b)                                           |
   +------------------------------------------------------------------------+ *)

lemma galois_max:
  assumes conn: "galois_connection A B f g" and yc: "y \<in> carrier B"
  shows "order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
proof -
  have "order A" by (metis conn galois_connection.is_order_A)
  thus ?thesis
    apply (simp add: order.is_max_def order.is_lub_def order.is_ub_def)
    apply safe
    apply (metis conn galois_connection.deflation yc)
    apply (metis conn ftype_pred galois_ump1 yc)
    by (metis conn galois_ump1 yc)
qed

lemma galois_min:
  assumes conn: "galois_connection A B f g" and xc: "x \<in> carrier A"
  shows "order.is_min B (f x) {y. x \<sqsubseteq>\<^bsub>A \<^esub>g y \<and> y \<in> carrier B}"
proof -
  have dual: "\<And>z. \<lbrakk>galois_connection (B\<sharp>) (A\<sharp>) g f; z \<in> carrier (A\<sharp>)\<rbrakk>
              \<Longrightarrow> order.is_max (B\<sharp>) (f z) {y. g y \<sqsubseteq>\<^bsub>(A\<sharp>)\<^esub> z \<and> y \<in> carrier (B\<sharp>)}"
    by (rule galois_max, auto)
  moreover have "order B" by (metis conn galois_connection.is_order_B)
  ultimately show ?thesis
    by (smt Collect_cong conn dual_is_max galois_dual inv_carrier_id inv_flip xc)
qed

theorem max_galois: "galois_connection A B f g = (isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<in> carrier B \<rightarrow> carrier A \<and> f \<in> carrier A \<rightarrow> carrier B)"
proof
  assume conn: "galois_connection A B f g"
  have "isotone A B f" by (metis conn galois_connection.lower_iso)
  moreover have "\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
    using galois_max conn by fast
  ultimately show "isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<in> carrier B \<rightarrow> carrier A \<and> f \<in> carrier A \<rightarrow> carrier B"
    by (metis (lifting) conn galois_connection.lower_closure galois_connection.upper_closure)
next
  assume "isotone A B f \<and> (\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<and> g \<in> carrier B \<rightarrow> carrier A \<and> f \<in> carrier A \<rightarrow> carrier B"
  hence f_iso: "isotone A B f"
    and max: "\<forall>y\<in>carrier B. order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
    and g_closed: "g \<in> carrier B \<rightarrow> carrier A"
    and f_closed: "f \<in> carrier A \<rightarrow> carrier B"
    by fast+
  show "galois_connection A B f g"
  proof (simp add: galois_ump1, safe, (smt g_closed f_closed)+)
    show "isotone A B f" by (metis f_iso)
  next
    fix y assume yc: "y \<in> carrier B"
    have "order A" and "order B" by (metis f_iso isotone_def)+
    hence "g y \<in> {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
      using max yc by (simp add: order.is_max_def)
    thus "f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y" by (metis mem_Collect_eq)
  next
    fix x y assume xc: "x \<in> carrier A" and yc: "y \<in> carrier B" and lower: "f x \<sqsubseteq>\<^bsub>B\<^esub> y"
    have oa: "order A" and ob: "order B" by (metis f_iso isotone_def)+
    hence lub1: "order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
      using max yc by (metis (mono_tags) Collect_mem_eq Collect_mono order.is_max_equiv)
    thus "x \<sqsubseteq>\<^bsub>A\<^esub> g y" using oa by (simp add: order.is_lub_def order.is_ub_def, metis lower xc)
  qed
qed

(* +------------------------------------------------------------------------+
   | Lemma 4.24(a) and 4.24(b)                                              |
   +------------------------------------------------------------------------+ *)

lemma set_image_type: "\<lbrakk>X \<subseteq> A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> f ` X \<subseteq> B"
  by (metis typed_application image_subsetI set_rev_mp)

lemma lower_ub:
  assumes Xc: "X \<subseteq> carrier A" and xc: "x \<in> carrier A"
  and lub: "order.is_lub A x X" and lower: "lower_adjoint A B f"
  shows "order.is_ub B (f x) (f ` X)"
proof -
  have fxc: "f x \<in> carrier B"
    by (metis lower lower_type typed_application xc)

  have fXc: "f ` X \<subseteq> carrier B"
    by (metis Xc lower lower_type set_image_type)

  have ord_B: "order B" and ord_A: "order A"
    by (metis galois_connection.is_order_B galois_connection.is_order_A lower lower_adjoint_def)+

  hence "\<forall>y\<in>X. y \<sqsubseteq>\<^bsub>A\<^esub> x" using lub
    by (simp add: order.is_lub_simp)

  hence "\<forall>y\<in>X. f y \<sqsubseteq>\<^bsub>B\<^esub> f x"
    apply (clarify, rule_tac ?A = A in use_iso2, simp_all add: xc)
    by (metis galois_connection.lower_iso lower lower_adjoint_def, metis Xc set_mp)

  thus ?thesis using ord_A ord_B
    by (simp add: order.is_ub_def, intro conjI, simp_all add: fxc fXc)
qed

lemma lower_lub:
  assumes Xc: "X\<subseteq>carrier A" and xc: "x \<in> carrier A"
  and il: "order.is_lub A x X" and la: "lower_adjoint A B f"
  shows "order.is_lub B (f x) (f ` X)"
proof -
  have ord_B: "order B" and ord_A: "order A"
    by (metis galois_connection.is_order_B galois_connection.is_order_A la lower_adjoint_def)+
  thus ?thesis apply (simp add: order.is_lub_def)
  proof
    show "order.is_ub B (f x) (f ` X)"
      by (metis Xc il la lower_ub xc)

    obtain g where gc: "galois_connection A B f g"
      by (metis la lower_adjoint_def)

    thus "\<forall>y\<in>carrier B. (\<forall>z\<in>X. f z \<sqsubseteq>\<^bsub>B\<^esub> y) \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y"
      by (smt typed_application Xc galois_ump1 gc galois_connection_def set_rev_mp xc il ord_A order.is_lub_def)
  qed
qed

lemma upper_glb:
  assumes Xc: "X\<subseteq>carrier B" and xc: "x \<in> carrier B"
  and il: "order.is_glb B x X" and la: "upper_adjoint A B g"
  shows "order.is_glb A (g x) (g ` X)"
proof -
  have ord_Bsh: "order (B\<sharp>)"
    by (metis galois_connection.is_order_B la ord_is_inv upper_adjoint_def)

  have ord_Ash: "order (A\<sharp>)"
    by (metis galois_connection.is_order_A la ord_is_inv upper_adjoint_def)

  have "order.is_lub (A\<sharp>) (g x) (g ` X)"
    apply (rule_tac ?A = "B\<sharp>" in lower_lub, simp_all add: Xc xc)
    using ord_Bsh ord_Ash by (simp_all add: il la)

  thus ?thesis using ord_Ash by simp
qed

lemma lower_preserves_ex_joins:
  assumes lower: "lower_adjoint A B f" shows "ex_join_preserving A B f"
proof (simp add: ex_join_preserving_def, safe)
  show "order A" and "order B"
    by (metis assms galois_connection.is_order_A galois_connection.is_order_B lower_adjoint_def)+
next
  fix X x assume Xc: "X \<subseteq> carrier A" and xc: "x \<in> carrier A" and il: "order.is_lub A x X"
  have "order B"
    by (metis assms galois_connection.is_order_B lower_adjoint_def)
  thus "order.lub B (f ` X) = f (order.lub A X)"
    by (metis order.lub_is_lub Xc assms galois_connection.is_order_A il lower_adjoint_def lower_lub xc)
qed

lemma upper_preserves_ex_meets:
  assumes upper: "upper_adjoint A B g" shows "ex_meet_preserving B A g"
proof -
  have "ex_join_preserving (B\<sharp>) (A\<sharp>) g"
    by (rule lower_preserves_ex_joins, simp add: upper)

  thus ?thesis by simp
qed

(* +------------------------------------------------------------------------+
   | Galois Connections for Complete Lattices                               |
   +------------------------------------------------------------------------+ *)

locale complete_lattice_connection = galois_connection +
  assumes is_cl_A: "complete_lattice \<X>"
  and is_cl_B: "complete_lattice \<Y>"

definition cl_lower_adjoint :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "cl_lower_adjoint A B f \<equiv> \<exists>g. complete_lattice_connection A B f g"

definition cl_upper_adjoint :: "('a, 'c) ord_scheme \<Rightarrow> ('b, 'd) ord_scheme \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "cl_upper_adjoint A B g \<equiv> \<exists>f. complete_lattice_connection A B f g"

lemma cl_conn_dual [simp]: "complete_lattice_connection (B\<sharp>) (A\<sharp>) g f = complete_lattice_connection A B f g"
  by (simp add: complete_lattice_connection_def complete_lattice_connection_axioms_def, auto)

lemma cl_lower_dual [simp]: "cl_lower_adjoint (B\<sharp>) (A\<sharp>) f = cl_upper_adjoint A B f"
  by (simp add: cl_lower_adjoint_def cl_upper_adjoint_def)

lemma cl_upper_dual [simp]: "cl_upper_adjoint (B\<sharp>) (A\<sharp>) f = cl_lower_adjoint A B f"
  by (simp add: cl_lower_adjoint_def cl_upper_adjoint_def)

lemma cl_to_galois: "complete_lattice_connection A B f g \<Longrightarrow> galois_connection A B f g"
  by (simp add: complete_lattice_connection_def)

lemma cl_is_order: "complete_lattice A \<Longrightarrow> order A"
  by (simp add: complete_lattice_def complete_join_semilattice_def)

lemma z: "\<exists>z\<in>A. P(z) \<Longrightarrow> \<exists>z. P(z)" by auto

lemma suprema_galois_left:
  assumes cl_A: "complete_lattice A" and cl_B: "complete_lattice B"
  and ft: "f \<in> carrier A \<rightarrow> carrier B" and gt: "g \<in> carrier B \<rightarrow> carrier A"
  and ejp: "ex_join_preserving A B f"
  and lub_prop: "\<forall>y\<in>carrier B. order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
  shows "complete_lattice_connection A B f g"
proof -
  have oa: "order A" and ob: "order B"
    by (metis cl_A cl_B cl_to_order)+

  have left: "\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. (f x \<sqsubseteq>\<^bsub>B\<^esub> y) \<longrightarrow> (x \<sqsubseteq>\<^bsub>A\<^esub> g y)"
  proof safe
    fix x y assume xc: "x \<in> carrier A" and yc: "y \<in> carrier B" and a: "f x \<sqsubseteq>\<^bsub>B\<^esub> y"
    hence "order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
      by (metis (full_types) lub_prop)
    thus "x \<sqsubseteq>\<^bsub>A\<^esub> g y" using oa
      apply (simp add: order.is_lub_def order.is_ub_def)
      by (metis a xc)
  qed

  have right: "\<forall>x\<in>carrier A. \<forall>y\<in>carrier B. (x \<sqsubseteq>\<^bsub>A\<^esub> g y) \<longrightarrow> (f x \<sqsubseteq>\<^bsub>B\<^esub> y)"
  proof safe
    fix x y assume xc: "x \<in> carrier A" and yc: "y \<in> carrier B" and a: "x \<sqsubseteq>\<^bsub>A\<^esub> g y"

    have lem: "\<Sigma>\<^bsub>B\<^esub>(f ` {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}) \<sqsubseteq>\<^bsub>B\<^esub> y"
      apply (rule order.the_lub_leq)
      apply (metis cl_B cl_to_order)
      apply (rule_tac ?A = "carrier B" in z)
      apply (rule complete_join_semilattice.lub_ex)
      apply (metis cl_B cl_to_cjs)
      apply (rule_tac ?A = "carrier A" in set_image_type)
      apply (metis (no_types) lub_prop order.is_lub_simp cl_A cl_to_order yc)
      apply (metis ft)
      using ob apply (simp add: order.is_lub_simp)
      apply safe
      by (metis yc)

    have "f x \<sqsubseteq>\<^bsub>B\<^esub> y \<Longrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> \<Sigma>\<^bsub>A\<^esub>{z. f z \<sqsubseteq>\<^bsub>B\<^esub> y \<and> z \<in> carrier A}"
      by (metis (full_types) a lub_prop oa order.lub_is_lub yc)
    moreover have "x \<sqsubseteq>\<^bsub>A\<^esub> \<Sigma>\<^bsub>A\<^esub>{z. f z \<sqsubseteq>\<^bsub>B\<^esub> y \<and> z \<in> carrier A} \<Longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f (\<Sigma>\<^bsub>A\<^esub>{z. f z \<sqsubseteq>\<^bsub>B\<^esub> y \<and> z \<in> carrier A})"
      apply (rule_tac f = f and A = A in use_iso2)
      apply (rule ex_join_preserving_is_iso)
      apply (metis ft)
      apply (metis cl_A cl_to_js)
      apply (metis cl_B cl_to_js)
      apply (metis ejp)
      apply (metis xc)
      apply (metis (lifting) ftype_pred gt lub_prop oa order.lub_is_lub yc)
      by (metis)
    moreover have "(f x \<sqsubseteq>\<^bsub>B\<^esub> f (\<Sigma>\<^bsub>A\<^esub>{z. f z \<sqsubseteq>\<^bsub>B\<^esub> y \<and> z \<in> carrier A})) = (f x \<sqsubseteq>\<^bsub>B\<^esub> \<Sigma>\<^bsub>B\<^esub>(f ` {z. f z \<sqsubseteq>\<^bsub>B\<^esub> y \<and> z \<in> carrier A}))"
      by (smt Collect_cong ejp ex_join_preserving_def lub_prop order.is_lub_simp yc)
    moreover have "... \<Longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> y" using lem (* Should just be trans !?! *)
      by (smt Collect_cong ejp ex_join_preserving_def ft ftype_pred lub_prop order.is_lub_simp order.lub_is_lub order.order_trans xc yc)
    ultimately show "f x \<sqsubseteq>\<^bsub>B\<^esub> y"
      by (metis (full_types) a lub_prop oa order.lub_is_lub yc)
  qed

  have "galois_connection A B f g" unfolding galois_connection_def
    apply safe
    apply (metis oa)
    apply (metis cl_B cl_to_order)
    apply (metis ft)
    apply (metis gt)
    apply (metis left)
    by (metis right)
  thus ?thesis unfolding complete_lattice_connection_def complete_lattice_connection_axioms_def
    by (metis cl_A cl_B)
qed

(*
lemma suprema_galois_right:
  assumes conn: "complete_lattice_connection A B f g"
  shows "complete_lattice A" and "complete_lattice B"
  and "f \<in> carrier A \<rightarrow> carrier B" and "g \<in> carrier B \<rightarrow> carrier A"
  and "ex_join_preserving A B f"
  and "\<forall>y\<in>carrier B. order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
  apply safe
  apply (metis assms complete_lattice_connection.is_cl_A)
  apply (metis assms complete_lattice_connection.is_cl_B)
  apply (metis assms cl_to_galois galois_connection.lower_closure)
  apply (metis assms cl_to_galois galois_connection.upper_closure)
  
  apply (metis assms cl_to_galois lower_adjoint_def lower_preserves_ex_joins)
proof -
  fix y assume yc: "y \<in> carrier B"
  have ord_A: "order A"
    by (metis assms cl_to_order complete_lattice_connection.is_cl_A)
  have "galois_connection A B f g"
    by (metis (lifting) assms cl_to_galois)
  hence "order.is_max A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}"
    by (smt Collect_cong galois_max yc)
  thus "order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub>y \<and> x \<in> carrier A}"
    using ord_A by (simp add: order.is_max_def)
qed

lemma suprema_galois:
  "complete_lattice_connection A B f g = (complete_lattice A \<and> complete_lattice B
                                         \<and> f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A
                                         \<and> ex_join_preserving A B f
                                         \<and> (\<forall>y\<in>carrier B. order.is_lub A (g y) {x. f x \<sqsubseteq>\<^bsub>B\<^esub> y \<and> x \<in> carrier A}))"
  by (smt Collect_cong suprema_galois_left suprema_galois_right(1) suprema_galois_right(2) suprema_galois_right(3) suprema_galois_right(4) suprema_galois_right(5) suprema_galois_right(6))
*)

lemma infima_galois_left:
  assumes cl_A: "complete_lattice A" and cl_B: "complete_lattice B"
  and ft: "f \<in> carrier A \<rightarrow> carrier B" and gt: "g \<in> carrier B \<rightarrow> carrier A"
  and emp: "ex_meet_preserving B A g"
  and lub_prop: "\<forall>y\<in>carrier A. order.is_glb B (f y) {x. y \<sqsubseteq>\<^bsub>A \<^esub>g x \<and> x \<in> carrier B}"
  shows "complete_lattice_connection A B f g"
proof -
  have "complete_lattice_connection (B\<sharp>) (A\<sharp>) g f"
  proof (rule suprema_galois_left, simp_all)
    show "complete_lattice B" by (metis cl_B)
    show "complete_lattice A" by (metis cl_A)
    show "g \<in> carrier B \<rightarrow> carrier A" by (metis gt)
    show "f \<in> carrier A \<rightarrow> carrier B" by (metis ft)
    show "ex_meet_preserving B A g" by (metis emp)
    show "\<forall>y\<in>carrier A. order.is_lub (B\<sharp>) (f y) {x. y \<sqsubseteq>\<^bsub>A \<^esub>g x \<and> x \<in> carrier B}"
      by (metis (lifting) dual_is_lub lub_prop cl_B cl_to_order)
  qed

  thus ?thesis by simp
qed

(*
lemma infima_galois_right:
  assumes conn: "complete_lattice_connection A B f g"
  shows"\<forall>y\<in>carrier A. order.is_glb B (f y) {x. y \<sqsubseteq>\<^bsub>A \<^esub>g x \<and> x \<in> carrier B}"
  sorry
  (* by (smt Collect_cong assms cl_conn_dual cl_to_galois dual_is_lub galois_connection.is_order_B inv_carrier_id inv_flip suprema_galois_right(6)) *)

(*
lemma infima_galois:
  "complete_lattice_connection A B f g = (complete_lattice A \<and> complete_lattice B
                                         \<and> f \<in> carrier A \<rightarrow> carrier B \<and> g \<in> carrier B \<rightarrow> carrier A
                                         \<and> ex_meet_preserving B A g
                                         \<and> (\<forall>y\<in>carrier A. order.is_glb B (f y) {x. y \<sqsubseteq>\<^bsub>A \<^esub>g x \<and> x \<in> carrier B}))"
  apply default
  apply safe
  apply (metis complete_lattice_connection.is_cl_A)
  apply (metis complete_lattice_connection.is_cl_B)
  apply (metis cl_to_galois galois_ump2)
  apply (metis cl_to_galois galois_ump2)
  apply (metis cl_conn_dual dual_ex_join_preserving suprema_galois_right(5))
  apply (simp add: infima_galois_right)
  by (simp add: infima_galois_left)
*)
*)

lemma cl_lower_join_preserving:
  assumes lower: "cl_lower_adjoint A B f" shows "join_preserving A B f"
proof -
  have "lower_adjoint A B f"
    by (metis assms cl_lower_adjoint_def cl_to_galois lower_adjoint_def)
  hence ejp: "ex_join_preserving A B f"
    by (metis lower_preserves_ex_joins)
  have "complete_lattice A"
    by (metis assms cl_lower_adjoint_def complete_lattice_connection.is_cl_A)
  hence "\<forall>X\<subseteq>carrier A. \<exists>x\<in>carrier A. order.is_lub A x X"
    by (simp add: complete_lattice_def complete_join_semilattice_def complete_join_semilattice_axioms_def)
  hence "\<forall>X\<subseteq>carrier A. order.lub B (f ` X) = f (order.lub A X)"
    by (metis ex_join_preserving_def ejp)
  thus ?thesis
    by (metis ejp ex_join_preserving_def join_preserving_def)
qed

lemma cl_upper_meet_preserving: "cl_upper_adjoint A B g \<Longrightarrow> meet_preserving B A g"
  by (metis cl_lower_dual cl_lower_join_preserving dual_join_preserving)

(* +------------------------------------------------------------------------+
   | Fixpoints and Galois connections                                       |
   +------------------------------------------------------------------------+ *)

lemma truncate_simp [simp]: "ord.truncate A = A"
  by (simp add: ord.truncate_def)

lemma least_fixpoint_closed:
  assumes cl: "complete_lattice A"
  and f_type: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "\<mu>\<^bsub>A\<^esub>f \<in> carrier A"
proof -
  have "\<exists>!x. is_lfp A x f" using cl f_type f_iso by (rule knaster_tarski)
  thus ?thesis by (metis least_fixpoint_set)
qed

lemma greatest_fixpoint_closed:
  assumes cl: "complete_lattice A"
  and f_type: "f \<in> carrier A \<rightarrow> carrier A"
  and f_iso: "isotone A A f"
  shows "\<mu>\<^bsub>A\<^esub>f \<in> carrier A"
  by (metis cl f_iso f_type least_fixpoint_closed)

lemma fixpoint_rolling: assumes conn: "complete_lattice_connection A B f g"
  shows "f (\<mu>\<^bsub>A\<^esub> (g \<circ> f)) = \<mu>\<^bsub>B\<^esub> (f \<circ> g)"
proof (rule lfp_equality_var)
  show "order B"
    by (metis assms cl_to_order complete_lattice_connection.is_cl_B)

  have cl_A: "complete_lattice A"
    by (metis assms complete_lattice_connection.is_cl_A)

  have cl_B: "complete_lattice B"
    by (metis assms complete_lattice_connection.is_cl_B)

  show closure1: "f \<circ> g \<in> carrier B \<rightarrow> carrier B"
    by (metis assms cl_to_galois typed_composition galois_connection.lower_closure galois_connection.upper_closure)

  have closure2: "g \<circ> f \<in> carrier A \<rightarrow> carrier A"
    by (metis assms cl_to_galois typed_composition galois_connection.lower_closure galois_connection.upper_closure)

  have closure3: "\<mu>\<^bsub>A \<^esub>(g \<circ> f) \<in> carrier A" using cl_A closure2
    by (rule least_fixpoint_closed, metis assms cl_to_galois gf_iso)

  thus closure4: "(f (\<mu>\<^bsub>A \<^esub>(g \<circ> f))) \<in> carrier B"
    by (metis assms cl_to_galois typed_application galois_connection.lower_closure)

  have "f (g (f (\<mu>\<^bsub>A\<^esub>(g \<circ> f)))) = f (\<mu>\<^bsub>A\<^esub>(g \<circ> f))"
    by (rule_tac f = f and A = A and B = B in semi_inverse1[symmetric], metis closure3, metis conn cl_to_galois)

  thus "(f \<circ> g) (f (\<mu>\<^bsub>A\<^esub>(g \<circ> f))) = f (\<mu>\<^bsub>A\<^esub>(g \<circ> f))"
    by (metis o_def)

  show "\<forall>y\<in>carrier B. (f \<circ> g) y = y \<longrightarrow> f (\<mu>\<^bsub>A\<^esub>(g \<circ> f)) \<sqsubseteq>\<^bsub>B\<^esub> y"
  proof safe
    fix y assume yc: "y \<in> carrier B" and fgy: "(f \<circ> g) y = y"
    have "complete_lattice A" by (metis cl_A)
    hence "\<mu>\<^bsub>A\<^esub>(g \<circ> f) \<sqsubseteq>\<^bsub>A\<^esub> g y"
      apply (rule fixpoint_induction)
      apply (metis closure2)
      apply (metis assms cl_to_galois typed_application upper_adjoint_def upper_type yc)
      apply (metis assms cl_to_galois gf_iso)
      by (metis assms cl_A cl_to_galois cl_to_order typed_application fgy galois_ump1 o_def order.eq_refl yc)
    thus "f (\<mu>\<^bsub>A\<^esub>(g \<circ> f)) \<sqsubseteq>\<^bsub>B\<^esub> y"
      by (metis assms cl_to_galois closure3 galois_ump2 yc)
  qed
qed

lemma greatest_fixpoint_rolling: assumes conn: "complete_lattice_connection A B f g"
  shows "g (\<nu>\<^bsub>B\<^esub> (f \<circ> g)) = \<nu>\<^bsub>A\<^esub> (g \<circ> f)"
proof -
  have "complete_lattice_connection (B\<sharp>) (A\<sharp>) g f \<Longrightarrow> g (\<mu>\<^bsub>(B\<sharp>)\<^esub>(f \<circ> g)) = \<mu>\<^bsub>(A\<sharp>)\<^esub>(g \<circ> f)"
    by (rule fixpoint_rolling, auto)
  thus ?thesis by (simp, metis conn)
qed

(* +------------------------------------------------------------------------+ *)
subsection {* Fixpoint fusion *}
(* +------------------------------------------------------------------------+ *)

theorem fixpoint_fusion [simp]:
  assumes upper_ex: "cl_lower_adjoint A B f"
  and ft: "f \<in> carrier A \<rightarrow> carrier B" and ht: "h \<in> carrier A \<rightarrow> carrier A" and kt: "k \<in> carrier B \<rightarrow> carrier B"
  and hiso: "isotone A A h" and kiso: "isotone B B k"
  and comm: "f\<circ>h = k\<circ>f"
  shows "f (\<mu>\<^bsub>A\<^esub> h) = \<mu>\<^bsub>B\<^esub> k"
proof (rule lfp_equality_var)
  obtain g where conn: "complete_lattice_connection A B f g"
    by (metis cl_lower_adjoint_def upper_ex)

  show "order B" by (metis isotone_def kiso)

  have cl_A: "complete_lattice A"
    by (metis cl_lower_adjoint_def complete_lattice_connection.is_cl_A upper_ex)

  have cl_B: "complete_lattice B"
    by (metis cl_lower_adjoint_def complete_lattice_connection.is_cl_B upper_ex)

  show "k \<in> carrier B \<rightarrow> carrier B" by (metis kt)

  have closure1: "\<mu>\<^bsub>A\<^esub>h \<in> carrier A" using cl_A ht hiso
    by (rule least_fixpoint_closed)

  thus closure2: "f (\<mu>\<^bsub>A\<^esub>h) \<in> carrier B"
    by (metis typed_application ft)

  have comm_var: "\<And>x. k (f x) = f (h x)"
    by (metis comm o_apply)

  show "k (f (\<mu>\<^bsub>A\<^esub>h)) = f (\<mu>\<^bsub>A\<^esub>h)"
    by (metis cl_A comm_var fixpoint_computation hiso ht)

  show "\<forall>y\<in>carrier B. k y = y \<longrightarrow> f (\<mu>\<^bsub>A\<^esub>h) \<sqsubseteq>\<^bsub>B\<^esub> y"
  proof clarify
    fix y assume yc: "y \<in> carrier B" and ky: "k y = y"

    have gy: "g y \<in> carrier A"
      by (metis cl_to_galois typed_application conn galois_ump2 yc)
    hence hgy: "h (g y) \<in> carrier A"
      by (metis typed_application ht)
    hence fhgy: "f (h (g y)) \<in> carrier B"
      by (metis typed_application ft)

    have "\<mu>\<^bsub>A\<^esub> h \<sqsubseteq>\<^bsub>A\<^esub> g y" using cl_A ht gy hiso
    proof (rule fixpoint_induction)
      have "f (g y) \<sqsubseteq>\<^bsub>B\<^esub> y"
        by (metis cl_to_galois conn galois_connection.deflation yc)
      hence "k (f (g y)) \<sqsubseteq>\<^bsub>B\<^esub> k y"
        by (metis typed_application ft gy kiso use_iso1 yc)
      hence "f (h (g y)) \<sqsubseteq>\<^bsub>B\<^esub> y"
        by (simp only: comm_var[symmetric] ky)
      thus "h (g y) \<sqsubseteq>\<^bsub>A\<^esub> g y" using gy hgy fhgy yc
        by (rule_tac lower = f and orderB = B in galois_connection.right, metis cl_to_galois conn, auto+)
    qed
    thus "f (\<mu>\<^bsub>A\<^esub> h) \<sqsubseteq>\<^bsub>B\<^esub> y"
      by (metis closure1 closure2 cl_to_galois conn galois_connection.left gy yc)
  qed
qed

theorem greatest_fixpoint_fusion [simp]:
  assumes lower_ex: "cl_upper_adjoint A B g"
  and ft: "f \<in> carrier A \<rightarrow> carrier B" and ht: "h \<in> carrier B \<rightarrow> carrier B" and kt: "k \<in> carrier A \<rightarrow> carrier A"
  and hiso: "isotone B B h" and kiso: "isotone A A k"
  and comm: "g\<circ>h = k\<circ>g"
  shows "g (\<nu>\<^bsub>B\<^esub> h) = \<nu>\<^bsub>A\<^esub> k"
proof -
  have gt: "g \<in> carrier B \<rightarrow> carrier A"
    by (metis cl_to_galois cl_upper_adjoint_def galois_ump2 lower_ex)
  have "g (\<mu>\<^bsub>B\<sharp>\<^esub>h) = \<mu>\<^bsub>A\<sharp>\<^esub>k"
    by (rule fixpoint_fusion, simp_all add: lower_ex ft ht kt gt hiso kiso comm)
  thus ?thesis by simp
qed

end
*)

end
