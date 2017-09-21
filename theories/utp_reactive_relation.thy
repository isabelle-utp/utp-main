theory utp_reactive_relation
  imports utp_reactive
begin

notation times (infixl "\<cdot>" 70)
  
typedef (overloaded) ('t::trace, '\<alpha>) rrel = 
  "{P :: ('t,'\<alpha>) hrel_rp. (P is R2) \<and> ($ok \<sharp> P) \<and> ($ok\<acute> \<sharp> P) \<and> ($wait \<sharp> P) \<and> ($wait\<acute> \<sharp> P)}"
  by (rule_tac x="R1(true)" in exI, rel_auto)
    
notation Abs_rrel ("\<lceil>_\<rceil>\<^sub>r")

setup_lifting type_definition_rrel

instantiation rrel :: (trace, type) order
begin
  lift_definition less_eq_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> bool" is "op \<le>" .
  lift_definition less_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> bool" is "op <" .
instance
  apply (intro_classes)
    apply (transfer, simp add: less_uexpr_def less_eq_uexpr_def)
    apply (transfer, simp add: less_uexpr_def less_eq_uexpr_def)
   apply (transfer, simp add: less_uexpr_def less_eq_uexpr_def)
  apply (transfer, simp)
  done
end

lemma unrest_inf [unrest]: 
  fixes P Q :: "('a::lattice, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<sharp> Q"
  shows "x \<sharp> (P \<squnion> Q)"
  using assms by (rel_auto)
  
lemma unrest_sup [unrest]: 
  fixes P Q :: "('a::lattice, '\<alpha>) uexpr"
  assumes "x \<sharp> P" "x \<sharp> Q"
  shows "x \<sharp> (P \<sqinter> Q)"
  using assms by (rel_auto)
    
instantiation rrel :: (trace, type) lattice
begin
  lift_definition inf_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel"
  is "op \<squnion>" by (auto simp add: unrest, metis Healthy_def R2_conj conj_upred_def)
  lift_definition sup_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel"
  is "op \<sqinter>" by (auto simp add: unrest, metis Healthy_def R2_disj disj_upred_def)
instance
  by (intro_classes, (transfer, rel_auto)+)
end
  
instantiation rrel :: (trace, type) bounded_lattice
begin
  lift_definition bot_rrel :: "('a, 'b) rrel" is "false"
    by (simp add: unrest Healthy_def R1_false R2_def R2s_false)
  lift_definition top_rrel :: "('a, 'b) rrel" is "R1(true)"
    by (simp add: unrest Healthy_def R2_R1_true)
instance
  apply (intro_classes)
  apply (transfer, rel_auto)
  apply (transfer, metis Healthy_if R1_mono R2_def utp_pred_laws.top_greatest)
done
end

instantiation rrel :: (trace, type) boolean_algebra
begin
  lift_definition minus_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel"
  is rea_diff by (simp add: rea_diff_def unrest closure, metis Healthy_def' R2_conj rea_not_R2_closed)
  lift_definition uminus_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel"
  is rea_not by (simp add: closure unrest)
instance
  apply (intro_classes)
     apply (transfer, rel_auto)
    apply (transfer, rel_auto)
   apply (transfer, metis Healthy_def' R1_idem R2_def disj_upred_def rea_not_or)    
  apply (transfer, rel_auto)
done
end
  
definition true_rrel :: "('t::trace, '\<alpha>) rrel"
where [upred_defs]: "true_rrel = \<bottom>"

definition false_rrel :: "('t::trace, '\<alpha>) rrel"
where [upred_defs]: "false_rrel = \<top>"

definition not_rrel :: "('t::trace, '\<alpha>) rrel \<Rightarrow> ('t, '\<alpha>) rrel" where
[upred_defs]: "not_rrel = uminus"
  
definition disj_rrel :: "('t::trace, '\<alpha>) rrel \<Rightarrow> ('t, '\<alpha>) rrel \<Rightarrow> ('t, '\<alpha>) rrel" where
[upred_defs]: "disj_rrel = Lattices.sup"
  
definition conj_rrel :: "('t::trace, '\<alpha>) rrel \<Rightarrow> ('t, '\<alpha>) rrel \<Rightarrow> ('t, '\<alpha>) rrel" where
[upred_defs]: "conj_rrel = Lattices.inf"

lift_definition impl_rrel :: "('t::trace, '\<alpha>) rrel \<Rightarrow> ('t, '\<alpha>) rrel \<Rightarrow> ('t, '\<alpha>) rrel" 
is "\<lambda> P Q. P \<Rightarrow>\<^sub>r Q" by (simp_all add: unrest closure)

adhoc_overloading
  utrue "true_rrel" and
  ufalse "false_rrel" and
  unot "not_rrel" and
  uconj "conj_rrel" and
  udisj "disj_rrel" and
  uimpl "impl_rrel"
  
interpretation boolean_algebra minus not_rrel conj_rrel "op \<le>" "op <"
  disj_rrel false_rrel true_rrel
  by (unfold_locales, simp_all add: conj_rrel_def disj_rrel_def false_rrel_def true_rrel_def 
      not_rrel_def distrib_lattice_class.sup_inf_distrib1 boolean_algebra_class.diff_eq)

(*
instantiation rrel :: (trace, type) complete_lattice
begin
  lift_definition bot_rrel :: "('a, 'b) rrel" is "false"
    by (simp add: unrest Healthy_def R1_false R2_def R2s_false)
  lift_definition top_rrel :: "('a, 'b) rrel" is "R1(true)"
    by (simp add: unrest Healthy_def R2_R1_true)
  lift_definition Inf_rrel :: "('a, 'b) rrel set \<Rightarrow> ('a, 'b) rrel"
  is "\<lambda> A. if (A = {}) then false else Sup A"
    apply (auto simp add: unrest Healthy_def R1_false R2_def R2s_false)
*)  
    
instantiation rrel :: (trace, type) monoid_mult
begin
  lift_definition one_rrel :: "('a, 'b) rrel" is
    "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R) :: ('a,'b) hrel_rp" by (rel_auto, metis minus_zero_eq)
  lift_definition times_rrel :: "('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel \<Rightarrow> ('a, 'b) rrel" is
    "op ;;" by (auto simp add: unrest closure)
instance
  apply (intro_classes)
    apply (transfer, simp add: upred_semiring.mult_assoc)  
   apply (transfer, clarify, rel_auto, meson)
  apply (transfer, clarify, rel_auto, meson)
  done 
end
      
end