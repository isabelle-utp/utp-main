(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_lattice.thy                                                      *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Predicate Lattice *}

theory utp_lattice
imports 
  utp_pred 
  utp_rel 
  utp_unrest 
  "../tactics/utp_pred_tac" 
  "../tactics/utp_rel_tac"
begin

notation
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900) and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

instantiation WF_PREDICATE :: (VALUE) lattice
begin

definition sup_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"sup_WF_PREDICATE = AndP"

definition inf_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"inf_WF_PREDICATE = OrP"

instance
  apply (intro_classes)
  apply (simp_all add: sup_WF_PREDICATE_def inf_WF_PREDICATE_def less_eq_WF_PREDICATE_def less_WF_PREDICATE_def)
  apply (utp_pred_auto_tac)+
done
end

declare sup_WF_PREDICATE_def [eval,evalr]
declare inf_WF_PREDICATE_def [eval,evalr]

instantiation WF_PREDICATE :: (VALUE) bounded_lattice
begin

definition top_WF_PREDICATE :: "'a WF_PREDICATE" where
"top_WF_PREDICATE = FalseP"

definition bot_WF_PREDICATE :: "'a WF_PREDICATE" where
"bot_WF_PREDICATE = TrueP"

instance proof

  fix a :: "'a WF_PREDICATE"
  show "bot \<le> a"
    apply (simp add:bot_WF_PREDICATE_def less_eq_WF_PREDICATE_def)
    apply (utp_pred_auto_tac)
  done

  show "a \<le> top_class.top"
    apply (simp add:top_WF_PREDICATE_def less_eq_WF_PREDICATE_def)
    apply (utp_pred_auto_tac)
  done
qed
end

declare bot_WF_PREDICATE_def [eval,evalr]
declare top_WF_PREDICATE_def [eval,evalr]

instantiation WF_PREDICATE :: (VALUE) Sup
begin

definition Sup_WF_PREDICATE ::
  "'VALUE WF_PREDICATE set \<Rightarrow>
   'VALUE WF_PREDICATE" where
"Sup_WF_PREDICATE ps = (if ps = {} then bot else mkPRED (\<Inter> (destPRED ` ps)))"

instance ..
end

instantiation WF_PREDICATE :: (VALUE) Inf
begin

definition Inf_WF_PREDICATE ::
  "'VALUE WF_PREDICATE set \<Rightarrow>
   'VALUE WF_PREDICATE" where
"Inf_WF_PREDICATE ps = (if ps = {} then top else mkPRED (\<Union> (destPRED ` ps)))"

instance ..
end

theorem EvalP_Inf [eval] :
"\<lbrakk>\<Sqinter> ps\<rbrakk>b = (\<exists> p \<in> ps . \<lbrakk>p\<rbrakk>b)"
apply (simp add: EvalP_def closure)
apply (simp add: Inf_WF_PREDICATE_def)
apply (clarify)
apply (simp add: top_WF_PREDICATE_def FalseP_def)
done

theorem EvalP_Sup [eval] :
"\<lbrakk>\<Squnion> ps\<rbrakk>b = (\<forall> p \<in> ps . \<lbrakk>p\<rbrakk>b)"
apply (simp add: EvalP_def closure)
apply (simp add: Sup_WF_PREDICATE_def)
apply (clarify)
apply (simp add: bot_WF_PREDICATE_def TrueP_def)
done

instantiation WF_PREDICATE :: (VALUE) complete_lattice
begin

instance
  apply (intro_classes)
  apply (simp_all add:less_eq_WF_PREDICATE_def)
  apply (utp_pred_auto_tac)+
done
end

declare INF_def [eval]
declare SUP_def [eval]

instantiation WF_PREDICATE :: (VALUE) complete_distrib_lattice
begin

instance
  apply (intro_classes)
  apply (utp_pred_auto_tac)+
done
end

instantiation WF_PREDICATE :: (VALUE) boolean_algebra
begin

definition uminus_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"uminus_WF_PREDICATE p = \<not>p p"

definition minus_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"minus_WF_PREDICATE p q = (p \<or>p \<not>p q)"

instance 
  apply (intro_classes)
  apply (simp_all add: uminus_WF_PREDICATE_def minus_WF_PREDICATE_def inf_WF_PREDICATE_def sup_WF_PREDICATE_def bot_WF_PREDICATE_def top_WF_PREDICATE_def)
  apply (utp_pred_tac)+
done
end

lemma Lattice_L1:
  fixes P :: "'VALUE WF_PREDICATE"
  shows "P \<sqsubseteq> \<Sqinter> S \<longleftrightarrow> (\<forall> X\<in>S. P \<sqsubseteq> X)"
  by (metis le_Inf_iff)

lemma Lattice_L1A:
  fixes X :: "'VALUE WF_PREDICATE"
  shows "X \<in> S \<Longrightarrow> \<Sqinter> S \<sqsubseteq> X"
  by (metis Inf_lower)

lemma Lattice_L1B:
  fixes P :: "'VALUE WF_PREDICATE"
  shows "\<forall> X \<in> S. P \<sqsubseteq> X \<Longrightarrow> P \<sqsubseteq> \<Sqinter> S"
  by (metis Lattice_L1)

lemma Lattice_L2:
  fixes Q :: "'VALUE WF_PREDICATE"
  shows "(\<Squnion> S) \<sqinter> Q = \<Squnion> { P \<sqinter> Q | P. P \<in> S}"
proof -

  have "(\<Squnion> S) \<sqinter> Q = Q \<sqinter> (\<Squnion> S)"
    by (metis inf.commute)

  also have "... = (SUP P:S. P \<sqinter> Q)"
    by (metis Sup_inf inf_commute)

  also have "... = \<Squnion> { P \<sqinter> Q | P. P \<in> S}"
    apply (simp add:SUP_def image_def)
    apply (subgoal_tac "{y. \<exists>x\<in>S. y = x \<sqinter> Q} = {P \<sqinter> Q |P. P \<in> S}")
    apply (simp)
    apply (auto)
  done

  ultimately show ?thesis by simp

qed
  
lemma Lattice_L3:
  fixes Q :: "'VALUE WF_PREDICATE"
  shows "(\<Sqinter> S) \<squnion> Q = \<Sqinter>{ P \<squnion> Q | P. P \<in> S}"
proof -

  have "(\<Sqinter> S) \<squnion> Q = (INF P:S. P \<squnion> Q)"
    by (metis Inf_sup)

  also have "... = \<Sqinter> { P \<squnion> Q | P. P \<in> S}"
    apply (simp add:INF_def image_def)
    apply (subgoal_tac "{y. \<exists>x\<in>S. y = x \<squnion> Q} = {P \<squnion> Q |P. P \<in> S}")
    apply (simp)
    apply (auto)
  done

  ultimately show ?thesis by simp

qed

lemma EvalR_SupP [evalr]:
  "\<lbrakk>\<Sqinter> ps\<rbrakk>R = \<Union> {\<lbrakk>p\<rbrakk>R | p . p \<in> ps}"
  by (auto simp add:EvalR_def Inf_WF_PREDICATE_def top_WF_PREDICATE_def FalseP_def)

lemma EvalR_InfP [evalr]:
  "\<lbrakk>\<Squnion> ps\<rbrakk>R = \<Inter> {\<lbrakk>p\<rbrakk>R | p . p \<in> ps}"
  apply (auto simp add:EvalR_def Sup_WF_PREDICATE_def bot_WF_PREDICATE_def TrueP_def)
  apply (simp add:image_def)
  defer
  apply (smt BindR_inject EvalR_def INT_I image_iff)
oops
  
lemma rel_Sup_comp_distl: "(\<Union> S) O Q = \<Union>{ P O Q | P. P \<in> S}"
  by (auto)

lemma rel_Sup_comp_distr: "P O (\<Union> S) = \<Union>{ P O Q | Q. Q \<in> S}"
  by (auto)

lemma Lattice_L4:
  fixes Q :: "'VALUE WF_PREDICATE"
  shows "(\<Sqinter> S) ; Q = \<Sqinter>{ P ; Q | P. P \<in> S}"
  apply (utp_rel_tac)
  apply (auto simp add:rel_Sup_comp_distl)
  apply (metis (hide_lams, no_types) EvalR_SemiR relcomp.intros)
done

subsection {* @{term UNREST} Theorems *}

theorem UNREST_BotP [unrest]: "UNREST vs bot"
  by (simp add:bot_WF_PREDICATE_def unrest)

theorem UNREST_TopP [unrest]: "UNREST vs top"
  by (simp add:top_WF_PREDICATE_def unrest)

theorem UNREST_sup :
"\<lbrakk>UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<squnion> p2)"
  by (simp add: sup_WF_PREDICATE_def UNREST_AndP)

theorem UNREST_inf [unrest]:
"\<lbrakk>UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<sqinter> p2)"
  by (auto simp add: inf_WF_PREDICATE_def UNREST_OrP)

theorem UNREST_Sup [unrest]:
"\<forall> p \<in> ps. UNREST vs p \<Longrightarrow> UNREST vs (\<Squnion> ps)"
  apply (simp add: Sup_WF_PREDICATE_def UNREST_BotP)
  apply (simp add: UNREST_def)
done

theorem UNREST_Inf [unrest]:
"\<forall> p \<in> ps. UNREST vs p \<Longrightarrow> UNREST vs (\<Sqinter> ps)"
  apply (simp add: Inf_WF_PREDICATE_def UNREST_TopP)
  apply (auto simp add: UNREST_def)
done

instantiation WF_PREDICATE :: (VALUE) monoid_mult
begin

definition 
  times_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
  "P * Q = P ; Q"

definition one_WF_PREDICATE :: "'a WF_PREDICATE" where
"1 = II"

instance 
  apply (intro_classes)
  apply (simp_all add:times_WF_PREDICATE_def one_WF_PREDICATE_def)
  apply (metis SemiP_assoc)
  apply (metis SemiP_SkipR_left)
  apply (metis SemiP_SkipR_right)
done
end

instantiation WF_PREDICATE :: (VALUE) comm_monoid_add
begin

definition 
  plus_WF_PREDICATE :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
  "plus_WF_PREDICATE p q = p \<or>p q"

definition 
  zero_WF_PREDICATE :: "'a WF_PREDICATE" where
  "0 = false"

instance 
  apply (intro_classes)
  apply (simp_all add: plus_WF_PREDICATE_def zero_WF_PREDICATE_def)
  apply (utp_pred_auto_tac)+
done
end

instantiation WF_PREDICATE :: (VALUE) semiring_1
begin

instance
  apply (intro_classes)
  apply (simp_all add:plus_WF_PREDICATE_def times_WF_PREDICATE_def 
                      zero_WF_PREDICATE_def one_WF_PREDICATE_def)
  apply (utp_rel_tac)+
  apply (auto simp add:Id_on_def WF_REL_BINDING_def)
done
end

end