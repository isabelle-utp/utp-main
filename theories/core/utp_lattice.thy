(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_lattice.thy                                                      *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Predicate Lattice *}

theory utp_lattice
imports 
  utp_pred 
  utp_rel 
  utp_unrest 
  "../laws/utp_rel_laws"
  "../tactics/utp_pred_tac" 
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  "../parser/utp_pred_parser"
begin

instantiation upred :: (TYPED_MODEL) lattice
begin
(* Lattice operators are now instantiated in utp_pred.thy. Change? *)
(*
definition sup_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"sup_upred = AndP"

definition inf_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"inf_upred = OrP"
*)
instance
apply (intro_classes)
apply (unfold less_eq_upred_def less_upred_def sup_upred_def inf_upred_def)
apply (utp_pred_auto_tac)+
done
end

declare sup_upred_def [eval, evalr, evalrx, evalpp, evalpr]
declare inf_upred_def [eval, evalr, evalrx, evalpp, evalpr]

(* Why did Simon redeclare notations from Lattice here? *)

(*
notation
  bot_class.bot ("\<top>") and
  top_class.top ("\<bottom>")
*)

(* Lattice syntax *)

default_sort type

syntax
  "_n_upred_inf"   :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "\<sqinter>" 65)
  "_n_upred_sup"   :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixl "\<squnion>" 70)
  "_n_upred_Inf"   :: "n_upreds \<Rightarrow> n_upred" ("\<Sqinter> {_}" [900] 900)
  "_n_upred_Sup"   :: "n_upreds \<Rightarrow> n_upred" ("\<Squnion> {_}" [900] 900)
  "_n_upred_INF1"  :: "pttrns \<Rightarrow> n_upred \<Rightarrow> n_upred" ("(3\<Sqinter>\<^sub>p _./ _)" [0, 10] 10)
  "_n_upred_INF"   :: "pttrn \<Rightarrow> 'b set \<Rightarrow> n_upred \<Rightarrow> n_upred"  ("(3\<Sqinter>\<^sub>p _:_./ _)" [0, 0, 10] 10)
  "_n_upred_SUP1"  :: "pttrns \<Rightarrow> n_upred \<Rightarrow> n_upred" ("(3\<Squnion>\<^sub>p _./ _)" [0, 10] 10)
  "_n_upred_SUP"   :: "pttrn \<Rightarrow> 'b set \<Rightarrow> n_upred \<Rightarrow> n_upred"  ("(3\<Squnion>\<^sub>p _:_./ _)" [0, 0, 10] 10)

translations
  "_n_upred_inf p q"     == "CONST sup_class.sup p q"
  "_n_upred_sup p q"     == "CONST inf_class.inf p q"
  "_n_upred_Inf ps"      == "CONST Sup ps"
  "_n_upred_Sup ps"      == "CONST Inf ps"
  "_n_upred_INF1 x y B"  == "SUP x. SUP y. B"
  "_n_upred_INF1 x B"    == "CONST SUPREMUM CONST UNIV (%x. B)"
  "_n_upred_INF x A B"   == "CONST SUPREMUM A (%x. B)"
  "_n_upred_SUP1 x y B"  == "INF x. INF y. B"
  "_n_upred_SUP1 x B"    == "CONST INFIMUM CONST UNIV (%x. B)"
  "_n_upred_SUP x A B"   == "CONST INFIMUM A (%x. B)"
  "_n_upreds x xs"       => "CONST insert x xs"
  "_n_upreds_end x"      => "{x}"

default_sort TYPED_MODEL

instantiation upred :: (TYPED_MODEL) bounded_lattice
begin
(* Lattice operators are now instantiated in utp_pred.thy. Change? *)
(*
definition bot_upred :: "'a upred" where
"bot_upred = TrueP"

definition top_upred :: "'a upred" where
"top_upred = FalseP"
*)
instance
apply (intro_classes)
apply (simp add: eval bot_upred_def)
apply (simp add: eval top_upred_def)
done
end

declare bot_upred_def [eval,evalr,evalrx,evalpp,evalpr]
declare top_upred_def [eval,evalr,evalrx,evalpp,evalpr]

(* Lattice operators are now instantiated in utp_pred.thy. Change? *)

(*
instantiation upred :: (TYPED_MODEL) Inf
begin

definition Inf_upred ::
  "'VALUE upred set \<Rightarrow>
   'VALUE upred" where
"Inf_upred ps = \<Or>\<^sub>p ps"

instance ..
end
*)

(*
instantiation upred :: (TYPED_MODEL) Sup
begin

definition Sup_upred ::
  "'VALUE upred set \<Rightarrow>
   'VALUE upred" where
"Sup_upred ps = \<And>\<^sub>p ps"

instance ..
end
*)

(* Are the following really needed? *)

lemma EvalP_Inf [eval] :
"\<lbrakk>\<Sqinter>\<^sub>p ps\<rbrakk>b = (\<exists> p \<in> ps . \<lbrakk>p\<rbrakk>b)"
  by (auto simp add: Sup_upred_def eval)

lemma EvalP_Sup [eval] :
"\<lbrakk>\<Squnion>\<^sub>p ps\<rbrakk>b = (\<forall> p \<in> ps . \<lbrakk>p\<rbrakk>b)"
  by (auto simp add: Inf_upred_def eval)

instantiation upred :: (TYPED_MODEL) complete_lattice
begin

instance
  apply (intro_classes)
  apply (simp_all add:less_eq_upred_def)
  apply (utp_pred_auto_tac)+
done
end

declare INF_def [eval,evalpp]
declare SUP_def [eval,evalpp]

instantiation upred :: (TYPED_MODEL) complete_distrib_lattice
begin

instance
  apply (intro_classes)
  apply (rule EvalP_intro)
  apply (simp only:eval)
  apply (utp_pred_tac)
  apply (simp only:eval)
  apply (utp_pred_tac)
done
end

instantiation upred :: (TYPED_MODEL) boolean_algebra
begin

definition uminus_upred :: "'a upred \<Rightarrow> 'a upred" where
"uminus_upred p = \<not>\<^sub>p p"

definition minus_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"minus_upred p q = (p \<and>\<^sub>p \<not>\<^sub>p q)"

instance 
  apply (intro_classes)
  apply (simp_all add: uminus_upred_def minus_upred_def inf_upred_def sup_upred_def bot_upred_def top_upred_def)
  apply (utp_pred_tac)+
done
end

theorem Lattice_L1:
  fixes P :: "'VALUE upred"
  shows "P \<sqsubseteq> \<Sqinter>\<^sub>p S \<longleftrightarrow> (\<forall> X\<in>S. P \<sqsubseteq> X)"
  by (metis Sup_le_iff)

theorem Lattice_L1A:
  fixes X :: "'VALUE upred"
  shows "X \<in> S \<Longrightarrow> \<Sqinter>\<^sub>p S \<sqsubseteq> X"
  by (metis Sup_upper)

theorem Lattice_L1B:
  fixes P :: "'VALUE upred"
  shows "\<forall> X \<in> S. P \<sqsubseteq> X \<Longrightarrow> P \<sqsubseteq> \<Sqinter>\<^sub>p S"
  by (metis Sup_le_iff)

theorem Lattice_L2:
  fixes Q :: "'VALUE upred"
  shows "(\<Squnion>\<^sub>p S) \<sqinter>\<^sub>p Q = \<Squnion>\<^sub>p { P \<sqinter>\<^sub>p Q | P. P \<in> S}"
proof -

  have "(\<Squnion>\<^sub>p S) \<sqinter>\<^sub>p Q = Q \<sqinter>\<^sub>p (\<Squnion>\<^sub>p S)"
    by (metis sup_commute)

  also have "... = (INF P:S. P \<sqinter>\<^sub>p Q)"
    by (metis Inf_sup sup_commute)

  also have "... = \<Squnion>\<^sub>p { P \<sqinter>\<^sub>p Q | P. P \<in> S}"
    apply (simp add:INF_def image_def)
    apply (subgoal_tac "{y. \<exists>x\<in>S. y = x \<sqinter>\<^sub>p Q} = {P \<sqinter>\<^sub>p Q |P. P \<in> S}")
    apply (simp)
    apply (auto)
  done

  ultimately show ?thesis by simp

qed
  
theorem Lattice_L3:
  fixes Q :: "'VALUE upred"
  shows "(\<Sqinter>\<^sub>p S) \<squnion>\<^sub>p Q = \<Sqinter>\<^sub>p{ P \<squnion>\<^sub>p Q | P. P \<in> S}"
proof -

  have "(\<Sqinter>\<^sub>p S) \<squnion>\<^sub>p Q = (SUP P:S. P \<squnion>\<^sub>p Q)"
    by (metis Sup_inf)

  also have "... = \<Sqinter>\<^sub>p { P \<squnion>\<^sub>p Q | P. P \<in> S}"
    apply (simp add:SUP_def image_def)
    apply (subgoal_tac "{y. \<exists>x\<in>S. y = x \<squnion>\<^sub>p Q} = {P \<squnion>\<^sub>p Q |P. P \<in> S}")
    apply (simp)
    apply (auto)
  done

  ultimately show ?thesis by simp

qed

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

lemma EvalR_SupP [evalr]:
  "\<lbrakk>\<Sqinter>\<^sub>p ps\<rbrakk>R = \<Union> {\<lbrakk>p\<rbrakk>R | p . p \<in> ps}"
  by (simp add:Sup_upred_def evalr)

lemma EvalRR_SupP [evalrr]:
  "\<lbrakk>\<Sqinter>\<^sub>p ps\<rbrakk>\<R> = \<Union> {\<lbrakk>p\<rbrakk>\<R> | p . p \<in> ps}"
  by (auto simp add:evalr MkRel_def)

lemma EvalRX_SupP [evalrx]:
  "\<lbrakk>\<Sqinter>\<^sub>p ps\<rbrakk>RX = \<Union> {\<lbrakk>p\<rbrakk>RX | p . p \<in> ps}"
  by (simp add:Sup_upred_def evalrx)

lemma EvalR_InfP [evalr]:
  "ps \<noteq> {} \<Longrightarrow> \<lbrakk>\<Squnion>\<^sub>p ps\<rbrakk>R = \<Inter> {\<lbrakk>p\<rbrakk>R | p . p \<in> ps}"
  by (simp add:Inf_upred_def evalr)

lemma EvalRR_InfP [evalrr]:
  "ps \<noteq> {} \<Longrightarrow> \<lbrakk>\<Squnion>\<^sub>p ps\<rbrakk>\<R> = \<Inter> {\<lbrakk>p\<rbrakk>\<R> | p . p \<in> ps}"
  apply (simp add:evalr MkRel_def)
  apply (rule trans)
  apply (rule image_Inter)
  apply (rule subset_inj_on)
  apply (rule map_prod_inj_on)
  apply (rule MkRelB_inj)
  apply (rule MkRelB_inj)
  apply (smt EvalR_range Sup_le_iff mem_Collect_eq)
  apply (auto)
done

lemma rel_Sup_comp_distl: "(\<Union> S) O Q = \<Union>{ P O Q | P. P \<in> S}"
  by (auto)

lemma rel_Sup_comp_distr: "P O (\<Union> S) = \<Union>{ P O Q | Q. Q \<in> S}"
  by (auto)

theorem Lattice_L4:
  fixes Q :: "'a upred"
  shows "(\<Sqinter>\<^sub>p S) ;\<^sub>R Q = \<Sqinter>\<^sub>p{ P ;\<^sub>R Q | P. P \<in> S}"
  apply (utp_rel_tac)
  apply (auto simp add:rel_Sup_comp_distl)
  apply (metis (hide_lams, no_types) EvalR_SemiR relcomp.intros)
done

theorem Lattice_L5:
  fixes P :: "'a upred"
  shows "P ;\<^sub>R (\<Sqinter>\<^sub>p S) = \<Sqinter>\<^sub>p{ P ;\<^sub>R Q | Q. Q \<in> S}"
  apply (utp_rel_tac)
  apply (simp add:rel_Sup_comp_distr)
  apply (auto)
  apply (metis (hide_lams, no_types) EvalR_SemiR relcomp.intros)
done

lemma Inter_inter_dist: "S \<noteq> {} \<Longrightarrow> (\<Inter> S) \<inter> P = \<Inter> {s \<inter> P | s. s \<in> S}"
  by (auto)

lemma "S \<noteq> {} \<Longrightarrow> (\<Squnion>\<^sub>p S) \<and>\<^sub>p P = (\<Squnion> {s \<and>\<^sub>p P | s. s \<in> S})"
  oops

subsection {* @{term UNREST} Theorems *}

lemma UNREST_BotP [unrest]: "UNREST vs \<bottom>"
  by (simp add:bot_upred_def unrest)

lemma UNREST_TopP [unrest]: "UNREST vs \<top>"
  by (simp add:top_upred_def unrest)

lemma UNREST_sup :
"\<lbrakk>UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<squnion>\<^sub>p p2)"
  by (simp add: inf_upred_def UNREST_AndP)

lemma UNREST_inf [unrest]:
"\<lbrakk>UNREST vs p1;
 UNREST vs p2\<rbrakk> \<Longrightarrow>
 UNREST vs (p1 \<sqinter>\<^sub>p p2)"
  by (auto simp add: sup_upred_def UNREST_OrP)

lemma UNREST_Sup [unrest]:
"\<forall> p \<in> ps. UNREST vs p \<Longrightarrow> UNREST vs (\<Squnion>\<^sub>p ps)"
  by (simp add: Inf_upred_def unrest)

lemma UNREST_Inf [unrest]:
"\<forall> p \<in> ps. UNREST vs p \<Longrightarrow> UNREST vs (\<Sqinter>\<^sub>p ps)"
  by (simp add: Sup_upred_def unrest)

lemma Sup_rel_closure [closure]:
  "ps \<subseteq> WF_RELATION \<Longrightarrow> \<Squnion>\<^sub>p ps \<in> WF_RELATION"
  by (simp add:Inf_upred_def closure)

lemma Inf_rel_closure [closure]:
  "ps \<subseteq> WF_RELATION \<Longrightarrow> \<Sqinter>\<^sub>p ps \<in> WF_RELATION"
  by (simp add:Sup_upred_def closure)

instantiation upred :: (TYPED_MODEL) monoid_mult
begin

definition 
  times_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
  "P * Q = P ;\<^sub>R Q"

definition one_upred :: "'a upred" where
"1 = II"

instance 
  apply (intro_classes)
  apply (simp_all add:times_upred_def one_upred_def SemiR_assoc)
done
end

declare times_upred_def [eval, evalr, evalrr, evalrx]
declare one_upred_def [eval, evalr, evalrr, evalrx]

instantiation upred :: (TYPED_MODEL) comm_monoid_add
begin

definition 
  plus_upred :: "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
  "plus_upred p q = p \<or>\<^sub>p q"

definition 
  zero_upred :: "'a upred" where
  "0 = FalseP"

instance 
  apply (intro_classes)
  apply (simp_all add: plus_upred_def zero_upred_def)
  apply (utp_pred_auto_tac)+
done
end

declare plus_upred_def [eval, evalr, evalrr, evalrx]
declare zero_upred_def [eval, evalr, evalrr, evalrx]

instantiation upred :: (TYPED_MODEL) semiring_1
begin

instance
  apply (intro_classes)
  apply (simp_all add:plus_upred_def times_upred_def 
                      zero_upred_def one_upred_def)
  apply (utp_rel_tac)+
done
end

theorem SkipR_SupP_def: 
  "II = \<Squnion>\<^sub>p { $\<^sub>ex\<acute> ==\<^sub>p $\<^sub>ex | x. x \<in> UNDASHED}"
  apply (auto intro!:destPRED_intro simp add:SkipR_def Inf_upred_def UNDASHED_nempty EqualP_def VarE.rep_eq AndDistP_rep_eq)
  apply (metis (lifting, full_types) LiftP.rep_eq destPRED_inverse mem_Collect_eq)
done

theorem SkipRA_SupP_def: 
  "\<lbrakk> vs \<subseteq> REL_VAR; HOMOGENEOUS vs \<rbrakk> \<Longrightarrow> 
     II\<^bsub>vs\<^esub> = \<Squnion>\<^sub>p { $\<^sub>ex\<acute> ==\<^sub>p $\<^sub>ex | x. x \<in> in vs}"
  apply (auto intro!:destPRED_intro simp add:SkipRA_rep_eq_alt Inf_upred_def UNDASHED_nempty EqualP_def VarE.rep_eq top_upred_def TrueP_def AndDistP_rep_eq)
  apply (metis (lifting, full_types) LiftP.rep_eq destPRED_inverse mem_Collect_eq)
done

subsection {* Big operator properties derived from the lattice *}

theorem OrP_AndDistP_dist:
  "p \<or>\<^sub>p \<And>\<^sub>p qs = \<And>\<^sub>p {p \<or>\<^sub>p q | q. q \<in> qs}"
proof -
  have "p \<or>\<^sub>p \<And>\<^sub>p qs = \<Squnion>\<^sub>p qs \<sqinter>\<^sub>p p"
    by (utp_pred_auto_tac)

  also have "... = \<Squnion>\<^sub>p { q \<sqinter>\<^sub>p p | q. q \<in> qs}"
    by (simp add: Lattice_L2)

  also have "... = \<Squnion>\<^sub>p { p \<or>\<^sub>p q | q. q \<in> qs}"
    by (utp_pred_auto_tac)

  finally show ?thesis
    by (simp add:Inf_upred_def)
qed

theorem ImpliesP_AndDistP_dist:
  "p \<Rightarrow>\<^sub>p \<And>\<^sub>p qs = \<And>\<^sub>p {p \<Rightarrow>\<^sub>p q | q. q \<in> qs}"
  by (simp add:OrP_AndDistP_dist ImpliesP_def)

lemma union_Union_dist:
  "qs \<noteq> {} \<Longrightarrow> p \<union> \<Union> qs = \<Union> {p \<union> q | q. q \<in> qs}"
  by (auto)

theorem OrP_OrDistP_dist:
  "qs \<noteq> {} \<Longrightarrow> p \<or>\<^sub>p \<Or>\<^sub>p qs = \<Or>\<^sub>p {p \<or>\<^sub>p q | q. q \<in> qs}"
  apply (utp_rel_tac)
  apply (simp add: union_Union_dist)
  apply (auto)
  apply (metis EvalR_OrP Un_iff)+
done

lemma inter_Inter_dist:
  "qs \<noteq> {} \<Longrightarrow> p \<inter> \<Inter> qs = \<Inter> {p \<inter> q | q. q \<in> qs}"
  by (auto)

theorem AndP_AndDistP_dist:
  "qs \<noteq> {} \<Longrightarrow> p \<and>\<^sub>p \<And>\<^sub>p qs = \<And>\<^sub>p {p \<and>\<^sub>p q | q. q \<in> qs}"
  apply (subgoal_tac "{p \<and>\<^sub>p q | q. q \<in> qs} \<noteq> {}")
  apply (utp_rel_tac)
  apply (simp add: inter_Inter_dist)
  apply (auto)
  apply (metis EvalR_AndP Int_iff)
done

theorem ImpliesP_OrDistP_dist:
  "qs \<noteq> {} \<Longrightarrow> p \<Rightarrow>\<^sub>p \<Or>\<^sub>p qs = \<Or>\<^sub>p {p \<Rightarrow>\<^sub>p q | q. q \<in> qs}"
  by (simp add:OrP_OrDistP_dist ImpliesP_def)

theorem OrDistP_SemiR_dist:
  "(\<Or>\<^sub>p ps) ;\<^sub>R q = \<Or>\<^sub>p {p ;\<^sub>R q | p. p \<in> ps}"
  by (simp add:Sup_upred_def[THEN sym] Lattice_L4)

theorem SemiR_OrDistP_dist:
  "p ;\<^sub>R (\<Or>\<^sub>p qs) = \<Or>\<^sub>p {p ;\<^sub>R q | q. q \<in> qs}"
  by (simp add:Sup_upred_def[THEN sym] Lattice_L5)

subsection {* Disjunctive / Monotonicity properties *}

lemma OrP_disjunctive2:
  "disjunctive2 (op \<or>\<^sub>p)"
  apply (simp add:disjunctive2_def)
  apply (utp_pred_auto_tac)
done

lemma OrP_mono2:
  "mono2 (op \<or>\<^sub>p)"
  by (metis OrP_disjunctive2 disjunctive2_mono2)

lemma AndP_disjunctive2:
  "disjunctive2 (op \<and>\<^sub>p)"
  apply (simp add:disjunctive2_def)
  apply (utp_pred_auto_tac)
done

lemma AndP_mono2:
  "mono2 (op \<and>\<^sub>p)"
  by (metis AndP_disjunctive2 disjunctive2_mono2)

lemma SemiR_disjunctive2:
  "disjunctive2 (op ;\<^sub>R)"
  apply (simp add:disjunctive2_def)
  apply (utp_rel_auto_tac)
done

lemma SemiR_mono2:
  "mono2 (op ;\<^sub>R)"
  by (metis SemiR_disjunctive2 disjunctive2_mono2)

end