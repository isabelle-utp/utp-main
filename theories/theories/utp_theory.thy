(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/theories/utp_theory.thy                                          *)
(* Author: Simon Foster and Frank Zeyda, University of York                   *)
(******************************************************************************)

header {* UTP Theories *}

theory utp_theory
imports 
  "../core/utp_pred"
  "../core/utp_unrest"
  "../tactics/utp_pred_tac"
  "../tactics/utp_rel_tac"
  "../tactics/utp_xrel_tac"
  "../poly/utp_poly_tac"
begin

definition is_healthy :: 
  " 'VALUE WF_PREDICATE 
  \<Rightarrow> 'VALUE WF_FUNCTION 
  \<Rightarrow> bool" ("_ is _") where
"is_healthy p H \<equiv> H p = p"

definition IDEMPOTENT_OVER ::
  "'a VAR set \<Rightarrow> 'a WF_FUNCTION set" where
"IDEMPOTENT_OVER vs = {f . \<forall> p \<in> WF_PREDICATE_OVER vs . f (f p) = f p}"

declare is_healthy_def [eval,evalr,evalrx,evalp]

lemma Healthy_intro [intro]:
  "H(P) = P \<Longrightarrow> P is H"
  by (simp add: is_healthy_def)

lemma Healthy_elim [elim]:
  "\<lbrakk> Q is H; \<lbrakk> H(Q) = Q \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add: is_healthy_def)

term "P is (H1 \<circ> H2)"

lemma Healthy_comp [closure]:
  "H2(P) is H1 \<Longrightarrow> P is H2 \<Longrightarrow> P is (H1 \<circ> H2)"
  by (simp add:is_healthy_def)

lemma Healthy_simp:
  "P is H \<Longrightarrow> H(P) = P"
  by (simp add:is_healthy_def)

lemma Healthy_apply [closure]:
  "\<lbrakk> H \<in> IDEMPOTENT_OVER vs; P \<in> WF_PREDICATE_OVER vs \<rbrakk> \<Longrightarrow> H(P) is H"
  by (simp add:is_healthy_def IDEMPOTENT_OVER_def)

type_synonym 'a THEORY = "('a VAR set set * 'a WF_FUNCTION set)"

definition WF_THEORY :: "('a THEORY) set" where
"WF_THEORY = {(A,H) | A H . \<forall>a\<in>A. \<forall> hc\<in>H. hc \<in> IDEMPOTENT_OVER a}"

typedef 'a WF_THEORY = "WF_THEORY :: ('a THEORY) set"
  morphisms DestTheory MkTheory
  by (auto simp add:WF_THEORY_def)

declare DestTheory [simp]
declare DestTheory_inverse [simp]
declare MkTheory_inverse [simp]

lemma DestTheory_intro [intro]:
  "(\<And> b. DestTheory x = DestTheory y) \<Longrightarrow> x = y"
  by (auto simp add: DestTheory_inject[THEN sym])

setup_lifting type_definition_WF_THEORY

definition utp_alphabets :: 
  "'VALUE WF_THEORY \<Rightarrow> 'VALUE VAR set set" ("\<A>") where
"utp_alphabets t = fst (DestTheory t)"

definition healthconds :: 
  "'VALUE WF_THEORY \<Rightarrow> 'VALUE WF_FUNCTION set" ("\<H>") where
"healthconds t = snd (DestTheory t)"

definition THEORY_PRED :: "'VALUE WF_THEORY \<Rightarrow> 'VALUE WF_PREDICATE set" where
"THEORY_PRED t \<equiv> {p. (\<exists> a \<in> \<A> t. UNREST (VAR - a) p) \<and>  (\<forall> H \<in> \<H> t. p is H)}"

instantiation WF_THEORY :: (VALUE) join_semilattice_zero
begin

lift_definition zero_WF_THEORY :: "'a WF_THEORY" is "(UNIV, {}) :: 'a THEORY"
  by (simp add:WF_THEORY_def)

lift_definition plus_WF_THEORY :: "'a::VALUE WF_THEORY \<Rightarrow> 'a WF_THEORY \<Rightarrow> 'a WF_THEORY" 
is "(\<lambda> (A1,HC1) (A2,HC2). (A1\<inter>A2,HC1\<union>HC2)) :: 'a THEORY \<Rightarrow> 'a THEORY \<Rightarrow> 'a THEORY"
  by (auto simp add:WF_THEORY_def)

definition less_eq_WF_THEORY :: "'a WF_THEORY \<Rightarrow> 'a WF_THEORY \<Rightarrow> bool" where
"less_eq_WF_THEORY x y \<longleftrightarrow> x + y = y"

definition less_WF_THEORY :: "'a WF_THEORY \<Rightarrow> 'a WF_THEORY \<Rightarrow> bool" where
"less_WF_THEORY x y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

instance
  apply (intro_classes)
  apply (simp add:less_eq_WF_THEORY_def)
  apply (simp add:less_WF_THEORY_def)
  apply (rule DestTheory_intro)
  apply (auto simp add:plus_WF_THEORY.rep_eq zero_WF_THEORY.rep_eq)
  apply (case_tac "DestTheory x", case_tac "DestTheory y", case_tac "DestTheory z")
  apply (auto)
  apply (rule DestTheory_intro)
  apply (auto simp add:plus_WF_THEORY.rep_eq zero_WF_THEORY.rep_eq)
  apply (case_tac "DestTheory x", case_tac "DestTheory y")
  apply (auto)
  apply (rule DestTheory_intro)
  apply (auto simp add:plus_WF_THEORY.rep_eq zero_WF_THEORY.rep_eq)
  apply (case_tac "DestTheory x")
  apply (auto)
done
end

end
