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
begin

definition is_healthy :: 
  " 'VALUE WF_PREDICATE 
  \<Rightarrow> 'VALUE WF_FUNCTION 
  \<Rightarrow> bool" ("_ is _") where
"is_healthy p H \<equiv> H p = p"

declare is_healthy_def [eval]

definition IDEMPOTENT_OVER ::
  "'VALUE VAR set \<Rightarrow> 'VALUE WF_FUNCTION set" where
"IDEMPOTENT_OVER vs = {f . \<forall> p \<in> WF_PREDICATE_OVER vs . f (f p) = f p}"

definition WF_THEORY :: "('VALUE VAR set set * 'VALUE WF_FUNCTION set) set" where
"WF_THEORY = {(A,H) | A H . \<forall>a\<in>A. \<forall> hc\<in>H. hc \<in> IDEMPOTENT_OVER a}"

typedef 'VALUE WF_THEORY = "WF_THEORY :: (('VALUE VAR) set set * 'VALUE WF_FUNCTION set) set"
  morphisms DestTheory MkTheory
  by (auto simp add:WF_THEORY_def)

declare DestTheory [simp]
declare DestTheory_inverse [simp]
declare MkTheory_inverse [simp]

setup_lifting type_definition_WF_THEORY

definition utp_alphabets :: 
  "'VALUE WF_THEORY \<Rightarrow> 'VALUE VAR set set" ("\<A>") where
"utp_alphabets t = fst (DestTheory t)"

definition healthconds :: 
  "'VALUE WF_THEORY \<Rightarrow> 'VALUE WF_FUNCTION set" ("\<H>") where
"healthconds t = snd (DestTheory t)"

definition THEORY_PRED :: "'VALUE WF_THEORY \<Rightarrow> 'VALUE WF_PREDICATE set" where
"THEORY_PRED t \<equiv> {p. (\<exists> a \<in> \<A> t. UNREST (VAR - a) p) \<and>  (\<forall> H \<in> \<H> t. p is H)}"

end
