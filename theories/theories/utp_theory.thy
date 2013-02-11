(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/theories/utp_theory.thy                                          *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* UTP Theories *}

theory utp_theory
imports "../alpha/utp_alpha_pred"
begin

abbreviation is_healthy :: 
  " 'VALUE WF_ALPHA_PREDICATE 
  \<Rightarrow> 'VALUE ALPHA_FUNCTION 
  \<Rightarrow> bool" ("_ is _ healthy") where
"is_healthy p H \<equiv> p = H p"

definition IDEMPOTENT_OVER ::
  "'VALUE ALPHABET \<Rightarrow> 'VALUE ALPHA_FUNCTION set" where
"IDEMPOTENT_OVER a = {f . \<forall> p \<in> WF_ALPHA_PREDICATE_OVER a . f (f p) = f p}"

definition WF_THEORY :: "('VALUE ALPHABET set * 'VALUE ALPHA_FUNCTION set) set" where
"WF_THEORY = {(A,H) | A H . \<forall>a\<in>A. \<forall> hc\<in>H. hc \<in> IDEMPOTENT_OVER a}"

typedef (open) 'VALUE WF_THEORY = "WF_THEORY :: ('VALUE ALPHABET set * 'VALUE ALPHA_FUNCTION set) set"
  by (auto simp add:WF_THEORY_def)

declare Rep_WF_THEORY [simp]
declare Rep_WF_THEORY_inverse [simp]
declare Abs_WF_THEORY_inverse [simp]

setup_lifting type_definition_WF_THEORY

definition utp_alphabets :: 
  "'VALUE WF_THEORY \<Rightarrow> 'VALUE ALPHABET set" ("\<A>") where
"utp_alphabets t = fst (Rep_WF_THEORY t)"

definition healthconds :: 
  "'VALUE WF_THEORY \<Rightarrow> 'VALUE ALPHA_FUNCTION set" ("\<H>") where
"healthconds t = snd (Rep_WF_THEORY t)"

definition THEORY_PRED :: "'VALUE WF_THEORY \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE set" where
"THEORY_PRED t \<equiv> {p. \<alpha> p \<in> \<A> t \<and> (\<forall> H \<in> \<H> t. p is H healthy)}"

end
