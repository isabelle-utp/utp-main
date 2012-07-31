(******************************************************************************)
(* Project: Unifying Theories of Programming                                  *)
(* File: utp_rel.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Relations *}

theory utp_rel
imports utp_pred utp_subst
begin

context PRED
begin

subsection {* Restrictions *}

definition NON_REL_VAR :: "'TYPE VAR set" where
"NON_REL_VAR = VAR - (DASHED \<union> UNDASHED)"

definition COMPOSABLE ::
  "(('VALUE, 'TYPE) BINDING \<times>
    ('VALUE, 'TYPE) BINDING) set" where
"COMPOSABLE = {(b1, b2) .
   (\<forall> v \<in> UNDASHED . b1(dash v) = b2 v) \<and> b1 \<cong> b2 on NON_REL_VAR}"

subsection {* Operators *}

subsubsection {* Skip *}

definition SkipR :: "('VALUE, 'TYPE) PREDICATE" where
"SkipR = {b \<in> WF_BINDING . \<forall> v \<in> UNDASHED . b v = b (dash v)}"

notation SkipR ("II")

subsubsection {* Sequential Composition *}

definition SemiR ::
  "('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE \<Rightarrow>
   ('VALUE, 'TYPE) PREDICATE" where
"p1 \<in> WF_PREDICATE \<and>
 p2 \<in> WF_PREDICATE \<longrightarrow>
 SemiR p1 p2 = {b1 \<oplus> b2 on DASHED | b1 b2 .
   b1 \<in> p1 \<and> b2 \<in> p2 \<and> (b1, b2) \<in> COMPOSABLE}"

(* Not sure about the precedence of sequential composition yet. *)

notation SemiR (infixr ";" 140)

subsection {* Theorems *}

subsubsection {* Closure Theorems *}

theorem SkipR_closure [closure] :
"II \<in> WF_PREDICATE"
apply (simp add: SkipR_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

theorem SemiR_closure [closure] :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 p1 ; p2 \<in> WF_PREDICATE"
apply (simp add: SemiR_def)
apply (simp add: WF_PREDICATE_def)
apply (auto)
done

subsection {* Proof Experiments *}

theorem SemiP_assoc :
"\<lbrakk>p1 \<in> WF_PREDICATE;
 p2 \<in> WF_PREDICATE;
 p3 \<in> WF_PREDICATE\<rbrakk> \<Longrightarrow>
 (p1 ; p2) ; p3 = p1 ; (p2 ; p3)"
apply (subgoal_tac "(p1 ; p2) \<in> WF_PREDICATE")
apply (subgoal_tac "(p2 ; p3) \<in> WF_PREDICATE")
apply (simp add: SemiR_def)
apply (safe)
(* This is still quite nasty, even in the simplified predicate model! *)
oops
end
end