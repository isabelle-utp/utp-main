(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_defined.thy                                                      *)
(* Author: Victor Bandur and Simon Foster, University of York (UK)            *)
(******************************************************************************)

header {* A theory of definedness in the UTP *}

theory utp_defined
imports 
  "../core/utp_pred"
  "../parser/utp_pred_parser"
  "../laws/utp_pred_laws"
  "../laws/utp_rename_laws"
  "../laws/utp_subst_laws"
  "../laws/utp_rel_laws"
  utp_theory
begin

default_sort BOOL_SORT

abbreviation "def  \<equiv> MkPlain ''def'' BoolType True"

(* Add a blackboard three *)
definition TVL :: "('a WF_PREDICATE * 'a WF_PREDICATE) \<Rightarrow> 'a WF_PREDICATE" where
(* "TVL \<equiv> \<lambda> (P,Q). `($def \<Rightarrow> P) \<and> (Q \<Leftrightarrow> $def)`" *)
"TVL = (\<lambda> (P,Q). `P \<lhd> $def \<rhd> \<not> Q`)"

declare TVL_def [eval]

syntax
  "_upred_tvl"     :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("\<three>'(_, _')")

translations
  "_upred_tvl p q"     == "CONST TVL (p, q)"

definition TrueT :: "'a WF_PREDICATE" where
"TrueT = `\<three>(true, true)`"

definition FalseT :: "'a WF_PREDICATE" where
"FalseT = `\<three>(false, true)`"

definition BotT :: "'a WF_PREDICATE" where
"BotT = `\<not> $def`"

definition NotT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"NotT P = `\<three>(\<not> P[true/def], \<not> P[false/def])`"

definition OrT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"OrT P Q = `\<three>(P[true/def] \<or> Q[true/def], \<not> P[false/def] \<and> \<not> Q[false/def])`"

definition AndT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"AndT P Q = `\<three>(P[true/def] \<and> Q[true/def], \<not> P[false/def] \<and> \<not> Q[false/def])`"

definition PredicateT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"PredicateT P = `P[true/def]`"

definition DefinedT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"DefinedT P = `\<not> P[false/def]`"

declare TrueT_def  [eval]
declare FalseT_def [eval]
declare BotT_def [eval]
declare NotT_def [eval]
declare OrT_def [eval]
declare AndT_def [eval]
declare PredicateT_def [eval]
declare DefinedT_def [eval]

syntax
  "_upred_truet"    :: "upred" ("true\<^sub>T")
  "_upred_falset"   :: "upred" ("false\<^sub>T")
  "_upred_bott"     :: "upred" ("\<bottom>\<^sub>T")
  "_upred_nott"     :: "upred \<Rightarrow> upred" ("\<not>\<^sub>T _" [40] 40)
  "_upred_andt"     :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<and>\<^sub>T" 35)
  "_upred_ort"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<or>\<^sub>T" 35)
  "_upred_definedt" :: "upred \<Rightarrow> upred" ("\<D>'(_')")
  "_upred_predicatet" :: "upred \<Rightarrow> upred" ("\<P>'(_')")

translations
  "_upred_truet"    == "CONST TrueT"
  "_upred_falset"   == "CONST FalseT"
  "_upred_bott"     == "CONST BotT"
  "_upred_nott p"   == "CONST NotT p"
  "_upred_andt p q" == "CONST AndT p q"
  "_upred_ort p q"  == "CONST OrT p q"
  "_upred_definedt p" == "CONST DefinedT p"
  "_upred_predicatet p" == "CONST PredicateT p"

lemma TrueT_unfold:
  "`true\<^sub>T` = `$def`"
  by (utp_pred_tac)

lemma FalseT_unfold:
  "`false\<^sub>T` = `false`"
  by (utp_pred_tac)

definition DH :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"DH(P) = `P \<and> (\<D>(P) \<sqsubseteq> \<P>(P))`"

declare DH_def [eval]

lemma DH_idem: "DH (DH P) = DH P"
  by (utp_pred_auto_tac)

lemma DH_refine: "P is DH \<Longrightarrow> `\<D>(P) \<sqsubseteq> \<P>(P)`"
  by (utp_pred_auto_tac)

lemma DH_defined_anhil: "P is DH \<Longrightarrow> `\<D>(P) \<and> \<P>(P)` = `\<P>(P)`"
  by (utp_pred_auto_tac)

lemma TVL_inject: "`\<three>(\<P>(P), \<D>(P))` = P"
  apply (simp add:TVL_def PredicateT_def DefinedT_def)
  apply (rule BoolType_aux_var_split_eq_intro[of "def"])
  apply (simp_all add:TrueT_def TVL_def AndT_def usubst typing defined CondR_true CondR_false DH_def is_healthy_def)
done

lemma TVL_left:
  "`\<P>(\<three>(P, Q))` = `P[true/def]`"
  by (simp add:TVL_def PredicateT_def usubst typing defined CondR_true)

lemma TVL_right:
  "`\<D>(\<three>(P, Q))` = `Q[false/def]`"
  by (simp add:TVL_def usubst typing defined unrest closure CondR_false DefinedT_def)

(*
definition DH :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
(* "DH(P) = `\<three>(P[true/def], \<not> P[false/def])`" *)
"DH(P) = `($def \<Leftrightarrow> \<D> P) \<and> P`"

declare DH_def [eval]
*)


lemma TVL_DH:
  "\<lbrakk> UNREST {def} P; UNREST {def} Q; Q \<sqsubseteq> P \<rbrakk> \<Longrightarrow> `\<three>(P, Q)` is DH"
  apply (simp add:is_healthy_def DH_def TVL_right PredicateT_def)
  apply (simp add:TVL_def)
  apply (rule_tac BoolType_aux_var_split_eq_intro[of "def"])
  apply (simp_all add:typing defined usubst CondR_true CondR_false)
  apply (utp_pred_auto_tac)
  apply (utp_pred_auto_tac)
done

lemma DefinedT_BotT:
  "`\<not> \<D>(\<bottom>\<^sub>T)`"
  by (utp_pred_tac, utp_expr_tac)

lemma DefinedT_TrueT:
  "`\<D>(true\<^sub>T)`"
  by (utp_pred_tac, utp_expr_tac)

lemma DefinedT_FalseT:
  "`\<D>(false\<^sub>T)`"
  by (utp_pred_tac)

lemma TVL_extreme_point1:
  "`\<three>(true, false)` = `true`"
  by (utp_pred_tac)

lemma TVL_extreme_point2:
  "`\<three>(false, false)` = `\<not> $def`"
  by (utp_pred_tac)

(*
lemma TVL_trade:
  "`\<three>(P \<and> Q, Q)` = `\<three>(P, Q)`"
  apply (utp_pred_auto_tac)
*)

lemma AndT_left_unit:
  "`true\<^sub>T \<and>\<^sub>T P` = `P`"
  apply (rule BoolType_aux_var_split_eq_intro[of "def"])
  apply (simp_all add:TrueT_def TVL_def AndT_def usubst typing defined CondR_true CondR_false)
done

lemma AndT_right_unit:
  "`P \<and>\<^sub>T true\<^sub>T` = `P`"
  apply (rule BoolType_aux_var_split_eq_intro[of "def"])
  apply (simp_all add:TrueT_def TVL_def AndT_def usubst typing defined CondR_true CondR_false)
done

lemma "`true\<^sub>T` is DH"
  apply (simp add:is_healthy_def DH_def TrueT_def TVL_def usubst typing defined CondR_false DefinedT_def)
  apply (utp_pred_tac)
done

lemma "`false\<^sub>T` is DH"
  apply (simp add:is_healthy_def DH_def FalseT_def TVL_def usubst typing defined CondR_false DefinedT_def)
  apply (utp_pred_tac)
done

lemma OrT_left_anhil:
  "P is DH \<Longrightarrow> `true\<^sub>T \<or>\<^sub>T P` = `true`"
  apply (simp_all add:TrueT_def TVL_def OrT_def DefinedT_def usubst typing defined CondR_true CondR_false)
  apply (simp add: DH_def is_healthy_def)
  apply (simp add: OrT_def)
  by (utp_pred_tac, utp_expr_tac, auto)

lemma OrT_right_anhil:
  "`P \<or>\<^sub>T true\<^sub>T` = `$def \<Leftrightarrow> \<D> P`"
  by (utp_pred_tac, utp_expr_tac, auto)

lemma AndT_assoc:
  "`(P \<and>\<^sub>T Q) \<and>\<^sub>T R` = `P \<and>\<^sub>T Q \<and>\<^sub>T R`"
  by (utp_pred_tac, utp_expr_tac, auto)

lemma AndT_commute: 
  "`P \<and>\<^sub>T Q` = `Q \<and>\<^sub>T P`"
  by (utp_pred_tac, utp_expr_tac, auto)

lemma OrT_assoc:
  "`(P \<or>\<^sub>T Q) \<or>\<^sub>T R` = `P \<or>\<^sub>T Q \<or>\<^sub>T R`"
  by (utp_pred_tac, utp_expr_tac, auto)

lemma OrT_commute:
  "`P \<or>\<^sub>T Q` = `Q \<or>\<^sub>T P`"
  by (utp_pred_tac, utp_expr_tac, auto)

lemma NotT_double: "P is DH \<Longrightarrow> `\<not>\<^sub>T \<not>\<^sub>T P` = `P`"
  by (utp_pred_tac, utp_expr_tac, auto)

lemma NotT_TrueT: "`\<not>\<^sub>T true\<^sub>T` = `false\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

lemma AndT_BotT_left: "`\<bottom>\<^sub>T \<and>\<^sub>T P` = `\<bottom>\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

lemma AndT_BotT_right: "`P \<and>\<^sub>T \<bottom>\<^sub>T` = `\<bottom>\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

lemma NotT_BotT: "`\<not>\<^sub>T \<bottom>\<^sub>T` = `\<bottom>\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

end