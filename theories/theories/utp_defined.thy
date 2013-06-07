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

definition TVL :: "('a WF_PREDICATE * 'a WF_PREDICATE) \<Rightarrow> 'a WF_PREDICATE" where
"TVL \<equiv> \<lambda> (P,Q). `($def \<Rightarrow> P) \<and> (Q \<Leftrightarrow> $def)`"

declare TVL_def [eval]

syntax
  "_upred_tvl"     :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("TVL[_, _]")

translations
  "_upred_tvl p q"     == "CONST TVL (p, q)"

definition TrueT :: "'a WF_PREDICATE" where
"TrueT = `TVL[TrueP, TrueP]`"

definition FalseT :: "'a WF_PREDICATE" where
"FalseT = `TVL[FalseP, TrueP]`"

definition BotT :: "'a WF_PREDICATE" where
"BotT = `\<not> $def`"

definition NotT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"NotT P = `TVL[\<not> P[true/def], \<not> P[false/def]]`"

definition OrT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"OrT P Q = `TVL[P[true/def] \<or> Q[true/def], \<not> P[false/def] \<and> \<not> Q[false/def]]`"

definition AndT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"AndT P Q = `TVL[P[true/def] \<and> Q[true/def], \<not> P[false/def] \<and> \<not> Q[false/def]]`"

definition DefinedT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"DefinedT P = `\<not> P[false/def]`"

declare TrueT_def  [eval]
declare FalseT_def [eval]
declare BotT_def [eval]
declare NotT_def [eval]
declare OrT_def [eval]
declare AndT_def [eval]
declare DefinedT_def [eval]

syntax
  "_upred_truet"    :: "upred" ("true\<^sub>T")
  "_upred_falset"   :: "upred" ("false\<^sub>T")
  "_upred_bott"     :: "upred" ("\<bottom>\<^sub>T")
  "_upred_nott"     :: "upred \<Rightarrow> upred" ("\<not>\<^sub>T _" [40] 40)
  "_upred_andt"     :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<and>\<^sub>T" 35)
  "_upred_ort"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<or>\<^sub>T" 35)
  "_upred_definedt" :: "upred \<Rightarrow> upred" ("\<D> _")

translations
  "_upred_truet"    == "CONST TrueT"
  "_upred_falset"   == "CONST FalseT"
  "_upred_bott"     == "CONST BotT"
  "_upred_nott p"   == "CONST NotT p"
  "_upred_andt p q" == "CONST AndT p q"
  "_upred_ort p q"  == "CONST OrT p q"
  "_upred_definedt p" == "CONST DefinedT p"

lemma TrueT_unfold:
  "`true\<^sub>T` = `$def`"
  by (utp_pred_tac)

lemma FalseT_unfold:
  "`false\<^sub>T` = `false`"
  by (utp_pred_tac)

definition DH :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"DH(P) = `TVL[P[true/def], \<not> P[false/def]]`"

declare DH_def [eval]

lemma DefinedT_BotT:
  "`\<not> \<D> \<bottom>\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

lemma DefinedT_TrueT:
  "`\<D> true\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

lemma DefinedT_FalseT:
  "`\<D> false\<^sub>T`"
  by (utp_pred_tac)

lemma TVL_extreme_point1:
  "`TVL[true, false]` = `\<not> $def`"
  by (utp_pred_tac)

lemma TVL_extreme_point2:
  "`TVL[false, false]` = `\<not> $def`"
  by (utp_pred_tac)

lemma TVL_trade:
  "`TVL[P \<and> Q, Q]` = `TVL[P, Q]`"
  by (utp_pred_auto_tac)

lemma TVL_def_true:
  "\<lbrakk> UNREST {def} P; UNREST {def} Q \<rbrakk> \<Longrightarrow> 
  `TVL[P, Q][true/def]` = `P \<and> Q`"
  by (simp add:TVL_def usubst typing defined unrest closure)

lemma TVL_def_false:
  "\<lbrakk> UNREST {def} P; UNREST {def} Q \<rbrakk> \<Longrightarrow> 
  `TVL[P, Q][false/def]` = `\<not> Q`"
  by (simp add:TVL_def usubst typing defined unrest closure)

lemma AndT_left_unit:
  "P is DH \<Longrightarrow> `true\<^sub>T \<and>\<^sub>T P` = `P`"
  by (utp_pred_tac, utp_expr_tac)

lemma AndT_right_unit:
  "P is DH \<Longrightarrow> `P \<and>\<^sub>T true\<^sub>T` = `P`"
  by (utp_pred_tac, utp_expr_tac)

lemma OrT_left_anhil:
  "`true\<^sub>T \<or>\<^sub>T P` = `$def \<Leftrightarrow> \<D> P`"
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