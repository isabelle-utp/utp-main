(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_definedness.thy                                                  *)
(* Author: Victor Bandur and Simon Foster, University of York (UK)            *)
(******************************************************************************)

header {* A theory of definedness in the UTP *}

theory utp_definedness
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
(* "TVL = (\<lambda> (P,Q). `P \<lhd> $def \<rhd> \<not> Q`)" *)

definition PredicateT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"PredicateT P = `P[true/def]`"

definition DefinedT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"DefinedT P = `\<not> P[false/def]`"

declare TVL_def [eval]
declare PredicateT_def [eval]
declare DefinedT_def [eval]

syntax
  "_upred_tvl"     :: "upred \<Rightarrow> upred \<Rightarrow> upred" ("\<three>'(_, _')")
  "_upred_definedt" :: "upred \<Rightarrow> upred" ("\<D>'(_')")
  "_upred_predicatet" :: "upred \<Rightarrow> upred" ("\<P>'(_')")

translations
  "_upred_tvl p q"     == "CONST TVL (p, q)"
  "_upred_definedt p" == "CONST DefinedT p"
  "_upred_predicatet p" == "CONST PredicateT p"


definition TrueT :: "'a WF_PREDICATE" where
"TrueT = `\<three>(true, true)`"

definition FalseT :: "'a WF_PREDICATE" where
"FalseT = `\<three>(false, true)`"

definition BotT :: "'a WF_PREDICATE" where
"BotT = `\<not> $def`"

definition NotT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"NotT P = `\<three>(\<not> \<P>(P), \<D>(P))`"

definition OrT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"OrT P Q = `\<three>(\<P>(P) \<or> \<P>(Q), \<D>(P) \<and> \<D>(Q))`"

definition AndT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"AndT P Q = `\<three>(\<P>(P) \<and> \<P>(Q), \<D>(P) \<and> \<D>(Q))`"

definition AllDefinedT :: "'a VAR set \<Rightarrow> 'a WF_PREDICATE" where
"AllDefinedT xs = mkPRED {b. \<forall>x\<in>xs. \<D> (\<langle>b\<rangle>\<^sub>b x)}"

definition ExistsT :: "'a VAR set \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"ExistsT xs p = (\<exists>p xs. AllDefinedT xs \<and>p p)"

notation ExistsT ("(\<exists>t _ ./ _)" [0, 10] 10)

definition ForallT :: "'a VAR set \<Rightarrow> 'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"ForallT xs p = (\<forall>p xs. AllDefinedT xs \<Rightarrow>p p)"

notation ForallT ("(\<forall>t _ ./ _)" [0, 10] 10)

definition ClosureT :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"ClosureT p = (\<forall>t VAR. p)"

declare TrueT_def  [eval]
declare FalseT_def [eval]
declare BotT_def [eval]
declare NotT_def [eval]
declare OrT_def [eval]
declare AndT_def [eval]

text {* DH for a given TVL (P, Q) ensures that P is true only when Q is also true,
        i.e. a true valuation must also be a defined evaluation. *}

definition DH :: "'a WF_PREDICATE \<Rightarrow> 'a WF_PREDICATE" where
"DH(P) = `P \<and> (\<D>(P) \<sqsubseteq> \<P>(P))`"

declare DH_def [eval]

syntax
  "_upred_truet"    :: "upred" ("true\<^sub>T")
  "_upred_falset"   :: "upred" ("false\<^sub>T")
  "_upred_bott"     :: "upred" ("\<bottom>\<^sub>T")
  "_upred_nott"     :: "upred \<Rightarrow> upred" ("\<not>\<^sub>T _" [40] 40)
  "_upred_andt"     :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<and>\<^sub>T" 35)
  "_upred_ort"      :: "upred \<Rightarrow> upred \<Rightarrow> upred" (infixr "\<or>\<^sub>T" 35)
  "_upred_clost"    :: "upred \<Rightarrow> upred" ("[_]\<^sub>T")
  "_upred_dh"       :: "upred \<Rightarrow> upred" ("DH'(_')")

translations
  "_upred_truet"    == "CONST TrueT"
  "_upred_falset"   == "CONST FalseT"
  "_upred_bott"     == "CONST BotT"
  "_upred_nott p"   == "CONST NotT p"
  "_upred_andt p q" == "CONST AndT p q"
  "_upred_ort p q"  == "CONST OrT p q"
  "_upred_clost p"  == "CONST ClosureT p"
  "_upred_dh p"     == "CONST DH p"

lemma TrueT_unfold:
  "`true\<^sub>T` = `$def`"
  by (utp_pred_tac)

lemma FalseT_unfold:
  "`false\<^sub>T` = `false`"
  by (utp_pred_tac)

lemma DH_idem: 
  "DH (DH P) = DH P"
  by (utp_pred_auto_tac)

lemma DH_refine: "P is DH \<Longrightarrow> `\<D>(P) \<sqsubseteq> \<P>(P)`"
  by (utp_pred_auto_tac)

lemma DH_defined_anhil: "P is DH \<Longrightarrow> `\<D>(P) \<and> \<P>(P)` = `\<P>(P)`"
  by (utp_pred_auto_tac)

lemma TVL_inject: "P is DH \<Longrightarrow> `\<three>(\<P>(P), \<D>(P))` = P"
  apply (simp add:DH_def is_healthy_def TVL_def DefinedT_def PredicateT_def)
  apply (rule BoolType_aux_var_split_eq_intro[of "def"])
  apply (simp_all add:typing defined usubst CondR_true CondR_false)
  apply (utp_pred_auto_tac)
done

lemma DH_TVL: "UNREST {def} Q \<Longrightarrow> `\<three>(P, Q)` is DH"
  apply (simp add:TVL_def DH_def is_healthy_def DefinedT_def PredicateT_def usubst typing defined)
  apply (utp_pred_auto_tac)
done

lemma DH_BotT: "`\<bottom>\<^sub>T` is DH"
  by (utp_pred_tac, utp_expr_tac)

lemma DH_TrueT: "`true\<^sub>T` is DH"
  by (utp_pred_tac, utp_expr_tac)

lemma DH_FalseT: "`false\<^sub>T` is DH"
  by (utp_pred_tac)

lemma DH_AndT: "\<lbrakk> P is DH; Q is DH \<rbrakk> \<Longrightarrow> `P \<and>\<^sub>T Q` is DH"
  apply (simp add: AndT_def)
  apply (rule DH_TVL)
  apply (simp add:DefinedT_def unrest typing defined)
done

lemma TVL_left:
  "`\<P>(\<three>(P, Q))` = `(P \<and> Q)[true/def]`"
  by (simp add:TVL_def PredicateT_def usubst typing defined)

lemma TVL_right:
  "`\<D>(\<three>(P, Q))` = `Q[false/def]`"
  by (utp_pred_tac, utp_expr_tac)

lemma DefinedT_BotT:
  "[\<not> \<D>(\<bottom>\<^sub>T)]"
  by (utp_pred_tac, utp_expr_tac)

lemma DefinedT_TrueT:
  "`\<D>(true\<^sub>T)`"
  by (utp_pred_tac, utp_expr_tac)

lemma DefinedT_FalseT:
  "`\<D>(false\<^sub>T)`"
  by (utp_pred_tac)

lemma TVL_extreme_point1:
  "`\<three>(true, false)` = `\<not> $def`"
  by (utp_pred_tac)

lemma TVL_extreme_point2:
  "`\<three>(false, false)` = `\<not> $def`"
  by (utp_pred_tac)

lemma AndT_left_unit:
  "P is DH \<Longrightarrow> `true\<^sub>T \<and>\<^sub>T P` = `P`"
  apply (simp add:TVL_def AndT_def DefinedT_def TrueT_def PredicateT_def)
  apply (rule BoolType_aux_var_split_eq_intro[of "def"])
  apply (simp_all add:typing defined usubst)
  apply (metis AndP_comm DH_defined_anhil DefinedT_def PredicateT_def)
done

lemma AndT_right_unit:
  "P is DH \<Longrightarrow> `P \<and>\<^sub>T true\<^sub>T` = `P`"
  apply (simp add:TVL_def AndT_def DefinedT_def TrueT_def PredicateT_def)
  apply (rule BoolType_aux_var_split_eq_intro[of "def"])
  apply (simp_all add:typing defined usubst)
  apply (metis AndP_comm DH_defined_anhil DefinedT_def PredicateT_def)
done


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
  apply (simp add:NotT_def TVL_def PredicateT_def DefinedT_def)
  apply (rule BoolType_aux_var_split_eq_intro[of "def"])
  apply (simp_all add:typing defined usubst)
  apply (utp_pred_auto_tac)
done

lemma NotT_TrueT: "`\<not>\<^sub>T true\<^sub>T` = `false\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

lemma AndT_BotT_left: "`\<bottom>\<^sub>T \<and>\<^sub>T P` = `\<bottom>\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

lemma AndT_BotT_right: "`P \<and>\<^sub>T \<bottom>\<^sub>T` = `\<bottom>\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

lemma NotT_BotT: "`\<not>\<^sub>T \<bottom>\<^sub>T` = `\<bottom>\<^sub>T`"
  by (utp_pred_tac, utp_expr_tac)

end