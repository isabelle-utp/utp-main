(*<*)
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

abbreviation "def  \<equiv> MkBoolV ''def'' True"
(*>*)

text {* A TVL pair (Three-Valued Logic) consists of a pair of
predicates, the first of which give the true valued region of the
predicate, and second gives the defined region of the predicate. *}

definition TVL :: 
  "('a upred * 'a upred) \<Rightarrow> 'a upred" 
where "TVL \<equiv> \<lambda> (P,Q). `($def \<Rightarrow> P) \<and> (Q \<Leftrightarrow> $def)`"

text {* We then define functions to extract the first and second
elements of the TVL pair, by substituting @{term def} for
\textsf{true}, substituting @{term def} for false and negating,
respectively. *}

definition PredicateT :: "'a upred \<Rightarrow> 'a upred" where
"PredicateT P = `P[true/def]`"

definition DefinedT :: "'a upred \<Rightarrow> 'a upred" where
"DefinedT P = `\<not> P[false/def]`"

(*<*)
declare TVL_def [eval,evalp]
declare PredicateT_def [eval,evalp]
declare DefinedT_def [eval,evalp]

syntax
  "_n_upred_tvl"        :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" ("\<three>'(_, _')")
  "_n_upred_definedt"   :: "n_upred \<Rightarrow> n_upred" ("\<D>'(_')")
  "_n_upred_predicatet" :: "n_upred \<Rightarrow> n_upred" ("\<P>'(_')")

translations
  "_n_upred_tvl p q"      == "CONST TVL (p, q)"
  "_n_upred_definedt p"   == "CONST DefinedT p"
  "_n_upred_predicatet p" == "CONST PredicateT p"
(*>*)

text {* We also extend the parser with suitable syntax so that a
TVL-pair can be written as @{term "`\<three>(P, Q)`"}, the truth valuation of a
predicate can be extracted with @{term "`\<P>(P)`"} and the definedness of
a predicate can be extracted with @{term "`\<D>(P)`"}. This then allows us
to define some of the common syntax of three-valued logic. *}

definition TrueT :: "'a upred" where
"TrueT = `\<three>(true, true)`"

definition FalseT :: "'a upred" where
"FalseT = `\<three>(false, true)`"

text {* Predicates $\textsf{true}_T$ and $\textsf{false}_T$ are
both defined, and exhibit their respective truth values. *}

definition BotT :: "'a upred" where
"BotT = `\<not> $def`"

text {* Bottom (undefined) is the predicate which is never defined. *}

definition NotT :: "'a upred \<Rightarrow> 'a upred" where
"NotT P = `\<three>(\<not> \<P>(P), \<D>(P))`"

text {* Boolean not ($\neg_T P$) negates the truth valuation and
leaves the definedness as is. *}

definition AndT :: 
  "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"AndT P Q = `\<three>(\<P>(P) \<and> \<P>(Q), \<D>(P) \<and> \<D>(Q))`"

definition OrT :: 
  "'a upred \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"OrT P Q = `\<three>(\<P>(P) \<or> \<P>(Q), \<D>(P) \<and> \<D>(Q))`"

text {* Conjunction ($\wedge_T$) and disjunction $\vee_T$,
respectively, conjoin and disjoin the truth valuations of the
respective predicates, and both conjoin the definedness regions, as
both sides must be defined. *}

(*<*)
definition AllDefinedT :: "'a uvar set \<Rightarrow> 'a upred" where
"AllDefinedT xs = mkPRED {b. \<forall>x\<in>xs. \<D> (\<langle>b\<rangle>\<^sub>b x)}"

definition ExistsT :: "'a uvar set \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"ExistsT xs p = (\<exists>\<^sub>p xs. AllDefinedT xs \<and>\<^sub>p p)"

notation ExistsT ("(\<exists>\<^sub>t _ ./ _)" [0, 10] 10)

definition ForallT :: "'a uvar set \<Rightarrow> 'a upred \<Rightarrow> 'a upred" where
"ForallT xs p = (\<forall>\<^sub>p xs. AllDefinedT xs \<Rightarrow>\<^sub>p p)"

notation ForallT ("(\<forall>\<^sub>t _ ./ _)" [0, 10] 10)

definition ClosureT :: "'a upred \<Rightarrow> 'a upred" where
"ClosureT p = (\<forall>\<^sub>t VAR. p)"

declare TrueT_def  [eval,evalpp]
declare FalseT_def [eval,evalpp]
declare BotT_def [eval,evalpp]
declare NotT_def [eval,evalpp]
declare OrT_def [eval,evalpp]
declare AndT_def [eval,evalpp]

text {* DH for a given TVL (P, Q) ensures that P is true only when Q is also true,
        i.e. a true valuation must also be a defined evaluation. *}

definition DH :: "'a upred \<Rightarrow> 'a upred" where
"DH(P) = `P \<and> (\<D>(P) \<sqsubseteq> \<P>(P))`"

declare DH_def [eval,evalp]

syntax
  "_n_upred_truet"    :: "n_upred" ("true\<^sub>T")
  "_n_upred_falset"   :: "n_upred" ("false\<^sub>T")
  "_n_upred_bott"     :: "n_upred" ("\<bottom>\<^sub>T")
  "_n_upred_nott"     :: "n_upred \<Rightarrow> n_upred" ("\<not>\<^sub>T _" [40] 40)
  "_n_upred_andt"     :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<and>\<^sub>T" 35)
  "_n_upred_ort"      :: "n_upred \<Rightarrow> n_upred \<Rightarrow> n_upred" (infixr "\<or>\<^sub>T" 35)
  "_n_upred_clost"    :: "n_upred \<Rightarrow> n_upred" ("[_]\<^sub>T")
  "_n_upred_dh"       :: "n_upred \<Rightarrow> n_upred" ("DH'(_')")

translations
  "_n_upred_truet"    == "CONST TrueT"
  "_n_upred_falset"   == "CONST FalseT"
  "_n_upred_bott"     == "CONST BotT"
  "_n_upred_nott p"   == "CONST NotT p"
  "_n_upred_andt p q" == "CONST AndT p q"
  "_n_upred_ort p q"  == "CONST OrT p q"
  "_n_upred_clost p"  == "CONST ClosureT p"
  "_n_upred_dh p"     == "CONST DH p"

lemma TrueT_unfold:
  "`true\<^sub>T` = `$def`"
  by (utp_poly_tac)

lemma FalseT_unfold:
  "`false\<^sub>T` = `false`"
  by (utp_poly_tac)

lemma DH_idem: 
  "DH (DH P) = DH P"
  by (utp_pred_auto_tac)

lemma DH_refine: "P is DH \<Longrightarrow> `\<D>(P) \<sqsubseteq> \<P>(P)`"
  by (utp_pred_auto_tac)

lemma DH_defined_anhil: "P is DH \<Longrightarrow> `\<D>(P) \<and> \<P>(P)` = `\<P>(P)`"
  by (utp_pred_auto_tac)

lemma TVL_inject: "P is DH \<Longrightarrow> `\<three>(\<P>(P), \<D>(P))` = P"
  apply (simp add:DH_def is_healthy_def TVL_def DefinedT_def PredicateT_def)
  apply (rule BoolType_aux_var_split_eq_intro[of "def\<down>"])
  apply (simp_all add:typing defined usubst CondR_true CondR_false erasure)
  apply (utp_pred_auto_tac)
done

lemma DH_TVL: "UNREST {def\<down>} Q \<Longrightarrow> `\<three>(P, Q)` is DH"
  apply (simp add:TVL_def DH_def is_healthy_def DefinedT_def PredicateT_def usubst typing defined)
  apply (utp_pred_auto_tac)
done

lemma DH_BotT: "`\<bottom>\<^sub>T` is DH"
  apply (utp_poly_tac)
  apply (metis UTypedef.axm4 UTypedef_bool)
done

lemma DH_TrueT: "`true\<^sub>T` is DH"
  apply (utp_poly_tac)
  apply (metis UTypedef.axm4 UTypedef_bool)
done

lemma DH_FalseT: "`false\<^sub>T` is DH"
  by (utp_poly_tac)

lemma DH_AndT: "\<lbrakk> P is DH; Q is DH \<rbrakk> \<Longrightarrow> `P \<and>\<^sub>T Q` is DH"
  apply (simp add: AndT_def)
  apply (rule DH_TVL)
  apply (simp add:DefinedT_def unrest typing defined)
done

lemma TVL_left:
  "`\<P>(\<three>(P, Q))` = `(P \<and> Q)[true/def]`"
  apply (utp_poly_tac)
  apply (metis UTypedef.axm4 UTypedef_bool)
done

lemma TVL_right:
  "`\<D>(\<three>(P, Q))` = `Q[false/def]`"
  apply (utp_poly_tac)
  apply (metis UTypedef.axm4 UTypedef_bool)
done

lemma DefinedT_BotT:
  "[\<not> \<D>(\<bottom>\<^sub>T)]"
  apply (utp_poly_tac)
  apply (metis UTypedef.axm4 UTypedef_bool)
done

lemma DefinedT_TrueT:
  "`\<D>(true\<^sub>T)`"
  apply (utp_poly_tac)
  apply (metis UTypedef.axm4 UTypedef_bool)
done

lemma DefinedT_FalseT:
  "`\<D>(false\<^sub>T)`"
  by (utp_poly_tac)

lemma TVL_extreme_point1:
  "`\<three>(true, false)` = `\<not> $def`"
  by (utp_poly_tac)

lemma TVL_extreme_point2:
  "`\<three>(false, false)` = `\<not> $def`"
  by (utp_poly_tac)

lemma AndT_left_unit:
  "P is DH \<Longrightarrow> `true\<^sub>T \<and>\<^sub>T P` = `P`"
  apply (utp_poly_tac)
  apply (metis (full_types) UTypedef.axm4 UTypedef_bool binding_upd_drop_ty pvaux_MkPVAR)
done

lemma AndT_right_unit:
  "P is DH \<Longrightarrow> `P \<and>\<^sub>T true\<^sub>T` = `P`"
  apply (utp_poly_tac)
  apply (metis (full_types) UTypedef.axm4 UTypedef_bool binding_upd_drop_ty pvaux_MkPVAR)
done
(*>*)

lemma TVL_unrest [unrest]:
  "\<lbrakk> vs \<sharp> p; vs \<sharp> q; def\<down> \<notin> vs \<rbrakk> \<Longrightarrow> vs \<sharp> TVL (p, q)"
  by (simp add:TVL_def unrest)

lemma TrueT_unrest [unrest]:
  "def\<down> \<notin> vs \<Longrightarrow> vs \<sharp> TrueT"
  by (simp add:TrueT_def unrest)

lemma FalseT_unrest [unrest]:
  "def\<down> \<notin> vs \<Longrightarrow> vs \<sharp> FalseT"
  by (simp add:FalseT_def unrest)

text {* We can then prove some simple properties about the new
operators which we've defined, such as as that both conjunction and
disjunction are commutative and associative. *}

lemma AndT_assoc:
  "`(P \<and>\<^sub>T Q) \<and>\<^sub>T R` = `P \<and>\<^sub>T Q \<and>\<^sub>T R`"
  apply (utp_poly_tac)
  apply (auto simp add: inju)
done

lemma AndT_commute: 
  "`P \<and>\<^sub>T Q` = `Q \<and>\<^sub>T P`"
  by (utp_poly_auto_tac)

lemma OrT_assoc:
  "`(P \<or>\<^sub>T Q) \<or>\<^sub>T R` = `P \<or>\<^sub>T Q \<or>\<^sub>T R`"
  apply (utp_poly_tac)
  apply (auto simp add: inju)
done

lemma OrT_commute:
  "`P \<or>\<^sub>T Q` = `Q \<or>\<^sub>T P`"
  by (utp_poly_auto_tac)

(*<*)
lemma NotT_double: "P is DH \<Longrightarrow> `\<not>\<^sub>T \<not>\<^sub>T P` = `P`"
  apply (utp_poly_tac)
  apply (metis (full_types) UTypedef.axm4 UTypedef_bool binding_upd_drop_ty pvaux_MkPVAR)
done
(*>*)

lemma NotT_TrueT: "`\<not>\<^sub>T true\<^sub>T` = `false\<^sub>T`"
  apply (utp_poly_tac)
  apply (simp add: inju)
done

lemma AndT_BotT_left: "`\<bottom>\<^sub>T \<and>\<^sub>T P` = `\<bottom>\<^sub>T`"
  apply (utp_poly_tac)
  apply (simp add: inju)
done

lemma AndT_BotT_right: "`P \<and>\<^sub>T \<bottom>\<^sub>T` = `\<bottom>\<^sub>T`"
  apply (utp_poly_tac)
  apply (simp add: inju)
done

lemma NotT_BotT: "`\<not>\<^sub>T \<bottom>\<^sub>T` = `\<bottom>\<^sub>T`"
  apply (utp_poly_tac)
  apply (simp add: inju)
done

(*<*)
end
(*>*)