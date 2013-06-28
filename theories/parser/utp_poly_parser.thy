(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_poly_parser.thy                                                  *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Polymorphic Predicate Parser *}

theory utp_poly_parser
imports 
  "../core/utp_pred"
  "../core/utp_expr"
  "../core/utp_rel"
  "../poly/utp_poly_expr"
begin

nonterminal pexpr and pexprs

text {* Several of these operators come in both strongly and weakly typed varieties,
        indicated by a w subscript. Those which are strong must match the type exactly,
        whilst those which are weak just work directly on model values *}

syntax
  (* Core Expression Syntax *)
  "_pexpr_quote"        :: "pexpr \<Rightarrow> ('a, 'm) WF_PEXPRESSION" ("(1\<parallel>_\<parallel>)")
  "_pexpr_pred_quote"   :: "pexpr \<Rightarrow> 'a WF_PREDICATE" ("(1`_`)")
  "_pexprs"             :: "[pexpr, pexprs] => pexprs" ("_,/ _")
  ""                    :: "pexpr => pexprs" ("_")
  "_pexpr_brack"        :: "pexpr \<Rightarrow> pexpr" ("'(_')")
  "_pexpr_pred_var"     :: "idt \<Rightarrow> pexpr" ("(_)")
  "_pexpr_expr_var"     :: "idt \<Rightarrow> pexpr" ("@_")
  "_pexpr_evar"         :: "('a, 'm) PVAR \<Rightarrow> pexpr" ("$_")
  "_pexpr_wvar"         :: "('a, 'm) PVAR \<Rightarrow> pexpr" ("$_\<^sub>w")
  "_pexpr_subst"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> ('a, 'm) PVAR \<Rightarrow> pexpr" ("(_[_'/_])" [999,999] 1000)
  "_pexpr_prime"        :: "pexpr \<Rightarrow> pexpr" ("_\<acute>" [999] 999)

syntax
  (* Basic logical operators *)
  "_pexpr_equal"        :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "=" 50)
  "_pexpr_true"         :: "pexpr" ("true")
  "_pexpr_false"        :: "pexpr" ("false")
  "_pexpr_and"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<and>" 35)
  "_pexpr_or"           :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<or>" 35)
  "_pexpr_imp"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<Rightarrow>" 25)
  "_pexpr_iff"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<Leftrightarrow>" 25)
  "_pexpr_ref"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "\<sqsubseteq>" 25)
  "_pexpr_clos"         :: "pexpr \<Rightarrow> pexpr" ("[_]")
  "_pexpr_not"          :: "pexpr \<Rightarrow> pexpr" ("\<not> _" [40] 40)
  "_pexpr_all1"         :: "('a, 'm) PVAR \<Rightarrow> pexpr \<Rightarrow> pexpr"  ("(3\<forall> _./ _)" [0, 10] 10) 
  "_pexpr_exists1"      :: "('a, 'm) PVAR \<Rightarrow> pexpr \<Rightarrow> pexpr"  ("(3\<exists> _./ _)" [0, 10] 10) 

syntax
  (* Relational operators *)

  "_pexpr_skip"         :: "pexpr" ("II")
  "_pexpr_skipa"        :: "'VALUE VAR set \<Rightarrow> pexpr" ("II\<^bsub>_\<^esub>")
  "_pexpr_seq"          :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr ";" 36)
  "_pexpr_cond"         :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_ \<lhd> _ \<rhd> _")
  "_pexpr_assign"       :: "('a, 'm) PVAR \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_ := _" [100] 100)
  "_pexpr_wassign"      :: "'m VAR \<Rightarrow> 'm WF_EXPRESSION \<Rightarrow> pexpr" ("_ :=\<^sub>w _" [100] 100)
  "_pexpr_conv"         :: "pexpr \<Rightarrow> pexpr" ("(_\<^sup>\<smile>)" [1000] 999)
  "_pexpr_varopen"      :: "('a, 'm) PVAR \<Rightarrow> pexpr" ("var _")
  "_pexpr_varclose"     :: "('a, 'm) PVAR \<Rightarrow> pexpr" ("end _")

syntax
  (* Data Structures *)
  "_pexpr_int"          :: "int \<Rightarrow> pexpr" ("<_>")
  "_pexpr_plus"         :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "+" 65)
  "_pexpr_list"         :: "pexprs \<Rightarrow> pexpr" ("\<langle>_\<rangle>")
  "_pexpr_list_nil"     :: "pexpr" ("\<langle>\<rangle>")
  "_pexpr_list_append"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixr "^" 65)
  "_pexpr_fset"         :: "pexprs \<Rightarrow> pexpr" ("{_}")
  "_pexpr_fset_empty"   :: "pexpr" ("{}")
  "_pexpr_fset_union"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "\<union>" 65)
  "_pexpr_fset_inter"   :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" (infixl "\<inter>" 70)
  "_pexpr_fset_member"  :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(_/ \<in> _)" [51, 51] 50)
  "_pexpr_fset_nmember" :: "pexpr \<Rightarrow> pexpr \<Rightarrow> pexpr" ("(_/ \<notin> _)" [51, 51] 50)
  "_pexpr_event"        :: "NAME \<Rightarrow> pexpr \<Rightarrow> pexpr" ("_?_" 50)

translations
  (* Core Expression Syntax *)
  "_pexpr_quote e"             => "e"
  "_pexpr_pred_quote e"        == "CONST PExprP e"
  "_pexpr_pred_var p"          == "CONST PredPE p"
  "_pexpr_expr_var v"          => "v"
  "_pexpr_evar x"              == "CONST PVarPE x"
  "_pexpr_wvar x"              == "CONST WVarPE x"
  "_pexpr_brack e"             => "e"
  "_pexpr_subst e v x"         == "CONST PSubstPE e v x"
  "_pexpr_prime e"             == "CONST RenamePE e (CONST SS)"

translations
  (* Basic logical operators *)
  "_pexpr_equal e f"           == "CONST EqualPE e f"
  "_pexpr_true"                == "CONST TruePE"
  "_pexpr_false"               == "CONST FalsePE"
  "_pexpr_and p q"             == "CONST PredOp2PE (CONST AndP) p q"
  "_pexpr_or p q"              == "CONST PredOp2PE (CONST OrP) p q"
  "_pexpr_imp p q"             == "CONST PredOp2PE (CONST ImpliesP) p q"
  "_pexpr_iff p q"             == "CONST PredOp2PE (CONST IffP) p q"
  "_pexpr_ref p q"             == "CONST PredOp2PE (CONST RefP) p q"
  "_pexpr_clos p"              == "CONST PredOp1PE (CONST ClosureP) p"
  "_pexpr_not p"               == "CONST PredOp1PE (CONST NotP) p"
  "_pexpr_all1 x p"            == "CONST PredOp1PE (CONST ForallP {[x]\<^sub>*}) p"
  "_pexpr_exists1 x p"         == "CONST PredOp1PE (CONST ExistsP {[x]\<^sub>*}) p"

translations
  (* Relational operators *)
  "_pexpr_skip"                == "CONST PredPE (CONST SkipR)"
  "_pexpr_skipa vs"            == "CONST PredPE (CONST SkipRA vs)"
  "_pexpr_seq p q"             == "CONST PredOp2PE (CONST SemiR) p q"
  "_pexpr_cond p q r"          == "CONST PredOp3PE (CONST CondR) p q r"
  "_pexpr_assign x v"          == "CONST AssignRPE x v"
  "_pexpr_wassign x v"         == "CONST WAssignRPE x v"
  "_pexpr_conv p"              == "CONST PredOp1PE (CONST ConvR) p"
  "_pexpr_varopen x"           == "CONST PredPE (CONST VarOpenP [x]\<^sub>*)"
  "_pexpr_varclose x"          == "CONST PredPE (CONST VarCloseP [x]\<^sub>*)"

translations
  (* Data Structures *)
  "_pexpr_int x"               == "CONST IntPE x"
  "_pexpr_plus x y"            == "CONST PlusPE x y"
  "_pexpr_list_nil"            == "CONST NilPE"
  "_pexpr_list_append e f"     == "CONST ConcatPE e f"
  "_pexpr_list (_pexprs x xs)" == "CONST ConsPE x (_pexpr_list xs)"
  "_pexpr_list x"              == "CONST ConsPE x (CONST NilPE)"
  "_pexpr_fset (_pexprs x xs)" == "CONST FInsertPE x (_pexpr_fset xs)"
  "_pexpr_fset x"              == "CONST FInsertPE x CONST FEmptyPE"
  "_pexpr_fset_empty"          == "CONST FEmptyPE"
  "_pexpr_fset_union xs ys"    == "CONST FUnionPE xs ys"
  "_pexpr_fset_inter xs ys"    == "CONST FInterPE xs ys"
  "_pexpr_fset_member x xs"    == "CONST FMemberPE x xs"
  "_pexpr_fset_nmember x xs"   == "CONST FNotMemberPE x xs"
  "_pexpr_event n v"           == "CONST EventPE n v"

(* Some regression tests *)
term "`x \<in> {true,false} \<union> {false,true}`"
term "`($x)\<acute> = $(y\<acute>)`"
term "`p[($x)\<acute>/y\<acute>]`"

lemma "`<2> \<in> {<1>,<2>,<3>}`"
  by (utp_pred_tac)

(* w00t! refinementz rool! *)
lemma "`($x \<in> {<1>,<2>,<3>}) \<sqsubseteq> ($x = <2>)`"
  by (utp_pred_tac)

lemma "`p \<Leftrightarrow> q` = `p = q`"
  by (utp_pred_tac)

lemma "`(x = false) = (\<not> x)`"
  by (utp_pred_tac)

lemma "`\<exists> x. $x = true`"
  apply (utp_pred_auto_tac)
  apply (rule_tac x="\<B>([x]\<^sub>* :=\<^sub>b MkBool True)" in exI)
  apply (simp add:typing defined)
done

(*
lemma "x \<in> PUNDASHED \<Longrightarrow> `x := <1> ; x := $x + <1>` = `x := <2>`"
  apply (subgoal_tac "PExprE (IntPE 1) \<rhd>\<^sub>e [x]\<^sub>*")
  apply (subgoal_tac "UNREST_EXPR DASHED (PExprE (IntPE 1) :: 'a WF_EXPRESSION)")
  apply (subgoal_tac "PExprE (IntPE 2) \<rhd>\<^sub>e [x]\<^sub>*")
  apply (subgoal_tac "UNREST_EXPR DASHED (PExprE (IntPE 2) :: 'a WF_EXPRESSION)")
  apply (subgoal_tac "PExprE (PlusPE (PVarPE x) (IntPE 1)) \<rhd>\<^sub>e [x]\<^sub>*")
  apply (subgoal_tac "UNREST_EXPR DASHED (PExprE (PlusPE (PVarPE x) (IntPE 1)) :: 'a WF_EXPRESSION)")

  apply (utp_rel_tac)


  apply (simp add:evale eval closure typing defined relcomp_unfold)
  apply (auto intro:typing defined unrest)
  apply (rule)
  apply (simp add:typing defined)
*)

term "`x :=\<^sub>w v`"
term "WAssignRPE x k"
term "`($x\<^sub>w\<acute> = @v) \<and> II\<^bsub>REL_VAR - {x,x\<acute>}\<^esub>`"

lemma "`<1> + <1> = <2>`"
  by (utp_pred_tac)

lemma "\<not> `<6> = <7>`"
  by (utp_pred_tac)

term "\<parallel>\<langle>n?<5>, m?{<1>}\<rangle> ^ \<langle>\<rangle>\<parallel>"

end