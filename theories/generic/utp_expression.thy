(******************************************************************************)
(* Project: Deep Mechanisation of the UTP                                     *)
(* File: utp/generic/utp_expression.thy                                       *)
(* Author: Simon Foster and Frank Zeyda, University of York                   *)
(******************************************************************************)

header {* Generic Expressions *}

theory utp_expression
imports "../utp_types" utp_gen_pred utp_eval_tactic utp_value2
begin

ML {*
  structure TypeThm =
    Named_Thms (val name = @{binding "type"} val description = "typing rules");
*}

setup {* TypeThm.setup *}

ML {*
  structure DefinedThm =
    Named_Thms (val name = @{binding "defined"} val description = "definedness rules");
*}

setup {* DefinedThm.setup *}

type_synonym ('VALUE, 'TYPE) BINDING_MAP =
  "('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE"

type_synonym ('VALUE, 'TYPE) EXPRESSION =
  "('VALUE, 'TYPE) BINDING_MAP \<times> 'TYPE"

type_synonym ('VALUE, 'TYPE) ALPHA_EXPRESSION =
  "('TYPE ALPHABET) \<times> ('VALUE, 'TYPE) EXPRESSION"

locale GEN_EXPR = GEN_PRED where type_rel = type_rel + 
                  BASIC_VALUE where type_rel = type_rel
  for type_rel :: "'VALUE \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":" 50)
begin

abbreviation expr_body :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) BINDING_MAP" ("\<beta>e") where
"expr_body x \<equiv> fst (snd x)"

abbreviation expr_eval :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE" ("_<_>") where
"e<b> \<equiv> expr_body e b"

abbreviation expr_type :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 'TYPE" where
"expr_type x \<equiv> snd (snd x)"

notation expr_type ("\<tau>e")

abbreviation expr_dom :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) BINDING set" where
"expr_dom e \<equiv> fdom (expr_body e)"

abbreviation expr_has_type :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 'TYPE \<Rightarrow> bool" (infix ":e:" 50) where
"expr_has_type e t \<equiv> (expr_type e = t)"

abbreviation expr_alpha :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('TYPE ALPHABET)" where
"expr_alpha \<equiv> fst"

notation expr_alpha ("\<alpha>e")

definition var_dom :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 'TYPE VAR \<Rightarrow> 'VALUE set" where
"var_dom e x = {f x | f . f \<in> expr_dom e}"

subsection {* Well-defined bindings *}
definition WD_BINDING :: "'TYPE VAR set \<Rightarrow> ('VALUE, 'TYPE) BINDING_SET" where
"WD_BINDING vs = {b . b \<in> WF_BINDING \<and> (\<forall> v \<in> vs. b v \<noteq> \<bottom>)}"

subsection {* Expressions *}

text {* We require expressions to be defined only for well formed bindings. 
        We also don't allow dependent types at this point (though they could be fun...).
     *}
definition WF_BINDING_MAP :: "('TYPE ALPHABET) \<Rightarrow> 'TYPE \<Rightarrow> ('VALUE, 'TYPE) BINDING_MAP set" where
"WF_BINDING_MAP a t \<equiv> {bm. fdom bm \<subseteq> WF_BINDING
                         \<and> (\<forall> v \<in> fran bm. v : t)
                         \<and> (\<forall> b1 \<in> WF_BINDING. \<forall> b2 \<in> WF_BINDING. 
                              b1 \<cong> b2 on a \<longrightarrow> bm b1 = bm b2)}"

definition WF_ALPHA_EXPR :: "('VALUE, 'TYPE) ALPHA_EXPRESSION set" where
"WF_ALPHA_EXPR \<equiv> {e. \<alpha>e e \<in> WF_ALPHABET \<and> \<beta>e e \<in> WF_BINDING_MAP (\<alpha>e e) (\<tau>e e)}"

(*
definition wfexpr_body :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> (('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE)" ("\<beta>e") where
"x \<in> WF_ALPHA_EXPR \<longrightarrow> wfexpr_body x v = the (expr_body x v)"
*)

(*
abbreviation wfe :: "('VALUE, 'TYPE) BINDING set \<Rightarrow> 'TYPE \<Rightarrow> (('VALUE, 'TYPE) BINDING \<Rightarrow> 'VALUE) \<Rightarrow> ('VALUE, 'TYPE) BINDING_MAP" where
"wfe bs t f \<equiv> \<lambda> b. if (b \<in> bs) then Some (coerce t (f b)) else None"
*)

(*
lemma wfexpr_binding_set[binding]: "bm \<in> WF_BINDING_MAP a t \<Longrightarrow> fdom bm \<in> WF_BINDING_SET a"
  by (auto simp add:WF_BINDING_SET_def WF_BINDING_MAP_def dom_def)
*)

abbreviation wfe :: "('VALUE, 'TYPE) BINDING_MAP \<Rightarrow> ('VALUE, 'TYPE) BINDING_MAP" where
"wfe f \<equiv> \<lambda>b. if (b \<in> WF_BINDING) then f b else \<bottom>"

subsection {* Basic Properties *}

lemma WF_ALPHA_EXPR_intro[intro]: 
"\<lbrakk> \<alpha>e e \<in> WF_ALPHABET; expr_dom e \<subseteq> WF_BINDING; \<forall>v \<in> fran (\<beta>e e). v : \<tau>e e; 
  (\<forall> b1 \<in> WF_BINDING. \<forall> b2 \<in> WF_BINDING. 
     b1 \<cong> b2 on (\<alpha>e e) \<longrightarrow> expr_body e b1 = expr_body e b2) \<rbrakk> \<Longrightarrow>
   e \<in> WF_ALPHA_EXPR"
  by (auto simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)

lemma wfexpr_binding_set[binding]: "bm \<in> WF_BINDING_MAP a t \<Longrightarrow> fdom bm \<in> WF_BINDING_SET a"
  by (auto simp add:WF_BINDING_SET_def WF_BINDING_MAP_def fdom_def dom_def to_map_def)

lemma wfexpr_wfbinding[binding]: "\<lbrakk> e \<in> WF_ALPHA_EXPR; b \<in> expr_dom e \<rbrakk>
                                \<Longrightarrow> b \<in> WF_BINDING"
  by (auto simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)

lemma wfexpr_uclosed[binding]: "\<lbrakk> e \<in> WF_ALPHA_EXPR; b1 \<in> expr_dom e
                                ; b2 \<in> WF_BINDING; b1 \<cong> b2 on \<alpha>e e \<rbrakk> 
                                \<Longrightarrow> b2 \<in> expr_dom e"
  by (auto simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def fdom_def dom_def to_map_def)

lemma wfexpr_binding[binding]: "\<lbrakk> e \<in> WF_ALPHA_EXPR; b1 \<in> WF_BINDING; b2 \<in> WF_BINDING
                                ; b1 \<cong> b2 on \<alpha>e e \<rbrakk> \<Longrightarrow> \<beta>e e b1 = \<beta>e e b2"
  by (auto simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)

lemma wfexpr_type[type]: 
  "\<lbrakk> e \<in> WF_ALPHA_EXPR; e :e: t; b \<in> expr_dom e \<rbrakk> \<Longrightarrow> 
   e<b> : t"
  apply (auto simp add:fran_def ran_def to_map_def WF_ALPHA_EXPR_def WF_BINDING_MAP_def WF_BINDING_SET_def)
  apply (metis MkBot_type)
done

subsection {* Operators *}

definition DefinedP :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("\<D>") where
"\<D>(e) = (\<alpha>e e, expr_dom e)"

definition BotE :: "'TYPE ALPHABET \<Rightarrow> 'TYPE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" ("\<bottom>e") where
"\<bottom>e a t = (a, fempty, t)"

definition VarE :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"VarE v \<equiv> ({v}, wfe (\<lambda> b. b v), var_type v)"

(* Should this definition using the definite description operator or should we be
   able to infer a type? *)
definition LitE :: "'VALUE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"LitE v \<equiv> ({}, (wfe (\<lambda> b. v), SOME t. v : t))"

definition TrueE :: "('VALUE, 'TYPE) ALPHA_EXPRESSION" ("true") where
"TrueE \<equiv> LitE (MkBool True)"

definition FalseE :: "('VALUE, 'TYPE) ALPHA_EXPRESSION" ("false") where
"FalseE \<equiv> LitE (MkBool False)"

definition PredE :: "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow> PredE p = (\<alpha> p, wfe (\<lambda> b. (MkBool (b \<in> \<beta> p))), BoolType)"

definition LamE :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"e \<in> WF_ALPHA_EXPR \<longrightarrow> 
 LamE x e = (\<alpha>e e - {x}, 
             (\<lambda> b. if (b \<in> WF_BINDING)
                      then (MkFunc (type x) (\<tau>e e) (\<lambda> v. \<beta>e e (b(x := v))))
                      else \<bottom>)
            , (type x) =p\<Rightarrow> (\<tau>e e))"

definition FunE :: "('VALUE \<Rightarrow> 'VALUE) \<Rightarrow> 'TYPE \<Rightarrow> 'TYPE \<Rightarrow>
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"FunE f a b \<equiv> ({}, wfe (\<lambda>v. MkFunc a b f), a =p\<Rightarrow> b)"

(* These functions for the time being are assumed to be closed, but this should change *)

(*
definition UopE :: "('VALUE \<Rightarrow> 'VALUE) \<Rightarrow>
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"UopE f x = (\<alpha>e x, (\<lambda> b. Option.map f (expr_body x b), expr_type x))"

definition BopE :: "('VALUE \<Rightarrow> 'VALUE \<Rightarrow> 'VALUE) \<Rightarrow>
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow>
                    ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"BopE f x y = (\<alpha>e x \<union> \<alpha>e y, (\<lambda> b. case (expr_body x b,expr_body y b) 
                                    of (Some a,Some b) \<Rightarrow> Some (f a b)
                                       | _ \<Rightarrow> None), expr_type x)"
*)


(* We probably want some extra provisos to ensure type-correctness here *)
definition AppE :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" where
"f \<in> WF_ALPHA_EXPR \<and> v \<in> WF_ALPHA_EXPR \<longrightarrow> 
AppE f v = (\<alpha>e f \<union> \<alpha>e v, 
            \<lambda> b. if (b \<in> expr_dom f \<inter> expr_dom v)
                    then (DestFunc f<b> v<b>)
                    else \<bottom>,
            out_type (\<tau>e f))"

subsection {* Predicates *}

text {* We conflate undefinedness and false here. Is this adequate? *}
definition ExprP :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"e :e: \<bool> \<longrightarrow> 
 ExprP e = (\<alpha>e e, {b \<in> fdom (\<beta>e e). (DestBool (e<b>) = True)})"

abbreviation VarP ::  "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("&_") where
"VarP v \<equiv> ExprP (VarE v)"

definition EqualP :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"e \<in> WF_ALPHA_EXPR \<and> f \<in> WF_ALPHA_EXPR \<longrightarrow> 
 EqualP e f = (\<alpha>e e \<union> \<alpha>e f, {b. b \<in> expr_dom e \<inter> expr_dom f \<and> (e<b> = f<b>)})"

notation EqualP (infixr "==p" 150)

abbreviation EqualVP :: "'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" where
"EqualVP v e \<equiv> EqualP (VarE v) e"

notation EqualVP (infixr "=p" 150)

text {* Coarse substitution *}
definition SubstP :: "('VALUE, 'TYPE) ALPHA_PREDICATE \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_PREDICATE" ("_[_|_]" [200]) where
"x \<notin> \<alpha>e e \<and> e :e: type x \<longrightarrow> SubstP p e x = (\<exists>-p {x} . p \<and>p (x =p e))"

definition SubstE :: "('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION \<Rightarrow> 'TYPE VAR \<Rightarrow> ('VALUE, 'TYPE) ALPHA_EXPRESSION" ("_[_|_]" [200]) where
"x \<notin> \<alpha>e v \<and> v :e: type x \<longrightarrow> SubstE e v x = 
  ((\<alpha>e e \<union> \<alpha>e v) - {x}, 
   \<lambda> b. if (b \<in> expr_dom v) 
        then \<beta>e e (b(x := v<b>))
        else \<bottom>,
   \<tau>e e)"

subsubsection {* Domain Theorems *}

lemma VarE_domain: "expr_dom (VarE x) = WD_BINDING {x}"
  apply (auto simp add:VarE_def fdom_def WD_BINDING_def to_map_def)
  apply (metis option.simps(2))
done

lemma LamE_domain: "e \<in> WF_ALPHA_EXPR \<Longrightarrow> expr_dom (LamE x e) = WF_BINDING"
  by (simp add:fdom_def LamE_def to_map_def dom_def)

lemma AppE_domain: 
"\<lbrakk> f \<in> WF_ALPHA_EXPR; v \<in> WF_ALPHA_EXPR \<rbrakk> \<Longrightarrow> 
 expr_dom (AppE f v) = {b. b \<in> (expr_dom f \<inter> expr_dom v) \<and> v<b> \<in> fdom (DestFunc f<b>) }"
  by (auto simp add:AppE_def dom_def fdom_def to_map_def)

lemma SubstE_domain:
"\<lbrakk> p \<in> WF_ALPHA_EXPR; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e; e :e: type x \<rbrakk> \<Longrightarrow>
 expr_dom(p[e|x]) = {b. b \<in> expr_dom e \<and> b(x := e<b>) \<in> expr_dom p}"
  by (auto simp add:SubstE_def dom_def fdom_def to_map_def)

subsubsection {* Closure Theorems *}

lemma DefinedP_closure[closure]:
"e \<in> WF_ALPHA_EXPR \<Longrightarrow> \<D>(e) \<in> WF_ALPHA_PREDICATE"
  by (auto intro: wfexpr_binding_set simp add:DefinedP_def WF_ALPHA_PREDICATE_def WF_ALPHA_EXPR_def)

lemma ExprP_closure[closure]:
"\<lbrakk> e \<in> WF_ALPHA_EXPR; e :e: BoolType \<rbrakk> \<Longrightarrow> 
 ExprP e \<in> WF_ALPHA_PREDICATE"
  apply (auto simp add: ExprP_def)
  apply (simp add:WF_BINDING_SET_def WF_ALPHA_PREDICATE_def)
  apply (auto)
  apply (simp add:WF_ALPHA_EXPR_def)
  apply (force simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def dom_def)
  apply (force simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def dom_def fdom_def to_map_def)
  apply (simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def dom_def)
  apply (auto)
done

lemma VarE_closure[closure]:
"VarE v \<in> WF_ALPHA_EXPR"
  apply (simp add:VarE_def)
  apply (simp add:WF_ALPHA_EXPR_def alpha_closure)
  apply (simp add:WF_BINDING_MAP_def)
  apply (auto simp add:fdom_def fran_def to_map_def)
  apply (metis not_Some_eq)
  apply (simp add:ran_def)
  apply (auto simp add:WF_BINDING_def)
  apply (smt MkBot_type option.inject option.simps(3))
  apply (simp add:beta_equiv_def)
done

lemma VarP_closure[closure]:
"type v = BoolType \<Longrightarrow> VarP v \<in> WF_ALPHA_PREDICATE"
  by (intro closure, simp add:VarE_def)

lemma LitE_closure[closure]:
assumes "v : t"
shows "LitE v \<in> WF_ALPHA_EXPR"
proof -
(*  obtain t where "v : t" by (metis type_rel_total) *)
  from assms have "op : v (Eps (op : v))"
    by (auto intro:someI)

  thus ?thesis
    apply (auto simp add:LitE_def alpha_closure WF_ALPHA_EXPR_def WF_BINDING_MAP_def WF_BINDING_SET_def fdom_def to_map_def)
    apply (metis not_Some_eq)
    apply (simp add:fran_def ran_def to_map_def)
    apply (metis not_Some_eq option.inject)
  done
qed

lemma EqualP_closure[closure]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR \<rbrakk> \<Longrightarrow>
 e ==p f \<in> WF_ALPHA_PREDICATE"
  apply (simp add:EqualP_def WF_ALPHA_PREDICATE_def WF_BINDING_SET_def)
  apply (simp add:alpha_closure var beta_equiv_union)
  apply (auto)
  apply (simp add:alpha_closure WF_ALPHA_EXPR_def)
  apply (force simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (metis (no_types) domD domI wfexpr_uclosed)
  apply (metis (no_types) domD domI wfexpr_uclosed)
  apply (metis (lifting) domI wfexpr_binding wfexpr_wfbinding)
done

lemma EqualVP_closure[closure]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e \<rbrakk> \<Longrightarrow>
 x =p e \<in> WF_ALPHA_PREDICATE"
  by (simp add:closure)

lemma SubstP_closure[closure]:
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e; e :e: type x \<rbrakk> \<Longrightarrow>
 p[e|x] \<in> WF_ALPHA_PREDICATE"
  by (simp add:SubstP_def closure alpha_closure)

lemma SubstE_closure[closure]:
"\<lbrakk> p \<in> WF_ALPHA_EXPR; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e; e :e: type x \<rbrakk> \<Longrightarrow>
 p[e|x] \<in> WF_ALPHA_EXPR"
  apply (rule WF_ALPHA_EXPR_intro)
  apply (simp add:SubstE_def closure alpha_closure WF_ALPHA_EXPR_def)
  apply (simp add:SubstE_def dom_def WF_ALPHA_EXPR_def WF_BINDING_MAP_def fdom_def to_map_def)
  apply (force)
  apply (simp add:SubstE_def ran_def fran_def to_map_def WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (auto)
  apply metis
  apply (subgoal_tac "\<beta>e e b1 = \<beta>e e b2")
  apply (simp add:SubstE_def ran_def fran_def to_map_def)
  apply (safe)
  apply (rule wfexpr_binding)
  apply (simp)
  apply (blast intro: binding type)+
  apply (subgoal_tac "e<b1> = e<b2>")
  apply (simp add:beta_equiv_def)
  apply (force)
  apply (simp add:fdom_def dom_def to_map_def)
  apply (metis not_Some_eq)
  apply (simp add:fdom_def dom_def to_map_def)
  apply (metis not_Some_eq)
  apply (rule wfexpr_binding)
  apply (simp_all)
  apply (simp add:beta_equiv_def SubstE_def)
  apply (force)
done

lemma TrueE_closure[closure]:
"true \<in> WF_ALPHA_EXPR"
  apply (simp add:TrueE_def closure alpha_closure)
  apply (metis LitE_closure MkBool_type)
done

lemma FalseE_closure[closure]:
"false \<in> WF_ALPHA_EXPR"
  apply (simp add:FalseE_def closure alpha_closure)
  apply (metis LitE_closure MkBool_type)
done

lemma elseNone [dest]: "(if e then f else None) = Some x \<Longrightarrow> e \<and> f = Some x"
  by (case_tac e, auto)

lemma PredE_closure[closure]:
"p \<in> WF_ALPHA_PREDICATE \<Longrightarrow> PredE p \<in> WF_ALPHA_EXPR"
  apply (simp only:PredE_def closure alpha_closure WF_ALPHA_PREDICATE_def WF_ALPHA_EXPR_def WF_BINDING_SET_def)
  apply (simp add:WF_BINDING_MAP_def WF_BINDING_SET_def fdom_def to_map_def fran_def)
  apply (safe)
  apply (metis option.simps(3))
  apply (simp add:ran_def)
  apply (safe)
  apply (smt MkBool_type fst_conv option.inject option.simps(2) snd_conv)
  apply (rule_tac f="MkBool" in cong)
  apply (simp)
  apply (rule iffI)
  apply (force)
  apply (metis beta_equiv_comm)
done

lemma LamE_closure[closure]: 
  assumes "e \<in> WF_ALPHA_EXPR" "|type x| \<le> FuncMaxCard" "|\<tau>e e| \<le> FuncMaxCard"
  shows "LamE x e \<in> WF_ALPHA_EXPR"
proof 
  from assms show "\<alpha>e (LamE x e) \<in> WF_ALPHABET"
    by (simp add:LamE_def alpha_closure WF_ALPHA_EXPR_def)

next

  from assms show "expr_dom (LamE x e) \<subseteq> WF_BINDING"
    by (auto simp add:LamE_domain WF_ALPHA_EXPR_def WF_BINDING_MAP_def LamE_def ran_def fran_def fdom_def to_map_def)
  
  from assms show "\<forall>v\<in>fran (\<beta>e (LamE x e)). v : \<tau>e (LamE x e)"
    apply (auto simp add:LamE_def ran_def fran_def to_map_def)
    apply (rule MkFunc_type)
    apply (unfold FuncSort_def')
    apply (auto)
    apply (simp add:fdom_def fran_def to_map_def dom_def)
    apply (metis (mono_tags) bindings_assign_type domI fdom_def to_map_def wfexpr_wfbinding)
    apply (simp add: fran_def to_map_def ran_def)
    apply (auto)
    apply (smt domIff fdom_def option.inject option.simps(2) to_map_def wfexpr_type)
  done

(*
  from assms show "\<forall>v\<in>ran (\<beta>e (LamE x e)). v : \<tau>e (LamE x e)"
    apply (auto intro!:MkPFunc_type simp add:LamE_def ran_def)
    apply (auto simp add:carrier_def WF_ALPHA_EXPR_def WF_BINDING_MAP_def ran_def restrict_map_def)
  done
*)
 
  show "\<forall>b1\<in>WF_BINDING.\<forall>b2\<in>WF_BINDING. 
        b1 \<cong> b2 on \<alpha>e (LamE x e) \<longrightarrow> \<beta>e (LamE x e) b1 = \<beta>e (LamE x e) b2"
  proof clarify
    fix b1 b2
    assume assms2: "b1 \<in> WF_BINDING" "b2 \<in> WF_BINDING" "b1 \<cong> b2 on \<alpha>e (LamE x e)"

    with assms show "\<beta>e (LamE x e) b1 = \<beta>e (LamE x e) b2"
      apply (unfold LamE_def)
  apply (auto)
  apply (rule_tac f="MkFunc (type x) (\<tau>e e)" and g="MkFunc (type x) (\<tau>e e)" in cong)
  apply (simp)
  apply (rule ext)
  apply (case_tac "\<not> (v : type x)")
  apply (simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (subgoal_tac "b1(x := v) \<notin> expr_dom e")
  apply (subgoal_tac "b2(x := v) \<notin> expr_dom e")
  apply (simp add:fdom_def dom_def to_map_def)
  apply (smt not_Some_eq)
  apply (subgoal_tac "b2(x := v) \<notin> WF_BINDING")
  apply (force)
  apply (simp add:WF_BINDING_def)
  apply (subgoal_tac "b1(x := v) \<notin> WF_BINDING")
  apply (force)
  apply (simp add:WF_BINDING_def)
  apply (simp)
  apply (simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (subgoal_tac "b1(x := v) \<in> WF_BINDING")
  apply (subgoal_tac "b2(x := v) \<in> WF_BINDING")
  apply (subgoal_tac "b1(x := v) \<cong> b2(x := v) on \<alpha>e e")
  apply (simp)
  apply (simp only:beta_equiv_def)
  apply (metis Diff_iff fun_upd_apply singletonE)
  apply (simp add:bindings_assign)
  apply (simp add:bindings_assign)
done
qed
qed

lemma AppE_closure[closure]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR; e :e: a =p\<Rightarrow> b; f :e: a \<rbrakk> \<Longrightarrow>
 AppE e f \<in> WF_ALPHA_EXPR"
  apply (rule WF_ALPHA_EXPR_intro)
  apply (simp add:AppE_def)
  apply (simp add:WF_ALPHA_EXPR_def alpha_closure)
  apply (auto)[1]
  apply (rule_tac e="e" in wfexpr_wfbinding)
  apply simp
  apply (auto simp add:dom_def fdom_def to_map_def AppE_def)[1]
  apply (simp add:AppE_def ran_def)
  apply (simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (auto)
  sorry
(*

  apply (metis (hide_lams, mono_tags) AppPFunc_type domI ranI the.simps) 
  apply (subgoal_tac "\<beta>e e b1 = \<beta>e e b2")
  apply (subgoal_tac "\<beta>e f b1 = \<beta>e f b2")
  apply (simp add: AppE_def)
  apply (auto)
  apply (metis beta_equiv_union domI the.simps wfexpr_binding)
  apply (metis (full_types) beta_equiv_union domI wfexpr_binding)
  apply (subgoal_tac "b1 \<cong> b2 on \<alpha>e f")
  apply (simp add: WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (simp add:AppE_def beta_equiv_union)
  apply (subgoal_tac "b1 \<cong> b2 on \<alpha>e e")
  apply (simp add: WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (simp add:AppE_def beta_equiv_union)
done
*)

(*
lemma FunE_closure[closure]: 
"\<lbrakk> ran (f |` carrier a) \<subseteq> carrier b \<rbrakk> \<Longrightarrow> FunE f a b \<in> WF_ALPHA_EXPR"
  by (auto simp add:FunE_def WF_ALPHA_EXPR_def WF_BINDING_MAP_def alpha_closure MkPFunc_type ran_def)
*)

lemma FunE_closure[closure]: 
"\<lbrakk> fdom f \<subseteq> carrier a; fran f \<subseteq> carrier b; |a| \<le> FuncMaxCard; |b| \<le> FuncMaxCard \<rbrakk> \<Longrightarrow> FunE f a b \<in> WF_ALPHA_EXPR"
  apply (subgoal_tac "f \<in> FuncSort a b")
  apply (simp add:FunE_def WF_ALPHA_EXPR_def alpha_closure WF_BINDING_MAP_def fdom_def to_map_def)
  apply (auto)
  apply (metis (lifting) domI domIff)
  apply (simp add:fran_def to_map_def ran_def)
  apply (auto)
  apply (case_tac "aa \<in> WF_BINDING")
  apply (auto)
  apply (rule MkFunc_type)
  apply (simp)
  apply (simp add:FuncSort_def')
done

subsubsection {* Alphabet Theorems *}

lemma VarE_alphabet [alphabet]: "\<alpha>e (VarE v) = {v}"
  by (simp add:VarE_def)

lemma EqualP_alphabet [alphabet]: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR \<rbrakk> \<Longrightarrow> \<alpha> (e ==p f) = \<alpha>e e \<union> \<alpha>e f"
  by (simp add:EqualP_def)

lemma LitE_alphabet [alphabet]:
"\<alpha>e (LitE v) = {}" by (simp add:LitE_def)

lemma ExprP_alphabet [alphabet]:
"\<lbrakk> e \<in> WF_ALPHA_EXPR; e :e: BoolType \<rbrakk> \<Longrightarrow> \<alpha> (ExprP e) = \<alpha>e e"
  by (simp add:ExprP_def)

lemma VarP_alphabet [alphabet]: "type v = BoolType \<Longrightarrow> \<alpha> (& v) = {v}"
  apply(subgoal_tac "(VarE v) :e: BoolType")
  apply(simp add:alphabet closure alpha_closure)
  apply(simp add:VarE_def)
done

lemma SubstP_alphabet [alphabet]:
"\<lbrakk> p \<in> WF_ALPHA_PREDICATE; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e; e :e: type x \<rbrakk> \<Longrightarrow> 
 \<alpha> (p[e|x]) = (\<alpha> p \<union> \<alpha>e e) - {x}"
  by (simp add:SubstP_def alphabet closure alpha_closure)

lemma SubstE_alphabet [alphabet]:
"\<lbrakk> p \<in> WF_ALPHA_EXPR; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e; e :e: type x \<rbrakk> \<Longrightarrow> 
 \<alpha>e (p[e|x]) = (\<alpha>e p \<union> \<alpha>e e) - {x}"
  by (simp add:SubstE_def)

lemma TrueE_alphabet [alphabet]:
"\<alpha>e true = {}" by (simp add:TrueE_def alphabet)

lemma FalseE_alphabet [alphabet]:
"\<alpha>e false = {}" by (simp add:FalseE_def alphabet)

lemma PredE_alphabet [alphabet]:
"p \<in> WF_ALPHA_PREDICATE \<longrightarrow> \<alpha>e (PredE p) = \<alpha> p"
  by (simp add:PredE_def)

lemma LamE_alphabet [alphabet]:
"e \<in> WF_ALPHA_EXPR \<Longrightarrow> \<alpha>e (LamE x e) = \<alpha>e e - {x}"
  by (simp add:LamE_def)

lemma AppE_alphabet [alphabet]:
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR \<rbrakk> \<Longrightarrow> \<alpha>e (AppE e f) = \<alpha>e e \<union> \<alpha>e f"
  by (simp add:AppE_def)

subsubsection {* Binding Theorems *}

lemma VarE_binding[simp]: "b \<in> WF_BINDING \<Longrightarrow> (VarE x)<b> = b x"
  by (simp add:VarE_def)
  
subsubsection {* Typing Theorems *}

lemma VarE_type[type]: "(VarE v) :e: type v"
  by (simp add:VarE_def)

lemma AppE_type[type]: 
  "\<lbrakk> f \<in> WF_ALPHA_EXPR; x \<in> WF_ALPHA_EXPR; 
     f :e: a =p\<Rightarrow> b; x :e: a \<rbrakk> \<Longrightarrow> 
     AppE f x :e: b"
  by (simp add:AppE_def)

lemma LamE_type[type]:
  "\<lbrakk> e \<in> WF_ALPHA_EXPR; e :e: b; type x = a \<rbrakk> \<Longrightarrow>
   LamE x e :e: a =p\<Rightarrow> b"
  by (simp add:LamE_def)

lemma SubstE_type [type]:
"\<lbrakk> p \<in> WF_ALPHA_EXPR; e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e; e :e: type x \<rbrakk> \<Longrightarrow> 
 \<tau>e (p[e|x]) = \<tau>e p"
  by (simp add:SubstE_def)

subsubsection {* Equality Theorems *}

lemma EqualP_refl: "e \<in> WF_ALPHA_EXPR \<Longrightarrow> taut (\<D> e \<Rightarrow>p (e ==p e))"
  apply (simp add:Tautology_def TrueP_def closure alpha_closure)
  apply (simp add:ImpliesP_def OrP_def closure)
  apply (simp add:NotP_def closure)
  apply (simp add:DefinedP_def EqualP_def)
  apply (simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (auto)
done

lemma EqualP_sym: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR; taut (e ==p f)\<rbrakk> 
 \<Longrightarrow> taut (f ==p e)"
  apply (insert EqualP_closure [where e="e" and f="f"])
  apply (insert EqualP_closure [where e="f" and f="e"])
  apply (simp add:Tautology_def EqualP_def WF_ALPHA_PREDICATE_def TrueP_def)
  apply (safe)
  apply (smt domI wfexpr_wfbinding)
  apply (auto)
  apply (force)
done

lemma EqualP_trans: 
"\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR; g \<in> WF_ALPHA_EXPR; taut (e ==p f); taut (f ==p g)\<rbrakk> 
 \<Longrightarrow> taut (e ==p g)"
  apply(insert EqualP_closure [where e="e" and f="f"])
  apply(insert EqualP_closure [where e="f" and f="g"])
  apply(insert EqualP_closure [where e="e" and f="g"])
  apply(simp add:Tautology_def EqualP_def WF_ALPHA_PREDICATE_def TrueP_def)
  apply(safe)
  apply (smt domI wfexpr_wfbinding)
  apply (auto)
  apply (force)
done

(*
declare EqualP_def [eval]
declare VarE_def [eval]
*)

(*
lemma EvalP_EqualVP[eval]: "\<lbrakk> e \<in> WF_ALPHA_EXPR; b \<in> WF_BINDING \<rbrakk> \<Longrightarrow> EvalP (x =p e) b \<longleftrightarrow> (b x = e<b>)"
  apply (simp add:EvalP_def closure)
  apply (simp add:EqualP_def alpha_closure closure)
  apply (auto)
  apply (metis (lifting) VarE_domain domD)
  apply (simp add:WF_BINDING_def WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (auto)



done

lemma expr_body_weaken[simp]: "\<lbrakk> e \<in> WF_ALPHA_EXPR; v \<notin> \<alpha>e e; b \<in> WF_BINDING; b' \<in> WF_BINDING \<rbrakk> \<Longrightarrow> \<beta>e e (b \<oplus> b' on {v}) = \<beta>e e b"
  apply(auto simp add: WF_ALPHA_EXPR_def)
  apply(subgoal_tac "b \<oplus> b' on {v} \<cong> b on \<alpha>e e")
  apply(erule_tac ballE)
  apply(erule_tac x="b \<oplus> b' on {v}" in ballE)
  apply(erule_tac x="b" in ballE)
  apply(auto)
  apply (metis Int_empty_left Int_insert_left beta_equiv_override_2)
done
*)

subsection {* Definedness Laws *}

lemma DefinedP_LitE: "x :! t \<Longrightarrow> taut (\<D> (LitE x))"
  apply (auto simp add:Tautology_def closure stype_rel_def)
  apply (auto simp add:DefinedP_def TrueP_def LitE_def closure dom_def alpha_closure fdom_def to_map_def)
done

(*
lemma DefinedP_TrueE: "taut (\<D> true)"
  by (simp add:TrueE_def closure DefinedP_LitE)

lemma DefinedP_FalseE: "taut (\<D> false)"
  by (simp add:FalseE_def closure DefinedP_LitE)
*)

subsection {* Substitution Laws *}

lemma SubstP_AndP: 
  "\<lbrakk> p \<in> WF_ALPHA_PREDICATE; q \<in> WF_ALPHA_PREDICATE; e \<in> WF_ALPHA_EXPR
   ; x \<notin> \<alpha>e e; e :e: type x \<rbrakk> \<Longrightarrow>
    (p \<and>p q)[e|x] = p[e|x] \<and>p q[e|x]"
  apply(simp add:SubstP_def)
  apply(intro eval_intro)
  apply(blast intro:closure alpha_closure)+
  apply(force simp add:alphabet closure alpha_closure)
  apply(simp add:eval closure alpha_closure)
  apply(auto)
  apply(rule_tac x="b'" in bexI)
  apply(auto)
  apply(subgoal_tac "b' \<cong> b'a on {x}")
  apply (metis (hide_lams, no_types) beta_equiv_override beta_equiv_override_3 override_on_cancel3')
  sorry

lemma SubstP_VarP: 
  "\<lbrakk> e \<in> WF_ALPHA_EXPR; x \<notin> \<alpha>e e; expr_type e = BoolType
   ; type x = BoolType; e :e: type x \<rbrakk> \<Longrightarrow> 
  (VarP x)[e|x] = ExprP e"
  apply(rule eval_intro)
  apply(simp add:closure alpha_closure VarE_type)+
  apply(simp add:alphabet closure alpha_closure VarE_type)
  apply(simp add:eval closure alpha_closure SubstP_def)
  apply(rule ballI)
  apply(rule iffI)
  apply(erule bexE)
  apply(simp add:EvalP_def closure binding)
  apply(simp add:ExprP_def VarE_def closure WF_ALPHA_EXPR_def)
  sorry

(*

  apply(force)
  apply(simp add:EvalP_def closure binding)
  apply(simp add:ExprP_def VarE_def closure  WF_ALPHA_EXPR_def)
  apply(auto)
  apply(metis (full_types) bindings_assign fun_upd_same option.inject)
done
*)

subsection {* Proof Laws *}

lemma EqualityE_intro: 
  "\<lbrakk> e \<in> WF_ALPHA_EXPR; f \<in> WF_ALPHA_EXPR; \<alpha>e e = \<alpha>e f; \<tau>e e = \<tau>e f
   ; expr_dom e = expr_dom f; \<forall>b \<in> expr_dom e. e<b> = f<b> \<rbrakk> \<Longrightarrow>
  e = f"
  apply (case_tac e)
  apply (case_tac f)
  apply (auto)
  apply (rule ext)
  apply (auto simp add:fdom_def to_map_def)
  apply (smt domIff option.simps(2))
done

subsection {* Lambda Laws *}

lemma LamE_reduce:
  assumes "e \<in> WF_ALPHA_EXPR" "v \<in> WF_ALPHA_EXPR" "v :e: a" "a = type x" "x \<notin> \<alpha>e v"
          "|a| \<le> FuncMaxCard" "|\<tau>e e| \<le> FuncMaxCard"
  shows "AppE (LamE x e) v = e[v|x]"
  apply (insert assms)
  apply (rule EqualityE_intro)
  apply (simp add:alpha_closure closure type)
  apply (simp add:alpha_closure closure type)
  apply (force simp add:alphabet closure)
  apply (simp add:type closure)
  apply (simp add:AppE_domain LamE_domain SubstE_domain closure)
  apply (subgoal_tac "\<forall>b\<in>expr_dom v. v<b> \<in> fdom (DestFunc LamE x e<b>) \<longleftrightarrow> b(x := v<b>) \<in> expr_dom e")
  apply (simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (auto)[1]
  apply (simp add:LamE_def)
  apply (rule ballI)
  apply (subgoal_tac "(\<lambda>v. \<beta>e e (b(x := v))) \<in> FuncSort (type x) (\<tau>e e)")
  apply (auto)[1]
  apply (force simp add:fdom_def fran_def to_map_def)
  apply (simp add:FuncSort_def')
  apply (auto)[1]
  apply (simp add:fdom_def to_map_def)
  apply (smt bindings_assign_type domIff fdom_def to_map_def wfexpr_wfbinding)
  apply (simp add:fran_def fdom_def to_map_def ran_def dom_def)
  apply (metis (mono_tags) fdom_def insertI1 insert_dom to_map_def wfexpr_wfbinding)
  apply (metis wfexpr_wfbinding)
  apply (simp add:FuncSort_def' fdom_def fran_def to_map_def ran_def)
  apply (auto)[1]
  apply (metis bindings_assign_type domI fdom_def option.simps(3) to_map_def wfexpr_wfbinding)
  apply (smt domIff fdom_def option.simps(3) to_map_def wfexpr_type)
  apply (auto)
  apply (subgoal_tac "(\<lambda>v. \<beta>e e (b(x := v))) \<in> FuncSort (type x) (\<tau>e e)")
  apply (simp add:AppE_def closure)
  apply (simp add:LamE_def SubstE_def closure)
  apply (auto)
  apply (auto simp add:fdom_def fran_def to_map_def)
  apply (smt domIff option.simps(3))
  apply (simp add:FuncSort_def' fdom_def fran_def to_map_def ran_def)
  apply (auto)[1]
  apply (metis bindings_assign_type domI fdom_def option.simps(3) to_map_def wfexpr_wfbinding)
  apply (smt domIff fdom_def option.simps(3) to_map_def wfexpr_type)
done

lemma inj_onD: "[| inj_on f A; f(x) = f(y); x \<in> A; y \<in> A |] ==> x=y"
  by (simp add: inj_on_def)


lemma "\<lbrakk> f \<in> WF_ALPHA_EXPR; f :e: a =p\<Rightarrow> b ; a = type x; x \<notin> \<alpha>e f
       ; expr_dom f = WF_BINDING; |a| \<le> FuncMaxCard; |b| \<le> FuncMaxCard \<rbrakk> \<Longrightarrow> 
       LamE x (AppE f (VarE x)) = f"
  apply (rule EqualityE_intro)
  apply (simp add:closure type)
  apply (simp)
  apply (simp add:alphabet closure alpha_closure type)
  apply (simp add: type closure)
  apply (simp add: LamE_domain AppE_domain VarE_domain closure type)
  apply (auto)
  apply (simp add:LamE_def closure alpha_closure type)
  apply (safe)
  apply (rule_tac f="DestFunc" and A="carrier (type x =p\<Rightarrow> b)" in inj_onD)


  apply (drule elseNone)
  apply (auto)
  apply (rule_tac f="DestPFunc" and A="UNIV" in inj_onD)
  apply (simp_all)
  apply (rule ext)
  apply (simp add:AppE_def closure alpha_closure type)
  apply (simp add:VarE_def closure alpha_closure type)
  apply (auto)
  apply (subgoal_tac "ba \<cong> ba(x := y) on \<alpha>e f")
  apply (simp add:WF_ALPHA_EXPR_def WF_BINDING_MAP_def)
  apply (simp add:beta_equiv_def)
  apply (simp add:WF_BINDING_def)
  apply (auto)
  apply (smt DestPFunc_ntype mem_Collect_eq wfexpr_type)
  apply (rule_tac bindings_assign)
  apply (auto)
  apply (metis (hide_lams, mono_tags) DestPFunc_ntype wfexpr_type)
done

end
end