(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_expr.thy                                                         *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Basic Expressions *}

theory utp_expr
imports utp_pred utp_unrest utp_sorts utp_rename
begin

text {* The type which an expression holds should be the maximal type, if such a notion exists *}
type_synonym 'VALUE EXPRESSION = "('VALUE WF_BINDING_FUN)"


text {* A well-formed expression must produce a well-typed value for every binding, and non well-formed bindings yield an fixed arbitrary well-typed value *}

definition WF_EXPRESSION :: "'VALUE EXPRESSION set" where
"WF_EXPRESSION = {f. \<exists> t. \<forall>b. f b : t}"

typedef (open) 'VALUE WF_EXPRESSION = "WF_EXPRESSION :: 'VALUE EXPRESSION set"
  apply (simp add:WF_EXPRESSION_def)
  apply (rule_tac x="(\<lambda> x. default someType)" in exI)
  apply (rule_tac x="someType" in exI)
  apply (force)
done

declare Rep_WF_EXPRESSION [simp]
declare Rep_WF_EXPRESSION_inverse [simp]
declare Abs_WF_EXPRESSION_inverse [simp]

lemma Rep_WF_EXPRESSION_intro [intro]:
  "Rep_WF_EXPRESSION x = Rep_WF_EXPRESSION y \<Longrightarrow> x = y"
  by (simp add:Rep_WF_EXPRESSION_inject)

lemma Rep_WF_EXPRESSION_elim [elim]:
  "\<lbrakk> x = y; Rep_WF_EXPRESSION x = Rep_WF_EXPRESSION y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

setup_lifting type_definition_WF_EXPRESSION

notation Rep_WF_EXPRESSION ("\<langle>_\<rangle>\<^sub>e")

lemma Rep_WF_EXPRESSION_typed [typing]:
  "\<exists> t. \<forall> b. \<langle>e\<rangle>\<^sub>e b : t"
  apply (insert Rep_WF_EXPRESSION[of e])
  apply (auto simp add:WF_EXPRESSION_def)
done

definition etype_rel :: "'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE UTYPE \<Rightarrow> bool" (infix ":\<^sub>e" 50) where
"etype_rel e t \<equiv> \<forall>b. \<langle>e\<rangle>\<^sub>e b : t"

definition expr_type :: "'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE UTYPE" where
"expr_type e \<equiv> THE t. e :\<^sub>e t"

definition evar_compat :: "'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE VAR \<Rightarrow> bool" (infix "\<rhd>\<^sub>e" 50) where
"evar_compat e x \<equiv> \<forall>b. \<langle>e\<rangle>\<^sub>e b \<rhd> x"

instantiation WF_EXPRESSION :: (VALUE) DEFINED
begin

definition Defined_WF_EXPRESSION :: "'a WF_EXPRESSION \<Rightarrow> bool" where
"Defined_WF_EXPRESSION e \<equiv> \<forall> b. \<D> (\<langle>e\<rangle>\<^sub>e b)"

instance ..

end

lemma evar_compat_intros [simp,intro]:
  "\<lbrakk> v :\<^sub>e vtype x; \<D> v \<rbrakk> \<Longrightarrow> v \<rhd>\<^sub>e x"
  "\<lbrakk> v :\<^sub>e vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> v \<rhd>\<^sub>e x"
  by (auto simp add:evar_compat_def etype_rel_def Defined_WF_EXPRESSION_def)

lemma evar_compat_cases [elim]:
  "\<lbrakk> v \<rhd>\<^sub>e x; \<lbrakk> v :\<^sub>e vtype x; \<D> v \<rbrakk> \<Longrightarrow> P
           ; \<lbrakk> v :\<^sub>e vtype x; \<not> aux x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp add:evar_compat_def etype_rel_def Defined_WF_EXPRESSION_def)

lemma evar_comp_dash [typing]:
  "v \<rhd>\<^sub>e x \<Longrightarrow> v \<rhd>\<^sub>e x\<acute>"
  by (simp add:evar_compat_def typing)

definition UNREST_EXPR :: "('VALUE VAR) set \<Rightarrow> 'VALUE WF_EXPRESSION \<Rightarrow> bool" where
"UNREST_EXPR vs e \<equiv> (\<forall> b1 b2. \<langle>e\<rangle>\<^sub>e(b1 \<oplus>\<^sub>b b2 on vs) = \<langle>e\<rangle>\<^sub>e b1)" 

definition WF_EXPRESSION_OVER ::
  "('VALUE VAR) set \<Rightarrow>
   'VALUE WF_EXPRESSION set" where
"WF_EXPRESSION_OVER vs = {e . UNREST_EXPR (VAR - vs) e}"

subsection {* Operators *}

subsubsection {* Equality *}

definition EqualP :: 
"'VALUE WF_EXPRESSION \<Rightarrow> 
 'VALUE WF_EXPRESSION \<Rightarrow> 
 'VALUE WF_PREDICATE" where
"EqualP e f = mkPRED {b. \<langle>e\<rangle>\<^sub>e b = \<langle>f\<rangle>\<^sub>e b}"

notation EqualP (infixr "==p" 200)

definition LitE :: "'VALUE \<Rightarrow> 'VALUE WF_EXPRESSION" where 
"LitE v = Abs_WF_EXPRESSION (if (\<exists> t. v : t) then (\<lambda> b. v) else (\<lambda> b. default someType))"

definition DefaultE :: "'VALUE UTYPE \<Rightarrow> 'VALUE WF_EXPRESSION" where
"DefaultE t \<equiv> LitE (default t)"

definition CoerceE :: "'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE UTYPE \<Rightarrow> 'VALUE WF_EXPRESSION" where
"CoerceE e t \<equiv> if (e :\<^sub>e t) then e else DefaultE t"

lift_definition VarE :: "'VALUE VAR \<Rightarrow> 'VALUE WF_EXPRESSION" is "\<lambda> x. (\<lambda> b. \<langle>b\<rangle>\<^sub>b x)"
  by (auto simp add:WF_EXPRESSION_def)

lemma LitE_rep_eq: 
  "\<langle>LitE v\<rangle>\<^sub>e = (if (\<exists> t. v : t) then (\<lambda> b. v) else (\<lambda> b. default someType))"
  apply (subgoal_tac "(if (\<exists> t. v : t) then (\<lambda> b. v) else (\<lambda> b. default someType)) \<in> WF_EXPRESSION")
  apply (auto simp add:LitE_def WF_EXPRESSION_def)
done

definition AppE :: 
  "'VALUE::FUNCTION_SORT WF_EXPRESSION \<Rightarrow> 'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE WF_EXPRESSION" where
"AppE f v = Abs_WF_EXPRESSION (\<lambda> b. DestFunc (\<langle>f\<rangle>\<^sub>e b) (\<langle>v\<rangle>\<^sub>e b))"

lemma AppE_rep_eq:
  "\<lbrakk> f :\<^sub>e FuncType a b; v :\<^sub>e a; \<D> f \<rbrakk> \<Longrightarrow> \<langle>AppE f v\<rangle>\<^sub>e = (\<lambda> b. DestFunc (\<langle>f\<rangle>\<^sub>e b) (\<langle>v\<rangle>\<^sub>e b))"
  apply (subgoal_tac "(\<lambda> b. DestFunc (\<langle>f\<rangle>\<^sub>e b) (\<langle>v\<rangle>\<^sub>e b)) \<in> WF_EXPRESSION")
  apply (simp add:AppE_def)
  apply (simp add:WF_EXPRESSION_def)
  apply (rule_tac x="b" in exI)
  apply (auto intro:typing simp add:etype_rel_def Defined_WF_EXPRESSION_def)
done

definition DefinedP :: "'VALUE WF_EXPRESSION \<Rightarrow> 'VALUE WF_PREDICATE" ("\<D>") where
"DefinedP e \<equiv> LiftP (\<D> \<circ> \<langle>e\<rangle>\<^sub>e)"

definition VarDefinedP :: "'VALUE VAR \<Rightarrow> 'VALUE WF_PREDICATE" ("\<V>") where
"\<V> x \<equiv> DefinedP (VarE x)"

lift_definition RenameE ::
  "'VALUE WF_EXPRESSION \<Rightarrow>
   'VALUE VAR_RENAME \<Rightarrow>
   'VALUE WF_EXPRESSION" ("_[_]\<epsilon>" [200]) is
"\<lambda> e ss. (\<langle>e\<rangle>\<^sub>e \<circ> (RenameB (inv\<^sub>s ss)))"
proof -
  fix e ss
  show "\<langle>e\<rangle>\<^sub>e \<circ> RenameB (inv\<^sub>s ss) \<in> WF_EXPRESSION"
    apply (simp add:WF_EXPRESSION_def)
    apply (insert Rep_WF_EXPRESSION_typed[of e])    
    apply (auto)
  done
qed

(* FIXME: Expression substitution doesn't substitute, it just identifies *)
lift_definition SubstE :: 
"'VALUE WF_EXPRESSION \<Rightarrow> 
 'VALUE WF_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE WF_EXPRESSION" ("_[_|_]" [200]) is
"\<lambda> f v x. (\<lambda> b. \<langle>f\<rangle>\<^sub>e (b(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b)))"
  apply (simp add: WF_EXPRESSION_def)
  apply (metis Rep_WF_EXPRESSION_typed)
done

definition SubstP_body ::
"'VALUE WF_PREDICATE \<Rightarrow> 
 'VALUE WF_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE VAR \<Rightarrow>
 'VALUE WF_PREDICATE" where
"SubstP_body p v x x' \<equiv> \<exists>p {x'} . p[id(x:=x') on {x}] \<and>p (VarE x' ==p v)"

definition is_SubstP_var ::
"'VALUE WF_PREDICATE \<Rightarrow> 
 'VALUE WF_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE VAR \<Rightarrow>
 bool" where
 "is_SubstP_var p v x x' \<equiv> x \<noteq> x' \<and> UNREST {x'} p \<and> UNREST_EXPR {x'} v \<and> vtype x' = vtype x \<and> aux x' = aux x"

(* Substitution generates a variable fresh in p and v and uses it to semantically substitute *)
definition SubstP ::
"'VALUE WF_PREDICATE \<Rightarrow> 
 'VALUE WF_EXPRESSION \<Rightarrow> 
 'VALUE VAR \<Rightarrow> 
 'VALUE WF_PREDICATE" ("_[_|_]" [200]) where
"p[v|x] \<equiv> mkPRED {b. b(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b) \<in> destPRED p}"

lemma SubstP_no_var: "\<lbrakk> UNREST {x} p; v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> p[v|x] = p"
  apply (simp add:SubstP_def)
  apply (auto simp add:UNREST_def)
  apply (metis (lifting) binding_compat binding_upd_simps binding_upd_upd evar_compat_def)
  apply (metis binding_upd_apply evar_compat_def)
done

(* SubstP_body p v x (SOME x'. is_SubstP_var p v x x')" *)

subsection {* Theorems *}

subsubsection {* Well-formed expression properties *}

lemma EXPRESSION_eqI [intro]:
  "\<lbrakk> \<forall> b. \<langle>e\<rangle>\<^sub>e b = \<langle>f\<rangle>\<^sub>e b \<rbrakk> \<Longrightarrow>
  e = f"
  apply (case_tac e, case_tac f, auto)
  apply (rule Rep_WF_EXPRESSION_intro)
  apply (auto)
done

(* It would be nice to have this as a typing rule, but it
   confuses the HO unifier... *)

theorem WF_EXPRESSION_type: 
"e :\<^sub>e t \<Longrightarrow>
\<langle>e\<rangle>\<^sub>e b : t"
  by (simp add:WF_EXPRESSION_def etype_rel_def)

(*
theorem WF_EXPRESSION_type: 
"e :e: t \<Longrightarrow>
\<langle>e\<rangle>\<^sub>e b : t"
  by (simp add:WF_EXPRESSION_def etype_rel_def)
*)

theorem WF_EXPRESSION_has_type [typing]: 
"\<exists> t. e :\<^sub>e t"
  by (metis Rep_WF_EXPRESSION_typed etype_rel_def)

lemma WF_EXPRESSION_value_exists:
  "\<exists> t v. v : t \<and> \<langle>e\<rangle>\<^sub>e b = v"
  by (metis Rep_WF_EXPRESSION_typed)

lemma WF_EXPRESSION_value_elim [elim]:
  "\<And> t v b. \<lbrakk> v : t; \<langle>e\<rangle>\<^sub>e b = v \<rbrakk> \<Longrightarrow> P \<Longrightarrow> P"
  by (simp)
 
subsubsection {* Closure Theorems *}

lemma WF_EXPRESSION_bindings [simp,intro]:
  "\<forall> b. e b : t \<Longrightarrow> e \<in> WF_EXPRESSION"
  by (auto simp add:WF_EXPRESSION_def)

subsubsection {* Typing Theorems *}

theorem VarE_type [typing]: "VarE x :\<^sub>e vtype x"
  by (simp add:VarE.rep_eq WF_BINDING_def typing etype_rel_def)

theorem LitE_type [typing]: 
"v : t \<Longrightarrow> LitE v :\<^sub>e t"
  by (auto simp add:LitE_rep_eq etype_rel_def typing)

theorem AppE_type [typing]:
"\<lbrakk> f :\<^sub>e FuncType a b; \<D> f; v :\<^sub>e a \<rbrakk> \<Longrightarrow> AppE f v :\<^sub>e b"
  by (auto intro:typing simp add:AppE_rep_eq etype_rel_def Defined_WF_EXPRESSION_def)

theorem DefaultE_type [typing]:
"DefaultE t :\<^sub>e t"
  by (simp add:DefaultE_def typing)

theorem CoerceE_type [typing]:
"CoerceE e t :\<^sub>e t"
  by (simp add: CoerceE_def typing)

theorem RenameE_type [typing]:
  "e :\<^sub>e t \<Longrightarrow> e[ss]\<epsilon> :\<^sub>e t" 
  by (simp add:etype_rel_def RenameE.rep_eq)

theorem SubstE_type [typing]:
"\<lbrakk> v :\<^sub>e vtype x; e :\<^sub>e t \<rbrakk> \<Longrightarrow>
 e[v|x] :\<^sub>e t"
  by (simp add:SubstE.rep_eq etype_rel_def WF_BINDING_update1)

subsubsection {* Definedness Theorems *}

theorem LitE_defined [defined]: "\<D> v \<Longrightarrow> \<D> (LitE v)"
  by (auto simp add:LitE_rep_eq Defined_WF_EXPRESSION_def defined)

theorem DefaultE_defined [defined]: "\<D> (DefaultE t)"
  by (auto intro:defined typing simp add: DefaultE_def)

theorem CoerceE_defined [defined]: "\<D> e \<Longrightarrow> \<D> (CoerceE e t)"
  by (auto simp add:CoerceE_def defined)

theorem VarE_defined [defined]: "aux x \<Longrightarrow> \<D> (VarE x)"
  by (simp add:VarE.rep_eq Defined_WF_EXPRESSION_def defined)

subsubsection {* bfun theorems *}

lemma LitE_bfun [simp]: "a : t \<Longrightarrow> \<langle>LitE a\<rangle>\<^sub>e = (\<lambda> x. a)"
  by (auto simp add:LitE_def)

subsubsection {* @{term UNREST_EXPR} Theorems *}

theorem UNREST_EXPR_member [unrest] :
"UNREST_EXPR vs f \<Longrightarrow> \<langle>f\<rangle>\<^sub>e b = \<langle>f\<rangle>\<^sub>e (b \<oplus>\<^sub>b b' on vs)"
  by (auto simp add:UNREST_EXPR_def)

theorem UNREST_EXPR_empty [unrest] :
"UNREST_EXPR {} e"
  by (simp add: UNREST_EXPR_def)

theorem UNREST_EXPR_subset [unrest] :
"\<lbrakk>UNREST_EXPR vs1 e;
 vs2 \<subseteq> vs1\<rbrakk> \<Longrightarrow>
 UNREST_EXPR vs2 e"
  apply (auto simp add:UNREST_EXPR_def)
  apply (metis binding_override_simps(5) double_diff order_refl)
done

theorem UNREST_EqualP [unrest] :
"\<lbrakk>UNREST_EXPR vs e; UNREST_EXPR vs f \<rbrakk> \<Longrightarrow>
 UNREST vs (e ==p f)"
  apply (auto simp add:EqualP_def)
  apply (drule_tac ?vs2.0="vs" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (drule_tac ?vs2.0="vs" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (simp add:UNREST_EXPR_def UNREST_def)
done

theorem UNREST_EqualP_alt [unrest] :
"\<lbrakk>UNREST_EXPR vs1 e; UNREST_EXPR vs2 f \<rbrakk> \<Longrightarrow>
 UNREST (vs1 \<inter> vs2) (e ==p f)"
  apply (auto simp add:EqualP_def)
  apply (drule_tac ?vs2.0="vs1 \<inter> vs2" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (drule_tac ?vs2.0="vs1 \<inter> vs2" in UNREST_EXPR_subset)
  apply (simp_all)
  apply (simp add:UNREST_EXPR_def UNREST_def)
done


(*
theorem UNREST_EXPR_wfexpr [unrest]:
"UNREST_EXPR vs e \<Longrightarrow> UNREST_EXPR vs (wfexpr e)"
  by (simp add:wfexpr_def UNREST_EXPR_def closure)
*)

theorem UNREST_EXPR_VarE [unrest] :
"UNREST_EXPR (vs - {x}) (VarE x)"
  by (simp add:VarE.rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_LitE [unrest] :
"UNREST_EXPR vs (LitE v)"
  by (simp add:LitE_rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_AppE [unrest] :
"\<lbrakk> f :\<^sub>e FuncType a b; v :\<^sub>e a; \<D> f; UNREST_EXPR vs f; UNREST_EXPR vs v \<rbrakk> \<Longrightarrow> UNREST_EXPR vs (AppE f v)"
  by (simp add:AppE_rep_eq UNREST_EXPR_def)

theorem UNREST_EXPR_DefaultE [unrest] :
"UNREST_EXPR vs (DefaultE t)"
  by (simp add:DefaultE_def unrest)

theorem UNREST_EXPR_CoerceE [unrest] :
"UNREST_EXPR vs e \<Longrightarrow> UNREST_EXPR vs (CoerceE e t)"
  by (auto intro:unrest simp add:CoerceE_def)

theorem UNREST_EXPR_RenameE [unrest] :
"UNREST_EXPR vs p \<Longrightarrow>
 UNREST_EXPR (\<langle>ss\<rangle>\<^sub>s ` vs) p[ss]\<epsilon>"
  by (auto simp add: UNREST_EXPR_def RenameE.rep_eq RenameB_override_distr1 closure)

theorem UNREST_EXPR_SubstE [unrest] :
"\<lbrakk> v \<rhd>\<^sub>e x;
   UNREST_EXPR vs1 f; UNREST_EXPR vs2 v \<rbrakk> \<Longrightarrow>
 UNREST_EXPR ((vs1 \<union> {x}) \<inter> vs2) (f[v|x])"
  apply (auto simp add:UNREST_EXPR_def SubstE.rep_eq evar_compat_def)
  apply (smt Rep_WF_BINDING_rep_eq binding_override_simps(3) binding_override_simps(5) binding_override_simps(6) binding_override_simps(7) binding_override_singleton etype_rel_def fun_upd_same inf.commute)
done

lemma dash_single_rename_func_on [closure]: "rename_func_on dash {x}"
  by (simp add:rename_func_on_def)

(* This is not quite right; if x is unrestricted in v (and restricted in p) then
   x should be unrestricted in the whole, but it never can be. *)

theorem UNREST_SubstP [unrest] :  
"\<lbrakk> v \<rhd>\<^sub>e x; UNREST vs1 p; UNREST_EXPR vs2 v; x \<notin> vs1; vs = (vs1 \<inter> vs2) \<rbrakk> \<Longrightarrow>
      UNREST vs p[v|x]"
  apply (auto simp add:SubstP_def UNREST_def UNREST_EXPR_def)
  apply (drule_tac x="b1(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b1)" in bspec, simp)
  apply (drule_tac x="b1" in spec)
  apply (drule_tac x="b1 \<oplus>\<^sub>b b2 on vs1" in spec) back
  apply (simp)
  apply (drule_tac x="b1(x :=\<^sub>b \<langle>v\<rangle>\<^sub>e b1) \<oplus>\<^sub>b b2 on vs2" in spec)
  apply (simp)
  apply (subgoal_tac "x \<notin> vs1 \<inter> vs2")
  apply (subgoal_tac "\<langle>v\<rangle>\<^sub>e b1 \<rhd> x")
  apply (simp)
  apply (metis inf_commute)
  apply (auto)
  apply (metis evar_compat_def)
done

(*
theorem UNREST_SubstP [unrest] :
  assumes 
   "v \<rhd>\<^sub>e x"
   "UNREST vs1 p" "UNREST_EXPR vs2 v" "x \<notin> vs1"
   "\<exists> x'. is_SubstP_var p v x x'"
  shows "UNREST (vs1 \<inter> vs2) p[v|x]"
proof -
  have "\<And> x'. is_SubstP_var p v x x' \<Longrightarrow> UNREST (vs1 \<inter> vs2) (\<exists>p {x'} . p[id(x:=x') on {x}] \<and>p VarE x' ==p v)"
  proof -
    fix x'
    assume assms':"is_SubstP_var p v x x'"

    moreover hence subst[simplified]: "MapRename [[x] [\<mapsto>] [x']] \<in> VAR_RENAME"
      apply (unfold is_SubstP_var_def)
      apply (rule VAR_RENAME_MapRename)
      apply (simp_all)
    done
    moreover from subst assms assms' have ur1:"UNREST (vs1 - {x'}) (p[id(x:=x') on {x}])"
        apply (simp add:RenamePMap_def closure)
        apply (rule_tac unrest)
        apply (force)
        thm rename_on_rep_eq[of dash "{x}"]
        apply (simp add: is_SubstP_var_def rename_on_rep_eq closure)
        apply (erule conjE)
    sorry

    moreover from assms have ur2:"UNREST ((vs2 - {x'}) \<inter> vs2) (VarE x' ==p v)"
      by (simp add:unrest closure)

    from assms assms' have "UNREST ((vs1 - {x'}) \<inter> (vs2 - {x'})) (p[id(x:=x') on {x}] \<and>p VarE x' ==p v)"
      apply (rule_tac UNREST_AndP_alt)
      apply (simp add:is_SubstP_var_def closure)
      apply (simp add:ur1)
      apply (subgoal_tac "(vs2 - {x'}) \<inter> vs2 = (vs2 - {x'})")
      apply (insert ur2)
      apply (simp)
      apply (force)
    done
    with assms assms' show "UNREST (vs1 \<inter> vs2) (\<exists>p {x'} . p[id(x:=x') on {x}] \<and>p VarE x' ==p v)"
      apply (rule_tac UNREST_ExistsP_minus)
      apply (subgoal_tac "(vs1 \<inter> vs2 - {x'}) = (vs1 - {x'}) \<inter> (vs2 - {x'})")
      apply (simp)
      apply (force)
    done

  qed

  with assms show ?thesis
    apply (simp add:SubstP_def SubstP_body_def)
    apply (auto)[1]
    apply (rule someI2)
    apply (force)
    apply (simp del:fun_upd_apply)
  sorry

qed
*)


(*
theorem "UNREST_EXPR {x} v \<Longrightarrow> UNREST vs (\<exists>p {x}. VarE x ==p v)"
  apply (auto simp add:UNREST_def UNREST_EXPR_def EqualP_def VarE_def ExistsP_def)
  apply (case_tac "x \<in> vs")
  apply (rule_tac x="b1a \<oplus>\<^sub>b b2 on vs" in exI)
  apply (auto)
  apply (rule_tac x="b2a \<oplus>\<^sub>b b2 on vs" in exI)
  apply (auto)
  apply (metis (no_types) binding_compat binding_override_simps(7) binding_upd_upd insert_Diff insert_Diff_single)
  apply (simp)
  apply (case_tac "x \<in> vs")
  apply (simp)
  apply (rule_tac x="b2a" in exI)
  apply (simp)

theorem UNREST_SubstP_nox [unrest] :
  assumes 
   "v \<rhd>\<^sub>e x"
   "UNREST vs p" "x \<in> vs"
   "\<exists> x'. is_SubstP_var p v x x'"
  shows "UNREST vs p[v|x]"
proof -
  have "\<And> x'. is_SubstP_var p v x x' \<Longrightarrow> UNREST vs (\<exists>p {x'} . p\<^bsup>[x \<mapsto> x']\<^esup> \<and>p VarE x' ==p v)"1
    apply (rule unrest) back
    apply (rule unrest)
    apply (rule unrest)
    apply (simp_all add: is_SubstP_var_def assms)
    apply (clarify)
    apply (insert assms(2))
    apply (subgoal_tac "UNREST ({x'} \<union> vs) p")
    apply (force intro:unrest)
    apply (auto intro:unrest)[1]
    apply (rule unrest) 
    apply (rule unrest)
    apply (rule unrest)
    apply (force intro:unrest)
*)

theorem UNREST_SubstP_var [unrest] :  
   "\<lbrakk> v \<rhd>\<^sub>e x; UNREST vs1 p; UNREST_EXPR vs2 v; x \<notin> vs1; x \<in> vs2 \<rbrakk> \<Longrightarrow>
      UNREST {x} p[v|x]"
  apply (auto simp add:SubstP_def UNREST_def UNREST_EXPR_def)
  apply (metis binding_compat binding_upd_override binding_upd_upd evar_compat_def)
done

(*
theorem UNREST_SubstP_var [unrest] :
  assumes 
   "v \<rhd>\<^sub>e x"
   "UNREST vs1 p" "UNREST_EXPR vs2 v" "x \<notin> vs1" "x \<in> vs2"
   "\<exists> x'. is_SubstP_var p v x x'"
  shows "UNREST {x} p[v|x]" 
proof -
  have "\<And> x'. is_SubstP_var p v x x' \<Longrightarrow> UNREST {x} (\<exists>p {x'} . p[id(x:=x') on {x}] \<and>p VarE x' ==p v)"
  proof -
    fix x'
    assume assms':"is_SubstP_var p v x x'"

    moreover hence subst[simplified]: "MapRename [[x] [\<mapsto>] [x']] \<in> VAR_RENAME"
      apply (unfold is_SubstP_var_def)
      apply (rule VAR_RENAME_MapRename)
      apply (simp_all)
    done
    moreover from subst assms assms' have ur1:"UNREST {x} (p[id(x:=x') on {x}])"
      apply (insert UNREST_RenameP[of "{dash x}" p "dash on {x}", simplified] assms)
      apply (auto simp add:closure rename_on_rep_eq is_SubstP_var_def)
   sorry

    moreover from assms assms' have ur2:"UNREST {x} (VarE x' ==p v)"
      apply (rule_tac UNREST_EqualP_alt [of "{x}" _ "{x}",simplified])
      apply (auto simp add:is_SubstP_var_def)
      apply (insert UNREST_EXPR_VarE[of "{x}" x', simplified], simp)
      apply (auto intro:unrest)
    done
    ultimately show "UNREST {x} (\<exists>p {x'} . p[id(x:=x') on {x}] \<and>p VarE x' ==p v)"
      by (auto intro:unrest)
  qed

  with assms show ?thesis
    apply (simp add:SubstP_def SubstP_body_def)
    apply (auto)[1]
    apply (rule someI2)
    apply (force)
    apply (simp del:fun_upd_apply)
  sorry
qed
*)

subsection {* Boolean Expressions *}

definition "TrueE \<equiv> LitE (MkBool True)"
definition "FalseE \<equiv> LitE (MkBool False)"
definition "ExprP e = LiftP (DestBool \<circ> \<langle>e\<rangle>\<^sub>e)"
definition "VarP v \<equiv> LiftP (DestBool \<circ> \<langle>VarE v\<rangle>\<^sub>e)"

lift_definition PredE :: "'VALUE::BOOL_SORT WF_PREDICATE \<Rightarrow> 'VALUE WF_EXPRESSION" is "\<lambda> p. \<lambda> b. MkBool (b \<in> destPRED p)"
  by (auto intro:typing simp add:WF_EXPRESSION_def)

subsubsection {* Typing Theorems *}

theorem TrueE_type [typing]: "TrueE :\<^sub>e BoolType"
  apply (simp add: TrueE_def)
  apply (rule typing)+
done

theorem FalseE_type [typing]: "FalseE :\<^sub>e BoolType"
  apply (simp add: FalseE_def)
  apply (rule typing)+
done

theorem PredE_type [typing]:
"PredE p :\<^sub>e BoolType"
  by (auto intro:typing simp add:PredE.rep_eq etype_rel_def)

subsubsection {* Definedness Theorems *}

theorem TrueE_defined [defined]: "\<D> TrueE"
  by (auto intro: defined typing simp add:TrueE_def)

theorem FalseE_defined [defined]: "\<D> FalseE"
  by (auto intro: defined typing simp add:FalseE_def)

subsubsection {* Laws about booleans *}
 
lemma ExprP_TrueE [simp]: "ExprP TrueE = true"
  by (auto intro:typing simp add:ExprP_def LitE_rep_eq TrueE_def LiftP_def TrueP_def)

lemma ExprP_FalseE [simp]: "ExprP FalseE = false"
  by (auto intro:typing simp add:ExprP_def LitE_rep_eq FalseE_def LiftP_def FalseP_def)

subsubsection {* @{term UNREST_EXPR} Theorems *}

theorem UNREST_EXPR_TrueE [unrest]: "UNREST_EXPR vs TrueE"
  by (simp add:TrueE_def unrest)

theorem UNREST_EXPR_FalseE [unrest]: "UNREST_EXPR vs FalseE"
  by (simp add:FalseE_def unrest)

theorem UNREST_ExprP [unrest]:
"\<lbrakk> UNREST_EXPR vs e; e :\<^sub>e BoolType \<rbrakk> \<Longrightarrow> UNREST vs (ExprP e)"
  apply (simp add:ExprP_def)
  apply (rule_tac ?vs1.0="VAR - vs" in UNREST_LiftP_alt)
  apply (simp add:WF_BINDING_PRED_def UNREST_EXPR_def)
  apply (clarify)
  apply (drule_tac x="b2" in spec)
  apply (drule_tac x="b1" in spec)
  apply (drule binding_override_equiv)
  apply (metis (full_types) binding_override_simps(10) binding_override_simps(5))
  apply (force)
done

theorem UNREST_EXPR_PredE [unrest]: 
"UNREST vs p \<Longrightarrow> UNREST_EXPR vs (PredE p)"
  apply (auto simp add:UNREST_EXPR_def UNREST_def MkBool_type PredE.rep_eq)
  apply (rule_tac f="MkBool" and g="MkBool" in cong, simp)
  apply (metis (full_types) binding_override_simps(2) binding_override_simps(3))
done
  
theorem UNREST_VarP [unrest]:
"UNREST (vs - {x}) (VarP x)"
apply (simp add:VarP_def)
apply (rule_tac ?vs1.0="{x}" in UNREST_LiftP_alt)
apply (auto)
apply (simp add:WF_BINDING_PRED_def VarE.rep_eq binding_equiv_def)
done

end