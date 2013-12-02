(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_rel.thy                                                          *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)

header {* Relations *}

theory utp_rel
imports 
  utp_pred 
  utp_expr 
  utp_rename 
  utp_unrest 
  "../tactics/utp_expr_tac"
  "../laws/utp_rename_laws"
begin

subsection {* Composable Bindings *}

definition COMPOSABLE_BINDINGS ::
  "('VALUE WF_BINDING \<times>
    'VALUE WF_BINDING) set" where
"COMPOSABLE_BINDINGS =
 {(b1, b2) . (\<forall> v \<in> UNDASHED . \<langle>b1\<rangle>\<^sub>b(dash v) = \<langle>b2\<rangle>\<^sub>b v) \<and> b1 \<cong> b2 on NON_REL_VAR}"

subsection {* Classes of relation *}

definition WF_RELATION :: "'VALUE WF_PREDICATE set" where
"WF_RELATION = {p. UNREST NON_REL_VAR p}"

definition WF_CONDITION :: "'VALUE WF_PREDICATE set" where
"WF_CONDITION = {p \<in> WF_RELATION. UNREST DASHED p}"

definition WF_POSTCOND :: "'VALUE WF_PREDICATE set" where
"WF_POSTCOND = {p \<in> WF_RELATION. UNREST UNDASHED p}"

text {* An assignment is a special kind of predicate whose sole
behaviour is to assign particular values to a particular set of
variables. All other variables are unrestricted. *}

definition WF_ASSIGN :: "'a VAR set \<Rightarrow> 'a WF_PREDICATE set" where
"WF_ASSIGN xs = {P. (\<forall>x\<in>xs. \<forall> b1 \<in> destPRED P. \<forall> b2 \<in> destPRED P. \<langle>b1\<rangle>\<^sub>b x = \<langle>b2\<rangle>\<^sub>b x)
                  \<and> (- xs) \<sharp> P
                  \<and> xs \<subseteq> DASHED}"

subsection {* Permutations *}

text {* The permutation @{term "SS"} swaps dashed and undashed variables. *}

abbreviation "SS  \<equiv> prime on UNDASHED"

text {* @{term "SS1"} swaps dashed and doubly-dashed variables. *}

abbreviation "SS1 \<equiv> prime on DASHED"

text {* @{term "SS2"} swaps undashed and doubly-dashed variables. *}

abbreviation "SS2 \<equiv> (prime \<circ> prime) on UNDASHED"

(*
lift_definition SS :: "'VALUE VAR_RENAME" is
"(\<lambda> v .
   if v \<in> UNDASHED then (dash v) else
   if v \<in> DASHED then (undash v) else v)"
  by (auto simp add:VAR_RENAME_def bij_def inj_on_def)

lift_definition SS1 :: "'VALUE VAR_RENAME" is
"(\<lambda> v .
   if (v \<in> DASHED) then (dash v) else
   if (v \<in> DASHED_TWICE) then (undash v) else v)"
  by (auto simp add: VAR_RENAME_def bij_def inj_on_def)

lift_definition SS2 :: "'VALUE VAR_RENAME" is
"(\<lambda> v .
   if v \<in> UNDASHED then dash (dash v) else
   if v \<in> DASHED_TWICE then undash (undash v) else v)"
  apply (auto simp add: VAR_RENAME_def bij_def inj_on_def)
  apply (metis (lifting) DASHED_TWICE_undash_DASHED dash_undash_DASHED dash_undash_DASHED_TWICE)
  apply (auto simp add: image_def)[1]
  apply (drule_tac x="dash (dash x)" in bspec) back
  apply (auto)
  apply (auto simp add: image_def)[1]
  apply (drule_tac x="x" in bspec) back
  apply (auto)
  apply (metis (lifting) DASHED_TWICE_undash_DASHED DASHED_undash_UNDASHED dash_undash_DASHED dash_undash_DASHED_TWICE)
done
*)

subsection {* Operators *}

subsubsection {* Skip *}

lift_definition SkipR :: "'VALUE WF_PREDICATE"
is "{b. \<forall> v \<in> UNDASHED . \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b (dash v)}"
done

notation SkipR ("II")

subsubsection {* Alphabet Skip *}

lift_definition SkipRA :: "'VALUE VAR set \<Rightarrow> 'VALUE WF_PREDICATE" ("II\<^bsub>_\<^esub>") is
"\<lambda> vs. (\<exists>\<^sub>p ((UNDASHED \<union> DASHED) - vs). II)"
done

(* notation SkipRA ("II") *)

lemma SkipRA_rep_eq_alt:
  "HOMOGENEOUS vs \<Longrightarrow> destPRED (II\<^bsub>vs\<^esub>) = {b. \<forall> v \<in> in vs . \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b (dash v)}"
  apply (auto simp add:SkipRA.rep_eq ExistsP.rep_eq SkipR.rep_eq)
  apply (metis Int_iff hom_alphabet_undash in_vars_def override_on_minus)
  apply (rule_tac x="x \<oplus>\<^sub>b \<B> on UNDASHED \<union> DASHED - vs" in exI)
  apply (safe)
  apply (rule_tac x="x" in exI)
  apply (force)
  apply (case_tac "v \<in> vs")
  apply (simp)
  apply (subgoal_tac "v\<acute> \<in> vs")
  apply (simp)
  apply (metis (lifting) hom_alphabet_undash)
  apply (simp)
  apply (subgoal_tac "v\<acute> \<notin> vs")
  apply (simp add:default_binding.rep_eq)
  apply (metis hom_alphabet_dash)
done

subsubsection {* Conditional *}

text {* Should we impose a constraint on b for it to be a condition? *}

definition CondR ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" where
"CondR p1 b p2 = (b \<and>\<^sub>p p1) \<or>\<^sub>p (\<not>\<^sub>p b \<and>\<^sub>p p2)"

notation CondR ("_ \<lhd> _ \<rhd> _")

subsubsection {* Sequential Composition *}

lift_definition SemiR ::
  "'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE \<Rightarrow>
   'VALUE WF_PREDICATE" is
"\<lambda> p1 p2.
 {b1 \<oplus>\<^sub>b b2 on DASHED | b1 b2 .
   b1 \<in> p1 \<and> b2 \<in> p2 \<and> (b1, b2) \<in> COMPOSABLE_BINDINGS}"
done

(* Not sure about the precedence of sequential composition yet. *)

notation SemiR (infixr ";" 140)

subsubsection {* Assignment *}

definition 
  "AssignF = {f :: 'a VAR \<Rightarrow> 'a WF_EXPRESSION. \<forall> x. f x \<rhd>\<^sub>e x}"

typedef 'a AssignF = "AssignF :: ('a VAR \<Rightarrow> 'a WF_EXPRESSION) set"
  apply (rule_tac x="\<lambda> x. DefaultE (vtype x)" in exI)
  apply (auto simp add:AssignF_def typing defined)
done

declare Rep_AssignF [simp]
declare Rep_AssignF_inverse [simp]
declare Abs_AssignF_inverse [simp]

notation
  Rep_AssignF ("\<langle>_\<rangle>\<^sub>a")

setup_lifting type_definition_AssignF

lift_definition AssignsR ::
"'m AssignF \<Rightarrow> 'm WF_PREDICATE"
is "\<lambda> f. {b. \<forall> v \<in> UNDASHED. \<langle>b\<rangle>\<^sub>b (v\<acute>) = \<langle>(\<langle>f\<rangle>\<^sub>a v)\<rangle>\<^sub>e b}" .

lift_definition IdA :: "'m AssignF" is "VarE"
  by (auto simp add: typing AssignF_def unrest)

lift_definition AssignF_upd :: "'a AssignF \<Rightarrow> 'a VAR \<Rightarrow> 'a WF_EXPRESSION \<Rightarrow> 'a AssignF" 
is "\<lambda> f x v. f(x := ecoerce v x)"
  by (simp add:AssignF_def typing)

nonterminal aupdbinds and aupdbind

syntax
  "_aupdbind" :: "['a, 'a] => aupdbind"               ("(2_ :=\<^sub>a/ _)")
  ""          :: "aupdbind => aupdbinds"              ("_")
  "_aupdbinds":: "[aupdbind, aupdbinds] => aupdbinds" ("_,/ _")
  "_AUpdate"  :: "['a, aupdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

translations
  "_AUpdate f (_aupdbinds b bs)" == "_AUpdate (_AUpdate f b) bs"
  "f(x:=\<^sub>ay)" == "CONST AssignF_upd f x y"

lemma AssignF_upd_rep_eq:
  "\<lbrakk> v \<rhd>\<^sub>e x \<rbrakk> \<Longrightarrow> \<langle>f(x:=\<^sub>av)\<rangle>\<^sub>a = \<langle>f\<rangle>\<^sub>a(x := v)"
  apply (subgoal_tac "\<langle>f\<rangle>\<^sub>a(x := v) \<in> AssignF")
  apply (simp add:AssignF_upd_def)
  apply (auto simp add:typing AssignF_def)
  apply (insert Rep_AssignF[of f])
  apply (simp add:AssignF_def)
done

(*
abbreviation "AssignR x v \<equiv> AssignsR (AssignF_upd IdA x v)"
*)


(*
abbreviation "AssignR x v \<equiv> AssignsR (IdA(x := v))"
*)

nonterminal avar and avars and aexpr and aexprs and assignment

syntax
  "_avar"    :: "'a VAR \<Rightarrow> avar" ("_")
  ""         :: "avar \<Rightarrow> avars" ("_")
  "_avars"   :: "[avar, avars] \<Rightarrow> avars" ("_,/ _")
  "_aexpr"   :: "'a WF_EXPRESSION \<Rightarrow> aexpr" ("_")
  ""         :: "aexpr \<Rightarrow> aexprs" ("_")
  "_aexprs"  :: "[aexpr, aexprs] \<Rightarrow> aexprs" ("_,/ _")
  "_assign"  :: "['a AssignF, avars, aexprs] \<Rightarrow> 'a AssignF" ("(1[_])")
  "_Assignment" :: "avars \<Rightarrow> aexprs \<Rightarrow> 'a WF_PREDICATE" ("(_ /:=\<^sub>R/ _)")   

translations
  "_assign m (_avar x) (_aexpr v)" == "CONST AssignF_upd m x v"
  "_assign m (_avars x xs) (_aexprs v vs)" == "_assign (_assign m x v) xs vs"
  "_Assignment xs vs" == "CONST AssignsR (_assign (CONST IdA) xs vs)"

term "x,y,z :=\<^sub>R $\<^sub>ey,$\<^sub>ex,$\<^sub>ez"

term "AssignsR (AssignF_upd IdA x v)"

lemma AssignsR_SkipR: "AssignsR IdA = II"
  by (auto simp add:SkipR.rep_eq AssignsR.rep_eq IdA.rep_eq VarE.rep_eq)

(*
lemma AssignsR_L1: "x \<noteq> y \<Longrightarrow> (x :=p e) = (x,y :=p e,VarE y)"
  apply (auto simp add:AssignsR.rep_eq VarE.rep_eq IdA.rep_eq AssignF_upd_rep_eq)

lemma AssignsR_L2: "x \<noteq> y \<Longrightarrow> x, y :=p e, f = y,x :=p f,e"
  by (auto simp add:AssignsR.rep_eq VarE.rep_eq IdA_def)
*)

(*
lift_definition AssignR ::
"'VALUE VAR \<Rightarrow>
 'VALUE WF_EXPRESSION \<Rightarrow>
 'VALUE WF_PREDICATE"
is "\<lambda> x e. {b. \<forall> v \<in> UNDASHED . if (v = x) then \<langle>b\<rangle>\<^sub>b v\<acute> = \<langle>e\<rangle>\<^sub>e b 
                                           else \<langle>b\<rangle>\<^sub>b v\<acute> = \<langle>b\<rangle>\<^sub>b v}" .

notation AssignR (infix ":=p" 190)



lemma "AssignRS (IdA(x := v)) = AssignR x v"
  apply (auto simp add:AssignRS.rep_eq AssignR.rep_eq IdA_def VarE.rep_eq)
*)

lift_definition AssignRA ::
"'VALUE VAR \<Rightarrow>
 'VALUE VAR set \<Rightarrow>
 'VALUE WF_EXPRESSION \<Rightarrow>
 'VALUE WF_PREDICATE" is "\<lambda> x vs v. (\<exists>\<^sub>p ((UNDASHED \<union> DASHED) - vs). x :=\<^sub>R v)" .

notation AssignRA (infix ":=\<^bsub>_\<^esub>" 190)

definition ConvR ::
"'VALUE WF_PREDICATE \<Rightarrow>
 'VALUE WF_PREDICATE" where
"ConvR p = SS\<bullet>p"

notation ConvR ("(_\<^sup>\<smile>)" [1000] 999)

setup {*
Adhoc_Overloading.add_variant @{const_name prime} @{const_name ConvR}
*}

definition VarOpenP ::
"'VALUE VAR \<Rightarrow> 'VALUE WF_PREDICATE" ("var") where
"VarOpenP x = (\<exists>\<^sub>p {x}. II)"

definition VarCloseP ::
"'VALUE VAR \<Rightarrow> 'VALUE WF_PREDICATE" ("end") where
"VarCloseP x = (\<exists>\<^sub>p {x\<acute>}. II)"

subsection {* Theorems *}

theorem DASHED_TWICE_NON_REL_VAR [simp,unrest]:
  "DASHED_TWICE \<subseteq> NON_REL_VAR"
  by (auto simp add: NON_REL_VAR_def DASHED_TWICE_def)

subsubsection {* Renaming Theorems *}

text {* Theorems for @{term SS} *}

theorem SS_UNDASHED_app [urename]:
"\<lbrakk>x \<in> UNDASHED\<rbrakk> \<Longrightarrow> SS\<bullet>x = dash x"
  by (simp add: rename_on_rep_eq closure)

theorem SS_DASHED_app [urename]:
"\<lbrakk>x \<in> DASHED\<rbrakk> \<Longrightarrow> SS\<bullet>x = undash x"
  apply (simp add:rename_on_rep_eq closure)
  apply (subgoal_tac "x \<notin> UNDASHED")
  apply (auto simp add:var_contra)
done

theorem SS_DASHED_TWICE_app [urename]:
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS\<bullet>x = x"
  apply (simp add:rename_on_rep_eq closure)
  apply (subgoal_tac "x \<notin> UNDASHED")
  apply (subgoal_tac "x \<notin> dash ` UNDASHED")
  apply (auto simp add:var_contra)
done

theorem SS_ident_app [urename]:
"\<lbrakk>\<not> x \<in> UNDASHED; \<not> x \<in> DASHED\<rbrakk> \<Longrightarrow> SS\<bullet>x = x"
  by (simp add:rename_on_rep_eq closure)

theorem SS_NON_REL_VAR [urename]:
"x \<in> NON_REL_VAR \<Longrightarrow> SS\<bullet>x = x"
  by (simp add:rename_on_rep_eq closure NON_REL_VAR_def)

theorem SS_VAR_RENAME_ON [closure] :
"SS \<in> VAR_RENAME_ON (UNDASHED \<union> DASHED)"
  by (simp add: VAR_RENAME_ON_rename_on[of dash UNDASHED, simplified] closure)

theorem SS_VAR_RENAME_INV [closure] :
"SS \<in> VAR_RENAME_INV"
  by (simp add: VAR_RENAME_INV_rename_on[of dash UNDASHED, simplified] closure)

theorem SS_inv [simp] :
"inv\<^sub>s SS = SS"
  by (simp add:closure)

theorem SS_inv' [simp] :
"inv \<langle>SS\<rangle>\<^sub>s = \<langle>SS\<rangle>\<^sub>s"
  apply (insert SS_inv)
  apply (erule Rep_VAR_RENAME_elim)
  apply (simp only: rename_inv_rep_eq)
done

lemma dash_inv_into_image [simp]: 
  "xs \<subseteq> DASHED \<Longrightarrow> inv_into UNDASHED dash ` xs = undash ` xs"
  by (metis dash_UNDASHED_image image_inv_into_cancel undash_dash_image)
 
theorem SS_UNDASHED_DASHED_image [urename]:
"\<lbrakk>vs \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 SS `\<^sub>s vs = dash ` (in vs) \<union> undash ` (out vs)"
  apply (simp only: rename_on_image closure)
  apply (auto simp add:in_vars_def out_vars_def)
done

theorem SS_DASHED_member :
"x \<in> DASHED \<Longrightarrow> \<not> (SS\<bullet>x) \<in> DASHED"
  by (metis DASHED_dash_elim SS_DASHED_app dash_eq_undash_contra1)

theorem SS_UNDASHED_image :
"\<langle>SS\<rangle>\<^sub>s ` UNDASHED = DASHED"
  by (metis (lifting) SS_UNDASHED_app dash_UNDASHED_image image_cong)

theorem SS_DASHED_image :
"\<langle>SS\<rangle>\<^sub>s ` DASHED = UNDASHED"
  by (metis (lifting) SS_DASHED_app image_cong undash_DASHED_image)

theorem SS_NON_REL_VAR_image :
"\<langle>SS\<rangle>\<^sub>s ` NON_REL_VAR = NON_REL_VAR"
  by (metis (no_types) Compl_eq_Diff_UNIV NON_REL_VAR_def RenameP_image_minus Rep_VAR_RENAME_surj SS_DASHED_image SS_UNDASHED_image image_Un sup_commute)

theorem SS_HOMOGENEOUS_image :
"HOMOGENEOUS vs \<Longrightarrow> \<langle>SS\<rangle>\<^sub>s ` vs = vs"
  apply (auto)
  apply (auto simp add:rename_on_rep_eq closure)
  apply (smt DASHED_dash_elim HOMOGENEOUS_def comp_alphabet_dash comp_vars_undash complete_inj_dom complete_inj_none complete_inj_ran dash_UNDASHED_image dash_elim dash_inv_into dash_undash_DASHED)
  apply (metis HOMOGENEOUS_dash_in in_vars_def out_member)
done

theorems SS_simps =
  SS_UNDASHED_app
  SS_DASHED_app
  SS_DASHED_TWICE_app
  SS_ident_app
  SS_inv
  SS_UNDASHED_DASHED_image
  SS_UNDASHED_image
  SS_DASHED_image
  SS_NON_REL_VAR_image
  SS_HOMOGENEOUS_image

declare SS_simps [urename]

lemma UNREST_NON_REL_VAR_SS [unrest]:
  "UNREST_EXPR NON_REL_VAR v \<Longrightarrow> UNREST_EXPR NON_REL_VAR (SS\<bullet>v)"
  by (auto intro:unrest UNREST_EXPR_subset simp add:urename)

text {* Theorems for @{term SS1} *}

theorem SS1_UNDASHED_app [urename]:
"\<lbrakk>x \<in> UNDASHED\<rbrakk> \<Longrightarrow> SS1\<bullet>x = x"
  by (simp add:rename_on_rep_eq closure)

theorem SS1_DASHED_app [urename]:
"\<lbrakk>x \<in> DASHED\<rbrakk> \<Longrightarrow> SS1\<bullet>x = dash x"
  by (simp add:rename_on_rep_eq closure)

theorem SS1_DASHED_TWICE_app [urename]:
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS1\<bullet>x = undash x"
  apply (simp add:rename_on_rep_eq closure)
  apply (subgoal_tac "x \<notin> DASHED")
  apply (subgoal_tac "x \<in> dash ` DASHED")
  apply (auto simp add:var_contra)
done

theorem SS1_DASHED_THRICE_app [urename]:
"\<lbrakk>x \<in> DASHED_THRICE\<rbrakk> \<Longrightarrow> SS1\<bullet>x = x"
  apply (auto simp add:rename_on_rep_eq closure urename)
  apply (subst complete_inj_none)
  apply (auto)
done

theorem SS1_ident_app [urename]:
"\<lbrakk>\<not> x \<in> DASHED; \<not> x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS1\<bullet>x = x"
  by (simp add:rename_on_rep_eq closure)

theorem SS1_VAR_RENAME_ON [closure] :
"SS1 \<in> VAR_RENAME_ON (DASHED \<union> DASHED_TWICE)"
  by (simp add: VAR_RENAME_ON_rename_on[of dash DASHED, simplified] closure)

theorem SS1_VAR_RENAME_INV [closure] :
"SS1 \<in> VAR_RENAME_INV"
  by (simp add: VAR_RENAME_INV_rename_on[of dash DASHED, simplified] closure)

theorem SS1_inv [simp] :
"inv\<^sub>s SS1 = SS1"
  by (simp add:closure)

theorem SS1_inv' [simp] :
"inv \<langle>SS1\<rangle>\<^sub>s = \<langle>SS1\<rangle>\<^sub>s"
  apply (insert SS1_inv)
  apply (erule Rep_VAR_RENAME_elim)
  apply (simp only: rename_inv_rep_eq)
done

theorem SS1_UNDASHED_DASHED_image [urename] :
"\<lbrakk>vs \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 SS1 `\<^sub>s vs = (in vs) \<union> dash ` (out vs)"
  apply (simp only: rename_on_image closure)
  apply (auto simp add:in_vars_def out_vars_def)
done

(*
theorem SS1_UNDASHED_image [urename] :
"\<langle>SS1\<rangle>\<^sub>s ` UNDASHED = UNDASHED"
  apply (auto simp add:urename)
  apply (metis SS1_UNDASHED_app image_iff)
done
*)

theorem SS1_UNDASHED_image [urename] :
"vs \<subseteq> UNDASHED \<Longrightarrow> \<langle>SS1\<rangle>\<^sub>s ` vs = vs"
  apply (auto simp add:urename)
  apply (metis SS1_UNDASHED_app image_iff set_mp)
done

theorem SS1_DASHED_image [urename] :
"\<langle>SS1\<rangle>\<^sub>s ` DASHED = DASHED_TWICE"
  by (metis (lifting) SS1_DASHED_app dash_DASHED_image image_cong)

theorem SS1_DASHED_TWICE_image [urename] :
"\<langle>SS1\<rangle>\<^sub>s ` DASHED_TWICE = DASHED"
  by (metis (lifting) SS1_DASHED_TWICE_app image_cong undash_DASHED_TWICE_image)

theorem SS1_DASHED_THRICE_image [urename] :
"\<langle>SS1\<rangle>\<^sub>s ` DASHED_THRICE = DASHED_THRICE"
  by (auto simp add:rename_on_rep_eq closure urename)

theorem SS1_NON_REL_VAR_image [urename]:
"\<langle>SS1\<rangle>\<^sub>s ` NON_REL_VAR = (NON_REL_VAR - DASHED_TWICE) \<union> DASHED"
  apply (simp add:NON_REL_VAR_def urename)
  apply (auto)
done

theorems SS1_simps =
  SS1_UNDASHED_app
  SS1_DASHED_app
  SS1_DASHED_TWICE_app
  SS1_DASHED_THRICE_app
  SS1_ident_app
  SS1_UNDASHED_DASHED_image
  SS1_UNDASHED_image
  SS1_DASHED_image
  SS1_DASHED_TWICE_image
  SS1_DASHED_THRICE_image

text {* Theorems for @{term SS2} *}

theorem SS2_DASHED_app [urename]:
"x \<in> DASHED \<Longrightarrow> SS2\<bullet>x = x"
  apply (simp add:rename_on_rep_eq closure)
  apply (subgoal_tac "x \<notin> UNDASHED")
  apply (subgoal_tac "x \<notin> (dash \<circ> dash) ` UNDASHED")
  apply (auto simp add:var_contra)
done

theorem SS2_UNDASHED_app [urename]:
"x \<in> UNDASHED \<Longrightarrow> SS2\<bullet>x = dash (dash x)"
  by (simp add:rename_on_rep_eq closure)

theorem SS2_DASHED_TWICE_app [urename]:
"\<lbrakk>x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS2\<bullet>x =  undash (undash x)"
  apply (simp add:rename_on_rep_eq closure)
  apply (subgoal_tac "x \<notin> UNDASHED")
  apply (subgoal_tac "x \<in> (dash \<circ> dash) ` UNDASHED")
  apply (simp)
  apply (smt DASHED_TWICE_dash_elim dash_elim dash_undash_DASHED dash_undash_DASHED_TWICE f_inv_into_f o_def)
  apply (auto simp add:var_contra)
  apply (metis dash_DASHED_image dash_UNDASHED_image image_compose)
done

lemma SS2_DASHED_THRICE_app [urename]:
  "\<lbrakk>x \<in> DASHED_THRICE\<rbrakk> \<Longrightarrow> SS2\<bullet>x = x"
  apply (auto simp add:rename_on_rep_eq closure urename)
  apply (subst complete_inj_none)
  apply (auto simp add:var_defs)
done

theorem SS2_ident_app [urename]:
"\<lbrakk>\<not> x \<in> UNDASHED; \<not> x \<in> DASHED_TWICE\<rbrakk> \<Longrightarrow> SS2\<bullet>x = x"
  apply (simp add:rename_on_rep_eq closure)
  apply (metis (lifting, full_types) complete_inj_none dash_DASHED_image dash_UNDASHED_image image_compose)
done

theorem SS2_VAR_RENAME_ON [closure] :
"SS2 \<in> VAR_RENAME_ON (UNDASHED \<union> DASHED_TWICE)"
  by (insert VAR_RENAME_ON_rename_on[of "dash \<circ> dash" UNDASHED, simplified], simp add:image_compose closure)

theorem SS2_VAR_RENAME_INV [closure] :
"SS2 \<in> VAR_RENAME_INV"
  by (metis VAR_RENAME_INV_rename_on dash_dash_UNDASHED_rename_func subset_refl)

theorem SS2_inv [simp] :
"inv\<^sub>s SS2 = SS2"
  by (simp add:closure)

theorem SS2_inv' [simp] :
"inv \<langle>SS2\<rangle>\<^sub>s = \<langle>SS2\<rangle>\<^sub>s"
  apply (insert SS2_inv)
  apply (erule Rep_VAR_RENAME_elim)
  apply (simp only: rename_inv_rep_eq)
done

theorem SS2_UNDASHED_DASHED_image [urename]:
"\<lbrakk>vs \<subseteq> UNDASHED \<union> DASHED\<rbrakk> \<Longrightarrow>
 SS2 `\<^sub>s vs = dash ` dash ` (in vs) \<union> (out vs)"
  apply (simp only: rename_on_image closure)
  apply (auto simp add:in_vars_def out_vars_def image_compose)
done

theorem SS2_UNDASHED_image [urename] :
"\<langle>SS2\<rangle>\<^sub>s ` UNDASHED = DASHED_TWICE"
  apply (auto simp add:urename)
  apply (metis DASHED_TWICE_dash_elim DASHED_dash_elim SS2_UNDASHED_app imageI)
done

theorem SS2_DASHED_image [urename] :
"vs \<subseteq> DASHED \<Longrightarrow> \<langle>SS2\<rangle>\<^sub>s ` vs = vs"
  apply (auto simp add:urename)
  apply (metis (hide_lams, no_types) SS2_DASHED_app image_iff set_mp)
done

theorem SS2_DASHED_TWICE_image [urename] :
"\<langle>SS2\<rangle>\<^sub>s ` DASHED_TWICE = UNDASHED"
  by (metis (hide_lams, no_types) SS2_UNDASHED_image SS2_VAR_RENAME_INV VAR_RENAME_INV_comp' id_apply image_compose image_id)

theorem SS2_DASHED_THRICE_image [urename] :
"\<langle>SS2\<rangle>\<^sub>s ` DASHED_THRICE = DASHED_THRICE"
  apply (auto simp add:rename_on_rep_eq closure urename)
  apply (subst complete_inj_none)
  apply (auto)
  apply (auto simp add:var_defs)[1]
  apply (metis SS2_DASHED_THRICE_app dash_dash_UNDASHED_rename_func equalityE image_eqI rename_on_rep_eq)
done

theorem SS2_NON_REL_VAR_image [urename]:
"\<langle>SS2\<rangle>\<^sub>s ` NON_REL_VAR = (NON_REL_VAR - DASHED_TWICE) \<union> UNDASHED"
  apply (simp add:NON_REL_VAR_def urename)
  apply (auto)
done

theorems SS2_simps =
  SS2_UNDASHED_app
  SS2_DASHED_app
  SS2_DASHED_TWICE_app
  SS2_DASHED_THRICE_app
  SS2_ident_app
  SS2_UNDASHED_DASHED_image

subsubsection {* Renamings Equalities *}

lemma SS1_SS_eq_SS2: "SS1 \<circ>\<^sub>s SS \<cong>\<^sub>s SS2 on UNDASHED"
  by (auto simp add:rename_equiv_def urename)

lemma SS2_SS_eq_SS1: "SS2 \<circ>\<^sub>s SS \<cong>\<^sub>s SS1 on DASHED"
  by (auto simp add:rename_equiv_def urename)

lemma SS1_eq_id: "SS1 \<cong>\<^sub>s id\<^sub>s on UNDASHED"
  by (auto simp add:rename_equiv_def urename)

lemma SS2_eq_id: "SS2 \<cong>\<^sub>s id\<^sub>s on DASHED"
  by (auto simp add:rename_equiv_def urename)

subsubsection {* Theorems for @{term "COMPOSABLE_BINDINGS"} *}

theorem COMPOSABLE_BINDINGS_dash [intro] :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS; x \<in> UNDASHED\<rbrakk> \<Longrightarrow> \<langle>b1\<rangle>\<^sub>b (dash x) = \<langle>b2\<rangle>\<^sub>b x"
apply (simp add: COMPOSABLE_BINDINGS_def)
done

theorem COMPOSABLE_BINDINGS_ident [intro] :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS; \<not> x \<in> UNDASHED; \<not> x \<in> DASHED\<rbrakk> \<Longrightarrow> \<langle>b1\<rangle>\<^sub>b x = \<langle>b2\<rangle>\<^sub>b x"
apply (simp only: COMPOSABLE_BINDINGS_def)
apply (simp add: NON_REL_VAR_def)
apply (simp add: binding_equiv_def)
done

subsubsection {* @{term UNREST} theorems *}

theorem UNREST_SkipR [unrest]:
"vs \<subseteq> NON_REL_VAR \<Longrightarrow> UNREST vs II"
  by (auto intro: UNREST_subset simp add:SkipR_def UNREST_def WF_BINDING_def override_on_def NON_REL_VAR_def)

theorem UNREST_SkipR_DASHED_TWICE [unrest]:
"UNREST DASHED_TWICE II"
  by (blast intro!:unrest intro:UNREST_subset)

lemma [dest]: "x \<notin> NON_REL_VAR \<Longrightarrow> x \<in> REL_VAR"
  by (simp add:NON_REL_VAR_def)

lemma [dest]: "\<lbrakk> x \<in> REL_VAR; x \<in> NON_REL_VAR \<rbrakk> \<Longrightarrow> False"
  by (simp add:NON_REL_VAR_def)

lemma [dest]: "\<lbrakk> x \<in> NON_REL_VAR; x \<in> REL_VAR \<rbrakk> \<Longrightarrow> False"
  by (simp add:NON_REL_VAR_def)

theorem UNREST_SkipRA [unrest]:
"UNREST (VAR - vs) (II\<^bsub>vs\<^esub>)"
  apply (simp add:SkipRA_def)
  apply (force intro:unrest)
done

theorem UNREST_SkipRA_NON_REL_VAR [unrest]:
"UNREST NON_REL_VAR (II\<^bsub>vs\<^esub>)"
  by (auto intro:closure unrest simp add:SkipRA_def)

theorem UNREST_SkipRA_DASHED_TWICE [unrest]:
"UNREST DASHED_TWICE (II\<^bsub>vs\<^esub>)"
  by (auto intro:closure unrest simp add:SkipRA_def)
  
theorem UNREST_AssignR [unrest]:
"\<lbrakk> x \<in> UNDASHED; NON_REL_VAR \<sharp> v \<rbrakk> \<Longrightarrow> NON_REL_VAR \<sharp> (x :=\<^sub>R v)"
  by (simp add:UNREST_def AssignsR.rep_eq AssignF_upd.rep_eq IdA.rep_eq unrest)

theorem UNREST_AssignR_DASHED_TWICE [unrest]:
"\<lbrakk> x \<in> UNDASHED; UNREST_EXPR DASHED_TWICE v \<rbrakk> \<Longrightarrow> UNREST DASHED_TWICE (x :=\<^sub>R v)"
  by (simp add:UNREST_def AssignsR.rep_eq AssignF_upd.rep_eq IdA.rep_eq unrest)

(* FIXME: Add complete set of UNREST rules for n-ary assignments (AssignF) *)

theorem UNREST_AssignRA [unrest]:
"\<lbrakk> x \<in> UNDASHED; (VAR - vs) \<sharp> v; vs \<subseteq> REL_VAR \<rbrakk> \<Longrightarrow> (VAR - vs) \<sharp> (x :=\<^bsub>vs\<^esub> v)"
  apply (simp add:AssignRA_def)
  apply (rule unrest) back
  apply (rule unrest) back
  apply (auto)
  apply (rule UNREST_EXPR_subset)
  apply (auto)
done

theorem UNREST_AssignRA' [unrest]:
"\<lbrakk> x \<in> UNDASHED; (VAR - vs2) \<sharp> v; vs2 \<subseteq> REL_VAR; vs1 \<subseteq> (VAR - vs2) \<rbrakk> \<Longrightarrow>
  vs1 \<sharp> (x :=\<^bsub>vs2\<^esub> v)"
  by (metis UNREST_AssignRA UNREST_subset)

lemma UNREST_EXPR_NON_REL_VAR_PrimeE [unrest]:
  "UNREST_EXPR NON_REL_VAR v \<Longrightarrow> UNREST_EXPR NON_REL_VAR v\<acute>"
  by (metis PrimeE_def UNREST_NON_REL_VAR_SS)

(*
theorem UNREST_AssignR [unrest]:
"\<lbrakk> UNREST_EXPR (VAR - vs1) v \<rbrakk> \<Longrightarrow> 
 UNREST (VAR - ({dash x} \<union> (vs1 \<union> vs2))) (x :=p\<^bsub>vs2\<^esub> v)"
  apply (simp add:AssignR_def)
  apply (rule unrest)
  apply (force intro :unrest)
  apply (force intro :unrest)
done
*)

(*
theorem UNREST_AssignR [unrest]:
"\<lbrakk> UNREST_EXPR (VAR - vs) v \<rbrakk> \<Longrightarrow> 
 UNREST (VAR - ({dash x} \<union> vs)) (x :=p\<^bsub>vs\<^esub> v)"
  apply (subgoal_tac "(VAR - insert (dash x) vs) = (VAR - {dash x}) \<inter> (- vs)") 
  apply (simp add:AssignR_def)
  apply (force intro:closure unrest simp add:AssignR_def)
  apply (auto)
done
*)

theorem UNREST_CondR [unrest]: 
  "\<lbrakk>UNREST vs p1; UNREST vs p2; UNREST vs b\<rbrakk> \<Longrightarrow>
   UNREST vs (p1 \<lhd> b \<rhd> p2)"
  by (auto intro:unrest simp add:CondR_def)

subsubsection {* Closure Theorems *}

theorem WF_CONDITION_WF_RELATION [closure]:
"p \<in> WF_CONDITION \<Longrightarrow> p \<in> WF_RELATION"
  by (auto simp add:WF_CONDITION_def)

theorem WF_POSTCOND_WF_RELATION [closure]:
"p \<in> WF_POSTCOND \<Longrightarrow> p \<in> WF_RELATION"
  by (auto simp add:WF_POSTCOND_def)

lemma WF_ASSIGN_WF_POSTCOND [closure]:
  "P \<in> WF_ASSIGN vs \<Longrightarrow> P \<in> WF_POSTCOND"
  apply (auto simp add:WF_ASSIGN_def WF_POSTCOND_def WF_RELATION_def)
  apply (force intro:UNREST_subset)
  apply (rule UNREST_subset)
  apply (auto)
done

theorem UNREST_DASHED_TWICE_WF_RELATION [closure]:
"p \<in> WF_RELATION \<Longrightarrow> UNREST DASHED_TWICE p"
  by (auto intro:unrest UNREST_subset simp add:WF_RELATION_def)

theorem UNREST_NON_REL_VAR_WF_RELATION [closure]:
"p \<in> WF_RELATION \<Longrightarrow> UNREST NON_REL_VAR p"
  by (simp add:WF_RELATION_def)

lemma UNREST_WF_CONDITION [closure]:
  "p \<in> WF_CONDITION \<Longrightarrow> UNREST (VAR - UNDASHED) p"
  apply (clarsimp simp add:WF_CONDITION_def WF_RELATION_def)
  apply (rule UNREST_subset)
  apply (rule UNREST_union)
  apply (assumption)
  apply (assumption) back
  apply (auto)
done

lemma WF_RELATION_UNREST_elim [elim]:
  "\<lbrakk> p \<in> WF_RELATION; UNREST NON_REL_VAR p \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp add:WF_RELATION_def)

theorem TrueP_rel_closure [closure]:
"true \<in> WF_RELATION"
  by (simp add:WF_RELATION_def unrest)

theorem TrueP_cond_closure [closure]:
"true \<in> WF_CONDITION"
  by (auto intro:closure unrest simp add:WF_CONDITION_def)

theorem FalseP_rel_closure [closure]:
"false \<in> WF_RELATION"
  by (simp add:WF_RELATION_def unrest)

theorem FalseP_cond_closure [closure]:
"false \<in> WF_CONDITION"
  by (auto intro:closure unrest simp add:WF_CONDITION_def)

theorem OrP_rel_closure [closure]:
  "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> p \<or>\<^sub>p q \<in> WF_RELATION"
  by (auto simp add:WF_RELATION_def intro:unrest)

theorem OrP_cond_closure [closure]:
  "\<lbrakk> p \<in> WF_CONDITION; q \<in> WF_CONDITION \<rbrakk> \<Longrightarrow> p \<or>\<^sub>p q \<in> WF_CONDITION"
  by (auto simp add:WF_CONDITION_def intro:unrest closure)

theorem AndP_rel_closure [closure]:
  "\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION \<rbrakk> \<Longrightarrow> p \<and>\<^sub>p q \<in> WF_RELATION"
  by (auto simp add:WF_RELATION_def intro:unrest)

theorem AndP_cond_closure [closure]:
  "\<lbrakk> p \<in> WF_CONDITION; q \<in> WF_CONDITION \<rbrakk> \<Longrightarrow> p \<and>\<^sub>p q \<in> WF_CONDITION"
  by (auto simp add:WF_CONDITION_def intro:unrest closure)

theorem NotP_rel_closure [closure]:
  "\<lbrakk> p \<in> WF_RELATION \<rbrakk> \<Longrightarrow> \<not>\<^sub>p p \<in> WF_RELATION"
  by (auto simp add:WF_RELATION_def intro:unrest)

theorem NotP_cond_closure [closure]:
  "\<lbrakk> p \<in> WF_CONDITION \<rbrakk> \<Longrightarrow> \<not>\<^sub>p p \<in> WF_CONDITION"
  by (auto simp add:WF_CONDITION_def intro:unrest closure)

lemma ImpliesP_rel_closure [closure]:
  "\<lbrakk>p \<in> WF_RELATION; q \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
   p \<Rightarrow>\<^sub>p q \<in> WF_RELATION"
  by (auto intro:unrest simp add:WF_RELATION_def)

lemma ImpliesP_cond_closure [closure]:
  "\<lbrakk>p \<in> WF_CONDITION; q \<in> WF_CONDITION\<rbrakk> \<Longrightarrow>
   p \<Rightarrow>\<^sub>p q \<in> WF_CONDITION"
  by (auto intro:unrest closure simp add:WF_CONDITION_def)

lemma ExistsP_rel_closure [closure]:
  "p \<in> WF_RELATION \<Longrightarrow> (\<exists>\<^sub>p vs. p) \<in> WF_RELATION"
  apply (simp add:WF_RELATION_def)
  apply (simp add:unrest)
done

theorem SkipR_closure [closure] :
"II \<in> WF_RELATION"
  by (simp add:WF_RELATION_def unrest)

theorem SkipRA_closure [closure] :
"vs \<subseteq> UNDASHED \<union> DASHED \<Longrightarrow> (II\<^bsub>vs\<^esub>) \<in> WF_RELATION"
  by (simp add:WF_RELATION_def unrest)

lemma AssignRA_rel_closure [closure]:
  "\<lbrakk> x \<in> UNDASHED; (VAR - vs) \<sharp> v; vs \<subseteq> REL_VAR \<rbrakk> \<Longrightarrow>
     x :=\<^bsub>vs\<^esub> v \<in> WF_RELATION"
  apply (simp add:WF_RELATION_def)
  apply (subgoal_tac "NON_REL_VAR = (VAR - REL_VAR :: 'a VAR set)")
  apply (metis (hide_lams, no_types) Diff_mono UNREST_AssignRA UNREST_subset VAR_subset)
  apply (auto)
done

theorem CondR_rel_closure [closure] :
"\<lbrakk> p1 \<in> WF_RELATION; p2 \<in> WF_RELATION; b \<in> WF_RELATION \<rbrakk> \<Longrightarrow>
   p1 \<lhd> b \<rhd> p2 \<in> WF_RELATION"
  by (simp add: CondR_def closure)

lemma SS_rel_closure [closure]:
  "P \<in> WF_RELATION \<Longrightarrow> SS\<bullet>P \<in> WF_RELATION"
  by (auto intro:unrest simp add:WF_RELATION_def urename)

theorem ConvR_rel_closure [closure] :
  "\<lbrakk> p \<in> WF_RELATION \<rbrakk> \<Longrightarrow> p\<^sup>\<smile> \<in> WF_RELATION"
  by (metis ConvR_def SS_rel_closure)

lemma PrimeP_WF_CONDITION_WF_POSTCOND [closure]:
  "p \<in> WF_CONDITION \<Longrightarrow> p\<acute> \<in> WF_POSTCOND"
  apply (simp add:WF_CONDITION_def WF_POSTCOND_def)
  apply (simp add:closure)
  apply (auto simp add:ConvR_def unrest urename)
done

lemma VarP_rel_closure [closure]:
  "x \<in> REL_VAR \<Longrightarrow> $\<^sub>px \<in> WF_RELATION"
  by (auto intro:unrest simp add:WF_RELATION_def)

lemma VarP_cond_closure [closure]:
  "x \<in> UNDASHED \<Longrightarrow> $\<^sub>px \<in> WF_CONDITION"
  by (auto intro:unrest simp add:WF_RELATION_def WF_CONDITION_def NON_REL_VAR_def)

lemma VarP_precond_closure [closure]:
  "x \<in> DASHED \<Longrightarrow> $\<^sub>px \<in> WF_POSTCOND"
  by (auto intro:unrest simp add:WF_RELATION_def WF_POSTCOND_def NON_REL_VAR_def)

lemma EqualP_rel_closure [closure]:
  "\<lbrakk> UNREST_EXPR NON_REL_VAR e; UNREST_EXPR NON_REL_VAR f \<rbrakk> \<Longrightarrow> (e ==\<^sub>p f) \<in> WF_RELATION"
  apply (simp add:WF_CONDITION_def WF_RELATION_def NON_REL_VAR_def)
  apply (auto intro:unrest)
done

lemma EqualP_cond_closure [closure]:
  "\<lbrakk> UNREST_EXPR (-UNDASHED) e; UNREST_EXPR (-UNDASHED) f \<rbrakk> \<Longrightarrow> (e ==\<^sub>p f) \<in> WF_CONDITION"
  apply (simp add:WF_CONDITION_def WF_RELATION_def NON_REL_VAR_def)
  apply (auto intro:unrest UNREST_EXPR_subset)
done

lemma EqualP_assign_closure[closure]:
  "\<lbrakk> v : vtype x; x \<in> DASHED \<rbrakk> \<Longrightarrow> ($\<^sub>ex ==\<^sub>p LitE v) \<in> WF_ASSIGN {x}"
  apply (auto simp add:WF_ASSIGN_def)
  apply (simp add:EqualP_def LitE_rep_eq VarE.rep_eq)
  apply (simp add:unrest)
done

subsection {* Validation of Soundness *}

lemma SemiR_algebraic_lemma1 :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS\<rbrakk> \<Longrightarrow>
  CompB ((b1 \<oplus>\<^sub>b b2 on DASHED) \<oplus>\<^sub>b (RenameB SS1 b1) on DASHED_TWICE) SS1 =
   b1 \<oplus>\<^sub>b (RenameB SS1 b2) on DASHED_TWICE"
apply (rule Rep_WF_BINDING_intro)
apply (simp add:CompB_rep_eq)
apply (rule ext)
apply (simp add: RenameB_def closure)
apply (case_tac "x \<in> UNDASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
done

lemma SemiR_algebraic_lemma2 :
"\<lbrakk>(b1, b2) \<in> COMPOSABLE_BINDINGS\<rbrakk> \<Longrightarrow>
 CompB ((b1 \<oplus>\<^sub>b b2 on DASHED) \<oplus>\<^sub>b (RenameB SS1 b1) on DASHED_TWICE) SS2 =
   b2 \<oplus>\<^sub>b (RenameB SS2 b1) on DASHED_TWICE"
apply (rule Rep_WF_BINDING_intro)
apply (simp)
apply (rule ext)
apply (simp add: RenameB_def closure)
apply (case_tac "x \<in> UNDASHED")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: COMPOSABLE_BINDINGS_dash)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
apply (simp add: COMPOSABLE_BINDINGS_ident)
done

theorem SemiR_algebraic :
"\<lbrakk>UNREST DASHED_TWICE p1;
 UNREST DASHED_TWICE p2\<rbrakk> \<Longrightarrow>
 p1 ; p2 = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>p2))"
apply (rule sym)
apply (utp_pred_tac)
apply (simp add: EvalP_def)
apply (simp add: SemiR_def)
apply (safe)
-- {* Subgoal 1 *}
apply (rule_tac x =
  "RenameB (inv\<^sub>s SS1) (b \<oplus>\<^sub>b b' on DASHED_TWICE) \<oplus>\<^sub>b b on DASHED_TWICE" in exI)
apply (rule_tac x =
  "RenameB (inv\<^sub>s SS2) (b \<oplus>\<^sub>b b' on DASHED_TWICE) \<oplus>\<^sub>b b on DASHED_TWICE" in exI)
apply (safe)
-- {* Subgoal 1.1 *}
apply (simp add: closure)
apply (rule Rep_WF_BINDING_intro)
apply (rule ext)
apply (case_tac "x \<in> DASHED")
apply (simp add: SS1_simps SS2_simps)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
-- {* Subgoal 1.2 *}
apply (auto intro: UNREST_binding_override) [1]
-- {* Subgoal 1.3 *}
apply (auto intro: UNREST_binding_override) [1]
-- {* Subgoal 1.3 *}
apply (simp add: RenameB_def closure)
apply (simp add: COMPOSABLE_BINDINGS_def)
apply (safe)
apply (simp add: SS1_simps SS2_simps)
apply (simp add: binding_equiv_def)
apply (simp add: NON_REL_VAR_def)
apply (rule ballI)
apply (clarsimp)
apply (case_tac "x \<in> DASHED_TWICE")
apply (simp add: SS1_simps SS2_simps)
apply (simp add: SS1_simps SS2_simps)
-- {* Subgoal 2 *}
apply (simp add: RenameB_def closure)
apply (rule_tac x = "RenameB SS1 b1" in exI)
apply (rule conjI)
-- {* Subgoal 2.1 *}
apply (simp add: SemiR_algebraic_lemma1)
apply (auto intro: UNREST_binding_override simp: closure) [1]
-- {* Subgoal 2.2 *}
apply (simp add: SemiR_algebraic_lemma2)
apply (auto intro: UNREST_binding_override simp: closure) [1]
done

theorem SemiR_algebraic_rel :
"\<lbrakk> p1 \<in> WF_RELATION; p2 \<in> WF_RELATION \<rbrakk> 
  \<Longrightarrow> p1 ; p2 = (\<exists>\<^sub>p DASHED_TWICE . (SS1\<bullet>p1) \<and>\<^sub>p (SS2\<bullet>p2))"
  apply (rule SemiR_algebraic)
  apply (simp_all add:WF_RELATION_def)
  apply (simp_all add:unrest UNREST_subset)
done

lemma VAR_minus_inter: 
  "(VAR - xs) \<inter> (VAR - ys) = (VAR - (xs \<union> ys))"
  by (auto)

lemma UNREST_SemiR_general:
      "\<lbrakk> vs1 \<sharp> p1; vs2 \<sharp> p2
       ; vs3 = (in vs1 \<union> out vs2 \<union> nrel (vs1 \<inter> vs2)) \<rbrakk> 
       \<Longrightarrow> vs3 \<sharp> (p1 ; p2)"
  apply (subst UNREST_def)
  apply (auto simp add:SemiR.rep_eq)
  apply (rule_tac x="b1a \<oplus>\<^sub>b b2a on in vs1 \<union> nrel (vs1 \<inter> vs2)" in exI)
  apply (rule_tac x="b2 \<oplus>\<^sub>b b2a on out vs2 \<union> nrel (vs1 \<inter> vs2)" in exI)
  apply (auto)
  apply (rule)
  apply (simp add:override_on_def)
  apply (rule)
  apply (auto simp add:var_defs nrel_vars_def)[1]
  apply (metis UNREST_binding_override UNREST_inter_1 UNREST_union in_vars_def nrel_vars_def)
  apply (metis UNREST_def UNREST_inter_1 UNREST_inter_2 UNREST_union nrel_vars_def out_vars_def)
  apply (auto simp add:COMPOSABLE_BINDINGS_def)
  apply (metis DASHED_not_NON_REL_VAR Int_iff UNDASHED_dash_DASHED UNDASHED_not_DASHED UNDASHED_not_NON_REL_VAR UnE nrel_vars_def out_vars_def override_on_apply_notin utp_var.not_dash_member_in)
  apply (rule binding_equiv_override_right_intro)
  apply (simp_all add: nrel_vars_def[THEN sym] var_dist)
  apply (rule binding_equiv_comm)
  apply (rule binding_equiv_override_right_intro)
  apply (simp_all add: nrel_vars_def[THEN sym] var_dist)
  apply (metis (hide_lams, no_types) Compl_eq_Diff_UNIV Diff_Int Int_Diff Int_UNIV_left binding_equiv_comm binding_equiv_minus in_vars_def inf.left_idem inf_commute)
  apply (subst Int_commute) back back
  apply (subst Int_assoc[THEN sym])
  apply (simp add:nrel_vars_def[THEN sym] var_dist nrel_NON_REL_VAR)
  apply (metis (hide_lams, no_types) Diff_Int Diff_Int_distrib Diff_cancel Int_left_commute binding_equiv_empty diff_eq inf_bot_right)
  apply (metis binding_equiv_subset binding_override_equiv1 sup_ge2)
done

lemma UNREST_SemiR:
      "\<lbrakk> UNREST (VAR - vs1) p1; UNREST (VAR - vs2) p2
       ; vs1 \<subseteq> UNDASHED \<union> DASHED; vs2 \<subseteq> UNDASHED \<union> DASHED
       ; vs3 = (VAR - (in vs1 \<union> out vs2)) \<rbrakk> 
       \<Longrightarrow> UNREST vs3 (p1 ; p2)"
  apply (rule UNREST_SemiR_general)
  apply (auto simp add:var_defs)
done

lemma UNREST_SemiR_UNDASHED [unrest]:
  "\<lbrakk> vs \<sharp> P; vs \<subseteq> UNDASHED \<rbrakk> \<Longrightarrow> vs \<sharp> (P ; Q)"
  apply (rule UNREST_SemiR_general[of _ _ "{}"])
  apply (simp_all add:var_dist unrest)
  apply (metis in_of_UNDASHED)
done

lemma UNREST_SemiR_DASHED [unrest]:
  "\<lbrakk> vs \<sharp> Q; vs \<subseteq> DASHED \<rbrakk> \<Longrightarrow> vs \<sharp> (P ; Q)"
  apply (rule UNREST_SemiR_general[of "{}"])
  apply (simp_all add:var_dist unrest)
  apply (metis out_of_DASHED)
done

lemma UNREST_SemiR_DASHED_TWICE [unrest]:
  "\<lbrakk> UNREST DASHED_TWICE p; UNREST DASHED_TWICE q \<rbrakk> \<Longrightarrow> UNREST DASHED_TWICE (p ; q)"
  apply (simp add:SemiR_algebraic)
  apply (force intro:unrest)
done

lemma UNREST_SemiR_NON_REL_VAR_single [unrest]:
  "\<lbrakk> x \<in> NON_REL_VAR; {x} \<sharp> P; {x} \<sharp> Q \<rbrakk> \<Longrightarrow> {x} \<sharp> (P ; Q)"
  apply (rule UNREST_SemiR_general)
  apply (auto simp add:var_defs)
done
 
lemma UNREST_SemiR_NON_REL_VAR [unrest]:
  "\<lbrakk> UNREST NON_REL_VAR p; UNREST NON_REL_VAR q \<rbrakk> \<Longrightarrow> UNREST NON_REL_VAR (p ; q)"
  apply (rule UNREST_SemiR_general)
  apply (simp_all)
  apply (simp add:var_dist)
done

theorem SemiR_closure [closure] :
"\<lbrakk>p1 \<in> WF_RELATION;
 p2 \<in> WF_RELATION\<rbrakk> \<Longrightarrow>
 p1 ; p2 \<in> WF_RELATION"
  apply (simp add:WF_RELATION_def)
  apply (blast intro:unrest)
done

theorem AssignR_rel_closure [closure] :
  "\<lbrakk> x \<in> UNDASHED; NON_REL_VAR \<sharp> v \<rbrakk> \<Longrightarrow> x :=\<^sub>R v \<in> WF_RELATION"
  apply (simp add:WF_RELATION_def)
  apply (simp add:unrest)
done

subsubsection {* Evaluation Theorems *}

theorem EvalP_SkipR [eval] :
"\<lbrakk>II\<rbrakk>b \<longleftrightarrow> (\<forall> v \<in> UNDASHED . \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b (dash v))"
apply (simp add: EvalP_def)
apply (simp add: SkipR_def)
done

theorem EvalP_SkipRA [eval] :
"HOMOGENEOUS vs \<Longrightarrow> \<lbrakk>II\<^bsub>vs\<^esub>\<rbrakk>b \<longleftrightarrow> (\<forall> v \<in> in vs . \<langle>b\<rangle>\<^sub>b v = \<langle>b\<rangle>\<^sub>b (dash v))"
  by (auto simp add: EvalP_def SkipRA_rep_eq_alt)

declare CondR_def [eval]

declare SemiR_algebraic [eval]

subsection {* Proof Experiments *}

theorem SemiP_assoc :
"\<lbrakk>UNREST DASHED_TWICE p1;
 UNREST DASHED_TWICE p2;
 UNREST DASHED_TWICE p3\<rbrakk> \<Longrightarrow>
 p1 ; (p2 ; p3) = (p1 ; p2) ; p3"
apply (subgoal_tac "UNREST DASHED_TWICE (p2 ; p3)")
apply (subgoal_tac "UNREST DASHED_TWICE (p1 ; p2)")
apply (utp_pred_tac)
apply (auto)
oops

lemma SkipR_as_SkipRA: "II = (II\<^bsub>REL_VAR\<^esub>)"
  apply (utp_pred_auto_tac)
  apply (simp add:var_dist)
done

lemma SkipR_ExistsP_in:
  "HOMOGENEOUS vs \<Longrightarrow> (\<exists>\<^sub>p vs. II) = (\<exists>\<^sub>p (in vs). II)"
  apply (utp_pred_auto_tac)
  apply (rule_tac x="RenameB SS b" in exI)
  apply (auto)
  apply (case_tac "v \<in> in vs")
  apply (simp add:urename)
  apply (metis (hide_lams, no_types) IntI hom_alphabet_dash in_vars_def override_on_def)
  apply (rule_tac x="\<B>" in exI)
  apply (auto)
  apply (case_tac "v \<in> vs")
  apply (auto)
  apply (subgoal_tac "v\<acute> \<notin> vs")
  apply (auto)
  apply (metis (hide_lams, no_types) Int_iff in_vars_def override_on_def)
done

lemma SkipR_ExistsP_out:
  "HOMOGENEOUS vs \<Longrightarrow> (\<exists>\<^sub>p vs. II) = (\<exists>\<^sub>p (out vs). II)"
  apply (utp_pred_auto_tac)
  apply (rule_tac x="RenameB SS b" in exI)
  apply (auto)
  apply (case_tac "v\<acute> \<in> out vs")
  apply (subgoal_tac "v \<notin> out vs")
  apply (simp add:urename RenameB_rep_eq)
  apply (metis Int_iff UNDASHED_not_DASHED out_vars_def)
  apply (case_tac "v\<acute> \<in> out vs")
  apply (simp_all)
  apply (subgoal_tac "v \<notin> out vs")
  apply (simp_all)
  apply (metis (mono_tags) UNDASHED_dash_DASHED hom_alphabet_undash out_member override_on_def)
  apply (metis Int_iff UNDASHED_not_DASHED out_vars_def)
  
  apply (rule_tac x="\<B>" in exI)
  apply (rule)
  apply (case_tac "v \<in> vs")
  apply (subgoal_tac "v\<acute> \<in> vs")
  apply (auto)
  apply (subgoal_tac "v\<acute> \<notin> vs")
  apply (auto)
  apply (smt Int_commute out_vars_def override_on_apply_notin override_on_cancel5)
done

end

(* FIXME: This is way assignments *should* be implemented but its too horrifying
to make all the changes need to implement it at the moment:

definition 
  "AssignF = {f :: 'a VAR \<rightharpoonup> 'a WF_EXPRESSION. (\<forall> x \<in> dom f. (the (f x) \<rhd>\<^sub>e x)) \<and> dom f \<subseteq> UNDASHED}"

typedef 'a AssignF = "AssignF :: ('a VAR \<rightharpoonup> 'a WF_EXPRESSION) set"
  by (auto simp add:AssignF_def)

declare Rep_AssignF [simp]
declare Rep_AssignF_inverse [simp]
declare Abs_AssignF_inverse [simp]

abbreviation Rep_AssignF_the :: "'a AssignF \<Rightarrow> 'a VAR \<Rightarrow> 'a WF_EXPRESSION" where
"Rep_AssignF_the f \<equiv> the \<circ> (Rep_AssignF f)"

notation
  Rep_AssignF ("\<langle>_\<rangle>\<^sub>a")

lemma AssignF_dom_DASHED:
  "dom \<langle>f\<rangle>\<^sub>a \<subseteq> UNDASHED"
  apply (insert Rep_AssignF[of "f"])
  apply (simp add:AssignF_def)
done

lemma AssignF_dom_DASHED_var:
  "x \<in> dom \<langle>f\<rangle>\<^sub>a \<Longrightarrow> x \<in> UNDASHED"
  apply (insert Rep_AssignF[of "f"])
  apply (auto simp add:AssignF_def)
done

(*
lemma UNREST_AssignF [unrest]: 
  "v \<in> ran \<langle>f\<rangle>\<^sub>a \<Longrightarrow> NON_REL_VAR \<sharp> v"
  apply (insert Rep_AssignF[of "f"])
  apply (auto simp add:AssignF_def ran_def)
  apply (drule_tac x="a" in bspec)
  apply (auto)
done
*)

setup_lifting type_definition_AssignF

lemma Rep_AssignF_compat [typing]:
  "x \<in> dom \<langle>f\<rangle>\<^sub>a \<Longrightarrow> the (\<langle>f\<rangle>\<^sub>a x) \<rhd>\<^sub>e x"
  apply (insert Rep_AssignF[of f])
  apply (auto simp add:AssignF_def)
done

lift_definition AssignsR ::
"'m AssignF \<Rightarrow> 'm WF_PREDICATE"
is "\<lambda> f. {b. \<forall> v \<in> dom \<langle>f\<rangle>\<^sub>a. \<langle>b\<rangle>\<^sub>b v\<acute> = \<langle>the (\<langle>f\<rangle>\<^sub>a v)\<rangle>\<^sub>e b}" .

lift_definition IdA :: "'m AssignF" 
  is "\<lambda> x. if x \<in> D\<^sub>0 then \<lfloor>$\<^sub>ex\<rfloor> else None"
  apply (auto simp add: typing AssignF_def unrest)
  apply (metis option.distinct(1))
done

definition AssignF_upd :: "'a AssignF \<Rightarrow> 'a VAR \<Rightarrow> 'a WF_EXPRESSION \<Rightarrow> 'a AssignF" where
"AssignF_upd f x v = Abs_AssignF (\<langle>f\<rangle>\<^sub>a(x := Some v))"

nonterminal aupdbinds and aupdbind

syntax
  "_aupdbind" :: "['a, 'a] => aupdbind"               ("(2_ :=\<^sub>a/ _)")
  ""          :: "aupdbind => aupdbinds"              ("_")
  "_aupdbinds":: "[aupdbind, aupdbinds] => aupdbinds" ("_,/ _")
  "_AUpdate"  :: "['a, aupdbinds] => 'a"              ("_/'((_)')" [1000, 0] 900)

translations
  "_AUpdate f (_aupdbinds b bs)" == "_AUpdate (_AUpdate f b) bs"
  "f(x:=\<^sub>ay)" == "CONST AssignF_upd f x y"

lemma AssignF_upd_rep_eq:
  "\<lbrakk> v \<rhd>\<^sub>e x; x \<in> D\<^sub>0 \<rbrakk> \<Longrightarrow> \<langle>f(x:=\<^sub>av)\<rangle>\<^sub>a = \<langle>f\<rangle>\<^sub>a(x := Some v)"
  apply (subgoal_tac "\<langle>f\<rangle>\<^sub>a(x := Some v) \<in> AssignF")
  apply (simp add:AssignF_upd_def)
  apply (auto simp add:typing AssignF_def unrest)
  apply (rule AssignF_dom_DASHED_var[of _ "f"])
  apply (simp add:dom_def)
done
 
*)