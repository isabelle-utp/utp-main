(*  Title:      JinjaDCI/J/Expr.thy
    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/Expr.thy by Tobias Nipkow
*)

section \<open> Expressions \<close>

theory Expr
imports "../Common/Exceptions"
begin

datatype bop = Eq | Add     \<comment> \<open>names of binary operations\<close>

datatype 'a exp
  = new cname      \<comment> \<open>class instance creation\<close>
  | Cast cname "('a exp)"      \<comment> \<open>type cast\<close>
  | Val val      \<comment> \<open>value\<close>
  | BinOp "('a exp)" bop "('a exp)"     ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)      \<comment> \<open>binary operation\<close>
  | Var 'a                                               \<comment> \<open>local variable (incl. parameter)\<close>
  | LAss 'a "('a exp)"     ("_:=_" [90,90]90)                    \<comment> \<open>local assignment\<close>
  | FAcc "('a exp)" vname cname     ("_\<bullet>_{_}" [10,90,99]90)      \<comment> \<open>field access\<close>
  | SFAcc cname vname cname     ("_\<bullet>\<^sub>s_{_}" [10,90,99]90)      \<comment> \<open>static field access\<close>
  | FAss "('a exp)" vname cname "('a exp)"     ("_\<bullet>_{_} := _" [10,90,99,90]90)      \<comment> \<open>field assignment\<close>
  | SFAss cname vname cname "('a exp)"     ("_\<bullet>\<^sub>s_{_} := _" [10,90,99,90]90)      \<comment> \<open>static field assignment\<close>
  | Call "('a exp)" mname "('a exp list)"     ("_\<bullet>_'(_')" [90,99,0] 90)            \<comment> \<open>method call\<close>
  | SCall cname mname "('a exp list)"     ("_\<bullet>\<^sub>s_'(_')" [90,99,0] 90)            \<comment> \<open>static method call\<close>
  | Block 'a ty "('a exp)"     ("'{_:_; _}")
  | Seq "('a exp)" "('a exp)"     ("_;;/ _"             [61,60]60)
  | Cond "('a exp)" "('a exp)" "('a exp)"     ("if '(_') _/ else _" [80,79,79]70)
  | While "('a exp)" "('a exp)"     ("while '(_') _"     [80,79]70)
  | throw "('a exp)"
  | TryCatch "('a exp)" cname 'a "('a exp)"     ("try _/ catch'(_ _') _"  [0,99,80,79] 70)
  | INIT cname "cname list" bool "('a exp)" ("INIT _ '(_,_') \<leftarrow> _" [60,60,60,60] 60) \<comment> \<open>internal initialization command: class, list of superclasses to initialize, preparation flag; command on hold\<close>
  | RI cname "('a exp)" "cname list" "('a exp)" ("RI '(_,_') ; _ \<leftarrow> _" [60,60,60,60] 60) \<comment> \<open>running of the initialization procedure for class with expression, classes still to initialize command on hold\<close>

type_synonym
  expr = "vname exp"            \<comment> \<open>Jinja expression\<close>
type_synonym
  J_mb = "vname list \<times> expr"    \<comment> \<open>Jinja method body: parameter names and expression\<close>
type_synonym
  J_prog = "J_mb prog"          \<comment> \<open>Jinja program\<close>

type_synonym
  init_stack = "expr list \<times> bool"  \<comment> \<open>Stack of expressions waiting on initialization in small step; indicator boolean True if current expression has been init checked\<close>

text\<open>The semantics of binary operators: \<close>

fun binop :: "bop \<times> val \<times> val \<Rightarrow> val option" where
  "binop(Eq,v\<^sub>1,v\<^sub>2) = Some(Bool (v\<^sub>1 = v\<^sub>2))"
| "binop(Add,Intg i\<^sub>1,Intg i\<^sub>2) = Some(Intg(i\<^sub>1+i\<^sub>2))"
| "binop(bop,v\<^sub>1,v\<^sub>2) = None"

lemma [simp]:
  "(binop(Add,v\<^sub>1,v\<^sub>2) = Some v) = (\<exists>i\<^sub>1 i\<^sub>2. v\<^sub>1 = Intg i\<^sub>1 \<and> v\<^sub>2 = Intg i\<^sub>2 \<and> v = Intg(i\<^sub>1+i\<^sub>2))"
(*<*)
apply(cases v\<^sub>1)
apply auto
apply(cases v\<^sub>2)
apply auto
done
(*>*)


lemma map_Val_throw_eq:
 "map Val vs @ throw ex # es = map Val vs' @ throw ex' # es' \<Longrightarrow> ex = ex'"
apply(induct vs arbitrary: vs')
 apply(case_tac vs', auto)+
done

lemma map_Val_nthrow_neq:
 "map Val vs = map Val vs' @ throw ex' # es' \<Longrightarrow> False"
apply(induct vs arbitrary: vs')
 apply(case_tac vs', auto)+
done

lemma map_Val_eq:
 "map Val vs = map Val vs' \<Longrightarrow> vs = vs'"
apply(induct vs arbitrary: vs')
 apply(case_tac vs', auto)+
done


lemma init_rhs_neq [simp]: "e \<noteq> INIT C (Cs,b) \<leftarrow> e"
proof -
  have "size e \<noteq> size (INIT C (Cs,b) \<leftarrow> e)" by auto
  then show ?thesis by fastforce
qed

lemma init_rhs_neq' [simp]: "INIT C (Cs,b) \<leftarrow> e \<noteq> e"
proof -
  have "size e \<noteq> size (INIT C (Cs,b) \<leftarrow> e)" by auto
  then show ?thesis by fastforce
qed

lemma ri_rhs_neq [simp]: "e \<noteq> RI(C,e');Cs \<leftarrow> e"
proof -
  have "size e \<noteq> size (RI(C,e');Cs \<leftarrow> e)" by auto
  then show ?thesis by fastforce
qed

lemma ri_rhs_neq' [simp]: "RI(C,e');Cs \<leftarrow> e \<noteq> e"
proof -
  have "size e \<noteq> size (RI(C,e');Cs \<leftarrow> e)" by auto
  then show ?thesis by fastforce
qed

subsection "Syntactic sugar"

abbreviation (input)
  InitBlock:: "'a \<Rightarrow> ty \<Rightarrow> 'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a exp"   ("(1'{_:_ := _;/ _})") where
  "InitBlock V T e1 e2 == {V:T; V := e1;; e2}"

abbreviation unit where "unit == Val Unit"
abbreviation null where "null == Val Null"
abbreviation "addr a == Val(Addr a)"
abbreviation "true == Val(Bool True)"
abbreviation "false == Val(Bool False)"

abbreviation
  Throw :: "addr \<Rightarrow> 'a exp" where
  "Throw a == throw(Val(Addr a))"

abbreviation
  THROW :: "cname \<Rightarrow> 'a exp" where
  "THROW xc == Throw(addr_of_sys_xcpt xc)"


subsection\<open>Free Variables\<close>

primrec fv :: "expr \<Rightarrow> vname set" and fvs :: "expr list \<Rightarrow> vname set" where
  "fv(new C) = {}"
| "fv(Cast C e) = fv e"
| "fv(Val v) = {}"
| "fv(e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(Var V) = {V}"
| "fv(LAss V e) = {V} \<union> fv e"
| "fv(e\<bullet>F{D}) = fv e"
| "fv(C\<bullet>\<^sub>sF{D}) = {}"
| "fv(e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(C\<bullet>\<^sub>sF{D}:=e\<^sub>2) = fv e\<^sub>2"
| "fv(e\<bullet>M(es)) = fv e \<union> fvs es"
| "fv(C\<bullet>\<^sub>sM(es)) = fvs es"
| "fv({V:T; e}) = fv e - {V}"
| "fv(e\<^sub>1;;e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(if (b) e\<^sub>1 else e\<^sub>2) = fv b \<union> fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(while (b) e) = fv b \<union> fv e"
| "fv(throw e) = fv e"
| "fv(try e\<^sub>1 catch(C V) e\<^sub>2) = fv e\<^sub>1 \<union> (fv e\<^sub>2 - {V})"
| "fv(INIT C (Cs,b) \<leftarrow> e) = fv e"
| "fv(RI (C,e);Cs \<leftarrow> e') = fv e \<union> fv e'"
| "fvs([]) = {}"
| "fvs(e#es) = fv e \<union> fvs es"

lemma [simp]: "fvs(es\<^sub>1 @ es\<^sub>2) = fvs es\<^sub>1 \<union> fvs es\<^sub>2"
(*<*)by (induct es\<^sub>1 type:list) auto(*>*)

lemma [simp]: "fvs(map Val vs) = {}"
(*<*)by (induct vs) auto(*>*)


subsection\<open>Accessing expression constructor arguments\<close>

fun val_of :: "'a exp \<Rightarrow> val option" where
"val_of (Val v) = Some v" |
"val_of _ = None"

lemma val_of_spec: "val_of e = Some v \<Longrightarrow> e = Val v"
proof(cases e) qed(auto)

fun lass_val_of :: "'a exp \<Rightarrow> ('a \<times> val) option" where
"lass_val_of (V:=Val v) = Some (V, v)" |
"lass_val_of _ = None"

lemma lass_val_of_spec:
assumes "lass_val_of e = \<lfloor>a\<rfloor>"
shows "e = (fst a:=Val (snd a))"
using assms proof(cases e)
  case (LAss V e') then show ?thesis using assms proof(cases e')qed(auto)
qed(auto)

fun map_vals_of :: "'a exp list \<Rightarrow> val list option" where
"map_vals_of (e#es) = (case val_of e of Some v \<Rightarrow> (case map_vals_of es of Some vs \<Rightarrow> Some (v#vs) 
                                                                        | _ \<Rightarrow> None)
                                      | _ \<Rightarrow> None)" |
"map_vals_of [] = Some []"

lemma map_vals_of_spec: "map_vals_of es = Some vs \<Longrightarrow> es = map Val vs"
proof(induct es arbitrary: vs) qed(auto simp: val_of_spec)

lemma map_vals_of_Vals[simp]: "map_vals_of (map Val vs) = \<lfloor>vs\<rfloor>" by(induct vs, auto)

lemma map_vals_of_throw[simp]:
 "map_vals_of (map Val vs @ throw e # es') = None"
 by(induct vs, auto)


fun bool_of :: "'a exp \<Rightarrow> bool option" where
"bool_of true = Some True" |
"bool_of false = Some False" |
"bool_of _ = None"

lemma bool_of_specT:
assumes "bool_of e = Some True" shows "e = true"
proof -
  have "bool_of e = Some True" by fact
  then show ?thesis
  proof(cases e)
    case (Val x3) with assms show ?thesis
    proof(cases x3)
      case (Bool x) with assms Val show ?thesis
      proof(cases x)qed(auto)
    qed(simp_all)
  qed(auto)
qed

lemma bool_of_specF:
assumes "bool_of e = Some False" shows "e = false"
proof -
  have "bool_of e = Some False" by fact
  then show ?thesis
  proof(cases e)
    case (Val x3) with assms show ?thesis
    proof(cases x3)
      case (Bool x) with assms Val show ?thesis
      proof(cases x)qed(auto)
    qed(simp_all)
  qed(auto)
qed


fun throw_of :: "'a exp \<Rightarrow> 'a exp option" where
"throw_of (throw e') = Some e'" |
"throw_of _ = None"

lemma throw_of_spec: "throw_of e = Some e' \<Longrightarrow> e = throw e'"
proof(cases e) qed(auto)

fun init_exp_of :: "'a exp \<Rightarrow> 'a exp option" where
"init_exp_of (INIT C (Cs,b) \<leftarrow> e) = Some e" |
"init_exp_of (RI(C,e');Cs \<leftarrow> e) = Some e" |
"init_exp_of _ = None"

lemma init_exp_of_neq [simp]: "init_exp_of e = \<lfloor>e'\<rfloor> \<Longrightarrow> e' \<noteq> e" by(cases e, auto)
lemma init_exp_of_neq'[simp]: "init_exp_of e = \<lfloor>e'\<rfloor> \<Longrightarrow> e \<noteq> e'" by(cases e, auto)


subsection\<open>Class initialization\<close>

text \<open> This section defines a few functions that return information
 about an expression's current initialization status. \<close>

 \<comment> \<open> True if expression contains @{text INIT}, @{text RI}, or a call to a static method @{term clinit} \<close>
primrec sub_RI :: "'a exp \<Rightarrow> bool" and sub_RIs :: "'a exp list \<Rightarrow> bool" where
  "sub_RI(new C) = False"
| "sub_RI(Cast C e) = sub_RI e"
| "sub_RI(Val v) = False"
| "sub_RI(e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = (sub_RI e\<^sub>1 \<or> sub_RI e\<^sub>2)"
| "sub_RI(Var V) = False"
| "sub_RI(LAss V e) = sub_RI e"
| "sub_RI(e\<bullet>F{D}) = sub_RI e"
| "sub_RI(C\<bullet>\<^sub>sF{D}) = False"
| "sub_RI(e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = (sub_RI e\<^sub>1 \<or> sub_RI e\<^sub>2)"
| "sub_RI(C\<bullet>\<^sub>sF{D}:=e\<^sub>2) = sub_RI e\<^sub>2"
| "sub_RI(e\<bullet>M(es)) = (sub_RI e \<or> sub_RIs es)"
| "sub_RI(C\<bullet>\<^sub>sM(es)) = (M = clinit \<or> sub_RIs es)"
| "sub_RI({V:T; e}) = sub_RI e"
| "sub_RI(e\<^sub>1;;e\<^sub>2) = (sub_RI e\<^sub>1 \<or> sub_RI e\<^sub>2)"
| "sub_RI(if (b) e\<^sub>1 else e\<^sub>2) = (sub_RI b \<or> sub_RI e\<^sub>1 \<or> sub_RI e\<^sub>2)"
| "sub_RI(while (b) e) = (sub_RI b \<or> sub_RI e)"
| "sub_RI(throw e) = sub_RI e"
| "sub_RI(try e\<^sub>1 catch(C V) e\<^sub>2) = (sub_RI e\<^sub>1 \<or> sub_RI e\<^sub>2)"
| "sub_RI(INIT C (Cs,b) \<leftarrow> e) = True"
| "sub_RI(RI (C,e);Cs \<leftarrow> e') = True"
| "sub_RIs([]) = False"
| "sub_RIs(e#es) = (sub_RI e \<or> sub_RIs es)"


lemmas sub_RI_sub_RIs_induct = sub_RI.induct sub_RIs.induct

lemma nsub_RIs_def[simp]:
 "\<not>sub_RIs es \<Longrightarrow> \<forall>e \<in> set es. \<not>sub_RI e"
 by(induct es, auto)

lemma sub_RI_base:
 "e = INIT C (Cs, b) \<leftarrow> e' \<or> e = RI(C,e\<^sub>0);Cs \<leftarrow> e' \<Longrightarrow> sub_RI e"
 by(cases e, auto)

lemma nsub_RI_Vals[simp]: "\<not>sub_RIs (map Val vs)"
 by(induct vs, auto)

lemma lass_val_of_nsub_RI: "lass_val_of e = \<lfloor>a\<rfloor> \<Longrightarrow> \<not>sub_RI e"
 by(drule lass_val_of_spec, simp)


 \<comment> \<open> is not currently initializing class @{text C'} (point past checking flag) \<close>
primrec not_init :: "cname \<Rightarrow> 'a exp \<Rightarrow> bool" and not_inits :: "cname \<Rightarrow> 'a exp list \<Rightarrow> bool" where
  "not_init C' (new C) = True"
| "not_init C' (Cast C e) = not_init C' e"
| "not_init C' (Val v) = True"
| "not_init C' (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = (not_init C' e\<^sub>1 \<and> not_init C' e\<^sub>2)"
| "not_init C' (Var V) = True"
| "not_init C' (LAss V e) = not_init C' e"
| "not_init C' (e\<bullet>F{D}) = not_init C' e"
| "not_init C' (C\<bullet>\<^sub>sF{D}) = True"
| "not_init C' (e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = (not_init C' e\<^sub>1 \<and> not_init C' e\<^sub>2)"
| "not_init C' (C\<bullet>\<^sub>sF{D}:=e\<^sub>2) = not_init C' e\<^sub>2"
| "not_init C' (e\<bullet>M(es)) = (not_init C' e \<and> not_inits C' es)"
| "not_init C' (C\<bullet>\<^sub>sM(es)) = not_inits C' es"
| "not_init C' ({V:T; e}) = not_init C' e"
| "not_init C' (e\<^sub>1;;e\<^sub>2) = (not_init C' e\<^sub>1 \<and> not_init C' e\<^sub>2)"
| "not_init C' (if (b) e\<^sub>1 else e\<^sub>2) = (not_init C' b \<and> not_init C' e\<^sub>1 \<and> not_init C' e\<^sub>2)"
| "not_init C' (while (b) e) = (not_init C' b \<and> not_init C' e)"
| "not_init C' (throw e) = not_init C' e"
| "not_init C' (try e\<^sub>1 catch(C V) e\<^sub>2) = (not_init C' e\<^sub>1 \<and> not_init C' e\<^sub>2)"
| "not_init C' (INIT C (Cs,b) \<leftarrow> e) = ((b \<longrightarrow> Cs = Nil \<or> C' \<noteq> hd Cs) \<and> C' \<notin> set(tl Cs) \<and> not_init C' e)"
| "not_init C' (RI (C,e);Cs \<leftarrow> e') = (C' \<notin> set (C#Cs) \<and> not_init C' e \<and> not_init C' e')"
| "not_inits C' ([]) = True"
| "not_inits C' (e#es) = (not_init C' e \<and> not_inits C' es)"

lemma not_inits_def'[simp]:
 "not_inits C es \<Longrightarrow> \<forall>e \<in> set es. not_init C e"
 by(induct es, auto)

lemma nsub_RIs_not_inits_aux: "\<forall>e \<in> set es. \<not>sub_RI e \<longrightarrow> not_init C e
  \<Longrightarrow> \<not>sub_RIs es \<Longrightarrow> not_inits C es"
 by(induct es, auto)

lemma nsub_RI_not_init: "\<not>sub_RI e \<Longrightarrow> not_init C e"
proof(induct e) qed(auto intro: nsub_RIs_not_inits_aux)

lemma nsub_RIs_not_inits: "\<not>sub_RIs es \<Longrightarrow> not_inits C es"
apply(rule nsub_RIs_not_inits_aux)
 apply(simp_all add: nsub_RI_not_init)
done

subsection\<open>Subexpressions\<close>

 \<comment> \<open> all strictly smaller subexpressions; does not include self \<close>
 primrec subexp :: "'a exp \<Rightarrow> 'a exp set" and subexps :: "'a exp list \<Rightarrow> 'a exp set" where
  "subexp(new C) = {}"
| "subexp(Cast C e) = {e} \<union> subexp e"
| "subexp(Val v) = {}"
| "subexp(e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = {e\<^sub>1, e\<^sub>2} \<union> subexp e\<^sub>1 \<union> subexp e\<^sub>2"
| "subexp(Var V) = {}"
| "subexp(LAss V e) = {e} \<union> subexp e"
| "subexp(e\<bullet>F{D}) = {e} \<union> subexp e"
| "subexp(C\<bullet>\<^sub>sF{D}) = {}"
| "subexp(e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = {e\<^sub>1, e\<^sub>2} \<union> subexp e\<^sub>1 \<union> subexp e\<^sub>2"
| "subexp(C\<bullet>\<^sub>sF{D}:=e\<^sub>2) = {e\<^sub>2} \<union>subexp e\<^sub>2"
| "subexp(e\<bullet>M(es)) = {e} \<union> set es \<union> subexp e \<union> subexps es"
| "subexp(C\<bullet>\<^sub>sM(es)) = set es \<union> subexps es"
| "subexp({V:T; e}) = {e} \<union> subexp e"
| "subexp(e\<^sub>1;;e\<^sub>2) = {e\<^sub>1, e\<^sub>2} \<union> subexp e\<^sub>1 \<union> subexp e\<^sub>2"
| "subexp(if (b) e\<^sub>1 else e\<^sub>2) = {b, e\<^sub>1, e\<^sub>2} \<union> subexp b \<union> subexp e\<^sub>1 \<union> subexp e\<^sub>2"
| "subexp(while (b) e) = {b, e} \<union> subexp b \<union> subexp e"
| "subexp(throw e) = {e} \<union> subexp e"
| "subexp(try e\<^sub>1 catch(C V) e\<^sub>2) = {e\<^sub>1, e\<^sub>2} \<union> subexp e\<^sub>1 \<union> subexp e\<^sub>2"
| "subexp(INIT C (Cs,b) \<leftarrow> e) = {e} \<union> subexp e"
| "subexp(RI (C,e);Cs \<leftarrow> e') = {e, e'} \<union> subexp e \<union> subexp e'"
| "subexps([]) = {}"
| "subexps(e#es) = {e} \<union> subexp e \<union> subexps es"


lemmas subexp_subexps_induct = subexp.induct subexps.induct

abbreviation subexp_of :: "'a exp \<Rightarrow> 'a exp \<Rightarrow> bool" where
 "subexp_of e e' \<equiv> e \<in> subexp e'"

lemma subexp_size_le:
 "(e' \<in> subexp e \<longrightarrow> size e' < size e) \<and> (e' \<in> subexps es \<longrightarrow> size e' < size_list size es)"
proof(induct rule: subexp_subexps.induct)
  case Call:11 then show ?case using not_less_eq size_list_estimation by fastforce
next
  case SCall:12 then show ?case using not_less_eq size_list_estimation by fastforce
qed(auto)

lemma subexps_def2: "subexps es = set es \<union> (\<Union>e \<in> set es. subexp e)" by(induct es, auto)

 \<comment> \<open> strong induction \<close>
lemma shows subexp_induct[consumes 1]: 
"(\<And>e. subexp e = {} \<Longrightarrow> R e) \<Longrightarrow> (\<And>e. (\<And>e'. e' \<in> subexp e \<Longrightarrow> R e') \<Longrightarrow> R e)
   \<Longrightarrow> (\<And>es. (\<And>e'. e' \<in> subexps es \<Longrightarrow> R e') \<Longrightarrow> Rs es) \<Longrightarrow> (\<forall>e'. e' \<in> subexp e \<longrightarrow> R e') \<and> R e"
and subexps_induct[consumes 1]:
 "(\<And>es. subexps es = {} \<Longrightarrow> Rs es) \<Longrightarrow> (\<And>e. (\<And>e'. e' \<in> subexp e \<Longrightarrow> R e') \<Longrightarrow> R e)
   \<Longrightarrow> (\<And>es. (\<And>e'. e' \<in> subexps es \<Longrightarrow> R e') \<Longrightarrow> Rs es) \<Longrightarrow> (\<forall>e'. e' \<in> subexps es \<longrightarrow> R e') \<and> Rs es"
proof(induct rule: subexp_subexps_induct)
  case (Cast x1 x2)
  then have "(\<forall>e'. subexp_of e' x2 \<longrightarrow> R e') \<and> R x2" by fast
  then have "(\<forall>e'. subexp_of e' (Cast x1 x2) \<longrightarrow> R e')" by auto
  then show ?case using Cast.prems(2) by fast
next
  case (BinOp x1 x2 x3)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" and "(\<forall>e'. subexp_of e' x3 \<longrightarrow> R e') \<and> R x3"
   by fast+
  then have "(\<forall>e'. subexp_of e' (x1 \<guillemotleft>x2\<guillemotright> x3) \<longrightarrow> R e')" by auto
  then show ?case using BinOp.prems(2) by fast
next
  case (LAss x1 x2)
  then have "(\<forall>e'. subexp_of e' x2 \<longrightarrow> R e') \<and> R x2" by fast
  then have "(\<forall>e'. subexp_of e' (LAss x1 x2) \<longrightarrow> R e')" by auto
  then show ?case using LAss.prems(2) by fast
next
  case (FAcc x1 x2 x3)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" by fast
  then have "(\<forall>e'. subexp_of e' (x1\<bullet>x2{x3}) \<longrightarrow> R e')" by auto
  then show ?case using FAcc.prems(2) by fast
next
  case (FAss x1 x2 x3 x4)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" and "(\<forall>e'. subexp_of e' x4 \<longrightarrow> R e') \<and> R x4"
   by fast+
  then have "(\<forall>e'. subexp_of e' (x1\<bullet>x2{x3} := x4) \<longrightarrow> R e')" by auto
  then show ?case using FAss.prems(2) by fast
next
  case (SFAss x1 x2 x3 x4)
  then have "(\<forall>e'. subexp_of e' x4 \<longrightarrow> R e') \<and> R x4" by fast
  then have "(\<forall>e'. subexp_of e' (x1\<bullet>\<^sub>sx2{x3} := x4) \<longrightarrow> R e')" by auto
  then show ?case using SFAss.prems(2) by fast
next
  case (Call x1 x2 x3)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" and "(\<forall>e'. e' \<in> subexps x3 \<longrightarrow> R e') \<and> Rs x3"
   by fast+
  then have "(\<forall>e'. subexp_of e' (x1\<bullet>x2(x3)) \<longrightarrow> R e')" using subexps_def2 by auto
  then show ?case using Call.prems(2) by fast
next
  case (SCall x1 x2 x3)
  then have "(\<forall>e'. e' \<in> subexps x3 \<longrightarrow> R e') \<and> Rs x3" by fast
  then have "(\<forall>e'. subexp_of e' (x1\<bullet>\<^sub>sx2(x3)) \<longrightarrow> R e')" using subexps_def2 by auto
  then show ?case using SCall.prems(2) by fast
next
  case (Block x1 x2 x3)
  then have "(\<forall>e'. subexp_of e' x3 \<longrightarrow> R e') \<and> R x3" by fast
  then have "(\<forall>e'. subexp_of e' {x1:x2; x3} \<longrightarrow> R e')" by auto
  then show ?case using Block.prems(2) by fast
next
  case (Seq x1 x2)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" and "(\<forall>e'. subexp_of e' x2 \<longrightarrow> R e') \<and> R x2"
   by fast+
  then have "(\<forall>e'. subexp_of e' (x1;; x2) \<longrightarrow> R e')" by auto
  then show ?case using Seq.prems(2) by fast
next
  case (Cond x1 x2 x3)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" and "(\<forall>e'. subexp_of e' x2 \<longrightarrow> R e') \<and> R x2"
    and "(\<forall>e'. subexp_of e' x3 \<longrightarrow> R e') \<and> R x3" by fast+
  then have "(\<forall>e'. subexp_of e' (if (x1) x2 else x3) \<longrightarrow> R e')" by auto
  then show ?case using Cond.prems(2) by fast
next
  case (While x1 x2)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" and "(\<forall>e'. subexp_of e' x2 \<longrightarrow> R e') \<and> R x2"
   by fast+
  then have "(\<forall>e'. subexp_of e' (while (x1) x2) \<longrightarrow> R e')" by auto
  then show ?case using While.prems(2) by fast
next
  case (throw x)
  then have "(\<forall>e'. subexp_of e' x \<longrightarrow> R e') \<and> R x" by fast
  then have "(\<forall>e'. subexp_of e' (throw x) \<longrightarrow> R e')" by auto
  then show ?case using throw.prems(2) by fast
next
  case (TryCatch x1 x2 x3 x4)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" and "(\<forall>e'. subexp_of e' x4 \<longrightarrow> R e') \<and> R x4"
   by fast+
  then have "(\<forall>e'. subexp_of e' (try x1 catch(x2 x3) x4) \<longrightarrow> R e')" by auto
  then show ?case using TryCatch.prems(2) by fast
next
  case (INIT x1 x2 x3 x4)
  then have "(\<forall>e'. subexp_of e' x4 \<longrightarrow> R e') \<and> R x4" by fast
  then have "(\<forall>e'. subexp_of e' (INIT x1 (x2,x3) \<leftarrow> x4) \<longrightarrow> R e')" by auto
  then show ?case using INIT.prems(2) by fast
next
  case (RI x1 x2 x3 x4)
  then have "(\<forall>e'. subexp_of e' x2 \<longrightarrow> R e') \<and> R x2" and "(\<forall>e'. subexp_of e' x4 \<longrightarrow> R e') \<and> R x4"
   by fast+
  then have "(\<forall>e'. subexp_of e' (RI (x1,x2) ; x3 \<leftarrow> x4) \<longrightarrow> R e')" by auto
  then show ?case using RI.prems(2) by fast
next
  case (Cons_exp x1 x2)
  then have "(\<forall>e'. subexp_of e' x1 \<longrightarrow> R e') \<and> R x1" and "(\<forall>e'. e' \<in> subexps x2 \<longrightarrow> R e') \<and> Rs x2"
   by fast+
  then have "(\<forall>e'. e' \<in> subexps (x1 # x2) \<longrightarrow> R e')" using subexps_def2 by auto
  then show ?case using Cons_exp.prems(3) by fast
qed(auto)


subsection"Final expressions"
(* these definitions and most of the lemmas were in BigStep.thy in the original Jinja *)

definition final :: "'a exp \<Rightarrow> bool"
where
  "final e  \<equiv>  (\<exists>v. e = Val v) \<or> (\<exists>a. e = Throw a)"

definition finals:: "'a exp list \<Rightarrow> bool"
where
  "finals es  \<equiv>  (\<exists>vs. es = map Val vs) \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')"

lemma [simp]: "final(Val v)"
(*<*)by(simp add:final_def)(*>*)

lemma [simp]: "final(throw e) = (\<exists>a. e = addr a)"
(*<*)by(simp add:final_def)(*>*)

lemma finalE: "\<lbrakk> final e;  \<And>v. e = Val v \<Longrightarrow> R;  \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
(*<*)by(auto simp:final_def)(*>*)

lemma final_fv[iff]: "final e \<Longrightarrow> fv e = {}"
 by (auto simp: final_def)

lemma finalsE:
 "\<lbrakk> finals es;  \<And>vs. es = map Val vs \<Longrightarrow> R;  \<And>vs a es'. es = map Val vs @ Throw a # es' \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
(*<*)by(auto simp:finals_def)(*>*)

lemma [iff]: "finals []"
(*<*)by(simp add:finals_def)(*>*)

lemma [iff]: "finals (Val v # es) = finals es"
(*<*)
apply(clarsimp simp add: finals_def)
apply(rule iffI)
 apply(erule disjE)
  apply simp
 apply(rule disjI2)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastforce
apply(erule disjE)
 apply clarsimp
apply(rule disjI2)
apply clarsimp
apply(rule_tac x = "v#vs" in exI)
apply simp
done
(*>*)

lemma finals_app_map[iff]: "finals (map Val vs @ es) = finals es"
(*<*)by(induct_tac vs, auto)(*>*)

lemma [iff]: "finals (map Val vs)"
(*<*)using finals_app_map[of vs "[]"]by(simp)(*>*)

lemma [iff]: "finals (throw e # es) = (\<exists>a. e = addr a)"
(*<*)
apply(simp add:finals_def)
apply(rule iffI)
 apply clarsimp
 apply(case_tac vs)
  apply simp
 apply fastforce
apply clarsimp
apply(rule_tac x = "[]" in exI)
apply simp
done
(*>*)

lemma not_finals_ConsI: "\<not> final e \<Longrightarrow> \<not> finals(e#es)"
 (*<*)
apply(clarsimp simp add:finals_def final_def)
apply(case_tac vs)
apply auto
done
(*>*)

lemma not_finals_ConsI2: "e = Val v \<Longrightarrow> \<not> finals es \<Longrightarrow> \<not> finals(e#es)"
 (*<*)
apply(clarsimp simp add:finals_def final_def)
apply(case_tac vs)
apply auto
done
(*>*)


end
