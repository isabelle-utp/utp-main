(*  Title:      JinjaDCI/Common/Objects.thy

    Author:     David von Oheimb, Susannah Mansky
    Copyright   1999 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory Common/Objects.thy by David von Oheimb
*)

section \<open> Objects and the Heap \<close>

theory Objects imports TypeRel Value begin

subsection\<open> Objects \<close>

type_synonym
  fields = "vname \<times> cname \<rightharpoonup> val"  \<comment> \<open>field name, defining class, value\<close>
type_synonym
  obj = "cname \<times> fields"    \<comment> \<open>class instance with class name and fields\<close>
type_synonym
  sfields = "vname \<rightharpoonup> val"  \<comment> \<open>field name to value\<close>

definition obj_ty  :: "obj \<Rightarrow> ty"
where
  "obj_ty obj  \<equiv>  Class (fst obj)"

 \<comment> \<open> initializes a given list of fields \<close>
definition init_fields :: "((vname \<times> cname) \<times> staticb \<times> ty) list \<Rightarrow> fields"
where
  "init_fields FDTs  \<equiv>  (map_of \<circ> map (\<lambda>((F,D),b,T). ((F,D),default_val T))) FDTs"

definition init_sfields :: "((vname \<times> cname) \<times> staticb \<times> ty) list \<Rightarrow> sfields"
where
  "init_sfields FDTs  \<equiv>  (map_of \<circ> map (\<lambda>((F,D),b,T). (F,default_val T))) FDTs"
  
  \<comment> \<open>a new, blank object with default values for instance fields:\<close>
definition blank :: "'m prog \<Rightarrow> cname \<Rightarrow> obj"
where
  "blank P C \<equiv>  (C,init_fields (ifields P C))"

  \<comment> \<open>a new, blank object with default values for static fields:\<close>
definition sblank :: "'m prog \<Rightarrow> cname \<Rightarrow> sfields"
where
  "sblank P C \<equiv> init_sfields (isfields P C)"

lemma [simp]: "obj_ty (C,fs) = Class C"
(*<*)by (simp add: obj_ty_def)(*>*)

(* replaced all vname, cname in below with `char list' and \<rightharpoonup> with returned option
  so that pretty printing works  -SM *)
translations
  (type) "fields" <= (type) "char list \<times> char list \<Rightarrow> val option"
  (type) "obj" <= (type) "char list \<times> fields"
  (type) "sfields" <= (type) "char list \<Rightarrow> val option"

subsection\<open> Heap \<close>

type_synonym heap  = "addr \<rightharpoonup> obj"

(* replaced addr with nat and \<rightharpoonup> with returned option so that pretty printing works  -SM *)
translations
 (type) "heap" <= (type) "nat \<Rightarrow> obj option"

abbreviation
  cname_of :: "heap \<Rightarrow> addr \<Rightarrow> cname" where
  "cname_of hp a == fst (the (hp a))"

definition new_Addr  :: "heap \<Rightarrow> addr option"
where
  "new_Addr h  \<equiv>  if \<exists>a. h a = None then Some(LEAST a. h a = None) else None"

definition cast_ok :: "'m prog \<Rightarrow> cname \<Rightarrow> heap \<Rightarrow> val \<Rightarrow> bool"
where
  "cast_ok P C h v  \<equiv>  v = Null \<or> P \<turnstile> cname_of h (the_Addr v) \<preceq>\<^sup>* C"

definition hext :: "heap \<Rightarrow> heap \<Rightarrow> bool" ("_ \<unlhd> _" [51,51] 50)
where
  "h \<unlhd> h'  \<equiv>  \<forall>a C fs. h a = Some(C,fs) \<longrightarrow> (\<exists>fs'. h' a = Some(C,fs'))"

primrec typeof_h :: "heap \<Rightarrow> val \<Rightarrow> ty option"  ("typeof\<^bsub>_\<^esub>")
where
  "typeof\<^bsub>h\<^esub>  Unit    = Some Void"
| "typeof\<^bsub>h\<^esub>  Null    = Some NT"
| "typeof\<^bsub>h\<^esub> (Bool b) = Some Boolean"
| "typeof\<^bsub>h\<^esub> (Intg i) = Some Integer"
| "typeof\<^bsub>h\<^esub> (Addr a) = (case h a of None \<Rightarrow> None | Some(C,fs) \<Rightarrow> Some(Class C))"

lemma new_Addr_SomeD:
  "new_Addr h = Some a \<Longrightarrow> h a = None"
 (*<*)by(fastforce simp: new_Addr_def split:if_splits intro:LeastI)(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Boolean) = (\<exists>b. v = Bool b)"
 (*<*)by(induct v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some Integer) = (\<exists>i. v = Intg i)"
(*<*)by(cases v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some NT) = (v = Null)"
 (*<*)by(cases v) auto(*>*)

lemma [simp]: "(typeof\<^bsub>h\<^esub> v = Some(Class C)) = (\<exists>a fs. v = Addr a \<and> h a = Some(C,fs))"
 (*<*)by(cases v) auto(*>*)

lemma [simp]: "h a = Some(C,fs) \<Longrightarrow> typeof\<^bsub>(h(a\<mapsto>(C,fs')))\<^esub> v = typeof\<^bsub>h\<^esub> v"
 (*<*)by(induct v) (auto simp:fun_upd_apply)(*>*)

text\<open> For literal values the first parameter of @{term typeof} can be
set to @{term empty} because they do not contain addresses: \<close>

abbreviation
  typeof :: "val \<Rightarrow> ty option" where
  "typeof v == typeof_h Map.empty v"

lemma typeof_lit_typeof:
  "typeof v = Some T \<Longrightarrow> typeof\<^bsub>h\<^esub> v = Some T"
 (*<*)by(cases v) auto(*>*)

lemma typeof_lit_is_type: 
  "typeof v = Some T \<Longrightarrow> is_type P T"
 (*<*)by (induct v) (auto simp:is_type_def)(*>*)


subsection \<open> Heap extension @{text"\<unlhd>"} \<close>

lemma hextI: "\<forall>a C fs. h a = Some(C,fs) \<longrightarrow> (\<exists>fs'. h' a = Some(C,fs')) \<Longrightarrow> h \<unlhd> h'"
(*<*)by(auto simp: hext_def)(*>*)

lemma hext_objD: "\<lbrakk> h \<unlhd> h'; h a = Some(C,fs) \<rbrakk> \<Longrightarrow> \<exists>fs'. h' a = Some(C,fs')"
(*<*)by(auto simp: hext_def)(*>*)

lemma hext_refl [iff]: "h \<unlhd> h"
(*<*)by (rule hextI) fast(*>*)

lemma hext_new [simp]: "h a = None \<Longrightarrow> h \<unlhd> h(a\<mapsto>x)"
(*<*)by (rule hextI) (auto simp:fun_upd_apply)(*>*)

lemma hext_trans: "\<lbrakk> h \<unlhd> h'; h' \<unlhd> h'' \<rbrakk> \<Longrightarrow> h \<unlhd> h''"
(*<*)by (rule hextI) (fast dest: hext_objD)(*>*)

lemma hext_upd_obj: "h a = Some (C,fs) \<Longrightarrow> h \<unlhd> h(a\<mapsto>(C,fs'))"
(*<*)by (rule hextI) (auto simp:fun_upd_apply)(*>*)

lemma hext_typeof_mono: "\<lbrakk> h \<unlhd> h'; typeof\<^bsub>h\<^esub> v = Some T \<rbrakk> \<Longrightarrow> typeof\<^bsub>h'\<^esub> v = Some T"
(*<*)
proof(cases v)
  case Addr assume "h \<unlhd> h'" and "typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>"
  then show ?thesis using Addr by(fastforce simp:hext_def)
qed simp_all
(*>*)

subsection\<open> Static field information function \<close>

datatype init_state = Done | Processing | Prepared | Error
	\<comment> \<open>@{term Done} = initialized\<close>
	\<comment> \<open>@{term Processing} = currently being initialized\<close>
	\<comment> \<open>@{term Prepared} = uninitialized and not currently being initialized\<close>
	\<comment> \<open>@{term Error} = previous initialization attempt resulted in erroneous state\<close>

inductive iprog :: "init_state \<Rightarrow> init_state \<Rightarrow> bool" ("_ \<le>\<^sub>i _" [51,51] 50)
where
  [simp]: "Prepared \<le>\<^sub>i i"
| [simp]: "Processing \<le>\<^sub>i Done"
| [simp]: "Processing \<le>\<^sub>i Error"
| [simp]: "i \<le>\<^sub>i i"

lemma iprog_Done[simp]: "(Done \<le>\<^sub>i i) = (i = Done)"
 by(simp only: iprog.simps, simp)

lemma iprog_Error[simp]: "(Error \<le>\<^sub>i i) = (i = Error)"
 by(simp only: iprog.simps, simp)

lemma iprog_Processing[simp]: "(Processing \<le>\<^sub>i i) = (i = Done \<or> i = Error \<or> i = Processing)"
 by(simp only: iprog.simps, simp)

lemma iprog_trans: "\<lbrakk> i \<le>\<^sub>i i'; i' \<le>\<^sub>i i'' \<rbrakk> \<Longrightarrow> i \<le>\<^sub>i i''"
(*<*)by(case_tac i; case_tac i') simp_all(*>*)

subsection\<open> Static Heap \<close>

text \<open>The static heap (sheap) is used for storing information about static
 field values and initialization status for classes.\<close>

type_synonym
  sheap = "cname \<rightharpoonup> sfields \<times> init_state"

translations
 (type) "sheap" <= (type) "char list \<Rightarrow> (sfields \<times> init_state) option"

definition shext :: "sheap \<Rightarrow> sheap \<Rightarrow> bool" ("_ \<unlhd>\<^sub>s _" [51,51] 50)
where
  "sh \<unlhd>\<^sub>s sh'  \<equiv>  \<forall>C sfs i. sh C = Some(sfs,i) \<longrightarrow> (\<exists>sfs' i'. sh' C = Some(sfs',i') \<and> i \<le>\<^sub>i i')"


lemma shextI: "\<forall>C sfs i. sh C = Some(sfs,i) \<longrightarrow> (\<exists>sfs' i'. sh' C = Some(sfs',i') \<and> i \<le>\<^sub>i i') \<Longrightarrow> sh \<unlhd>\<^sub>s sh'"
(*<*)by(auto simp: shext_def)(*>*)

lemma shext_objD: "\<lbrakk> sh \<unlhd>\<^sub>s sh'; sh C = Some(sfs,i) \<rbrakk> \<Longrightarrow> \<exists>sfs' i'. sh' C = Some(sfs', i') \<and> i \<le>\<^sub>i i'"
(*<*)by(auto simp: shext_def)(*>*)

lemma shext_refl [iff]: "sh \<unlhd>\<^sub>s sh"
(*<*)by (rule shextI) auto(*>*)

lemma shext_new [simp]: "sh C = None \<Longrightarrow> sh \<unlhd>\<^sub>s sh(C\<mapsto>x)"
(*<*)by (rule shextI) (auto simp:fun_upd_apply)(*>*)

lemma shext_trans: "\<lbrakk> sh \<unlhd>\<^sub>s sh'; sh' \<unlhd>\<^sub>s sh'' \<rbrakk> \<Longrightarrow> sh \<unlhd>\<^sub>s sh''"
(*<*)by (rule shextI) (fast dest: iprog_trans shext_objD)(*>*)

lemma shext_upd_obj: "\<lbrakk> sh C = Some (sfs,i); i \<le>\<^sub>i i' \<rbrakk> \<Longrightarrow> sh \<unlhd>\<^sub>s sh(C\<mapsto>(sfs',i'))"
(*<*)by (rule shextI) (auto simp:fun_upd_apply)(*>*)

end
