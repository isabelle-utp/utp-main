(*  Title:      JinjaDCI/Common/Exceptions.thy

    Author:     Gerwin Klein, Martin Strecker, Susannah Mansky
    Copyright   2002 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory Common/Exceptions.thy by Gerwin Klein and Martin Strecker
*)

section \<open> Exceptions \<close>

theory Exceptions imports Objects begin

definition ErrorCl :: "string" where "ErrorCl = ''Error''"
definition ThrowCl :: "string" where "ThrowCl = ''Throwable''"

definition NullPointer :: cname
where
  "NullPointer \<equiv> ''NullPointer''"

definition ClassCast :: cname
where
  "ClassCast \<equiv> ''ClassCast''"

definition OutOfMemory :: cname
where
  "OutOfMemory \<equiv> ''OutOfMemory''"

definition NoClassDefFoundError :: cname
where
  "NoClassDefFoundError \<equiv> ''NoClassDefFoundError''"

definition IncompatibleClassChangeError :: cname
where
  "IncompatibleClassChangeError \<equiv> ''IncompatibleClassChangeError''"

definition NoSuchFieldError :: cname
where
  "NoSuchFieldError \<equiv> ''NoSuchFieldError''"

definition NoSuchMethodError :: cname
where
  "NoSuchMethodError \<equiv> ''NoSuchMethodError''"

definition sys_xcpts :: "cname set"
where
  "sys_xcpts  \<equiv>  {NullPointer, ClassCast, OutOfMemory, NoClassDefFoundError,
                    IncompatibleClassChangeError, 
                    NoSuchFieldError, NoSuchMethodError}"

definition addr_of_sys_xcpt :: "cname \<Rightarrow> addr"
where
  "addr_of_sys_xcpt s \<equiv> if s = NullPointer then 0 else
                        if s = ClassCast then 1 else
                        if s = OutOfMemory then 2 else
                        if s = NoClassDefFoundError then 3 else
                        if s = IncompatibleClassChangeError then 4 else
                        if s = NoSuchFieldError then 5 else
                        if s = NoSuchMethodError then 6 else undefined"


lemmas sys_xcpts_defs = NullPointer_def ClassCast_def OutOfMemory_def NoClassDefFoundError_def
                       IncompatibleClassChangeError_def NoSuchFieldError_def NoSuchMethodError_def

lemma Start_nsys_xcpts: "Start \<notin> sys_xcpts"
 by(simp add: Start_def sys_xcpts_def sys_xcpts_defs)

lemma Start_nsys_xcpts1 [simp]: "Start \<noteq> NullPointer" "Start \<noteq> ClassCast"
 "Start \<noteq> OutOfMemory" "Start \<noteq> NoClassDefFoundError"
 "Start \<noteq> IncompatibleClassChangeError" "Start \<noteq> NoSuchFieldError"
 "Start \<noteq> NoSuchMethodError"
using Start_nsys_xcpts by(auto simp: sys_xcpts_def)

lemma Start_nsys_xcpts2 [simp]: "NullPointer \<noteq> Start" "ClassCast \<noteq> Start"
 "OutOfMemory \<noteq> Start" "NoClassDefFoundError \<noteq> Start"
 "IncompatibleClassChangeError \<noteq> Start" "NoSuchFieldError \<noteq> Start"
 "NoSuchMethodError \<noteq> Start"
using Start_nsys_xcpts by(auto simp: sys_xcpts_def dest: sym)

definition start_heap :: "'c prog \<Rightarrow> heap"
where
  "start_heap G \<equiv> Map.empty (addr_of_sys_xcpt NullPointer \<mapsto> blank G NullPointer)
                        (addr_of_sys_xcpt ClassCast \<mapsto> blank G ClassCast)
                        (addr_of_sys_xcpt OutOfMemory \<mapsto> blank G OutOfMemory)
                        (addr_of_sys_xcpt NoClassDefFoundError \<mapsto> blank G NoClassDefFoundError)
                        (addr_of_sys_xcpt IncompatibleClassChangeError \<mapsto> blank G IncompatibleClassChangeError)
                        (addr_of_sys_xcpt NoSuchFieldError \<mapsto> blank G NoSuchFieldError)
                        (addr_of_sys_xcpt NoSuchMethodError \<mapsto> blank G NoSuchMethodError)"

definition preallocated :: "heap \<Rightarrow> bool"
where
  "preallocated h \<equiv> \<forall>C \<in> sys_xcpts. \<exists>fs. h(addr_of_sys_xcpt C) = Some (C,fs)"

subsection "System exceptions"

lemma sys_xcpts_incl [simp]: "NullPointer \<in> sys_xcpts \<and> OutOfMemory \<in> sys_xcpts
   \<and> ClassCast \<in> sys_xcpts \<and> NoClassDefFoundError \<in> sys_xcpts
   \<and> IncompatibleClassChangeError \<in> sys_xcpts \<and> NoSuchFieldError \<in> sys_xcpts
   \<and> NoSuchMethodError \<in> sys_xcpts"
(*<*)by(simp add: sys_xcpts_def)(*>*)

lemma sys_xcpts_cases [consumes 1, cases set]:
  "\<lbrakk> C \<in> sys_xcpts; P NullPointer; P OutOfMemory; P ClassCast; P NoClassDefFoundError;
  P IncompatibleClassChangeError; P NoSuchFieldError;
  P NoSuchMethodError \<rbrakk> \<Longrightarrow> P C"
(*<*)by (auto simp: sys_xcpts_def)(*>*)

subsection "Starting heap"

lemma start_heap_sys_xcpts:
assumes "C \<in> sys_xcpts"
shows "start_heap P (addr_of_sys_xcpt C) = Some(blank P C)"
by(rule sys_xcpts_cases[OF assms])
  (auto simp add: start_heap_def sys_xcpts_def addr_of_sys_xcpt_def sys_xcpts_defs)

lemma start_heap_classes:
 "start_heap P a = Some(C,fs) \<Longrightarrow> C \<in> sys_xcpts"
 by(simp add: start_heap_def blank_def split: if_split_asm)

lemma start_heap_nStart: "start_heap P a = Some obj \<Longrightarrow> fst(obj) \<noteq> Start"
 by(cases obj, auto dest!: start_heap_classes simp: Start_nsys_xcpts)

subsection "@{term preallocated}"

lemma preallocated_dom [simp]: 
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> addr_of_sys_xcpt C \<in> dom h"
(*<*)by (fastforce simp:preallocated_def dom_def)(*>*)


lemma preallocatedD:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> \<exists>fs. h(addr_of_sys_xcpt C) = Some (C, fs)"
(*<*)by(auto simp: preallocated_def sys_xcpts_def)(*>*)


lemma preallocatedE [elim?]:
  "\<lbrakk> preallocated h;  C \<in> sys_xcpts; \<And>fs. h(addr_of_sys_xcpt C) = Some(C,fs) \<Longrightarrow> P h C\<rbrakk>
  \<Longrightarrow> P h C"
(*<*)by (fast dest: preallocatedD)(*>*)


lemma cname_of_xcp [simp]:
  "\<lbrakk> preallocated h; C \<in> sys_xcpts \<rbrakk> \<Longrightarrow> cname_of h (addr_of_sys_xcpt C) = C"
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_ClassCast [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt ClassCast)) = Some(Class ClassCast)" 
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_OutOfMemory [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt OutOfMemory)) = Some(Class OutOfMemory)" 
(*<*)by (auto elim: preallocatedE)(*>*)


lemma typeof_NullPointer [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NullPointer)) = Some(Class NullPointer)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_NoClassDefFoundError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NoClassDefFoundError)) = Some(Class NoClassDefFoundError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_IncompatibleClassChangeError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt IncompatibleClassChangeError)) = Some(Class IncompatibleClassChangeError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_NoSuchFieldError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NoSuchFieldError)) = Some(Class NoSuchFieldError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma typeof_NoSuchMethodError [simp]:
  "preallocated h \<Longrightarrow> typeof\<^bsub>h\<^esub> (Addr(addr_of_sys_xcpt NoSuchMethodError)) = Some(Class NoSuchMethodError)" 
(*<*)by (auto elim: preallocatedE)(*>*)

lemma preallocated_hext:
  "\<lbrakk> preallocated h; h \<unlhd> h' \<rbrakk> \<Longrightarrow> preallocated h'"
(*<*)by (simp add: preallocated_def hext_def)(*>*)

(*<*)
lemmas preallocated_upd_obj = preallocated_hext [OF _ hext_upd_obj]
lemmas preallocated_new  = preallocated_hext [OF _ hext_new]
(*>*)

lemma preallocated_start:
  "preallocated (start_heap P)"
 by(auto simp: start_heap_sys_xcpts blank_def preallocated_def)

end
