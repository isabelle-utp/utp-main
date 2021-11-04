(*  Title:      JinjaDCI/Compiler/J1WellForm.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory Compiler/J1WellForm.thy by Tobias Nipkow
*)

section \<open> Well-Formedness of Intermediate Language \<close>

theory J1WellForm
imports "../J/JWellForm" J1
begin

subsection "Well-Typedness"

type_synonym 
  env\<^sub>1  = "ty list"   \<comment> \<open>type environment indexed by variable number\<close>

inductive
  WT\<^sub>1 :: "[J\<^sub>1_prog,env\<^sub>1, expr\<^sub>1     , ty     ] \<Rightarrow> bool"
         ("(_,_ \<turnstile>\<^sub>1/ _ :: _)"   [51,51,51]50)
  and WTs\<^sub>1 :: "[J\<^sub>1_prog,env\<^sub>1, expr\<^sub>1 list, ty list] \<Rightarrow> bool"
         ("(_,_ \<turnstile>\<^sub>1/ _ [::] _)" [51,51,51]50)
  for P :: J\<^sub>1_prog
where
  
  WTNew\<^sub>1:
  "is_class P C  \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 new C :: Class C"

| WTCast\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class D;  is_class P C;  P \<turnstile> C \<preceq>\<^sup>* D \<or> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 Cast C e :: Class C"

| WTVal\<^sub>1:
  "typeof v = Some T \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 Val v :: T"

| WTVar\<^sub>1:
  "\<lbrakk> E!i = T; i < size E \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 Var i :: T"

| WTBinOp\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^sub>1 :: T\<^sub>1;  P,E \<turnstile>\<^sub>1 e\<^sub>2 :: T\<^sub>2;
     case bop of Eq \<Rightarrow> (P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1) \<and> T = Boolean
               | Add \<Rightarrow> T\<^sub>1 = Integer \<and> T\<^sub>2 = Integer \<and> T = Integer \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T"

| WTLAss\<^sub>1:
  "\<lbrakk> E!i = T;  i < size E; P,E \<turnstile>\<^sub>1 e :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 i:=e :: Void"

| WTFAcc\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class C;  P \<turnstile> C sees F,NonStatic:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<bullet>F{D} :: T"

| WTSFAcc\<^sub>1:
  "\<lbrakk> P \<turnstile> C sees F,Static:T in D \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 C\<bullet>\<^sub>sF{D} :: T"

| WTFAss\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^sub>1 :: Class C;  P \<turnstile> C sees F,NonStatic:T in D;  P,E \<turnstile>\<^sub>1 e\<^sub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<^sub>1\<bullet>F{D} := e\<^sub>2 :: Void"

| WTSFAss\<^sub>1:
  "\<lbrakk>  P \<turnstile> C sees F,Static:T in D;  P,E \<turnstile>\<^sub>1 e\<^sub>2 :: T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 C\<bullet>\<^sub>sF{D}:=e\<^sub>2 :: Void"

| WTCall\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Class C; P \<turnstile> C sees M,NonStatic:Ts' \<rightarrow> T = m in D;
    P,E \<turnstile>\<^sub>1 es [::] Ts;  P \<turnstile> Ts [\<le>] Ts' \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 e\<bullet>M(es) :: T"

| WTSCall\<^sub>1:
  "\<lbrakk> P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D;
     P,E \<turnstile>\<^sub>1 es [::] Ts';  P \<turnstile> Ts' [\<le>] Ts; M \<noteq> clinit \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 C\<bullet>\<^sub>sM(es) :: T"

| WTBlock\<^sub>1:
  "\<lbrakk> is_type P T; P,E@[T] \<turnstile>\<^sub>1 e::T' \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 {i:T; e} :: T'"

| WTSeq\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^sub>1::T\<^sub>1;  P,E \<turnstile>\<^sub>1 e\<^sub>2::T\<^sub>2 \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 e\<^sub>1;;e\<^sub>2 :: T\<^sub>2"

| WTCond\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Boolean;  P,E \<turnstile>\<^sub>1 e\<^sub>1::T\<^sub>1;  P,E \<turnstile>\<^sub>1 e\<^sub>2::T\<^sub>2;
    P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1;  P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T = T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T = T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 if (e) e\<^sub>1 else e\<^sub>2 :: T"

| WTWhile\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: Boolean;  P,E \<turnstile>\<^sub>1 c::T \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 while (e) c :: Void"

| WTThrow\<^sub>1:
  "P,E \<turnstile>\<^sub>1 e :: Class C  \<Longrightarrow>
  P,E \<turnstile>\<^sub>1 throw e :: Void"

| WTTry\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e\<^sub>1 :: T;  P,E@[Class C] \<turnstile>\<^sub>1 e\<^sub>2 :: T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E \<turnstile>\<^sub>1 try e\<^sub>1 catch(C i) e\<^sub>2 :: T"

| WTNil\<^sub>1:
  "P,E \<turnstile>\<^sub>1 [] [::] []"

| WTCons\<^sub>1:
  "\<lbrakk> P,E \<turnstile>\<^sub>1 e :: T; P,E \<turnstile>\<^sub>1 es [::] Ts \<rbrakk>
  \<Longrightarrow>  P,E \<turnstile>\<^sub>1 e#es [::] T#Ts"

(*<*)
declare  WT\<^sub>1_WTs\<^sub>1.intros[intro!]
declare WTNil\<^sub>1[iff]

lemmas WT\<^sub>1_WTs\<^sub>1_induct = WT\<^sub>1_WTs\<^sub>1.induct [split_format (complete)]
  and WT\<^sub>1_WTs\<^sub>1_inducts = WT\<^sub>1_WTs\<^sub>1.inducts [split_format (complete)]

inductive_cases eee[elim!]:
  "P,E \<turnstile>\<^sub>1 Val v :: T"
  "P,E \<turnstile>\<^sub>1 Var i :: T"
  "P,E \<turnstile>\<^sub>1 Cast D e :: T"
  "P,E \<turnstile>\<^sub>1 i:=e :: T"
  "P,E \<turnstile>\<^sub>1 {i:U; e} :: T"
  "P,E \<turnstile>\<^sub>1 e\<^sub>1;;e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 if (e) e\<^sub>1 else e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 while (e) c :: T"
  "P,E \<turnstile>\<^sub>1 throw e :: T"
  "P,E \<turnstile>\<^sub>1 try e\<^sub>1 catch(C i) e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 e\<bullet>F{D} :: T"
  "P,E \<turnstile>\<^sub>1 C\<bullet>\<^sub>sF{D} :: T"
  "P,E \<turnstile>\<^sub>1 e\<^sub>1\<bullet>F{D}:=e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 C\<bullet>\<^sub>sF{D}:=e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 :: T"
  "P,E \<turnstile>\<^sub>1 new C :: T"
  "P,E \<turnstile>\<^sub>1 e\<bullet>M(es) :: T"
  "P,E \<turnstile>\<^sub>1 C\<bullet>\<^sub>sM(es) :: T"
  "P,E \<turnstile>\<^sub>1 [] [::] Ts"
  "P,E \<turnstile>\<^sub>1 e#es [::] Ts"
(*>*)

lemma init_nWT\<^sub>1 [simp]:"\<not>P,E \<turnstile>\<^sub>1 INIT C (Cs,b) \<leftarrow> e :: T"
 by(auto elim:WT\<^sub>1.cases)
lemma rinit_nWT\<^sub>1 [simp]:"\<not>P,E \<turnstile>\<^sub>1 RI(C,e);Cs \<leftarrow> e' :: T"
 by(auto elim:WT\<^sub>1.cases)

lemma WTs\<^sub>1_same_size: "\<And>Ts. P,E \<turnstile>\<^sub>1 es [::] Ts \<Longrightarrow> size es = size Ts"
(*<*)by (induct es type:list) auto(*>*)


lemma WT\<^sub>1_unique:
  "P,E \<turnstile>\<^sub>1 e :: T\<^sub>1 \<Longrightarrow> (\<And>T\<^sub>2. P,E \<turnstile>\<^sub>1 e :: T\<^sub>2 \<Longrightarrow> T\<^sub>1 = T\<^sub>2)" and
  WTs\<^sub>1_unique: "P,E \<turnstile>\<^sub>1 es [::] Ts\<^sub>1 \<Longrightarrow> (\<And>Ts\<^sub>2. P,E \<turnstile>\<^sub>1 es [::] Ts\<^sub>2 \<Longrightarrow> Ts\<^sub>1 = Ts\<^sub>2)"
(*<*)
apply(induct rule:WT\<^sub>1_WTs\<^sub>1.inducts)
apply blast
apply blast
apply clarsimp
apply blast
apply clarsimp
apply(case_tac bop)
apply clarsimp
apply clarsimp
apply blast
apply (blast dest:sees_field_idemp sees_field_fun)
apply (blast dest:sees_field_fun)
apply blast
apply (blast dest:sees_field_fun)
apply (blast dest:sees_method_idemp sees_method_fun)
apply (blast dest:sees_method_fun)
apply blast
apply blast
apply blast
apply blast
apply clarify
apply blast
apply blast
apply blast
done
(*>*)


lemma assumes wf: "wf_prog p P"
shows WT\<^sub>1_is_type: "P,E \<turnstile>\<^sub>1 e :: T \<Longrightarrow> set E \<subseteq> types P \<Longrightarrow> is_type P T"
and "P,E \<turnstile>\<^sub>1 es [::] Ts \<Longrightarrow> True"
(*<*)
apply(induct rule:WT\<^sub>1_WTs\<^sub>1.inducts)
apply simp
apply simp
apply (simp add:typeof_lit_is_type)
apply (blast intro:nth_mem)
apply(simp split:bop.splits)
apply simp
apply (simp add:sees_field_is_type[OF _ wf])
apply (simp add:sees_field_is_type[OF _ wf])
apply simp
apply simp
apply(fastforce dest!: sees_wf_mdecl[OF wf] simp:wf_mdecl_def)
apply(fastforce dest!: sees_wf_mdecl[OF wf] simp:wf_mdecl_def)
apply simp
apply simp
apply blast
apply simp
apply simp
apply simp
apply simp
apply simp
done
(*>*)

lemma WT\<^sub>1_nsub_RI: "P,E \<turnstile>\<^sub>1 e :: T \<Longrightarrow> \<not>sub_RI e"
 and WTs\<^sub>1_nsub_RIs: "P,E \<turnstile>\<^sub>1 es [::] Ts \<Longrightarrow> \<not>sub_RIs es"
proof(induct rule: WT\<^sub>1_WTs\<^sub>1.inducts) qed(simp_all)

subsection\<open> Runtime Well-Typedness \<close>

inductive
  WTrt\<^sub>1 :: "J\<^sub>1_prog \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> env\<^sub>1 \<Rightarrow> expr\<^sub>1 \<Rightarrow> ty \<Rightarrow> bool"
  and WTrts\<^sub>1 :: "J\<^sub>1_prog \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> env\<^sub>1 \<Rightarrow> expr\<^sub>1 list \<Rightarrow> ty list \<Rightarrow> bool"
  and WTrt2\<^sub>1 :: "[J\<^sub>1_prog,env\<^sub>1,heap,sheap,expr\<^sub>1,ty] \<Rightarrow> bool"
        ("_,_,_,_ \<turnstile>\<^sub>1 _ : _"   [51,51,51,51]50)
  and WTrts2\<^sub>1 :: "[J\<^sub>1_prog,env\<^sub>1,heap,sheap,expr\<^sub>1 list, ty list] \<Rightarrow> bool"
        ("_,_,_,_ \<turnstile>\<^sub>1 _ [:] _" [51,51,51,51]50)
  for P :: J\<^sub>1_prog and h :: heap and sh :: sheap
where
  
  "P,E,h,sh \<turnstile>\<^sub>1 e : T \<equiv> WTrt\<^sub>1 P h sh E e T"
| "P,E,h,sh \<turnstile>\<^sub>1 es[:]Ts \<equiv> WTrts\<^sub>1 P h sh E es Ts"

| WTrtNew\<^sub>1:
  "is_class P C  \<Longrightarrow>
  P,E,h,sh \<turnstile>\<^sub>1 new C : Class C"

| WTrtCast\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 Cast C e : Class C"

| WTrtVal\<^sub>1:
  "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow>
  P,E,h,sh \<turnstile>\<^sub>1 Val v : T"

| WTrtVar\<^sub>1:
  "\<lbrakk> E!i = T; i < size E \<rbrakk>  \<Longrightarrow>
  P,E,h,sh \<turnstile>\<^sub>1 Var i : T"

| WTrtBinOpEq\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1 : T\<^sub>1;  P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>2 : T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1 \<guillemotleft>Eq\<guillemotright> e\<^sub>2 : Boolean"

| WTrtBinOpAdd\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1 : Integer;  P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>2 : Integer \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1 \<guillemotleft>Add\<guillemotright> e\<^sub>2 : Integer"

| WTrtLAss\<^sub>1:
  "\<lbrakk> E!i = T; i < size E; P,E,h,sh \<turnstile>\<^sub>1 e : T';  P \<turnstile> T' \<le> T \<rbrakk>
   \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 i:=e : Void"

| WTrtFAcc\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : Class C; P \<turnstile> C has F,NonStatic:T in D \<rbrakk> \<Longrightarrow>
  P,E,h,sh \<turnstile>\<^sub>1 e\<bullet>F{D} : T"

| WTrtFAccNT\<^sub>1:
  "P,E,h,sh \<turnstile>\<^sub>1 e : NT \<Longrightarrow>
  P,E,h,sh \<turnstile>\<^sub>1 e\<bullet>F{D} : T"

| WTrtSFAcc\<^sub>1:
  "\<lbrakk> P \<turnstile> C has F,Static:T in D \<rbrakk> \<Longrightarrow>
  P,E,h,sh \<turnstile>\<^sub>1 C\<bullet>\<^sub>sF{D} : T"

| WTrtFAss\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1 : Class C;  P \<turnstile> C has F,NonStatic:T in D; P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>2 : T\<^sub>2;  P \<turnstile> T\<^sub>2 \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1\<bullet>F{D}:=e\<^sub>2 : Void"

| WTrtFAssNT\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1:NT; P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>2 : T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1\<bullet>F{D}:=e\<^sub>2 : Void"

| WTrtSFAss\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>2 : T\<^sub>2; P \<turnstile> C has F,Static:T in D; P \<turnstile> T\<^sub>2 \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 C\<bullet>\<^sub>sF{D}:=e\<^sub>2 : Void"

| WTrtCall\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : Class C; P \<turnstile> C sees M,NonStatic:Ts \<rightarrow> T = m in D;
     P,E,h,sh \<turnstile>\<^sub>1 es [:] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 e\<bullet>M(es) : T"

| WTrtCallNT\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : NT; P,E,h,sh \<turnstile>\<^sub>1 es [:] Ts \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 e\<bullet>M(es) : T"

| WTrtSCall\<^sub>1:
  "\<lbrakk> P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D;
     P,E,h,sh \<turnstile>\<^sub>1 es [:] Ts'; P \<turnstile> Ts' [\<le>] Ts;
     M = clinit \<longrightarrow> sh D = \<lfloor>(sfs,Processing)\<rfloor> \<and> es = map Val vs \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 C\<bullet>\<^sub>sM(es) : T"

| WTrtBlock\<^sub>1:
  "P,E@[T],h,sh \<turnstile>\<^sub>1 e : T'  \<Longrightarrow>
  P,E,h,sh \<turnstile>\<^sub>1 {i:T; e} : T'"

| WTrtSeq\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1:T\<^sub>1;  P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>2:T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1;;e\<^sub>2 : T\<^sub>2"

| WTrtCond\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : Boolean;  P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1:T\<^sub>1;  P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>2:T\<^sub>2;
     P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T = T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T = T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 if (e) e\<^sub>1 else e\<^sub>2 : T"

| WTrtWhile\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : Boolean;  P,E,h,sh \<turnstile>\<^sub>1 c:T \<rbrakk>
  \<Longrightarrow>  P,E,h,sh \<turnstile>\<^sub>1 while(e) c : Void"

| WTrtThrow\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : T\<^sub>r; is_refT T\<^sub>r \<rbrakk> \<Longrightarrow>
  P,E,h,sh \<turnstile>\<^sub>1 throw e : T"

| WTrtTry\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1 : T\<^sub>1;  P,E@[Class C],h,sh \<turnstile>\<^sub>1 e\<^sub>2 : T\<^sub>2; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 try e\<^sub>1 catch(C i) e\<^sub>2 : T\<^sub>2"

| WTrtInit\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : T; \<forall>C' \<in> set (C#Cs). is_class P C'; \<not>sub_RI e;
     \<forall>C' \<in> set (tl Cs). \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>;
     b \<longrightarrow> (\<forall>C' \<in> set Cs. \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>);
     distinct Cs; supercls_lst P Cs \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 INIT C (Cs, b) \<leftarrow> e : T"

| WTrtRI\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : T; P,E,h,sh \<turnstile>\<^sub>1 e' : T'; \<forall>C' \<in> set (C#Cs). is_class P C'; \<not>sub_RI e';
     \<forall>C' \<in> set (C#Cs). not_init C' e;
     \<forall>C' \<in> set Cs. \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>;
     \<exists>sfs. sh C = \<lfloor>(sfs, Processing)\<rfloor> \<or> (sh C = \<lfloor>(sfs, Error)\<rfloor> \<and> e = THROW NoClassDefFoundError);
     distinct (C#Cs); supercls_lst P (C#Cs) \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 RI(C, e);Cs \<leftarrow> e' : T'"

\<comment> \<open>well-typed expression lists\<close>

| WTrtNil\<^sub>1:
  "P,E,h,sh \<turnstile>\<^sub>1 [] [:] []"

| WTrtCons\<^sub>1:
  "\<lbrakk> P,E,h,sh \<turnstile>\<^sub>1 e : T;  P,E,h,sh \<turnstile>\<^sub>1 es [:] Ts \<rbrakk>
  \<Longrightarrow>  P,E,h,sh \<turnstile>\<^sub>1 e#es [:] T#Ts"

(*<*)
declare WTrt\<^sub>1_WTrts\<^sub>1.intros[intro!] WTrtNil\<^sub>1[iff]
declare
  WTrtFAcc\<^sub>1[rule del] WTrtFAccNT\<^sub>1[rule del] WTrtSFAcc\<^sub>1[rule del]
  WTrtFAss\<^sub>1[rule del] WTrtFAssNT\<^sub>1[rule del] WTrtSFAss\<^sub>1[rule del]
  WTrtCall\<^sub>1[rule del] WTrtCallNT\<^sub>1[rule del] WTrtSCall\<^sub>1[rule del]

lemmas WTrt\<^sub>1_induct = WTrt\<^sub>1_WTrts\<^sub>1.induct [split_format (complete)]
  and WTrt\<^sub>1_inducts = WTrt\<^sub>1_WTrts\<^sub>1.inducts [split_format (complete)]
(*>*)

(*<*)
inductive_cases WTrt\<^sub>1_elim_cases[elim!]:
  "P,E,h,sh \<turnstile>\<^sub>1 Val v : T"
  "P,E,h,sh \<turnstile>\<^sub>1 Var i : T"
  "P,E,h,sh \<turnstile>\<^sub>1 v :=e : T"
  "P,E,h,sh \<turnstile>\<^sub>1 {i:U; e} : T"
  "P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1;;e\<^sub>2 : T\<^sub>2"
  "P,E,h,sh \<turnstile>\<^sub>1 if (e) e\<^sub>1 else e\<^sub>2 : T"
  "P,E,h,sh \<turnstile>\<^sub>1 while(e) c : T"
  "P,E,h,sh \<turnstile>\<^sub>1 throw e : T"
  "P,E,h,sh \<turnstile>\<^sub>1 try e\<^sub>1 catch(C V) e\<^sub>2 : T"
  "P,E,h,sh \<turnstile>\<^sub>1 Cast D e : T"
  "P,E,h,sh \<turnstile>\<^sub>1 e\<bullet>F{D} : T"
  "P,E,h,sh \<turnstile>\<^sub>1 C\<bullet>\<^sub>sF{D} : T"
  "P,E,h,sh \<turnstile>\<^sub>1 e\<bullet>F{D} := v : T"
  "P,E,h,sh \<turnstile>\<^sub>1 C\<bullet>\<^sub>sF{D} := v : T"
  "P,E,h,sh \<turnstile>\<^sub>1 e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
  "P,E,h,sh \<turnstile>\<^sub>1 new C : T"
  "P,E,h,sh \<turnstile>\<^sub>1 e\<bullet>M{D}(es) : T"
  "P,E,h,sh \<turnstile>\<^sub>1 C\<bullet>\<^sub>sM{D}(es) : T"
  "P,E,h,sh \<turnstile>\<^sub>1 INIT C (Cs,b) \<leftarrow> e : T"
  "P,E,h,sh \<turnstile>\<^sub>1 RI(C,e);Cs \<leftarrow> e' : T"
  "P,E,h,sh \<turnstile>\<^sub>1 [] [:] Ts"
  "P,E,h,sh \<turnstile>\<^sub>1 e#es [:] Ts"
(*>*)

lemma WT\<^sub>1_implies_WTrt\<^sub>1: "P,E \<turnstile>\<^sub>1 e :: T \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 e : T"
and WTs\<^sub>1_implies_WTrts\<^sub>1: "P,E \<turnstile>\<^sub>1 es [::] Ts \<Longrightarrow> P,E,h,sh \<turnstile>\<^sub>1 es [:] Ts"
(*<*)
apply(induct rule: WT\<^sub>1_WTs\<^sub>1_inducts)
apply fast
apply (fast)
apply(fastforce dest:typeof_lit_typeof)
apply(fast)
apply(rename_tac E e\<^sub>1 T\<^sub>1 e\<^sub>2 T\<^sub>2 bop T) apply(case_tac bop)
 apply(fastforce)
 apply(fastforce)
apply(fastforce)
apply(meson WTrtFAcc\<^sub>1 has_visible_field)
apply(meson WTrtSFAcc\<^sub>1 has_visible_field)
apply(meson WTrtFAss\<^sub>1 has_visible_field)
apply(meson WTrtSFAss\<^sub>1 has_visible_field)
apply(fastforce simp: WTrtCall\<^sub>1)
apply(fastforce simp: WTrtSCall\<^sub>1)
apply(fastforce)
apply(fastforce)
apply(fastforce simp: WTrtCond\<^sub>1)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(simp)
apply(fast)
done
(*>*)

subsection\<open> Well-formedness\<close>

\<comment> \<open>Indices in blocks increase by 1\<close>

primrec \<B> :: "expr\<^sub>1 \<Rightarrow> nat \<Rightarrow> bool"
  and \<B>s :: "expr\<^sub>1 list \<Rightarrow> nat \<Rightarrow> bool" where
"\<B> (new C) i = True" |
"\<B> (Cast C e) i = \<B> e i" |
"\<B> (Val v) i = True" |
"\<B> (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) i = (\<B> e\<^sub>1 i \<and> \<B> e\<^sub>2 i)" |
"\<B> (Var j) i = True" |
"\<B> (e\<bullet>F{D}) i = \<B> e i" |
"\<B> (C\<bullet>\<^sub>sF{D}) i = True" |
"\<B> (j:=e) i = \<B> e i" |
"\<B> (e\<^sub>1\<bullet>F{D} := e\<^sub>2) i = (\<B> e\<^sub>1 i \<and> \<B> e\<^sub>2 i)" |
"\<B> (C\<bullet>\<^sub>sF{D} := e\<^sub>2) i = \<B> e\<^sub>2 i" |
"\<B> (e\<bullet>M(es)) i = (\<B> e i \<and> \<B>s es i)" |
"\<B> (C\<bullet>\<^sub>sM(es)) i = \<B>s es i" |
"\<B> ({j:T ; e}) i = (i = j \<and> \<B> e (i+1))" |
"\<B> (e\<^sub>1;;e\<^sub>2) i = (\<B> e\<^sub>1 i \<and> \<B> e\<^sub>2 i)" |
"\<B> (if (e) e\<^sub>1 else e\<^sub>2) i = (\<B> e i \<and> \<B> e\<^sub>1 i \<and> \<B> e\<^sub>2 i)" |
"\<B> (throw e) i = \<B> e i" |
"\<B> (while (e) c) i = (\<B> e i \<and> \<B> c i)" |
"\<B> (try e\<^sub>1 catch(C j) e\<^sub>2) i = (\<B> e\<^sub>1 i \<and> i=j \<and> \<B> e\<^sub>2 (i+1))" |
"\<B> (INIT C (Cs,b) \<leftarrow> e) i = \<B> e i" |
"\<B> (RI(C,e);Cs \<leftarrow> e') i = (\<B> e i \<and> \<B> e' i)" |

"\<B>s [] i = True" |
"\<B>s (e#es) i = (\<B> e i \<and> \<B>s es i)"


definition wf_J\<^sub>1_mdecl :: "J\<^sub>1_prog \<Rightarrow> cname \<Rightarrow> expr\<^sub>1 mdecl \<Rightarrow> bool"
where
  "wf_J\<^sub>1_mdecl P C  \<equiv>  \<lambda>(M,b,Ts,T,body).
    \<not>sub_RI body \<and>
 (case b of
    NonStatic \<Rightarrow>
        (\<exists>T'. P,Class C#Ts \<turnstile>\<^sub>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
        \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1)
  | Static \<Rightarrow> (\<exists>T'. P,Ts \<turnstile>\<^sub>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
        \<D> body \<lfloor>{..<size Ts}\<rfloor> \<and> \<B> body (size Ts))"

lemma wf_J\<^sub>1_mdecl_NonStatic[simp]:
  "wf_J\<^sub>1_mdecl P C (M,NonStatic,Ts,T,body) \<equiv>
    (\<not>sub_RI body \<and>
    (\<exists>T'. P,Class C#Ts \<turnstile>\<^sub>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
     \<D> body \<lfloor>{..size Ts}\<rfloor> \<and> \<B> body (size Ts + 1))"
(*<*)by (simp add:wf_J\<^sub>1_mdecl_def)(*>*)

lemma wf_J\<^sub>1_mdecl_Static[simp]:
  "wf_J\<^sub>1_mdecl P C (M,Static,Ts,T,body) \<equiv>
    (\<not>sub_RI body \<and>
    (\<exists>T'. P,Ts \<turnstile>\<^sub>1 body :: T' \<and> P \<turnstile> T' \<le> T) \<and>
     \<D> body \<lfloor>{..<size Ts}\<rfloor> \<and> \<B> body (size Ts))"
(*<*)by (simp add:wf_J\<^sub>1_mdecl_def)(*>*)

abbreviation "wf_J\<^sub>1_prog == wf_prog wf_J\<^sub>1_mdecl"

lemma sees_wf\<^sub>1_nsub_RI:
 "\<lbrakk> wf_J\<^sub>1_prog P; P \<turnstile> C sees M,b : Ts\<rightarrow>T = body in D \<rbrakk> \<Longrightarrow> \<not>sub_RI body"
apply(drule sees_wf_mdecl, simp)
apply(unfold wf_J\<^sub>1_mdecl_def wf_mdecl_def, simp)
done

lemma wf\<^sub>1_types_clinit:
assumes wf:"wf_prog wf_md P" and ex: "class P C = Some a" and proc: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
shows "P,E,h,sh \<turnstile>\<^sub>1 C\<bullet>\<^sub>sclinit([]) : Void"
proof -
  from ex obtain D fs ms where "a = (D,fs,ms)" by(cases a)
  then have sP: "(C, D, fs, ms) \<in> set P" using ex map_of_SomeD[of P C a] by(simp add: class_def)
  then have "wf_clinit ms" using assms by(unfold wf_prog_def wf_cdecl_def, auto)
  then obtain m where sm: "(clinit, Static, [], Void, m) \<in> set ms"
    by(unfold wf_clinit_def) auto
  then have "P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = m in C"
    using mdecl_visible[OF wf sP sm] by simp
  then show ?thesis using WTrtSCall\<^sub>1 proc by blast
qed


lemma assumes wf: "wf_J\<^sub>1_prog P"
shows eval\<^sub>1_proc_pres: "P \<turnstile>\<^sub>1 \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>
  \<Longrightarrow> not_init C e \<Longrightarrow> \<exists>sfs. sh C = \<lfloor>(sfs, Processing)\<rfloor> \<Longrightarrow> \<exists>sfs'. sh' C = \<lfloor>(sfs', Processing)\<rfloor>"
  and evals\<^sub>1_proc_pres: "P \<turnstile>\<^sub>1 \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle>
  \<Longrightarrow> not_inits C es \<Longrightarrow> \<exists>sfs. sh C = \<lfloor>(sfs, Processing)\<rfloor> \<Longrightarrow> \<exists>sfs'. sh' C = \<lfloor>(sfs', Processing)\<rfloor>"
(*<*)
proof(induct rule:eval\<^sub>1_evals\<^sub>1_inducts)
  case Call\<^sub>1 then show ?case using sees_wf\<^sub>1_nsub_RI[OF wf Call\<^sub>1.hyps(6)] nsub_RI_not_init by auto
next
  case (SCallInit\<^sub>1 ps h l sh vs h\<^sub>1 l\<^sub>1 sh\<^sub>1 C' M Ts T body D v' h\<^sub>2 l\<^sub>2 sh\<^sub>2 l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3)
  then show ?case
    using SCallInit\<^sub>1 sees_wf\<^sub>1_nsub_RI[OF wf SCallInit\<^sub>1.hyps(3)] nsub_RI_not_init[of body] by auto
next
  case SCall\<^sub>1 then show ?case using sees_wf\<^sub>1_nsub_RI[OF wf SCall\<^sub>1.hyps(3)] nsub_RI_not_init by auto
next
  case (InitNone\<^sub>1 sh C1 C' Cs h l e' a a b) then show ?case by(cases "C = C1") auto
next
  case (InitDone\<^sub>1 sh C sfs C' Cs h l e' a a b) then show ?case by(cases Cs, auto)
next
  case (InitProcessing\<^sub>1 sh C sfs C' Cs h l e' a a b) then show ?case by(cases Cs, auto)
next
  case (InitError\<^sub>1 sh C1 sfs Cs h l e' a a b C') then show ?case by(cases "C = C1") auto
next
  case (InitObject\<^sub>1 sh C1 sfs sh' C' Cs h l e' a a b) then show ?case by(cases "C = C1") auto
next
  case (InitNonObject\<^sub>1 sh C1 sfs D a b sh' C' Cs h l e' a a b)
  then show ?case by(cases "C = C1") auto
next
  case (RInit\<^sub>1 e a a b v h' l' sh' C sfs i sh'' C' Cs e\<^sub>1 a a b) then show ?case by(cases Cs, auto)
next
  case (RInitInitFail\<^sub>1 e h l sh a h' l' sh' C1 sfs i sh'' D Cs e\<^sub>1 h1 l1 sh1)
  then show ?case using eval\<^sub>1_final by fastforce
qed(auto)

lemma clinit\<^sub>1_proc_pres:
  "\<lbrakk> wf_J\<^sub>1_prog P; P \<turnstile>\<^sub>1 \<langle>C\<^sub>0\<bullet>\<^sub>sclinit([]),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>;
     sh C' = \<lfloor>(sfs,Processing)\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>sfs. sh' C' = \<lfloor>(sfs,Processing)\<rfloor>"
 by(auto dest: eval\<^sub>1_proc_pres)

end
