(*  Title:      JinjaDCI/J/WellTypeRT.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/WellTypeRT.thy by Tobias Nipkow
*)

section \<open> Runtime Well-typedness \<close>

theory WellTypeRT
imports WellType
begin

inductive
  WTrt :: "J_prog \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
  and WTrts :: "J_prog \<Rightarrow> heap \<Rightarrow> sheap \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool"
  and WTrt2 :: "[J_prog,env,heap,sheap,expr,ty] \<Rightarrow> bool"
        ("_,_,_,_ \<turnstile> _ : _"   [51,51,51,51]50)
  and WTrts2 :: "[J_prog,env,heap,sheap,expr list, ty list] \<Rightarrow> bool"
        ("_,_,_,_ \<turnstile> _ [:] _" [51,51,51,51]50)
  for P :: J_prog and h :: heap and sh :: sheap
where
  
  "P,E,h,sh \<turnstile> e : T \<equiv> WTrt P h sh E e T"
| "P,E,h,sh \<turnstile> es[:]Ts \<equiv> WTrts P h sh E es Ts"

| WTrtNew:
  "is_class P C  \<Longrightarrow>
  P,E,h,sh \<turnstile> new C : Class C"

| WTrtCast:
  "\<lbrakk> P,E,h,sh \<turnstile> e : T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> Cast C e : Class C"

| WTrtVal:
  "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow>
  P,E,h,sh \<turnstile> Val v : T"

| WTrtVar:
  "E V = Some T  \<Longrightarrow>
  P,E,h,sh \<turnstile> Var V : T"

| WTrtBinOpEq:
  "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1 : T\<^sub>1;  P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1 \<guillemotleft>Eq\<guillemotright> e\<^sub>2 : Boolean"

| WTrtBinOpAdd:
  "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1 : Integer;  P,E,h,sh \<turnstile> e\<^sub>2 : Integer \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1 \<guillemotleft>Add\<guillemotright> e\<^sub>2 : Integer"

| WTrtLAss:
  "\<lbrakk> E V = Some T;  P,E,h,sh \<turnstile> e : T';  P \<turnstile> T' \<le> T \<rbrakk>
   \<Longrightarrow> P,E,h,sh \<turnstile> V:=e : Void"

| WTrtFAcc:
  "\<lbrakk> P,E,h,sh \<turnstile> e : Class C; P \<turnstile> C has F,NonStatic:T in D \<rbrakk> \<Longrightarrow>
  P,E,h,sh \<turnstile> e\<bullet>F{D} : T"

| WTrtFAccNT:
  "P,E,h,sh \<turnstile> e : NT \<Longrightarrow>
  P,E,h,sh \<turnstile> e\<bullet>F{D} : T"

| WTrtSFAcc:
  "\<lbrakk> P \<turnstile> C has F,Static:T in D \<rbrakk> \<Longrightarrow>
  P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D} : T"

| WTrtFAss:
  "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1 : Class C;  P \<turnstile> C has F,NonStatic:T in D; P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2;  P \<turnstile> T\<^sub>2 \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 : Void"

| WTrtFAssNT:
  "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1:NT; P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 : Void"

| WTrtSFAss:
  "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2; P \<turnstile> C has F,Static:T in D; P \<turnstile> T\<^sub>2 \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D}:=e\<^sub>2 : Void"

| WTrtCall:
  "\<lbrakk> P,E,h,sh \<turnstile> e : Class C; P \<turnstile> C sees M,NonStatic:Ts \<rightarrow> T = (pns,body) in D;
     P,E,h,sh \<turnstile> es [:] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<bullet>M(es) : T"

| WTrtCallNT:
  "\<lbrakk> P,E,h,sh \<turnstile> e : NT; P,E,h,sh \<turnstile> es [:] Ts \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<bullet>M(es) : T"

| WTrtSCall:
  "\<lbrakk> P \<turnstile> C sees M,Static:Ts \<rightarrow> T = (pns,body) in D;
     P,E,h,sh \<turnstile> es [:] Ts'; P \<turnstile> Ts' [\<le>] Ts;
     M = clinit \<longrightarrow> sh D = \<lfloor>(sfs,Processing)\<rfloor> \<and> es = map Val vs \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> C\<bullet>\<^sub>sM(es) : T"

| WTrtBlock:
  "P,E(V\<mapsto>T),h,sh \<turnstile> e : T'  \<Longrightarrow>
  P,E,h,sh \<turnstile> {V:T; e} : T'"

| WTrtSeq:
  "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1:T\<^sub>1;  P,E,h,sh \<turnstile> e\<^sub>2:T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1;;e\<^sub>2 : T\<^sub>2"

| WTrtCond:
  "\<lbrakk> P,E,h,sh \<turnstile> e : Boolean;  P,E,h,sh \<turnstile> e\<^sub>1:T\<^sub>1;  P,E,h,sh \<turnstile> e\<^sub>2:T\<^sub>2;
     P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T = T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T = T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 : T"

| WTrtWhile:
  "\<lbrakk> P,E,h,sh \<turnstile> e : Boolean;  P,E,h,sh \<turnstile> c:T \<rbrakk>
  \<Longrightarrow>  P,E,h,sh \<turnstile> while(e) c : Void"

| WTrtThrow:
  "\<lbrakk> P,E,h,sh \<turnstile> e : T\<^sub>r; is_refT T\<^sub>r \<rbrakk> \<Longrightarrow>
  P,E,h,sh \<turnstile> throw e : T"

| WTrtTry:
  "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1 : T\<^sub>1;  P,E(V \<mapsto> Class C),h,sh \<turnstile> e\<^sub>2 : T\<^sub>2; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 : T\<^sub>2"

| WTrtInit:
  "\<lbrakk> P,E,h,sh \<turnstile> e : T; \<forall>C' \<in> set (C#Cs). is_class P C'; \<not>sub_RI e;
     \<forall>C' \<in> set (tl Cs). \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>;
     b \<longrightarrow> (\<forall>C' \<in> set Cs. \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>);
     distinct Cs; supercls_lst P Cs \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> INIT C (Cs, b) \<leftarrow> e : T"

| WTrtRI:
  "\<lbrakk> P,E,h,sh \<turnstile> e : T; P,E,h,sh \<turnstile> e' : T'; \<forall>C' \<in> set (C#Cs). is_class P C'; \<not>sub_RI e';
     \<forall>C' \<in> set (C#Cs). not_init C' e;
     \<forall>C' \<in> set Cs. \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>;
     \<exists>sfs. sh C = \<lfloor>(sfs, Processing)\<rfloor> \<or> (sh C = \<lfloor>(sfs, Error)\<rfloor> \<and> e = THROW NoClassDefFoundError);
     distinct (C#Cs); supercls_lst P (C#Cs) \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> RI(C, e);Cs \<leftarrow> e' : T'"

\<comment> \<open>well-typed expression lists\<close>

| WTrtNil:
  "P,E,h,sh \<turnstile> [] [:] []"

| WTrtCons:
  "\<lbrakk> P,E,h,sh \<turnstile> e : T;  P,E,h,sh \<turnstile> es [:] Ts \<rbrakk>
  \<Longrightarrow>  P,E,h,sh \<turnstile> e#es [:] T#Ts"

(*<*)
declare WTrt_WTrts.intros[intro!] WTrtNil[iff]
declare
  WTrtFAcc[rule del] WTrtFAccNT[rule del] WTrtSFAcc[rule del]
  WTrtFAss[rule del] WTrtFAssNT[rule del] WTrtSFAss[rule del]
  WTrtCall[rule del] WTrtCallNT[rule del] WTrtSCall[rule del]

lemmas WTrt_induct = WTrt_WTrts.induct [split_format (complete)]
  and WTrt_inducts = WTrt_WTrts.inducts [split_format (complete)]
(*>*)


subsection\<open>Easy consequences\<close>

lemma [iff]: "(P,E,h,sh \<turnstile> [] [:] Ts) = (Ts = [])"
(*<*)
apply(rule iffI)
apply (auto elim: WTrts.cases)
done
(*>*)

lemma [iff]: "(P,E,h,sh \<turnstile> e#es [:] T#Ts) = (P,E,h,sh \<turnstile> e : T \<and> P,E,h,sh \<turnstile> es [:] Ts)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrts.cases)
done
(*>*)

lemma [iff]: "(P,E,h,sh \<turnstile> (e#es) [:] Ts) =
  (\<exists>U Us. Ts = U#Us \<and> P,E,h,sh \<turnstile> e : U \<and> P,E,h,sh \<turnstile> es [:] Us)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrts.cases)
done
(*>*)

lemma [simp]: "\<forall>Ts. (P,E,h,sh \<turnstile> es\<^sub>1 @ es\<^sub>2 [:] Ts) =
  (\<exists>Ts\<^sub>1 Ts\<^sub>2. Ts = Ts\<^sub>1 @ Ts\<^sub>2 \<and> P,E,h,sh \<turnstile> es\<^sub>1 [:] Ts\<^sub>1 & P,E,h,sh \<turnstile> es\<^sub>2[:]Ts\<^sub>2)"
(*<*)
apply(induct_tac es\<^sub>1)
 apply simp
apply clarsimp
apply(erule thin_rl)
apply (rule iffI)
 apply clarsimp
 apply(rule exI)+
 apply(rule conjI)
  prefer 2 apply blast
 apply simp
apply fastforce
done
(*>*)

lemma [iff]: "P,E,h,sh \<turnstile> Val v : T = (typeof\<^bsub>h\<^esub> v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

lemma [iff]: "P,E,h,sh \<turnstile> Var v : T = (E v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

lemma [iff]: "P,E,h,sh \<turnstile> e\<^sub>1;;e\<^sub>2 : T\<^sub>2 = (\<exists>T\<^sub>1. P,E,h,sh \<turnstile> e\<^sub>1:T\<^sub>1 \<and> P,E,h,sh \<turnstile> e\<^sub>2:T\<^sub>2)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)

lemma [iff]: "P,E,h,sh \<turnstile> {V:T; e} : T'  =  (P,E(V\<mapsto>T),h,sh \<turnstile> e : T')"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt.cases)
done
(*>*)
(*<*)
inductive_cases WTrt_elim_cases[elim!]:
  "P,E,h,sh \<turnstile> v :=e : T"
  "P,E,h,sh \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 : T"
  "P,E,h,sh \<turnstile> while(e) c : T"
  "P,E,h,sh \<turnstile> throw e : T"
  "P,E,h,sh \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 : T"
  "P,E,h,sh \<turnstile> Cast D e : T"
  "P,E,h,sh \<turnstile> e\<bullet>F{D} : T"
  "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D} : T"
  "P,E,h,sh \<turnstile> e\<bullet>F{D} := v : T"
  "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D} := v : T"
  "P,E,h,sh \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
  "P,E,h,sh \<turnstile> new C : T"
  "P,E,h,sh \<turnstile> e\<bullet>M{D}(es) : T"
  "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sM{D}(es) : T"
  "P,E,h,sh \<turnstile> INIT C (Cs,b) \<leftarrow> e : T"
  "P,E,h,sh \<turnstile> RI(C,e);Cs \<leftarrow> e' : T"
(*>*)

subsection\<open>Some interesting lemmas\<close>

lemma WTrts_Val[simp]:
 "\<And>Ts. (P,E,h,sh \<turnstile> map Val vs [:] Ts) = (map (typeof\<^bsub>h\<^esub>) vs = map Some Ts)"
(*<*)
apply(induct vs)
 apply simp
apply(case_tac Ts)
 apply simp
apply simp
done
(*>*)


lemma WTrts_same_length: "\<And>Ts. P,E,h,sh \<turnstile> es [:] Ts \<Longrightarrow> length es = length Ts"
(*<*)by(induct es type:list)auto(*>*)


lemma WTrt_env_mono:
  "P,E,h,sh \<turnstile> e : T \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h,sh \<turnstile> e : T)" and
  "P,E,h,sh \<turnstile> es [:] Ts \<Longrightarrow> (\<And>E'. E \<subseteq>\<^sub>m E' \<Longrightarrow> P,E',h,sh \<turnstile> es [:] Ts)"
(*<*)
proof(induct rule: WTrt_inducts)
  case (WTrtVar E V T)
  then show ?case by(simp add: WTrtVar map_le_def dom_def)
next
  case (WTrtLAss E V T e T')
  then show ?case by(force simp: map_le_def)
qed(fastforce intro: WTrt_WTrts.intros)+
(*>*)


lemma WTrt_hext_mono: "P,E,h,sh \<turnstile> e : T \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h',sh \<turnstile> e : T"
and WTrts_hext_mono: "P,E,h,sh \<turnstile> es [:] Ts \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,E,h',sh \<turnstile> es [:] Ts"
(*<*)
apply(induct rule: WTrt_inducts)
apply(simp add: WTrtNew)
apply(fastforce simp: WTrtCast)
apply(fastforce simp: WTrtVal dest:hext_typeof_mono)
apply(simp add: WTrtVar)
apply(fastforce simp add: WTrtBinOpEq)
apply(fastforce simp add: WTrtBinOpAdd)
apply(fastforce simp add: WTrtLAss)
apply(fast intro: WTrtFAcc)
apply(simp add: WTrtFAccNT)
apply(fast intro: WTrtSFAcc)
apply(fastforce simp: WTrtFAss del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce simp: WTrtFAssNT)
apply(fastforce simp: WTrtSFAss del:WTrt_WTrts.intros WTrt_elim_cases)
apply(fastforce simp: WTrtCall)
apply(fastforce simp: WTrtCallNT)
using WTrtSCall apply blast
apply(fastforce)
apply(fastforce simp add: WTrtSeq)
apply(fastforce simp add: WTrtCond)
apply(fastforce simp add: WTrtWhile)
apply(fastforce simp add: WTrtThrow)
apply(fastforce simp: WTrtTry)
apply(simp add: WTrtInit)
apply(simp add: WTrtRI)
apply(simp add: WTrtNil)
apply(simp add: WTrtCons)
done
(*>*)

lemma WTrt_shext_mono: "P,E,h,sh \<turnstile> e : T \<Longrightarrow> sh \<unlhd>\<^sub>s sh' \<Longrightarrow> \<not>sub_RI e \<Longrightarrow> P,E,h,sh' \<turnstile> e : T"
and WTrts_shext_mono: "P,E,h,sh \<turnstile> es [:] Ts \<Longrightarrow> sh \<unlhd>\<^sub>s sh' \<Longrightarrow> \<not>sub_RIs es \<Longrightarrow> P,E,h,sh' \<turnstile> es [:] Ts"
(*<*)
by(induct rule: WTrt_inducts)
  (auto simp add: WTrt_WTrts.intros)
(*>*)

lemma WTrt_hext_shext_mono: "P,E,h,sh \<turnstile> e : T
   \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> sh \<unlhd>\<^sub>s sh' \<Longrightarrow> \<not>sub_RI e \<Longrightarrow> P,E,h',sh' \<turnstile> e : T"
 by(auto intro: WTrt_hext_mono WTrt_shext_mono)

lemma WTrts_hext_shext_mono: "P,E,h,sh \<turnstile> es [:] Ts
   \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> sh \<unlhd>\<^sub>s sh' \<Longrightarrow> \<not>sub_RIs es \<Longrightarrow> P,E,h',sh' \<turnstile> es [:] Ts"
 by(auto intro: WTrts_hext_mono WTrts_shext_mono)


lemma WT_implies_WTrt: "P,E \<turnstile> e :: T \<Longrightarrow> P,E,h,sh \<turnstile> e : T"
and WTs_implies_WTrts: "P,E \<turnstile> es [::] Ts \<Longrightarrow> P,E,h,sh \<turnstile> es [:] Ts"
(*<*)
apply(induct rule: WT_WTs_inducts)
apply fast
apply (fast)
apply(fastforce dest:typeof_lit_typeof)
apply(simp)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(meson WTrtFAcc has_visible_field)
apply(meson WTrtSFAcc has_visible_field)
apply(meson WTrtFAss has_visible_field)
apply(meson WTrtSFAss has_visible_field)
apply(fastforce simp: WTrtCall)
apply(fastforce simp: WTrtSCall)
apply(fastforce)
apply(fastforce)
apply(fastforce simp: WTrtCond)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(simp)
apply(simp)
done
(*>*)

end
