(*  Title:      JinjaDCI/J/SmallStep.thy
    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/SmallStep.thy by Tobias Nipkow
*)

section \<open> Small Step Semantics \<close>

theory SmallStep
imports Expr State WWellForm
begin

fun blocks :: "vname list * ty list * val list * expr \<Rightarrow> expr"
where
 "blocks(V#Vs, T#Ts, v#vs, e) = {V:T := Val v; blocks(Vs,Ts,vs,e)}"
|"blocks([],[],[],e) = e"

lemmas blocks_induct = blocks.induct[split_format (complete)]

lemma [simp]:
  "\<lbrakk> size vs = size Vs; size Ts = size Vs \<rbrakk> \<Longrightarrow> fv(blocks(Vs,Ts,vs,e)) = fv e - set Vs"
(*<*)
by (induct rule:blocks_induct) auto
(*>*)


lemma sub_RI_blocks_body[iff]: "length vs = length pns \<Longrightarrow> length Ts = length pns
 \<Longrightarrow> sub_RI (blocks (pns, Ts, vs, body)) \<longleftrightarrow> sub_RI body"
proof(induct pns arbitrary: Ts vs)
  case Nil then show ?case by simp
next
  case Cons then show ?case by(cases vs; cases Ts) auto
qed


definition assigned :: "'a \<Rightarrow> 'a exp \<Rightarrow> bool"
where
  "assigned V e  \<equiv>  \<exists>v e'. e = (V := Val v;; e')"

\<comment> \<open> expression is okay to go the right side of @{text INIT} or @{text "RI \<leftarrow>"}
 or to have indicator Boolean be True (in latter case, given that class is
 also verified initialized) \<close>
fun icheck :: "'m prog \<Rightarrow> cname \<Rightarrow> 'a exp \<Rightarrow> bool" where
"icheck P C' (new C) = (C' = C)" |
"icheck P D' (C\<bullet>\<^sub>sF{D}) = ((D' = D) \<and> (\<exists>T. P \<turnstile> C has F,Static:T in D))" |
"icheck P D' (C\<bullet>\<^sub>sF{D}:=(Val v)) = ((D' = D) \<and> (\<exists>T. P \<turnstile> C has F,Static:T in D))" |
"icheck P D (C\<bullet>\<^sub>sM(es)) = ((\<exists>vs. es = map Val vs) \<and> (\<exists>Ts T m. P \<turnstile> C sees M,Static:Ts\<rightarrow>T = m in D))" |
"icheck P _ _ = False"

lemma nicheck_SFAss_nonVal: "val_of e\<^sub>2 = None \<Longrightarrow> \<not>icheck P C' (C\<bullet>\<^sub>sF{D} := (e\<^sub>2::'a exp))"
 by(rule notI, cases e\<^sub>2, auto)

inductive_set
  red  :: "J_prog \<Rightarrow> ((expr \<times> state \<times> bool) \<times> (expr \<times> state \<times> bool)) set"
  and reds  :: "J_prog \<Rightarrow> ((expr list \<times> state \<times> bool) \<times> (expr list \<times> state \<times> bool)) set"
  and red' :: "J_prog \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_,/_\<rangle>) \<rightarrow>/ (1\<langle>_,/_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
  and reds' :: "J_prog \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_,/_\<rangle>) [\<rightarrow>]/ (1\<langle>_,/_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
  for P :: J_prog
where

  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<equiv> ((e,s,b), e',s',b') \<in> red P"
| "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle> \<equiv> ((es,s,b), es',s',b') \<in> reds P"

| RedNew:
  "\<lbrakk> new_Addr h = Some a; P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>blank P C) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C, (h,l,sh), True\<rangle> \<rightarrow> \<langle>addr a, (h',l,sh), False\<rangle>"

| RedNewFail:
  "\<lbrakk> new_Addr h = None; is_class P C \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>new C, (h,l,sh), True\<rangle> \<rightarrow> \<langle>THROW OutOfMemory, (h,l,sh), False\<rangle>"

| NewInitDoneRed:
  "sh C = Some (sfs, Done) \<Longrightarrow>
  P \<turnstile> \<langle>new C, (h,l,sh), False\<rangle> \<rightarrow> \<langle>new C, (h,l,sh), True\<rangle>"

| NewInitRed:
  "\<lbrakk> \<nexists>sfs. sh C = Some (sfs, Done); is_class P C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh),False\<rangle> \<rightarrow> \<langle>INIT C ([C],False) \<leftarrow> new C,(h,l,sh),False\<rangle>"

| CastRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e, s, b\<rangle> \<rightarrow> \<langle>Cast C e', s', b'\<rangle>"

| RedCastNull:
  "P \<turnstile> \<langle>Cast C null, s, b\<rangle> \<rightarrow> \<langle>null,s,b\<rangle>"

| RedCast:
 "\<lbrakk> h a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C (addr a), (h,l,sh), b\<rangle> \<rightarrow> \<langle>addr a, (h,l,sh), b\<rangle>"

| RedCastFail:
  "\<lbrakk> h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C (addr a), (h,l,sh), b\<rangle> \<rightarrow> \<langle>THROW ClassCast, (h,l,sh), b\<rangle>"

| BinOpRed1:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e \<guillemotleft>bop\<guillemotright> e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>e' \<guillemotleft>bop\<guillemotright> e\<^sub>2, s', b'\<rangle>"

| BinOpRed2:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> e, s, b\<rangle> \<rightarrow> \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> e', s', b'\<rangle>"

| RedBinOp:
  "binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<Longrightarrow>
  P \<turnstile> \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> (Val v\<^sub>2), s, b\<rangle> \<rightarrow> \<langle>Val v,s,b\<rangle>"

| RedVar:
  "l V = Some v \<Longrightarrow>
  P \<turnstile> \<langle>Var V,(h,l,sh),b\<rangle> \<rightarrow> \<langle>Val v,(h,l,sh),b\<rangle>"

| LAssRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>V:=e,s,b\<rangle> \<rightarrow> \<langle>V:=e',s',b'\<rangle>"

| RedLAss:
  "P \<turnstile> \<langle>V:=(Val v), (h,l,sh), b\<rangle> \<rightarrow> \<langle>unit, (h,l(V\<mapsto>v),sh), b\<rangle>"

| FAccRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D}, s, b\<rangle> \<rightarrow> \<langle>e'\<bullet>F{D}, s', b'\<rangle>"

| RedFAcc:
  "\<lbrakk> h a = Some(C,fs); fs(F,D) = Some v;
     P \<turnstile> C has F,NonStatic:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>F{D}, (h,l,sh), b\<rangle> \<rightarrow> \<langle>Val v,(h,l,sh),b\<rangle>"

| RedFAccNull:
  "P \<turnstile> \<langle>null\<bullet>F{D}, s, b\<rangle> \<rightarrow> \<langle>THROW NullPointer, s, b\<rangle>"

| RedFAccNone:
  "\<lbrakk> h a = Some(C,fs); \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>F{D},(h,l,sh),b\<rangle> \<rightarrow> \<langle>THROW NoSuchFieldError,(h,l,sh),b\<rangle>"

| RedFAccStatic:
  "\<lbrakk> h a = Some(C,fs); P \<turnstile> C has F,Static:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>F{D},(h,l,sh),b\<rangle> \<rightarrow> \<langle>THROW IncompatibleClassChangeError,(h,l,sh),b\<rangle>"

| RedSFAcc:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     sh D = Some (sfs,i);
     sfs F = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh),True\<rangle> \<rightarrow> \<langle>Val v,(h,l,sh),False\<rangle>"

| SFAccInitDoneRed:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     sh D = Some (sfs,Done) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh),False\<rangle> \<rightarrow> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh),True\<rangle>"

| SFAccInitRed:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh D = Some (sfs,Done) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh),False\<rangle> \<rightarrow> \<langle>INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF{D},(h,l,sh),False\<rangle>"

| RedSFAccNone:
  "\<not>(\<exists>b t. P \<turnstile> C has F,b:t in D)
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh),b\<rangle> \<rightarrow> \<langle>THROW NoSuchFieldError,(h,l,sh),False\<rangle>"

| RedSFAccNonStatic:
  "P \<turnstile> C has F,NonStatic:t in D
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh),b\<rangle> \<rightarrow> \<langle>THROW IncompatibleClassChangeError,(h,l,sh),False\<rangle>"

| FAssRed1:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D}:=e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>e'\<bullet>F{D}:=e\<^sub>2, s', b'\<rangle>"

| FAssRed2:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Val v\<bullet>F{D}:=e, s, b\<rangle> \<rightarrow> \<langle>Val v\<bullet>F{D}:=e', s', b'\<rangle>"

| RedFAss:
  "\<lbrakk> P \<turnstile> C has F,NonStatic:t in D; h a = Some(C,fs) \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>(addr a)\<bullet>F{D}:=(Val v), (h,l,sh), b\<rangle> \<rightarrow> \<langle>unit, (h(a \<mapsto> (C,fs((F,D) \<mapsto> v))),l,sh), b\<rangle>"

| RedFAssNull:
  "P \<turnstile> \<langle>null\<bullet>F{D}:=Val v, s, b\<rangle> \<rightarrow> \<langle>THROW NullPointer, s, b\<rangle>"

| RedFAssNone:
  "\<lbrakk> h a = Some(C,fs); \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>F{D}:=(Val v),(h,l,sh),b\<rangle> \<rightarrow> \<langle>THROW NoSuchFieldError,(h,l,sh),b\<rangle>"

| RedFAssStatic:
  "\<lbrakk> h a = Some(C,fs); P \<turnstile> C has F,Static:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>F{D}:=(Val v),(h,l,sh),b\<rangle> \<rightarrow> \<langle>THROW IncompatibleClassChangeError,(h,l,sh),b\<rangle>"

| SFAssRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e, s, b\<rangle> \<rightarrow> \<langle>C\<bullet>\<^sub>sF{D}:=e', s', b'\<rangle>"

| RedSFAss:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     sh D = Some(sfs,i);
     sfs' = sfs(F\<mapsto>v); sh' = sh(D\<mapsto>(sfs',i)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=(Val v),(h,l,sh),True\<rangle> \<rightarrow> \<langle>unit,(h,l,sh'),False\<rangle>"

| SFAssInitDoneRed:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     sh D = Some(sfs,Done) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=(Val v),(h,l,sh),False\<rangle> \<rightarrow> \<langle>C\<bullet>\<^sub>sF{D}:=(Val v),(h,l,sh),True\<rangle>"

| SFAssInitRed:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh D = Some(sfs,Done) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=(Val v),(h,l,sh),False\<rangle> \<rightarrow> \<langle>INIT D ([D],False)\<leftarrow> C\<bullet>\<^sub>sF{D}:=(Val v),(h,l,sh),False\<rangle>"

| RedSFAssNone:
  "\<not>(\<exists>b t. P \<turnstile> C has F,b:t in D)
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=(Val v),s,b\<rangle> \<rightarrow> \<langle>THROW NoSuchFieldError,s,False\<rangle>"

| RedSFAssNonStatic:
  "P \<turnstile> C has F,NonStatic:t in D
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=(Val v),s,b\<rangle> \<rightarrow> \<langle>THROW IncompatibleClassChangeError,s,False\<rangle>"

| CallObj:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>M(es),s,b\<rangle> \<rightarrow> \<langle>e'\<bullet>M(es),s',b'\<rangle>"

| CallParams:
  "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>(Val v)\<bullet>M(es),s,b\<rangle> \<rightarrow> \<langle>(Val v)\<bullet>M(es'),s',b'\<rangle>"

| RedCall:
  "\<lbrakk> h a = Some(C,fs); P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D; size vs = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs), (h,l,sh), b\<rangle> \<rightarrow> \<langle>blocks(this#pns, Class D#Ts, Addr a#vs, body), (h,l,sh), b\<rangle>"

| RedCallNull:
  "P \<turnstile> \<langle>null\<bullet>M(map Val vs),s,b\<rangle> \<rightarrow> \<langle>THROW NullPointer,s,b\<rangle>"

| RedCallNone:
  "\<lbrakk> h a = Some(C,fs); \<not>(\<exists>b Ts T m D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs),(h,l,sh),b\<rangle> \<rightarrow> \<langle>THROW NoSuchMethodError,(h,l,sh),b\<rangle>"

| RedCallStatic:
  "\<lbrakk> h a = Some(C,fs); P \<turnstile> C sees M,Static:Ts\<rightarrow>T = m in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>(addr a)\<bullet>M(map Val vs),(h,l,sh),b\<rangle> \<rightarrow> \<langle>THROW IncompatibleClassChangeError,(h,l,sh),b\<rangle>"

| SCallParams:
  "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s,b\<rangle> \<rightarrow> \<langle>C\<bullet>\<^sub>sM(es'),s',b'\<rangle>"

| RedSCall:
  "\<lbrakk> P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     length vs = length pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),s,True\<rangle> \<rightarrow> \<langle>blocks(pns, Ts, vs, body), s, False\<rangle>"

| SCallInitDoneRed:
  "\<lbrakk> P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     sh D = Some(sfs,Done) \<or> (M = clinit \<and> sh D = Some(sfs,Processing)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h,l,sh), False\<rangle> \<rightarrow> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h,l,sh), True\<rangle>"

| SCallInitRed:
  "\<lbrakk> P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     \<nexists>sfs. sh D = Some(sfs,Done); M \<noteq> clinit \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),(h,l,sh), False\<rangle> \<rightarrow> \<langle>INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sM(map Val vs),(h,l,sh),False\<rangle>"

| RedSCallNone:
  "\<lbrakk> \<not>(\<exists>b Ts T m D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),s,b\<rangle> \<rightarrow> \<langle>THROW NoSuchMethodError,s,False\<rangle>"

| RedSCallNonStatic:
  "\<lbrakk> P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = m in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(map Val vs),s,b\<rangle> \<rightarrow> \<langle>THROW IncompatibleClassChangeError,s,False\<rangle>"

| BlockRedNone:
  "\<lbrakk> P \<turnstile> \<langle>e, (h,l(V:=None),sh), b\<rangle> \<rightarrow> \<langle>e', (h',l',sh'), b'\<rangle>; l' V = None; \<not> assigned V e \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T; e}, (h,l,sh), b\<rangle> \<rightarrow> \<langle>{V:T; e'}, (h',l'(V := l V),sh'), b'\<rangle>"

| BlockRedSome:
  "\<lbrakk> P \<turnstile> \<langle>e, (h,l(V:=None),sh), b\<rangle> \<rightarrow> \<langle>e', (h',l',sh'), b'\<rangle>; l' V = Some v;\<not> assigned V e \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T; e}, (h,l,sh), b\<rangle> \<rightarrow> \<langle>{V:T := Val v; e'}, (h',l'(V := l V),sh'), b'\<rangle>"

| InitBlockRed:
  "\<lbrakk> P \<turnstile> \<langle>e, (h,l(V\<mapsto>v),sh), b\<rangle> \<rightarrow> \<langle>e', (h',l',sh'), b'\<rangle>; l' V = Some v' \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>{V:T := Val v; e}, (h,l,sh), b\<rangle> \<rightarrow> \<langle>{V:T := Val v'; e'}, (h',l'(V := l V),sh'), b'\<rangle>"

| RedBlock:
  "P \<turnstile> \<langle>{V:T; Val u}, s, b\<rangle> \<rightarrow> \<langle>Val u, s, b\<rangle>"

| RedInitBlock:
  "P \<turnstile> \<langle>{V:T := Val v; Val u}, s, b\<rangle> \<rightarrow> \<langle>Val u, s, b\<rangle>"

| SeqRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e;;e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>e';;e\<^sub>2, s', b'\<rangle>"

| RedSeq:
  "P \<turnstile> \<langle>(Val v);;e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>e\<^sub>2, s, b\<rangle>"

| CondRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>if (e') e\<^sub>1 else e\<^sub>2, s', b'\<rangle>"

| RedCondT:
  "P \<turnstile> \<langle>if (true) e\<^sub>1 else e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>e\<^sub>1, s, b\<rangle>"

| RedCondF:
  "P \<turnstile> \<langle>if (false) e\<^sub>1 else e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>e\<^sub>2, s, b\<rangle>"

| RedWhile:
  "P \<turnstile> \<langle>while(b) c, s, b'\<rangle> \<rightarrow> \<langle>if(b) (c;;while(b) c) else unit, s, b'\<rangle>"

| ThrowRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e, s, b\<rangle> \<rightarrow> \<langle>throw e', s', b'\<rangle>"

| RedThrowNull:
  "P \<turnstile> \<langle>throw null, s, b\<rangle> \<rightarrow> \<langle>THROW NullPointer, s, b\<rangle>"

| TryRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>try e catch(C V) e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>try e' catch(C V) e\<^sub>2, s', b'\<rangle>"

| RedTry:
  "P \<turnstile> \<langle>try (Val v) catch(C V) e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>Val v, s, b\<rangle>"

| RedTryCatch:
  "\<lbrakk> hp s a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try (Throw a) catch(C V) e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>{V:Class C := addr a; e\<^sub>2}, s, b\<rangle>"

| RedTryFail:
  "\<lbrakk> hp s a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try (Throw a) catch(C V) e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>Throw a, s, b\<rangle>"

| ListRed1:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e#es,s,b\<rangle> [\<rightarrow>] \<langle>e'#es,s',b'\<rangle>"

| ListRed2:
  "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Val v # es,s,b\<rangle> [\<rightarrow>] \<langle>Val v # es',s',b'\<rangle>"

\<comment> \<open>Initialization procedure\<close>

| RedInit:
  "\<not>sub_RI e \<Longrightarrow> P \<turnstile> \<langle>INIT C (Nil,b) \<leftarrow> e,s,b'\<rangle> \<rightarrow> \<langle>e,s,icheck P C e\<rangle>"

| InitNoneRed:
  "sh C = None
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh(C \<mapsto> (sblank P C, Prepared))),b\<rangle>"

| RedInitDone:
  "sh C = Some(sfs,Done)
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h,l,sh),b\<rangle>"

| RedInitProcessing:
  "sh C = Some(sfs,Processing)
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h,l,sh),b\<rangle>"

| RedInitError:
  "sh C = Some(sfs,Error)
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>RI (C,THROW NoClassDefFoundError);Cs \<leftarrow> e,(h,l,sh),b\<rangle>"

| InitObjectRed:
  "\<lbrakk> sh C = Some(sfs,Prepared);
     C = Object;
     sh' = sh(C \<mapsto> (sfs,Processing)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>INIT C' (C#Cs,True) \<leftarrow> e,(h,l,sh'),b\<rangle>"

| InitNonObjectSuperRed:
  "\<lbrakk> sh C = Some(sfs,Prepared);
     C \<noteq> Object;
     class P C = Some (D,r);
     sh' = sh(C \<mapsto> (sfs,Processing)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>INIT C' (D#C#Cs,False) \<leftarrow> e,(h,l,sh'),b\<rangle>"

| RedInitRInit:
  "P \<turnstile> \<langle>INIT C' (C#Cs,True) \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>RI (C,C\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> e,(h,l,sh),b\<rangle>"

| RInitRed:
  "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>RI (C,e);Cs \<leftarrow> e\<^sub>0, s, b\<rangle> \<rightarrow> \<langle>RI (C,e');Cs \<leftarrow> e\<^sub>0, s', b'\<rangle>"

| RedRInit:
  "\<lbrakk> sh C = Some (sfs, i);
     sh' = sh(C \<mapsto> (sfs,Done));
     C' = last(C#Cs) \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>RI (C, Val v);Cs \<leftarrow> e, (h,l,sh), b\<rangle> \<rightarrow> \<langle>INIT C' (Cs,True) \<leftarrow> e, (h,l,sh'), b\<rangle>"

\<comment> \<open>Exception propagation\<close>

| CastThrow: "P \<turnstile> \<langle>Cast C (throw e), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| BinOpThrow1: "P \<turnstile> \<langle>(throw e) \<guillemotleft>bop\<guillemotright> e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| BinOpThrow2: "P \<turnstile> \<langle>(Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> (throw e), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| LAssThrow: "P \<turnstile> \<langle>V:=(throw e), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| FAccThrow: "P \<turnstile> \<langle>(throw e)\<bullet>F{D}, s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| FAssThrow1: "P \<turnstile> \<langle>(throw e)\<bullet>F{D}:=e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| FAssThrow2: "P \<turnstile> \<langle>Val v\<bullet>F{D}:=(throw e), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| SFAssThrow: "P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=(throw e), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| CallThrowObj: "P \<turnstile> \<langle>(throw e)\<bullet>M(es), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| CallThrowParams: "\<lbrakk> es = map Val vs @ throw e # es' \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>(Val v)\<bullet>M(es), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| SCallThrowParams: "\<lbrakk> es = map Val vs @ throw e # es' \<rbrakk> \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| BlockThrow: "P \<turnstile> \<langle>{V:T; Throw a}, s, b\<rangle> \<rightarrow> \<langle>Throw a, s, b\<rangle>"
| InitBlockThrow: "P \<turnstile> \<langle>{V:T := Val v; Throw a}, s, b\<rangle> \<rightarrow> \<langle>Throw a, s, b\<rangle>"
| SeqThrow: "P \<turnstile> \<langle>(throw e);;e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| CondThrow: "P \<turnstile> \<langle>if (throw e) e\<^sub>1 else e\<^sub>2, s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| ThrowThrow: "P \<turnstile> \<langle>throw(throw e), s, b\<rangle> \<rightarrow> \<langle>throw e, s, b\<rangle>"
| RInitInitThrow: "\<lbrakk> sh C = Some(sfs,i); sh' = sh(C \<mapsto> (sfs,Error)) \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>RI (C,Throw a);D#Cs \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>RI (D,Throw a);Cs \<leftarrow> e,(h,l,sh'),b\<rangle>"
| RInitThrow: "\<lbrakk> sh C = Some(sfs, i); sh' = sh(C \<mapsto> (sfs,Error)) \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>RI (C,Throw a);Nil \<leftarrow> e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>Throw a,(h,l,sh'),b\<rangle>"
(*<*)
lemmas red_reds_induct = red_reds.induct [split_format (complete)]
  and red_reds_inducts = red_reds.inducts [split_format (complete)]

inductive_cases [elim!]:
 "P \<turnstile> \<langle>V:=e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
 "P \<turnstile> \<langle>e1;;e2,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
(*>*)

subsection\<open> The reflexive transitive closure \<close>

abbreviation
  Step :: "J_prog \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_,/_\<rangle>) \<rightarrow>*/ (1\<langle>_,/_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
  where "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<equiv> ((e,s,b), e',s',b') \<in> (red P)\<^sup>*"

abbreviation
  Steps :: "J_prog \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_,/_\<rangle>) [\<rightarrow>]*/ (1\<langle>_,/_,/_\<rangle>))" [51,0,0,0,0,0,0] 81)
  where "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle> \<equiv> ((es,s,b), es',s',b') \<in> (reds P)\<^sup>*"


lemmas converse_rtrancl_induct3 =
  converse_rtrancl_induct [of "(ax, ay, az)" "(bx, by, bz)", split_format (complete),
    consumes 1, case_names refl step]

lemma converse_rtrancl_induct_red[consumes 1]:
assumes "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow>* \<langle>e',(h',l',sh'),b'\<rangle>"
and "\<And>e h l sh b. R e h l sh b e h l sh b"
and "\<And>e\<^sub>0 h\<^sub>0 l\<^sub>0 sh\<^sub>0 b\<^sub>0 e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 b\<^sub>1 e' h' l' sh' b'.
       \<lbrakk> P \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0,sh\<^sub>0),b\<^sub>0\<rangle> \<rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1,sh\<^sub>1),b\<^sub>1\<rangle>; R e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 b\<^sub>1 e' h' l' sh' b' \<rbrakk>
   \<Longrightarrow> R e\<^sub>0 h\<^sub>0 l\<^sub>0 sh\<^sub>0 b\<^sub>0 e' h' l' sh' b'"
shows "R e h l sh b e' h' l' sh' b'"
(*<*)
proof -
  { fix s s'
    assume reds: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
       and base: "\<And>e s b. R e (hp s) (lcl s) (shp s) b e (hp s) (lcl s) (shp s) b"
       and red\<^sub>1: "\<And>e\<^sub>0 s\<^sub>0 b\<^sub>0 e\<^sub>1 s\<^sub>1 b\<^sub>1 e' s' b'.
           \<lbrakk> P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0,b\<^sub>0\<rangle> \<rightarrow> \<langle>e\<^sub>1,s\<^sub>1,b\<^sub>1\<rangle>; R e\<^sub>1 (hp s\<^sub>1) (lcl s\<^sub>1) (shp s\<^sub>1) b\<^sub>1 e' (hp s') (lcl s') (shp s') b' \<rbrakk>
           \<Longrightarrow> R e\<^sub>0 (hp s\<^sub>0) (lcl s\<^sub>0) (shp s\<^sub>0) b\<^sub>0 e' (hp s') (lcl s') (shp s') b'"
    from reds have "R e (hp s) (lcl s) (shp s) b e' (hp s') (lcl s') (shp s') b'"
    proof (induct rule:converse_rtrancl_induct3)
      case refl show ?case by(rule base)
    next
      case step
      thus ?case by(blast intro:red\<^sub>1)
    qed
    }
  with assms show ?thesis by fastforce
qed
(*>*)


subsection\<open>Some easy lemmas\<close>

lemma [iff]: "\<not> P \<turnstile> \<langle>[],s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>"
(*<*)by(blast elim: reds.cases)(*>*)

lemma [iff]: "\<not> P \<turnstile> \<langle>Val v,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
(*<*)by(fastforce elim: red.cases)(*>*)

lemma val_no_step: "val_of e = \<lfloor>v\<rfloor> \<Longrightarrow> \<not> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
(*<*)by(drule val_of_spec, simp)(*>*)

lemma [iff]: "\<not> P \<turnstile> \<langle>Throw a,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
(*<*)by(fastforce elim: red.cases)(*>*)


lemma map_Vals_no_step [iff]: "\<not> P \<turnstile> \<langle>map Val vs,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>"
(*<*)
apply(induct vs arbitrary: es', simp)
apply(rule notI)
apply(erule reds.cases, auto)
done
(*>*)

lemma vals_no_step: "map_vals_of es = \<lfloor>vs\<rfloor> \<Longrightarrow> \<not> P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>"
(*<*)by(drule map_vals_of_spec, simp)(*>*)

lemma vals_throw_no_step [iff]: "\<not> P \<turnstile> \<langle>map Val vs @ Throw a # es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>"
(*<*)
apply(induct vs arbitrary: es', auto)
apply(erule reds.cases, auto)
apply(erule reds.cases, auto)
done
(*>*)

lemma lass_val_of_red:
 "\<lbrakk> lass_val_of e = \<lfloor>a\<rfloor>; P \<turnstile> \<langle>e,(h, l, sh),b\<rangle> \<rightarrow> \<langle>e',(h', l', sh'),b'\<rangle> \<rbrakk>
  \<Longrightarrow> e' = unit \<and> h' = h \<and> l' = l(fst a\<mapsto>snd a) \<and> sh' = sh \<and> b = b'"
(*<*)by(drule lass_val_of_spec, auto)(*>*)


lemma final_no_step [iff]: "final e \<Longrightarrow> \<not> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
(*<*)by(erule finalE, simp+)(*>*)

lemma finals_no_step [iff]: "finals es \<Longrightarrow> \<not> P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>"
(*<*)by(erule finalsE, simp+)(*>*)

lemma reds_final_same:
"P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> final e \<Longrightarrow> e = e' \<and> s = s' \<and> b = b'"
proof(induct rule:converse_rtrancl_induct3)
  case refl show ?case by simp
next
  case (step e0 s0 b0 e1 s1 b1) show ?case
  proof(rule finalE[OF step.prems(1)])
    fix v assume "e0 = Val v" then show ?thesis using step by simp
  next
    fix a assume "e0 = Throw a" then show ?thesis using step by simp
  qed
qed

lemma reds_throw:
"P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle> \<Longrightarrow> (\<And>e\<^sub>t. throw_of e = \<lfloor>e\<^sub>t\<rfloor> \<Longrightarrow> \<exists>e\<^sub>t'. throw_of e' = \<lfloor>e\<^sub>t'\<rfloor>)"
proof(induct rule:converse_rtrancl_induct3)
  case refl then show ?case by simp
next
  case (step e0 s0 b0 e1 s1 b1)
  then show ?case by(auto elim: red.cases)
qed

lemma red_hext_incr: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>  \<Longrightarrow> h \<unlhd> h'"
  and reds_hext_incr: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle>  \<Longrightarrow> h \<unlhd> h'"
(*<*)
proof(induct rule:red_reds_inducts)
  case RedNew thus ?case
    by(fastforce dest:new_Addr_SomeD simp:hext_def split:if_splits)
next
  case RedFAss thus ?case by(simp add:hext_def split:if_splits)
qed simp_all
(*>*)


lemma red_lcl_incr: "P \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0,sh\<^sub>0),b\<rangle> \<rightarrow> \<langle>e',(h\<^sub>1,l\<^sub>1,sh\<^sub>1),b'\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
and reds_lcl_incr: "P \<turnstile> \<langle>es,(h\<^sub>0,l\<^sub>0,sh\<^sub>0),b\<rangle> [\<rightarrow>] \<langle>es',(h\<^sub>1,l\<^sub>1,sh\<^sub>1),b'\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
(*<*)by(induct rule: red_reds_inducts)(auto simp del:fun_upd_apply)(*>*)

lemma red_lcl_add: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>l\<^sub>0. P \<turnstile> \<langle>e,(h,l\<^sub>0++l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l\<^sub>0++l',sh'),b'\<rangle>)"
and reds_lcl_add: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>l\<^sub>0. P \<turnstile> \<langle>es,(h,l\<^sub>0++l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l\<^sub>0++l',sh'),b'\<rangle>)"
(*<*)
proof (induct rule:red_reds_inducts)
  case RedCast thus ?case by(fastforce intro:red_reds.intros)
next
  case RedCastFail thus ?case by(force intro:red_reds.intros)
next
  case RedFAcc thus ?case by(fastforce intro:red_reds.intros)
next
  case RedCall thus ?case by(fastforce intro:red_reds.intros)
next
  case (InitBlockRed e h l V v sh b e' h' l' sh' b' v' T l\<^sub>0)
  have IH: "\<And>l\<^sub>0. P \<turnstile> \<langle>e,(h, l\<^sub>0 ++ l(V \<mapsto> v), sh),b\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0 ++ l', sh'),b'\<rangle>"
    and l'V: "l' V = Some v'" by fact+
  from IH have IH': "P \<turnstile> \<langle>e,(h, (l\<^sub>0 ++ l)(V \<mapsto> v), sh),b\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0 ++ l', sh'),b'\<rangle>"
    by simp
  have "(l\<^sub>0 ++ l')(V := (l\<^sub>0 ++ l) V) = l\<^sub>0 ++ l'(V := l V)"
    by(rule ext)(simp add:map_add_def)
  with red_reds.InitBlockRed[OF IH'] l'V show ?case by(simp del:fun_upd_apply)
next
  case (BlockRedNone e h l V sh b e' h' l' sh' b' T l\<^sub>0)
  have IH: "\<And>l\<^sub>0. P \<turnstile> \<langle>e,(h, l\<^sub>0 ++ l(V := None), sh),b\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0 ++ l', sh'),b'\<rangle>"
    and l'V: "l' V = None" and unass: "\<not> assigned V e" by fact+
  have "l\<^sub>0(V := None) ++ l(V := None) = (l\<^sub>0 ++ l)(V := None)"
    by(simp add:fun_eq_iff map_add_def)
  hence IH': "P \<turnstile> \<langle>e,(h, (l\<^sub>0++l)(V := None), sh),b\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0(V := None) ++ l', sh'),b'\<rangle>"
    using IH[of "l\<^sub>0(V := None)"] by simp
  have "(l\<^sub>0(V := None) ++ l')(V := (l\<^sub>0 ++ l) V) = l\<^sub>0 ++ l'(V := l V)"
    by(simp add:fun_eq_iff map_add_def)
  with red_reds.BlockRedNone[OF IH' _ unass] l'V show ?case
    by(simp add: map_add_def)
next
  case (BlockRedSome e h l V sh b e' h' l' sh' b' v T l\<^sub>0)
  have IH: "\<And>l\<^sub>0. P \<turnstile> \<langle>e,(h, l\<^sub>0 ++ l(V := None), sh),b\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0 ++ l', sh'),b'\<rangle>"
    and l'V: "l' V = Some v" and unass: "\<not> assigned V e" by fact+
  have "l\<^sub>0(V := None) ++ l(V := None) = (l\<^sub>0 ++ l)(V := None)"
    by(simp add:fun_eq_iff map_add_def)
  hence IH': "P \<turnstile> \<langle>e,(h, (l\<^sub>0++l)(V := None), sh),b\<rangle> \<rightarrow> \<langle>e',(h', l\<^sub>0(V := None) ++ l', sh'),b'\<rangle>"
    using IH[of "l\<^sub>0(V := None)"] by simp
  have "(l\<^sub>0(V := None) ++ l')(V := (l\<^sub>0 ++ l) V) = l\<^sub>0 ++ l'(V := l V)"
    by(simp add:fun_eq_iff map_add_def)
  with red_reds.BlockRedSome[OF IH' _ unass] l'V show ?case
    by(simp add:map_add_def)
next
  case RedTryCatch thus ?case by(fastforce intro:red_reds.intros)
next
  case RedTryFail thus ?case by(force intro!:red_reds.intros)
qed (simp_all add:red_reds.intros)
(*>*)


lemma Red_lcl_add:
assumes "P \<turnstile> \<langle>e,(h,l,sh), b\<rangle> \<rightarrow>* \<langle>e',(h',l',sh'), b'\<rangle>" shows "P \<turnstile> \<langle>e,(h,l\<^sub>0++l,sh),b\<rangle> \<rightarrow>* \<langle>e',(h',l\<^sub>0++l',sh'),b'\<rangle>"
(*<*)
using assms
proof(induct rule:converse_rtrancl_induct_red)
  case 1 thus ?case by simp
next
  case 2 thus ?case
    by (blast dest: red_lcl_add intro: converse_rtrancl_into_rtrancl)
qed
(*>*)

lemma assumes wf: "wwf_J_prog P"
shows red_proc_pres: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>
  \<Longrightarrow> not_init C e \<Longrightarrow> sh C = \<lfloor>(sfs, Processing)\<rfloor> \<Longrightarrow> not_init C e' \<and> (\<exists>sfs'. sh' C = \<lfloor>(sfs', Processing)\<rfloor>)"
  and reds_proc_pres: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle>
  \<Longrightarrow> not_inits C es \<Longrightarrow> sh C = \<lfloor>(sfs, Processing)\<rfloor> \<Longrightarrow> not_inits C es' \<and> (\<exists>sfs'. sh' C = \<lfloor>(sfs', Processing)\<rfloor>)"
(*<*)
proof(induct rule:red_reds_inducts)
  case RedCall then show ?case
  using sees_wwf_nsub_RI[OF wf RedCall.hyps(2)] sub_RI_blocks_body nsub_RI_not_init by auto
next
  case RedSCall then show ?case
  using sees_wwf_nsub_RI[OF wf RedSCall.hyps(1)] sub_RI_blocks_body nsub_RI_not_init by auto
next
  case (RedInitDone sh C sfs C' Cs e h l b)
  then show ?case by(cases Cs, auto)
next
  case (RedInitProcessing sh C sfs C' Cs e h l b)
  then show ?case by(cases Cs, auto)
next
  case (RedRInit sh C sfs i sh' C' Cs v e h l b)
  then show ?case by(cases Cs, auto)
next
  case (CallThrowParams es vs e es' v M h l sh b)
  then show ?case by(auto dest: not_inits_def')
next
  case (SCallThrowParams es vs e es' C M h l sh b)
  then show ?case by(auto dest: not_inits_def')
qed(auto)

end
