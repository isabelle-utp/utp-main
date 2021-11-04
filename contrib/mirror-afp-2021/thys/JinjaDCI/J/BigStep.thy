(*  Title:      JinjaDCI/J/BigStep.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/BigStep.thy by Tobias Nipkow
*)

section \<open> Big Step Semantics \<close>

theory BigStep imports Expr State WWellForm begin

inductive
  eval :: "J_prog \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> state \<Rightarrow> bool"
          ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  and evals :: "J_prog \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> expr list \<Rightarrow> state \<Rightarrow> bool"
           ("_ \<turnstile> ((1\<langle>_,/_\<rangle>) [\<Rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  for P :: J_prog
where

  New:
  "\<lbrakk> sh C = Some (sfs, Done); new_Addr h = Some a;
     P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>blank P C) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>addr a,(h',l,sh)\<rangle>"

| NewFail:
  "\<lbrakk> sh C = Some (sfs, Done); new_Addr h = None; is_class P C \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>new C, (h,l,sh)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l,sh)\<rangle>"

| NewInit:
  "\<lbrakk> \<nexists>sfs. sh C = Some (sfs, Done); P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v',(h',l',sh')\<rangle>;
     new_Addr h' = Some a; P \<turnstile> C has_fields FDTs; h'' = h'(a\<mapsto>blank P C) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>addr a,(h'',l',sh')\<rangle>"

| NewInitOOM:
  "\<lbrakk> \<nexists>sfs. sh C = Some (sfs, Done); P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v',(h',l',sh')\<rangle>;
     new_Addr h' = None; is_class P C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h',l',sh')\<rangle>"

| NewInitThrow:
  "\<lbrakk> \<nexists>sfs. sh C = Some (sfs, Done); P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>;
     is_class P C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"

| Cast:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>; h a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>"

| CastNull:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"

| CastFail:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle>\<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>; h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,(h,l,sh)\<rangle>"

| CastThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Val:
  "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"

| BinOp:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>2,s\<^sub>2\<rangle>; binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>2\<rangle>"

| BinOpThrow1:
  "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle>"

| BinOpThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle>"

| Var:
  "l V = Some v \<Longrightarrow>
  P \<turnstile> \<langle>Var V,(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h,l,sh)\<rangle>"

| LAss:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l,sh)\<rangle>; l' = l(V\<mapsto>v) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h,l',sh)\<rangle>"

| LAssThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>V:=e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAcc:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>; h a = Some(C,fs);
     P \<turnstile> C has F,NonStatic:t in D;
     fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,l,sh)\<rangle>"

| FAccNull:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"

| FAccThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAccNone:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>; h a = Some(C,fs);
    \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h,l,sh)\<rangle>"

| FAccStatic:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>; h a = Some(C,fs);
    P \<turnstile> C has F,Static:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h,l,sh)\<rangle>"

| SFAcc:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     sh D = Some (sfs,Done);
     sfs F = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h,l,sh)\<rangle>"

| SFAccInit:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh D = Some (sfs,Done); P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v',(h',l',sh')\<rangle>;
     sh' D = Some (sfs,i);
     sfs F = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h',l',sh')\<rangle>"

| SFAccInitThrow:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh D = Some (sfs,Done); P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},(h,l,sh)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"

| SFAccNone:
  "\<lbrakk> \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,s\<rangle>"

| SFAccNonStatic:
  "\<lbrakk> P \<turnstile> C has F,NonStatic:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,s\<rangle>"

| FAss:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C has F,NonStatic:t in D;
     fs' = fs((F,D)\<mapsto>v); h\<^sub>2' = h\<^sub>2(a\<mapsto>(C,fs')) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h\<^sub>2',l\<^sub>2,sh\<^sub>2)\<rangle>"

| FAssNull:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"

| FAssThrow1:
  "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAssThrow2:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| FAssNone:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"

| FAssStatic:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C has F,Static:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"

| SFAss:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C has F,Static:t in D;
     sh\<^sub>1 D = Some(sfs,Done); sfs' = sfs(F\<mapsto>v); sh\<^sub>1' = sh\<^sub>1(D\<mapsto>(sfs',Done)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1')\<rangle>"

| SFAssInit:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done); P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>Val v',(h',l',sh')\<rangle>;
     sh' D = Some(sfs,i);
     sfs' = sfs(F\<mapsto>v); sh'' = sh'(D\<mapsto>(sfs',i)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h',l',sh'')\<rangle>"

| SFAssInitThrow:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done); P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"

| SFAssThrow:
  "P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| SFAssNone:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
    \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"

| SFAssNonStatic:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
    P \<turnstile> C has F,NonStatic:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"

| CallObjThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| CallParamsThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw ex # es',s\<^sub>2\<rangle> \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"

| CallNull:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"

| CallNone:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); \<not>(\<exists>b Ts T m D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchMethodError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"

| CallStatic:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C sees M,Static:Ts\<rightarrow>T = m in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"

| Call:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile> \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D;
     length vs = length pns;  l\<^sub>2' = [this\<mapsto>Addr a, pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2,sh\<^sub>3)\<rangle>"

| SCallParamsThrow:
  "\<lbrakk> P \<turnstile> \<langle>es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs @ throw ex # es',s\<^sub>2\<rangle> \<rbrakk>
   \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"

| SCallNone:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle>;
     \<not>(\<exists>b Ts T m D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchMethodError,s\<^sub>2\<rangle>"

| SCallNonStatic:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle>;
     P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = m in D \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,s\<^sub>2\<rangle>"

| SCallInitThrow:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     \<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done); M \<noteq> clinit;
     P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"

| SCallInit:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     \<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done); M \<noteq> clinit;
     P \<turnstile> \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>Val v',(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     length vs = length pns;  l\<^sub>2' = [pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2,sh\<^sub>3)\<rangle>"

| SCall:
  "\<lbrakk> P \<turnstile> \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D;
     sh\<^sub>2 D = Some(sfs,Done) \<or> (M = clinit \<and> sh\<^sub>2 D = Some(sfs,Processing));
     length vs = length pns;  l\<^sub>2' = [pns[\<mapsto>]vs];
     P \<turnstile> \<langle>body,(h\<^sub>2,l\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,l\<^sub>2,sh\<^sub>3)\<rangle>"

| Block:
  "P \<turnstile> \<langle>e\<^sub>0,(h\<^sub>0,l\<^sub>0(V:=None),sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>{V:T; e\<^sub>0},(h\<^sub>0,l\<^sub>0,sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,l\<^sub>1(V:=l\<^sub>0 V),sh\<^sub>1)\<rangle>"

| Seq:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"

| SeqThrow:
  "P \<turnstile> \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle>"

| CondT:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"

| CondF:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle>; P \<turnstile> \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"

| CondThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| WhileF:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,s\<^sub>1\<rangle>"

| WhileT:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>; P \<turnstile> \<langle>while (e) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle>"

| WhileCondThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| WhileBodyThrow:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile> \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| Throw:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,s\<^sub>1\<rangle>"

| ThrowNull:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"

| ThrowThrow:
  "P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Try:
  "P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>"

| TryCatch:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;  h\<^sub>1 a = Some(D,fs);  P \<turnstile> D \<preceq>\<^sup>* C;
     P \<turnstile> \<langle>e\<^sub>2,(h\<^sub>1,l\<^sub>1(V\<mapsto>Addr a),sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,l\<^sub>2(V:=l\<^sub>1 V),sh\<^sub>2)\<rangle>"

| TryThrow:
  "\<lbrakk> P \<turnstile> \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;  h\<^sub>1 a = Some(D,fs);  \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>"

| Nil:
  "P \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>[],s\<rangle>"

| Cons:
  "\<lbrakk> P \<turnstile> \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>Val v # es',s\<^sub>2\<rangle>"

| ConsThrow:
  "P \<turnstile> \<langle>e, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e', s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile> \<langle>e#es, s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>throw e' # es, s\<^sub>1\<rangle>"

\<comment> \<open> init rules \<close>

| InitFinal:
  "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile> \<langle>INIT C (Nil,b) \<leftarrow> e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

| InitNone:
  "\<lbrakk> sh C = None; P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh(C \<mapsto> (sblank P C, Prepared)))\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

| InitDone:
  "\<lbrakk> sh C = Some(sfs,Done); P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

| InitProcessing:
  "\<lbrakk> sh C = Some(sfs,Processing); P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

\<comment> \<open> note that @{text RI} will mark all classes in the list Cs with the Error flag \<close>
| InitError:
  "\<lbrakk> sh C = Some(sfs,Error);
     P \<turnstile> \<langle>RI (C, THROW NoClassDefFoundError);Cs \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

| InitObject:
  "\<lbrakk> sh C = Some(sfs,Prepared);
     C = Object;
     sh' = sh(C \<mapsto> (sfs,Processing));
     P \<turnstile> \<langle>INIT C' (C#Cs,True) \<leftarrow> e,(h,l,sh')\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

| InitNonObject:
  "\<lbrakk> sh C = Some(sfs,Prepared);
     C \<noteq> Object;
     class P C = Some (D,r);
     sh' = sh(C \<mapsto> (sfs,Processing));
     P \<turnstile> \<langle>INIT C' (D#C#Cs,False) \<leftarrow> e,(h,l,sh')\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

| InitRInit:
  "P \<turnstile> \<langle>RI (C,C\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
  \<Longrightarrow> P \<turnstile> \<langle>INIT C' (C#Cs,True) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

| RInit:
  "\<lbrakk> P \<turnstile> \<langle>e',s\<rangle> \<Rightarrow> \<langle>Val v, (h',l',sh')\<rangle>;
     sh' C = Some(sfs, i); sh'' = sh'(C \<mapsto> (sfs, Done));
     C' = last(C#Cs);
     P \<turnstile> \<langle>INIT C' (Cs,True) \<leftarrow> e, (h',l',sh'')\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>RI (C,e');Cs \<leftarrow> e,s\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle>"

| RInitInitFail:
  "\<lbrakk> P \<turnstile> \<langle>e',s\<rangle> \<Rightarrow> \<langle>throw a, (h',l',sh')\<rangle>;
     sh' C = Some(sfs, i); sh'' = sh'(C \<mapsto> (sfs, Error));
     P \<turnstile> \<langle>RI (D,throw a);Cs \<leftarrow> e, (h',l',sh'')\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>RI (C,e');D#Cs \<leftarrow> e,s\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle>"

| RInitFailFinal:
  "\<lbrakk> P \<turnstile> \<langle>e',s\<rangle> \<Rightarrow> \<langle>throw a, (h',l',sh')\<rangle>;
     sh' C = Some(sfs, i); sh'' = sh'(C \<mapsto> (sfs, Error)) \<rbrakk>
  \<Longrightarrow> P \<turnstile> \<langle>RI (C,e');Nil \<leftarrow> e,s\<rangle> \<Rightarrow> \<langle>throw a, (h',l',sh'')\<rangle>"

(*<*)
lemmas eval_evals_induct = eval_evals.induct [split_format (complete)]
  and eval_evals_inducts = eval_evals.inducts [split_format (complete)]

inductive_cases eval_cases [cases set]:
 "P \<turnstile> \<langle>new C,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>Cast C e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>Var v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>V:=e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<bullet>F{D},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<bullet>M(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>C\<bullet>\<^sub>sM(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>{V:T;e\<^sub>1},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e\<^sub>1;;e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>INIT C (Cs,b) \<leftarrow> e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>RI (C,e);Cs \<leftarrow> e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 
inductive_cases evals_cases [cases set]:
 "P \<turnstile> \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
 "P \<turnstile> \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
(*>*) 

subsection "Final expressions"

lemma eval_final: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> final e'"
 and evals_final: "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es'"
(*<*)by(induct rule:eval_evals.inducts, simp_all)(*>*)

text\<open> Only used later, in the small to big translation, but is already a
good sanity check: \<close>

lemma eval_finalId:  "final e \<Longrightarrow> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e,s\<rangle>"
(*<*)by (erule finalE) (iprover intro: eval_evals.intros)+(*>*)

lemma eval_final_same: "\<lbrakk> P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>; final e \<rbrakk> \<Longrightarrow> e = e' \<and> s = s'"
(*<*)by(auto elim!: finalE eval_cases)(*>*)

lemma eval_finalsId:
assumes finals: "finals es" shows "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"
(*<*)
  using finals
proof (induct es type: list)
  case Nil show ?case by (rule eval_evals.intros)
next
  case (Cons e es)
  have hyp: "finals es \<Longrightarrow> P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>"
   and finals: "finals (e # es)" by fact+
  show "P \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>e # es,s\<rangle>"
  proof cases
    assume "final e"
    thus ?thesis
    proof (cases rule: finalE)
      fix v assume e: "e = Val v"
      have "P \<turnstile> \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>" by (simp add: eval_finalId)
      moreover from finals e have "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es,s\<rangle>" by(fast intro:hyp)
      ultimately have "P \<turnstile> \<langle>Val v#es,s\<rangle> [\<Rightarrow>] \<langle>Val v#es,s\<rangle>"
        by (rule eval_evals.intros)
      with e show ?thesis by simp
    next
      fix a assume e: "e = Throw a"
      have "P \<turnstile> \<langle>Throw a,s\<rangle> \<Rightarrow> \<langle>Throw a,s\<rangle>" by (simp add: eval_finalId)
      hence "P \<turnstile> \<langle>Throw a#es,s\<rangle> [\<Rightarrow>] \<langle>Throw a#es,s\<rangle>" by (rule eval_evals.intros)
      with e show ?thesis by simp
    qed
  next
    assume "\<not> final e"
    with not_finals_ConsI finals have False by blast
    thus ?thesis ..
  qed
qed
(*>*)

lemma evals_finals_same:
assumes finals: "finals es"
shows "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> es = es' \<and> s = s'"
  using finals
proof (induct es arbitrary: es' type: list)
  case Nil then show ?case using evals_cases(1) by blast
next
  case (Cons e es)
  have IH: "\<And>es'. P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es \<Longrightarrow> es = es' \<and> s = s'"
   and step: "P \<turnstile> \<langle>e # es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle>" and finals: "finals (e # es)" by fact+
  then obtain e' es'' where es': "es' = e'#es''" by (meson Cons.prems(1) evals_cases(2))
  have fe: "final e" using finals not_finals_ConsI by auto
  show ?case
  proof(rule evals_cases(2)[OF step])
    fix v s\<^sub>1 es1 assume es1: "es' = Val v # es1"
      and estep: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>" and esstep: "P \<turnstile> \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>es1,s'\<rangle>"
    then have "e = Val v" using eval_final_same fe by auto
    then have "finals es" using es' not_finals_ConsI2 finals by blast
    then show ?thesis using es' IH estep esstep es1 eval_final_same fe by blast
  next
    fix e' assume es1: "es' = throw e' # es" and estep: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>throw e',s'\<rangle>"
    then have "e = throw e'" using eval_final_same fe by auto
    then show ?thesis using es' estep es1 eval_final_same fe by blast
  qed
qed
(*>*)

subsection "Property preservation"

lemma evals_length: "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> length es = length es'"
 by(induct es arbitrary:es' s s', auto elim: evals_cases)

corollary evals_empty: "P \<turnstile> \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> (es = []) = (es' = [])"
 by(drule evals_length, fastforce)

(****)

theorem eval_hext: "P \<turnstile> \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle> \<Longrightarrow> h \<unlhd> h'"
and evals_hext:  "P \<turnstile> \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle> \<Longrightarrow> h \<unlhd> h'"
(*<*)
proof (induct rule: eval_evals_inducts)
  case New thus ?case
    by(fastforce intro!: hext_new intro:LeastI simp:new_Addr_def
                split:if_split_asm simp del:fun_upd_apply)
next
  case NewInit thus ?case
    by (meson hext_new hext_trans new_Addr_SomeD)
next
  case FAss thus ?case
    by(auto simp:sym[THEN hext_upd_obj] simp del:fun_upd_apply
            elim!: hext_trans)
qed (auto elim!: hext_trans)
(*>*)


lemma eval_lcl_incr: "P \<turnstile> \<langle>e,(h\<^sub>0,l\<^sub>0,sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
 and evals_lcl_incr: "P \<turnstile> \<langle>es,(h\<^sub>0,l\<^sub>0,sh\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>es',(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Longrightarrow> dom l\<^sub>0 \<subseteq> dom l\<^sub>1"
(*<*)
proof (induct rule: eval_evals_inducts)
  case BinOp show ?case by(rule subset_trans)(rule BinOp.hyps)+
next
  case Call thus ?case
    by(simp del: fun_upd_apply)
next
  case Seq show ?case by(rule subset_trans)(rule Seq.hyps)+
next
  case CondT show ?case by(rule subset_trans)(rule CondT.hyps)+
next
  case CondF show ?case by(rule subset_trans)(rule CondF.hyps)+
next
  case WhileT thus ?case by(blast)
next
  case TryCatch thus ?case by(clarsimp simp:dom_def split:if_split_asm) blast
next
  case Cons show ?case by(rule subset_trans)(rule Cons.hyps)+
next
  case Block thus ?case by(auto simp del:fun_upd_apply)
qed auto
(*>*)

lemma
shows init_ri_same_loc: "P \<turnstile> \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>
   \<Longrightarrow> (\<And>C Cs b M a. e = INIT C (Cs,b) \<leftarrow> unit \<or> e = C\<bullet>\<^sub>sM([]) \<or> e = RI (C,Throw a) ; Cs \<leftarrow> unit
          \<or> e = RI (C,C\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> unit
           \<Longrightarrow> l = l')"
  and "P \<turnstile> \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle> \<Longrightarrow> True"
proof(induct rule: eval_evals_inducts)
  case (RInitInitFail e h l sh a')
  then show ?case using eval_final[of _ _ _ "throw a'"]
     by(fastforce dest: eval_final_same[of _ "Throw a"])
next
  case RInitFailFinal then show ?case by(auto dest: eval_final_same)
qed(auto dest: evals_cases eval_cases(17) eval_final_same)

lemma init_same_loc: "P \<turnstile> \<langle>INIT C (Cs,b) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle> \<Longrightarrow> l = l'"
 by(simp add: init_ri_same_loc)

(****)

lemma assumes wf: "wwf_J_prog P"
shows eval_proc_pres': "P \<turnstile> \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>
  \<Longrightarrow> not_init C e \<Longrightarrow> \<exists>sfs. sh C = \<lfloor>(sfs, Processing)\<rfloor> \<Longrightarrow> \<exists>sfs'. sh' C = \<lfloor>(sfs', Processing)\<rfloor>"
  and evals_proc_pres': "P \<turnstile> \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle>
  \<Longrightarrow> not_inits C es \<Longrightarrow> \<exists>sfs. sh C = \<lfloor>(sfs, Processing)\<rfloor> \<Longrightarrow> \<exists>sfs'. sh' C = \<lfloor>(sfs', Processing)\<rfloor>"
(*<*)
proof(induct rule:eval_evals_inducts)
  case Call then show ?case using sees_wwf_nsub_RI[OF wf Call.hyps(6)] nsub_RI_not_init by auto
next
  case (SCallInit ps h l sh vs h\<^sub>1 l\<^sub>1 sh\<^sub>1 C' M Ts T pns body D v' h\<^sub>2 l\<^sub>2 sh\<^sub>2 l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3)
  then show ?case
    using SCallInit sees_wwf_nsub_RI[OF wf SCallInit.hyps(3)] nsub_RI_not_init[of body] by auto
next
  case SCall then show ?case using sees_wwf_nsub_RI[OF wf SCall.hyps(3)] nsub_RI_not_init by auto
next
  case (InitNone sh C1 C' Cs h l e' a a b) then show ?case by(cases "C = C1") auto
next
  case (InitDone sh C sfs C' Cs h l e' a a b) then show ?case by(cases Cs, auto)
next
  case (InitProcessing sh C sfs C' Cs h l e' a a b) then show ?case by(cases Cs, auto)
next
  case (InitError sh C1 sfs Cs h l e' a a b C') then show ?case by(cases "C = C1") auto
next
  case (InitObject sh C1 sfs sh' C' Cs h l e' a a b) then show ?case by(cases "C = C1") auto
next
  case (InitNonObject sh C1 sfs D a b sh' C' Cs h l e' a a b)
  then show ?case by(cases "C = C1") auto
next
  case (RInit e a a b v h' l' sh' C sfs i sh'' C' Cs e\<^sub>1 a a b) then show ?case by(cases Cs, auto)
next
  case (RInitInitFail e h l sh a h' l' sh' C1 sfs i sh'' D Cs e\<^sub>1 h1 l1 sh1)
  then show ?case using eval_final by fastforce
qed(auto)

(************************************************)

subsection\<open>Init Elimination rules\<close>

lemma init_NilE:
assumes init: "P \<turnstile> \<langle>INIT C (Nil,b) \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "e' = unit \<and> s' = s"
proof(rule eval_cases(19)[OF init]) \<comment> \<open> Init \<close> qed(auto dest: eval_final_same)

lemma init_ProcessingE:
assumes shC: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
 and init: "P \<turnstile> \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
shows "e' = unit \<and> s' = (h,l,sh)"
proof(rule eval_cases(19)[OF init]) \<comment> \<open> Init \<close>
  fix sha Ca sfs Cs ha la
  assume "(h, l, sh) = (ha, la, sha)" and "sha Ca = \<lfloor>(sfs, Processing)\<rfloor>"
   and "P \<turnstile> \<langle>INIT C (Cs,True) \<leftarrow> unit,(ha, la, sha)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>" and "[C] = Ca # Cs"
  then show ?thesis using init_NilE by simp
next
  fix sha sfs Cs ha la
  assume "(h, l, sh) = (ha, la, sha)" and "sha Object = \<lfloor>(sfs, Prepared)\<rfloor>"
     and "[C] = Object # Cs"
  then show ?thesis using shC by clarsimp
qed(auto simp: assms)


lemma rinit_throwE:
"P \<turnstile> \<langle>RI (C,throw e) ; Cs \<leftarrow> e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
   \<Longrightarrow> \<exists>a s\<^sub>t. e' = throw a \<and> P \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>throw a,s\<^sub>t\<rangle>"
proof(induct Cs arbitrary: C e s)
  case Nil
  then show ?case
  proof(rule eval_cases(20)) \<comment> \<open> RI \<close>
    fix v h' l' sh' assume "P \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>Val v,(h', l', sh')\<rangle>"
    then show ?case using eval_cases(17) by blast
  qed(auto)
next
  case (Cons C' Cs')
  show ?case using Cons.prems(1)
  proof(rule eval_cases(20)) \<comment> \<open> RI \<close>
    fix v h' l' sh' assume "P \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>Val v,(h', l', sh')\<rangle>"
    then show ?case using eval_cases(17) by blast
  next
    fix a h' l' sh' sfs i D Cs''
    assume e''step: "P \<turnstile> \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>throw a,(h', l', sh')\<rangle>"
       and shC: "sh' C = \<lfloor>(sfs, i)\<rfloor>"
       and riD: "P \<turnstile> \<langle>RI (D,throw a) ; Cs'' \<leftarrow> e\<^sub>0,(h', l', sh'(C \<mapsto> (sfs, Error)))\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
       and "C' # Cs' = D # Cs''"
    then show ?thesis using Cons.hyps eval_final eval_final_same by blast
  qed(simp)
qed

lemma rinit_ValE:
assumes ri: "P \<turnstile> \<langle>RI (C,e) ; Cs \<leftarrow> unit,s\<rangle> \<Rightarrow> \<langle>Val v',s'\<rangle>"
shows "\<exists>v'' s''. P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v'',s''\<rangle>"
proof(rule eval_cases(20)[OF ri]) \<comment> \<open> RI \<close>
  fix a h' l' sh' sfs i D Cs'
  assume "P \<turnstile> \<langle>RI (D,throw a) ; Cs' \<leftarrow> unit,(h', l', sh'(C \<mapsto> (sfs, Error)))\<rangle> \<Rightarrow> \<langle>Val v',s'\<rangle>"
  then show ?thesis using rinit_throwE by blast
qed(auto)

subsection "Some specific evaluations"

lemma lass_val_of_eval:
 "\<lbrakk> lass_val_of e = \<lfloor>a\<rfloor>; P \<turnstile> \<langle>e,(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',(h', l', sh')\<rangle> \<rbrakk>
  \<Longrightarrow> e' = unit \<and> h' = h \<and> l' = l(fst a\<mapsto>snd a) \<and> sh' = sh"
 by(drule lass_val_of_spec, auto elim: eval.cases)

lemma eval_throw_nonVal:
assumes eval: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
shows "val_of e = None"
proof(cases "val_of e")
  case (Some v) show ?thesis using eval by(auto simp: val_of_spec[OF Some] intro: eval.cases)
qed(simp)

lemma eval_throw_nonLAss:
assumes eval: "P \<turnstile> \<langle>e,s\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
shows "lass_val_of e = None"
proof(cases "lass_val_of e")
  case (Some v) show ?thesis using eval by(auto simp: lass_val_of_spec[OF Some] intro: eval.cases)
qed(simp)

end
