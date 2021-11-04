(*  Title:      JinjaDCI/Compiler/J1.thy
    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory Compiler/J1.thy by Tobias Nipkow
*)

chapter \<open> Compilation \label{cha:comp} \<close>

section \<open> An Intermediate Language \<close>

theory J1 imports "../J/BigStep" begin

type_synonym expr\<^sub>1 = "nat exp"
type_synonym J\<^sub>1_prog = "expr\<^sub>1 prog"
type_synonym state\<^sub>1 = "heap \<times> (val list) \<times> sheap"

definition hp\<^sub>1 :: "state\<^sub>1 \<Rightarrow> heap"
where
  "hp\<^sub>1  \<equiv>  fst"
definition lcl\<^sub>1 :: "state\<^sub>1 \<Rightarrow> val list"
where
  "lcl\<^sub>1  \<equiv>  fst \<circ> snd"
definition shp\<^sub>1 :: "state\<^sub>1 \<Rightarrow> sheap"
where
  "shp\<^sub>1  \<equiv>  snd \<circ> snd"

(*<*)
declare hp\<^sub>1_def[simp] lcl\<^sub>1_def[simp] shp\<^sub>1_def[simp]
(*>*)

primrec
  max_vars :: "'a exp \<Rightarrow> nat"
  and max_varss :: "'a exp list \<Rightarrow> nat"
where
  "max_vars(new C) = 0"
| "max_vars(Cast C e) = max_vars e"
| "max_vars(Val v) = 0"
| "max_vars(e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2)"
| "max_vars(Var V) = 0"
| "max_vars(V:=e) = max_vars e"
| "max_vars(e\<bullet>F{D}) = max_vars e"
| "max_vars(C\<bullet>\<^sub>sF{D}) = 0"
| "max_vars(FAss e\<^sub>1 F D e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2)"
| "max_vars(SFAss C F D e\<^sub>2) = max_vars e\<^sub>2"
| "max_vars(e\<bullet>M(es)) = max (max_vars e) (max_varss es)"
| "max_vars(C\<bullet>\<^sub>sM(es)) = max_varss es"
| "max_vars({V:T; e}) = max_vars e + 1"
| "max_vars(e\<^sub>1;;e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2)"
| "max_vars(if (e) e\<^sub>1 else e\<^sub>2) =
   max (max_vars e) (max (max_vars e\<^sub>1) (max_vars e\<^sub>2))"
| "max_vars(while (b) e) = max (max_vars b) (max_vars e)"
| "max_vars(throw e) = max_vars e"
| "max_vars(try e\<^sub>1 catch(C V) e\<^sub>2) = max (max_vars e\<^sub>1) (max_vars e\<^sub>2 + 1)"
| "max_vars(INIT C (Cs,b) \<leftarrow> e) = max_vars e"
| "max_vars(RI(C,e);Cs \<leftarrow> e') = max (max_vars e) (max_vars e')"

| "max_varss [] = 0"
| "max_varss (e#es) = max (max_vars e) (max_varss es)"

inductive
  eval\<^sub>1 :: "J\<^sub>1_prog \<Rightarrow> expr\<^sub>1 \<Rightarrow> state\<^sub>1 \<Rightarrow> expr\<^sub>1 \<Rightarrow> state\<^sub>1 \<Rightarrow> bool"
          ("_ \<turnstile>\<^sub>1 ((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  and evals\<^sub>1 :: "J\<^sub>1_prog \<Rightarrow> expr\<^sub>1 list \<Rightarrow> state\<^sub>1 \<Rightarrow> expr\<^sub>1 list \<Rightarrow> state\<^sub>1 \<Rightarrow> bool"
           ("_ \<turnstile>\<^sub>1 ((1\<langle>_,/_\<rangle>) [\<Rightarrow>]/ (1\<langle>_,/_\<rangle>))" [51,0,0,0,0] 81)
  for P :: J\<^sub>1_prog
where

  New\<^sub>1:
  "\<lbrakk> sh C = Some (sfs, Done); new_Addr h = Some a;
     P \<turnstile> C has_fields FDTs; h' = h(a\<mapsto>blank P C) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>addr a,(h',l,sh)\<rangle>"
| NewFail\<^sub>1:
  "\<lbrakk> sh C = Some (sfs, Done); new_Addr h = None \<rbrakk> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>new C, (h,l,sh)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h,l,sh)\<rangle>"
| NewInit\<^sub>1:
  "\<lbrakk> \<nexists>sfs. sh C = Some (sfs, Done); P \<turnstile>\<^sub>1 \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v',(h',l',sh')\<rangle>;
     new_Addr h' = Some a; P \<turnstile> C has_fields FDTs; h'' = h'(a\<mapsto>blank P C) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>addr a,(h'',l',sh')\<rangle>"
| NewInitOOM\<^sub>1:
  "\<lbrakk> \<nexists>sfs. sh C = Some (sfs, Done); P \<turnstile>\<^sub>1 \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>Val v',(h',l',sh')\<rangle>;
     new_Addr h' = None; is_class P C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>THROW OutOfMemory,(h',l',sh')\<rangle>"
| NewInitThrow\<^sub>1:
  "\<lbrakk> \<nexists>sfs. sh C = Some (sfs, Done); P \<turnstile>\<^sub>1 \<langle>INIT C ([C],False) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>;
     is_class P C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>new C,(h,l,sh)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"

| Cast\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>; h a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>"
| CastNull\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>"
| CastFail\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,l,sh)\<rangle>; h a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW ClassCast,(h,l,sh)\<rangle>"
| CastThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Val\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>Val v,s\<rangle>"

| BinOp\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>2,s\<^sub>2\<rangle>; binop(bop,v\<^sub>1,v\<^sub>2) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>2\<rangle>"
| BinOpThrow\<^sub>1\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle>"
| BinOpThrow\<^sub>2\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>2\<rangle>"

| Var\<^sub>1:
  "\<lbrakk> ls!i = v; i < size ls \<rbrakk> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>Var i,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h,ls,sh)\<rangle>"

| LAss\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,ls,sh)\<rangle>; i < size ls; ls' = ls[i := v] \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>i:= e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h,ls',sh)\<rangle>"
| LAssThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>i:= e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| FAcc\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,ls,sh)\<rangle>; h a = Some(C,fs);
     P \<turnstile> C has F,NonStatic:t in D;
     fs(F,D) = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h,ls,sh)\<rangle>"
| FAccNull\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"
| FAccThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"
| FAccNone\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,ls,sh)\<rangle>; h a = Some(C,fs);
    \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h,ls,sh)\<rangle>"
| FAccStatic\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,(h,ls,sh)\<rangle>; h a = Some(C,fs);
    P \<turnstile> C has F,Static:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h,ls,sh)\<rangle>"

| SFAcc\<^sub>1:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     sh D = Some (sfs,Done);
     sfs F = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D},(h,ls,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h,ls,sh)\<rangle>"
| SFAccInit\<^sub>1:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh D = Some (sfs,Done); P \<turnstile>\<^sub>1 \<langle>INIT D ([D],False) \<leftarrow> unit,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>Val v',(h',ls',sh')\<rangle>;
     sh' D = Some (sfs,i);
     sfs F = Some v \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D},(h,ls,sh)\<rangle> \<Rightarrow> \<langle>Val v,(h',ls',sh')\<rangle>"
| SFAccInitThrow\<^sub>1:
  "\<lbrakk> P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh D = Some (sfs,Done); P \<turnstile>\<^sub>1 \<langle>INIT D ([D],False) \<leftarrow> unit,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D},(h,ls,sh)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
| SFAccNone\<^sub>1:
  "\<lbrakk> \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D},s\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,s\<rangle>"
| SFAccNonStatic\<^sub>1:
  "\<lbrakk> P \<turnstile> C has F,NonStatic:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D},s\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,s\<rangle>"


| FAss\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C has F,NonStatic:t in D;
     fs' = fs((F,D)\<mapsto>v); h\<^sub>2' = h\<^sub>2(a\<mapsto>(C,fs')) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h\<^sub>2',l\<^sub>2,sh\<^sub>2)\<rangle>"
| FAssNull\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>;  P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>2\<rangle> \<rbrakk> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"
| FAssThrow\<^sub>1\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"
| FAssThrow\<^sub>2\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
| FAssNone\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"
| FAssStatic\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C has F,Static:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"

| SFAss\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C has F,Static:t in D;
     sh\<^sub>1 D = Some(sfs,Done); sfs' = sfs(F\<mapsto>v); sh\<^sub>1' = sh\<^sub>1(D\<mapsto>(sfs',Done)) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1')\<rangle>"
| SFAssInit\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done); P \<turnstile>\<^sub>1 \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>Val v',(h',l',sh')\<rangle>;
     sh' D = Some(sfs,i);
     sfs' = sfs(F\<mapsto>v); sh'' = sh'(D\<mapsto>(sfs',i)) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,(h',l',sh'')\<rangle>"
| SFAssInitThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C has F,Static:t in D;
     \<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done); P \<turnstile>\<^sub>1 \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,l\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
| SFAssThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"
| SFAssNone\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
    \<not>(\<exists>b t. P \<turnstile> C has F,b:t in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchFieldError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"
| SFAssNonStatic\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>;
    P \<turnstile> C has F,NonStatic:t in D \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,l\<^sub>2,sh\<^sub>2)\<rangle>"

| CallObjThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"
| CallNull\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>2\<rangle>"
| Call\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>;
    h\<^sub>2 a = Some(C,fs); P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = body in D;
    size vs = size Ts; ls\<^sub>2' = (Addr a) # vs @ replicate (max_vars body) undefined;
    P \<turnstile>\<^sub>1 \<langle>body,(h\<^sub>2,ls\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,ls\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,ls\<^sub>2,sh\<^sub>3)\<rangle>"
| CallParamsThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^sub>2\<rangle>;
     es' = map Val vs @ throw ex # es\<^sub>2 \<rbrakk>
   \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
| CallNone\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile>\<^sub>1 \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); \<not>(\<exists>b Ts T body D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = body in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchMethodError,(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>"
| CallStatic\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle>;  P \<turnstile>\<^sub>1 \<langle>ps,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>;
     h\<^sub>2 a = Some(C,fs); P \<turnstile> C sees M,Static:Ts\<rightarrow>T = body in D \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>"

| SCallParamsThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>es',s\<^sub>2\<rangle>; es' = map Val vs @ throw ex # es\<^sub>2 \<rbrakk>
   \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sM(es),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw ex,s\<^sub>2\<rangle>"
| SCallNone\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle>;
     \<not>(\<exists>b Ts T body D. P \<turnstile> C sees M,b:Ts\<rightarrow>T = body in D) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NoSuchMethodError,s\<^sub>2\<rangle>"
| SCallNonStatic\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,s\<^sub>2\<rangle>;
     P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = body in D \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW IncompatibleClassChangeError,s\<^sub>2\<rangle>"
| SCallInitThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = body in D;
     \<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done); M \<noteq> clinit;
     P \<turnstile>\<^sub>1 \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw a,s'\<rangle>"
| SCallInit\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle>;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = body in D;
     \<nexists>sfs. sh\<^sub>1 D = Some(sfs,Done); M \<noteq> clinit;
     P \<turnstile>\<^sub>1 \<langle>INIT D ([D],False) \<leftarrow> unit,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>Val v',(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>;
     size vs = size Ts; ls\<^sub>2' = vs @ replicate (max_vars body) undefined;
     P \<turnstile>\<^sub>1 \<langle>body,(h\<^sub>2,ls\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,ls\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,ls\<^sub>2,sh\<^sub>3)\<rangle>"
| SCall\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>ps,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>map Val vs,(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>;
     P \<turnstile> C sees M,Static:Ts\<rightarrow>T = body in D;
     sh\<^sub>2 D = Some(sfs,Done) \<or> (M = clinit \<and> sh\<^sub>2 D = \<lfloor>(sfs, Processing)\<rfloor>);
     size vs = size Ts; ls\<^sub>2' = vs @ replicate (max_vars body) undefined;
     P \<turnstile>\<^sub>1 \<langle>body,(h\<^sub>2,ls\<^sub>2',sh\<^sub>2)\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,ls\<^sub>3,sh\<^sub>3)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sM(ps),s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',(h\<^sub>3,ls\<^sub>2,sh\<^sub>3)\<rangle>"

| Block\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>1\<rangle> \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>Block i T e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>1\<rangle>"

| Seq\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2,s\<^sub>2\<rangle>"
| SeqThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>0,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e\<^sub>0;;e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e,s\<^sub>1\<rangle>"

| CondT\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"
| CondF\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,s\<^sub>1\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e',s\<^sub>2\<rangle>"
| CondThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>if (e) e\<^sub>1 else e\<^sub>2, s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| WhileF\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>false,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>unit,s\<^sub>1\<rangle>"
| WhileT\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>2\<rangle>;
    P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>2\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>3,s\<^sub>3\<rangle>"
| WhileCondThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"
| WhileBodyThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>true,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>c,s\<^sub>1\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>\<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>while (e) c,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>2\<rangle>"

| Throw\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>addr a,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,s\<^sub>1\<rangle>"
| ThrowNull\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>null,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>THROW NullPointer,s\<^sub>1\<rangle>"
| ThrowThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>throw e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle>"

| Try\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>try e\<^sub>1 catch(C i) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v\<^sub>1,s\<^sub>1\<rangle>"
| TryCatch\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle>;
    h\<^sub>1 a = Some(D,fs); P \<turnstile> D \<preceq>\<^sup>* C; i < length ls\<^sub>1;
    P \<turnstile>\<^sub>1 \<langle>e\<^sub>2,(h\<^sub>1,ls\<^sub>1[i:=Addr a],sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>try e\<^sub>1 catch(C i) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>e\<^sub>2',(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>"
| TryThrow\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e\<^sub>1,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle>; h\<^sub>1 a = Some(D,fs); \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>try e\<^sub>1 catch(C i) e\<^sub>2,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle>"

| Nil\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>[],s\<rangle>"

| Cons\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>Val v,s\<^sub>1\<rangle>; P \<turnstile>\<^sub>1 \<langle>es,s\<^sub>1\<rangle> [\<Rightarrow>] \<langle>es',s\<^sub>2\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>Val v # es',s\<^sub>2\<rangle>"
| ConsThrow\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<^sub>0\<rangle> \<Rightarrow> \<langle>throw e',s\<^sub>1\<rangle> \<Longrightarrow>
  P \<turnstile>\<^sub>1 \<langle>e#es,s\<^sub>0\<rangle> [\<Rightarrow>] \<langle>throw e' # es, s\<^sub>1\<rangle>"

\<comment> \<open> init rules \<close>

| InitFinal\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>INIT C (Nil,b) \<leftarrow> e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
| InitNone\<^sub>1:
  "\<lbrakk> sh C = None; P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh(C \<mapsto> (sblank P C, Prepared)))\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
| InitDone\<^sub>1:
  "\<lbrakk> sh C = Some(sfs,Done); P \<turnstile>\<^sub>1 \<langle>INIT C' (Cs,True) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
| InitProcessing\<^sub>1:
  "\<lbrakk> sh C = Some(sfs,Processing); P \<turnstile>\<^sub>1 \<langle>INIT C' (Cs,True) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
| InitError\<^sub>1:
  "\<lbrakk> sh C = Some(sfs,Error);
     P \<turnstile>\<^sub>1 \<langle>RI (C, THROW NoClassDefFoundError);Cs \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
| InitObject\<^sub>1:
  "\<lbrakk> sh C = Some(sfs,Prepared);
     C = Object;
     sh' = sh(C \<mapsto> (sfs,Processing));
     P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,True) \<leftarrow> e,(h,l,sh')\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
| InitNonObject\<^sub>1:
  "\<lbrakk> sh C = Some(sfs,Prepared);
     C \<noteq> Object;
     class P C = Some (D,r);
     sh' = sh(C \<mapsto> (sfs,Processing));
     P \<turnstile>\<^sub>1 \<langle>INIT C' (D#C#Cs,False) \<leftarrow> e,(h,l,sh')\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,False) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
| InitRInit\<^sub>1:
  "P \<turnstile>\<^sub>1 \<langle>RI (C,C\<bullet>\<^sub>sclinit([]));Cs \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>INIT C' (C#Cs,True) \<leftarrow> e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"

| RInit\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>Val v, (h',l',sh')\<rangle>;
     sh' C = Some(sfs, i); sh'' = sh'(C \<mapsto> (sfs, Done));
     C' = last(C#Cs);
     P \<turnstile>\<^sub>1 \<langle>INIT C' (Cs,True) \<leftarrow> e', (h',l',sh'')\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>RI (C,e);Cs \<leftarrow> e',s\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle>"
| RInitInitFail\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>throw a, (h',l',sh')\<rangle>;
     sh' C = Some(sfs, i); sh'' = sh'(C \<mapsto> (sfs, Error));
     P \<turnstile>\<^sub>1 \<langle>RI (D,throw a);Cs \<leftarrow> e', (h',l',sh'')\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle> \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>RI (C,e);D#Cs \<leftarrow> e',s\<rangle> \<Rightarrow> \<langle>e\<^sub>1,s\<^sub>1\<rangle>"
| RInitFailFinal\<^sub>1:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>throw a, (h',l',sh')\<rangle>;
     sh' C = Some(sfs, i); sh'' = sh'(C \<mapsto> (sfs, Error)) \<rbrakk>
  \<Longrightarrow> P \<turnstile>\<^sub>1 \<langle>RI (C,e);Nil \<leftarrow> e',s\<rangle> \<Rightarrow> \<langle>throw a, (h',l',sh'')\<rangle>"


(*<*)
lemmas eval\<^sub>1_evals\<^sub>1_induct = eval\<^sub>1_evals\<^sub>1.induct [split_format (complete)]
  and eval\<^sub>1_evals\<^sub>1_inducts = eval\<^sub>1_evals\<^sub>1.inducts [split_format (complete)]
(*>*)


inductive_cases eval\<^sub>1_cases [cases set]:
 "P \<turnstile>\<^sub>1 \<langle>new C,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>Cast C e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>Val v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>Var v,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>V:=e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>e\<bullet>F{D},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1\<bullet>F{D}:=e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sF{D}:=e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>e\<bullet>M(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>C\<bullet>\<^sub>sM(es),s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>{V:T;e\<^sub>1},s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>e\<^sub>1;;e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>if (e) e\<^sub>1 else e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>while (b) c,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>try e\<^sub>1 catch(C V) e\<^sub>2,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>INIT C (Cs,b) \<leftarrow> e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>RI (C,e);Cs \<leftarrow> e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
 
inductive_cases evals\<^sub>1_cases [cases set]:
 "P \<turnstile>\<^sub>1 \<langle>[],s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
 "P \<turnstile>\<^sub>1 \<langle>e#es,s\<rangle> [\<Rightarrow>] \<langle>e',s'\<rangle>"
(*>*) 


lemma eval\<^sub>1_final: "P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> final e'"
 and evals\<^sub>1_final: "P \<turnstile>\<^sub>1 \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> finals es'"
(*<*)by(induct rule:eval\<^sub>1_evals\<^sub>1.inducts, simp_all)(*>*)


lemma eval\<^sub>1_final_same: "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>; final e \<rbrakk> \<Longrightarrow> e = e' \<and> s = s'"
(*<*)
apply(erule finalE)
 using eval\<^sub>1_cases(3) apply blast
by (metis eval\<^sub>1_cases(3,17) exp.distinct(101) exp.inject(3) val.distinct(13))
(*>*)

subsection "Property preservation"

lemma eval\<^sub>1_preserves_len:
  "P \<turnstile>\<^sub>1 \<langle>e\<^sub>0,(h\<^sub>0,ls\<^sub>0,sh\<^sub>0)\<rangle> \<Rightarrow> \<langle>e\<^sub>1,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle> \<Longrightarrow> length ls\<^sub>0 = length ls\<^sub>1"
and evals\<^sub>1_preserves_len:
  "P \<turnstile>\<^sub>1 \<langle>es\<^sub>0,(h\<^sub>0,ls\<^sub>0,sh\<^sub>0)\<rangle> [\<Rightarrow>] \<langle>es\<^sub>1,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle> \<Longrightarrow> length ls\<^sub>0 = length ls\<^sub>1"
(*<*)by (induct rule:eval\<^sub>1_evals\<^sub>1_inducts, simp_all)(*>*)


lemma evals\<^sub>1_preserves_elen:
  "\<And>es' s s'. P \<turnstile>\<^sub>1 \<langle>es,s\<rangle> [\<Rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> length es = length es'"
(*<*)
apply(induct es type:list)
apply (auto elim:evals\<^sub>1.cases)
done
(*>*)


lemma clinit\<^sub>1_loc_pres:
 "P \<turnstile>\<^sub>1 \<langle>C\<^sub>0\<bullet>\<^sub>sclinit([]),(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle> \<Longrightarrow> l = l'"
 by(auto elim!: eval\<^sub>1_cases(12) evals\<^sub>1_cases(1))

lemma
shows init\<^sub>1_ri\<^sub>1_same_loc: "P \<turnstile>\<^sub>1 \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>
   \<Longrightarrow> (\<And>C Cs b M a. e = INIT C (Cs,b) \<leftarrow> unit \<or> e = C\<bullet>\<^sub>sM([]) \<or> e = RI (C,Throw a) ; Cs \<leftarrow> unit
          \<or> e = RI (C,C\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> unit
           \<Longrightarrow> l = l')"
  and "P \<turnstile>\<^sub>1 \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle> \<Longrightarrow> True"
proof(induct rule: eval\<^sub>1_evals\<^sub>1_inducts)
  case (RInitInitFail\<^sub>1 e h l sh a')
  then show ?case using eval\<^sub>1_final[of _ _ _ "throw a'"]
     by(fastforce dest: eval\<^sub>1_final_same[of _ "Throw a"])
next
  case RInitFailFinal\<^sub>1 then show ?case by(auto dest: eval\<^sub>1_final_same)
qed(auto dest: evals\<^sub>1_cases eval\<^sub>1_cases(17) eval\<^sub>1_final_same)

lemma init\<^sub>1_same_loc: "P \<turnstile>\<^sub>1 \<langle>INIT C (Cs,b) \<leftarrow> unit,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle> \<Longrightarrow> l = l'"
 by(simp add: init\<^sub>1_ri\<^sub>1_same_loc)


theorem eval\<^sub>1_hext: "P \<turnstile>\<^sub>1 \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle> \<Longrightarrow> h \<unlhd> h'"
and evals\<^sub>1_hext:  "P \<turnstile>\<^sub>1 \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle> \<Longrightarrow> h \<unlhd> h'"
(*<*)
proof (induct rule: eval\<^sub>1_evals\<^sub>1_inducts)
  case New\<^sub>1 thus ?case
    by(fastforce intro!: hext_new intro:LeastI simp:new_Addr_def
                split:if_split_asm simp del:fun_upd_apply)
next
  case NewInit\<^sub>1 thus ?case
    by (meson hext_new hext_trans new_Addr_SomeD)
next
  case FAss\<^sub>1 thus ?case
    by(auto simp:sym[THEN hext_upd_obj] simp del:fun_upd_apply
            elim!: hext_trans)
qed (auto elim!: hext_trans)
(*>*)

subsection "Initialization"

lemma rinit\<^sub>1_throw:
 "P\<^sub>1 \<turnstile>\<^sub>1 \<langle>RI (D,Throw xa) ; Cs \<leftarrow> e,(h, l, sh)\<rangle> \<Rightarrow> \<langle>e',(h', l', sh')\<rangle>
    \<Longrightarrow> e' = Throw xa"
apply(induct Cs arbitrary: D h l sh h' l' sh')
 apply(drule eval\<^sub>1_cases(20), auto elim: eval\<^sub>1_cases)
apply(drule eval\<^sub>1_cases(20), auto elim: eval\<^sub>1_cases dest: eval\<^sub>1_final_same simp: final_def)
done

lemma rinit\<^sub>1_throwE:
"P \<turnstile>\<^sub>1 \<langle>RI (C,throw e) ; Cs \<leftarrow> e\<^sub>0,s\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>
   \<Longrightarrow> \<exists>a s\<^sub>t. e' = throw a \<and> P \<turnstile>\<^sub>1 \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>throw a,s\<^sub>t\<rangle>"
proof(induct Cs arbitrary: C e s)
  case Nil
  then show ?case
  proof(rule eval\<^sub>1_cases(20)) \<comment> \<open> RI \<close>
    fix v h' l' sh' assume "P \<turnstile>\<^sub>1 \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>Val v,(h', l', sh')\<rangle>"
    then show ?case using eval\<^sub>1_cases(17) by blast
  qed(auto)
next
  case (Cons C' Cs')
  show ?case using Cons.prems(1)
  proof(rule eval\<^sub>1_cases(20)) \<comment> \<open> RI \<close>
    fix v h' l' sh' assume "P \<turnstile>\<^sub>1 \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>Val v,(h', l', sh')\<rangle>"
    then show ?case using eval\<^sub>1_cases(17) by blast
  next
    fix a h' l' sh' sfs i D Cs''
    assume e''step: "P \<turnstile>\<^sub>1 \<langle>throw e,s\<rangle> \<Rightarrow> \<langle>throw a,(h', l', sh')\<rangle>"
       and shC: "sh' C = \<lfloor>(sfs, i)\<rfloor>"
       and riD: "P \<turnstile>\<^sub>1 \<langle>RI (D,throw a) ; Cs'' \<leftarrow> e\<^sub>0,(h', l', sh'(C \<mapsto> (sfs, Error)))\<rangle> \<Rightarrow> \<langle>e',s'\<rangle>"
       and "C' # Cs' = D # Cs''"
    then show ?thesis using Cons.hyps eval\<^sub>1_final eval\<^sub>1_final_same by blast
  qed(simp)
qed

end
