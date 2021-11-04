(*  Title:      JinjaDCI/J/Progress.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/Progress.thy by Tobias Nipkow
*)

section \<open> Progress of Small Step Semantics \<close>

theory Progress
imports WellTypeRT DefAss "../Common/Conform" EConform
begin

lemma final_addrE:
  "\<lbrakk> P,E,h,sh \<turnstile> e : Class C; final e;
    \<And>a. e = addr a \<Longrightarrow> R;
    \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
(*<*)by(auto simp:final_def)(*>*)


lemma finalRefE:
 "\<lbrakk> P,E,h,sh \<turnstile> e : T; is_refT T; final e;
   e = null \<Longrightarrow> R;
   \<And>a C. \<lbrakk> e = addr a; T = Class C \<rbrakk> \<Longrightarrow> R;
   \<And>a. e = Throw a \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
(*<*)by(auto simp:final_def is_refT_def)(*>*)


text\<open> Derivation of new induction scheme for well typing: \<close>

inductive
  WTrt' :: "[J_prog,heap,sheap,env,expr,ty] \<Rightarrow> bool"
  and WTrts' :: "[J_prog,heap,sheap,env,expr list, ty list] \<Rightarrow> bool"
  and WTrt2' :: "[J_prog,env,heap,sheap,expr,ty] \<Rightarrow> bool"
        ("_,_,_,_ \<turnstile> _ :'' _"   [51,51,51,51]50)
  and WTrts2' :: "[J_prog,env,heap,sheap,expr list, ty list] \<Rightarrow> bool"
        ("_,_,_,_ \<turnstile> _ [:''] _" [51,51,51,51]50)
  for P :: J_prog and h :: heap and sh :: sheap
where
  "P,E,h,sh \<turnstile> e :' T \<equiv> WTrt' P h sh E e T"
| "P,E,h,sh \<turnstile> es [:'] Ts \<equiv> WTrts' P h sh E es Ts"

| "is_class P C  \<Longrightarrow>  P,E,h,sh \<turnstile> new C :' Class C"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' T; is_refT T; is_class P C \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> Cast C e :' Class C"
| "typeof\<^bsub>h\<^esub> v = Some T \<Longrightarrow> P,E,h,sh \<turnstile> Val v :' T"
| "E v = Some T  \<Longrightarrow>  P,E,h,sh \<turnstile> Var v :' T"
| "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1 :' T\<^sub>1;  P,E,h,sh \<turnstile> e\<^sub>2 :' T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1 \<guillemotleft>Eq\<guillemotright> e\<^sub>2 :' Boolean"
| "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1 :' Integer;  P,E,h,sh \<turnstile> e\<^sub>2 :' Integer \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1 \<guillemotleft>Add\<guillemotright> e\<^sub>2 :' Integer"
| "\<lbrakk> P,E,h,sh \<turnstile> Var V :' T;  P,E,h,sh \<turnstile> e :' T';  P \<turnstile> T' \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> V:=e :' Void"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' Class C; P \<turnstile> C has F,NonStatic:T in D \<rbrakk> \<Longrightarrow> P,E,h,sh \<turnstile> e\<bullet>F{D} :' T"
| "P,E,h,sh \<turnstile> e :' NT \<Longrightarrow> P,E,h,sh \<turnstile> e\<bullet>F{D} :' T"
| "\<lbrakk> P \<turnstile> C has F,Static:T in D \<rbrakk> \<Longrightarrow> P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D} :' T"
| "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1 :' Class C;  P \<turnstile> C has F,NonStatic:T in D;
    P,E,h,sh \<turnstile> e\<^sub>2 :' T\<^sub>2;  P \<turnstile> T\<^sub>2 \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 :' Void"
| "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1:'NT; P,E,h,sh \<turnstile> e\<^sub>2 :' T\<^sub>2 \<rbrakk> \<Longrightarrow> P,E,h,sh \<turnstile> e\<^sub>1\<bullet>F{D}:=e\<^sub>2 :' Void"
| "\<lbrakk> P \<turnstile> C has F,Static:T in D;
    P,E,h,sh \<turnstile> e\<^sub>2 :' T\<^sub>2;  P \<turnstile> T\<^sub>2 \<le> T \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D}:=e\<^sub>2 :' Void"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' Class C; P \<turnstile> C sees M,NonStatic:Ts \<rightarrow> T = (pns,body) in D;
    P,E,h,sh \<turnstile> es [:'] Ts'; P \<turnstile> Ts' [\<le>] Ts \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> e\<bullet>M(es) :' T"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' NT; P,E,h,sh \<turnstile> es [:'] Ts \<rbrakk> \<Longrightarrow> P,E,h,sh \<turnstile> e\<bullet>M(es) :' T"
| "\<lbrakk> P \<turnstile> C sees M,Static:Ts \<rightarrow> T = (pns,body) in D;
    P,E,h,sh \<turnstile> es [:'] Ts'; P \<turnstile> Ts' [\<le>] Ts;
    M = clinit \<longrightarrow> sh D = \<lfloor>(sfs,Processing)\<rfloor> \<and> es = map Val vs \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> C\<bullet>\<^sub>sM(es) :' T"
| "P,E,h,sh \<turnstile> [] [:'] []"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' T;  P,E,h,sh \<turnstile> es [:'] Ts \<rbrakk> \<Longrightarrow>  P,E,h,sh \<turnstile> e#es [:'] T#Ts"
| "\<lbrakk> typeof\<^bsub>h\<^esub> v = Some T\<^sub>1; P \<turnstile> T\<^sub>1 \<le> T; P,E(V\<mapsto>T),h,sh \<turnstile> e\<^sub>2 :' T\<^sub>2 \<rbrakk>
  \<Longrightarrow>  P,E,h,sh \<turnstile> {V:T := Val v; e\<^sub>2} :' T\<^sub>2"
| "\<lbrakk> P,E(V\<mapsto>T),h,sh \<turnstile> e :' T'; \<not> assigned V e \<rbrakk> \<Longrightarrow>  P,E,h,sh \<turnstile> {V:T; e} :' T'"
| "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1:' T\<^sub>1;  P,E,h,sh \<turnstile> e\<^sub>2:'T\<^sub>2 \<rbrakk>  \<Longrightarrow>  P,E,h,sh \<turnstile> e\<^sub>1;;e\<^sub>2 :' T\<^sub>2"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' Boolean;  P,E,h,sh \<turnstile> e\<^sub>1:' T\<^sub>1;  P,E,h,sh \<turnstile> e\<^sub>2:' T\<^sub>2;
    P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<or> P \<turnstile> T\<^sub>2 \<le> T\<^sub>1;
    P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<longrightarrow> T = T\<^sub>2; P \<turnstile> T\<^sub>2 \<le> T\<^sub>1 \<longrightarrow> T = T\<^sub>1 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> if (e) e\<^sub>1 else e\<^sub>2 :' T"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' Boolean;  P,E,h,sh \<turnstile> c:' T \<rbrakk>
  \<Longrightarrow>  P,E,h,sh \<turnstile> while(e) c :' Void"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' T\<^sub>r; is_refT T\<^sub>r \<rbrakk>  \<Longrightarrow>  P,E,h,sh \<turnstile> throw e :' T"
| "\<lbrakk> P,E,h,sh \<turnstile> e\<^sub>1 :' T\<^sub>1;  P,E(V \<mapsto> Class C),h,sh \<turnstile> e\<^sub>2 :' T\<^sub>2; P \<turnstile> T\<^sub>1 \<le> T\<^sub>2 \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> try e\<^sub>1 catch(C V) e\<^sub>2 :' T\<^sub>2"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' T; \<forall>C' \<in> set (C#Cs). is_class P C'; \<not>sub_RI e;
     \<forall>C' \<in> set (tl Cs). \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>;
     b \<longrightarrow> (\<forall>C' \<in> set Cs. \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>);
     distinct Cs; supercls_lst P Cs \<rbrakk> \<Longrightarrow> P,E,h,sh \<turnstile> INIT C (Cs, b) \<leftarrow> e :' T"
| "\<lbrakk> P,E,h,sh \<turnstile> e :' T; P,E,h,sh \<turnstile> e' :' T'; \<forall>C' \<in> set (C#Cs). is_class P C'; \<not>sub_RI e';
     \<forall>C' \<in> set (C#Cs). not_init C' e;
     \<forall>C' \<in> set Cs. \<exists>sfs. sh C' = \<lfloor>(sfs,Processing)\<rfloor>;
     \<exists>sfs. sh C = \<lfloor>(sfs, Processing)\<rfloor> \<or> (sh C = \<lfloor>(sfs, Error)\<rfloor> \<and> e = THROW NoClassDefFoundError);
     distinct (C#Cs); supercls_lst P (C#Cs) \<rbrakk>
  \<Longrightarrow> P,E,h,sh \<turnstile> RI(C, e);Cs \<leftarrow> e' :' T'"

(*<*)
lemmas WTrt'_induct = WTrt'_WTrts'.induct [split_format (complete)]
  and WTrt'_inducts = WTrt'_WTrts'.inducts [split_format (complete)]

inductive_cases WTrt'_elim_cases[elim!]:
  "P,E,h,sh \<turnstile> V :=e :' T"
(*>*)

lemma [iff]: "P,E,h,sh \<turnstile> e\<^sub>1;;e\<^sub>2 :' T\<^sub>2 = (\<exists>T\<^sub>1. P,E,h,sh \<turnstile> e\<^sub>1:' T\<^sub>1 \<and> P,E,h,sh \<turnstile> e\<^sub>2:' T\<^sub>2)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done
(*>*)

lemma [iff]: "P,E,h,sh \<turnstile> Val v :' T = (typeof\<^bsub>h\<^esub> v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done
(*>*)

lemma [iff]: "P,E,h,sh \<turnstile> Var v :' T = (E v = Some T)"
(*<*)
apply(rule iffI)
apply (auto elim: WTrt'.cases intro!:WTrt'_WTrts'.intros)
done
(*>*)


lemma wt_wt': "P,E,h,sh \<turnstile> e : T \<Longrightarrow> P,E,h,sh \<turnstile> e :' T"
and wts_wts': "P,E,h,sh \<turnstile> es [:] Ts \<Longrightarrow> P,E,h,sh \<turnstile> es [:'] Ts"
(*<*)
apply (induct rule:WTrt_inducts)
prefer 17
apply(case_tac "assigned V e")
apply(clarsimp simp add:fun_upd_same assigned_def simp del:fun_upd_apply)
apply(erule (2) WTrt'_WTrts'.intros)
apply(erule (1) WTrt'_WTrts'.intros)
apply(blast intro:WTrt'_WTrts'.intros)+
done
(*>*)


lemma wt'_wt: "P,E,h,sh \<turnstile> e :' T \<Longrightarrow> P,E,h,sh \<turnstile> e : T"
and wts'_wts: "P,E,h,sh \<turnstile> es [:'] Ts \<Longrightarrow> P,E,h,sh \<turnstile> es [:] Ts"
(*<*)
apply (induct rule:WTrt'_inducts)
prefer 19
apply(rule WTrt_WTrts.intros)
apply(rule WTrt_WTrts.intros)
apply(rule WTrt_WTrts.intros)
apply simp
apply(erule (2) WTrt_WTrts.intros)
apply(blast intro:WTrt_WTrts.intros)+
done
(*>*)


corollary wt'_iff_wt: "(P,E,h,sh \<turnstile> e :' T) = (P,E,h,sh \<turnstile> e : T)"
(*<*)by(blast intro:wt_wt' wt'_wt)(*>*)


corollary wts'_iff_wts: "(P,E,h,sh \<turnstile> es [:'] Ts) = (P,E,h,sh \<turnstile> es [:] Ts)"
(*<*)by(blast intro:wts_wts' wts'_wts)(*>*)

(*<*)
lemmas WTrt_inducts2 = WTrt'_inducts [unfolded wt'_iff_wt wts'_iff_wts,
 case_names WTrtNew WTrtCast WTrtVal WTrtVar WTrtBinOpEq WTrtBinOpAdd WTrtLAss
 WTrtFAcc WTrtFAccNT WTrtSFAcc WTrtFAss WTrtFAssNT WTrtSFAss WTrtCall WTrtCallNT WTrtSCall
 WTrtNil WTrtCons WTrtInitBlock WTrtBlock WTrtSeq WTrtCond WTrtWhile WTrtThrow WTrtTry
 WTrtInit WTrtRI, consumes 1]
(*>*)

theorem assumes wf: "wwf_J_prog P" and hconf: "P \<turnstile> h \<surd>" and shconf: "P,h \<turnstile>\<^sub>s sh \<surd>"
shows progress: "P,E,h,sh \<turnstile> e : T \<Longrightarrow>
 (\<And>l. \<lbrakk> \<D> e \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (e,b) \<surd>; \<not> final e \<rbrakk> \<Longrightarrow> \<exists>e' s' b'. P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>)"
and "P,E,h,sh \<turnstile> es [:] Ts \<Longrightarrow>
 (\<And>l. \<lbrakk> \<D>s es \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (es,b) \<surd>; \<not> finals es \<rbrakk> \<Longrightarrow> \<exists>es' s' b'. P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>)"
(*<*)
proof (induct rule:WTrt_inducts2)
  case (WTrtNew C) show ?case
  proof (cases b)
    case True then show ?thesis
    proof cases
      assume "\<exists>a. h a = None"
      with assms WTrtNew True show ?thesis
        by (fastforce del:exE intro!:RedNew simp add:new_Addr_def
                     elim!:wf_Fields_Ex[THEN exE])
    next
      assume "\<not>(\<exists>a. h a = None)"
      with assms WTrtNew True show ?thesis
        by(fastforce intro:RedNewFail simp:new_Addr_def)
    qed
  next
    case False then show ?thesis
    proof cases
      assume "\<exists>sfs. sh C = Some (sfs, Done)"
      with assms WTrtNew False show ?thesis
        by(fastforce intro:NewInitDoneRed simp:new_Addr_def)
    next
      assume "\<nexists>sfs. sh C = Some (sfs, Done)"
      with assms WTrtNew False show ?thesis
        by(fastforce intro:NewInitRed simp:new_Addr_def)
    qed
  qed
next
  case (WTrtCast E e T C)
  have wte: "P,E,h,sh \<turnstile> e : T" and ref: "is_refT T"
   and IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (e,b) \<surd>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' b'. P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
   and D: "\<D> (Cast C e) \<lfloor>dom l\<rfloor>"
   and castconf: "P,sh \<turnstile>\<^sub>b (Cast C e,b) \<surd>" by fact+
  from D have De: "\<D> e \<lfloor>dom l\<rfloor>" by auto
  have bconf: "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using castconf bconf_Cast by fast
  show ?case
  proof cases
    assume "final e"
    with wte ref show ?thesis
    proof (rule finalRefE)
      assume "e = null" thus ?case by(fastforce intro:RedCastNull)
    next
      fix D a assume A: "T = Class D" "e = addr a"
      show ?thesis
      proof cases
        assume "P \<turnstile> D \<preceq>\<^sup>* C"
        thus ?thesis using A wte by(fastforce intro:RedCast)
      next
        assume "\<not> P \<turnstile> D \<preceq>\<^sup>* C"
        thus ?thesis using A wte by(fastforce elim!:RedCastFail)
      qed
    next
      fix a assume "e = Throw a"
      thus ?thesis by(blast intro!:red_reds.CastThrow)
    qed
  next
    assume nf: "\<not> final e"
    from IH[OF De bconf nf] show ?thesis by (blast intro:CastRed)
  qed
next
  case WTrtVal thus ?case by(simp add:final_def)
next
  case WTrtVar thus ?case by(fastforce intro:RedVar simp:hyper_isin_def)
next
  case (WTrtBinOpEq E e1 T1 e2 T2) show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v1 assume eV[simp]: "e1 = Val v1"
      show ?thesis
      proof cases
        assume "final e2"
        thus ?thesis
        proof (rule finalE)
          fix v2 assume "e2 = Val v2"
          thus ?thesis using WTrtBinOpEq by(fastforce intro:RedBinOp)
        next
          fix a assume "e2 = Throw a"
          thus ?thesis using eV by(blast intro:red_reds.BinOpThrow2)
        qed
      next
        assume nf: "\<not> final e2"
        then have "P,sh \<turnstile>\<^sub>b (e2,b) \<surd>" using WTrtBinOpEq.prems(2) by(simp add:bconf_BinOp)
        with WTrtBinOpEq nf show ?thesis
          by simp (fast intro!:BinOpRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by (fast intro:red_reds.BinOpThrow1)
    qed
  next
    assume nf: "\<not> final e1"
    then have e1: "val_of e1 = None" proof(cases e1)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e1,b) \<surd>" using WTrtBinOpEq.prems(2) by(simp add:bconf_BinOp)
    with WTrtBinOpEq nf e1 show ?thesis
      by simp (fast intro:BinOpRed1)
  qed
next
  case (WTrtBinOpAdd E e1 e2) show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v1 assume eV[simp]: "e1 = Val v1"
      show ?thesis
      proof cases
        assume "final e2"
        thus ?thesis
        proof (rule finalE)
          fix v2 assume eV2:"e2 = Val v2"
          then obtain i1 i2 where "v1 = Intg i1 \<and> v2 = Intg i2" using WTrtBinOpAdd by clarsimp
          thus ?thesis using WTrtBinOpAdd eV eV2 by(fastforce intro:RedBinOp)
        next
          fix a assume "e2 = Throw a"
          thus ?thesis using eV by(blast intro:red_reds.BinOpThrow2)
        qed
      next
        assume nf:"\<not> final e2"
        then have "P,sh \<turnstile>\<^sub>b (e2,b) \<surd>" using WTrtBinOpAdd.prems(2) by(simp add:bconf_BinOp)
        with WTrtBinOpAdd nf show ?thesis
          by simp (fast intro!:BinOpRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by(fast intro:red_reds.BinOpThrow1)
    qed
  next
    assume nf: "\<not> final e1"
    then have e1: "val_of e1 = None" proof(cases e1)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e1,b) \<surd>" using WTrtBinOpAdd.prems(2) by(simp add:bconf_BinOp)
    with WTrtBinOpAdd nf e1 show ?thesis
      by simp (fast intro:BinOpRed1)
  qed
next
  case (WTrtLAss E V T e T')
  then have bconf: "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using bconf_LAss by fast
  show ?case
  proof cases
    assume "final e" with WTrtLAss show ?thesis
      by(fastforce simp:final_def intro: red_reds.RedLAss red_reds.LAssThrow)
  next
    assume "\<not> final e" with WTrtLAss bconf show ?thesis
      by simp (fast intro:LAssRed)
  qed
next
  case (WTrtFAcc E e C F T D)
  then have bconf: "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using bconf_FAcc by fast
  have wte: "P,E,h,sh \<turnstile> e : Class C"
   and field: "P \<turnstile> C has F,NonStatic:T in D" by fact+
  show ?case
  proof cases
    assume "final e"
    with wte show ?thesis
    proof (rule final_addrE)
      fix a assume e: "e = addr a"
      with wte obtain fs where hp: "h a = Some(C,fs)" by auto
      with hconf have "P,h \<turnstile> (C,fs) \<surd>" using hconf_def by fastforce
      then obtain v where "fs(F,D) = Some v" using field
        by(fastforce dest:has_fields_fun simp:oconf_def has_field_def)
      with hp e show ?thesis by (meson field red_reds.RedFAcc)
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fastforce intro:red_reds.FAccThrow)
    qed
  next
    assume "\<not> final e" with WTrtFAcc bconf show ?thesis
      by(fastforce intro!:FAccRed)
  qed
next
  case (WTrtFAccNT E e F D T)
  then have bconf: "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using bconf_FAcc by fast
  show ?case
  proof cases
    assume "final e"  \<comment> \<open>@{term e} is @{term null} or @{term throw}\<close>
    with WTrtFAccNT show ?thesis
      by(fastforce simp:final_def intro: red_reds.RedFAccNull red_reds.FAccThrow)
  next
    assume "\<not> final e" \<comment> \<open>@{term e} reduces by IH\<close>
    with WTrtFAccNT bconf show ?thesis by simp (fast intro:FAccRed)
  qed
next
case (WTrtSFAcc C F T D E) then show ?case
  proof (cases b)
    case True
    then obtain sfs i where shD: "sh D = \<lfloor>(sfs,i)\<rfloor>"
      using bconf_def[of P sh "C\<bullet>\<^sub>sF{D}" b] WTrtSFAcc.prems(2) initPD_def by auto
    with shconf have "P,h,D \<turnstile>\<^sub>s sfs \<surd>" using shconf_def[of P h sh] by auto
    then obtain v where sfsF: "sfs F = Some v" using WTrtSFAcc.hyps
      by(unfold soconf_def) (auto dest:has_field_idemp)
    then show ?thesis using WTrtSFAcc.hyps shD sfsF True
      by(fastforce elim:RedSFAcc)
  next
    case False
    with assms WTrtSFAcc show ?thesis
      by(metis (full_types) SFAccInitDoneRed SFAccInitRed)
  qed
next
  case (WTrtFAss E e1 C F T D e2 T2)
  have wte1: "P,E,h,sh \<turnstile> e1 : Class C" and field: "P \<turnstile> C has F,NonStatic:T in D" by fact+
  show ?case
  proof cases
    assume "final e1"
    with wte1 show ?thesis
    proof (rule final_addrE)
      fix a assume e1: "e1 = addr a"
      show ?thesis
      proof cases
        assume "final e2"
        thus ?thesis
        proof (rule finalE)
          fix v assume "e2 = Val v"
          thus ?thesis using e1 wte1 by(fastforce intro: RedFAss[OF field])
        next
          fix a assume "e2 = Throw a"
          thus ?thesis using e1 by(fastforce intro:red_reds.FAssThrow2)
        qed
      next
        assume nf: "\<not> final e2"
        then have "P,sh \<turnstile>\<^sub>b (e2,b) \<surd>" using WTrtFAss.prems(2) e1 by(simp add:bconf_FAss)
        with WTrtFAss e1 nf show ?thesis
          by simp (fast intro!:FAssRed2)
      qed
    next
      fix a assume "e1 = Throw a"
      thus ?thesis by(fastforce intro:red_reds.FAssThrow1)
    qed
  next
    assume nf: "\<not> final e1"
    then have e1: "val_of e1 = None" proof(cases e1)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e1,b) \<surd>" using WTrtFAss.prems(2) by(simp add:bconf_FAss)
    with WTrtFAss nf e1 show ?thesis
      by simp (blast intro!:FAssRed1)
  qed
next
  case (WTrtFAssNT E e\<^sub>1 e\<^sub>2 T\<^sub>2 F D)
  show ?case
  proof cases
    assume e1: "final e\<^sub>1"  \<comment> \<open>@{term e\<^sub>1} is @{term null} or @{term throw}\<close>
    show ?thesis
    proof cases
      assume "final e\<^sub>2"  \<comment> \<open>@{term e\<^sub>2} is @{term Val} or @{term throw}\<close>
      with WTrtFAssNT e1 show ?thesis
        by(fastforce simp:final_def
                    intro: red_reds.RedFAssNull red_reds.FAssThrow1 red_reds.FAssThrow2)
    next
      assume nf: "\<not> final e\<^sub>2" \<comment> \<open>@{term e\<^sub>2} reduces by IH\<close>
      show ?thesis
      proof (rule finalE[OF e1])
        fix v assume ev: "e\<^sub>1 = Val v"
        then have "P,sh \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using WTrtFAssNT.prems(2) nf by(simp add:bconf_FAss)
        with WTrtFAssNT ev nf show ?thesis by auto (meson red_reds.FAssRed2)
      next
        fix a assume et: "e\<^sub>1 = Throw a"
        then have "P,sh \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using WTrtFAssNT.prems(2) nf by(simp add:bconf_FAss)
        with WTrtFAssNT et nf show ?thesis by(fastforce intro: red_reds.FAssThrow1)
      qed
    qed
  next
    assume nf: "\<not> final e\<^sub>1" \<comment> \<open>@{term e\<^sub>1} reduces by IH\<close>
    then have e1: "val_of e\<^sub>1 = None" proof(cases e\<^sub>1)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e\<^sub>1,b) \<surd>" using WTrtFAssNT.prems(2) by(simp add:bconf_FAss)
    with WTrtFAssNT nf e1 show ?thesis
      by simp (blast intro!:FAssRed1)
  qed
next
  case (WTrtSFAss C F T D E e2 T\<^sub>2)
  have field: "P \<turnstile> C has F,Static:T in D" by fact+
  show ?case
  proof cases
    assume "final e2"
    thus ?thesis
    proof (rule finalE)
      fix v assume ev: "e2 = Val v"
      then show ?case
      proof (cases b)
        case True
        then obtain sfs i where shD: "sh D = \<lfloor>(sfs,i)\<rfloor>"
          using bconf_def[of P _ "C\<bullet>\<^sub>sF{D} := e2"] WTrtSFAss.prems(2) initPD_def ev by auto
        with shconf have "P,h,D \<turnstile>\<^sub>s sfs \<surd>" using shconf_def[of P] by auto
        then obtain v where sfsF: "sfs F = Some v" using field
          by(unfold soconf_def) (auto dest:has_field_idemp)
        then show ?thesis using WTrtSFAss.hyps shD sfsF True ev
          by(fastforce elim:RedSFAss)
      next
        case False
        with assms WTrtSFAss ev show ?thesis
          by(metis (full_types) SFAssInitDoneRed SFAssInitRed)
      qed
    next
      fix a assume "e2 = Throw a"
      thus ?thesis by(fastforce intro:red_reds.SFAssThrow)
    qed
  next
    assume nf: "\<not> final e2"
    then have "val_of e2 = None" using final_def val_of_spec by fastforce
    then have "P,sh \<turnstile>\<^sub>b (e2,b) \<surd>" using WTrtSFAss.prems(2) by(simp add:bconf_SFAss)
    with WTrtSFAss nf show ?thesis
      by simp (fast intro!:SFAssRed)
  qed
next
  case (WTrtCall E e C M Ts T pns body D es Ts')
  have wte: "P,E,h,sh \<turnstile> e : Class C"
   and "method": "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D"
   and wtes: "P,E,h,sh \<turnstile> es [:] Ts'"and sub: "P \<turnstile> Ts' [\<le>] Ts"
   and IHes: "\<And>l.
             \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (es,b) \<surd>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s' b'. P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>"
   and D: "\<D> (e\<bullet>M(es)) \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e"
    with wte show ?thesis
    proof (rule final_addrE)
      fix a assume e_addr: "e = addr a"
      show ?thesis
      proof cases
        assume es: "\<exists>vs. es = map Val vs"
        from wte e_addr obtain fs where ha: "h a = Some(C,fs)" by auto
        show ?thesis
          using e_addr ha "method" WTrts_same_length[OF wtes] sub es sees_wf_mdecl[OF wf "method"]
          by(fastforce intro!: RedCall simp:list_all2_iff wf_mdecl_def)
      next
        assume "\<not>(\<exists>vs. es = map Val vs)"
        hence not_all_Val: "\<not>(\<forall>e \<in> set es. \<exists>v. e = Val v)"
          by(simp add:ex_map_conv)
        let ?ves = "takeWhile (\<lambda>e. \<exists>v. e = Val v) es"
        let ?rest = "dropWhile (\<lambda>e. \<exists>v. e = Val v) es"
        let ?ex = "hd ?rest" let ?rst = "tl ?rest"
        from not_all_Val have nonempty: "?rest \<noteq> []" by auto
        hence es: "es = ?ves @ ?ex # ?rst" by simp
        have "\<forall>e \<in> set ?ves. \<exists>v. e = Val v" by(fastforce dest:set_takeWhileD)
        then obtain vs where ves: "?ves = map Val vs"
          using ex_map_conv by blast
        show ?thesis
        proof cases
          assume "final ?ex"
          moreover from nonempty have "\<not>(\<exists>v. ?ex = Val v)"
            by(auto simp:neq_Nil_conv simp del:dropWhile_eq_Nil_conv)
              (simp add:dropWhile_eq_Cons_conv)
          ultimately obtain b where ex_Throw: "?ex = Throw b"
            by(fast elim!:finalE)
          show ?thesis using e_addr es ex_Throw ves
            by(fastforce intro:CallThrowParams)
        next
          assume not_fin: "\<not> final ?ex"
          have "finals es = finals(?ves @ ?ex # ?rst)" using es
            by(rule arg_cong)
          also have "\<dots> = finals(?ex # ?rst)" using ves by simp
          finally have "finals es = finals(?ex # ?rst)" .
          hence fes: "\<not> finals es" using not_finals_ConsI[OF not_fin] by blast
          have "P,sh \<turnstile>\<^sub>b (es,b) \<surd>" using bconf_Call WTrtCall.prems(2)
            by (metis e_addr option.simps(5) val_of.simps(1))
          thus ?thesis using fes e_addr D IHes by(fastforce intro!:CallParams)
        qed
      qed
    next
      fix a assume "e = Throw a"
      with WTrtCall.prems show ?thesis by(fast intro!:CallThrowObj)
    qed
  next
    assume nf: "\<not> final e"
    then have e1: "val_of e = None" proof(cases e)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using WTrtCall.prems(2) by(simp add:bconf_Call)
    with WTrtCall nf e1 show ?thesis by simp (blast intro!:CallObj)
  qed
next
  case (WTrtCallNT E e es Ts M T) show ?case
  proof cases
    assume "final e"
    moreover
    { fix v assume e: "e = Val v"
      hence "e = null" using WTrtCallNT by simp
      have ?case
      proof cases
        assume "finals es"
        moreover
        { fix vs assume "es = map Val vs"
          with WTrtCallNT e have ?thesis by(fastforce intro: RedCallNull) }
        moreover
        { fix vs a es' assume "es = map Val vs @ Throw a # es'"
          with WTrtCallNT e have ?thesis by(fastforce intro: CallThrowParams) }
        ultimately show ?thesis by(fastforce simp:finals_def)
      next
        assume nf: "\<not> finals es" \<comment> \<open>@{term es} reduces by IH\<close>
        have "P,sh \<turnstile>\<^sub>b (es,b) \<surd>" using WTrtCallNT.prems(2) e by (simp add: bconf_Call)
        with WTrtCallNT e nf show ?thesis by(fastforce intro: CallParams)
      qed
    }
    moreover
    { fix a assume "e = Throw a"
      with WTrtCallNT have ?case by(fastforce intro: CallThrowObj) }
    ultimately show ?thesis by(fastforce simp:final_def)
  next
    assume nf: "\<not> final e" \<comment> \<open>@{term e} reduces by IH\<close>
    then have "val_of e = None" proof(cases e)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using WTrtCallNT.prems(2) by(simp add:bconf_Call)
    with WTrtCallNT nf show ?thesis by (fastforce intro:CallObj)
  qed
next
  case (WTrtSCall C M Ts T pns body D E es Ts' sfs vs)
  have "method": "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D"
   and wtes: "P,E,h,sh \<turnstile> es [:] Ts'"and sub: "P \<turnstile> Ts' [\<le>] Ts"
   and IHes: "\<And>l.
             \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (es,b) \<surd>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s' b'. P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>"
   and clinit: "M = clinit \<longrightarrow> sh D = \<lfloor>(sfs, Processing)\<rfloor> \<and> es = map Val vs"
   and D: "\<D> (C\<bullet>\<^sub>sM(es)) \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume es: "\<exists>vs. es = map Val vs"
    show ?thesis
    proof (cases b)
      case True
      then show ?thesis
      using "method" WTrts_same_length[OF wtes] sub es sees_wf_mdecl[OF wf "method"] True
      by(fastforce intro!: RedSCall simp:list_all2_iff wf_mdecl_def)
    next
      case False
      show ?thesis
      using "method" clinit WTrts_same_length[OF wtes] sub es False
        by (metis (full_types) red_reds.SCallInitDoneRed red_reds.SCallInitRed)
    qed
  next
    assume nmap: "\<not>(\<exists>vs. es = map Val vs)"
    hence not_all_Val: "\<not>(\<forall>e \<in> set es. \<exists>v. e = Val v)"
      by(simp add:ex_map_conv)
    let ?ves = "takeWhile (\<lambda>e. \<exists>v. e = Val v) es"
    let ?rest = "dropWhile (\<lambda>e. \<exists>v. e = Val v) es"
    let ?ex = "hd ?rest" let ?rst = "tl ?rest"
    from not_all_Val have nonempty: "?rest \<noteq> []" by auto
    hence es: "es = ?ves @ ?ex # ?rst" by simp
    have "\<forall>e \<in> set ?ves. \<exists>v. e = Val v" by(fastforce dest:set_takeWhileD)
    then obtain vs where ves: "?ves = map Val vs"
      using ex_map_conv by blast
    show ?thesis
    proof cases
      assume "final ?ex"
      moreover from nonempty have "\<not>(\<exists>v. ?ex = Val v)"
        by(auto simp:neq_Nil_conv simp del:dropWhile_eq_Nil_conv)
          (simp add:dropWhile_eq_Cons_conv)
      ultimately obtain b where ex_Throw: "?ex = Throw b"
        by(fast elim!:finalE)
      show ?thesis using es ex_Throw ves
        by(fastforce intro:SCallThrowParams)
    next
      assume not_fin: "\<not> final ?ex"
      have "finals es = finals(?ves @ ?ex # ?rst)" using es
        by(rule arg_cong)
      also have "\<dots> = finals(?ex # ?rst)" using ves by simp
      finally have "finals es = finals(?ex # ?rst)" .
      hence fes: "\<not> finals es" using not_finals_ConsI[OF not_fin] by blast
      have "P,sh \<turnstile>\<^sub>b (es,b) \<surd>"
        by (meson WTrtSCall.prems(2) nmap bconf_SCall map_vals_of_spec not_None_eq)
      thus ?thesis using fes D IHes by(fastforce intro!:SCallParams)
    qed
  qed
next
  case WTrtNil thus ?case by simp
next
  case (WTrtCons E e T es Ts)
  have IHe: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (e,b) \<surd>; \<not> final e\<rbrakk>
                \<Longrightarrow> \<exists>e' s' b'. P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
   and IHes: "\<And>l. \<lbrakk>\<D>s es \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (es,b) \<surd>; \<not> finals es\<rbrakk>
             \<Longrightarrow> \<exists>es' s' b'. P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>"
   and D: "\<D>s (e#es) \<lfloor>dom l\<rfloor>" and not_fins: "\<not> finals(e # es)" by fact+
  have De: "\<D> e \<lfloor>dom l\<rfloor>" and Des: "\<D>s es (\<lfloor>dom l\<rfloor> \<squnion> \<A> e)"
    using D by auto
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume e: "e = Val v"
      hence Des': "\<D>s es \<lfloor>dom l\<rfloor>" using De Des by auto
      have bconfs: "P,sh \<turnstile>\<^sub>b (es,b) \<surd>" using WTrtCons.prems(2) e by(simp add: bconf_Cons)
      have not_fins_tl: "\<not> finals es" using not_fins e by simp
      show ?thesis using e IHes[OF Des' bconfs not_fins_tl]
        by (blast intro!:ListRed2)
    next
      fix a assume "e = Throw a"
      hence False using not_fins by simp
      thus ?thesis ..
    qed
  next
    assume nf:"\<not> final e"
    then have "val_of e = None" proof(cases e)qed(auto)
    then have bconf: "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using WTrtCons.prems(2) by(simp add: bconf_Cons)
    with IHe[OF De bconf nf] show ?thesis by(fast intro!:ListRed1)
  qed
next
  case (WTrtInitBlock v T\<^sub>1 T E V e\<^sub>2 T\<^sub>2)
  have IH2: "\<And>l. \<lbrakk>\<D> e\<^sub>2 \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>; \<not> final e\<^sub>2\<rbrakk>
                  \<Longrightarrow> \<exists>e' s' b'. P \<turnstile> \<langle>e\<^sub>2,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
   and D: "\<D> {V:T := Val v; e\<^sub>2} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e\<^sub>2"
    then show ?thesis
    proof (rule finalE)
      fix v\<^sub>2 assume "e\<^sub>2 = Val v\<^sub>2"
      thus ?thesis by(fast intro:RedInitBlock)
    next
      fix a assume "e\<^sub>2 = Throw a"
      thus ?thesis by(fast intro:red_reds.InitBlockThrow)
    qed
  next
    assume not_fin2: "\<not> final e\<^sub>2"
    then have "val_of e\<^sub>2 = None" proof(cases e\<^sub>2)qed(auto)
    from D have D2: "\<D> e\<^sub>2 \<lfloor>dom(l(V\<mapsto>v))\<rfloor>" by (auto simp:hyperset_defs)
    have e2conf: "P,sh \<turnstile>\<^sub>b (e\<^sub>2,b) \<surd>" using WTrtInitBlock.prems(2) by(simp add: bconf_InitBlock)
    from IH2[OF D2 e2conf not_fin2]
    obtain h' l' sh' e' b' where red2: "P \<turnstile> \<langle>e\<^sub>2,(h, l(V\<mapsto>v),sh),b\<rangle> \<rightarrow> \<langle>e',(h', l',sh'),b'\<rangle>"
      by auto
    from red_lcl_incr[OF red2] have "V \<in> dom l'" by auto
    with red2 show ?thesis by(fastforce intro:InitBlockRed)
  qed
next
  case (WTrtBlock E V T e T')
  have IH: "\<And>l. \<lbrakk>\<D> e \<lfloor>dom l\<rfloor>; P,sh \<turnstile>\<^sub>b (e,b) \<surd>; \<not> final e\<rbrakk>
                 \<Longrightarrow> \<exists>e' s' b'. P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
   and unass: "\<not> assigned V e" and D: "\<D> {V:T; e} \<lfloor>dom l\<rfloor>" by fact+
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume "e = Val v" thus ?thesis by(fast intro:RedBlock)
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro:red_reds.BlockThrow)
    qed
  next
    assume not_fin: "\<not> final e"
    then have "val_of e = None" proof(cases e)qed(auto)
    from D have De: "\<D> e \<lfloor>dom(l(V:=None))\<rfloor>" by(simp add:hyperset_defs)
    have bconf: "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using WTrtBlock by(simp add: bconf_Block)
    from IH[OF De bconf not_fin]
    obtain h' l' sh' e' b' where red: "P \<turnstile> \<langle>e,(h,l(V:=None),sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>"
      by auto
    show ?thesis
    proof (cases "l' V")
      assume "l' V = None"
      with red unass show ?thesis by(blast intro: BlockRedNone)
    next
      fix v assume "l' V = Some v"
      with red unass show ?thesis by(blast intro: BlockRedSome)
    qed
  qed
next
  case (WTrtSeq E e1 T1 e2 T2) show ?case
  proof cases
    assume "final e1"
    thus ?thesis
      by(fast elim:finalE intro:RedSeq red_reds.SeqThrow)
  next
    assume nf: "\<not> final e1"
    then have e1: "val_of e1 = None" proof(cases e1)qed(auto)
    then show ?thesis
    proof(cases "lass_val_of e1")
      case None
      then have "P,sh \<turnstile>\<^sub>b (e1,b) \<surd>" using WTrtSeq.prems(2) e1 by(simp add: bconf_Seq)
      with WTrtSeq nf e1 None show ?thesis by simp (blast intro:SeqRed)
    next
      case (Some p)
      obtain V v where "e1 = V:=Val v" using lass_val_of_spec[OF Some] by simp
      then show ?thesis using SeqRed[OF RedLAss] by blast
    qed
  qed
next
  case (WTrtCond E e e\<^sub>1 T\<^sub>1 e\<^sub>2 T\<^sub>2 T)
  have wt: "P,E,h,sh \<turnstile> e : Boolean" by fact
  show ?case
  proof cases
    assume "final e"
    thus ?thesis
    proof (rule finalE)
      fix v assume val: "e = Val v"
      then obtain b where v: "v = Bool b" using wt by auto
      show ?thesis
      proof (cases b)
        case True with val v show ?thesis by(fastforce intro:RedCondT simp: prod_cases3)
      next
        case False with val v show ?thesis by(fastforce intro:RedCondF simp: prod_cases3)
      qed
    next
      fix a assume "e = Throw a"
      thus ?thesis by(fast intro:red_reds.CondThrow)
    qed
  next
    assume nf: "\<not> final e"
    then have "bool_of e = None" proof(cases e)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using WTrtCond.prems(2) by(simp add: bconf_Cond)
    with WTrtCond nf show ?thesis by simp (blast intro:CondRed)
  qed
next
  case WTrtWhile show ?case by(fast intro:RedWhile)
next
  case (WTrtThrow E e T\<^sub>r T) show ?case
  proof cases
    assume "final e" \<comment> \<open>Then @{term e} must be @{term throw} or @{term null}\<close>
    with WTrtThrow show ?thesis
      by(fastforce simp:final_def is_refT_def
                  intro:red_reds.ThrowThrow red_reds.RedThrowNull)
  next
    assume nf: "\<not> final e" \<comment> \<open>Then @{term e} must reduce\<close>
    then have "val_of e = None" proof(cases e)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using WTrtThrow.prems(2) by(simp add: bconf_Throw)
    with WTrtThrow nf show ?thesis by simp (blast intro:ThrowRed)
  qed
next
  case (WTrtTry E e1 T1 V C e2 T2)
  have wt1: "P,E,h,sh \<turnstile> e1 : T1" by fact
  show ?case
  proof cases
    assume "final e1"
    thus ?thesis
    proof (rule finalE)
      fix v assume "e1 = Val v"
      thus ?thesis by(fast intro:RedTry)
    next
      fix a assume e1_Throw: "e1 = Throw a"
      with wt1 obtain D fs where ha: "h a = Some(D,fs)" by fastforce
      show ?thesis
      proof cases
        assume "P \<turnstile> D \<preceq>\<^sup>* C"
        with e1_Throw ha show ?thesis by(fastforce intro!:RedTryCatch)
      next
        assume "\<not> P \<turnstile> D \<preceq>\<^sup>* C"
        with e1_Throw ha show ?thesis by(fastforce intro!:RedTryFail)
      qed
    qed
  next
    assume nf: "\<not> final e1"
    then have "val_of e1 = None" proof(cases e1)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e1,b) \<surd>" using WTrtTry.prems(2) by(simp add: bconf_Try)
    with WTrtTry nf show ?thesis by simp (fast intro:TryRed)
  qed
next
  case (WTrtInit E e T\<^sub>r C Cs b) show ?case
  proof(cases Cs)
    case Nil then show ?thesis using WTrtInit by(fastforce intro!: RedInit)
  next
    case (Cons C' Cs')
    show ?thesis
    proof(cases b)
      case True then show ?thesis using Cons by(fastforce intro!: RedInitRInit)
    next
      case False
      show ?thesis
      proof(cases "sh C'")
        case None
        then show ?thesis using False Cons by(fastforce intro!: InitNoneRed)
      next
        case (Some sfsi)
        then obtain sfs i where sfsi:"sfsi = (sfs,i)" by(cases sfsi)
        show ?thesis
        proof(cases i)
          case Done
          then show ?thesis using False Some sfsi Cons by(fastforce intro!: RedInitDone)
        next
          case Processing
          then show ?thesis using False Some sfsi Cons by(fastforce intro!: RedInitProcessing)
        next
          case Error
          then show ?thesis using False Some sfsi Cons by(fastforce intro!: RedInitError)
        next
          case Prepared
          show ?thesis
          proof cases
            assume "C' = Object"
            then show ?thesis using False Some sfsi Prepared Cons by(fastforce intro: InitObjectRed)
          next
            assume "C' \<noteq> Object"
            then show ?thesis using False Some sfsi Prepared WTrtInit.hyps(3) Cons
              by(simp only: is_class_def)(fastforce intro!: InitNonObjectSuperRed)
          qed
        qed
      qed
    qed
  qed
next
  case (WTrtRI E e T\<^sub>r e' T\<^sub>r' C Cs)
  obtain sfs i where shC: "sh C = \<lfloor>(sfs, i)\<rfloor>" using WTrtRI.hyps(9) by blast
  show ?case
  proof cases
    assume fin: "final e" then show ?thesis
    proof (rule finalE)
      fix v assume e: "e = Val v"
      then show ?thesis using shC e by(fast intro:RedRInit)
    next
      fix a assume eThrow: "e = Throw a"
      show ?thesis
      proof(cases Cs)
        case Nil then show ?thesis using eThrow shC by(fastforce intro!: RInitThrow)
      next
        case Cons then show ?thesis using eThrow shC by(fastforce intro!: RInitInitThrow)
      qed
    qed
  next
    assume nf: "\<not> final e"
    then have "val_of e = None" proof(cases e)qed(auto)
    then have "P,sh \<turnstile>\<^sub>b (e,b) \<surd>" using WTrtRI.prems(2) by(simp add: bconf_RI)
    with WTrtRI nf show ?thesis by simp (meson red_reds.RInitRed)
  qed
qed
(*>*)

end
