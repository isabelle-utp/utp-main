(*  Title:      JinjaDCI/J/TypeSafe.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/TypeSafe.thy by Tobias Nipkow
*)

section \<open> Type Safety Proof \<close>

theory TypeSafe
imports Progress BigStep SmallStep JWellForm
begin

(* here because it requires well-typing def *)
lemma red_shext_incr: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>
  \<Longrightarrow> (\<And>E T. P,E,h,sh \<turnstile> e : T \<Longrightarrow> sh \<unlhd>\<^sub>s sh')"
  and reds_shext_incr: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle>
  \<Longrightarrow> (\<And>E Ts. P,E,h,sh \<turnstile> es [:] Ts \<Longrightarrow> sh \<unlhd>\<^sub>s sh')"
(*<*)
proof(induct rule:red_reds_inducts) qed(auto simp: shext_def)
(*>*)

lemma wf_types_clinit:
assumes wf:"wf_prog wf_md P" and ex: "class P C = Some a" and proc: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
shows "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sclinit([]) : Void"
proof -
  from ex obtain D fs ms where "a = (D,fs,ms)" by(cases a)
  then have sP: "(C, D, fs, ms) \<in> set P" using ex map_of_SomeD[of P C a] by(simp add: class_def)
  then have "wf_clinit ms" using assms by(unfold wf_prog_def wf_cdecl_def, auto)
  then obtain pns body where sm: "(clinit, Static, [], Void, pns, body) \<in> set ms"
    by(unfold wf_clinit_def) auto
  then have "P \<turnstile> C sees clinit,Static:[] \<rightarrow> Void = (pns,body) in C"
    using mdecl_visible[OF wf sP sm] by simp
  then show ?thesis using WTrtSCall proc by simp
qed

subsection\<open>Basic preservation lemmas\<close>

text\<open> First some easy preservation lemmas. \<close>

theorem red_preserves_hconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>T E. \<lbrakk> P,E,h,sh \<turnstile> e : T; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"
and reds_preserves_hconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>Ts E. \<lbrakk> P,E,h,sh \<turnstile> es [:] Ts; P \<turnstile> h \<surd> \<rbrakk> \<Longrightarrow> P \<turnstile> h' \<surd>)"
(*<*)
proof (induct rule:red_reds_inducts)
  case (RedNew h a C FDTs h' l sh es)
  have new: "new_Addr h = Some a" and fields: "P \<turnstile> C has_fields FDTs"
   and h': "h' = h(a\<mapsto>blank P C)"
   and hconf: "P \<turnstile> h \<surd>" by fact+
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  moreover have "P,h \<turnstile> blank P C \<surd>"
    using fields by(rule oconf_blank)
  ultimately show "P \<turnstile> h' \<surd>" using h' by(fast intro: hconf_new[OF hconf])
next
  case (RedFAss C F t D h a fs v l sh b')
  let ?fs' = "fs((F,D)\<mapsto>v)"
  have hconf: "P \<turnstile> h \<surd>" and ha: "h a = Some(C,fs)"
   and wt: "P,E,h,sh \<turnstile> addr a\<bullet>F{D}:=Val v : T" by fact+
  from wt ha obtain TF Tv where typeofv: "typeof\<^bsub>h\<^esub> v = Some Tv"
    and has: "P \<turnstile> C has F,NonStatic:TF in D"
    and sub: "P \<turnstile> Tv \<le> TF" by auto
  have "P,h \<turnstile> (C, ?fs') \<surd>"
  proof (rule oconf_fupd[OF has])
    show "P,h \<turnstile> (C, fs) \<surd>" using hconf ha by(simp add:hconf_def)
    show "P,h \<turnstile> v :\<le> TF" using sub typeofv by(simp add:conf_def)
  qed
  with hconf ha show "P \<turnstile> h(a\<mapsto>(C, ?fs')) \<surd>"  by (rule hconf_upd_obj)
qed(auto elim: WTrt.cases)
(*>*)


theorem red_preserves_lconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow>
  (\<And>T E. \<lbrakk> P,E,h,sh \<turnstile> e:T; P,h \<turnstile> l (:\<le>) E \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E)"
and reds_preserves_lconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow>
  (\<And>Ts E. \<lbrakk> P,E,h,sh \<turnstile> es[:]Ts; P,h \<turnstile> l (:\<le>) E \<rbrakk> \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E)"
(*<*)
proof(induct rule:red_reds_inducts)
  case RedNew thus ?case
    by(fast intro:lconf_hext red_hext_incr[OF red_reds.RedNew])
next
  case RedLAss thus ?case by(fastforce elim: lconf_upd simp:conf_def)
next
  case RedFAss thus ?case
    by(fast intro:lconf_hext red_hext_incr[OF red_reds.RedFAss])
next
  case (InitBlockRed e h l V v sh b e' h' l' sh' b' v' T T')
  have red: "P \<turnstile> \<langle>e, (h, l(V\<mapsto>v),sh),b\<rangle> \<rightarrow> \<langle>e',(h', l',sh'),b'\<rangle>"
   and IH: "\<And>T E . \<lbrakk> P,E,h,sh \<turnstile> e:T; P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E \<rbrakk>
                     \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E"
   and l'V: "l' V = Some v'" and lconf: "P,h \<turnstile> l (:\<le>) E"
   and wt: "P,E,h,sh \<turnstile> {V:T := Val v; e} : T'" by fact+
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover from IH lconf wt have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(auto simp del: fun_upd_apply simp: fun_upd_same lconf_upd2 conf_def)
  ultimately show "P,h' \<turnstile> l'(V := l V) (:\<le>) E"
    by (fastforce simp:lconf_def split:if_split_asm)
next
  case (BlockRedNone e h l V sh b e' h' l' sh' b' T T')
  have red: "P \<turnstile> \<langle>e,(h, l(V := None),sh),b\<rangle> \<rightarrow> \<langle>e',(h', l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk> P,E,h,sh \<turnstile> e : T; P,h \<turnstile> l(V:=None) (:\<le>) E \<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E"
   and lconf: "P,h \<turnstile> l (:\<le>) E" and wt: "P,E,h,sh \<turnstile> {V:T; e} : T'" by fact+
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(rule IH, insert lconf wt, auto simp:lconf_def)
  ultimately show "P,h' \<turnstile> l'(V := l V) (:\<le>) E"
    by (fastforce simp:lconf_def split:if_split_asm)
next
  case (BlockRedSome e h l V sh b e' h' l' sh' b' v T T')
  have red: "P \<turnstile> \<langle>e,(h, l(V := None),sh),b\<rangle> \<rightarrow> \<langle>e',(h', l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E,h,sh \<turnstile> e : T; P,h \<turnstile> l(V:=None) (:\<le>) E\<rbrakk>
                   \<Longrightarrow> P,h' \<turnstile> l' (:\<le>) E"
   and lconf: "P,h \<turnstile> l (:\<le>) E" and wt: "P,E,h,sh \<turnstile> {V:T; e} : T'" by fact+
  from lconf_hext[OF lconf red_hext_incr[OF red]]
  have "P,h' \<turnstile> l (:\<le>) E" .
  moreover have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)"
    by(rule IH, insert lconf wt, auto simp:lconf_def)
  ultimately show "P,h' \<turnstile> l'(V := l V) (:\<le>) E"
    by (fastforce simp:lconf_def split:if_split_asm)
qed(auto elim: WTrt.cases)
(*>*)


theorem red_preserves_shconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>T E. \<lbrakk> P,E,h,sh \<turnstile> e : T; P,h \<turnstile>\<^sub>s sh \<surd> \<rbrakk> \<Longrightarrow> P,h' \<turnstile>\<^sub>s sh' \<surd>)"
and reds_preserves_shconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> (\<And>Ts E. \<lbrakk> P,E,h,sh \<turnstile> es [:] Ts; P,h \<turnstile>\<^sub>s sh \<surd> \<rbrakk> \<Longrightarrow> P,h' \<turnstile>\<^sub>s sh' \<surd>)"
(*<*)
proof (induct rule:red_reds_inducts)
  case (RedNew h a C FDTs h' l sh es)
  have new: "new_Addr h = Some a"
   and h': "h' = h(a\<mapsto>blank P C)"
   and shconf: "P,h \<turnstile>\<^sub>s sh \<surd>" by fact+
  from new have None: "h a = None" by(rule new_Addr_SomeD)
  then show "P,h' \<turnstile>\<^sub>s sh \<surd>" using h' by(fast intro: shconf_hnew[OF shconf])
next
  case (RedFAss C F t D h a fs v l sh b)
  let ?fs' = "fs((F,D)\<mapsto>v)"
  have shconf: "P,h \<turnstile>\<^sub>s sh \<surd>" and ha: "h a = Some(C,fs)" by fact+
  then show "P,h(a\<mapsto>(C, ?fs')) \<turnstile>\<^sub>s sh \<surd>" by (rule shconf_hupd_obj)
next
  case (RedSFAss C F t D sh sfs i sfs' v sh' h l)
  let ?sfs' = "sfs(F\<mapsto>v)"
  have shconf: "P,h \<turnstile>\<^sub>s sh \<surd>" and shD: "sh D = \<lfloor>(sfs, i)\<rfloor>"
    and wt: "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D} := Val v : T" by fact+
  from wt obtain TF Tv where typeofv: "typeof\<^bsub>h\<^esub> v = Some Tv"
    and has: "P \<turnstile> C has F,Static:TF in D"
    and sub: "P \<turnstile> Tv \<le> TF" by (auto elim: WTrt.cases)
  have has': "P \<turnstile> D has F,Static:TF in D" using has by(rule has_field_idemp)
  have "P,h,D \<turnstile>\<^sub>s ?sfs' \<surd>"
  proof (rule soconf_fupd[OF has'])
    show "P,h,D \<turnstile>\<^sub>s sfs \<surd>" using shconf shD by(simp add:shconf_def)
    show "P,h \<turnstile> v :\<le> TF" using sub typeofv by(simp add:conf_def)
  qed
  with shconf have "P,h \<turnstile>\<^sub>s sh(D\<mapsto>(?sfs',i)) \<surd>" by (rule shconf_upd_obj)
  then show ?case using RedSFAss.hyps(3) RedSFAss.hyps(4) by blast
next
  case (InitNoneRed sh C C' Cs e h l)
  let ?sfs' = "sblank P C"
  have "P,h \<turnstile>\<^sub>s sh(C \<mapsto> (?sfs', Prepared)) \<surd>"
  proof(rule shconf_upd_obj)
    show "P,h \<turnstile>\<^sub>s sh \<surd>" using InitNoneRed by simp
    show "P,h,C \<turnstile>\<^sub>s sblank P C \<surd>" by (metis has_field_def soconf_def soconf_sblank)
  qed
  then show ?case by blast
next
  case (InitObjectRed sh C sfs sh' C' Cs e h l)
  have sh': "sh' = sh(C \<mapsto> (sfs, Processing))" by fact
  have "P,h \<turnstile>\<^sub>s sh(C \<mapsto> (sfs, Processing)) \<surd>"
  proof(rule shconf_upd_obj)
    show "P,h \<turnstile>\<^sub>s sh \<surd>" using InitObjectRed by simp
    moreover have "sh C = \<lfloor>(sfs, Prepared)\<rfloor>" using InitObjectRed by simp
    ultimately show "P,h,C \<turnstile>\<^sub>s sfs \<surd>" using shconfD by blast
  qed
  then show ?case using sh' by blast
next
  case (InitNonObjectSuperRed sh C sfs D a b sh' C' Cs e h l)
  have sh': "sh' = sh(C \<mapsto> (sfs, Processing))" by fact
  have "P,h \<turnstile>\<^sub>s sh(C \<mapsto> (sfs, Processing)) \<surd>"
  proof(rule shconf_upd_obj)
    show "P,h \<turnstile>\<^sub>s sh \<surd>" using InitNonObjectSuperRed by simp
    moreover have "sh C = \<lfloor>(sfs, Prepared)\<rfloor>" using InitNonObjectSuperRed by simp
    ultimately show "P,h,C \<turnstile>\<^sub>s sfs \<surd>" using shconfD by blast
  qed
  then show ?case using sh' by blast
next
  case (RedRInit sh C sfs i sh' C' Cs e v h l)
  have sh': "sh' = sh(C \<mapsto> (sfs, Done))" by fact
  have "P,h \<turnstile>\<^sub>s sh(C \<mapsto> (sfs, Done)) \<surd>"
  proof(rule shconf_upd_obj)
    show "P,h \<turnstile>\<^sub>s sh \<surd>" using RedRInit by simp
    moreover have "sh C = \<lfloor>(sfs, i)\<rfloor>" using RedRInit by simp
    ultimately show "P,h,C \<turnstile>\<^sub>s sfs \<surd>" using shconfD by blast
  qed
  then show ?case using sh' by blast
next
  case (RInitInitThrow sh C sfs i sh' a D Cs e h l)
  have sh': "sh' = sh(C \<mapsto> (sfs, Error))" by fact
  have "P,h \<turnstile>\<^sub>s sh(C \<mapsto> (sfs, Error)) \<surd>"
  proof(rule shconf_upd_obj)
    show "P,h \<turnstile>\<^sub>s sh \<surd>" using RInitInitThrow by simp
    moreover have "sh C = \<lfloor>(sfs, i)\<rfloor>" using RInitInitThrow by simp
    ultimately show "P,h,C \<turnstile>\<^sub>s sfs \<surd>" using shconfD by blast
  qed
  then show ?case using sh' by blast
next
  case (RInitThrow sh C sfs i sh' a e' h l)
  have sh': "sh' = sh(C \<mapsto> (sfs, Error))" by fact
  have "P,h \<turnstile>\<^sub>s sh(C \<mapsto> (sfs, Error)) \<surd>"
  proof(rule shconf_upd_obj)
    show "P,h \<turnstile>\<^sub>s sh \<surd>" using RInitThrow by simp
    moreover have "sh C = \<lfloor>(sfs, i)\<rfloor>" using RInitThrow by simp
    ultimately show "P,h,C \<turnstile>\<^sub>s sfs \<surd>" using shconfD by blast
  qed
  then show ?case using sh' by blast
qed(auto elim: WTrt.cases)
(*>*)

theorem assumes wf: "wwf_J_prog P"
shows red_preserves_iconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> iconf sh e \<Longrightarrow> iconf sh' e'"
and reds_preserves_iconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> iconfs sh es \<Longrightarrow> iconfs sh' es'"
(*<*)
proof (induct rule:red_reds_inducts)
  case (BinOpRed1 e h l sh b e' h' l' sh' b' bop e\<^sub>2)
  then show ?case using BinOpRed1 nsub_RI_iconf[of e\<^sub>2 sh'] val_of_spec
  proof(cases "val_of e") qed(simp,fast)
next
  case (FAssRed1 e h l sh b e' h' l' sh' b' F D e\<^sub>2)
  then show ?case using FAssRed1 nsub_RI_iconf[of e\<^sub>2 sh'] val_of_spec
  proof(cases "val_of e") qed(simp,fast)
next
  case (CallObj e h l sh b e' h' l' sh' b' M es)
  then show ?case using CallObj nsub_RIs_iconfs[of es sh'] val_of_spec
  proof(cases "val_of e") qed(simp,fast)
next
  case RedCall then show ?case using sees_wwf_nsub_RI[OF wf RedCall.hyps(2)]
    by (clarsimp simp: assigned_def nsub_RI_iconf)
next
  case (RedSCall C M Ts T pns body D vs a a b)
  then have "\<not>sub_RI (blocks (pns, Ts, vs, body))"
    using sees_wwf_nsub_RI[OF wf RedSCall.hyps(1)] by simp
  then show ?case by(rule nsub_RI_iconf)
next
  case SCallInitRed then show ?case by fastforce
next
  case (BlockRedNone e h l V sh b e' h' l' sh' b' T)
  then show ?case by auto
next
  case (SeqRed e h l sh b e' h' l' sh' b' e\<^sub>2)
  then show ?case
  proof(cases "lass_val_of e")
    case None then show ?thesis using SeqRed nsub_RI_iconf by(auto dest: val_of_spec)
  next
    case (Some a)
    have "e' = unit \<and> sh' = sh" by(simp add: lass_val_of_red[OF Some SeqRed(1)])
    then show ?thesis using SeqRed Some by(auto dest: val_of_spec)
  qed
next
  case (ListRed1 e h l sh b e' h' l' sh' b' es)
  then show ?case using ListRed1 nsub_RIs_iconfs[of es sh'] val_of_spec
  proof(cases "val_of e") qed(simp,fast)
next
  case RedInit then show ?case by(auto simp: nsub_RI_iconf)
next
  case (RedInitDone sh C sfs C' Cs e h l b)
  then show ?case proof(cases Cs) qed(auto simp: initPD_def)
next
  case (RedInitProcessing sh C sfs C' Cs e h l b)
  then show ?case proof(cases Cs) qed(auto simp: initPD_def)
next
  case (RedRInit sh C sfs i sh' C' Cs v e h l b)
  then show ?case proof(cases Cs) qed(auto simp: initPD_def)
next
  case CallThrowParams then show ?case by(auto simp: iconfs_map_throw)
next
  case SCallThrowParams then show ?case by(auto simp: iconfs_map_throw)
qed(auto simp: nsub_RI_iconf lass_val_of_iconf)
(*>*)


lemma Seq_bconf_preserve_aux:
assumes "P \<turnstile> \<langle>e,(h, l, sh),b\<rangle> \<rightarrow> \<langle>e',(h', l', sh'),b'\<rangle>" and "P,sh \<turnstile>\<^sub>b (e;; e\<^sub>2,b) \<surd>"
  and "P,sh \<turnstile>\<^sub>b (e::expr,b) \<surd> \<longrightarrow> P,sh' \<turnstile>\<^sub>b (e'::expr,b') \<surd>"
shows "P,sh' \<turnstile>\<^sub>b (e';;e\<^sub>2,b') \<surd>"
proof(cases "val_of e")
  case None show ?thesis
  proof(cases "lass_val_of e")
    case lNone: None show ?thesis
    proof(cases "lass_val_of e'")
      case lNone': None
      then show ?thesis using None assms lNone
        by(auto dest: val_of_spec simp: bconf_def option.distinct(1))
    next
      case (Some a)
      then show ?thesis using None assms lNone by(auto dest: lass_val_of_spec simp: bconf_def)
    qed
  next
    case (Some a)
    then show ?thesis using None assms by(auto dest: lass_val_of_spec)
  qed
next
  case (Some a)
  then show ?thesis using assms by(auto dest: val_of_spec)
qed

theorem red_preserves_bconf:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> iconf sh e \<Longrightarrow> P,sh \<turnstile>\<^sub>b (e,b) \<surd> \<Longrightarrow> P,sh' \<turnstile>\<^sub>b (e',b') \<surd>"
and reds_preserves_bconf:
  "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> iconfs sh es \<Longrightarrow> P,sh \<turnstile>\<^sub>b (es,b) \<surd> \<Longrightarrow> P,sh' \<turnstile>\<^sub>b (es',b') \<surd>"
(*<*)
proof (induct rule:red_reds_inducts)
  case (CastRed e a a b b e' a a b b' C) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (BinOpRed1 e h l sh b e' h' l' sh' b' bop e\<^sub>2) show ?case
  proof(cases b')
    case True with BinOpRed1 val_of_spec show ?thesis
    proof(cases "val_of e") qed(simp,fast)
  next
    case False then show ?thesis by (simp add: bconf_def)
  qed
next
case (BinOpRed2 e a a b b e' a a b b' v\<^sub>1 bop) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (LAssRed e a a b b e' a a b b' V) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (FAccRed e a a b b e' a a b b' F D) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (RedSFAccNonStatic C F t D h l sh b) then show ?case
    using has_field_fun[of P C F NonStatic] by (auto simp: bconf_def)
next
  case (FAssRed1 e h l sh b e' h' l' sh' b' F D e\<^sub>2) show ?case
  proof(cases b')
    case True with FAssRed1 val_of_spec show ?thesis
    proof(cases "val_of e'")qed((simp,fast)+)
  next
    case False then show ?thesis by(simp add: bconf_def)
  qed
next
  case (FAssRed2 e a a b b e' a a b b' v F D) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (SFAssRed e h l sh b e' h' l' sh' b' C F D) then show ?case
  proof(cases b') qed(fastforce simp: bconf_def val_no_step)+
next
  case (RedSFAssNonStatic C F t D v a a b b) then show ?case
    using has_field_fun[of P C F NonStatic] by (auto simp: bconf_def)
next
  case (CallObj e h l sh b e' h' l' sh' b' M es) show ?case
  proof(cases b')
    case True with CallObj val_of_spec show ?thesis
    proof(cases "val_of e'")qed((simp,fast)+)
  next
    case False then show ?thesis by(simp add: bconf_def)
  qed
next
  case (CallParams es a a b b es' a a b b' v M) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (SCallParams es h l sh b es' h' l' sh' b' C M) show ?case
  proof(cases b')
    case b': True show ?thesis
    proof(cases "map_vals_of es'")
      case None
      then show ?thesis using SCallParams b' vals_no_step
      proof(cases "map_vals_of es")qed(clarsimp,fast)
    next
      case f: Some
      then show ?thesis using SCallParams b' vals_no_step
      proof(cases "map_vals_of es")qed(clarsimp,fast)
    qed
  next
    case False then show ?thesis by(simp add: bconf_def)
  qed
next
  case (SCallInitDoneRed C M Ts T pns body D sh sfs vs h l)
    then show ?case by(auto simp: bconf_def initPD_def) (rule_tac x=D in exI, auto)+
next
  case (RedSCallNonStatic C M Ts T a b D vs h l sh b) then show ?case
    using sees_method_fun[of P C M NonStatic] by (auto simp: bconf_def)
next
  case (BlockRedNone e h l V sh b e' h' l' sh' b' T) show ?case
  proof(cases "assigned V e'")
    case True
    then obtain v e2 where "e' = V := Val v;;e2" by(clarsimp simp: assigned_def)
    then show ?thesis using BlockRedNone by(clarsimp simp: bconf_def)
  next
    case False then show ?thesis using BlockRedNone by simp
  qed
next
  case (BlockRedSome e h l V sh b e' h' l' sh' b' v T) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (InitBlockRed e h l V v sh b e' h' l' sh' b' v' T) show ?case
  proof(cases b')
    case True
    then show ?thesis using InitBlockRed by (simp add: assigned_def)
  next
    case False then show ?thesis by(simp add: bconf_def)
  qed
next
  case (RedBlock V T u)
  then have "\<not>assigned V (Val u)" by(clarsimp simp: assigned_def)
  then show ?case using RedBlock by(simp add: bconf_def)
next
  case (SeqRed e h l sh b e' h' l' sh' b' e\<^sub>2)
  have "iconf sh e"
  proof(cases "lass_val_of e")
    case (Some a) show ?thesis by(rule lass_val_of_iconf[OF Some])
  next
    case None then show ?thesis using SeqRed by(auto dest: val_of_spec)
  qed
  then show ?case using SeqRed Seq_bconf_preserve_aux by simp
next
  case (CondRed e a a b b e' a a b b' e\<^sub>1 e\<^sub>2) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (ThrowRed e a a b b e' a a b b') then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (TryRed e a a b b e' a a b b' C V e\<^sub>2) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (ListRed1 e h l sh b e' h' l' sh' b' es)
  with val_of_spec show ?case
  proof(cases b') qed((clarsimp,fast),simp add: bconfs_def)
next
  case (RedInit C b' e X Y b b'')
  then show ?case
   by(auto simp: bconf_def icheck_ss_exp icheck_init_class icheck_curr_init)
next
  case (RInitRed e a a b b e' a a b b' C Cs e\<^sub>0) then show ?case
  proof(cases b') qed(simp, simp add: bconf_def)
next
  case (BlockThrow V T a)
  then have "\<not>assigned V (Throw a)" by(simp add: assigned_def)
  then show ?case using BlockThrow by simp
qed(simp_all, auto simp: bconf_def initPD_def)
(*>*)

text\<open> Preservation of definite assignment more complex and requires a
few lemmas first. \<close>

lemma [iff]: "\<And>A. \<lbrakk> length Vs = length Ts; length vs = length Ts\<rbrakk> \<Longrightarrow>
 \<D> (blocks (Vs,Ts,vs,e)) A = \<D> e (A \<squnion> \<lfloor>set Vs\<rfloor>)"
(*<*)
apply(induct Vs Ts vs e rule:blocks_induct)
apply(simp_all add:hyperset_defs)
done
(*>*)


lemma red_lA_incr: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>
   \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A> e \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A> e'"
and reds_lA_incr: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle>
   \<Longrightarrow> \<lfloor>dom l\<rfloor> \<squnion> \<A>s es \<sqsubseteq>  \<lfloor>dom l'\<rfloor> \<squnion> \<A>s es'"
(*<*)
apply(induct rule:red_reds_inducts)
apply(simp_all del:fun_upd_apply add:hyperset_defs)
apply auto
apply(blast dest:red_lcl_incr)+
done
(*>*)

text\<open> Now preservation of definite assignment. \<close>

lemma assumes wf: "wf_J_prog P"
shows red_preserves_defass:
  "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow> \<D> e \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom l'\<rfloor>"
and "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow> \<D>s es \<lfloor>dom l\<rfloor> \<Longrightarrow> \<D>s es' \<lfloor>dom l'\<rfloor>"
(*<*)
proof (induct rule:red_reds_inducts)
  case BinOpRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case FAssRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CallObj thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
next
  case RedCall thus ?case
    by (auto dest!:sees_wf_mdecl[OF wf] simp:wf_mdecl_def hyperset_defs elim!:D_mono')
next
  case RedSCall thus ?case
    by (auto dest!:sees_wf_mdecl[OF wf] simp:wf_mdecl_def hyperset_defs elim!:D_mono')
next
  case SCallInitRed
  then show ?case by(auto simp:hyperset_defs Ds_Vals)
next
  case InitBlockRed thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case BlockRedNone thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case BlockRedSome thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply)
next
  case SeqRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CondRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case TryRed thus ?case
    by (fastforce dest:red_lcl_incr intro:D_mono' simp:hyperset_defs)
next
  case ListRed1 thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
next
  case RedWhile thus ?case by(auto simp:hyperset_defs elim!:D_mono')
next
  case RedInit then show ?case by (auto intro: D_mono' simp: hyperset_defs)
next
  case (RInitRed e h l sh b e' h' l' sh' b' C Cs e\<^sub>0)
  then show ?case by(auto simp:hyperset_defs dest:red_lcl_incr elim!:D_mono')
qed(auto simp:hyperset_defs)
(*>*)


text\<open> Combining conformance of heap, static heap, and local variables: \<close>

definition sconf :: "J_prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> bool"   ("_,_ \<turnstile> _ \<surd>"   [51,51,51]50)
where
  "P,E \<turnstile> s \<surd>  \<equiv>  let (h,l,sh) = s in P \<turnstile> h \<surd> \<and> P,h \<turnstile> l (:\<le>) E \<and> P,h \<turnstile>\<^sub>s sh \<surd>"

lemma red_preserves_sconf:
  "\<lbrakk> P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>; P,E,hp s,shp s \<turnstile> e : T; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
by(fastforce intro:red_preserves_hconf red_preserves_lconf red_preserves_shconf
            simp add:sconf_def)
(*>*)

lemma reds_preserves_sconf:
  "\<lbrakk> P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>; P,E,hp s,shp s \<turnstile> es [:] Ts; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
by(fastforce intro:reds_preserves_hconf reds_preserves_lconf reds_preserves_shconf
            simp add:sconf_def)
(*>*)


subsection "Subject reduction"

lemma wt_blocks:
 "\<And>E. \<lbrakk> length Vs = length Ts; length vs = length Ts \<rbrakk> \<Longrightarrow>
       (P,E,h,sh \<turnstile> blocks(Vs,Ts,vs,e) : T) =
       (P,E(Vs[\<mapsto>]Ts),h,sh \<turnstile> e:T \<and> (\<exists>Ts'. map (typeof\<^bsub>h\<^esub>) vs = map Some Ts' \<and> P \<turnstile> Ts' [\<le>] Ts))"
(*<*)
apply(induct Vs Ts vs e rule:blocks_induct)
apply (force simp add:rel_list_all2_Cons2)
apply simp_all
done
(*>*)

theorem assumes wf: "wf_J_prog P"
shows subject_reduction2: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle> \<Longrightarrow>
  (\<And>E T. \<lbrakk> P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e:T \<rbrakk>
           \<Longrightarrow> \<exists>T'. P,E,h',sh' \<turnstile> e':T' \<and> P \<turnstile> T' \<le> T)"
and subjects_reduction2: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle> \<Longrightarrow>
  (\<And>E Ts. \<lbrakk> P,E \<turnstile> (h,l,sh) \<surd>; iconfs sh es; P,E,h,sh \<turnstile> es [:] Ts \<rbrakk>
            \<Longrightarrow> \<exists>Ts'. P,E,h',sh' \<turnstile> es' [:] Ts' \<and> P \<turnstile> Ts' [\<le>] Ts)"
(*<*)
proof (induct rule:red_reds_inducts)
  case RedNew then show ?case by (auto simp: blank_def)
next
  case RedNewFail thus ?case
    by (unfold sconf_def hconf_def) (fastforce elim!:typeof_OutOfMemory)
next
  case CastRed thus ?case
    by(clarsimp simp:is_refT_def)
      (blast intro: widens_trans dest!:widen_Class[THEN iffD1])
next
  case RedCastFail thus ?case
    by (unfold sconf_def hconf_def)  (fastforce elim!:typeof_ClassCast)
next
  case (BinOpRed1 e\<^sub>1 h l sh b e\<^sub>1' h' l' sh' b' bop e\<^sub>2)
  have red: "P \<turnstile> \<langle>e\<^sub>1,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e\<^sub>1',(h',l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e\<^sub>1; P,E,h,sh \<turnstile> e\<^sub>1:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e\<^sub>1' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)"
   and wt: "P,E,h,sh \<turnstile> e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T" by fact+
  have val: "val_of e\<^sub>1 = None" using red iconf val_no_step by auto
  then have iconf1: "iconf sh e\<^sub>1" and nsub_RI2: "\<not>sub_RI e\<^sub>2" using iconf by simp+
  have "P,E,h',sh' \<turnstile> e\<^sub>1' \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T"
  proof (cases bop)
    assume [simp]: "bop = Eq"
    from wt obtain T\<^sub>1 T\<^sub>2 where [simp]: "T = Boolean"
      and wt\<^sub>1: "P,E,h,sh \<turnstile> e\<^sub>1 : T\<^sub>1" and wt\<^sub>2: "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2" by auto
    show ?thesis
      using WTrt_hext_shext_mono[OF wt\<^sub>2 red_hext_incr[OF red] red_shext_incr[OF red wt\<^sub>1] nsub_RI2]
        IH[OF conf iconf1 wt\<^sub>1] by auto
  next
    assume  [simp]: "bop = Add"
    from wt have [simp]: "T = Integer"
      and wt\<^sub>1: "P,E,h,sh \<turnstile> e\<^sub>1 : Integer" and wt\<^sub>2: "P,E,h,sh \<turnstile> e\<^sub>2 : Integer"
      by auto
    show ?thesis
      using WTrt_hext_shext_mono[OF wt\<^sub>2 red_hext_incr[OF red] red_shext_incr[OF red wt\<^sub>1] nsub_RI2]
        IH[OF conf iconf1 wt\<^sub>1] by auto
  qed
  thus ?case by auto
next
  case (BinOpRed2 e\<^sub>2 h l sh b e\<^sub>2' h' l' sh' b' v\<^sub>1 bop)
  have red: "P \<turnstile> \<langle>e\<^sub>2,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e\<^sub>2',(h',l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e\<^sub>2; P,E,h,sh \<turnstile> e\<^sub>2:T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e\<^sub>2' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (Val v\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2)"
   and wt: "P,E,h,sh \<turnstile> (Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> e\<^sub>2 : T" by fact+
  have iconf2: "iconf sh e\<^sub>2" using iconf by simp
  have "P,E,h',sh' \<turnstile> (Val v\<^sub>1) \<guillemotleft>bop\<guillemotright> e\<^sub>2' : T"
  proof (cases bop)
    assume [simp]: "bop = Eq"
    from wt obtain T\<^sub>1 T\<^sub>2 where [simp]: "T = Boolean"
      and wt\<^sub>1: "P,E,h,sh \<turnstile> Val v\<^sub>1 : T\<^sub>1" and wt\<^sub>2: "P,E,h,sh \<turnstile> e\<^sub>2:T\<^sub>2" by auto
    show ?thesis
      using IH[OF conf iconf2 wt\<^sub>2] WTrt_hext_mono[OF wt\<^sub>1 red_hext_incr[OF red]]
      by auto
  next
    assume  [simp]: "bop = Add"
    from wt have [simp]: "T = Integer"
      and wt\<^sub>1: "P,E,h,sh \<turnstile> Val v\<^sub>1 : Integer" and wt\<^sub>2: "P,E,h,sh \<turnstile> e\<^sub>2 : Integer"
      by auto
    show ?thesis
      using IH[OF conf iconf2 wt\<^sub>2] WTrt_hext_mono[OF wt\<^sub>1 red_hext_incr[OF red]]
      by auto
  qed
  thus ?case by auto
next
  case (RedBinOp bop) thus ?case
  proof (cases bop)
    case Eq thus ?thesis using RedBinOp by auto
  next
    case Add thus ?thesis using RedBinOp by auto
  qed
next
  case RedVar thus ?case by (fastforce simp:sconf_def lconf_def conf_def)
next
  case (LAssRed e h l sh b e' h' l' sh' b' V)
  obtain Te where Te: "P,E,h,sh \<turnstile> e : Te \<and> P \<turnstile> Te \<le> the(E V)" using LAssRed.prems(3) by auto
  then have wide: "P \<turnstile> Te \<le> the(E V)" using LAssRed by simp
  then have "\<exists>T'. P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> Te"
    using LAssRed.hyps(2) LAssRed.prems(1,2) Te widen_trans[OF _ wide] by auto
  then obtain T' where wt: "P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> Te" by clarsimp
  have "P,E,h',sh' \<turnstile> V:=e' : Void" using LAssRed wt widen_trans[OF _ wide] by auto
  then show ?case using LAssRed by(rule_tac x = Void in exI) auto
next
  case (FAccRed e h l sh b e' h' l' sh' b' F D)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (e\<bullet>F{D})"
   and wt: "P,E,h,sh \<turnstile> e\<bullet>F{D} : T" by fact+
  have iconf': "iconf sh e" using iconf by simp+
  \<comment> \<open>The goal: ?case = @{prop ?case}\<close>
  \<comment> \<open>Now distinguish the two cases how wt can have arisen.\<close>
  { fix C assume wte: "P,E,h,sh \<turnstile> e : Class C"
             and has: "P \<turnstile> C has F,NonStatic:T in D"
    from IH[OF conf iconf' wte]
    obtain U where wte': "P,E,h',sh' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      by auto
    \<comment> \<open>Now distinguish what @{term U} can be.\<close>
    { assume "U = NT" hence ?case using wte'
        by(blast intro:WTrtFAccNT widen_refl) }
    moreover
    { fix C' assume U: "U = Class C'" and C'subC: "P \<turnstile> C' \<preceq>\<^sup>* C"
      from has_field_mono[OF has C'subC] wte' U
      have ?case by(blast intro:WTrtFAcc) }
    ultimately have ?case using UsubC by(simp add: widen_Class) blast }
  moreover
  { assume "P,E,h,sh \<turnstile> e : NT"
    hence "P,E,h',sh' \<turnstile> e' : NT" using IH[OF conf iconf'] by fastforce
    hence ?case  by(fastforce intro:WTrtFAccNT widen_refl) }
  ultimately show ?case using wt by blast
next
  case RedFAcc thus ?case
    by(fastforce simp:sconf_def hconf_def oconf_def conf_def has_field_def
                dest:has_fields_fun)
next
  case RedFAccNull thus ?case
    by(fastforce intro: widen_refl WTThrow[OF WTVal] elim!: typeof_NullPointer
                simp: sconf_def hconf_def)
next
  case RedSFAccNone then show ?case
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_NoSuchFieldError
      simp: sconf_def hconf_def)
next
  case RedFAccStatic then show ?case
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError
      simp: sconf_def hconf_def)
next
  case (RedSFAcc C F t D sh sfs i v h l es)
  then have "P \<turnstile> C has F,Static:T in D" by fast
  then have dM: "P \<turnstile> D has F,Static:T in D" by(rule has_field_idemp)
  then show ?case using RedSFAcc by(fastforce simp:sconf_def shconf_def soconf_def conf_def)
next
  case SFAccInitDoneRed then show ?case by (meson widen_refl)
next
  case (SFAccInitRed C F t D sh h l E T)
  have "is_class P D" using SFAccInitRed.hyps(1) by(rule has_field_is_class')
  then have "P,E,h,sh \<turnstile> INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF{D} : T \<and> P \<turnstile> T \<le> T"
    using SFAccInitRed WTrtInit[OF SFAccInitRed.prems(3)] by clarsimp
  then show ?case by(rule exI)
next
  case RedSFAccNonStatic then show ?case
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError
      simp: sconf_def hconf_def)
next
  case (FAssRed1 e h l sh b e' h' l' sh' b' F D e\<^sub>2)
  have red: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (e\<bullet>F{D} := e\<^sub>2)"
   and wt: "P,E,h,sh \<turnstile> e\<bullet>F{D}:=e\<^sub>2 : T" by fact+
  have val: "val_of e = None" using red iconf val_no_step by auto
  then have iconf': "iconf sh e" and nsub_RI2: "\<not>sub_RI e\<^sub>2" using iconf by simp+
  from wt have void: "T = Void" by blast
  \<comment> \<open>We distinguish if @{term e} has type @{term NT} or a Class type\<close>
  \<comment> \<open>Remember ?case = @{term ?case}\<close>
  { assume wt':"P,E,h,sh \<turnstile> e : NT"
    hence "P,E,h',sh' \<turnstile> e' : NT" using IH[OF conf iconf'] by fastforce
    moreover obtain T\<^sub>2 where "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2" using wt by auto
    from this red_hext_incr[OF red] red_shext_incr[OF red wt'] nsub_RI2 have  "P,E,h',sh' \<turnstile> e\<^sub>2 : T\<^sub>2"
      by(rule WTrt_hext_shext_mono)
    ultimately have ?case using void by(blast intro!:WTrtFAssNT)
  }
  moreover
  { fix C TF T\<^sub>2 assume wt\<^sub>1: "P,E,h,sh \<turnstile> e : Class C" and wt\<^sub>2: "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2"
    and has: "P \<turnstile> C has F,NonStatic:TF in D" and sub: "P \<turnstile> T\<^sub>2 \<le> TF"
    obtain U where wt\<^sub>1': "P,E,h',sh' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf iconf' wt\<^sub>1] by blast
    have wt\<^sub>2': "P,E,h',sh' \<turnstile> e\<^sub>2 : T\<^sub>2"
      by(rule WTrt_hext_shext_mono[OF wt\<^sub>2 red_hext_incr[OF red] red_shext_incr[OF red wt\<^sub>1] nsub_RI2])
    \<comment> \<open>Is @{term U} the null type or a class type?\<close>
    { assume "U = NT" with wt\<^sub>1' wt\<^sub>2' void have ?case
        by(blast intro!:WTrtFAssNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and "subclass": "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,h',sh' \<turnstile> e' : Class C'" using wt\<^sub>1' UClass by auto
      moreover have "P \<turnstile> C' has F,NonStatic:TF in D"
        by(rule has_field_mono[OF has "subclass"])
      ultimately have ?case using wt\<^sub>2' sub void by(blast intro:WTrtFAss) }
    ultimately have ?case using UsubC by(auto simp add:widen_Class) }
  ultimately show ?case using wt by blast
next
  case (FAssRed2 e\<^sub>2 h l sh b e\<^sub>2' h' l' sh' b' v F D)
  have red: "P \<turnstile> \<langle>e\<^sub>2,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e\<^sub>2',(h',l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e\<^sub>2; P,E,h,sh \<turnstile> e\<^sub>2 : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e\<^sub>2' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (Val v\<bullet>F{D} := e\<^sub>2)"
   and wt: "P,E,h,sh \<turnstile> Val v\<bullet>F{D}:=e\<^sub>2 : T" by fact+
  have iconf2: "iconf sh e\<^sub>2" using iconf by simp
  from wt have [simp]: "T = Void" by auto
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix C TF T\<^sub>2
    assume wt\<^sub>1: "P,E,h,sh \<turnstile> Val v : Class C"
      and has: "P \<turnstile> C has F,NonStatic:TF in D"
      and wt\<^sub>2: "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2" and TsubTF: "P \<turnstile> T\<^sub>2 \<le> TF"
    have wt\<^sub>1': "P,E,h',sh' \<turnstile> Val v : Class C"
      using WTrt_hext_mono[OF wt\<^sub>1 red_hext_incr[OF red]] by auto
    obtain T\<^sub>2' where wt\<^sub>2': "P,E,h',sh' \<turnstile> e\<^sub>2' : T\<^sub>2'" and T'subT: "P \<turnstile> T\<^sub>2' \<le> T\<^sub>2"
      using IH[OF conf iconf2 wt\<^sub>2] by blast
    have "P,E,h',sh' \<turnstile> Val v\<bullet>F{D}:=e\<^sub>2' : Void"
      by(rule WTrtFAss[OF wt\<^sub>1' has wt\<^sub>2' widen_trans[OF T'subT TsubTF]])
    thus ?case by auto
  next
    fix T\<^sub>2 assume null: "P,E,h,sh \<turnstile> Val v : NT" and wt\<^sub>2: "P,E,h,sh \<turnstile> e\<^sub>2 : T\<^sub>2"
    from null have "v = Null" by simp
    moreover
    obtain T\<^sub>2' where "P,E,h',sh' \<turnstile> e\<^sub>2' : T\<^sub>2' \<and> P \<turnstile> T\<^sub>2' \<le> T\<^sub>2"
      using IH[OF conf iconf2 wt\<^sub>2] by blast
    ultimately show ?thesis by(fastforce intro:WTrtFAssNT)
  qed
next
  case RedFAss thus ?case by(auto simp del:fun_upd_apply)
next
  case RedFAssNull thus ?case
    by(fastforce intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp:sconf_def hconf_def)
next
  case RedFAssStatic then show ?case 
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError
      simp: sconf_def hconf_def)
next
  case (SFAssRed e h l sh b e' h' l' sh' b' C F D E T)
  have IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (C\<bullet>\<^sub>sF{D} := e)"
   and wt: "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sF{D}:=e : T" by fact+
  have iconf': "iconf sh e" using iconf by simp
  from wt have [simp]: "T = Void" by auto
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix TF T1
    assume has: "P \<turnstile> C has F,Static:TF in D"
      and wt1: "P,E,h,sh \<turnstile> e : T1" and TsubTF: "P \<turnstile> T1 \<le> TF"
    obtain T' where wt1': "P,E,h',sh' \<turnstile> e' : T'" and T'subT: "P \<turnstile> T' \<le> T1"
      using IH[OF conf iconf' wt1] by blast
    have "P,E,h',sh' \<turnstile> C\<bullet>\<^sub>sF{D}:=e' : Void"
      by(rule WTrtSFAss[OF wt1' has widen_trans[OF T'subT TsubTF]])
    thus ?case by auto
  qed
next
  case SFAssInitDoneRed then show ?case by (meson widen_refl)
next
  case (SFAssInitRed C F t D sh v h l E T)
  have "is_class P D" using SFAssInitRed.hyps(1) by(rule has_field_is_class')
  then have "P,E,h,sh \<turnstile> INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF{D} := Val v : T \<and> P \<turnstile> T \<le> T"
    using SFAssInitRed WTrtInit[OF SFAssInitRed.prems(3)] by clarsimp
  then show ?case by(rule exI)
next
  case RedSFAssNone then show ?case
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_NoSuchFieldError
      simp: sconf_def hconf_def)
next
  case RedSFAssNonStatic then show ?case
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError
      simp: sconf_def hconf_def)
next
  case (CallObj e h l sh b e' h' l' sh' b' M es)
  have red: "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                 \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (e\<bullet>M(es))"
   and wt: "P,E,h,sh \<turnstile> e\<bullet>M(es) : T" by fact+
  have val: "val_of e = None" using red iconf val_no_step by auto
  then have iconf': "iconf sh e" and nsub_RIs: "\<not>sub_RIs es" using iconf by simp+
  \<comment> \<open>We distinguish if @{term e} has type @{term NT} or a Class type\<close>
  \<comment> \<open>Remember ?case = @{term ?case}\<close>
  { assume wt':"P,E,h,sh \<turnstile> e:NT"
    hence "P,E,h',sh' \<turnstile> e' : NT" using IH[OF conf iconf'] by fastforce
    moreover
    fix Ts assume wtes: "P,E,h,sh \<turnstile> es [:] Ts"
    have "P,E,h',sh' \<turnstile> es [:] Ts"
      by(rule WTrts_hext_shext_mono[OF wtes red_hext_incr[OF red] red_shext_incr[OF red wt'] nsub_RIs])
    ultimately have ?case by(blast intro!:WTrtCallNT) }
  moreover
  { fix C D Ts Us pns body
    assume wte: "P,E,h,sh \<turnstile> e : Class C"
      and "method": "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "P,E,h,sh \<turnstile> es [:] Us" and subs: "P \<turnstile> Us [\<le>] Ts"
    obtain U where wte': "P,E,h',sh' \<turnstile> e' : U" and UsubC: "P \<turnstile> U \<le> Class C"
      using IH[OF conf iconf' wte] by blast
    \<comment> \<open>Is @{term U} the null type or a class type?\<close>
    { assume "U = NT"
      moreover have "P,E,h',sh' \<turnstile> es [:] Us"
        by(rule WTrts_hext_shext_mono[OF wtes red_hext_incr[OF red] red_shext_incr[OF red wte] nsub_RIs])
      ultimately have ?case using wte' by(blast intro!:WTrtCallNT) }
    moreover
    { fix C' assume UClass: "U = Class C'" and "subclass": "P \<turnstile> C' \<preceq>\<^sup>* C"
      have "P,E,h',sh' \<turnstile> e' : Class C'" using wte' UClass by auto
      moreover obtain Ts' T' pns' body' D'
        where method': "P \<turnstile> C' sees M,NonStatic:Ts'\<rightarrow>T' = (pns',body') in D'"
        and subs': "P \<turnstile> Ts [\<le>] Ts'" and sub': "P \<turnstile> T' \<le> T"
        using Call_lemma[OF "method" "subclass" wf] by fast
      moreover have "P,E,h',sh' \<turnstile> es [:] Us"
        by(rule WTrts_hext_shext_mono[OF wtes red_hext_incr[OF red] red_shext_incr[OF red wte] nsub_RIs])
      ultimately have ?case
        using subs by(blast intro:WTrtCall rtrancl_trans widens_trans) }
    ultimately have ?case using UsubC by(auto simp add:widen_Class) }
  ultimately show ?case using wt by auto
next
  case (CallParams es h l sh b es' h' l' sh' b' v M)
  have reds: "P \<turnstile> \<langle>es,(h,l,sh),b\<rangle> [\<rightarrow>] \<langle>es',(h',l',sh'),b'\<rangle>"
   and IH: "\<And>E Ts. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconfs sh es; P,E,h,sh \<turnstile> es [:] Ts\<rbrakk>
                 \<Longrightarrow> \<exists>Us. P,E,h',sh' \<turnstile> es' [:] Us \<and> P \<turnstile> Us [\<le>] Ts"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (Val v\<bullet>M(es))"
   and wt: "P,E,h,sh \<turnstile> Val v\<bullet>M(es) : T" by fact+
  have iconfs: "iconfs sh es" using iconf by simp
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix C D Ts Us pns body
    assume wte: "P,E,h,sh \<turnstile> Val v : Class C"
      and "P \<turnstile> C sees M,NonStatic:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "P,E,h,sh \<turnstile> es [:] Us" and "P \<turnstile> Us [\<le>] Ts"
    moreover have "P,E,h',sh' \<turnstile> Val v : Class C"
      using WTrt_hext_mono[OF wte reds_hext_incr[OF reds]] by auto
    moreover
    obtain Us' where "P,E,h',sh' \<turnstile> es' [:] Us' \<and> P \<turnstile> Us' [\<le>] Us"
      using IH[OF conf iconfs wtes] by blast
    ultimately show ?thesis by(blast intro:WTrtCall widens_trans)
  next
    fix Us
    assume null: "P,E,h,sh \<turnstile> Val v : NT" and wtes: "P,E,h,sh \<turnstile> es [:] Us"
    from null have "v = Null" by simp
    moreover
    obtain Us' where "P,E,h',sh' \<turnstile> es' [:] Us' \<and> P \<turnstile> Us' [\<le>] Us"
      using IH[OF conf iconfs wtes] by blast
    ultimately show ?thesis by(fastforce intro:WTrtCallNT)
  qed
next
  case (RedCall h a C fs M Ts T pns body D vs l sh b E T')
  have hp: "h a = Some(C,fs)"
   and "method": "P \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (pns,body) in D"
   and wt: "P,E,h,sh \<turnstile> addr a\<bullet>M(map Val vs) : T'" by fact+
  obtain Ts' where wtes: "P,E,h,sh \<turnstile> map Val vs [:] Ts'"
    and subs: "P \<turnstile> Ts' [\<le>] Ts" and T'isT: "T' = T"
    using wt "method" hp by (auto dest:sees_method_fun)
  from wtes subs have length_vs: "length vs = length Ts"
    by(fastforce simp:list_all2_iff dest!:WTrts_same_length)
  from sees_wf_mdecl[OF wf "method"] obtain T''
    where wtabody: "P,[this#pns [\<mapsto>] Class D#Ts] \<turnstile> body :: T''"
    and T''subT: "P \<turnstile> T'' \<le> T" and length_pns: "length pns = length Ts"
    by(fastforce simp:wf_mdecl_def simp del:map_upds_twist)
  from wtabody have "P,Map.empty(this#pns [\<mapsto>] Class D#Ts),h,sh \<turnstile> body : T''"
    by(rule WT_implies_WTrt)
  hence "P,E(this#pns [\<mapsto>] Class D#Ts),h,sh \<turnstile> body : T''"
    by(rule WTrt_env_mono) simp
  hence "P,E,h,sh \<turnstile> blocks(this#pns, Class D#Ts, Addr a#vs, body) : T''"
  using wtes subs hp sees_method_decl_above[OF "method"] length_vs length_pns
    by(fastforce simp add:wt_blocks rel_list_all2_Cons2)
  with T''subT T'isT show ?case by blast
next
  case RedCallNull thus ?case
    by(fastforce intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp: sconf_def hconf_def)
next
  case RedCallStatic then show ?case 
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError
      simp: sconf_def hconf_def)
next
  case (SCallParams es h l sh b es' h' l' sh' b' C M)
  have IH: "\<And>E Ts. \<lbrakk>P,E \<turnstile> (h,l,sh) \<surd>; iconfs sh es; P,E,h,sh \<turnstile> es [:] Ts\<rbrakk>
                 \<Longrightarrow> \<exists>Us. P,E,h',sh' \<turnstile> es' [:] Us \<and> P \<turnstile> Us [\<le>] Ts"
   and conf: "P,E \<turnstile> (h,l,sh) \<surd>" and iconf: "iconf sh (C\<bullet>\<^sub>sM(es))"
   and wt: "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sM(es) : T" by fact+
  have iconfs: "iconfs sh es" using iconf by simp
  from wt show ?case
  proof (rule WTrt_elim_cases)
    fix D Ts Us pns body sfs vs
    assume method: "P \<turnstile> C sees M,Static:Ts\<rightarrow>T = (pns,body) in D"
      and wtes: "P,E,h,sh \<turnstile> es [:] Us" and us: "P \<turnstile> Us [\<le>] Ts"
      and clinit: "M = clinit \<longrightarrow> sh D = \<lfloor>(sfs,Processing)\<rfloor> \<and> es = map Val vs"
    obtain Us' where es': "P,E,h',sh' \<turnstile> es' [:] Us'" and us': "P \<turnstile> Us' [\<le>] Us"
      using IH[OF conf iconfs wtes] by blast
    show ?thesis
    proof(cases "M = clinit")
      case True then show ?thesis using clinit SCallParams.hyps(1) by blast
    next
      case False
      then show ?thesis using es' method us us' by(blast intro:WTrtSCall widens_trans)
    qed
  qed
next
  case (RedSCall C M Ts T pns body D vs h l sh E T')
  have "method": "P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (pns,body) in D"
   and wt: "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sM(map Val vs) : T'" by fact+
  obtain Ts' where wtes: "P,E,h,sh \<turnstile> map Val vs [:] Ts'"
    and subs: "P \<turnstile> Ts' [\<le>] Ts" and T'isT: "T' = T"
    using wt "method" map_Val_eq by(auto dest:sees_method_fun)+
  from wtes subs have length_vs: "length vs = length Ts"
    by(fastforce simp:list_all2_iff dest!:WTrts_same_length)
  from sees_wf_mdecl[OF wf "method"] obtain T''
    where wtabody: "P,[pns [\<mapsto>] Ts] \<turnstile> body :: T''"
    and T''subT: "P \<turnstile> T'' \<le> T" and length_pns: "length pns = length Ts"
    by(fastforce simp:wf_mdecl_def simp del:map_upds_twist)
  from wtabody have "P,Map.empty(pns [\<mapsto>] Ts),h,sh \<turnstile> body : T''"
    by(rule WT_implies_WTrt)
  hence "P,E(pns [\<mapsto>] Ts),h,sh \<turnstile> body : T''"
    by(rule WTrt_env_mono) simp
  hence "P,E,h,sh \<turnstile> blocks(pns, Ts, vs, body) : T''"
  using wtes subs sees_method_decl_above[OF "method"] length_vs length_pns
    by(fastforce simp add:wt_blocks rel_list_all2_Cons2)
  with T''subT T'isT show ?case by blast
next
  case SCallInitDoneRed then show ?case by (meson widen_refl)
next
  case (SCallInitRed C F Ts t pns body D sh v h l E T)
  have "is_class P D" using SCallInitRed.hyps(1) by(rule sees_method_is_class')
  then have "P,E,h,sh \<turnstile> INIT D ([D],False) \<leftarrow> C\<bullet>\<^sub>sF(map Val v) : T \<and> P \<turnstile> T \<le> T"
    using SCallInitRed WTrtInit[OF SCallInitRed.prems(3)] by clarsimp
  then show ?case by(rule exI)
next
  case RedSCallNone then show ?case
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_NoSuchMethodError
      simp: sconf_def hconf_def)
next
  case RedSCallNonStatic then show ?case 
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_IncompatibleClassChangeError
      simp: sconf_def hconf_def)
next
  case BlockRedNone thus ?case
    by(auto simp del:fun_upd_apply)(fastforce simp:sconf_def lconf_def)
next
  case (BlockRedSome e h l V sh b e' h' l' sh' b' v T E Te)
  have red: "P \<turnstile> \<langle>e,(h,l(V:=None),sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l(V:=None),sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                   \<Longrightarrow> \<exists>T'. P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
   and Some: "l' V = Some v" and conf: "P,E \<turnstile> (h,l,sh) \<surd>"
   and iconf: "iconf sh {V:T; e}"
   and wt: "P,E,h,sh \<turnstile> {V:T; e} : Te" by fact+
  obtain Te' where IH': "P,E(V\<mapsto>T),h',sh' \<turnstile> e' : Te' \<and> P \<turnstile> Te' \<le> Te"
    using IH conf iconf wt by(fastforce simp:sconf_def lconf_def)
  have "P,h' \<turnstile> l' (:\<le>) E(V\<mapsto>T)" using conf wt
    by(fastforce intro:red_preserves_lconf[OF red] simp:sconf_def lconf_def)
  hence "P,h' \<turnstile> v :\<le> T" using Some by(fastforce simp:lconf_def)
  with IH' show ?case
    by(fastforce simp:sconf_def conf_def fun_upd_same simp del:fun_upd_apply)
next
  case (InitBlockRed e h l V v sh b e' h' l' sh' b' v' T E T')
  have red: "P \<turnstile> \<langle>e, (h,l(V\<mapsto>v),sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>"
   and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h,l(V\<mapsto>v),sh) \<surd>; iconf sh e; P,E,h,sh \<turnstile> e : T\<rbrakk>
                    \<Longrightarrow> \<exists>U. P,E,h',sh' \<turnstile> e' : U \<and> P \<turnstile> U \<le> T"
   and v': "l' V = Some v'" and conf: "P,E \<turnstile> (h,l,sh) \<surd>"
   and iconf: "iconf sh {V:T; V:=Val v;; e}"
   and wt: "P,E,h,sh \<turnstile> {V:T := Val v; e} : T'" by fact+
  from wt obtain T\<^sub>1 where wt\<^sub>1: "typeof\<^bsub>h\<^esub> v = Some T\<^sub>1"
    and T1subT: "P \<turnstile> T\<^sub>1 \<le> T" and wt\<^sub>2: "P,E(V\<mapsto>T),h,sh \<turnstile> e : T'" by auto
  have lconf\<^sub>2: "P,h \<turnstile> l(V\<mapsto>v) (:\<le>) E(V\<mapsto>T)" using conf wt\<^sub>1 T1subT
    by(simp add:sconf_def lconf_upd2 conf_def)
  have "\<exists>T\<^sub>1'. typeof\<^bsub>h'\<^esub> v' = Some T\<^sub>1' \<and> P \<turnstile> T\<^sub>1' \<le> T"
    using v' red_preserves_lconf[OF red wt\<^sub>2 lconf\<^sub>2]
    by(fastforce simp:lconf_def conf_def)
  with IH conf iconf lconf\<^sub>2 wt\<^sub>2 show ?case by (fastforce simp add:sconf_def)
next
  case (SeqRed e h l sh b e' h' l' sh' b' e\<^sub>2)
  then have val: "val_of e = None" by (simp add: val_no_step)
  show ?case
  proof(cases "lass_val_of e")
    case None
    then show ?thesis
      using SeqRed val by(auto elim: WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])
  next
    case (Some a)
    have "sh = sh'" using SeqRed lass_val_of_spec[OF Some] by auto
    then show ?thesis using SeqRed val Some
      by(auto intro: lass_val_of_iconf[OF Some] elim: WTrt_hext_mono[OF _ red_hext_incr])
  qed
next
  case CondRed thus ?case
    by auto (blast intro:WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])+
next
  case ThrowRed thus ?case
    by(auto simp:is_refT_def)(blast dest:widen_Class[THEN iffD1])+
next
  case RedThrowNull thus ?case
    by(fastforce intro: WTThrow[OF WTVal] elim!:typeof_NullPointer simp:sconf_def hconf_def)
next
  case TryRed thus ?case
    by auto (blast intro:widen_trans WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])
next
  case RedTryFail thus ?case
    by(fastforce intro: WTrtThrow[OF WTrtVal] simp:sconf_def hconf_def)
next
  case (ListRed1 e h l sh b e' h' l' sh' b' es)
    then have val: "val_of e = None" by(simp add: val_no_step)
    obtain U Us where Ts: "Ts = U # Us" using ListRed1 by auto
    then have nsub_RI: "\<not> sub_RIs es" and wts: "P,E,h,sh \<turnstile> es [:] Us" and wt: "P,E,h,sh \<turnstile> e : U"
     and IH: "\<And>E T. \<lbrakk>P,E \<turnstile> (h, l, sh) \<surd>; P,E,h,sh \<turnstile> e : T\<rbrakk> \<Longrightarrow> \<exists>T'. P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T"
      using ListRed1 val by auto
    obtain T' where
    "\<forall>E0 E1. (\<exists>T2. P,E1,h',sh' \<turnstile> e' : T2 \<and> P \<turnstile> T2 \<le> E0) = (P,E1,h',sh' \<turnstile> e' : T' E0 E1 \<and> P \<turnstile> T' E0 E1 \<le> E0)"
      by moura
    then have disj: "\<forall>E t. \<not> P,E \<turnstile> (h, l, sh) \<surd> \<or> \<not> P,E,h,sh \<turnstile> e : t \<or> P,E,h',sh' \<turnstile> e' : T' t E \<and> P \<turnstile> T' t E \<le> t"
      using IH by presburger
    have "P,E,h',sh' \<turnstile> es [:] Us"
      using nsub_RI wts wt by (metis (no_types) ListRed1.hyps(1) WTrts_hext_shext_mono red_hext_incr red_shext_incr)
    then have "\<exists>ts. (\<exists>t tsa. ts = t # tsa \<and> P,E,h',sh' \<turnstile> e' : t \<and> P,E,h',sh' \<turnstile> es [:] tsa) \<and> P \<turnstile> ts [\<le>] (U # Us)"
      using disj wt ListRed1.prems(1) by blast
    then show ?case using Ts by auto
next
  case ListRed2 thus ?case
    by(fastforce dest: hext_typeof_mono[OF reds_hext_incr])
next
  case (InitNoneRed sh C C' Cs e h l b)
  then have sh: "sh \<unlhd>\<^sub>s sh(C \<mapsto> (sblank P C, Prepared))" by(simp add: shext_def)
  have wt: "P,E,h,sh(C \<mapsto> (sblank P C, Prepared)) \<turnstile> INIT C' (C # Cs,False) \<leftarrow> e : T"
      using InitNoneRed WTrt_shext_mono[OF _ sh] by fastforce
  then show ?case by(rule_tac x = T in exI) (simp add: fun_upd_def)
next
  case (RedInitDone sh C sfs C' Cs e h l b)
  then have "P,E,h,sh \<turnstile> INIT C' (Cs,True) \<leftarrow> e : T" by auto (metis Nil_tl list.set_sel(2))
  then show ?case by(rule_tac x = T in exI) simp
next
  case (RedInitProcessing sh C sfs C' Cs e h l b)
  then have "P,E,h,sh \<turnstile> INIT C' (Cs,True) \<leftarrow> e : T" by auto (metis Nil_tl list.set_sel(2))+
  then show ?case by(rule_tac x = T in exI) simp
next
  case RedInitError then show ?case
    by(fastforce intro: WTrtThrow[OF WTrtVal] elim!: typeof_NoClassDefFoundError
      simp: sconf_def hconf_def)
next
  case (InitObjectRed sh C sfs sh' C' Cs e h l b)
  then have sh: "sh \<unlhd>\<^sub>s sh(Object \<mapsto> (sfs, Processing))" by(simp add: shext_def)
  have "P,E,h,sh' \<turnstile> INIT C' (C # Cs,True) \<leftarrow> e : T"
    using InitObjectRed WTrt_shext_mono[OF _ sh] by auto
  then show ?case by(rule_tac x = T in exI) (simp add: fun_upd_def)
next
  case (InitNonObjectSuperRed sh C sfs D fs ms sh' C' Cs e h l b)
  then have sh: "sh \<unlhd>\<^sub>s sh(C \<mapsto> (sfs, Processing))" by(simp add: shext_def)
  then have cd: "is_class P D" using InitNonObjectSuperRed class_wf wf wf_cdecl_supD by blast
  have sup': "supercls_lst P (C # Cs)" using InitNonObjectSuperRed.prems(3) by auto
  then have sup: "supercls_lst P (D # C # Cs)"
    using supercls_lst_app[of P C Cs D] subcls1I[OF InitNonObjectSuperRed.hyps(3,2)] by auto
  have "distinct (C # Cs)" using InitNonObjectSuperRed.prems(3) by auto
  then have dist: "distinct (D # C # Cs)"
    using wf_supercls_distinct_app[OF wf InitNonObjectSuperRed.hyps(2-3) sup'] by simp
  have "P,E,h,sh' \<turnstile> INIT C' (D # C # Cs,False) \<leftarrow> e : T"
    using InitNonObjectSuperRed WTrt_shext_mono[OF _ sh] cd sup dist by auto
  then show ?case by(rule_tac x = T in exI) simp
next
  case (RedInitRInit C' C Cs e' h l sh b E T)
  then obtain a sfs where C: "class P C = \<lfloor>a\<rfloor>" and proc: "sh C = \<lfloor>(sfs, Processing)\<rfloor>"
    using WTrtInit by(auto simp: is_class_def)
  then have T': "P,E,h,sh \<turnstile> C\<bullet>\<^sub>sclinit([]) : Void" using wf_types_clinit[OF wf C] by simp
  have "P,E,h,sh \<turnstile> RI (C,C\<bullet>\<^sub>sclinit([])) ; Cs \<leftarrow> e' : T"
    using RedInitRInit by(auto intro: T')
  then show ?case by(rule_tac x = T in exI) simp
next
  case (RInitRed e h l sh b e' h' l' sh' b' C Cs e\<^sub>0 E T)
  then have "(\<And>E T. P,E \<turnstile> (h, l, sh) \<surd> \<Longrightarrow> P,E,h,sh \<turnstile> e : T \<Longrightarrow> \<exists>T'. P,E,h',sh' \<turnstile> e' : T' \<and> P \<turnstile> T' \<le> T)"
    by auto
  then have "\<exists>T'. P,E,h',sh' \<turnstile> e' : T'" using RInitRed by blast
  then obtain T' where e': "P,E,h',sh' \<turnstile> e' : T'" by auto
  have wt\<^sub>0: "P,E,h',sh' \<turnstile> e\<^sub>0 : T"
   using RInitRed by simp (auto intro: WTrt_hext_shext_mono[OF _ red_hext_incr red_shext_incr])
  have nip: "\<forall>C' \<in> set (C#Cs). not_init C' e' \<and> (\<exists>sfs. sh' C' = \<lfloor>(sfs, Processing)\<rfloor>)"
   using RInitRed red_proc_pres[OF wf_prog_wwf_prog[OF wf]] by auto
  have shC: "\<exists>sfs. sh' C = \<lfloor>(sfs, Processing)\<rfloor> \<or> sh' C = \<lfloor>(sfs, Error)\<rfloor> \<and> e' = THROW NoClassDefFoundError"
    using RInitRed red_proc_pres[OF wf_prog_wwf_prog[OF wf] RInitRed.hyps(1)] by blast
  have "P,E,h',sh' \<turnstile> RI (C,e') ; Cs \<leftarrow> e\<^sub>0 : T" using RInitRed e' wt\<^sub>0 nip shC by auto
  then show ?case by(rule_tac x = T in exI) simp
next
  case (RedRInit sh C sfs i sh' C' Cs v e h l b)
  then have sh: "sh \<unlhd>\<^sub>s sh(C \<mapsto> (sfs, Done))" by(auto simp: shext_def)
  have wt: "P,E,h,sh(C \<mapsto> (sfs, Done)) \<turnstile> e : T"
    using RedRInit WTrt_shext_mono[OF _ sh] by auto
  have shC: "\<forall>C' \<in> set(tl Cs). \<exists>sfs. sh C' = \<lfloor>(sfs, Processing)\<rfloor>" using RedRInit by(cases Cs, auto)
  have "P,E,h,sh' \<turnstile> INIT C' (Cs,True) \<leftarrow> e : T" using RedRInit wt shC by(cases Cs, auto)
  then show ?case by(rule_tac x = T in exI) simp
next
  case (SCallThrowParams es vs e es' C M h l sh b)
    then show ?case using map_Val_nthrow_neq[of _ vs e es'] by fastforce
next
  case (RInitInitThrow sh C sfs i sh' a D Cs e h l b)
  then have sh: "sh \<unlhd>\<^sub>s sh(C \<mapsto> (sfs, Error))" by(auto simp: shext_def)
  have wt: "P,E,h,sh(C \<mapsto> (sfs, Error)) \<turnstile> e : T"
   using RInitInitThrow WTrt_shext_mono[OF _ sh] by clarsimp
  then have "P,E,h,sh' \<turnstile> RI (D,Throw a) ; Cs \<leftarrow> e : T" using RInitInitThrow by auto
  then show ?case by(rule_tac x = T in exI) simp
qed fastforce+ (* esp all Throw propagation rules except RInitInit are dealt with here *)
(*>*)


corollary subject_reduction:
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>; P,E \<turnstile> s \<surd>; iconf (shp s) e; P,E,hp s,shp s \<turnstile> e:T \<rbrakk>
  \<Longrightarrow> \<exists>T'. P,E,hp s',shp s' \<turnstile> e':T' \<and> P \<turnstile> T' \<le> T"
(*<*)by(cases s, cases s', fastforce dest:subject_reduction2)(*>*)

corollary subjects_reduction:
  "\<lbrakk> wf_J_prog P; P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>] \<langle>es',s',b'\<rangle>; P,E \<turnstile> s \<surd>; iconfs (shp s) es; P,E,hp s,shp s \<turnstile> es[:]Ts \<rbrakk>
  \<Longrightarrow> \<exists>Ts'. P,E,hp s',shp s' \<turnstile> es'[:]Ts' \<and> P \<turnstile> Ts' [\<le>] Ts"
(*<*)by(cases s, cases s', fastforce dest:subjects_reduction2)(*>*)


subsection \<open> Lifting to @{text"\<rightarrow>*"} \<close>

text\<open> Now all these preservation lemmas are first lifted to the transitive
closure \dots \<close>

lemma Red_preserves_sconf:
assumes wf: "wf_J_prog P" and Red: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "\<And>T. \<lbrakk> P,E,hp s,shp s \<turnstile> e : T; iconf (shp s) e; P,E \<turnstile> s \<surd> \<rbrakk> \<Longrightarrow> P,E \<turnstile> s' \<surd>"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step e s b e' s' b')
  obtain h l sh h' l' sh' where s:"s = (h,l,sh)" and s':"s' = (h',l',sh')"
    by(cases s, cases s')
  then have "P \<turnstile> \<langle>e,(h,l,sh),b\<rangle> \<rightarrow> \<langle>e',(h',l',sh'),b'\<rangle>" using step.hyps(1) by simp
  then have iconf': "iconf (shp s') e'" using red_preserves_iconf[OF wf_prog_wwf_prog[OF wf]]
    step.prems(2) s s' by simp
  thus ?case using step
    by(blast intro:red_preserves_sconf dest: subject_reduction[OF wf])
qed
(*>*)

lemma Red_preserves_iconf:
assumes wf: "wwf_J_prog P" and Red: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "iconf (shp s) e \<Longrightarrow> iconf (shp s') e'"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step e s b e' s' b')
  thus ?case using wf step by(cases s, cases s', simp) (blast intro:red_preserves_iconf)
qed
(*>*)

lemma Reds_preserves_iconf:
assumes wf: "wwf_J_prog P" and Red: "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle>"
shows "iconfs (shp s) es \<Longrightarrow> iconfs (shp s') es'"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step e s b e' s' b')
  thus ?case using wf step by(cases s, cases s', simp) (blast intro:reds_preserves_iconf)
qed
(*>*)

lemma Red_preserves_bconf:
assumes wf: "wwf_J_prog P" and Red: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "iconf (shp s) e \<Longrightarrow> P,(shp s) \<turnstile>\<^sub>b (e,b) \<surd> \<Longrightarrow> P,(shp s') \<turnstile>\<^sub>b (e'::expr,b') \<surd>"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step e s1 b e' s2 b')
  then have "iconf (shp s2) e'" using step red_preserves_iconf[OF wf]
   by(cases s1, cases s2) auto
  thus ?case using step by(cases s1, cases s2, simp) (blast intro:red_preserves_bconf)
qed
(*>*)

lemma Reds_preserves_bconf:
assumes wf: "wwf_J_prog P" and Red: "P \<turnstile> \<langle>es,s,b\<rangle> [\<rightarrow>]* \<langle>es',s',b'\<rangle>"
shows "iconfs (shp s) es \<Longrightarrow> P,(shp s) \<turnstile>\<^sub>b (es,b) \<surd> \<Longrightarrow> P,(shp s') \<turnstile>\<^sub>b (es'::expr list,b') \<surd>"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl show ?case by fact
next
  case (step es s1 b es' s2 b')
  then have "iconfs (shp s2) es'" using step reds_preserves_iconf[OF wf]
   by(cases s1, cases s2) auto
  thus ?case using step by(cases s1, cases s2, simp) (blast intro:reds_preserves_bconf)
qed
(*>*)

lemma Red_preserves_defass:
assumes wf: "wf_J_prog P" and reds: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "\<D> e \<lfloor>dom(lcl s)\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom(lcl s')\<rfloor>"
using reds
proof (induct rule:converse_rtrancl_induct3)
  case refl thus ?case .
next
  case (step e s b e' s' b') thus ?case
    by(cases s,cases s')(auto dest:red_preserves_defass[OF wf])
qed


lemma Red_preserves_type:
assumes wf: "wf_J_prog P" and Red: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "!!T. \<lbrakk> P,E \<turnstile> s\<surd>; iconf (shp s) e; P,E,hp s,shp s \<turnstile> e:T \<rbrakk>
    \<Longrightarrow> \<exists>T'. P \<turnstile> T' \<le> T \<and> P,E,hp s',shp s' \<turnstile> e':T'"
(*<*)
using Red
proof (induct rule:converse_rtrancl_induct3)
  case refl thus ?case by blast
next
  case step thus ?case
    by(blast intro:widen_trans red_preserves_sconf Red_preserves_iconf[OF wf_prog_wwf_prog[OF wf]]
             dest:subject_reduction[OF wf])
qed
(*>*)


subsection "The final polish"

text\<open> The above preservation lemmas are now combined and packed nicely. \<close>

definition wf_config :: "J_prog \<Rightarrow> env \<Rightarrow> state \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"   ("_,_,_ \<turnstile> _ : _ \<surd>"   [51,0,0,0,0]50)
where
  "P,E,s \<turnstile> e:T \<surd>  \<equiv>  P,E \<turnstile> s \<surd> \<and> iconf (shp s) e \<and> P,E,hp s,shp s \<turnstile> e:T"

theorem Subject_reduction: assumes wf: "wf_J_prog P"
shows "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle> \<Longrightarrow> P,E,s \<turnstile> e : T \<surd>
       \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e' : T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
by(cases s, cases s')
  (force simp: wf_config_def
         elim:red_preserves_sconf red_preserves_iconf[OF wf_prog_wwf_prog[OF wf]]
         dest:subject_reduction[OF wf])
(*>*)


theorem Subject_reductions:
assumes wf: "wf_J_prog P" and reds: "P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>"
shows "\<And>T. P,E,s \<turnstile> e:T \<surd> \<Longrightarrow> \<exists>T'. P,E,s' \<turnstile> e':T' \<surd> \<and> P \<turnstile> T' \<le> T"
(*<*)
using reds
proof (induct rule:converse_rtrancl_induct3)
  case refl thus ?case by blast
next
  case step thus ?case
    by(blast dest:Subject_reduction[OF wf] intro:widen_trans)
qed
(*>*)


corollary Progress: assumes wf: "wf_J_prog P"
shows "\<lbrakk> P,E,s  \<turnstile> e : T \<surd>; \<D> e \<lfloor>dom(lcl s)\<rfloor>; P,shp s \<turnstile>\<^sub>b (e,b) \<surd>; \<not> final e \<rbrakk>
   \<Longrightarrow> \<exists>e' s' b'. P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow> \<langle>e',s',b'\<rangle>"
(*<*)
using progress[OF wf_prog_wwf_prog[OF wf]]
by(cases b) (auto simp:wf_config_def sconf_def)
(*>*)

corollary TypeSafety:
  "\<lbrakk> wf_J_prog P; P,E \<turnstile> s \<surd>; P,E \<turnstile> e::T; \<D> e \<lfloor>dom(lcl s)\<rfloor>;
     iconf (shp s) e; P,(shp s) \<turnstile>\<^sub>b (e,b) \<surd>;
     P \<turnstile> \<langle>e,s,b\<rangle> \<rightarrow>* \<langle>e',s',b'\<rangle>; \<not>(\<exists>e'' s'' b''. P \<turnstile> \<langle>e',s',b'\<rangle> \<rightarrow> \<langle>e'',s'',b''\<rangle>) \<rbrakk>
 \<Longrightarrow> (\<exists>v. e' = Val v \<and> P,hp s' \<turnstile> v :\<le> T) \<or>
      (\<exists>a. e' = Throw a \<and> a \<in> dom(hp s'))"
(*<*)
apply(subgoal_tac "wwf_J_prog P")
 prefer 2 apply(rule wf_prog_wwf_prog, simp)
apply(subgoal_tac " P,E,s \<turnstile> e:T \<surd>")
 prefer 2
 apply(fastforce simp:wf_config_def dest:WT_implies_WTrt)
apply(frule (2) Subject_reductions)
apply(erule exE conjE)+
apply(frule (2) Red_preserves_defass)
apply(frule (3) Red_preserves_bconf)
apply(subgoal_tac "final e'")
 prefer 2
 apply(blast dest: Progress)
apply (fastforce simp:wf_config_def final_def conf_def dest: Progress)
done
(*>*)


end
