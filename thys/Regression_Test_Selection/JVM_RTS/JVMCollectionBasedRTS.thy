(* File: RTS/JVM_RTS/JVMCollectionBasedRTS.thy *)
(* Author: Susannah Mansky, UIUC 2020 *)
(* Proof of safety of certain collection based RTS algorithms for Jinja JVM *)

section "Instantiating @{term CollectionBasedRTS} with Jinja JVM"

theory JVMCollectionBasedRTS
imports "../Common/CollectionBasedRTS" JVMCollectionSemantics
   JinjaDCI.BVSpecTypeSafe "../JinjaSuppl/JVMExecStepInductive"

begin

lemma eq_equiv[simp]: "equiv UNIV {(x, y). x = y}"
by(simp add: equiv_def refl_on_def sym_def trans_def)

(**********************************************)
subsection \<open> Some @{text "classes_above"} lemmas \<close>
(* here because they require ClassAdd/StartProg *)

lemma start_prog_classes_above_Start:
 "classes_above (start_prog P C M) Start = {Object,Start}"
using start_prog_Start_super[of C M P] subcls1_confluent by auto

lemma class_add_classes_above:
assumes ns: "\<not> is_class P C" and "\<not>P \<turnstile> D \<preceq>\<^sup>* C"
shows "classes_above (class_add P (C, cdec)) D = classes_above P D"
using assms by(auto intro: class_add_subcls class_add_subcls_rev)

lemma class_add_classes_above_xcpts:
assumes ns: "\<not> is_class P C"
 and ncp: "\<And>D. D \<in> sys_xcpts \<Longrightarrow> \<not>P \<turnstile> D \<preceq>\<^sup>* C"
shows "classes_above_xcpts (class_add P (C, cdec)) = classes_above_xcpts P"
using assms class_add_classes_above by simp

(*********)
subsection "JVM next-step lemmas for initialization calling"

lemma JVM_New_next_step:
assumes step: "\<sigma>' \<in> JVMsmall P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = New C"
 and nDone: "\<not>(\<exists>sfs i. sheap \<sigma> C = Some(sfs,i) \<and> i = Done)"
 and ics: "ics_of(hd(frames_of \<sigma>)) = No_ics"
shows "ics_of (hd(frames_of \<sigma>')) = Calling C [] \<and> sheap \<sigma> = sheap \<sigma>' \<and> \<sigma>' \<notin> JVMendset"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then obtain f1 frs1 where frs: "frs=f1#frs1" using nend by(cases frs, simp_all add: JVMendset_def)
  then obtain stk loc C' M' pc ics where f1:"f1=(stk,loc,C',M',pc,ics)" by(cases f1)
  have xp: "xp = None" using \<sigma> nend by(simp add: JVMendset_def)
  obtain xp' h' frs' sh' where \<sigma>': "\<sigma>'=(xp',h',frs',sh')" by(cases \<sigma>')
  have "ics_of (hd frs') = Calling C [] \<and> sh = sh' \<and> frs' \<noteq> [] \<and> xp' = None"
  proof(cases "sh C")
    case None then show ?thesis using \<sigma>' xp f1 frs \<sigma> assms by auto
  next
    case (Some a)
    then obtain sfs i where a: "a=(sfs,i)" by(cases a)
    then have nDone': "i \<noteq> Done" using nDone Some f1 frs \<sigma> by simp
    show ?thesis using a Some \<sigma>' xp f1 frs \<sigma> assms by(auto split: init_state.splits)
  qed
  then show ?thesis using ics \<sigma> \<sigma>' by(cases frs', auto simp: JVMendset_def)
qed

lemma JVM_Getstatic_next_step:
assumes step: "\<sigma>' \<in> JVMsmall P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Getstatic C F D"
 and fC: "P \<turnstile> C has F,Static:t in D"
 and nDone: "\<not>(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)"
 and ics: "ics_of(hd(frames_of \<sigma>)) = No_ics"
shows "ics_of (hd(frames_of \<sigma>')) = Calling D [] \<and> sheap \<sigma> = sheap \<sigma>' \<and> \<sigma>' \<notin> JVMendset"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then obtain f1 frs1 where frs: "frs=f1#frs1" using nend by(cases frs, simp_all add: JVMendset_def)
  then obtain stk loc C' M' pc ics where f1:"f1=(stk,loc,C',M',pc,ics)" by(cases f1)
  have xp: "xp = None" using \<sigma> nend by(simp add: JVMendset_def)
  obtain xp' h' frs' sh' where \<sigma>': "\<sigma>'=(xp',h',frs',sh')" by(cases \<sigma>')
  have ex': "\<exists>t b. P \<turnstile> C has F,b:t in D" using fC by auto
  have field: "\<exists>t. field P D F = (D,Static,t)"
    using fC field_def2 has_field_idemp has_field_sees by blast
  have nCalled': "\<forall>Cs. ics \<noteq> Called Cs" using ics f1 frs \<sigma> by simp
  have "ics_of (hd frs') = Calling D [] \<and> sh = sh' \<and> frs' \<noteq> [] \<and> xp' = None"
  proof(cases "sh D")
    case None then show ?thesis using field ex' \<sigma>' xp f1 frs \<sigma> assms by auto
  next
    case (Some a)
    then obtain sfs i where a: "a=(sfs,i)" by(cases a)
    show ?thesis using field ex' a Some \<sigma>' xp f1 frs \<sigma> assms by(auto split: init_state.splits)
  qed
  then show ?thesis using ics \<sigma> \<sigma>' by(auto simp: JVMendset_def)
qed

lemma JVM_Putstatic_next_step:
assumes step: "\<sigma>' \<in> JVMsmall P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Putstatic C F D"
 and fC: "P \<turnstile> C has F,Static:t in D"
 and nDone: "\<not>(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)"
 and ics: "ics_of(hd(frames_of \<sigma>)) = No_ics"
shows "ics_of (hd(frames_of \<sigma>')) = Calling D [] \<and> sheap \<sigma> = sheap \<sigma>' \<and> \<sigma>' \<notin> JVMendset"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then obtain f1 frs1 where frs: "frs=f1#frs1" using nend by(cases frs, simp_all add: JVMendset_def)
  then obtain stk loc C' M' pc ics where f1:"f1=(stk,loc,C',M',pc,ics)" by(cases f1)
  have xp: "xp = None" using \<sigma> nend by(simp add: JVMendset_def)
  obtain xp' h' frs' sh' where \<sigma>': "\<sigma>'=(xp',h',frs',sh')" by(cases \<sigma>')
  have ex': "\<exists>t b. P \<turnstile> C has F,b:t in D" using fC by auto
  have field: "field P D F = (D,Static,t)"
    using fC field_def2 has_field_idemp has_field_sees by blast
  have ics': "ics_of (hd frs') = Calling D [] \<and> sh = sh' \<and> frs' \<noteq> [] \<and> xp' = None"
  proof(cases "sh D")
    case None then show ?thesis using field ex' \<sigma>' xp f1 frs \<sigma> assms by auto
  next
    case (Some a)
    then obtain sfs i where a: "a=(sfs,i)" by(cases a)
    show ?thesis using field ex' a Some \<sigma>' xp f1 frs \<sigma> assms by(auto split: init_state.splits)
  qed
  then show ?thesis using ics \<sigma> \<sigma>' by(auto simp: JVMendset_def)
qed

lemma JVM_Invokestatic_next_step:
assumes step: "\<sigma>' \<in> JVMsmall P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Invokestatic C M n"
 and mC: "P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D"
 and nDone: "\<not>(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)"
 and ics: "ics_of(hd(frames_of \<sigma>)) = No_ics"
shows "ics_of (hd(frames_of \<sigma>')) = Calling D [] \<and> sheap \<sigma> = sheap \<sigma>' \<and> \<sigma>' \<notin> JVMendset"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then obtain f1 frs1 where frs: "frs=f1#frs1" using nend by(cases frs, simp_all add: JVMendset_def)
  then obtain stk loc C' M' pc ics where f1:"f1=(stk,loc,C',M',pc,ics)" by(cases f1)
  have xp: "xp = None" using \<sigma> nend by(simp add: JVMendset_def)
  obtain xp' h' frs' sh' where \<sigma>': "\<sigma>'=(xp',h',frs',sh')" by(cases \<sigma>')
  have ex': "\<exists>Ts T m D b. P \<turnstile> C sees M,b:Ts \<rightarrow> T = m in D" using mC by fastforce
  have method: "\<exists>m. method P C M = (D,Static,m)" using mC by(cases m, auto)
  have ics': "ics_of (hd frs') = Calling D [] \<and> sh = sh' \<and> frs' \<noteq> [] \<and> xp' = None"
  proof(cases "sh D")
    case None then show ?thesis using method ex' \<sigma>' xp f1 frs \<sigma> assms by auto
  next
    case (Some a)
    then obtain sfs i where a: "a=(sfs,i)" by(cases a)
    then have nDone': "i \<noteq> Done" using nDone Some f1 frs \<sigma> by simp
    show ?thesis using method ex' a Some \<sigma>' xp f1 frs \<sigma> assms by(auto split: init_state.splits)
  qed
  then show ?thesis using ics \<sigma> \<sigma>' by(auto simp: JVMendset_def)
qed

(***********************************************)
subsection "Definitions"

definition main :: "string" where "main = ''main''"
definition Test :: "string" where "Test = ''Test''"
definition test_oracle :: "string" where "test_oracle = ''oracle''"

type_synonym jvm_class = "jvm_method cdecl"
type_synonym jvm_prog_out = "jvm_state \<times> cname set"

text "A deselection algorithm based on classes that have changed from
 @{text P1} to @{text P2}:"
primrec jvm_deselect :: "jvm_prog \<Rightarrow> jvm_prog_out \<Rightarrow> jvm_prog \<Rightarrow> bool" where
"jvm_deselect P1 (\<sigma>, cset) P2 = (cset \<inter> (classes_changed P1 P2) = {})"

definition jvm_progs :: "jvm_prog set" where
"jvm_progs \<equiv> {P. wf_jvm_prog P \<and> \<not>is_class P Start \<and> \<not>is_class P Test
             \<and> (\<forall>b' Ts' T' m' D'. P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'
                                            \<longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void) }"

definition jvm_tests :: "jvm_class set" where
"jvm_tests = {t. fst t = Test
 \<and> (\<forall>P \<in> jvm_progs. wf_jvm_prog (t#P) \<and> (\<exists>m. t#P \<turnstile> Test sees main,Static: [] \<rightarrow> Void = m in Test)) }"

abbreviation jvm_make_test_prog :: "jvm_prog \<Rightarrow> jvm_class \<Rightarrow> jvm_prog" where
"jvm_make_test_prog P t \<equiv> start_prog (t#P) (fst t) main"

declare jvm_progs_def [simp]
declare jvm_tests_def [simp]

(*****************************************************************************************)
subsection "Definition lemmas"

lemma jvm_progs_tests_nStart:
assumes P: "P \<in> jvm_progs" and t: "t \<in> jvm_tests"
shows "\<not>is_class (t#P) Start"
using assms by(simp add: is_class_def class_def Start_def Test_def)

lemma jvm_make_test_prog_classes_above_xcpts:
assumes P: "P \<in> jvm_progs" and t: "t \<in> jvm_tests"
shows "classes_above_xcpts (jvm_make_test_prog P t) = classes_above_xcpts P"
proof -
  have nS: "\<not>is_class (t#P) Start" by(rule jvm_progs_tests_nStart[OF P t])
  from P have nT: "\<not>is_class P Test" by simp
  from P t have "wf_syscls (t#P) \<and> wf_syscls P"
    by(simp add: wf_jvm_prog_def wf_jvm_prog_phi_def wf_prog_def)

  then have [simp]: "\<And>D. D \<in> sys_xcpts \<Longrightarrow> is_class (t#P) D \<and> is_class P D"
    by(cases t, auto simp: wf_syscls_def is_class_def class_def dest!: weak_map_of_SomeI)
  from wf_nclass_nsub[OF _ _ nS] P t have nspS: "\<And>D. D \<in> sys_xcpts \<Longrightarrow> \<not>(t#P) \<turnstile> D \<preceq>\<^sup>* Start"
    by(auto simp: wf_jvm_prog_def wf_jvm_prog_phi_def)
  from wf_nclass_nsub[OF _ _ nT] P have nspT: "\<And>D. D \<in> sys_xcpts \<Longrightarrow> \<not>P \<turnstile> D \<preceq>\<^sup>* Test"
    by(auto simp: wf_jvm_prog_def wf_jvm_prog_phi_def)

  from class_add_classes_above_xcpts[where P="t#P" and C=Start, OF nS nspS]
  have "classes_above_xcpts (jvm_make_test_prog P t) = classes_above_xcpts (t#P)" by simp
  also from class_add_classes_above_xcpts[where P=P and C=Test, OF nT nspT] t
  have "\<dots> = classes_above_xcpts P" by(cases t, simp)
  finally show ?thesis by simp
qed

lemma jvm_make_test_prog_sees_Test_main:
assumes P: "P \<in> jvm_progs" and t: "t \<in> jvm_tests"
shows "\<exists>m. jvm_make_test_prog P t \<turnstile> Test sees main, Static :  []\<rightarrow>Void = m in Test"
proof -
  let ?P = "jvm_make_test_prog P t"
  from P t obtain m where
    meth: "t#P \<turnstile> Test sees main,Static:[] \<rightarrow> Void = m in Test" and
    nstart: "\<not> is_class (t # P) Start"
   by(auto simp: is_class_def class_def Start_def Test_def)
  from class_add_sees_method[OF meth nstart] show ?thesis by fastforce
qed

(************************************************)
subsection "Naive RTS algorithm"

subsubsection "Definitions"

fun jvm_naive_out :: "jvm_prog \<Rightarrow> jvm_class \<Rightarrow> jvm_prog_out set" where
"jvm_naive_out P t = JVMNaiveCollectionSemantics.cbig (jvm_make_test_prog P t) (start_state (t#P))"

abbreviation jvm_naive_collect_start :: "jvm_prog \<Rightarrow> cname set" where
"jvm_naive_collect_start P \<equiv> {}"

lemma jvm_naive_out_xcpts_collected:
assumes "o1 \<in> jvm_naive_out P t"
shows "classes_above_xcpts (start_prog (t # P) (fst t) main) \<subseteq> snd o1"
using assms
proof -
  obtain \<sigma>' coll' where "o1 = (\<sigma>', coll')" and
    cbig: "(\<sigma>', coll') \<in> JVMNaiveCollectionSemantics.cbig (start_prog (t#P) (fst t) main) (start_state (t#P))"
   using assms by(cases o1, simp)
  with JVMNaiveCollectionSemantics.cbig_stepD[OF cbig start_state_nend]
  show ?thesis by(auto simp: JVMNaiveCollectionSemantics.csmall_def start_state_def)
qed

(***********************************************************)
subsubsection "Naive algorithm correctness"

text "We start with correctness over @{term exec_instr}, then all the
 functions/pieces that are used by naive @{term csmall} (that is, pieces
 used by @{term exec} - such as which frames are used based on @{term ics}
 - and all functions used by the collection function). We then prove that
 @{term csmall} is existence safe, extend this result to @{term cbig}, and
 finally prove the @{term existence_safe} statement over the locale pieces."

\<comment> \<open> if collected classes unchanged, @{term exec_instr} unchanged \<close>
lemma ncollect_exec_instr:
assumes "JVMinstr_ncollect P i h stk \<inter> classes_changed P P' = {}"
  and above_C: "classes_above P C \<inter> classes_changed P P' = {}"
  and ics: "ics = Called [] \<or> ics = No_ics"
  and i: "i = instrs_of P C M ! pc"
shows "exec_instr i P h stk loc C M pc ics frs sh = exec_instr i P' h stk loc C M pc ics frs sh"
using assms proof(cases i)
  case (New C1) then show ?thesis using assms classes_above_blank[of C1 P P']
    by(auto split: init_state.splits option.splits)
next
  case (Getfield F1 C1) show ?thesis
  proof(cases "hd stk = Null")
    case True then show ?thesis using Getfield assms by simp
  next
    case False
    let ?D = "(cname_of h (the_Addr (hd stk)))"
    have D: "classes_above P ?D \<inter> classes_changed P P' = {}"
      using False Getfield assms by simp
    show ?thesis
    proof(cases "\<exists>b t. P \<turnstile> ?D has F1,b:t in C1")
      case True
      then obtain b1 t1 where "P \<turnstile> ?D has F1,b1:t1 in C1" by auto
      then have has: "P' \<turnstile> ?D has F1,b1:t1 in C1"
       using Getfield assms classes_above_has_field[OF D] by auto
      have "P \<turnstile> ?D \<preceq>\<^sup>* C1" using has_field_decl_above True by auto
      then have "classes_above P C1 \<subseteq> classes_above P ?D" by(rule classes_above_subcls_subset)
      then have C1: "classes_above P C1 \<inter> classes_changed P P' = {}" using D by auto
      then show ?thesis using has True Getfield assms classes_above_field[of C1 P P' F1]
        by(cases "field P' C1 F1", cases "the (h (the_Addr (hd stk)))", auto)
    next
      case nex: False
      then have "\<nexists>b t. P' \<turnstile> ?D has F1,b:t in C1"
       using False Getfield assms
         classes_above_has_field2[where C="?D" and P=P and P'=P' and F=F1 and C'=C1]
        by auto
      then show ?thesis using nex Getfield assms classes_above_field[of C1 P P' F1]
        by(cases "field P' C1 F1", cases "the (h (the_Addr (hd stk)))", auto)
    qed
  qed
next
  case (Getstatic C1 F1 D1)
  then have C1: "classes_above P C1 \<inter> classes_changed P P' = {}" using assms by auto
  show ?thesis
  proof(cases "\<exists>b t. P \<turnstile> C1 has F1,b:t in D1")
    case True
    then obtain b t where meth: "P \<turnstile> C1 has F1,b:t in D1" by auto
    then have "P \<turnstile> C1 \<preceq>\<^sup>* D1" by(rule has_field_decl_above)
    then have D1: "classes_above P D1 \<inter> classes_changed P P' = {}"
      using C1 rtrancl_trans by fastforce
    have "P' \<turnstile> C1 has F1,b:t in D1"
     using meth Getstatic assms classes_above_has_field[OF C1] by auto
    then show ?thesis using True D1 Getstatic assms classes_above_field[of D1 P P' F1]
      by(cases "field P' D1 F1", auto)
  next
    case False
    then have "\<nexists>b t. P' \<turnstile> C1 has F1,b:t in D1"
     using Getstatic assms
       classes_above_has_field2[where C=C1 and P=P and P'=P' and F=F1 and C'=D1]
      by auto
    then show ?thesis using False Getstatic assms
      by(cases "field P' D1 F1", auto)
  qed
next
  case (Putfield F1 C1) show ?thesis
  proof(cases "hd(tl stk) = Null")
    case True then show ?thesis using Putfield assms by simp
  next
    case False
    let ?D = "(cname_of h (the_Addr (hd (tl stk))))"
    have D: "classes_above P ?D \<inter> classes_changed P P' = {}" using False Putfield assms by simp
    show ?thesis
    proof(cases "\<exists>b t. P \<turnstile> ?D has F1,b:t in C1")
      case True
      then obtain b1 t1 where "P \<turnstile> ?D has F1,b1:t1 in C1" by auto
      then have has: "P' \<turnstile> ?D has F1,b1:t1 in C1"
       using Putfield assms classes_above_has_field[OF D] by auto
      have "P \<turnstile> ?D \<preceq>\<^sup>* C1" using has_field_decl_above True by auto
      then have "classes_above P C1 \<subseteq> classes_above P ?D" by(rule classes_above_subcls_subset)
      then have C1: "classes_above P C1 \<inter> classes_changed P P' = {}" using D by auto
      then show ?thesis using has True Putfield assms classes_above_field[of C1 P P' F1]
        by(cases "field P' C1 F1", cases "the (h (the_Addr (hd (tl stk))))", auto)
    next
      case nex: False
      then have "\<nexists>b t. P' \<turnstile> ?D has F1,b:t in C1"
       using False Putfield assms
         classes_above_has_field2[where C="?D" and P=P and P'=P' and F=F1 and C'=C1]
        by auto
      then show ?thesis using nex Putfield assms classes_above_field[of C1 P P' F1]
        by(cases "field P' C1 F1", cases "the (h (the_Addr (hd (tl stk))))", auto)
    qed
  qed
next
  case (Putstatic C1 F1 D1)
  then have C1: "classes_above P C1 \<inter> classes_changed P P' = {}" using Putstatic assms by auto
  show ?thesis
  proof(cases "\<exists>b t. P \<turnstile> C1 has F1,b:t in D1")
    case True
    then obtain b t where meth: "P \<turnstile> C1 has F1,b:t in D1" by auto
    then have "P \<turnstile> C1 \<preceq>\<^sup>* D1" by(rule has_field_decl_above)
    then have D1: "classes_above P D1 \<inter> classes_changed P P' = {}"
      using C1 rtrancl_trans by fastforce
    then have "P' \<turnstile> C1 has F1,b:t in D1"
     using meth Putstatic assms classes_above_has_field[OF C1] by auto
    then show ?thesis using True D1 Putstatic assms classes_above_field[of D1 P P' F1]
      by(cases "field P' D1 F1", auto)
  next
    case False
    then have "\<nexists>b t. P' \<turnstile> C1 has F1,b:t in D1"
     using Putstatic assms classes_above_has_field2[where C=C1 and P=P and P'=P' and F=F1 and C'=D1]
      by auto
    then show ?thesis using False Putstatic assms
      by(cases "field P' D1 F1", auto)
  qed
next
  case (Checkcast C1)
  then show ?thesis using assms
  proof(cases "hd stk = Null")
    case False then show ?thesis
     using Checkcast assms classes_above_subcls classes_above_subcls2
      by(simp add: cast_ok_def) blast
  qed(simp add: cast_ok_def)
next
  case (Invoke M n)
  let ?C = "cname_of h (the_Addr (stk ! n))"
  show ?thesis
  proof(cases "stk ! n = Null")
    case True then show ?thesis using Invoke assms by simp
  next
    case False
    then have above: "classes_above P ?C \<inter> classes_changed P P' = {}"
      using Invoke assms by simp
    obtain D b Ts T mxs mxl ins xt where meth: "method P' ?C M = (D,b,Ts,T,mxs,mxl,ins,xt)"
      by(cases "method P' ?C M", clarsimp)
    have meq: "method P ?C M = method P' ?C M"
     using classes_above_method[OF above] by simp
    then show ?thesis
    proof(cases "\<exists>Ts T m D b. P \<turnstile> ?C sees M,b:Ts \<rightarrow> T = m in D")
      case nex: False
      then have "\<not>(\<exists>Ts T m D b. P' \<turnstile> ?C sees M,b:Ts \<rightarrow> T = m in D)"
        using classes_above_sees_method2[OF above, of M] by clarsimp
      then show ?thesis using nex False Invoke by simp
    next
      case True
      then have "\<exists>Ts T m D b. P' \<turnstile> ?C sees M,b:Ts \<rightarrow> T = m in D"
        by(fastforce dest!: classes_above_sees_method[OF above, of M])
      then show ?thesis using meq meth True Invoke by simp
    qed
  qed
next
  case (Invokestatic C1 M n)
  then have above: "classes_above P C1 \<inter> classes_changed P P' = {}"
    using assms by simp
  obtain D b Ts T mxs mxl ins xt where meth: "method P' C1 M = (D,b,Ts,T,mxs,mxl,ins,xt)"
    by(cases "method P' C1 M", clarsimp)
  have meq: "method P C1 M = method P' C1 M"
   using classes_above_method[OF above] by simp
  show ?thesis
  proof(cases "\<exists>Ts T m D b. P \<turnstile> C1 sees M,b:Ts \<rightarrow> T = m in D")
    case False
    then have "\<not>(\<exists>Ts T m D b. P' \<turnstile> C1 sees M,b:Ts \<rightarrow> T = m in D)"
      using classes_above_sees_method2[OF above, of M] by clarsimp
    then show ?thesis using False Invokestatic by simp
  next
    case True
    then have "\<exists>Ts T m D b. P' \<turnstile> C1 sees M,b:Ts \<rightarrow> T = m in D"
      by(fastforce dest!: classes_above_sees_method[OF above, of M])
    then show ?thesis using meq meth True Invokestatic by simp
  qed
next
  case Return then show ?thesis using assms classes_above_method[OF above_C]
    by(cases frs, auto)
next
  case (Load x1) then show ?thesis using assms by auto
next
  case (Store x2) then show ?thesis using assms by auto
next
  case (Push x3) then show ?thesis using assms by auto
next
  case (Goto x15) then show ?thesis using assms by auto
next
  case (IfFalse x17) then show ?thesis using assms by auto
qed(auto)


\<comment> \<open> if collected classes unchanged, instruction collection unchanged \<close>
lemma ncollect_JVMinstr_ncollect:
assumes "JVMinstr_ncollect P i h stk \<inter> classes_changed P P' = {}"
shows "JVMinstr_ncollect P i h stk = JVMinstr_ncollect P' i h stk"
proof(cases i)
  case (New C1)
  then show ?thesis using assms classes_above_set[of C1 P P'] by auto
next
  case (Getfield F C1) show ?thesis
  proof(cases "hd stk = Null")
    case True then show ?thesis using Getfield assms by simp
  next
    case False
    let ?D = "cname_of h (the_Addr (hd stk))"
    have "classes_above P ?D \<inter> classes_changed P P' = {}" using False Getfield assms by auto
    then have "classes_above P ?D = classes_above P' ?D"
      using classes_above_set by blast
    then show ?thesis using assms Getfield by auto
  qed
next
  case (Getstatic C1 P1 D1)
  then have "classes_above P C1 \<inter> classes_changed P P' = {}" using assms by auto
  then have "classes_above P C1 = classes_above P' C1"
    using classes_above_set assms Getstatic by blast
  then show ?thesis using assms Getstatic  by auto
next
  case (Putfield F C1) show ?thesis
  proof(cases "hd(tl stk) = Null")
    case True then show ?thesis using Putfield assms by simp
  next
    case False
    let ?D = "cname_of h (the_Addr (hd (tl stk)))"
    have "classes_above P ?D \<inter> classes_changed P P' = {}" using False Putfield assms by auto
    then have "classes_above P ?D = classes_above P' ?D"
      using classes_above_set by blast
    then show ?thesis using assms Putfield by auto
  qed
next
  case (Putstatic C1 F D1)
  then have "classes_above P C1 \<inter> classes_changed P P' = {}" using assms by auto
  then have "classes_above P C1 = classes_above P' C1"
    using classes_above_set assms Putstatic by blast
  then show ?thesis using assms Putstatic  by auto
next
  case (Checkcast C1)
  then show ?thesis using assms
   classes_above_set[of "cname_of h (the_Addr (hd stk))" P P'] by auto
next
  case (Invoke M n)
  then show ?thesis using assms
   classes_above_set[of "cname_of h (the_Addr (stk ! n))" P P'] by auto
next
  case (Invokestatic C1 M n)
  then show ?thesis using assms classes_above_set[of C1 P P'] by auto
next
  case Return
  then show ?thesis using assms classes_above_set[of _ P P'] by auto
next
  case Throw
  then show ?thesis using assms
   classes_above_set[of "cname_of h (the_Addr (hd stk))" P P'] by auto
qed(auto)

\<comment> \<open> if collected classes unchanged, @{term exec_step} unchanged \<close>
lemma ncollect_exec_step:
assumes "JVMstep_ncollect P h stk C M pc ics \<inter> classes_changed P P' = {}"
  and above_C: "classes_above P C \<inter> classes_changed P P' = {}"
shows "exec_step P h stk loc C M pc ics frs sh = exec_step P' h stk loc C M pc ics frs sh"
proof(cases ics)
  case No_ics then show ?thesis
  using ncollect_exec_instr assms classes_above_method[OF above_C, THEN sym]
    by simp
next
  case (Calling C1 Cs)
  then have above_C1: "classes_above P C1 \<inter> classes_changed P P' = {}"
    using assms(1) by auto
  show ?thesis
  proof(cases "sh C1")
    case None
    then show ?thesis using Calling assms classes_above_sblank[OF above_C1] by simp
  next
    case (Some a)
    then obtain sfs i where sfsi: "a = (sfs, i)" by(cases a)
    then show ?thesis using Calling Some assms
    proof(cases i)
      case Prepared then show ?thesis
       using above_C1 sfsi Calling Some assms classes_above_method[OF above_C1]
         by(simp add: split_beta classes_above_class classes_changed_class[where cn=C1])
    next
      case Error then show ?thesis
       using above_C1 sfsi Calling Some assms classes_above_method[of C1 P P']
         by(simp add: split_beta classes_above_class classes_changed_class[where cn=C1])
    qed(auto)
  qed
next
  case (Called Cs) show ?thesis
  proof(cases Cs)
    case Nil then show ?thesis
    using ncollect_exec_instr assms classes_above_method[OF above_C, THEN sym] Called
      by simp
  next
    case (Cons C1 Cs1)
    then have above_C': "classes_above P C1 \<inter> classes_changed P P' = {}" using assms Called by auto
    show ?thesis using assms classes_above_method[OF above_C'] Cons Called by simp
  qed
next
  case (Throwing Cs a) then show ?thesis using assms by(cases Cs; simp)
qed

\<comment> \<open> if collected classes unchanged, @{term exec_step} collection unchanged \<close>
lemma ncollect_JVMstep_ncollect:
assumes "JVMstep_ncollect P h stk C M pc ics \<inter> classes_changed P P' = {}"
  and above_C: "classes_above P C \<inter> classes_changed P P' = {}"
shows "JVMstep_ncollect P h stk C M pc ics = JVMstep_ncollect P' h stk C M pc ics"
proof(cases ics)
  case No_ics then show ?thesis
  using assms ncollect_JVMinstr_ncollect classes_above_method[OF above_C]
   by simp
next
  case (Calling C1 Cs)
  then have above_C: "classes_above P C1 \<inter> classes_changed P P' = {}"
    using assms(1) by auto
  let ?C = "fst(method P C1 clinit)"
  show ?thesis using Calling assms classes_above_method[OF above_C]
   classes_above_set[OF above_C] by auto
next
  case (Called Cs) show ?thesis
  proof(cases Cs)
    case Nil then show ?thesis
    using assms ncollect_JVMinstr_ncollect classes_above_method[OF above_C] Called
     by simp
  next
    case (Cons C1 Cs1)
    then have above_C1: "classes_above P C1 \<inter> classes_changed P P' = {}"
      and above_C': "classes_above P (fst (method P C1 clinit)) \<inter> classes_changed P P' = {}"
     using assms Called by auto
    show ?thesis using assms Cons Called classes_above_set[OF above_C1]
     classes_above_set[OF above_C'] classes_above_method[OF above_C1]
      by simp
  qed
next
  case (Throwing Cs a) then show ?thesis
  using assms classes_above_set[of "cname_of h a" P P'] by simp
qed

\<comment> \<open> if collected classes unchanged, @{term classes_above_frames} unchanged \<close>
lemma ncollect_classes_above_frames:
 "JVMexec_ncollect P (None, h, (stk,loc,C,M,pc,ics)#frs, sh) \<inter> classes_changed P P' = {}
 \<Longrightarrow> classes_above_frames P frs = classes_above_frames P' frs"
proof(induct frs)
  case (Cons f frs')
  then obtain stk loc C M pc ics where f: "f = (stk,loc,C,M,pc,ics)" by(cases f)
  then have above_C: "classes_above P C \<inter> classes_changed P P' = {}" using Cons by auto
  show ?case using f Cons classes_above_subcls[OF above_C]
   classes_above_subcls2[OF above_C] by auto
qed(auto)

\<comment> \<open> if collected classes unchanged, @{term classes_above_xcpts} unchanged \<close>
lemma ncollect_classes_above_xcpts:
assumes "JVMexec_ncollect P (None, h, (stk,loc,C,M,pc,ics)#frs, sh) \<inter> classes_changed P P' = {}"
shows "classes_above_xcpts P = classes_above_xcpts P'"
proof -
  have left: "\<And>x x'. x' \<in> sys_xcpts \<Longrightarrow> P \<turnstile> x' \<preceq>\<^sup>* x \<Longrightarrow> \<exists>xa\<in>sys_xcpts. P' \<turnstile> xa \<preceq>\<^sup>* x"
  proof -
    fix x x'
    assume x': "x' \<in> sys_xcpts" and above: "P \<turnstile> x' \<preceq>\<^sup>* x"
    then show "\<exists>xa\<in>sys_xcpts. P' \<turnstile> xa \<preceq>\<^sup>* x" using assms classes_above_subcls[OF _ above]
      by(rule_tac x=x' in bexI) auto
  qed
  have right: "\<And>x x'. x' \<in> sys_xcpts \<Longrightarrow> P' \<turnstile> x' \<preceq>\<^sup>* x \<Longrightarrow> \<exists>xa\<in>sys_xcpts. P \<turnstile> xa \<preceq>\<^sup>* x"
  proof -
    fix x x'
    assume x': "x' \<in> sys_xcpts" and above: "P' \<turnstile> x' \<preceq>\<^sup>* x"
    then show "\<exists>xa\<in>sys_xcpts. P \<turnstile> xa \<preceq>\<^sup>* x" using assms classes_above_subcls2[OF _ above]
      by(rule_tac x=x' in bexI) auto
  qed
  show ?thesis using left right by auto
qed

\<comment> \<open> if collected classes unchanged, @{term exec} collection unchanged \<close>
lemma ncollect_JVMexec_ncollect:
assumes "JVMexec_ncollect P \<sigma> \<inter> classes_changed P P' = {}"
shows "JVMexec_ncollect P \<sigma> = JVMexec_ncollect P' \<sigma>"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma> = (xp,h,frs,sh)" by(cases \<sigma>)
  then show ?thesis using assms
  proof(cases "\<exists>x. xp = Some x \<or> frs = []")
    case False
    then obtain stk loc C M pc ics frs' where frs: "frs = (stk,loc,C,M,pc,ics)#frs'"
      by(cases frs, auto)
    have step: "JVMstep_ncollect P h stk C M pc ics \<inter> classes_changed P P' = {}"
      using False \<sigma> frs assms by(cases ics, auto simp: JVMNaiveCollectionSemantics.csmall_def)
    have above_C: "classes_above P C \<inter> classes_changed P P' = {}"
      using False \<sigma> frs assms by(auto simp: JVMNaiveCollectionSemantics.csmall_def)
    have frames: "classes_above_frames P frs' = classes_above_frames P' frs'"
     using ncollect_classes_above_frames frs \<sigma> False assms by simp
    have xcpts: "classes_above_xcpts P = classes_above_xcpts P'"
     using ncollect_classes_above_xcpts frs \<sigma> False assms by simp
    show ?thesis using False xcpts frames frs \<sigma> ncollect_JVMstep_ncollect[OF step above_C]
        classes_above_subcls[OF above_C] classes_above_subcls2[OF above_C]
      by auto
  qed(auto)
qed

\<comment> \<open> if collected classes unchanged, classes above an exception returned
 by @{term exec_instr} unchanged \<close>
lemma ncollect_exec_instr_xcpts:
assumes collect: "JVMinstr_ncollect P i h stk \<inter> classes_changed P P' = {}"
  and xpcollect: "classes_above_xcpts P \<inter> classes_changed P P' = {}"
  and prealloc: "preallocated h"
  and \<sigma>': "\<sigma>' = exec_instr i P h stk loc C M pc ics' frs sh"
  and xp: "fst \<sigma>' = Some a"
  and i: "i = instrs_of P C M ! pc"
shows "classes_above P (cname_of h a) \<inter> classes_changed P P' = {}"
using assms exec_instr_xcpts[OF \<sigma>' xp]
proof(cases i)
  case Throw then show ?thesis using assms by(cases "hd stk", fastforce+)
qed(fastforce+)

\<comment> \<open> if collected classes unchanged, classes above an exception returned
 by @{term exec_step} unchanged \<close>
lemma ncollect_exec_step_xcpts:
assumes collect: "JVMstep_ncollect P h stk C M pc ics \<inter> classes_changed P P' = {}"
  and xpcollect: "classes_above_xcpts P \<inter> classes_changed P P' = {}"
  and prealloc: "preallocated h"
  and \<sigma>': "\<sigma>' = exec_step P h stk loc C M pc ics frs sh"
  and xp: "fst \<sigma>' = Some a"
shows "classes_above P (cname_of h a) \<inter> classes_changed P P' = {}"
proof(cases ics)
  case No_ics then show ?thesis using assms ncollect_exec_instr_xcpts by simp
next
  case (Calling x21 x22)
  then show ?thesis using assms by(clarsimp split: option.splits init_state.splits if_split_asm)
next
  case (Called Cs) then show ?thesis using assms ncollect_exec_instr_xcpts by(cases Cs; simp)
next
  case (Throwing Cs a) then show ?thesis using assms by(cases Cs; simp)
qed

\<comment> \<open> if collected classes unchanged, if @{term csmall} returned a result
 under @{term P}, @{term P'} returns the same \<close>
lemma ncollect_JVMsmall:
assumes collect: "(\<sigma>', cset) \<in> JVMNaiveCollectionSemantics.csmall P \<sigma>"
  and intersect: "cset \<inter> classes_changed P P' = {}"
  and prealloc: "preallocated (fst(snd \<sigma>))"
shows "(\<sigma>', cset) \<in> JVMNaiveCollectionSemantics.csmall P' \<sigma>"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma> = (xp,h,frs,sh)" by(cases \<sigma>)
  then have prealloc': "preallocated h" using prealloc by simp
  show ?thesis using \<sigma> assms
  proof(cases "\<exists>x. xp = Some x \<or> frs = []")
    case False
    then obtain stk loc C M pc ics frs' where frs: "frs = (stk,loc,C,M,pc,ics)#frs'"
      by(cases frs, auto)
    have step: "JVMstep_ncollect P h stk C M pc ics \<inter> classes_changed P P' = {}"
      using False \<sigma> frs assms by(cases ics, auto simp: JVMNaiveCollectionSemantics.csmall_def)
    have above_C: "classes_above P C \<inter> classes_changed P P' = {}"
      using False \<sigma> frs assms by(auto simp: JVMNaiveCollectionSemantics.csmall_def)
    obtain xp1 h1 frs1 sh1 where exec: "exec_step P' h stk loc C M pc ics frs' sh = (xp1,h1,frs1,sh1)"
      by(cases "exec_step P' h stk loc C M pc ics frs' sh")
    have collect: "JVMexec_ncollect P \<sigma> = JVMexec_ncollect P' \<sigma>"
      using assms ncollect_JVMexec_ncollect by(simp add: JVMNaiveCollectionSemantics.csmall_def)
    have exec_instr: "exec_step P h stk loc C M pc ics frs' sh
      = exec_step P' h stk loc C M pc ics frs' sh"
      using ncollect_exec_step[OF step above_C] \<sigma> frs False by simp
    show ?thesis
    proof(cases xp1)
      case None then show ?thesis
      using None \<sigma> frs step False assms ncollect_exec_step[OF step above_C] collect exec
        by(auto simp: JVMNaiveCollectionSemantics.csmall_def)
    next
      case (Some a)
      then show ?thesis using \<sigma> assms
      proof(cases xp)
        case None
        have frames: "classes_above_frames P (frames_of \<sigma>) \<inter> classes_changed P P' = {}"
          using None Some frs \<sigma> assms by(auto simp: JVMNaiveCollectionSemantics.csmall_def)
        have frsi: "classes_above_frames P frs \<inter> classes_changed P P' = {}" using \<sigma> frames by simp
        have xpcollect: "classes_above_xcpts P \<inter> classes_changed P P' = {}"
          using None Some frs \<sigma> assms by(auto simp: JVMNaiveCollectionSemantics.csmall_def)
        have xp: "classes_above P (cname_of h a) \<inter> classes_changed P P' = {}"
         using ncollect_exec_step_xcpts[OF step xpcollect prealloc',
             where \<sigma>' = "(xp1,h1,frs1,sh1)" and frs=frs' and loc=loc and a=a and sh=sh]
           exec exec_instr Some assms by auto
        show ?thesis using Some exec \<sigma> frs False assms exec_instr collect
             classes_above_find_handler[where h=h and sh=sh, OF xp frsi]
         by(auto simp: JVMNaiveCollectionSemantics.csmall_def)
      qed(auto simp: JVMNaiveCollectionSemantics.csmall_def)
    qed
  qed(auto simp: JVMNaiveCollectionSemantics.csmall_def)
qed

\<comment> \<open> if collected classes unchanged, if @{term cbig} returned a result
 under @{term P}, @{term P'} returns the same \<close>
lemma ncollect_JVMbig:
assumes collect: "(\<sigma>', cset) \<in> JVMNaiveCollectionSemantics.cbig P \<sigma>"
  and intersect: "cset \<inter> classes_changed P P' = {}"
  and prealloc: "preallocated (fst(snd \<sigma>))"
shows "(\<sigma>', cset) \<in> JVMNaiveCollectionSemantics.cbig P' \<sigma>"
using JVMNaiveCollectionSemantics.csmall_to_cbig_prop2[where R="\<lambda>P P' cset. cset \<inter> classes_changed P P' = {}"
   and Q="\<lambda>\<sigma>. preallocated (fst(snd \<sigma>))" and P=P and P'=P' and \<sigma>=\<sigma> and \<sigma>'=\<sigma>' and coll=cset]
   ncollect_JVMsmall JVMsmall_prealloc_pres assms by auto

\<comment> \<open> and finally, RTS algorithm based on @{term ncollect} is existence safe \<close>
theorem jvm_naive_existence_safe:
assumes p: "P \<in> jvm_progs" and "P' \<in> jvm_progs" and t: "t \<in> jvm_tests"
 and out: "o1 \<in> jvm_naive_out P t" and "jvm_deselect P o1 P'"
shows "\<exists>o2 \<in> jvm_naive_out P' t. o1 = o2"
using assms
proof -
  let ?P = "start_prog (t#P) (fst t) main"
  let ?P' = "start_prog (t#P') (fst t) main"
  obtain wf_md where wf': "wf_prog wf_md (t#P)" using p t
   by(auto simp: wf_jvm_prog_def wf_jvm_prog_phi_def)
  have ns: "\<not>is_class (t#P) Start" using p t
   by(clarsimp simp: is_class_def class_def Start_def Test_def)
  obtain \<sigma>1 coll1 where o1: "o1 = (\<sigma>1, coll1)" by(cases o1)
  then have cbig: "(\<sigma>1, coll1) \<in> JVMNaiveCollectionSemantics.cbig ?P (start_state (t # P))"
   using assms by simp
  have "coll1 \<inter> classes_changed P P' = {}" using cbig o1 assms by auto
  then have changed: "coll1 \<inter> classes_changed (t#P) (t#P') = {}" by(rule classes_changed_int_Cons)
  then have changed': "coll1 \<inter> classes_changed ?P ?P' = {}" by(rule classes_changed_int_Cons)
  have "classes_above_xcpts ?P = classes_above_xcpts (t#P)"
    using class_add_classes_above[OF ns wf_sys_xcpt_nsub_Start[OF wf' ns]] by simp
  then have "classes_above_xcpts (t#P) \<inter> classes_changed (t#P) (t#P') = {}"
   using jvm_naive_out_xcpts_collected[OF out] o1 changed by auto
  then have ss_eq: "start_state (t#P) = start_state (t#P')"
    using classes_above_start_state by simp
  show ?thesis using ncollect_JVMbig[OF cbig changed']
    preallocated_start_state changed' ss_eq o1 assms by auto
qed

\<comment> \<open> ...thus @{term JVMNaiveCollection} is an instance of @{term CollectionBasedRTS} \<close>
interpretation JVMNaiveCollectionRTS :
  CollectionBasedRTS "(=)" jvm_deselect jvm_progs jvm_tests
     JVMendset JVMcombine JVMcollect_id JVMsmall JVMNaiveCollect jvm_naive_out
     jvm_make_test_prog jvm_naive_collect_start
 by unfold_locales (rule jvm_naive_existence_safe, auto simp: start_state_def)

(***********************************************************************************************)
subsection "Smarter RTS algorithm"

subsubsection "Definitions and helper lemmas"

fun jvm_smart_out :: "jvm_prog \<Rightarrow> jvm_class \<Rightarrow> jvm_prog_out set" where
"jvm_smart_out P t
 = {(\<sigma>',coll'). \<exists>coll. (\<sigma>',coll) \<in> JVMSmartCollectionSemantics.cbig
                                       (jvm_make_test_prog P t) (start_state (t#P))
                            \<and> coll' = coll \<union> classes_above_xcpts P \<union> {Object,Start}}"

abbreviation jvm_smart_collect_start :: "jvm_prog \<Rightarrow> cname set" where
"jvm_smart_collect_start P \<equiv> classes_above_xcpts P \<union> {Object,Start}"


lemma jvm_naive_iff_smart:
"(\<exists>cset\<^sub>n. (\<sigma>',cset\<^sub>n) \<in> jvm_naive_out P t) \<longleftrightarrow> (\<exists>cset\<^sub>s. (\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t)"
 by(auto simp: JVMNaiveCollectionSemantics.cbig_big_equiv
               JVMSmartCollectionSemantics.cbig_big_equiv)

(**************************************************)

lemma jvm_smart_out_classes_above_xcpts:
assumes s: "(\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t" and P: "P \<in> jvm_progs" and t: "t \<in> jvm_tests"
shows "classes_above_xcpts (jvm_make_test_prog P t) \<subseteq> cset\<^sub>s"
 using jvm_make_test_prog_classes_above_xcpts[OF P t] s by clarsimp

lemma jvm_smart_collect_start_make_test_prog:
 "\<lbrakk> P \<in> jvm_progs; t \<in> jvm_tests \<rbrakk>
  \<Longrightarrow> jvm_smart_collect_start (jvm_make_test_prog P t) = jvm_smart_collect_start P"
 using jvm_make_test_prog_classes_above_xcpts by simp

lemma jvm_smart_out_classes_above_start_heap:
assumes s: "(\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t" and h: "start_heap (t#P) a = Some(C,fs)"
 and P: "P \<in> jvm_progs" and t: "t \<in> jvm_tests"
shows "classes_above (jvm_make_test_prog P t) C \<subseteq> cset\<^sub>s"
using start_heap_classes[OF h] jvm_smart_out_classes_above_xcpts[OF s P t] by auto

lemma jvm_smart_out_classes_above_start_sheap:
assumes "(\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t" and "start_sheap C = Some(sfs,i)"
shows "classes_above (jvm_make_test_prog P t) C \<subseteq> cset\<^sub>s"
using assms start_prog_classes_above_Start by(clarsimp split: if_split_asm)

lemma jvm_smart_out_classes_above_frames:
 "(\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t
   \<Longrightarrow> classes_above_frames (jvm_make_test_prog P t) (frames_of (start_state (t#P))) \<subseteq> cset\<^sub>s"
using start_prog_classes_above_Start by(clarsimp split: if_split_asm simp: start_state_def)

(**************************************************)
subsubsection "Additional well-formedness conditions"

\<comment> \<open> returns class to be initialized by given instruction, if applicable \<close>
(* NOTE: similar to exp-taking init_class from J/EConform - but requires field existence checks *)
fun coll_init_class :: "'m prog \<Rightarrow> instr \<Rightarrow> cname option" where
"coll_init_class P (New C) = Some C" |
"coll_init_class P (Getstatic C F D) = (if \<exists>t. P \<turnstile> C has F,Static:t in D
                                       then Some D else None)" |
"coll_init_class P (Putstatic C F D) = (if \<exists>t. P \<turnstile> C has F,Static:t in D
                                       then Some D else None)" |
"coll_init_class P (Invokestatic C M n) = seeing_class P C M" |
"coll_init_class _ _ = None"

\<comment> \<open> checks whether the given value is a pointer; if it's an address,
 checks whether it points to an object in the given heap \<close>
fun is_ptr :: "heap \<Rightarrow> val \<Rightarrow> bool" where
"is_ptr h Null = True" |
"is_ptr h (Addr a) = (\<exists>Cfs. h a = Some Cfs)" |
"is_ptr h _ = False"

lemma is_ptrD: "is_ptr h v \<Longrightarrow> v = Null \<or> (\<exists>a. v = Addr a \<and> (\<exists>Cfs. h a = Some Cfs))"
 by(cases v, auto)

\<comment> \<open> shorthand for: given stack has entries required by given instr,
 including pointer where necessary \<close>
fun stack_safe :: "instr \<Rightarrow> heap \<Rightarrow> val list \<Rightarrow> bool" where
"stack_safe (Getfield F C) h stk = (length stk > 0 \<and> is_ptr h (hd stk))" |
"stack_safe (Putfield F C) h stk = (length stk > 1 \<and> is_ptr h (hd (tl stk)))" |
"stack_safe (Checkcast C) h stk = (length stk > 0 \<and> is_ptr h (hd stk))" |
"stack_safe (Invoke M n) h stk = (length stk > n \<and> is_ptr h (stk ! n))" |
"stack_safe JVMInstructions.Throw h stk = (length stk > 0 \<and> is_ptr h (hd stk))" |
"stack_safe i h stk = True"

lemma well_formed_stack_safe:
assumes wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" and correct: "P,\<Phi> \<turnstile> (xp,h,(stk,loc,C,M,pc,ics)#frs,sh)\<surd>"
shows "stack_safe (instrs_of P C M ! pc) h stk"
proof -
  from correct obtain b Ts T mxs mxl\<^sub>0 ins xt where
    mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C" and
    pc: "pc < length ins" by clarsimp
  from sees_wf_mdecl[OF _ mC] wtp have "wt_method P C b Ts T mxs mxl\<^sub>0 ins xt (\<Phi> C M)"
    by(auto simp: wf_jvm_prog_phi_def wf_mdecl_def)
  with pc have wt: "P,T,mxs,length ins,xt \<turnstile> ins ! pc,pc :: \<Phi> C M" by(simp add: wt_method_def)
  from mC correct obtain ST LT where
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" by fastforce
  show ?thesis
  proof(cases "instrs_of P C M ! pc")
    case (Getfield F D)
    with mC \<Phi> wt stk obtain oT ST' where
      oT: "P \<turnstile> oT \<le> Class D" and
      ST: "ST = oT # ST'" by fastforce
    with stk obtain ref stk' where
      stk': "stk = ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> oT" by auto
    with ref oT have "ref = Null \<or> (ref \<noteq> Null \<and> P,h \<turnstile> ref :\<le> Class D)" by auto
    with Getfield mC have "is_ptr h ref" by(fastforce dest: non_npD)
    with stk' Getfield show ?thesis by auto
  next
    case (Putfield F D)
    with mC \<Phi> wt stk obtain vT oT ST' where
      oT: "P \<turnstile> oT \<le> Class D" and
      ST: "ST = vT # oT # ST'" by fastforce
    with stk obtain v ref stk' where
      stk': "stk = v#ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> oT" by auto
    with ref oT have "ref = Null \<or> (ref \<noteq> Null \<and> P,h \<turnstile> ref :\<le> Class D)" by auto
    with Putfield mC have "is_ptr h ref" by(fastforce dest: non_npD)
    with stk' Putfield show ?thesis by auto
  next
    case (Checkcast D)
    with mC \<Phi> wt stk obtain oT ST' where
      oT: "is_refT oT" and
      ST: "ST = oT # ST'" by fastforce
    with stk obtain ref stk' where
      stk': "stk = ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> oT" by auto
    with ref oT have "ref = Null \<or> (ref \<noteq> Null \<and> (\<exists>D'. P,h \<turnstile> ref :\<le> Class D'))"
      by(auto simp: is_refT_def)
    with Checkcast mC have "is_ptr h ref" by(fastforce dest: non_npD)
    with stk' Checkcast show ?thesis by auto
  next
    case (Invoke M1 n)
    with mC \<Phi> wt stk have
      ST: "n < size ST" and
      oT: "ST!n = NT \<or> (\<exists>D. ST!n = Class D)" by auto
    with stk have stk': "n < size stk" by (auto simp: list_all2_lengthD)
    with stk ST oT list_all2_nthD2
    have "stk!n = Null \<or> (stk!n \<noteq> Null \<and> (\<exists>D. P,h \<turnstile> stk!n :\<le> Class D))" by fastforce
    with Invoke mC have "is_ptr h (stk!n)" by(fastforce dest: non_npD)
    with stk' Invoke show ?thesis by auto
  next
    case Throw
    with mC \<Phi> wt stk obtain oT ST' where
      oT: "is_refT oT" and
      ST: "ST = oT # ST'" by fastforce
    with stk obtain ref stk' where
      stk': "stk = ref#stk'" and
      ref:  "P,h \<turnstile> ref :\<le> oT" by auto
    with ref oT have "ref = Null \<or> (ref \<noteq> Null \<and> (\<exists>D'. P,h \<turnstile> ref :\<le> Class D'))"
      by(auto simp: is_refT_def)
    with Throw mC have "is_ptr h ref" by(fastforce dest: non_npD)
    with stk' Throw show ?thesis by auto
  qed(simp_all)
qed

(******************************************)
subsubsection \<open> Proving naive @{text "\<subseteq>"} smart \<close>

text \<open> We prove that, given well-formedness of the program and state, and "promises"
 about what has or will be collected in previous or future steps, @{term jvm_smart}
 collects everything @{term jvm_naive} does. We prove that promises about previously-
 collected classes ("backward promises") are maintained by execution, and promises
 about to-be-collected classes ("forward promises") are met by the end of execution.
 We then show that the required initial conditions (well-formedness and backward
 promises) are met by the defined start states, and thus that a run test will
 collect at least those classes collected by the naive algorithm. \<close>

\<comment> \<open> Backward promises (classes that should already be collected) \<close>
  \<comment> \<open> - Classes of objects in the heap are collected \<close>
  \<comment> \<open> - Non-@{term None} classes on the static heap are collected \<close>
  \<comment> \<open> - Current classes from the frame stack are collected \<close>
  \<comment> \<open> - Classes of system exceptions are collected \<close>

text "If backward promises have been kept, a single step preserves this property;
 i.e., any classes that have been added to this set (new heap objects, newly prepared
 sheap classes, new frames) are collected by the smart collection algorithm in that
 step or by forward promises:"
lemma backward_coll_promises_kept:
assumes
\<comment> \<open> well-formedness \<close>
      wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and correct: "P,\<Phi> \<turnstile> (xp,h,frs,sh)\<surd>"
\<comment> \<open> defs \<close>
  and f': "hd frs = (stk,loc,C',M',pc,ics)"
\<comment> \<open> backward promises - will be collected prior \<close>
  and heap: "\<And>C fs. \<exists>a. h a = Some(C,fs) \<Longrightarrow> classes_above P C \<subseteq> cset"
  and sheap: "\<And>C sfs i. sh C = Some(sfs,i) \<Longrightarrow> classes_above P C \<subseteq> cset"
  and xcpts: "classes_above_xcpts P \<subseteq> cset"
  and frames: "classes_above_frames P frs \<subseteq> cset"
\<comment> \<open> forward promises - will be collected after if not already \<close>
  and init_class_prom: "\<And>C. ics = Called [] \<or> ics = No_ics
       \<Longrightarrow> coll_init_class P (instrs_of P C' M' ! pc) = Some C \<Longrightarrow> classes_above P C \<subseteq> cset"
  and Calling_prom: "\<And>C' Cs'. ics = Calling C' Cs' \<Longrightarrow> classes_above P C' \<subseteq> cset"
\<comment> \<open> collection and step \<close>
  and smart: "JVMexec_scollect P (xp,h,frs,sh) \<subseteq> cset"
  and small: "(xp',h',frs',sh') \<in> JVMsmall P (xp,h,frs,sh)"
shows "(h' a = Some(C,fs) \<longrightarrow> classes_above P C \<subseteq> cset)
     \<and> (sh' C = Some(sfs',i') \<longrightarrow> classes_above P C \<subseteq> cset)
     \<and> (classes_above_frames P frs' \<subseteq> cset)"
using assms
proof(cases frs)
  case (Cons f1 frs1)
(****)
  then have cr': "P,\<Phi> \<turnstile> (xp,h,(stk,loc,C',M',pc,ics)#frs1,sh)\<surd>" using correct f' by simp
  let ?i = "instrs_of P C' M' ! pc"
  from well_formed_stack_safe[OF wtp cr'] correct_state_Throwing_ex[OF cr'] obtain
    stack_safe: "stack_safe ?i h stk" and
    Throwing_ex: "\<And>Cs a. ics = Throwing Cs a \<Longrightarrow> \<exists>obj. h a = Some obj" by simp
  have confc: "conf_clinit P sh frs" using correct Cons by simp
  have Called_prom: "\<And>C' Cs'. ics = Called (C'#Cs')
           \<Longrightarrow> classes_above P C' \<subseteq> cset \<and> classes_above P (fst(method P C' clinit)) \<subseteq> cset"
  proof -
    fix C' Cs' assume [simp]: "ics = Called (C'#Cs')"
    then have "C' \<in> set(clinit_classes frs)" using f' Cons by simp
    then obtain sfs where shC': "sh C' = Some(sfs, Processing)" and "is_class P C'"
      using confc by(auto simp: conf_clinit_def)
    then have C'eq: "C' = fst(method P C' clinit)" using wf_sees_clinit wtp
      by(fastforce simp: is_class_def wf_jvm_prog_phi_def)
    then show "classes_above P C' \<subseteq> cset \<and> classes_above P (fst(method P C' clinit)) \<subseteq> cset"
      using sheap shC' by auto
  qed
  have Called_prom2: "\<And>Cs. ics = Called Cs \<Longrightarrow> \<exists>C1 sobj. Called_context P C1 ?i \<and> sh C1 = Some sobj"
    using cr' by(auto simp: conf_f_def2)
  have Throwing_prom: "\<And>C' Cs a. ics = Throwing (C'#Cs) a \<Longrightarrow> \<exists>sfs. sh C' = Some(sfs, Processing)"
  proof -
    fix C' Cs a assume [simp]: "ics = Throwing (C'#Cs) a"
    then have "C' \<in> set(clinit_classes frs)" using f' Cons by simp
    then show "\<exists>sfs. sh C' = Some(sfs, Processing)" using confc by(clarsimp simp: conf_clinit_def)
  qed
(****)
  show ?thesis using Cons assms
  proof(cases xp)
    case None
    then have exec: "exec (P, None, h, (stk,loc,C',M',pc,ics)#frs1, sh) = Some (xp',h',frs',sh')"
      using small f' Cons by auto
    obtain si where si: "exec_step_input P C' M' pc ics = si" by simp
    obtain xp\<^sub>0 h\<^sub>0 frs\<^sub>0 sh\<^sub>0 where
     exec_step: "exec_step P h stk loc C' M' pc ics frs1 sh = (xp\<^sub>0, h\<^sub>0, frs\<^sub>0, sh\<^sub>0)"
      by(cases "exec_step P h stk loc C' M' pc ics frs1 sh")
    then have ind: "exec_step_ind si P h stk loc C' M' pc ics frs1 sh
                       (xp\<^sub>0, h\<^sub>0, frs\<^sub>0, sh\<^sub>0)" using exec_step_ind_equiv si by auto
    then show ?thesis using heap sheap frames exec exec_step f' Cons
      si init_class_prom stack_safe Calling_prom Called_prom Called_prom2 Throwing_prom
    proof(induct rule: exec_step_ind.induct)
      case exec_step_ind_Load show ?case using exec_step_ind_Load.prems(1-7) by auto
    next
      case exec_step_ind_Store show ?case using exec_step_ind_Store.prems(1-7) by auto
    next
      case exec_step_ind_Push show ?case using exec_step_ind_Push.prems(1-7) by auto
    next
      case exec_step_ind_NewOOM_Called show ?case using exec_step_ind_NewOOM_Called.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_NewOOM_Done show ?case using exec_step_ind_NewOOM_Done.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_New_Called show ?case
       using exec_step_ind_New_Called.hyps exec_step_ind_New_Called.prems(1-9)
        by(auto split: if_split_asm simp: blank_def dest!: exec_step_input_StepID) blast+
    next
      case exec_step_ind_New_Done show ?case
       using exec_step_ind_New_Done.hyps exec_step_ind_New_Done.prems(1-9)
        by(auto split: if_split_asm simp: blank_def dest!: exec_step_input_StepID) blast+
    next
      case exec_step_ind_New_Init show ?case
        using exec_step_ind_New_Init.prems(1-7) by auto
    next
      case exec_step_ind_Getfield_Null show ?case using exec_step_ind_Getfield_Null.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Getfield_NoField show ?case
       using exec_step_ind_Getfield_NoField.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Getfield_Static show ?case
       using exec_step_ind_Getfield_Static.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Getfield show ?case
       using exec_step_ind_Getfield.prems(1-7) by auto
    next
      case exec_step_ind_Getstatic_NoField show ?case
       using exec_step_ind_Getstatic_NoField.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Getstatic_NonStatic show ?case
       using exec_step_ind_Getstatic_NonStatic.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Getstatic_Called show ?case
        using exec_step_ind_Getstatic_Called.prems(1-7) by auto
    next
      case exec_step_ind_Getstatic_Done show ?case
        using exec_step_ind_Getstatic_Done.prems(1-7) by auto
    next
      case exec_step_ind_Getstatic_Init show ?case
        using exec_step_ind_Getstatic_Init.prems(1-7) by auto
    next
      case exec_step_ind_Putfield_Null show ?case
       using exec_step_ind_Putfield_Null.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Putfield_NoField show ?case
       using exec_step_ind_Putfield_NoField.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Putfield_Static show ?case
       using exec_step_ind_Putfield_Static.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case (exec_step_ind_Putfield v stk r a D fs h D' b t P C F loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
      obtain a C1 fs where addr: "hd (tl stk) = Null \<or> (hd (tl stk) = Addr a \<and> h a = Some(C1,fs))"
       using exec_step_ind_Putfield.prems(8,10) by(auto dest!: exec_step_input_StepID is_ptrD)
      then have "\<And>a. hd(tl stk) = Addr a \<Longrightarrow> classes_above P C1 \<subseteq> cset"
        using exec_step_ind_Putfield.prems(1) addr by auto
      then show ?case using exec_step_ind_Putfield.hyps exec_step_ind_Putfield.prems(1-7) addr
        by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_Putstatic_NoField show ?case
       using exec_step_ind_Putstatic_NoField.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Putstatic_NonStatic show ?case
       using exec_step_ind_Putstatic_NonStatic.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case (exec_step_ind_Putstatic_Called D' b t P D F C sh sfs i h stk loc C\<^sub>0 M\<^sub>0 pc Cs frs)
      then have "P \<turnstile> D sees F,Static:t in D" by(simp add: has_field_sees[OF has_field_idemp])
      then have D'eq: "D' = D" using exec_step_ind_Putstatic_Called.hyps(1) by simp
      obtain sobj where "sh D = Some sobj"
       using exec_step_ind_Putstatic_Called.hyps(2) exec_step_ind_Putstatic_Called.prems(8,13)
        by(fastforce dest!: exec_step_input_StepID)
      then show ?case using exec_step_ind_Putstatic_Called.hyps
                         exec_step_ind_Putstatic_Called.prems(1-7) D'eq
        by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_Putstatic_Done show ?case
       using exec_step_ind_Putstatic_Done.hyps exec_step_ind_Putstatic_Done.prems(1-7)
        by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_Putstatic_Init show ?case
       using exec_step_ind_Putstatic_Init.hyps exec_step_ind_Putstatic_Init.prems(1-7)
        by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_Checkcast show ?case
        using exec_step_ind_Checkcast.prems(1-7) by auto
    next
      case exec_step_ind_Checkcast_Error show ?case using exec_step_ind_Checkcast_Error.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Invoke_Null show ?case using exec_step_ind_Invoke_Null.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Invoke_NoMethod show ?case using exec_step_ind_Invoke_NoMethod.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Invoke_Static show ?case using exec_step_ind_Invoke_Static.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case (exec_step_ind_Invoke ps n stk r C h D b Ts T mxs mxl\<^sub>0 ins xt P)
      have "classes_above P D \<subseteq> cset"
       using exec_step_ind_Invoke.hyps(2,3,5) exec_step_ind_Invoke.prems(1,8,10,13)
        rtrancl_trans[OF sees_method_decl_above[OF exec_step_ind_Invoke.hyps(6)]]
       by(auto dest!: exec_step_input_StepID is_ptrD) blast+
      then show ?case
        using exec_step_ind_Invoke.hyps(7) exec_step_ind_Invoke.prems(1-7) by auto
    next
      case exec_step_ind_Invokestatic_NoMethod
       show ?case using exec_step_ind_Invokestatic_NoMethod.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Invokestatic_NonStatic
       show ?case using exec_step_ind_Invokestatic_NonStatic.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case (exec_step_ind_Invokestatic_Called ps n stk D b Ts T mxs mxl\<^sub>0 ins xt P C M)
      have "seeing_class P C M = Some D" using exec_step_ind_Invokestatic_Called.hyps(2,3)
        by(fastforce simp: seeing_class_def)
      then have "classes_above P D \<subseteq> cset" using exec_step_ind_Invokestatic_Called.prems(8-9)
        by(fastforce dest!: exec_step_input_StepID)
      then show ?case
        using exec_step_ind_Invokestatic_Called.hyps exec_step_ind_Invokestatic_Called.prems(1-7)
          by(auto simp: seeing_class_def)
    next
      case (exec_step_ind_Invokestatic_Done ps n stk D b Ts T mxs mxl\<^sub>0 ins xt P C M)
      have "seeing_class P C M = Some D" using exec_step_ind_Invokestatic_Done.hyps(2,3)
        by(fastforce simp: seeing_class_def)
      then have "classes_above P D \<subseteq> cset" using exec_step_ind_Invokestatic_Done.prems(8-9)
        by(fastforce dest!: exec_step_input_StepID)
      then show ?case
       using exec_step_ind_Invokestatic_Done.hyps exec_step_ind_Invokestatic_Done.prems(1-7)
        by auto blast+
    next
      case exec_step_ind_Invokestatic_Init show ?case
       using exec_step_ind_Invokestatic_Init.hyps exec_step_ind_Invokestatic_Init.prems(1-7)
        by auto blast+
    next
      case exec_step_ind_Return_Last_Init show ?case
       using exec_step_ind_Return_Last_Init.prems(1-7) by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_Return_Last show ?case
       using exec_step_ind_Return_Last.prems(1-7) by auto
    next
      case exec_step_ind_Return_Init show ?case
       using exec_step_ind_Return_Init.prems(1-7) by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_Return_NonStatic show ?case
       using exec_step_ind_Return_NonStatic.prems(1-7) by auto
    next
      case exec_step_ind_Return_Static show ?case
       using exec_step_ind_Return_Static.prems(1-7) by auto
    next
      case exec_step_ind_Pop show ?case using exec_step_ind_Pop.prems(1-7) by auto
    next
      case exec_step_ind_IAdd show ?case using exec_step_ind_IAdd.prems(1-7)by auto
    next
      case exec_step_ind_IfFalse_False show ?case
        using exec_step_ind_IfFalse_False.prems(1-7) by auto
    next
      case exec_step_ind_IfFalse_nFalse show ?case
        using exec_step_ind_IfFalse_nFalse.prems(1-7) by auto
    next
      case exec_step_ind_CmpEq show ?case using exec_step_ind_CmpEq.prems(1-7) by auto
    next
      case exec_step_ind_Goto show ?case using exec_step_ind_Goto.prems(1-7) by auto
    next
      case exec_step_ind_Throw show ?case using exec_step_ind_Throw.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case exec_step_ind_Throw_Null show ?case using exec_step_ind_Throw_Null.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    next
      case (exec_step_ind_Init_None_Called sh C Cs P)
      have "classes_above P C \<subseteq> cset" using exec_step_ind_Init_None_Called.prems(8,11)
        by(auto dest!: exec_step_input_StepCD)
      then show ?case using exec_step_ind_Init_None_Called.prems(1-7)
        by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_Init_Done show ?case
       using exec_step_ind_Init_Done.prems(1-7) by auto
    next
      case exec_step_ind_Init_Processing show ?case
       using exec_step_ind_Init_Processing.prems(1-7) by auto
    next
      case exec_step_ind_Init_Error show ?case
       using exec_step_ind_Init_Error.prems(1-7) by auto
    next
      case exec_step_ind_Init_Prepared_Object show ?case
       using exec_step_ind_Init_Prepared_Object.hyps
             exec_step_ind_Init_Prepared_Object.prems(1-7,10)
        by(auto split: if_split_asm dest!: exec_step_input_StepCD) blast+
    next
      case exec_step_ind_Init_Prepared_nObject show ?case
       using exec_step_ind_Init_Prepared_nObject.hyps exec_step_ind_Init_Prepared_nObject.prems(1-7)
        by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_Init show ?case
       using exec_step_ind_Init.prems(1-7,8,12)
        by(auto simp: split_beta dest!: exec_step_input_StepC2D)
    next
      case (exec_step_ind_InitThrow C Cs a P h stk loc C\<^sub>0 M\<^sub>0 pc ics frs sh)
      obtain sfs where "sh C = Some(sfs,Processing)"
        using exec_step_ind_InitThrow.prems(8,14) by(fastforce dest!: exec_step_input_StepTD)
      then show ?case using exec_step_ind_InitThrow.prems(1-7)
        by(auto split: if_split_asm) blast+
    next
      case exec_step_ind_InitThrow_End show ?case using exec_step_ind_InitThrow_End.prems(1-7)
        by(auto simp del: find_handler.simps dest!: find_handler_pieces) blast+
    qed
  qed(simp)
qed(simp)

\<comment> \<open> Forward promises (classes that will be collected by the end of execution) \<close>
  \<comment> \<open> - Classes that the current instruction will check initialization for will be collected \<close>
  \<comment> \<open> - Class whose initialization is actively being called by the current frame will be collected \<close>

text \<open> We prove that an @{term ics} of @{text "Calling C Cs"} (meaning @{text C}'s
 initialization procedure is actively being called) means that classes above @{text C}
 will be collected by @{term cbig} (i.e., by the end of execution) using proof by
 induction, proving the base and IH separately. \<close>

\<comment> \<open> base case: @{term Object} \<close>
lemma Calling_collects_base:
assumes big: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and ics: "ics_of (hd(frames_of \<sigma>)) = Calling Object Cs"
shows "classes_above P Object \<subseteq> cset \<union> cset'"
proof(cases "frames_of \<sigma>")
  case Nil then show ?thesis using nend by(clarsimp simp: JVMendset_def)
next
  case (Cons f1 frs1)
  then obtain stk loc C M pc ics where "f1 = (stk,loc,C,M,pc,ics)" by(cases f1)
  then show ?thesis
    using JVMSmartCollectionSemantics.cbig_stepD[OF big nend] nend ics Cons
     by(clarsimp simp: JVMSmartCollectionSemantics.csmall_def JVMendset_def)
qed

\<comment> \<open> IH case where @{text C} has not been prepared yet \<close>
lemma Calling_None_next_state:
assumes ics: "ics_of (hd(frames_of \<sigma>)) = Calling C Cs"
 and none: "sheap \<sigma> C = None"
 and set: "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
               \<longrightarrow> classes_above P C' \<subseteq> cset"
 and \<sigma>': "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
shows "\<sigma>' \<notin> JVMendset \<and> ics_of (hd(frames_of \<sigma>')) = Calling C Cs
  \<and> (\<exists>sfs. sheap \<sigma>' C = Some(sfs,Prepared))
  \<and> (\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> C \<noteq> C'
    \<longrightarrow> (\<exists>sfs i. sheap \<sigma>' C' = Some(sfs,i)) \<longrightarrow> classes_above P C' \<subseteq> cset)"
proof(cases "frames_of \<sigma> = [] \<or> (\<exists>x. fst \<sigma> = Some x)")
  case True then show ?thesis using assms
     by(cases \<sigma>, auto simp: JVMSmartCollectionSemantics.csmall_def)
next
  case False
  then obtain f1 frs1 where frs: "frames_of \<sigma> = f1#frs1" by(cases "frames_of \<sigma>", auto)
  obtain stk loc C' M pc ics where f1: "f1 = (stk,loc,C',M,pc,ics)" by(cases f1)
  show ?thesis using f1 frs False assms
    by(cases \<sigma>, cases "method P C clinit")
      (clarsimp simp: split_beta JVMSmartCollectionSemantics.csmall_def JVMendset_def)
qed

\<comment> \<open> IH case where @{text C} has been prepared (and has a direct superclass
 - i.e., is not @{term Object}) \<close>
lemma Calling_Prepared_next_state:
assumes sub: "P \<turnstile> C \<prec>\<^sup>1 D"
 and obj: "P \<turnstile> D \<preceq>\<^sup>* Object"
 and ics: "ics_of (hd(frames_of \<sigma>)) = Calling C Cs"
 and prep: "sheap \<sigma> C = Some(sfs,Prepared)"
 and set: "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> C \<noteq> C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
                \<longrightarrow> classes_above P C' \<subseteq> cset"
 and \<sigma>': "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
shows "\<sigma>' \<notin> JVMendset \<and> ics_of (hd (frames_of \<sigma>')) = Calling D (C#Cs)
  \<and> (\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>' C' = Some(sfs,i))
         \<longrightarrow> classes_above P C' \<subseteq> cset)"
using sub
proof(cases "C=Object")
  case nobj:False show ?thesis
  proof(cases "frames_of \<sigma> = [] \<or> (\<exists>x. fst \<sigma> = Some x)")
    case True then show ?thesis using assms
       by(cases \<sigma>, auto simp: JVMSmartCollectionSemantics.csmall_def)
  next
    case False
    then obtain f1 frs1 where frs: "frames_of \<sigma> = f1#frs1" by(cases "frames_of \<sigma>", auto)
    obtain stk loc C' M pc ics where f1: "f1 = (stk,loc,C',M,pc,ics)" by(cases f1)
    have "C \<noteq> D" using sub obj subcls_self_superclass by auto
    then have dimp: "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow>  P \<turnstile> C \<preceq>\<^sup>* C' \<and> C \<noteq> C'"
      using sub subcls_of_Obj_acyclic[OF obj] by fastforce
    have "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> C \<noteq> C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>' C' = Some(sfs,i))
               \<longrightarrow> classes_above P C' \<subseteq> cset"
     using f1 frs False nobj assms
      by(cases \<sigma>, cases "method P C clinit")
        (auto simp: JVMSmartCollectionSemantics.csmall_def JVMendset_def)
    then have "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>' C' = Some(sfs,i))
         \<longrightarrow> classes_above P C' \<subseteq> cset" using sub dimp by auto
    then show ?thesis using f1 frs False nobj assms
      by(cases \<sigma>, cases "method P C clinit")
        (auto dest:subcls1D simp: JVMSmartCollectionSemantics.csmall_def JVMendset_def)
  qed
qed(simp)

\<comment> \<open> completed IH case: non-@{term Object} (pulls together above IH cases) \<close>
lemma Calling_collects_IH:
assumes sub: "P \<turnstile> C \<prec>\<^sup>1 D"
 and obj: "P \<turnstile> D \<preceq>\<^sup>* Object"
 and step: "\<And>\<sigma> cset' Cs. (\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma> \<Longrightarrow> \<sigma> \<notin> JVMendset
           \<Longrightarrow> ics_of (hd(frames_of \<sigma>)) = Calling D Cs
           \<Longrightarrow> \<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
                   \<longrightarrow> classes_above P C' \<subseteq> cset
           \<Longrightarrow> classes_above P D \<subseteq> cset \<union> cset'"
 and big: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "ics_of (hd(frames_of \<sigma>)) = Calling C Cs"
 and set: "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
               \<longrightarrow> classes_above P C' \<subseteq> cset"
shows "classes_above P C \<subseteq> cset \<union> cset'"
proof(cases "frames_of \<sigma>")
  case Nil then show ?thesis using nend by(clarsimp simp: JVMendset_def)
next
  case (Cons f1 frs1)
  show ?thesis using sub
  proof(cases "\<exists>sfs i. sheap \<sigma> C = Some(sfs,i)")
    case True then show ?thesis using set by auto
  next
    case False
    obtain stk loc C' M pc ics where f1: "f1 = (stk,loc,C',M,pc,ics)" by(cases f1)
    then obtain \<sigma>1 coll1 coll where \<sigma>1: "(\<sigma>1, coll1) \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
      "cset' = coll1 \<union> coll" "(\<sigma>', coll) \<in> JVMSmartCollectionSemantics.cbig P \<sigma>1"
      using JVMSmartCollectionSemantics.cbig_stepD[OF big nend] by clarsimp
    show ?thesis
    proof(cases "\<exists>sfs. sheap \<sigma> C = Some(sfs,Prepared)")
      case True
      then obtain sfs where sfs: "sheap \<sigma> C = Some(sfs,Prepared)" by clarsimp
      have set': "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> C\<noteq>C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
               \<longrightarrow> classes_above P C' \<subseteq> cset" using set by auto
      then have "\<sigma>1 \<notin> JVMendset \<and> ics_of (hd (frames_of \<sigma>1)) = Calling D (C#Cs)"
          "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>1 C' = Some(sfs,i))
               \<longrightarrow> classes_above P C' \<subseteq> cset"
        using Calling_Prepared_next_state[OF sub obj curr sfs set' \<sigma>1(1)]
         by(auto simp: JVMSmartCollectionSemantics.csmall_def)
      then show ?thesis using step[of coll \<sigma>1] classes_above_def2[OF sub] \<sigma>1 f1 Cons nend curr
        by(clarsimp simp: JVMSmartCollectionSemantics.csmall_def JVMendset_def)
    next
      case none: False \<comment> \<open> @{text "Calling C Cs"} is the next @{text ics}, but after that is @{text "Calling D (C#Cs)"} \<close>
      then have sNone: "sheap \<sigma> C = None" using False by(cases "sheap \<sigma> C", auto)
      then have nend1: "\<sigma>1 \<notin> JVMendset" and curr1: "ics_of (hd (frames_of \<sigma>1)) = Calling C Cs"
        and prep: "\<exists>sfs. sheap \<sigma>1 C = \<lfloor>(sfs, Prepared)\<rfloor>"
        and set1: "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> C \<noteq> C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>1 C' = \<lfloor>(sfs, i)\<rfloor>)
               \<longrightarrow> classes_above P C' \<subseteq> cset"
       using Calling_None_next_state[OF curr sNone set \<sigma>1(1)] by simp+
      then obtain f2 frs2 where frs2: "frames_of \<sigma>1 = f2#frs2"
        by(cases \<sigma>1, cases "frames_of \<sigma>1", clarsimp simp: JVMendset_def)
      obtain sfs1 where sfs1: "sheap \<sigma>1 C = Some(sfs1,Prepared)" using prep by clarsimp
      obtain stk2 loc2 C2 M2 pc2 ics2 where f2: "f2 = (stk2,loc2,C2,M2,pc2,ics2)" by(cases f2)
      then obtain \<sigma>2 coll2 coll' where \<sigma>2: "(\<sigma>2, coll2) \<in> JVMSmartCollectionSemantics.csmall P \<sigma>1"
        "coll = coll2 \<union> coll'" "(\<sigma>', coll') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>2"
        using JVMSmartCollectionSemantics.cbig_stepD[OF \<sigma>1(3) nend1] by clarsimp
      then have "\<sigma>2 \<notin> JVMendset \<and> ics_of (hd (frames_of \<sigma>2)) = Calling D (C#Cs)"
          "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>2 C' = Some(sfs,i))
               \<longrightarrow> classes_above P C' \<subseteq> cset"
        using Calling_Prepared_next_state[OF sub obj curr1 sfs1 set1 \<sigma>2(1)]
         by(auto simp: JVMSmartCollectionSemantics.csmall_def)
      then show ?thesis using step[of coll' \<sigma>2] classes_above_def2[OF sub] \<sigma>2 \<sigma>1 f2 frs2 f1 Cons
        nend1 nend curr1 curr
        by(clarsimp simp: JVMSmartCollectionSemantics.csmall_def JVMendset_def)
    qed
  qed
qed

\<comment> \<open>pulls together above base and IH cases \<close>
lemma Calling_collects:
assumes sub: "P \<turnstile> C \<preceq>\<^sup>* Object"
 and "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>"
 and "\<sigma> \<notin> JVMendset"
 and "ics_of (hd(frames_of \<sigma>)) = Calling C Cs"
 and "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
           \<longrightarrow> classes_above P C' \<subseteq> cset"
 and "cset' \<subseteq> cset"
shows "classes_above P C \<subseteq> cset"
proof -
  have base: "\<forall>\<sigma> cset' Cs.
       (\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma> \<longrightarrow> \<sigma> \<notin> JVMendset
       \<longrightarrow> ics_of (hd (frames_of \<sigma>)) = Calling Object Cs
       \<longrightarrow> (\<forall>C'. P \<turnstile> Object \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = \<lfloor>(sfs, i)\<rfloor>)
             \<longrightarrow> classes_above P C' \<subseteq> cset)
       \<longrightarrow> classes_above P Object \<subseteq> JVMcombine cset cset'" using Calling_collects_base by simp
  have IH: "\<And>y z. P \<turnstile> y \<prec>\<^sup>1 z \<Longrightarrow>
        P \<turnstile> z \<preceq>\<^sup>* Object \<Longrightarrow>
        \<forall>\<sigma> cset' Cs. (\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma> \<longrightarrow> \<sigma> \<notin> JVMendset
           \<longrightarrow> ics_of (hd(frames_of \<sigma>)) = Calling z Cs
           \<longrightarrow> (\<forall>C'. P \<turnstile> z \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
                 \<longrightarrow> classes_above P C' \<subseteq> cset)
           \<longrightarrow> classes_above P z \<subseteq> cset \<union> cset' \<Longrightarrow>
        \<forall>\<sigma> cset' Cs. (\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma> \<longrightarrow> \<sigma> \<notin> JVMendset
           \<longrightarrow> ics_of (hd(frames_of \<sigma>)) = Calling y Cs
           \<longrightarrow> (\<forall>C'. P \<turnstile> y \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
                 \<longrightarrow> classes_above P C' \<subseteq> cset)
           \<longrightarrow> classes_above P y \<subseteq> cset \<union> cset'"
     using Calling_collects_IH by blast
  have result: "\<forall>\<sigma> cset' Cs.
       (\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma> \<longrightarrow> \<sigma> \<notin> JVMendset
       \<longrightarrow> ics_of (hd(frames_of \<sigma>)) = Calling C Cs
       \<longrightarrow> (\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
               \<longrightarrow> classes_above P C' \<subseteq> cset)
       \<longrightarrow> classes_above P C \<subseteq> cset \<union> cset'"
    using converse_rtrancl_induct[OF sub,
      where P="\<lambda>C. \<forall>\<sigma> cset' Cs. (\<sigma>',cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma> \<longrightarrow> \<sigma> \<notin> JVMendset
                    \<longrightarrow> ics_of (hd(frames_of \<sigma>)) = Calling C Cs
                    \<longrightarrow> (\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
                              \<longrightarrow> classes_above P C' \<subseteq> cset)
                    \<longrightarrow> classes_above P C \<subseteq> cset \<union> cset'"]
    using base IH by blast
  then show ?thesis using assms by blast
qed

(*******************)
text "Instructions that call the initialization procedure will collect classes above
  the class initialized by the end of execution (using the above @{text Calling_collects})."

lemma New_collects:
assumes sub: "P \<turnstile> C \<preceq>\<^sup>* Object"
 and cbig: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = New C"
 and ics: "ics_of (hd(frames_of \<sigma>)) = No_ics"
 and sheap: "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
           \<longrightarrow> classes_above P C' \<subseteq> cset"
 and smart: "cset' \<subseteq> cset"
shows "classes_above P C \<subseteq> cset"
proof(cases "(\<exists>sfs i. sheap \<sigma> C = Some(sfs,i) \<and> i = Done)")
  case True then show ?thesis using sheap by auto
next
  case False
  obtain n where nstep: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma> n"
    and "n \<noteq> 0" using nend cbig JVMSmartCollectionSemantics.cbig_def2
   JVMSmartCollectionSemantics.csmall_nstep_base  by (metis empty_iff insert_iff)
  then show ?thesis
  proof(cases n)
    case (Suc n1)
    then obtain \<sigma>1 cset0 cset1 where \<sigma>1: "(\<sigma>1,cset1) \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
       "cset' = cset1 \<union> cset0" "(\<sigma>',cset0) \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma>1 n1"
      using JVMSmartCollectionSemantics.csmall_nstep_SucD nstep by blast
    obtain xp h frs sh where "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
    then have ics1: "ics_of (hd(frames_of \<sigma>1)) = Calling C []"
      and sheap': "sheap \<sigma> = sheap \<sigma>1" and nend1: "\<sigma>1 \<notin> JVMendset"
     using JVM_New_next_step[OF _ nend curr] \<sigma>1(1) False ics
       by(simp add: JVMSmartCollectionSemantics.csmall_def)+
    have "\<sigma>' \<in> JVMendset" using cbig JVMSmartCollectionSemantics.cbig_def2 by blast
    then have cbig1: "(\<sigma>', cset0) \<in> JVMSmartCollectionSemantics.cbig P \<sigma>1"
      using JVMSmartCollectionSemantics.cbig_def2 \<sigma>1(3) by blast
    have sheap1: "\<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>1 C' = \<lfloor>(sfs, i)\<rfloor>)
     \<longrightarrow> classes_above P C' \<subseteq> cset" using sheap' sheap by simp
    have "cset0 \<subseteq> cset" using \<sigma>1(2) smart by blast
    then have "classes_above P C \<subseteq> cset"
      using Calling_collects[OF sub cbig1 nend1 ics1 sheap1] by simp
    then show ?thesis using \<sigma>1(2) smart by auto
  qed(simp)
qed

lemma Getstatic_collects:
assumes sub: "P \<turnstile> D \<preceq>\<^sup>* Object"
 and cbig: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Getstatic C F D"
 and ics: "ics_of (hd(frames_of \<sigma>)) = No_ics"
 and fC: "P \<turnstile> C has F,Static:t in D"
 and sheap: "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
           \<longrightarrow> classes_above P C' \<subseteq> cset"
 and smart: "cset' \<subseteq> cset"
shows "classes_above P D \<subseteq> cset"
proof(cases "(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)
           \<or> (ics_of(hd(frames_of \<sigma>)) = Called [])")
  case True then show ?thesis
  proof(cases "\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done")
    case True then show ?thesis using sheap by auto
  next
    case False
    then have "ics_of(hd(frames_of \<sigma>)) = Called []" using True by clarsimp
    then show ?thesis using ics by auto
  qed
next
  case False
  obtain n where nstep: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma> n"
    and "n \<noteq> 0" using nend cbig JVMSmartCollectionSemantics.cbig_def2
   JVMSmartCollectionSemantics.csmall_nstep_base  by (metis empty_iff insert_iff)
  then show ?thesis
  proof(cases n)
    case (Suc n1)
    then obtain \<sigma>1 cset0 cset1 where \<sigma>1: "(\<sigma>1,cset1) \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
       "cset' = cset1 \<union> cset0" "(\<sigma>',cset0) \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma>1 n1"
      using JVMSmartCollectionSemantics.csmall_nstep_SucD nstep by blast
    obtain xp h frs sh where "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
    then have curr1: "ics_of (hd(frames_of \<sigma>1)) = Calling D []"
      and sheap': "sheap \<sigma> = sheap \<sigma>1" and nend1: "\<sigma>1 \<notin> JVMendset"
     using JVM_Getstatic_next_step[OF _ nend curr fC] \<sigma>1(1) False ics
       by(simp add: JVMSmartCollectionSemantics.csmall_def)+
    have "\<sigma>' \<in> JVMendset" using cbig JVMSmartCollectionSemantics.cbig_def2 by blast
    then have cbig1: "(\<sigma>', cset0) \<in> JVMSmartCollectionSemantics.cbig P \<sigma>1"
      using JVMSmartCollectionSemantics.cbig_def2 \<sigma>1(3) by blast
    have sheap1: "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>1 C' = \<lfloor>(sfs, i)\<rfloor>)
     \<longrightarrow> classes_above P C' \<subseteq> cset" using sheap' sheap by simp
    have "cset0 \<subseteq> cset" using \<sigma>1(2) smart by blast
    then have "classes_above P D \<subseteq> cset"
      using Calling_collects[OF sub cbig1 nend1 curr1 sheap1] by simp
    then show ?thesis using \<sigma>1(2) smart by auto
  qed(simp)
qed

lemma Putstatic_collects:
assumes sub: "P \<turnstile> D \<preceq>\<^sup>* Object"
 and cbig: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Putstatic C F D"
 and ics: "ics_of (hd(frames_of \<sigma>)) = No_ics"
 and fC: "P \<turnstile> C has F,Static:t in D"
 and sheap: "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
           \<longrightarrow> classes_above P C' \<subseteq> cset"
 and smart: "cset' \<subseteq> cset"
shows "classes_above P D \<subseteq> cset"
proof(cases "(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)
           \<or> (ics_of(hd(frames_of \<sigma>)) = Called [])")
  case True then show ?thesis
  proof(cases "\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done")
    case True then show ?thesis using sheap by auto
  next
    case False
    then have "ics_of(hd(frames_of \<sigma>)) = Called []" using True by clarsimp
    then show ?thesis using ics by auto
  qed
next
  case False
  obtain n where nstep: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma> n"
    and "n \<noteq> 0" using nend cbig JVMSmartCollectionSemantics.cbig_def2
   JVMSmartCollectionSemantics.csmall_nstep_base  by (metis empty_iff insert_iff)
  then show ?thesis
  proof(cases n)
    case (Suc n1)
    then obtain \<sigma>1 cset0 cset1 where \<sigma>1: "(\<sigma>1,cset1) \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
       "cset' = cset1 \<union> cset0" "(\<sigma>',cset0) \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma>1 n1"
      using JVMSmartCollectionSemantics.csmall_nstep_SucD nstep by blast
    obtain xp h frs sh where "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
    then have curr1: "ics_of (hd(frames_of \<sigma>1)) = Calling D []"
      and sheap': "sheap \<sigma> = sheap \<sigma>1" and nend1: "\<sigma>1 \<notin> JVMendset"
     using JVM_Putstatic_next_step[OF _ nend curr fC] \<sigma>1(1) False ics
       by(simp add: JVMSmartCollectionSemantics.csmall_def)+
    have "\<sigma>' \<in> JVMendset" using cbig JVMSmartCollectionSemantics.cbig_def2 by blast
    then have cbig1: "(\<sigma>', cset0) \<in> JVMSmartCollectionSemantics.cbig P \<sigma>1"
      using JVMSmartCollectionSemantics.cbig_def2 \<sigma>1(3) by blast
    have sheap1: "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>1 C' = \<lfloor>(sfs, i)\<rfloor>)
     \<longrightarrow> classes_above P C' \<subseteq> cset" using sheap' sheap by simp
    have "cset0 \<subseteq> cset" using \<sigma>1(2) smart by blast
    then have "classes_above P D \<subseteq> cset"
      using Calling_collects[OF sub cbig1 nend1 curr1 sheap1] by simp
    then show ?thesis using \<sigma>1(2) smart by auto
  qed(simp)
qed

lemma Invokestatic_collects:
assumes sub: "P \<turnstile> D \<preceq>\<^sup>* Object"
 and cbig: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>"
 and smart: "cset' \<subseteq> cset"
 and nend: "\<sigma> \<notin> JVMendset"
 and curr: "curr_instr P (hd(frames_of \<sigma>)) = Invokestatic C M n"
 and ics: "ics_of (hd(frames_of \<sigma>)) = No_ics"
 and mC: "P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D"
 and sheap: "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma> C' = Some(sfs,i))
           \<longrightarrow> classes_above P C' \<subseteq> cset"
shows "classes_above P D \<subseteq> cset"
proof(cases "(\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done)
           \<or> (ics_of(hd(frames_of \<sigma>)) = Called [])")
  case True then show ?thesis
  proof(cases "\<exists>sfs i. sheap \<sigma> D = Some(sfs,i) \<and> i = Done")
    case True then show ?thesis using sheap by auto
  next
    case False
    then have "ics_of(hd(frames_of \<sigma>)) = Called []" using True by clarsimp
    then show ?thesis using ics by auto
  qed
next
  case False
  obtain n where nstep: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma> n"
    and "n \<noteq> 0" using nend cbig JVMSmartCollectionSemantics.cbig_def2
   JVMSmartCollectionSemantics.csmall_nstep_base  by (metis empty_iff insert_iff)
  then show ?thesis
  proof(cases n)
    case (Suc n1)
    then obtain \<sigma>1 cset0 cset1 where \<sigma>1: "(\<sigma>1,cset1) \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
       "cset' = cset1 \<union> cset0" "(\<sigma>',cset0) \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma>1 n1"
      using JVMSmartCollectionSemantics.csmall_nstep_SucD nstep by blast
    obtain xp h frs sh where "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
    then have curr1: "ics_of (hd(frames_of \<sigma>1)) = Calling D []"
      and sheap': "sheap \<sigma> = sheap \<sigma>1" and nend1: "\<sigma>1 \<notin> JVMendset"
     using JVM_Invokestatic_next_step[OF _ nend curr mC] \<sigma>1(1) False ics
       by(simp add: JVMSmartCollectionSemantics.csmall_def)+
    have "\<sigma>' \<in> JVMendset" using cbig JVMSmartCollectionSemantics.cbig_def2 by blast
    then have cbig1: "(\<sigma>', cset0) \<in> JVMSmartCollectionSemantics.cbig P \<sigma>1"
      using JVMSmartCollectionSemantics.cbig_def2 \<sigma>1(3) by blast
    have sheap1: "\<forall>C'. P \<turnstile> D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>1 C' = \<lfloor>(sfs, i)\<rfloor>)
     \<longrightarrow> classes_above P C' \<subseteq> cset" using sheap' sheap by simp
    have "cset0 \<subseteq> cset" using \<sigma>1(2) smart by blast
    then have "classes_above P D \<subseteq> cset"
      using Calling_collects[OF sub cbig1 nend1 curr1 sheap1] by simp
    then show ?thesis using \<sigma>1(2) smart by auto
  qed(simp)
qed

(*********)

text "The @{text smart_out} execution function keeps the promise to
 collect above the initial class (@{term Test}):"
lemma jvm_smart_out_classes_above_Test:
assumes s: "(\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t" and P: "P \<in> jvm_progs" and t: "t \<in> jvm_tests"
shows "classes_above (jvm_make_test_prog P t) Test \<subseteq> cset\<^sub>s"
 (is "classes_above ?P ?D \<subseteq> ?cset")
proof -
  let ?\<sigma> = "start_state (t#P)" and ?M = main
  let ?ics = "ics_of (hd(frames_of ?\<sigma>))"
  have called: "?ics = Called [] \<Longrightarrow> classes_above ?P ?D \<subseteq> ?cset"
    by(simp add: start_state_def)
  then show ?thesis
  proof(cases "?ics = Called []")
    case True then show ?thesis using called by simp
  next
    case False
    from P t obtain wf_md where wf: "wf_prog wf_md (t#P)"
     by(auto simp: wf_jvm_prog_phi_def wf_jvm_prog_def)
    from jvm_make_test_prog_sees_Test_main[OF P t] obtain m where
     mC: "?P \<turnstile> ?D sees ?M,Static:[] \<rightarrow> Void = m in ?D" by fast
  (****)
    then have "?P \<turnstile> ?D \<preceq>\<^sup>* Object" by(rule sees_method_sub_Obj)
    moreover from s obtain cset' where
      cbig: "(\<sigma>', cset') \<in> JVMSmartCollectionSemantics.cbig ?P ?\<sigma>" and "cset' \<subseteq> ?cset" by clarsimp
    moreover have nend: "?\<sigma> \<notin> JVMendset" by(rule start_state_nend)
    moreover from start_prog_start_m_instrs[OF wf] t
    have curr: "curr_instr ?P (hd(frames_of ?\<sigma>)) = Invokestatic ?D ?M 0"
      by(simp add: start_state_def)
    moreover have ics: "?ics = No_ics"
      by(simp add: start_state_def)
    moreover note mC
    moreover from jvm_smart_out_classes_above_start_sheap[OF s]
    have sheap: "\<forall>C'. ?P \<turnstile> ?D \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap ?\<sigma> C' = Some(sfs,i))
              \<longrightarrow> classes_above ?P C' \<subseteq> ?cset" by(simp add: start_state_def)
    ultimately show ?thesis by(rule Invokestatic_collects)
  qed
qed

(**********************************************)
text "Using lemmas proving preservation of backward promises and keeping
 of forward promises, we prove that the smart algorithm collects at least
 the classes as the naive algorithm does."

\<comment> \<open> first over a single execution step (assumes promises) \<close>
lemma jvm_naive_to_smart_exec_collect:
assumes
\<comment> \<open> well-formedness \<close>
      wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and correct: "P,\<Phi> \<turnstile> (xp,h,frs,sh)\<surd>"
\<comment> \<open> defs \<close>
  and f': "hd frs = (stk,loc,C',M',pc,ics)"
\<comment> \<open> backward promises - will be collected prior \<close>
  and heap: "\<And>C fs. \<exists>a. h a = Some(C,fs) \<Longrightarrow> classes_above P C \<subseteq> cset"
  and sheap: "\<And>C sfs i. sh C = Some(sfs,i) \<Longrightarrow> classes_above P C \<subseteq> cset"
  and xcpts: "classes_above_xcpts P \<subseteq> cset"
  and frames: "classes_above_frames P frs \<subseteq> cset"
\<comment> \<open> forward promises - will be collected after if not already \<close>
  and init_class_prom: "\<And>C. ics = Called [] \<or> ics = No_ics
       \<Longrightarrow> coll_init_class P (instrs_of P C' M' ! pc) = Some C \<Longrightarrow> classes_above P C \<subseteq> cset"
  and Calling_prom: "\<And>C' Cs'. ics = Calling C' Cs' \<Longrightarrow> classes_above P C' \<subseteq> cset"
\<comment> \<open> collection \<close>
  and smart: "JVMexec_scollect P (xp,h,frs,sh) \<subseteq> cset"
shows "JVMexec_ncollect P (xp,h,frs,sh) \<subseteq> cset"
using assms
proof(cases frs)
  case (Cons f' frs')
  then have [simp]: "classes_above P C' \<subseteq> cset" using frames f' by simp
  let ?i = "instrs_of P C' M' ! pc"
  have cr': "P,\<Phi> \<turnstile> (xp,h,(stk,loc,C',M',pc,ics)#frs',sh)\<surd>" using correct f' Cons by simp
  from well_formed_stack_safe[OF wtp cr'] correct_state_Throwing_ex[OF cr'] obtain
    stack_safe: "stack_safe ?i h stk" and
    Throwing_ex: "\<And>Cs a. ics = Throwing Cs a \<Longrightarrow> \<exists>obj. h a = Some obj" by simp
  have confc: "conf_clinit P sh frs" using correct Cons by simp
  have Called_prom: "\<And>C' Cs'. ics = Called (C'#Cs')
           \<Longrightarrow> classes_above P C' \<subseteq> cset \<and> classes_above P (fst(method P C' clinit)) \<subseteq> cset"
  proof -
    fix C' Cs' assume [simp]: "ics = Called (C'#Cs')"
    then have "C' \<in> set(clinit_classes frs)" using f' Cons by simp
    then obtain sfs where shC': "sh C' = Some(sfs, Processing)" and "is_class P C'"
      using confc by(auto simp: conf_clinit_def)
    then have C'eq: "C' = fst(method P C' clinit)" using wf_sees_clinit wtp
      by(fastforce simp: is_class_def wf_jvm_prog_phi_def)
    then show "classes_above P C' \<subseteq> cset \<and> classes_above P (fst(method P C' clinit)) \<subseteq> cset"
      using sheap shC' by auto
  qed
  show ?thesis using Cons assms
  proof(cases xp)
    case None
    { assume ics: "ics = Called [] \<or> ics = No_ics"
      then have [simp]: "JVMexec_ncollect P (xp,h,frs,sh)
         = JVMinstr_ncollect P ?i h stk \<union> classes_above P C'
             \<union> classes_above_frames P frs \<union> classes_above_xcpts P"
        and [simp]: "JVMexec_scollect P (xp,h,frs,sh) = JVMinstr_scollect P ?i"
        using f' None Cons by auto
      have ?thesis using assms
      proof(cases ?i)
        case (New C)
        then have "classes_above P C \<subseteq> cset" using ics New assms by simp
        then show ?thesis using New xcpts frames smart f' by auto
      next
        case (Getfield F C) show ?thesis
        proof(cases "hd stk = Null")
          case True then show ?thesis using Getfield assms by simp
        next
          case False
          let ?C = "cname_of h (the_Addr (hd stk))"
          have above_stk: "classes_above P ?C \<subseteq> cset"
            using stack_safe heap f' False Cons Getfield by(auto dest!: is_ptrD) blast
          then show ?thesis using Getfield assms by auto
        qed
      next
        case (Getstatic C F D)
        show ?thesis
        proof(cases "\<exists>t. P \<turnstile> C has F,Static:t in D")
          case True
          then have above_D: "classes_above P D \<subseteq> cset" using ics init_class_prom Getstatic by simp
          have sub: "P \<turnstile> C \<preceq>\<^sup>* D" using has_field_decl_above True by blast
          then have above_C: "classes_between P C D - {D} \<subseteq> cset"
            using True Getstatic above_D smart f' by simp
          then have "classes_above P C \<subseteq> cset"
            using classes_above_sub_classes_between_eq[OF sub] above_D above_C by auto
          then show ?thesis using Getstatic assms by auto
        next
          case False then show ?thesis using Getstatic assms by auto
        qed
      next
        case (Putfield F C) show ?thesis
        proof(cases "hd(tl stk) = Null")
          case True then show ?thesis using Putfield assms by simp
        next
          case False
          let ?C = "cname_of h (the_Addr (hd (tl stk)))"
          have above_stk: "classes_above P ?C \<subseteq> cset"
            using stack_safe heap f' False Cons Putfield by(auto dest!: is_ptrD) blast
          then show ?thesis using Putfield assms by auto
        qed
      next
        case (Putstatic C F D)
        show ?thesis
        proof(cases "\<exists>t. P \<turnstile> C has F,Static:t in D")
          case True
          then have above_D: "classes_above P D \<subseteq> cset" using ics init_class_prom Putstatic by simp
          have sub: "P \<turnstile> C \<preceq>\<^sup>* D" using has_field_decl_above True by blast
          then have above_C: "classes_between P C D - {D} \<subseteq> cset"
            using True Putstatic above_D smart f' by simp
          then have "classes_above P C \<subseteq> cset"
            using classes_above_sub_classes_between_eq[OF sub] above_D above_C by auto
          then show ?thesis using Putstatic assms by auto
        next
          case False then show ?thesis using Putstatic assms by auto
        qed
      next
        case (Checkcast C) show ?thesis
        proof(cases "hd stk = Null")
          case True then show ?thesis using Checkcast assms by simp
        next
          case False
          let ?C = "cname_of h (the_Addr (hd stk))"
          have above_stk: "classes_above P ?C \<subseteq> cset"
            using stack_safe heap False Cons f' Checkcast by(auto dest!: is_ptrD) blast
          then show ?thesis using above_stk Checkcast assms by(cases "hd stk = Null", auto)
        qed
      next
        case (Invoke M n) show ?thesis
        proof(cases "stk ! n = Null")
          case True then show ?thesis using Invoke assms by simp
        next
          case False
          let ?C = "cname_of h (the_Addr (stk ! n))"
          have above_stk: "classes_above P ?C \<subseteq> cset" using stack_safe heap False Cons f' Invoke
            by(auto dest!: is_ptrD) blast
          then show ?thesis using Invoke assms by auto
        qed
      next
        case (Invokestatic C M n)
        let ?D = "fst (method P C M)"
        show ?thesis
        proof(cases "\<exists>Ts T m D. P \<turnstile> C sees M,Static:Ts \<rightarrow> T = m in D")
          case True
          then have above_D: "classes_above P ?D \<subseteq> cset" using ics init_class_prom Invokestatic
            by(simp add: seeing_class_def)
          have sub: "P \<turnstile> C \<preceq>\<^sup>* ?D" using method_def2 sees_method_decl_above True by auto
          then show ?thesis
          proof(cases "C = ?D")
            case True then show ?thesis
              using Invokestatic above_D xcpts frames smart f' by auto
          next
            case False
            then have above_C: "classes_between P C ?D - {?D} \<subseteq> cset"
              using True Invokestatic above_D smart f' by simp
            then have "classes_above P C \<subseteq> cset"
              using classes_above_sub_classes_between_eq[OF sub] above_D above_C by auto
            then show ?thesis using Invokestatic assms by auto
          qed
        next
          case False then show ?thesis using Invokestatic assms by auto
        qed
      next
        case Throw show ?thesis
        proof(cases "hd stk = Null")
          case True then show ?thesis using Throw assms by simp
        next
          case False
          let ?C = "cname_of h (the_Addr (hd stk))"
          have above_stk: "classes_above P ?C \<subseteq> cset"
            using stack_safe heap False Cons f' Throw by(auto dest!: is_ptrD) blast
          then show ?thesis using above_stk Throw assms by auto
        qed
      next
        case Load then show ?thesis using assms by auto
      next
        case Store then show ?thesis using assms by auto
      next
        case Push then show ?thesis using assms by auto
      next
        case Goto then show ?thesis using assms by auto
      next
        case IfFalse then show ?thesis using assms by auto
      qed(auto)
    }
    moreover
    { fix C1 Cs1 assume ics: "ics = Called (C1#Cs1)"
      then have ?thesis using None Cons Called_prom[OF ics] xcpts frames f' by simp
    }
    moreover
    { fix Cs1 a assume ics: "ics = Throwing Cs1 a"
      then obtain C fs where "h a = Some(C,fs)" using Throwing_ex by fastforce
      then have above_stk: "classes_above P (cname_of h a) \<subseteq> cset" using heap by auto
      then have ?thesis using ics None Cons xcpts frames f' by simp
    }
    moreover
    { fix C1 Cs1 assume ics: "ics = Calling C1 Cs1"
      then have ?thesis using None Cons Calling_prom[OF ics] xcpts frames f' by simp
    }
    ultimately show ?thesis by (metis ics_classes.cases list.exhaust)
  qed(simp)
qed(simp)

\<comment> \<open> ... which is the same as @{term csmall} \<close>
lemma jvm_naive_to_smart_csmall:
assumes
\<comment> \<open> well-formedness \<close>
      wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and correct: "P,\<Phi> \<turnstile> (xp,h,frs,sh)\<surd>"
\<comment> \<open> defs \<close>
  and f': "hd frs = (stk,loc,C',M',pc,ics)"
\<comment> \<open> backward promises - will be collected prior \<close>
  and heap: "\<And>C fs. \<exists>a. h a = Some(C,fs) \<Longrightarrow> classes_above P C \<subseteq> cset"
  and sheap: "\<And>C sfs i. sh C = Some(sfs,i) \<Longrightarrow> classes_above P C \<subseteq> cset"
  and xcpts: "classes_above_xcpts P \<subseteq> cset"
  and frames: "classes_above_frames P frs \<subseteq> cset"
\<comment> \<open> forward promises - will be collected after if not already \<close>
  and init_class_prom: "\<And>C. ics = Called [] \<or> ics = No_ics
    \<Longrightarrow> coll_init_class P (instrs_of P C' M' ! pc) = Some C \<Longrightarrow> classes_above P C \<subseteq> cset"
  and Calling_prom: "\<And>C' Cs'. ics = Calling C' Cs' \<Longrightarrow> classes_above P C' \<subseteq> cset"
\<comment> \<open> collections \<close>
  and smart_coll: "(\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.csmall P (xp,h,frs,sh)"
  and naive_coll: "(\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.csmall P (xp,h,frs,sh)"
  and smart: "cset\<^sub>s \<subseteq> cset"
shows "cset\<^sub>n \<subseteq> cset"
using jvm_naive_to_smart_exec_collect[where h=h and sh=sh, OF assms(1-9)]
      smart smart_coll naive_coll
   by(fastforce simp: JVMNaiveCollectionSemantics.csmall_def
                      JVMSmartCollectionSemantics.csmall_def)

\<comment> \<open> ...which means over @{term csmall_nstep}, stepping from the end state
 (the point by which future promises will have been fulfilled) (uses backward
 and forward promise lemmas) \<close>
lemma jvm_naive_to_smart_csmall_nstep:
"\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P;
   P,\<Phi> \<turnstile> (xp,h,frs,sh)\<surd>;
   hd frs = (stk,loc,C',M',pc,ics);
   \<And>C fs. \<exists>a. h a = Some(C,fs) \<Longrightarrow> classes_above P C \<subseteq> cset;
   \<And>C sfs i. sh C = Some(sfs,i) \<Longrightarrow> classes_above P C \<subseteq> cset;
   classes_above_xcpts P \<subseteq> cset;
   classes_above_frames P frs \<subseteq> cset;
   \<And>C. ics = Called [] \<or> ics = No_ics
      \<Longrightarrow> coll_init_class P (instrs_of P C' M' ! pc) = Some C \<Longrightarrow> classes_above P C \<subseteq> cset;
   \<And>C' Cs'. ics = Calling C' Cs' \<Longrightarrow> classes_above P C' \<subseteq> cset;
  (\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.csmall_nstep P (xp,h,frs,sh) n;
  (\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.csmall_nstep P (xp,h,frs,sh) n;
   cset\<^sub>s \<subseteq> cset;
   \<sigma>' \<in> JVMendset \<rbrakk>
  \<Longrightarrow> cset\<^sub>n \<subseteq> cset"
proof(induct n arbitrary: xp h frs sh stk loc C' M' pc ics \<sigma>' cset\<^sub>n cset\<^sub>s cset)
  case 0 then show ?case
    using JVMNaiveCollectionSemantics.csmall_nstep_base subsetI old.prod.inject singletonD
      by (metis (no_types, lifting) equals0D)
next
  case (Suc n1)
  let ?\<sigma> = "(xp,h,frs,sh)"
  obtain \<sigma>1 cset1 cset' where \<sigma>1: "(\<sigma>1, cset1) \<in> JVMNaiveCollectionSemantics.csmall P ?\<sigma>"
    "cset\<^sub>n = cset1 \<union> cset'" "(\<sigma>', cset') \<in> JVMNaiveCollectionSemantics.csmall_nstep P \<sigma>1 n1"
    using JVMNaiveCollectionSemantics.csmall_nstep_SucD[OF Suc.prems(10)] by clarsimp+
  obtain \<sigma>1' cset1' cset'' where \<sigma>1': "(\<sigma>1', cset1') \<in> JVMSmartCollectionSemantics.csmall P ?\<sigma>"
    "cset\<^sub>s = cset1' \<union> cset''" "(\<sigma>', cset'') \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma>1' n1"
    using JVMSmartCollectionSemantics.csmall_nstep_SucD[OF Suc.prems(11)] by clarsimp+
  have \<sigma>_eq: "\<sigma>1 = \<sigma>1'" using \<sigma>1(1) \<sigma>1'(1) by(simp add: JVMNaiveCollectionSemantics.csmall_def
                                                        JVMSmartCollectionSemantics.csmall_def)
  have sub1': "cset1' \<subseteq> cset" and sub'': "cset'' \<subseteq> cset" using Suc.prems(12) \<sigma>1'(2) by auto
  then have sub1: "cset1 \<subseteq> cset"
    using jvm_naive_to_smart_csmall[where h=h and sh=sh and \<sigma>'=\<sigma>1, OF Suc.prems(1-9) _ _ sub1']
      Suc.prems(11,12) \<sigma>1(1) \<sigma>1'(1) \<sigma>_eq by fastforce
  show ?case
  proof(cases n1)
    case 0 then show ?thesis using \<sigma>1(2,3) sub1 by auto
  next
    case Suc2: (Suc n2)
    then have nend1: "\<sigma>1 \<notin> JVMendset"
      using JVMNaiveCollectionSemantics.csmall_nstep_Suc_nend \<sigma>1(3) by blast
    obtain xp1 h1 frs1 sh1 where \<sigma>1_case [simp]: "\<sigma>1 = (xp1,h1,frs1,sh1)" by(cases \<sigma>1)
    obtain stk1 loc1 C1' M1' pc1 ics1 where f1': "hd frs1 = (stk1,loc1,C1',M1',pc1,ics1)"
      by(cases "hd frs1")
    then obtain frs1' where [simp]: "frs1 = (stk1,loc1,C1',M1',pc1,ics1)#frs1'"
     using JVMendset_def nend1 by(cases frs1, auto)
    have cbig1: "(\<sigma>', cset') \<in> JVMNaiveCollectionSemantics.cbig P \<sigma>1"
      "(\<sigma>', cset'') \<in> JVMSmartCollectionSemantics.cbig P \<sigma>1" using \<sigma>1(3) \<sigma>1'(3) Suc.prems(13) \<sigma>_eq
      using JVMNaiveCollectionSemantics.cbig_def2
            JVMSmartCollectionSemantics.cbig_def2 by blast+
    obtain \<sigma>2' cset2' cset2'' where \<sigma>2': "(\<sigma>2', cset2') \<in> JVMSmartCollectionSemantics.csmall P \<sigma>1"
      "cset'' = cset2' \<union> cset2''" "(\<sigma>', cset2'') \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma>2' n2"
      using JVMSmartCollectionSemantics.csmall_nstep_SucD \<sigma>1'(3) Suc2 \<sigma>_eq by blast
(*****)
    have wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" by fact
    let ?i1 = "instrs_of P C1' M1' ! pc1"
    let ?ics1 = "ics_of (hd (frames_of \<sigma>1))"
    have step: "P \<turnstile> (xp,h,frs,sh) -jvm\<rightarrow> (xp1,h1,frs1,sh1)"
    proof -
      have "exec (P, ?\<sigma>) = \<lfloor>\<sigma>1'\<rfloor>" using JVMsmart_csmallD[OF \<sigma>1'(1)] by simp
      then have "P \<turnstile> ?\<sigma> -jvm\<rightarrow> \<sigma>1'" using jvm_one_step1[OF exec_1.exec_1I] by simp
      then show ?thesis using Suc.prems(12) \<sigma>_eq by fastforce
    qed
    have correct1: "P,\<Phi> \<turnstile> (xp1,h1,frs1,sh1)\<surd>" by(rule BV_correct[OF wtp step Suc.prems(2)])
(**)
    have vics1: "P,h1,sh1 \<turnstile>\<^sub>i (C1', M1', pc1, ics1)"
      using correct1 Suc.prems(7) by(auto simp: conf_f_def2)
    from correct1 obtain b Ts T mxs mxl\<^sub>0 ins xt ST LT where
      meth1: "P \<turnstile> C1' sees M1',b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C1'" and
      pc1: "pc1 < length ins" and
      \<Phi>_pc1: "\<Phi> C1' M1'!pc1 = Some (ST,LT)" by(auto dest: sees_method_fun)
    then have wt1: "P,T,mxs,size ins,xt \<turnstile> ins!pc1,pc1 :: \<Phi> C1' M1'"
      using wt_jvm_prog_impl_wt_instr[OF wtp meth1] by fast
(**)
    have "\<And>a C fs sfs' i'. (h1 a = \<lfloor>(C, fs)\<rfloor> \<longrightarrow> classes_above P C \<subseteq> cset) \<and>
      (sh1 C = \<lfloor>(sfs', i')\<rfloor> \<longrightarrow> classes_above P C \<subseteq> cset) \<and>
      classes_above_frames P frs1 \<subseteq> cset"
    proof -
      fix a C fs sfs' i'
      show "(h1 a = \<lfloor>(C, fs)\<rfloor> \<longrightarrow> classes_above P C \<subseteq> cset) \<and>
      (sh1 C = \<lfloor>(sfs', i')\<rfloor> \<longrightarrow> classes_above P C \<subseteq> cset) \<and>
      (classes_above_frames P frs1 \<subseteq> cset)"
      using Suc.prems(11-12) \<sigma>1' \<sigma>_eq[THEN sym] JVMsmart_csmallD[OF \<sigma>1'(1)]
        backward_coll_promises_kept[where h=h and xp=xp and sh=sh and frs=frs and frs'=frs1
          and xp'=xp1 and h'=h1 and sh'=sh1, OF Suc.prems(1-9)] by auto
    qed
    then have heap1: "\<And>C fs. \<exists>a. h1 a = Some(C,fs) \<Longrightarrow> classes_above P C \<subseteq> cset"
     and sheap1: "\<And>C sfs i. sh1 C = Some(sfs,i) \<Longrightarrow> classes_above P C \<subseteq> cset"
     and frames1: "classes_above_frames P frs1 \<subseteq> cset" by blast+
    have xcpts1: "classes_above_xcpts P \<subseteq> cset" using Suc.prems(6) by auto
\<comment> \<open> @{text init_class} promise \<close>
    have sheap2: "\<And>C. coll_init_class P ?i1 = Some C
      \<Longrightarrow> \<forall>C'. P \<turnstile> C \<preceq>\<^sup>* C' \<longrightarrow> (\<exists>sfs i. sheap \<sigma>1 C' = \<lfloor>(sfs, i)\<rfloor>)
       \<longrightarrow> classes_above P C' \<subseteq> cset" using sheap1 by auto
    have called: "\<And>C. coll_init_class P ?i1 = Some C
      \<Longrightarrow> ics_of (hd (frames_of \<sigma>1)) = Called [] \<Longrightarrow> classes_above P C \<subseteq> cset"
    proof -
      fix C assume cic: "coll_init_class P ?i1 = Some C" and
                   ics: "ics_of (hd (frames_of \<sigma>1)) = Called []"
      then obtain sobj where "sh1 C = Some sobj" using vics1 f1'
        by(cases ?i1, auto simp: seeing_class_def split: if_split_asm)
      then show "classes_above P C \<subseteq> cset" using sheap1 by(cases sobj, simp)
    qed
    have init_class_prom1: "\<And>C. ics1 = Called [] \<or> ics1 = No_ics
      \<Longrightarrow> coll_init_class P ?i1 = Some C \<Longrightarrow> classes_above P C \<subseteq> cset"
    proof -
      fix C assume "ics1 = Called [] \<or> ics1 = No_ics" and cic: "coll_init_class P ?i1 = Some C"
      then have ics: "?ics1 = Called [] \<or> ?ics1 = No_ics" using f1' by simp
      then show "classes_above P C \<subseteq> cset" using cic
      proof(cases "?ics1 = Called []")
        case True then show ?thesis using cic called by simp
      next
        case False
        then have ics': "?ics1 = No_ics" using ics by simp
        then show ?thesis using cic
        proof(cases ?i1)
          case (New C1)
          then have "is_class P C1" using \<Phi>_pc1 wt1 meth1 by auto
          then have "P \<turnstile> C1 \<preceq>\<^sup>* Object" using wtp is_class_is_subcls
            by(auto simp: wf_jvm_prog_phi_def)
          then show ?thesis using New_collects[OF _ cbig1(2) nend1 _ ics' sheap2 sub'']
           f1' ics cic New by auto
        next
          case (Getstatic C1 F1 D1)
          then obtain t where mC1: "P \<turnstile> C1 has F1,Static:t in D1" and eq: "C = D1"
           using cic by (metis coll_init_class.simps(2) option.inject option.simps(3))
          then have "is_class P C" using has_field_is_class'[OF mC1] by simp
          then have "P \<turnstile> C \<preceq>\<^sup>* Object" using wtp is_class_is_subcls
            by(auto simp: wf_jvm_prog_phi_def)
          then show ?thesis using Getstatic_collects[OF _ cbig1(2) nend1 _ ics' _ sheap2 sub'']
            eq f1' Getstatic ics cic by fastforce
        next
          case (Putstatic C1 F1 D1)
          then obtain t where mC1: "P \<turnstile> C1 has F1,Static:t in D1" and eq: "C = D1"
           using cic by (metis coll_init_class.simps(3) option.inject option.simps(3))
          then have "is_class P C" using has_field_is_class'[OF mC1] by simp
          then have "P \<turnstile> C \<preceq>\<^sup>* Object" using wtp is_class_is_subcls
            by(auto simp: wf_jvm_prog_phi_def)
          then show ?thesis using Putstatic_collects[OF _ cbig1(2) nend1 _ ics' _ sheap2 sub'']
            eq f1' Putstatic ics cic by fastforce
        next
          case (Invokestatic C1 M1 n')
          then obtain Ts T m where mC: "P \<turnstile> C1 sees M1, Static :  Ts\<rightarrow>T = m in C"
            using cic by(fastforce simp: seeing_class_def split: if_split_asm)
          then have "is_class P C" by(rule sees_method_is_class')
          then have Obj: "P \<turnstile> C \<preceq>\<^sup>* Object" using wtp is_class_is_subcls
            by(auto simp: wf_jvm_prog_phi_def)
          show ?thesis using Invokestatic_collects[OF _ cbig1(2) sub'' nend1 _ ics' mC sheap2]
            Obj mC f1' Invokestatic ics cic by auto
        qed(simp+)
      qed
    qed
\<comment> \<open> Calling promise \<close>
    have Calling_prom1: "\<And>C' Cs'. ics1 = Calling C' Cs' \<Longrightarrow> classes_above P C' \<subseteq> cset"
    proof -
      fix C' Cs' assume ics: "ics1 = Calling C' Cs'"
      then have "is_class P C'" using vics1 by simp
      then have obj: "P \<turnstile> C' \<preceq>\<^sup>* Object" using wtp is_class_is_subcls
        by(auto simp: wf_jvm_prog_phi_def)
      have sheap3: "\<forall>C1. P \<turnstile> C' \<preceq>\<^sup>* C1 \<longrightarrow> (\<exists>sfs i. sheap \<sigma>1 C1 = \<lfloor>(sfs, i)\<rfloor>)
        \<longrightarrow> classes_above P C1 \<subseteq> cset" using sheap1 by auto
      show "classes_above P C' \<subseteq> cset"
        using Calling_collects[OF obj cbig1(2) nend1 _ sheap3 sub''] ics f1' by simp
    qed
    have in_naive: "(\<sigma>', cset') \<in> JVMNaiveCollectionSemantics.csmall_nstep P (xp1, h1, frs1, sh1) n1"
      and in_smart: "(\<sigma>', cset'') \<in> JVMSmartCollectionSemantics.csmall_nstep P (xp1, h1, frs1, sh1) n1"
     using \<sigma>1(3) \<sigma>1'(3) \<sigma>_eq[THEN sym] by simp+
    have sub2: "cset' \<subseteq> cset"
     by(rule Suc.hyps[OF wtp correct1 f1' heap1 sheap1 xcpts1 frames1 init_class_prom1
                         Calling_prom1 in_naive in_smart sub'' Suc.prems(13)]) simp_all
    then show ?thesis using \<sigma>1(2) \<sigma>1'(2) sub1 sub2 by fastforce
  qed
qed

\<comment> \<open> ...which means over @{term cbig} \<close>
lemma jvm_naive_to_smart_cbig:
assumes
\<comment> \<open> well-formedness \<close>
      wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  and correct: "P,\<Phi> \<turnstile> (xp,h,frs,sh)\<surd>"
\<comment> \<open> defs \<close>
  and f': "hd frs = (stk,loc,C',M',pc,ics)"
\<comment> \<open> backward promises - will be collected/maintained prior \<close>
  and heap: "\<And>C fs. \<exists>a. h a = Some(C,fs) \<Longrightarrow> classes_above P C \<subseteq> cset"
  and sheap: "\<And>C sfs i. sh C = Some(sfs,i) \<Longrightarrow> classes_above P C \<subseteq> cset"
  and xcpts: "classes_above_xcpts P \<subseteq> cset"
  and frames: "classes_above_frames P frs \<subseteq> cset"
\<comment> \<open> forward promises - will be collected after if not already \<close>
  and init_class_prom: "\<And>C. ics = Called [] \<or> ics = No_ics
    \<Longrightarrow> coll_init_class P (instrs_of P C' M' ! pc) = Some C \<Longrightarrow> classes_above P C \<subseteq> cset"
  and Calling_prom: "\<And>C' Cs'. ics = Calling C' Cs' \<Longrightarrow> classes_above P C' \<subseteq> cset"
\<comment> \<open> collections \<close>
  and n: "(\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.cbig P (xp,h,frs,sh)"
  and s: "(\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.cbig P (xp,h,frs,sh)"
  and smart: "cset\<^sub>s \<subseteq> cset"
shows "cset\<^sub>n \<subseteq> cset"
proof -
  let ?\<sigma> = "(xp,h,frs,sh)"
  have nend: "\<sigma>' \<in> JVMendset" using n by(simp add: JVMNaiveCollectionSemantics.cbig_def)
  obtain n where n': "(\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.csmall_nstep P ?\<sigma> n" "\<sigma>' \<in> JVMendset"
    using JVMNaiveCollectionSemantics.cbig_def2 n by auto
  obtain s where s': "(\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.csmall_nstep P ?\<sigma> s" "\<sigma>' \<in> JVMendset"
    using JVMSmartCollectionSemantics.cbig_def2 s by auto
  have "n=s" using jvm_naive_to_smart_csmall_nstep_last_eq[OF n n'(1) s'(1)] by simp
  then have sn: "(\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.csmall_nstep P ?\<sigma> n" using s'(1) by simp
  then show ?thesis
   using jvm_naive_to_smart_csmall_nstep[OF assms(1-9) n'(1) sn assms(12) nend] by fast
qed

\<comment> \<open>...thus naive @{text "\<subseteq>"} smart over the out function, since all conditions will be met - and promises
 kept - by the defined starting point \<close>
lemma jvm_naive_to_smart_collection:
assumes naive: "(\<sigma>',cset\<^sub>n) \<in> jvm_naive_out P t" and smart: "(\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t"
  and P: "P \<in> jvm_progs" and t: "t \<in> jvm_tests"
shows "cset\<^sub>n \<subseteq> cset\<^sub>s"                      
proof -
  let ?P = "jvm_make_test_prog P t"
  let ?\<sigma> = "start_state (t#P)"
  let ?i = "instrs_of ?P Start start_m ! 0" and ?ics = No_ics
  obtain xp h frs sh where
    [simp]: "?\<sigma> = (xp,h,frs,sh)" and
    [simp]: "h = start_heap (t#P)" and
    [simp]: "frs = [([], [], Start, start_m, 0, No_ics)]" and
    [simp]: "sh = start_sheap"
   by(clarsimp simp: start_state_def)

  from P t have nS: "\<not> is_class (t # P) Start"
   by(simp add: is_class_def class_def Start_def Test_def)
  from P have nT: "\<not> is_class P Test" by simp
  from P t obtain m where tPm: "t # P \<turnstile> (fst t) sees main, Static :  []\<rightarrow>Void = m in (fst t)"
   by auto
  have nclinit: "main \<noteq> clinit" by(simp add: main_def clinit_def)
  have Objp: "\<And>b' Ts' T' m' D'.
      t#P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D' \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
  proof -
    fix b' Ts' T' m' D'
    assume mObj: "t#P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'"
    from P have ot_nsub: "\<not> P \<turnstile> Object \<preceq>\<^sup>* Test"
     by(clarsimp simp: wf_jvm_prog_def wf_jvm_prog_phi_def)
    from class_add_sees_method_rev[OF _ ot_nsub] mObj t
    have "P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'" by(cases t, auto)
    with P jvm_progs_def show "b' = Static \<and> Ts' = [] \<and> T' = Void" by blast
  qed
  from P t obtain \<Phi> where wtp0: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> (t#P)" by(auto simp: wf_jvm_prog_def)
  let ?\<Phi>' = "\<lambda>C f. if C = Start \<and> (f = start_m \<or> f = clinit) then start_\<phi>\<^sub>m else \<Phi> C f"
  from wtp0 have wtp: "wf_jvm_prog\<^bsub>?\<Phi>'\<^esub> ?P"
  proof -
    note wtp0 nS tPm nclinit
    moreover obtain "\<And>C. C \<noteq> Start \<Longrightarrow> ?\<Phi>' C = \<Phi> C" "?\<Phi>' Start start_m = start_\<phi>\<^sub>m"
      "?\<Phi>' Start clinit = start_\<phi>\<^sub>m" by simp
    moreover note Objp
    ultimately show ?thesis by(rule start_prog_wf_jvm_prog_phi)
  qed
  have cic: "coll_init_class ?P ?i = Some Test"
  proof -
    from wtp0 obtain wf_md where wf: "wf_prog wf_md (t#P)"
     by(clarsimp dest!: wt_jvm_progD)
    with start_prog_start_m_instrs t have i: "?i = Invokestatic Test main 0" by simp
    from jvm_make_test_prog_sees_Test_main[OF P t] obtain m where
      "?P \<turnstile> Test sees main, Static :  []\<rightarrow>Void = m in Test" by fast
    with t have "seeing_class (jvm_make_test_prog P t) Test main = \<lfloor>Test\<rfloor>"
      by(cases m, fastforce simp: seeing_class_def)
    with i show ?thesis by simp
  qed
\<comment> \<open> well-formedness \<close>
  note wtp
  moreover have correct: "?P,?\<Phi>' \<turnstile> (xp,h,frs,sh)\<surd>"
  proof -
    note wtp0 nS tPm nclinit
    moreover have "?\<Phi>' Start start_m = start_\<phi>\<^sub>m" by simp
    ultimately have "?P,?\<Phi>' \<turnstile> ?\<sigma>\<surd>" by(rule BV_correct_initial)
    then show ?thesis by simp
  qed
\<comment> \<open> defs \<close>
  moreover have "hd frs = ([], [], Start, start_m, 0, No_ics)" by simp
\<comment> \<open> backward promises \<close>
  moreover from jvm_smart_out_classes_above_start_heap[OF smart _ P t]
  have heap: "\<And>C fs. \<exists>a. h a = Some(C,fs) \<Longrightarrow> classes_above ?P C \<subseteq> cset\<^sub>s" by auto
  moreover from jvm_smart_out_classes_above_start_sheap[OF smart]
  have sheap: "\<And>C sfs i. sh C = Some(sfs,i) \<Longrightarrow> classes_above ?P C \<subseteq> cset\<^sub>s" by simp
  moreover from jvm_smart_out_classes_above_xcpts[OF smart P t]
  have xcpts: "classes_above_xcpts ?P \<subseteq> cset\<^sub>s" by simp
  moreover from jvm_smart_out_classes_above_frames[OF smart]
  have frames: "classes_above_frames ?P frs \<subseteq> cset\<^sub>s" by simp
\<comment> \<open> forward promises - will be collected after if not already \<close>
  moreover from jvm_smart_out_classes_above_Test[OF smart P t] cic
  have init_class_prom: "\<And>C. ?ics = Called [] \<or> ?ics = No_ics
    \<Longrightarrow> coll_init_class ?P ?i = Some C \<Longrightarrow> classes_above ?P C \<subseteq> cset\<^sub>s" by simp
  moreover have "\<And>C' Cs'. ?ics = Calling C' Cs' \<Longrightarrow> classes_above ?P C' \<subseteq> cset\<^sub>s" by simp
\<comment> \<open> collections \<close>
  moreover from naive
  have n: "(\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.cbig ?P (xp,h,frs,sh)" by simp
  moreover from smart obtain cset\<^sub>s' where
    s: "(\<sigma>', cset\<^sub>s') \<in> JVMSmartCollectionSemantics.cbig ?P (xp,h,frs,sh)" and
       "cset\<^sub>s' \<subseteq> cset\<^sub>s"
   by clarsimp
  ultimately show "cset\<^sub>n \<subseteq> cset\<^sub>s" by(rule jvm_naive_to_smart_cbig; simp)
qed


(******************************************)
subsubsection \<open> Proving smart @{text "\<subseteq>"} naive \<close>

text "We prove that @{term jvm_naive} collects everything @{term jvm_smart}
 does. Combined with the other direction, this shows that the naive and smart
 algorithms collect the same set of classes."

lemma jvm_smart_to_naive_exec_collect:
  "JVMexec_scollect P \<sigma> \<subseteq> JVMexec_ncollect P \<sigma>"
proof -
  obtain xp h frs sh where \<sigma>: "\<sigma>=(xp,h,frs,sh)" by(cases \<sigma>)
  then show ?thesis
  proof(cases "\<exists>x. xp = Some x \<or> frs = []")
    case False
    then obtain stk loc C M pc ics frs'
     where none: "xp = None" and frs: "frs=(stk,loc,C,M,pc,ics)#frs'"
      by(cases xp, auto, cases frs, auto)
    have instr_case: "ics = Called [] \<or> ics = No_ics \<Longrightarrow> ?thesis"
    proof -
      assume ics: "ics = Called [] \<or> ics = No_ics"
      then show ?thesis using \<sigma> none frs
      proof(cases "curr_instr P (stk,loc,C,M,pc,ics)") qed(auto split: if_split_asm)
    qed
    then show ?thesis using \<sigma> none frs
    proof(cases ics)
      case(Called Cs) then show ?thesis using instr_case \<sigma> none frs by(cases Cs, auto)
    qed(auto)
  qed(auto)
qed

lemma jvm_smart_to_naive_csmall:
assumes "(\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.csmall P \<sigma>"
    and "(\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
shows "cset\<^sub>s \<subseteq> cset\<^sub>n"
using jvm_smart_to_naive_exec_collect assms
   by(auto simp: JVMNaiveCollectionSemantics.csmall_def
                 JVMSmartCollectionSemantics.csmall_def)

lemma jvm_smart_to_naive_csmall_nstep:
"\<lbrakk> (\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.csmall_nstep P \<sigma> n;
   (\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma> n \<rbrakk>
  \<Longrightarrow> cset\<^sub>s \<subseteq> cset\<^sub>n"
proof(induct n arbitrary: \<sigma> \<sigma>' cset\<^sub>n cset\<^sub>s)
  case (Suc n')
  obtain \<sigma>1 cset1 cset' where \<sigma>1: "(\<sigma>1, cset1) \<in> JVMNaiveCollectionSemantics.csmall P \<sigma>"
    "cset\<^sub>n = cset1 \<union> cset'" "(\<sigma>', cset') \<in> JVMNaiveCollectionSemantics.csmall_nstep P \<sigma>1 n'"
    using JVMNaiveCollectionSemantics.csmall_nstep_SucD [OF Suc.prems(1)] by clarsimp+
  obtain \<sigma>1' cset1' cset'' where \<sigma>1': "(\<sigma>1', cset1') \<in> JVMSmartCollectionSemantics.csmall P \<sigma>"
    "cset\<^sub>s = cset1' \<union> cset''" "(\<sigma>', cset'') \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma>1' n'"
    using JVMSmartCollectionSemantics.csmall_nstep_SucD [OF Suc.prems(2)] by clarsimp+
  have \<sigma>_eq: "\<sigma>1 = \<sigma>1'" using \<sigma>1(1) \<sigma>1'(1) by(simp add: JVMNaiveCollectionSemantics.csmall_def
                                                        JVMSmartCollectionSemantics.csmall_def)
  then have sub1: "cset1' \<subseteq> cset1" using \<sigma>1(1) \<sigma>1'(1) jvm_smart_to_naive_csmall by blast
  have sub2: "cset'' \<subseteq> cset'" using \<sigma>1(3) \<sigma>1'(3) \<sigma>_eq Suc.hyps by blast
  then show ?case using \<sigma>1(2) \<sigma>1'(2) sub1 sub2 by blast
qed(simp)

lemma jvm_smart_to_naive_cbig:
assumes n: "(\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.cbig P \<sigma>"
    and s: "(\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.cbig P \<sigma>"
shows "cset\<^sub>s \<subseteq> cset\<^sub>n"
proof -
  obtain n where n': "(\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.csmall_nstep P \<sigma> n" "\<sigma>' \<in> JVMendset"
    using JVMNaiveCollectionSemantics.cbig_def2 n by auto
  obtain s where s': "(\<sigma>', cset\<^sub>s) \<in> JVMSmartCollectionSemantics.csmall_nstep P \<sigma> s" "\<sigma>' \<in> JVMendset"
    using JVMSmartCollectionSemantics.cbig_def2 s by auto
  have "n=s" using jvm_naive_to_smart_csmall_nstep_last_eq[OF n n'(1) s'(1)] by simp
  then show ?thesis using jvm_smart_to_naive_csmall_nstep n'(1) s'(1) by blast
qed

lemma jvm_smart_to_naive_collection:
assumes naive: "(\<sigma>',cset\<^sub>n) \<in> jvm_naive_out P t" and smart: "(\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t"
  and "P \<in> jvm_progs" and "t \<in> jvm_tests"
shows "cset\<^sub>s \<subseteq> cset\<^sub>n"
proof -
  have nend: "start_state (t#P) \<notin> JVMendset" by(simp add: JVMendset_def start_state_def)
  from naive obtain n where
    nstep: "(\<sigma>', cset\<^sub>n) \<in> JVMNaiveCollectionSemantics.csmall_nstep
                                     (jvm_make_test_prog P t) (start_state (t#P)) n"
    by(auto dest!: JVMNaiveCollectionSemantics.cbigD)
  with nend naive obtain n' where n': "n = Suc n'"
    by(cases n; simp add: JVMNaiveCollectionSemantics.cbig_def)
  from start_prog_classes_above_Start
  have "classes_above_frames (jvm_make_test_prog P t) (frames_of (start_state (t#P))) = {Object,Start}"
   by(simp add: start_state_def)
  with nstep n'
  have "jvm_smart_collect_start (jvm_make_test_prog P t) \<subseteq> cset\<^sub>n"
   by(auto simp: start_state_def JVMNaiveCollectionSemantics.csmall_def
           dest!: JVMNaiveCollectionSemantics.csmall_nstep_SucD
           simp del: JVMNaiveCollectionSemantics.csmall_nstep_Rec)
  with jvm_smart_to_naive_cbig[where P="jvm_make_test_prog P t" and \<sigma>="start_state (t#P)" and \<sigma>'=\<sigma>']
       jvm_smart_collect_start_make_test_prog assms show ?thesis by auto
qed

(**************************************************)
subsubsection "Safety of the smart algorithm"

text "Having proved containment in both directions, we get naive = smart:"
lemma jvm_naive_eq_smart_collection:
assumes naive: "(\<sigma>',cset\<^sub>n) \<in> jvm_naive_out P t" and smart: "(\<sigma>',cset\<^sub>s) \<in> jvm_smart_out P t"
  and "P \<in> jvm_progs" and "t \<in> jvm_tests"
shows "cset\<^sub>n = cset\<^sub>s"
using jvm_naive_to_smart_collection[OF assms] jvm_smart_to_naive_collection[OF assms] by simp

text "Thus, since the RTS algorithm based on @{term ncollect} is existence safe,
 the algorithm based on @{term scollect} is as well."
theorem jvm_smart_existence_safe:
assumes P: "P \<in> jvm_progs" and P': "P' \<in> jvm_progs" and t: "t \<in> jvm_tests"
 and out: "o1 \<in> jvm_smart_out P t" and dss: "jvm_deselect P o1 P'"
shows "\<exists>o2 \<in> jvm_smart_out P' t. o1 = o2"
proof -
  obtain \<sigma>' cset\<^sub>s where o1[simp]: "o1=(\<sigma>',cset\<^sub>s)" by(cases o1)
  with jvm_naive_iff_smart out obtain cset\<^sub>n where n: "(\<sigma>',cset\<^sub>n) \<in> jvm_naive_out P t" by blast

  from jvm_naive_eq_smart_collection[OF n _ P t] out have eq: "cset\<^sub>n = cset\<^sub>s" by simp
  with jvm_naive_existence_safe[OF P P' t n] dss have n': "(\<sigma>',cset\<^sub>n) \<in> jvm_naive_out P' t" by simp
  with jvm_naive_iff_smart obtain cset\<^sub>s' where s': "(\<sigma>', cset\<^sub>s') \<in> jvm_smart_out P' t" by blast

  from jvm_naive_eq_smart_collection[OF n' s' P' t] eq have "cset\<^sub>s = cset\<^sub>s'" by simp
  then show ?thesis using s' by simp
qed

text "...thus @{term JVMSmartCollection} is an instance of @{term CollectionBasedRTS}:"
interpretation JVMSmartCollectionRTS :
  CollectionBasedRTS "(=)" jvm_deselect jvm_progs jvm_tests
     JVMendset JVMcombine JVMcollect_id JVMsmall JVMSmartCollect jvm_smart_out
     jvm_make_test_prog jvm_smart_collect_start
 by unfold_locales (rule jvm_smart_existence_safe, auto simp: start_state_def)

end