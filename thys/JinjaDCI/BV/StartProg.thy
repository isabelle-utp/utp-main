(*  Title: JinjaDCI/BV/StartProg.thy
    Author:     Susannah Mansky
    2019-20, UIUC
*)
section "Properties and types of the starting program"

theory StartProg
imports ClassAdd
begin

lemmas wt_defs = correct_state_def conf_f_def wt_instr_def eff_def norm_eff_def app_def xcpt_app_def

declare wt_defs [simp] \<comment> \<open> removed from @{text simp} at the end of file \<close>
declare start_class_def [simp]

subsection "Types"

abbreviation start_\<phi>\<^sub>m :: "ty\<^sub>m" where
"start_\<phi>\<^sub>m \<equiv> [Some([],[]),Some([Void],[])]"

fun \<Phi>_start :: "ty\<^sub>P \<Rightarrow> ty\<^sub>P" where
"\<Phi>_start \<Phi> C M = (if C=Start \<and> (M=start_m \<or> M=clinit) then start_\<phi>\<^sub>m else \<Phi> C M)"

lemma \<Phi>_start: "\<And>C. C \<noteq> Start \<Longrightarrow> \<Phi>_start \<Phi> C = \<Phi> C"
 "\<Phi>_start \<Phi> Start start_m = start_\<phi>\<^sub>m" "\<Phi>_start \<Phi> Start clinit = start_\<phi>\<^sub>m"
 by auto

lemma check_types_\<phi>\<^sub>m: "check_types (start_prog P C M) 1 0 (map OK start_\<phi>\<^sub>m)"
 by (auto simp: check_types_def JVM_states_unfold)

(***************************************************************************************)

subsection "Some simple properties"

lemma preallocated_start_state: "start_state P = \<sigma> \<Longrightarrow> preallocated (fst(snd \<sigma>))"
using preallocated_start[of P] by(auto simp: start_state_def split_beta)

lemma start_prog_Start_super: "start_prog P C M \<turnstile> Start \<prec>\<^sup>1 Object"
 by(auto intro!: subcls1I simp: class_def fun_upd_apply)

lemma start_prog_Start_fields:
 "start_prog P C M \<turnstile> Start has_fields FDTs \<Longrightarrow> map_of FDTs (F, Start) = None"
 by(drule Fields.cases, auto simp: class_def fun_upd_apply Object_fields)

lemma start_prog_Start_soconf:
 "(start_prog P C M),h,Start \<turnstile>\<^sub>s Map.empty \<surd>"
 by(simp add: soconf_def has_field_def start_prog_Start_fields)

lemma start_prog_start_shconf:
 "start_prog P C M,start_heap P \<turnstile>\<^sub>s start_sheap \<surd>"
(*<*) using start_prog_Start_soconf by (simp add: shconf_def fun_upd_apply) (*>*)

(************************************)

subsection "Well-typed and well-formed"

lemma start_wt_method:
assumes "P \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D" and "M \<noteq> clinit" and "\<not> is_class P Start"
shows "wt_method (start_prog P C M) Start Static [] Void 1 0 [Invokestatic C M 0, Return] [] start_\<phi>\<^sub>m"
 (is "wt_method ?P ?C ?b ?Ts ?T\<^sub>r ?mxs ?mxl\<^sub>0 ?is ?xt ?\<tau>s")
proof -
  let ?cdec = "(Object, [], [start_method C M, start_clinit])"
  obtain mxs mxl ins xt where m: "m = (mxs,mxl,ins,xt)" by(cases m)
  have ca_sees: "class_add P (Start, ?cdec) \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D"
    by(rule class_add_sees_method[OF assms(1,3)])
  have "\<And>pc. pc < size ?is \<Longrightarrow> ?P,?T\<^sub>r,?mxs,size ?is,?xt \<turnstile> ?is!pc,pc :: ?\<tau>s"
  proof -
    fix pc assume pc: "pc < size ?is"
    then show "?P,?T\<^sub>r,?mxs,size ?is,?xt \<turnstile> ?is!pc,pc :: ?\<tau>s"
    proof(cases "pc = 0")
      case True with assms m ca_sees show ?thesis
       by(fastforce simp: wt_method_def wt_start_def relevant_entries_def
                          is_relevant_entry_def xcpt_eff_def)
    next
      case False with pc show ?thesis
       by(simp add: wt_method_def wt_start_def relevant_entries_def
                    is_relevant_entry_def xcpt_eff_def)
    qed
  qed
  with assms check_types_\<phi>\<^sub>m show ?thesis by(simp add: wt_method_def wt_start_def)
qed

lemma start_clinit_wt_method:
assumes "P \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D" and "M \<noteq> clinit" and "\<not> is_class P Start"
shows "wt_method (start_prog P C M) Start Static [] Void 1 0 [Push Unit,Return] [] start_\<phi>\<^sub>m"
 (is "wt_method ?P ?C ?b ?Ts ?T\<^sub>r ?mxs ?mxl\<^sub>0 ?is ?xt ?\<tau>s")
proof -
  let ?cdec = "(Object, [], [start_method C M, start_clinit])"
  obtain mxs mxl ins xt where m: "m = (mxs,mxl,ins,xt)" by(cases m)
  have ca_sees: "class_add P (Start, ?cdec) \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D"
    by(rule class_add_sees_method[OF assms(1,3)])
  have "\<And>pc. pc < size ?is \<Longrightarrow> ?P,?T\<^sub>r,?mxs,size ?is,?xt \<turnstile> ?is!pc,pc :: ?\<tau>s"
  proof -
    fix pc assume pc: "pc < size ?is"
    then show "?P,?T\<^sub>r,?mxs,size ?is,?xt \<turnstile> ?is!pc,pc :: ?\<tau>s"
    proof(cases "pc = 0")
      case True with assms m ca_sees show ?thesis
       by(fastforce simp: wt_method_def wt_start_def relevant_entries_def
                          is_relevant_entry_def xcpt_eff_def)
    next
      case False with pc show ?thesis
       by(simp add: wt_method_def wt_start_def relevant_entries_def
                    is_relevant_entry_def xcpt_eff_def)
    qed
  qed
  with assms check_types_\<phi>\<^sub>m show ?thesis by(simp add: wt_method_def wt_start_def)
qed

lemma start_class_wf:
assumes "P \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D"
 and "M \<noteq> clinit" and "\<not> is_class P Start"
 and "\<Phi> Start start_m = start_\<phi>\<^sub>m" and "\<Phi> Start clinit = start_\<phi>\<^sub>m"
 and "is_class P Object"
 and "\<And>b' Ts' T' m' D'. P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
 and "\<And>b' Ts' T' m' D'. P \<turnstile> Object sees clinit, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
shows "wf_cdecl (\<lambda>P C (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M))
       (start_prog P C M) (start_class C M)"
proof -
  from assms start_wt_method start_clinit_wt_method class_add_sees_method_rev_Obj[where P=P and C=Start]
   show ?thesis
    by(auto simp: start_method_def wf_cdecl_def wf_fdecl_def wf_mdecl_def
                  is_class_def class_def fun_upd_apply wf_clinit_def) fast+
qed

lemma start_prog_wf_jvm_prog_phi:
assumes wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
 and nstart: "\<not> is_class P Start"
 and meth: "P \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D" and nclinit: "M \<noteq> clinit"
 and \<Phi>: "\<And>C. C \<noteq> Start \<Longrightarrow> \<Phi>' C = \<Phi> C"
 and \<Phi>': "\<Phi>' Start start_m = start_\<phi>\<^sub>m" "\<Phi>' Start clinit = start_\<phi>\<^sub>m"
 and Obj_start_m: "\<And>b' Ts' T' m' D'. P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
shows "wf_jvm_prog\<^bsub>\<Phi>'\<^esub> (start_prog P C M)"
proof -
  let ?wf_md = "(\<lambda>P C (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi> C M))"
  let ?wf_md' = "(\<lambda>P C (M,b,Ts,T\<^sub>r,(mxs,mxl\<^sub>0,is,xt)). wt_method P C b Ts T\<^sub>r mxs mxl\<^sub>0 is xt (\<Phi>' C M))"
  from wtp have wf: "wf_prog ?wf_md P" by(simp add: wf_jvm_prog_phi_def)
  from wf_subcls_nCls'[OF wf nstart]
  have nsp: "\<And>cd D'. cd \<in> set P \<Longrightarrow> \<not>P \<turnstile> fst cd \<preceq>\<^sup>* Start" by simp
  have wf_md':
    "\<And>C\<^sub>0 S fs ms m. (C\<^sub>0, S, fs, ms) \<in> set P \<Longrightarrow> m \<in> set ms \<Longrightarrow> ?wf_md' (start_prog P C M) C\<^sub>0 m"
  proof -
    fix C\<^sub>0 S fs ms m assume asms: "(C\<^sub>0, S, fs, ms) \<in> set P" "m \<in> set ms"
    with nstart have ns: "C\<^sub>0 \<noteq> Start" by(auto simp: is_class_def class_def dest: weak_map_of_SomeI)
    from wf asms have "?wf_md P C\<^sub>0 m" by(auto simp: wf_prog_def wf_cdecl_def wf_mdecl_def)

    with \<Phi>[OF ns] class_add_wt_method[OF _ wf nstart]
     show "?wf_md' (start_prog P C M) C\<^sub>0 m" by fastforce
  qed
  from wtp have a1: "is_class P Object" by (simp add: wf_jvm_prog_phi_def)
  with wf_sees_clinit[where P=P and C=Object] wtp
   have a2: "\<And>b' Ts' T' m' D'. P \<turnstile> Object sees clinit, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
    by(fastforce simp: wf_jvm_prog_phi_def is_class_def dest: sees_method_fun)
  from wf have dist: "distinct_fst P" by (simp add: wf_prog_def)
  with class_add_distinct_fst[OF _ nstart] have "distinct_fst (start_prog P C M)" by simp
  moreover from wf have "wf_syscls (start_prog P C M)" by(simp add: wf_prog_def wf_syscls_def)
  moreover
  from class_add_wf_cdecl'[where wf_md'="?wf_md'", OF _ _ nsp dist] wf_md' nstart wf
  have "\<And>c. c \<in> set P \<Longrightarrow> wf_cdecl ?wf_md' (start_prog P C M) c" by(fastforce simp: wf_prog_def)
  moreover from start_class_wf[OF meth] nclinit nstart \<Phi>' a1 Obj_start_m a2
  have "wf_cdecl ?wf_md' (start_prog P C M) (start_class C M)" by simp
  ultimately show ?thesis by(simp add: wf_jvm_prog_phi_def wf_prog_def)
qed

lemma start_prog_wf_jvm_prog:
assumes wf: "wf_jvm_prog P"
 and nstart: "\<not> is_class P Start"
 and meth: "P \<turnstile> C sees M, Static :  []\<rightarrow>Void = m in D" and nclinit: "M \<noteq> clinit"
 and Obj_start_m: "\<And>b' Ts' T' m' D'. P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void"
shows "wf_jvm_prog (start_prog P C M)"
proof -
  from wf obtain \<Phi> where wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" by(clarsimp simp: wf_jvm_prog_def)

  let ?\<Phi>' = "\<lambda>C f. if C = Start \<and> (f = start_m \<or> f = clinit) then start_\<phi>\<^sub>m else \<Phi> C f"

  from start_prog_wf_jvm_prog_phi[OF wtp nstart meth nclinit _ _ _ Obj_start_m] have
    "wf_jvm_prog\<^bsub>?\<Phi>'\<^esub> (start_prog P C M)" by simp
  then show ?thesis by(auto simp: wf_jvm_prog_def)
qed

(*****************************************************************************)

subsection "Methods and instructions"

lemma start_prog_Start_sees_methods:
 "P \<turnstile> Object sees_methods Mm
 \<Longrightarrow> start_prog P C M \<turnstile>
  Start sees_methods Mm ++ (map_option (\<lambda>m. (m,Start)) \<circ> map_of [start_method C M, start_clinit])"
 by (auto simp: class_def fun_upd_apply
          dest!: class_add_sees_methods_Obj[where P=P and C=Start] intro: sees_methods_rec)

lemma start_prog_Start_sees_start_method:
 "P \<turnstile> Object sees_methods Mm
  \<Longrightarrow> start_prog P C M \<turnstile>
         Start sees start_m, Static : []\<rightarrow>Void = (1, 0, [Invokestatic C M 0,Return], []) in Start"
 by(auto simp: start_method_def Method_def fun_upd_apply
         dest!: start_prog_Start_sees_methods)

lemma wf_start_prog_Start_sees_start_method:
assumes wf: "wf_prog wf_md P"
shows "start_prog P C M \<turnstile>
         Start sees start_m, Static : []\<rightarrow>Void = (1, 0, [Invokestatic C M 0,Return], []) in Start"
proof -
  from wf have "is_class P Object" by simp
  with sees_methods_Object  obtain Mm where "P \<turnstile> Object sees_methods Mm"
   by(fastforce simp: is_class_def dest: sees_methods_Object)
  then show ?thesis by(rule start_prog_Start_sees_start_method)
qed

lemma start_prog_start_m_instrs:
assumes wf: "wf_prog wf_md P"
shows "(instrs_of (start_prog P C M) Start start_m) = [Invokestatic C M 0, Return]"
proof -
  from wf_start_prog_Start_sees_start_method[OF wf]
  have "start_prog P C M \<turnstile> Start sees start_m, Static :
           []\<rightarrow>Void = (1,0,[Invokestatic C M 0,Return],[]) in Start" by simp
  then show ?thesis by simp
qed

(******************************************************************)

declare wt_defs [simp del]

end