(*  Title:      JinjaDCI/BV/BVSpecTypeSafe.thy

    Author:     Cornelia Pusch, Gerwin Klein, Susannah Mansky
    Copyright   1999 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory BV/BVSpecTypeSafe.thy by Cornelia Pusch and Gerwin Klein
*)


section \<open> BV Type Safety Proof \label{sec:BVSpecTypeSafe} \<close>

theory BVSpecTypeSafe
imports BVConform StartProg
begin

text \<open>
  This theory contains proof that the specification of the bytecode
  verifier only admits type safe programs.  
\<close>

subsection \<open> Preliminaries \<close>

text \<open>
  Simp and intro setup for the type safety proof:
\<close>
lemmas defs1 = correct_state_def conf_f_def wt_instr_def eff_def norm_eff_def app_def xcpt_app_def

lemmas widen_rules [intro] = conf_widen confT_widen confs_widens confTs_widen

  
subsection \<open> Exception Handling \<close>


text \<open>
  For the @{text Invoke} instruction the BV has checked all handlers
  that guard the current @{text pc}.
\<close>
lemma Invoke_handlers:
  "match_ex_table P C pc xt = Some (pc',d') \<Longrightarrow> 
  \<exists>(f,t,D,h,d) \<in> set (relevant_entries P (Invoke n M) pc xt). 
   P \<turnstile> C \<preceq>\<^sup>* D \<and> pc \<in> {f..<t} \<and> pc' = h \<and> d' = d"
  by (induct xt) (auto simp: relevant_entries_def matches_ex_entry_def 
                                 is_relevant_entry_def split: if_split_asm)

text \<open>
  For the @{text Invokestatic} instruction the BV has checked all handlers
  that guard the current @{text pc}.
\<close>
lemma Invokestatic_handlers:
  "match_ex_table P C pc xt = Some (pc',d') \<Longrightarrow> 
  \<exists>(f,t,D,h,d) \<in> set (relevant_entries P (Invokestatic C\<^sub>0 n M) pc xt). 
   P \<turnstile> C \<preceq>\<^sup>* D \<and> pc \<in> {f..<t} \<and> pc' = h \<and> d' = d"
  by (induct xt) (auto simp: relevant_entries_def matches_ex_entry_def 
                                 is_relevant_entry_def split: if_split_asm)

text \<open>
  For the instrs in @{text Called_set} the BV has checked all handlers
  that guard the current @{text pc}.
\<close>
lemma Called_set_handlers:
  "match_ex_table P C pc xt = Some (pc',d') \<Longrightarrow> i \<in> Called_set \<Longrightarrow>
  \<exists>(f,t,D,h,d) \<in> set (relevant_entries P i pc xt). 
   P \<turnstile> C \<preceq>\<^sup>* D \<and> pc \<in> {f..<t} \<and> pc' = h \<and> d' = d"
  by (induct xt) (auto simp: relevant_entries_def matches_ex_entry_def 
                                 is_relevant_entry_def split: if_split_asm)

text \<open>
  We can prove separately that the recursive search for exception
  handlers (@{text find_handler}) in the frame stack results in 
  a conforming state (if there was no matching exception handler 
  in the current frame). We require that the exception is a valid
  heap address, and that the state before the exception occurred
  conforms. 
\<close>
lemma uncaught_xcpt_correct:
  assumes wt: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes h:  "h xcp = Some obj"
  shows "\<And>f. P,\<Phi> \<turnstile> (None, h, f#frs, sh)\<surd>
     \<Longrightarrow> curr_method f \<noteq> clinit \<Longrightarrow> P,\<Phi> \<turnstile> find_handler P xcp h frs sh \<surd>" 
  (is "\<And>f. ?correct (None, h, f#frs, sh) \<Longrightarrow> ?prem f \<Longrightarrow> ?correct (?find frs)")
(*<*)
proof (induct frs) 
  \<comment> \<open>the base
 case is trivial as it should be\<close>
  show "?correct (?find [])" by (simp add: correct_state_def)
next
  \<comment> \<open>we will need both forms @{text wf_jvm_prog} and @{text wf_prog} later\<close>
  from wt obtain mb where wf: "wf_prog mb P" by (simp add: wf_jvm_prog_phi_def)

  \<comment> \<open>the assumptions for the cons case:\<close>
  fix f f' frs' assume cr: "?correct (None, h, f#f'#frs', sh)"
  assume pr: "?prem f"

  \<comment> \<open>the induction hypothesis:\<close>
  assume IH: "\<And>f. ?correct (None, h, f#frs', sh) \<Longrightarrow> ?prem f \<Longrightarrow> ?correct (?find frs')"

  from cr pr conf_clinit_Cons[where frs="f'#frs'" and f=f] obtain
        confc: "conf_clinit P sh (f'#frs')"
    and cr': "?correct (None, h, f'#frs', sh)" by(fastforce simp: correct_state_def)
    
  obtain stk loc C M pc ics where [simp]: "f' = (stk,loc,C,M,pc,ics)" by (cases f')

  from cr' obtain b Ts T mxs mxl\<^sub>0 ins xt where
    meth: "P \<turnstile> C sees M,b:Ts \<rightarrow> T = (mxs,mxl\<^sub>0,ins,xt) in C"
    by (simp add: correct_state_def, blast)

  hence xt[simp]: "ex_table_of P C M = xt" by simp

  have cls: "is_class P C" by(rule sees_method_is_class'[OF meth])
  from cr' obtain sfs where
    sfs: "M = clinit \<Longrightarrow> sh C = Some(sfs,Processing)" by(fastforce simp: defs1 conf_clinit_def)

  show "?correct (?find (f'#frs'))" 
  proof (cases "match_ex_table P (cname_of h xcp) pc xt")
    case None with cr' IH[of f'] show ?thesis
    proof(cases "M=clinit")
      case True then show ?thesis using xt cr' IH[of f'] None h conf_clinit_Called_Throwing
        conf_f_Throwing[where h=h and sh=sh, OF _ cls h sfs]
       by(cases frs', auto simp: correct_state_def image_iff) fastforce
    qed(auto)
  next
    fix pc_d
    assume "match_ex_table P (cname_of h xcp) pc xt = Some pc_d"
    then obtain pc' d' where 
      match: "match_ex_table P (cname_of h xcp) pc xt = Some (pc',d')"
      (is "?match (cname_of h xcp) = _")
      by (cases pc_d) auto 

    from wt meth cr' [simplified]
    have wti: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M" 
      by (fastforce simp: correct_state_def conf_f_def
                   dest: sees_method_fun
                   elim!: wt_jvm_prog_impl_wt_instr)
    
    from cr' obtain ST LT where \<Phi>: "\<Phi> C M ! pc = Some (ST, LT)"
        by(fastforce dest: sees_method_fun simp: correct_state_def)

    from cr' \<Phi> meth have conf': "conf_f P h sh (ST, LT) ins f'"
      by (unfold correct_state_def) (fastforce dest: sees_method_fun)
    hence loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and 
          stk: "P,h \<turnstile> stk [:\<le>] ST" by (unfold conf_f_def) auto
    hence [simp]: "size stk = size ST" by (simp add: list_all2_lengthD)

    from cr meth pr
    obtain D n M' where
      ins: "ins!pc = Invoke n M' \<or> ins!pc = Invokestatic D n M'" (is "_ = ?i \<or> _ = ?i'")
      by(fastforce dest: sees_method_fun simp: correct_state_def)
    
    with match obtain f1 t D where
      rel: "(f1,t,D,pc',d') \<in> set (relevant_entries P (ins!pc) pc xt)" and
      D: "P \<turnstile> cname_of h xcp \<preceq>\<^sup>* D"
      by(fastforce dest: Invoke_handlers Invokestatic_handlers)
      
    from rel have 
      "(pc', Some (Class D # drop (size ST - d') ST, LT)) \<in> set (xcpt_eff (ins!pc) P pc (ST,LT) xt)"
      (is "(_, Some (?ST',_)) \<in> _")
      by (force simp: xcpt_eff_def image_def)      
    with wti \<Phi> obtain 
      pc: "pc' < size ins" and
      "P \<turnstile> Some (?ST', LT) \<le>' \<Phi> C M ! pc'"
      by (clarsimp simp: defs1) blast
    then obtain ST' LT' where
      \<Phi>': "\<Phi> C M ! pc' = Some (ST',LT')" and
      less: "P \<turnstile> (?ST', LT) \<le>\<^sub>i (ST',LT')"
      by (auto simp: sup_state_opt_any_Some)   

    let ?f = "(Addr xcp # drop (length stk - d') stk, loc, C, M, pc',No_ics)"
    have "conf_f P h sh (ST',LT') ins ?f" 
    proof -
      from wf less loc have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" by simp blast
      moreover from D h have "P,h \<turnstile> Addr xcp :\<le> Class D" 
        by (simp add: conf_def obj_ty_def case_prod_unfold)
      with less stk
      have "P,h \<turnstile> Addr xcp # drop (length stk - d') stk  [:\<le>] ST'" 
        by (auto intro!: list_all2_dropI)
      ultimately show ?thesis using pc conf' by(auto simp: conf_f_def)
    qed

    with cr' match \<Phi>' meth pc
    show ?thesis by (unfold correct_state_def)
                    (cases "M=clinit"; fastforce dest: sees_method_fun simp: conf_clinit_def distinct_clinit_def)
  qed
qed
(*>*)

text \<open>
  The requirement of lemma @{text uncaught_xcpt_correct} (that
  the exception is a valid reference on the heap) is always met
  for welltyped instructions and conformant states:
\<close>
lemma exec_instr_xcpt_h:
  "\<lbrakk>  fst (exec_instr (ins!pc) P h stk vars C M pc ics frs sh) = Some xcp;
       P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M;
       P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk>
  \<Longrightarrow> \<exists>obj. h xcp = Some obj" 
  (is "\<lbrakk> ?xcpt; ?wt; ?correct \<rbrakk> \<Longrightarrow> ?thesis")
(*<*)
proof -
  note [simp] = split_beta
  note [split] = if_split_asm option.split_asm 
  
  assume wt: ?wt ?correct
  hence pre: "preallocated h" by (simp add: correct_state_def hconf_def)

  assume xcpt: ?xcpt
  with exec_instr_xcpts have
   opt: "ins!pc = Throw \<or> xcp \<in> {a. \<exists>x \<in> sys_xcpts. a = addr_of_sys_xcpt x}" by simp

  with pre show ?thesis 
  proof (cases "ins!pc")
    case Throw with xcpt wt pre show ?thesis 
      by (clarsimp iff: list_all2_Cons2 simp: defs1) 
         (auto dest: non_npD simp: is_refT_def elim: preallocatedE)
  qed (auto elim: preallocatedE)
qed
(*>*)

lemma exec_step_xcpt_h:
assumes xcpt: "fst (exec_step P h stk vars C M pc ics frs sh) = Some xcp"
 and ins: "instrs_of P C M = ins"
 and wti: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
 and correct: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
shows "\<exists>obj. h xcp = Some obj"
proof -
  from correct have pre: "preallocated h" by(simp add: defs1 hconf_def)
  { fix C' Cs assume ics[simp]: "ics = Calling C' Cs"
    with xcpt have "xcp = addr_of_sys_xcpt NoClassDefFoundError"
      by(cases ics, auto simp: split_beta split: init_state.splits if_split_asm)
    with pre have ?thesis using preallocated_def by force
  }
  moreover
  { fix Cs a assume [simp]: "ics = Throwing Cs a"
    with xcpt have eq: "a = xcp" by(cases Cs; simp)

    from correct have "P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)" by(auto simp: defs1)
    with eq have ?thesis by simp
  }
  moreover
  { fix Cs assume ics: "ics = No_ics \<or> ics = Called Cs"
    with exec_instr_xcpt_h[OF _ wti correct] xcpt ins have ?thesis by(cases Cs, auto)
  }
  ultimately show ?thesis by(cases ics, auto)
qed

lemma conf_sys_xcpt:
  "\<lbrakk>preallocated h; C \<in> sys_xcpts\<rbrakk> \<Longrightarrow> P,h \<turnstile> Addr (addr_of_sys_xcpt C) :\<le> Class C"
  by (auto elim: preallocatedE)

lemma match_ex_table_SomeD:
  "match_ex_table P C pc xt = Some (pc',d') \<Longrightarrow> 
  \<exists>(f,t,D,h,d) \<in> set xt. matches_ex_entry P C pc (f,t,D,h,d) \<and> h = pc' \<and> d=d'"
  by (induct xt) (auto split: if_split_asm)

text \<open>
  Finally we can state that, whenever an exception occurs, the
  next state always conforms:
\<close>
lemma xcpt_correct:
  fixes \<sigma>' :: jvm_state
  assumes wtp:  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes meth: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes xp:   "fst (exec_step P h stk loc C M pc ics frs sh) = Some xcp"
  assumes s':   "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes correct: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from wtp obtain wfmb where wf: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)

  from meth have ins[simp]: "instrs_of P C M = ins" by simp
  have cls: "is_class P C" by(rule sees_method_is_class[OF meth])
  from correct obtain sfs where
    sfs: "M = clinit \<Longrightarrow> sh C = Some(sfs,Processing)"
     by(auto simp: correct_state_def conf_clinit_def conf_f_def2)

  note conf_sys_xcpt [elim!]
  note xp' = meth s' xp

  from correct meth
  obtain ST LT where
    h_ok:  "P \<turnstile> h \<surd>" and
    sh_ok:  "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>_pc: "\<Phi> C M ! pc = Some (ST, LT)" and
    frame:  "conf_f P h sh (ST,LT) ins (stk,loc,C,M,pc,ics)" and
    frames: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)" and
    vics: "P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"
   by(auto simp: defs1 dest: sees_method_fun)

  from frame obtain 
    stk: "P,h \<turnstile> stk [:\<le>] ST" and
    loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc:  "pc < size ins" 
    by (unfold conf_f_def) auto

  from h_ok have preh: "preallocated h" by (simp add: hconf_def)

  note wtp
  moreover
  from exec_step_xcpt_h[OF xp ins wt correct]
  obtain obj where h: "h xcp = Some obj" by clarify
  moreover note correct
  ultimately
  have fh: "curr_method (stk,loc,C,M,pc,ics) \<noteq> clinit
    \<Longrightarrow> P,\<Phi> \<turnstile> find_handler P xcp h frs sh \<surd>" by (rule uncaught_xcpt_correct)
  with xp'
  have "M \<noteq> clinit \<Longrightarrow> \<forall>Cs a. ics \<noteq> Throwing Cs a
   \<Longrightarrow> match_ex_table P (cname_of h xcp) pc xt = None \<Longrightarrow> ?thesis" 
    (is "?nc \<Longrightarrow> ?t \<Longrightarrow> ?m (cname_of h xcp) = _ \<Longrightarrow> _" is "?nc \<Longrightarrow> ?t \<Longrightarrow> ?match = _ \<Longrightarrow> _")
    by(cases ics; simp add: split_beta)
  moreover
  from correct xp' conf_clinit_Called_Throwing conf_f_Throwing[where h=h and sh=sh, OF _ cls h sfs]
  have "M = clinit \<Longrightarrow> \<forall>Cs a. ics \<noteq> Throwing Cs a
   \<Longrightarrow> match_ex_table P (cname_of h xcp) pc xt = None \<Longrightarrow> ?thesis"
    by(cases frs, auto simp: correct_state_def image_iff split_beta) fastforce
  moreover
  { fix pc_d assume "?match = Some pc_d"
    then obtain pc' d' where some_handler: "?match = Some (pc',d')" 
      by (cases pc_d) auto
    
    from stk have [simp]: "size stk = size ST" ..
  
    from wt \<Phi>_pc have
      eff: "\<forall>(pc', s')\<in>set (xcpt_eff (ins!pc) P pc (ST,LT) xt).
             pc' < size ins \<and> P \<turnstile> s' \<le>' \<Phi> C M!pc'"
      by (auto simp: defs1)

    from some_handler obtain f t D where
      xt: "(f,t,D,pc',d') \<in> set xt" and
      "matches_ex_entry P (cname_of h xcp) pc (f,t,D,pc',d')"
      by (auto dest: match_ex_table_SomeD)

    hence match: "P \<turnstile> cname_of h xcp \<preceq>\<^sup>* D"  "pc \<in> {f..<t}"
      by (auto simp: matches_ex_entry_def)
    
    { fix C' Cs assume ics: "ics = Calling C' Cs \<or> ics = Called (C'#Cs)"

      let ?stk' = "Addr xcp # drop (length stk - d') stk"
      let ?f = "(?stk', loc, C, M, pc', No_ics)"
      from some_handler xp' ics
      have \<sigma>': "\<sigma>' = (None, h, ?f#frs, sh)"
        by (cases ics; simp add: split_beta)

      from xp ics have "xcp = addr_of_sys_xcpt NoClassDefFoundError"
        by(cases ics, auto simp: split_beta split: init_state.splits if_split_asm)
      with match preh have conf: "P,h \<turnstile> Addr xcp :\<le> Class D" by fastforce

      from correct ics obtain C1 where "Called_context P C1 (ins!pc)"
        by(fastforce simp: correct_state_def conf_f_def2)
      then have "ins!pc \<in> Called_set" by(rule Called_context_Called_set)
      with xt match have "(f,t,D,pc',d') \<in> set (relevant_entries P (ins!pc) pc xt)"
        by(auto simp: relevant_entries_def is_relevant_entry_def)

      with eff obtain ST' LT' where
        \<Phi>_pc': "\<Phi> C M ! pc' = Some (ST', LT')" and
        pc':   "pc' < size ins" and
        less:  "P \<turnstile> (Class D # drop (size ST - d') ST, LT) \<le>\<^sub>i (ST', LT')"
        by (fastforce simp: xcpt_eff_def sup_state_opt_any_Some)
  
      with conf loc stk conf_f_def2 frame ics have "conf_f P h sh (ST',LT') ins ?f" 
        by (auto simp: defs1 intro: list_all2_dropI)
      with meth h_ok frames \<Phi>_pc' \<sigma>' sh_ok confc ics
      have ?thesis
        by (unfold correct_state_def)
           (auto dest: sees_method_fun conf_clinit_diff' sees_method_is_class; fastforce)
    }
    moreover
    { assume ics: "ics = No_ics \<or> ics = Called []"

      let ?stk' = "Addr xcp # drop (length stk - d') stk"
      let ?f = "(?stk', loc, C, M, pc', No_ics)"
      from some_handler xp' ics
      have \<sigma>': "\<sigma>' = (None, h, ?f#frs, sh)"
        by (cases ics; simp add: split_beta)
  
      from xp ics obtain
        "(f,t,D,pc',d') \<in> set (relevant_entries P (ins!pc) pc xt)" and
        conf: "P,h \<turnstile> Addr xcp :\<le> Class D"
      proof (cases "ins!pc")
        case Return
        with xp ics have False by(cases ics; cases frs, auto simp: split_beta split: if_split_asm)
        then show ?thesis by simp
      next
        case New with xp match 
        have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (simp add: is_relevant_entry_def)
        moreover
        from xp wt correct obtain obj where xcp: "h xcp = Some obj" 
          by (blast dest: exec_step_xcpt_h[OF _ ins])
        ultimately
        show ?thesis using xt match
          by (auto simp: relevant_entries_def conf_def case_prod_unfold intro: that)
      next
        case Getfield with xp ics
        have xcp: "xcp = addr_of_sys_xcpt NullPointer \<or> xcp = addr_of_sys_xcpt NoSuchFieldError
          \<or> xcp = addr_of_sys_xcpt IncompatibleClassChangeError"
          by (cases ics; simp add: split_beta split: if_split_asm staticb.splits)
        with Getfield match preh have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (fastforce simp: is_relevant_entry_def)
        with match preh xt xcp
        show ?thesis by(fastforce simp: relevant_entries_def intro: that)
      next
        case Getstatic with xp match 
        have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (simp add: is_relevant_entry_def)
        moreover
        from xp wt correct obtain obj where xcp: "h xcp = Some obj" 
          by (blast dest: exec_step_xcpt_h[OF _ ins])
        ultimately
        show ?thesis using xt match
          by (auto simp: relevant_entries_def conf_def case_prod_unfold intro: that)
      next
        case Putfield with xp ics
        have xcp: "xcp = addr_of_sys_xcpt NullPointer \<or> xcp = addr_of_sys_xcpt NoSuchFieldError
          \<or> xcp = addr_of_sys_xcpt IncompatibleClassChangeError"
          by (cases ics; simp add: split_beta split: if_split_asm staticb.splits)
        with Putfield match preh have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (fastforce simp: is_relevant_entry_def)
        with match preh xt xcp
        show ?thesis by (fastforce simp: relevant_entries_def intro: that)
      next
        case Putstatic with xp match 
        have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (simp add: is_relevant_entry_def)
        moreover
        from xp wt correct obtain obj where xcp: "h xcp = Some obj" 
          by (blast dest: exec_step_xcpt_h[OF _ ins])
        ultimately
        show ?thesis using xt match
          by (auto simp: relevant_entries_def conf_def case_prod_unfold intro: that)
      next
        case Checkcast with xp ics
        have [simp]: "xcp = addr_of_sys_xcpt ClassCast" 
          by (cases ics; simp add: split_beta split: if_split_asm)
        with Checkcast match preh have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (simp add: is_relevant_entry_def)
        with match preh xt
        show ?thesis by (fastforce simp: relevant_entries_def intro: that)
      next
        case Invoke with xp match 
        have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (simp add: is_relevant_entry_def)
        moreover
        from xp wt correct obtain obj where xcp: "h xcp = Some obj" 
          by (blast dest: exec_step_xcpt_h[OF _ ins])
        ultimately
        show ?thesis using xt match
          by (auto simp: relevant_entries_def conf_def case_prod_unfold intro: that)
      next
        case Invokestatic with xp match 
        have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (simp add: is_relevant_entry_def)
        moreover
        from xp wt correct obtain obj where xcp: "h xcp = Some obj" 
          by (blast dest: exec_step_xcpt_h[OF _ ins])
        ultimately
        show ?thesis using xt match
          by (auto simp: relevant_entries_def conf_def case_prod_unfold intro: that)
      next
        case Throw with xp match preh 
        have "is_relevant_entry P (ins!pc) pc (f,t,D,pc',d')"
          by (simp add: is_relevant_entry_def)
        moreover
        from xp wt correct obtain obj where xcp: "h xcp = Some obj" 
          by (blast dest: exec_step_xcpt_h[OF _ ins])
        ultimately
        show ?thesis using xt match
          by (auto simp: relevant_entries_def conf_def case_prod_unfold intro: that)
      qed(cases ics, (auto)[5])+
  
      with eff obtain ST' LT' where
        \<Phi>_pc': "\<Phi> C M ! pc' = Some (ST', LT')" and
        pc':   "pc' < size ins" and
        less:  "P \<turnstile> (Class D # drop (size ST - d') ST, LT) \<le>\<^sub>i (ST', LT')"
        by (fastforce simp: xcpt_eff_def sup_state_opt_any_Some)
  
      with conf loc stk conf_f_def2 frame ics have "conf_f P h sh (ST',LT') ins ?f" 
        by (auto simp: defs1 intro: list_all2_dropI)
      with meth h_ok frames \<Phi>_pc' \<sigma>' sh_ok confc ics
      have ?thesis
        by (unfold correct_state_def) (auto dest: sees_method_fun conf_clinit_diff'; fastforce)
    }
    ultimately
    have "\<forall>Cs a. ics \<noteq> Throwing Cs a \<Longrightarrow> ?thesis" by(cases ics; metis list.exhaust)
  }
  moreover
  { fix Cs a assume "ics = Throwing Cs a"
    with xp' have ics: "ics = Throwing [] xcp" by(cases Cs; clarsimp)

    let ?frs = "(stk,loc,C,M,pc,No_ics)#frs"

    have eT: "exec_step P h stk loc C M pc (Throwing [] xcp) frs sh = (Some xcp, h, ?frs, sh)"
      by auto
    with xp' ics have \<sigma>'_fh: "\<sigma>' = find_handler P xcp h ?frs sh" by simp

    from meth have [simp]: "xt = ex_table_of P C M" by simp

    let ?match = "match_ex_table P (cname_of h xcp) pc xt"
  
    { assume clinit: "M = clinit" and None: "?match = None"
      note asms = clinit None

      have "P,\<Phi> |- find_handler P xcp h ?frs sh [ok]"
      proof(cases frs)
       case Nil
        with h_ok sh_ok asms show "P,\<Phi> |- find_handler P xcp h ?frs sh [ok]"
          by(simp add: correct_state_def)
      next
        case [simp]: (Cons f' frs')
        obtain stk' loc' C' M' pc' ics' where
          [simp]: "f' = (stk',loc',C',M',pc',ics')" by(cases f')

        have cls: "is_class P C" by(rule sees_method_is_class[OF meth])
        have shC: "sh C = Some(sfs,Processing)" by(rule sfs[OF clinit])

        from correct obtain b Ts T mxs' mxl\<^sub>0' ins' xt' ST' LT' where
          meth': "P \<turnstile> C' sees M', b :  Ts\<rightarrow>T = (mxs', mxl\<^sub>0', ins', xt') in C'" and
          \<Phi>_pc': "\<Phi> C' M' ! pc' = \<lfloor>(ST', LT')\<rfloor>" and
          frame': "conf_f P h sh (ST',LT') ins' (stk', loc', C', M', pc', ics')" and
          frames': "conf_fs P h sh \<Phi> C' M' (length Ts) T frs'" and
          confc': "conf_clinit P sh ((stk',loc',C',M',pc',ics')#frs')"
         by(auto dest: conf_clinit_Cons simp: correct_state_def)
  
        from meth' have
          ins'[simp]: "instrs_of P C' M' = ins'"
          and [simp]: "xt' = ex_table_of P C' M'" by simp+

        let ?f' = "case ics' of Called Cs' \<Rightarrow> (stk',loc',C',M',pc',Throwing (C#Cs') xcp)
                              | _ \<Rightarrow> (stk',loc',C',M',pc',ics')"

        from asms confc have confc_T: "conf_clinit P sh (?f'#frs')"
          by(cases ics', auto simp: conf_clinit_def distinct_clinit_def)

        from asms conf_f_Throwing[where h=h and sh=sh, OF _ cls h shC] frame' have
         frame_T: "conf_f P h sh (ST', LT') ins' ?f'" by(cases ics'; simp)
        with h_ok sh_ok meth' \<Phi>_pc' confc_T frames'
         have "P,\<Phi> |- (None, h, ?f'#frs', sh) [ok]"
          by(cases ics') (fastforce simp: correct_state_def)+

        with asms show ?thesis by(cases ics'; simp)
      qed
    }
    moreover
    { assume asms: "M \<noteq> clinit" "?match = None"

      from asms uncaught_xcpt_correct[OF wtp h correct]
       have "P,\<Phi> |- find_handler P xcp h frs sh [ok]" by simp
      with asms have "P,\<Phi> |- find_handler P xcp h ?frs sh [ok]" by auto
    }
    moreover
    { fix pc_d assume some_handler: "?match = \<lfloor>pc_d\<rfloor>"
        (is "?match = \<lfloor>pc_d\<rfloor>")
      then obtain pc1 d1 where sh': "?match = Some(pc1,d1)" by(cases pc_d, simp)

      let ?stk' = "Addr xcp # drop (length stk - d1) stk"
      let ?f = "(?stk', loc, C, M, pc1, No_ics)"

      from stk have [simp]: "size stk = size ST" ..

      from wt \<Phi>_pc have
        eff: "\<forall>(pc1, s')\<in>set (xcpt_eff (ins!pc) P pc (ST,LT) xt).
               pc1 < size ins \<and> P \<turnstile> s' \<le>' \<Phi> C M!pc1"
        by (auto simp: defs1)

      from match_ex_table_SomeD[OF sh'] obtain f t D where
        xt: "(f,t,D,pc1,d1) \<in> set xt" and
        "matches_ex_entry P (cname_of h xcp) pc (f,t,D,pc1,d1)" by auto
  
      hence match: "P \<turnstile> cname_of h xcp \<preceq>\<^sup>* D"  "pc \<in> {f..<t}"
        by (auto simp: matches_ex_entry_def)

      from ics vics obtain C1 where "Called_context P C1 (ins ! pc)" by auto
      then have "ins!pc \<in> Called_set" by(rule Called_context_Called_set)
      with match xt xp ics obtain
        res: "(f,t,D,pc1,d1) \<in> set (relevant_entries P (ins!pc) pc xt)"
       by(auto simp: relevant_entries_def is_relevant_entry_def)

      with h match xt xp ics have conf: "P,h \<turnstile> Addr xcp :\<le> Class D"
        by (auto simp: relevant_entries_def conf_def case_prod_unfold)

      with eff res obtain ST1 LT1 where
        \<Phi>_pc1: "\<Phi> C M ! pc1 = Some (ST1, LT1)" and
        pc1:   "pc1 < size ins" and
        less1:  "P \<turnstile> (Class D # drop (size ST - d1) ST, LT) \<le>\<^sub>i (ST1, LT1)"
        by (fastforce simp: xcpt_eff_def sup_state_opt_any_Some)
 
      with conf loc stk conf_f_def2 frame ics have frame1: "conf_f P h sh (ST1,LT1) ins ?f" 
        by (auto simp: defs1 intro: list_all2_dropI)

      from \<Phi>_pc1 h_ok sh_ok meth frame1 frames conf_clinit_diff'[OF confc] have
        "P,\<Phi> |- (None, h, ?f # frs, sh) [ok]" by(fastforce simp: correct_state_def)
      with sh' have "P,\<Phi> |- find_handler P xcp h ?frs sh [ok]" by auto
    }
    ultimately
    have cr': "P,\<Phi> |- find_handler P xcp h ?frs sh [ok]" by(cases "?match") blast+

    with \<sigma>'_fh have ?thesis by simp
  }
  ultimately
  show ?thesis by (cases "?match") blast+
qed
(*>*)

(**********Non-exception Single-step correctness*************************)
declare defs1 [simp]

subsection \<open> Initialization procedure steps \<close>

text \<open>
  In this section we prove that, for states that result in a step of the
  initialization procedure rather than an instruction execution, the state
  after execution of the step still conforms.
\<close>

lemma Calling_correct:
  fixes \<sigma>' :: jvm_state
  assumes wtprog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc ics frs sh) = None"
  assumes ics: "ics = Calling C' Cs"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof -
  from wtprog obtain wfmb where wf: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)

  from mC cf obtain ST LT where
    h_ok: "P \<turnstile> h \<surd>" and
    sh_ok: "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:  "conf_f P h sh (ST, LT) ins (stk,loc,C,M,pc,ics)" and
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)" and
    vics: "P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"
    by (fastforce dest: sees_method_fun)

  with ics have confc\<^sub>0: "conf_clinit P sh ((stk,loc,C,M,pc,Calling C' Cs)#frs)" by simp

  from vics ics have cls': "is_class P C'" by auto

  { assume None: "sh C' = None"

    let ?sh = "sh(C' \<mapsto> (sblank P C', Prepared))"

    obtain FDTs where
     flds: "P \<turnstile> C' has_fields FDTs" using wf_Fields_Ex[OF wf cls'] by clarsimp
  
    from shconf_upd_obj[where C=C', OF sh_ok soconf_sblank[OF flds]]
    have sh_ok': "P,h \<turnstile>\<^sub>s ?sh \<surd>" by simp

    from None have "\<forall>sfs. sh C' \<noteq> Some(sfs,Processing)" by simp
    with conf_clinit_nProc_dist[OF confc] have
     dist': "distinct (C' # clinit_classes ((stk, loc, C, M, pc, ics) # frs))" by simp
    then have dist'': "distinct (C' # clinit_classes frs)" by simp

    have confc': "conf_clinit P ?sh ((stk, loc, C, M, pc, ics) # frs)"
     by(rule conf_clinit_shupd[OF confc dist'])
    have fs': "conf_fs P h ?sh \<Phi> C M (size Ts) T frs" by(rule conf_fs_shupd[OF fs dist''])
    from vics ics have vics': "P,h,?sh \<turnstile>\<^sub>i (C, M, pc, ics)" by auto
  
    from s' ics None have "\<sigma>' = (None, h, (stk, loc, C, M, pc, ics)#frs, ?sh)" by auto
  
    with mC h_ok sh_ok' \<Phi> stk loc pc fs' confc vics' confc' frame None
    have ?thesis by fastforce
  }
  moreover
  { fix a assume "sh C' = Some a"
    then obtain sfs i where shC'[simp]: "sh C' = Some(sfs,i)" by(cases a, simp)

    from confc ics have last: "\<exists>sobj. sh (last(C'#Cs)) = Some sobj"
      by(fastforce simp: conf_clinit_def)

    let "?f" = "\<lambda>ics'. (stk, loc, C, M, pc, ics'::init_call_status)"

    { assume i: "i = Done \<or> i = Processing"
      let ?ics = "Called Cs"

      from last vics ics have vics': "P,h,sh \<turnstile>\<^sub>i (C, M, pc, ?ics)" by auto
      from confc ics have confc': "conf_clinit P sh (?f ?ics#frs)"
        by(cases "M=clinit"; clarsimp simp: conf_clinit_def distinct_clinit_def)

      from i s' ics have "\<sigma>' = (None, h, ?f ?ics#frs, sh)" by auto

      with mC h_ok sh_ok \<Phi> stk loc pc fs confc' vics' frame ics
      have ?thesis by fastforce
    }
    moreover
    { assume i[simp]: "i = Error"
      let ?a = "addr_of_sys_xcpt NoClassDefFoundError"
      let ?ics = "Throwing Cs ?a"

      from h_ok have preh: "preallocated h" by (simp add: hconf_def)
      then obtain obj where ha: "h ?a = Some obj" by(clarsimp simp: preallocated_def sys_xcpts_def)
      with vics ics have vics': "P,h,sh \<turnstile>\<^sub>i (C, M, pc, ?ics)" by auto

      from confc ics have confc'': "conf_clinit P sh (?f ?ics#frs)"
        by(cases "M=clinit"; clarsimp simp: conf_clinit_def distinct_clinit_def)

      from s' ics have \<sigma>': "\<sigma>' = (None, h, ?f ?ics#frs, sh)" by auto

      from mC h_ok sh_ok \<Phi> stk loc pc fs confc'' vics \<sigma>' ics ha
      have ?thesis by fastforce
    }
    moreover
    { assume i[simp]: "i = Prepared"
      let ?sh = "sh(C' \<mapsto> (sfs,Processing))"
      let ?D = "fst(the(class P C'))"
      let ?ics = "if C' = Object then Called (C'#Cs) else Calling ?D (C'#Cs)"

      from shconf_upd_obj[where C=C', OF sh_ok shconfD[OF sh_ok shC']]
      have sh_ok': "P,h \<turnstile>\<^sub>s ?sh \<surd>" by simp

      from cls' have "C' \<noteq> Object \<Longrightarrow> P \<turnstile> C' \<preceq>\<^sup>* ?D" by(auto simp: is_class_def intro!: subcls1I)
      with is_class_supclass[OF wf _ cls'] have D: "C' \<noteq>  Object \<Longrightarrow> is_class P ?D" by simp

      from i have "\<forall>sfs. sh C' \<noteq> Some(sfs,Processing)" by simp
      with conf_clinit_nProc_dist[OF confc\<^sub>0] have
       dist': "distinct (C' # clinit_classes ((stk, loc, C, M, pc, Calling C' Cs) # frs))" by fast
      then have dist'': "distinct (C' # clinit_classes frs)" by simp

      from conf_clinit_shupd_Calling[OF confc\<^sub>0 dist' cls']
           conf_clinit_shupd_Called[OF confc\<^sub>0 dist' cls']
      have confc': "conf_clinit P ?sh (?f ?ics#frs)" by clarsimp
      with last ics have "\<exists>sobj. ?sh (last(C'#Cs)) = Some sobj"
        by(auto simp: conf_clinit_def fun_upd_apply)
      with D vics ics have vics': "P,h,?sh \<turnstile>\<^sub>i (C, M, pc, ?ics)" by auto

      have fs': "conf_fs P h ?sh \<Phi> C M (size Ts) T frs" by(rule conf_fs_shupd[OF fs dist''])

      from frame vics' have frame': "conf_f P h ?sh (ST, LT) ins (?f ?ics)" by simp

      from i s' ics have "\<sigma>' = (None, h, ?f ?ics#frs, ?sh)" by(auto simp: if_split_asm)

      with mC h_ok sh_ok' \<Phi> stk loc pc fs' confc' frame' ics
      have ?thesis by fastforce
    }
    ultimately have ?thesis by(cases i, auto)
  }
  ultimately show ?thesis by(cases "sh C'", auto)
qed

lemma Throwing_correct:
  fixes \<sigma>' :: jvm_state
  assumes wtprog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc ics frs sh) = None"
  assumes ics: "ics = Throwing (C'#Cs) a"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof -
  from wtprog obtain wfmb where wf: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)

  from mC cf obtain ST LT where
    h_ok: "P \<turnstile> h \<surd>" and
    sh_ok: "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:  "conf_f P h sh (ST, LT) ins (stk,loc,C,M,pc,ics)" and
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)" and
    vics: "P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"
    by (fastforce dest: sees_method_fun)

  with ics have confc\<^sub>0: "conf_clinit P sh ((stk,loc,C,M,pc,Throwing (C'#Cs) a)#frs)" by simp

  from frame ics mC have
   cc: "\<exists>C1. Called_context P C1 (ins ! pc)" by(clarsimp simp: conf_f_def2)

  from frame ics obtain obj where ha: "h a = Some obj" by(auto simp: conf_f_def2)

  from confc ics obtain sfs i where shC': "sh C' = Some(sfs,i)" by(clarsimp simp: conf_clinit_def)
  then have sfs: "P,h,C' \<turnstile>\<^sub>s sfs \<surd>" by(rule shconfD[OF sh_ok])

  from s' ics
  have \<sigma>': "\<sigma>' = (None, h, (stk,loc,C,M,pc,Throwing Cs a)#frs, sh(C' \<mapsto> (fst(the(sh C')), Error)))"
    (is "\<sigma>' = (None, h, ?f'#frs, ?sh')")
   by simp

  from confc ics have dist: "distinct (C' # clinit_classes (?f' # frs))"
    by (simp add: conf_clinit_def distinct_clinit_def)
  then have dist': "distinct (C' # clinit_classes frs)" by simp

  from conf_clinit_Throwing confc ics have confc': "conf_clinit P sh (?f' # frs)" by simp

  from shconf_upd_obj[OF sh_ok sfs] shC' have "P,h \<turnstile>\<^sub>s ?sh' \<surd>" by simp
  moreover
  have "conf_fs P h ?sh' \<Phi> C M (length Ts) T frs" by(rule conf_fs_shupd[OF fs dist'])
  moreover
  have "conf_clinit P ?sh' (?f' # frs)" by(rule conf_clinit_shupd[OF confc' dist])
  moreover note \<sigma>' h_ok mC \<Phi> pc stk loc ha cc
  ultimately show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastforce
qed

lemma Called_correct:
  fixes \<sigma>' :: jvm_state
  assumes wtprog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc ics frs sh) = None"
  assumes ics[simp]: "ics = Called (C'#Cs)"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
proof -
  from wtprog obtain wfmb where wf: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)

  from mC cf obtain ST LT where
    h_ok: "P \<turnstile> h \<surd>" and
    sh_ok: "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    frame:  "conf_f P h sh (ST, LT) ins (stk,loc,C,M,pc,ics)" and
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)" and
    vics: "P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"
    by (fastforce dest: sees_method_fun)

  then have confc\<^sub>0: "conf_clinit P sh ((stk,loc,C,M,pc,Called (C'#Cs))#frs)" by simp

  from frame mC obtain C1 sobj where
    ss: "Called_context P C1 (ins ! pc)" and
    shC1: "sh C1 = Some sobj"  by(clarsimp simp: conf_f_def2)

  from confc wf_sees_clinit[OF wf] obtain mxs' mxl' ins' xt' where
   clinit: "P \<turnstile> C' sees clinit,Static: [] \<rightarrow> Void=(mxs',mxl',ins',xt') in C'"
    by(fastforce simp: conf_clinit_def is_class_def)

  let ?loc' = "replicate mxl' undefined"

  from s' clinit
  have \<sigma>': "\<sigma>' = (None, h, ([],?loc',C',clinit,0,No_ics)#(stk,loc,C,M,pc,Called Cs)#frs, sh)"
    (is "\<sigma>' = (None, h, ?if#?f'#frs, sh)")
   by simp

  with wtprog clinit
  obtain start: "wt_start P C' Static [] mxl' (\<Phi> C' clinit)" and ins': "ins' \<noteq> []"
    by (auto dest: wt_jvm_prog_impl_wt_start)
  then obtain LT\<^sub>0 where LT\<^sub>0: "\<Phi> C' clinit ! 0 = Some ([], LT\<^sub>0)"
    by (clarsimp simp: wt_start_def defs1 sup_state_opt_any_Some split: staticb.splits)
  moreover
  have "conf_f P h sh ([], LT\<^sub>0) ins' ?if"
  proof -
    let ?LT = "replicate mxl' Err"
    have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] ?LT" by simp
    also from start LT\<^sub>0 have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT\<^sub>0" by (simp add: wt_start_def)
    finally have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] LT\<^sub>0" .
    thus ?thesis using ins' by simp
  qed
  moreover
  from conf_clinit_Called confc clinit have "conf_clinit P sh (?if # ?f' # frs)" by simp
  moreover note \<sigma>' h_ok sh_ok mC \<Phi> pc stk loc clinit ss shC1 fs
  ultimately show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastforce
qed

subsection \<open> Single Instructions \<close>

text \<open>
  In this section we prove for each single (welltyped) instruction
  that the state after execution of the instruction still conforms.
  Since we have already handled exceptions above, we can now assume that
  no exception occurs in this step. For instructions that may call
  the initialization procedure, we cover the calling and non-calling
  cases separately.
\<close>

lemma Invoke_correct: 
  fixes \<sigma>' :: jvm_state
  assumes wtprog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes meth_C: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes ins:    "ins ! pc = Invoke M' n"
  assumes wti:    "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes \<sigma>': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes approx: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes no_xcp: "fst (exec_step P h stk loc C M pc ics frs sh) = None"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>" 
(*<*)
proof -
  from meth_C approx ins have [simp]: "ics = No_ics" by(cases ics, auto)

  note split_paired_Ex [simp del]
  
  from wtprog obtain wfmb where wfprog: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)
      
  from ins meth_C approx obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    frame:   "conf_f P h sh (ST,LT) ins (stk,loc,C,M,pc,ics)" and
    frames:  "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc:   "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)"
    by (fastforce dest: sees_method_fun)

  from ins wti \<Phi>_pc
  have n: "n < size ST" by simp
  
  { assume "stk!n = Null"
    with ins no_xcp meth_C have False by (simp add: split_beta)
    hence ?thesis ..
  } 
  moreover
  { assume "ST!n = NT"
    moreover 
    from frame have "P,h \<turnstile> stk [:\<le>] ST" by simp
    with n have "P,h \<turnstile> stk!n :\<le> ST!n" by (simp add: list_all2_conv_all_nth)
    ultimately 
    have "stk!n = Null" by simp
    with ins no_xcp meth_C have False by (simp add: split_beta)
    hence ?thesis ..
  } 
  moreover {
    assume NT: "ST!n \<noteq> NT" and Null: "stk!n \<noteq> Null"
    
    from NT ins wti \<Phi>_pc obtain D D' b Ts T m ST' LT' where
      D:   "ST!n = Class D" and
      pc': "pc+1 < size ins" and
      m_D: "P \<turnstile> D sees M',b: Ts\<rightarrow>T = m in D'" and
      Ts:  "P \<turnstile> rev (take n ST) [\<le>] Ts" and
      \<Phi>':  "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
      LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
      ST': "P \<turnstile> (T # drop (n+1) ST) [\<le>] ST'" and
      b[simp]: "b = NonStatic"
      by (clarsimp simp: sup_state_opt_any_Some)

    from frame obtain 
    stk: "P,h \<turnstile> stk [:\<le>] ST" and
    loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" by simp
    
    from n stk D have "P,h \<turnstile> stk!n :\<le> Class D"
      by (auto simp: list_all2_conv_all_nth)
    with Null obtain a C' fs where
      Addr:   "stk!n = Addr a" and
      obj:    "h a = Some (C',fs)" and
      C'subD: "P \<turnstile> C' \<preceq>\<^sup>* D"
      by (fastforce dest!: conf_ClassD) 

    with wfprog m_D no_xcp
    obtain Ts' T' D'' mxs' mxl' ins' xt' where
      m_C': "P \<turnstile> C' sees M',NonStatic: Ts'\<rightarrow>T' = (mxs',mxl',ins',xt') in D''" and
      T':   "P \<turnstile> T' \<le> T" and
      Ts':  "P \<turnstile> Ts [\<le>] Ts'"
      by (auto dest: sees_method_mono)
    with wf_NonStatic_nclinit wtprog have nclinit: "M' \<noteq> clinit" by(simp add: wf_jvm_prog_phi_def)

    have D''subD': "P \<turnstile> D'' \<preceq>\<^sup>* D'" by(rule sees_method_decl_mono[OF C'subD m_D m_C'])

    let ?loc' = "Addr a # rev (take n stk) @ replicate mxl' undefined"
    let ?f' = "([], ?loc', D'', M', 0, No_ics)"
    let ?f  = "(stk, loc, C, M, pc, ics)"

    from Addr obj m_C' ins \<sigma>' meth_C no_xcp
    have s': "\<sigma>' = (None, h, ?f' # ?f # frs, sh)" by simp

    from Ts n have [simp]: "size Ts = n" 
      by (auto dest: list_all2_lengthD simp: min_def)
    with Ts' have [simp]: "size Ts' = n" 
      by (auto dest: list_all2_lengthD)

    from m_C' wfprog
    obtain mD'': "P \<turnstile> D'' sees M',NonStatic:Ts'\<rightarrow>T'=(mxs',mxl',ins',xt') in D''"
      by (fast dest: sees_method_idemp)
    moreover 
    with wtprog 
    obtain start: "wt_start P D'' NonStatic Ts' mxl' (\<Phi> D'' M')" and ins': "ins' \<noteq> []"
      by (auto dest: wt_jvm_prog_impl_wt_start)    
    then obtain LT\<^sub>0 where LT\<^sub>0: "\<Phi> D'' M' ! 0 = Some ([], LT\<^sub>0)"
      by (clarsimp simp: wt_start_def defs1 sup_state_opt_any_Some split: staticb.splits)
    moreover
    have "conf_f P h sh ([], LT\<^sub>0) ins' ?f'"
    proof -
      let ?LT = "OK (Class D'') # (map OK Ts') @ (replicate mxl' Err)"

      from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
      hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" by simp
      also note Ts also note Ts' finally
      have "P,h \<turnstile> rev (take n stk) [:\<le>\<^sub>\<top>] map OK Ts'" by simp 
      also
      have "P,h \<turnstile> replicate mxl' undefined [:\<le>\<^sub>\<top>] replicate mxl' Err" 
        by simp
      also from m_C' have "P \<turnstile> C' \<preceq>\<^sup>* D''" by (rule sees_method_decl_above)
      with obj have "P,h \<turnstile> Addr a :\<le> Class D''" by (simp add: conf_def)
      ultimately
      have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] ?LT" by simp
      also from start LT\<^sub>0 have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT\<^sub>0" by (simp add: wt_start_def)
      finally have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] LT\<^sub>0" .
      thus ?thesis using ins' nclinit by simp
    qed
    moreover
    have "conf_clinit P sh (?f'#?f#frs)" using conf_clinit_Invoke[OF confc nclinit] by simp
    ultimately
    have ?thesis using s' \<Phi>_pc approx meth_C m_D T' ins D nclinit D''subD'
     by(fastforce dest: sees_method_fun [of _ C])
  }
  ultimately show ?thesis by blast
qed
(*>*)

lemma Invokestatic_nInit_correct: 
  fixes \<sigma>' :: jvm_state
  assumes wtprog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes meth_C: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes ins:    "ins ! pc = Invokestatic D M' n" and nclinit: "M' \<noteq> clinit"
  assumes wti:    "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes \<sigma>': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes approx: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes no_xcp: "fst (exec_step P h stk loc C M pc ics frs sh) = None"
  assumes cs: "ics = Called [] \<or> (ics = No_ics \<and> (\<exists>sfs. sh (fst(method P D M')) = Some(sfs, Done)))"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>" 
(*<*)
proof -
  note split_paired_Ex [simp del]
  
  from wtprog obtain wfmb where wfprog: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)
      
  from ins meth_C approx obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    frame:   "conf_f P h sh (ST,LT) ins (stk,loc,C,M,pc,ics)" and
    frames:  "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc:   "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)"
    by (fastforce dest: sees_method_fun)

  from ins wti \<Phi>_pc have n: "n \<le> size ST" by simp

  from ins wti \<Phi>_pc obtain D' b Ts T mxs' mxl' ins' xt' ST' LT' where
    pc': "pc+1 < size ins" and
    m_D: "P \<turnstile> D sees M',b: Ts\<rightarrow>T = (mxs',mxl',ins',xt') in D'" and
    Ts:  "P \<turnstile> rev (take n ST) [\<le>] Ts" and
    \<Phi>':  "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
    LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and
    ST': "P \<turnstile> (T # drop n ST) [\<le>] ST'" and
    b[simp]: "b = Static"
    by (clarsimp simp: sup_state_opt_any_Some)

  from frame obtain 
  stk: "P,h \<turnstile> stk [:\<le>] ST" and
  loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" by simp

  let ?loc' = "rev (take n stk) @ replicate mxl' undefined"
  let ?f' = "([], ?loc', D', M', 0, No_ics)"
  let ?f  = "(stk, loc, C, M, pc, No_ics)"

  from m_D ins \<sigma>' meth_C no_xcp cs
  have s': "\<sigma>' = (None, h, ?f' # ?f # frs, sh)" by auto

  from Ts n have [simp]: "size Ts = n"
    by (auto dest: list_all2_lengthD)

  from m_D wfprog b
  obtain mD': "P \<turnstile> D' sees M',Static:Ts\<rightarrow>T=(mxs',mxl',ins',xt') in D'"
    by (fast dest: sees_method_idemp)
  moreover 
  with wtprog
  obtain start: "wt_start P D' Static Ts mxl' (\<Phi> D' M')" and ins': "ins' \<noteq> []"
    by (auto dest: wt_jvm_prog_impl_wt_start)
  then obtain LT\<^sub>0 where LT\<^sub>0: "\<Phi> D' M' ! 0 = Some ([], LT\<^sub>0)"
    by (clarsimp simp: wt_start_def defs1 sup_state_opt_any_Some split: staticb.splits)
  moreover
  have "conf_f P h sh ([], LT\<^sub>0) ins' ?f'"
  proof -
    let ?LT = "(map OK Ts) @ (replicate mxl' Err)"

    from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
    hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" by simp
    also note Ts finally
    have "P,h \<turnstile> rev (take n stk) [:\<le>\<^sub>\<top>] map OK Ts" by simp 
    also
    have "P,h \<turnstile> replicate mxl' undefined [:\<le>\<^sub>\<top>] replicate mxl' Err" 
      by simp
    also from m_D have "P \<turnstile> D \<preceq>\<^sup>* D'" by (rule sees_method_decl_above)
    ultimately
    have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] ?LT" by simp
    also from start LT\<^sub>0 have "P \<turnstile> \<dots> [\<le>\<^sub>\<top>] LT\<^sub>0" by (simp add: wt_start_def)
    finally have "P,h \<turnstile> ?loc' [:\<le>\<^sub>\<top>] LT\<^sub>0" .
    thus ?thesis using ins' by simp
  qed
  moreover
  have "conf_clinit P sh (?f'#?f#frs)" by(rule conf_clinit_Invoke[OF confc nclinit])
  ultimately
  show ?thesis using s' \<Phi>_pc approx meth_C m_D ins nclinit
    by (fastforce dest: sees_method_fun [of _ C])
qed
(*>*)

lemma Invokestatic_Init_correct: 
  fixes \<sigma>' :: jvm_state
  assumes wtprog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes meth_C: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes ins:    "ins ! pc = Invokestatic D M' n" and nclinit: "M' \<noteq> clinit"
  assumes wti:    "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes \<sigma>': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)"
  assumes approx: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)\<surd>"
  assumes no_xcp: "fst (exec_step P h stk loc C M pc No_ics frs sh) = None"
  assumes nDone: "\<forall>sfs. sh (fst(method P D M')) \<noteq> Some(sfs, Done)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>" 
(*<*)
proof -
  note split_paired_Ex [simp del]
  
  from wtprog obtain wfmb where wfprog: "wf_prog wfmb P" 
    by (simp add: wf_jvm_prog_phi_def)
      
  from ins meth_C approx obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and
    frames:  "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc:   "conf_clinit P sh ((stk,loc,C,M,pc,No_ics)#frs)" and
    pc:      "pc < size ins"
    by (fastforce dest: sees_method_fun)

  from ins wti \<Phi>_pc obtain D' b Ts T mxs' mxl' ins' xt' where
    m_D: "P \<turnstile> D sees M',b: Ts\<rightarrow>T = (mxs',mxl',ins',xt') in D'" and
    b[simp]: "b = Static"
    by clarsimp

  let ?f  = "(stk, loc, C, M, pc, Calling D' [])"

  from m_D ins \<sigma>' meth_C no_xcp nDone
  have s': "\<sigma>' = (None, h, ?f # frs, sh)" by(auto split: init_state.splits)

  have cls: "is_class P D'" by(rule sees_method_is_class'[OF m_D])

  from confc have confc': "conf_clinit P sh (?f#frs)"
    by(auto simp: conf_clinit_def distinct_clinit_def split: if_split_asm)
  with s' \<Phi>_pc approx meth_C m_D ins nclinit stk loc pc cls frames
  show ?thesis by(fastforce dest: sees_method_fun [of _ C])
qed
(*>*)

declare list_all2_Cons2 [iff]

lemma Return_correct:
  fixes \<sigma>' :: jvm_state
  assumes wt_prog: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes meth: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes ins: "ins ! pc = Return"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes correct: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from meth correct ins have [simp]: "ics = No_ics" by(cases ics, auto)

  from wt_prog 
  obtain wfmb where wf: "wf_prog wfmb P" by (simp add: wf_jvm_prog_phi_def)

  from meth ins s'
  have "frs = [] \<Longrightarrow> ?thesis" by (simp add: correct_state_def)
  moreover
  { fix f frs' assume frs': "frs = f#frs'"
    then obtain stk' loc' C' M' pc' ics' where 
      f: "f = (stk',loc',C',M',pc',ics')" by (cases f)

    from correct meth
    obtain ST LT where
      h_ok:   "P \<turnstile> h \<surd>" and
      sh_ok:   "P,h \<turnstile>\<^sub>s sh \<surd>" and
      \<Phi>_pc: "\<Phi> C M ! pc = Some (ST, LT)" and
      frame:  "conf_f P h sh (ST, LT) ins (stk,loc,C,M,pc,ics)" and
      frames: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
      confc: "conf_clinit P sh frs"
      by (auto dest: sees_method_fun conf_clinit_Cons simp: correct_state_def)

    from \<Phi>_pc ins wt
    obtain U ST\<^sub>0 where "ST = U # ST\<^sub>0" "P \<turnstile> U \<le> T"
      by (simp add: wt_instr_def app_def) blast    
    with wf frame 
    have hd_stk: "P,h \<turnstile> hd stk :\<le> T" by (auto simp: conf_f_def)

    from f frs' frames meth
    obtain ST' LT' b' Ts'' T'' mxs' mxl\<^sub>0' ins' xt' where
      \<Phi>': "\<Phi> C' M' ! pc' = Some (ST', LT')" and
      meth_C':  "P \<turnstile> C' sees M',b':Ts''\<rightarrow>T''=(mxs',mxl\<^sub>0',ins',xt') in C'" and
      frame':   "conf_f P h sh (ST',LT') ins' f" and
      conf_fs:  "conf_fs P h sh \<Phi> C' M' (size Ts'') T'' frs'"
     by clarsimp

    from f frame' obtain
      stk': "P,h \<turnstile> stk' [:\<le>] ST'" and
      loc': "P,h \<turnstile> loc' [:\<le>\<^sub>\<top>] LT'" and
      pc':  "pc' < size ins'"
      by (simp add: conf_f_def)

    { assume b[simp]: "b = NonStatic"

      from wf_NonStatic_nclinit[OF wf] meth have nclinit[simp]: "M \<noteq> clinit" by simp

      from f frs' meth ins s'
      have \<sigma>':
        "\<sigma>' = (None,h,(hd stk#(drop (1+size Ts) stk'),loc',C',M',pc'+1,ics')#frs',sh)"
        (is "\<sigma>' = (None,h,?f'#frs',sh)")
        by simp
      from f frs' confc conf_clinit_diff have confc'': "conf_clinit P sh (?f'#frs')" by blast
    
      with \<Phi>' meth_C' f frs' frames meth
      obtain D Ts' T' m D' where
        ins': "ins' ! pc' = Invoke M (size Ts)" and
        D: "ST' ! (size Ts) = Class D" and
        meth_D: "P \<turnstile> D sees M,b: Ts'\<rightarrow>T' = m in D'" and
        T': "P \<turnstile> T \<le> T'" and
        CsubD': "P \<turnstile> C \<preceq>\<^sup>* D'"
       by(auto dest: sees_method_fun sees_method_fun[OF sees_method_idemp])

      from wt_prog meth_C' pc'  
      have "P,T'',mxs',size ins',xt' \<turnstile> ins'!pc',pc' :: \<Phi> C' M'"
        by (rule wt_jvm_prog_impl_wt_instr)
      with ins' \<Phi>' D meth_D
      obtain ST'' LT'' where
        \<Phi>_suc:   "\<Phi> C' M' ! Suc pc' = Some (ST'', LT'')" and
        less:    "P \<turnstile> (T' # drop (size Ts+1) ST', LT') \<le>\<^sub>i (ST'', LT'')" and
        suc_pc': "Suc pc' < size ins'" 
        by (clarsimp simp: sup_state_opt_any_Some)
  
      from hd_stk T' have hd_stk': "P,h \<turnstile> hd stk :\<le> T'"  ..
  
      have frame'':
        "conf_f P h sh (ST'',LT'') ins' ?f'" 
      proof -
        from stk'
        have "P,h \<turnstile> drop (1+size Ts) stk' [:\<le>] drop (1+size Ts) ST'" ..
        moreover
        with hd_stk' less
        have "P,h \<turnstile> hd stk # drop (1+size Ts) stk' [:\<le>] ST''" by auto
        moreover
        from wf loc' less have "P,h \<turnstile> loc' [:\<le>\<^sub>\<top>] LT''" by auto
        moreover note suc_pc' 
        moreover
        from f frs' frames (* ics' = No_ics *)
        have "P,h,sh \<turnstile>\<^sub>i (C', M', Suc pc', ics')" by auto
        ultimately show ?thesis by (simp add: conf_f_def)
      qed
  
      with \<sigma>' frs' f meth h_ok sh_ok hd_stk \<Phi>_suc frames confc'' meth_C' \<Phi>'
      have ?thesis by(fastforce dest: sees_method_fun [of _ C'])
    }
    moreover
    { assume b[simp]: "b = Static" and nclinit[simp]: "M \<noteq> clinit"

      from f frs' meth ins s'
      have \<sigma>':
        "\<sigma>' = (None,h,(hd stk#(drop (size Ts) stk'),loc',C',M',pc'+1,ics')#frs',sh)"
        (is "\<sigma>' = (None,h,?f'#frs',sh)")
        by simp
      from f frs' confc conf_clinit_diff have confc'': "conf_clinit P sh (?f'#frs')" by blast

      with \<Phi>' meth_C' f frs' frames meth
      obtain D Ts' T' m where
        ins': "ins' ! pc' = Invokestatic D M (size Ts)" and
        meth_D: "P \<turnstile> D sees M,b: Ts'\<rightarrow>T' = m in C" and
        T': "P \<turnstile> T \<le> T'"
       by(auto dest: sees_method_fun sees_method_mono2[OF _ wf sees_method_idemp])
      
      from wt_prog meth_C' pc'  
      have "P,T'',mxs',size ins',xt' \<turnstile> ins'!pc',pc' :: \<Phi> C' M'"
        by (rule wt_jvm_prog_impl_wt_instr)
      with ins' \<Phi>' meth_D
      obtain ST'' LT'' where
        \<Phi>_suc:   "\<Phi> C' M' ! Suc pc' = Some (ST'', LT'')" and
        less:    "P \<turnstile> (T' # drop (size Ts) ST', LT') \<le>\<^sub>i (ST'', LT'')" and
        suc_pc': "Suc pc' < size ins'" 
        by (clarsimp simp: sup_state_opt_any_Some)
  
      from hd_stk T' have hd_stk': "P,h \<turnstile> hd stk :\<le> T'"  ..
  
      have frame'':
        "conf_f P h sh (ST'',LT'') ins' ?f'" 
      proof -
        from stk'
        have "P,h \<turnstile> drop (size Ts) stk' [:\<le>] drop (size Ts) ST'" ..
        moreover
        with hd_stk' less
        have "P,h \<turnstile> hd stk # drop (size Ts) stk' [:\<le>] ST''" by auto
        moreover
        from wf loc' less have "P,h \<turnstile> loc' [:\<le>\<^sub>\<top>] LT''" by auto
        moreover note suc_pc' 
        moreover
        from f frs' frames (* ics' = No_ics *)
        have "P,h,sh \<turnstile>\<^sub>i (C', M', Suc pc', ics')" by auto
        ultimately show ?thesis by (simp add: conf_f_def)
      qed
  
      with \<sigma>' frs' f meth h_ok sh_ok hd_stk \<Phi>_suc frames confc'' meth_C' \<Phi>'
      have ?thesis by(fastforce dest: sees_method_fun [of _ C'])
    }
    moreover
    { assume b[simp]: "b = Static" and clinit[simp]: "M = clinit"

      from frs' meth ins s'
      have \<sigma>':
        "\<sigma>' = (None,h,frs,sh(C\<mapsto>(fst(the(sh C)), Done)))" (is "\<sigma>' = (None,h,frs,?sh)")
        by simp

      from correct have dist': "distinct (C # clinit_classes frs)"
        by(simp add: conf_clinit_def distinct_clinit_def)

      from f frs' correct have confc1:
       "conf_clinit P sh ((stk, loc, C, clinit, pc, No_ics) # (stk',loc',C',M',pc',ics') # frs')"
        by simp
      then have ics_dist: "distinct (C # ics_classes ics')"
        by(simp add: conf_clinit_def distinct_clinit_def)

      from conf_clinit_Cons_Cons[OF confc1] have dist'': "distinct (C # clinit_classes frs')"
        by(simp add: conf_clinit_def distinct_clinit_def)

      from correct shconf_upd_obj[OF sh_ok _ [OF shconfD[OF sh_ok]]]
       have sh'_ok: "P,h \<turnstile>\<^sub>s ?sh \<surd>" by(clarsimp simp: conf_clinit_def)

      have frame'':
        "conf_f P h ?sh (ST',LT') ins' f" 
      proof -
        note stk' loc' pc' f valid_ics_shupd[OF _ ics_dist]
        moreover
        from f frs' frames
        have "P,h,sh \<turnstile>\<^sub>i (C', M', pc', ics')" by auto
        ultimately show ?thesis by (simp add: conf_f_def2)
      qed
      have conf_fs': "conf_fs P h ?sh \<Phi> C' M' (length Ts'') T'' frs'"
       by(rule conf_fs_shupd[OF conf_fs dist''])

      have confc'': "conf_clinit P ?sh frs" by(rule conf_clinit_shupd[OF confc dist'])

      from \<sigma>' f frs' h_ok sh'_ok conf_fs' frame'' \<Phi>' stk' loc' pc' meth_C' confc''
       have ?thesis by(fastforce dest: sees_method_fun)
    }
    ultimately have ?thesis by (cases b) blast+
  }
  ultimately
  show ?thesis by (cases frs) blast+
qed
(*>*)

declare sup_state_opt_any_Some [iff]
declare not_Err_eq [iff]

lemma Load_correct:
"\<lbrakk> wf_prog wt P;
    P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
    ins!pc = Load idx; 
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh); 
    P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk>
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
  apply(subgoal_tac "ics = No_ics")
   prefer 2 apply(cases ics, (auto)[4])
  apply clarsimp 
  apply (drule (1) sees_method_fun)
  apply(fastforce elim!: confTs_confT_sup conf_clinit_diff)
  done
(*>*)

declare [[simproc del: list_to_set_comprehension]]

lemma Store_correct:
"\<lbrakk> wf_prog wt P;
  P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C;
  ins!pc = Store idx;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M;
  Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh);
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk>
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
  apply(subgoal_tac "ics = No_ics")
   prefer 2 apply(cases ics, (auto)[4])
  apply clarsimp 
  apply (drule (1) sees_method_fun)
  apply (blast intro!: list_all2_update_cong conf_clinit_diff)+
  done
(*>*)


lemma Push_correct:
"\<lbrakk> wf_prog wt P;
    P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
    ins!pc = Push v;
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh);
    P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk>
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>" 
(*<*)
  apply(subgoal_tac "ics = No_ics")
   prefer 2 apply(cases ics, (auto)[4])
  apply clarsimp 
  apply (drule (1) sees_method_fun)
  apply (blast dest: typeof_lit_conf conf_clinit_diff)+
  done
(*>*)


lemma Cast_conf2:
  "\<lbrakk> wf_prog ok P; P,h \<turnstile> v :\<le> T; is_refT T; cast_ok P C h v; 
     P \<turnstile> Class C \<le> T'; is_class P C\<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> v :\<le> T'"
(*<*)
  apply (unfold cast_ok_def is_refT_def)
  apply (frule Class_widen)
  apply (elim exE disjE) 
     apply simp
    apply simp
   apply simp  
  apply (clarsimp simp: conf_def obj_ty_def)
  apply (cases v)
  apply (auto intro: rtrancl_trans)
  done
(*>*)


lemma Checkcast_correct:
"\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P;
    P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
    ins!pc = Checkcast D; 
    P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
    Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) ; 
    P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>;
    fst (exec_step P h stk loc C M pc ics frs sh) = None \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
  apply(subgoal_tac "ics = No_ics")
   prefer 2 apply(cases ics, (auto)[4])
  apply (clarsimp simp: wf_jvm_prog_phi_def split: if_split_asm)
  apply (drule (1) sees_method_fun)
  apply (blast intro: Cast_conf2 dest: sees_method_fun conf_clinit_diff)
  done
(*>*)

declare split_paired_All [simp del]

lemmas widens_Cons [iff] = list_all2_Cons1 [of "widen P"] for P

lemma Getfield_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes i:  "ins!pc = Getfield F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc ics frs sh) = None"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from mC cf i have [simp]: "ics = No_ics" by(cases ics, auto)

  from mC cf obtain ST LT where    
    "h\<surd>": "P \<turnstile> h \<surd>" and
    "sh\<surd>": "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)"
    by (fastforce dest: sees_method_fun)
       
  from i \<Phi> wt obtain oT ST'' vT ST' LT' vT' where 
    oT: "P \<turnstile> oT \<le> Class D" and
    ST: "ST = oT # ST''" and
    F:  "P \<turnstile> D sees F,NonStatic:vT in D" and
    pc': "pc+1 < size ins"  and
    \<Phi>': "\<Phi> C M ! (pc+1) = Some (vT'#ST', LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and  
    vT': "P \<turnstile> vT \<le> vT'"
    by fastforce

  from stk ST obtain ref stk' where 
    stk': "stk = ref#stk'" and
    ref:  "P,h \<turnstile> ref :\<le> oT" and
    ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
    by auto

  from stk' i mC s' xc have "ref \<noteq> Null"
    by (simp add: split_beta split:if_split_asm)
  moreover from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
  ultimately obtain a D' fs where 
    a: "ref = Addr a" and h: "h a = Some (D', fs)" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
    by (blast dest: non_npD)

  from D' F have has_field: "P \<turnstile> D' has F,NonStatic:vT in D"      
    by (blast intro: has_field_mono has_visible_field)
  moreover from "h\<surd>" h have "P,h \<turnstile> (D', fs) \<surd>" by (rule hconfD)
  ultimately obtain v where v: "fs (F, D) = Some v" "P,h \<turnstile> v :\<le> vT"
    by (clarsimp simp: oconf_def has_field_def) 
       (blast dest: has_fields_fun)

  from conf_clinit_diff[OF confc]
   have confc': "conf_clinit P sh ((v#stk',loc,C,M,pc+1,ics)#frs)" by simp

  from a h i mC s' stk' v xc has_field
  have "\<sigma>' = (None, h, (v#stk',loc,C,M,pc+1,ics)#frs, sh)"
   by(simp add: split_beta split: if_split_asm)
  moreover
  from ST'' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" ..
  moreover
  from v vT' have "P,h \<turnstile> v :\<le> vT'" by blast
  moreover
  from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
  moreover
  note "h\<surd>" "sh\<surd>" mC \<Phi>' pc' v fs confc'
  ultimately
  show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastforce
qed
(*>*)

lemma Getstatic_nInit_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes i:  "ins!pc = Getstatic C' F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc ics frs sh) = None"
  assumes cs: "ics = Called [] \<or> (ics = No_ics \<and> (\<exists>sfs. sh (fst(field P D F)) = Some(sfs, Done)))"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "P \<turnstile> h \<surd>" and
    "sh\<surd>": "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)" and
    vics: "P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"
    by (fastforce dest: sees_method_fun)

  from i \<Phi> wt cs obtain vT ST' LT' vT' where 
    F:  "P \<turnstile> C' sees F,Static:vT in D" and
    pc': "pc+1 < size ins"  and
    \<Phi>': "\<Phi> C M ! (pc+1) = Some (vT'#ST', LT')" and
    ST': "P \<turnstile> ST [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" and  
    vT': "P \<turnstile> vT \<le> vT'"
    by fastforce

  with mC i vics obtain sobj where
    cc': "ics = Called [] \<Longrightarrow> Called_context P D (ins!pc) \<and> sh D = Some sobj"
   by(fastforce dest: has_visible_field)

  from field_def2[OF sees_field_idemp[OF F]] have D[simp]: "fst(field P D F) = D" by simp
  from cs cc' obtain sfs i where shD: "sh D = Some(sfs,i)" by(cases sobj, auto)

  note has_field_idemp[OF has_visible_field[OF F]]
  moreover from "sh\<surd>" shD have "P,h,D \<turnstile>\<^sub>s sfs \<surd>" by (rule shconfD)
  ultimately obtain v where v: "sfs F = Some v" "P,h \<turnstile> v :\<le> vT"
    by (clarsimp simp: soconf_def has_field_def) blast

  from i mC s' v xc F cs cc' shD
  have "\<sigma>' = (None, h, (v#stk,loc,C,M,pc+1,No_ics)#frs, sh)"
   by(fastforce simp: split_beta split: if_split_asm init_call_status.splits)
  moreover
  from stk ST' have "P,h \<turnstile> stk [:\<le>] ST'" ..
  moreover
  from v vT' have "P,h \<turnstile> v :\<le> vT'" by blast
  moreover
  from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
  moreover
  have "conf_clinit P sh ((v#stk,loc,C,M,pc+1,No_ics)#frs)" by(rule conf_clinit_diff'[OF confc])
  moreover
  note "h\<surd>" "sh\<surd>" mC \<Phi>' pc' v fs
  ultimately
  show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastforce
qed
(*>*)

lemma Getstatic_Init_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes i:  "ins!pc = Getstatic C' F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc No_ics frs sh) = None"
  assumes nDone: "\<forall>sfs. sh (fst(field P D F)) \<noteq> Some(sfs, Done)"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "P \<turnstile> h \<surd>" and
    "sh\<surd>": "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,No_ics)#frs)"
   by (fastforce dest: sees_method_fun)

  from i \<Phi> wt nDone obtain vT where 
    F:  "P \<turnstile> C' sees F,Static:vT in D"
    by fastforce
  then have has_field: "P \<turnstile> C' has F,Static:vT in D" by(rule has_visible_field)

  from field_def2[OF sees_field_idemp[OF F]] has_field_is_class'[OF has_field] obtain
    D[simp]: "fst(field P D F) = D" and
    cls: "is_class P D" by simp

  from i mC s' xc F nDone
  have "\<sigma>' = (None, h, (stk,loc,C,M,pc,Calling D [])#frs, sh)"
   by(auto simp: split_beta split: if_split_asm init_state.splits)
  moreover
  from confc have "conf_clinit P sh ((stk,loc,C,M,pc,Calling D [])#frs)"
     by(auto simp: conf_clinit_def distinct_clinit_def split: if_split_asm)
  moreover
  note loc stk "h\<surd>" "sh\<surd>" mC \<Phi> pc fs i has_field cls
  ultimately
  show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastforce
qed
(*>*)

lemma Putfield_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes i:  "ins!pc = Putfield F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc ics frs sh) = None"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from mC cf i have [simp]: "ics = No_ics" by(cases ics, auto)

  from mC cf obtain ST LT where    
    "h\<surd>": "P \<turnstile> h \<surd>" and      
    "sh\<surd>": "P,h \<turnstile>\<^sub>s sh \<surd>" and    
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,ics) # frs)"
    by (fastforce dest: sees_method_fun)
  
  from i \<Phi> wt obtain vT vT' oT ST'' ST' LT' where 
    ST: "ST = vT # oT # ST''" and
    field: "P \<turnstile> D sees F,NonStatic:vT' in D" and
    oT: "P \<turnstile> oT \<le> Class D" and vT: "P \<turnstile> vT \<le> vT'" and
    pc': "pc+1 < size ins" and 
    \<Phi>': "\<Phi> C M!(pc+1) = Some (ST',LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'"
    by clarsimp

  from stk ST obtain v ref stk' where 
    stk': "stk = v#ref#stk'" and
    v:    "P,h \<turnstile> v :\<le> vT" and 
    ref:  "P,h \<turnstile> ref :\<le> oT" and
    ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
    by auto

  from stk' i mC s' xc have "ref \<noteq> Null" by (auto simp: split_beta)
  moreover from ref oT have "P,h \<turnstile> ref :\<le> Class D" ..
  ultimately obtain a D' fs where 
    a: "ref = Addr a" and h: "h a = Some (D', fs)" and D': "P \<turnstile> D' \<preceq>\<^sup>* D"
    by (blast dest: non_npD)

  from v vT have vT': "P,h \<turnstile> v :\<le> vT'" ..

  from field D' have has_field: "P \<turnstile> D' has F,NonStatic:vT' in D"
    by (blast intro: has_field_mono has_visible_field)

  let ?h' = "h(a\<mapsto>(D', fs((F, D)\<mapsto>v)))" and ?f' = "(stk',loc,C,M,pc+1,ics)"
  from h have hext: "h \<unlhd> ?h'" by (rule hext_upd_obj)

  have "sh\<surd>'": "P,?h' \<turnstile>\<^sub>s sh \<surd>" by(rule shconf_hupd_obj[OF "sh\<surd>" h])

  from a h i mC s' stk' has_field field
  have "\<sigma>' = (None, ?h', ?f'#frs, sh)" by(simp split: if_split_asm)
  moreover
  from "h\<surd>" h have "P,h \<turnstile> (D',fs)\<surd>" by (rule hconfD) 
  with has_field vT' have "P,h \<turnstile> (D',fs((F, D)\<mapsto>v))\<surd>" ..
  with "h\<surd>" h have "P \<turnstile> ?h'\<surd>" by (rule hconf_upd_obj)
  moreover
  from ST'' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" ..
  from this hext have "P,?h' \<turnstile> stk' [:\<le>] ST'" by (rule confs_hext)
  moreover
  from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
  from this hext have "P,?h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" by (rule confTs_hext)
  moreover
  from fs hext
  have "conf_fs P ?h' sh \<Phi> C M (size Ts) T frs" by (rule conf_fs_hext)
  moreover
  have "conf_clinit P sh (?f' # frs)" by(rule conf_clinit_diff[OF confc])
  moreover
  note mC \<Phi>' pc' "sh\<surd>'"
  ultimately
  show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastforce
qed
(*>*)

lemma Putstatic_nInit_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes i:  "ins!pc = Putstatic C' F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc ics frs sh) = None"
  assumes cs: "ics = Called [] \<or> (ics = No_ics \<and> (\<exists>sfs. sh (fst(field P D F)) = Some(sfs, Done)))"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "P \<turnstile> h \<surd>" and
    "sh\<surd>": "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,ics)#frs)" and
    vics: "P,h,sh \<turnstile>\<^sub>i (C,M,pc,ics)"
    by (fastforce dest: sees_method_fun)

  from i \<Phi> wt cs obtain vT vT' ST'' ST' LT' where 
    ST: "ST = vT # ST''" and
    F:  "P \<turnstile> C' sees F,Static:vT' in D" and
    vT: "P \<turnstile> vT \<le> vT'" and
    pc': "pc+1 < size ins"  and
    \<Phi>': "\<Phi> C M ! (pc+1) = Some (ST', LT')" and
    ST': "P \<turnstile> ST'' [\<le>] ST'" and LT': "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'"
    by fastforce

  from stk ST obtain v stk' where 
    stk': "stk = v#stk'" and
    v:    "P,h \<turnstile> v :\<le> vT" and
    ST'': "P,h \<turnstile> stk' [:\<le>] ST''"
    by auto

  from v vT have vT': "P,h \<turnstile> v :\<le> vT'" ..

  with mC i vics obtain sobj where
    cc': "ics = Called [] \<Longrightarrow> Called_context P D (ins!pc) \<and> sh D = Some sobj"
   by(fastforce dest: has_visible_field)

  from field_def2[OF sees_field_idemp[OF F]] have D[simp]: "fst(field P D F) = D" by simp
  from cs cc' obtain sfs i where shD: "sh D = Some(sfs,i)" by(cases sobj, auto)

  let ?sh' = "sh(D\<mapsto>(sfs(F\<mapsto>v),i))" and ?f' = "(stk',loc,C,M,pc+1,No_ics)"

  have m_D: "P \<turnstile> D has F,Static:vT' in D" by (rule has_field_idemp[OF has_visible_field[OF F]])
  from "sh\<surd>" shD have sfs: "P,h,D \<turnstile>\<^sub>s sfs \<surd>" by (rule shconfD)

  have "sh'\<surd>": "P,h \<turnstile>\<^sub>s ?sh' \<surd>" by (rule shconf_upd_obj[OF "sh\<surd>" soconf_fupd[OF m_D vT' sfs]])

  from i mC s' v xc F cs cc' shD stk'
  have "\<sigma>' = (None, h, (stk',loc,C,M,pc+1,No_ics)#frs, ?sh')"
   by(fastforce simp: split_beta split: if_split_asm init_call_status.splits)
  moreover
  from ST'' ST' have "P,h \<turnstile> stk' [:\<le>] ST'" ..
  moreover
  from loc LT' have "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'" ..
  moreover
  have "conf_fs P h ?sh' \<Phi> C M (size Ts) T frs" by (rule conf_fs_shupd'[OF fs shD])
  moreover
  have "conf_clinit P ?sh' ((stk',loc,C,M,pc+1,No_ics)#frs)"
   by(rule conf_clinit_diff'[OF conf_clinit_shupd'[OF confc shD]])
  moreover
  note "h\<surd>" "sh'\<surd>" mC \<Phi>' pc' v vT'
  ultimately
  show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastforce
qed
(*>*)

lemma Putstatic_Init_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf: "wf_prog wt P"
  assumes mC: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes i:  "ins!pc = Putstatic C' F D"
  assumes wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes s': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)"
  assumes cf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)\<surd>"
  assumes xc: "fst (exec_step P h stk loc C M pc No_ics frs sh) = None"
  assumes nDone: "\<forall>sfs. sh (fst(field P D F)) \<noteq> Some(sfs, Done)"

  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from mC cf obtain ST LT where    
    "h\<surd>": "P \<turnstile> h \<surd>" and
    "sh\<surd>": "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>: "\<Phi> C M ! pc = Some (ST,LT)" and
    stk: "P,h \<turnstile> stk [:\<le>] ST" and loc: "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT" and
    pc: "pc < size ins" and 
    fs: "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc: "conf_clinit P sh ((stk,loc,C,M,pc,No_ics)#frs)"
   by (fastforce dest: sees_method_fun)

  from i \<Phi> wt nDone obtain vT where 
    F:  "P \<turnstile> C' sees F,Static:vT in D"
    by fastforce
  then have has_field: "P \<turnstile> C' has F,Static:vT in D" by(rule has_visible_field)

  from field_def2[OF sees_field_idemp[OF F]] has_field_is_class'[OF has_field] obtain
    D[simp]: "fst(field P D F) = D" and
    cls: "is_class P D" by simp

  from i mC s' xc F nDone
  have "\<sigma>' = (None, h, (stk,loc,C,M,pc,Calling D [])#frs, sh)"
   by(auto simp: split_beta split: if_split_asm init_state.splits)
  moreover
  from confc have "conf_clinit P sh ((stk,loc,C,M,pc,Calling D [])#frs)"
     by(auto simp: conf_clinit_def distinct_clinit_def split: if_split_asm)
  moreover
  note loc stk "h\<surd>" "sh\<surd>" mC \<Phi> pc fs i has_field cls
  ultimately
  show "P,\<Phi> \<turnstile> \<sigma>' \<surd>" by fastforce
qed
(*>*)
  
(* FIXME: move *)
lemma oconf_blank2 [intro, simp]:
    "\<lbrakk>is_class P C; wf_prog wt P\<rbrakk> \<Longrightarrow> P,h \<turnstile> blank P C \<surd>"
(*<*)
  by (fastforce simp: oconf_blank dest: wf_Fields_Ex)
(*>*)

lemma obj_ty_blank [iff]: "obj_ty (blank P C) = Class C"
  by (simp add: blank_def)

lemma New_nInit_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes ins:  "ins!pc = New X"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes exec: "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
  assumes conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
  assumes no_x: "fst (exec_step P h stk loc C M pc ics frs sh) = None"
  assumes cs: "ics = Called [] \<or> (ics = No_ics \<and> (\<exists>sfs. sh X = Some(sfs, Done)))"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    sheap_ok: "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    frame:   "conf_f P h sh (ST,LT) ins (stk,loc,C,M,pc,ics)" and
    frames:  "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc:   "conf_clinit P sh ((stk,loc,C,M,pc,ics) # frs)"
    by (auto dest: sees_method_fun)

  from \<Phi>_pc ins wt
  obtain ST' LT' where
    is_class_X: "is_class P X" and
    mxs:       "size ST < mxs" and
    suc_pc:     "pc+1 < size ins" and
    \<Phi>_suc:      "\<Phi> C M!(pc+1) = Some (ST', LT')" and
    less:       "P \<turnstile> (Class X # ST, LT) \<le>\<^sub>i (ST', LT')"
    by auto

  from ins no_x cs meth obtain oref where new_Addr: "new_Addr h = Some oref" by auto
  hence h: "h oref = None" by (rule new_Addr_SomeD) 
  
  with exec ins meth new_Addr cs have \<sigma>':
    "\<sigma>' = (None, h(oref \<mapsto> blank P X), (Addr oref#stk,loc,C,M,pc+1,No_ics)#frs, sh)"
    (is "\<sigma>' = (None, ?h', ?f # frs, sh)")
    by auto
  moreover
  from wf h heap_ok is_class_X have h': "P \<turnstile> ?h' \<surd>"
    by (auto intro: hconf_new)
  moreover
  from h frame less suc_pc wf
  have "conf_f P ?h' sh (ST', LT') ins ?f"
    apply (clarsimp simp: fun_upd_apply conf_def blank_def split_beta)
    apply (auto intro: confs_hext confTs_hext)
    done      
  moreover
  from h have "h \<unlhd> ?h'" by simp
  with frames have "conf_fs P ?h' sh \<Phi> C M (size Ts) T frs" by (rule conf_fs_hext)
  moreover
  have "P,?h' \<turnstile>\<^sub>s sh \<surd>" by(rule shconf_hnew[OF sheap_ok h])
  moreover
  have "conf_clinit P sh (?f # frs)" by(rule conf_clinit_diff'[OF confc])
  ultimately
  show ?thesis using meth \<Phi>_suc by fastforce 
qed
(*>*)

lemma New_Init_correct:
  fixes \<sigma>' :: jvm_state
  assumes wf:   "wf_prog wt P"
  assumes meth: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
  assumes ins:  "ins!pc = New X"
  assumes wt:   "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
  assumes exec: "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)"
  assumes conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)\<surd>"
  assumes no_x: "fst (exec_step P h stk loc C M pc No_ics frs sh) = None"
  assumes nDone: "\<forall>sfs. sh X \<noteq> Some(sfs, Done)"
  shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof - 
  from ins conf meth
  obtain ST LT where
    heap_ok: "P\<turnstile> h\<surd>" and
    sheap_ok: "P,h \<turnstile>\<^sub>s sh \<surd>" and
    \<Phi>_pc:    "\<Phi> C M!pc = Some (ST,LT)" and
    frame:   "conf_f P h sh (ST,LT) ins (stk,loc,C,M,pc,No_ics)" and
    frames:  "conf_fs P h sh \<Phi> C M (size Ts) T frs" and
    confc:   "conf_clinit P sh ((stk,loc,C,M,pc,No_ics) # frs)"
    by (auto dest: sees_method_fun)

  from \<Phi>_pc ins wt
  obtain ST' LT' where
    is_class_X: "is_class P X" and
    mxs:       "size ST < mxs" and
    suc_pc:     "pc+1 < size ins" and
    \<Phi>_suc:      "\<Phi> C M!(pc+1) = Some (ST', LT')" and
    less:       "P \<turnstile> (Class X # ST, LT) \<le>\<^sub>i (ST', LT')"
    by auto
  
  with exec ins meth nDone have \<sigma>':
    "\<sigma>' = (None, h, (stk,loc,C,M,pc,Calling X [])#frs, sh)"
    (is "\<sigma>' = (None, h, ?f # frs, sh)")
    by(auto split: init_state.splits)
  moreover
  from meth frame is_class_X ins
  have "conf_f P h sh (ST, LT) ins ?f" by auto
  moreover note heap_ok sheap_ok frames
  moreover
  from confc have "conf_clinit P sh (?f # frs)"
    by(auto simp: conf_clinit_def distinct_clinit_def split: if_split_asm)
  ultimately
  show ?thesis using meth \<Phi>_pc by fastforce 
qed
(*>*)


lemma Goto_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
  ins ! pc = Goto branch; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) ; 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply(subgoal_tac "ics = No_ics")
 prefer 2 apply(cases ics, (auto)[4])
apply clarsimp 
apply (drule (1) sees_method_fun)
apply (fastforce elim!: conf_clinit_diff)
done
(*>*)


lemma IfFalse_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
  ins ! pc = IfFalse branch; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) ; 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply(subgoal_tac "ics = No_ics")
 prefer 2 apply(cases ics, (auto)[4])
apply clarsimp
apply (drule (1) sees_method_fun)
apply (fastforce elim!: conf_clinit_diff)
done
(*>*)

lemma CmpEq_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
  ins ! pc = CmpEq;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) ; 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply(subgoal_tac "ics = No_ics")
 prefer 2 apply(cases ics, (auto)[4])
apply clarsimp
apply (drule (1) sees_method_fun)
apply (fastforce elim!: conf_clinit_diff)
done
(*>*)

lemma Pop_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
  ins ! pc = Pop;
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) ; 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply(subgoal_tac "ics = No_ics")
 prefer 2 apply(cases ics, (auto)[4])
apply clarsimp
apply (drule (1) sees_method_fun)
apply (fastforce elim!: conf_clinit_diff)
done
(*>*)


lemma IAdd_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
  ins ! pc = IAdd; 
  P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M; 
  Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) ; 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply(subgoal_tac "ics = No_ics")
 prefer 2 apply(cases ics, (auto)[4])
apply (clarsimp simp: conf_def)
apply (drule (1) sees_method_fun)
apply (fastforce elim!: conf_clinit_diff)
done
(*>*)


lemma Throw_correct:
"\<lbrakk> wf_prog wt P; 
  P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C; 
  ins ! pc = Throw; 
  Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh) ; 
  P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>;
  fst (exec_step P h stk loc C M pc ics frs sh) = None \<rbrakk> 
\<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
apply(subgoal_tac "ics = No_ics")
 prefer 2 apply(cases ics, (auto)[4])
apply simp
done

text \<open>
  The next theorem collects the results of the sections above,
  i.e.~exception handling, initialization procedure steps, and
  the execution step for each instruction. It states type safety
  for single step execution: in welltyped programs, a conforming
  state is transformed into another conforming state when one
  step of execution is performed.
\<close>
lemma step_correct:
fixes \<sigma>' :: jvm_state
assumes wtp: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
 and meth: "P \<turnstile> C sees M,b:Ts\<rightarrow>T=(mxs,mxl\<^sub>0,ins,xt) in C"
 and exec: "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,ics)#frs, sh)"
 and conf: "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd>"
shows "P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
proof -
  from assms have pc: "pc < length ins" by(auto dest: sees_method_fun)
  with wt_jvm_prog_impl_wt_instr[OF wtp meth] have wt: "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
    by simp
  
  from conf obtain ST LT where \<Phi>: "\<Phi> C M ! pc = Some(ST,LT)" by clarsimp

  show ?thesis
  proof(cases "fst (exec_step P h stk loc C M pc ics frs sh)")
    case Some show ?thesis by(rule xcpt_correct[OF wtp meth wt Some exec conf])
  next
    case None
    from wt_jvm_progD[OF wtp] obtain wf_md where wf: "wf_prog wf_md P" by clarify
    
    { assume [simp]: "ics = No_ics"

      from exec conf None obtain
           exec': "Some \<sigma>' = exec (P, None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)"
       and conf': "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,No_ics)#frs, sh)\<surd>"
       and None': "fst (exec_step P h stk loc C M pc No_ics frs sh) = None" by simp

      have ?thesis
      proof(cases "ins!pc")
        case Load from Load_correct[OF wf meth this wt exec conf] show ?thesis by simp
      next
        case Store from Store_correct[OF wf meth this wt exec conf] show ?thesis by simp
      next
        case Push from Push_correct[OF wf meth this wt exec conf] show ?thesis by simp
      next
        case (New C) show ?thesis
        proof(cases "\<exists>sfs. sh C = Some(sfs, Done)")
          case True
          with New_nInit_correct[OF wf meth New wt exec conf None] show ?thesis by simp
        next
          case False
          with New_Init_correct[OF wf meth New wt exec' conf' None'] show ?thesis by simp
        qed
      next
        case Getfield from Getfield_correct[OF wf meth this wt exec conf None]
          show ?thesis by simp
      next
        case (Getstatic C F D) show ?thesis
        proof(cases "\<exists>sfs. sh (fst (field P D F)) = Some(sfs, Done)")
          case True
          with Getstatic_nInit_correct[OF wf meth Getstatic wt exec conf None] show ?thesis by simp
        next
          case False
          with Getstatic_Init_correct[OF wf meth Getstatic wt exec' conf' None']
           show ?thesis by simp
        qed
      next
        case Putfield from Putfield_correct[OF wf meth this wt exec conf None]
         show ?thesis by simp
      next
        case (Putstatic C F D) show ?thesis
        proof(cases "\<exists>sfs. sh (fst (field P D F)) = Some(sfs, Done)")
          case True
          with Putstatic_nInit_correct[OF wf meth Putstatic wt exec conf None] show ?thesis by simp
        next
          case False
          with Putstatic_Init_correct[OF wf meth Putstatic wt exec' conf' None']
           show ?thesis by simp
        qed
      next
        case Checkcast from Checkcast_correct[OF wtp meth this wt exec conf None]
          show ?thesis by simp
      next
        case Invoke with Invoke_correct[OF wtp meth this wt exec conf None] show ?thesis by simp
      next
        case (Invokestatic C M n)
        from wf_jvm_prog_nclinit[OF wtp meth wt pc \<Phi> this] have ncl: "M \<noteq> clinit" by simp
        show ?thesis
        proof(cases "\<exists>sfs. sh (fst (method P C M)) = Some(sfs, Done)")
          case True
          with Invokestatic_nInit_correct[OF wtp meth Invokestatic ncl wt exec conf None]
           show ?thesis by simp
        next
          case False
          with Invokestatic_Init_correct[OF wtp meth Invokestatic ncl wt exec' conf' None']
           show ?thesis by simp
        qed
      next
        case Return with Return_correct[OF wtp meth this wt exec conf] show ?thesis by simp
      next
        case Pop with Pop_correct[OF wf meth this wt exec conf] show ?thesis by simp
      next
        case IAdd with IAdd_correct[OF wf meth this wt exec conf] show ?thesis by simp
      next
        case Goto with Goto_correct[OF wf meth this wt exec conf] show ?thesis by simp
      next
        case CmpEq with CmpEq_correct[OF wf meth this wt exec conf] show ?thesis by simp
      next
        case IfFalse with IfFalse_correct[OF wf meth this wt exec conf] show ?thesis by simp
      next
        case Throw with Throw_correct[OF wf meth this exec conf None] show ?thesis by simp
      qed
    }
    moreover
    { fix Cs assume [simp]: "ics = Called Cs"
      have ?thesis
      proof(cases Cs)
        case [simp]: Nil
        from conf meth obtain C1 where "Called_context P C1 (ins ! pc)"
         by(clarsimp simp: conf_f_def2 intro!: Called_context_Called_set)
        then have "ins!pc \<in> Called_set" by(rule Called_context_Called_set)
        then show ?thesis
        proof(cases "ins!pc")
          case (New C)
           from New_nInit_correct[OF wf meth this wt exec conf None] show ?thesis by simp
        next
          case (Getstatic C F D)
           from Getstatic_nInit_correct[OF wf meth this wt exec conf None] show ?thesis by simp
        next
          case (Putstatic C F D)
           from Putstatic_nInit_correct[OF wf meth this wt exec conf None] show ?thesis by simp
        next
          case (Invokestatic C M n)
          from wf_jvm_prog_nclinit[OF wtp meth wt pc \<Phi> this] have ncl: "M \<noteq> clinit" by simp
          with Invokestatic_nInit_correct[OF wtp meth Invokestatic ncl wt exec conf None]
            show ?thesis by simp
        qed(simp_all)
      next
        case (Cons C' Cs') with Called_correct[OF wtp meth exec conf None] show ?thesis by simp
      qed
    }
    moreover
    { fix C' Cs assume [simp]: "ics = Calling C' Cs"
      with Calling_correct[OF wtp meth exec conf None] have ?thesis by simp
    }
    moreover
    { fix Cs a assume [simp]: "ics = Throwing Cs a"
      have ?thesis
      proof(cases Cs)
        case Nil with exec None show ?thesis by simp
      next
        case (Cons C' Cs')
        with Throwing_correct[OF wtp meth exec conf None] show ?thesis by simp
      qed
    }
    ultimately show ?thesis by(cases ics) auto
  qed
qed
(*>*)

subsection \<open> Main \<close>

lemma correct_state_impl_Some_method:
  "P,\<Phi> \<turnstile> (None, h, (stk,loc,C,M,pc,ics)#frs, sh)\<surd> 
  \<Longrightarrow> \<exists>b m Ts T. P \<turnstile> C sees M,b:Ts\<rightarrow>T = m in C"
  by fastforce

lemma BV_correct_1 [rule_format]:
"\<And>\<sigma>. \<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,\<Phi> \<turnstile> \<sigma>\<surd>\<rbrakk> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow>\<^sub>1 \<sigma>' \<longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply (simp only: split_tupled_all exec_1_iff)
apply (rename_tac xp h frs sh)
apply (case_tac xp)
 apply (case_tac frs)
  apply simp
 apply (simp only: split_tupled_all)
 apply hypsubst
 apply (frule correct_state_impl_Some_method)
 apply clarify
 apply (rule step_correct)
    apply assumption+
  apply (rule sym)
  apply assumption+
apply (case_tac frs)
 apply simp_all
done
(*>*)


theorem progress:
  "\<lbrakk> xp=None; frs\<noteq>[] \<rbrakk> \<Longrightarrow> \<exists>\<sigma>'. P \<turnstile> (xp,h,frs,sh) -jvm\<rightarrow>\<^sub>1 \<sigma>'"
  by (clarsimp simp: exec_1_iff neq_Nil_conv split_beta
               simp del: split_paired_Ex)

lemma progress_conform:
  "\<lbrakk>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,\<Phi> \<turnstile> (xp,h,frs,sh)\<surd>; xp=None; frs\<noteq>[]\<rbrakk> 
  \<Longrightarrow> \<exists>\<sigma>'. P \<turnstile> (xp,h,frs,sh) -jvm\<rightarrow>\<^sub>1 \<sigma>' \<and> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply (drule progress)
 apply assumption
apply (fast intro: BV_correct_1)
done
(*>*)

theorem BV_correct [rule_format]:
"\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>' \<rbrakk> \<Longrightarrow> P,\<Phi> \<turnstile> \<sigma>\<surd> \<longrightarrow> P,\<Phi> \<turnstile> \<sigma>'\<surd>"
(*<*)
apply (simp only: exec_all_def1)
apply (erule rtrancl_induct)
 apply simp
apply clarify
apply (erule (2) BV_correct_1)
done
(*>*)

lemma hconf_start:   
  assumes wf: "wf_prog wf_mb P"
  shows "P \<turnstile> (start_heap P) \<surd>"
(*<*)
  apply (unfold hconf_def)
  apply (simp add: preallocated_start)
  apply (clarify)
  apply (drule sym)
  apply (unfold start_heap_def)
  apply (insert wf)
  apply (auto simp: fun_upd_apply is_class_xcpt split: if_split_asm)
  done
(*>*)

lemma shconf_start:   
  "\<not> is_class P Start \<Longrightarrow> P,start_heap P \<turnstile>\<^sub>s start_sheap \<surd>"
(*<*)
  apply (unfold shconf_def)
  apply (clarsimp simp: preallocated_start fun_upd_apply soconf_def has_field_is_class)
  done
(*>*)

lemma BV_correct_initial: 
  shows "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<not>is_class P Start;
     P \<turnstile> C sees M,Static:[]\<rightarrow>Void = m in C; M \<noteq> clinit;
     \<Phi>' Start start_m = start_\<phi>\<^sub>m \<rbrakk>
  \<Longrightarrow> start_prog P C M,\<Phi>' \<turnstile> start_state P \<surd>"
(*<*)
  apply(subgoal_tac "is_class P Object")
   prefer 2 apply(simp add: wf_jvm_prog_phi_def)
  apply(subgoal_tac "\<exists>Mm. P \<turnstile> Object sees_methods Mm")
   prefer 2 apply(fastforce simp: is_class_def dest: sees_methods_Object)
  apply (cases m)                            
  apply (unfold  start_state_def)
  apply (unfold correct_state_def)
  apply (simp del: defs1)
  apply (rule conjI)
   apply (simp add: wf_jvm_prog_phi_def class_add_hconf_wf[OF _ hconf_start] start_heap_nStart)
  apply (rule conjI)
   using start_prog_start_shconf apply(simp add: wf_jvm_prog_phi_def)
  apply (rule conjI)
   apply(simp add: conf_clinit_def distinct_clinit_def)
  apply (drule wt_jvm_prog_impl_wt_start, assumption+)
  apply (unfold conf_f_def wt_start_def)
  apply (fastforce dest: start_prog_Start_sees_start_method)
  done

declare [[simproc add: list_to_set_comprehension]]
(*>*)

theorem typesafe:
  assumes welltyped:   "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"
  assumes nstart:      "\<not> is_class P Start"
  assumes main_method: "P \<turnstile> C sees M,Static:[]\<rightarrow>Void = m in C"
  assumes nclinit:     "M \<noteq> clinit"
  assumes \<Phi>:           "\<And>C. C \<noteq> Start \<Longrightarrow> \<Phi>' C = \<Phi> C"
  assumes \<Phi>':          "\<Phi>' Start start_m = start_\<phi>\<^sub>m" "\<Phi>' Start clinit = start_\<phi>\<^sub>m"
  assumes Obj_start_m:
    "(\<And>b' Ts' T' m' D'. P \<turnstile> Object sees start_m, b' :  Ts'\<rightarrow>T' = m' in D'
         \<Longrightarrow> b' = Static \<and> Ts' = [] \<and> T' = Void)"
  shows "start_prog P C M \<turnstile> start_state P -jvm\<rightarrow> \<sigma>  \<Longrightarrow>  start_prog P C M,\<Phi>' \<turnstile> \<sigma> \<surd>"
(*<*)
proof -
  from welltyped nstart main_method nclinit \<Phi>'(1)
  have "start_prog P C M,\<Phi>' \<turnstile> start_state P \<surd>" by (rule BV_correct_initial)
  moreover
  assume "start_prog P C M \<turnstile> start_state P -jvm\<rightarrow> \<sigma>"
  moreover
  from start_prog_wf_jvm_prog_phi[OF welltyped nstart main_method nclinit \<Phi> \<Phi>' Obj_start_m]
   have "wf_jvm_prog\<^bsub>\<Phi>'\<^esub>(start_prog P C M)" by simp
  ultimately  
  show "start_prog P C M,\<Phi>' \<turnstile> \<sigma> \<surd>" using welltyped by - (rule BV_correct)
qed
(*>*)

end
