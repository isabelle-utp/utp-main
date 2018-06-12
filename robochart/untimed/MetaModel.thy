section \<open> RoboChart Meta-Model \<close>

theory MetaModel
  imports Actions
begin

subsection \<open> State Machine Syntax \<close>

text \<open> All state machine statespace types extend the following type which provides a state control variable \<close>

alphabet robochart_ctrl =
  rc_ctrl :: string 

type_synonym 's rcst = "'s robochart_ctrl_scheme"
type_synonym ('s, 'e) RoboAction = "('s robochart_ctrl_scheme, 'e) Action"
type_synonym 's RoboPred = "'s robochart_ctrl_scheme upred"

translations
  (type) "'s rcst" <= (type) "'s robochart_ctrl_scheme"
  (type) "('s, 'e) RoboAction" <= (type) "('s rcst, 'e) Action"
  (type) "'s RoboPred" <= (type) "'s rcst upred"

abbreviation "rc_state \<equiv> robochart_ctrl_child_lens"

notation rc_state ("\<^bold>r")

syntax
  "_svid_rc_state"  :: "svid" ("\<^bold>r")

translations
  "_svid_rc_state" == "CONST rc_state"

record ('s, 'e) Transition = 
  tn_source    :: string
  tn_target    :: string
  tn_trigger   :: "('s, 'e) Action option"
  tn_condition :: "'s upred"
  tn_action    :: "('s, 'e) Action"

declare Transition.defs [simp]

record ('s, 'e) Node =
  n_name   :: "string"
  n_entry  :: "('s, 'e) Action"
  n_during :: "('s, 'e) Action"
  n_exit   :: "('s, 'e) Action"

declare Node.defs [simp]

record ('s, 'e) StateMachine =
  sm_initial     :: "string" ("init\<index>")
  sm_finals      :: "string list" ("finals\<index>")
  sm_nodes       :: "('s, 'e) Node list" ("nodes\<index>")
  sm_transitions :: "('s, 'e) Transition list" ("\<^bold>T\<index>")

declare StateMachine.defs [simp]

thm set_map

definition sm_node_names :: "('s, 'e) StateMachine \<Rightarrow> string set" ("nnames\<index>") where
"sm_node_names sm \<equiv> n_name ` set(sm_nodes sm)"

definition sm_inters :: "('s, 'e) StateMachine \<Rightarrow> ('s, 'e) Node list" where
"sm_inters sm = filter (\<lambda> n. n_name n \<notin> set(sm_finals sm)) (sm_nodes sm)"

definition sm_inter_names ("inames\<index>") where
"sm_inter_names sm \<equiv> n_name ` set (sm_inters sm)"

abbreviation sm_final_names ("fnames\<index>") where
"sm_final_names M \<equiv> set (finals\<^bsub>M\<^esub>)"

definition sm_node_map :: "('s, 'e) StateMachine \<Rightarrow> (string \<rightharpoonup> ('s, 'e) Node)" ("nmap\<index>") where
"sm_node_map M = map_of (map (\<lambda> n. (n_name n, n)) (sm_nodes M))"

definition sm_trans_map :: "('s, 'e) StateMachine \<Rightarrow> (string \<rightharpoonup> ('s, 'e) Transition list)" ("tmap\<index>") where
"sm_trans_map M = map_of (map (\<lambda> n. (n_name n, filter (\<lambda> t. tn_source t = n_name n) (sm_transitions M))) (sm_nodes M))"

lemma dom_sm_node_map: "dom(nmap\<^bsub>M\<^esub>) = nnames\<^bsub>M\<^esub>"
  using image_iff by (force simp add: sm_node_map_def sm_node_names_def dom_map_of_conv_image_fst)

lemma dom_sm_trans_map: "dom(tmap\<^bsub>M\<^esub>) = nnames\<^bsub>M\<^esub>"
  using image_iff by (force simp add: sm_trans_map_def sm_node_names_def dom_map_of_conv_image_fst)

lemma nnames_finite: "finite(nnames\<^bsub>M\<^esub>)"
  by (force simp add: sm_node_names_def)

abbreviation sm_init_node :: "('s, 'e) StateMachine \<Rightarrow> ('s, 'e) Node" ("ninit\<index>") where
"sm_init_node M \<equiv> the (sm_node_map M (sm_initial M))"

subsection \<open> Well-Formedness \<close>

locale WfStateMachine =
  fixes M :: "('s, 'm) StateMachine" (structure)
  -- \<open> The list of nnames is a set \<close>
  assumes nnames_distinct: "distinct (map n_name (nodes\<^bsub>M\<^esub>))"
  and init_is_state: "init \<in> nnames"
  and init_not_final: "init \<notin> fnames"
  and trans_wf: " \<And> t. t \<in> set(\<^bold>T) \<Longrightarrow> tn_source t \<in> inames \<and> tn_target t \<in> nnames"
begin
  lemma init_is_inter: "init \<in> inames"
    using init_is_state init_not_final by (auto simp add: sm_inters_def sm_inter_names_def sm_node_names_def)

  lemma nmap_init: "nmap init = Some ninit"
    by (metis domIff dom_sm_node_map init_is_state option.exhaust_sel)

  lemma n_name_init: "n_name ninit = init"
  proof (simp add: sm_node_map_def)
    have "map_of (map (\<lambda>n. (n_name n, n)) (sm_nodes M)) init = Some (the (map_of (map (\<lambda>n. (n_name n, n)) (sm_nodes M)) init))"
      by (metis (no_types) nmap_init sm_node_map_def)
    then show "n_name (the (map_of (map (\<lambda>n. (n_name n, n)) (sm_nodes M)) init)) = init"
      using map_of_SomeD by force
  qed

  lemma nmap_name:
    assumes "n \<in> set(sm_nodes M)"
    shows "nmap (n_name n) = Some n"
  proof -
    have "distinct (map fst (map (\<lambda>n. (n_name n, n)) (sm_nodes M)))"
      by (simp add: comp_def nnames_distinct)
    with assms show ?thesis
      by (simp add: sm_node_map_def)
  qed

  lemma ninit_is_node: "ninit \<in> set(sm_nodes M)"
    using init_is_state nmap_name by (auto simp add: sm_node_names_def)

  lemma tmap_node_in_trans: 
    assumes "n \<in> nnames" "ts \<in> ran(tmap)"
    shows "set(ts) \<subseteq> set(\<^bold>T)"
    using assms by (auto simp add: sm_trans_map_def ran_distinct nnames_distinct comp_def)

  lemma node_tran_exists:
    assumes "n \<in> nnames" "t \<in> set(the(tmap n))"
    shows "t \<in> set(\<^bold>T)"
    by (metis (mono_tags, hide_lams) assms(1) assms(2) domIff dom_sm_trans_map in_mono init_is_state option.collapse ranI tmap_node_in_trans)

end

method check_machine uses defs = 
  (unfold_locales, 
   simp_all add: defs sm_node_names_def sm_inter_names_def sm_inters_def, safe, simp_all)

subsection \<open> State Machine Semantics \<close>

abbreviation "trigger_semantics t null_event \<equiv> 
  (case tn_trigger t of Some e \<Rightarrow> if productive e then e else sync null_event | None \<Rightarrow> sync null_event)"

definition tr_semantics :: "('s, 'e) Transition \<Rightarrow> 'e \<Rightarrow> ('s, 'e) RoboAction" ("\<lbrakk>_\<rbrakk>\<^sub>T") where
"tr_semantics t null_event \<equiv> 
  tn_condition t \<oplus>\<^sub>p rc_state \<^bold>& 
  rc_state:[trigger_semantics t null_event ; tn_action t]\<^sub>A\<^sup>+ ; rc_ctrl := \<guillemotleft>tn_target t\<guillemotright>"

definition node_semantics :: 
  "('s, 'e) StateMachine \<Rightarrow> 'e \<Rightarrow> ('s, 'e) Node \<Rightarrow> ('s, 'e) RoboAction" ("_;_ \<turnstile> \<lbrakk>_\<rbrakk>\<^sub>N" [10,0,0] 10) where
  "node_semantics M null_event node  = 
  (rc_state:[n_entry node]\<^sub>A\<^sup>+ ;
   (foldr (op \<box>) (map (\<lambda> t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) (the (tmap\<^bsub>M\<^esub> (n_name node)))) stop) ;
   rc_state:[n_exit node]\<^sub>A\<^sup>+)"

definition sm_semantics :: "('s, 'e) StateMachine \<Rightarrow> 'e \<Rightarrow> ('s, 'e) RoboAction" ("\<lbrakk>_\<rbrakk>\<^sub>M") where
"sm_semantics M null_event = 
    (rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ;
    iteration (map (\<lambda> n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) (sm_inters M)))"

lemmas sm_sem_def = sm_semantics_def node_semantics_def sm_inters_def sm_inter_names_def

lemma tr_semantics_subst_ctrl: "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> (\<lbrakk>a\<rbrakk>\<^sub>T null_event) = \<lbrakk>a\<rbrakk>\<^sub>T null_event"
  by (simp add: tr_semantics_def action_simp usubst unrest frame_asubst)

lemma tr_choice_subst_ctrl:
  "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> foldr op \<box> (map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) ts) stop = foldr op \<box> (map (\<lambda>t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) ts) stop"
  by (induct ts, simp_all add: action_simp usubst tr_semantics_subst_ctrl)

lemma sm_semantics_subst_ctrl:
  "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>k\<guillemotright>] \<dagger> node_semantics M null_event node = node_semantics M null_event node"
  by (simp add: node_semantics_def action_simp frame_asubst tr_choice_subst_ctrl unrest)

subsection \<open> Theorems \<close>

lemma productive_tr_semantics [closure]: "productive (\<lbrakk>t\<rbrakk>\<^sub>T null_event)"
  by (cases "tn_trigger t", auto simp add: tr_semantics_def action_rep_eq closure unrest)

lemma productive_node_semantics:
  "productive (M;null_event \<turnstile> \<lbrakk>node\<rbrakk>\<^sub>N)"
proof -
  have "\<And> ts. productive (foldr (op \<box>) (map (\<lambda> t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) ts) stop)"
    by (rename_tac ts, induct_tac ts, auto simp add: action_rep_eq closure, simp add: closure productive_Productive)
  hence "productive (foldr (op \<box>) (map (\<lambda> t. \<lbrakk>t\<rbrakk>\<^sub>T null_event) (the (tmap\<^bsub>M\<^esub> (n_name node)))) stop)"
    by blast
  thus ?thesis
    by (simp add: action_rep_eq closure node_semantics_def)
qed

lemma Sup_Collect_as_UINF:
  "\<Sqinter> {P x | x. x \<in> A} = (\<Sqinter> x \<in> A \<bullet> P x)"
  apply (simp add: UINF_as_Sup[THEN sym], rel_simp)
  apply (rule cong[of Sup Sup])
   apply (auto)
  done
  

lemma Sup_Collect_2_as_UINF:
  "\<Sqinter> {P x y | x y. (x, y) \<in> A} = (\<Sqinter> (x, y) \<in> A \<bullet> P x y)"
  apply (simp add: UINF_as_Sup[THEN sym], rel_simp)
  apply (rule cong[of Sup Sup])
   apply (auto)
  done

lemma UINF_Collect: "(\<Sqinter> b \<in> {F(x)| x . x \<in> A} \<bullet> b) = (\<Sqinter> x \<in> A \<bullet> F(x))"
  by (simp add: Sup_Collect_as_UINF UINF_as_Sup)

lemma ueq_literlise [lit_simps]: 
  "(\<guillemotleft>x = y\<guillemotright>) = (\<guillemotleft>x\<guillemotright> =\<^sub>u \<guillemotleft>y\<guillemotright>)"
  by (rel_auto)

lemma seq_refine_mono:
  fixes P\<^sub>1 P\<^sub>2 Q\<^sub>1 Q\<^sub>2 :: "('s, 'e) Action"
  assumes "P\<^sub>1 \<sqsubseteq> Q\<^sub>1" "P\<^sub>2 \<sqsubseteq> Q\<^sub>2"
  shows "P\<^sub>1 ; P\<^sub>2 \<sqsubseteq> Q\<^sub>1 ; Q\<^sub>2"
  using assms
  by (simp add: action_rep_eq seqr_mono)

lemma StateMachine_refine_intro:
  fixes 
    S :: "('s, 'e) RoboAction" and
    M :: "('s, 'e) StateMachine"
  assumes 
    "WfStateMachine M"
    "S \<sqsubseteq> (M;null_event \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N)"
    "\<And> n. n \<in> inames\<^bsub>M\<^esub> \<Longrightarrow> S \<sqsubseteq> S ; (M;null_event \<turnstile> \<lbrakk>the(nmap\<^bsub>M\<^esub> n)\<rbrakk>\<^sub>N)"
  shows "S \<sqsubseteq> \<lbrakk>M\<rbrakk>\<^sub>M null_event"
proof -
  interpret wf: WfStateMachine M
    by (simp add: assms)
  have 1: "\<And>n. n \<in> set(sm_inters M) \<Longrightarrow> productive (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
    by (simp add: productive_node_semantics)
  have 2: "S \<sqsubseteq> rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> ; [\<not> (\<Sqinter> (b, P) \<in> (\<lambda>n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) ` set(sm_inters M) \<bullet> b)]\<^sub>A"
  proof -
    have a:"(\<lambda> n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright> :: 's RoboPred, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) ` set(sm_inters M) =
             {(&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)| n . n \<in> set(sm_inters M)}"
      by (auto)
    have b: "(\<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> \<notin>\<^sub>u \<guillemotleft>inames\<^bsub>M\<^esub>\<guillemotright>) = false"
      by (literalise, metis (full_types) false_alt_def true_alt_def utp_pred_laws.compl_top_eq wf.init_is_inter)
    have "(\<Sqinter> (b, P) \<in> (\<lambda>n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright> :: 's RoboPred, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) ` set(sm_inters M) \<bullet> b) =
           (\<Sqinter> (b, P) \<in> {(&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)| n . n \<in> set(sm_inters M)} \<bullet> b)"
      by (simp add: a)
    also have "...  = (\<Sqinter> b \<in> {&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>| n . n \<in> set(sm_inters M)} \<bullet> b)"
      by (rel_auto)      
    also have "... = (&rc_ctrl \<in>\<^sub>u \<guillemotleft>inames\<^bsub>M\<^esub>\<guillemotright>)"
      apply (simp add: UINF_Collect, rel_auto)
      apply (simp add: sm_inter_names_def sm_sem_def(3))
      using sm_inter_names_def apply fastforce
      done
    finally show ?thesis
      by (simp add: action_simp usubst b miracle_top)
  qed
  have 3: "S \<sqsubseteq> rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> ; [\<not> (&rc_ctrl \<in>\<^sub>u \<guillemotleft>inames\<^bsub>M\<^esub>\<guillemotright>)]\<^sub>A" (is "?lhs \<sqsubseteq> ?rhs")
  proof -
    have "?rhs = [\<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> \<notin>\<^sub>u \<guillemotleft>inames\<^bsub>M\<^esub>\<guillemotright>]\<^sub>A ; rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright>"
      by (simp add: action_simp usubst)
    also have "... = [false]\<^sub>A ; rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright>"
      by (literalise, simp add: wf.init_is_inter, unliteralise, simp)
    also have "... = miracle"
      by (simp add: action_simp)
    finally
    show ?thesis by (simp add: miracle_top)
  qed
  have 4:"\<And>n. n \<in> set(sm_inters M) \<Longrightarrow> S \<sqsubseteq> rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
  proof -
    fix n
    assume a:"n \<in> set(sm_inters M)"
    show "S \<sqsubseteq> rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
    proof (cases "n=ninit\<^bsub>M\<^esub>")
      case True
      hence "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright>] \<dagger> (M;null_event \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N) = (M;null_event \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N)"
        by (simp add: sm_semantics_subst_ctrl)
      with True assms(2) show ?thesis
        by (simp add: action_simp usubst wf.n_name_init)
    next
      case False
      with a have "(init\<^bsub>M\<^esub> = n_name n) = False"
      proof -
        have "n \<in> {n. n \<in> set(sm_nodes M) \<and> \<not> n_name n \<in> set(finals\<^bsub>M\<^esub>)}"
          by (metis a set_filter sm_sem_def(3))
        then have "nmap\<^bsub>M\<^esub> (n_name n) = Some n"
          using WfStateMachine.nmap_name wf.WfStateMachine_axioms by blast
        then show ?thesis
          using False by fastforce
      qed
      hence "((\<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> =\<^sub>u \<guillemotleft>n_name n\<guillemotright>) :: 's RoboPred) = false"
        by (rel_auto)
      thus ?thesis
        by (simp add: action_simp usubst miracle_top)
    qed
  qed
  have 5: "\<And>n. n \<in> set(sm_inters M) \<Longrightarrow> S \<sqsubseteq> S ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
  proof -
    fix n
    assume a:"n \<in> set(sm_inters M)"
    have "S \<sqsubseteq> S ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
    proof -
      have f1: "{n. (n::('s, 'e) Node) \<in> set(sm_nodes M) \<and> \<not> n_name n \<in> set(finals\<^bsub>M\<^esub>)} = set(sm_inters M)"
        by (simp add: sm_sem_def(3))
      then have "n_name n \<in> n_name ` {n. (n::('s, 'e) Node) \<in> set(sm_nodes M) \<and> \<not> n_name n \<in> set(finals\<^bsub>M\<^esub>)}"
        using a by force
      then have "n_name n \<in> inames\<^bsub>M\<^esub>"
        by (simp add: sm_inter_names_def sm_sem_def(3))
      then show ?thesis
        using f1 a assms(3) wf.nmap_name by fastforce
    qed
    moreover have "S ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N) \<sqsubseteq> S ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
      by (rule seq_refine_mono, simp_all add: asm_pre_refine)
    ultimately show "S \<sqsubseteq> S ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
      using dual_order.trans by blast
  qed

  show ?thesis
    apply (simp add: sm_semantics_def)
    apply (rule iterate_refine_intro)
    apply (simp_all)
    apply (auto simp add: 1 2 3 4 5)
    done
qed
(*
lemma StateMachine_sinv_refine_intro:
  fixes 
    S :: "('s, 'e) RoboAction" and
    M :: "('s, 'e) StateMachine"
  assumes 
    "WfStateMachine M"
    "sinv\<^sub>A(s) \<sqsubseteq> (M;null_event \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N)"
    "\<And> n. n \<in> inames\<^bsub>M\<^esub> \<Longrightarrow> S \<sqsubseteq> S ; (M;null_event \<turnstile> \<lbrakk>the(nmap\<^bsub>M\<^esub> n)\<rbrakk>\<^sub>N)"
  shows "S \<sqsubseteq> \<lbrakk>M\<rbrakk>\<^sub>M null_event"
*)

(*
lemma "sinv\<^sub>A (&rc_ctrl \<in>\<^sub>u \<guillemotleft>nnames\<^bsub>M\<^esub>\<guillemotright>) \<sqsubseteq> r:[P]\<^sub>A\<^sup>+"
  apply (simp add: action_rep_eq, safe)
   apply (rdes_refine_split)
  apply (rel_simp)

lemma 
  assumes "WfStateMachine M"
  shows "sinv\<^sub>A(&rc_ctrl \<in>\<^sub>u \<guillemotleft>nnames\<^bsub>M\<^esub>\<guillemotright>) \<sqsubseteq> \<lbrakk>M\<rbrakk>\<^sub>M null_event"
proof (rule StateMachine_refine_intro[OF assms])
  show "sinv\<^sub>A(&rc_ctrl \<in>\<^sub>u \<guillemotleft>nnames\<^bsub>M\<^esub>\<guillemotright>) \<sqsubseteq> (M;null_event \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N)"
    apply (simp add: node_semantics_def)
*)

subsection \<open> Divergence Freedom \<close>

locale DivFreeSM = WfStateMachine +
  assumes 
    n_entry_divf: "\<And> n. n \<in> set(nodes) \<Longrightarrow> divf \<sqsubseteq> n_entry n" and
    n_during_divf: "\<And> n. n \<in> set(nodes) \<Longrightarrow> divf \<sqsubseteq> n_exit n" and
    n_exit_divf: "\<And> n. n \<in> set(nodes) \<Longrightarrow> divf \<sqsubseteq> n_exit n" and
    tn_trigger_divf: "\<And> t e. \<lbrakk> t \<in> set(\<^bold>T); tn_trigger t = Some e \<rbrakk> \<Longrightarrow> divf \<sqsubseteq> e" and
    tn_action_divf: "\<And> t. t \<in> set(\<^bold>T) \<Longrightarrow> divf \<sqsubseteq> tn_action t"

lemma DivFreeSM_divf:
  assumes "DivFreeSM M"
  shows "divf \<sqsubseteq> \<lbrakk>M\<rbrakk>\<^sub>M \<epsilon>"
proof (rule StateMachine_refine_intro)
  interpret dvs: DivFreeSM M
    by (simp add: assms)
  show "WfStateMachine M"
    by (simp add: dvs.WfStateMachine_axioms)
  have "\<And> n t. \<lbrakk> n \<in> nnames\<^bsub>M\<^esub>; t \<in> set(the (tmap\<^bsub>M\<^esub> n)) \<rbrakk> \<Longrightarrow> divf \<sqsubseteq> \<lbrakk>t\<rbrakk>\<^sub>T \<epsilon>"  
  proof -
    fix n t
    assume a: "n \<in> nnames\<^bsub>M\<^esub>" "t \<in> set(the (tmap\<^bsub>M\<^esub> n))"
    have "divf \<sqsubseteq> trigger_semantics t \<epsilon>"
    proof (cases "tn_trigger t")
      case None
      then show ?thesis by (simp add: divf_sync)
    next
      case (Some a)
      then show ?thesis
        using a(1) a(2) divf_sync dvs.node_tran_exists dvs.tn_trigger_divf by fastforce
    qed
    thus "divf \<sqsubseteq> \<lbrakk>t\<rbrakk>\<^sub>T \<epsilon>"
      apply (simp add: tr_semantics_def)
      apply (rule divf_guard)
      apply (rule divf_seq_refine)
       apply (rule divf_seq_refine)
        apply (rule divf_frame_ext)
        apply (simp)
       apply (rule divf_frame_ext)
      using a(1) a(2) dvs.node_tran_exists dvs.tn_action_divf apply blast
      apply (simp add: divf_assigns)
      done
  qed
  hence b:"\<And> n. n \<in> inames\<^bsub>M\<^esub> \<Longrightarrow> divf \<sqsubseteq> (M;\<epsilon> \<turnstile> \<lbrakk>the (nmap\<^bsub>M\<^esub> n)\<rbrakk>\<^sub>N)"
    apply (simp add: node_semantics_def)
    apply (rule divf_seq_refine)
    apply (rule divf_frame_ext)
    apply (smt dvs.n_entry_divf dvs.nmap_name filter_is_subset imageE option.sel sm_inter_names_def sm_inters_def subset_eq)
    apply (rule divf_seq_refine)
     apply (rule divf_extchoice_fold_refine)
    apply (auto)
    apply (smt dvs.nmap_name filter_is_subset image_iff option.sel sm_inter_names_def sm_inters_def sm_node_names_def subset_code(1))
    apply (rule divf_frame_ext)
    apply (smt dvs.n_exit_divf dvs.nmap_name filter_is_subset imageE option.sel sm_inter_names_def sm_inters_def subset_eq)
    done
  show "divf \<sqsubseteq> (M;\<epsilon> \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N)"
    by (simp add: b dvs.init_is_inter)
  show "\<And>n. n \<in> inames\<^bsub>M\<^esub> \<Longrightarrow> divf \<sqsubseteq> divf ; (M;\<epsilon> \<turnstile> \<lbrakk>the (nmap\<^bsub>M\<^esub> n)\<rbrakk>\<^sub>N)"
    by (simp add: b divf_seq_refine)
qed

subsection \<open> Transition and State Parsers \<close>

syntax
  "_transition" :: "id \<Rightarrow> id \<Rightarrow> raction \<Rightarrow> logic \<Rightarrow> raction \<Rightarrow> logic"
  ("from _ to _ trigger _ condition _ action _" [0,0,0,0,10] 10)

  "_transition_action" :: "id \<Rightarrow> id \<Rightarrow> raction \<Rightarrow> logic"
  ("from _ to _ action _" [0,0,10] 10)

  "_transition_condition" :: "id \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic"
  ("from _ to _ condition _" [0,0,10] 10)

  "_transition_condition_action" :: "id \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> raction \<Rightarrow> logic"
  ("from _ to _ condition _ action _" [0,0,0,10] 10)

  "_transition_trigger" :: "id \<Rightarrow> id \<Rightarrow> raction \<Rightarrow> logic"
  ("from _ to _ trigger _" [0,0,10] 10)

  "_state" :: "raction \<Rightarrow> raction \<Rightarrow> raction \<Rightarrow> logic"
  ("entry _ during _ exit _" [0,0,10] 10)

  "_state_entry" :: "raction \<Rightarrow> logic"
  ("entry _" [10] 10)

translations
  "_transition s1 s2 e b a" =>
  "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST Some e) b a"

  "_transition_action s1 s2 a" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) true a"

  "_transition_condition s1 s2 b" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) b (CONST Actions.skips)"

  "_transition_condition_action s1 s2 b a" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) b a"

  "_transition_trigger s1 s2 t" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST Some t) true (CONST Actions.skips)"

  "_state e d x" => "CONST Node.make (CONST undefined) e d x"

  "_state_entry e" => "CONST Node.make (CONST undefined) e skip skip"

term "from s1 to s2 trigger y := 1; x?(y) ; z!(1) condition b action a"
term "from s1 to s2 action a"
term "from s1 to s2 trigger e"
term "entry e during d exit x"
term "entry e"

term "entry skip during skip exit skip"

end