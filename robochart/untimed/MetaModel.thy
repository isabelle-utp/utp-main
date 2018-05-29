section \<open> RoboChart Meta-Model \<close>

theory MetaModel
  imports Actions
begin


subsection \<open> State Machine Syntax \<close>

text \<open> All state machine statespace types extend the following type which provides a state control variable \<close>

alphabet robochart_ctrl =
  rc_ctrl :: string 

abbreviation "rc_state \<equiv> robochart_ctrl_child_lens"

notation rc_state ("\<^bold>r")

record ('s, 'e) Transition = 
  tn_source    :: string
  tn_target    :: string
  tn_trigger   :: "('s, 'e) Action option"
  tn_condition :: "'s upred"
  tn_action    :: "('s, 'e) Action"

record ('s, 'e) NodeBody =
  n_entry  :: "('s, 'e) Action"
  n_during :: "('s, 'e) Action"
  n_exit   :: "('s, 'e) Action"

type_synonym ('s, 'e) Node = "string \<times> ('s, 'e) NodeBody"

record ('s, 'e) StateMachine =
  sm_initial     :: "string"
  sm_finals      :: "string list"
  sm_nodes       :: "('s, 'e) Node list"
  sm_transitions :: "('s, 'e) Transition list"

abbreviation "sm_node_names sm \<equiv> map fst (sm_nodes sm)"

definition "sm_inters sm \<equiv> filter (\<lambda> (n,s). n \<notin> set(sm_finals sm)) (sm_nodes sm)"

definition "sm_inter_names sm \<equiv> map fst (sm_inters sm)"

subsection \<open> State Machine Semantics \<close>

abbreviation "trigger_semantics t null_event \<equiv> 
  (case tn_trigger t of Some e \<Rightarrow> if productive e then e else sync null_event | None \<Rightarrow> sync null_event)"

definition tr_semantics :: "('s, 'e) Transition \<Rightarrow> 'e \<Rightarrow> ('s robochart_ctrl_scheme, 'e) Action" ("\<lbrakk>_\<rbrakk>\<^sub>T") where
"tr_semantics t null_event \<equiv> 
  tn_condition t \<oplus>\<^sub>p rc_state \<^bold>& 
  rc_state:[trigger_semantics t null_event ; tn_action t]\<^sub>A\<^sup>+ ; rc_ctrl := \<guillemotleft>tn_target t\<guillemotright>"

text \<open> The following function extracts a tree representation of nodes and the transitions for each state
  in the state machine. We exclude final states as reaching these should lead to termination even though
  there is no outgoing edges. \<close>

definition sm_tree :: "('s, 'e) StateMachine \<Rightarrow> (('s, 'e) Node \<times> ('s, 'e) Transition list) list" where
"sm_tree sm \<equiv> map (\<lambda> s. (s, filter (\<lambda> t. tn_source t = fst s) (sm_transitions sm))) (sm_inters sm)"

definition "state_action null_event b ts \<equiv>
        rc_state:[n_entry b]\<^sub>A\<^sup>+ ;
        (foldr (\<lambda>t P. \<lbrakk>t\<rbrakk>\<^sub>T null_event \<box> P) ts stop) ;
        rc_state:[n_exit b]\<^sub>A\<^sup>+"

definition state_semantics :: "'e \<Rightarrow> ('s, 'e) Node \<times> ('s, 'e) Transition list \<Rightarrow> 'a robochart_ctrl_scheme upred \<times> ('s robochart_ctrl_scheme, 'e) Action" where
  "state_semantics null_event
    = (\<lambda> ((n, b), ts). 
       (&rc_ctrl =\<^sub>u \<guillemotleft>n\<guillemotright>,
        state_action null_event b ts
       )
      )"

definition sm_semantics :: "('s, 'e) StateMachine \<Rightarrow> 'e \<Rightarrow> 'e Process" ("\<lbrakk>_\<rbrakk>\<^sub>M") where
"sm_semantics sm null_event = 
  state_decl (
    rc_ctrl := \<guillemotleft>sm_initial sm\<guillemotright> ;
    iteration (map (state_semantics null_event) (sm_tree sm)))"

lemmas sm_sem_def = sm_semantics_def state_semantics_def state_action_def sm_inters_def sm_inter_names_def sm_tree_def Transition.defs StateMachine.defs NodeBody.defs

subsection \<open> Theorems \<close>

lemma productive_tr_semantics [closure]: "productive (\<lbrakk>t\<rbrakk>\<^sub>T null_event)"
  by (cases "tn_trigger t", auto simp add: tr_semantics_def action_rep_eq closure unrest)

lemma productive_state_semantics:
  "productive (state_action null_event s ts)"
proof -
  have "productive (foldr (\<lambda>t. op \<box> (\<lbrakk>t\<rbrakk>\<^sub>T null_event)) ts stop)"
    by (induct ts, auto simp add: action_rep_eq, simp add: closure productive_Productive)
  thus ?thesis
    by (simp add: action_rep_eq state_semantics_def state_action_def)
qed

lemma Sup_Collect_2_as_UINF:
  "\<Sqinter> {P x y | x y. (x, y) \<in> A} = (\<Sqinter> (x, y) \<in> A \<bullet> P x y)"
  apply (simp add: UINF_as_Sup[THEN sym], rel_simp)
  apply (rule cong[of Sup Sup])
   apply (auto)
  done
  
lemma guard_form_lemma:
  "(\<Sqinter> (b, P) \<in> state_semantics null_event ` set(sm_tree M) \<bullet> b) = (&rc_ctrl \<in>\<^sub>u \<guillemotleft>set(sm_inter_names M)\<guillemotright>)"
  (is "?lhs = ?rhs")
proof -
  have 1:"fst ` state_semantics null_event ` set(sm_tree M) = {&rc_ctrl =\<^sub>u \<guillemotleft>n\<guillemotright> | n s. (n, s) \<in> set(sm_inters M)}"
    apply (simp add: sm_tree_def)
    apply (induct "sm_transitions M")
     apply (auto simp add: state_semantics_def prod.case_eq_if)
    apply (auto simp add: image_def)
    done
  have 2:"?lhs = (\<Sqinter> (fst ` state_semantics null_event ` set(sm_tree M)))"
    by (pred_auto, metis fst_conv, metis imageI prod.exhaust_sel)
  also have "... = (\<Sqinter> (n, s) \<in> set(sm_inters M) \<bullet> (&rc_ctrl =\<^sub>u \<guillemotleft>n\<guillemotright>))"
    by (simp only: 1 Sup_Collect_2_as_UINF)
  also have "... = (&rc_ctrl \<in>\<^sub>u \<guillemotleft>set(sm_inter_names M)\<guillemotright>)"
    by (simp add: sm_inter_names_def, rel_auto, force)
  finally show ?thesis .
qed

lemma StateMachine_dlf_intro:
  fixes M :: "('s, 'e) StateMachine"
  assumes 
    "(dlf :: ('s robochart_ctrl_scheme, 'e) Action) \<sqsubseteq> rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ; [\<not> (&rc_ctrl \<in>\<^sub>u \<guillemotleft>set(sm_inter_names M)\<guillemotright>)]\<^sub>A"
    "\<And> n b ts. ((n, b), ts) \<in> set(sm_tree M) \<Longrightarrow> dlf \<sqsubseteq> dlf ; [&rc_ctrl =\<^sub>u \<guillemotleft>n\<guillemotright>]\<^sub>A ; state_action null_event b ts"
    "\<And> n b ts. ((n, b), ts) \<in> set(sm_tree M) \<Longrightarrow> dlf \<sqsubseteq> rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ; [&rc_ctrl =\<^sub>u \<guillemotleft>n\<guillemotright>]\<^sub>A ; state_action null_event b ts"
  shows "dlf \<sqsubseteq> \<lbrakk>M\<rbrakk>\<^sub>M null_event"
  apply (simp add: sm_semantics_def)
  apply (rule dlf_state_decl)
  apply (rule iterate_refine_intro)
     apply (auto simp add: prod.case_eq_if comp_def image_Collect) 
  apply (simp add: state_semantics_def productive_state_semantics)
    apply (simp add: guard_form_lemma assms)
   apply (auto simp add: state_semantics_def assms)
  done

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

translations
  "_transition s1 s2 e b a" =>
  "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST Some e) b a"

  "_transition_action s1 s2 a" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) true a"

  "_transition_condition s1 s2 b" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) b (CONST Actions.skips)"

  "_transition_condition_action s1 s2 b a" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) b a"

  "_transition_trigger s1 s2 t" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST Some t) true (CONST Actions.skips)"

  "_state e d x" =>
  "CONST NodeBody.make e d x"

term "from s1 to s2 trigger y := 1; x?(y) ; z!(1) condition b action a"
term "from s1 to s2 action a"
term "from s1 to s2 trigger e"
term "entry e during d exit x"

term "entry skip during skip exit skip"

end