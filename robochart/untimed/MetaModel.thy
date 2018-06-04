section \<open> RoboChart Meta-Model \<close>

theory MetaModel
  imports Actions
begin

subsection \<open> State Machine Syntax \<close>

text \<open> All state machine statespace types extend the following type which provides a state control variable \<close>

alphabet robochart_ctrl =
  rc_ctrl :: string 

type_synonym ('s, 'e) RoboAction = "('s robochart_ctrl_scheme, 'e) Action"
type_synonym 's RoboPred = "'s robochart_ctrl_scheme upred"

translations
  (type) "('s, 'e) RoboAction" <= (type) "('s robochart_ctrl_scheme, 'e) Action"
  (type) "'s RoboPred" <= (type) "'s robochart_ctrl_scheme upred"

abbreviation "rc_state \<equiv> robochart_ctrl_child_lens"

notation rc_state ("\<^bold>r")

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

(* type_synonym ('s, 'e) Node = "string \<times> ('s, 'e) NodeBody" *)

record ('s, 'e) StateMachine =
  sm_initial     :: "string" ("init\<index>")
  sm_finals      :: "string list" ("finals\<index>")
  sm_nodes       :: "('s, 'e) Node list"
  sm_transitions :: "('s, 'e) Transition list" ("\<^bold>T\<index>")

declare StateMachine.defs [simp]

abbreviation sm_node_names :: "('s, 'e) StateMachine \<Rightarrow> string list" ("nodes\<index>") where
"sm_node_names sm \<equiv> map n_name (sm_nodes sm)"

definition sm_inters :: "('s, 'e) StateMachine \<Rightarrow> ('s, 'e) Node list" where
"sm_inters sm = filter (\<lambda> n. n_name n \<notin> set(sm_finals sm)) (sm_nodes sm)"

definition sm_inter_names ("inters\<index>") where
"sm_inter_names sm \<equiv> map n_name (sm_inters sm)"

definition sm_node_map :: "('s, 'e) StateMachine \<Rightarrow> (string \<rightharpoonup> ('s, 'e) Node)" ("nmap\<index>") where
"sm_node_map M = map_of (map (\<lambda> n. (n_name n, n)) (sm_nodes M))"

definition sm_trans_map :: "('s, 'e) StateMachine \<Rightarrow> (string \<rightharpoonup> ('s, 'e) Transition list)" ("tmap\<index>") where
"sm_trans_map M = map_of (map (\<lambda> n. (n_name n, filter (\<lambda> t. tn_source t = n_name n) (sm_transitions M))) (sm_nodes M))"

lemma dom_sm_node_map: "dom(nmap\<^bsub>M\<^esub>) = set(nodes\<^bsub>M\<^esub>)"
  using image_iff by (force simp add: sm_node_map_def dom_map_of_conv_image_fst)

abbreviation sm_init_node :: "('s, 'e) StateMachine \<Rightarrow> ('s, 'e) Node" ("ninit\<index>") where
"sm_init_node M \<equiv> the (sm_node_map M (sm_initial M))"

subsection \<open> Well-Formedness \<close>

locale WfStateMachine =
  fixes M :: "('s, 'm) StateMachine" (structure)
  -- \<open> The list of nodes is a set \<close>
  assumes nodes_distinct: "distinct nodes"
  and init_is_state: "init \<in> set(nodes)"
  and init_not_final: "init \<notin> set(finals)"
  and trans_wf: " \<And> t. t \<in> set(\<^bold>T) \<Longrightarrow> tn_source t \<in> set(inters) \<and> tn_target t \<in> set(nodes)"
begin
  lemma init_is_inter: "init \<in> set(inters)"
    using init_is_state init_not_final by (auto simp add: sm_inters_def sm_inter_names_def)

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
      by (simp add: comp_def nodes_distinct)
    with assms show ?thesis
      by (simp add: sm_node_map_def)
  qed

  lemma ninit_is_node: "ninit \<in> set(sm_nodes M)"
    using init_is_state nmap_name by auto

end

method check_machine uses defs = 
  (unfold_locales, 
   simp_all add: defs sm_inter_names_def sm_inters_def, safe, simp_all)

subsection \<open> State Machine Semantics \<close>

abbreviation "trigger_semantics t null_event \<equiv> 
  (case tn_trigger t of Some e \<Rightarrow> if productive e then e else sync null_event | None \<Rightarrow> sync null_event)"

definition tr_semantics :: "('s, 'e) Transition \<Rightarrow> 'e \<Rightarrow> ('s, 'e) RoboAction" ("\<lbrakk>_\<rbrakk>\<^sub>T") where
"tr_semantics t null_event \<equiv> 
  tn_condition t \<oplus>\<^sub>p rc_state \<^bold>& 
  rc_state:[trigger_semantics t null_event ; tn_action t]\<^sub>A\<^sup>+ ; rc_ctrl := \<guillemotleft>tn_target t\<guillemotright>"

text \<open> The following function extracts a tree representation of nodes and the transitions for each state
  in the state machine. We exclude final states as reaching these should lead to termination even though
  there is no outgoing edges. \<close>

definition sm_tree :: "('s, 'e) StateMachine \<Rightarrow> (('s, 'e) Node \<times> ('s, 'e) Transition list) list" where
"sm_tree sm \<equiv> map (\<lambda> s. (s, filter (\<lambda> t. tn_source t = n_name s) (sm_transitions sm))) (sm_inters sm)"

definition node_semantics :: 
  "('s, 'e) StateMachine \<Rightarrow> 'e \<Rightarrow> ('s, 'e) Node \<Rightarrow> ('s, 'e) RoboAction" ("_;_ \<turnstile> \<lbrakk>_\<rbrakk>\<^sub>N" [10,0,0] 10) where
  "node_semantics M null_event node  = 
  ([&rc_ctrl =\<^sub>u \<guillemotleft>n_name node\<guillemotright>]\<^sub>A ;
   rc_state:[n_entry node]\<^sub>A\<^sup>+ ;
   (foldr (\<lambda>t P. \<lbrakk>t\<rbrakk>\<^sub>T null_event \<box> P) (the (tmap\<^bsub>M\<^esub> (n_name node))) stop) ;
   rc_state:[n_exit node]\<^sub>A\<^sup>+)"

definition sm_semantics :: "('s, 'e) StateMachine \<Rightarrow> 'e \<Rightarrow> ('s, 'e) RoboAction" ("\<lbrakk>_\<rbrakk>\<^sub>M") where
"sm_semantics M null_event = 
    (rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ;
    iteration (map (\<lambda> n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) (sm_nodes M)))"

lemmas sm_sem_def = sm_semantics_def node_semantics_def sm_inters_def sm_inter_names_def sm_tree_def Transition.defs StateMachine.defs Node.defs

subsection \<open> Theorems \<close>

lemma productive_tr_semantics [closure]: "productive (\<lbrakk>t\<rbrakk>\<^sub>T null_event)"
  by (cases "tn_trigger t", auto simp add: tr_semantics_def action_rep_eq closure unrest)

lemma productive_node_semantics:
  "productive (M;null_event \<turnstile> \<lbrakk>node\<rbrakk>\<^sub>N)"
proof -
  have "\<And> ts. productive (foldr (\<lambda>t P. \<lbrakk>t\<rbrakk>\<^sub>T null_event \<box> P) ts stop)"
    by (rename_tac ts, induct_tac ts, auto simp add: action_rep_eq closure, simp add: closure productive_Productive)
  hence "productive (foldr (\<lambda>t. op \<box> (\<lbrakk>t\<rbrakk>\<^sub>T null_event)) (the (tmap\<^bsub>M\<^esub> (n_name node))) stop)"
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
(*
lemma guard_form_lemma:
  "(\<Sqinter> (b, P) \<in> state_semantics null_event ` set(sm_tree M) \<bullet> b) = (&rc_ctrl \<in>\<^sub>u \<guillemotleft>set(sm_inter_names M)\<guillemotright>)"
  (is "?lhs = ?rhs")
proof -
  have 1:"fst ` state_semantics null_event ` set(sm_tree M) = {&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright> | n. n \<in> set(sm_inters M)}"
    apply (simp add: sm_tree_def)
    apply (induct "sm_transitions M")
     apply (auto simp add: state_semantics_def prod.case_eq_if)
    apply (auto simp add: image_def)
    done
  have 2:"?lhs = (\<Sqinter> (fst ` state_semantics null_event ` set(sm_tree M)))"
    by (pred_auto, metis fst_conv, metis imageI prod.exhaust_sel)
  also have "... = (\<Sqinter> n \<in> set(sm_inters M) \<bullet> (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>))"
    by (simp only: Sup_Collect_as_UINF 1)
  also have "... = (&rc_ctrl \<in>\<^sub>u \<guillemotleft>set(sm_inter_names M)\<guillemotright>)"
    by (simp add: sm_inter_names_def, rel_auto)
  finally show ?thesis .
qed
*)

lemma asm_assign:
  "vwb_lens x \<Longrightarrow> [&x =\<^sub>u k]\<^sub>A ; x := k =  [&x =\<^sub>u k]\<^sub>A"
  apply (simp add: action_rep_eq)
  apply (rdes_eq)
  using vwb_lens.put_eq apply force+
  done

lemma asubst_twice [action_simp]: 
  fixes P :: "('s, 'e) Action"
  shows "\<sigma> \<dagger> \<rho> \<dagger> P = (\<rho> \<circ> \<sigma>) \<dagger> P"
  by (simp add: action_rep_eq usubst)

lemma asubst_seq [action_simp]:
  fixes P Q :: "('s, 'e) Action"
  shows "\<sigma> \<dagger> (P ; Q) = ((\<sigma> \<dagger> P) ; Q)"
  by (simp add: action_rep_eq usubst)

lemma UINF_Collect: "(\<Sqinter> b \<in> {F(x)| x . x \<in> A} \<bullet> b) = (\<Sqinter> x \<in> A \<bullet> F(x))"
  by (simp add: Sup_Collect_as_UINF UINF_as_Sup)



lemma ueq_literlise [lit_simps]: 
  "(\<guillemotleft>x = y\<guillemotright>) = (\<guillemotleft>x\<guillemotright> =\<^sub>u \<guillemotleft>y\<guillemotright>)"
  by (rel_auto)

declare [[show_sorts]]

lemma StateMachine_refine_intro:
  fixes 
    S :: "('s, 'e) RoboAction" and
    M :: "('s, 'e) StateMachine"
  assumes 
    "WfStateMachine M"
    "S \<sqsubseteq> (M;null_event \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N)"
    "\<And> n. n \<in> set(sm_nodes M) \<Longrightarrow> S \<sqsubseteq> S ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
  shows "S \<sqsubseteq> \<lbrakk>M\<rbrakk>\<^sub>M null_event"
proof -
  interpret wf: WfStateMachine M
    by (simp add: assms)
  have 1: "\<And>n. n \<in> set(sm_nodes M) \<Longrightarrow> productive (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
    by (simp add: productive_node_semantics)
  have 2: "S \<sqsubseteq> rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> ; [\<not> (\<Sqinter> (b, P) \<in> (\<lambda>n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) ` set(sm_nodes M) \<bullet> b)]\<^sub>A"
  proof -
    have a:"(\<lambda> n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright> :: 's RoboPred, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) ` set(sm_nodes M) =
             {(&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)| n . n \<in> set(sm_nodes M)}"
      by (auto)
    have b: "(\<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> \<notin>\<^sub>u \<guillemotleft>n_name ` set(sm_nodes M)\<guillemotright>) = false"
      by (literalise, metis (full_types) false_alt_def image_set true_alt_def utp_pred_laws.compl_top_eq wf.init_is_state)
    have "(\<Sqinter> (b, P) \<in> (\<lambda>n. (&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright> :: 's RoboPred, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)) ` set(sm_nodes M) \<bullet> b) =
           (\<Sqinter> (b, P) \<in> {(&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>, M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)| n . n \<in> set(sm_nodes M)} \<bullet> b)"
      by (simp add: a)
    also have "...  = (\<Sqinter> b \<in> {&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>| n . n \<in> set(sm_nodes M)} \<bullet> b)"
      by (rel_auto)      
    also have "... = (&rc_ctrl \<in>\<^sub>u \<guillemotleft>set(sm_node_names M)\<guillemotright>)"
      by (simp add: UINF_Collect, rel_auto)
    finally show ?thesis
      by (simp add: action_simp usubst b miracle_top)
  qed
  have 3: "S \<sqsubseteq> rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ; [\<not> (&rc_ctrl \<in>\<^sub>u \<guillemotleft>set(sm_inter_names M)\<guillemotright>)]\<^sub>A" (is "?lhs \<sqsubseteq> ?rhs")
  proof -
    have "?rhs = [\<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> \<notin>\<^sub>u \<guillemotleft>set(inters\<^bsub>M\<^esub>)\<guillemotright>]\<^sub>A ; rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright>"
      by (simp add: action_simp usubst)
    also have "... = [false]\<^sub>A ; rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright>"
      by (literalise, simp add: wf.init_is_inter, unliteralise, simp)
    also have "... = miracle"
      by (simp add: action_simp)
    finally
    show ?thesis by (simp add: miracle_top)
  qed
  have 4:"\<And>n. n \<in> set(sm_nodes M) \<Longrightarrow> S \<sqsubseteq> rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
  proof -
    fix n
    assume a:"n \<in> set(sm_nodes M)"
    show "S \<sqsubseteq> rc_ctrl := \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
    proof (cases "n=ninit\<^bsub>M\<^esub>")
      case True
      hence "[&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright>] \<dagger> (M;null_event \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N) = (M;null_event \<turnstile> \<lbrakk>ninit\<^bsub>M\<^esub>\<rbrakk>\<^sub>N)"
        apply (simp add: node_semantics_def action_simp usubst)
      with True assms(2) show ?thesis
        by (simp add: action_simp usubst wf.n_name_init)
    next
      case False
      with a have "(init\<^bsub>M\<^esub> = n_name n) = False"
        using wf.nmap_name by auto
      hence "((\<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> =\<^sub>u \<guillemotleft>n_name n\<guillemotright>) :: 's RoboPred) = false"
        by (rel_auto)
      thus ?thesis
        by (simp add: action_simp usubst miracle_top)
    qed
  qed
  have 5: "\<And>n. n \<in> set(sm_nodes M) \<Longrightarrow> S \<sqsubseteq> S ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
  proof -
    fix n
    assume a:"n \<in> set(sm_nodes M)"
    have "S \<sqsubseteq> S ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
      by (simp add: a assms(3))
    hence "S \<sqsubseteq> S ; [&rc_ctrl =\<^sub>u \<guillemotleft>n_name n\<guillemotright>]\<^sub>A ; (M;null_event \<turnstile> \<lbrakk>n\<rbrakk>\<^sub>N)"
      apply (simp add: node_semantics_def)


(*
  moreover have "\<And> n b ts. ((n, b), ts) \<in> set(sm_tree M) \<Longrightarrow> S \<sqsubseteq> rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ; [&rc_ctrl =\<^sub>u \<guillemotleft>n\<guillemotright>]\<^sub>A ; state_action null_event b ts"
  proof -
    fix n b ts
    assume "((n, b), ts) \<in> set(sm_tree M)"
    have "rc_ctrl := \<guillemotleft>sm_initial M\<guillemotright> ; [&rc_ctrl =\<^sub>u \<guillemotleft>n\<guillemotright>]\<^sub>A ; state_action null_event b ts 
          = [\<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright> =\<^sub>u \<guillemotleft>n\<guillemotright>]\<^sub>A ; ([&rc_ctrl \<mapsto>\<^sub>s \<guillemotleft>init\<^bsub>M\<^esub>\<guillemotright>] \<dagger> (state_action null_event b ts))"
      by (simp add: action_simp usubst)
*)  
  show ?thesis
    apply (simp add: sm_semantics_def)
    apply (rule iterate_refine_intro)
    apply (auto simp add: 1 2 3 4)
    apply (simp add: guard_form_lemma 2)
   apply (auto simp add: state_semantics_def assms)
    done
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

translations
  "_transition s1 s2 e b a" =>
  "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST Some e) b a"

  "_transition_action s1 s2 a" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) true a"

  "_transition_condition s1 s2 b" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) b (CONST Actions.skips)"

  "_transition_condition_action s1 s2 b a" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) b a"

  "_transition_trigger s1 s2 t" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST Some t) true (CONST Actions.skips)"

  "_state e d x" =>
  "CONST Node.make (CONST undefined) e d x"

term "from s1 to s2 trigger y := 1; x?(y) ; z!(1) condition b action a"
term "from s1 to s2 action a"
term "from s1 to s2 trigger e"
term "entry e during d exit x"

term "entry skip during skip exit skip"

end