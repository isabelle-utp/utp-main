section \<open> RoboChart Meta-Model \<close>

theory MetaModel
  imports "UTP-Circus.utp_circus"
begin

subsection \<open> Action Syntax and Semantics\<close>

nonterminal raction

syntax
  "_skip_raction"      :: "raction" ("skip")
  "_seq_raction"       :: "raction \<Rightarrow> raction \<Rightarrow> raction" (infixr ";" 71)
  "_if_raction"        :: "logic \<Rightarrow> raction \<Rightarrow> raction \<Rightarrow> raction" ("if _ then _ else _ end")
  "_assign_raction"    :: "id \<Rightarrow> logic \<Rightarrow> raction" (infixr ":=" 72)
  "_basic_ev_raction"  :: "id \<Rightarrow> raction" ("_")
  "_rcv_ev_raction"    :: "id \<Rightarrow> id \<Rightarrow> raction" ("_?'(_')" [85,86])
  "_send_ev_raction"   :: "id \<Rightarrow> logic \<Rightarrow> raction" ("_!'(_')" [85,86]) 

translations
  "_skip_raction"          => "CONST Skip"
  "_seq_raction P Q"       => "P ;; Q"
  "_if_raction b P Q"      => "P \<triangleleft> b \<triangleright>\<^sub>R Q"
  "_assign_raction x v"    => "x :=\<^sub>C v"
  "_basic_ev_raction e"    => "e \<^bold>\<rightarrow> CONST Skip"
  "_rcv_ev_raction c x"    => "CONST InputVarCSP c x (\<lambda> x. true)"
  "_send_ev_raction c v"   => "CONST OutputCSP c v (CONST Skip)"

subsection \<open> State Machine Syntax \<close>

text \<open> All state machine statespace types extend the following type which provides a state control variable \<close>

alphabet robochart_ctrl =
  rc_ctrl :: string 

abbreviation "rc_state \<equiv> robochart_ctrl_child_lens"

record ('s, 'e) Transition = 
  tn_source    :: string
  tn_target    :: string
  tn_trigger   :: "('s, 'e) action option"
  tn_condition :: "'s upred"
  tn_action    :: "('s, 'e) action"

record ('s, 'e) NodeBody =
  n_entry  :: "('s, 'e) action"
  n_during :: "('s, 'e) action"
  n_exit   :: "('s, 'e) action"

type_synonym ('s, 'e) Node = "string \<times> ('s, 'e) NodeBody"

record ('s, 'e) StateMachine =
  sm_nodes       :: "('s, 'e) Node list"
  sm_transitions :: "('s, 'e) Transition list"

abbreviation "sm_node_names sm \<equiv> map fst (sm_nodes sm)"

subsection \<open> State Machine Semantics \<close>

definition tr_semantics :: "('s, 'e) Transition \<Rightarrow> 'e \<Rightarrow> ('s robochart_ctrl_scheme, 'e) action" where
"tr_semantics t null_event = 
  tn_condition t \<oplus>\<^sub>p rc_state &\<^sub>u 
  rc_state:[(case tn_trigger t of Some e \<Rightarrow> e | None \<Rightarrow> null_event \<^bold>\<rightarrow> Skip) ;; tn_action t]\<^sub>R\<^sup>+ ;; rc_ctrl :=\<^sub>C \<guillemotleft>tn_target t\<guillemotright>"

definition sm_semantics :: "('s, 'e) StateMachine \<Rightarrow> 'e \<Rightarrow> ('s robochart_ctrl_scheme, 'e) action" where
"sm_semantics sm null_event = 
  (do\<^sub>R i\<in>{0..<length(sm_nodes sm)} 
       \<bullet> &rc_ctrl =\<^sub>u \<guillemotleft>sm_node_names sm ! i\<guillemotright> 
       \<rightarrow> rc_state:[n_entry (snd (sm_nodes sm ! i))]\<^sub>R\<^sup>+ ;;
          (let ts = filter (\<lambda> t. tn_source t = fst(sm_nodes sm ! i)) (sm_transitions sm) in
           \<box> j\<in>{0..<length(ts)} \<bullet> tr_semantics (ts ! j) null_event) ;;
          rc_state:[n_exit (snd (sm_nodes sm ! i))]\<^sub>R\<^sup>+
   od)"

subsection \<open> Transition and State Parsers \<close>

syntax
  "_transition" :: "id \<Rightarrow> id \<Rightarrow> raction \<Rightarrow> logic \<Rightarrow> raction \<Rightarrow> logic"
  ("from _ to _ trigger _ condition _ action _")

  "_transition_action" :: "id \<Rightarrow> id \<Rightarrow> raction \<Rightarrow> logic"
  ("from _ to _ action _")

  "_transition_condition" :: "id \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic"
  ("from _ to _ condition _")

  "_transition_condition_action" :: "id \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> raction \<Rightarrow> logic"
  ("from _ to _ condition _ action _")

  "_transition_trigger" :: "id \<Rightarrow> id \<Rightarrow> raction \<Rightarrow> logic"
  ("from _ to _ trigger _")

  "_state" :: "raction \<Rightarrow> raction \<Rightarrow> raction \<Rightarrow> logic"
  ("entry _ during _ exit _")

translations
  "_transition s1 s2 e b a" =>
  "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST Some e) b a"

  "_transition_action s1 s2 a" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) true a"

  "_transition_condition s1 s2 b" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) b (CONST Skip)"

  "_transition_condition_action s1 s2 b a" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST None) b a"

  "_transition_trigger s1 s2 t" => "CONST Transition.make IDSTR(s1) IDSTR(s2) (CONST Some t) true (CONST Skip)"

  "_state e d x" =>
  "CONST NodeBody.make e d x"

term "from s1 to s2 trigger y := 1; x?(y) ; z!(1) condition b action a"
term "from s1 to s2 action a"
term "from s1 to s2 trigger e"
term "entry e during d exit x"

term "entry skip during skip exit skip"

end