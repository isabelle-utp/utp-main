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
  sm_nodes       :: "('s, 'e) Node list"
  sm_transitions :: "('s, 'e) Transition list"

abbreviation "sm_node_names sm \<equiv> map fst (sm_nodes sm)"

subsection \<open> State Machine Semantics \<close>

definition tr_semantics :: "('s, 'e) Transition \<Rightarrow> 'e \<Rightarrow> ('s robochart_ctrl_scheme, 'e) Action" ("\<lbrakk>_\<rbrakk>\<^sub>T") where
"tr_semantics t null_event \<equiv> 
  tn_condition t \<oplus>\<^sub>p rc_state \<^bold>& 
  rc_state:[(case tn_trigger t of Some e \<Rightarrow> e | None \<Rightarrow> sync null_event) ; tn_action t]\<^sub>A\<^sup>+ ; rc_ctrl := \<guillemotleft>tn_target t\<guillemotright>"

abbreviation sm_tree :: "('s, 'e) StateMachine \<Rightarrow> (('s, 'e) Node \<times> ('s, 'e) Transition list) list" where
"sm_tree sm \<equiv> map (\<lambda> s. (s, filter (\<lambda> t. tn_source t = fst s) (sm_transitions sm))) (sm_nodes sm)"

definition sm_semantics :: "('s, 'e) StateMachine \<Rightarrow> 'e \<Rightarrow> ('s robochart_ctrl_scheme, 'e) Action" ("\<lbrakk>_\<rbrakk>\<^sub>M") where
"sm_semantics sm null_event = 
    rc_ctrl := \<guillemotleft>sm_initial sm\<guillemotright> ;
    iteration 
       (map (\<lambda> ((n, b), ts). 
              ( &rc_ctrl =\<^sub>u \<guillemotleft>n\<guillemotright>
              , rc_state:[n_entry b]\<^sub>A\<^sup>+ ;
                (foldr (\<lambda>t P. \<lbrakk>t\<rbrakk>\<^sub>T null_event \<box> P) ts stop) ;
                rc_state:[n_exit b]\<^sub>A\<^sup>+)) (sm_tree sm))"

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