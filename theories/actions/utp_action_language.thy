section \<open> Action Language \<close>

theory utp_action_language
  imports "UTP.utp"
begin

subsection \<open> Action Syntax \<close>

text \<open> The concept of an ``action'' is ubiquitous in UTP theories of the Circus language family.
  An action is a reactive program that can both perform state updates and exchange events with
  an environment. However, there are several semantic models that can be given to actions,
  such as the untimed theory of stateful-failure reactive designs as used by Circus vs.
  the timed theory in CircusTime vs. the refusal testing model vs. probabilistic actions.
  Here, we describe a syntax for actions and a mechanism for assigning a particular semantic model
  to it that also obeys certain laws. \<close>

consts
  seq_comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr ";" 71)

text \<open> The action type is parametrised by a state-space type @{typ 's} and an event alphabet 
  @{typ 'e}. The former will usually be a record (with lenses), and the latter an algebraic
  datatype to represent channels. We cannot directly refer to the types of particular variables
  and channels in this type, as this would require existential quantification. We therefore
  adopt point-free operators that refer only to the state-space type and event type. \<close>

record ('s, 'e) Event =
  ev_pred   :: "'e \<Rightarrow> 's upred" 
  ev_update :: "'e \<Rightarrow> 's usubst"

datatype ('s, 'e) Action = 
  -- {* The deadlock action *}
  stop |

  -- {* Generalised assignment that applies a state transformation *}
  assigns "'s usubst" |

  -- {* Generalised event; takes an event predicate $P$ that can refer to state variables, and
    a substitution $\sigma$ parametrised by events. The assumed semantics of this is that any 
    event $e$ satisfying $P$ can be accepted, and when it is the state update $\sigma(e)$ is 
    executed. *}
  event "('s, 'e) Event" |

  -- {* Sequential composition *}
  seq "('s, 'e) Action" "('s, 'e) Action" |

  -- {* If-then-else conditional *}
  ifthenelse "'s upred" "('s, 'e) Action" "('s, 'e) Action" ("if _ then _ else _ end") |

  -- {* Internal choice *}
  intchoice "('s, 'e) Action" "('s, 'e) Action" |

  -- {* External choice *}
  extchoice "('s, 'e) Action" "('s, 'e) Action" |

  -- {* Guard *}
  guard "'s upred" "('s, 'e) Action"

text \<open> A process is just an action without an unit state-space, since state updates are not
  observable. \<close>

type_synonym 'e Process = "(unit, 'e) Action"

translations
  (type) "'e Process" <= (type) "(unit, 'e) Action"

text \<open> We overload some of the polymorphic operators in Isabelle to give the above a nicer top-level
  syntax. \<close>

adhoc_overloading seq_comp seq
adhoc_overloading uassigns assigns

instantiation Action :: (type, type) sup
begin
  definition sup_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> ('a, 'b) Action"
    where "sup_Action = intchoice"
instance ..
end

text \<open> We derive several operators from our generic constructors. \<close>

definition skips :: "('s, 'e) Action" ("skip") where
"skips = \<langle>id\<rangle>\<^sub>a"

definition assign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> ('s, 'e) Action" where
"assign x v = \<langle>[x \<mapsto>\<^sub>s v]\<rangle>\<^sub>a"

definition sync :: "'e \<Rightarrow> ('s, 'e) Action" where
"sync a = event \<lparr> ev_pred = (\<lambda> b. \<guillemotleft>a = b\<guillemotright>), ev_update = (\<lambda> x. id) \<rparr>"

definition recv :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> ('s, 'e) Action" ("_\<^bold>?'(_')") where
"recv c x = event \<lparr> ev_pred = (\<lambda> a. \<guillemotleft>a \<in> range c\<guillemotright>), ev_update = (\<lambda> a. [x \<mapsto>\<^sub>s \<guillemotleft>inv c a\<guillemotright>]) \<rparr>"

definition send :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> ('s, 'e) Action" ("_\<^bold>!'(_')") where
"send c v = event \<lparr> ev_pred = (\<lambda> a. \<guillemotleft>a\<guillemotright> =\<^sub>u (c\<cdot>v)\<^sub>u), ev_update = (\<lambda> a. id) \<rparr>"

subsection \<open> Action Syntax Parser \<close>

nonterminal raction

syntax
  "_bracket_raction"   :: "raction \<Rightarrow> raction" ("'(_')")
  "_skip_raction"      :: "raction" ("skip")
  "_seq_raction"       :: "raction \<Rightarrow> raction \<Rightarrow> raction" (infixr ";/" 71)
  "_if_raction"        :: "logic \<Rightarrow> raction \<Rightarrow> raction \<Rightarrow> raction" ("if _ then _ else _ end")
  "_assign_raction"    :: "id \<Rightarrow> logic \<Rightarrow> raction" (infixr ":=" 72)
  "_basic_ev_raction"  :: "id \<Rightarrow> raction" ("_")
  "_rcv_ev_raction"    :: "svid \<Rightarrow> id \<Rightarrow> raction" ("_?'(_')" [85,86])
  "_send_ev_raction"   :: "id \<Rightarrow> logic \<Rightarrow> raction" ("_!'(_')" [85,86]) 

translations
  "_bracket_raction P"     => "P"
  "_skip_raction"          == "CONST skips"
  "_seq_raction P Q"       => "P ; Q"
  "_if_raction b P Q"      == "CONST ifthenelse P b Q"
  "_assign_raction x v"    => "CONST assigns [x \<mapsto>\<^sub>s v]"
  "_basic_ev_raction e"    == "CONST sync e"
  "_rcv_ev_raction c x"    == "CONST recv c x"
  "_send_ev_raction c v"   == "CONST send c v"

subsection \<open> Semantic Models \<close>

text \<open> A semantic model for the action language is parametrised by three types: @{typ 's} and @{typ 'e},
  to represent the state space and events, and @{typ '\<alpha>} to represent the alphabet of the predicate
  that provides the semantic domain. It consists of two constants: @{text act_sem}, a semantic 
  function for actions, and @{text act_hcond}, which is the healthiness condition of the underlying
  UTP theory. \<close>

record ('s, 'e, '\<alpha>) Action_Semantics =
  act_sem   :: "('s, 'e) Action \<Rightarrow> '\<alpha> upred" ("\<lbrakk>_\<rbrakk>\<^sub>A\<index>")
  act_hcond :: "'\<alpha> upred \<Rightarrow> '\<alpha> upred" ("\<H>\<^sub>A\<index>")

text \<open> We use this to define equality on actions. \<close>

definition asem_eq :: "('s, 'e, '\<alpha>) Action_Semantics \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action \<Rightarrow> bool" (infix "\<approx>\<index>" 50) where
"asem_eq AS P Q = (act_sem AS P = act_sem AS Q)"

text \<open> An action semantics expects certain laws to be satisfied \<close>

locale action_semantics =
  fixes AS :: "('s, 'e, '\<alpha>) Action_Semantics" (structure)
  assumes 
    sem_healthy [closure]: "\<lbrakk>P\<rbrakk>\<^sub>A is \<H>\<^sub>A" and
    seq_assoc: "(P ; Q) ; R \<approx> P ; (Q ; R)" and
    seq_left_unit: "skip ; P \<approx> P" and
    seq_right_unit: "P ; skip \<approx> P" and
    if_true: "if true then P else Q end \<approx> P" and
    if_false: "if false then P else Q end \<approx> Q"
  
end