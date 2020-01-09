section \<open> GasAnalysis Model \<close>

theory GasAnalysis
imports Chemical
begin

consts thr :: Intensity

text \<open> Gas Analysis State Machine Definition \<close>

statemachine GasAnalysis =
  vars sts::Status  gs::"GasSensor list"  ins::Intensity  anl::real
  events resume  stop  turn::real  gas::"GasSensor list"
  states InitState NoGas Reading FinalState
         Analysis: "entry sts := analysis(gs)" 
         GasDetected: "entry ins := intensity(gs)" 
  initial InitState finals FinalState
  transitions
    t1: "from InitState to NoGas action gs := []; anl := 0"
    t2: "from NoGas to Analysis trigger gas?(gs)"
    t3: "from Analysis to NoGas condition (sts = noGas) action resume"
    t4: "from Analysis to GasDetected condition (sts = gasD)"
    t5: "from GasDetected to FinalState condition goreq(ins, thr) action stop"
    t6: "from GasDetected to Reading condition (\<not> goreq(ins, thr)) 
         action anl := location(gs) ; turn!(anl)"
    t7: "from Reading to Analysis trigger gas?(gs)"

text \<open> Boilerplate code -- will eventually be automatically generated \<close>

lemma Wf: "WfStateMachine GasAnalysis.machine"
  by (check_machine defs: GasAnalysis.defs)

lemma GasAnalysis_nmap:"nmap\<^bsub>GasAnalysis.machine\<^esub> = 
    [''InitState'' \<mapsto> GasAnalysis.InitState, ''NoGas'' \<mapsto> GasAnalysis.NoGas, ''Reading'' \<mapsto> GasAnalysis.Reading, ''FinalState'' \<mapsto>
     GasAnalysis.FinalState, ''Analysis'' \<mapsto> GasAnalysis.Analysis, ''GasDetected'' \<mapsto> GasAnalysis.GasDetected]"
  by (simp add: sm_node_map_def GasAnalysis.machine_def GasAnalysis.states_def GasAnalysis.simps)

lemma GasAnalysis_tmap:"tmap\<^bsub>GasAnalysis.machine\<^esub> = [''InitState'' \<mapsto> [GasAnalysis.t1], ''NoGas'' \<mapsto> [GasAnalysis.t2], ''Reading'' \<mapsto> [GasAnalysis.t7], ''FinalState'' \<mapsto> [], ''Analysis'' 
     \<mapsto> [GasAnalysis.t4, GasAnalysis.t3], ''GasDetected'' \<mapsto> [GasAnalysis.t6, GasAnalysis.t5]]"
  by (simp add: sm_trans_map_def GasAnalysis.machine_def GasAnalysis.states_def GasAnalysis.transitions_def GasAnalysis.simps)


lemma [simp]: "ninit\<^bsub>GasAnalysis.machine\<^esub> = GasAnalysis.InitState"
  by (simp add: GasAnalysis.defs sm_node_map_def)

lemma GasAnalysis_nodes:
  "nnames\<^bsub>GasAnalysis.machine\<^esub> = {''GasDetected'', ''Analysis'', ''FinalState'', ''Reading'', ''NoGas'', ''InitState''}"
  by (simp add: sm_node_names_def GasAnalysis.defs)

lemma GasAnalysis_inters:
  "inames\<^bsub>GasAnalysis.machine\<^esub> = {''Analysis'', ''GasDetected'', ''Reading'', ''NoGas'', ''InitState''}"
  by (auto simp add: sm_inter_names_def sm_inters_def GasAnalysis.defs)

notation GasAnalysis.null_event ("\<^bold>\<epsilon>")
notation GasAnalysis.gas ("gas")
notation GasAnalysis.stop ("stop")
notation GasAnalysis.turn ("turn")
notation GasAnalysis.resume ("resume")

text \<open> Deadlock Freedom Check \<close>

lemma GasAnalysis_deadlock_free: "dlockf \<sqsubseteq> GasAnalysis.action"
  \<comment> \<open> The following line produces three proof obligations that can be discharged by sledgehammer \<close>
  apply ((sm_induct wf:Wf simps: GasAnalysis.action_def GasAnalysis_inters, sm_calc simps: GasAnalysis_nmap GasAnalysis_tmap GasAnalysis.semantics GasAnalysis.simps); (simp add: action_rep_eq, rdes_refine))
  oops


end