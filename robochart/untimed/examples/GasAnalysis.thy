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

context GasAnalysis
begin

lemma nmap:"nmap\<^bsub>machine\<^esub> = 
    [''InitState'' \<mapsto> InitState, ''NoGas'' \<mapsto> NoGas, ''Reading'' \<mapsto> Reading, ''FinalState'' \<mapsto>
     FinalState, ''Analysis'' \<mapsto> Analysis, ''GasDetected'' \<mapsto> GasDetected]"
  by (simp add: sm_node_map_def machine_def states_def simps)

lemma tmap:"tmap\<^bsub>machine\<^esub> = [''InitState'' \<mapsto> [t1], ''NoGas'' \<mapsto> [t2], ''Reading'' \<mapsto> [t7], ''FinalState'' \<mapsto> [], ''Analysis'' 
     \<mapsto> [t4, t3], ''GasDetected'' \<mapsto> [t6, t5]]"
  by (simp add: sm_trans_map_def machine_def states_def transitions_def simps)

lemma [simp]: "ninit\<^bsub>machine\<^esub> = InitState"
  by (simp add: defs sm_node_map_def)

lemma nds:
  "nodes\<^bsub>machine\<^esub> = [GasDetected, Analysis, FinalState, Reading, NoGas, InitState]"
  by (simp add: machine_def states_def)

lemma fnds:
  "finals\<^bsub>machine\<^esub> = [''FinalState'']"
  by (simp add: machine_def states_def)
lemma nodes:
  "nnames\<^bsub>machine\<^esub> = {''GasDetected'', ''Analysis'', ''FinalState'', ''Reading'', ''NoGas'', ''InitState''}"
  by (simp add: sm_node_names_def defs)

lemma inters:
  "inames\<^bsub>machine\<^esub> = {''Analysis'', ''GasDetected'', ''Reading'', ''NoGas'', ''InitState''}"
  by (auto simp add: sm_inter_names_def sm_inters_def defs)

notation null_event ("\<^bold>\<epsilon>")
notation gas ("gas")
notation stop ("stop")
notation turn ("turn")
notation resume ("resume")

text \<open> Deadlock Freedom Check \<close>

lemma deadlock_free: "dlockf \<sqsubseteq> local.action"
  \<comment> \<open> The following line produces three proof obligations that can be discharged by sledgehammer \<close>
  apply ((sm_induct wf:Wf simps: action_def inters, sm_calc simps: nmap tmap semantics simps); (simp add: action_rep_eq, rdes_refine))
  oops
end

end