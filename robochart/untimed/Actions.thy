section \<open> Action Languages \<close>

theory Actions
  imports "UTP-Circus.utp_circus"
begin

typedef ('s, 'e) Action = "{P :: ('s, 'e) action. (P is C2) \<and> (P is NCSP)}"
  by (rule_tac x="Skip" in exI, simp add: closure)

setup_lifting type_definition_Action

lift_definition chaos :: "('s, 'e) Action" is Chaos by (simp add: closure)

lift_definition miracle :: "('s, 'e) Action" is Miracle by (simp add: closure)

lift_definition skips :: "('s, 'e) Action" is Skip by (simp add: closure)

lift_definition stop :: "('s, 'e) Action" is Stop by (simp add: closure)

lift_definition seq :: 
  "('s, 'e) Action \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" (infixr ";" 71) is "op ;;"
  by (simp add: closure)

lift_definition cond :: "('s, 'e) Action \<Rightarrow> 's upred \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action"
  is "cond_srea" by (simp add: closure)

lift_definition assigns :: "'s usubst \<Rightarrow> ('s, 'e) Action" is "AssignsCSP"
  by (simp_all add: closure)
  
adhoc_overloading uassigns assigns

lift_definition guard :: "'s upred \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" (infixr "\<^bold>&" 70) is "GuardCSP"
  by (simp add: closure)

lift_definition sync :: "'e \<Rightarrow> ('s, 'e) Action" is "\<lambda> e. e \<^bold>\<rightarrow> Skip" by (simp add: closure)

lift_definition send :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> ('s, 'e) Action"
  is "\<lambda> c v. c!(v) \<^bold>\<rightarrow> Skip" by (simp add: closure)

lift_definition receive :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> ('s, 'e) Action"
  is "\<lambda> c x. c?(v) \<^bold>\<rightarrow> x :=\<^sub>C \<guillemotleft>v\<guillemotright>" by (simp add: InputCSP_def closure)

lift_definition ext_choice :: "('s, 'e) Action \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" is "op \<box>"
  by (simp add: closure)

lift_definition frame_ext_Action :: "('s \<Longrightarrow> 't) \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('t, 'e) Action"
is "\<lambda> a P. if (vwb_lens a) then a:[P]\<^sub>R\<^sup>+ else Miracle" by (simp add: closure)

syntax
  "_act_frame_ext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>A\<^sup>+" [99,0] 100)

translations
  "_act_frame_ext x P" => "CONST frame_ext_Action x P"
  "_rea_frame_ext (_salphaset (_salphamk x)) P" <= "CONST frame_ext_Action x P"

lift_definition alternate :: "('s upred \<times> ('s, 'e) Action) list \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" is AlternateR_list
  apply (auto)
  apply (rule AlternateR_list_C2_closed)
  apply (simp_all add: closure)
  apply (metis (no_types, lifting) list.pred_set pred_prod_inject)
  apply (metis (no_types, lifting) Ball_set pred_prod_inject)
  apply (rule AlternateR_list_NCSP_closed)
  apply (metis (no_types, lifting) list.pred_set pred_prod_inject)
  apply (metis (no_types, lifting))
  done

adhoc_overloading ualtern_list alternate

text \<open> For the time being, we assume that all branches of an iteration must be productive so
  that we can statically check well-formedness. A more general definition may be helpful in
  future. \<close>

lift_definition iteration :: "('s upred \<times> ('s, 'e) Action) list \<Rightarrow> ('s, 'e) Action" 
is "\<lambda> A. (if (\<forall> (b, P) \<in> set A. P is Productive) then IterateC_list A else Chaos)"
  apply (auto simp add: closure)
  apply (rule IterateC_list_C2_closed)
  apply (metis (no_types, lifting) list.pred_set pred_prod_inject)
  apply blast
  apply (metis (no_types, lifting) Ball_set pred_prod_inject)
  apply (metis (no_types, lifting) Ball_set IterateC_list_NCSP_closed case_prodD pred_prod_inject)
  done

adhoc_overloading uiterate_list iteration

lift_definition productive :: "('s, 'e) Action \<Rightarrow> bool" is "\<lambda> P. P is Productive" .

purge_notation
  extChoice (infixl "\<box>" 65)

notation
  ext_choice (infixl "\<box>" 65)

lemma seq_assoc [simp]: "(P ; Q) ; R = P ; Q ; R"
  by (transfer, simp add: seqr_assoc)

lemma ext_choice_idem [simp]: "P \<box> P = P"
  by (transfer, simp add: NCSP_implies_CSP extChoice_idem)

lemma skip_left_unit [simp]: "skips ; P = P"
  by (transfer, metis Skip_left_unit)

lemma skip_right_unit [simp]: "P ; skips = P"
  by (transfer, metis Skip_right_unit)

lemma stop_choice_left_zero [simp]: "stop \<box> P = P"
  by (transfer, simp add: extChoice_Stop closure)

lemma stop_choice_right_zero [simp]: "P \<box> stop = P"
  by (transfer, subst extChoice_comm, simp add: extChoice_Stop closure)

lemma stop_seq_left_zero [simp]: "stop ; P = stop"
  by (transfer, simp add: NCSP_implies_CSP Stop_left_zero)

lemma true_guard [simp]: "true \<^bold>& P = P"
  by (transfer, simp add: NCSP_implies_CSP)

lemma false_guard [simp]: "false \<^bold>& P = stop"
  by (transfer, simp add: NCSP_implies_CSP)

lemma frame_seq [simp]: "vwb_lens a \<Longrightarrow> a:[P ; Q]\<^sub>A\<^sup>+ = a:[P]\<^sub>A\<^sup>+ ; a:[Q]\<^sub>A\<^sup>+"
  by (transfer, clarsimp simp add: NCSP_implies_NSRD seq_srea_frame)

lemma frame_skip [simp]: "vwb_lens a \<Longrightarrow> a:[skips]\<^sub>A\<^sup>+ = skips"
  by (transfer, simp add: Skip_frame)

lemma frame_sync [simp]: "vwb_lens a \<Longrightarrow> a:[sync e]\<^sub>A\<^sup>+ = sync e"
  by (transfer, rdes_eq)

subsection \<open> Action Syntax \<close>

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
  "_skip_raction"          == "CONST skips"
  "_seq_raction P Q"       => "P ; Q"
  "_if_raction b P Q"      == "CONST cond P b Q"
  "_assign_raction x v"    => "x := v"
  "_basic_ev_raction e"    == "CONST sync e"
  "_rcv_ev_raction c x"    == "CONST receive c x"
  "_send_ev_raction c v"   == "CONST send c v"



end