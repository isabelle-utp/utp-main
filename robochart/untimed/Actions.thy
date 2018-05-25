section \<open> Action Languages \<close>

theory Actions
  imports "UTP-Circus.utp_circus"
begin

typedef ('s, 'e) Action = "{P :: ('s, 'e) action. P is CACT}"
  by (rule_tac x="Skip" in exI, simp add: closure)

notation Rep_Action ("\<lbrakk>_\<rbrakk>\<^sub>A")

type_synonym 'e Process = "(unit, 'e) Action"

translations
  (type) "'e Process" <= (type) "(unit, 'e) Action"

setup_lifting type_definition_Action

instantiation Action :: (type, type) refine
begin
  lift_definition less_eq_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> bool" is "less_eq" .
  lift_definition less_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> bool" is "less" .
instance by (intro_classes; transfer, simp add: less_uexpr_def)
end

lift_definition chaos :: "('s, 'e) Action" is Chaos by (simp add: closure)

lift_definition miracle :: "('s, 'e) Action" is Miracle by (simp add: closure)

lift_definition skips :: "('s, 'e) Action" is Skip by (simp add: closure)

syntax
  "_skips" :: "logic" ("skip")

translations
  "_skips" == "CONST skips"

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

lift_definition sync :: "'e \<Rightarrow> ('s, 'e) Action" ("\<^bold>s'(_')") is "\<lambda> e. e \<^bold>\<rightarrow> Skip" by (simp add: closure)

lift_definition send :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> ('s, 'e) Action" ("_\<^bold>!'(_')" [999,0] 999)
  is "\<lambda> c v. c!(v) \<^bold>\<rightarrow> Skip" by (simp add: closure)

lift_definition receive :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> ('s, 'e) Action" ("_\<^bold>?'(_')" [999,0] 999)
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
  apply (rule AlternateR_list_CACT_closed)
  apply (metis (no_types, lifting) list.pred_set pred_prod_inject)
  apply (metis (no_types, lifting))
  done

adhoc_overloading ualtern_list alternate

text \<open> For the time being, we assume that all branches of an iteration must be productive so
  that we can statically check well-formedness. A more general definition may be helpful in
  future. \<close>

lift_definition iteration :: "('s upred \<times> ('s, 'e) Action) list \<Rightarrow> ('s, 'e) Action" 
is "\<lambda> A. (if (\<forall> (b, P) \<in> set A. P is Productive) then IterateC_list A else Chaos)"
  apply (rename_tac A)
  apply (case_tac "\<forall>(b, P)\<in>set(A). P is Productive")
  apply (simp_all add: closure)
  apply (metis (no_types, lifting) IterateC_list_CACT_closed case_prodD list.pred_set pred_prod_inject)
  apply blast
  done

adhoc_overloading uiterate_list iteration

lift_definition interleave :: "'e Process \<Rightarrow> 'e Process \<Rightarrow> 'e Process" is "InterleaveCSP"
  by (simp add: closure)

lift_definition synchronise :: "'e Process \<Rightarrow> 'e Process \<Rightarrow> 'e Process" is "SynchroniseCSP"
  by (simp add: closure)

purge_notation
  InterleaveCSP (infixr "|||" 75) and
  SynchroniseCSP (infixr "||" 75)

notation
  interleave (infixr "|||" 75) and
  synchronise (infixr "||" 75)

lift_definition rename :: "'e Process \<Rightarrow> ('e \<Rightarrow> 'f) \<Rightarrow> 'f Process" ("_\<lparr>_\<rparr>\<^sub>A" [999,0] 999) is "RenameCSP"
  by (simp add: closure)

lift_definition productive :: "('s, 'e) Action \<Rightarrow> bool" is "\<lambda> P. P is Productive" .

lemma CDF_is_C2 [closure]: "CDF is C2"
  unfolding CDF_def by (rule C2_rdes_intro, simp_all add: closure unrest, rel_auto+)

lemma CDF_is_CACT [closure]: "CDF is CACT"
  by (simp add: CACT_intro closure)

lift_definition dlf :: "('s, 'e) Action" is "CDF"
  by (simp add: closure)

purge_notation
  extChoice (infixl "\<box>" 65)

notation
  ext_choice (infixl "\<box>" 85)

lift_definition state_decl :: "('s, 'e) Action \<Rightarrow> 'e Process" is "state_srea TYPE('s)"
  by (simp add: closure)

subsection \<open> Action Syntax \<close>

nonterminal raction

syntax
  "_bracket_raction"   :: "raction \<Rightarrow> raction" ("'(_')")
  "_skip_raction"      :: "raction" ("skip")
  "_seq_raction"       :: "raction \<Rightarrow> raction \<Rightarrow> raction" (infixr ";/" 71)
  "_if_raction"        :: "logic \<Rightarrow> raction \<Rightarrow> raction \<Rightarrow> raction" ("if _ then _ else _ end")
  "_assign_raction"    :: "id \<Rightarrow> logic \<Rightarrow> raction" (infixr ":=" 72)
  "_basic_ev_raction"  :: "id \<Rightarrow> raction" ("_")
  "_rcv_ev_raction"    :: "id \<Rightarrow> id \<Rightarrow> raction" ("_?'(_')" [85,86])
  "_send_ev_raction"   :: "id \<Rightarrow> logic \<Rightarrow> raction" ("_!'(_')" [85,86]) 
  "_action_state"      :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("decl _ \<bullet>/ _" [0,10] 10)

translations
  "_bracket_raction P"     => "P"
  "_skip_raction"          == "CONST skips"
  "_seq_raction P Q"       => "P ; Q"
  "_if_raction b P Q"      == "CONST cond P b Q"
  "_assign_raction x v"    => "x := v"
  "_basic_ev_raction e"    == "CONST sync e"
  "_rcv_ev_raction c x"    == "CONST receive c x"
  "_send_ev_raction c v"   == "CONST send c v"
  "decl x \<bullet> P"             == "CONST state_decl (LOCAL x \<bullet> P)"

subsection \<open> Algebraic Laws \<close>

named_theorems action_simp

lemma seq_assoc [simp, action_simp]: "(P ; Q) ; R = P ; Q ; R"
  by (transfer, simp add: seqr_assoc)

lemma ext_choice_idem [simp, action_simp]: "P \<box> P = P"
  by (transfer, simp add: extChoice_idem closure)

lemma skip_left_unit [simp, action_simp]: "skip ; P = P"
  by (transfer, simp add: Skip_left_unit closure)

lemma skip_right_unit [simp, action_simp]: "P ; skip = P"
  by (transfer, simp add: Skip_right_unit closure)

lemma stop_choice_left_zero [simp, action_simp]: "stop \<box> P = P"
  by (transfer, simp add: extChoice_Stop closure)

lemma stop_choice_right_zero [simp, action_simp]: "P \<box> stop = P"
  by (transfer, subst extChoice_comm, simp add: extChoice_Stop closure)

lemma stop_seq_left_zero [simp, action_simp]: "stop ; P = stop"
  by (transfer, simp add: closure Stop_left_zero)

lemma true_guard [simp, action_simp]: "true \<^bold>& P = P"
  by (transfer, simp add: closure)

lemma false_guard [simp, action_simp]: "false \<^bold>& P = stop"
  by (transfer, simp add: NCSP_implies_CSP)

lemma frame_seq [simp]: "vwb_lens a \<Longrightarrow> a:[P ; Q]\<^sub>A\<^sup>+ = a:[P]\<^sub>A\<^sup>+ ; a:[Q]\<^sub>A\<^sup>+"
  by (transfer, clarsimp simp add: closure seq_srea_frame)

lemma frame_skip [simp]: "vwb_lens a \<Longrightarrow> a:[skips]\<^sub>A\<^sup>+ = skips"
  by (transfer, simp add: Skip_frame)

lemma frame_sync [simp]: "vwb_lens a \<Longrightarrow> a:[sync e]\<^sub>A\<^sup>+ = sync e"
  by (transfer, rdes_eq)

lemma decl_Skip [simp]: "(decl x \<bullet> skips) = skips"
  by (simp add: state_block_def, transfer, rdes_eq)

lemma interleave_commute: "P ||| Q = Q ||| P"
  by (transfer, simp add: interleave_commute)

lemma interleave_unit: "P ||| skips = P"
  by (transfer, simp add: interleave_unit)

lemma interleave_miracle: "miracle ||| P = miracle"
  by (transfer, simp add: parallel_miracle closure)

lemma sync_commute: "P || Q = Q || P"
  apply (transfer) using parallel_commutative zero_lens_indep' by blast

lemma rename_skip: "skips\<lparr>f\<rparr>\<^sub>A = skips"
  by (transfer, simp add: rename_Skip)

subsection \<open> Proof Tactics \<close>

lemmas action_rep_eq = state_block_def dlf_def state_decl.rep_eq seq.rep_eq assigns.rep_eq iteration.rep_eq send.rep_eq sync.rep_eq closure

method action_refine = (simp add: action_rep_eq, rdes_refine)

method action_eq = (simp add: action_rep_eq, rdes_eq)

end