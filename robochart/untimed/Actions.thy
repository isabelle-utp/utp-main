section \<open> Action Languages \<close>

theory Actions
  imports ReactiveSpec
begin

typedef ('s, 'e) Action = "{P :: ('s, 'e) action. P is CACT}"
  by (rule_tac x="Skip" in exI, simp add: closure)

notation Rep_Action ("\<lbrakk>_\<rbrakk>\<^sub>A")

type_synonym 'e Process = "(unit, 'e) Action"

translations
  (type) "'e Process" <= (type) "(unit, 'e) Action"

setup_lifting type_definition_Action

lemma Action_eq_transfer: "P = Q \<longleftrightarrow> \<lbrakk>P\<rbrakk>\<^sub>A = \<lbrakk>Q\<rbrakk>\<^sub>A"
  by (auto, metis Rep_Action_inverse)

lemma Rep_Action_CACT_closed [closure]: "\<lbrakk>P\<rbrakk>\<^sub>A is CACT"
  using Rep_Action by auto

lemma map_prod_Rep_Action_CACT_closed [closure]:
  "(b, P) \<in> map_prod id Rep_Action ` A \<Longrightarrow> P is CACT"
  using Rep_Action_CACT_closed by blast

lemma map_prod_memE:
  "\<lbrakk> (x, y) \<in> map_prod f g ` A; \<And> i j. (i, j) \<in> A \<Longrightarrow> P (f i) (g j) \<rbrakk> \<Longrightarrow> P x y"
  by blast

instantiation Action :: (type, type) refine
begin
  lift_definition less_eq_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> bool" is "less_eq" .
  lift_definition less_Action :: "('a, 'b) Action \<Rightarrow> ('a, 'b) Action \<Rightarrow> bool" is "less" .
instance by (intro_classes; transfer, simp add: less_uexpr_def)
end

lift_definition chaos :: "('s, 'e) Action" is Chaos by (simp add: closure)

lift_definition miracle :: "('s, 'e) Action" is Miracle by (simp add: closure)

lift_definition skips :: "('s, 'e) Action" ("skip") is Skip by (simp add: closure)

lift_definition stop :: "('s, 'e) Action" is Stop by (simp add: closure)

lift_definition 
  spec :: "('a \<Longrightarrow> 's) \<Rightarrow> 's upred \<Rightarrow> 's upred \<Rightarrow> ('s, 'e) Action" ("_:[_, _]" [999, 0, 0] 999) 
  is "SpecC"
  by (simp add: closure)

utp_lift_notation spec (0)

lift_definition assumption :: "'s upred \<Rightarrow> ('s, 'e) Action" ("[_]\<^sub>A") is "AssumeCircus"
  by (simp add: closure)

lift_definition seq :: 
  "('s, 'e) Action \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" is "(;;)"
  by (simp add: closure)

adhoc_overloading seq_comp seq

lift_definition cond :: "'s upred \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action"
  ("if _ then _ else _ end")
  is "\<lambda> b P Q. cond_srea P b Q" by (simp add: closure)

utp_lift_notation cond (1 2)

lift_definition assigns :: "'s usubst \<Rightarrow> ('s, 'e) Action" is "AssignsCSP"
  by (simp_all add: closure)

adhoc_overloading uassigns assigns

lemma st_subst_NCSP_closed [closure]:
  assumes "P is NCSP"
  shows "\<sigma> \<dagger>\<^sub>S P is NCSP"
  by (rdes_simp cls: assms)

lemma st_subst_C2_closed [closure]:
  assumes "P is NCSP" "P is C2"
  shows "\<sigma> \<dagger>\<^sub>S P is C2"
  by (rdes_simp cls: assms, simp add: C2_rdes_intro closure assms unrest)

lemma st_subst_CACT_closed [closure]:
  assumes "P is CACT"
  shows "\<sigma> \<dagger>\<^sub>S P is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lift_definition asubst :: "'s usubst \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" is st_subst
  by (simp add: closure)

adhoc_overloading usubst asubst

lift_definition guard :: "'s upred \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" (infixr "\<^bold>&" 60) is "GuardCSP"
  by (simp add: closure)

utp_lift_notation guard (1)

lift_definition sync :: "'e \<Rightarrow> ('s, 'e) Action" ("\<^bold>s'(_')") is "\<lambda> e. e \<^bold>\<rightarrow> Skip" by (simp add: closure)

lift_definition send :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> ('s, 'e) Action" ("_\<^bold>!'(_')" [999,0] 999)
  is "\<lambda> c v. c!(v) \<^bold>\<rightarrow> Skip" by (simp add: closure)

utp_lift_notation send (0)

lift_definition receive :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> ('s, 'e) Action" ("_\<^bold>?'(_')" [999,0] 999)
  is "\<lambda> c x. c?(v) \<^bold>\<rightarrow> x :=\<^sub>C \<guillemotleft>v\<guillemotright>" by (simp add: InputCSP_def closure)

lift_definition ext_choice :: "('s, 'e) Action \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" is "(\<box>)"
  by (simp add: closure)

lift_definition frame_ext_Action :: "('s \<Longrightarrow> 't) \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('t, 'e) Action"
is "\<lambda> a P. if (vwb_lens a) then a:[P]\<^sub>R\<^sup>+ else Miracle" by (simp add: closure)

syntax
  "_act_frame_ext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>A\<^sup>+" [99,0] 100)

translations
  "_act_frame_ext x P" => "CONST frame_ext_Action x P"
  "_act_frame_ext (_salphaset (_salphamk x)) P" <= "CONST frame_ext_Action x P"

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
  unfolding CDF_def by (rule C2_rdes_intro, simp_all add: closure unrest)

lemma CDF_is_CACT [closure]: "CDF is CACT"
  by (simp add: CACT_intro closure)

lemma choose_srd_CACT [closure]: "ndiv\<^sub>R is CACT"
  by (simp add: rdes_def closure unrest CACT_rdes_intro)

lift_definition divf :: "('s, 'e) Action" is "ndiv\<^sub>R"
  by (simp add: closure)

lift_definition dlockf :: "('s, 'e) Action" is "CDF"
  by (simp add: closure)

purge_notation
  extChoice (infixl "\<box>" 59)

notation
  ext_choice (infixl "\<box>" 59)

lift_definition state_decl :: "('s, 'e) Action \<Rightarrow> 'e Process" is "state_srea TYPE('s)"
  by (simp add: closure)

lemma ex_st'_CDC_closed [closure]: "P is CDC \<Longrightarrow> (\<exists> $st\<acute> \<bullet> P) is CDC"
  by (rel_blast)

lift_definition contract :: "('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) rrel \<Rightarrow> ('s, 'e) Action" ("[_\<turnstile>_|_]")
is "\<lambda> P Q R. \<^bold>R\<^sub>s(RC1(P) \<turnstile> (\<exists> $st\<acute> \<bullet> Q) \<diamondop> (\<exists> $ref\<acute> \<bullet> R))"
  apply (rule CACT_intro)
   apply (rule NCSP_rdes_intro)
  apply (simp_all add: closure unrest)
  apply (metis (no_types, lifting) CRC_intro'' Healthy_intro RC1_def RC1_idem rea_not_CRR_closed rea_true_RR seq_CRR_closed)
  apply (rule C2_rdes_intro)
       apply (simp_all add: closure unrest)
  apply (metis (no_types, lifting) CRC_intro'' Healthy_intro RC1_def RC1_idem rea_not_CRR_closed rea_true_RR seq_CRR_closed)
  done

lift_definition pre\<^sub>A :: "('s, 'e) Action \<Rightarrow> ('s, 'e) rrel" is "pre\<^sub>R"
  by (metis CACT_implies_NCSP NCSP_implies_NSRD NSRD_neg_pre_RC false_CDC preR_CRR wp_rea_CDC_closed wp_rea_RC_false)

lift_definition StateInvA :: "'s upred \<Rightarrow> ('s, 'e) Action" ("sinv\<^sub>A") is StateInvR
  by (simp add: closure)

lemmas action_rep_eq = 
  less_eq_Action.rep_eq
  productive.rep_eq
  assumption.rep_eq
  guard.rep_eq
  stop.rep_eq
  skips.rep_eq
  receive.rep_eq
  send.rep_eq sync.rep_eq
  ext_choice.rep_eq
  frame_ext_Action.rep_eq
  interleave.rep_eq
  synchronise.rep_eq
  Action_eq_transfer
  contract.rep_eq
  asubst.rep_eq
  miracle.rep_eq
  state_block_def 
  divf.rep_eq
  dlockf.rep_eq 
  state_decl.rep_eq seq.rep_eq assigns.rep_eq iteration.rep_eq 
  StateInvA.rep_eq

subsection \<open> Action Syntax \<close>

nonterminal raction

syntax
  "_bracket_raction"   :: "raction \<Rightarrow> raction" ("'(_')")
  "_skip_raction"      :: "raction" ("skip")
  "_seq_raction"       :: "raction \<Rightarrow> raction \<Rightarrow> raction" (infixr ";/" 71)
  "_if_raction"        :: "logic \<Rightarrow> raction \<Rightarrow> raction \<Rightarrow> raction" ("if _ then _ else _ end")
  "_assign_raction"    :: "id \<Rightarrow> logic \<Rightarrow> raction" (infixr ":=" 72)
  "_basic_ev_raction"  :: "id \<Rightarrow> raction" ("_")
  "_rcv_ev_raction"    :: "svid \<Rightarrow> id \<Rightarrow> raction" ("_?'(_')" [85,0] 86)
  "_send_ev_raction"   :: "id \<Rightarrow> logic \<Rightarrow> raction" ("_!'(_')" [85,0] 86) 
  "_action_state"      :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("decl _ \<bullet>/ _" [0,10] 10)

translations
  "_bracket_raction P"     => "P"
  "_skip_raction"          == "CONST skips"
  "_seq_raction P Q"       => "P ; Q"
  "_if_raction b P Q"      == "CONST cond P b Q"
  "_assign_raction x v"    => "CONST assigns [x \<mapsto>\<^sub>s v]"
  "_basic_ev_raction e"    == "CONST sync e"
  "_rcv_ev_raction c x"    == "CONST receive c x"
  "_send_ev_raction c v"   == "CONST send c v"
(*
  "decl x \<bullet> P"             == "CONST state_decl (LOCAL x \<bullet> P)"
*)

subsection \<open> Algebraic Laws \<close>

lemma productive_sync [simp]: "productive (sync e)"
  by (transfer, simp add: closure)

lemma productive_receive [simp]: "productive (receive e x)"
  by (transfer, simp add: closure)

lemma productive_send [simp]: "productive (send e v)"
  by (transfer, simp add: closure)

lemma productive_Productive:
  "productive P \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>A is Productive"  
  by (simp add: productive.rep_eq)

named_theorems action_simp

lemma seq_assoc [action_simp]: "((P :: ('s, 'e) Action) ; Q) ; R = P ; Q ; R"
  by (transfer, simp add: seqr_assoc)

lemma miracle_left_anhil [action_simp]: "miracle ; P = miracle"
  by (transfer, simp add: CACT_implies_NCSP csp_theory.Top_Left_Zero)

lemma assigns_seq [action_simp]: 
  fixes P :: "('s, 'e) Action"
  shows "\<langle>\<sigma>\<rangle>\<^sub>a ; P = (\<sigma> \<dagger> P)"
  by (transfer, metis (no_types, lifting) AssignsCSP_as_AssignsR CACT_implies_NCSP NCSP_implies_NSRD assigns_srd_left_seq csp_theory.Unit_Left seqr_assoc)

lemma asubst_asm [action_simp]: "\<sigma> \<dagger> [b]\<^sub>A = [\<sigma> \<dagger> b]\<^sub>A ; \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: action_rep_eq, rdes_eq)

lemma asubst_twice [action_simp]: 
  fixes P :: "('s, 'e) Action"
  shows "\<sigma> \<dagger> \<rho> \<dagger> P = (\<rho> \<circ>\<^sub>s \<sigma>) \<dagger> P"
  by (simp add: action_rep_eq usubst)

lemma asubst_seq [action_simp]:
  fixes P Q :: "('s, 'e) Action"
  shows "\<sigma> \<dagger> (P ; Q) = ((\<sigma> \<dagger> P) ; Q)"
  by (simp add: action_rep_eq usubst)

lemma asubst_skip [action_simp]:
  "\<sigma> \<dagger> skip = \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: action_rep_eq, rdes_eq)

lemma asubst_stop [action_simp]:
  "\<sigma> \<dagger> stop = stop"
  by (simp add: action_rep_eq, rdes_eq)

lemma asubst_assigns [action_simp]:
  "\<sigma> \<dagger> (\<langle>\<rho>\<rangle>\<^sub>a :: ('s, 'e) Action) = \<langle>\<rho> \<circ>\<^sub>s \<sigma>\<rangle>\<^sub>a"
  by (simp add: action_rep_eq, rdes_eq)

lemma GuardCSP_usubst:
  assumes "P is NCSP"
  shows "\<sigma> \<dagger>\<^sub>S (b &\<^sub>C P) = (\<sigma> \<dagger> b) &\<^sub>C (\<sigma> \<dagger>\<^sub>S P)"
  by (rdes_eq cls: assms)

lemma extChoice_usubst:
  assumes "P is NCSP" "Q is NCSP"
  shows "\<sigma> \<dagger>\<^sub>S (extChoice P Q) = extChoice (\<sigma> \<dagger>\<^sub>S P) (\<sigma> \<dagger>\<^sub>S Q)"
  by (rdes_eq cls: assms)

lemma asubst_extchoice [action_simp]:
  "\<sigma> \<dagger> (P \<box> Q) = (\<sigma> \<dagger> P) \<box> (\<sigma> \<dagger> Q)"
  by (simp add: action_rep_eq extChoice_usubst closure)

lemma asubst_guard [action_simp]:
  "\<sigma> \<dagger> (b \<^bold>& P) = (\<sigma> \<dagger> b) \<^bold>& (\<sigma> \<dagger> P)"
  by (simp add: action_rep_eq GuardCSP_usubst closure)

lemma asubst_sync [action_simp]:
  "\<sigma> \<dagger> sync e = sync e ; \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: action_rep_eq, rdes_eq)

lemma asubst_send [action_simp]:
  "\<sigma> \<dagger> send e v = send e (\<sigma> \<dagger> v) ; \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: action_rep_eq, rdes_eq)

lemma asubst_recv:
  "\<lbrakk> vwb_lens x; x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> receive e x = receive e x ; \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: action_rep_eq, rdes_eq)

lemma asm_false [action_simp]: "[false]\<^sub>A = miracle"
  by (transfer, rdes_eq)

lemma miracle_top: "P \<sqsubseteq> miracle"
  by (simp add: action_rep_eq closure)

lemma ext_choice_idem [action_simp]: "P \<box> P = P"
  by (transfer, simp add: extChoice_idem closure)

lemma skip_left_unit [action_simp]: "skip ; P = P"
  by (transfer, simp add: Skip_left_unit closure)

lemma skip_right_unit [action_simp]: "P ; skip = P"
  by (transfer, simp add: Skip_right_unit closure)

lemma stop_choice_left_zero [action_simp]: "stop \<box> P = P"
  by (transfer, simp add: extChoice_Stop closure)

lemma stop_choice_right_zero [action_simp]: "P \<box> stop = P"
  by (transfer, subst extChoice_comm, simp add: extChoice_Stop closure)

lemma stop_seq_left_zero [action_simp]: "stop ; P = stop"
  by (transfer, simp add: closure Stop_left_zero)

lemma stop_sinv_refine: "sinv\<^sub>A(a) \<sqsubseteq> stop"
  by (transfer, rdes_refine)

lemma extchoice_sinv_refine:
  assumes "sinv\<^sub>A(a) \<sqsubseteq> P" "sinv\<^sub>A(a) \<sqsubseteq> Q"
  shows "sinv\<^sub>A(a) \<sqsubseteq> (P \<box> Q)"
  using assms by (transfer, simp add: CACT_implies_NCSP extchoice_StateInvR_refine)

lemma true_guard [action_simp]: "true \<^bold>& P = P"
  by (transfer, simp add: closure)

lemma false_guard [action_simp]: "false \<^bold>& P = stop"
  by (transfer, simp add: NCSP_implies_CSP)

lemma frame_seq [simp]: "vwb_lens a \<Longrightarrow> a:[P ; Q]\<^sub>A\<^sup>+ = a:[P]\<^sub>A\<^sup>+ ; a:[Q]\<^sub>A\<^sup>+"
  by (transfer, clarsimp simp add: closure seq_srea_frame)

lemma frame_skip [simp]: "vwb_lens a \<Longrightarrow> a:[skips]\<^sub>A\<^sup>+ = skips"
  by (transfer, simp add: Skip_frame)

lemma frame_sync [simp]: "vwb_lens a \<Longrightarrow> a:[sync e]\<^sub>A\<^sup>+ = sync e"
  by (transfer, rdes_eq)

lemma frame_receive [simp]: "vwb_lens a \<Longrightarrow> a:[receive c x]\<^sub>A\<^sup>+ = receive c (x ;\<^sub>L a)"
  by (transfer, rdes_eq)

lemma frame_send [simp]: "vwb_lens a \<Longrightarrow> a:[send c v]\<^sub>A\<^sup>+ = send c (v \<oplus>\<^sub>p a)"
  by (simp add: action_rep_eq, rdes_eq)

lemma frame_assigns [simp]: "vwb_lens a \<Longrightarrow> a:[\<langle>\<sigma>\<rangle>\<^sub>a]\<^sub>A\<^sup>+ = \<langle>\<sigma> \<oplus>\<^sub>s a\<rangle>\<^sub>a"
  by (simp add: action_rep_eq, rdes_eq)
         
lemma frame_assign_commute_unrest_aux:
  assumes "vwb_lens x" "x \<bowtie> a" "a \<sharp> v" "$x \<sharp> P" "$x\<acute> \<sharp> P"
  shows "\<lceil>[x \<mapsto>\<^sub>s v]\<rceil>\<^sub>s \<dagger> a:[P] = a:[P] ;; x := v"
  by (metis assigns_r_comp assms frame_assign_commute_unrest subst_upd_pr_var)


lemma rea_frame_ext_subst_CRR:
  assumes "vwb_lens x" "x \<bowtie> a" "a \<sharp> v" "P is CRR" "$ref\<acute> \<sharp> P"
  shows "[x \<mapsto>\<^sub>s v] \<dagger>\<^sub>S a:[P]\<^sub>r\<^sup>+ = a:[P]\<^sub>r\<^sup>+ ;; \<Phi>(true,[&x \<mapsto>\<^sub>s v],\<guillemotleft>[]\<guillemotright>)"
proof -
  have "[x \<mapsto>\<^sub>s v] \<dagger>\<^sub>S a:[P]\<^sub>r\<^sup>+ = \<lceil>[st:x \<mapsto>\<^sub>s v \<oplus>\<^sub>p st]\<rceil>\<^sub>s \<dagger> a:[P]\<^sub>r\<^sup>+"
    by (rel_auto)
  also have "... = a:[P]\<^sub>r\<^sup>+ ;; st:x := v \<oplus>\<^sub>p st"
    using assms(1-3,5)
    by (simp add: rea_frame_ext_def rea_frame_def frame_assign_commute_unrest_aux unrest)
  also have "... = a:[CRR P]\<^sub>r\<^sup>+ ;; st:x := v \<oplus>\<^sub>p st"
    by (metis Healthy_def assms(4))
  also have "... = a:[CRR P]\<^sub>r\<^sup>+ ;; \<Phi>(true,[&x \<mapsto>\<^sub>s v],\<guillemotleft>[]\<guillemotright>)"
    using assms(5) by (rel_blast)
  finally show ?thesis
    by (simp add: Healthy_if assms(4))
qed

lemma rdes_frame_ext_asubst:
  assumes "vwb_lens x" "x \<bowtie> a" "a \<sharp> v" "P is NCSP"
  shows "[x \<mapsto>\<^sub>s v] \<dagger>\<^sub>S a:[P]\<^sub>R\<^sup>+ = a:[P]\<^sub>R\<^sup>+ ;; x :=\<^sub>C v"
  apply (rdes_eq_split cls: assms(4))
    apply (simp_all add: rea_frame_ext_subst_CRR closure unrest assms)
  apply (rel_auto)
    apply (simp_all add: assms(2) lens_indep.lens_put_irr2)
  apply (rel_auto)
   apply (simp_all add: assms(2) lens_indep.lens_put_irr2)
  apply (rel_auto)
   apply (simp_all add: assms(2) lens_indep.lens_put_irr2)
  done


lemma frame_asubst: 
  assumes "vwb_lens x" "vwb_lens a" "x \<bowtie> a" "a \<sharp> v" 
  shows "[x \<mapsto>\<^sub>s v] \<dagger> a:[P]\<^sub>A\<^sup>+ = a:[P]\<^sub>A\<^sup>+ ; x := v"
proof -
  obtain \<sigma> where s: "\<sigma> = [x \<mapsto>\<^sub>s v]"
    by simp
  have "\<sigma> \<dagger> a:[P]\<^sub>A\<^sup>+ = a:[P]\<^sub>A\<^sup>+ ; \<langle>\<sigma>\<rangle>\<^sub>a"
    by (transfer fixing: \<sigma> a, simp add: s assms CACT_implies_NCSP rdes_frame_ext_asubst subst_upd_pr_var)
  thus ?thesis by (simp add: pr_var_def s)
qed

(*
lemma decl_Skip [simp]: "(decl x \<bullet> skips) = skips"
  by (simp add: state_block_def, transfer, rdes_eq)
*)

lemma interleave_commute: "P ||| Q = Q ||| P"
  by (transfer, simp add: interleave_commute)

lemma interleave_unit [action_simp]: "P ||| skips = P"
  by (transfer, simp add: interleave_unit)

lemma interleave_miracle [action_simp]: "miracle ||| P = miracle"
  by (transfer, simp add: parallel_miracle closure)

lemma sync_commute: "P || Q = Q || P"
  apply (transfer)
  by (meson parallel_commutative zero_lens_indep) 

lemma rename_skip: "skip\<lparr>f\<rparr>\<^sub>A = skip"
  by (transfer, simp add: rename_Skip)
  
lemma iterate_Nil: "iteration [] = skip"
  by (transfer, simp add: IterateC_list_def IterateC_def WhileC_false closure)

lemma iterate_refine_lemma:
  "A \<noteq> {} \<Longrightarrow> (\<Or> (i, j) \<in> map_prod f g ` A \<bullet> P i j) = (\<Or> (i, j) \<in> A \<bullet> P (f i) (g j))"
  apply (simp add: map_prod_def)
  apply (rel_auto)
  apply (smt Collect_cong fst_conv imageE pair_imageI prod.case_eq_if prod.collapse snd_conv)
  done

lemma assumption_true [simp]: "[true]\<^sub>A = skip"
  by (transfer, simp add: AssumeCircus_def)

lemma asm_assign:
  "vwb_lens x \<Longrightarrow> [&x =\<^sub>u k]\<^sub>A ; (x := k) =  [&x =\<^sub>u k]\<^sub>A"
  apply (simp add: action_rep_eq)
  apply (rdes_eq)
  using vwb_lens.put_eq apply force+
  done

lemma asm_pre_refine: "P \<sqsubseteq> [b]\<^sub>A ; P"
  by (simp add: action_rep_eq rdes_assume_pre_refine closure)

lemma iterate_refine_intro:
  assumes  
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> productive P"
    "S \<sqsubseteq> I ; [\<not> (\<Or> (b, P) \<in> set A \<bullet> b)]\<^sub>A"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> S \<sqsubseteq> S ; [b]\<^sub>A ; P"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> S \<sqsubseteq> I ; [b]\<^sub>A ; P" 
  shows "S \<sqsubseteq> I ; iteration A"
proof (cases "A = []")
  case True
  then show ?thesis
    using assms(2)
    by (simp add: iterate_Nil UINF_false)
next
  case False
  then show ?thesis 
  using assms
  apply (simp add: action_rep_eq)
  apply (safe)
  apply (rule IterateC_list_outer_refine_init_intro, simp_all add: closure prod.case_eq_if iterate_refine_lemma gcmd_AssumeCircus)
  apply (auto elim: map_prod_memE simp add: AssumeR_comp_AssumeCircus closure)
  done
qed

lemma dlockf_refine_intro: "dlockf \<sqsubseteq> P \<Longrightarrow> dlockf \<sqsubseteq> (dlockf ; P)"
  by (transfer, simp add: CDF_refine_intro)

lemma dlockf_state_decl:
  "dlockf \<sqsubseteq> P \<Longrightarrow> dlockf \<sqsubseteq> state_decl P"
  by (transfer, simp add: state_srea_refine alpha)

lemma divf_frame_ext:
  "divf \<sqsubseteq> P \<Longrightarrow> divf \<sqsubseteq> a:[P]\<^sub>A\<^sup>+"
  by (transfer, simp add: ndiv_srd_refines_preR_true closure rdes, safe, simp add: rdes_def rdes alpha closure)

lemma divf_seq_refine:
  assumes "divf \<sqsubseteq> P" "divf \<sqsubseteq> Q"
  shows "divf \<sqsubseteq> (P ; Q)"
  using assms by (transfer, simp add: ndiv_srd_refines_preR_true closure rdes rpred wp)

lemma divf_extchoice_refine:
  assumes "divf \<sqsubseteq> P" "divf \<sqsubseteq> Q"
  shows "divf \<sqsubseteq> (P \<box> Q)"
  using assms by (transfer, simp add: ndiv_srd_refines_preR_true closure rdes rpred wp)

lemma divf_stop: "divf \<sqsubseteq> stop"
  by (transfer, rdes_refine)

lemma divf_extchoice_fold_refine:
  assumes "\<And> P. P \<in> set(xs) \<Longrightarrow> divf \<sqsubseteq> P"
  shows "divf \<sqsubseteq> foldr (\<box>) xs stop"
  using assms
  apply (induct xs)
   apply (simp_all add: divf_stop)
  apply (rule divf_extchoice_refine)
   apply (auto simp add: assms)
  done

lemma divf_assigns: "divf \<sqsubseteq> \<langle>\<sigma>\<rangle>\<^sub>a"
  by (transfer, simp add: ndiv_srd_refines_preR_true closure rdes rpred wp)

lemma divf_guard: "divf \<sqsubseteq> P \<Longrightarrow> divf \<sqsubseteq> b \<^bold>& P"
  by (transfer, simp add: ndiv_srd_refines_preR_true closure rdes rpred wp)

lemma divf_sync: "divf \<sqsubseteq> sync e"
  by (transfer, simp add: ndiv_srd_refines_preR_true closure rdes rpred usubst wp)

subsection \<open> Contract Theorems \<close>

named_theorems contract

lemma chaos_contract [contract]: "chaos = [false \<turnstile> false | false]"
  by (transfer, rdes_eq)

lemma stop_contract [contract]: "stop = [true \<turnstile> \<^bold>\<E>(true,\<guillemotleft>[]\<guillemotright>,{}\<^sub>u) | false]"
  by (simp add: action_rep_eq rrel_rep_eq, rdes_eq)

lemma sync_contract [contract]: "sync e = [true \<turnstile> \<^bold>\<E>(true,\<guillemotleft>[]\<guillemotright>,{\<guillemotleft>e\<guillemotright>}\<^sub>u) | \<^bold>\<Phi>(true,id\<^sub>s,\<guillemotleft>[e]\<guillemotright>)]"
  by (simp add: action_rep_eq rrel_rep_eq, rdes_eq)

lemma seq_lemma_1: 
  assumes "Q\<^sub>1 is CRR"
  shows "(\<exists> $ref\<acute> \<bullet> P\<^sub>3) wp\<^sub>r RC1 Q\<^sub>1 = P\<^sub>3 wp\<^sub>r RC1 Q\<^sub>1"
proof -
  have "(\<exists> $ref\<acute> \<bullet> P\<^sub>3) wp\<^sub>r CRC Q\<^sub>1 = P\<^sub>3 wp\<^sub>r CRC Q\<^sub>1"
    by (rel_auto)
  thus ?thesis
    by (simp add: CRC_def CRR_implies_RR CRR_unrest_ref Healthy_if RC_def assms ex_unrest ref_unrest_RC1)
  
qed

lemma seq_lemma_2: 
  assumes "Q\<^sub>2 is CRR"
  shows "((\<exists> $st\<acute> \<bullet> P\<^sub>2) \<or> (\<exists> $ref\<acute> \<bullet> P\<^sub>3) ;; (\<exists> $st\<acute> \<bullet> Q\<^sub>2)) = (\<exists> $st\<acute> \<bullet> P\<^sub>2 \<or> P\<^sub>3 ;; Q\<^sub>2)"
proof -
  have "((\<exists> $st\<acute> \<bullet> P\<^sub>2) \<or> (\<exists> $ref\<acute> \<bullet> P\<^sub>3) ;; (\<exists> $st\<acute> \<bullet> CRR(Q\<^sub>2))) = (\<exists> $st\<acute> \<bullet> P\<^sub>2 \<or> P\<^sub>3 ;; CRR(Q\<^sub>2))"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma seq_lemma_3:
  assumes "Q\<^sub>3 is CRR"
  shows "(\<exists> $ref\<acute> \<bullet> P\<^sub>3) ;; (\<exists> $ref\<acute> \<bullet> Q\<^sub>3) = (\<exists> $ref\<acute> \<bullet> P\<^sub>3 ;; Q\<^sub>3)"
proof -
  have "(\<exists> $ref\<acute> \<bullet> P\<^sub>3) ;; (\<exists> $ref\<acute> \<bullet> CRR(Q\<^sub>3)) = (\<exists> $ref\<acute> \<bullet> P\<^sub>3 ;; CRR(Q\<^sub>3))"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

(*
lemma contract_choice [contract]:
  "[P\<^sub>1 \<turnstile> P\<^sub>2 | P\<^sub>3] \<sqinter> [Q\<^sub>1 \<turnstile> Q\<^sub>2 | Q\<^sub>3] = [P\<^sub>1 \<and> Q\<^sub>1 \<turnstile> P\<^sub>2 \<or> Q\<^sub>2 | P\<^sub>3 \<or> Q\<^sub>3]"
*)

lemma CDC_ex_st' [rpred]: "CDC(\<exists> $st\<acute> \<bullet> P) = (\<exists> $st\<acute> \<bullet> CDC(P))"
  by (rel_auto)

lemma CDC_disj [rpred]: "CDC(P \<or> Q) = (CDC P \<or> CDC Q)"
  by (rel_auto)


declare RC1_RR_closed [closure]

lemma ex_disj:"(\<exists> x \<bullet> P \<or> Q) = ((\<exists> x \<bullet> P) \<or> (\<exists> x \<bullet> Q))"
  by (rel_auto)

lemma contract_extchoice [contract]:
  assumes "$st\<acute> \<sharp> P\<^sub>2"
  shows "[P\<^sub>1 \<turnstile> P\<^sub>2 | P\<^sub>3] \<box> [Q\<^sub>1 \<turnstile> Q\<^sub>2 | Q\<^sub>3] = [P\<^sub>1 \<and> Q\<^sub>1 \<turnstile> [P\<^sub>2 \<and> Q\<^sub>2]\<^sub>\<box> \<or> [P\<^sub>2 \<or> Q\<^sub>2]\<^sub>\<rhd> | P\<^sub>3 \<or> Q\<^sub>3]"
  using assms
  apply (transfer)
  apply (simp_all add: rdes_def closure unrest rpred RC1_conj ex_disj)
  apply (rule srdes_tri_eq_intro)
  apply (simp_all add: unrest ex_unrest)
  apply (rel_simp)
  done


lemma contract_seqr [contract]:
  "[P\<^sub>1 \<turnstile> P\<^sub>2 | P\<^sub>3] ; [Q\<^sub>1 \<turnstile> Q\<^sub>2 | Q\<^sub>3] = [P\<^sub>1 \<and> P\<^sub>3 wp Q\<^sub>1 \<turnstile> (P\<^sub>2 \<or> P\<^sub>3 ; Q\<^sub>2) | (P\<^sub>3 ; Q\<^sub>3)]"
  apply (transfer)
  apply (subst rdes_def)
  apply (simp_all add: closure unrest)
  apply (metis (no_types, lifting) CRR_implies_RR R1_seqr_closure R1_true_comp RA1 RC1_RR_closed RC1_def RC_intro rea_not_R1 rea_not_not rea_true_R1)
  apply (rule srdes_tri_eq_intro)
    apply (simp add: seq_lemma_1)
    apply (metis (no_types, lifting) CRR_implies_RR R1_seqr_closure R2_implies_R1 RA1 RC1_conj RC1_def RR_implies_R2 rea_not_R2_closed rea_not_not rea_true_R1 wp_rea_def)
   apply (simp add: seq_lemma_2)
  apply (simp_all add: seq_lemma_2 seq_lemma_3)
  oops

lemma [unrest]: "$st\<acute> \<sharp> \<^bold>\<E>(true,\<guillemotleft>[]\<guillemotright>,{\<guillemotleft>a\<guillemotright>}\<^sub>u)"
  by (simp add: runrest.rep_eq rrel_rep_eq unrest)

lemma [simp]: "[P \<and> Q]\<^sub>\<box> = ([P]\<^sub>\<box> \<and> [Q]\<^sub>\<box>)"
  by (transfer; simp add: rpred)

lemma [simp]: "[P \<or> Q]\<^sub>\<rhd> = ([P]\<^sub>\<rhd> \<or> [Q]\<^sub>\<rhd>)"
  by (transfer; simp add: rpred)

lemma [simp]: "[\<^bold>\<E>(s,\<guillemotleft>[]\<guillemotright>,E)]\<^sub>\<box> = \<^bold>\<E>(s,\<guillemotleft>[]\<guillemotright>,E)"
  by (transfer; simp add: rpred)

lemma [simp]: "[\<^bold>\<E>(s,\<guillemotleft>[]\<guillemotright>,E)]\<^sub>\<rhd> = false"
  by (transfer; simp add: rpred)

lemma [simp]: "(\<^bold>\<E>(s\<^sub>1,\<guillemotleft>[]\<guillemotright>,E\<^sub>1) \<and> \<^bold>\<E>(s\<^sub>2,\<guillemotleft>[]\<guillemotright>,E\<^sub>2)) = \<^bold>\<E>(s\<^sub>1 \<and> s\<^sub>2,\<guillemotleft>[]\<guillemotright>,(E\<^sub>1 \<union>\<^sub>u E\<^sub>2))"
  by (simp add: rrel_rep_eq rpred)

lemma "sync a \<box> sync b ; sync c = undefined"
  apply (simp add: contract unrest)
  oops

subsection \<open> Proof Tactics \<close>

method action_refine = (simp add: action_rep_eq, rdes_refine)

method action_eq = (simp add: action_rep_eq, rdes_eq)

end