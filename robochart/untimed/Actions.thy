section \<open> Action Languages \<close>

theory Actions
  imports "UTP-Circus.utp_circus"
begin

typedef ('s, 'e) Action = "{P :: ('s, 'e) action. (P is C2) \<and> (P is NCSP)}"
  by (rule_tac x="Skip" in exI, simp add: closure)

setup_lifting type_definition_Action

lift_definition chaos :: "('s, 'e) Action" is Chaos by (simp add: closure)

lift_definition miracle :: "('s, 'e) Action" is Miracle by (simp add: closure)

lift_definition skip :: "('s, 'e) Action" is Skip by (simp add: closure)

lift_definition stop :: "('s, 'e) Action" is Stop by (simp add: closure)

lift_definition seq :: 
  "('s, 'e) Action \<Rightarrow> ('s, 'e) Action \<Rightarrow> ('s, 'e) Action" (infixr ";" 71) is "op ;;"
  by (simp add: closure)

lift_definition assign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> ('s, 'e) Action" is "\<lambda> x v. x :=\<^sub>C v"
  by (simp add: closure)

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

purge_notation
  extChoice (infixl "\<box>" 65)

notation
  ext_choice (infixl "\<box>" 65)

lemma ext_choice_idem [simp]: "P \<box> P = P"
  by (transfer, simp add: NCSP_implies_CSP extChoice_idem)

lemma skip_left_unit [simp]: "skip ; P = P"
  by (transfer, metis Skip_left_unit)

lemma stop_choice_left_zero [simp]: "stop \<box> P = P"
  by (transfer, simp add: extChoice_Stop closure)

lemma stop_seq_left_zero [simp]: "stop ; P = stop"
  by (transfer, simp add: NCSP_implies_CSP Stop_left_zero)

lemma true_guard [simp]: "true \<^bold>& P = P"
  by (transfer, simp add: NCSP_implies_CSP)

lemma false_guard [simp]: "false \<^bold>& P = stop"
  by (transfer, simp add: NCSP_implies_CSP)


end