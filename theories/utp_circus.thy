(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus.thy                                                       *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 28 June 2017 *)

section {* Theory of {\Circus} *}

theory utp_circus
imports utp_theories_deep utp_circus_prel
begin (* recall_syntax *)

text {* Types are not printed correctly, have a chat with Simon Foster. *}

typ "('\<sigma>, '\<epsilon>) st_csp"

(* type_synonym 'a relation = "'a Relation.rel" *)

(* translations (type) "'a relation" \<rightleftharpoons> (type)"'a Relation.rel" *)

text {* The below cause ambiguities wrt the corresponding CSP definitions. *}

hide_const utp_cml.Skip
hide_const utp_cml.Stop

subsection {* Process Semantics *}

text {*
  We could get away without the hiding of the state alphabet if we assume that
  all processes have the same state type. The two lemmas we prove following the
  definition establish this and are useful in proofs It is still on open issue
  to what extent the hiding of the state alphabet poses challenges to proofs.
*}

definition Process ::
  "('\<sigma>, '\<epsilon>) action \<Rightarrow>
   (unit, '\<epsilon>) action" where
"Process P = hide_state (\<exists> {$st,$st\<acute>} \<bullet> P)"

text {* The function below makes the state type explicit via an argument. *}

definition ProcessSt ::
  "('\<sigma> itself) \<Rightarrow>
   ('\<sigma>, '\<epsilon>) action \<Rightarrow>
   (unit, '\<epsilon>) action" where
"ProcessSt t P = Process P"

definition Action ::
  "('\<epsilon>, '\<alpha>) action \<Rightarrow>
   (('\<epsilon>, '\<alpha>) action \<Rightarrow> ('\<epsilon>, '\<alpha>) action) \<Rightarrow>
   ('\<epsilon>, '\<alpha>) action" where
"Action = Let"

definition RecAction ::
  "(('\<sigma>, '\<epsilon>) action \<Rightarrow>
    ('\<sigma>, '\<epsilon>) action \<times> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
   ('\<sigma>, '\<epsilon>) action" where
"RecAction act_body =
  Action (\<mu>\<^sub>C X \<bullet> fst (act_body X)) (\<lambda>X. snd (act_body X))"

lemmas circus_syntax =
  Process_def ProcessSt_def Action_def RecAction_def

subsection {* Process Syntax *}

nonterminal statep and action and actions and process

text {*
  We support both basic and composite process definitions. Moreover, processes
  may be parametrised and can include an option state paragraph which must be
  of the form @{text "state('\<sigma>)"}, where @{typ "'\<sigma>"} is a HOL type to be used
  for the state space. If no state paragraph is given, it is inferred by type
  checking. Parametrised actions are current not supported - this is work in
  progress. For examples, see the bottom of the theory.
*}

syntax
  "_State" :: "type \<Rightarrow> statep"                  ("state'(_')")
  "_Action"  :: "[pttrn, logic] \<Rightarrow> action"     ("(2_ =/ _)" 10)
  ""         :: "action \<Rightarrow> actions"            ("_")
  "_Actions" :: "[action, actions] \<Rightarrow> actions" ("_and//_")
  "_ProcBody" :: "[actions, logic] \<Rightarrow> process"          ("((2begin//(_)//\<bullet> (_))//end)")
  "_ProcBodySt" :: "[statep, actions, logic] \<Rightarrow> process" ("((2begin//(_)//(_)//\<bullet> (_))//end)")
  "_BasicProc" :: "idt \<Rightarrow> process \<Rightarrow> bool"     ("(process _ \<triangleq>//_)" [0, 10] 10)
  "_BasicDefn" :: "idt \<Rightarrow> logic   \<Rightarrow> bool"     ("(process _ \<triangleq>//_)" [0, 10] 10)
  "_ParamProc" :: "idt \<Rightarrow> args \<Rightarrow> process \<Rightarrow> bool" ("(process _ _ \<triangleq>//_)" [0, 0, 10] 10)
  "_ParamDefn" :: "idt \<Rightarrow> args \<Rightarrow> logic   \<Rightarrow> bool" ("(process _ _ \<triangleq>//_)" [0, 0, 10] 10)
  "_BasicProcSt" :: "idt \<Rightarrow> type \<Rightarrow> process \<Rightarrow> bool"
  "_ParamProcSt" :: "idt \<Rightarrow> args \<Rightarrow> type \<Rightarrow> process \<Rightarrow> bool"

syntax (output) -- {* Cosmetics *}
  "_Actions_tr'" :: "[action, actions] \<Rightarrow> actions"  ("_//_")

text {*
  Interestingly, it matters whether we split the below into separate blocks
  of @{command translations} statements. Isabelle seems to respect the order
  of translations only when they are included in the same block. Here, the
  order is very important.
*}

translations
  (statep) "state('type)" \<rightleftharpoons> "TYPE('type)"
-- \<open>Shift the type argument from ProcBodySt into (Basic/Param)ProcSt.\<close>
  "_BasicProc name (_ProcBodySt type actions main)" \<rightleftharpoons>
  "_BasicProcSt name type (_ProcBody actions main)"
  "_ParamProc name args (_ProcBodySt type actions main)" \<rightleftharpoons>
  "_ParamProcSt name args type (_ProcBody actions main)"
  "_ProcBody (_Actions     act acts) e" \<rightharpoonup> "_ProcBody act (_ProcBody acts e)"
  "_ProcBody (_Actions_tr' act acts) e" \<leftharpoondown> "_ProcBody act (_ProcBody acts e)"
(*"_ProcBody (_Action name act) more" \<rightleftharpoons> "(CONST Action) act (\<lambda>name. more)"*)
  "_ProcBody (_Action name act) more" \<rightleftharpoons> "(CONST RecAction) (\<lambda>name. (act, more))"
  "_BasicProc name      body" \<rightleftharpoons> "name =         (CONST Process) body"
  "_ParamProc name args body" \<rightleftharpoons> "name = (\<lambda>args. (CONST Process) body)"
  "_BasicProcSt name      type body" \<rightleftharpoons> "name =         (CONST ProcessSt) type body"
  "_ParamProcSt name args type body" \<rightleftharpoons> "name = (\<lambda>args. (CONST ProcessSt) type body)"
-- \<open>Making the below pretty-print can produce convoluted syntax.\<close>
  "_BasicDefn name      body" \<rightharpoonup> "name = body"
  "_ParamDefn name args body" \<rightharpoonup> "name = (\<lambda>args. body)"

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr'
    @{const_syntax Action} @{syntax_const "_Action"}]
*}

text {* Hide non-terminals as this interferes with parsing the action type. *}

hide_type (open)
  utp_circus.action
  utp_circus.actions

(***********************)
(* REVIEWED UNTIL HERE *)
(***********************)

subsection {* Stub Constructs (TODO) *}

text {* TODO: Define the semantics of the operators below. *}

text {*
  Make parallel composition bind weaker than set union, so that the latter can
  be used to combine channel sets. Operator precedence is still and issue that
  we need to address within Isabelle/UTP.
*}

purge_notation
  ParCSP_NS (infixr "[|_|]" 105) and
  InterleaveCSP (infixr "|||" 105)

consts ParCircus ::
  "('\<sigma>, '\<phi>) action  \<Rightarrow> ('\<phi> event set) \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow>
   ('\<sigma>, '\<phi>) action" (infixl "[|(_)|]" 60)

consts HideCircus ::
  "('\<sigma>, '\<phi>) action  \<Rightarrow> ('\<phi> event set) \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\\" 55)

consts InterruptCircus ::
  "('\<sigma>, '\<phi>) action  \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\<triangle>" 100)

subsection {* Circus Conditional *}

syntax "_if_then_else" ::
  "'a upred \<Rightarrow> ('a, 'b) rel \<Rightarrow> ('a, 'b) rel \<Rightarrow> ('a, 'b) rel"
    ("(if\<^sub>\<C> (_)/ then\<^sub>\<C> (_)/ else\<^sub>\<C> (_))" [0, 0, 10] 10)

translations "if\<^sub>\<C> b then\<^sub>\<C> P else\<^sub>\<C> Q" \<rightleftharpoons> "P \<triangleleft> b \<triangleright>\<^sub>r Q"

subsection {* Iterated Constructs *}

text {* In this section, we define various iterated constructs. *}

subsubsection {* Iterated Interleaving *}

primrec interleave_iter ::
  "'a list \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<phi>) action) \<Rightarrow> ('\<sigma>, '\<phi>) action" where
"interleave_iter [] f = Skip" |
"interleave_iter (h # t) f = (f h) ||| (interleave_iter t f)"

syntax "_interleave_iter_iter" ::
  "pttrn \<Rightarrow> 'a list \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action"
  ("(3||| _ : _ \<bullet>/ _)" [0, 0, 10] 10)

translations "||| x : l \<bullet> P" \<rightleftharpoons> "(CONST interleave_iter) l (\<lambda>x. P)"

subsection {* Proof Experiments *}

text {* Make the below a default simplification! [TODO] *}

declare mu_const [simp]

lemma mu_CSP_const [simp]:
"(\<mu>\<^sub>C X \<bullet> P) = P"
apply (unfold comp_def)
apply (simp only: mu_const)
done

theorem
"process P \<triangleq> begin A = Act1 and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = Process (Main (Act1, Act2 ;; Act1))"
apply (unfold circus_syntax)
apply (unfold Let_def) -- {* \todo{How to apply the copy rule selectively?!} *}
apply (simp add: o_def)
done

theorem
"process P \<triangleq> begin state(vstore) A = Act1 and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = ProcessSt TYPE(vstore) (Main (Act1, Act2 ;; Act1))"
apply (unfold circus_syntax)
apply (unfold Let_def) -- {* \todo{How to apply the copy rule selectively?!} *}
apply (simp add: o_def)
done

theorem
"process P(x::nat) \<triangleq> begin state('\<sigma>) A = Act1 x and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = (\<lambda>x. ProcessSt TYPE('\<sigma>) (Main (Act1 x, Act2 ;; Act1 x)))"
apply (unfold circus_syntax)
apply (unfold Let_def) -- {* \todo{How to apply the copy rule selectively?!} *}
apply (simp add: o_def)
done

subsection {* Supplementary Laws *}

lemma all_true [simp]:
"(\<forall> x \<bullet> true) = true"
apply(pred_auto)
done

text \<open>Simplification laws for processes with the same state type.\<close>

lemma Process_eq_simp:
"(Process P = Process Q) \<longleftrightarrow>
  ((\<exists> {$st, $st\<acute>} \<bullet> P) = (\<exists> {$st, $st\<acute>} \<bullet> Q))"
apply (unfold Process_def)
apply (unfold hide_state_def)
apply (rel_simp)
done

lemma Process_ref_simp:
"(Process P \<sqsubseteq> Process Q) \<longleftrightarrow>
  ((\<exists> {$st, $st\<acute>} \<bullet> P) \<sqsubseteq> (\<exists> {$st, $st\<acute>} \<bullet> Q))"
apply (unfold Process_def)
apply (rel_simp)
done

lemma preR_ex_st_vars [rdes]:
"pre\<^sub>R(\<exists> {$st, $st\<acute>} \<bullet> P) = (\<forall> {$st, $st\<acute>} \<bullet> pre\<^sub>R P)"
apply (rel_auto)
done

lemma periR_ex_st_vars [rdes]:
"peri\<^sub>R(\<exists> {$st, $st\<acute>} \<bullet> P) = (\<exists> {$st, $st\<acute>} \<bullet> peri\<^sub>R P)"
apply (rel_auto)
done

lemma postR_ex_st_vars [rdes]:
"post\<^sub>R(\<exists> {$st, $st\<acute>} \<bullet> P) = (\<exists> {$st, $st\<acute>} \<bullet> post\<^sub>R P)"
apply (rel_auto)
done
end