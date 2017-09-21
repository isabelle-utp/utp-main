(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus.thy                                                       *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 20 Sep 2017 *)

section {* Theory of {\Circus} *}

theory utp_circus
imports utp_circus_prel
begin

text {* The below cause ambiguities wrt the corresponding CSP definitions. *}

hide_const utp_cml.Skip
hide_const utp_cml.Stop

subsection {* Process Semantics *}

text {*
  We could get away without the hiding of the state alphabet if we assume that
  all processes have the same state type. The lemmas we prove in {\Circus} laws
  section establish this and may be useful in proofs. It is still an open issue
  to what extent the hiding of the state alphabet poses challenges in proofs.
*}

definition Process ::
  "('\<sigma>, '\<phi>) action \<Rightarrow>
   (unit, '\<phi>) action" where
"Process P = state '\<sigma> \<bullet> P"

definition ProcessSt ::
  "('\<sigma> itself) \<Rightarrow>
   ('\<sigma>, '\<phi>) action \<Rightarrow>
   (unit, '\<phi>) action" where
"ProcessSt t P = Process P"

definition LocalAction ::
  "('\<sigma>, '\<phi>) action \<Rightarrow>
   (('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action) \<Rightarrow>
   ('\<sigma>, '\<phi>) action" where
"LocalAction = Let"

definition RecAction ::
  "(('\<sigma>, '\<phi>) action \<Rightarrow>
    ('\<sigma>, '\<phi>) action \<times> ('\<sigma>, '\<phi>) action) \<Rightarrow>
   ('\<sigma>, '\<phi>) action" where
"RecAction body =
  LocalAction (\<mu>\<^sub>C X \<bullet> fst (body X)) (\<lambda>X. snd (body X))"

lemmas circus_syntax =
  Process_def ProcessSt_def LocalAction_def RecAction_def

declare circus_syntax [rdes]

subsection {* Process Syntax *}

nonterminal p_state and action and actions and process

text {*
  We support both basic and composite process definitions. Moreover, processes
  may be parametrised and can include an optional state paragraph which must be
  of the form \<open>state('\<sigma>)\<close>, where @{typ "'\<sigma>"} is the HOL type to be used for the
  state space. If no state paragraph is given, it is inferred by type checking.
  Parametrised actions are current not supported - this is a work in progress.
*}

syntax
  "_State" :: "type \<Rightarrow> p_state"                ("state'(_')")
  "_Action"  :: "[pttrn, logic] \<Rightarrow> action"     ("(2_ =/ _)" 10)
  ""         :: "action \<Rightarrow> actions"            ("_")
  "_Actions" :: "[action, actions] \<Rightarrow> actions" ("_and//_")
  "_ProcBody" :: "[actions, logic] \<Rightarrow> process" ("((2begin//(_)//\<bullet> (_))//end)")
  "_ProcBodySt" :: "[p_state, actions, logic] \<Rightarrow> process" ("((2begin//(_)//(_)//\<bullet> (_))//end)")
  "_BasicProc" :: "idt \<Rightarrow> process \<Rightarrow> bool"     ("(process _ \<triangleq>//_)" [0, 10] 10)
  "_BasicDefn" :: "idt \<Rightarrow> logic   \<Rightarrow> bool"     ("(process _ \<triangleq>//_)" [0, 10] 10)
  "_ParamProc" :: "idt \<Rightarrow> args \<Rightarrow> process \<Rightarrow> bool" ("(process _ _ \<triangleq>//_)" [0, 0, 10] 10)
  "_ParamDefn" :: "idt \<Rightarrow> args \<Rightarrow> logic   \<Rightarrow> bool" ("(process _ _ \<triangleq>//_)" [0, 0, 10] 10)
  "_BasicProcSt" :: "idt \<Rightarrow> type \<Rightarrow> process \<Rightarrow> bool"
  "_ParamProcSt" :: "idt \<Rightarrow> args \<Rightarrow> type \<Rightarrow> process \<Rightarrow> bool"

syntax (output) -- {* Cosmetics *}
  "_Actions_tr'" :: "[action, actions] \<Rightarrow> actions"  ("_//_")

text {*
  Interestingly, it does make a difference whether we split translations into
  separate blocks of @{command translations} statements. Isabelle seems to
  respect the order of translations only when they are included in the same
  block. Here, the order is very important.
*}

translations
  (p_state) "state('type)" \<rightleftharpoons> "TYPE('type)"
-- \<open>Shift the type argument from ProcBodySt into (Basic/Param)ProcSt.\<close>
  "_BasicProc name (_ProcBodySt type actions main)" \<rightleftharpoons>
  "_BasicProcSt name type (_ProcBody actions main)"
  "_ParamProc name args (_ProcBodySt type actions main)" \<rightleftharpoons>
  "_ParamProcSt name args type (_ProcBody actions main)"
  "_ProcBody (_Actions     act acts) e" \<rightharpoonup> "_ProcBody act (_ProcBody acts e)"
  "_ProcBody (_Actions_tr' act acts) e" \<leftharpoondown> "_ProcBody act (_ProcBody acts e)"
(*"_ProcBody (_Action name act) more" \<rightleftharpoons> "(CONST LocalAction) act (\<lambda>name. more)"*)
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
    @{const_syntax LocalAction} @{syntax_const "_Action"}]
*}

text {* Hide non-terminals as this interferes with parsing the action type. *}

hide_type (open)
  utp_circus.action
  utp_circus.actions

subsection {* {\Circus} Constructs *}

text {*
  The semantics of some of the constructs still needs to be defined, namely of
  channel hiding and {\Circus} interrupt. With regards to iterated sequence,
  it is an open issue whether we require a {\Circus}-specific version of it.
  In syntactic terms, perhaps make parallel composition bind weaker than set
  union so that the latter can be used to combine channel sets. Precedence of
  operators in Isabelle/UTP is still an issue in general that may need to be
  look at more carefully.
*}

subsubsection {* Channel Hiding *}

text {* \todo{Define the semantics of this operator and prove relevant laws.} *}

consts HideCircus ::
  "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<phi> event set) \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\\" 55)

subsubsection {* {\Circus} Interrupt *}

text {* \todo{Define the semantics of this operator and prove relevant laws.} *}

consts IntCircus ::
  "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\<triangle>" 100)

subsubsection {* Iterated Sequence *}

definition seqc_iter ::
  "'a list \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<phi>) action) \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[urel_defs]: "seqc_iter xs body = foldr (\<lambda>x A. body(x) ;; A) xs Skip"

syntax "_seqc_iter" ::
  "pttrn \<Rightarrow> 'a list \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action"
  ("(3;;\<^sub>C _ : _ \<bullet>/ _)" [0, 0, 10] 10)

translations
  ";;\<^sub>C x : xs \<bullet> P" \<rightleftharpoons> "(CONST seqc_iter) xs (\<lambda>x. P)"

-- {* Prevent eta-contraction for robust pretty-printing. *}

print_translation {*
 [Syntax_Trans.preserve_binder_abs2_tr'
   @{const_syntax seqc_iter} @{syntax_const "_seqc_iter"}]
*}

lemma seqc_iter_simps [simp]:
"(;;\<^sub>C x : [] \<bullet> P x) = Skip"
"(;;\<^sub>C x : (x # xs) \<bullet> P x) = P x ;; (;;\<^sub>C x : xs \<bullet> P x)"
apply (unfold seqc_iter_def)
apply (simp_all)
done

lemma seqc_iter_singleton [simp]:
"(P c) is CSP4 \<Longrightarrow> (;;\<^sub>C x : [c] \<bullet> P x) = P c"
apply (unfold seqc_iter_def)
apply (simp)
apply (metis CSP4_def Healthy_if)
done

subsubsection {* Iterated Interleaving *}

primrec interleave_iter ::
  "'a list \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<phi>) action) \<Rightarrow> ('\<sigma>, '\<phi>) action" where
"interleave_iter [] body = Skip" |
"interleave_iter (x # xs) body = (body x) ||| (interleave_iter xs body)"

syntax "_interleave_iter" ::
  "pttrn \<Rightarrow> 'a list \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action"
  ("(3||| _ : _ \<bullet>/ _)" [0, 0, 10] 10)

syntax "_interleave_iter_alt" ::
  "pttrn \<Rightarrow> 'a list \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action"
  ("(3'(||| _ : _ \<bullet>/ _'))" [0, 0, 10])

translations
  "( ||| x : xs \<bullet> P)" \<rightharpoonup> "(CONST interleave_iter) xs (\<lambda>x. P)"
  "(||| x : xs \<bullet> P)" \<rightleftharpoons> "(CONST interleave_iter) xs (\<lambda>x. P)"

-- {* Prevent eta-contraction for robust pretty-printing. *}

print_translation {*
 [Syntax_Trans.preserve_binder_abs2_tr'
   @{const_syntax interleave_iter} @{syntax_const "_interleave_iter"}]
*}

lemma interleave_iter_simps [simp]:
"(||| x : [] \<bullet> P x) = Skip"
"(||| x : (x # xs) \<bullet> P x) = P x ||| (||| x : xs \<bullet> P x)"
apply (unfold interleave_iter_def)
apply (simp_all)
done

lemma interleave_iter_singleton [simp]:
"(P c) is CSP5 \<Longrightarrow> (||| x : [c] \<bullet> P x) = P c"
apply (simp)
apply (metis CSP5_def Healthy_if)
done

subsubsection {* Iterated Parallel *}

primrec parallel_iter :: "'a list \<Rightarrow> ('a \<Rightarrow> ('\<phi> set \<times> ('\<sigma>, '\<phi>) action)) \<Rightarrow>
  ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" where
"parallel_iter [] cs_body env = env" |
"parallel_iter (x # xs) cs_body env =
  snd (cs_body x) \<lbrakk>fst (cs_body x)\<rbrakk>\<^sub>C (parallel_iter xs cs_body env)"

syntax "_parallel_iter" :: "pttrn \<Rightarrow>
  'a list \<Rightarrow> '\<phi> set \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action"
  ("(3|| _ : _ \<bullet>/ [_] _ | _)" [0, 0, 0, 0, 10] 10)

syntax "_parallel_iter" :: "pttrn \<Rightarrow>
  'a list \<Rightarrow> '\<phi> set \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action"
  ("(3'(|| _ : _ \<bullet>/ [_] _ | _'))" [0, 0, 0, 0, 10])

syntax "_parallel_iter_noenv" :: "pttrn \<Rightarrow>
  'a list \<Rightarrow> '\<phi> set \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action"
  ("(3|| _ : _ \<bullet>/ [_] _)" [0, 0, 0, 10] 10)

syntax "_parallel_iter_noenv" :: "pttrn \<Rightarrow>
  'a list \<Rightarrow> '\<phi> set \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action"
  ("(3'(|| _ : _ \<bullet>/ [_] _'))" [0, 0, 0, 10])

translations
  "( || x : xs \<bullet> [cs] P | Env)" \<rightharpoonup> "(CONST parallel_iter) xs (\<lambda>x. (cs, P)) Env"
  "(|| x : xs \<bullet> [cs] P | Env)" \<rightleftharpoons> "(CONST parallel_iter) xs (\<lambda>x. (cs, P)) Env"

translations
  "( || x : xs \<bullet> [cs] P)" \<rightharpoonup> "(CONST parallel_iter) xs (\<lambda>x. (cs, P)) (CONST Skip)"
  "(|| x : xs \<bullet> [cs] P)" \<rightleftharpoons> "(CONST parallel_iter) xs (\<lambda>x. (cs, P)) (CONST Skip)"

-- {* \todo{How to prevent eta-contraction for robust pretty-printing here?} *}

lemma parallel_iter_simps [simp]:
"(|| x : [] \<bullet> [cs x] P x | Env) = Env"
"(|| x : (x # xs) \<bullet> [cs x] P x | Env) =
  P x \<lbrakk>cs x\<rbrakk>\<^sub>C  (|| x : xs \<bullet> [cs x] P x | Env)"
apply (simp_all)
done

subsection {* {\Circus} Laws *}

text {* Make the below a default simplification in @{theory utp_recursion}! *}

declare mu_const [simp]

lemma mu_CSP_const [simp]:
"(\<mu>\<^sub>C X \<bullet> P) = P"
apply (unfold comp_def)
apply (rule mu_const)
done

text \<open>Why did I add the law below?!\<close>

lemma all_true [simp]:
"(\<forall> x \<bullet> true) = true"
apply(pred_auto)
done

paragraph \<open>Simplification laws for processes with the same state alphabet.\<close>

text \<open>These are in particular useful for processes with deep/axiomatic states.\<close>

lemma Process_eq_simp:
"(Process P = Process Q) \<longleftrightarrow>
  (\<exists> {$st, $st\<acute>} \<bullet> P) = (\<exists> {$st, $st\<acute>} \<bullet> Q)"
apply (unfold Process_def)
apply (rel_simp)
done

lemma Process_ref_simp:
"(Process P \<sqsubseteq> Process Q) \<longleftrightarrow>
  (\<exists> {$st, $st\<acute>} \<bullet> P) \<sqsubseteq> (\<exists> {$st, $st\<acute>} \<bullet> Q)"
apply (unfold Process_def)
apply (rel_simp)
done

lemma pre_ex_st_dist [rdes]:
"pre\<^sub>R(\<exists> {$st, $st\<acute>} \<bullet> P) = (\<forall> {$st, $st\<acute>} \<bullet> pre\<^sub>R P)"
apply (rel_auto)
done

lemma peri_ex_st_dist [rdes]:
"peri\<^sub>R(\<exists> {$st, $st\<acute>} \<bullet> P) = (\<exists> {$st, $st\<acute>} \<bullet> peri\<^sub>R P)"
apply (rel_auto)
done

lemma post_ex_st_dist [rdes]:
"post\<^sub>R(\<exists> {$st, $st\<acute>} \<bullet> P) = (\<exists> {$st, $st\<acute>} \<bullet> post\<^sub>R P)"
apply (rel_auto)
done

subsection {* Proof Experiments *}

text {* \todo{Tactic to apply the copy rule selectively.} *}

theorem
"process P \<triangleq> begin A = Act1 and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = Process (Main (Act1, Act2 ;; Act1))"
apply (unfold circus_syntax)
apply (unfold Let_def)
apply (simp add: o_def)
done

theorem
"process P \<triangleq> begin state(vstore) A = Act1 and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = ProcessSt TYPE(vstore) (Main (Act1, Act2 ;; Act1))"
apply (unfold circus_syntax)
apply (unfold Let_def)
apply (simp add: o_def)
done

theorem
"process P(x::nat) \<triangleq> begin state('\<sigma>) A = Act1 x and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = (\<lambda>x. ProcessSt TYPE('\<sigma>) (Main (Act1 x, Act2 ;; Act1 x)))"
apply (unfold circus_syntax)
apply (unfold Let_def)
apply (simp add: o_def)
done
end