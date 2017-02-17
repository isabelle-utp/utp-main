(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus.thy                                                       *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 8 Feb 2017 *)

section {* Theory of {\Circus} *}

theory utp_circus
imports utp_csp utp_avar
begin

subsection {* Process Semantics *}

text {*
  An open issue is whether we should contract the alphabet as well i.e.~to
  the type @{type unit}. Since we use deep (or axiomatic) variables, we can
  strictly get away without that. But it might be more accurate in terms of
  the semantics of \emph{Circus} processes. I talked to Simon Foster about
  this who then added definitions that are necessary to carry out alphabet
  restrictions of program-state alphabets within various UTP theories.
*}

-- {* \todo{Additionally perform an alphabet restriction below.} *}

definition Process ::
  "('\<epsilon>, '\<alpha>) hrelation_csp \<Rightarrow>
   ('\<epsilon>, '\<alpha>) hrelation_csp" where
"Process p = (\<exists> \<Sigma>\<^sub>C\<^sub>x\<^sub>C \<bullet> p) (*\<restriction>\<^sub>p \<Sigma>\<^sub>C\<^sub>x\<^sub>C*)"

definition Action ::
  "('\<epsilon>, '\<alpha>) hrelation_csp \<Rightarrow>
  (('\<epsilon>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<epsilon>, '\<alpha>) hrelation_csp) \<Rightarrow>
  ('\<epsilon>, '\<alpha>) hrelation_csp" where
"Action = Let"

definition RecAction ::
  "(('\<epsilon>, '\<alpha>) hrelation_csp \<Rightarrow>
    ('\<epsilon>, '\<alpha>) hrelation_csp \<times> ('\<epsilon>, '\<alpha>) hrelation_csp) \<Rightarrow>
  ('\<epsilon>, '\<alpha>) hrelation_csp" where
"RecAction act_body =
  Action (SUPREMUM UNIV (\<lambda>X. fst (act_body X))) (\<lambda>X. snd (act_body X))"

lemmas circus_syntax =
  Process_def Action_def RecAction_def

subsection {* Process Syntax *}

nonterminal action and actions

syntax
  "_Action"  :: "[pttrn, 'a] \<Rightarrow> action"        ("(2_ =/ _)" 10)
  ""         :: "action \<Rightarrow> actions"            ("_")
  "_Actions" :: "[action, actions] \<Rightarrow> actions" ("_and//_")
  "_Process" :: "[actions, 'a] \<Rightarrow> 'a"          ("((2begin//(_)//\<bullet> (_))//end)")
  "_ParamProcDef" :: "idt \<Rightarrow> args \<Rightarrow> 'a \<Rightarrow> bool" ("(process _ _ \<triangleq>//_)" [0, 0, 10] 10)
  "_BasicProcDef" :: "idt \<Rightarrow> 'a \<Rightarrow> bool"         ("(process _ \<triangleq>//_)" [0, 10] 10)

syntax (output)
  "_Actions_tr'"   :: "[action, actions] \<Rightarrow> actions"  ("_//_")

translations
  "_Process (_Actions act acts) e" \<rightharpoonup> "_Process act (_Process acts e)"
  "_Process (_Actions_tr' act acts) e" \<leftharpoondown> "_Process act (_Process acts e)"
(* "_Process (_Action name act) more" \<rightleftharpoons> "(CONST Action) act (\<lambda>name. more)" *)
  "_Process (_Action name act) more" \<rightleftharpoons> "(CONST RecAction) (\<lambda>name. (act, more))"
  "_ParamProcDef name args body" \<rightleftharpoons> "name = (\<lambda>args. (CONST Process) body)"
  "_BasicProcDef name      body" \<rightleftharpoons> "name = (CONST Process) body"

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr'
    @{const_syntax Action} @{syntax_const "_Action"}]
*}

subsection {* Substitution *}

definition subst_upd_avar ::
  "('\<alpha>::ust, '\<beta>) psubst \<Rightarrow>
    'a::injectable uvar.var \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>, '\<beta>) psubst" where
"subst_upd_avar ss v e = (\<lambda>\<sigma>. ss (put\<^bsub>avar\<^sub>L v\<^esub> \<sigma> (\<lbrakk>e\<rbrakk>\<^sub>e\<sigma>)))"

adhoc_overloading subst_upd subst_upd_avar

subsection {* Instantiations *}

instantiation alpha_d_ext :: (ust) ust
begin
definition ust_lens_alpha_d_ext :: "ustate \<Longrightarrow> 'a alphabet_d" where
"ust_lens_alpha_d_ext = ust\<^sub>L ;\<^sub>L \<Sigma>\<^sub>D"
instance
apply (intro_classes)
apply (unfold ust_lens_alpha_d_ext_def)
apply (simp)
done
end

instantiation alpha_rp'_ext :: (ordered_cancel_monoid_diff, ust) ust
begin
definition ust_lens_alpha_rp'_ext ::
  "ustate \<Longrightarrow> ('a, 'b) alpha_rp'_scheme" where
"ust_lens_alpha_rp'_ext = ust\<^sub>L ;\<^sub>L \<Sigma>\<^sub>r"
instance
apply (intro_classes)
apply (unfold ust_lens_alpha_rp'_ext_def)
apply (simp)
done
end

instantiation alpha_csp'_ext :: (type, ust) ust
begin
definition ust_lens_alpha_csp'_ext ::
  "ustate \<Longrightarrow> ('a, 'b) alpha_csp'_scheme" where
"ust_lens_alpha_csp'_ext = ust\<^sub>L ;\<^sub>L \<Sigma>\<^sub>c"
instance
apply (intro_classes)
apply (unfold ust_lens_alpha_csp'_ext_def)
apply (simp)
done
end

subsection {* Proof Experiments *}

theorem
"process P \<triangleq> begin A = Act1 and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = Process (Main (Act1, Act2 ;; Act1))"
apply (unfold circus_syntax)
apply (unfold Let_def) -- {* \todo{How to apply the copy rule selectively?!} *}
apply (clarsimp)
done

theorem
"process P(x::nat) \<triangleq> begin A = Act1 x and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = (\<lambda>x. Process (Main (Act1 x, Act2 ;; Act1 x)))"
apply (unfold circus_syntax)
apply (unfold Let_def) -- {* \todo{How to apply the copy rule selectively?!} *}
apply (clarsimp)
done
end