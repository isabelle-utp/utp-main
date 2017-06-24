(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus.thy                                                       *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 23 June 2017 *)

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

lemma Process_eq_simp:
"(Process P = Process Q) \<longleftrightarrow>
  ((\<exists> {$st,$st\<acute>} \<bullet> P) = (\<exists> {$st,$st\<acute>} \<bullet> Q))"
apply (unfold Process_def)
apply (unfold hide_state_def)
apply (rel_simp)
done

lemma Process_ref_simp:
"(Process P \<sqsubseteq> Process Q) \<longleftrightarrow>
  ((\<exists> {$st,$st\<acute>} \<bullet> P) \<sqsubseteq> (\<exists> {$st,$st\<acute>} \<bullet> Q))"
apply (unfold Process_def)
apply (unfold hide_state_def)
apply (rel_simp)
done

lemma Process_eqI:
"((\<exists> {$st,$st\<acute>} \<bullet> P) = (\<exists> {$st,$st\<acute>} \<bullet> Q)) \<Longrightarrow> (Process P = Process Q)"
apply (unfold Process_eq_simp)
apply (assumption)
done

lemma Process_refI:
"((\<exists> {$st,$st\<acute>} \<bullet> P) \<sqsubseteq> (\<exists> {$st,$st\<acute>} \<bullet> Q)) \<Longrightarrow> (Process P \<sqsubseteq> Process Q)"
apply (unfold Process_ref_simp)
apply (assumption)
done

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
  Action (\<mu> X \<bullet> fst (act_body X)) (\<lambda>X. snd (act_body X))"

lemmas circus_syntax =
  Process_def ProcessSt_def Action_def RecAction_def

subsection {* Process Syntax *}

nonterminal state and action and actions and process

text {*
  We support both basic and composite process definitions. Moreover, processes
  may be parametrised and can include an option state paragraph which must be
  of the form @{text "state('\<sigma>)"}, where @{typ "'\<sigma>"} is a HOL type to be used
  for the state space. If no state paragraph is given, it is inferred by type
  checking. Parametrised actions are current not supported - this is work in
  progress. For examples, see the bottom of the theory.
*}

syntax
  "_State" :: "type \<Rightarrow> state"                  ("state'(_')")
  "_Action"  :: "[pttrn, logic] \<Rightarrow> action"     ("(2_ =/ _)" 10)
  ""         :: "action \<Rightarrow> actions"            ("_")
  "_Actions" :: "[action, actions] \<Rightarrow> actions" ("_and//_")
  "_ProcBody" :: "[actions, logic] \<Rightarrow> process" ("((2begin//(_)//\<bullet> (_))//end)")
  "_ProcBodySt" :: "[state, actions, logic] \<Rightarrow> process" ("((2begin//(_)//(_)//\<bullet> (_))//end)")
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
  (state) "state('type)" \<rightleftharpoons> "TYPE('type)"
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

purge_syntax
  "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" ("!'(_')")
  "_output_prefix" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem'" (".'(_')")

consts ParCircus ::
  "('\<sigma>, '\<phi>) action  \<Rightarrow> ('\<phi> event set) \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow>
   ('\<sigma>, '\<phi>) action" (infixl "[|(_)|]" 60)

definition InterleaveCircus ::
  "('\<sigma>, '\<phi>) action  \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow>
   ('\<sigma>, '\<phi>) action" (infixl "|||" 62) where
"P ||| Q = P [| {} |] Q"

consts HideCircus ::
  "('\<sigma>, '\<phi>) action  \<Rightarrow> ('\<phi> event set) \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\\" 55)

consts InterruptCircus ::
  "('\<sigma>, '\<phi>) action  \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\<triangle>" 100)

subsection {* Input Prefix (OLD) *}

(*
definition do\<^sub>I :: "
  ('a, '\<epsilon>) chan \<Rightarrow>
  ('a \<Longrightarrow> ('\<sigma>, '\<epsilon>) st_csp) \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
  ('\<sigma>, '\<epsilon>) action" where
"do\<^sub>I c x P =
  (($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>$x\<acute>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>)))"
*)

definition InputCircus ::
  "('a::{continuum, two}, '\<epsilon>) chan \<Rightarrow>
    ('a, ('\<sigma>, '\<epsilon>) st_csp) lvar \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    (('a \<Longrightarrow> ('\<sigma>, '\<epsilon>) st_csp) \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('\<sigma>, '\<epsilon>) action" where
"InputCircus c x P A =
  (var\<^bsub>RDES\<^esub> x \<bullet> \<^bold>R\<^sub>s(true \<turnstile> (do\<^sub>I c x P) \<and> (\<exists> $x\<acute> \<bullet> II)) ;; A(x))"

text {* A few syntactic adjustments, remove them and adapt @{text "fmi.thy"}. *}

no_notation utp_rel_opsem.trel (infix "\<rightarrow>\<^sub>u" 85)

syntax
  "_circus_sync" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<rightarrow>\<^sub>u" 80)
  "_circus_input" :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"
    ("_?\<^sub>u'(_ :/ _') \<rightarrow> _" [81, 0, 0, 80] 80)
  "_circus_output" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"
    ("_!\<^sub>u'(_') \<rightarrow> _" [81, 0, 80] 80)

translations
  "c \<rightarrow>\<^sub>u A" \<rightleftharpoons> "(CONST OutputCSP) c ()\<^sub>u A"
  "c!\<^sub>u(v) \<rightarrow> A" \<rightleftharpoons> "(CONST OutputCSP) c v A"
  "c?\<^sub>u(x : P) \<rightarrow> A" \<rightharpoonup> "(CONST InputCircus) c
    (*(CONST top_var \<dots>*) (CONST MkDVar IDSTR(x)) (\<lambda>x. P) (\<lambda>x. A)"
  "c?\<^sub>u(x : P) \<rightarrow> A" \<leftharpoondown> "(CONST InputCircus) c x (\<lambda>v. P) (\<lambda>w. A)"

subsection {* Mixed Prefixes *}

text {* In this section, we provide support for mixed prefixes. *}

(*
syntax
  "_circus_sync" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow> _" [81, 80] 80)
  "_circus_output" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"
    ("_!\<^sub>u'(_') \<rightarrow> _" [81, 0, 80] 80)
  "_circus_input"  :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"
    ("_?\<^sub>u'(_ :/ _') \<rightarrow> _" [81, 0, 0, 80] 80)
*)
(*
no_translations
  "c \<^bold>\<rightarrow> A"      \<leftharpoondown> "(CONST OutputCSP) c ()\<^sub>u A"
  "c!\<^sub>u(v) \<rightarrow> A" \<leftharpoondown> "(CONST OutputCSP) c v A"
*)

subsubsection {* Prefix Semantics *}

text {*
  We first define a new and simplified version of the @{const InputCircus}
  operator. Simplification is due to its action argument being parametrised
  by the a (HOL) value rather than a variable lens. This makes a subsequent
  definition of syntax and translations for mixed prefixes much easier. We
  note that all different kinds of prefixes will be expressed in terms of
  input communications with appropriate constraints on variables that are
  introduced by the prefix construct.
*}

definition new_do\<^sub>I :: "
  ('a, '\<epsilon>) chan \<Rightarrow> 'a \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
  ('\<sigma>, '\<epsilon>) action" where
"new_do\<^sub>I c x P =
  (($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>)))"

definition new_do\<^sub>I' :: "
  ('a, '\<epsilon>) chan \<Rightarrow> 'a \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
  ('\<sigma>, '\<epsilon>) action" where
"new_do\<^sub>I' c x P =
  (($tr\<acute> =\<^sub>u $tr \<and> (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute>) \<triangleleft> $wait\<acute> \<triangleright> (($tr\<acute> - $tr) =\<^sub>u \<langle>(c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>))"

definition NewInputCircus ::
  "('a, '\<epsilon>) chan \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('\<sigma>, '\<epsilon>) action" where
"NewInputCircus c P A = (\<^bold>\<exists> x \<bullet> \<^bold>R\<^sub>s(true \<turnstile> (new_do\<^sub>I c x P) \<and> II) ;; A(x))"

definition NewInputCircus' ::
  "('a, '\<epsilon>) chan \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('\<sigma>, '\<epsilon>) action" where
"NewInputCircus' c P A = (\<^bold>\<exists> x \<bullet> \<^bold>R\<^sub>s(true \<turnstile> (new_do\<^sub>I' c x P) \<and> II) ;; A(x))"

lemma "NewInputCircus = NewInputCircus'"
apply (rule ext)+
apply (unfold NewInputCircus_def NewInputCircus'_def)
apply (unfold new_do\<^sub>I_def new_do\<^sub>I'_def)
-- {* TODO: Allow simplification theorems to be passed to rel\_simp. *}
apply (rel_simp)
apply (safe; clarsimp?)
apply (blast)
apply (simp_all add: zero_list_def)    
apply (blast)
apply (metis)
apply (metis)
apply (blast)
apply (blast)
apply (metis)+
done

(* Need to figure out how to state the law below... ?! *)

lemma
"vwb_lens x \<Longrightarrow> NewInputCircus c P A = InputCircus c x P B"
apply (unfold NewInputCircus_def InputCircus_def)
apply (unfold new_do\<^sub>I_def do\<^sub>I_def chan_type_def)
apply (rel_simp)
apply (safe; clarsimp simp add: comp_def)
oops

subsubsection {* Syntax and Translations *}

text {* We next configure a syntax for mixed prefixes. *}

nonterminal prefix_elem and mixed_prefix

syntax "" :: "prefix_elem \<Rightarrow> mixed_prefix" ("_")

text {* Input Prefix: @{text "\<dots>?(x)"} *}

syntax "_simple_input_prefix" :: "id \<Rightarrow> prefix_elem"  ("?'(_')")

text {* Input Prefix with Constraint: @{text "\<dots>?(x : P)"} *}

syntax "_input_prefix" :: "id \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> prefix_elem" ("?'(_ :/ _')")

text {* Output Prefix: @{text "\<dots>![v]e"} *}

text {* A variable name must currently be provided for outputs, too. Fix?! *}

syntax "_output_prefix" :: "id \<Rightarrow> ('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem" ("![_]_")
syntax "_output_prefix" :: "id \<Rightarrow> ('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem" (".[_]_")

syntax (output) "_output_prefix_pp" :: "('a, '\<sigma>) uexpr \<Rightarrow> prefix_elem" ("!_")

text {* Synchronisation Action: @{text "c \<rightarrow>\<^sub>\<C> A"} *}

syntax "_sync_action" ::
  "('a, '\<epsilon>) chan \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> ('\<sigma>, '\<epsilon>) action" (infixr "\<rightarrow>\<^sub>\<C>" 80)

text {* Mixed-Prefix Action: @{text "c\<dots>(prefix) \<rightarrow>\<^sub>\<C> A"} *}

syntax "_mixed_prefix" :: "prefix_elem \<Rightarrow> mixed_prefix \<Rightarrow> mixed_prefix" ("__")

syntax "_prefix_action" ::
  "('a, '\<epsilon>) chan \<Rightarrow> mixed_prefix \<Rightarrow> ('\<sigma>, '\<epsilon>) action \<Rightarrow> ('\<sigma>, '\<epsilon>) action"
  ("(__ \<rightarrow>\<^sub>\<C>/ _)" [81, 81, 80] 80)

text {* Syntax translations *}

translations
  "_simple_input_prefix x" \<rightleftharpoons> "_input_prefix x true"
  "_output_prefix x e" \<rightharpoonup> "_input_prefix x (\<guillemotleft>x\<guillemotright> =\<^sub>u e)"
  "_output_prefix_pp e" \<leftharpoondown> "_input_prefix v (\<guillemotleft>x\<guillemotright> =\<^sub>u e)" (* Better do in ML! *)

translations
  "_mixed_prefix (_input_prefix x P) (_input_prefix y Q)" \<rightleftharpoons>
  "_input_prefix (_pattern x y) (P \<and> Q)"

translations
  "_sync_action c A" \<rightleftharpoons> "(CONST OutputCSP) c ()\<^sub>u A"
  "_prefix_action c (_input_prefix x P) A"  \<rightharpoonup>
  "(CONST NewInputCircus) c (\<lambda>x. P) (\<lambda>x. A)"
(* "_prefix_action c (_input_prefix x P) A"  \<leftharpoondown>
  "(CONST NewInputCircus) c (\<lambda>x. P) (\<lambda>v. A)" *)

text {*
  The ML print translation for @{const NewInputCircus} below is a little more
  robust than using Isabelle in-built @{command translations} in dealing with
  unwanted eta-contraction.
*}

ML {*
signature CIRCUS_PREFIX =
sig
  val mk_pattern: term list -> term
  val strip_abs_tr': term list -> term -> term list * term
  val mk_input_prefix: term -> term -> term
  val mk_prefix_action: term -> term -> term -> term -> term
  val InputCircus_tr': term list -> term
end;

structure Circus_Prefix : CIRCUS_PREFIX =
struct
  fun mk_pattern [] = Const (@{syntax_const "_unit"}, dummyT)
  | mk_pattern [x] = x
  | mk_pattern (h :: t) =
    Const (@{syntax_const "_pattern"}, dummyT) $ h $ (mk_pattern t);

  fun strip_abs_tr' vs (Abs abs) =
    let val (v, body) = Syntax_Trans.atomic_abs_tr' abs in
      strip_abs_tr' (vs @ [v]) body
    end
  | strip_abs_tr' vs
      (Const (@{const_syntax case_prod}, _) $ (Abs abs)) =
    let val (v, body) = Syntax_Trans.atomic_abs_tr' abs in
      strip_abs_tr' (vs @ [v]) body
    end
  | strip_abs_tr' vs term = (vs, term);

  fun mk_input_prefix x P =
    Const (@{syntax_const "_input_prefix"}, dummyT) $ x $ P;

  fun mk_prefix_action c x P A =
    Const (@{syntax_const "_prefix_action"}, dummyT) $ c $
      (mk_input_prefix x P) $ A;

  fun InputCircus_tr' [c, P, A] = let
    val (vs, P') = strip_abs_tr' [] P;
    val (vs', A') = strip_abs_tr' [] A in
      if (vs = vs') then
        (mk_prefix_action c (mk_pattern vs) P' A')
      else raise Match
    end
  | InputCircus_tr' _ = raise Match;
end;
*}

print_translation {*
  [(@{const_syntax NewInputCircus}, K Circus_Prefix.InputCircus_tr')]
*}

text {* Testing *}

text {* All of the below seem to work! *}

term "c?(x : true) \<rightarrow>\<^sub>\<C> A x"
term "c?(x : true)?(y : true) \<rightarrow>\<^sub>\<C> A x y"
term "c?(x : true)?(y : true)?(z : true) \<rightarrow>\<^sub>\<C> A x y z"
term "c?(x : \<guillemotleft>x\<guillemotright> <\<^sub>u \<guillemotleft>10::nat\<guillemotright>) \<rightarrow>\<^sub>\<C> A x"
term "c?(x)?(y : true) \<rightarrow>\<^sub>\<C> A x y"
term "c?(x : true)![st]\<guillemotleft>1::nat\<guillemotright> \<rightarrow>\<^sub>\<C> A x"
term "c![st]\<guillemotleft>1::nat\<guillemotright>?(x : true) \<rightarrow>\<^sub>\<C> A x"
term "c![st]\<guillemotleft>1::nat\<guillemotright> \<rightarrow>\<^sub>\<C> A"
term "c![x]\<guillemotleft>1::nat\<guillemotright>![y]\<guillemotleft>2::nat\<guillemotright> \<rightarrow>\<^sub>\<C> A"
term "c \<rightarrow>\<^sub>\<C> A"

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

declare utp_recursion.mu_const [simp]

theorem
"process P \<triangleq> begin A = Act1 and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = Process (Main (Act1, Act2 ;; Act1))"
apply (unfold circus_syntax)
apply (unfold Let_def) -- {* \todo{How to apply the copy rule selectively?!} *}
apply (clarsimp)
done

theorem
"process P \<triangleq> begin state(vstore) A = Act1 and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = ProcessSt TYPE(vstore) (Main (Act1, Act2 ;; Act1))"
apply (unfold circus_syntax)
apply (unfold Let_def) -- {* \todo{How to apply the copy rule selectively?!} *}
apply (clarsimp)
done

theorem
"process P(x::nat) \<triangleq> begin state('\<sigma>) A = Act1 x and B = (Act2 ;; A) \<bullet> Main(A, B) end \<Longrightarrow>
 P = (\<lambda>x. ProcessSt TYPE('\<sigma>) (Main (Act1 x, Act2 ;; Act1 x)))"
apply (unfold circus_syntax)
apply (unfold Let_def) -- {* \todo{How to apply the copy rule selectively?!} *}
apply (clarsimp)
done
end