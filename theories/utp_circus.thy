(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus.thy                                                       *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 21 Mar 2017 *)

section {* Theory of {\Circus} *}

theory utp_circus
imports utp_theories_deep "../utp/models/utp_axm"
begin recall_syntax

text {* Types are not printed correctly, have a chat with Simon Foster. *}

typ "('\<sigma>, '\<epsilon>) st_csp"

text {* Renaming HOL's relation type available. *}

type_synonym 'a relation = "'a Relation.rel"

translations (type) "'a relation" \<rightleftharpoons> (type)"'a Relation.rel"

hide_type Relation.rel -- {* TODO: Let the recall package hide types too! *}

text {* The below interfere with the corresponding CSP definitions. *}

hide_const utp_cml.Skip
hide_const utp_cml.Stop

text {* Move this back to the theory @{theory utp_csp}. *}

definition [lens_defs]: "\<Sigma>\<^sub>C\<^sub>x\<^sub>C = \<Sigma>\<^sub>C \<times>\<^sub>L \<Sigma>\<^sub>C"

subsection {* Channel Event Syntax *}

text {* The bellow is useful to construct synchronisation sets of events. *}

definition events :: "('a, '\<phi>) chan \<Rightarrow> '\<phi> set" ("\<epsilon>'(_')") where
"events c = c ` UNIV"

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
  "('\<epsilon>, '\<alpha>) action \<Rightarrow>
   ('\<epsilon>, '\<alpha>) action" where
"Process p = (\<exists> \<Sigma>\<^sub>C\<^sub>x\<^sub>C \<bullet> p) (*\<restriction>\<^sub>p \<Sigma>\<^sub>C\<^sub>x\<^sub>C*)"

definition Action ::
  "('\<epsilon>, '\<alpha>) action \<Rightarrow>
  (('\<epsilon>, '\<alpha>) action \<Rightarrow> ('\<epsilon>, '\<alpha>) action) \<Rightarrow>
  ('\<epsilon>, '\<alpha>) action" where
"Action = Let"

text {* Instead of using the SUPREMUM we should use a mu below. *}

definition RecAction ::
  "(('\<epsilon>, '\<alpha>) action \<Rightarrow>
    ('\<epsilon>, '\<alpha>) action \<times> ('\<epsilon>, '\<alpha>) action) \<Rightarrow>
  ('\<epsilon>, '\<alpha>) action" where
"RecAction act_body =
  Action (SUPREMUM UNIV (\<lambda>X. fst (act_body X))) (\<lambda>X. snd (act_body X))"

lemmas circus_syntax =
  Process_def Action_def RecAction_def

subsection {* Process Syntax *}

nonterminal action and actions

syntax
  "_Action"  :: "[pttrn, logic] \<Rightarrow> action"     ("(2_ =/ _)" 10)
  ""         :: "action \<Rightarrow> actions"            ("_")
  "_Actions" :: "[action, actions] \<Rightarrow> actions" ("_and//_")
  "_Process" :: "[actions,  logic] \<Rightarrow> logic"   ("((2begin//(_)//\<bullet> (_))//end)")
  "_ParamProc" :: "idt \<Rightarrow> args \<Rightarrow> logic \<Rightarrow> bool" ("(process _ _ \<triangleq>//_)" [0, 0, 10] 10)
  "_BasicProc" :: "idt \<Rightarrow>         logic \<Rightarrow> bool" ("(process _ \<triangleq>//_)" [0, 10] 10)

syntax (output)
  "_Actions_tr'"   :: "[action, actions] \<Rightarrow> actions"  ("_//_")

translations
  "_Process (_Actions act acts) e" \<rightharpoonup> "_Process act (_Process acts e)"
  "_Process (_Actions_tr' act acts) e" \<leftharpoondown> "_Process act (_Process acts e)"
(* "_Process (_Action name act) more" \<rightleftharpoons> "(CONST Action) act (\<lambda>name. more)" *)
  "_Process (_Action name act) more" \<rightleftharpoons> "(CONST RecAction) (\<lambda>name. (act, more))"
  "_ParamProc name args body" \<rightleftharpoons> "name = (\<lambda>args. (CONST Process) body)"
  "_BasicProc name      body" \<rightleftharpoons> "name = (CONST Process) body"

print_translation {*
  [Syntax_Trans.preserve_binder_abs2_tr'
    @{const_syntax Action} @{syntax_const "_Action"}]
*}

text {* Hide non-terminals as this interferes with parsing the action type. *}

hide_type (open)
  utp_circus.action
  utp_circus.actions

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
  ('a, ('\<sigma>, '\<epsilon>) st_csp) uvar \<Rightarrow>
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
    (('a, ('\<sigma>, '\<epsilon>) st_csp) uvar \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
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
apply (blast)
apply (metis)
apply (simp add: zero_list_def)
apply (blast)
apply (blast)
apply (metis)
apply (simp add: zero_list_def)
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

subsubsection {* Iterated Sequence *}

text {*
  An open question is whether to use a different Skip below. Here, I believe
  it is not needed; the main issue is to exploit the property of @{term "II"}
  being a right unit (@{thm seqr_right_unit}). Alternatively, we may use the
  singleton list as the base case to circumvent the problem.
*}

primrec useq_iter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b hrel) \<Rightarrow> 'b hrel" where
"useq_iter [] f = II" |
"useq_iter (h # t) f = (f h) ;; (useq_iter t f)"

syntax "_useq_iter" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> '\<sigma> hrel \<Rightarrow> '\<sigma> hrel"
  ("(3;; _ : _ \<bullet>/ _)" [0, 0, 10] 10)

translations ";; x : l \<bullet> P" \<rightleftharpoons> "(CONST useq_iter) l (\<lambda>x. P)"

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