(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus_prefix.thy                                                *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 28 June 2017 *)

section {* {\Circus} Prefixes (OLD) *}

theory utp_circus_prefix
imports "UTP-Theories-Deep.utp_theories_deep"
begin (* recall_syntax *)

text \<open>TODO: Allow simplification theorems to be passed to @{method rel_simp}.\<close>

subsection {* Simplification of @{const do\<^sub>I} *}

text \<open>Original @{const "do\<^sub>I"} function from theory @{theory utp_csp}.\<close>

text {*
\<open>definition do\<^sub>I :: "
  ('a, '\<theta>) chan \<Rightarrow>
  ('a \<Longrightarrow> ('\<sigma>, '\<theta>) st_csp) \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<theta>) action) \<Rightarrow>
  ('\<sigma>, '\<theta>) action" where
"do\<^sub>I c x P = (
  ($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>$x\<acute>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>)))"\<close>
*}

text \<open>Simplifications that are parametrised by a value rather than a lens.\<close>

definition new_do\<^sub>I :: "
  ('a, '\<epsilon>) chan \<Rightarrow> 'a \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
  ('\<sigma>, '\<epsilon>) action" where
"new_do\<^sub>I c x P =
  ($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  ($tr\<acute> - $tr \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>))"

definition new_do\<^sub>I' :: "
  ('a, '\<epsilon>) chan \<Rightarrow> 'a \<Rightarrow>
  ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
  ('\<sigma>, '\<epsilon>) action" where
"new_do\<^sub>I' c x P =
  ($tr\<acute> =\<^sub>u $tr \<and> (\<^bold>\<forall>x | P(x) \<bullet> (c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute>))
    \<triangleleft> $wait\<acute> \<triangleright>
  ($tr\<acute> - $tr =\<^sub>u \<langle>(c\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle> \<and> P(x))"

declare new_do\<^sub>I_def  [urel_defs]
declare new_do\<^sub>I'_def [urel_defs]

text \<open>For @{const inj}ective channels, the two definitions are equivalent.\<close>

-- \<open>Perhaps all channels should be injective by construction.\<close>

lemma diff_eq_singletonD:
"t - s = [x] \<Longrightarrow> s \<le> t \<Longrightarrow> last t = x"
apply (metis last_snoc less_eq_list_def prefix_concat_minus)
done

lemma new_do\<^sub>I_iff_new_do\<^sub>I':
"inj c \<Longrightarrow> `$tr \<le>\<^sub>u $tr\<acute> \<Rightarrow> (new_do\<^sub>I c x P \<Leftrightarrow> new_do\<^sub>I' c x P)`"
apply (rel_simp)
apply (safe; clarsimp?)
-- {* Subgoal 1 *}
apply (blast)
-- {* Subgoal 2 *}
apply (simp add: diff_eq_singletonD)
-- {* Subgoal 3 *}
apply (drule_tac diff_eq_singletonD)
apply (assumption)
using injD apply (fastforce)
-- {* Subgoal 4 *}
apply (blast)
-- {* Subgoal 5 *}
apply (simp add: diff_eq_singletonD)
done

subsection {* Input Prefix *}

text \<open>Simplifications based on the original definition of Marcel Oliveira.\<close>

definition NewInputCircus ::
  "('a, '\<epsilon>) chan \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('\<sigma>, '\<epsilon>) action" where
"NewInputCircus c P A = (\<^bold>\<exists> x \<bullet> \<^bold>R\<^sub>s(true \<turnstile> (new_do\<^sub>I c x P) \<and> II) ;; A(x))"

declare NewInputCircus_def [urel_defs]

definition NewInputCircus' ::
  "('a, '\<epsilon>) chan \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('a \<Rightarrow> ('\<sigma>, '\<epsilon>) action) \<Rightarrow>
    ('\<sigma>, '\<epsilon>) action" where
"NewInputCircus' c P A = (\<^bold>\<exists> x \<bullet> \<^bold>R\<^sub>s(true \<turnstile> (new_do\<^sub>I' c x P) \<and> II) ;; A(x))"

declare NewInputCircus'_def [urel_defs]

lemma "inj c \<Longrightarrow> NewInputCircus c P A = NewInputCircus' c P A"
apply (rel_simp)
apply (safe; clarsimp?)
apply (metis)+
done

(************************)
(* REVIEWED UNNTIL HERE *)
(************************)

subsection {* Mixed Prefixes *}

text {* In this section, we provide support for mixed prefixes. *}

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
  "c?\<^sub>u(x : P) \<rightarrow> A" \<rightharpoonup> "(CONST InputCSP) c
    (*(CONST top_var \<dots>*) (CONST MkDVar IDSTR(x)) (\<lambda>x. P) (\<lambda>x. A)"
  "c?\<^sub>u(x : P) \<rightarrow> A" \<leftharpoondown> "(CONST InputCSP) c x (\<lambda>v. P) (\<lambda>w. A)"

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
  We first define a new and simplified version of the @{const InputCSP}
  operator. Simplification is due to its action argument being parametrised
  by the a (HOL) value rather than a variable lens. This makes a subsequent
  definition of syntax and translations for mixed prefixes much easier. We
  note that all different kinds of prefixes will be expressed in terms of
  input communications with appropriate constraints on variables that are
  introduced by the prefix construct.
*}

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
end