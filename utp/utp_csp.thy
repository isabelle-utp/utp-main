(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_csp.thy                                                          *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 31 Jan 2017 *)

section {* Theory of CSP *}

theory utp_csp
imports utp_rea_designs utp_procedure utp_tactics
begin

subsection {* Preliminaries *}

text {*
  Simon, why is the precedence of the following operator so low? My view is
  that non-logical operator should not have a precedence below 51, otherwise
  they bind, for instance, weaker than equality. On the other hand, perhaps
  you want equality to bind stronger than the sequence. Could we have a chat
  about this? Precedence of other UTP operators may need need discussion too.
*}

purge_notation useq (infixr ";;" 15)
   notation useq (infixr ";;" 51)

text {*
  We can indeed use the notation @{term "R(P)"} without having to forfeit use
  of @{term R} as a variable. The trick is to make the parentheses part of the
  syntax of @{text "R(_)"}. TODO: Alter this in theory @{theory utp_reactive}.
*}

purge_notation RH ("\<^bold>R")
   notation RH ("R'(_')")

subsection {* CSP Alphabet *}

text {* We note that the type @{typ "'\<phi>"} below is the event type. *}

text {*
  Why is the type name @{typ "'\<phi>"} used below rather than @{typ "'\<theta>"}, as in
  the theory @{theory utp_event}? Of course, it does not affect the model but
  perhaps free type names should be used consistenctly to avoid confusion.
*}

record '\<phi> alpha_csp' =
  ref\<^sub>v :: "'\<phi> set"

declare alpha_csp'.splits [alpha_splits]

text {*
  The following two locale interpretations are a technicality to improve the
  behaviour of the automatic tactics. They enable (re)interpretation of state
  spaces in order to remove any occurrences of lens types, replacing them by
  tuple types after the tactics @{method pred_simp} and @{method rel_simp}
  are applied. Eventually, it would be desirable to automate preform these
  interpretations automatically as part of the @{command alphabet} command.
*}

interpretation alphabet_csp_prd:
  lens_interp "\<lambda>(ok, wait, tr, m). (ok, wait, tr, ref\<^sub>v m, more m)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_csp_rel:
  lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', m, m').
    (ok, ok', wait, wait', tr, tr', ref\<^sub>v m, ref\<^sub>v m', more m, more m')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

text {*
  Type @{typ "'\<phi>"} is used for events and type @{typ "'\<alpha>"} determines the
  program state. The trace type of the underlying reactive process model is
  instantiated as HOL @{type "list"}s of events @{typ "'\<phi>"}.
*}

type_synonym ('\<phi>, '\<alpha>) alpha_csp_scheme =
  "('\<phi> list, ('\<phi>, '\<alpha>) alpha_csp'_scheme) alpha_rp_scheme"

type_synonym ('\<phi>, '\<alpha>) alphabet_csp = "('\<phi>, '\<alpha>) alpha_csp_scheme alphabet"

translations (type) "('\<phi>, '\<alpha>) alphabet_csp" \<leftharpoondown>
  (type) "(_ list, ('\<phi>, '\<alpha>) alpha_csp'_scheme) alphabet_rp"

type_synonym ('\<phi>, '\<alpha>) rel_alphabet_csp = -- {* Added by Frank Zeyda *}
  "('\<phi>, '\<alpha>) alphabet_csp \<times> ('\<phi>, '\<alpha>) alphabet_csp"

text {* Why is @{text "'\<sigma>"} used below rather than @{text "'\<alpha>"} as above? *}

type_synonym ('\<phi>, '\<sigma>) predicate_csp  = "('\<phi>, '\<sigma>) alphabet_csp upred"

type_synonym ('\<phi>, '\<alpha>, '\<beta>) relation_csp  =
  "(('\<phi>, '\<alpha>) alphabet_csp, ('\<phi>, '\<beta>) alphabet_csp) relation"

type_synonym ('\<phi>, '\<alpha>) hrelation_csp  = "('\<phi>, '\<alpha>, '\<alpha>) relation_csp"

text {* By default, CSP processes do not have program state. *}

type_synonym '\<phi> csp = "('\<phi>, unit) hrelation_csp"

subsection {* CSP Variables *}

text {*
  It is not quite obvious why we need so many definitions for each variable,
  and what the purpose of the various definitions is. For instance, what is
  the different between @{text "ref"} and @{text "ref\<^sub>r"}? Ask Simon Foster if
  he could insert some comments here to clarify this. Maybe we can do with
  introducing less definitions?! Unless all of them are needed at some point.
*}

definition [uvar_defs]: "ref\<^sub>c = VAR ref\<^sub>v"
definition [uvar_defs]: "\<Sigma>\<^sub>c = VAR more"
definition [uvar_defs]: "ref = (ref\<^sub>c ;\<^sub>L \<Sigma>\<^sub>R)"
definition [uvar_defs]: "ref\<^sub>r = (ref\<^sub>c ;\<^sub>L \<Sigma>\<^sub>r)"
definition [uvar_defs]: "\<Sigma>\<^sub>C = (\<Sigma>\<^sub>c ;\<^sub>L \<Sigma>\<^sub>R)"
definition [uvar_defs]: "\<Sigma>\<^sub>C\<^sub>x\<^sub>C = \<Sigma>\<^sub>C \<times>\<^sub>L \<Sigma>\<^sub>C"

subsubsection {* Lens Laws *}

paragraph {* Lens Membership *}

lemma ref\<^sub>c_vwb_lens
[simp]: "vwb_lens ref\<^sub>c"
apply (unfold_locales)
apply (unfold ref\<^sub>c_def)
apply (simp_all)
done

lemma csp_vwb_lens
[simp]: "vwb_lens \<Sigma>\<^sub>c"
apply (unfold_locales)
apply (unfold \<Sigma>\<^sub>c_def)
apply (simp_all)
done

lemma ref_vwb_lens
[simp]: "vwb_lens ref"
apply (unfold ref_def)
apply (simp)
done

lemma ref\<^sub>r_vwb_lens
[simp]: "vwb_lens ref\<^sub>r"
apply (unfold ref\<^sub>r_def)
apply (simp)
done

lemma csp_lens_vwb_lens
[simp]: "vwb_lens \<Sigma>\<^sub>C"
apply (unfold \<Sigma>\<^sub>C_def)
apply (simp)
done

paragraph {* Lens Independence *}

lemma ok_indep_ref
[simp]: "ok \<bowtie> ref" "ref \<bowtie> ok"
apply (unfold ref_def)
apply (simp_all)
done

lemma wait_indep_ref
[simp]: "wait \<bowtie> ref" "ref \<bowtie> wait"
apply (unfold ref_def)
apply (simp_all)
done

lemma tr_indep_ref
[simp]: "tr \<bowtie> ref" "ref \<bowtie> tr"
apply (unfold ref_def)
apply (simp_all)
done

lemma csp_lens_indep_ok
[simp]: "\<Sigma>\<^sub>C \<bowtie> ok" "ok \<bowtie> \<Sigma>\<^sub>C"
apply (unfold \<Sigma>\<^sub>C_def)
apply (simp_all)
done

lemma csp_lens_indep_wait
[simp]: "\<Sigma>\<^sub>C \<bowtie> wait" "wait \<bowtie> \<Sigma>\<^sub>C"
apply (unfold \<Sigma>\<^sub>C_def)
apply (simp_all)
done

text {*
  Omitting detailed type information (@{text "_"} below) might save effort in
  writing but overall it is not very helpful for someone reading the theories
  and trying to understand its definitions. I.e. just by looking at the code I
  struggle to see what the below achieves. In particular, that no comments are
  included. I believe the purpose is to coerce a relational expression on the
  state variables alone into a lifted relational expression on the entire CSP
  alphabet. Is that true? If so, maybe put a comment here to explain. Also,
  the name is not well chosen i.e.~what kind of lifting is performed here?
*}

abbreviation lift_csp :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>C") where
"\<lceil>P\<rceil>\<^sub>C \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>C \<times>\<^sub>L \<Sigma>\<^sub>C)"

subsubsection {* Instantiations *}

text {*
  Class @{class vst} has to be instantiated in order to located the store for
  deep variables within the type @{typ "('\<phi>, '\<alpha>) alpha_csp'_ext"}. This is to
  support deep variables in CSP processes.
*}

instantiation alpha_csp'_ext :: (type, vst) vst
begin
definition vstore_lens_alpha_csp'_ext ::
  "vstore \<Longrightarrow> ('a, 'b) alpha_csp'_scheme" where
"vstore_lens_alpha_csp'_ext = \<V> ;\<^sub>L \<Sigma>\<^sub>c"
instance
apply (intro_classes)
apply (unfold vstore_lens_alpha_csp'_ext_def)
apply (simp)
done
end

subsection {* CSP Trace Merge *}

text {*
  The function below defines the parallel composition of two CSP event traces.
  It is parametrised by the set of events on which the traces must synchronise.
  The definition is given in terms of distributed concatenation @{term "op \<^sup>\<frown>"}
  of (sets of) lists. We note that type @{typ "'\<theta> event"} is synonymous for
  @{typ "'\<theta>"} (see theory @{theory utp_event}).
*}

fun tr_par ::
  "'\<theta> event set \<Rightarrow> '\<theta> event list \<Rightarrow> '\<theta> event list \<Rightarrow> '\<theta> event list set" where
"tr_par cs [] [] = {[]}" |
"tr_par cs (e # t) [] = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs t []))" |
"tr_par cs [] (e # t) = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs [] t))" |
"tr_par cs (e\<^sub>1 # t\<^sub>1) (e\<^sub>2 # t\<^sub>2) =
  (if e\<^sub>1 = e\<^sub>2
    then
      if e\<^sub>1 \<in> cs (* \<and> e\<^sub>2 \<in> cs *)
        then {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 t\<^sub>2)
        else
          ({[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))) \<union>
          ({[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))
    else
      if e\<^sub>1 \<in> cs then
        if e\<^sub>2 \<in> cs then {[]}
        else
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2)
      else
        if e\<^sub>2 \<in> cs then
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))
        else
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)) \<union>
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))"

subsubsection {* Lifted Trace Merge *}

syntax "_utr_par" ::
  "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(_ \<star>\<^bsub>_\<^esub>/ _)" [100, 0, 101] 100)

text {* The function @{const trop} is used to lift ternary operators. *}

translations
  "t1 \<star>\<^bsub>cs\<^esub> t2" == "(CONST trop) (CONST tr_par) cs t1 t2"

subsubsection {* Trace Merge Lemmas *}

lemma tr_par_empty:
"tr_par cs t1 [] = {takeWhile (\<lambda>x. x \<notin> cs) t1}"
"tr_par cs [] t2 = {takeWhile (\<lambda>x. x \<notin> cs) t2}"
-- {* Subgoal 1 *}
apply (induct t1; simp)
-- {* Subgoal 2 *}
apply (induct t2; simp)
done

lemma tr_par_sym:
"tr_par cs t1 t2 = tr_par cs t2 t1"
apply (induct t1 arbitrary: t2)
-- {* Subgoal 1 *}
apply (simp add: tr_par_empty)
-- {* Subgoal 2 *}
apply (induct_tac t2)
-- {* Subgoal 2.1 *}
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (clarsimp)
apply (blast)
done

subsection {* Healthiness Conditions *}

text {* We here define extra healthiness conditions for CSP processes. *}

text {*
  Simon, the definition below did not explicitly include type information. I
  think it is good practice to specify types in all definitions, I thus added
  the type @{typ "'\<phi> csp"}. Is that correct? I suppose pure CSP processes do
  not consider program state?!
*}

definition STOP :: "'\<phi> csp" where
[upred_defs]: "STOP = CSP1($ok\<acute> \<and> R3c($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition SKIP :: "'\<phi> csp" where
[upred_defs]: "SKIP = R(\<exists> $ref \<bullet> CSP1(II))"

text {*
  It is a bit strange that @{const CSP1} and @{const CSP2} are not defined here
  as well. Are both consider to be part of the theory of reactive designs? Or
  is it just so that laws can be proved in the theory @{theory utp_rea_designs}
  that refer to them? If the latter is the case, perhaps some the of those laws
  could be proved here instead? That might give us a cleaner separation between
  the theory of reactive designs and the theory of CSP.
*}

(* definition [upred_defs]: "CSP1(P) = (P \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))" *)
(* definition [upred_defs]: "CSP2(P) = H2(P)" *)
definition [upred_defs]: "CSP3(P) = (SKIP ;; P)"
definition [upred_defs]: "CSP4(P) = (P ;; SKIP)"

subsection {* CSP Constructs *}

definition [upred_defs]:
"Stop = R(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition [upred_defs]:
"Skip = R(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> (\<not> $wait\<acute>) \<and> \<lceil>II\<rceil>\<^sub>R))"

text {* Simon, why is none of the below tagged with @{attribute upred_defs}? *}

definition Guard ::
  "('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow>
   ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow>
   ('\<theta>, '\<alpha>) hrelation_csp" (infix "&\<^sub>u" 65) where
"g &\<^sub>u A = R((g \<Rightarrow> \<not> A\<^sup>f\<^sub>f) \<turnstile> ((g \<and> A\<^sup>t\<^sub>f) \<or> (\<not> g) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition ExtChoice ::
  "('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow>
   ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow>
   ('\<theta>, '\<alpha>) hrelation_csp" (infixl "\<box>" 65) where
"A\<^sub>1 \<box> A\<^sub>2 =
  R(\<not> A\<^sub>1\<^sup>f\<^sub>f \<and> \<not> A\<^sub>2\<^sup>f\<^sub>f \<turnstile> (A\<^sub>1\<^sup>t\<^sub>f \<and> A\<^sub>2\<^sup>t\<^sub>f) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (A\<^sub>1\<^sup>t\<^sub>f \<or> A\<^sub>2\<^sup>t\<^sub>f))"

text {*
  Simon, I changed the type of the parameter @{term e} of @{text "do\<^sub>u"} to
  an expression over undashed variable only rather then relational ones. I
  considered changing it to @{typ "'\<alpha>"} but realised that this causes some
  inconveniences as increasing the need for explicit coercions of alphabet
  types, for instance, if variables used in @{term e} have a state-space
  type consistent with the theory of CSP rather than plain program states.
  Intuitively, we may want to exclude that expression @{term e} refers to
  dashed or auxiliary variables though, which motivated my use @{typ "'\<alpha>"}.
*}

definition do\<^sub>u ::
  "('\<theta>, (*'\<alpha>*) ('\<theta>, '\<alpha>) alphabet_csp) uexpr \<Rightarrow>
   ('\<theta>, '\<alpha>) hrelation_csp" where
"do\<^sub>u e = (let e\<^sub>r = \<lceil>e\<rceil>\<^sub>< in
  ($tr\<acute> =\<^sub>u $tr \<and> e\<^sub>r \<notin>\<^sub>u $ref\<acute> \<triangleleft> $wait\<acute> \<triangleright> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>e\<^sub>r\<rangle>))"

text {*
  Simon, I believe we need a conjunction with @{term "\<lceil>II\<rceil>\<^sub>R"} here too, namely
  if we assume the operator will be used in the context of stateful processes.
  Otherwise, anything might happen to the program variables after the output
  communication was performed. Do you agree with this? If yes, just remove the
  comment with the next commit. If not, perhaps catch me and we talk about it!
*}

definition OutputCSP ::
  "('a, '\<theta>) chan \<Rightarrow>
  ('a, (*'\<alpha>*) ('\<theta>, '\<alpha>) alphabet_csp) uexpr \<Rightarrow>
  ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow>
  ('\<theta>, '\<alpha>) hrelation_csp" where
"OutputCSP c v A = (R(true \<turnstile> (do\<^sub>u (c\<cdot>v)\<^sub>u \<and> \<lceil>II\<rceil>\<^sub>R)) ;; A)"


definition do\<^sub>I :: "
  ('a, '\<theta>) chan \<Rightarrow>
  ('a, (*'\<alpha>*) ('\<theta>, '\<alpha>) alphabet_csp) uvar \<Rightarrow>
  ('a \<Rightarrow> (*'\<alpha>*) ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow>
  ('\<theta>, '\<alpha>) hrelation_csp" where
"do\<^sub>I c x P = (
  ($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
    \<triangleleft> $wait\<acute> \<triangleright>
  ($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c\<cdot>\<guillemotleft>e\<guillemotright>)\<^sub>u\<rangle>}\<^sub>u \<and> (c\<cdot>$x\<acute>)\<^sub>u =\<^sub>u last\<^sub>u($tr\<acute>))"

text {*
  Simon, I believe there was an earlier problem here due to the conjunction
  with @{term "\<lceil>II\<rceil>\<^sub>R"} as this also puts a constraint on variable @{term x}.
  If you agree with the fix below, feel free to remove this comments. Below
  I also highlighted places where we could consider using the plain program
  state type @{typ "'\<alpha>"}. I did not adopt this for the same reason as noted
  above, making usage more error-prone due to additional need for coercions.
*}

definition InputCSP ::
  "('a::{continuum, two}, '\<theta>) chan \<Rightarrow>
    ('a, (*'\<alpha>*) ('\<theta>, '\<alpha>) alphabet_csp) lvar \<Rightarrow>
    ('a \<Rightarrow> (*'\<alpha>*) ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow>
    (('a, ('\<theta>, '\<alpha>) alphabet_csp) uvar \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow>
    ('\<theta>, (*'\<alpha>*) '\<alpha>) hrelation_csp" where
"InputCSP c x P A = (var\<^bsub>RDES\<^esub> x \<bullet> R(true \<turnstile> ((do\<^sub>I c x P) \<and> (\<exists> $x\<acute> \<bullet> II))) ;; A(x))"

syntax
  "_csp_sync" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>u _" [81, 80] 80)
  "_csp_output" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"
    ("_!\<^sub>u'(_') \<rightarrow> _" [81, 0, 80] 80)
  "_csp_input"  :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"
    ("_?\<^sub>u'(_ :/ _') \<rightarrow> _" [81, 0, 0, 80] 80)

text {*
  Simon, I think @{text "(CONST top_var \<dots>"} below was a bug since the result
  is not a type instance of @{typ "('a, '\<alpha>) lvar"} but @{typ "('a, '\<alpha>) uvar"}.
  Could you perhaps check with the previous version of the translation rules?
  Pretty-printing of input prefixes now soft of works, although there is still
  an issue with eta-contractions (@{text "Syntax_Trans.preserve_binder_abs_\<dots>"}
  only handles the suppression of eta-contraction up to the second argument.
*}

translations
  "c \<rightarrow>\<^sub>u A"         \<rightleftharpoons> "(CONST OutputCSP) c ()\<^sub>u A"
  "c!\<^sub>u(v) \<rightarrow> A"     \<rightleftharpoons> "(CONST OutputCSP) c v A"
  "c?\<^sub>u(x : P) \<rightarrow> A" \<rightharpoonup> "(CONST InputCSP) c
    (*(CONST top_var \<dots>*) (CONST MkDVar IDSTR(x)) (\<lambda>x. P) (\<lambda>x. A)"
  "c?\<^sub>u(x : P) \<rightarrow> A" \<leftharpoondown> "(CONST InputCSP) c x (\<lambda>v. P) (\<lambda>w. A)"

subsection {* Parallel Composition *}

subsection {* Merge Predicates *}

text {*
  Simon, why @{term "$tr\<acute> \<le>\<^sub>u $tr\<^sub><"} and not @{term "$tr\<^sub>< \<le>\<^sub>u $tr\<acute>"} below?
  Also as the function appears to be the merge operation for reactive designs
  (subscript @{text "R"}), would it conceptually not be better placed in the
  theory @{theory utp_rea_designs}? Strangely, the function below appears not
  to be used anywhere else. Is it redundant now? If so, perhaps remove it!
*}

definition merge_rd ("M\<^sub>R") where
[upred_defs]: "M\<^sub>R(M) =
  ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and> $wait\<acute> =\<^sub>u ($0-wait \<and> $1-wait) \<and> $tr\<acute> \<le>\<^sub>u $tr\<^sub>< \<and> M)"

text {*
  I wonder if there is a possibility that the terms @{term "$0-tr - $tr\<^sub><"} and
  @{term "$1-tr - $tr\<^sub><"} could be undefined. What ensures, for instance, that
  @{term "$tr\<^sub>< \<le>\<^sub>u $0-tr"} holds? I presume this is guaranteed by both operand
  processes of the parallel composition being healthy, right? So maybe we do
  not have to worry about it here. Another issues may be the constraint on the
  refusal set. Do we not need to take into account @{term cs} as well in order
  to calculate the refusals @{term "$ref\<acute>"} of the composition? Ask Simon!
*}

definition N0 :: "'\<psi> set \<Rightarrow> (('\<psi>, unit) alphabet_csp) merge" where
[upred_defs]: "N0(cs) = (
  $wait\<acute> =\<^sub>u ($0-wait \<or> $1-wait) \<and>
  (* Not sure about the next line... (Frank) *)
  $ref\<acute> =\<^sub>u ($0-ref \<union>\<^sub>u $1-ref) \<and>
  $tr\<^sub>< \<le>\<^sub>u $tr\<acute> \<and>
  ($tr\<acute> - $tr\<^sub><) \<in>\<^sub>u ($0-tr - $tr\<^sub><) \<star>\<^bsub>\<guillemotleft>cs\<guillemotright>\<^esub> ($1-tr - $tr\<^sub><) \<and>
  ($0-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u ($1-tr - $tr\<^sub><) \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>)"

text {* The definition below does not seem to be used anywhere... Remove? *}

definition M0 :: "'\<psi> set \<Rightarrow> (('\<psi>, unit) alphabet_csp) merge" where
[upred_defs]: "M0(cs) = (N0(cs) ;; SKIP)"

definition CSPMerge' ("N\<^sub>C\<^sub>S\<^sub>P") where
[upred_defs]: "CSPMerge'(cs) = ($ok\<acute> =\<^sub>u ($0-ok \<and> $1-ok) \<and> N0(cs))"

text {*
  I suppose composition with @{term SKIP} is to remove and constraints on the
  refusal set after termination, and thus make the process CSP-healthy.
*}

definition CSPMerge ("M\<^sub>C\<^sub>S\<^sub>P") where
[upred_defs]: "CSPMerge(cs) = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP)"

subsection {* Parallel Operator *}

text {*
  So we are not considering processes with program state. Is there a way to
  generalise the definition below to cater fro state too? Or are there some
  semantic issues associated with this, beyond merging the state spaces?
*}

abbreviation ParCSP ::
  "'\<theta> csp \<Rightarrow> '\<theta> event set \<Rightarrow> '\<theta> csp \<Rightarrow> '\<theta> csp" (infixl "[|_|]" 85) where
"P [|cs|] Q \<equiv> P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q"

subsubsection {* CSP Merge Laws *}

text {* Jim's merge predicate lemmas. *}

lemma JL1: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by (rel_auto)

lemma JL2: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by (rel_auto)

lemma JL3: "(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk> = (N0(cs) ;; R1(true))"
  by (rel_auto)

lemma SKIP_no_start: "(SKIP\<lbrakk>false/$ok\<rbrakk>) = R1(true)"
  by (rel_auto)

lemma SKIP_pre: "SKIP\<^sup>f = R1(\<not> $ok)"
  by (rel_auto)

lemma parallel_ok_cases:
"((P \<parallel>\<^sub>s Q) ;; M) = (
  ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
  ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
  ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
  ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
proof -
  have "((P \<parallel>\<^sub>s Q) ;; M) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (P \<parallel>\<^sub>s Q)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<acute>\<rbrakk> ;; M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<rbrakk>)"
    by (subst seqr_middle[of "left_uvar ok"], simp_all)
  also have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> \<^bold>\<exists> ok\<^sub>1 \<bullet> ((P \<parallel>\<^sub>s Q)\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<acute>\<rbrakk>\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$1-ok\<acute>\<rbrakk>) ;; (M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$0-ok\<rbrakk>\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$1-ok\<rbrakk>))"
    by (subst seqr_middle[of "right_uvar ok"], simp_all)
  also have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> \<^bold>\<exists> ok\<^sub>1 \<bullet> (P\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> \<parallel>\<^sub>s Q\<lbrakk>\<guillemotleft>ok\<^sub>1\<guillemotright>/$ok\<acute>\<rbrakk>) ;; (M\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>,\<guillemotleft>ok\<^sub>1\<guillemotright>/$0-ok,$1-ok\<rbrakk>))"
    by (rel_auto)
  also have "... = (
      ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>t) ;; (M\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>t \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f \<parallel>\<^sub>s Q\<^sup>f) ;; (M\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
    by (simp add: true_alt_def[THEN sym] false_alt_def[THEN sym] disj_assoc
      utp_pred.sup.left_commute utp_pred.sup_commute usubst)
  finally show ?thesis .
qed

lemma SKIP_alt_def: "SKIP = R(\<exists> $ref \<bullet> II\<^sub>r)"
  by (rel_auto)

lemma SKIP_rea_des: "SKIP = R(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute>))"
  by (rel_auto)

lemma SKIP_is_R1: "SKIP is R1"
  by (rel_auto)

lemma SKIP_is_R2: "SKIP is R2"
  by (rel_auto)

lemma SKIP_is_R3c: "SKIP is R3c"
apply (rel_auto)
apply (simp_all add: zero_list_def)
apply (metis append_Nil2 append_minus strict_prefixE)
done

lemma SKIP_is_CSP1: "SKIP is CSP1"
  by (rel_auto)

lemma SKIP_is_CSP2: "SKIP is CSP2"
  by (rel_auto)

lemma CSPMerge'_is_R1m:
"CSPMerge'(cs) is R1m"
  by (rel_auto)

lemma CSPMerge_is_R1m:
"CSPMerge(cs) is R1m"
  by (rel_auto)

lemma parallel'_is_R1:
"(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R1"
  by (simp add: CSPMerge'_is_R1m R1_par_by_merge)

lemma CSPMerge'_alt_def:
"(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = ((P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) ;; SKIP)"
  by (simp add: par_by_merge_def CSPMerge_def seqr_assoc)

lemma parallel_is_R1:
"(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R1"
  by (simp add: CSPMerge'_alt_def R1_seqr_closure SKIP_is_R1 parallel'_is_R1)

lemma parallel'_is_R2:
assumes "P is R2" "Q is R2"
shows "(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R2"
proof -
  have "N\<^sub>C\<^sub>S\<^sub>P cs is R2m"
    by (rel_auto)
  thus ?thesis
    using R2_par_by_merge assms(1) assms(2) by blast
qed

theorem parallel_is_R2:
assumes "P is R2" "Q is R2"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R2"
  by (simp add: CSPMerge'_alt_def R2_seqr_closure SKIP_is_R2 assms(1) assms(2) parallel'_is_R2)

lemma parallel'_is_R3:
assumes "P is R3" "Q is R3"
shows "(P \<parallel>\<^bsub>N\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R3"
proof -
  have "(skip\<^sub>m ;; N\<^sub>C\<^sub>S\<^sub>P(cs)) = II"
    apply (rel_auto) using strict_prefixE by fastforce
  thus ?thesis
    by (simp add: R3_par_by_merge assms)
qed

lemma CSPMerge_div_prop:
"(div\<^sub>m ;; CSPMerge(cs)) = R1 true"
apply (rel_auto)
apply (rename_tac ok wait tr ref ok' wait' tr' ref')
apply (rule_tac x = "ok" in exI)
apply (rule_tac x = "wait" in exI)
apply (rule_tac x = "tr" in exI)
apply (rule_tac x = "ref" in exI)
apply (simp)
apply (metis minus_cancel order_refl singletonI tr_par.simps(1))
done

lemma CSPMerge_wait_prop:
"(wait\<^sub>m ;; M\<^sub>C\<^sub>S\<^sub>P(cs)) = II\<lbrakk>true,true/$ok,$wait\<rbrakk>"
apply (rel_auto)
apply (metis minus_zero_eq zero_list_def)
using zero_list_def apply auto
done

lemma parallel_is_R3c:
assumes "P is R1" "Q is R1" "P is CSP1" "Q is CSP1" "P is R3c" "Q is R3c"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is R3c"
  by (simp add: CSPMerge_div_prop CSPMerge_wait_prop R3c_par_by_merge assms)

lemma parallel_is_CSP1:
assumes "P is R1" "Q is R1" "P is CSP1" "Q is CSP1"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP1"
  by (simp add: CSP1_par_by_merge CSPMerge_div_prop CSPMerge_is_R1m assms)

lemma parallel_is_CSP2:
"(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP2"
proof -
  have "M\<^sub>C\<^sub>S\<^sub>P(cs) is CSP2"
  proof -
    have "CSP2(M\<^sub>C\<^sub>S\<^sub>P(cs)) = (M\<^sub>C\<^sub>S\<^sub>P(cs) ;; J)"
      by (simp add: CSP2_def H2_def)
    also have "... = ((N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP) ;; J)"
      by (simp add: CSPMerge_def)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; (SKIP ;; J))"
      by (simp add: seqr_assoc)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; (CSP2(SKIP)))"
      by (simp add: CSP2_def H2_def)
    also have "... = (N\<^sub>C\<^sub>S\<^sub>P(cs) ;; SKIP)"
      by (simp add: Healthy_if SKIP_is_CSP2)
    finally show ?thesis
      by (simp add: Healthy_def' CSPMerge_def)
  qed
  thus ?thesis
    using CSP2_par_by_merge by blast
qed

lemma parallel_is_CSP:
assumes "P is CSP" "Q is CSP"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) is CSP"
  by (metis CSP_healths(1-4) CSP_intro assms parallel_is_CSP1 parallel_is_CSP2
    parallel_is_R1 parallel_is_R2 parallel_is_R3c)

lemma parallel_precondition:
assumes "P is CSP2"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f = ((P \<parallel>\<^sub>s Q) ;; M\<^sub>C\<^sub>S\<^sub>P(cs))\<^sup>f\<^sub>f"
    by (simp add: par_by_merge_def)
  also have "... = (((P \<^sub>f \<parallel>\<^sub>s Q \<^sub>f) ;; N\<^sub>C\<^sub>S\<^sub>P(cs)) ;; R1(\<not> $ok))"
    by rel_blast
  also have "... = ((
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>))) ;; R1(\<not> $ok))"
    by (subst parallel_ok_cases, subst_tac)
  also have "... = ((
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok))) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N\<^sub>C\<^sub>S\<^sub>P cs)\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk> ;; R1(\<not> $ok)))) )"
    (is "_ = (?C1 \<or>\<^sub>p ?C2 \<or>\<^sub>p ?C3 \<or>\<^sub>p ?C4)")
    by (simp add: seqr_or_distl seqr_assoc)
  also have "... = (?C2 \<or> ?C3)"
  proof -
    have "?C1 = false"
      by (rel_auto)
    moreover have "`?C4 \<Rightarrow> ?C3`" (is "`(?A ;; ?B) \<Rightarrow> (?C ;; ?D)`")
    proof -
      from assms have "`P\<^sup>f \<Rightarrow> P\<^sup>t`"
        by (metis CSP2_def H2_equivalence Healthy_def')
      hence P: "`P\<^sup>f\<^sub>f \<Rightarrow> P\<^sup>t\<^sub>f`"
        by (rel_auto)
      have "`?A \<Rightarrow> ?C`"
        using P by rel_auto
      moreover have "`?B \<Rightarrow> ?D`"
        by (rel_auto)
      ultimately show ?thesis
        by (simp add: impl_seqr_mono)
    qed
    ultimately show ?thesis
      by (simp add: subsumption2)
  qed
  also have "... = (
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((N0 cs ;; R1(\<not> $ok)))) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((N0 cs ;; R1(\<not> $ok)))))"
    by (rel_blast)
  also have "... = (
      (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(\<not> $ok)\<^esub> Q\<^sup>t\<^sub>f) \<or>
      (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(\<not> $ok)\<^esub> Q\<^sup>f\<^sub>f))"
    (is "_ = ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>?M1\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>?M2\<^esub> Q\<^sup>f\<^sub>f))")
    by (simp add: par_by_merge_def)
  also have "... = (
      (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<or>
      (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))"
  proof -
    have "?M1 = (N0 cs ;; R1(true))"
      by (rel_auto)
    moreover have "?M2 = (N0 cs ;; R1(true))"
      by (rel_auto)
    ultimately show ?thesis by simp
  qed

  finally show ?thesis .
qed

lemma parallel_postcondition:
assumes "P is CSP2"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f = (
  (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f) \<or>
  (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<or>
  (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0(cs) ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f = ((P \<parallel>\<^sub>s Q) ;; M\<^sub>C\<^sub>S\<^sub>P(cs))\<^sup>t\<^sub>f"
    by (simp add: par_by_merge_def)
  also have "... = ((P \<^sub>f \<parallel>\<^sub>s Q \<^sub>f) ;; (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t)"
    by (rel_blast)
  also have "... = (
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,false/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>false,false/$0-ok,$1-ok\<rbrakk>)))"
    by (subst parallel_ok_cases, subst_tac)
  also have "... = (
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))))"
      (is "_ = (?C1 \<or>\<^sub>p ?C2 \<or>\<^sub>p ?C3 \<or>\<^sub>p ?C4)")
    by (simp add: JL1 JL2 JL3)
  also have "... = (
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; ((M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>)) \<or>
      ((P\<^sup>f\<^sub>f \<parallel>\<^sub>s Q\<^sup>t\<^sub>f) ;; (N0(cs) ;; R1(true))) \<or>
      ((P\<^sup>t\<^sub>f \<parallel>\<^sub>s Q\<^sup>f\<^sub>f) ;; (N0(cs) ;; R1(true))))"
  proof -
    from assms have "`P\<^sup>f \<Rightarrow> P\<^sup>t`"
      by (metis CSP2_def H2_equivalence Healthy_def')
    hence P:"`P\<^sup>f\<^sub>f \<Rightarrow> P\<^sup>t\<^sub>f`"
      by (rel_auto)
    have "`?C4 \<Rightarrow> ?C3`" (is "`(?A ;; ?B) \<Rightarrow> (?C ;; ?D)`")
    proof -
      have "`?A \<Rightarrow> ?C`"
        using P by rel_auto
      thus ?thesis
        by (simp add: impl_seqr_mono)
    qed
    thus ?thesis
      by (simp add: subsumption2)
  qed
  finally show ?thesis
    by (simp add: par_by_merge_def)
qed

theorem parallel_reactive_design:
assumes "P is CSP" "Q is CSP"
shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = R(
  (\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))
    \<turnstile>
  (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f))"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = R((\<not> (P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>f\<^sub>f) \<turnstile> (P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q)\<^sup>t\<^sub>f)"
    by (simp add: CSP_reactive_design assms parallel_is_CSP)
  also have "... = R(
    (\<not> ((P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f) \<or> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>f\<^sub>f)))
      \<turnstile>
    (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f \<or>
     P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<or>
     P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f))"
    by (simp add: parallel_precondition parallel_postcondition CSP_healths(5) assms(1))
  also have "... = R(
    (\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))
      \<turnstile>
    ((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 (true)\<^esub> Q\<^sup>t\<^sub>f \<or> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<and>
    (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f \<or>
     P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<or>
     P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)))"
    by (simp add: design_export_pre)
  also have "... = R(
    (\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))
      \<turnstile>
    ((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f \<or> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f)) \<and>
      (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f)))"
    by (subst neg_conj_cancel2, simp)
  also have "... = R(
    (\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>t\<^sub>f) \<and> \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> Q\<^sup>f\<^sub>f))
      \<turnstile>
    (P\<^sup>t\<^sub>f \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> Q\<^sup>t\<^sub>f))"
    by (simp add: design_export_pre)
  finally show ?thesis by simp
qed

lemma design_subst_ok_ok: "(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true/$ok\<rbrakk>) = (P \<turnstile> Q)"
  by (rel_auto)

theorem parallel_reactive_design':
  assumes "P is CSP" "Q is CSP"
  shows "(P \<parallel>\<^bsub>M\<^sub>C\<^sub>S\<^sub>P(cs)\<^esub> Q) = R(
    (\<not> ((\<not> pre\<^sub>R(P)) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
     \<not> (cmt\<^sub>R(P) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> (\<not> pre\<^sub>R(Q)))) \<turnstile>
    (cmt\<^sub>R(P) \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> cmt\<^sub>R(Q)))"
proof -
  have 1:"(P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk> = (\<not> pre\<^sub>R(P)) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> cmt\<^sub>R(Q)"
    by (rel_blast)

  have 2:"(P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk> = (cmt\<^sub>R(P) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> (\<not> pre\<^sub>R(Q)))"
    by (rel_blast)

  have 3:"(P\<^sup>t\<^sub>f \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk> =
      cmt\<^sub>R P \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> cmt\<^sub>R Q"
    by (rel_blast)

  have "R((\<not> P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<and> \<not> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f) \<turnstile>
             P\<^sup>t\<^sub>f \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> Q\<^sup>t\<^sub>f) =
        R((\<not> P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f \<and> \<not> P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk> \<turnstile>
            (P\<^sup>t\<^sub>f \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: design_subst_ok_ok)

  also have "... =
      R((\<not> (P\<^sup>f\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk> \<and>
         \<not> (P\<^sup>t\<^sub>f \<parallel>\<^bsub>N0 cs ;; R1 true\<^esub> Q\<^sup>f\<^sub>f)\<lbrakk>true/$ok\<rbrakk>) \<turnstile>
        (P\<^sup>t\<^sub>f \<parallel>\<^bsub>[$0-ok \<mapsto>\<^sub>s true, $1-ok \<mapsto>\<^sub>s true] \<dagger> (M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<^esub> Q\<^sup>t\<^sub>f)\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: usubst)

  also have "... =
      R((\<not> ((\<not> pre\<^sub>R(P)) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> cmt\<^sub>R(Q)) \<and>
         \<not> (cmt\<^sub>R(P) \<parallel>\<^bsub>N0 cs ;; R1(true)\<^esub> (\<not> pre\<^sub>R(Q)))) \<turnstile>
        (cmt\<^sub>R(P) \<parallel>\<^bsub>(M\<^sub>C\<^sub>S\<^sub>P cs)\<^sup>t\<lbrakk>true,true/$0-ok,$1-ok\<rbrakk>\<^esub> cmt\<^sub>R(Q)))"
    by (simp add: 1 2 3)

  finally show ?thesis
    by (simp add: parallel_reactive_design assms)
qed

theorem STOP_is_Stop: "STOP = Stop"
apply (rel_simp)
apply (simp_all add: zero_list_def)
apply (metis minus_cancel minus_zero_eq order_refl zero_list_def)
done

lemma Skip_is_rea_skip: "Skip = II\<^sub>r"
apply (rel_auto) using minus_zero_eq by (blast)+

lemma swap_CSPMerge': "(swap\<^sub>m ;; N\<^sub>C\<^sub>S\<^sub>P cs) = N\<^sub>C\<^sub>S\<^sub>P cs"
  by (rel_auto, (metis tr_par_sym)+)

lemma swap_CSPMerge: "(swap\<^sub>m ;; M\<^sub>C\<^sub>S\<^sub>P cs) = M\<^sub>C\<^sub>S\<^sub>P cs"
  by (simp add: CSPMerge_def seqr_assoc swap_CSPMerge')

theorem parallel_commutative:
  "(P [|cs|] Q) = (Q [|cs|] P)"
  by (simp add: par_by_merge_commute swap_CSPMerge)

lemma STOP_pre: "pre\<^sub>R(STOP) = true"
  by (rel_auto)

lemma STOP_cmt: "cmt\<^sub>R(STOP) = ($wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr)"
  by (rel_auto)

lemma STOP_reactive_design: "STOP = R(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"
  by (simp add: STOP_is_Stop Stop_def)

lemma STOP_is_CSP: "STOP is CSP"
  by (simp add: STOP_reactive_design RH_design_is_CSP unrest)
end