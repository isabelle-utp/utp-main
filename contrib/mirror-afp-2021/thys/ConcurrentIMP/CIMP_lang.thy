(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP_lang
imports
  CIMP_pred
  LTL
begin

(*>*)
section\<open>CIMP syntax and semantics \label{sec:cimp-syntax-semantics}\<close>

text\<open>

We define a small sequential programming language with synchronous
message passing primitives for describing the individual
processes. This has the advantage over raw transition systems in that
it is programmer-readable, includes sequential composition, supports a
program logic and VCG (\S\ref{sec:cimp-vcg}), etc. These processes are
composed in parallel at the top-level.

CIMP is inspired by IMP, as presented by @{cite [cite_macro=citet]
"Winskel:1993"} and @{cite [cite_macro=citet]
"ConcreteSemantics:2014"}, and the classical process algebras CCS
@{cite [cite_macro=citep] "Milner:1980" and "Milner:1989"} and CSP
@{cite [cite_macro=citep] "Hoare:1985"}. Note that the algebraic
properties of this language have not been developed.

As we operate in a concurrent setting, we need to provide a small-step
semantics (\S\ref{sec:cimp-semantics}), which we give in the style of
\emph{structural operational semantics} (SOS) as popularised by @{cite
[cite_macro=citet] "DBLP:journals/jlp/Plotkin04"}. The semantics of a
complete system (\S\ref{sec:cimp-system-steps}) is presently taken
simply to be the states reachable by interleaving the enabled steps of
the individual processes, subject to message passing rendezvous. We
leave a trace or branching semantics to future work.

This theory contains all the trusted definitions. The soundness of the other
theories supervenes upon this one.

\<close>


subsection\<open>Syntax\<close>

text\<open>

Programs are represented using an explicit (deep embedding) of their
syntax, as the semantics needs to track the progress of multiple
threads of control. Each (atomic) \emph{basic command}
(\S\ref{sec:cimp-decompose}) is annotated with a @{typ "'location"},
which we use in our assertions (\S\ref{sec:cimp-control-predicates}).
These locations need not be unique, though in practice they likely
will be.

Processes maintain \emph{local states} of type @{typ "'state"}. These
can be updated with arbitrary relations of @{typ "'state \<Rightarrow> 'state
set"} with \<open>LocalOp\<close>, and conditions of type @{typ "'s \<Rightarrow>
bool"} are similarly shallowly embedded. This arrangement allows the
end-user to select their own level of atomicity.

The sequential composition operator and control constructs are
standard. We add the infinite looping construct \<open>Loop\<close> so we
can construct single-state reactive systems; this has implications for
fairness assertions.

\<close>

type_synonym 's bexp = "'s \<Rightarrow> bool"

datatype ('answer, 'location, 'question, 'state) com
  = Request  "'location" "'state \<Rightarrow> 'question" "'answer \<Rightarrow> 'state \<Rightarrow> 'state set"        ("\<lbrace>_\<rbrace> Request _ _"  [0, 70, 70] 71)
  | Response "'location" "'question \<Rightarrow> 'state \<Rightarrow> ('state \<times> 'answer) set"               ("\<lbrace>_\<rbrace> Response _"  [0, 70] 71)
  | LocalOp  "'location" "'state \<Rightarrow> 'state set"                                       ("\<lbrace>_\<rbrace> LocalOp _" [0, 70] 71)
  | Cond1    "'location" "'state bexp" "('answer, 'location, 'question, 'state) com" ("\<lbrace>_\<rbrace> IF _ THEN _ FI" [0, 0, 0] 71)
  | Cond2    "'location" "'state bexp" "('answer, 'location, 'question, 'state) com"
                           "('answer, 'location, 'question, 'state) com"             ("\<lbrace>_\<rbrace> IF _/ THEN _/ ELSE _/ FI"  [0, 0, 0, 0] 71)
  | Loop     "('answer, 'location, 'question, 'state) com"                           ("LOOP DO _/ OD"  [0] 71)
  | While    "'location" "'state bexp" "('answer, 'location, 'question, 'state) com" ("\<lbrace>_\<rbrace> WHILE _/ DO _/ OD"  [0, 0, 0] 71)
  | Seq      "('answer, 'location, 'question, 'state) com"
              "('answer, 'location, 'question, 'state) com"                           (infixr ";;" 69)
  | Choose   "('answer, 'location, 'question, 'state) com"
              "('answer, 'location, 'question, 'state) com"                           (infixl "\<oplus>" 68)

text\<open>

We provide a one-armed conditional as it is the common form and avoids
the need to discover a label for an internal \<open>SKIP\<close> and/or
trickier proofs about the VCG.

In contrast to classical process algebras, we have local state and
distinct request and response actions. These provide an interface to
Isabelle/HOL's datatypes that avoids the need for binding (ala the
$\pi$-calculus of @{cite [cite_macro=citet] "Milner:1989"}) or large
non-deterministic sums (ala CCS @{cite [cite_macro=citep] \<open>\S2.8\<close>
"Milner:1980"}). Intuitively the requester poses a @{typ "'question"} with
a \<open>Request\<close> command, which upon rendezvous with a
responder's \<open>Response\<close> command receives an @{typ
"'answer"}. The @{typ "'question"} is a deterministic function of the
requester's local state, whereas responses can be
non-deterministic. Note that CIMP does not provide a notion of
channel; these can be modelled by a judicious choice of @{typ
"'question"}.

We also provide a binary external choice operator @{term\<open>Choose\<close>} (infix @{term\<open>(\<oplus>)\<close>}).
Internal choice can be recovered in combination with local operations
(see @{cite [cite_macro=citet] \<open>\S2.3\<close> "Milner:1980"}).

We abbreviate some common commands: \<open>SKIP\<close> is a local
operation that does nothing, and the floor brackets simplify
deterministic \<open>LocalOp\<close>s. We also adopt some syntax magic from
Makarius's \<open>Hoare\<close> and \<open>Multiquote\<close> theories in the Isabelle/HOL
distribution.

\<close>

abbreviation SKIP_syn ("\<lbrace>_\<rbrace>/ SKIP" [0] 71) where
  "\<lbrace>l\<rbrace> SKIP \<equiv> \<lbrace>l\<rbrace> LocalOp (\<lambda>s. {s})"

abbreviation (input) DetLocalOp :: "'location \<Rightarrow> ('state \<Rightarrow> 'state)
                                  \<Rightarrow> ('answer, 'location, 'question, 'state) com" ("\<lbrace>_\<rbrace> \<lfloor>_\<rfloor>" [0, 0] 71) where
  "\<lbrace>l\<rbrace> \<lfloor>f\<rfloor> \<equiv> \<lbrace>l\<rbrace> LocalOp (\<lambda>s. {f s})"

syntax
  "_quote"        :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)" ("\<guillemotleft>_\<guillemotright>" [0] 1000)
  "_antiquote"    :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<acute>_" [1000] 1000)
  "_Assign"       :: "'location \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> ('answer, 'location, 'question, 'state) com" ("(\<lbrace>_\<rbrace> \<acute>_ :=/ _)" [0, 0, 70] 71)
  "_NonDetAssign" :: "'location \<Rightarrow> idt \<Rightarrow> 'b set \<Rightarrow> ('answer, 'location, 'question, 'state) com" ("(\<lbrace>_\<rbrace> \<acute>_ :\<in>/ _)" [0, 0, 70] 71)

abbreviation (input) NonDetAssign :: "'location \<Rightarrow> (('val \<Rightarrow> 'val) \<Rightarrow> 'state \<Rightarrow> 'state) \<Rightarrow> ('state \<Rightarrow> 'val set)
                                   \<Rightarrow> ('answer, 'location, 'question, 'state) com" where
  "NonDetAssign l upd es \<equiv> \<lbrace>l\<rbrace> LocalOp (\<lambda>s. { upd \<langle>e\<rangle> s |e. e \<in> es s })"

translations
  "\<lbrace>l\<rbrace> \<acute>x := e" => "CONST DetLocalOp l \<guillemotleft>\<acute>(_update_name x (\<lambda>_. e))\<guillemotright>"
  "\<lbrace>l\<rbrace> \<acute>x :\<in> es" => "CONST NonDetAssign l (_update_name x) \<guillemotleft>es\<guillemotright>"

parse_translation \<open>
  let
    fun antiquote_tr i (Const (@{syntax_const "_antiquote"}, _) $
          (t as Const (@{syntax_const "_antiquote"}, _) $ _)) = skip_antiquote_tr i t
      | antiquote_tr i (Const (@{syntax_const "_antiquote"}, _) $ t) =
          antiquote_tr i t $ Bound i
      | antiquote_tr i (t $ u) = antiquote_tr i t $ antiquote_tr i u
      | antiquote_tr i (Abs (x, T, t)) = Abs (x, T, antiquote_tr (i + 1) t)
      | antiquote_tr _ a = a
    and skip_antiquote_tr i ((c as Const (@{syntax_const "_antiquote"}, _)) $ t) =
          c $ skip_antiquote_tr i t
      | skip_antiquote_tr i t = antiquote_tr i t;

    fun quote_tr [t] = Abs ("s", dummyT, antiquote_tr 0 (Term.incr_boundvars 1 t))
      | quote_tr ts = raise TERM ("quote_tr", ts);
  in [(@{syntax_const "_quote"}, K quote_tr)] end
\<close>


subsection\<open>Process semantics \label{sec:cimp-semantics} \<close>

text\<open>

Here we define the semantics of a single process's program. We begin
by defining the type of externally-visible behaviour:

\<close>

datatype ('answer, 'question) seq_label
  = sl_Internal ("\<tau>")
  | sl_Send 'question 'answer ("\<guillemotleft>_, _\<guillemotright>")
  | sl_Receive 'question 'answer ("\<guillemotright>_, _\<guillemotleft>")

text\<open>

We define a \emph{labelled transition system} (an LTS) using an
execution-stack style of semantics that avoids special treatment of
the \<open>SKIP\<close>s introduced by a traditional small step
semantics (such as @{cite [cite_macro=citet] \<open>Chapter~14\<close>
"Winskel:1993"}) when a basic command is executed. This was suggested
by Thomas Sewell; @{cite [cite_macro=citet] "PittsAM:opespe"} gave a
semantics to an ML-like language using this approach.

We record the location of the command that was executed to support
fairness constraints.

\<close>

type_synonym ('answer, 'location, 'question, 'state) local_state
  = "('answer, 'location, 'question, 'state) com list \<times> 'location option \<times> 'state"

inductive
  small_step :: "('answer, 'location, 'question, 'state) local_state
               \<Rightarrow> ('answer, 'question) seq_label
               \<Rightarrow> ('answer, 'location, 'question, 'state) local_state \<Rightarrow> bool" ("_ \<rightarrow>\<^bsub>_\<^esub> _" [55, 0, 56] 55)
where
  "\<lbrakk> \<alpha> = action s; s' \<in> val \<beta> s \<rbrakk> \<Longrightarrow> (\<lbrace>l\<rbrace> Request action val # cs, _, s) \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> (cs, Some l, s')"
| "(s', \<beta>) \<in> action \<alpha> s \<Longrightarrow> (\<lbrace>l\<rbrace> Response action # cs, _, s) \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> (cs, Some l, s')"

| "s' \<in> R s \<Longrightarrow> (\<lbrace>l\<rbrace> LocalOp R # cs, _, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (cs, Some l, s')"

| "b s \<Longrightarrow> (\<lbrace>l\<rbrace> IF b THEN c FI # cs, _, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (c # cs, Some l, s)"
| "\<not>b s \<Longrightarrow> (\<lbrace>l\<rbrace> IF b THEN c FI # cs, _, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (cs, Some l, s)"

| "b s \<Longrightarrow> (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI # cs, _, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (c1 # cs, Some l, s)"
| "\<not>b s \<Longrightarrow> (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI # cs, _, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (c2 # cs, Some l, s)"

| "(c # LOOP DO c OD # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s') \<Longrightarrow> (LOOP DO c OD # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s')"

| "b s \<Longrightarrow> (\<lbrace>l\<rbrace> WHILE b DO c OD # cs, _, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (c # \<lbrace>l\<rbrace> WHILE b DO c OD # cs, Some l, s)"
| "\<not> b s \<Longrightarrow> (\<lbrace>l\<rbrace> WHILE b DO c OD # cs, _, s) \<rightarrow>\<^bsub>\<tau>\<^esub> (cs, Some l, s)"

| "(c1 # c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s') \<Longrightarrow> (c1;; c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s')"

| Choose1: "(c1 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s') \<Longrightarrow> (c1 \<oplus> c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s')"
| Choose2: "(c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s') \<Longrightarrow> (c1 \<oplus> c2 # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> (cs', s')"

text\<open>

The following projections operate on local states. These should not
appear to the end-user.

\<close>

abbreviation cPGM :: "('answer, 'location, 'question, 'state) local_state \<Rightarrow> ('answer, 'location, 'question, 'state) com list" where
  "cPGM \<equiv> fst"

abbreviation cTKN :: "('answer, 'location, 'question, 'state) local_state \<Rightarrow> 'location option" where
  "cTKN s \<equiv> fst (snd s)"

abbreviation cLST :: "('answer, 'location, 'question, 'state) local_state \<Rightarrow> 'state" where
  "cLST s \<equiv> snd (snd s)"


subsection\<open>System steps \label{sec:cimp-system-steps}\<close>

text\<open>

A global state maps process names to process' local states. One might
hope to allow processes to have distinct types of local state, but
there remains no good solution yet in a simply-typed setting; see
@{cite [cite_macro=citet] "DBLP:journals/entcs/SchirmerW09"}.

\<close>

type_synonym ('answer, 'location, 'proc, 'question, 'state) global_state
  = "'proc \<Rightarrow> ('answer, 'location, 'question, 'state) local_state"

type_synonym ('proc, 'state) local_states
  = "'proc \<Rightarrow> 'state"

text\<open>

An execution step of the overall system is either any enabled internal
@{term "\<tau>"} step of any process, or a communication rendezvous between
two processes. For the latter to occur, a @{const "Request"} action
must be enabled in process @{term "p1"}, and a @{const "Response"}
action in (distinct) process @{term "p2"}, where the request/response
labels @{term "\<alpha>"} and @{term "\<beta>"} (semantically) match.

We also track global communication history here to support assertional
reasoning (see \S\ref{sec:cimp-invariants}).

\<close>

type_synonym ('answer, 'question) event = "'question \<times> 'answer"
type_synonym ('answer, 'question) history = "('answer, 'question) event list"

record ('answer, 'location, 'proc, 'question, 'state) system_state =
  GST :: "('answer, 'location, 'proc, 'question, 'state) global_state"
  HST :: "('answer, 'question) history"

inductive \<comment>\<open> This is a predicate of the current state, so the successor state comes first. \<close>
  system_step :: "'proc set
              \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) system_state
              \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) system_state
              \<Rightarrow> bool"
where
  LocalStep: "\<lbrakk> GST sh p \<rightarrow>\<^bsub>\<tau>\<^esub> ls'; GST sh' = (GST sh)(p := ls'); HST sh' = HST sh \<rbrakk> \<Longrightarrow> system_step {p} sh' sh"
| CommunicationStep: "\<lbrakk> GST sh p \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> ls1'; GST sh q \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> ls2'; p \<noteq> q;
                        GST sh' = (GST sh)(p := ls1', q := ls2'); HST sh' = HST sh @ [(\<alpha>, \<beta>)] \<rbrakk> \<Longrightarrow> system_step {p, q} sh' sh"

text\<open>

In classical process algebras matching communication actions yield
\<open>\<tau>\<close> steps, which aids nested parallel composition
and the restriction operation @{cite [cite_macro=citep]
\<open>\S2.2\<close> "Milner:1980"}. As CIMP does not provide either
we do not need to hide communication labels. In CCS/CSP it is not
clear how one reasons about the communication history, and it seems
that assertional reasoning about these languages is not well
developed.

\<close>

text\<open>

We define predicates over communication histories and system states. These are uncurried to ease composition.

\<close>

type_synonym ('answer, 'location, 'proc, 'question, 'state) state_pred
  = "('answer, 'location, 'proc, 'question, 'state) system_state \<Rightarrow> bool"

text\<open>

The \<open>LST\<close> operator (written as a postfix \<open>\<down>\<close>) projects
the local states of the processes from a \<^typ>\<open>('answer, 'location, 'proc, 'question, 'state) system_state\<close>, i.e. it
discards control location information.

Conversely the \<open>LSTP\<close> operator lifts predicates over
local states into predicates over \<^typ>\<open>('answer, 'location, 'proc, 'question, 'state) system_state\<close>.

Predicates that do not depend on control locations were termed @{emph
\<open>universal assertions\<close>} by @{cite [cite_macro=citet]
\<open>\S3.6\<close> "DBLP:journals/acta/LevinG81"}.

\<close>

type_synonym ('proc, 'state) local_state_pred
  = "('proc, 'state) local_states \<Rightarrow> bool"

definition LST :: "('answer, 'location, 'proc, 'question, 'state) system_state
                 \<Rightarrow> ('proc, 'state) local_states" ("_\<down>" [1000] 1000) where
  "s\<down> = cLST \<circ> GST s"

abbreviation (input) LSTP :: "('proc, 'state) local_state_pred
                            \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred" where
  "LSTP P \<equiv> \<lambda>s. P s\<down>"


subsection\<open>Control predicates \label{sec:cimp-control-predicates}\<close>

text\<open>

Following @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80"}\footnote{@{cite [cite_macro=citet]
"MannaPnueli:1995"} also develop a theory of locations. I think
Lamport attributes control predicates to Owicki in her PhD thesis
(under Gries). I did not find a treatment of procedures. @{cite
[cite_macro=citet] "MannaPnueli:1991"} observe that a notation for
making assertions over sets of locations reduces clutter
significantly.}, we define the \<open>at\<close> predicate, which
holds of a process when control resides at that location. Due to
non-determinism processes can be \<open>at\<close> a set of locations;
it is more like ``a statement with this location is enabled'', which
incidentally handles non-unique locations. Lamport's language is
deterministic, so he doesn't have this problem. This also allows him
to develop a stronger theory about his control predicates.

\<close>

type_synonym 'location label = "'location set"

primrec
  atC :: "('answer, 'location, 'question, 'state) com \<Rightarrow> 'location label"
where
  "atC (\<lbrace>l\<rbrace> Request action val) = {l}"
| "atC (\<lbrace>l\<rbrace> Response action) = {l}"
| "atC (\<lbrace>l\<rbrace> LocalOp f) = {l}"
| "atC (\<lbrace>l\<rbrace> IF _ THEN _ FI) = {l}"
| "atC (\<lbrace>l\<rbrace> IF _ THEN _ ELSE _ FI) = {l}"
| "atC (\<lbrace>l\<rbrace> WHILE _ DO _ OD) = {l}"
| "atC (LOOP DO c OD) = atC c"
| "atC (c1;; c2) = atC c1"
| "atC (c1 \<oplus> c2) = atC c1 \<union> atC c2"

primrec atCs :: "('answer, 'location, 'question, 'state) com list \<Rightarrow> 'location label" where
  "atCs [] = {}"
| "atCs (c # _) = atC c"

text\<open>

We provide the following definitions to the end-user.

\<open>AT\<close> maps process names to a predicate that is true of
locations where control for that process resides, and the abbreviation \<open>at\<close> provides a conventional
way to use it. The constant \<open>atS\<close> specifies that control for process \<open>p\<close> resides at one of
the given locations. This stands in for, and generalises, the \<open>in\<close> predicate of @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80"}.

\<close>

definition AT :: "('answer, 'location, 'proc, 'question, 'state) system_state \<Rightarrow> 'proc \<Rightarrow> 'location label" where
  "AT s p = atCs (cPGM (GST s p))"

abbreviation at :: "'proc \<Rightarrow> 'location \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred" where
  "at p l s \<equiv> l \<in> AT s p"

definition atS :: "'proc \<Rightarrow> 'location set \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred" where
  "atS p ls s = (\<exists>l\<in>ls. at p l s)"

(* FIXME rename, document, rules. Identifies a process's control state label precisely as one element of a set. *)
definition atLs :: "'proc \<Rightarrow> 'location label set \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred" where
  "atLs p labels s = (AT s p \<in> labels)"

(* FIXME rename, document. Identifies a process's control state label precisely. Relate atL to at/atS, ex/ *)
abbreviation (input) atL :: "'proc \<Rightarrow> 'location label \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred" where
  "atL p label \<equiv> atLs p {label}"

(* FIXME rename, document. Processes are at the given labels. *)
definition atPLs :: "('proc \<times> 'location label) set \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred" where
  "atPLs pls = (\<^bold>\<forall>p label. \<langle>(p, label) \<in> pls\<rangle> \<^bold>\<longrightarrow> atL p label)"

text\<open>

The constant \<open>taken\<close> provides a way of identifying which transition was taken. It is somewhat like
Lamport's \<open>after\<close>, but not quite due to the presence of non-determinism here. This does not work well
for invariants or preconditions.

\<close>

definition taken :: "'proc \<Rightarrow> 'location \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred" where
  "taken p l s \<longleftrightarrow> cTKN (GST s p) = Some l"

text\<open>

\label{sec:cimp-termination}

A process is terminated if it not at any control location.

\<close>

abbreviation (input) terminated :: "'proc \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred" where
  "terminated p \<equiv> atL p {}"

text\<open>

A complete system consists of one program per process, and a (global)
constraint on their initial local states. From these we can construct
the set of initial global states and all those reachable by system
steps (\S\ref{sec:cimp-system-steps}).

\<close>

type_synonym ('answer, 'location, 'proc, 'question, 'state) programs
  = "'proc \<Rightarrow> ('answer, 'location, 'question, 'state) com"

record ('answer, 'location, 'proc, 'question, 'state) pre_system =
  PGMs :: "('answer, 'location, 'proc, 'question, 'state) programs"
  INIT :: "('proc, 'state) local_state_pred"

definition
  initial_state :: "('answer, 'location, 'proc, 'question, 'state, 'ext) pre_system_ext
                   \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) global_state
                   \<Rightarrow> bool"
where
  "initial_state sys s = ((\<forall>p. cPGM (s p) = [PGMs sys p] \<and> cTKN (s p) = None) \<and> INIT sys (cLST \<circ> s))"

text\<open>

We construct infinite runs of a system by allowing stuttering, i.e., arbitrary repetitions of states
following @{cite [cite_macro=citet] \<open>Chapter~8\<close>"Lamport:2002"}, by taking the reflexive
closure of the @{const system_step} relation. Therefore terminated
programs infinitely repeat their final state (but note our definition
of terminated processes in \S\ref{sec:cimp-termination}).

Some accounts define stuttering as the @{emph \<open>finite\<close>} repetition of states. With or without this constraint
\<open>prerun\<close> contains @{emph \<open>junk\<close>} in the form of unfair runs, where particular processes do not progress.

\<close>

definition
  system_step_reflclp :: "('answer, 'location, 'proc, 'question, 'state) system_state seq_pred"
where
  "system_step_reflclp \<sigma> \<longleftrightarrow> (\<lambda>sh sh'. \<exists>pls. system_step pls sh' sh)\<^sup>=\<^sup>= (\<sigma> 0) (\<sigma> 1)"

definition
  prerun :: "('answer, 'location, 'proc, 'question, 'state, 'ext) pre_system_ext
         \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) system_state seq_pred"
where
  "prerun sys = ((\<lambda>\<sigma>. initial_state sys (GST (\<sigma> 0)) \<and> HST (\<sigma> 0) = []) \<^bold>\<and> \<box>system_step_reflclp)"

definition \<comment>\<open> state-based invariants only \<close>
  prerun_valid :: "('answer, 'location, 'proc, 'question, 'state, 'ext) pre_system_ext
                   \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred \<Rightarrow> bool" ("_ \<Turnstile>\<^bsub>pre\<^esub> _" [11, 0] 11) (* FIXME priorities *)
where
  "(sys \<Turnstile>\<^bsub>pre\<^esub> \<phi>) \<longleftrightarrow> (\<forall>\<sigma>. prerun sys \<sigma> \<longrightarrow> (\<box>\<lceil>\<phi>\<rceil>) \<sigma>)"

text\<open>

A \<open>run\<close> of a system is a @{const \<open>prerun\<close>} that satisfies the \<open>FAIR\<close> requirement.
Typically this would include @{emph \<open>weak fairness\<close>} for every transition of every process.

\<close>

record ('answer, 'location, 'proc, 'question, 'state) system =
  "('answer, 'location, 'proc, 'question, 'state) pre_system"
+ FAIR :: "('answer, 'location, 'proc, 'question, 'state) system_state seq_pred"

definition
  run :: "('answer, 'location, 'proc, 'question, 'state) system
       \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) system_state seq_pred"
where
  "run sys = (prerun sys \<^bold>\<and> FAIR sys)"

definition
  valid :: "('answer, 'location, 'proc, 'question, 'state) system
                   \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) system_state seq_pred \<Rightarrow> bool" ("_ \<Turnstile> _" [11, 0] 11) (* FIXME priorities *)
where
  "(sys \<Turnstile> \<phi>) \<longleftrightarrow> (\<forall>\<sigma>. run sys \<sigma> \<longrightarrow> \<phi> \<sigma>)"
(*<*)

end
(*>*)
