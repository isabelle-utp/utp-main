(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_event.thy                                                        *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 30 Jan 2017 *)

section {* UTP Events *}

theory utp_event
imports utp_pred
begin

subsection {* Events *}

text {* Events of some type @{typ "'\<theta>"} are just the elements of that type. *}

type_synonym '\<theta> event = "'\<theta>"

subsection {* Channels *}

text {*
  Typed channels are modelled as functions. Below, @{typ "'a"} determines the
  channel type and @{typ "'\<theta>"} the underlying event type. As with values, it
  is difficult to introduce channels as monomorphic types due to the fact that
  they can have arbitrary parametrisations in term of @{typ "'a"}. Applying a
  channel to an element of its type yields an event, as we may expect. Though
  this is not formalised here, we may also sensibly assume that all channel-
  representing functions are injective. Note: is there benefit in formalising
  this here?
*}

type_synonym ('a, '\<theta>) chan = "'a \<Rightarrow> '\<theta> event"

text {*
  A downside of the approach is that the event type @{typ "'\<theta>"} must be able
  to encode \emph{all} events of a process model, and hence cannot be fixed
  upfront for a single channel or channel set. To do so, we actually require
  a notion of `extensible' datatypes, in analogy to extensible record types.
  Another solution is to encode a notion of channel scoping that namely uses
  @{type sum} types to lift channel types into extensible ones, that is using
  channel-set specific scoping operators. This is a current work in progress.
*}

subsubsection {* Operators *}

text {*
  The Z type of a channel corresponds to the entire carrier of the underlying
  HOL type of that channel. Strictly, the function is redundant but was added
  to mirror the mathematical account in [?]. (TODO: Ask Simon Foster for [?])
*}

definition chan_type :: "('a, '\<theta>) chan \<Rightarrow> 'a set" ("\<delta>\<^sub>u") where
[upred_defs]: "\<delta>\<^sub>u c = UNIV"

text {*
  The next lifted function creates an expression that yields a channel event,
  from an expression on the channel type @{typ "'a"}.
*}

definition chan_apply ::
  "('a, '\<theta>) chan \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<theta> event, '\<alpha>) uexpr" ("'(_\<cdot>/_')\<^sub>u") where
[upred_defs]: "(c\<cdot>e)\<^sub>u = \<guillemotleft>c\<guillemotright>(e)\<^sub>a"

lemma unrest_chan_apply [unrest]: "x \<sharp> e \<Longrightarrow> x \<sharp> (c\<cdot>e)\<^sub>u"
  by (rel_auto)

lemma usubst_chan_apply [usubst]: "\<sigma> \<dagger> (c\<cdot>v)\<^sub>u = (c\<cdot>\<sigma> \<dagger> v)\<^sub>u"
  by (rel_auto)

end