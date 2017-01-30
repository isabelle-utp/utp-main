(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_event.thy                                                        *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 9 Jan 2017 *)

section {* UTP Events *}

theory utp_event
imports utp_pred
begin

text {*
  Like values, it is difficult to introduce events and channels generically
  due to the fact that channels can have arbitrary parametrisations in terms
  of HOL types. Hence, they have to be constructed in an \textit{ad hoc}
  manner for each CSP model. A generic model may be realisable if we added
  support for something like `open datatypes' (in analogy to open records).
  Such, however, constitutes a considerable implementation effort. Another
  possibility would be a deep model of channels, making use of the axiomatic
  value model; but this would forfeit the benefit of host-level typing. A
  fully compositional solution for channel declarations is pending work.
*}

subsection {* Events *}

text {*
  Events of some (event) type @{typ "'\<theta>"} are just the elements of that type.
*}

type_synonym '\<theta> event = "'\<theta>"

subsection {* Channels *}

text {*
  Typed channels are modelled by functions. Below, @{typ "'a"} determines the
  channel type and @{typ "'\<theta>"} the underlying event type. Hence as we expect,
  applying a channel to an element of its type yields an event. We note that
  @{typ "'\<theta>"} may potentially encode the events of several channels. Although
  this is not formalised, we may also claim that the function is an injection.
*}

type_synonym ('a, '\<theta>) chan = "'a \<Rightarrow> '\<theta> event"

paragraph {* Channel Operators *}

text {*
  The (Z) type of a channel corresponds to the entire carrier of the underlying
  HOL type of that channel. Note: Ask Simon why he defined this function!
*}

definition chan_type :: "('a, '\<theta>) chan \<Rightarrow> 'a set" ("\<delta>\<^sub>u")
where "\<delta>\<^sub>u c = UNIV"

text {*
  The next function creates an expression that yields a channel event, from
  an expression on the channels type @{typ "'a"}. Note: I believe that naming
  is not quite consistent here i.e.~why is a subscript @{text "\<^sub>e"} used rather
  than @{text "\<^sub>u"} as it is usually the case for expressions? Perhaps a better
  name for the function may be @{text "chan_event"} or @{text "chan_apply"}.
  Lastly, I am not convinced of the syntax @{text "(c, e)\<^sub>e"}.
*}

definition event ::
  "('a, '\<theta>) chan \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<theta> event, '\<alpha>) uexpr" ("'(_,/ _')\<^sub>e") where
[upred_defs]: "(c, e)\<^sub>e = \<guillemotleft>c\<guillemotright>\<lparr>e\<rparr>\<^sub>u"
end