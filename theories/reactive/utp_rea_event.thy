section \<open> Events for Reactive Processes \<close>

theory utp_rea_event
imports "UTP1.utp"
begin

subsection \<open> Events \<close>

text \<open> Events of some type @{typ "'\<theta>"} are just the elements of that type. \<close>

type_synonym '\<theta> event = "'\<theta>"

subsection \<open> Channels \<close>

text \<open>
  Typed channels are modelled as prisms. Below, @{typ "'a"} determines the
  channel type and @{typ "'\<theta>"} the underlying event alphabet type. As with values, it
  is difficult to introduce channels as monomorphic types due to the fact that
  they can have arbitrary parametrisations in term of @{typ "'a"}. Applying a
  channel to an element of its type yields an event, as we may expect. Though
  this is not formalised here, we may also sensibly assume that all channel-
  representing functions are injective.
\<close>

type_synonym ('a, '\<theta>) chan = "'a \<Longrightarrow>\<^sub>\<triangle> '\<theta> event"

text \<open>
  A downside of the approach is that the event type @{typ "'\<theta>"} must be able
  to encode \emph{all} events of a process model, and hence cannot be fixed
  upfront for a single channel or channel set. To do so, we actually require
  a notion of `extensible' datatypes, in analogy to extensible record types.
  Another solution is to encode a notion of channel scoping that namely uses
  @{type sum} types to lift channel types into extensible ones, that is using
  channel-set specific scoping operators. This is a current work in progress.
\<close>

subsubsection \<open> Operators \<close>

text \<open>
  The next lifted function creates an expression that yields a channel event,
  from an expression on the channel type @{typ "'a"}.
\<close>

definition chan_apply ::
  "('a, '\<theta>) chan \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<theta> event, '\<alpha>) uexpr" ("'(_\<cdot>/_')\<^sub>u") where
[upred_defs]: "(c\<cdot>e)\<^sub>u = uop (build\<^bsub>c\<^esub>) e"

no_utp_lift chan_apply (0)

lemma unrest_chan_apply [unrest]: "x \<sharp> e \<Longrightarrow> x \<sharp> (c\<cdot>e)\<^sub>u"
  by (rel_auto)

lemma usubst_chan_apply [usubst]: "\<sigma> \<dagger> (c\<cdot>v)\<^sub>u = (c\<cdot>\<sigma> \<dagger> v)\<^sub>u"
  by (rel_auto)

lemma msubst_event [usubst]:
  "(c\<cdot>v x)\<^sub>u\<lbrakk>x\<rightarrow>u\<rbrakk> = (c\<cdot>(v x)\<lbrakk>x\<rightarrow>u\<rbrakk>)\<^sub>u"
  by (pred_simp)

lemma msubst_event_2 [usubst]:
  "(c\<cdot>v x y)\<^sub>u\<lbrakk>(x,y)\<rightarrow>u\<rbrakk> = (c\<cdot>(v x y)\<lbrakk>(x,y)\<rightarrow>u\<rbrakk>)\<^sub>u"
  by (pred_simp)+

lemma aext_event [alpha]: "(c\<cdot>v)\<^sub>u \<oplus>\<^sub>p a = (c\<cdot>v \<oplus>\<^sub>p a)\<^sub>u"
  by (pred_auto)

end