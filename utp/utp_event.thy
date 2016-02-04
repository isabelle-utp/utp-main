section {* UTP events *}

theory utp_event
  imports utp_pred
begin

type_synonym ('a, '\<theta>) chan = "'a \<Rightarrow> '\<theta>"
type_synonym '\<theta> event = '\<theta>

definition chan_type :: "('a, '\<theta>) chan \<Rightarrow> 'a set" ("\<delta>\<^sub>u")
where "\<delta>\<^sub>u(c) = UNIV"

definition event :: "('a, '\<theta>) chan \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<theta> event, '\<alpha>) uexpr" ("'(_,/ _')\<^sub>e")
where "(c, v)\<^sub>e = \<guillemotleft>c\<guillemotright>\<lparr>v\<rparr>\<^sub>u"

declare event_def [upred_defs]

end