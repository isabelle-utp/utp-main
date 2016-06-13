section {* Program variables *}

theory utp_state
  imports utp_rel
begin

record '\<Sigma> state =
  palpha\<^sub>u :: '\<Sigma>

type_synonym ('\<Sigma>, '\<O>) palpha = "'\<Sigma> \<Longrightarrow> ('\<Sigma>, '\<O>) state_scheme"

type_synonym ('\<Sigma>, '\<O>) oalpha = "'\<O> \<Longrightarrow> ('\<Sigma>, '\<O>) state_scheme"

type_synonym ('\<Sigma>\<^sub>1, '\<Sigma>\<^sub>2, '\<O>\<^sub>1, '\<O>\<^sub>2) urel = "(('\<Sigma>\<^sub>1, '\<O>\<^sub>1) state_scheme, ('\<Sigma>\<^sub>2, '\<O>\<^sub>2) state_scheme) relation"
type_synonym ('\<Sigma>, '\<O>) hrel = "('\<Sigma>, '\<O>) state_scheme hrelation"

definition palpha :: "('\<Sigma>, '\<O>) palpha" ("\<^bold>v") where
"palpha = VAR palpha\<^sub>u"

syntax
  "_svid_palpha"  :: "svid" ("\<^bold>v")

translations
  "_svid_palpha" => "CONST palpha"

type_synonym ('a, '\<alpha>) lvar = "('a list, '\<alpha>) uvar"

type_synonym ('a, '\<Sigma>, '\<O>) uproc = "'a \<Rightarrow> ('\<Sigma>, '\<O>) hrel"

definition 
  val_parm :: "('a::two, '\<Sigma>) lvar \<Rightarrow> (('a, '\<Sigma>) uvar \<Rightarrow> ('\<Sigma>, '\<O>) hrel) 
               \<Rightarrow> (('a, '\<alpha>) uexpr, '\<Sigma>, '\<O>) uproc"
where "val_parm x P = undefined"


end