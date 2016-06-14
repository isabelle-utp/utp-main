section {* Program and observational variables *}

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

definition obs :: "('\<Sigma>, '\<O>) oalpha" ("\<O>") where
"obs = VAR more"

definition state_make :: "'\<Sigma> \<times> '\<O> \<Longrightarrow> ('\<Sigma>, '\<O>) state_scheme" where
"state_make = \<lparr> lens_get = \<lambda> v. (palpha\<^sub>u v, more v)
              , lens_put = \<lambda> s v. \<lparr> palpha\<^sub>u = fst v, \<dots> = snd v \<rparr> \<rparr>"

lemma state_make_bij:
  "bij_lens state_make"
  by (unfold_locales, simp_all add: state_make_def)
(*
definition state_map :: 
  "('\<Sigma>\<^sub>1 \<Longrightarrow> '\<Sigma>\<^sub>2) \<Rightarrow> ('\<O>\<^sub>1 \<Longrightarrow> '\<O>\<^sub>2) \<Rightarrow> (('\<Sigma>\<^sub>1, '\<O>\<^sub>1) state_scheme \<Longrightarrow> ('\<Sigma>\<^sub>2, '\<O>\<^sub>2) state_scheme)" where
"state_map = "
*) 

syntax
  "_svid_palpha" :: "svid" ("\<^bold>v")
  "_svid_obs"    :: "svid" ("\<O>")

translations
  "_svid_palpha" => "CONST palpha"
  "_svid_obs" => "CONST obs"

lemma palpha_uvar [simp]: "uvar \<^bold>v"
  by (unfold_locales, simp_all add: palpha_def)

lemma obs_uvar [simp]: "uvar \<O>"
  by (unfold_locales, simp_all add: obs_def)

lemma palpha_obs_indep [simp]:
  "\<^bold>v \<bowtie> \<O>" "\<O> \<bowtie> \<^bold>v"
  by (auto intro: lens_indepI simp add: palpha_def obs_def)

lemma palpha_obs_bij: "bij_lens (\<^bold>v +\<^sub>L \<O>)"
  by (unfold_locales, simp_all add: lens_plus_def prod.case_eq_if obs_def palpha_def)

lemma palpha_obs_state: "\<^bold>v +\<^sub>L \<O> \<approx>\<^sub>L 1\<^sub>L"
  using bij_lens_equiv_id palpha_obs_bij by blast

end