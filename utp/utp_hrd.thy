section {* Hybrid reactive designs *}

theory utp_hrd
imports 
  utp_designs
  utp_reactive
begin

record 't::linordered_semidom htime =
  htime :: 't

type_synonym ('t, '\<theta>, '\<alpha>) alphabet_hrd = "('\<theta>, ('t, '\<alpha>) htime_scheme) alphabet_rp"
type_synonym ('t, '\<theta>, '\<alpha>, '\<beta>) hrd = "(('t, '\<theta>, '\<alpha>) alphabet_hrd, ('t, '\<theta>, '\<beta>) alphabet_hrd) relation"

definition "time\<^sub>h = VAR htime"

definition "time = time\<^sub>h ;\<^sub>L \<Sigma>\<^sub>R"

definition "\<Sigma>\<^sub>h = VAR more"

definition "\<Sigma>\<^sub>H = \<Sigma>\<^sub>h ;\<^sub>L \<Sigma>\<^sub>R"

lemma time\<^sub>h_uvar [simp]: "uvar time\<^sub>h"
  by (unfold_locales, simp_all add: time\<^sub>h_def)

lemma \<Sigma>\<^sub>h_uvar [simp]: "uvar \<Sigma>\<^sub>h"
  by (unfold_locales, simp_all add: \<Sigma>\<^sub>h_def)

lemma time_uvar [simp]: "uvar time"
  by (metis comp_vwb_lens rea_lens_under_des_lens sublens_pres_vwb time\<^sub>h_uvar time_def uvar_des_lens)

lemma \<Sigma>\<^sub>H_uvar [simp]: "uvar \<Sigma>\<^sub>H"
  by (metis \<Sigma>\<^sub>H_def \<Sigma>\<^sub>h_uvar comp_vwb_lens rea_lens_under_des_lens sublens_pres_vwb uvar_des_lens)

definition lift_hrd :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>H") where
"\<lceil>P\<rceil>\<^sub>H = P \<oplus>\<^sub>p (\<Sigma>\<^sub>H \<times>\<^sub>L \<Sigma>\<^sub>H)"

definition drop_hrd :: "_ \<Rightarrow> _" ("\<lfloor>_\<rfloor>\<^sub>H") where
"\<lfloor>P\<rfloor>\<^sub>H = P \<restriction>\<^sub>p (\<Sigma>\<^sub>H \<times>\<^sub>L \<Sigma>\<^sub>H)"

definition "\<L> = $time\<acute> - $time"

definition "HR1(P) = (P \<and> $time \<le>\<^sub>u $time\<acute>)"

definition "HR = HR1 \<circ> RH"

definition wait'_cond :: "_ \<Rightarrow> _ \<Rightarrow> _" (infix "\<diamondop>" 65) where
"P \<diamondop> Q = (P \<triangleleft> $wait\<acute> \<triangleright> Q)"

definition "Wait n = HR(true \<turnstile> ((\<L> <\<^sub>u n) \<diamondop> (\<L> =\<^sub>u n)) \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $tr\<acute> =\<^sub>u $tr)"

definition "hlift(s) = HR(true \<turnstile> \<lceil>\<langle>s\<rangle>\<^sub>a\<rceil>\<^sub>H \<and> $tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute>)"

fun time_trel :: "_ \<times> _ \<Rightarrow> _ \<Rightarrow> _ \<times> _ \<Rightarrow> bool" (infix "\<leadsto>[_]\<^sub>h" 85) where
"(\<sigma>, P) \<leadsto>[t]\<^sub>h (\<rho>, Q) \<longleftrightarrow> (hlift(\<sigma>) ;; P) \<sqsubseteq> (hlift(\<rho>) ;; Wait t ;; Q)"

lemma "(Wait m ;; Wait n) = Wait (m + n)"
  oops

lemma "(\<sigma>, Wait (m + n)) \<leadsto>[m]\<^sub>h (\<sigma>, Wait n)"
  oops

end