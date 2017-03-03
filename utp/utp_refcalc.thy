section {* Refinement calculus *}

theory utp_refcalc
  imports utp_designs
begin

abbreviation spec_stat :: "('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> hrel_des" where
"spec_stat w pre post \<equiv> (pre \<turnstile>\<^sub>n w:[\<lceil>post\<rceil>\<^sub>>])"

syntax
  "_spec_stat" :: "salpha \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> hrel_des" ("_:[_,_]\<^sub>u" [70,0,0] 70)

translations
  "_spec_stat w pre post" \<rightleftharpoons> "CONST spec_stat w pre post"

lemma rc_strengthen_post:
  assumes "`post' \<Rightarrow> post`"
  shows "w:[pre, post]\<^sub>u \<sqsubseteq> w:[pre, post']\<^sub>u"
  using assms by (rel_auto)

lemma rc_weaken_pre:
  assumes "`pre \<Rightarrow> pre'`"
  shows "w:[pre, post]\<^sub>u \<sqsubseteq> w:[pre', post]\<^sub>u"
  using assms by (rel_auto)

lemma rc_skip:
  assumes "`pre \<Rightarrow> post`"
  shows "w:[pre, post]\<^sub>u \<sqsubseteq> II\<^sub>D"
  using assms by (rel_auto)

lemma rc_seq:
  assumes "vwb_lens w"
  shows "w:[pre, post]\<^sub>u \<sqsubseteq> w:[pre, mid]\<^sub>u ;; w:[mid, post]\<^sub>u"
  using assms
  by (rel_auto, metis vwb_lens.put_eq)
end