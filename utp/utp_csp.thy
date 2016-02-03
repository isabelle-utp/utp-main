section {* Theory of CSP *}

theory utp_csp
  imports utp_reactive
begin

abbreviation wait_f::"('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("_\<^sub>f" [1000] 1000)
where "wait_f R \<equiv> R\<lbrakk>false/$wait\<acute>\<rbrakk>"

abbreviation wait_t::"('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("_\<^sub>t" [1000] 1000)
where "wait_t R \<equiv> R\<lbrakk>true/$wait\<acute>\<rbrakk>"

definition "Stop = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition "Skip = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> (\<not> $wait\<acute>) \<and> \<lceil>II\<rceil>\<^sub>R))"

definition "SKIP = RH(\<exists> $ref \<bullet> II)"

definition "Chaos = RH(false \<turnstile> true)"

definition Guard :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infix "&\<^sub>u" 65)
where "g &\<^sub>u A = RH((g \<Rightarrow> \<not> A\<^sup>f\<^sub>f) \<turnstile> ((g \<and> A\<^sup>t\<^sub>f) \<or> ((\<not> g) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"

definition ExtChoice :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infixl "\<box>" 65)
where "A\<^sub>1 \<box> A\<^sub>2 = RH(\<not> A\<^sub>1\<^sup>f\<^sub>f \<and> \<not> A\<^sub>2\<^sup>f\<^sub>f \<turnstile> (A\<^sub>1\<^sup>t\<^sub>f \<and> A\<^sub>2\<^sup>t\<^sub>f) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (A\<^sub>1\<^sup>t\<^sub>f \<or> A\<^sub>2\<^sup>t\<^sub>f))"

definition "CSP1(P) = (P \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

text {* CSP2 is just H2 since the type system will automatically have J identifying the reactive
        variables as required. *}

definition "CSP2(P) = H2(P)"

definition "CSP3(P) = (SKIP ;; P)"

definition "CSP4(P) = (P ;; SKIP)"


end