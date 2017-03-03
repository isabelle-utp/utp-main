section {* Theory of invariants *}

theory utp_invariants
  imports utp_designs
begin

subsection {* Operation invariants *}

definition "OIH(\<psi>)(D) = (D \<and> ($ok \<and> \<not> D\<^sup>f \<Rightarrow> \<psi>))"

declare OIH_def [upred_defs]

lemma OIH_design:
  assumes "D is H1_H2"
  shows "OIH(\<psi>)(D) = ((\<not> D\<^sup>f) \<turnstile> (D\<^sup>t \<and> \<psi>))"
proof -
  have "OIH(\<psi>)(D) = (((\<not> D\<^sup>f) \<turnstile> D\<^sup>t) \<and> ($ok \<and> \<not> D\<^sup>f \<Rightarrow> \<psi>))"
    by (metis H1_H2_commute H1_H2_is_design H1_idem Healthy_def' OIH_def assms)
  also have "... = (($ok \<and> \<not> D\<^sup>f \<Rightarrow> $ok\<acute> \<and> D\<^sup>t) \<and> ($ok \<and> \<not> D\<^sup>f \<Rightarrow> \<psi>))"
    by (simp add: design_def)
  also have "... = ((\<not> D\<^sup>f) \<turnstile> (D\<^sup>t \<and> \<psi>))"
    by (pred_auto)
  finally show ?thesis .
qed

lemma OIH_idem:
  assumes "D is H1_H2" "$ok\<acute> \<sharp> \<psi>"
  shows "OIH(\<psi>)(OIH(\<psi>)(D)) = OIH(\<psi>)(D)"
  using assms
  by (simp add: OIH_design design_is_H1_H2 unrest) (simp add: design_def usubst, rel_auto)

lemma OIH_of_design:
  "$ok\<acute> \<sharp> P \<Longrightarrow> OIH(\<psi>)(P \<turnstile> Q) = (P \<turnstile> (Q \<and> \<psi>))"
  by (simp add: OIH_def design_def usubst, rel_auto)

subsection {* State invariants *}

definition "ISH(\<psi>)(D) = (D \<or> ($ok \<and> \<not> D\<^sup>f \<and> \<lceil>\<psi>\<rceil>\<^sub>< \<Rightarrow> $ok\<acute> \<and> D\<^sup>t))"

declare ISH_def [upred_defs]

lemma ISH_design: "ISH(\<psi>)(D) = (\<not> D\<^sup>f \<and> \<lceil>\<psi>\<rceil>\<^sub><) \<turnstile> D\<^sup>t"
  by (rel_auto, metis+)

lemma ISH_idem: "ISH(\<psi>)(ISH(\<psi>)(D)) = ISH(\<psi>)(D)"
  by (simp add: ISH_design usubst design_def, pred_auto)

lemma ISH_of_design:
  "\<lbrakk> $ok\<acute> \<sharp> P; $ok\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> ISH(\<psi>)(P \<turnstile> Q) = ((P \<and> \<lceil>\<psi>\<rceil>\<^sub><) \<turnstile> Q)"
  by (simp add: ISH_design design_def usubst, pred_auto)

definition "OSH(\<psi>)(D) = (D \<and> ($ok \<and> \<not> D\<^sup>f \<and> \<lceil>\<psi>\<rceil>\<^sub>< \<Rightarrow> \<lceil>\<psi>\<rceil>\<^sub>>))"

declare OSH_def [upred_defs]

lemma OSH_as_OIH:
  "OSH(\<psi>)(D) = OIH(\<lceil>\<psi>\<rceil>\<^sub>< \<Rightarrow> \<lceil>\<psi>\<rceil>\<^sub>>)(D)"
  by (simp add: OSH_def OIH_def, pred_auto)

lemma OSH_design:
  assumes "D is H1_H2"
  shows "OSH(\<psi>)(D) = ((\<not> D\<^sup>f) \<turnstile> (D\<^sup>t \<and> (\<lceil>\<psi>\<rceil>\<^sub>< \<Rightarrow> \<lceil>\<psi>\<rceil>\<^sub>>)))"
  by (simp add: OSH_as_OIH OIH_design assms)

lemma OSH_of_design:
  "\<lbrakk> $ok\<acute> \<sharp> P; $ok\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> OSH(\<psi>)(P \<turnstile> Q) = (P \<turnstile> (Q \<and> (\<lceil>\<psi>\<rceil>\<^sub>< \<Rightarrow> \<lceil>\<psi>\<rceil>\<^sub>>)))"
  by (simp add: OSH_design design_is_H1_H2 unrest, simp add: design_def usubst, pred_auto)

definition "SIH(\<psi>) = ISH(\<psi>) \<circ> OSH(\<psi>)"

declare SIH_def [upred_defs]

lemma SIH_of_design:
  "\<lbrakk> $ok\<acute> \<sharp> P; $ok\<acute> \<sharp> Q; ok \<sharp> \<psi> \<rbrakk> \<Longrightarrow> SIH(\<psi>)(P \<turnstile> Q) = ((P \<and> \<lceil>\<psi>\<rceil>\<^sub><) \<turnstile> (Q \<and> \<lceil>\<psi>\<rceil>\<^sub>>))"
  by (simp add: SIH_def OSH_of_design ISH_of_design unrest, pred_auto)
end