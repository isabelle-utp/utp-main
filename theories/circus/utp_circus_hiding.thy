theory utp_circus_hiding
imports utp_circus
begin

definition hide_rea ("hide\<^sub>r") where
[upred_defs]: "hide\<^sub>r P E = (\<^bold>\<exists> s \<bullet> (P\<lbrakk>$tr^\<^sub>u\<guillemotleft>s\<guillemotright>,\<guillemotleft>E\<guillemotright>\<union>\<^sub>u$ref\<acute>/$tr\<acute>,$ref\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr^\<^sub>u(\<guillemotleft>s\<guillemotright>\<restriction>\<^sub>u\<guillemotleft>-E\<guillemotright>)))"

lemma hide_rea_RR_closed [closure]: 
  assumes "P is RR"
  shows "hide\<^sub>r P E is RR"
proof -
  have "RR(hide\<^sub>r (RR P) E) = hide\<^sub>r (RR P) E"
    by (rel_auto, fastforce+)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

definition abs_rea ("abs\<^sub>r") where
[upred_defs]: "abs\<^sub>r P E = (\<not>\<^sub>r ((\<^bold>\<exists> s \<bullet> (\<not>\<^sub>r P\<lbrakk>$tr^\<^sub>u\<guillemotleft>s\<guillemotright>,\<guillemotleft>E\<guillemotright>\<union>\<^sub>u$ref\<acute>/$tr\<acute>,$ref\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr^\<^sub>u(\<guillemotleft>s\<guillemotright>\<restriction>\<^sub>u\<guillemotleft>-E\<guillemotright>))) ;; true\<^sub>r))"

lemma abs_rea_false [rpred]: "abs\<^sub>r false E = false"
  by (rel_simp, metis append.right_neutral order_refl seq_filter_Nil)

lemma abs_rea_true [rpred]: "abs\<^sub>r true\<^sub>r E = true\<^sub>r"
  by (rel_auto)

lemma hide_rea_RC_closed [closure]:
  "RC(hide_rea (RC P) E) = hide_rea (RC P) E"
  oops

definition HidingCSP  :: "('s, 'e) action \<Rightarrow> 'e set \<Rightarrow> ('s, 'e) action" (infixl "\\\<^sub>C" 80) where 
  [upred_defs, rdes_def]: 
  "HidingCSP P E = \<^bold>R\<^sub>s(abs\<^sub>r(pre\<^sub>R(P)) E \<turnstile> hide\<^sub>r (peri\<^sub>R(P)) E \<diamondop> hide\<^sub>r (post\<^sub>R(P)) E)"

lemma "Chaos \\\<^sub>C E = Chaos"
  by (rdes_simp, rel_auto)

lemma [rpred]: "hide\<^sub>r \<E>(true,\<langle>\<rangle>, {\<guillemotleft>a\<guillemotright>}\<^sub>u) {a} = false"
  by (simp add: csp_enable_def, rel_auto)

lemma [rpred]: "hide\<^sub>r \<Phi>(s,\<sigma>,t) E = \<Phi>(s,\<sigma>,t \<restriction>\<^sub>u \<guillemotleft>-E\<guillemotright>)"
  by (rel_auto)


lemma [rpred]: "hide\<^sub>r \<Phi>(true,id,\<langle>\<guillemotleft>a\<guillemotright>\<rangle>) {a} = \<Phi>(true,id,\<langle>\<rangle>)"
  by (rel_auto)

lemma 
  assumes "P is NCSP" 
  shows "P \\\<^sub>C A \\\<^sub>C B = P \\\<^sub>C (A \<union> B)"
  apply (rdes_eq' cls: assms)

lemma "Stop \\\<^sub>C A = Stop"
  by (rdes_eq)

lemma "Miracle \\\<^sub>C A = Miracle"
  by (rdes_eq)

lemma "(a \<^bold>\<rightarrow> Skip) \\\<^sub>C {a} = Skip"
  apply (rdes_eq)

lemma "a \<noteq> b \<Longrightarrow> (a \<^bold>\<rightarrow> Skip) \\\<^sub>C {b} = (a \<^bold>\<rightarrow> Skip)"
  by (rdes_eq)

lemma "a \<noteq> b \<Longrightarrow> (a \<^bold>\<rightarrow> b \<^bold>\<rightarrow> Skip) \\\<^sub>C {b} = (a \<^bold>\<rightarrow> Skip)"
  by (rdes_eq)
(*
\<^bold>R\<^sub>s(\<^bold>\<exists> s \<bullet> P\<lbrakk>$tr^\<^sub>u\<guillemotleft>s\<guillemotright>,\<guillemotleft>e\<guillemotright>\<union>\<^sub>u$ref\<acute>/$tr,$ref\<acute>\<rbrakk> \<and> (($tr\<acute> - $tr) \<restriction>\<^sub>u (- \<guillemotleft>e\<guillemotright>) =\<^sub>u \<guillemotleft>s\<guillemotright>)) ;; Skip"

definition HidingCSP  :: "('s, 'e) action \<Rightarrow> 'e set \<Rightarrow> ('s, 'e) action" (infixr "\\\<^sub>C" 80) where 
  [upred_defs]: "HidingCSP P e = \<^bold>R\<^sub>s(\<^bold>\<exists> s \<bullet> P\<lbrakk>$tr^\<^sub>u\<guillemotleft>s\<guillemotright>,\<guillemotleft>e\<guillemotright>\<union>\<^sub>u$ref\<acute>/$tr,$ref\<acute>\<rbrakk> \<and> (($tr\<acute> - $tr) \<restriction>\<^sub>u (- \<guillemotleft>e\<guillemotright>) =\<^sub>u \<guillemotleft>s\<guillemotright>)) ;; Skip"

theorem "(\<^bold>R\<^sub>s(P \<turnstile> Q)) \\\<^sub>C E = R3h(\<^bold>\<exists> s \<bullet> ((\<^bold>R\<^sub>s(P \<turnstile> Q))\<lbrakk>$tr^\<^sub>u\<guillemotleft>s\<guillemotright>, $ref\<acute>\<union>\<^sub>u \<guillemotleft>E\<guillemotright> / $tr\<acute>,$ref\<acute> \<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u (\<guillemotleft>s\<guillemotright> \<restriction>\<^sub>u (- \<guillemotleft>E\<guillemotright>)))) ;; Skip"

theorem "hide_rea (\<^bold>R\<^sub>s(P \<turnstile> Q)) E = 

(*theorem "(\<^bold>R\<^sub>s(P \<turnstile> Q)) \\\<^sub>C E = \<^bold>R\<^sub>s(\<not> (\<not> P\<lbrakk>$tr ^\<^sub>u   \<rbrakk>))"*)
*)

end