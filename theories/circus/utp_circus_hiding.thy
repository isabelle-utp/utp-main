subsection \<open> Hiding \<close>

theory utp_circus_hiding
imports utp_circus_parallel
begin

definition hide_rea ("hide\<^sub>r") where
[upred_defs]: "hide\<^sub>r P E = (\<^bold>\<exists> s \<bullet> (P\<lbrakk>$tr^\<^sub>u\<guillemotleft>s\<guillemotright>,\<guillemotleft>E\<guillemotright>\<union>\<^sub>u$ref\<acute>/$tr\<acute>,$ref\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr^\<^sub>u(\<guillemotleft>s\<guillemotright>\<restriction>\<^sub>u\<guillemotleft>-E\<guillemotright>)))"

lemma hide_rea_CRR_closed [closure]: 
  assumes "P is CRR"
  shows "hide\<^sub>r P E is CRR"
proof -
  have "CRR(hide\<^sub>r (CRR P) E) = hide\<^sub>r (CRR P) E"
    by (rel_auto, fastforce+)
  thus ?thesis
    by (metis Healthy_def' assms)
qed

lemma hide_rea_CDC [closure]:
  assumes "P is CDC"
  shows "hide\<^sub>r P E is CDC"
proof -
  have "CDC(hide\<^sub>r (CDC P) E) = hide\<^sub>r (CDC P) E"
    by (rel_blast)
  thus ?thesis
    by (simp add: Healthy_if Healthy_intro assms)
qed

lemma st'_unrest_hide_rea [unrest]: "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> hide\<^sub>r P E"
  by (simp add: hide_rea_def unrest)

lemma ref'_unrest_hide_rea [unrest]: "$ref\<acute> \<sharp> P \<Longrightarrow> $ref\<acute> \<sharp> hide\<^sub>r P E"
  by (simp add: hide_rea_def unrest usubst)

typedef (overloaded) 't::trace tchain = "{f :: nat \<Rightarrow> 't. f(0) = 0 \<and> (\<forall> n. f(n) \<le> f(Suc n))}" 
  by (rule_tac x="\<lambda> n. 0" in exI, auto)

setup_lifting type_definition_tchain

lift_definition infinite_tchain :: "'t::trace tchain \<Rightarrow> bool" is "\<lambda> f. (\<forall> n. f(n) < f(Suc n))" .

definition abs_rea :: "('s, 'e) action \<Rightarrow> 'e set \<Rightarrow> ('s, 'e) action" ("abs\<^sub>r") where
[upred_defs]: "abs\<^sub>r P E = (\<not>\<^sub>r (hide\<^sub>r (\<not>\<^sub>r P) E ;; true\<^sub>r))"

lemma abs_rea_false [rpred]: "abs\<^sub>r false E = false"
  by (rel_simp, metis append.right_neutral seq_filter_Nil)

lemma abs_rea_true [rpred]: "abs\<^sub>r true\<^sub>r E = true\<^sub>r"
  by (rel_auto)

lemma abs_rea_RC_closed [closure]:
  assumes "P is CRR"
  shows "abs\<^sub>r P E is CRC"
proof -
  have "RC1 (abs\<^sub>r (CRR P) E) = abs\<^sub>r (CRR P) E"
    apply (rel_auto)
    apply (metis order_refl)
    apply blast
    done
  hence "abs\<^sub>r P E is RC1"
    by (simp add: assms Healthy_if Healthy_intro closure)
  thus ?thesis
    by (rule_tac CRC_intro'', simp_all add: abs_rea_def closure assms unrest)
qed

definition HidingCSP  :: "('s, 'e) action \<Rightarrow> 'e set \<Rightarrow> ('s, 'e) action" (infixl "\\\<^sub>C" 80) where 
  [upred_defs, rdes_def]: 
  "HidingCSP P E = \<^bold>R\<^sub>s(abs\<^sub>r(pre\<^sub>R(P)) E \<turnstile> hide\<^sub>r (peri\<^sub>R(P)) E \<diamondop> hide\<^sub>r (post\<^sub>R(P)) E)"

lemma HidingCSP_NCSP_closed [closure]: "P is NCSP \<Longrightarrow> P \\\<^sub>C E is NCSP"
  by (simp add: HidingCSP_def closure unrest)

lemma HidingCSP_C2_closed [closure]: 
  assumes "P is NCSP" "P is C2"
  shows "P \\\<^sub>C E is C2"
  by (rdes_simp cls: assms, simp add: C2_rdes_intro closure unrest assms)

lemma HidingCSP_CACT_closed [closure]:
  assumes "P is CACT"
  shows "P \\\<^sub>C E is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

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
  apply (rdes_simp cls: assms)
  oops

lemma "Stop \\\<^sub>C A = Stop"
  by (rdes_eq)

lemma "Miracle \\\<^sub>C A = Miracle"
  by (rdes_eq)

lemma "(a \<^bold>\<rightarrow> Skip) \\\<^sub>C {a} = Skip"
  by (rdes_eq)

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