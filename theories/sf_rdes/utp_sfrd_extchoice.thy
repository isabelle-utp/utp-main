section \<open> External Choice \<close>

theory utp_sfrd_extchoice
  imports 
    utp_sfrd_healths
    utp_sfrd_rel
begin

subsection \<open> Definitions and syntax \<close>

definition EXTCHOICE :: "'a set \<Rightarrow> ('a \<Rightarrow> ('\<sigma>, '\<phi>) action) \<Rightarrow> ('\<sigma>, '\<phi>) action" where
ExtChoice_def [upred_defs]: "EXTCHOICE A F = \<^bold>R\<^sub>s((\<Squnion> P\<in>A \<bullet> pre\<^sub>R(F P)) \<turnstile> ((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R(F P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R(F P))))"

abbreviation ExtChoice :: "('\<sigma>, '\<phi>) action set \<Rightarrow> ('\<sigma>, '\<phi>) action" where 
"ExtChoice A \<equiv> EXTCHOICE A id"

syntax
  "_ExtChoice" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<box> _\<in>_ \<bullet>/ _)" [0, 0, 10] 10)
  "_ExtChoice_simp" :: "pttrn \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<box> _ \<bullet>/ _)" [0, 10] 10)

translations
  "\<box>P\<in>A \<bullet> B"   \<rightleftharpoons> "CONST EXTCHOICE A (\<lambda>P. B)"
  "\<box>P \<bullet> B"     \<rightleftharpoons> "CONST EXTCHOICE (CONST UNIV) (\<lambda>P. B)"

definition extChoice ::
  "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" (infixl "\<box>" 59) where
[upred_defs]: "P \<box> Q \<equiv> ExtChoice {P, Q}"

text \<open> Small external choice as an indexed big external choice. \<close>

lemma extChoice_alt_def:
  "P \<box> Q = (\<box>i::nat\<in>{0,1} \<bullet> P \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q)"
  by (simp add: extChoice_def ExtChoice_def)

subsection \<open> Basic laws \<close>

subsection \<open> Algebraic laws \<close>

lemma ExtChoice_empty: "EXTCHOICE {} F = Stop"
  by (simp add: ExtChoice_def cond_def Stop_def)

lemma ExtChoice_single:
  "P is CSP \<Longrightarrow> ExtChoice {P} = P"
  by (simp add: ExtChoice_def usup_and uinf_or SRD_reactive_design_alt)

subsection \<open> Reactive design calculations \<close>

lemma ExtChoice_rdes:
  assumes "\<And> i. $ok\<acute> \<sharp> P(i)" "A \<noteq> {}"
  shows "(\<box>i\<in>A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) = \<^bold>R\<^sub>s((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> Q(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> Q(i))))"
proof -
  have "(\<box>i\<in>A \<bullet> \<^bold>R\<^sub>s(P(i) \<turnstile> Q(i))) =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> pre\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))))"
    by (simp add: ExtChoice_def)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))))"
    by (simp add: rea_pre_RHS_design rea_cmt_RHS_design)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            R1(R2c
            ((\<Squnion>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> R1(R2c(cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            R1(R2c
            ((\<Squnion>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i)))))))"
    by (simp add: R2c_UINF R2c_condr R1_cond R1_idem R1_R2c_commute R2c_idem R1_UINF assms R1_USUP R2c_USUP)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            cmt\<^sub>s \<dagger>
            ((\<Squnion>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (cmt\<^sub>s \<dagger> (P(i) \<Rightarrow> Q(i))))))"
    by (metis (no_types, lifting) RHS_design_export_R1 RHS_design_export_R2c rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            cmt\<^sub>s \<dagger>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
             (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: usubst)
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> R1 (R2c (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: rdes_export_cmt)
  also have "... =
        \<^bold>R\<^sub>s ((R1(R2c(\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i))))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: not_UINF R1_UINF R2c_UINF assms)
  also have "... =
        \<^bold>R\<^sub>s ((R2c(\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: R1_design_R1_pre)
  also have "... =
        \<^bold>R\<^sub>s (((\<Squnion>i\<in>A \<bullet> (pre\<^sub>s \<dagger> P(i)))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (metis (no_types, lifting) RHS_design_R2c_pre)
  also have "... =
        \<^bold>R\<^sub>s (([$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> (\<Squnion>i\<in>A \<bullet> P(i))) \<turnstile>
            ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
  proof -
    from assms have "\<And> i. pre\<^sub>s \<dagger> P(i) = [$ok \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false] \<dagger> P(i)"
      by (rel_auto)
    thus ?thesis
      by (simp add: usubst)
  qed
  also have "... =
        \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i))) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> (P(i) \<Rightarrow> Q(i)))))"
    by (simp add: rdes_export_pre not_UINF)
  also have "... = \<^bold>R\<^sub>s ((\<Squnion>i\<in>A \<bullet> P(i)) \<turnstile> ((\<Squnion>i\<in>A \<bullet> Q(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter>i\<in>A \<bullet> Q(i))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto, blast+)

  finally show ?thesis .
qed

lemma ExtChoice_tri_rdes:
  assumes "\<And> i . $ok\<acute> \<sharp> P\<^sub>1(i)" "A \<noteq> {}"
  shows "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
proof -
  have "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> ((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: ExtChoice_rdes assms)
  also
  have "... =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> ((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: conj_comm)
  also
  have "... =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))))"
    by (simp add: cond_conj wait'_cond_def)
  also
  have "... = \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> P\<^sub>2(i)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> i\<in>A \<bullet> P\<^sub>2(i))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma ExtChoice_tri_rdes' [rdes_def]:
  assumes "\<And> i . $ok\<acute> \<sharp> P\<^sub>1(i)" "A \<noteq> {}"
  shows "(\<box> i\<in>A \<bullet> \<^bold>R\<^sub>s(P\<^sub>1(i) \<turnstile> P\<^sub>2(i) \<diamondop> P\<^sub>3(i))) =
         \<^bold>R\<^sub>s ((\<Squnion> i\<in>A \<bullet> P\<^sub>1(i)) \<turnstile> (((\<Squnion> i\<in>A \<bullet> R5(P\<^sub>2(i))) \<or> (\<Sqinter> i\<in>A \<bullet> R4(P\<^sub>2(i)))) \<diamondop> (\<Sqinter> i\<in>A \<bullet> P\<^sub>3(i))))"
  by (simp add: ExtChoice_tri_rdes assms, rel_auto, simp_all add: less_le assms)

lemma ExtChoice_tri_rdes_def:
  assumes "\<And> i. i\<in>A \<Longrightarrow> F i is CSP"
  shows "(\<box> i\<in>A \<bullet> F i) = \<^bold>R\<^sub>s ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (F P)) \<turnstile> (((\<Squnion> P\<in>A \<bullet> peri\<^sub>R (F P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (F P))) \<diamondop> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (F P))))"
proof -
  have "((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R (F P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R (F P))) =
        (((\<Squnion> P\<in>A \<bullet> cmt\<^sub>R (F P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R (F P))) \<diamondop> (\<Sqinter> P\<in>A \<bullet> cmt\<^sub>R (F P)))"
    by (rel_auto)
  also have "... = (((\<Squnion> P\<in>A \<bullet> peri\<^sub>R (F P)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (F P))) \<diamondop> (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (F P)))"
    by (rel_auto)
  finally show ?thesis
    by (simp add: ExtChoice_def)
qed

lemma extChoice_rdes:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2) = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
proof -
  have "(\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s (P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> \<^bold>R\<^sub>s (Q\<^sub>1 \<turnstile> Q\<^sub>2)) = (\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s ((P\<^sub>1 \<turnstile> P\<^sub>2) \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> (Q\<^sub>1 \<turnstile> Q\<^sub>2)))"
    by (simp only: RHS_cond R2c_lit)
  also have "... = (\<box>i::nat\<in>{0, 1} \<bullet> \<^bold>R\<^sub>s ((P\<^sub>1 \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q\<^sub>1) \<turnstile> (P\<^sub>2 \<triangleleft> \<guillemotleft>i = 0\<guillemotright> \<triangleright> Q\<^sub>2)))"
    by (simp add: design_condr)
  also have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)))"
    by (subst ExtChoice_rdes, simp_all add: assms unrest uinf_or usup_and)
  finally show ?thesis by (simp add: extChoice_alt_def)
qed

lemma extChoice_tri_rdes:
  assumes "$ok\<acute> \<sharp> P\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>1"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
         \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
proof -
  have "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
        \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: extChoice_rdes assms)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: conj_comm)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile>
               (((P\<^sub>2 \<diamondop> P\<^sub>3 \<and> Q\<^sub>2 \<diamondop> Q\<^sub>3) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)) \<diamondop> (P\<^sub>2 \<diamondop> P\<^sub>3 \<or> Q\<^sub>2 \<diamondop> Q\<^sub>3)))"
    by (simp add: cond_conj wait'_cond_def)
  also
  have "... = \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  finally show ?thesis .
qed

lemma extChoice_rdes_def:
  assumes "P\<^sub>1 is RR" "Q\<^sub>1 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
         \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> (((P\<^sub>2 \<and> Q\<^sub>2) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
  by (subst extChoice_tri_rdes, simp_all add: assms unrest)

lemma extChoice_rdes_def' [rdes_def]:
  assumes "P\<^sub>1 is RR" "Q\<^sub>1 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<box> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) =
         \<^bold>R\<^sub>s ((P\<^sub>1 \<and> Q\<^sub>1) \<turnstile> ((R5(P\<^sub>2 \<and> Q\<^sub>2) \<or> R4(P\<^sub>2 \<or> Q\<^sub>2)) \<diamondop> (P\<^sub>3 \<or> Q\<^sub>3)))"
  by (simp add: extChoice_rdes_def assms, rel_auto, simp_all add: less_le)

lemma CSP_ExtChoice [closure]:
  "EXTCHOICE A F is CSP"
  by (simp add: ExtChoice_def RHS_design_is_SRD unrest)

lemma CSP_extChoice [closure]:
  "P \<box> Q is CSP"
  by (simp add: CSP_ExtChoice extChoice_def)

lemma preR_EXTCHOICE [rdes]:
  assumes "A \<noteq> {}" "\<And> i. i\<in>A \<Longrightarrow> F i is NCSP"
  shows "pre\<^sub>R(EXTCHOICE A F) = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R(F P))"
  by (simp add: ExtChoice_tri_rdes_def closure rdes assms)

lemma preR_ExtChoice:
  assumes "A \<noteq> {}" "\<forall> P\<in>A. P is NCSP"
  shows "pre\<^sub>R(ExtChoice A) = (\<Squnion> P\<in>A \<bullet> pre\<^sub>R(P))"
  using assms by (auto simp add: preR_EXTCHOICE)

lemma periR_ExtChoice [rdes]:
  assumes "A \<noteq> {}" "\<And> i. i\<in>A \<Longrightarrow> F i is NCSP"
  shows "peri\<^sub>R(EXTCHOICE A F) = (((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (F P))) \<triangleleft> \<^U>($tr\<acute> = $tr) \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (F P)))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (F P)) \<triangleleft> \<^U>($tr\<acute> = $tr) \<triangleright> (\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (F P)))"
    by (simp add: ExtChoice_tri_rdes_def closure rdes assms)
  also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> pre\<^sub>R (F P) \<Rightarrow>\<^sub>r peri\<^sub>R (F P)) \<triangleleft> \<^U>($tr\<acute> = $tr) \<triangleright> (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R (F P) \<Rightarrow>\<^sub>r peri\<^sub>R (F P)))"
    by (simp add: NSRD_peri_under_pre assms closure cong: UINF_cong USUP_cong)
  also have "... = ((\<Squnion> P\<in>A \<bullet> RR(pre\<^sub>R (F P))) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> RR(pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r RR(peri\<^sub>R (F P))) \<triangleleft> \<^U>($tr\<acute> = $tr) \<triangleright> (\<Sqinter> P\<in>A \<bullet> RR(pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r RR(peri\<^sub>R (F P))))"
    by (simp add: Healthy_if assms closure cong: UINF_cong USUP_cong)
  also from assms(1) have "... = ((\<Squnion> P\<in>A \<bullet> RR(pre\<^sub>R (F P))) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> RR(pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r RR(peri\<^sub>R (F P)))) \<triangleleft> \<^U>($tr\<acute> = $tr) \<triangleright> ((\<Sqinter> P\<in>A \<bullet> RR(pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r RR(peri\<^sub>R (F P))))"
    by (rel_auto)
  finally show ?thesis
    by (simp add: Healthy_if NSRD_peri_under_pre assms closure cong: UINF_cong USUP_cong)
qed

lemma periR_ExtChoice':
  assumes "A \<noteq> {}" "\<And> i. i\<in>A \<Longrightarrow> F i is NCSP"
  shows "peri\<^sub>R(EXTCHOICE A F) = (R5((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r (\<Squnion> P\<in>A \<bullet> peri\<^sub>R (F P))) \<or> R4(\<Sqinter> P\<in>A \<bullet> peri\<^sub>R (F P)))"
  by (simp add: periR_ExtChoice assms, rel_auto)

lemma postR_ExtChoice [rdes]:
  assumes "A \<noteq> {}" "\<And> i. i\<in>A \<Longrightarrow> F i is NCSP"
  shows "post\<^sub>R(EXTCHOICE A F) = (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (F P))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> post\<^sub>R (F P)))"
    by (simp add: ExtChoice_tri_rdes_def closure rdes assms)
  also have "... = ((\<Squnion> P\<in>A \<bullet> pre\<^sub>R (F P)) \<Rightarrow>\<^sub>r (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R (F P) \<Rightarrow>\<^sub>r post\<^sub>R (F P)))"
    by (simp add: NSRD_post_under_pre assms closure cong: UINF_cong)
  also have "... = (\<Sqinter> P\<in>A \<bullet> pre\<^sub>R (F P) \<Rightarrow>\<^sub>r post\<^sub>R (F P))"
    by (rel_auto)
  finally show ?thesis
    by (simp add: NSRD_post_under_pre assms closure cong: UINF_cong)
qed

lemma preR_extChoice' [rdes]:
  assumes "P is NCSP" "Q is NCSP"  
  shows "pre\<^sub>R(P \<box> Q) = (pre\<^sub>R(P) \<and> pre\<^sub>R(Q))"  
  by (simp add: extChoice_def preR_ExtChoice assms closure usup_and)
    
lemma periR_extChoice [rdes]:
  assumes "P is NCSP" "Q is NCSP"
  shows "peri\<^sub>R(P \<box> Q) = ((pre\<^sub>R(P) \<and> pre\<^sub>R(Q) \<Rightarrow>\<^sub>r peri\<^sub>R(P) \<and> peri\<^sub>R(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>R(P) \<or> peri\<^sub>R(Q)))"
  using assms
  by (simp add: extChoice_def, subst periR_ExtChoice, auto simp add: usup_and uinf_or)
  
lemma postR_extChoice [rdes]:
  assumes "P is NCSP" "Q is NCSP"
  shows "post\<^sub>R(P \<box> Q) = (post\<^sub>R(P) \<or> post\<^sub>R(Q))"
  using assms
  by (simp add: extChoice_def, subst postR_ExtChoice, auto simp add: usup_and uinf_or)
    
lemma ExtChoice_cong:
  assumes "\<And> P. P \<in> A \<Longrightarrow> F(P) = G(P)"
  shows "(\<box> P\<in>A \<bullet> F(P)) = (\<box> P\<in>A \<bullet> G(P))"
  by (simp add: ExtChoice_def assms cong: UINF_cong USUP_cong)

lemma ref_unrest_ExtChoice:
  assumes
    "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P)"
    "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> cmt\<^sub>R(P)"
  shows "$ref \<sharp> (ExtChoice A)\<lbrakk>false/$wait\<rbrakk>"
proof -
  have "\<And> P. P \<in> A \<Longrightarrow> $ref \<sharp> pre\<^sub>R(P\<lbrakk>0/$tr\<rbrakk>)"
    using assms by (rel_blast)
  with assms show ?thesis
    by (simp add: ExtChoice_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest)
qed

lemma CSP4_ExtChoice:
  assumes "\<And> i. i\<in>A \<Longrightarrow> F i is NCSP"
  shows "EXTCHOICE A F is CSP4"
proof (cases "A = {}")
  case True thus ?thesis
    by (simp add: ExtChoice_empty Healthy_def CSP4_def, simp add: Skip_is_CSP Stop_left_zero)
next
  case False
  have 1:"(\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R (EXTCHOICE A F)) ;;\<^sub>h R1 true) = pre\<^sub>R (EXTCHOICE A F)"
  proof -
    have "\<And> P. P \<in> A \<Longrightarrow> (\<not>\<^sub>r pre\<^sub>R(F P)) ;; R1 true = (\<not>\<^sub>r pre\<^sub>R(F P))"
      by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_neg_pre_unit assms)
    thus ?thesis
      apply (simp add: False preR_EXTCHOICE closure NCSP_set_unrest_pre_wait' assms not_UINF seq_UINF_distr not_USUP)
      apply (rule USUP_cong)
      apply (simp add: rpred assms closure)
      done
  qed
  have 2: "$st\<acute> \<sharp> peri\<^sub>R (EXTCHOICE A F)"
  proof -
    have a: "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> pre\<^sub>R(F P)"
      by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_st'_unrest_pre assms)
    have b: "\<And> P. P \<in> A \<Longrightarrow> $st\<acute> \<sharp> peri\<^sub>R(F P)"
      by (simp add: NCSP_Healthy_subset_member NCSP_implies_NSRD NSRD_st'_unrest_peri assms)
    from a b show ?thesis
      apply (subst periR_ExtChoice)
        apply (simp_all add: assms closure unrest CSP4_set_unrest_pre_st' NCSP_set_unrest_pre_wait' False) 
      done
  qed
  have 3: "$ref\<acute> \<sharp> post\<^sub>R (EXTCHOICE A F)"
  proof -
    have a: "\<And> P. P \<in> A \<Longrightarrow> $ref\<acute> \<sharp> pre\<^sub>R(F P)"
      by (simp add: CSP4_ref'_unrest_pre assms closure)
    have b: "\<And> P. P \<in> A \<Longrightarrow> $ref\<acute> \<sharp> post\<^sub>R(F P)"
      by (simp add: CSP4_ref'_unrest_post assms closure)
    from a b show ?thesis
      by (subst postR_ExtChoice, simp_all add: assms CSP4_set_unrest_pre_st' NCSP_set_unrest_pre_wait' unrest False)
  qed
  show ?thesis
    by (rule CSP4_tri_intro, simp_all add: 1 2 3 assms closure)
       (metis "1" R1_seqr_closure rea_not_R1 rea_not_not rea_true_R1)
qed

lemma CSP4_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<box> Q is CSP4"
  by (simp add: extChoice_def, rule CSP4_ExtChoice, auto simp add: assms)

lemma NCSP_ExtChoice [closure]:
  assumes "\<And> i. i\<in>A \<Longrightarrow> F i is NCSP"
  shows "EXTCHOICE A F is NCSP"
proof (cases "A = {}")
  case True
  then show ?thesis by (simp add: ExtChoice_empty closure)
next
  case False
  show ?thesis
  proof (rule NCSP_intro)
    show 1:"EXTCHOICE A F is CSP"
      by (metis (mono_tags) CSP_ExtChoice)
    show "EXTCHOICE A F is CSP3"
      by (rule_tac CSP3_SRD_intro, simp_all add: CSP_Healthy_subset_member CSP3_Healthy_subset_member closure rdes unrest assms 1 False) 
    show "EXTCHOICE A F is CSP4"
      by (simp add: CSP4_ExtChoice assms)
  qed
qed

lemma ExtChoice_NCSP_closed [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P(i) is NCSP"
  shows "(\<box> i\<in>I \<bullet> P(i)) is NCSP"
  by (simp add: NCSP_ExtChoice assms image_subset_iff)

lemma NCSP_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP"
  shows "P \<box> Q is NCSP"
  unfolding extChoice_def
  by (auto intro: NCSP_ExtChoice simp add: assms)

subsection \<open> Productivity and Guardedness \<close>

lemma Productive_ExtChoice [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P(i) is NCSP" "\<And> i. i \<in> I \<Longrightarrow> P(i) is Productive"
  shows "EXTCHOICE I P is Productive"
proof (cases "I = {}")
  case True
  then show ?thesis
    by (simp add: ExtChoice_empty Productive_Stop)
next
  case False
  have 1: "\<And> i. i \<in> I \<Longrightarrow> $wait\<acute> \<sharp> pre\<^sub>R(P i)"
    using NCSP_implies_NSRD NSRD_wait'_unrest_pre assms(1) by blast

  show ?thesis
  proof (rule Productive_intro, simp_all add: assms closure rdes unrest 1 False)
    have "((\<Squnion> i\<in>I \<bullet> pre\<^sub>R (P i)) \<and> (\<Sqinter> i\<in>I \<bullet> post\<^sub>R (P i))) =
          ((\<Squnion> i\<in>I \<bullet> pre\<^sub>R (P i)) \<and> (\<Sqinter> i\<in>I \<bullet> (pre\<^sub>R (P i) \<and> post\<^sub>R (P i))))"
      by (rel_auto)
    moreover have "(\<Sqinter> i\<in>I \<bullet> (pre\<^sub>R (P i) \<and> post\<^sub>R (P i))) = (\<Sqinter> i\<in>I \<bullet> ((pre\<^sub>R (P i) \<and> post\<^sub>R (P i)) \<and> $tr <\<^sub>u $tr\<acute>))"
      by (rule UINF_cong, metis (no_types, lifting) "1" NCSP_implies_CSP Productive_post_refines_tr_increase assms utp_pred_laws.inf.absorb1)

    ultimately show "U($tr < $tr\<acute>) \<sqsubseteq> ((\<Squnion> i\<in>I \<bullet> pre\<^sub>R (P i)) \<and> ((\<Sqinter> i\<in>I \<bullet> post\<^sub>R (P i))))"
      by (rel_auto)
  qed
qed

lemma Productive_extChoice [closure]:
  assumes "P is NCSP" "Q is NCSP" "P is Productive" "Q is Productive"
  shows "P \<box> Q is Productive"
  unfolding extChoice_def
  by (auto intro: Productive_ExtChoice simp add: assms)

lemma ExtChoice_Guarded [closure]:
  assumes  "\<And> P. P \<in> A \<Longrightarrow> Guarded P"
  shows "Guarded (\<lambda> X. \<box>P\<in>A \<bullet> P(X))"
proof (rule GuardedI)
  fix X n
  have "\<And> Y. ((\<box>P\<in>A \<bullet> P Y) \<and> gvrt(n+1)) = ((\<box>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    fix Y
    let ?lhs = "((\<box>P\<in>A \<bullet> P Y) \<and> gvrt(n+1))" and ?rhs = "((\<box>P\<in>A \<bullet> (P Y \<and> gvrt(n+1))) \<and> gvrt(n+1))"
    have a:"?lhs\<lbrakk>false/$ok\<rbrakk> = ?rhs\<lbrakk>false/$ok\<rbrakk>"
      by (rel_auto)
    have b:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>true/$wait\<rbrakk>"
      by (rel_auto)
    have c:"?lhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk> = ?rhs\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk>"
      by (simp add: ExtChoice_def RHS_def R1_def R2c_def R2s_def R3h_def design_def usubst unrest, rel_blast)
    show "?lhs = ?rhs"
      using a b c
      by (rule_tac bool_eq_splitI[of "in_var ok"], simp, rule_tac bool_eq_splitI[of "in_var wait"], simp_all)
  qed
  moreover have "((\<box>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) \<and> gvrt(n+1)) =  ((\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1))) \<and> gvrt(n+1))"
  proof -
    have "(\<box>P\<in>A \<bullet> (P X \<and> gvrt(n+1))) = (\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)) \<and> gvrt(n+1)))"
    proof (rule ExtChoice_cong)
      fix P assume "P \<in> A"
      thus "(P X \<and> gvrt(n+1)) = (P (X \<and> gvrt(n)) \<and> gvrt(n+1))"
        using Guarded_def assms by blast
    qed
    thus ?thesis by simp
  qed
  ultimately show "((\<box>P\<in>A \<bullet> P X) \<and> gvrt(n+1)) = ((\<box>P\<in>A \<bullet> (P (X \<and> gvrt(n)))) \<and> gvrt(n+1))"
    by simp
qed

lemma ExtChoice_image: "ExtChoice (P ` A) = EXTCHOICE A P"
  by (rel_auto)

lemma extChoice_Guarded [closure]:
  assumes "Guarded P" "Guarded Q"
  shows "Guarded (\<lambda> X. P(X) \<box> Q(X))"
proof -
  have "Guarded (\<lambda> X. \<box>F\<in>{P,Q} \<bullet> F(X))"
    by (rule ExtChoice_Guarded, auto simp add: assms)
  thus ?thesis
    by (subst (asm) ExtChoice_image[THEN sym], simp add: extChoice_def)
qed

subsection \<open> Algebraic laws \<close>

lemma extChoice_comm:
  "P \<box> Q = Q \<box> P"
  by (unfold extChoice_def, simp add: insert_commute)

lemma extChoice_idem:
  "P is CSP \<Longrightarrow> P \<box> P = P"
  by (unfold extChoice_def, simp add: ExtChoice_single)

lemma extChoice_assoc:
  assumes "P is CSP" "Q is CSP" "R is CSP"
  shows "P \<box> Q \<box> R = P \<box> (Q \<box> R)"
proof -
  have "P \<box> Q \<box> R = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(R) \<turnstile> cmt\<^sub>R(R))"
    by (simp add: SRD_reactive_design_alt assms(1) assms(2) assms(3))
  also have "... =
    \<^bold>R\<^sub>s (((pre\<^sub>R P \<and> pre\<^sub>R Q) \<and> pre\<^sub>R R) \<turnstile>
          (((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<and> cmt\<^sub>R R)
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           ((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<or> cmt\<^sub>R R)))"
    by (simp add: extChoice_rdes unrest)
  also have "... =
    \<^bold>R\<^sub>s (((pre\<^sub>R P \<and> pre\<^sub>R Q) \<and> pre\<^sub>R R) \<turnstile>
          (((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<and> cmt\<^sub>R R)
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
            ((cmt\<^sub>R P \<or> cmt\<^sub>R Q) \<or> cmt\<^sub>R R)))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... =
    \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q \<and> pre\<^sub>R R) \<turnstile>
          ((cmt\<^sub>R P \<and> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) )
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           (cmt\<^sub>R P \<or> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))))"
    by (simp add: conj_assoc disj_assoc)
  also have "... =
    \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q \<and> pre\<^sub>R R) \<turnstile>
          ((cmt\<^sub>R P \<and> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))
              \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
           (cmt\<^sub>R P \<or> (cmt\<^sub>R Q \<and> cmt\<^sub>R R) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R Q \<or> cmt\<^sub>R R))))"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> (\<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(R) \<turnstile> cmt\<^sub>R(R)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = P \<box> (Q \<box> R)"
    by (simp add: SRD_reactive_design_alt assms(1) assms(2) assms(3))
  finally show ?thesis .
qed

lemma extChoice_Stop:
  assumes "Q is CSP"
  shows "Stop \<box> Q = Q"
  using assms
proof -
  have "Stop \<box> Q = \<^bold>R\<^sub>s (true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Stop_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> ((($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>) \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<or> cmt\<^sub>R Q)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> cmt\<^sub>R Q))"
    by (metis (no_types, lifting) cond_def eq_upred_sym neg_conj_cancel1 utp_pred_laws.inf.left_idem)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> cmt\<^sub>R Q)"
    by (simp add: cond_idem)
  also have "... = Q"
    by (simp add: SRD_reactive_design_alt assms)
  finally show ?thesis .
qed

lemma extChoice_Chaos:
  assumes "Q is CSP"
  shows "Chaos \<box> Q = Chaos"
proof -
  have "Chaos \<box> Q = \<^bold>R\<^sub>s (false \<turnstile> true) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q))"
    by (simp add: Chaos_def SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> (cmt\<^sub>R Q \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> true))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s (false \<turnstile> true)"
    by (rule cong[of "\<^bold>R\<^sub>s" "\<^bold>R\<^sub>s"], simp, rel_auto)
  also have "... = Chaos"
    by (simp add: Chaos_def)
  finally show ?thesis .
qed

lemma extChoice_Dist:
  assumes "P is CSP" "S \<subseteq> \<lbrakk>CSP\<rbrakk>\<^sub>H" "S \<noteq> {}"
  shows "P \<box> (\<Sqinter> S) = (\<Sqinter> Q\<in>S. P \<box> Q)"
proof -
  let ?S1 = "pre\<^sub>R ` S" and ?S2 = "cmt\<^sub>R ` S"
  have "P \<box> (\<Sqinter> S) = P \<box> (\<Sqinter> Q\<in>S \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)))"
    by (simp add: SRD_as_reactive_design[THEN sym] Healthy_SUPREMUM UINF_as_Sup_collect assms)
  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s((\<Squnion> Q \<in> S \<bullet> pre\<^sub>R(Q)) \<turnstile> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))"
    by (simp add: RHS_design_USUP SRD_reactive_design_alt assms)
  also have "... = \<^bold>R\<^sub>s ((pre\<^sub>R(P) \<and> (\<Squnion> Q \<in> S \<bullet> pre\<^sub>R(Q))) \<turnstile>
                       ((cmt\<^sub>R(P) \<and> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))
                         \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright>
                        (cmt\<^sub>R(P) \<or> (\<Sqinter> Q \<in> S \<bullet> cmt\<^sub>R(Q)))))"
    by (simp add: extChoice_rdes unrest)
  also have "... = \<^bold>R\<^sub>s ((\<Squnion> Q\<in>S \<bullet> pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile>
                       (\<Sqinter> Q\<in>S \<bullet> (cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q)))"
    by (simp add: conj_USUP_dist conj_UINF_dist disj_UINF_dist cond_UINF_dist assms)
  also have "... = (\<Sqinter> Q \<in> S \<bullet> \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> pre\<^sub>R Q) \<turnstile>
                                  ((cmt\<^sub>R P \<and> cmt\<^sub>R Q) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<triangleright> (cmt\<^sub>R P \<or> cmt\<^sub>R Q))))"
    by (simp add: assms RHS_design_USUP)
  also have "... = (\<Sqinter> Q\<in>S \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> cmt\<^sub>R(P)) \<box> \<^bold>R\<^sub>s(pre\<^sub>R(Q) \<turnstile> cmt\<^sub>R(Q)))"
    by (simp add: extChoice_rdes unrest)
  also have "... = (\<Sqinter> Q\<in>S. P \<box> CSP(Q))"
    by (simp add: UINF_as_Sup_collect, metis (no_types, lifting) Healthy_if SRD_as_reactive_design assms(1))
  also have "... = (\<Sqinter> Q\<in>S. P \<box> Q)"
    by (rule SUP_cong, simp_all add: Healthy_subset_member[OF assms(2)])
  finally show ?thesis .
qed

lemma extChoice_dist:
  assumes "P is CSP" "Q is CSP" "R is CSP"
  shows "P \<box> (Q \<sqinter> R) = (P \<box> Q) \<sqinter> (P \<box> R)"
  using assms extChoice_Dist[of P "{Q, R}"] by simp

lemma ExtChoice_seq_distr:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P i is PCSP" "Q is NCSP"
  shows "(\<box> i\<in>A \<bullet> P i) ;; Q = (\<box> i\<in>A \<bullet> P i ;; Q)"
proof (cases "A = {}")
  case True
  then show ?thesis 
    by (simp add: ExtChoice_empty NCSP_implies_CSP Stop_left_zero assms(2))
next
  case False
  show ?thesis
  proof -
    have 1:"(\<box> i\<in>A \<bullet> P i) = (\<box> i\<in>A \<bullet> (\<^bold>R\<^sub>s ((pre\<^sub>R (P i)) \<turnstile> peri\<^sub>R (P i) \<diamondop> (R4(post\<^sub>R (P i))))))"
      (is "?X = ?Y")
      by (rule ExtChoice_cong, metis (no_types, hide_lams) R4_def Healthy_if NCSP_implies_CSP PCSP_implies_NCSP Productive_form assms(1) comp_apply)
    have 2:"(\<box> i\<in>A \<bullet> P i ;; Q) = (\<box> i\<in>A \<bullet> (\<^bold>R\<^sub>s ((pre\<^sub>R (P i)) \<turnstile> peri\<^sub>R (P i) \<diamondop> (R4(post\<^sub>R (P i))))) ;; Q)"
      (is "?X = ?Y")
      by (rule ExtChoice_cong, metis (no_types, hide_lams) R4_def Healthy_if NCSP_implies_CSP PCSP_implies_NCSP Productive_form assms(1) comp_apply)
    show ?thesis
      by (simp add: 1 2, rdes_eq cls: assms False cong: ExtChoice_cong USUP_cong)
  qed
qed

lemma extChoice_seq_distr:
  assumes "P is PCSP" "Q is PCSP" "R is NCSP"
  shows "(P \<box> Q) ;; R = (P ;; R \<box> Q ;; R)"
  by (rdes_eq' cls: assms)

lemma extChoice_seq_distl:
  assumes "P is ICSP" "Q is ICSP" "R is NCSP"
  shows "P ;; (Q \<box> R) = (P ;; Q \<box> P ;; R)"
  by (rdes_eq cls: assms)

lemma extchoice_StateInvR_refine:
  assumes 
    "P is NCSP" "Q is NCSP"
    "sinv\<^sub>R(b) \<sqsubseteq> P" "sinv\<^sub>R(b) \<sqsubseteq> Q"
  shows "sinv\<^sub>R(b) \<sqsubseteq> P \<box> Q"
proof -
  have "P is R2" "Q is R2" by (simp_all add: closure assms)
  hence 1:
    "pre\<^sub>R P \<sqsubseteq> [b]\<^sub>S\<^sub><" "[b]\<^sub>S\<^sub>> \<sqsubseteq> ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R P)"
    "pre\<^sub>R Q \<sqsubseteq> [b]\<^sub>S\<^sub><" "[b]\<^sub>S\<^sub>> \<sqsubseteq> ([b]\<^sub>S\<^sub>< \<and> post\<^sub>R Q)"
    by (metis (no_types, lifting) CRR_implies_RR NCSP_implies_CSP RHS_tri_design_refine SRD_reactive_tri_design StateInvR_def assms periR_RR postR_RR preR_CRR rea_st_cond_RR rea_true_RR refBy_order st_post_CRR)+
  show ?thesis
    by (rdes_refine_split cls: assms(1-2), simp_all add: 1 closure assms truer_bottom_rpred  utp_pred_laws.inf_sup_distrib1)
qed

end