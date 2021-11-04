theory Konig
  imports
    Cofinality
    Cardinal_Library

begin

text\<open>Now, using the Axiom of choice, we can show that all successor
cardinals are regular.\<close>

lemma cf_csucc:
  assumes "InfCard(z)"
  shows "cf(z\<^sup>+) = z\<^sup>+"
proof (rule ccontr)
  assume "cf(z\<^sup>+) \<noteq> z\<^sup>+"
  moreover from \<open>InfCard(z)\<close>
  have "Ord(z\<^sup>+)" "Ord(z)" "Limit(z)" "Limit(z\<^sup>+)" "Card(z\<^sup>+)" "Card(z)"
    using InfCard_csucc Card_is_Ord InfCard_is_Card InfCard_is_Limit
    by fastforce+
  moreover from calculation
  have "cf(z\<^sup>+) < z\<^sup>+"
    using cf_le_cardinal[of "z\<^sup>+", THEN le_iff[THEN iffD1]]
      Card_cardinal_eq
    by simp
  ultimately
  obtain G where "G:cf(z\<^sup>+)\<rightarrow> z\<^sup>+" "\<forall>\<beta>\<in>z\<^sup>+. \<exists>y\<in>cf(z\<^sup>+). \<beta> < G`y"
    using Limit_cofinal_fun_lt[of "z\<^sup>+" _ "cf(z\<^sup>+)"] Ord_cf
      cf_le_cf_fun[of "z\<^sup>+" "cf(z\<^sup>+)"] le_refl[of "cf(z\<^sup>+)"]
    by auto
  with \<open>Card(z)\<close> \<open>Card(z\<^sup>+)\<close> \<open>Ord(z\<^sup>+)\<close>
  have "\<forall>\<beta>\<in>cf(z\<^sup>+). |G`\<beta>| \<le> z"
    using apply_type[of G "cf(z\<^sup>+)" "\<lambda>_. z\<^sup>+", THEN ltI] Card_lt_iff[THEN iffD2]
      Ord_in_Ord[OF Card_is_Ord, of "z\<^sup>+"] cardinal_lt_csucc_iff[THEN iffD1]
    by auto
  from \<open>cf(z\<^sup>+) < z\<^sup>+\<close> \<open>InfCard(z)\<close> \<open>Ord(z)\<close>
  have "cf(z\<^sup>+) \<lesssim> z"
    using cardinal_lt_csucc_iff[of "z" "cf(z\<^sup>+)"] Card_csucc[of "z"]
      le_Card_iff[of "z" "cf(z\<^sup>+)"] InfCard_is_Card
      Card_lt_iff[of "cf(z\<^sup>+)" "z\<^sup>+"] lt_Ord[of "cf(z\<^sup>+)" "z\<^sup>+"]
    by simp
  with \<open>cf(z\<^sup>+) < z\<^sup>+\<close> \<open>\<forall>\<beta>\<in>cf(z\<^sup>+). |G`\<beta>| \<le> _\<close> \<open>InfCard(z)\<close>
  have "|\<Union>\<beta>\<in>cf(z\<^sup>+). G`\<beta>| \<le> z"
    using InfCard_csucc[of z]
      subset_imp_lepoll[THEN lepoll_imp_cardinal_le, of "\<Union>\<beta>\<in>cf(z\<^sup>+). G`\<beta>" "z"]
    by (rule_tac leqpoll_imp_cardinal_UN_le) auto
  moreover
  note \<open>Ord(z)\<close>
  moreover from \<open>\<forall>\<beta>\<in>z\<^sup>+. \<exists>y\<in>cf(z\<^sup>+). \<beta> < G`y\<close> and this
  have "z\<^sup>+ \<subseteq> (\<Union>\<beta>\<in>cf(z\<^sup>+). G`\<beta>)"
    by (blast dest:ltD)
  ultimately
  have "z\<^sup>+ \<le> z"
    using subset_imp_le_cardinal[of "z\<^sup>+" "\<Union>\<beta>\<in>cf(z\<^sup>+). G`\<beta>"] le_trans
      InfCard_is_Card Card_csucc[of z] Card_cardinal_eq
    by auto
  with \<open>Ord(z)\<close>
  show "False"
    using lt_csucc[of z] not_lt_iff_le[THEN iffD2, of z "z\<^sup>+"]
      Card_csucc[THEN Card_is_Ord]
    by auto
qed

text\<open>And this finishes the calculation of cofinality of Alephs.\<close>

lemma cf_Aleph_succ: "Ord(z) \<Longrightarrow> cf(\<aleph>\<^bsub>succ(z)\<^esub>) = \<aleph>\<^bsub>succ(z)\<^esub>"
  using Aleph_succ cf_csucc InfCard_Aleph by simp

subsection\<open>König's Theorem\label{sec:konig}\<close>

text\<open>We end this section by proving König's Theorem on the cofinality
of cardinal exponentiation. This is a strengthening of Cantor's theorem
and it is essentially the only basic way to prove strict cardinal
inequalities.

It is proved rather straightforwardly with the tools already developed.\<close>

lemma konigs_theorem:
  notes [dest] = InfCard_is_Card Card_is_Ord
    and [trans] = lt_trans1 lt_trans2
  assumes
    "InfCard(\<kappa>)" "InfCard(\<nu>)" "cf(\<kappa>) \<le> \<nu>"
  shows
    "\<kappa> < \<kappa>\<^bsup>\<up>\<nu>\<^esup>"
  using assms(1,2) Card_cexp
proof (intro not_le_iff_lt[THEN iffD1] notI)
  assume "\<kappa>\<^bsup>\<up>\<nu>\<^esup> \<le> \<kappa>"
  moreover
  note \<open>InfCard(\<kappa>)\<close>
  moreover from calculation
  have "\<nu> \<rightarrow> \<kappa> \<lesssim> \<kappa>"
    using Card_cardinal_eq[OF InfCard_is_Card, symmetric]
      Card_le_imp_lepoll
    unfolding cexp_def by simp
  ultimately
  obtain G where "G \<in> surj(\<kappa>, \<nu> \<rightarrow> \<kappa>)"
    using inj_imp_surj[OF _ function_space_nonempty,
        OF _ nat_into_InfCard] by blast
  from assms
  obtain f where "f:\<nu> \<rightarrow> \<kappa>" "cf_fun(f,\<kappa>)"
    using cf_le_cf_fun[OF _ InfCard_is_Limit] by blast
  define H where "H(\<alpha>) \<equiv> \<mu> x. x\<in>\<kappa> \<and> (\<forall>m<f`\<alpha>. G`m`\<alpha> \<noteq> x)"
    (is "_ \<equiv> \<mu> x. ?P(\<alpha>,x)") for \<alpha>
  have H_satisfies: "?P(\<alpha>,H(\<alpha>))" if "\<alpha> \<in> \<nu>" for \<alpha>
  proof -
    obtain h where "?P(\<alpha>,h)"
    proof -
      from \<open>\<alpha>\<in>\<nu>\<close> \<open>f:\<nu> \<rightarrow> \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "f`\<alpha> < \<kappa>"
        using apply_type[of _ _ "\<lambda>_ . \<kappa>"] by (auto intro:ltI)
      have "|{G`m`\<alpha> . m \<in> {x\<in>\<kappa> . x < f`\<alpha>}}| \<le> |{x\<in>\<kappa> . x < f`\<alpha>}|"
        using cardinal_RepFun_le by simp
      also from \<open>f`\<alpha> < \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "|{x\<in>\<kappa> . x < f`\<alpha>}| < |\<kappa>|"
        using Card_lt_iff[OF lt_Ord, THEN iffD2, of "f`\<alpha>" \<kappa> \<kappa>]
          Ord_eq_Collect_lt[of "f`\<alpha>" \<kappa>] Card_cardinal_eq
        by force
      finally
      have "|{G`m`\<alpha> . m \<in> {x\<in>\<kappa> . x < f`\<alpha>}}| < |\<kappa>|" .
      moreover from \<open>f`\<alpha> < \<kappa>\<close> \<open>InfCard(\<kappa>)\<close>
      have "m<f`\<alpha> \<Longrightarrow> m\<in>\<kappa>" for m
        using Ord_trans[of m "f`\<alpha>" \<kappa>]
        by (auto dest:ltD)
      ultimately
      have "\<exists>h. ?P(\<alpha>,h)"
        using lt_cardinal_imp_not_subset by blast
      with that
      show ?thesis by blast
    qed
    with assms
    show "?P(\<alpha>,H(\<alpha>))"
      using LeastI[of "?P(\<alpha>)" h] lt_Ord Ord_in_Ord
      unfolding H_def by fastforce
  qed
  then
  have "(\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>)): \<nu> \<rightarrow> \<kappa>"
    using lam_type by auto
  with \<open>G \<in> surj(\<kappa>, \<nu> \<rightarrow> \<kappa>)\<close>
  obtain n where "n\<in>\<kappa>" "G`n = (\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>))"
    unfolding surj_def by blast
  moreover
  note \<open>InfCard(\<kappa>)\<close> \<open>f: \<nu> \<rightarrow> \<kappa>\<close> \<open>cf_fun(f,_)\<close>
  ultimately
  obtain \<alpha> where "n < f`\<alpha>" "\<alpha>\<in>\<nu>"
    using Limit_cofinal_fun_lt[OF InfCard_is_Limit] by blast
  moreover from calculation and \<open>G`n = (\<lambda>\<alpha>\<in>\<nu>. H(\<alpha>))\<close>
  have "G`n`\<alpha> = H(\<alpha>)"
    using ltD by simp
  moreover from calculation and H_satisfies
  have "\<forall>m<f`\<alpha>. G`m`\<alpha> \<noteq> H(\<alpha>)" by simp
  ultimately
  show "False" by blast
qed blast+

lemma cf_cexp:
  assumes
    "Card(\<kappa>)" "InfCard(\<nu>)" "2 \<le> \<kappa>"
  shows
    "\<nu> < cf(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)"
proof (rule ccontr)
  assume "\<not> \<nu> < cf(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)"
  with \<open>InfCard(\<nu>)\<close>
  have "cf(\<kappa>\<^bsup>\<up>\<nu>\<^esup>) \<le> \<nu>" 
    using not_lt_iff_le Ord_cf InfCard_is_Card Card_is_Ord by simp
  moreover
  note assms
  moreover from calculation
  have "InfCard(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)" using InfCard_cexp by simp
  moreover from calculation
  have "\<kappa>\<^bsup>\<up>\<nu>\<^esup> < (\<kappa>\<^bsup>\<up>\<nu>\<^esup>)\<^bsup>\<up>\<nu>\<^esup>" 
    using konigs_theorem by simp
  ultimately
  show "False" using cexp_cexp_cmult InfCard_csquare_eq by auto
qed

text\<open>Finally, the next two corollaries illustrate the only possible
exceptions to the value of the cardinality of the continuum: The limit
cardinals of countable cofinality. That these are the only exceptions
is a consequence of Easton's Theorem~\cite[Thm 15.18]{Jech_Millennium}.\<close>

corollary cf_continuum: "\<aleph>\<^bsub>0\<^esub> < cf(2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^esup>)"
  using cf_cexp InfCard_Aleph nat_into_Card by simp

corollary continuum_not_eq_Aleph_nat: "2\<^bsup>\<up>\<aleph>\<^bsub>0\<^esub>\<^esup> \<noteq> \<aleph>\<^bsub>\<omega>\<^esub>"
  using cf_continuum cf_Aleph_Limit[OF Limit_nat] cf_nat
    Aleph_zero_eq_nat by auto

end