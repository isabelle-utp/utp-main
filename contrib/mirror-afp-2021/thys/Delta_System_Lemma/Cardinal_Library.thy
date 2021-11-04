section\<open>Cardinal Arithmetic under Choice\label{sec:cardinal-lib}\<close>

theory Cardinal_Library
  imports
    ZF_Library
    ZF.Cardinal_AC

begin

text\<open>This theory includes results on cardinalities that depend on $\AC$\<close>


subsection\<open>Results on cardinal exponentiation\<close>

text\<open>Non trivial instances of cardinal exponentiation require that
     the relevant function spaces are well-ordered, hence this 
     implies a strong use of choice.\<close>

lemma cexp_eqpoll_cong:
  assumes
    "A \<approx> A'" "B \<approx> B'"
  shows
    "A\<^bsup>\<up>B\<^esup> = A'\<^bsup>\<up>B'\<^esup>"
  unfolding cexp_def using cardinal_eqpoll_iff
    function_space_eqpoll_cong assms
  by simp

lemma cexp_cexp_cmult: "(\<kappa>\<^bsup>\<up>\<nu>1\<^esup>)\<^bsup>\<up>\<nu>2\<^esup> = \<kappa>\<^bsup>\<up>\<nu>2 \<otimes> \<nu>1\<^esup>"
proof -
  have "(\<kappa>\<^bsup>\<up>\<nu>1\<^esup>)\<^bsup>\<up>\<nu>2\<^esup> = (\<nu>1 \<rightarrow> \<kappa>)\<^bsup>\<up>\<nu>2\<^esup>"
    using cardinal_eqpoll
    by (intro cexp_eqpoll_cong) (simp_all add:cexp_def)
  also
  have " \<dots> = \<kappa>\<^bsup>\<up>\<nu>2 \<times> \<nu>1\<^esup>"
    unfolding cexp_def using curry_eqpoll cardinal_cong by blast
  also
  have " \<dots> = \<kappa>\<^bsup>\<up>\<nu>2 \<otimes> \<nu>1\<^esup>"
    using cardinal_eqpoll[THEN eqpoll_sym]
    unfolding cmult_def by (intro cexp_eqpoll_cong) (simp)
  finally
  show ?thesis  .
qed

lemma cardinal_Pow: "|Pow(X)| = 2\<^bsup>\<up>X\<^esup>" \<comment> \<open>Perhaps it's better with |X|\<close>
  using cardinal_eqpoll_iff[THEN iffD2, OF Pow_eqpoll_function_space]
  unfolding cexp_def by simp

lemma cantor_cexp:
  assumes "Card(\<nu>)"
  shows "\<nu> < 2\<^bsup>\<up>\<nu>\<^esup>"
  using assms Card_is_Ord Card_cexp
proof (intro not_le_iff_lt[THEN iffD1] notI)
  assume "2\<^bsup>\<up>\<nu>\<^esup> \<le> \<nu>"
  then
  have "|Pow(\<nu>)| \<le> \<nu>"
    using cardinal_Pow by simp
  with assms
  have "Pow(\<nu>) \<lesssim> \<nu>"
    using cardinal_eqpoll_iff Card_le_imp_lepoll Card_cardinal_eq
    by auto
  then
  obtain g where "g \<in> inj(Pow(\<nu>), \<nu>)"
    by blast
  then
  show "False"
    using cantor_inj by simp
qed simp

lemma cexp_left_mono:
  assumes "\<kappa>1 \<le> \<kappa>2"
  shows "\<kappa>1\<^bsup>\<up>\<nu>\<^esup> \<le> \<kappa>2\<^bsup>\<up>\<nu>\<^esup>"
    (* \<comment> \<open>short, unreadable proof: \<close>
  unfolding cexp_def
  using subset_imp_lepoll[THEN lepoll_imp_cardinal_le]
    assms le_subset_iff[THEN iffD1, OF assms]
    Pi_weaken_type[of _ _ "\<lambda>_. \<kappa>1" "\<lambda>_. \<kappa>2"] by auto *)
proof -
  from assms
  have "\<kappa>1 \<subseteq> \<kappa>2"
    using le_subset_iff by simp
  then
  have "\<nu> \<rightarrow> \<kappa>1  \<subseteq> \<nu> \<rightarrow> \<kappa>2"
    using Pi_weaken_type by auto
  then
  show ?thesis unfolding cexp_def
    using lepoll_imp_cardinal_le subset_imp_lepoll by simp
qed

lemma cantor_cexp':
  assumes "2 \<le> \<kappa>" "Card(\<nu>)"
  shows "\<nu> < \<kappa>\<^bsup>\<up>\<nu>\<^esup>"
  using cexp_left_mono assms cantor_cexp lt_trans2 by blast

lemma InfCard_cexp:
  assumes "2 \<le> \<kappa>" "InfCard(\<nu>)"
  shows "InfCard(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)"
  using assms cantor_cexp'[THEN leI] le_trans Card_cexp
  unfolding InfCard_def by auto

lemmas InfCard_cexp' = InfCard_cexp[OF nats_le_InfCard, simplified]
  \<comment> \<open>\<^term>\<open>InfCard(\<kappa>) \<Longrightarrow> InfCard(\<nu>) \<Longrightarrow> InfCard(\<kappa>\<^bsup>\<up>\<nu>\<^esup>)\<close>\<close>


subsection\<open>Miscellaneous\<close>

lemma cardinal_RepFun_le: "|{f(a) . a\<in>A}| \<le> |A|"
proof -
  have "(\<lambda>x\<in>A. f(x)) \<in> surj(A, {f(a) . a\<in>A})"
    unfolding surj_def using lam_funtype by auto
  then
  show ?thesis
    using  surj_implies_cardinal_le by blast
qed

lemma subset_imp_le_cardinal: "A \<subseteq> B \<Longrightarrow> |A| \<le> |B|"
  using subset_imp_lepoll[THEN lepoll_imp_cardinal_le] .

lemma lt_cardinal_imp_not_subset: "|A| < |B| \<Longrightarrow> \<not> B \<subseteq> A"
  using subset_imp_le_cardinal le_imp_not_lt by blast

lemma cardinal_lt_csucc_iff: "Card(K) \<Longrightarrow> |K'| < K\<^sup>+ \<longleftrightarrow> |K'| \<le> K"
  by (simp add: Card_lt_csucc_iff)

lemma cardinal_UN_le_nat:
  "(\<And>i. i\<in>\<omega> \<Longrightarrow> |X(i)| \<le> \<omega>) \<Longrightarrow> |\<Union>i\<in>\<omega>. X(i)| \<le> \<omega>"
  by (simp add: cardinal_UN_le InfCard_nat)

lemma leqpoll_imp_cardinal_UN_le:
  notes [dest] = InfCard_is_Card Card_is_Ord
  assumes "InfCard(K)" "J \<lesssim> K" "\<And>i. i\<in>J \<Longrightarrow> |X(i)| \<le> K"
  shows "|\<Union>i\<in>J. X(i)| \<le> K"
proof -
  from \<open>J \<lesssim> K\<close>
  obtain f where "f \<in> inj(J,K)" by blast
  define Y where "Y(k) \<equiv> if k\<in>range(f) then X(converse(f)`k) else 0" for k
  have "i\<in>J \<Longrightarrow> f`i \<in> K" for i
    using inj_is_fun[OF \<open>f \<in> inj(J,K)\<close>] by auto
  have "(\<Union>i\<in>J. X(i)) \<subseteq> (\<Union>i\<in>K. Y(i))"
  proof (standard, elim UN_E)
    fix x i
    assume "i\<in>J" "x\<in>X(i)"
    with \<open>f \<in> inj(J,K)\<close> \<open>i\<in>J \<Longrightarrow> f`i \<in> K\<close>
    have "x \<in> Y(f`i)" "f`i \<in> K"
      unfolding Y_def
      using inj_is_fun[OF \<open>f \<in> inj(J,K)\<close>]
        right_inverse apply_rangeI by auto
    then
    show "x \<in> (\<Union>i\<in>K. Y(i))" by auto
  qed
  then
  have "|\<Union>i\<in>J. X(i)| \<le> |\<Union>i\<in>K. Y(i)|"
    unfolding Y_def using subset_imp_le_cardinal by simp
  with assms \<open>\<And>i. i\<in>J \<Longrightarrow> f`i \<in> K\<close>
  show "|\<Union>i\<in>J. X(i)| \<le> K"
    using inj_converse_fun[OF \<open>f \<in> inj(J,K)\<close>] unfolding Y_def
    by (rule_tac le_trans[OF _ cardinal_UN_le]) (auto intro:Ord_0_le)+
qed

lemma cardinal_lt_csucc_iff':
  includes Ord_dests
  assumes "Card(\<kappa>)"
  shows "\<kappa> < |X| \<longleftrightarrow> \<kappa>\<^sup>+ \<le> |X|"
  using assms cardinal_lt_csucc_iff[of \<kappa> X] Card_csucc[of \<kappa>]
    not_le_iff_lt[of "\<kappa>\<^sup>+" "|X|"] not_le_iff_lt[of "|X|" \<kappa>]
  by blast

lemma lepoll_imp_subset_bij: "X \<lesssim> Y \<longleftrightarrow> (\<exists>Z. Z \<subseteq> Y \<and> Z \<approx> X)"
proof
  assume "X \<lesssim> Y"
  then
  obtain j where  "j \<in> inj(X,Y)"
    by blast
  then
  have "range(j) \<subseteq> Y" "j \<in> bij(X,range(j))"
    using inj_bij_range inj_is_fun range_fun_subset_codomain
    by blast+
  then
  show "\<exists>Z. Z \<subseteq> Y \<and> Z \<approx> X"
    using eqpoll_sym unfolding eqpoll_def
    by force
next
  assume "\<exists>Z. Z \<subseteq> Y \<and> Z \<approx> X"
  then
  obtain Z f where "f \<in> bij(Z,X)" "Z \<subseteq> Y"
    unfolding eqpoll_def by force
  then
  have "converse(f) \<in> inj(X,Y)"
    using bij_is_inj inj_weaken_type bij_converse_bij by blast
  then
  show "X \<lesssim> Y" by blast
qed

text\<open>The following result proves to be very useful when combining
     \<^term>\<open>cardinal\<close> and \<^term>\<open>eqpoll\<close> in a calculation.\<close>

lemma cardinal_Card_eqpoll_iff: "Card(\<kappa>) \<Longrightarrow> |X| = \<kappa> \<longleftrightarrow> X \<approx> \<kappa>"
  using Card_cardinal_eq[of \<kappa>] cardinal_eqpoll_iff[of X \<kappa>] by auto
    \<comment> \<open>Compare @{thm "le_Card_iff"}\<close>

lemma lepoll_imp_lepoll_cardinal: assumes "X \<lesssim> Y" shows "X \<lesssim> |Y|"
  using assms cardinal_Card_eqpoll_iff[of "|Y|" Y]
    lepoll_eq_trans[of _ _ "|Y|"] by simp

lemma lepoll_Un:
  assumes "InfCard(\<kappa>)" "A \<lesssim> \<kappa>" "B \<lesssim> \<kappa>"
  shows "A \<union> B \<lesssim> \<kappa>"
proof -
  have "A \<union> B \<lesssim> sum(A,B)"
    using Un_lepoll_sum .
  moreover
  note assms
  moreover from this
  have "|sum(A,B)| \<le> \<kappa> \<oplus> \<kappa>"
    using sum_lepoll_mono[of A \<kappa> B \<kappa>] lepoll_imp_cardinal_le
    unfolding cadd_def by auto
  ultimately
  show ?thesis
    using InfCard_cdouble_eq Card_cardinal_eq
      InfCard_is_Card Card_le_imp_lepoll[of "sum(A,B)" \<kappa>]
      lepoll_trans[of "A\<union>B"]
    by auto
qed

lemma cardinal_Un_le:
  assumes "InfCard(\<kappa>)" "|A| \<le> \<kappa>" "|B| \<le> \<kappa>"
  shows "|A \<union> B| \<le> \<kappa>"
  using assms lepoll_Un le_Card_iff InfCard_is_Card by auto

text\<open>This is the unconditional version under choice of 
     @{thm Cardinal.Finite_cardinal_iff}.\<close>
lemma Finite_cardinal_iff': "Finite(|i|) \<longleftrightarrow> Finite(i)"
  using cardinal_eqpoll_iff eqpoll_imp_Finite_iff by fastforce

lemma cardinal_subset_of_Card:
  assumes "Card(\<gamma>)" "a \<subseteq> \<gamma>"
  shows "|a| < \<gamma> \<or> |a| = \<gamma>"
proof -
  from assms
  have "|a| < |\<gamma>| \<or> |a| = |\<gamma>|"
    using subset_imp_le_cardinal le_iff by simp
  with assms
  show ?thesis
    using Card_cardinal_eq by simp
qed

lemma cardinal_cases:
  includes Ord_dests
  shows "Card(\<gamma>) \<Longrightarrow> |X| < \<gamma> \<longleftrightarrow> \<not> |X| \<ge> \<gamma>"
  using not_le_iff_lt
  by auto


subsection\<open>Countable and uncountable sets\<close>

\<comment> \<open>Kunen's Definition I.10.5\<close>
definition
  countable :: "i\<Rightarrow>o" where
  "countable(X) \<equiv> X \<lesssim> \<omega>"

lemma countableI[intro]: "X \<lesssim> \<omega> \<Longrightarrow> countable(X)"
  unfolding countable_def by simp

lemma countableD[dest]: "countable(X) \<Longrightarrow> X \<lesssim> \<omega>"
  unfolding countable_def by simp

lemma countable_iff_cardinal_le_nat: "countable(X) \<longleftrightarrow> |X| \<le> \<omega>"
  using le_Card_iff[of \<omega> X] Card_nat
  unfolding countable_def by simp

lemma lepoll_countable: "X \<lesssim> Y \<Longrightarrow> countable(Y) \<Longrightarrow> countable(X)"
  using lepoll_trans[of X Y] by blast

\<comment> \<open>Next lemma can be proved without using AC\<close>
lemma surj_countable: "countable(X) \<Longrightarrow> f \<in> surj(X,Y) \<Longrightarrow> countable(Y)"
  using surj_implies_cardinal_le[of f X Y, THEN le_trans]
    countable_iff_cardinal_le_nat by simp

lemma Finite_imp_countable: "Finite(X) \<Longrightarrow> countable(X)"
  unfolding Finite_def
  by (auto intro:InfCard_nat nats_le_InfCard[of _ \<omega>,
        THEN le_imp_lepoll] dest!:eq_lepoll_trans[of X _ \<omega>])

lemma countable_imp_countable_UN:
  assumes "countable(J)" "\<And>i. i\<in>J \<Longrightarrow> countable(X(i))"
  shows "countable(\<Union>i\<in>J. X(i))"
  using assms leqpoll_imp_cardinal_UN_le[of \<omega> J X] InfCard_nat
    countable_iff_cardinal_le_nat
  by auto

lemma countable_union_countable:
  assumes "\<And>x. x \<in> C \<Longrightarrow> countable(x)" "countable(C)"
  shows "countable(\<Union>C)"
  using assms countable_imp_countable_UN[of C "\<lambda>x. x"] by simp

abbreviation
  uncountable :: "i\<Rightarrow>o" where
  "uncountable(X) \<equiv> \<not> countable(X)"

lemma uncountable_iff_nat_lt_cardinal:
  "uncountable(X) \<longleftrightarrow> \<omega> < |X|"
  using countable_iff_cardinal_le_nat not_le_iff_lt by simp

lemma uncountable_not_empty: "uncountable(X) \<Longrightarrow> X \<noteq> 0"
  using empty_lepollI by auto

lemma uncountable_imp_Infinite: "uncountable(X) \<Longrightarrow> Infinite(X)"
  using uncountable_iff_nat_lt_cardinal[of X] lepoll_nat_imp_Infinite[of X]
    cardinal_le_imp_lepoll[of \<omega> X] leI
  by simp

lemma uncountable_not_subset_countable:
  assumes "countable(X)" "uncountable(Y)"
  shows "\<not> (Y \<subseteq> X)"
  using assms lepoll_trans subset_imp_lepoll[of Y X]
  by blast


subsection\<open>Results on Alephs\<close>

lemma nat_lt_Aleph1: "\<omega> < \<aleph>\<^bsub>1\<^esub>"
  by (simp add: Aleph_def lt_csucc)

lemma zero_lt_Aleph1: "0 < \<aleph>\<^bsub>1\<^esub>"
  by (rule lt_trans[of _ "\<omega>"], auto simp add: ltI nat_lt_Aleph1)

lemma le_aleph1_nat: "Card(k) \<Longrightarrow> k<\<aleph>\<^bsub>1\<^esub> \<Longrightarrow> k \<le> \<omega>"
  by (simp add: Aleph_def Card_lt_csucc_iff Card_nat)

lemma Aleph_succ: "\<aleph>\<^bsub>succ(\<alpha>)\<^esub> = \<aleph>\<^bsub>\<alpha>\<^esub>\<^sup>+"
  unfolding Aleph_def by simp

lemma lesspoll_aleph_plus_one:
  assumes "Ord(\<alpha>)"
  shows "d \<prec> \<aleph>\<^bsub>succ(\<alpha>)\<^esub> \<longleftrightarrow> d \<lesssim> \<aleph>\<^bsub>\<alpha>\<^esub>"
  using assms lesspoll_csucc Aleph_succ Card_is_Ord by simp

lemma cardinal_Aleph [simp]: "Ord(\<alpha>) \<Longrightarrow> |\<aleph>\<^bsub>\<alpha>\<^esub>| = \<aleph>\<^bsub>\<alpha>\<^esub>"
  using Card_cardinal_eq by simp

\<comment> \<open>Could be proved without using AC\<close>
lemma Aleph_lesspoll_increasing:
  includes Aleph_intros
  shows "a < b \<Longrightarrow> \<aleph>\<^bsub>a\<^esub> \<prec> \<aleph>\<^bsub>b\<^esub>"
  using cardinal_lt_iff_lesspoll[of "\<aleph>\<^bsub>a\<^esub>" "\<aleph>\<^bsub>b\<^esub>"] Card_cardinal_eq[of "\<aleph>\<^bsub>b\<^esub>"]
    lt_Ord lt_Ord2 Card_Aleph[THEN Card_is_Ord] by auto

lemma uncountable_iff_subset_eqpoll_Aleph1:
  includes Ord_dests
  notes Aleph_zero_eq_nat[simp] Card_nat[simp] Aleph_succ[simp]
  shows "uncountable(X) \<longleftrightarrow> (\<exists>S. S \<subseteq> X \<and> S \<approx> \<aleph>\<^bsub>1\<^esub>)"
proof
  assume "uncountable(X)"
  then
  have "\<aleph>\<^bsub>1\<^esub> \<lesssim> X"
    using uncountable_iff_nat_lt_cardinal cardinal_lt_csucc_iff'
      cardinal_le_imp_lepoll by force
  then
  obtain S where "S \<subseteq> X" "S \<approx> \<aleph>\<^bsub>1\<^esub>"
    using lepoll_imp_subset_bij by auto
  then
  show "\<exists>S. S \<subseteq> X \<and> S \<approx> \<aleph>\<^bsub>1\<^esub>"
    using cardinal_cong Card_csucc[of \<omega>] Card_cardinal_eq by auto
next
  assume "\<exists>S. S \<subseteq> X \<and> S \<approx> \<aleph>\<^bsub>1\<^esub>"
  then
  have "\<aleph>\<^bsub>1\<^esub> \<lesssim> X"
    using subset_imp_lepoll[THEN [2] eq_lepoll_trans, of "\<aleph>\<^bsub>1\<^esub>" _ X,
        OF eqpoll_sym] by auto
  then
  show "uncountable(X)"
    using Aleph_lesspoll_increasing[of 0 1, THEN [2] lesspoll_trans1,
        of "\<aleph>\<^bsub>1\<^esub>"] lepoll_trans[of "\<aleph>\<^bsub>1\<^esub>" X \<omega>]
    by auto
qed

lemma lt_Aleph_imp_cardinal_UN_le_nat: "function(G) \<Longrightarrow> domain(G) \<lesssim> \<omega> \<Longrightarrow>
   \<forall>n\<in>domain(G). |G`n|<\<aleph>\<^bsub>1\<^esub> \<Longrightarrow> |\<Union>n\<in>domain(G). G`n|\<le>\<omega>"
proof -
  assume "function(G)"
  let ?N="domain(G)" and ?R="\<Union>n\<in>domain(G). G`n"
  assume "?N \<lesssim> \<omega>"
  assume Eq1: "\<forall>n\<in>?N. |G`n|<\<aleph>\<^bsub>1\<^esub>"
  {
    fix n
    assume "n\<in>?N"
    with Eq1 have "|G`n| \<le> \<omega>"
      using le_aleph1_nat by simp
  }
  then
  have "n\<in>?N \<Longrightarrow> |G`n| \<le> \<omega>" for n .
  with \<open>?N \<lesssim> \<omega>\<close>
  show ?thesis
    using InfCard_nat leqpoll_imp_cardinal_UN_le by simp
qed

lemma Aleph1_eq_cardinal_vimage: "f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega> \<Longrightarrow> \<exists>n\<in>\<omega>. |f-``{n}| = \<aleph>\<^bsub>1\<^esub>"
proof -
  assume "f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega>"
  then
  have "function(f)" "domain(f) = \<aleph>\<^bsub>1\<^esub>" "range(f)\<subseteq>\<omega>"
    by (simp_all add: domain_of_fun fun_is_function range_fun_subset_codomain)
  let ?G="\<lambda>n\<in>range(f). f-``{n}"
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega>\<close>
  have "range(f) \<subseteq> \<omega>" by (simp add: range_fun_subset_codomain)
  then
  have "domain(?G) \<lesssim> \<omega>"
    using subset_imp_lepoll by simp
  have "function(?G)" by (simp add:function_lam)
  from \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega>\<close>
  have "n\<in>\<omega> \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>" for n
    using Pi_vimage_subset by simp
  with \<open>range(f) \<subseteq> \<omega>\<close>
  have "\<aleph>\<^bsub>1\<^esub> = (\<Union>n\<in>range(f). f-``{n})"
  proof (intro equalityI, intro subsetI)
    fix x
    assume "x \<in> \<aleph>\<^bsub>1\<^esub>"
    with \<open>f:\<aleph>\<^bsub>1\<^esub>\<rightarrow>\<omega>\<close> \<open>function(f)\<close> \<open>domain(f) = \<aleph>\<^bsub>1\<^esub>\<close>
    have "x \<in> f-``{f`x}" "f`x \<in> range(f)"
      using function_apply_Pair vimage_iff apply_rangeI by simp_all
    then
    show "x \<in> (\<Union>n\<in>range(f). f-``{n})" by auto
  qed auto
  {
    assume "\<forall>n\<in>range(f). |f-``{n}| < \<aleph>\<^bsub>1\<^esub>"
    then
    have "\<forall>n\<in>domain(?G). |?G`n| < \<aleph>\<^bsub>1\<^esub>"
      using zero_lt_Aleph1 by (auto)
    with \<open>function(?G)\<close> \<open>domain(?G) \<lesssim> \<omega>\<close>
    have "|\<Union>n\<in>domain(?G). ?G`n|\<le>\<omega>"
      using lt_Aleph_imp_cardinal_UN_le_nat by blast
    then
    have "|\<Union>n\<in>range(f). f-``{n}|\<le>\<omega>" by simp
    with \<open>\<aleph>\<^bsub>1\<^esub> = _\<close>
    have "|\<aleph>\<^bsub>1\<^esub>| \<le> \<omega>" by simp
    then
    have "\<aleph>\<^bsub>1\<^esub> \<le> \<omega>"
      using Card_Aleph Card_cardinal_eq
      by simp
    then
    have "False"
      using nat_lt_Aleph1 by (blast dest:lt_trans2)
  }
  with \<open>range(f)\<subseteq>\<omega>\<close>
  obtain n where "n\<in>\<omega>" "\<not>(|f -`` {n}| < \<aleph>\<^bsub>1\<^esub>)"
    by blast
  moreover from this
  have "\<aleph>\<^bsub>1\<^esub> \<le> |f-``{n}|"
    using not_lt_iff_le Card_is_Ord by auto
  moreover
  note \<open>n\<in>\<omega> \<Longrightarrow> f-``{n} \<subseteq> \<aleph>\<^bsub>1\<^esub>\<close>
  ultimately
  show ?thesis
    using subset_imp_le_cardinal[THEN le_anti_sym, of _ "\<aleph>\<^bsub>1\<^esub>"]
      Card_Aleph Card_cardinal_eq by auto
qed

\<comment> \<open>There is some asymmetry between assumptions and conclusion
    (\<^term>\<open>(\<approx>)\<close> versus \<^term>\<open>cardinal\<close>)\<close>
lemma eqpoll_Aleph1_cardinal_vimage:
  assumes "X \<approx> \<aleph>\<^bsub>1\<^esub>" "f : X \<rightarrow> \<omega>"
  shows "\<exists>n\<in>\<omega>. |f-``{n}| = \<aleph>\<^bsub>1\<^esub>"
proof -
  from assms
  obtain g where "g\<in>bij(\<aleph>\<^bsub>1\<^esub>,X)"
    using eqpoll_sym by blast
  with \<open>f : X \<rightarrow> \<omega>\<close>
  have "f O g : \<aleph>\<^bsub>1\<^esub> \<rightarrow> \<omega>" "converse(g) \<in> bij(X, \<aleph>\<^bsub>1\<^esub>)"
    using bij_is_fun comp_fun bij_converse_bij by blast+
  then
  obtain n where "n\<in>\<omega>" "|(f O g)-``{n}| = \<aleph>\<^bsub>1\<^esub>"
    using Aleph1_eq_cardinal_vimage by auto
  then
  have "\<aleph>\<^bsub>1\<^esub> = |converse(g) `` (f -``{n})|"
    using image_comp converse_comp
    unfolding vimage_def by simp
  also from \<open>converse(g) \<in> bij(X, \<aleph>\<^bsub>1\<^esub>)\<close> \<open>f: X\<rightarrow> \<omega>\<close>
  have "\<dots> = |f -``{n}|"
    using range_of_subset_eqpoll[of "converse(g)" X  _ "f -``{n}"]
      bij_is_inj cardinal_cong bij_is_fun eqpoll_sym Pi_vimage_subset
    by fastforce
  finally
  show ?thesis using \<open>n\<in>\<omega>\<close> by auto
qed


subsection\<open>Applications of transfinite recursive constructions\<close>

definition
  rec_constr :: "[i,i] \<Rightarrow> i" where
  "rec_constr(f,\<alpha>) \<equiv> transrec(\<alpha>,\<lambda>a g. f`(g``a))"

text\<open>The function \<^term>\<open>rec_constr\<close> allows to perform \<^emph>\<open>recursive
     constructions\<close>: given a choice function on the powerset of some
     set, a transfinite sequence is created by successively choosing
     some new element.

     The next result explains its use.\<close>

lemma rec_constr_unfold: "rec_constr(f,\<alpha>) = f`({rec_constr(f,\<beta>). \<beta>\<in>\<alpha>})"
  using def_transrec[OF rec_constr_def, of f \<alpha>] image_lam by simp

lemma rec_constr_type: assumes "f:Pow(G)\<rightarrow> G" "Ord(\<alpha>)"
  shows "rec_constr(f,\<alpha>) \<in> G"
  using assms(2,1)
  by (induct rule:trans_induct)
    (subst rec_constr_unfold, rule apply_type[of f "Pow(G)" "\<lambda>_. G"], auto)

text\<open>The next lemma is an application of recursive constructions.
     It works under the assumption that whenever the already constructed
     subsequence is small enough, another element can be added.\<close>

lemma bounded_cardinal_selection:
  includes Ord_dests
  assumes
    "\<And>X. |X| < \<gamma> \<Longrightarrow> X \<subseteq> G \<Longrightarrow> \<exists>a\<in>G. \<forall>s\<in>X. Q(s,a)" "b\<in>G" "Card(\<gamma>)"
  shows
    "\<exists>S. S : \<gamma> \<rightarrow> G \<and> (\<forall>\<alpha> \<in> \<gamma>. \<forall>\<beta> \<in> \<gamma>.  \<alpha><\<beta> \<longrightarrow> Q(S`\<alpha>,S`\<beta>))"
proof -
  let ?cdlt\<gamma>="{X\<in>Pow(G) . |X|<\<gamma>}" \<comment> \<open>“cardinal less than \<^term>\<open>\<gamma>\<close>”\<close>
    and ?inQ="\<lambda>Y.{a\<in>G. \<forall>s\<in>Y. Q(s,a)}"
  from assms
  have "\<forall>Y \<in> ?cdlt\<gamma>. \<exists>a. a \<in> ?inQ(Y)"
    by blast
  then
  have "\<exists>f. f \<in> Pi(?cdlt\<gamma>,?inQ)"
    using AC_ball_Pi[of ?cdlt\<gamma> ?inQ] by simp
  then
  obtain f where f_type:"f \<in> Pi(?cdlt\<gamma>,?inQ)"
    by auto
  moreover
  define Cb where "Cb \<equiv> \<lambda>_\<in>Pow(G)-?cdlt\<gamma>. b"
  moreover from \<open>b\<in>G\<close>
  have "Cb \<in> Pow(G)-?cdlt\<gamma> \<rightarrow> G"
    unfolding Cb_def by simp
  moreover
  note \<open>Card(\<gamma>)\<close>
  ultimately
  have "f \<union> Cb : (\<Prod>x\<in>Pow(G). ?inQ(x) \<union> G)" using
      fun_Pi_disjoint_Un[ of f ?cdlt\<gamma>  ?inQ Cb "Pow(G)-?cdlt\<gamma>" "\<lambda>_.G"]
      Diff_partition[of "{X\<in>Pow(G). |X|<\<gamma>}" "Pow(G)", OF Collect_subset]
    by auto
  moreover
  have "?inQ(x) \<union> G = G" for x by auto
  ultimately
  have "f \<union> Cb : Pow(G) \<rightarrow> G" by simp
  define S where "S\<equiv>\<lambda>\<alpha>\<in>\<gamma>. rec_constr(f \<union> Cb, \<alpha>)"
  from \<open>f \<union> Cb: Pow(G) \<rightarrow> G\<close> \<open>Card(\<gamma>)\<close>
  have "S : \<gamma> \<rightarrow> G"
    using Ord_in_Ord unfolding S_def
    by (intro lam_type rec_constr_type) auto
  moreover
  have "\<forall>\<alpha>\<in>\<gamma>. \<forall>\<beta>\<in>\<gamma>. \<alpha> < \<beta> \<longrightarrow> Q(S ` \<alpha>, S ` \<beta>)"
  proof (intro ballI impI)
    fix \<alpha> \<beta>
    assume "\<beta>\<in>\<gamma>"
    with \<open>Card(\<gamma>)\<close>
    have "{rec_constr(f \<union> Cb, x) . x\<in>\<beta>} = {S`x . x \<in> \<beta>}"
      using Ord_trans[OF _ _ Card_is_Ord, of _ \<beta> \<gamma>]
      unfolding S_def
      by auto
    moreover from \<open>\<beta>\<in>\<gamma>\<close> \<open>S : \<gamma> \<rightarrow> G\<close> \<open>Card(\<gamma>)\<close>
    have "{S`x . x \<in> \<beta>} \<subseteq> G"
      using Ord_trans[OF _ _ Card_is_Ord, of _ \<beta> \<gamma>]
        apply_type[of S \<gamma> "\<lambda>_. G"] by auto
    moreover from \<open>Card(\<gamma>)\<close> \<open>\<beta>\<in>\<gamma>\<close>
    have "|{S`x . x \<in> \<beta>}| < \<gamma>"
      using cardinal_RepFun_le[of \<beta>]  Ord_in_Ord
        lt_trans1[of "|{S`x . x \<in> \<beta>}|" "|\<beta>|" \<gamma>]
        Card_lt_iff[THEN iffD2, of \<beta> \<gamma>, OF _ _ ltI]
      by force
    moreover
    have "\<forall>x\<in>\<beta>. Q(S`x, f ` {S`x . x \<in> \<beta>})"
    proof -
      from calculation and f_type
      have "f ` {S`x . x \<in> \<beta>} \<in> {a\<in>G. \<forall>x\<in>\<beta>. Q(S`x,a)}"
        using apply_type[of f ?cdlt\<gamma> ?inQ "{S`x . x \<in> \<beta>}"]
        by blast
      then
      show ?thesis by simp
    qed
    moreover
    assume "\<alpha>\<in>\<gamma>" "\<alpha> < \<beta>"
    moreover
    note \<open>\<beta>\<in>\<gamma>\<close> \<open>Cb \<in> Pow(G)-?cdlt\<gamma> \<rightarrow> G\<close>
    ultimately
    show "Q(S ` \<alpha>, S ` \<beta>)"
      using fun_disjoint_apply1[of "{S`x . x \<in> \<beta>}" Cb f]
        domain_of_fun[of Cb] ltD[of \<alpha> \<beta>]
      by (subst (2) S_def, auto) (subst rec_constr_unfold, auto)
  qed
  ultimately
  show ?thesis by blast
qed

text\<open>The following basic result can, in turn, be proved by a
     bounded-cardinal selection.\<close>
lemma Infinite_iff_lepoll_nat: "Infinite(X) \<longleftrightarrow> \<omega> \<lesssim> X"
proof
  assume "Infinite(X)"
  then
  obtain b where "b\<in>X"
    using Infinite_not_empty by auto
  {
    fix Y
    assume "|Y| < \<omega>"
    then
    have "Finite(Y)"
      using Finite_cardinal_iff' ltD nat_into_Finite by blast
    with \<open>Infinite(X)\<close>
    have "X \<noteq> Y" by auto
  }
  with \<open>b\<in>X\<close>
  obtain S where "S : \<omega> \<rightarrow> X"  "\<forall>\<alpha>\<in>\<omega>. \<forall>\<beta>\<in>\<omega>. \<alpha> < \<beta> \<longrightarrow> S`\<alpha> \<noteq> S`\<beta>"
    using bounded_cardinal_selection[of \<omega> X "\<lambda>x y. x\<noteq>y"]
      Card_nat by blast
  moreover from this
  have "\<alpha> \<in> \<omega> \<Longrightarrow> \<beta> \<in> \<omega> \<Longrightarrow> \<alpha>\<noteq>\<beta> \<Longrightarrow> S`\<alpha> \<noteq> S`\<beta>" for \<alpha> \<beta>
    by (rule_tac lt_neq_symmetry[of "\<omega>" "\<lambda>\<alpha> \<beta>. S`\<alpha> \<noteq> S`\<beta>"])
      auto
  ultimately
  show "\<omega> \<lesssim> X"
    unfolding lepoll_def inj_def by blast
qed (intro lepoll_nat_imp_Infinite)

lemma Infinite_InfCard_cardinal: "Infinite(X) \<Longrightarrow> InfCard(|X|)"
  using lepoll_eq_trans eqpoll_sym lepoll_nat_imp_Infinite
    Infinite_iff_lepoll_nat Inf_Card_is_InfCard cardinal_eqpoll
  by simp

lemma Finite_to_one_surj_imp_cardinal_eq:
  assumes "F \<in> Finite_to_one(X,Y) \<inter> surj(X,Y)" "Infinite(X)"
  shows "|Y| = |X|"
proof -
  from \<open>F \<in> Finite_to_one(X,Y) \<inter> surj(X,Y)\<close>
  have "X = (\<Union>y\<in>Y. {x\<in>X . F`x = y})"
    using apply_type by fastforce
  show ?thesis
  proof (cases "Finite(Y)")
    case True
    with \<open>X = (\<Union>y\<in>Y. {x\<in>X . F`x = y})\<close> and assms
    show ?thesis
      using Finite_RepFun[THEN [2] Finite_Union, of Y "\<lambda>y. {x\<in>X . F`x = y}"]
      by auto
  next
    case False
    moreover from this
    have "Y \<lesssim> |Y|"
      using cardinal_eqpoll eqpoll_sym eqpoll_imp_lepoll by simp
    moreover
    note assms
    moreover from calculation
    have "y \<in> Y \<Longrightarrow> |{x\<in>X . F`x = y}| \<le> |Y|" for y
      using Infinite_imp_nats_lepoll[THEN lepoll_imp_cardinal_le, of Y
          "|{x\<in>X . F`x = y}|"] cardinal_idem by auto
    ultimately
    have "|\<Union>y\<in>Y. {x\<in>X . F`x = y}| \<le> |Y|"
      using leqpoll_imp_cardinal_UN_le[of "|Y|" Y]
        Infinite_InfCard_cardinal[of Y] by simp
    moreover from \<open>F \<in> Finite_to_one(X,Y) \<inter> surj(X,Y)\<close>
    have "|Y| \<le> |X|"
      using surj_implies_cardinal_le by auto
    moreover
    note \<open>X = (\<Union>y\<in>Y. {x\<in>X . F`x = y})\<close>
    ultimately
    show ?thesis
      using le_anti_sym by auto
  qed
qed

lemma cardinal_map_Un:
  assumes "Infinite(X)" "Finite(b)"
  shows "|{a \<union> b . a \<in> X}| = |X|"
proof -
  have "(\<lambda>a\<in>X. a \<union> b) \<in> Finite_to_one(X,{a \<union> b . a \<in> X})"
    "(\<lambda>a\<in>X. a \<union> b) \<in>  surj(X,{a \<union> b . a \<in> X})"
    unfolding surj_def
  proof
    fix d
    have "Finite({a \<in> X . a \<union> b = d})" (is "Finite(?Y(b,d))")
      using \<open>Finite(b)\<close>
    proof (induct arbitrary:d)
      case 0
      have "{a \<in> X . a \<union> 0 = d} = (if d\<in>X then {d} else 0)"
        by auto
      then
      show ?case by simp
    next
      case (cons c b)
      from \<open>c \<notin> b\<close>
      have "?Y(cons(c,b),d) \<subseteq> (if c\<in>d then ?Y(b,d) \<union> ?Y(b,d-{c}) else 0)"
        by auto
      with cons
      show ?case
        using subset_Finite
        by simp
    qed
    moreover
    assume "d \<in> {x \<union> b . x \<in> X}"
    ultimately
    show "Finite({a \<in> X . (\<lambda>x\<in>X. x \<union> b) ` a = d})"
      by simp
  qed (auto intro:lam_funtype)
  with assms
  show ?thesis
    using Finite_to_one_surj_imp_cardinal_eq by fast
qed

end