section \<open>Ordinal Partitions\<close>

text \<open>Material from Jean A. Larson,
     A short proof of a partition theorem for the ordinal $\omega^\omega$.
     \emph{Annals of Mathematical Logic}, 6:129–-145, 1973.
Also from ``Partition Relations'' by A. Hajnal and J. A. Larson,
in \emph{Handbook of Set Theory}, edited by Matthew Foreman and Akihiro Kanamori
(Springer, 2010).\<close>

theory Partitions
  imports Library_Additions "ZFC_in_HOL.ZFC_Typeclasses" "ZFC_in_HOL.Cantor_NF"

begin

abbreviation tp :: "V set \<Rightarrow> V"
  where "tp A \<equiv> ordertype A VWF"

subsection \<open>Ordinal Partitions: Definitions\<close>

definition partn_lst :: "[('a \<times> 'a) set, 'a set, V list, nat] \<Rightarrow> bool"
  where "partn_lst r B \<alpha> n \<equiv> \<forall>f \<in> [B]\<^bsup>n\<^esup>  \<rightarrow>  {..<length \<alpha>}.
              \<exists>i < length \<alpha>. \<exists>H. H \<subseteq> B \<and> ordertype H r = (\<alpha>!i) \<and> f ` (nsets H n) \<subseteq> {i}"

abbreviation partn_lst_VWF :: "V \<Rightarrow> V list \<Rightarrow> nat \<Rightarrow> bool"
  where "partn_lst_VWF \<beta> \<equiv> partn_lst VWF (elts \<beta>)"

lemma partn_lst_E:
  assumes "partn_lst r B \<alpha> n" "f \<in> nsets B n \<rightarrow>  {..<l}" "l = length \<alpha>"
  obtains i H where "i < l" "H \<subseteq> B"
                     "ordertype H r = \<alpha>!i" "f ` (nsets H n) \<subseteq> {i}"
  using assms by (auto simp: partn_lst_def)

lemma partn_lst_VWF_nontriv:
  assumes "partn_lst_VWF \<beta> \<alpha> n" "l = length \<alpha>" "Ord \<beta>" "l > 0"
  obtains i where "i < l" "\<alpha>!i \<le> \<beta>"
proof -
  have "{..<l} \<noteq> {}"
    by (simp add: \<open>l > 0\<close> lessThan_empty_iff)
  then obtain f where  "f \<in> nsets (elts \<beta>) n  \<rightarrow>  {..<l}"
    by (meson Pi_eq_empty equals0I)
  then obtain i H where "i < l" "H \<subseteq> elts \<beta>" and eq: "tp H = \<alpha>!i"
    using assms by (metis partn_lst_E)
  then have "\<alpha>!i \<le> \<beta>"
    by (metis \<open>H \<subseteq> elts \<beta>\<close> \<open>Ord \<beta>\<close> eq ordertype_le_Ord)
  then show thesis
    using \<open>i < l\<close> that by auto
qed

lemma partn_lst_triv0:
  assumes "\<alpha>!i = 0" "i < length \<alpha>" "n \<noteq> 0"
  shows "partn_lst r B \<alpha> n"
  by (metis partn_lst_def assms bot_least image_empty nsets_empty_iff ordertype_empty)

lemma partn_lst_triv1:
  assumes "\<alpha>!i \<le> 1" "i < length \<alpha>" "n > 1" "B \<noteq> {}" "wf r"  
  shows "partn_lst r B \<alpha> n"
  unfolding partn_lst_def
proof clarsimp
  obtain \<gamma> where "\<gamma> \<in> B" "\<alpha> \<noteq> []"
    using assms mem_0_Ord by fastforce
  have 01: "\<alpha>!i = 0 \<or> \<alpha>!i = 1"
    using assms by (fastforce simp: one_V_def)
  fix f
  assume f: "f \<in> [B]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>}"
  with assms have "ordertype {\<gamma>} r = 1 \<and> f ` [{\<gamma>}]\<^bsup>n\<^esup> \<subseteq> {i}"
                  "ordertype {} r = 0 \<and> f ` [{}]\<^bsup>n\<^esup> \<subseteq> {i}"
    by (auto simp: one_V_def ordertype_insert nsets_eq_empty)
  with assms 01 show "\<exists>i<length \<alpha>. \<exists>H\<subseteq>B. ordertype H r = \<alpha> ! i \<and> f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
    using \<open>\<gamma> \<in> B\<close> by auto
qed

lemma partn_lst_two_swap:
  assumes "partn_lst r B [x,y] n" shows "partn_lst r B [y,x] n"
proof -
  { fix f :: "'a set \<Rightarrow> nat"
    assume f: "f \<in> [B]\<^bsup>n\<^esup> \<rightarrow> {..<2}"
    then have f': "(\<lambda>i. 1 - i) \<circ> f \<in> [B]\<^bsup>n\<^esup> \<rightarrow> {..<2}"
      by (auto simp: Pi_def)
    obtain i H where "i<2" "H \<subseteq> B" "ordertype H r = ([x,y]!i)" "((\<lambda>i. 1 - i) \<circ> f) ` (nsets H n) \<subseteq> {i}"
      by (auto intro: partn_lst_E [OF assms f'])
    moreover have "f x = Suc 0" if "Suc 0 \<le> f x" "x\<in>[H]\<^bsup>n\<^esup>" for x
      using f that \<open>H \<subseteq> B\<close> nsets_mono  by (fastforce simp: Pi_iff)
    ultimately have "ordertype H r = [y,x] ! (1-i) \<and> f ` [H]\<^bsup>n\<^esup> \<subseteq> {1-i}"
      by (force simp: eval_nat_numeral less_Suc_eq)
    then have "\<exists>i H. i<2 \<and> H\<subseteq>B \<and> ordertype H r = [y,x] ! i \<and> f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
      by (metis Suc_1 \<open>H \<subseteq> B\<close> diff_less_Suc) }
  then show ?thesis
    by (auto simp: partn_lst_def eval_nat_numeral)
qed

lemma partn_lst_greater_resource:
  assumes M: "partn_lst r B \<alpha> n" and "B \<subseteq> C"
  shows "partn_lst r C \<alpha> n"
proof (clarsimp simp: partn_lst_def)
  fix f
  assume "f \<in> [C]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>}"
  then have "f \<in> [B]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>}"
    by (metis \<open>B \<subseteq> C\<close> part_fn_def part_fn_subset)
  then obtain i H where "i < length \<alpha>"
                   and "H \<subseteq> B" "ordertype H r = (\<alpha>!i)"
                   and "f ` nsets H n \<subseteq> {i}"
    using M partn_lst_def by metis
  then show "\<exists>i<length \<alpha>. \<exists>H\<subseteq>C. ordertype H r = \<alpha> ! i \<and> f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
    using \<open>B \<subseteq> C\<close> by blast
qed


lemma partn_lst_less:
  assumes M: "partn_lst r B \<alpha> n" and eq: "length \<alpha>' = length \<alpha>" and "List.set \<alpha>' \<subseteq> ON"
    and le: "\<And>i. i < length \<alpha> \<Longrightarrow> \<alpha>'!i \<le> \<alpha>!i "
    and r: "wf r" "trans r" "total_on B r" and "small B"
  shows "partn_lst r B \<alpha>' n"
proof (clarsimp simp: partn_lst_def)
  fix f
  assume "f \<in> [B]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>'}"
  then obtain i H where "i < length \<alpha>"
                   and "H \<subseteq> B" "small H" and H: "ordertype H r = (\<alpha>!i)"
                   and fi: "f ` nsets H n \<subseteq> {i}"
    using assms by (auto simp: partn_lst_def smaller_than_small)
  then have bij: "bij_betw (ordermap H r) H (elts (\<alpha>!i))"
    using ordermap_bij [of r H]
    by (smt assms(8) in_mono r(1) r(3) smaller_than_small total_on_def)
  define H' where "H' = inv_into H (ordermap H r) ` (elts (\<alpha>'!i))"
  have "H' \<subseteq> H"
    using bij \<open>i < length \<alpha>\<close> bij_betw_imp_surj_on le
    by (force simp: H'_def image_subset_iff intro: inv_into_into)
  moreover have ot: "ordertype H' r = (\<alpha>'!i)"
  proof (subst ordertype_eq_iff)
    show "Ord (\<alpha>' ! i)"
      using assms by (simp add: \<open>i < length \<alpha>\<close> subset_eq)
    show "small H'"
      by (simp add: H'_def)
    show "\<exists>f. bij_betw f H' (elts (\<alpha>' ! i)) \<and> (\<forall>x\<in>H'. \<forall>y\<in>H'. (f x < f y) = ((x, y) \<in> r))"
    proof (intro exI conjI ballI)
      show "bij_betw (ordermap H r) H' (elts (\<alpha>' ! i))"
        using \<open>H' \<subseteq> H\<close>
        by (metis H'_def \<open>i < length \<alpha>\<close> bij bij_betw_inv_into_RIGHT bij_betw_subset le less_eq_V_def)
      show "(ordermap H r x < ordermap H r y) = ((x, y) \<in> r)"
        if "x \<in> H'" "y \<in> H'" for x y
      proof (intro iffI ordermap_mono_less)
        assume "ordermap H r x < ordermap H r y"
        then show "(x, y) \<in> r"
          by (metis \<open>H \<subseteq> B\<close> assms(8) calculation in_mono leD ordermap_mono_le r smaller_than_small that total_on_def)
      qed (use assms that \<open>H' \<subseteq> H\<close> \<open>small H\<close> in auto)
    qed
    show "total_on H' r"
      using r by (meson \<open>H \<subseteq> B\<close> \<open>H' \<subseteq> H\<close> subsetD total_on_def)
  qed (use r in auto)
  ultimately show "\<exists>i<length \<alpha>'. \<exists>H\<subseteq>B. ordertype H r = \<alpha>' ! i \<and> f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
    using \<open>H \<subseteq> B\<close> \<open>i < length \<alpha>\<close> fi assms
    by (metis image_mono nsets_mono subset_trans)
qed


text \<open>Holds because no $n$-sets exist!\<close>
lemma partn_lst_VWF_degenerate:
  assumes "k < n"
  shows "partn_lst_VWF \<omega> (ord_of_nat k # \<alpha>s) n"
proof (clarsimp simp: partn_lst_def)
  fix f :: "V set \<Rightarrow> nat"
  have "[elts (ord_of_nat k)]\<^bsup>n\<^esup> = {}"
    by (simp add: nsets_eq_empty assms finite_Ord_omega)
  then have "f ` [elts (ord_of_nat k)]\<^bsup>n\<^esup> \<subseteq> {0}"
    by auto
  then show "\<exists>i < Suc (length \<alpha>s). \<exists>H\<subseteq>elts \<omega>. tp H = (ord_of_nat k # \<alpha>s) ! i \<and> f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
    using assms ordertype_eq_Ord [of "ord_of_nat k"] elts_ord_of_nat less_Suc_eq_0_disj
    by fastforce
qed

lemma partn_lst_VWF_\<omega>_2:
  assumes "Ord \<alpha>"
  shows "partn_lst_VWF (\<omega> \<up> (1+\<alpha>)) [2, \<omega> \<up> (1+\<alpha>)] 2" (is  "partn_lst_VWF ?\<beta> _ _")
proof (clarsimp simp: partn_lst_def)
  fix f
  assume f: "f \<in> [elts ?\<beta>]\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
  show "\<exists>i<Suc (Suc 0). \<exists>H\<subseteq>elts ?\<beta>. tp H = [2, ?\<beta>] ! i \<and> f ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
  proof (cases "\<exists>x \<in> elts ?\<beta>. \<exists>y \<in> elts ?\<beta>. x \<noteq> y \<and> f{x,y} = 0")
    case True
    then obtain x y where "x \<in> elts ?\<beta>" "y \<in> elts ?\<beta>" "x \<noteq> y" "f {x, y} = 0"
      by auto
    then have "{x,y} \<subseteq> elts ?\<beta>" "tp {x,y} = 2"
      "f ` [{x, y}]\<^bsup>2\<^esup> \<subseteq> {0}"
      by auto (simp add: eval_nat_numeral ordertype_VWF_finite_nat)
    with \<open>x \<noteq> y\<close> show ?thesis
      by (metis nth_Cons_0 zero_less_Suc)
  next
    case False
    with f have "\<forall>x\<in>elts ?\<beta>. \<forall>y\<in>elts ?\<beta>. x \<noteq> y \<longrightarrow> f {x, y} = 1"
      unfolding Pi_iff using lessThan_Suc by force
    then have "tp (elts ?\<beta>) = ?\<beta>" "f ` [elts ?\<beta>]\<^bsup>2\<^esup> \<subseteq> {Suc 0}"
      by (auto simp: assms nsets_2_eq)
    then show ?thesis
      by (metis lessI nth_Cons_0 nth_Cons_Suc subsetI)
  qed
qed


subsection \<open>Relating partition properties on @{term VWF} to the general case\<close>

text \<open>Two very similar proofs here!\<close>

lemma partn_lst_imp_partn_lst_VWF_eq:
  assumes part: "partn_lst r U \<alpha> n" and \<beta>: "ordertype U r = \<beta>" "small U" 
    and r: "wf r" "trans r" "total_on U r"
  shows "partn_lst_VWF \<beta> \<alpha> n"
  unfolding partn_lst_def
proof clarsimp
  fix f
  assume f: "f \<in> [elts \<beta>]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>}"
  define cv where "cv \<equiv> \<lambda>X. ordermap U r ` X"
  have bij: "bij_betw (ordermap U r) U (elts \<beta>)"
    using ordermap_bij [of "r" U] assms by blast 
  then have bij_cv: "bij_betw cv ([U]\<^bsup>n\<^esup>) ([elts \<beta>]\<^bsup>n\<^esup>)"
    using bij_betw_nsets cv_def by blast
  then have func: "f \<circ> cv \<in> [U]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>}" and "inj_on (ordermap U r) U"
    using bij bij_betw_def bij_betw_apply f by fastforce+
  then have cv_part: "\<lbrakk>\<forall>x\<in>[X]\<^bsup>n\<^esup>. f (cv x) = i; X \<subseteq> U; a \<in> [cv X]\<^bsup>n\<^esup>\<rbrakk> \<Longrightarrow> f a = i" for a X i n
    by (force simp: cv_def nsets_def subset_image_iff inj_on_subset finite_image_iff card_image)
  have ot_eq [simp]: "tp (cv X) = ordertype X r" if "X \<subseteq> U" for X
    unfolding cv_def
  proof (rule ordertype_inc_eq)
    fix u v
    assume "u \<in> X" "v \<in> X" and "(u,v) \<in> r"
    with that have "ordermap U r u < ordermap U r v"
      by (simp add: assms ordermap_mono_less subset_eq)
    then show "(ordermap U r u, ordermap U r v) \<in> VWF"
      by (simp add: r)
  next
    show "total_on X r"
      using that r by (auto simp: total_on_def)
    show "small X"
      by (meson \<open>small U\<close> smaller_than_small that)
  qed (use assms in auto)
  obtain X i where "X \<subseteq> U" and X: "ordertype X r = \<alpha>!i" "(f \<circ> cv) ` [X]\<^bsup>n\<^esup> \<subseteq> {i}" 
    and "i < length \<alpha>"
    using part func by (auto simp: partn_lst_def)
  show "\<exists>i < length \<alpha>. \<exists>H\<subseteq>elts \<beta>. tp H = \<alpha>!i \<and> f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
  proof (intro exI conjI)
    show "i < length \<alpha>"
      by (simp add: \<open>i < length \<alpha>\<close>)
    show "cv X \<subseteq> elts \<beta>"
      using \<open>X \<subseteq> U\<close> bij bij_betw_imp_surj_on cv_def by blast
    show "tp (cv X) = \<alpha> ! i"
      by (simp add: X(1) \<open>X \<subseteq> U\<close>)
    show "f ` [cv X]\<^bsup>n\<^esup> \<subseteq> {i}"
      using X \<open>X \<subseteq> U\<close> cv_part unfolding image_subset_iff cv_def
      by (metis comp_apply insertCI singletonD)
  qed
qed

lemma partn_lst_imp_partn_lst_VWF:
  assumes part: "partn_lst r U \<alpha> n" and \<beta>: "ordertype U r \<le> \<beta>" "small U" 
    and r: "wf r" "trans r" "total_on U r"
  shows "partn_lst_VWF \<beta> \<alpha> n"
  by (metis assms less_eq_V_def partn_lst_imp_partn_lst_VWF_eq partn_lst_greater_resource)

lemma partn_lst_VWF_imp_partn_lst_eq:
  assumes part: "partn_lst_VWF \<beta> \<alpha> n" and \<beta>: "ordertype U r = \<beta>" "small U" 
    and r: "wf r" "trans r" "total_on U r"
  shows "partn_lst r U \<alpha> n"
  unfolding partn_lst_def
proof clarsimp
  fix f
  assume f: "f \<in> [U]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>}"
  define cv where "cv \<equiv> \<lambda>X. inv_into U (ordermap U r) ` X"
  have bij: "bij_betw (ordermap U r) U (elts \<beta>)"
    using ordermap_bij [of "r" U] assms by blast 
  then have bij_cv: "bij_betw cv ([elts \<beta>]\<^bsup>n\<^esup>) ([U]\<^bsup>n\<^esup>)"
    using bij_betw_nsets bij_betw_inv_into unfolding cv_def by blast
  then have func: "f \<circ> cv \<in> [elts \<beta>]\<^bsup>n\<^esup> \<rightarrow> {..<length \<alpha>}"
    using bij_betw_apply f by fastforce
  have "inj_on (ordermap U r) U"
    using bij bij_betw_def by blast
  then have cv_part: "\<lbrakk>\<forall>x\<in>[X]\<^bsup>n\<^esup>. f (cv x) = i; X \<subseteq> elts \<beta>; a \<in> [cv X]\<^bsup>n\<^esup>\<rbrakk> \<Longrightarrow> f a = i" for a X i n
    apply ( simp add: cv_def nsets_def subset_image_iff inj_on_subset finite_image_iff card_image)
    by (metis bij bij_betw_def card_image inj_on_finite inj_on_inv_into subset_eq)
  have ot_eq [simp]: "ordertype (cv X) r = tp X" if "X \<subseteq> elts \<beta>" for X
    unfolding cv_def
  proof (rule ordertype_inc_eq)
    show "small X"
      using down that by auto
    show "(inv_into U (ordermap U r) x, inv_into U (ordermap U r) y) \<in> r"
      if "x \<in> X" "y \<in> X" and "(x,y) \<in> VWF" for x y
    proof -
      have xy: "x \<in> ordermap U r ` U" "y \<in> ordermap U r ` U"
        using \<open>X \<subseteq> elts \<beta>\<close> \<open>x \<in> X\<close> \<open>y \<in> X\<close> bij bij_betw_imp_surj_on by blast+
      then have eq: "ordermap U r (inv_into U (ordermap U r) x) = x" "ordermap U r (inv_into U (ordermap U r) y) = y"
        by (meson f_inv_into_f)+
      then have "y \<notin> elts x"
        by (metis (no_types) VWF_non_refl mem_imp_VWF that(3) trans_VWF trans_def)
      then show ?thesis
        by (metis (no_types) VWF_non_refl xy eq assms(3) inv_into_into ordermap_mono r(1) r(3) that(3) total_on_def)
    qed
  qed (use r in auto)
  obtain X i where "X \<subseteq> elts \<beta>" and X: "tp X = \<alpha>!i" "(f \<circ> cv) ` [X]\<^bsup>n\<^esup> \<subseteq> {i}" 
    and "i < length \<alpha>"
    using part func by (auto simp: partn_lst_def)
  show "\<exists>i < length \<alpha>. \<exists>H\<subseteq>U. ordertype H r = \<alpha>!i \<and> f ` [H]\<^bsup>n\<^esup> \<subseteq> {i}"
  proof (intro exI conjI)
    show "i < length \<alpha>"
      by (simp add: \<open>i < length \<alpha>\<close>)
    show "cv X \<subseteq> U"
      using \<open>X \<subseteq> elts \<beta>\<close> bij bij_betw_imp_surj_on bij_betw_inv_into cv_def by blast
    show "ordertype (cv X) r = \<alpha> ! i"
      by (simp add: X(1) \<open>X \<subseteq> elts \<beta>\<close>)
    show "f ` [cv X]\<^bsup>n\<^esup> \<subseteq> {i}"
      using X \<open>X \<subseteq> elts \<beta>\<close> cv_part unfolding image_subset_iff cv_def
      by (metis comp_apply insertCI singletonD)
  qed
qed

corollary partn_lst_VWF_imp_partn_lst:
  assumes "partn_lst_VWF \<beta> \<alpha> n" and \<beta>: "ordertype U r \<ge> \<beta>" "small U" 
          "wf r" "trans r" "total_on U r"
  shows "partn_lst r U \<alpha> n"
  by (metis assms less_eq_V_def partn_lst_VWF_imp_partn_lst_eq partn_lst_greater_resource)

subsection \<open>Simple consequences of the definitions\<close>

text \<open>A restatement of the infinite Ramsey theorem using partition notation\<close>
lemma Ramsey_partn: "partn_lst_VWF \<omega> [\<omega>,\<omega>] 2"
proof (clarsimp simp: partn_lst_def)
  fix f
  assume "f \<in> [elts \<omega>]\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
  then have *: "\<forall>x\<in>elts \<omega>. \<forall>y\<in>elts \<omega>. x \<noteq> y \<longrightarrow> f {x, y} < 2"
    by (auto simp: nsets_def eval_nat_numeral)
  obtain H i where H: "H \<subseteq> elts \<omega>" and "infinite H"
    and t: "i < Suc (Suc 0)"
    and teq: "\<forall>x\<in>H. \<forall>y\<in>H. x \<noteq> y \<longrightarrow> f {x, y} = i"
    using Ramsey2 [OF infinite_\<omega> *] by (auto simp: eval_nat_numeral)
  then have "tp H = [\<omega>, \<omega>] ! i"
    using less_2_cases eval_nat_numeral ordertype_infinite_\<omega> by force
  moreover have "f ` {N. N \<subseteq> H \<and> finite N \<and> card N = 2} \<subseteq> {i}"
    by (force simp: teq card_2_iff)
  ultimately have "f ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
    by (metis (no_types) nsets_def numeral_2_eq_2)
  then show "\<exists>i<Suc (Suc 0). \<exists>H\<subseteq>elts \<omega>. tp H = [\<omega>,\<omega>] ! i \<and> f ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
    using H \<open>tp H = [\<omega>, \<omega>] ! i\<close> t by blast
qed

text \<open>This is the counterexample sketched in Hajnal and Larson, section 9.1.\<close>
proposition omega_basic_counterexample:
  assumes "Ord \<alpha>"
  shows "\<not> partn_lst_VWF \<alpha> [succ (vcard \<alpha>), \<omega>] 2"
proof -
  obtain \<pi> where fun\<pi>: "\<pi> \<in> elts \<alpha> \<rightarrow> elts (vcard \<alpha>)" and inj\<pi>: "inj_on \<pi> (elts \<alpha>)"
    using inj_into_vcard by auto
  have Ord\<pi>: "Ord (\<pi> x)" if "x \<in> elts \<alpha>" for x
    using Ord_in_Ord fun\<pi> that by fastforce
  define f where "f A \<equiv> @i::nat. \<exists>x y. A = {x,y} \<and> x < y \<and> (\<pi> x < \<pi> y \<and> i=0 \<or> \<pi> y < \<pi> x \<and> i=1)" for A
  have f_Pi: "f \<in> [elts \<alpha>]\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
  proof
    fix A
    assume "A \<in> [elts \<alpha>]\<^bsup>2\<^esup>"
    then obtain x y where xy: "x \<in> elts \<alpha>" "y \<in> elts \<alpha>" "x < y" and A: "A = {x,y}"
      apply (clarsimp simp: nsets_2_eq)
      by (metis Ord_in_Ord Ord_linear_lt assms insert_commute)
    consider "\<pi> x < \<pi> y" | "\<pi> y < \<pi> x"
      by (metis Ord\<pi> Ord_linear_lt inj\<pi> inj_onD less_imp_not_eq2 xy)
    then show "f A \<in> {..<Suc (Suc 0)}"
      by (metis A One_nat_def lessI lessThan_iff zero_less_Suc \<open>x < y\<close> A exE_some [OF _ f_def])
  qed
  have fiff: "\<pi> x < \<pi> y \<and> i=0 \<or> \<pi> y < \<pi> x \<and> i=1"
    if f: "f {x,y} = i" and xy: "x \<in> elts \<alpha>" "y \<in> elts \<alpha>" "x<y" for x y i
  proof -
    consider "\<pi> x < \<pi> y" | "\<pi> y < \<pi> x"
      using xy by (metis Ord\<pi> Ord_linear_lt inj\<pi> inj_onD less_V_def)
    then show ?thesis
    proof cases
      case 1
      then have "f{x,y} = 0"
        using \<open>x<y\<close> by (force simp: f_def Set.doubleton_eq_iff)
    then show ?thesis
      using "1" f by auto
    next
      case 2
      then have "f{x,y} = 1"
      using \<open>x<y\<close> by (force simp: f_def Set.doubleton_eq_iff)
    then show ?thesis
      using "2" f by auto
    qed
  qed
  have False
    if eq: "tp H = succ (vcard \<alpha>)" and H: "H \<subseteq> elts \<alpha>"
    and 0: "\<And>A. A \<in> [H]\<^bsup>2\<^esup> \<Longrightarrow> f A = 0" for H
  proof -
    have [simp]: "small H"
      using H down by auto
    have OH: "Ord x" if "x \<in> H" for x
      using H Ord_in_Ord \<open>Ord \<alpha>\<close> that by blast
    have \<pi>: "\<pi> x < \<pi> y" if "x\<in>H" "y\<in>H" "x<y" for x y
      using 0 [of "{x,y}"] that H fiff by (fastforce simp: nsets_2_eq)
    have sub_vcard: "\<pi> ` H \<subseteq> elts (vcard \<alpha>)"
      using H fun\<pi> by auto
    have "tp H = tp (\<pi> ` H)"
    proof (rule ordertype_VWF_inc_eq [symmetric])
      show "\<pi> ` H \<subseteq> ON"
      using H Ord\<pi> by blast
    qed (auto simp: \<pi> OH subsetI)
    also have "\<dots> \<le> vcard \<alpha>"
      by (simp add: H sub_vcard assms ordertype_le_Ord)
    finally show False
      by (simp add: eq succ_le_iff)
  qed
  moreover have False
    if eq: "tp H = \<omega>" and H: "H \<subseteq> elts \<alpha>"
      and 1: "\<And>A. A \<in> [H]\<^bsup>2\<^esup> \<Longrightarrow> f A = Suc 0" for H
  proof -
    have [simp]: "small H"
      using H down by auto
    define \<eta> where "\<eta> \<equiv> inv_into H (ordermap H VWF) \<circ> ord_of_nat"
    have bij: "bij_betw (ordermap H VWF) H (elts \<omega>)"
      by (metis ordermap_bij \<open>small H\<close> eq total_on_VWF wf_VWF)
    then have "bij_betw (inv_into H (ordermap H VWF)) (elts \<omega>) H"
      by (simp add: bij_betw_inv_into)
    then have \<eta>: "bij_betw \<eta> UNIV H"
      unfolding \<eta>_def
      by (metis \<omega>_def bij_betw_comp_iff2 bij_betw_def elts_of_set inf inj_ord_of_nat order_refl)
    have Ord\<eta>: "Ord (\<eta> k)" for k
      by (meson H Ord_in_Ord UNIV_I \<eta> assms bij_betw_apply subsetD)
    obtain k where k: "((\<pi> \<circ> \<eta>)(Suc k), (\<pi> \<circ> \<eta>) k) \<notin> VWF"
      using wf_VWF wf_iff_no_infinite_down_chain by blast
    have \<pi>: "\<pi> y < \<pi> x" if "x\<in>H" "y\<in>H" "x<y" for x y
      using 1 [of "{x,y}"] that H fiff by (fastforce simp: nsets_2_eq)
    have False if "\<eta> (Suc k) \<le> \<eta> k"
    proof -
      have "(\<eta> (Suc k), \<eta> k) \<in> VWF \<or> \<eta> (Suc k) = \<eta> k"
        using that Ord\<eta> Ord_mem_iff_lt by auto
      then have "ordermap H VWF (\<eta> (Suc k)) \<le> ordermap H VWF (\<eta> k)"
        by (metis \<eta> \<open>small H\<close> bij_betw_imp_surj_on ordermap_mono_le rangeI trans_VWF wf_VWF)
      moreover have "ordermap H VWF (\<eta> (Suc k)) = succ (ord_of_nat k)"
        unfolding \<eta>_def using bij bij_betw_inv_into_right by force
      moreover have "ordermap H VWF (\<eta> k) = ord_of_nat k"
        apply (simp add: \<eta>_def)
        by (meson bij bij_betw_inv_into_right ord_of_nat_\<omega>)
      ultimately have "succ (ord_of_nat k) \<le> ord_of_nat k"
        by simp
      then show False
        by (simp add: less_eq_V_def)
    qed
    then have "\<eta> k < \<eta> (Suc k)"
      by (metis Ord\<eta> Ord_linear_lt dual_order.strict_implies_order eq_refl)
    then have "(\<pi> \<circ> \<eta>)(Suc k) < (\<pi> \<circ> \<eta>)k"
      using \<pi> \<eta> bij_betw_apply by force
    then show False
      using k
      apply (simp add: subset_iff)
      by (metis H Ord\<pi> UNIV_I VWF_iff_Ord_less \<eta> bij_betw_imp_surj_on image_subset_iff)
  qed
  ultimately show ?thesis
    apply (simp add: partn_lst_def image_subset_iff)
    by (metis f_Pi less_2_cases nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
qed

subsection \<open>Specker's theorem\<close>

definition form_split :: "[nat,nat,nat,nat,nat] \<Rightarrow> bool" where
  "form_split a b c d i \<equiv> a \<le> c \<and> (i=0 \<and> a<b \<and> b<c \<and> c<d \<or>
                                    i=1 \<and> a<c \<and> c<b \<and> b<d \<or>
                                    i=2 \<and> a<c \<and> c<d \<and> d<b \<or>
                                    i=3 \<and> a=c \<and> b\<noteq>d)"

definition form :: "[(nat*nat)set, nat] \<Rightarrow> bool" where
  "form u i \<equiv> \<exists>a b c d. u = {(a,b),(c,d)} \<and> form_split a b c d i"

definition scheme :: "[(nat*nat)set] \<Rightarrow> nat set" where
  "scheme u \<equiv> fst ` u \<union> snd ` u"

definition UU :: "(nat*nat) set"
  where "UU \<equiv> {(a,b). a < b}"

lemma ordertype_UNIV_\<omega>2: "ordertype UNIV pair_less = \<omega>\<up>2"
  using ordertype_Times [of concl: UNIV UNIV less_than less_than]
  by (simp add: total_less_than pair_less_def ordertype_nat_\<omega> numeral_2_eq_2)

lemma ordertype_UU_ge_\<omega>2:  "ordertype UNIV pair_less \<le> ordertype UU pair_less"
proof (rule ordertype_inc_le)
  define \<pi> where "\<pi> \<equiv> \<lambda>(m,n). (m, Suc (m+n))"
  show "(\<pi> (x::nat \<times> nat), \<pi> y) \<in> pair_less" if "(x, y) \<in> pair_less" for x y
    using that by (auto simp: \<pi>_def pair_less_def split: prod.split)
  show "range \<pi> \<subseteq> UU"
    by (auto simp: \<pi>_def UU_def)
qed auto

lemma ordertype_UU_\<omega>2: "ordertype UU pair_less = \<omega>\<up>2"
  by (metis eq_iff ordertype_UNIV_\<omega>2 ordertype_UU_ge_\<omega>2 ordertype_mono small top_greatest trans_pair_less wf_pair_less)


text \<open>Lemma 2.3 of Jean A. Larson,
     A short proof of a partition theorem for the ordinal $\omega^\omega$.
     \emph{Annals of Mathematical Logic}, 6:129–-145, 1973.\<close>
lemma lemma_2_3:
  fixes f :: "(nat \<times> nat) set \<Rightarrow> nat"
  assumes "f \<in> [UU]\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
  obtains N js where "infinite N" and "\<And>k u. \<lbrakk>k < 4; u \<in> [UU]\<^bsup>2\<^esup>; form u k; scheme u \<subseteq> N\<rbrakk> \<Longrightarrow> f u = js!k"
proof -
  have f_less2: "f {p,q} < Suc (Suc 0)" if "p \<noteq> q" "p \<in> UU" "q \<in> UU" for p q
  proof -
    have "{p,q} \<in> [UU]\<^bsup>2\<^esup>"
      using that by (simp add: nsets_def)
    then show ?thesis
      using assms by (simp add: Pi_iff)
  qed
  define f0 where "f0 \<equiv> (\<lambda>A::nat set. THE x. \<exists>a b c d. A = {a,b,c,d} \<and> a<b \<and> b<c \<and> c<d \<and> x = f {(a,b),(c,d)})"
  have f0: "f0 {a,b,c,d} = f {(a,b),(c,d)}" if "a<b" "b<c" "c<d" for a b c d
    unfolding f0_def
    apply (rule theI2 [where a = "f {(a,b), (c,d)}"])
    using that by (force simp: insert_eq_iff split: if_split_asm)+
  have "f0 X < Suc (Suc 0)"
    if "finite X" and "card X = 4" for X
  proof -
    have "X \<in> [X]\<^bsup>4\<^esup>"
      using that by (auto simp: nsets_def)
    then obtain a b c d where "X = {a,b,c,d} \<and> a<b \<and> b<c \<and> c<d"
      by (auto simp: ordered_nsets_4_eq)
    then show ?thesis
      using f0 f_less2 by (auto simp: UU_def)
  qed
  then have "\<exists>N t. infinite N \<and> t < Suc (Suc 0)
            \<and> (\<forall>X. X \<subseteq> N \<and> finite X \<and> card X = 4 \<longrightarrow> f0 X = t)"
    using Ramsey [of UNIV 4 f0 2] by (simp add: eval_nat_numeral)
  then obtain N0 j0 where "infinite N0" and j0: "j0 < Suc (Suc 0)" and N0: "\<And>A. A \<in> [N0]\<^bsup>4\<^esup> \<Longrightarrow> f0 A = j0"
    by (auto simp: nsets_def)

  define f1 where "f1 \<equiv> (\<lambda>A::nat set. THE x. \<exists>a b c d. A = {a,b,c,d} \<and> a<b \<and> b<c \<and> c<d \<and> x = f {(a,c),(b,d)})"
  have f1: "f1 {a,b,c,d} = f {(a,c),(b,d)}" if "a<b" "b<c" "c<d" for a b c d
    unfolding f1_def
    apply (rule theI2 [where a = "f {(a,c), (b,d)}"])
    using that by (force simp: insert_eq_iff split: if_split_asm)+
  have "f1 X < Suc (Suc 0)"
    if "finite X" and "card X = 4" for X
  proof -
    have "X \<in> [X]\<^bsup>4\<^esup>"
      using that by (auto simp: nsets_def)
    then obtain a b c d where "X = {a,b,c,d} \<and> a<b \<and> b<c \<and> c<d"
      by (auto simp: ordered_nsets_4_eq)
    then show ?thesis
      using f1 f_less2 by (auto simp: UU_def)
  qed
  then have "\<exists>N t. N \<subseteq> N0 \<and> infinite N \<and> t < Suc (Suc 0)
            \<and> (\<forall>X. X \<subseteq> N \<and> finite X \<and> card X = 4 \<longrightarrow> f1 X = t)"
    using \<open>infinite N0\<close> Ramsey [of N0 4 f1 2] by (simp add: eval_nat_numeral)
  then obtain N1 j1 where "N1 \<subseteq> N0" "infinite N1" and j1: "j1 < Suc (Suc 0)" and N1: "\<And>A. A \<in> [N1]\<^bsup>4\<^esup> \<Longrightarrow> f1 A = j1"
    by (auto simp: nsets_def)

  define f2 where "f2 \<equiv> (\<lambda>A::nat set. THE x. \<exists>a b c d. A = {a,b,c,d} \<and> a<b \<and> b<c \<and> c<d \<and> x = f {(a,d),(b,c)})"
  have f2: "f2 {a,b,c,d} = f {(a,d),(b,c)}" if "a<b" "b<c" "c<d" for a b c d
    unfolding f2_def
    apply (rule theI2 [where a = "f {(a,d), (b,c)}"])
    using that by (force simp: insert_eq_iff split: if_split_asm)+
  have "f2 X < Suc (Suc 0)"
    if "finite X" and "card X = 4" for X
  proof -
    have "X \<in> [X]\<^bsup>4\<^esup>"
      using that by (auto simp: nsets_def)
    then obtain a b c d where "X = {a,b,c,d} \<and> a<b \<and> b<c \<and> c<d"
      by (auto simp: ordered_nsets_4_eq)
    then show ?thesis
      using f2 f_less2 by (auto simp: UU_def)
  qed
  then have "\<exists>N t. N \<subseteq> N1 \<and> infinite N \<and> t < Suc (Suc 0)
            \<and> (\<forall>X. X \<subseteq> N \<and> finite X \<and> card X = 4 \<longrightarrow> f2 X = t)"
    using \<open>infinite N1\<close> Ramsey [of N1 4 f2 2] by (simp add: eval_nat_numeral)
  then obtain N2 j2 where "N2 \<subseteq> N1" "infinite N2" and j2: "j2 < Suc (Suc 0)" and N2: "\<And>A. A \<in> [N2]\<^bsup>4\<^esup> \<Longrightarrow> f2 A = j2"
    by (auto simp: nsets_def)

  define f3 where "f3 \<equiv> (\<lambda>A::nat set. THE x. \<exists>a b c. A = {a,b,c} \<and> a<b \<and> b<c \<and> x = f {(a,b),(a,c)})"
  have f3: "f3 {a,b,c} = f {(a,b),(a,c)}" if "a<b" "b<c" for a b c
    unfolding f3_def
    apply (rule theI2 [where a = "f {(a,b), (a,c)}"])
    using that by (force simp: insert_eq_iff split: if_split_asm)+
  have f3': "f3 {a,b,c} = f {(a,b),(a,c)}" if "a<c" "c<b" for a b c
    using f3 [of a c b] that
    by (simp add: insert_commute)
  have "f3 X < Suc (Suc 0)"
    if "finite X" and "card X = 3" for X
  proof -
    have "X \<in> [X]\<^bsup>3\<^esup>"
      using that by (auto simp: nsets_def)
    then obtain a b c where "X = {a,b,c} \<and> a<b \<and> b<c"
      by (auto simp: ordered_nsets_3_eq)
    then show ?thesis
      using f3 f_less2 by (auto simp: UU_def)
  qed
  then have "\<exists>N t. N \<subseteq> N2 \<and> infinite N \<and> t < Suc (Suc 0)
            \<and> (\<forall>X. X \<subseteq> N \<and> finite X \<and> card X = 3 \<longrightarrow> f3 X = t)"
    using \<open>infinite N2\<close> Ramsey [of N2 3 f3 2] by (simp add: eval_nat_numeral)
  then obtain N3 j3 where "N3 \<subseteq> N2" "infinite N3" and j3: "j3 < Suc (Suc 0)" and N3: "\<And>A. A \<in> [N3]\<^bsup>3\<^esup> \<Longrightarrow> f3 A = j3"
    by (auto simp: nsets_def)

  show thesis
  proof
    fix k u
    assume "k < 4"
      and u: "form u k" "scheme u \<subseteq> N3"
      and UU: "u \<in> [UU]\<^bsup>2\<^esup>"
    then consider (0) "k=0" | (1) "k=1" | (2) "k=2" | (3) "k=3"
      by linarith
    then show "f u = [j0,j1,j2,j3] ! k"
    proof cases
      case 0
      have "N3 \<subseteq> N0"
        using \<open>N1 \<subseteq> N0\<close> \<open>N2 \<subseteq> N1\<close> \<open>N3 \<subseteq> N2\<close> by auto
      then show ?thesis
        using u 0
        apply (auto simp: form_def form_split_def scheme_def simp flip: f0)
        apply (force simp: nsets_def intro: N0)
        done
    next
      case 1
      have "N3 \<subseteq> N1"
        using \<open>N2 \<subseteq> N1\<close> \<open>N3 \<subseteq> N2\<close> by auto
      then show ?thesis
        using u 1
        apply (auto simp: form_def form_split_def scheme_def simp flip: f1)
        apply (force simp: nsets_def intro: N1)
        done
    next
      case 2
      then show ?thesis
        using u \<open>N3 \<subseteq> N2\<close>
        apply (auto simp: form_def form_split_def scheme_def nsets_def simp flip: f2)
        apply (force simp: nsets_def intro: N2)
        done
    next
      case 3
      { fix a b d
        assume "{(a, b), (a, d)} \<in> [UU]\<^bsup>2\<^esup>"
          and *: "a \<in> N3" "b \<in> N3" "d \<in> N3" "b \<noteq> d"
        then have "a<b" "a<d"
          by (auto simp: UU_def nsets_def)
        then have "f {(a, b), (a, d)} = j3"
          using *
          apply (auto simp: neq_iff simp flip: f3 f3')
           apply (force simp: nsets_def intro: N3)+
          done
      }
      then show ?thesis
        using u UU 3
        by (auto simp: form_def form_split_def scheme_def)
    qed
  qed (rule \<open>infinite N3\<close>)
qed


text \<open>Lemma 2.4 of Jean A. Larson, ibid.\<close>
lemma lemma_2_4:
  assumes "infinite N" "k < 4"
  obtains M where "M \<in> [UU]\<^bsup>m\<^esup>" "\<And>u. u \<in> [M]\<^bsup>2\<^esup> \<Longrightarrow> form u k" "\<And>u. u \<in> [M]\<^bsup>2\<^esup> \<Longrightarrow> scheme u \<subseteq> N"
proof -
  obtain f:: "nat \<Rightarrow> nat" where "bij_betw f UNIV N" "strict_mono f"
    using assms by (meson bij_enumerate enumerate_mono strict_monoI)
  then have iff[simp]: "f x = f y \<longleftrightarrow> x=y" "f x < f y \<longleftrightarrow> x<y" for x y
    by (simp_all add: strict_mono_eq strict_mono_less)
  have [simp]: "f x \<in> N" for x
    using bij_betw_apply [OF \<open>bij_betw f UNIV N\<close>] by blast
  define M0 where "M0 = (\<lambda>i. (f(2*i), f(Suc(2*i)))) ` {..<m}"
  define M1 where "M1 = (\<lambda>i. (f i, f(m+i))) ` {..<m}"
  define M2 where "M2 = (\<lambda>i. (f i, f(2*m-i))) ` {..<m}"
  define M3 where "M3 = (\<lambda>i. (f 0, f (Suc i))) ` {..<m}"
  consider (0) "k=0" | (1) "k=1" | (2) "k=2" | (3) "k=3"
    using assms by linarith
  then show thesis
  proof cases
    case 0
    show ?thesis
    proof
      have "inj_on (\<lambda>i. (f (2 * i), f (Suc (2 * i)))) {..<m}"
        by (auto simp: inj_on_def)
      then show "M0 \<in> [UU]\<^bsup>m\<^esup>"
        by (simp add: M0_def nsets_def card_image UU_def image_subset_iff)
    next
      fix u
      assume u: "(u::(nat \<times> nat) set) \<in> [M0]\<^bsup>2\<^esup>"
      then obtain x y where "u = {x,y}" "x \<noteq> y" "x \<in> M0" "y \<in> M0"
        by (auto simp: nsets_2_eq)
      then obtain i j where "i<j" "j<m" and ueq: "u = {(f(2*i), f(Suc(2*i))), (f(2*j), f(Suc(2*j)))}"
        apply (clarsimp simp: M0_def)
        apply (metis (full_types) insert_commute less_linear)+
        done
      moreover have "f (2 * i) \<le> f (2 * j)"
        by (simp add: \<open>i<j\<close> less_imp_le_nat)
      ultimately show "form u k"
        apply (simp add: 0 form_def form_split_def nsets_def)
        apply (rule_tac x="f (2 * i)" in exI)
        apply (rule_tac x="f (Suc (2 * i))" in exI)
        apply (rule_tac x="f (2 * j)" in exI)
        apply (rule_tac x="f (Suc (2 * j))" in exI)
        apply auto
        done
      show "scheme u \<subseteq> N"
        using ueq by (auto simp: scheme_def)
    qed
  next
    case 1
    show ?thesis
    proof
      have "inj_on (\<lambda>i. (f i, f(m+i))) {..<m}"
        by (auto simp: inj_on_def)
      then show "M1 \<in> [UU]\<^bsup>m\<^esup>"
        by (simp add: M1_def nsets_def card_image UU_def image_subset_iff)
    next
      fix u
      assume u: "(u::(nat \<times> nat) set) \<in> [M1]\<^bsup>2\<^esup>"
      then obtain x y where "u = {x,y}" "x \<noteq> y" "x \<in> M1" "y \<in> M1"
        by (auto simp: nsets_2_eq)
      then obtain i j where "i<j" "j<m" and ueq: "u = {(f i, f(m+i)), (f j, f(m+j))}"
        apply (auto simp: M1_def)
        apply (metis (full_types) insert_commute less_linear)+
        done
      then show "form u k"
        apply (simp add: 1 form_def form_split_def nsets_def)
        by (metis iff(2) nat_add_left_cancel_less nat_less_le trans_less_add1)
      show "scheme u \<subseteq> N"
        using ueq by (auto simp: scheme_def)
    qed
  next
    case 2
    show ?thesis
    proof
      have "inj_on (\<lambda>i. (f i, f(2*m-i))) {..<m}"
        by (auto simp: inj_on_def)
      then show "M2 \<in> [UU]\<^bsup>m\<^esup>"
        by (auto simp: M2_def nsets_def card_image UU_def image_subset_iff)
    next
      fix u
      assume u: "(u::(nat \<times> nat) set) \<in> [M2]\<^bsup>2\<^esup>"
      then obtain x y where "u = {x,y}" "x \<noteq> y" "x \<in> M2" "y \<in> M2"
        by (auto simp: nsets_2_eq)
      then obtain i j where "i<j" "j<m" and ueq: "u = {(f i, f(2*m-i)), (f j, f(2*m-j))}"
        apply (auto simp: M2_def)
        apply (metis (full_types) insert_commute less_linear)+
        done
      then show "form u k"
        apply (simp add: 2 form_def form_split_def nsets_def)
        apply (rule_tac x="f i" in exI)
        apply (rule_tac x="f (2 * m - i)" in exI)
        apply (rule_tac x="f j" in exI)
        apply (rule_tac x="f (2 * m - j)" in exI)
        apply (auto simp: less_imp_le_nat)
        done
      show "scheme u \<subseteq> N"
        using ueq by (auto simp: scheme_def)
    qed
  next
    case 3
    show ?thesis
    proof
      have "inj_on (\<lambda>i. (f 0, f (Suc i))) {..<m}"
        by (auto simp: inj_on_def)
      then show "M3 \<in> [UU]\<^bsup>m\<^esup>"
        by (auto simp: M3_def nsets_def card_image UU_def image_subset_iff)
    next
      fix u
      assume u: "(u::(nat \<times> nat) set) \<in> [M3]\<^bsup>2\<^esup>"
      then obtain x y where "u = {x,y}" "x \<noteq> y" "x \<in> M3" "y \<in> M3"
        by (auto simp: nsets_2_eq)
      then obtain i j where "i<j" "j<m" and ueq: "u = {(f 0, f(Suc i)), (f 0, f(Suc j))}"
        apply (auto simp: M3_def)
        apply (metis (full_types) insert_commute less_linear)+
        done
      then show "form u k"
        by (fastforce simp: 3 form_def form_split_def nsets_def)
      show "scheme u \<subseteq> N"
        using ueq by (auto simp: scheme_def)
    qed
  qed
qed


text \<open>Lemma 2.5 of Jean A. Larson, ibid.\<close>
lemma lemma_2_5:
  assumes "infinite N"
  obtains X where "X \<subseteq> UU" "ordertype X pair_less = \<omega>\<up>2"
            "\<And>u. u \<in> [X]\<^bsup>2\<^esup> \<Longrightarrow> (\<exists>k<4. form u k) \<and> scheme u \<subseteq> N"
proof -
  obtain C
    where dis: "pairwise (\<lambda>i j. disjnt (C i) (C j)) UNIV"
      and N: "(\<Union>i. C i) \<subseteq> N" and infC: "\<And>i::nat. infinite (C i)"
    using assms infinite_infinite_partition by blast
  then have "\<exists>\<phi>::nat \<Rightarrow> nat. inj \<phi> \<and> range \<phi> = C i \<and> strict_mono \<phi>" for i
    by (metis bij_betw_imp_inj_on bij_betw_imp_surj_on bij_enumerate enumerate_mono infC strict_mono_def)
  then obtain \<phi>:: "[nat,nat] \<Rightarrow> nat"
      where \<phi>: "\<And>i. inj (\<phi> i) \<and> range (\<phi> i) = C i \<and> strict_mono (\<phi> i)"
    by metis
  then have \<pi>_in_C [simp]: "\<phi> i j \<in> C i' \<longleftrightarrow> i'=i" for i i' j
    using dis by (fastforce simp: pairwise_def disjnt_def)
  have less_iff [simp]: "\<phi> i j' < \<phi> i j \<longleftrightarrow> j' < j" for i j' j
    by (simp add: \<phi> strict_mono_less)
  let ?a = "\<phi> 0"
  define X where "X \<equiv> {(?a i, b) | i b. ?a i < b \<and> b \<in> C (Suc i)}"
  show thesis
  proof
    show "X \<subseteq> UU"
      by (auto simp: X_def UU_def)
    show "ordertype X pair_less = \<omega>\<up>2"
    proof (rule antisym)
      have "ordertype X pair_less \<le> ordertype UU pair_less"
        by (simp add: \<open>X \<subseteq> UU\<close> ordertype_mono)
      then show "ordertype X pair_less \<le> \<omega>\<up>2"
        using ordertype_UU_\<omega>2 by auto
      define \<pi> where "\<pi> \<equiv> \<lambda>(i,j::nat). (?a i, \<phi> (Suc i) (?a j))"
      have "\<And>i j. i < j \<Longrightarrow> \<phi> 0 i < \<phi> (Suc i) (\<phi> 0 j)"
        by (meson \<phi> le_less_trans less_iff strict_mono_imp_increasing)
      then have subX: "\<pi> ` UU \<subseteq> X"
        by (auto simp: UU_def \<pi>_def X_def)
      then have "ordertype (\<pi> ` UU) pair_less \<le> ordertype X pair_less"
        by (simp add: ordertype_mono)
      moreover have "ordertype (\<pi> ` UU) pair_less = ordertype UU pair_less"
      proof (rule ordertype_inc_eq)
        show "(\<pi> x, \<pi> y) \<in> pair_less"
          if "x \<in> UU" "y \<in> UU" and "(x, y) \<in> pair_less" for x y
          using that by (auto simp: UU_def \<pi>_def pair_less_def)
      qed auto
      ultimately show "\<omega>\<up>2 \<le> ordertype X pair_less"
        using ordertype_UU_\<omega>2 by simp
    qed
  next
    fix U
    assume "U \<in> [X]\<^bsup>2\<^esup>"
    then obtain a b c d where Ueq: "U = {(a,b),(c,d)}" and ne: "(a,b) \<noteq> (c,d)" and inX: "(a,b) \<in> X" "(c,d) \<in> X" and "a \<le> c"
      apply (auto simp: nsets_def subset_iff eval_nat_numeral card_Suc_eq Set.doubleton_eq_iff)
       apply (metis  nat_le_linear)+
      done
    show "(\<exists>k<4. form U k) \<and> scheme U \<subseteq> N"
    proof
      show "scheme U \<subseteq> N"
        using inX N \<phi> by (fastforce simp: scheme_def Ueq X_def)
    next
      consider "a < c" | "a = c \<and> b \<noteq> d"
        using \<open>a \<le> c\<close> ne nat_less_le by blast
      then show "\<exists>k<4. form U k"
      proof cases
        case 1
        have *: "a < b"  "b \<noteq> c" "c < d"
          using inX by (auto simp: X_def)
        moreover have "\<lbrakk>a < c; c < b; \<not> d < b\<rbrakk> \<Longrightarrow> b < d"
          using inX apply (clarsimp simp: X_def not_less)
          by (metis \<phi> \<pi>_in_C imageE nat.inject nat_less_le)
        ultimately consider (k0) "a<b \<and> b<c \<and> c<d" | (k1) "a<c \<and> c<b \<and> b<d" | (k2) "a<c \<and> c<d \<and> d<b"
          using 1 less_linear by blast
        then show ?thesis
        proof cases
          case k0
          then have "form U 0"
            unfolding form_def form_split_def using Ueq \<open>a \<le> c\<close> by blast
          then show ?thesis by force
        next
          case k1
          then have "form U 1"
            unfolding form_def form_split_def using Ueq \<open>a \<le> c\<close> by blast
          then show ?thesis by force
        next
          case k2
          then have "form U 2"
            unfolding form_def form_split_def using Ueq \<open>a \<le> c\<close> by blast
          then show ?thesis by force
        qed
      next
        case 2
        then have "form_split a b c d 3"
          by (auto simp: form_split_def)
        then show ?thesis
          using Ueq form_def leI by force
      qed
    qed
  qed
qed

text \<open>Theorem 2.1 of Jean A. Larson, ibid.\<close>
lemma Specker_aux:
  assumes "\<alpha> \<in> elts \<omega>"
  shows "partn_lst pair_less UU [\<omega>\<up>2,\<alpha>] 2"
  unfolding partn_lst_def
proof clarsimp
  fix f
  assume f: "f \<in> [UU]\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
  let ?P0 = "\<exists>X \<subseteq> UU. ordertype X pair_less = \<omega>\<up>2 \<and> f ` [X]\<^bsup>2\<^esup> \<subseteq> {0}"
  let ?P1 = "\<exists>M \<subseteq> UU. ordertype M pair_less = \<alpha> \<and> f ` [M]\<^bsup>2\<^esup> \<subseteq> {1}"
  have \<dagger>: "?P0 \<or> ?P1"
  proof (rule disjCI)
    assume "\<not> ?P1"
    then have not1: "\<And>M. \<lbrakk>M \<subseteq> UU; ordertype M pair_less = \<alpha>\<rbrakk> \<Longrightarrow> \<exists>x\<in>[M]\<^bsup>2\<^esup>. f x \<noteq> Suc 0" 
      by auto
    obtain m where m: "\<alpha> = ord_of_nat m"
      using assms elts_\<omega> by auto
    then have f_eq_0: "M \<in> [UU]\<^bsup>m\<^esup> \<Longrightarrow> \<exists>x\<in>[M]\<^bsup>2\<^esup>. f x = 0" for M
      using not1 [of M] finite_ordertype_eq_card [of M pair_less m] f
      apply (clarsimp simp: nsets_def eval_nat_numeral Pi_def)
      by (meson less_Suc0 not_less_less_Suc_eq subset_trans)
    obtain N js where "infinite N" and N: "\<And>k u. \<lbrakk>k < 4; u \<in> [UU]\<^bsup>2\<^esup>; form u k; scheme u \<subseteq> N\<rbrakk> \<Longrightarrow> f u = js!k"
      using f lemma_2_3 by blast
    obtain M0 where M0: "M0 \<in> [UU]\<^bsup>m\<^esup>" "\<And>u. u \<in> [M0]\<^bsup>2\<^esup> \<Longrightarrow> form u 0" "\<And>u. u \<in> [M0]\<^bsup>2\<^esup> \<Longrightarrow> scheme u \<subseteq> N"
      by (rule lemma_2_4 [OF \<open>infinite N\<close>]) auto
    obtain M1 where M1: "M1 \<in> [UU]\<^bsup>m\<^esup>" "\<And>u. u \<in> [M1]\<^bsup>2\<^esup> \<Longrightarrow> form u 1" "\<And>u. u \<in> [M1]\<^bsup>2\<^esup> \<Longrightarrow> scheme u \<subseteq> N"
      by (rule lemma_2_4 [OF \<open>infinite N\<close>]) auto
    obtain M2 where M2: "M2 \<in> [UU]\<^bsup>m\<^esup>" "\<And>u. u \<in> [M2]\<^bsup>2\<^esup> \<Longrightarrow> form u 2" "\<And>u. u \<in> [M2]\<^bsup>2\<^esup> \<Longrightarrow> scheme u \<subseteq> N"
      by (rule lemma_2_4 [OF \<open>infinite N\<close>]) auto
    obtain M3 where M3: "M3 \<in> [UU]\<^bsup>m\<^esup>" "\<And>u. u \<in> [M3]\<^bsup>2\<^esup> \<Longrightarrow> form u 3" "\<And>u. u \<in> [M3]\<^bsup>2\<^esup> \<Longrightarrow> scheme u \<subseteq> N"
      by (rule lemma_2_4 [OF \<open>infinite N\<close>]) auto
    have "js!0 = 0"
      using N [of 0 ] M0 f_eq_0 [of M0] by (force simp: nsets_def eval_nat_numeral)
    moreover have "js!1 = 0"
      using N [of 1] M1 f_eq_0 [of M1] by (force simp: nsets_def eval_nat_numeral)
    moreover have "js!2 = 0"
      using N [of 2 ] M2 f_eq_0 [of M2] by (force simp: nsets_def eval_nat_numeral)
    moreover have "js!3 = 0"
      using N [of 3 ] M3 f_eq_0 [of M3] by (force simp: nsets_def eval_nat_numeral)
    ultimately have js0: "js!k = 0" if "k < 4" for k
      using that by (auto simp: eval_nat_numeral less_Suc_eq)
    obtain X where "X \<subseteq> UU" and otX: "ordertype X pair_less = \<omega>\<up>2"
      and X: "\<And>u. u \<in> [X]\<^bsup>2\<^esup> \<Longrightarrow> (\<exists>k<4. form u k) \<and> scheme u \<subseteq> N"
      using \<open>infinite N\<close> lemma_2_5 by auto
    moreover have "f ` [X]\<^bsup>2\<^esup> \<subseteq> {0}"
    proof (clarsimp simp: image_subset_iff)
      fix u
      assume u: "u \<in> [X]\<^bsup>2\<^esup>"
      then have u_UU2: "u \<in> [UU]\<^bsup>2\<^esup>"
        using \<open>X \<subseteq> UU\<close> nsets_mono by blast
      show "f u = 0"
        using X u N [OF _ u_UU2] js0 by auto
    qed
    ultimately show "\<exists>X \<subseteq> UU. ordertype X pair_less = \<omega>\<up>2 \<and> f ` [X]\<^bsup>2\<^esup> \<subseteq> {0}"
      by blast
  qed
  then show "\<exists>i<Suc (Suc 0). \<exists>H\<subseteq>UU. ordertype H pair_less = [\<omega>\<up>2, \<alpha>] ! i \<and> f ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
  proof 
    show "?P0 \<Longrightarrow> ?thesis"
      by (metis nth_Cons_0 numeral_2_eq_2 pos2)
    show "?P1 \<Longrightarrow> ?thesis"
      by (metis One_nat_def lessI nth_Cons_0 nth_Cons_Suc)
  qed
qed

theorem Specker: "\<alpha> \<in> elts \<omega> \<Longrightarrow> partn_lst_VWF (\<omega>\<up>2) [\<omega>\<up>2,\<alpha>] 2"
  using partn_lst_imp_partn_lst_VWF_eq [OF Specker_aux] ordertype_UU_\<omega>2 wf_pair_less by blast

end
