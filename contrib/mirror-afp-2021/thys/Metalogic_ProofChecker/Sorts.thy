section "Sorts"

(* 
  Some stuff on sorts. Mostly from Sort.ML I think.
*)

theory Sorts
imports Term
begin

definition [simp]: "empty_osig = ({}, Map.empty)"

definition "sort_les cs s1 s2 = (sort_leq cs s1 s2 \<and> \<not> sort_leq cs s2 s1)"
definition "sort_eqv cs s1 s2 = (sort_leq cs s1 s2 \<and> sort_leq cs s2 s1)"

lemmas class_defs = class_leq_def class_les_def class_ex_def
lemmas sort_defs = sort_leq_def sort_les_def sort_eqv_def sort_ex_def

lemma sort_ex_class_ex: "sort_ex cs S \<equiv> \<forall>c \<in> S. class_ex cs c"
  by (auto simp add: sort_ex_def class_ex_def subset_eq)

(* Did not want to write the wf_subclass cs assumption each time + allowed type class instances inside
  Now probably more trouble than help
*)
locale wf_subclass_loc =
  fixes cs :: "class rel"
  assumes wf[simp]: "wf_subclass cs"
begin 

lemma class_les_irrefl: "\<not> class_les cs c c"
  using wf by (simp add: class_les_def)
lemma class_les_trans: "class_les cs x y \<Longrightarrow> class_les cs y z \<Longrightarrow> class_les cs x z"
  using wf by (auto simp add: class_les_def class_leq_def trans_def)

lemma class_leq_refl[iff]: "class_ex cs c \<Longrightarrow> class_leq cs c c" 
  using wf by (simp add: class_leq_def class_ex_def refl_on_def) 
lemma class_leq_trans: "class_leq cs x y \<Longrightarrow> class_leq cs y z \<Longrightarrow> class_leq cs x z"
  using wf by (auto simp add: class_leq_def elim: transE)
lemma class_leq_antisym: "class_leq cs c1 c2 \<Longrightarrow> class_leq cs c2 c1 \<Longrightarrow> c1=c2" 
  using wf by (auto intro: antisymD simp: trans_def class_leq_def)

(* classes form a ~ partial order with class_les/class_leq a for a well-formed a*)
lemma sort_leq_refl[iff]: "sort_ex cs s \<Longrightarrow> sort_leq cs s s" 
  using class_leq_refl by (auto simp add: sort_ex_class_ex sort_leq_def)
lemma sort_leq_trans: "sort_leq cs x y \<Longrightarrow> sort_leq cs y z \<Longrightarrow> sort_leq cs x z"
  by (meson class_leq_trans sort_leq_def)
lemma sort_leq_ex: "sort_leq cs s1 s2 \<Longrightarrow> sort_ex cs s2"
  by (auto simp add: sort_ex_def class_leq_def sort_leq_def intro: FieldI2)
(* ... *)

lemma sort_leq_minimize: 
  "sort_leq cs s1 s2 \<Longrightarrow> \<exists>s1'. (\<forall>c1 \<in> s1' . \<exists>c2 \<in> s2. class_leq cs c1 c2) \<and> sort_leq cs s1' s2"
  by (meson class_leq_refl sort_ex_class_ex sort_leq_ex sort_leq_refl)

lemma "sort_ex cs s2 \<Longrightarrow> s1 \<subseteq> s2 \<Longrightarrow> sort_ex cs s1"
  by (meson sort_ex_def subset_trans)

lemma superset_imp_sort_leq: "sort_ex cs s2 \<Longrightarrow> s1 \<supseteq> s2 \<Longrightarrow> sort_leq cs s1 s2"
  by (auto simp add: sort_ex_class_ex sort_leq_def sort_ex_def)
lemma full_sort_top: "sort_ex cs s \<Longrightarrow> sort_leq cs s full_sort" 
  by (simp add: sort_leq_def)

(* Is this even useful? *)
lemma sort_les_trans: "sort_les cs x y \<Longrightarrow> sort_les cs y z \<Longrightarrow> sort_les cs x z"
  using sort_les_def sort_leq_trans by blast
                                                               
lemma sort_eqvI: "sort_leq cs s1 s2 \<Longrightarrow> sort_leq cs s2 s1 \<Longrightarrow> sort_eqv cs s1 s2" 
  by (simp add: sort_eqv_def)
lemma sort_eqv_refl: "sort_ex cs s \<Longrightarrow> sort_eqv cs s s" 
  using sort_leq_refl by (auto simp add: sort_eqv_def)
lemma sort_eqv_trans: "sort_eqv cs x y \<Longrightarrow> sort_eqv cs y z \<Longrightarrow> sort_eqv cs x z"
  using sort_eqv_def sort_leq_trans by blast
lemma sort_eqv_sym: "sort_eqv cs x y \<Longrightarrow> sort_eqv cs y x"
  by (auto simp add: sort_eqv_def)
(* sort_eqv a is ~ equivalence relation.. *)

lemma normalize_sort_empty[simp]: "normalize_sort cs full_sort = full_sort"
  by (simp add: normalize_sort_def)
lemma normalize_sort_normalize_sort[simp]: 
  "normalize_sort cs (normalize_sort cs s) = normalize_sort cs s" 
  by (auto simp add: normalize_sort_def)

lemma sort_ex_norm_sort: "sort_ex cs s \<Longrightarrow> sort_ex cs (normalize_sort cs s)"
  by (simp add: normalize_sort_def sort_ex_class_ex)

lemma normalized_sort_subset: "normalize_sort cs s \<subseteq> s"
  by (auto simp add: normalize_sort_def)

lemma normalize_sort_removed_elem_irrelevant':
  assumes "sort_ex cs (insert c s)"
  assumes "c \<notin> (normalize_sort cs (insert c s))"
  shows "normalize_sort cs (insert c s) = normalize_sort cs s"
proof-
  have "class_ex cs c" using assms(1) by (auto simp add: sort_ex_class_ex)
  from this assms(2) obtain c' where "class_les cs c' c" "c' \<in> s"
    using class_les_irrefl by (auto simp add: normalize_sort_def)
  thus ?thesis 
    using \<open>class_ex cs c\<close> class_les_irrefl class_les_trans by (simp add: normalize_sort_def) blast
qed

corollary normalize_sort_removed_elem_irrelevant:
  assumes "sort_ex cs (insert c s)"
  assumes "c \<notin> (normalize_sort cs (insert c s))"
  shows "normalize_sort cs (insert c s) = normalize_sort cs s"
  using assms normalize_sort_removed_elem_irrelevant' 
  by (simp add: normalize_sort_def)

lemma normalize_sort_nempt_is_nempty:
  assumes finite: "finite s"
  assumes nempty: "s \<noteq> full_sort"
  assumes "sort_ex cs s"
  shows "normalize_sort cs s \<noteq> full_sort"
using assms proof (induction s rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert c s)
  note ICons = this
  then show ?case
  proof(cases s)
    case emptyI
    hence "normalize_sort cs (insert c s) = {c}"
      using insert class_les_irrefl by (auto simp add: normalize_sort_def sort_ex_class_ex)
    then show ?thesis by simp
  next
    case (insertI c' s')
    hence "normalize_sort cs s \<noteq> full_sort" 
      using ICons by (auto simp add: normalize_sort_def sort_ex_class_ex)
    then show ?thesis
    proof (cases "c \<in> (normalize_sort cs s)")
      case True
      hence "insert c s = s" 
        using normalized_sort_subset by fastforce
      then show ?thesis 
        using ICons by (auto simp add: normalize_sort_def sort_ex_class_ex class_les_def)
    next
      case False
      then show ?thesis 
        using normalize_sort_removed_elem_irrelevant
        using insert.prems(2) ICons(3) \<open>normalize_sort cs s \<noteq> full_sort\<close> by auto
    qed
  qed
qed

lemma choose_smaller_in_sort:
  assumes elem: "c \<in> s" and nelem: "c \<notin> (normalize_sort cs s)" and "sort_ex cs s"
  obtains c' where "c' \<in> s" and "class_les cs c' c"
  using assms by (auto simp add: normalize_sort_def sort_ex_class_ex)

lemma normalize_ex_bound':
  assumes finite: "finite s" and elem: "c \<in> s" and nelem: "c \<notin> (normalize_sort cs s)" 
    and "sort_ex cs s"
  shows "\<exists>c' \<in> (normalize_sort cs s) . class_les cs c' c"
using assms proof (induction s arbitrary: c)
  case empty
  then show ?case by simp
next
  case (insert ic s)
  then show ?case
  proof(cases "ic=c")
    case True
    then show ?thesis
      by (smt choose_smaller_in_sort class_les_irrefl class_les_trans insert.IH insert.prems(2) 
          insert.prems(3) insert_iff insert_subset normalize_sort_removed_elem_irrelevant' sort_ex_def)
  next
    case False
    hence "c \<in> s" using insert.prems by simp
    then show ?thesis
    proof(cases "ic \<in> (normalize_sort cs (insert ic s))")
      case True
      then show ?thesis
      proof(cases "class_les cs ic c")
        case True
        then show ?thesis
          using insert \<open>c \<in> s\<close> normalize_sort_removed_elem_irrelevant' sort_ex_def
          by (metis insert_subset)
      next
        case False
        
        obtain c'' where c'': "c'' \<in> (normalize_sort cs s)" "class_les cs c'' c"
          using insert \<open>c \<in> s\<close> normalize_sort_removed_elem_irrelevant' sort_ex_def
          by (metis False choose_smaller_in_sort class_les_trans insert_iff insert_subset)
        moreover have "(c'', c) \<in> cs" "(c, c'') \<notin> cs"
          using c'' by (simp_all add: class_leq_def class_les_def)
        moreover hence "\<not> class_les cs ic c''"
          by (meson False class_leq_def class_les_def class_les_trans)

        ultimately show ?thesis 
          by (auto simp add: normalize_sort_def sort_ex_class_ex class_ex_def class_leq_def class_les_def)
      qed
    next
      case False
      then show ?thesis
        by (metis (full_types) insert.IH insert.prems(2) insert.prems(3) \<open>c \<in> s\<close> 
            normalize_sort_removed_elem_irrelevant sort_ex_def insert_subset)
    qed
  qed
qed

corollary normalize_ex_bound:
  assumes finite: "finite s" and elem: "c \<in> s" and nelem: "c \<notin> (normalize_sort cs s)" 
    and "sort_ex cs s"
  obtains c' where "c' \<in> (normalize_sort cs s)" and "class_les cs c' c"
  using assms normalize_ex_bound' by auto

lemma "sort_ex cs s \<Longrightarrow> sort_leq cs s (normalize_sort cs s)" 
  by (auto simp add: normalize_sort_def sort_leq_def sort_ex_class_ex)
lemma sort_eqv_normalize_sort:
  assumes "finite s"
  assumes "sort_ex cs s" 
  shows "sort_eqv cs s (normalize_sort cs s)"
proof (intro sort_eqvI)
  show "sort_leq cs s (normalize_sort cs s)" 
    using assms(2) by (auto simp add:  normalize_sort_def sort_leq_def sort_ex_class_ex)
next
  show "sort_leq cs (normalize_sort cs s) s"
  proof (unfold sort_leq_def; intro ballI)
    fix c2 assume "c2 \<in> s"
    show "\<exists>c1 \<in> normalize_sort cs s. class_leq cs c1 c2"
    proof (cases "c2 \<in> normalize_sort cs s")
      case True
      then show ?thesis using \<open>c2 \<in> s\<close> assms sort_ex_class_ex by fast
    next
      case False
      from this obtain c' where "c' \<in> normalize_sort cs s" and "class_les cs c' c2" 
        using \<open>c2 \<in> s\<close> normalize_ex_bound assms by metis
      then show ?thesis using class_les_def by metis
    qed 
  qed
qed

lemma normalize_sort_eq_imp_sort_eqv: "sort_ex cs s1 \<Longrightarrow> sort_ex cs s2 \<Longrightarrow> finite s1 \<Longrightarrow> finite s2
  \<Longrightarrow> normalize_sort cs s1 = normalize_sort cs s2
  \<Longrightarrow> sort_eqv cs s1 s2"
  by (metis sort_eqv_sym sort_eqv_trans wf_subclass_loc.sort_eqv_normalize_sort wf_subclass_loc_axioms)

lemma "class_leq cs c1 c2 \<longleftrightarrow> class_les cs c1 c2 \<or> (c1=c2 \<and> class_ex cs c1)"
  by (meson FieldI1 class_ex_def class_leq_antisym class_leq_def class_leq_refl class_les_def)

lemma sort_eqv_imp_normalize_sort_eq:
  assumes "sort_ex cs s1" "sort_ex cs s2" "sort_eqv cs s1 s2"
  shows "normalize_sort cs s1 = normalize_sort cs s2"
proof (rule ccontr)
  have "sort_leq cs s1 s2" "sort_leq cs s2 s1"
    using assms(3) by (auto simp add: sort_eqv_def)

  assume "normalize_sort cs s1 \<noteq> normalize_sort cs s2"
  hence "\<not> normalize_sort cs s1 \<subseteq> normalize_sort cs s2 \<or> 
    \<not> normalize_sort cs s2 \<subseteq> normalize_sort cs s1"
    by simp
  from this consider "\<not> normalize_sort cs s1 \<subseteq> normalize_sort cs s2"
    | "normalize_sort cs s1 \<subseteq> normalize_sort cs s2" 
      "\<not> normalize_sort cs s2 \<subseteq> normalize_sort cs s1"
    by blast
  thus False
  proof cases
    case 1
    from this obtain c where c: "c \<in> normalize_sort cs s1" "c \<notin> normalize_sort cs s2"
      by blast
    from this obtain c' where c': "c' \<in> normalize_sort cs s2" "class_les cs c' c"
      by (smt \<open>sort_leq cs s1 s2\<close> \<open>sort_leq cs s2 s1\<close> class_les_def mem_Collect_eq normalize_sort_def 
          sort_leq_def wf_subclass_loc.class_leq_antisym wf_subclass_loc.class_leq_trans wf_subclass_loc_axioms)
    then show ?thesis
    proof(cases "c' \<in> normalize_sort cs s1")
      case True
      hence "c \<notin> normalize_sort cs s1"
        using c c' by (auto simp add: normalize_sort_def)
      then show ?thesis using c(1) by simp
    next
      case False
      from False c' obtain c'' where c'': "c'' \<in> normalize_sort cs s1" "class_les cs c'' c'"
      by (smt \<open>sort_leq cs s1 s2\<close> \<open>sort_leq cs s2 s1\<close> class_les_def mem_Collect_eq normalize_sort_def 
          sort_leq_def wf_subclass_loc.class_leq_antisym wf_subclass_loc.class_leq_trans wf_subclass_loc_axioms)
      hence "class_les cs c'' c"
        using c'(2) class_les_trans by blast
      hence "c \<notin> normalize_sort cs s1"
        using c c'' by (auto simp add: normalize_sort_def)
      then show ?thesis using c(1) by simp
    qed
  next
    (* Should work analogous, let's see *)
    case 2
    from this obtain c where c: "c \<in> normalize_sort cs s2" "c \<notin> normalize_sort cs s1"
      by blast
    from this obtain c' where c': "c' \<in> normalize_sort cs s1" "class_les cs c' c"
      by (smt \<open>sort_leq cs s1 s2\<close> \<open>sort_leq cs s2 s1\<close> class_les_def mem_Collect_eq normalize_sort_def 
          sort_leq_def wf_subclass_loc.class_leq_antisym wf_subclass_loc.class_leq_trans wf_subclass_loc_axioms)
    then show ?thesis
    proof(cases "c' \<in> normalize_sort cs s2")
      case True
      hence "c \<notin> normalize_sort cs s2"
        using c c' by (auto simp add: normalize_sort_def)
      then show ?thesis using c(1) by simp
    next
      case False
      from False c' obtain c'' where c'':"c''\<in> normalize_sort cs s2" "class_les cs c'' c'"
      by (smt \<open>sort_leq cs s1 s2\<close> \<open>sort_leq cs s2 s1\<close> class_les_def mem_Collect_eq normalize_sort_def 
          sort_leq_def wf_subclass_loc.class_leq_antisym wf_subclass_loc.class_leq_trans wf_subclass_loc_axioms)
      hence "class_les cs c'' c"
        using c'(2) class_les_trans by blast
      hence "c \<notin> normalize_sort cs s2"
        using c c'' by (auto simp add: normalize_sort_def)
      then show ?thesis using c(1) by simp
    qed
  qed
qed

corollary sort_eqv_iff_normalize_sort_eq:
  assumes "finite s1" "finite s2"
  assumes "sort_ex cs s1" "sort_ex cs s2"
  shows "sort_eqv cs s1 s2 \<longleftrightarrow> normalize_sort cs s1 = normalize_sort cs s2"
using assms normalize_sort_eq_imp_sort_eqv sort_eqv_imp_normalize_sort_eq by blast

end

lemma tcsigs_sorts_defined: "wf_osig oss \<Longrightarrow> 
  (\<forall>ars \<in> ran (tcsigs oss) . \<forall>ss \<in> ran ars . \<forall>s \<in> set ss. sort_ex (subclass oss) s)"
  by (cases oss) (simp add: wf_sort_def all_normalized_and_ex_tcsigs_def)

lemma osig_subclass_loc: "wf_osig oss \<Longrightarrow> wf_subclass_loc (subclass oss)"
  using wf_subclass_loc.intro by (cases oss) simp

lemma wf_osig_imp_wf_subclass_loc: "wf_osig oss \<Longrightarrow> wf_subclass_loc (subclass oss)"
  by (cases oss) (simp add: wf_subclass_loc_def)

lemma has_sort_Tv_imp_sort_leq: "has_sort oss (Tv idn S) S' \<Longrightarrow> sort_leq (subclass oss) S S'"
  by (auto simp add: has_sort.simps)

end