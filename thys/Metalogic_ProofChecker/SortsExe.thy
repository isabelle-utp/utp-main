
section "Executable Sorts"

theory SortsExe
  imports Sorts
begin

type_synonym exeosig = "(class \<times> class) list \<times> (name \<times> (class \<times> sort list) list) list"

abbreviation (input) "execlasses \<equiv> fst"
abbreviation (input) "exetcsigs \<equiv> snd"

(* Eliminate fully? *)
abbreviation alist_conds :: "('k::linorder \<times> 'v) list \<Rightarrow> bool" where
  "alist_conds al \<equiv> distinct (map fst al)"

(* This is not executable *)
definition exe_ars_conds :: "(name \<times> (class \<times> sort list) list) list \<Rightarrow> bool" where
  "exe_ars_conds arss \<longleftrightarrow> alist_conds arss \<and> (\<forall>ars \<in> snd ` set arss . alist_conds ars)"

fun exe_ars_conds' :: "(('k1::linorder) \<times> (('k2::linorder) \<times> 's list) list) list \<Rightarrow> bool" where
  "exe_ars_conds' arss \<longleftrightarrow> alist_conds arss \<and> (\<forall>ars \<in> snd ` set arss . alist_conds ars)"

lemma [code]: "exe_ars_conds arss \<longleftrightarrow> exe_ars_conds' arss"
  by (simp add: exe_ars_conds_def)

definition exe_class_conds :: "(class \<times> class) list \<Rightarrow> bool" where
  "exe_class_conds cs \<equiv> distinct cs"

definition exe_osig_conds :: "exeosig \<Rightarrow> bool" where
  "exe_osig_conds a \<equiv> exe_class_conds (execlasses a) \<and> exe_ars_conds (exetcsigs a)"

fun translate_ars :: "(name \<times> (class \<times> sort list) list) list \<Rightarrow> name \<rightharpoonup> (class \<rightharpoonup> sort list)" where
  "translate_ars ars = map_of (map (apsnd map_of) ars)"

abbreviation "illformed_osig \<equiv> ({}, Map.empty(STR ''A'' \<mapsto> Map.empty(STR ''A'' \<mapsto> [{STR ''A''}])))"

lemma illformed_osig_not_wf_osig: "\<not> wf_osig illformed_osig"
  by (auto simp add: coregular_tcsigs_def complete_tcsigs_def consistent_length_tcsigs_def
      all_normalized_and_ex_tcsigs_def sort_ex_def wf_sort_def)

(* I should probably do this with an option return type instead... *)
fun translate_osig :: "exeosig \<Rightarrow> osig" where
  "translate_osig (cs, arss) = (if exe_osig_conds (cs, arss) 
    then (set cs, translate_ars arss)
    else illformed_osig)"

definition "exe_consistent_length_tcsigs arss \<equiv> (\<forall>ars \<in> snd ` set arss .
  \<forall>ss\<^sub>1 \<in> snd ` set ars. \<forall>ss\<^sub>2 \<in> snd ` set ars. length ss\<^sub>1 = length ss\<^sub>2)"

lemma in_alist_imp_in_map_of: "distinct (map fst arss) 
  \<Longrightarrow> (name, ars) \<in> set arss \<Longrightarrow> translate_ars arss name = Some (map_of ars)"
  by (induction arss) (auto simp add: rev_image_eqI)

lemma "exe_ars_conds arss \<Longrightarrow> \<exists>name . map_of (map (apsnd map_of) arss) name = Some ars
  \<Longrightarrow> \<exists>name arsl . (name, arsl) \<in> set arss \<and> map_of arsl = ars"
  by (force simp add: exe_ars_conds_def)

lemma "exe_ars_conds arss 
  \<Longrightarrow> (name, arsl) \<in> set arss \<and> map_of arsl = ars
  \<Longrightarrow> map_of (map (apsnd map_of) arss) name = Some ars"
  by (force simp add: exe_ars_conds_def)

lemma consistent_length_tcsigs_imp_exe_consistent_length_tcsigs: 
  "exe_ars_conds arss \<Longrightarrow> consistent_length_tcsigs (translate_ars arss) 
  \<Longrightarrow> exe_consistent_length_tcsigs arss"
  unfolding consistent_length_tcsigs_def exe_consistent_length_tcsigs_def 
  apply (clarsimp simp add: exe_ars_conds_def)
  by (metis in_alist_imp_in_map_of map_of_is_SomeI ranI snd_conv translate_ars.simps)

lemma exe_consistent_length_tcsigs_imp_consistent_length_tcsigs:
  assumes "exe_ars_conds arss" "exe_consistent_length_tcsigs arss" 
  shows "consistent_length_tcsigs (translate_ars arss)"
proof-
  {
    fix ars ss\<^sub>1 ss\<^sub>2
    assume p: "ars \<in> ran (map_of (map (apsnd map_of) arss))" "ss\<^sub>1 \<in> ran ars" "ss\<^sub>2 \<in> ran ars"
    from p(1) obtain name where "map_of (map (apsnd map_of) arss) name = Some ars"
      by (meson in_range_if_ex_key)
    from this obtain arsl where "(name, arsl) \<in> set arss" "map_of arsl = ars"
      using assms(1) by (auto simp add: exe_ars_conds_def)
    from this obtain c1 c2 where "ars c1 = Some ss\<^sub>1" "ars c2 = Some ss\<^sub>2"
      by (metis in_range_if_ex_key p(2) p(3))
    hence "(c1, ss\<^sub>1) \<in> set arsl" "(c2, ss\<^sub>2) \<in> set arsl"
      by (simp_all add: \<open>map_of arsl = ars\<close> map_of_SomeD)
    hence "length ss\<^sub>1 = length ss\<^sub>2"
      using assms(2) \<open>(name, arsl) \<in> set arss\<close> 
      by (fastforce simp add: exe_consistent_length_tcsigs_def)
  }
  note 1 = this
  show ?thesis 
    by (simp add: consistent_length_tcsigs_def exe_consistent_length_tcsigs_def) (use 1 in blast)
qed

lemma consistent_length_tcsigs_iff_exe_consistent_length_tcsigs: 
  "exe_ars_conds arss \<Longrightarrow> 
    consistent_length_tcsigs (translate_ars arss) \<longleftrightarrow> exe_consistent_length_tcsigs arss"
  using consistent_length_tcsigs_imp_exe_consistent_length_tcsigs 
    exe_consistent_length_tcsigs_imp_consistent_length_tcsigs by blast

(* Do I even have to translate the relation? *)
definition "exe_complete_tcsigs cs arss
 \<equiv> (\<forall>ars \<in> snd ` set arss . 
  \<forall>(c\<^sub>1, c\<^sub>2) \<in> set cs . c\<^sub>1\<in>fst ` set ars \<longrightarrow> c\<^sub>2\<in>fst ` set ars)"

lemma exe_complete_tcsigs_imp_complete_tcsigs: 
  assumes "exe_ars_conds arss" "exe_complete_tcsigs cs arss"
  shows "complete_tcsigs (set cs) (translate_ars arss)"
proof-
  {
    fix ars a b y 
    assume p: "ars \<in> ran (map_of (map (apsnd map_of) arss))"
       "(a, b) \<in> set cs" "ars a = Some y" 

    from p(1) obtain name where "map_of (map (apsnd map_of) arss) name = Some ars"
      by (meson in_range_if_ex_key)
    from this obtain arsl where "(name, arsl) \<in> set arss" "map_of arsl = ars"
      using assms(1) by (auto simp add: exe_ars_conds_def)
    hence "(a, y) \<in> set arsl" 
      by (simp add: map_of_SomeD p(3))
    hence"\<exists>y. ars b = Some y"
      using assms(2) \<open>(name, arsl) \<in> set arss\<close> 
      apply (clarsimp simp add: exe_complete_tcsigs_def)
      by (metis (no_types, lifting) \<open>map_of arsl = ars\<close> case_prodD domD domI dom_map_of_conv_image_fst
          p(2) p(3) snd_conv)
  }
  note 1 = this
  show ?thesis 
    by (simp add: complete_tcsigs_def exe_complete_tcsigs_def) (use 1 in blast)
qed

lemma complete_tcsigs_imp_exe_complete_tcsigs: "exe_ars_conds arss \<Longrightarrow> 
    complete_tcsigs (set cs) (translate_ars arss) \<Longrightarrow> exe_complete_tcsigs cs arss"
  unfolding complete_tcsigs_def exe_complete_tcsigs_def exe_ars_conds_def
  by (metis (mono_tags, lifting) case_prod_unfold dom_map_of_conv_image_fst in_alist_imp_in_map_of
      in_range_if_ex_key map_of_SomeD ran_distinct)

lemma exe_complete_tcsigs_iff_complete_tcsigs:
  "exe_ars_conds arss \<Longrightarrow> 
    complete_tcsigs (set cs) (translate_ars arss) \<longleftrightarrow> exe_complete_tcsigs cs arss"
  using exe_complete_tcsigs_imp_complete_tcsigs complete_tcsigs_imp_exe_complete_tcsigs
  by blast
  
definition "exe_coregular_tcsigs (cs :: (class \<times> class) list) arss
  \<equiv> (\<forall>ars \<in> snd ` set arss .
  \<forall>c\<^sub>1 \<in> fst ` set ars. \<forall>c\<^sub>2 \<in> fst ` set ars.
    (class_leq (set cs) c\<^sub>1 c\<^sub>2 \<longrightarrow> 
      list_all2 (sort_leq (set cs)) (the (lookup (\<lambda>x. x=c\<^sub>1) ars)) (the (lookup (\<lambda>x. x=c\<^sub>2) ars))))" 


lemma exe_coregular_tcsigs_imp_coregular_tcsigs: 
  assumes "exe_ars_conds arss" "exe_coregular_tcsigs cs arss"
  shows "coregular_tcsigs (set cs) (translate_ars arss)"
proof-
  {
    fix ars c\<^sub>1 c\<^sub>2 ss1 ss2
    assume p: "ars \<in> ran (map_of (map (apsnd map_of) arss))" "ars c\<^sub>1 = Some ss1" "ars c\<^sub>2 = Some ss2"
      "class_leq (set cs) c\<^sub>1 c\<^sub>2" 
    from p(1) obtain name where "map_of (map (apsnd map_of) arss) name = Some ars"
      by (meson in_range_if_ex_key)
    from this obtain arsl where "(name, arsl) \<in> set arss" "map_of arsl = ars"
      using assms(1) by (auto simp add: exe_ars_conds_def)
    from this obtain c1 c2 where "ars c1 = Some ss1" "ars c2 = Some ss2" "class_leq (set cs) c1 c2"
      using p(2) p(3) p(4) by blast
    hence "(c1, ss1) \<in> set arsl" "(c2, ss2) \<in> set arsl"
      by (simp_all add: \<open>map_of arsl = ars\<close> map_of_SomeD)
    hence "lookup (\<lambda>x. x=c1) arsl = Some ss1" "lookup (\<lambda>x. x=c2) arsl = Some ss2"
      by (metis \<open>(name, arsl) \<in> set arss\<close> assms(1) exe_ars_conds_def 
          image_eqI lookup_present_eq_key snd_conv)+
    hence "list_all2 (sort_leq (set cs)) ss1 ss2"
      using assms(2) \<open>(name, arsl) \<in> set arss\<close> \<open>(c1, ss1) \<in> set arsl\<close> \<open>(c2, ss2) \<in> set arsl\<close> 
        \<open>class_leq (set cs) c1 c2\<close>
      by (fastforce simp add: exe_coregular_tcsigs_def)  
  }
  note 1 = this
  show ?thesis 
    by (auto simp add: coregular_tcsigs_def exe_coregular_tcsigs_def) (use 1 in blast)

qed

lemma coregular_tcsigs_imp_exe_coregular_tcsigs: 
  assumes "exe_ars_conds arss" "coregular_tcsigs (set cs) (translate_ars arss)"
  shows "exe_coregular_tcsigs cs arss"
proof-
  {
    fix name ars c1 ss1 c2 ss2 
    assume p: "(name, ars) \<in> set arss" "(c1, ss1) \<in> set ars" "(c2, ss2) \<in> set ars" 
      "class_leq (set cs) c1 c2"

    have s1: "(lookup (\<lambda>x. x = c1) ars) = Some ss1"
      using assms(1) lookup_present_eq_key p(1) p(2) by (force simp add: exe_ars_conds_def)
    have s2: "(lookup (\<lambda>x. x = c2) ars) = Some ss2"
      using assms(1) lookup_present_eq_key p(1) p(3) by (force simp add: exe_ars_conds_def)
    have "list_all2 (sort_leq (set cs)) (the (lookup (\<lambda>x. x = c1) ars)) (the (lookup (\<lambda>x. x = c2) ars))"
      using assms apply (simp add: coregular_tcsigs_def s1 s2 exe_ars_conds_def)
      by (metis domIff in_alist_imp_in_map_of map_of_is_SomeI option.distinct(1) option.sel 
          p(1) p(2) p(3) p(4) ranI snd_conv translate_ars.simps)
  }
  note 1 = this
  show ?thesis 
    by (auto simp add: coregular_tcsigs_def exe_coregular_tcsigs_def) (use 1 in blast)
qed

lemma coregular_tcsigs_iff_exe_coregular_tcsigs: 
  "exe_ars_conds arss \<Longrightarrow> coregular_tcsigs (set cs) (translate_ars arss) \<longleftrightarrow> exe_coregular_tcsigs cs arss"
  using coregular_tcsigs_imp_exe_coregular_tcsigs exe_coregular_tcsigs_imp_coregular_tcsigs by blast

lemma "wf_subclass sub \<Longrightarrow> Field sub = Domain sub"
  using refl_on_def by fastforce

definition [simp]: "exefield rel = List.union (map fst rel) (map snd rel)"
lemma Field_set_code: "Field (set rel) = set (exefield rel)"
  by (induction rel) fastforce+

lemma class_ex_rec: "finite r \<Longrightarrow> class_ex (insert (a,b) r) c = (a=c \<or> b=c \<or> class_ex r c)"
  by (induction r rule: finite_induct) (auto simp add: class_ex_def)

definition [simp]: "execlass_ex rel c = List.member (exefield rel) c"
lemma execlass_ex_code: "class_ex (set rel) c = execlass_ex rel c"
  by (metis Field_set_code class_ex_def execlass_ex_def in_set_member)

definition [simp]: "exesort_ex rel S = (\<forall>x\<in>S . (List.member (exefield rel) x))"
lemma sort_ex_code: "sort_ex (set rel) S = exesort_ex rel S"
  by (simp add: execlass_ex_code sort_ex_class_ex)

definition [simp]: "execlass_les cs c1 c2 = (List.member cs (c1,c2) \<and> \<not> List.member cs (c2,c1))"
lemma execlass_les_code: "class_les (set cs) c1 c2 = execlass_les cs c1 c2"
  by (simp add: class_leq_def class_les_def member_def)

definition [simp]: "exenormalize_sort cs (s::sort)
  = {c \<in> s . \<not> (\<exists>c' \<in> s . execlass_les cs c' c)}"
definition [simp]: "exenormalized_sort cs s \<equiv> (exenormalize_sort cs s) = s"

lemma normalize_sort_code[code]: "normalize_sort (set cs) s = exenormalize_sort cs s"
  by (auto simp add: normalize_sort_def List.member_def list_ex_iff class_leq_def class_les_def)

lemma normalized_sort_code[code]: "normalized_sort (set cs) s = exenormalized_sort cs s"
  using exenormalized_sort_def normalize_sort_code by presburger

definition [simp]: "exewf_sort sub S \<equiv> exenormalized_sort sub S \<and> exesort_ex sub S"
lemma wf_sort_code:
  assumes "exe_class_conds sub"
  shows "wf_sort (set sub) S = exewf_sort sub S"
  using normalized_sort_code sort_ex_code assms
  by (simp add: sort_ex_code wf_sort_def)

declare exewf_sort_def[code del]
lemma [code]: "exewf_sort sub S \<equiv> (S = {} \<or> exenormalized_sort sub S \<and> exesort_ex sub S)"
  by simp (smt ball_empty bot_set_def empty_Collect_eq)

definition "exe_all_normalized_and_ex_tcsigs cs arss
 \<equiv> (\<forall>ars \<in> snd ` set arss . \<forall>ss \<in> snd ` set ars . \<forall>s \<in> set ss. exewf_sort cs s)"

lemma all_normalized_and_ex_tcsigs_imp_exe_all_normalized_and_ex_tcsigs:
  assumes "exe_ars_conds arss" "all_normalized_and_ex_tcsigs (set cs) (translate_ars arss)" 
  shows "exe_all_normalized_and_ex_tcsigs cs arss"
proof-
  have ac: "alist_conds arss"
    using assms(1) exe_ars_conds_def by blast
  {
    fix s ars
    assume a1: "(s, ars) \<in> set arss"
    fix c Ss
    assume a2: "(c,Ss) \<in> set ars"
    fix S
    assume a3: "S \<in> set Ss"

    have "map_of ars \<in> ran (map_of (map (apsnd map_of) arss))"
      using ac a1 by (metis  in_alist_imp_in_map_of ranI translate_ars.simps)
    moreover have "Ss \<in> ran (map_of ars)"
      using a1 a2 assms(1) by (metis exe_ars_conds_def map_of_is_SomeI ranI ran_distinct)
    ultimately have "wf_sort (set cs) S"
      using assms(2) a1 a2 a3 by (auto simp add: all_normalized_and_ex_tcsigs_def )
  }
  thus ?thesis 
    using normalize_sort_code wf_sort_def
    by (clarsimp simp add: all_normalized_and_ex_tcsigs_def exe_all_normalized_and_ex_tcsigs_def
      exe_ars_conds_def wf_sort_def wf_sort_code normalize_sort_def sort_ex_code) 
qed
  
lemma exe_all_normalized_and_ex_tcsigs_imp_all_normalized_and_ex_tcsigs: 
  assumes "exe_ars_conds arss" "exe_all_normalized_and_ex_tcsigs cs arss"
  shows "all_normalized_and_ex_tcsigs (set cs) (translate_ars arss)"
proof-
  {
    fix ars ss s
    assume p: "ars \<in> ran (map_of (map (apsnd map_of) arss))"
      "ss \<in> ran ars" "s \<in> set ss"

    from p(1) obtain name where "map_of (map (apsnd map_of) arss) name = Some ars"
      by (meson in_range_if_ex_key)
    from this obtain arsl where "(name, arsl) \<in> set arss" "map_of arsl = ars"
      using assms(1) by (auto simp add: exe_ars_conds_def)
    from this obtain c where c: "ars c = Some ss"
      using in_range_if_ex_key p(2) by force
    have "exewf_sort cs s"
      by (metis (no_types, hide_lams) \<open>(name, arsl) \<in> set arss\<close> \<open>map_of arsl = ars\<close> assms(1) assms(2) 
          exe_all_normalized_and_ex_tcsigs_def exe_ars_conds_def image_iff p(2) p(3) ran_distinct snd_conv)
    hence "wf_sort (set cs) s"
      by (simp add: normalize_sort_code sort_ex_code wf_sort_def)
  }
  note 1 = this
  show ?thesis 
    using 1 by (clarsimp simp add: wf_sort_def all_normalized_and_ex_tcsigs_def
        exe_all_normalized_and_ex_tcsigs_def)
qed

lemma all_normalized_and_ex_tcsigs_iff_exe_all_normalized_and_ex_tcsigs:
  "exe_ars_conds arss \<Longrightarrow> all_normalized_and_ex_tcsigs (set cs) (translate_ars arss) 
    \<longleftrightarrow> exe_all_normalized_and_ex_tcsigs cs arss"
  using all_normalized_and_ex_tcsigs_imp_exe_all_normalized_and_ex_tcsigs exe_all_normalized_and_ex_tcsigs_imp_all_normalized_and_ex_tcsigs by blast

definition [simp]: "exe_wf_tcsigs (cs :: (class \<times> class) list) arss \<equiv> 
    exe_coregular_tcsigs cs arss 
  \<and> exe_complete_tcsigs cs arss
  \<and> exe_consistent_length_tcsigs arss
  \<and> exe_all_normalized_and_ex_tcsigs cs arss"

lemma wf_tcsigs_iff_exe_wf_tcsigs:
  "exe_ars_conds arss \<Longrightarrow> wf_tcsigs (set cs) (translate_ars arss) \<longleftrightarrow> exe_wf_tcsigs cs arss"
  using all_normalized_and_ex_tcsigs_iff_exe_all_normalized_and_ex_tcsigs 
    consistent_length_tcsigs_imp_exe_consistent_length_tcsigs 
    coregular_tcsigs_iff_exe_coregular_tcsigs exe_complete_tcsigs_iff_complete_tcsigs 
    exe_consistent_length_tcsigs_imp_consistent_length_tcsigs exe_wf_tcsigs_def wf_tcsigs_def 
  by blast

fun exe_antisym :: "('a \<times> 'a) list \<Rightarrow> bool" where
  "exe_antisym [] \<longleftrightarrow> True"
| "exe_antisym ((x,y)#r) \<longleftrightarrow> ((y,x)\<in>set r \<longrightarrow> x=y) \<and> exe_antisym r"

lemma exe_antisym_imp_antisym: "exe_antisym l \<Longrightarrow> antisym (set l)"
  by (induction l) (auto simp add: antisym_def)

lemma antisym_imp_exe_antisym: "antisym (set l) \<Longrightarrow> exe_antisym l"
proof (induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by (simp add: antisym_def) (metis exe_antisym.simps(2) surj_pair)
qed

lemma antisym_iff_exe_antisym: "antisym (set l) = exe_antisym l"
  using antisym_imp_exe_antisym exe_antisym_imp_antisym by blast

definition "exe_wf_subclass cs = (trans (set cs) \<and> exe_antisym cs \<and> Refl (set cs))"

lemma wf_classes_iff_exe_wf_classes: "wf_subclass (set cs) \<longleftrightarrow> exe_wf_subclass cs"
  by (simp add: antisym_iff_exe_antisym exe_wf_subclass_def)

definition [simp]: "exe_wf_osig oss \<equiv> exe_wf_subclass (execlasses oss)
  \<and> exe_wf_tcsigs (execlasses oss) (exetcsigs oss) \<and> exe_osig_conds oss"

lemma exe_wf_osig_imp_wf_osig: "exe_wf_osig oss \<Longrightarrow> wf_osig (translate_osig oss)"
  using exe_coregular_tcsigs_imp_coregular_tcsigs exe_complete_tcsigs_imp_complete_tcsigs
    exe_complete_tcsigs_imp_complete_tcsigs exe_all_normalized_and_ex_tcsigs_imp_all_normalized_and_ex_tcsigs
    exe_consistent_length_tcsigs_imp_consistent_length_tcsigs 
  by (cases oss) (auto simp add: exe_wf_subclass_def exe_antisym_imp_antisym  exe_osig_conds_def)

lemma classes_translate: "exe_osig_conds oss \<Longrightarrow> subclass (translate_osig oss) = set (execlasses oss)"
  by (cases oss) simp_all

lemma tcsigs_translate: "exe_osig_conds oss
  \<Longrightarrow> tcsigs (translate_osig oss) = translate_ars (exetcsigs oss)"
  by (cases oss) simp_all

lemma wf_osig_translate_imp_exe_osig_conds:
  "wf_osig (translate_osig oss) \<Longrightarrow> exe_osig_conds oss" 
  using illformed_osig_not_wf_osig by (metis translate_osig.elims)

lemma wf_osig_imp_exe_wf_osig:
  assumes "wf_osig (translate_osig oss)" shows "exe_wf_osig oss"
  apply (cases "translate_osig oss")
  using classes_translate tcsigs_translate assms wf_osig_translate_imp_exe_osig_conds 
  by (metis (full_types) exe_osig_conds_def exe_wf_osig_def subclass.simps tcsigs.simps
      wf_classes_iff_exe_wf_classes wf_osig.simps wf_tcsigs_iff_exe_wf_tcsigs)

lemma wf_osig_iff_exe_wf_osig: "wf_osig (translate_osig oss) \<longleftrightarrow> exe_wf_osig oss"
  using exe_wf_osig_imp_wf_osig wf_osig_imp_exe_wf_osig by blast

end