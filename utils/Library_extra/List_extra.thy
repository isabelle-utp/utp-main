theory List_extra
imports 
  Main
  "~~/src/HOL/Library/Sublist"
  "~~/src/HOL/Library/Monad_Syntax"
begin

subsection {* Extra list functions *}

text {*
The following variant of the standard @{text nth} function returns
@{text "\<bottom>"} if the index is out of range.
*}

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" ("_\<langle>_\<rangle>\<^sub>l" [90, 0] 91)
where
  "[]\<langle>i\<rangle>\<^sub>l = None"
| "(x # xs)\<langle>i\<rangle>\<^sub>l = (case i of 0 \<Rightarrow> Some x | Suc j \<Rightarrow> xs \<langle>j\<rangle>\<^sub>l)"

fun sequence :: "'a option list \<Rightarrow> 'a list option" where
"sequence [] = Some []" |
"sequence (f # fs) = do { x \<leftarrow> f; xs \<leftarrow> sequence fs; Some (x # xs) }"

abbreviation "mapM f \<equiv> sequence \<circ> map f"

subsection {* List lemmas *}

lemma nth_el_appendl[simp]: "i < length xs \<Longrightarrow> (xs @ ys)\<langle>i\<rangle>\<^sub>l = xs\<langle>i\<rangle>\<^sub>l"
  apply (induct xs arbitrary: i)
  apply simp
  apply (case_tac i)
  apply simp_all
done

lemma nth_el_appendr[simp]: "length xs \<le> i \<Longrightarrow> (xs @ ys)\<langle>i\<rangle>\<^sub>l = ys\<langle>i - length xs\<rangle>\<^sub>l"
  apply (induct xs arbitrary: i)
  apply simp
  apply (case_tac i)
  apply simp_all
done

lemma sorted_last [simp]: "\<lbrakk> x \<in> set xs; sorted xs \<rbrakk> \<Longrightarrow> x \<le> last xs"
  apply (induct xs)
  apply (auto)
  apply (metis last_in_set sorted_Cons)+
done

lemma prefix_length_eq:
  "\<lbrakk> length xs = length ys; prefixeq xs ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (metis not_equal_is_parallel parallel_def)

lemma prefixeq_Cons_elim [elim]:
  assumes "prefixeq (x # xs) ys"
  obtains ys' where "ys = x # ys'" "prefixeq xs ys'"
  using assms by (auto elim!: prefixeqE)

lemma prefixeq_map_inj:
  "\<lbrakk> inj_on f (set xs \<union> set ys); prefixeq (map f xs) (map f ys) \<rbrakk> \<Longrightarrow>
   prefixeq xs ys"
  apply (induct xs arbitrary:ys)
  apply (simp_all)
  apply (erule prefixeq_Cons_elim)
  apply (auto)
  apply (metis image_insert insertI1 insert_Diff_if singletonE)
done

lemma prefixeq_map_inj_eq [simp]:
  "inj_on f (set xs \<union> set ys) \<Longrightarrow>
   prefixeq (map f xs) (map f ys) \<longleftrightarrow> prefixeq xs ys"
  by (metis map_prefixeqI prefixeq_map_inj)

lemma prefix_Cons_elim [elim]:
  assumes "prefix (x # xs) ys"
  obtains ys' where "ys = x # ys'" "prefix xs ys'"
  using assms 
  apply (auto elim!: prefixE)
  apply (metis (full_types) prefix_order.le_less prefixeq_Cons_elim)
done

lemma prefix_map_inj:
  "\<lbrakk> inj_on f (set xs \<union> set ys); prefix (map f xs) (map f ys) \<rbrakk> \<Longrightarrow>
   prefix xs ys"
  apply (induct xs arbitrary:ys)
  apply (auto)
  using prefix_bot.bot.not_eq_extremum apply fastforce
  apply (erule prefix_Cons_elim)
  apply (auto)
  apply (metis (hide_lams, full_types) image_insert insertI1 insert_Diff_if singletonE)
done

lemma prefix_map_inj_eq [simp]:
  "inj_on f (set xs \<union> set ys) \<Longrightarrow>
   prefix (map f xs) (map f ys) \<longleftrightarrow> prefix xs ys"
  by (metis inj_on_map_eq_map map_prefixeqI prefix_map_inj prefix_order.less_le)

lemma prefixeq_drop:
  "\<lbrakk> drop (length xs) ys = zs; prefixeq xs ys \<rbrakk> 
   \<Longrightarrow> ys = xs @ zs"
  by (metis append_eq_conv_conj prefixeq_def)

subsection {* Minus on lists *}

instantiation list :: (type) minus
begin

definition "xs - ys = (if (prefixeq ys xs) then drop (length ys) xs else undefined)"

instance ..
end

lemma minus_cancel [simp]: "xs - xs = []"
  by (simp add: minus_list_def)

lemma append_minus [simp]: "(xs @ ys) - xs = ys"
  by (simp add: minus_list_def)

lemma minus_right_nil [simp]: "xs - [] = xs"
  by (simp add: minus_list_def)

subsection {* Interleaving operations *}

fun interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
"interleave [] ys = {ys}" |
"interleave (x # xs) (y # ys) = (Cons x) ` (interleave xs (y # ys)) 
                              \<union> (Cons y) ` (interleave (x # xs) ys)" |
"interleave xs [] = {xs}"

lemma interleave_finite [simp]:
  "finite (interleave xs ys)"
  apply (induct xs arbitrary: ys)
  apply (simp)
  apply (induct_tac ys)
  apply (auto)
done

lemma interleave_right_nil [simp]:
  "interleave xs [] = {xs}"
  by (induct xs, auto)

lemma interleave_headE [elim!]:
  "\<lbrakk> z # zs \<in> interleave xs ys
   ; \<And> xs'. xs = z # xs' \<Longrightarrow> P
   ; \<And> ys'. ys = z # ys' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (induct xs)
  apply (auto)
  apply (induct ys)
  apply (auto)
done

lemma interleave_member:
  "\<lbrakk> zs \<in> interleave xs ys; z \<in> set zs \<rbrakk> \<Longrightarrow> z \<in> set xs \<or> z \<in> set ys"
  apply (induct xs arbitrary: zs)
  apply (auto)
  apply (induct ys)
  apply (auto)
oops

(* FIXME: What happens if no progress can be made? *)
fun intersync :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
"intersync s (x # xs) (y # ys) 
  = (case (x = y , x \<in> s , y \<in> s) of
          (True  , True   , _      ) \<Rightarrow> Cons x ` intersync s xs ys |
          (True  , False  , _      ) \<Rightarrow> ((Cons x ` intersync s xs (y # ys))
                                         \<union> (Cons y ` intersync s (x # xs) ys)) |
          (False , True   , True   ) \<Rightarrow> {[]} |
          (False , True   , False  ) \<Rightarrow> Cons y ` intersync s (x # xs) ys |
          (False , False  , True   ) \<Rightarrow> Cons x ` intersync s xs (y # ys) |
          (False , False  , False  ) \<Rightarrow> ((Cons x ` intersync s xs (y # ys))
                                         \<union> (Cons y ` intersync s (x # xs) ys)))" |
"intersync s [] (y # ys) = 
   (if (y \<in> s) then {[]} else Cons y ` intersync s [] ys)" |
"intersync s (x # xs) [] = 
   (if (x \<in> s) then {[]} else Cons x ` intersync s xs [])" |
"intersync s [] [] = {[]}"

(* FIXME: We should be able to prove this property... *)
lemma intersync_empty_interleave:
  "intersync {} xs ys = interleave xs ys"
  apply (induct xs)
  apply (simp_all)
  apply (induct ys)
  apply (simp_all)
  apply (induct ys arbitrary: a xs)
  apply (simp_all)
  apply (case_tac "aa = a")
  apply (simp_all)
oops

subsection {* Sorting of lists *}

definition is_sorted_list_of_set :: "('a::ord) set \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sorted_list_of_set A xs = ((\<forall> i<length(xs) - 1. xs!i < xs!(i + 1)) \<and> set(xs) = A)"

lemma sorted_distinct [intro]: "\<lbrakk> sorted (xs); distinct(xs) \<rbrakk> \<Longrightarrow> (\<forall> i<length xs - 1. xs!i < xs!(i + 1))"
  apply (induct xs)
  apply (auto)
  apply (smt Suc_lessI diff_le_self distinct.simps(2) le_neq_trans length_Cons lessI less_SucI list.sel(3) nat_neq_iff nth_Cons' nth_eq_iff_index_eq nth_mem nth_tl sorted_equals_nth_mono)
done 

lemma sorted_is_sorted_list_of_set: 
  assumes "is_sorted_list_of_set A xs"
  shows "sorted(xs)" and "distinct(xs)"
using assms proof (induct xs arbitrary: A)
  show "sorted []"
    by auto
next
  show "distinct []"
    by auto
next
  fix A :: "'a set"
  case (Cons x xs) note hyps = this
  assume isl: "is_sorted_list_of_set A (x # xs)"
  hence srt: "(\<forall>i<length xs - Suc 0. xs ! i < xs ! Suc i)"
    using less_diff_conv by (auto simp add: is_sorted_list_of_set_def)
  with hyps(1) have srtd: "sorted xs"
    by (simp add: is_sorted_list_of_set_def)
  with isl show "sorted (x # xs)"
    apply (auto simp add: is_sorted_list_of_set_def)
    apply (metis length_pos_if_in_set less_imp_le nth_Cons_0 sorted.simps sorted_many sorted_single)
  done
  from srt hyps(2) have "distinct xs"
    by (simp add: is_sorted_list_of_set_def)
  with isl show "distinct (x # xs)"
    by (smt One_nat_def `sorted (x # xs)` antisym diff_Suc_1 distinct.simps(2) distinct_singleton is_sorted_list_of_set_def length_Cons length_pos_if_in_set list.sel(3) list.size(3) list.size(4) not_less_iff_gr_or_eq nth_Cons_0 nth_tl set_ConsD sorted.simps sorted_many_eq)
qed

lemma is_sorted_list_of_set_alt_def:
  "is_sorted_list_of_set A xs \<longleftrightarrow> sorted (xs) \<and> distinct (xs) \<and> set(xs) = A"
  apply (auto intro: sorted_is_sorted_list_of_set)
  apply (auto simp add: is_sorted_list_of_set_def)
  apply (metis Nat.add_0_right One_nat_def add_Suc_right sorted_distinct)
done

(*
lemma sorted_alt_def:
  "(\<forall> i<(length xs) - 1. xs!i < xs!(i + 1)) \<longleftrightarrow> sorted (xs) \<and> distinct (xs)"
  apply (auto)
  sledgehammer
oops
*)

definition sorted_list_of_set_alt :: "('a::ord) set \<Rightarrow> 'a list" where
"sorted_list_of_set_alt A = 
  (if (A = {}) then [] else (THE xs. is_sorted_list_of_set A xs))"

lemma is_sorted_list_of_set: 
  "finite A \<Longrightarrow> is_sorted_list_of_set A (sorted_list_of_set A)"
  apply (simp add: is_sorted_list_of_set_def)
  apply (smt Suc_pred card_length le_less_trans less_imp_diff_less linorder_not_less not_less_eq not_less_iff_gr_or_eq nth_eq_iff_index_eq sorted_list_of_set sorted_nth_mono zero_less_Suc)
done

lemma sorted_list_of_set_other_def:
  "finite A \<Longrightarrow> sorted_list_of_set(A) = (THE xs. sorted(xs) \<and> distinct(xs) \<and> set xs = A)"
  apply (rule sym)
  apply (rule the_equality)
  apply (auto)
  apply (simp add: sorted_distinct_set_unique)
done

lemma sorted_list_of_set_alt [simp]:
  "finite A \<Longrightarrow> sorted_list_of_set_alt(A) = sorted_list_of_set(A)"
  apply (rule sym)
  apply (auto simp add: sorted_list_of_set_alt_def is_sorted_list_of_set_alt_def sorted_list_of_set_other_def)
done


text {* Greatest common prefix *}

fun gcp :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"gcp [] ys = []" |
"gcp (x # xs) (y # ys) = (if (x = y) then x # gcp xs ys else [])" |
"gcp _ _ = []"

lemma gcp_right [simp]: "gcp xs [] = []"
  by (induct xs, auto)

lemma gcp_append [simp]: "gcp (xs @ ys) (xs @ zs) = xs @ gcp ys zs"
  by (induct xs, auto)
  
lemma gcp_lb1: "prefixeq (gcp xs ys) xs"
  apply (induct xs arbitrary: ys, auto)
  apply (case_tac ys, auto)
done

lemma gcp_lb2: "prefixeq (gcp xs ys) ys"
  apply (induct ys arbitrary: xs, auto)
  apply (case_tac xs, auto)
done

interpretation prefix_semilattice: semilattice_inf gcp prefixeq prefix
proof
  fix xs ys :: "'a list"
  show "prefixeq (gcp xs ys) xs"
    by (induct xs arbitrary: ys, auto, case_tac ys, auto)
  show "prefixeq (gcp xs ys) ys"
    by (induct ys arbitrary: xs, auto, case_tac xs, auto)
next
  fix xs ys zs :: "'a list"
  assume "prefixeq xs ys" "prefixeq xs zs"
  thus "prefixeq xs (gcp ys zs)"
    by (simp add: prefixeq_def, auto)
qed

text {* Extra laws to do with prefix and order *}

lemma lexord_append:
  assumes "(xs\<^sub>1 @ ys\<^sub>1, xs\<^sub>2 @ ys\<^sub>2) \<in> lexord R" "length(xs\<^sub>1) = length(xs\<^sub>2)"
  shows "(xs\<^sub>1, xs\<^sub>2) \<in> lexord R \<or> (xs\<^sub>1 = xs\<^sub>2 \<and> (ys\<^sub>1, ys\<^sub>2) \<in> lexord R)"
using assms 
proof (induct xs\<^sub>2 arbitrary: xs\<^sub>1)
  case (Cons x\<^sub>2 xs\<^sub>2') note hyps = this
  from hyps(3) obtain x\<^sub>1 xs\<^sub>1' where xs\<^sub>1: "xs\<^sub>1 = x\<^sub>1 # xs\<^sub>1'" "length(xs\<^sub>1') = length(xs\<^sub>2')" 
    by (auto, metis Suc_length_conv)
  with hyps(2) have xcases: "(x\<^sub>1, x\<^sub>2) \<in> R \<or> (xs\<^sub>1' @ ys\<^sub>1, xs\<^sub>2' @ ys\<^sub>2) \<in> lexord R"
    by (auto)
  show ?case
  proof (cases "(x\<^sub>1, x\<^sub>2) \<in> R")
    case True with xs\<^sub>1 show ?thesis
      by (auto)
  next
    case False
    with xcases have "(xs\<^sub>1' @ ys\<^sub>1, xs\<^sub>2' @ ys\<^sub>2) \<in> lexord R"
      by (auto)
    with hyps(1) xs\<^sub>1 have dichot: "(xs\<^sub>1', xs\<^sub>2') \<in> lexord R \<or> (xs\<^sub>1' = xs\<^sub>2' \<and> (ys\<^sub>1, ys\<^sub>2) \<in> lexord R)"
      by (auto)
    have "x\<^sub>1 = x\<^sub>2"
      using False hyps(2) xs\<^sub>1(1) by auto
    with dichot xs\<^sub>1 show ?thesis
      by (simp)
  qed
next
  case Nil thus ?case
    by auto
qed

lemma prefix_lexord_rel:
  "prefix xs ys \<Longrightarrow> (xs, ys) \<in> lexord R"
  by (metis lexord_append_rightI prefixE')

lemma prefix_lexord_left:
  assumes "trans R" "(xs, ys) \<in> lexord R" "prefixeq xs' xs"
  shows "(xs', ys) \<in> lexord R"
  by (metis assms lexord_trans prefix_def prefix_lexord_rel)

lemma prefix_lexord_right:
  assumes "trans R" "(xs, ys) \<in> lexord R" "prefixeq ys ys'"
  shows "(xs, ys') \<in> lexord R"
  by (metis assms lexord_trans prefix_def prefix_lexord_rel)

lemma lexord_eq_length:
  assumes "(xs, ys) \<in> lexord R" "length xs = length ys"
  shows "\<exists> i. (xs!i, ys!i) \<in> R \<and> i < length xs \<and> (\<forall> j<i. xs!j = ys!j)"
using assms proof (induct xs arbitrary: ys)
  case (Cons x xs) note hyps = this
  then obtain y ys' where ys: "ys = y # ys'" "length ys' = length xs"
    by (metis Suc_length_conv)
  show ?case
  proof (cases "(x, y) \<in> R")
    case True with ys show ?thesis
      by (rule_tac x="0" in exI, simp)
  next
    case False
    with ys hyps(2) have xy: "x = y" "(xs, ys') \<in> lexord R"
      by auto
    with hyps(1,3) ys obtain i where "(xs!i, ys'!i) \<in> R" "i < length xs" "(\<forall> j<i. xs!j = ys'!j)"
      by force
    with xy ys show ?thesis
      apply (rule_tac x="Suc i" in exI)
      apply (auto simp add: less_Suc_eq_0_disj)
    done
  qed
next
  case Nil thus ?case by (auto)
qed

lemma lexord_intro_elems:
  assumes "length xs > i" "length ys > i" "(xs!i, ys!i) \<in> R" "\<forall> j<i. xs!j = ys!j"
  shows "(xs, ys) \<in> lexord R"
using assms proof (induct i arbitrary: xs ys)
  case 0 thus ?case
    by (auto, metis lexord_cons_cons list.exhaust nth_Cons_0)
next
  case (Suc i) note hyps = this
  then obtain x' y' xs' ys' where "xs = x' # xs'" "ys = y' # ys'"
    by (metis Suc_length_conv Suc_lessE)
  moreover with hyps(5) have "\<forall>j<i. xs' ! j = ys' ! j"
    by (auto)
  ultimately show ?case using hyps
    by (auto)
qed

lemma prefixeq_consE [elim]:
  "\<lbrakk> prefixeq (x # xs) ys; \<And> ys'. \<lbrakk> ys = x # ys'; prefixeq xs ys' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis Cons_prefixeq_Cons Nil_prefixeq list.exhaust prefix_order.eq_iff)

lemma prefix_consE [elim]:
  "\<lbrakk> prefix (x # xs) ys; \<And> ys'. \<lbrakk> ys = x # ys'; prefix xs ys' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis neq_Nil_conv prefix_order.dual_order.strict_trans prefix_order.less_irrefl prefix_simps(2) prefix_simps(3))

text {* Sorting lists according to a relation *}

definition is_sorted_list_of_set_by :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sorted_list_of_set_by R A xs = ((\<forall> i<length(xs) - 1. (xs!i, xs!(i + 1)) \<in> R) \<and> set(xs) = A)"

definition sorted_list_of_set_by :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a list" where
"sorted_list_of_set_by R A = (THE xs. is_sorted_list_of_set_by R A xs)"

definition fin_set_lexord :: "'a rel \<Rightarrow> 'a set rel" where
"fin_set_lexord R = {(A, B). finite A \<and> finite B \<and> 
                             (\<exists> xs ys. is_sorted_list_of_set_by R A xs \<and> is_sorted_list_of_set_by R B ys 
                              \<and> (xs, ys) \<in> lexord R)}"

lemma is_sorted_list_of_set_by_mono:
  "\<lbrakk> R \<subseteq> S; is_sorted_list_of_set_by R A xs \<rbrakk> \<Longrightarrow> is_sorted_list_of_set_by S A xs"
  by (auto simp add: is_sorted_list_of_set_by_def)

lemma lexord_mono': 
  "\<lbrakk> (\<And> x y. f x y \<longrightarrow> g x y); (xs, ys) \<in> lexord {(x, y). f x y} \<rbrakk> \<Longrightarrow> (xs, ys) \<in> lexord {(x, y). g x y}"
  by (metis case_prodI lexord_take_index_conv mem_Collect_eq splitD)


lemma fin_set_lexord_mono [mono]: 
  "(\<And> x y. f x y \<longrightarrow> g x y) \<Longrightarrow> (xs, ys) \<in> fin_set_lexord {(x, y). f x y} \<longrightarrow> (xs, ys) \<in> fin_set_lexord {(x, y). g x y}"
proof
  assume 
    fin: "(xs, ys) \<in> fin_set_lexord {(x, y). f x y}" and
    hyp: "(\<And> x y. f x y \<longrightarrow> g x y)"

  from fin have "finite xs" "finite ys"
    using fin_set_lexord_def by fastforce+

  with fin hyp show "(xs, ys) \<in> fin_set_lexord {(x, y). g x y}"
    apply (auto simp add: fin_set_lexord_def)
    apply (rule_tac x="xsa" in exI)
    apply (auto)
    apply (metis case_prodI is_sorted_list_of_set_by_def mem_Collect_eq splitD)
    apply (rule_tac x="ysa" in exI)
    apply (auto)
    apply (metis case_prodI is_sorted_list_of_set_by_def mem_Collect_eq splitD)
    using lexord_mono' apply blast
  done
qed

definition distincts :: "'a set \<Rightarrow> 'a list set" where
"distincts A = {xs \<in> lists A. distinct(xs)}"

lemma tl_element:
  "\<lbrakk> x \<in> set xs; x \<noteq> hd(xs) \<rbrakk> \<Longrightarrow> x \<in> set(tl(xs))"
  by (metis in_set_insert insert_Nil list.collapse list.distinct(2) set_ConsD)

subsection {* Z mathematical tool kit for sequences *}

abbreviation seq_dom :: "'a list \<Rightarrow> nat set" ("dom\<^sub>l") where
"seq_dom xs \<equiv> {0..<length xs}"

abbreviation seq_ran :: "'a list \<Rightarrow> 'a set" ("ran\<^sub>l") where
"seq_ran xs \<equiv> set xs"

definition seq_extract :: "nat set \<Rightarrow> 'a list \<Rightarrow> 'a list" (infix "\<upharpoonleft>\<^sub>l" 80) where
"seq_extract A xs = sublist xs A"

lemma seq_extract_Nil [simp]: "A \<upharpoonleft>\<^sub>l [] = []"
  by (simp add: seq_extract_def)

lemma seq_extract_Cons: 
  "A \<upharpoonleft>\<^sub>l (x # xs) = (if 0 \<in> A then [x] else []) @ {j. Suc j \<in> A} \<upharpoonleft>\<^sub>l xs"
  by (simp add: seq_extract_def sublist_Cons)

lemma seq_extract_empty [simp]: "{} \<upharpoonleft>\<^sub>l xs = []"
  by (simp add: seq_extract_def) 

lemma seq_extract_ident [simp]: "{0..<length xs} \<upharpoonleft>\<^sub>l xs = xs"
  unfolding list_eq_iff_nth_eq
  by (auto simp add: seq_extract_def length_sublist atLeast0LessThan)

lemma seq_extract_split:
  assumes "i \<le> length xs"
  shows "{0..<i} \<upharpoonleft>\<^sub>l xs @ {i..<length xs} \<upharpoonleft>\<^sub>l xs = xs"
using assms
proof (induct xs arbitrary: i)
  case Nil thus ?case by (simp add: seq_extract_def)
next
  case (Cons x xs) note hyp = this
  have "{j. Suc j < i} = {0..<i - 1}"
    by (auto)
  moreover have "{j. i \<le> Suc j \<and> j < length xs} = {i - 1..<length xs}"
    by (auto)
  ultimately show ?case
    using hyp by (force simp add: seq_extract_def sublist_Cons)
qed

lemma seq_extract_append:
  "A \<upharpoonleft>\<^sub>l (xs @ ys) = (A \<upharpoonleft>\<^sub>l xs) @ ({j. j + length xs \<in> A} \<upharpoonleft>\<^sub>l ys)"
  by (simp add: seq_extract_def sublist_append)

lemma seq_extract_range: "A \<upharpoonleft>\<^sub>l xs = (A \<inter> dom\<^sub>l(xs)) \<upharpoonleft>\<^sub>l xs"
  apply (auto simp add: seq_extract_def sublist_def)
  apply (metis (no_types, lifting) atLeastLessThan_iff filter_cong in_set_zip nth_mem set_upt)
done

lemma seq_extract_out_of_range:
  "A \<inter> dom\<^sub>l(xs) = {} \<Longrightarrow> A \<upharpoonleft>\<^sub>l xs = []"
  by (metis seq_extract_def seq_extract_range sublist_empty)

lemma seq_append_as_extract:
  "xs = ys @ zs \<longleftrightarrow> (\<exists> i\<le>length(xs). ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length(xs)} \<upharpoonleft>\<^sub>l xs)"
proof
  assume xs: "xs = ys @ zs"
  moreover have "ys = {0..<length ys} \<upharpoonleft>\<^sub>l (ys @ zs)"
    by (simp add: seq_extract_append)
  moreover have "zs = {length ys..<length ys + length zs} \<upharpoonleft>\<^sub>l (ys @ zs)"
  proof -
    have "{length ys..<length ys + length zs} \<inter> {0..<length ys} = {}"
      by auto
    moreover have s1: "{j. j < length zs} = {0..<length zs}"
      by auto
    ultimately show ?thesis
      by (simp add: seq_extract_append seq_extract_out_of_range)
  qed
  ultimately show "(\<exists> i\<le>length(xs). ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length(xs)} \<upharpoonleft>\<^sub>l xs)"
    by (rule_tac x="length ys" in exI, auto)
next
  assume "\<exists>i\<le>length xs. ys = {0..<i} \<upharpoonleft>\<^sub>l xs \<and> zs = {i..<length xs} \<upharpoonleft>\<^sub>l xs"
  thus "xs = ys @ zs"
    by (auto simp add: seq_extract_split)
qed

definition seq_filter :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" (infix "\<restriction>\<^sub>l" 80) where
"seq_filter xs A = filter (\<lambda> x. x \<in> A) xs"

lemma seq_filter_Nil [simp]: "[] \<restriction>\<^sub>l A = []"
  by (simp add: seq_filter_def)

lemma seq_filter_empty [simp]: "xs \<restriction>\<^sub>l {} = []"
  by (simp add: seq_filter_def)

lemma seq_filter_append: "(xs @ ys) \<restriction>\<^sub>l A = (xs \<restriction>\<^sub>l A) @ (ys \<restriction>\<^sub>l A)"
  by (simp add: seq_filter_def) 

end