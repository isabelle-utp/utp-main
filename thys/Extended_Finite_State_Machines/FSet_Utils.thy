section\<open>FSet Utilities\<close>
text\<open>This theory provides various additional lemmas, definitions, and syntax over the fset data type.\<close>
theory FSet_Utils
  imports "HOL-Library.FSet"
begin

notation (latex output)
  "FSet.fempty" ("\<emptyset>") and
  "FSet.fmember" ("\<in>")

syntax (ASCII)
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3ALL (_/:_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX (_/:_)./ _)" [0, 0, 10] 10)
  "_fBex1"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX! (_/:_)./ _)" [0, 0, 10] 10)

syntax (input)
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3! (_/:_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3? (_/:_)./ _)" [0, 0, 10] 10)
  "_fBex1"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3?! (_/:_)./ _)" [0, 0, 10] 10)

syntax
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBnex"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<nexists>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBex1"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>!(_/|\<in>|_)./ _)" [0, 0, 10] 10)

translations
  "\<forall>x|\<in>|A. P" \<rightleftharpoons> "CONST fBall A (\<lambda>x. P)"
  "\<exists>x|\<in>|A. P" \<rightleftharpoons> "CONST fBex  A (\<lambda>x. P)"
  "\<nexists>x|\<in>|A. P" \<rightleftharpoons> "CONST fBall A (\<lambda>x. \<not>P)"
  "\<exists>!x|\<in>|A. P" \<rightharpoonup> "\<exists>!x. x |\<in>| A \<and> P"

lemma fset_of_list_remdups [simp]: "fset_of_list (remdups l) = fset_of_list l"
  apply (induct l)
   apply simp
  by (simp add: finsert_absorb fset_of_list_elem)

definition "fSum \<equiv> fsum (\<lambda>x. x)"

lemma fset_both_sides: "(Abs_fset s = f) = (fset (Abs_fset s) = fset f)"
  by (simp add: fset_inject)

lemma Abs_ffilter: "(ffilter f s = s') = ({e \<in> (fset s). f e} = (fset s'))"
  by (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)

lemma size_ffilter_card: "size (ffilter f s) = card ({e \<in> (fset s). f e})"
  by (simp add: ffilter_def fset_both_sides Abs_fset_inverse Set.filter_def)

lemma ffilter_empty [simp]: "ffilter f {||} = {||}"
  by auto

lemma ffilter_finsert:
  "ffilter f (finsert a s) = (if f a then finsert a (ffilter f s) else (ffilter f s))"
  apply simp
  apply standard
   apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
   apply auto[1]
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

lemma fset_equiv: "(f1 = f2) = (fset f1 = fset f2)"
  by (simp add: fset_inject)

lemma finsert_equiv: "(finsert e f = f') = (insert e (fset f) = (fset f'))"
  by (simp add: finsert_def fset_both_sides Abs_fset_inverse)

lemma filter_elements:
  "x |\<in>| Abs_fset (Set.filter f (fset s)) = (x \<in> (Set.filter f (fset s)))"
  by (metis ffilter.rep_eq fset_inverse notin_fset)

lemma sorted_list_of_fempty [simp]: "sorted_list_of_fset {||} = []"
  by (simp add: sorted_list_of_fset_def)

lemma fmember_implies_member: "e |\<in>| f \<Longrightarrow> e \<in> fset f"
  by (simp add: fmember_def)

lemma fold_union_ffUnion: "fold (|\<union>|) l {||} = ffUnion (fset_of_list l)"
by(induct l rule: rev_induct, auto)

lemma filter_filter:
  "ffilter P (ffilter Q xs) = ffilter (\<lambda>x. Q x \<and> P x) xs"
  by auto

lemma fsubset_strict:
  "x2 |\<subset>| x1 \<Longrightarrow> \<exists>e. e |\<in>| x1 \<and> e |\<notin>| x2"
  by auto

lemma fsubset:
  "x2 |\<subset>| x1 \<Longrightarrow> \<nexists>e. e |\<in>| x2 \<and> e |\<notin>| x1"
  by auto

lemma size_fsubset_elem:
  assumes "\<exists>e. e |\<in>| x1 \<and> e |\<notin>| x2"
      and "\<nexists>e. e |\<in>| x2 \<and> e |\<notin>| x1"
    shows "size x2 < size x1"
  using assms
  apply (simp add: fmember_def)
  by (metis card_seteq finite_fset linorder_not_le subsetI)

lemma size_fsubset: "x2 |\<subset>| x1 \<Longrightarrow> size x2 < size x1"
  by (metis fsubset fsubset_strict size_fsubset_elem)

definition fremove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  where [code_abbrev]: "fremove x A = A - {|x|}"

lemma arg_cong_ffilter:
  "\<forall>e |\<in>| f. p e = p' e \<Longrightarrow> ffilter p f = ffilter p' f"
  by auto

lemma ffilter_singleton: "f e \<Longrightarrow> ffilter f {|e|} = {|e|}"
  apply (simp add: ffilter_def fset_both_sides Abs_fset_inverse)
  by auto

lemma fset_eq_alt: "(x = y) = (x |\<subseteq>| y \<and> size x = size y)"
  by (metis exists_least_iff le_less size_fsubset)

lemma ffold_empty [simp]: "ffold f b {||} = b"
  by (simp add: ffold_def)

lemma sorted_list_of_fset_sort:
  "sorted_list_of_fset (fset_of_list l) = sort (remdups l)"
  by (simp add: fset_of_list.rep_eq sorted_list_of_fset.rep_eq sorted_list_of_set_sort_remdups)

lemma fMin_Min: "fMin (fset_of_list l) = Min (set l)"
  by (simp add: fMin.F.rep_eq fset_of_list.rep_eq)

lemma sorted_hd_Min:
  "sorted l \<Longrightarrow>
   l \<noteq> [] \<Longrightarrow>
   hd l = Min (set l)"
  by (metis List.finite_set Min_eqI eq_iff hd_Cons_tl insertE list.set_sel(1) list.simps(15) sorted.simps(2))

lemma hd_sort_Min: "l \<noteq> [] \<Longrightarrow> hd (sort l) = Min (set l)"
  by (metis sorted_hd_Min set_empty set_sort sorted_sort)

lemma hd_sort_remdups: "hd (sort (remdups l)) = hd (sort l)"
  by (metis hd_sort_Min remdups_eq_nil_iff set_remdups)

lemma exists_fset_of_list: "\<exists>l. f = fset_of_list l"
  using exists_fset_of_list by fastforce

lemma hd_sorted_list_of_fset:
  "s \<noteq> {||} \<Longrightarrow> hd (sorted_list_of_fset s) = (fMin s)"
  apply (insert exists_fset_of_list[of s])
  apply (erule exE)
  apply simp
  apply (simp add: sorted_list_of_fset_sort fMin_Min hd_sort_remdups)
  by (metis fset_of_list_simps(1) hd_sort_Min)

lemma fminus_filter_singleton:
  "fset_of_list l |-| {|x|} = fset_of_list (filter (\<lambda>e. e \<noteq> x) l)"
  by auto

lemma card_minus_fMin:
  "s \<noteq> {||} \<Longrightarrow> card (fset s - {fMin s}) < card (fset s)"
  by (metis Min_in bot_fset.rep_eq card_Diff1_less fMin.F.rep_eq finite_fset fset_equiv)

(* Provides a deterministic way to fold fsets similar to List.fold that works with the code generator *)
function ffold_ord :: "(('a::linorder) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b \<Rightarrow> 'b" where
  "ffold_ord f s b = (
    if s = {||} then
      b
    else
      let
        h = fMin s;
        t = s - {|h|}
      in
        ffold_ord f t (f h b)
  )"
  by auto
termination
  apply (relation "measures [\<lambda>(a, s, ab). size s]")
   apply simp
  by (simp add: card_minus_fMin)

lemma sorted_list_of_fset_Cons:
  "\<exists>h t. (sorted_list_of_fset (finsert s ss)) = h#t"
  apply (simp add: sorted_list_of_fset_def)
  by (cases "insort s (sorted_list_of_set (fset ss - {s}))", auto)

lemma list_eq_hd_tl:
  "l \<noteq> [] \<Longrightarrow>
   hd l = h \<Longrightarrow>
   tl l = t \<Longrightarrow>
   l = (h#t)"
  by auto

lemma fset_of_list_sort: "fset_of_list l = fset_of_list (sort l)"
  by (simp add: fset_of_list.abs_eq)

lemma exists_sorted_distinct_fset_of_list:
  "\<exists>l. sorted l \<and> distinct l \<and> f = fset_of_list l"
  by (metis distinct_sorted_list_of_set sorted_list_of_fset.rep_eq sorted_list_of_fset_simps(2) sorted_sorted_list_of_set)

lemma fset_of_list_empty [simp]: "(fset_of_list l = {||}) = (l = [])"
  by (metis fset_of_list.rep_eq fset_of_list_simps(1) set_empty)

lemma ffold_ord_cons: assumes sorted: "sorted (h#t)"
    and distinct: "distinct (h#t)"
  shows "ffold_ord f (fset_of_list (h#t)) b = ffold_ord f (fset_of_list t) (f h b)"
proof-
  have h_is_min: "h = fMin (fset_of_list (h#t))"
    by (metis sorted fMin_Min list.sel(1) list.simps(3) sorted_hd_Min)
  have remove_min: "fset_of_list t = (fset_of_list (h#t)) - {|h|}"
    using distinct fset_of_list_elem by force
  show ?thesis
    apply (simp only: ffold_ord.simps[of f "fset_of_list (h#t)"])
    by (metis h_is_min remove_min fset_of_list_empty list.distinct(1))
qed

lemma sorted_distinct_ffold_ord: assumes "sorted l"
      and "distinct l"
    shows "ffold_ord f (fset_of_list l) b = fold f l b"
  using assms
  apply (induct l arbitrary: b)
   apply simp
  by (metis distinct.simps(2) ffold_ord_cons fold_simps(2) sorted.simps(2))

lemma ffold_ord_fold_sorted: "ffold_ord f s b = fold f (sorted_list_of_fset s) b"
  by (metis exists_sorted_distinct_fset_of_list sorted_distinct_ffold_ord distinct_remdups_id sorted_list_of_fset_sort sorted_sort_id)

context includes fset.lifting begin
  lift_definition fprod  :: "'a fset \<Rightarrow> 'b fset \<Rightarrow> ('a \<times> 'b) fset " (infixr "|\<times>|" 80) is "\<lambda>a b. fset a \<times> fset b"
    by simp

  lift_definition fis_singleton :: "'a fset \<Rightarrow> bool" is "\<lambda>A. is_singleton (fset A)".
end

lemma fprod_empty_l: "{||} |\<times>| a = {||}"
  using bot_fset_def fprod.abs_eq by force

lemma fprod_empty_r: "a |\<times>| {||} = {||}"
  by (simp add: fprod_def bot_fset_def Abs_fset_inverse)

lemmas fprod_empty = fprod_empty_l fprod_empty_r

lemma fprod_finsert: "(finsert a as) |\<times>| (finsert b bs) =
   finsert (a, b) (fimage (\<lambda>b. (a, b)) bs |\<union>| fimage (\<lambda>a. (a, b)) as |\<union>| (as |\<times>| bs))"
  apply (simp add: fprod_def fset_both_sides Abs_fset_inverse)
  by auto

lemma fprod_member:
  "x |\<in>| xs \<Longrightarrow>
   y |\<in>| ys \<Longrightarrow>
   (x, y) |\<in>| xs |\<times>| ys"
  by (simp add: fmember_def fprod_def Abs_fset_inverse)

lemma fprod_subseteq:
  "x |\<subseteq>| x' \<and> y |\<subseteq>| y' \<Longrightarrow> x |\<times>| y |\<subseteq>| x' |\<times>| y'"
  apply (simp add: fprod_def less_eq_fset_def Abs_fset_inverse)
  by auto

lemma fimage_fprod:
  "(a, b) |\<in>| A |\<times>| B \<Longrightarrow> f a b |\<in>| (\<lambda>(x, y). f x y) |`| (A |\<times>| B)"
  by force

lemma fprod_singletons: "{|a|} |\<times>| {|b|} = {|(a, b)|}"
  apply (simp add: fprod_def)
  by (metis fset_inverse fset_simps(1) fset_simps(2))

lemma fprod_equiv:
  "(fset (f |\<times>| f') = s) = (((fset f) \<times> (fset f')) = s)"
  by (simp add: fprod_def Abs_fset_inverse)

lemma fis_singleton_alt: "fis_singleton f = (\<exists>e. f = {|e|})"
  by (metis fis_singleton.rep_eq fset_inverse fset_simps(1) fset_simps(2) is_singleton_def)

lemma singleton_singleton [simp]: "fis_singleton {|a|}"
  by (simp add: fis_singleton_def)

lemma not_singleton_empty [simp]: "\<not> fis_singleton {||}"
  apply (simp add: fis_singleton_def)
  by (simp add: is_singleton_altdef)

lemma fis_singleton_fthe_elem:
  "fis_singleton A \<longleftrightarrow> A = {|fthe_elem A|}"
  by (metis fis_singleton_alt fthe_felem_eq)

lemma fBall_ffilter:
  "\<forall>x |\<in>| X. f x \<Longrightarrow> ffilter f X = X"
  by auto

lemma fBall_ffilter2:
  "X = Y \<Longrightarrow>
   \<forall>x |\<in>| X. f x \<Longrightarrow>
   ffilter f X = Y"
  by auto

lemma size_fset_of_list: "size (fset_of_list l) = length (remdups l)"
  apply (induct l)
   apply simp
  by (simp add: fset_of_list.rep_eq insert_absorb)

lemma size_fsingleton: "(size f = 1) = (\<exists>e. f = {|e|})"
  apply (insert exists_fset_of_list[of f])
  apply clarify
  apply (simp only: size_fset_of_list)
  apply (simp add: fset_of_list_def fset_both_sides Abs_fset_inverse)
  by (metis List.card_set One_nat_def card.insert card_1_singletonE card.empty empty_iff finite.intros(1))

lemma ffilter_mono: "(ffilter X xs = f) \<Longrightarrow> \<forall>x |\<in>| xs. X x = Y x \<Longrightarrow> (ffilter Y xs = f)"
  by auto

lemma size_fimage: "size (fimage f s) \<le> size s"
  apply (induct s)
   apply simp
  by (simp add: card_insert_if)

lemma size_ffilter: "size (ffilter P f) \<le> size f"
  apply (induct f)
   apply simp
  apply (simp only: ffilter_finsert)
  apply (case_tac "P x")
   apply (simp add: fmember.rep_eq)
  by (simp add: card_insert_if)

lemma fimage_size_le: "\<And>f s. size s \<le> n \<Longrightarrow> size (fimage f s) \<le> n"
  using le_trans size_fimage by blast

lemma ffilter_size_le: "\<And>f s. size s \<le> n \<Longrightarrow> size (ffilter f s) \<le> n"
  using dual_order.trans size_ffilter by blast

lemma set_membership_eq: "A = B \<longleftrightarrow> (\<lambda>x. Set.member x A) = (\<lambda>x. Set.member x B)"
  apply standard
   apply simp
  by (meson equalityI subsetI)

lemmas ffilter_eq_iff = Abs_ffilter set_membership_eq fun_eq_iff

lemma size_le_1: "size f \<le> 1 = (f = {||} \<or> (\<exists>e. f = {|e|}))"
  apply standard
   apply (metis bot.not_eq_extremum gr_implies_not0 le_neq_implies_less less_one size_fsingleton size_fsubset)
  by auto

lemma size_gt_1: "1 < size f \<Longrightarrow> \<exists>e1 e2 f'. e1 \<noteq> e2 \<and> f = finsert e1 (finsert e2 f')"
  apply (induct f)
   apply simp
  apply (rule_tac x=x in exI)
  by (metis finsertCI leD not_le_imp_less size_le_1)

end
