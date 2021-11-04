subsection \<open>Executable version\<close>
theory Multiset_Extension2_Impl
imports
  "HOL-Library.DAList_Multiset"
  List_Order
  Multiset_Extension2 
  Multiset_Extension_Pair_Impl
begin

(**
We use the lifting when it is sufficient to prove the non-strict
domination to also prove the strict one. For example if [a > x] then
it is sufficient to prove that [A \<ge> X] to get [A + {#a#} > X + {#x#}]
**)

lemma mul_ext_list_ext: "\<exists> s ns. list_order_extension_impl s ns mul_ext"
proof(intro exI)
  let ?s = "\<lambda> s ns. {(as,bs). (mset as, mset bs) \<in> s_mul_ext ns s}"
  let ?ns = "\<lambda> s ns. {(as,bs). (mset as, mset bs) \<in> ns_mul_ext ns s}" 
  let ?m = mset
  show "list_order_extension_impl ?s ?ns mul_ext"
  proof
    fix s ns
    show "?s {(a,b). s a b} {(a,b). ns a b} = {(as,bs). fst (mul_ext (\<lambda> a b. (s a b, ns a b)) as bs)}"
      unfolding mul_ext_def Let_def by auto
  next
    fix s ns
    show "?ns {(a,b). s a b} {(a,b). ns a b} = {(as,bs). snd (mul_ext (\<lambda> a b. (s a b, ns a b)) as bs)}"
      unfolding mul_ext_def Let_def by auto
  next
    fix s ns s' ns' as bs
    assume "set as \<times> set bs \<inter> ns \<subseteq> ns'"
           "set as \<times> set bs \<inter> s \<subseteq> s'"
           "(as,bs) \<in> ?s s ns"
    then show "(as,bs) \<in> ?s s' ns'"
      using s_mul_ext_local_mono[of "?m as" "?m bs" ns ns' s s']
      unfolding set_mset_mset by auto
  next
    fix s ns s' ns' as bs
    assume "set as \<times> set bs \<inter> ns \<subseteq> ns'"
           "set as \<times> set bs \<inter> s \<subseteq> s'"
           "(as,bs) \<in> ?ns s ns"
    then show "(as,bs) \<in> ?ns s' ns'"
      using ns_mul_ext_local_mono[of "?m as" "?m bs" ns ns' s s']
      unfolding set_mset_mset by auto
  qed
qed

context fixes sns :: "'a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool"
begin

fun mul_ext_impl :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
and mul_ex_dom :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
where
  "mul_ext_impl [] []       = (False, True)"
| "mul_ext_impl [] ys       = (False, False)"
| "mul_ext_impl xs []       = (True, True)"
| "mul_ext_impl xs (y # ys) = mul_ex_dom xs [] y ys"

| "mul_ex_dom []       xs' y ys = (False, False)"
| "mul_ex_dom (x # xs) xs' y ys =
    (case sns x y of
      (True, _) \<Rightarrow> if snd (mul_ext_impl (xs @ xs') (filter (\<lambda>y. \<not> fst (sns x y)) ys)) then (True, True)
                   else mul_ex_dom xs (x # xs') y ys
    | (False, True) \<Rightarrow> or2 (mul_ext_impl (xs @ xs') ys) (mul_ex_dom xs (x # xs') y ys)
    | _ \<Rightarrow> mul_ex_dom xs (x # xs') y ys)"

end

context
begin
lemma mul_ext_impl_sound0:
  "mul_ext_impl sns xs ys = mult2_impl (\<lambda>x y. sns y x) ys xs"
  "mul_ex_dom sns xs xs' y ys = mult2_ex_dom (\<lambda>x y. sns y x) y ys xs xs'"
by (induct xs ys and xs xs' y ys taking: sns rule: mul_ext_impl_mul_ex_dom.induct)
  (auto split: prod.splits bool.splits)

private definition cond1 where
  "cond1 f bs y xs ys \<equiv>
  ((\<exists>b. b \<in> set bs \<and> fst (f b y) \<and> snd (mul_ext f (remove1 b xs) [y\<leftarrow>ys . \<not> fst (f b y)]))
  \<or> (\<exists>b. b \<in> set bs \<and> snd (f b y) \<and> fst (mul_ext f (remove1 b xs) ys)))"

private lemma cond1_propagate:
  assumes "cond1 f bs y xs ys"
  shows "cond1 f (b # bs) y xs ys"
using assms unfolding cond1_def by auto

private definition cond2 where
  "cond2 f bs y xs ys \<equiv> (cond1 f bs y xs ys
  \<or> (\<exists>b. b \<in> set bs \<and> snd (f b y) \<and> snd (mul_ext f (remove1 b xs) ys)))"

private lemma cond2_propagate:
  assumes "cond2 f bs y xs ys"
  shows "cond2 f (b # bs) y xs ys"
using assms and cond1_propagate[of f bs y xs ys]
unfolding cond2_def by auto

private lemma cond1_cond2:
  assumes "cond1 f bs y xs ys"
  shows "cond2 f bs y xs ys"
using assms unfolding cond2_def by simp

lemma mul_ext_impl_sound:
  shows "mul_ext_impl f xs ys = mul_ext f xs ys"
unfolding mul_ext_def s_mul_ext_def ns_mul_ext_def
by (auto simp: Let_def converse_def mul_ext_impl_sound0 mult2_impl_sound)

lemma mul_ext_code [code]: "mul_ext = mul_ext_impl"
  by (intro ext, unfold mul_ext_impl_sound, auto)

lemma mul_ext_impl_cong[fundef_cong]:
  assumes "\<And>x x'. x \<in> set xs \<Longrightarrow> x' \<in> set ys \<Longrightarrow> f x x' = g x x'"
  shows "mul_ext_impl f xs ys = mul_ext_impl g xs ys"
using assms
 stri_mul_ext_map[of xs ys g f id] nstri_mul_ext_map[of xs ys g f id]
 stri_mul_ext_map[of xs ys f g id] nstri_mul_ext_map[of xs ys f g id]
  by (auto simp: mul_ext_impl_sound mul_ext_def Let_def)
end

fun ass_list_to_single_list :: "('a \<times> nat) list \<Rightarrow> 'a list"
  where
    "ass_list_to_single_list [] = []"
  | "ass_list_to_single_list ((x, n) # xs) = replicate n x @ ass_list_to_single_list xs"

lemma set_ass_list_to_single_list [simp]:
  "set (ass_list_to_single_list xs) = {x. \<exists>n. (x, n) \<in> set xs \<and> n > 0}"
  by (induct xs rule: ass_list_to_single_list.induct) auto

lemma count_mset_replicate [simp]:
  "count (mset (replicate n x)) x = n"
  by (induct n) (auto)

lemma count_mset_lal_ge:
  "(x, n) \<in> set xs \<Longrightarrow> count (mset (ass_list_to_single_list xs)) x \<ge> n"
  by (induct xs) auto

lemma count_of_count_mset_lal [simp]:
  "distinct (map fst y) \<Longrightarrow> count_of y x = count (mset (ass_list_to_single_list y)) x"
  by (induct y) (auto simp: count_mset_lal_ge count_of_empty)

lemma Bag_mset: "Bag xs = mset (ass_list_to_single_list (DAList.impl_of xs))"
  by (intro multiset_eqI, induct xs) (auto simp: Alist_inverse)

lemma Bag_Alist_Cons:
  "x \<notin> fst ` set xs \<Longrightarrow> distinct (map fst xs) \<Longrightarrow>
    Bag (Alist ((x, n) # xs)) = mset (replicate n x) + Bag (Alist xs)"
  by (induct xs) (auto simp: Bag_mset Alist_inverse)

lemma mset_lal [simp]:
  "distinct (map fst xs) \<Longrightarrow> mset (ass_list_to_single_list xs) = Bag (Alist xs)"
  apply (induct xs) apply (auto simp: Bag_Alist_Cons)
  apply (simp add: Mempty_Bag empty.abs_eq)
  done

lemma Bag_s_mul_ext:
  "(Bag xs, Bag ys) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)} \<longleftrightarrow>
    fst (mul_ext f (ass_list_to_single_list (DAList.impl_of xs)) (ass_list_to_single_list (DAList.impl_of ys)))"
  by (auto simp: mul_ext_def Let_def Alist_impl_of)

lemma Bag_ns_mul_ext:
  "(Bag xs, Bag ys) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)} \<longleftrightarrow>
    snd (mul_ext f (ass_list_to_single_list (DAList.impl_of xs)) (ass_list_to_single_list (DAList.impl_of ys)))"
  by (auto simp: mul_ext_def Let_def Alist_impl_of)

lemma smulextp_code[code]:
  "smulextp f (Bag xs) (Bag ys) \<longleftrightarrow> fst (mul_ext f (ass_list_to_single_list (DAList.impl_of xs)) (ass_list_to_single_list (DAList.impl_of ys)))"
  unfolding smulextp_def Bag_s_mul_ext ..

lemma nsmulextp_code[code]:
  "nsmulextp f (Bag xs) (Bag ys) \<longleftrightarrow> snd (mul_ext f (ass_list_to_single_list (DAList.impl_of xs)) (ass_list_to_single_list (DAList.impl_of ys)))"
  unfolding nsmulextp_def Bag_ns_mul_ext ..

lemma mulextp_code[code]:
  "mulextp f (Bag xs) (Bag ys) = mul_ext f (ass_list_to_single_list (DAList.impl_of xs)) (ass_list_to_single_list (DAList.impl_of ys))"
  unfolding mulextp_def by (simp add: nsmulextp_code smulextp_code) 

end
