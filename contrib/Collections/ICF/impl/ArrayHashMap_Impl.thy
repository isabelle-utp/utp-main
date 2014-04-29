(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
header {* \isaheader{Array-based hash map implementation} *}
theory ArrayHashMap_Impl imports 
  "../../Lib/HashCode"
  "../../Lib/Diff_Array"
  "../gen_algo/ListGA"
  "ListMapImpl"
  "../../Iterator/Array_Iterator"
begin

text {*  Misc. *}

setup Locale_Code.open_block
interpretation a_idx_it!: 
  idx_iteratei_loc list_of_array "\<lambda>_. True" array_length array_get
  apply unfold_locales
  apply (case_tac [!] s) [2]
  apply auto
  done
setup Locale_Code.close_block

(*
lemma idx_iteratei_aux_array_get_Array_conv_nth:
  "idx_iteratei_aux array_get sz i (Array xs) c f \<sigma> = idx_iteratei_aux op ! sz i xs c f \<sigma>"
apply(induct get\<equiv>"op ! :: 'b list \<Rightarrow> nat \<Rightarrow> 'b" sz i xs c f \<sigma> rule: idx_iteratei_aux.induct)
apply(subst (1 2) idx_iteratei_aux.simps)
apply simp
done

lemma idx_iteratei_array_get_Array_conv_nth:
  "idx_iteratei array_get array_length (Array xs) = idx_iteratei nth length xs"
by(simp add: idx_iteratei_def fun_eq_iff idx_iteratei_aux_array_get_Array_conv_nth)

lemma idx_iteratei_aux_nth_conv_foldli_drop:
  fixes xs :: "'b list"
  assumes "i \<le> length xs"
  shows "idx_iteratei_aux op ! (length xs) i xs c f \<sigma> = foldli (drop (length xs - i) xs) c f \<sigma>"
using assms
proof(induct get\<equiv>"op ! :: 'b list \<Rightarrow> nat \<Rightarrow> 'b" sz\<equiv>"length xs" i xs c f \<sigma> rule: idx_iteratei_aux.induct)
  case (1 i l c f \<sigma>)
  show ?case
  proof(cases "i = 0 \<or> \<not> c \<sigma>")
    case True thus ?thesis
      by(subst idx_iteratei_aux.simps)(auto)
  next
    case False
    hence i: "i > 0" and c: "c \<sigma>" by auto
    hence "idx_iteratei_aux op ! (length l) i l c f \<sigma> = idx_iteratei_aux op ! (length l) (i - 1) l c f (f (l ! (length l - i)) \<sigma>)"
      by(subst idx_iteratei_aux.simps) simp
    also have "\<dots> = foldli (drop (length l - (i - 1)) l) c f (f (l ! (length l - i)) \<sigma>)"
      using `i \<le> length l` i c by -(rule 1, auto)
    also from `i \<le> length l` i
    have "drop (length l - i) l = (l ! (length l - i)) # drop (length l - (i - 1)) l"
      by(subst nth_drop'[symmetric])(simp_all, metis Suc_eq_plus1_left add_diff_assoc)
    hence "foldli (drop (length l - (i - 1)) l) c f (f (l ! (length l - i)) \<sigma>) = foldli (drop (length l - i) l) c f \<sigma>"
      using c by simp
    finally show ?thesis .
  qed
qed

lemma idx_iteratei_nth_length_conv_foldli: "idx_iteratei nth length = foldli"
by(rule ext)+(simp add: idx_iteratei_def idx_iteratei_aux_nth_conv_foldli_drop)
*)

subsection {* Type definition and primitive operations *}

definition load_factor :: nat -- "in percent"
  where "load_factor = 75"

text {*
  We do not use @{typ "('k, 'v) assoc_list"} for the buckets but plain lists of key-value pairs.
  This speeds up rehashing because we then do not have to go through the abstract operations.
*}

datatype ('key, 'val) hashmap =
  HashMap "('key \<times> 'val) list array" "nat"

subsection {* Operations *}

definition new_hashmap_with :: "nat \<Rightarrow> ('key :: hashable, 'val) hashmap"
where "\<And>size. new_hashmap_with size = HashMap (new_array [] size) 0"

definition ahm_empty :: "unit \<Rightarrow> ('key :: hashable, 'val) hashmap"
where "ahm_empty \<equiv> \<lambda>_. new_hashmap_with (def_hashmap_size TYPE('key))"

definition bucket_ok :: "nat \<Rightarrow> nat \<Rightarrow> (('key :: hashable) \<times> 'val) list \<Rightarrow> bool"
where "bucket_ok len h kvs = (\<forall>k \<in> fst ` set kvs. bounded_hashcode len k = h)"

definition ahm_invar_aux :: "nat \<Rightarrow> (('key :: hashable) \<times> 'val) list array \<Rightarrow> bool"
where
  "ahm_invar_aux n a \<longleftrightarrow>
  (\<forall>h. h < array_length a \<longrightarrow> bucket_ok (array_length a) h (array_get a h) \<and> distinct (map fst (array_get a h))) \<and>
  array_foldl (\<lambda>_ n kvs. n + size kvs) 0 a = n \<and>
  array_length a > 1"

primrec ahm_invar :: "('key :: hashable, 'val) hashmap \<Rightarrow> bool"
where "ahm_invar (HashMap a n) = ahm_invar_aux n a"

definition ahm_\<alpha>_aux :: "(('key :: hashable) \<times> 'val) list array \<Rightarrow> 'key \<Rightarrow> 'val option"
where [simp]: "ahm_\<alpha>_aux a k = map_of (array_get a (bounded_hashcode (array_length a) k)) k"

primrec ahm_\<alpha> :: "('key :: hashable, 'val) hashmap \<Rightarrow> 'key \<Rightarrow> 'val option"
where
  "ahm_\<alpha> (HashMap a _) = ahm_\<alpha>_aux a"

definition ahm_lookup :: "'key \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> 'val option"
where "ahm_lookup k hm  = ahm_\<alpha> hm k"

primrec ahm_iteratei_aux :: "((('key :: hashable) \<times> 'val) list array) \<Rightarrow> ('key \<times> 'val, '\<sigma>) set_iterator"
where "ahm_iteratei_aux (Array xs) c f = foldli (concat xs) c f"

primrec ahm_iteratei :: "(('key :: hashable, 'val) hashmap) \<Rightarrow> (('key \<times> 'val), '\<sigma>) set_iterator"
where
  "ahm_iteratei (HashMap a n) = ahm_iteratei_aux a"

definition ahm_rehash_aux' :: "nat \<Rightarrow> 'key \<times> 'val \<Rightarrow> (('key :: hashable) \<times> 'val) list array \<Rightarrow> ('key \<times> 'val) list array"
where
  "ahm_rehash_aux' n kv a =
   (let h = bounded_hashcode n (fst kv)
    in array_set a h (kv # array_get a h))"

definition ahm_rehash_aux :: "(('key :: hashable) \<times> 'val) list array \<Rightarrow> nat \<Rightarrow> ('key \<times> 'val) list array"
where
  "ahm_rehash_aux a sz = ahm_iteratei_aux a (\<lambda>x. True) (ahm_rehash_aux' sz) (new_array [] sz)"

primrec ahm_rehash :: "('key :: hashable, 'val) hashmap \<Rightarrow> nat \<Rightarrow> ('key, 'val) hashmap"
where "ahm_rehash (HashMap a n) sz = HashMap (ahm_rehash_aux a sz) n"

primrec hm_grow :: "('key :: hashable, 'val) hashmap \<Rightarrow> nat"
where "hm_grow (HashMap a n) = 2 * array_length a + 3"

primrec ahm_filled :: "('key :: hashable, 'val) hashmap \<Rightarrow> bool"
where "ahm_filled (HashMap a n) = (array_length a * load_factor \<le> n * 100)"

primrec ahm_update_aux :: "('key :: hashable, 'val) hashmap \<Rightarrow> 'key \<Rightarrow> 'val \<Rightarrow> ('key, 'val) hashmap"
where
  "ahm_update_aux (HashMap a n) k v = 
  (let h = bounded_hashcode (array_length a) k;
       m = array_get a h;
       insert = map_of m k = None
   in HashMap (array_set a h (AList.update k v m)) (if insert then n + 1 else n))"

definition ahm_update :: "'key \<Rightarrow> 'val \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> ('key, 'val) hashmap"
where
  "ahm_update k v hm = 
   (let hm' = ahm_update_aux hm k v
    in (if ahm_filled hm' then ahm_rehash hm' (hm_grow hm') else hm'))"

primrec ahm_delete :: "'key \<Rightarrow> ('key :: hashable, 'val) hashmap \<Rightarrow> ('key, 'val) hashmap"
where
  "ahm_delete k (HashMap a n) =
  (let h = bounded_hashcode (array_length a) k;
       m = array_get a h;
       deleted = (map_of m k \<noteq> None)
   in HashMap (array_set a h (AList.delete k m)) (if deleted then n - 1 else n))"


lemma hm_grow_gt_1 [iff]:
  "Suc 0 < hm_grow hm"
by(cases hm)(simp)

lemma bucket_ok_Nil [simp]: "bucket_ok len h [] = True"
by(simp add: bucket_ok_def)

lemma bucket_okD:
  "\<lbrakk> bucket_ok len h xs; (k, v) \<in> set xs \<rbrakk>
  \<Longrightarrow> bounded_hashcode len k = h"
by(auto simp add: bucket_ok_def)

lemma bucket_okI:
  "(\<And>k. k \<in> fst ` set kvs \<Longrightarrow> bounded_hashcode len k = h) \<Longrightarrow> bucket_ok len h kvs"
by(simp add: bucket_ok_def)


subsection {* @{term ahm_invar} *}

lemma ahm_invar_auxE:
  assumes "ahm_invar_aux n a"
  obtains "\<forall>h. h < array_length a \<longrightarrow> bucket_ok (array_length a) h (array_get a h) \<and> distinct (map fst (array_get a h))"
  and "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a" and "array_length a > 1"
using assms unfolding ahm_invar_aux_def by blast

lemma ahm_invar_auxI:
  "\<lbrakk> \<And>h. h < array_length a \<Longrightarrow> bucket_ok (array_length a) h (array_get a h);
     \<And>h. h < array_length a \<Longrightarrow> distinct (map fst (array_get a h));
     n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a; array_length a > 1 \<rbrakk>
  \<Longrightarrow> ahm_invar_aux n a"
unfolding ahm_invar_aux_def by blast

lemma ahm_invar_distinct_fst_concatD:
  assumes inv: "ahm_invar_aux n (Array xs)"
  shows "distinct (map fst (concat xs))"
proof -
  { fix h
    assume "h < length xs"
    with inv have "bucket_ok (length xs) h (xs ! h)" "distinct (map fst (xs ! h))"
      by(simp_all add: ahm_invar_aux_def) }
  note no_junk = this

  show ?thesis unfolding map_concat
  proof(rule distinct_concat')
    have "distinct [x\<leftarrow>xs . x \<noteq> []]" unfolding distinct_conv_nth
    proof(intro allI ballI impI)
      fix i j
      assume "i < length [x\<leftarrow>xs . x \<noteq> []]" "j < length [x\<leftarrow>xs . x \<noteq> []]" "i \<noteq> j"
      from filter_nth_ex_nth[OF `i < length [x\<leftarrow>xs . x \<noteq> []]`]
      obtain i' where "i' \<ge> i" "i' < length xs" and ith: "[x\<leftarrow>xs . x \<noteq> []] ! i = xs ! i'" 
        and eqi: "[x\<leftarrow>take i' xs . x \<noteq> []] = take i [x\<leftarrow>xs . x \<noteq> []]" by blast
      from filter_nth_ex_nth[OF `j < length [x\<leftarrow>xs . x \<noteq> []]`]
      obtain j' where "j' \<ge> j" "j' < length xs" and jth: "[x\<leftarrow>xs . x \<noteq> []] ! j = xs ! j'"
        and eqj: "[x\<leftarrow>take j' xs . x \<noteq> []] = take j [x\<leftarrow>xs . x \<noteq> []]" by blast
      show "[x\<leftarrow>xs . x \<noteq> []] ! i \<noteq> [x\<leftarrow>xs . x \<noteq> []] ! j"
      proof
        assume "[x\<leftarrow>xs . x \<noteq> []] ! i = [x\<leftarrow>xs . x \<noteq> []] ! j"
        hence eq: "xs ! i' = xs ! j'" using ith jth by simp
        from `i < length [x\<leftarrow>xs . x \<noteq> []]`
        have "[x\<leftarrow>xs . x \<noteq> []] ! i \<in> set [x\<leftarrow>xs . x \<noteq> []]" by(rule nth_mem)
        with ith have "xs ! i' \<noteq> []" by simp
        then obtain kv where "kv \<in> set (xs ! i')" by(fastforce simp add: neq_Nil_conv)
        with no_junk[OF `i' < length xs`] have "bounded_hashcode (length xs) (fst kv) = i'"
          by(simp add: bucket_ok_def)
        moreover from eq `kv \<in> set (xs ! i')` have "kv \<in> set (xs ! j')" by simp
        with no_junk[OF `j' < length xs`] have "bounded_hashcode (length xs) (fst kv) = j'"
          by(simp add: bucket_ok_def)
        ultimately have [simp]: "i' = j'" by simp
        from `i < length [x\<leftarrow>xs . x \<noteq> []]` have "i = length (take i [x\<leftarrow>xs . x \<noteq> []])" by simp
        also from eqi eqj have "take i [x\<leftarrow>xs . x \<noteq> []] = take j [x\<leftarrow>xs . x \<noteq> []]" by simp
        finally show False using `i \<noteq> j` `j < length [x\<leftarrow>xs . x \<noteq> []]` by simp
      qed
    qed
    moreover have "inj_on (map fst) {x \<in> set xs. x \<noteq> []}"
    proof(rule inj_onI)
      fix x y
      assume "x \<in> {x \<in> set xs. x \<noteq> []}" "y \<in> {x \<in> set xs. x \<noteq> []}" "map fst x = map fst y"
      hence "x \<in> set xs" "y \<in> set xs" "x \<noteq> []" "y \<noteq> []" by auto
      from `x \<in> set xs` obtain i where "xs ! i = x" "i < length xs" unfolding set_conv_nth by fastforce
      from `y \<in> set xs` obtain j where "xs ! j = y" "j < length xs" unfolding set_conv_nth by fastforce
      from `x \<noteq> []` obtain k v x' where "x = (k, v) # x'" by(cases x) auto
      with no_junk[OF `i < length xs`] `xs ! i = x`
      have "bounded_hashcode (length xs) k = i" by(auto simp add: bucket_ok_def)
      moreover from `map fst x = map fst y` `x = (k, v) # x'` obtain v' where "(k, v') \<in> set y" by fastforce
      with no_junk[OF `j < length xs`] `xs ! j = y`
      have "bounded_hashcode (length xs) k = j" by(auto simp add: bucket_ok_def)
      ultimately have "i = j" by simp
      with `xs ! i = x` `xs ! j = y` show "x = y" by simp
    qed
    ultimately show "distinct [ys\<leftarrow>map (map fst) xs . ys \<noteq> []]"
      by(simp add: filter_map o_def distinct_map)
  next
    fix ys
    assume "ys \<in> set (map (map fst) xs)"
    thus "distinct ys" by(clarsimp simp add: set_conv_nth)(rule no_junk)
  next
    fix ys zs
    assume "ys \<in> set (map (map fst) xs)" "zs \<in> set (map (map fst) xs)" "ys \<noteq> zs"
    then obtain ys' zs' where [simp]: "ys = map fst ys'" "zs = map fst zs'" 
      and "ys' \<in> set xs" "zs' \<in> set xs" by auto
    have "fst ` set ys' \<inter> fst ` set zs' = {}"
    proof(rule equals0I)
      fix k
      assume "k \<in> fst ` set ys' \<inter> fst ` set zs'"
      then obtain v v' where "(k, v) \<in> set ys'" "(k, v') \<in> set zs'" by(auto)
      from `ys' \<in> set xs` obtain i where "xs ! i = ys'" "i < length xs" unfolding set_conv_nth by fastforce
      with `(k, v) \<in> set ys'` have "bounded_hashcode (length xs) k = i" by(auto dest: no_junk bucket_okD)
      moreover
      from `zs' \<in> set xs` obtain j where "xs ! j = zs'" "j < length xs" unfolding set_conv_nth by fastforce
      with `(k, v') \<in> set zs'` have "bounded_hashcode (length xs) k = j" by(auto dest: no_junk bucket_okD)
      ultimately have "i = j" by simp
      with `xs ! i = ys'` `xs ! j = zs'` have "ys' = zs'" by simp
      with `ys \<noteq> zs` show False by simp
    qed
    thus "set ys \<inter> set zs = {}" by simp
  qed
qed

subsection {* @{term "ahm_\<alpha>"} *}

lemma finite_dom_ahm_\<alpha>_aux:
  assumes "ahm_invar_aux n a"
  shows "finite (dom (ahm_\<alpha>_aux a))"
proof -
  have "dom (ahm_\<alpha>_aux a) \<subseteq> (\<Union>h \<in> range (bounded_hashcode (array_length a) :: 'a \<Rightarrow> nat). dom (map_of (array_get a h)))"
    by(force simp add: dom_map_of_conv_image_fst ahm_\<alpha>_aux_def dest: map_of_SomeD)
  moreover have "finite \<dots>"
  proof(rule finite_UN_I)
    from `ahm_invar_aux n a` have "array_length a > 1" by(simp add: ahm_invar_aux_def)
    hence "range (bounded_hashcode (array_length a) :: 'a \<Rightarrow> nat) \<subseteq> {0..<array_length a}"
      by(auto simp add: bounded_hashcode_bounds)
    thus "finite (range (bounded_hashcode (array_length a) :: 'a \<Rightarrow> nat))"
      by(rule finite_subset) simp
  qed(rule finite_dom_map_of)
  ultimately show ?thesis by(rule finite_subset)
qed

lemma ahm_\<alpha>_aux_conv_map_of_concat:
  assumes inv: "ahm_invar_aux n (Array xs)"
  shows "ahm_\<alpha>_aux (Array xs) = map_of (concat xs)"
proof
  fix k
  show "ahm_\<alpha>_aux (Array xs) k = map_of (concat xs) k"
  proof(cases "map_of (concat xs) k")
    case None
    hence "k \<notin> fst ` set (concat xs)" by(simp add: map_of_eq_None_iff)
    hence "k \<notin> fst ` set (xs ! bounded_hashcode (length xs) k)"
    proof(rule contrapos_nn)
      assume "k \<in> fst ` set (xs ! bounded_hashcode (length xs) k)"
      then obtain v where "(k, v) \<in> set (xs ! bounded_hashcode (length xs) k)" by auto
      moreover from inv have "bounded_hashcode (length xs) k < length xs"
        by(simp add: bounded_hashcode_bounds ahm_invar_aux_def)
      ultimately show "k \<in> fst ` set (concat xs)"
        by(force intro: rev_image_eqI)
    qed
    thus ?thesis unfolding None by(simp add: map_of_eq_None_iff)
  next
    case (Some v)
    hence "(k, v) \<in> set (concat xs)" by(rule map_of_SomeD)
    then obtain ys where "ys \<in> set xs" "(k, v) \<in> set ys"
      unfolding set_concat by blast
    from `ys \<in> set xs` obtain i j where "i < length xs" "xs ! i = ys"
      unfolding set_conv_nth by auto
    with inv `(k, v) \<in> set ys`
    show ?thesis unfolding Some
      by(force dest: bucket_okD simp add: ahm_invar_aux_def)
  qed
qed

lemma ahm_invar_aux_card_dom_ahm_\<alpha>_auxD:
  assumes inv: "ahm_invar_aux n a"
  shows "card (dom (ahm_\<alpha>_aux a)) = n"
proof(cases a)
  case (Array xs)[simp]
  from inv have "card (dom (ahm_\<alpha>_aux (Array xs))) = card (dom (map_of (concat xs)))"
    by(simp add: ahm_\<alpha>_aux_conv_map_of_concat)
  also from inv have "distinct (map fst (concat xs))"
    by(simp add: ahm_invar_distinct_fst_concatD)
  hence "card (dom (map_of (concat xs))) = length (concat xs)"
    by(rule card_dom_map_of)
  also have "length (concat xs) = foldl op + 0 (map length xs)"
    by (simp add: length_concat foldl_conv_fold add_commute fold_plus_listsum_rev)
  also from inv
  have "\<dots> = n" unfolding foldl_map by(simp add: ahm_invar_aux_def array_foldl_foldl)
  finally show ?thesis by(simp)
qed

lemma finite_dom_ahm_\<alpha>:
  "ahm_invar hm \<Longrightarrow> finite (dom (ahm_\<alpha> hm))"
by(cases hm)(auto intro: finite_dom_ahm_\<alpha>_aux)

lemma finite_map_ahm_\<alpha>_aux:
  "finite_map ahm_\<alpha>_aux (ahm_invar_aux n)"
by(unfold_locales)(rule finite_dom_ahm_\<alpha>_aux)

lemma finite_map_ahm_\<alpha>:
  "finite_map ahm_\<alpha> ahm_invar"
by(unfold_locales)(rule finite_dom_ahm_\<alpha>)

subsection {* @{term ahm_empty} *}

lemma ahm_invar_aux_new_array:
  assumes "n > 1"
  shows "ahm_invar_aux 0 (new_array [] n)"
proof -
  have "foldl (\<lambda>b (k, v). b + length v) 0 (zip [0..<n] (replicate n [])) = 0"
    by(induct n)(simp_all add: replicate_Suc_conv_snoc del: replicate_Suc)
  with assms show ?thesis by(simp add: ahm_invar_aux_def array_foldl_new_array)
qed

lemma ahm_invar_new_hashmap_with:
  "n > 1 \<Longrightarrow> ahm_invar (new_hashmap_with n)"
by(auto simp add: ahm_invar_def new_hashmap_with_def intro: ahm_invar_aux_new_array)

lemma ahm_\<alpha>_new_hashmap_with:
  "n > 1 \<Longrightarrow> ahm_\<alpha> (new_hashmap_with n) = empty"
by(simp add: new_hashmap_with_def bounded_hashcode_bounds fun_eq_iff)

lemma ahm_invar_ahm_empty [simp]: "ahm_invar (ahm_empty ())"
using def_hashmap_size[where ?'a = 'a]
by(auto intro: ahm_invar_new_hashmap_with simp add: ahm_empty_def)

lemma ahm_empty_correct [simp]: "ahm_\<alpha> (ahm_empty ()) = Map.empty"
using def_hashmap_size[where ?'a = 'a]
by(auto intro: ahm_\<alpha>_new_hashmap_with simp add: ahm_empty_def)

lemma ahm_empty_impl: "map_empty ahm_\<alpha> ahm_invar ahm_empty"
by(unfold_locales)(auto)

subsection {* @{term "ahm_lookup"} *}

lemma ahm_lookup_impl: "map_lookup ahm_\<alpha> ahm_invar ahm_lookup"
by(unfold_locales)(simp add: ahm_lookup_def)

subsection {* @{term "ahm_iteratei"} *}

lemma ahm_iteratei_aux_impl:
  assumes invar_m: "ahm_invar_aux n m"
  shows "map_iterator (ahm_iteratei_aux m) (ahm_\<alpha>_aux m)"
proof -
  obtain ms where m_eq[simp]: "m = Array ms" by (cases m)

  from ahm_invar_distinct_fst_concatD[of n ms] invar_m
  have dist: "distinct (map fst (concat ms))" by simp

  show "map_iterator (ahm_iteratei_aux m) (ahm_\<alpha>_aux m)" 
    using  set_iterator_foldli_correct[of "concat ms"] dist
    by (simp add: ahm_\<alpha>_aux_conv_map_of_concat[OF invar_m[unfolded m_eq]]
                  ahm_iteratei_aux_def map_to_set_map_of[OF dist] distinct_map)
qed 

lemma ahm_iteratei_correct:
  assumes invar_hm: "ahm_invar hm"
  shows "map_iterator (ahm_iteratei hm) (ahm_\<alpha> hm)"
proof -
  obtain A n where hm_eq [simp]: "hm = HashMap A n" by(cases hm)

  from ahm_iteratei_aux_impl[of n A] invar_hm
    show map_it: "map_iterator (ahm_iteratei hm) (ahm_\<alpha> hm)" by simp 
qed

lemma ahm_iteratei_aux_code [code]:
  "ahm_iteratei_aux a c f \<sigma> = a_idx_it.idx_iteratei a c (\<lambda>x. foldli x c f) \<sigma>"
proof(cases a)
  case (Array xs)[simp]

  have "ahm_iteratei_aux a c f \<sigma> = foldli (concat xs) c f \<sigma>" by simp
  also have "\<dots> = foldli xs c (\<lambda>x. foldli x c f) \<sigma>" by (simp add: foldli_concat)
  thm a_idx_it.idx_iteratei_correct
  also have "\<dots> = a_idx_it.idx_iteratei a c (\<lambda>x. foldli x c f) \<sigma>"
    by (simp add: a_idx_it.idx_iteratei_correct)
  finally show ?thesis .
qed
subsection {* @{term "ahm_rehash"} *}

lemma array_length_ahm_rehash_aux':
  "array_length (ahm_rehash_aux' n kv a) = array_length a"
by(simp add: ahm_rehash_aux'_def Let_def)

lemma ahm_rehash_aux'_preserves_ahm_invar_aux:
  assumes inv: "ahm_invar_aux n a"
  and fresh: "k \<notin> fst ` set (array_get a (bounded_hashcode (array_length a) k))"
  shows "ahm_invar_aux (Suc n) (ahm_rehash_aux' (array_length a) (k, v) a)"
  (is "ahm_invar_aux _ ?a")
proof(rule ahm_invar_auxI)
  fix h
  assume "h < array_length ?a"
  hence hlen: "h < array_length a" by(simp add: array_length_ahm_rehash_aux')
  with inv have bucket: "bucket_ok (array_length a) h (array_get a h)"
    and dist: "distinct (map fst (array_get a h))"
    by(auto elim: ahm_invar_auxE)
  let ?h = "bounded_hashcode (array_length a) k"
  from hlen bucket show "bucket_ok (array_length ?a) h (array_get ?a h)"
    by(cases "h = ?h")(auto simp add: ahm_rehash_aux'_def Let_def array_length_ahm_rehash_aux' array_get_array_set_other dest: bucket_okD intro!: bucket_okI)
  from dist hlen fresh
  show "distinct (map fst (array_get ?a h))"
    by(cases "h = ?h")(auto simp add: ahm_rehash_aux'_def Let_def array_get_array_set_other)
next
  let ?f = "\<lambda>n kvs. n + length kvs"
  { fix n :: nat and xs :: "('a \<times> 'b) list list"
    have "foldl ?f n xs = n + foldl ?f 0 xs"
      by(induct xs arbitrary:  rule: rev_induct) simp_all }
  note fold = this
  let ?h = "bounded_hashcode (array_length a) k"

  obtain xs where a [simp]: "a = Array xs" by(cases a)
  from inv have [simp]: "bounded_hashcode (length xs) k < length xs"
    by(simp add: ahm_invar_aux_def bounded_hashcode_bounds)
  have xs: "xs = take ?h xs @ (xs ! ?h) # drop (Suc ?h) xs" by(simp add: nth_drop')
  from inv have "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a"
    by(auto elim: ahm_invar_auxE)
  hence "n = foldl ?f 0 (take ?h xs) + length (xs ! ?h) + foldl ?f 0 (drop (Suc ?h) xs)"
    by(simp add: array_foldl_foldl)(subst xs, simp, subst (1 2 3 4) fold, simp)
  thus "Suc n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 ?a"
    by(simp add: ahm_rehash_aux'_def Let_def array_foldl_foldl foldl_list_update)(subst (1 2 3 4) fold, simp)
next
  from inv have "1 < array_length a" by(auto elim: ahm_invar_auxE)
  thus "1 < array_length ?a" by(simp add: array_length_ahm_rehash_aux')
qed

declare [[coercion_enabled = false]]

lemma ahm_rehash_aux_correct:
  fixes a :: "(('key :: hashable) \<times> 'val) list array"
  assumes inv: "ahm_invar_aux n a"
  and "sz > 1"
  shows "ahm_invar_aux n (ahm_rehash_aux a sz)" (is "?thesis1")
  and "ahm_\<alpha>_aux (ahm_rehash_aux a sz) = ahm_\<alpha>_aux a" (is "?thesis2")
proof -
  (*interpret ahm!: map_iterator "ahm_\<alpha>_aux" "ahm_invar_aux n" "ahm_iteratei_aux"
    by(rule ahm_iteratei_aux_impl)*)
  let ?a = "ahm_rehash_aux a sz"
  let ?I = "\<lambda>it a'. ahm_invar_aux (n - card it) a' \<and> array_length a' = sz \<and> (\<forall>k. if k \<in> it then ahm_\<alpha>_aux a' k = None else ahm_\<alpha>_aux a' k = ahm_\<alpha>_aux a k)"
  have "?I {} ?a \<or> (\<exists>it\<subseteq>dom (ahm_\<alpha>_aux a). it \<noteq> {} \<and> \<not> True \<and> ?I it ?a)"
    unfolding ahm_rehash_aux_def

  proof (rule map_iterator_rule_P[OF ahm_iteratei_aux_impl[OF inv], where
      c = "\<lambda>_. True" and f="ahm_rehash_aux' sz" and ?\<sigma>0.0 = "new_array [] sz"
      and I="?I"]
    )

    from inv have "card (dom (ahm_\<alpha>_aux a)) = n" by(rule ahm_invar_aux_card_dom_ahm_\<alpha>_auxD)
    moreover from `1 < sz` have "ahm_invar_aux 0 (new_array ([] :: ('key \<times> 'val) list) sz)"
      by(rule ahm_invar_aux_new_array)
    moreover {
      fix k
      assume "k \<notin> dom (ahm_\<alpha>_aux a)"
      hence "ahm_\<alpha>_aux a k = None" by auto
      moreover have "bounded_hashcode sz k < sz" using `1 < sz`
        by(simp add: bounded_hashcode_bounds)
      ultimately have "ahm_\<alpha>_aux (new_array [] sz) k = ahm_\<alpha>_aux a k" by simp }
    ultimately show "?I (dom (ahm_\<alpha>_aux a)) (new_array [] sz)"
      by(auto simp add: bounded_hashcode_bounds[OF `1 < sz`])
  next
    fix k :: 'key
      and v :: 'val
      and it a'
    assume "k \<in> it" "ahm_\<alpha>_aux a k = Some v" 
      and it_sub: "it \<subseteq> dom (ahm_\<alpha>_aux a)"
      and I: "?I it a'"
    from I have inv': "ahm_invar_aux (n - card it) a'" 
      and a'_eq_a: "\<And>k. k \<notin> it \<Longrightarrow> ahm_\<alpha>_aux a' k = ahm_\<alpha>_aux a k" 
      and a'_None: "\<And>k. k \<in> it \<Longrightarrow> ahm_\<alpha>_aux a' k = None"
      and [simp]: "sz = array_length a'" by(auto split: split_if_asm)
    from it_sub finite_dom_ahm_\<alpha>_aux[OF inv] have "finite it" by(rule finite_subset)
    moreover with `k \<in> it` have "card it > 0" by(auto simp add: card_gt_0_iff)
    moreover from finite_dom_ahm_\<alpha>_aux[OF inv] it_sub
    have "card it \<le> card (dom (ahm_\<alpha>_aux a))" by(rule card_mono)
    moreover have "\<dots> = n" using inv
      by(simp add: ahm_invar_aux_card_dom_ahm_\<alpha>_auxD)
    ultimately have "n - card (it - {k}) = (n - card it) + 1" using `k \<in> it` by auto
    moreover from `k \<in> it` have "ahm_\<alpha>_aux a' k = None" by(rule a'_None)
    hence "k \<notin> fst ` set (array_get a' (bounded_hashcode (array_length a') k))"
      by(simp add: map_of_eq_None_iff)
    ultimately have "ahm_invar_aux (n - card (it - {k})) (ahm_rehash_aux' sz (k, v) a')"
      using inv' by(auto intro: ahm_rehash_aux'_preserves_ahm_invar_aux)
    moreover have "array_length (ahm_rehash_aux' sz (k, v) a') = sz"
      by(simp add: array_length_ahm_rehash_aux')
    moreover {
      fix k'
      assume "k' \<in> it - {k}"
      with bounded_hashcode_bounds[OF `1 < sz`, of k'] a'_None[of k']
      have "ahm_\<alpha>_aux (ahm_rehash_aux' sz (k, v) a') k' = None"
        by(cases "bounded_hashcode sz k = bounded_hashcode sz k'")(auto simp add: array_get_array_set_other ahm_rehash_aux'_def Let_def)
    } moreover {
      fix k'
      assume "k' \<notin> it - {k}"
      with bounded_hashcode_bounds[OF `1 < sz`, of k'] bounded_hashcode_bounds[OF `1 < sz`, of k] a'_eq_a[of k'] `k \<in> it`
      have "ahm_\<alpha>_aux (ahm_rehash_aux' sz (k, v) a') k' = ahm_\<alpha>_aux a k'"
        unfolding ahm_rehash_aux'_def Let_def using `ahm_\<alpha>_aux a k = Some v`
        by(cases "bounded_hashcode sz k = bounded_hashcode sz k'")(case_tac [!] "k' = k", simp_all add: array_get_array_set_other) }
    ultimately show "?I (it - {k}) (ahm_rehash_aux' sz (k, v) a')" by simp
  qed auto
  thus ?thesis1 ?thesis2 unfolding ahm_rehash_aux_def
    by(auto intro: ext)
qed

lemma ahm_rehash_correct:
  fixes hm :: "('key :: hashable, 'val) hashmap"
  assumes inv: "ahm_invar hm"
  and "sz > 1"
  shows "ahm_invar (ahm_rehash hm sz)" "ahm_\<alpha> (ahm_rehash hm sz) = ahm_\<alpha> hm"
using assms
by -(case_tac [!] hm, auto intro: ahm_rehash_aux_correct)

subsection {* @{term ahm_update} *}

lemma ahm_update_aux_correct:
  assumes inv: "ahm_invar hm"
  shows "ahm_invar (ahm_update_aux hm k v)" (is ?thesis1)
  and "ahm_\<alpha> (ahm_update_aux hm k v) = (ahm_\<alpha> hm)(k \<mapsto> v)" (is ?thesis2)
proof -
  obtain a n where [simp]: "hm = HashMap a n" by(cases hm)

  let ?h = "bounded_hashcode (array_length a) k"
  let ?a' = "array_set a ?h (AList.update k v (array_get a ?h))"
  let ?n' = "if map_of (array_get a ?h) k = None then n + 1 else n"

  have "ahm_invar (HashMap ?a' ?n')" unfolding ahm_invar.simps
  proof(rule ahm_invar_auxI)
    fix h
    assume "h < array_length ?a'"
    hence "h < array_length a" by simp
    with inv have "bucket_ok (array_length a) h (array_get a h)"
      by(auto elim: ahm_invar_auxE)
    thus "bucket_ok (array_length ?a') h (array_get ?a' h)"
      using `h < array_length a`
      apply(cases "h = bounded_hashcode (array_length a) k")
      apply(fastforce intro!: bucket_okI simp add: dom_update array_get_array_set_other dest: bucket_okD del: imageE elim: imageE)+
      done
    from `h < array_length a` inv have "distinct (map fst (array_get a h))"
      by(auto elim: ahm_invar_auxE)
    with `h < array_length a`
    show "distinct (map fst (array_get ?a' h))"
      by(cases "h = bounded_hashcode (array_length a) k")(auto simp add: array_get_array_set_other intro: distinct_update)
  next
    obtain xs where a [simp]: "a = Array xs" by(cases a)

    let ?f = "\<lambda>n kvs. n + length kvs"
    { fix n :: nat and xs :: "('a \<times> 'b) list list"
      have "foldl ?f n xs = n + foldl ?f 0 xs"
        by(induct xs arbitrary:  rule: rev_induct) simp_all }
    note fold = this

    from inv have [simp]: "bounded_hashcode (length xs) k < length xs"
      by(simp add: ahm_invar_aux_def bounded_hashcode_bounds)
    have xs: "xs = take ?h xs @ (xs ! ?h) # drop (Suc ?h) xs" by(simp add: nth_drop')
    from inv have "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a"
      by(auto elim: ahm_invar_auxE)
    hence "n = foldl ?f 0 (take ?h xs) + length (xs ! ?h) + foldl ?f 0 (drop (Suc ?h) xs)"
      by(simp add: array_foldl_foldl)(subst xs, simp, subst (1 2 3 4) fold, simp)
    thus "?n' = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 ?a'"
      apply(simp add: ahm_rehash_aux'_def Let_def array_foldl_foldl foldl_list_update map_of_eq_None_iff)
      apply(subst (1 2 3 4 5 6 7 8) fold)
      apply(simp add: length_update)
      done
  next
    from inv have "1 < array_length a" by(auto elim: ahm_invar_auxE)
    thus "1 < array_length ?a'" by simp
  qed
  moreover have "ahm_\<alpha> (ahm_update_aux hm k v) = ahm_\<alpha> hm(k \<mapsto> v)"
  proof
    fix k'
    from inv have "1 < array_length a" by(auto elim: ahm_invar_auxE)
    with bounded_hashcode_bounds[OF this, of k]
    show "ahm_\<alpha> (ahm_update_aux hm k v) k' = (ahm_\<alpha> hm(k \<mapsto> v)) k'"
      by(cases "bounded_hashcode (array_length a) k = bounded_hashcode (array_length a) k'")(auto simp add: Let_def update_conv array_get_array_set_other)
  qed
  ultimately show ?thesis1 ?thesis2 by(simp_all add: Let_def)
qed

lemma ahm_update_correct:
  assumes inv: "ahm_invar hm"
  shows "ahm_invar (ahm_update k v hm)"
  and "ahm_\<alpha> (ahm_update k v hm) = (ahm_\<alpha> hm)(k \<mapsto> v)"
using assms
by(simp_all add: ahm_update_def Let_def ahm_rehash_correct ahm_update_aux_correct)

lemma ahm_update_impl:
  "map_update ahm_\<alpha> ahm_invar ahm_update"
by(unfold_locales)(simp_all add: ahm_update_correct)

subsection {* @{term "ahm_delete"} *}

lemma ahm_delete_correct:
  assumes inv: "ahm_invar hm"
  shows "ahm_invar (ahm_delete k hm)" (is "?thesis1")
  and "ahm_\<alpha> (ahm_delete k hm) = (ahm_\<alpha> hm) |` (- {k})" (is "?thesis2")
proof -
  obtain a n where hm [simp]: "hm = HashMap a n" by(cases hm)

  let ?h = "bounded_hashcode (array_length a) k"
  let ?a' = "array_set a ?h (AList.delete k (array_get a ?h))"
  let ?n' = "if map_of (array_get a (bounded_hashcode (array_length a) k)) k = None then n else n - 1"
  
  have "ahm_invar_aux ?n' ?a'"
  proof(rule ahm_invar_auxI)
    fix h
    assume "h < array_length ?a'"
    hence "h < array_length a" by simp
    with inv have "bucket_ok (array_length a) h (array_get a h)"
      and "1 < array_length a" 
      and "distinct (map fst (array_get a h))" by(auto elim: ahm_invar_auxE)
    thus "bucket_ok (array_length ?a') h (array_get ?a' h)"
      and "distinct (map fst (array_get ?a' h))"
      using bounded_hashcode_bounds[of "array_length a" k] 
      by-(case_tac [!] "h = bounded_hashcode (array_length a) k", auto simp add: array_get_array_set_other set_delete_conv intro!: bucket_okI dest: bucket_okD intro: distinct_delete)
  next
    obtain xs where a [simp]: "a = Array xs" by(cases a)

    let ?f = "\<lambda>n kvs. n + length kvs"
    { fix n :: nat and xs :: "('a \<times> 'b) list list"
      have "foldl ?f n xs = n + foldl ?f 0 xs"
        by(induct xs arbitrary:  rule: rev_induct) simp_all }
    note fold = this

    from inv have [simp]: "bounded_hashcode (length xs) k < length xs"
      by(simp add: ahm_invar_aux_def bounded_hashcode_bounds)
    from inv have "distinct (map fst (array_get a ?h))" by(auto elim: ahm_invar_auxE)
    moreover
    have xs: "xs = take ?h xs @ (xs ! ?h) # drop (Suc ?h) xs" by(simp add: nth_drop')
    from inv have "n = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 a"
      by(auto elim: ahm_invar_auxE)
    hence "n = foldl ?f 0 (take ?h xs) + length (xs ! ?h) + foldl ?f 0 (drop (Suc ?h) xs)"
      by(simp add: array_foldl_foldl)(subst xs, simp, subst (1 2 3 4) fold, simp)
    ultimately show "?n' = array_foldl (\<lambda>_ n kvs. n + length kvs) 0 ?a'"
      apply(simp add: array_foldl_foldl foldl_list_update map_of_eq_None_iff)
      apply(subst (1 2 3 4 5 6 7 8) fold)
      apply(auto simp add: length_distinct in_set_conv_nth)
      done
  next
    from inv show "1 < array_length ?a'" by(auto elim: ahm_invar_auxE)
  qed
  thus "?thesis1" by(auto simp add: Let_def)

  have "ahm_\<alpha>_aux ?a' = ahm_\<alpha>_aux a |` (- {k})"
  proof
    fix k' :: 'a
    from inv have "bounded_hashcode (array_length a) k < array_length a"
      by(auto elim: ahm_invar_auxE simp add: bounded_hashcode_bounds)
    thus "ahm_\<alpha>_aux ?a' k' = (ahm_\<alpha>_aux a |` (- {k})) k'"
      by(cases "?h = bounded_hashcode (array_length a) k'")(auto simp add: restrict_map_def array_get_array_set_other delete_conv)
  qed
  thus ?thesis2 by(simp add: Let_def)
qed

lemma ahm_delete_impl:
  "map_delete ahm_\<alpha> ahm_invar ahm_delete"
by(unfold_locales)(blast intro: ahm_delete_correct)+

hide_const (open) HashMap ahm_empty bucket_ok ahm_invar ahm_\<alpha> ahm_lookup
  ahm_iteratei ahm_rehash hm_grow ahm_filled ahm_update ahm_delete
hide_type (open) hashmap

end
