(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
header {* \isaheader{Implementation of a trie with explicit invariants} *}
theory Trie_Impl imports
  "../../Lib/Assoc_List"
begin

subsection {* Type definition and primitive operations *}

datatype ('key, 'val) trie = Trie "'val option" "('key \<times> ('key, 'val) trie) list"

lemma trie_induct [case_names Trie, induct type]:
  "(\<And>vo kvs. (\<And>k t. (k, t) \<in> set kvs \<Longrightarrow> P t) \<Longrightarrow> P (Trie vo kvs)) \<Longrightarrow> P t"
apply(induction_schema)
  apply pat_completeness
 apply(lexicographic_order)
done

definition empty :: "('key, 'val) trie"
where "empty = Trie None []"

fun lookup :: "('key, 'val) trie \<Rightarrow> 'key list \<Rightarrow> 'val option"
where
  "lookup (Trie vo _) [] = vo"
| "lookup (Trie _ ts) (k#ks) = (case map_of ts k of None \<Rightarrow> None | Some t \<Rightarrow> lookup t ks)"

fun update :: "('key, 'val) trie \<Rightarrow> 'key list \<Rightarrow> 'val \<Rightarrow> ('key, 'val) trie"
where
  "update (Trie vo ts) [] v = Trie (Some v) ts"
| "update (Trie vo ts) (k#ks) v = Trie vo (Assoc_List.update_with_aux (Trie None []) k (\<lambda>t. update t ks v) ts)"

primrec isEmpty :: "('key, 'val) trie \<Rightarrow> bool"
where "isEmpty (Trie vo ts) \<longleftrightarrow> vo = None \<and> ts = []"

fun delete :: "('key, 'val) trie \<Rightarrow> 'key list \<Rightarrow> ('key, 'val) trie"
where
  "delete (Trie vo ts) [] = Trie None ts"
| "delete (Trie vo ts) (k#ks) =
   (case map_of ts k of None \<Rightarrow> Trie vo ts
                    | Some t \<Rightarrow> let t' = delete t ks 
                                in if isEmpty t'
                                   then Trie vo (Assoc_List.delete_aux k ts)
                                   else Trie vo (AList.update k t' ts))"

fun trie_invar :: "('key, 'val) trie \<Rightarrow> bool"
where "trie_invar (Trie vo kts) = (distinct (map fst kts) \<and> (\<forall>(k, t) \<in> set kts. \<not> isEmpty t \<and> trie_invar t))"

fun iteratei_postfixed :: "'key list \<Rightarrow> ('key, 'val) trie \<Rightarrow> 
    ('key list \<times> 'val, '\<sigma>) set_iterator"
where
  "iteratei_postfixed ks (Trie vo ts) c f \<sigma> =
   (if c \<sigma> 
    then foldli ts c (\<lambda>(k, t) \<sigma>. iteratei_postfixed (k # ks) t c f \<sigma>)
           (case vo of None \<Rightarrow> \<sigma> | Some v \<Rightarrow> f (ks, v) \<sigma>) 
    else \<sigma>)"

definition iteratei :: "('key, 'val) trie \<Rightarrow> ('key list \<times> 'val, '\<sigma>) set_iterator"
where "iteratei t c f \<sigma> = iteratei_postfixed [] t c f \<sigma>"

lemma iteratei_postfixed_interrupt:
  "\<not> c \<sigma> \<Longrightarrow> iteratei_postfixed ks t c f \<sigma> = \<sigma>"
by(cases t) simp

lemma iteratei_interrupt:
  "\<not> c \<sigma> \<Longrightarrow> iteratei t c f \<sigma> = \<sigma>"
unfolding iteratei_def by (simp add: iteratei_postfixed_interrupt)

lemma iteratei_postfixed_alt_def :
  "iteratei_postfixed ks ((Trie vo ts)::('key, 'val) trie) =
   (set_iterator_union 
     (option_case set_iterator_emp (\<lambda>v. set_iterator_sng (ks, v)) vo) 
     (set_iterator_image snd
     (set_iterator_product (foldli ts) 
        (\<lambda>(k, t'). iteratei_postfixed (k # ks) t'))
     ))"
proof -
  have aux: "\<And>c f. (\<lambda>(k, t). iteratei_postfixed (k # ks) t c f) =
              (\<lambda>a. iteratei_postfixed (fst a # ks) (snd a) c f)"
    by auto

  show ?thesis
    apply (rule ext)+ apply (rename_tac c f \<sigma>)
    apply (simp add: set_iterator_product_def set_iterator_image_filter_def
                     set_iterator_union_def set_iterator_sng_def set_iterator_image_alt_def
                     prod_case_beta set_iterator_emp_def 
            split: option.splits)
    apply (simp add: aux)
  done
qed

subsection {* Lookup simps *}

lemma lookup_eq_Some_iff :
assumes invar: "trie_invar ((Trie vo kvs) :: ('key, 'val) trie)"
shows "lookup (Trie vo kvs) ks = Some v \<longleftrightarrow>
    (ks = [] \<and> vo = Some v) \<or>
    (\<exists>k t ks'. ks = k # ks' \<and> 
        (k, t) \<in> set kvs \<and> lookup t ks' = Some v)"
proof (cases ks)
  case Nil thus ?thesis by simp
next
  case (Cons k ks')
  note ks_eq[simp] = Cons

  show ?thesis
  proof (cases "map_of kvs k")
    case None thus ?thesis 
      apply (simp)
      apply (auto simp add: map_of_eq_None_iff image_iff Ball_def)
    done
  next
    case (Some t') note map_eq = this
    from invar have dist_kvs: "distinct (map fst kvs)" by simp

    from map_of_eq_Some_iff[OF dist_kvs, of k] map_eq
    show ?thesis by simp metis
  qed
qed

lemma lookup_eq_None_iff :
assumes invar: "trie_invar ((Trie vo kvs) :: ('key, 'val) trie)"
shows "lookup (Trie vo kvs) ks = None \<longleftrightarrow>
    (ks = [] \<and> vo = None) \<or>
    (\<exists>k ks'. ks = k # ks' \<and> (\<forall>t. (k, t) \<in> set kvs \<longrightarrow> lookup t ks' = None))"
using lookup_eq_Some_iff[of vo kvs ks, OF invar]
  apply (cases ks)
    apply auto[]
  apply (auto split: option.split)
    apply (metis option.simps(3) weak_map_of_SomeI)
    apply (metis option.exhaust)
    apply (metis option.exhaust)
done

subsection {* The empty trie *}

lemma trie_invar_empty [simp, intro!]: "trie_invar empty"
by(simp add: empty_def)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
proof
  fix ks show "lookup empty ks = Map.empty ks"
    by(cases ks)(auto simp add: empty_def)
qed

lemma lookup_empty' [simp]:
  "lookup (Trie None []) ks = None"
by(simp add: lookup_empty[unfolded empty_def])

subsection {* Emptyness check *}

lemma isEmpty_conv:
  "isEmpty ts \<longleftrightarrow> ts = Trie None []"
by(cases ts)(simp)

lemma update_not_empty: "\<not> isEmpty (update t ks v)"
apply(cases t)
apply(rename_tac kvs)
apply(cases ks)
apply(case_tac [2] kvs)
apply auto
done

lemma isEmpty_lookup_empty:
  "trie_invar t \<Longrightarrow> isEmpty t \<longleftrightarrow> lookup t = Map.empty"
proof(induct t)
  case (Trie vo kvs)
  thus ?case
    apply(cases kvs)
    apply(auto simp add: fun_eq_iff elim: allE[where x="[]"])
    apply(erule meta_allE)+
    apply(erule meta_impE)
    apply(rule disjI1)
    apply(fastforce intro: exI[where x="a # b", standard])+
    done
qed

subsection {* Trie update *}

lemma lookup_update:
  "lookup (update t ks v) ks' = (if ks = ks' then Some v else lookup t ks')"
proof(induct t ks v arbitrary: ks' rule: update.induct)
  case (1 vo ts v)
  show ?case by(fastforce simp add: neq_Nil_conv dest: not_sym)
next
  case (2 vo ts k ks v)
  note IH = `\<And>t ks'. lookup (update t ks v) ks' = (if ks = ks' then Some v else lookup t ks')`
  show ?case by(cases ks')(auto simp add: map_of_update_with_aux IH split: option.split)
qed

lemma lookup_update':
  "lookup (update t ks v) = (lookup t)(ks \<mapsto> v)"
by(rule ext)(simp add: lookup_update)


lemma trie_invar_update: "trie_invar t \<Longrightarrow> trie_invar (update t ks v)"
by(induct t ks v rule: update.induct)(auto simp add: set_update_with_aux update_not_empty split: option.splits)
 
subsection {* Trie removal *}

lemma delete_eq_empty_lookup_other_fail:
  "\<lbrakk> delete t ks = Trie None []; ks' \<noteq> ks \<rbrakk> \<Longrightarrow> lookup t ks' = None"
proof(induct t ks arbitrary: ks' rule: delete.induct)
  case (1 vo ts)
  thus ?case by(auto simp add: neq_Nil_conv)
next
  case (2 vo ts k ks)
  note IH = `\<And>t ks'. \<lbrakk>map_of ts k = Some t; delete t ks = Trie None []; ks' \<noteq> ks\<rbrakk>
           \<Longrightarrow> lookup t ks' = None`
  note ks' = `ks' \<noteq> k # ks`
  note empty = `delete (Trie vo ts) (k # ks) = Trie None []`
  show ?case
  proof(cases "map_of ts k")
    case (Some t)
    from Some empty show ?thesis
    proof(cases ks')
      case (Cons k' ks'')
      with Some empty ks' show ?thesis
      proof(cases "k' = k")
        case False
        from Some Cons empty have "delete_aux k ts = []"
          by(clarsimp simp add: Let_def split: split_if_asm)
        with False have "map_of ts k' = None"
          by(cases "map_of ts k'")(auto dest: map_of_is_SomeD simp add: delete_aux_eq_Nil_conv)
        thus ?thesis using False Some Cons empty by simp
      next
        case True
        with Some empty ks' Cons show ?thesis
          by(clarsimp simp add: IH Let_def isEmpty_conv split: split_if_asm)
      qed
    qed(simp add: Let_def split: split_if_asm)
  next
    case None thus ?thesis using empty by simp
  qed
qed

lemma lookup_delete:
  "trie_invar t \<Longrightarrow> lookup (delete t ks) ks' = (if ks = ks' then None else lookup t ks')"
proof(induct t ks arbitrary: ks' rule: delete.induct)
  case (1 vo ts)
  show ?case by(fastforce dest: not_sym simp add: neq_Nil_conv)
next
  case (2 vo ts k ks)
  note IH = `\<And>t ks'. \<lbrakk> map_of ts k = Some t; trie_invar t \<rbrakk>
           \<Longrightarrow> lookup (delete t ks) ks' = (if ks = ks' then None else lookup t ks')`
  note invar = `trie_invar (Trie vo ts)`
  show ?case
  proof(cases ks')
    case Nil thus ?thesis
      by(simp split: option.split add: Let_def)
  next
    case (Cons k' ks'')[simp]
    show ?thesis
    proof(cases "k' = k")
      case False thus ?thesis using invar
        by(auto simp add: Let_def update_conv' map_of_delete_aux split: option.split)
    next
      case True[simp]
      show ?thesis
      proof(cases "map_of ts k")
        case None thus ?thesis by simp
      next
        case (Some t)
        thus ?thesis 
        proof(cases "isEmpty (delete t ks)")
          case True
          with Some invar show ?thesis
            by(auto simp add: map_of_delete_aux isEmpty_conv dest: delete_eq_empty_lookup_other_fail)
        next
          case False
          thus ?thesis using Some IH[of t ks''] invar by(auto simp add: update_conv')
        qed
      qed
    qed
  qed
qed

lemma lookup_delete':
  "trie_invar t \<Longrightarrow> lookup (delete t ks) = (lookup t)(ks := None)"
by(rule ext)(simp add: lookup_delete)

lemma trie_invar_delete:
  "trie_invar t \<Longrightarrow> trie_invar (delete t ks)"
proof(induct t ks rule: delete.induct)
  case (1 vo ts)
  thus ?case by simp
next
  case (2 vo ts k ks)
  note invar = `trie_invar (Trie vo ts)`
  show ?case
  proof(cases "map_of ts k")
    case None
    thus ?thesis using invar by simp
  next
    case (Some t)
    with invar have "trie_invar t" by auto
    with Some have "trie_invar (delete t ks)" by(rule 2)
    from invar Some have distinct: "distinct (map fst ts)" "\<not> isEmpty t" by auto
    show ?thesis
    proof(cases "isEmpty (delete t ks)")
      case True
      { fix k' t'
        assume k't': "(k', t') \<in> set (delete_aux k ts)"
        with distinct have "map_of (delete_aux k ts) k' = Some t'" by simp
        hence "map_of ts k' = Some t'" using distinct
          by (auto 
            simp del: map_of_eq_Some_iff map_upd_eq_restrict
            simp add: map_of_delete_aux 
            split: split_if_asm)
        with invar  have "\<not> isEmpty t' \<and> trie_invar t'" by auto }
      with invar have "trie_invar (Trie vo (delete_aux k ts))" by auto
      thus ?thesis using True Some by(simp)
    next
      case False
      { fix k' t'
        assume k't':"(k', t') \<in> set (AList.update k (delete t ks) ts)"
        hence "map_of (AList.update k (delete t ks) ts) k' = Some t'"
          using invar by(auto simp add: distinct_update)
        hence eq: "((map_of ts)(k \<mapsto> delete t ks)) k' = Some t'" unfolding update_conv .
        have "\<not> isEmpty t' \<and> trie_invar t'"
        proof(cases "k' = k")
          case True
          with eq have "t' = delete t ks" by simp
          with `trie_invar (delete t ks)` False
          show ?thesis by simp
        next
          case False
          with eq distinct have "(k', t') \<in> set ts" by simp
          with invar show ?thesis by auto
        qed }
      thus ?thesis using Some invar False by(auto simp add: distinct_update)
    qed
  qed
qed

subsection {* Domain of a trie *}

lemma dom_lookup: 
  "dom (lookup (Trie vo kts)) = 
  (\<Union>k\<in>dom (map_of kts). Cons k ` dom (lookup (the (map_of kts k)))) \<union>
  (if vo = None then {} else {[]})"
unfolding dom_def
apply(rule sym)
apply(safe)
  apply simp
 apply(clarsimp simp add: split_if_asm)
apply(case_tac x)
apply(auto split: option.split_asm)
done

lemma finite_dom_trie_lookup:
  "finite (dom (lookup t))"
proof(induct t)
  case (Trie vo kts)
  have "finite (\<Union>k\<in>dom (map_of kts). Cons k ` dom (lookup (the (map_of kts k))))"
  proof(rule finite_UN_I)
    show "finite (dom (map_of kts))" by(rule finite_dom_map_of)
  next
    fix k
    assume "k \<in> dom (map_of kts)"
    then obtain v where "(k, v) \<in> set kts" "map_of kts k = Some v" by(auto dest: map_of_SomeD)
    hence "finite (dom (lookup (the (map_of kts k))))" by simp(rule Trie)
    thus "finite (Cons k ` dom (lookup (the (map_of kts k))))" by(rule finite_imageI)
  qed
  thus ?case by(simp add: dom_lookup)
qed

lemma dom_lookup_empty_conv: "trie_invar t \<Longrightarrow> dom (lookup t) = {} \<longleftrightarrow> isEmpty t"
proof(induct t)
  case (Trie vo kvs)
  show ?case
  proof
    assume dom: "dom (lookup (Trie vo kvs)) = {}"
    have "vo = None"
    proof(cases vo)
      case (Some v)
      hence "[] \<in> dom (lookup (Trie vo kvs))" by auto
      with dom have False by simp
      thus ?thesis ..
    qed
    moreover have "kvs = []"
    proof(cases kvs)
      case (Cons kt kvs')
      with `trie_invar (Trie vo kvs)`
      have "\<not> isEmpty (snd kt)" "trie_invar (snd kt)" by auto
      from Cons have "(fst kt, snd kt) \<in> set kvs" by simp
      hence "dom (lookup (snd kt)) = {} \<longleftrightarrow> isEmpty (snd kt)"
        using `trie_invar (snd kt)` by(rule Trie)
      with `\<not> isEmpty (snd kt)` have "dom (lookup (snd kt)) \<noteq> {}" by simp
      with dom Cons have False by(auto simp add: dom_lookup)
      thus ?thesis ..
    qed
    ultimately show "isEmpty (Trie vo kvs)" by simp
  next
    assume "isEmpty (Trie vo kvs)"
    thus "dom (lookup (Trie vo kvs)) = {}"
      by(simp add: lookup_empty[unfolded empty_def])
  qed
qed

subsection {* Interuptible iterator *}

lemma iteratei_postfixed_correct :
  assumes invar: "trie_invar (t :: ('key, 'val) trie)"
  shows "set_iterator ((iteratei_postfixed ks0 t)::('key list \<times> 'val, '\<sigma>) set_iterator)
           ((\<lambda>ksv. (rev (fst ksv) @ ks0, (snd ksv))) ` (map_to_set (lookup t)))"
using invar
proof (induct t arbitrary: ks0)
  case (Trie vo kvs)
  note ind_hyp = Trie(1)
  note invar = Trie(2)

  from invar 
  have dist_fst_kvs : "distinct (map fst kvs)"
   and dist_kvs: "distinct kvs"
   and invar_child: "\<And>k t. (k, t) \<in> set kvs \<Longrightarrow> trie_invar t"
  by (simp_all add: Ball_def distinct_map)

  -- "root iterator"
  def it_vo \<equiv> "(case vo of None \<Rightarrow> set_iterator_emp 
                        | Some v \<Rightarrow> set_iterator_sng (ks0, v)) :: 
                  ('key list \<times> 'val, '\<sigma>) set_iterator"
  def vo_S \<equiv> "case vo of None \<Rightarrow> {} | Some v \<Rightarrow> {(ks0, v)}"
  have it_vo_OK: "set_iterator it_vo vo_S"
    unfolding it_vo_def vo_S_def
    by (simp split: option.split 
             add: set_iterator_emp_correct set_iterator_sng_correct)

  -- "children iterator"
  def it_prod \<equiv> "(set_iterator_product (foldli kvs)
      (\<lambda>(k, y). iteratei_postfixed (k # ks0) y))::
          (('key \<times> ('key, 'val) trie) \<times> 'key list \<times> 'val, '\<sigma>) set_iterator"

    def it_prod_S \<equiv> "SIGMA kt:set kvs.
       (\<lambda>ksv. (rev (fst ksv) @ ((fst kt) # ks0), snd ksv)) `
       map_to_set (lookup (snd kt))"

  have it_prod_OK: "set_iterator it_prod it_prod_S"
  proof -
    from set_iterator_foldli_correct[OF dist_kvs]
    have it_foldli: "set_iterator (foldli kvs) (set kvs)" .

    { fix kt 
      assume kt_in: "kt \<in> set kvs"
      hence k_t_in: "(fst kt, snd kt) \<in> set kvs" by simp

      note ind_hyp [OF k_t_in, OF invar_child[OF k_t_in], of "fst kt # ks0"]
    } note it_child = this
       
    show ?thesis
      unfolding it_prod_def it_prod_S_def
      apply (rule set_iterator_product_correct [OF it_foldli])
      apply (insert it_child)
      apply (simp add: prod_case_beta)
    done
  qed

  have it_image_OK : "set_iterator (set_iterator_image snd it_prod) (snd ` it_prod_S)"
  proof (rule set_iterator_image_correct[OF it_prod_OK])
    from dist_fst_kvs
    have "\<And>k v1 v2. (k, v1) \<in> set kvs \<Longrightarrow> (k, v2) \<in> set kvs \<Longrightarrow> v1 = v2"
       by (induct kvs) (auto simp add: image_iff)
    thus "inj_on snd it_prod_S" 
      unfolding inj_on_def it_prod_S_def
      apply (simp add: image_iff Ball_def map_to_set_def)
      apply auto
    done
  qed auto

  -- "overall iterator"
  have it_all_OK: "set_iterator 
      ((iteratei_postfixed ks0 (Trie vo kvs)):: ('key list \<times> 'val, '\<sigma>) set_iterator)
     (vo_S \<union> snd ` it_prod_S)"
    unfolding iteratei_postfixed_alt_def 
       it_vo_def[symmetric]
       it_prod_def[symmetric]
  proof (rule set_iterator_union_correct [OF it_vo_OK it_image_OK])
    show "vo_S \<inter> snd ` it_prod_S = {}"
      unfolding vo_S_def it_prod_S_def
      by (simp split: option.split add: set_eq_iff image_iff)
  qed

  -- "rewrite result set"
  have it_set_rewr: "((\<lambda>ksv. (rev (fst ksv) @ ks0, snd ksv)) `
      map_to_set (lookup (Trie vo kvs))) = (vo_S \<union> snd ` it_prod_S)"
    (is "?ls = ?rs")
    apply (simp add: map_to_set_def lookup_eq_Some_iff[OF invar]
                     set_eq_iff image_iff vo_S_def it_prod_S_def Ball_def Bex_def)
    apply (simp split: option.split del: ex_simps add: ex_simps[symmetric])
    apply (intro allI impI iffI)
    apply auto[]
    apply (metis append_Cons append_Nil append_assoc rev.simps)
  done
    
  -- "done"
  show ?case
    unfolding it_set_rewr using it_all_OK by fast
qed

definition trie_reverse_key where
  "trie_reverse_key ksv = (rev (fst ksv), (snd ksv))"

lemma trie_reverse_key_alt_def[code] :
  "trie_reverse_key (ks, v) = (rev ks, v)"
unfolding trie_reverse_key_def by auto

lemma trie_reverse_key_reverse[simp] :
  "trie_reverse_key (trie_reverse_key ksv) = ksv"
by (simp add: trie_reverse_key_def)

lemma trie_iteratei_correct:
  assumes invar: "trie_invar (t :: ('key, 'val) trie)"
  shows "set_iterator ((iteratei t)::('key list \<times> 'val, '\<sigma>) set_iterator)
           (trie_reverse_key ` (map_to_set (lookup t)))"
unfolding trie_reverse_key_def[abs_def] iteratei_def[abs_def]
using iteratei_postfixed_correct [OF invar, of "[]"]
by simp

hide_const (open) empty isEmpty iteratei lookup update delete
hide_type (open) trie

end
