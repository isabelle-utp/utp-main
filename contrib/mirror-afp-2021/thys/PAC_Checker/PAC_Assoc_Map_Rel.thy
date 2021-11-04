theory PAC_Assoc_Map_Rel
  imports PAC_Map_Rel
begin

section \<open>Hash Map as association list\<close>

type_synonym ('k, 'v) hash_assoc = \<open>('k \<times> 'v) list\<close>

definition hassoc_map_rel_raw :: \<open>(('k, 'v) hash_assoc \<times> _) set\<close> where
  \<open>hassoc_map_rel_raw = br map_of (\<lambda>_. True)\<close>

abbreviation hassoc_map_assn :: \<open>('k \<Rightarrow> 'v option) \<Rightarrow> ('k, 'v) hash_assoc \<Rightarrow> assn\<close> where
  \<open>hassoc_map_assn \<equiv> pure (hassoc_map_rel_raw)\<close>

lemma hassoc_map_rel_raw_empty[simp]:
  \<open>([], m) \<in> hassoc_map_rel_raw \<longleftrightarrow> m = Map.empty\<close>
  \<open>(p, Map.empty) \<in> hassoc_map_rel_raw \<longleftrightarrow> p = []\<close>
  \<open>hassoc_map_assn Map.empty [] = emp\<close>
  by (auto simp: hassoc_map_rel_raw_def br_def pure_def)

definition hassoc_new :: \<open>('k, 'v) hash_assoc Heap\<close>where
  \<open>hassoc_new = return []\<close>

  lemma precise_hassoc_map_assn: \<open>precise hassoc_map_assn\<close>
    by (auto intro!: precise_pure)
     (auto simp: single_valued_def hassoc_map_rel_raw_def
      br_def)

  definition hassoc_isEmpty :: "('k \<times> 'v) list \<Rightarrow> bool Heap" where
   "hassoc_isEmpty ht \<equiv> return (length ht = 0)"


 interpretation hassoc: bind_map_empty hassoc_map_assn hassoc_new
    by unfold_locales
     (auto intro: precise_hassoc_map_assn
         simp: ent_refl_true hassoc_new_def
       intro!: return_cons_rule)


  interpretation hassoc: bind_map_is_empty hassoc_map_assn hassoc_isEmpty
    by unfold_locales
      (auto simp: precise_hassoc_map_assn hassoc_isEmpty_def ent_refl_true
       intro!: precise_pure return_cons_rule)

  definition "op_assoc_empty \<equiv> IICF_Map.op_map_empty"

  interpretation hassoc: map_custom_empty op_assoc_empty
    by unfold_locales (simp add: op_assoc_empty_def)


  lemmas [sepref_fr_rules] = hassoc.empty_hnr[folded op_assoc_empty_def]

  definition hassoc_update :: "'k \<Rightarrow> 'v \<Rightarrow> ('k, 'v) hash_assoc \<Rightarrow> ('k, 'v) hash_assoc Heap" where
   "hassoc_update k v ht = return ((k, v ) # ht)"

  lemma hassoc_map_assn_Cons:
     \<open>hassoc_map_assn (m) (p) \<Longrightarrow>\<^sub>A hassoc_map_assn (m(k \<mapsto> v)) ((k, v) # p) * true\<close>
     by (auto simp: hassoc_map_rel_raw_def pure_def br_def)

  interpretation hassoc: bind_map_update hassoc_map_assn hassoc_update
    by unfold_locales
     (auto intro!: return_cons_rule
      simp: hassoc_update_def hassoc_map_assn_Cons)


  definition hassoc_delete :: \<open>'k \<Rightarrow> ('k, 'v) hash_assoc \<Rightarrow> ('k, 'v) hash_assoc Heap\<close> where
    \<open>hassoc_delete k ht = return (filter (\<lambda>(a, b). a \<noteq> k) ht)\<close>

  lemma hassoc_map_of_filter_all:
    \<open>map_of p |` (- {k}) = map_of (filter (\<lambda>(a, b). a \<noteq> k) p)\<close>
    apply (induction p)
    apply (auto simp: restrict_map_def fun_eq_iff split: if_split)
    apply presburger+
    done

  lemma hassoc_map_assn_hassoc_delete: \<open><hassoc_map_assn m p> hassoc_delete k p <hassoc_map_assn (m |` (- {k}))>\<^sub>t\<close>
   by (auto simp: hassoc_delete_def hassoc_map_rel_raw_def pure_def br_def
           hassoc_map_of_filter_all
         intro!: return_cons_rule)

  interpretation hassoc: bind_map_delete hassoc_map_assn hassoc_delete
    by unfold_locales
     (auto intro: hassoc_map_assn_hassoc_delete)


  definition hassoc_lookup :: \<open>'k \<Rightarrow> ('k, 'v) hash_assoc \<Rightarrow> 'v option Heap\<close> where
    \<open>hassoc_lookup k ht = return (map_of ht k)\<close>

  lemma hassoc_map_assn_hassoc_lookup:
    \<open><hassoc_map_assn m p> hassoc_lookup k p <\<lambda>r. hassoc_map_assn m p * \<up> (r = m k)>\<^sub>t\<close>
     by (auto simp: hassoc_lookup_def hassoc_map_rel_raw_def pure_def br_def
             hassoc_map_of_filter_all
           intro!: return_cons_rule)

  interpretation hassoc: bind_map_lookup hassoc_map_assn hassoc_lookup
    by unfold_locales
     (rule hassoc_map_assn_hassoc_lookup)

  setup Locale_Code.open_block
  interpretation hassoc: gen_contains_key_by_lookup hassoc_map_assn hassoc_lookup
    by unfold_locales
  setup Locale_Code.close_block

  interpretation hassoc: bind_map_contains_key hassoc_map_assn hassoc.contains_key
    by unfold_locales


subsection \<open>Conversion from assoc to other map\<close>

definition hash_of_assoc_map where
\<open>hash_of_assoc_map xs = fold (\<lambda>(k, v) m. if m k \<noteq> None then m else m(k \<mapsto> v)) xs Map.empty\<close>

lemma map_upd_map_add_left:
  \<open>m(a  \<mapsto> b) ++ m' = m ++ (if a \<notin> dom m' then m'(a  \<mapsto> b) else m')\<close>
proof -
  have \<open>m' a = Some y \<Longrightarrow> m(a \<mapsto> b) ++ m' = m ++ m'\<close> for y
    by (metis (no_types) fun_upd_triv fun_upd_upd map_add_assoc map_add_empty map_add_upd
        map_le_iff_map_add_commute)
  then show ?thesis
    by auto
qed

lemma fold_map_of_alt:
  \<open>fold (\<lambda>(k, v) m. if m k \<noteq> None then m else m(k \<mapsto> v)) xs m' = map_of xs ++ m'\<close>
  by (induction xs arbitrary: m')
    (auto simp: map_upd_map_add_left)

lemma map_of_alt_def:
  \<open>map_of xs = hash_of_assoc_map xs\<close>
  using fold_map_of_alt[of xs Map.empty]
  unfolding hash_of_assoc_map_def
  by auto

definition hashmap_conv where
  [simp]: \<open>hashmap_conv x = x\<close>

lemma hash_of_assoc_map_id:
  \<open>(hash_of_assoc_map, hashmap_conv) \<in> hassoc_map_rel_raw \<rightarrow> Id\<close>
  by (auto intro!: fun_relI simp: hassoc_map_rel_raw_def br_def map_of_alt_def)

definition hassoc_map_rel where
  hassoc_map_rel_internal_def:
  \<open>hassoc_map_rel K V = hassoc_map_rel_raw O \<langle>K,V\<rangle>map_rel\<close>

lemma hassoc_map_rel_def:
  \<open>\<langle>K,V\<rangle> hassoc_map_rel = hassoc_map_rel_raw O \<langle>K,V\<rangle>map_rel\<close>
  unfolding relAPP_def hassoc_map_rel_internal_def
  by auto


end

