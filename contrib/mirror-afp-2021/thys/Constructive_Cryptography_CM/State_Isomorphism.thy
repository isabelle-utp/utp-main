theory State_Isomorphism
  imports
    More_CC
begin


section \<open>State Isomorphism\<close>

type_synonym 
  ('a, 'b) state_iso = "('a \<Rightarrow> 'b) \<times> ('b \<Rightarrow> 'a)"

definition 
  state_iso :: "('a, 'b) state_iso \<Rightarrow> bool" 
  where
    "state_iso \<equiv> (\<lambda>(f, g). type_definition f g UNIV)"

definition 
  apply_state_iso :: " ('s1, 's2) state_iso \<Rightarrow> ('s1, 'i, 'o) oracle' \<Rightarrow> ('s2, 'i, 'o) oracle'" 
  where
    "apply_state_iso \<equiv> (\<lambda>(f, g). map_fun g (map_fun id (map_spmf (map_prod id f))))"

lemma apply_state_iso_id: "apply_state_iso (id, id) = id"
  by (auto simp add: apply_state_iso_def map_prod.id spmf.map_id0 map_fun_id) 

lemma apply_state_iso_compose: "apply_state_iso si1 (apply_state_iso si2 oracle) = 
    apply_state_iso (map_prod (\<lambda>f. f o (fst si2)) ((o) (snd si2)) si1) oracle"
  unfolding apply_state_iso_def
  by (auto simp add: split_def id_def o_def map_prod_def map_fun_def map_spmf_conv_bind_spmf)

lemma apply_wiring_state_iso_assoc:
    "apply_wiring wr (apply_state_iso si oracle) = apply_state_iso si (apply_wiring wr oracle)"
  unfolding apply_state_iso_def apply_wiring_def
  by (auto simp add: split_def id_def o_def map_prod_def map_fun_def map_spmf_conv_bind_spmf)

lemma 
  resource_of_oracle_state_iso:
  assumes "state_iso fg"
  shows "resource_of_oracle (apply_state_iso fg oracle) s = resource_of_oracle oracle (snd fg s)" 
proof -
  have [simp]: "snd fg (fst fg x) = x" for x
    using assms by(simp add: state_iso_def split_beta type_definition.Rep_inverse)
  show ?thesis
    by(coinduction arbitrary: s)
      (auto 4 3 simp add: rel_fun_def spmf_rel_map apply_state_iso_def split_def intro!: rel_spmf_reflI)
qed


subsection \<open>Parallel State Isomorphism\<close>

definition 
  parallel_state_iso :: " (('s_core1 \<times> 's_core2) \<times> ('s_rest1 \<times> 's_rest2),
    ('s_core1 \<times> 's_rest1) \<times> ('s_core2 \<times> 's_rest2)) state_iso" 
  where
    "parallel_state_iso = 
      (\<lambda>((s11, s12), (s21, s22)). ((s11, s21), (s12, s22)),
        \<lambda>((s11, s21), (s12, s22)). ((s11, s12), (s21, s22)))"

lemma 
  state_iso_parallel_state_iso [simp]: "state_iso parallel_state_iso"
  by (auto simp add: type_definition_def state_iso_def parallel_state_iso_def)



subsection \<open>Trisplit State Isomorphism\<close>

definition 
  iso_trisplit 
  where
    "iso_trisplit = 
      (\<lambda>(((s11, s12), s13), (s21, s22), s23). (((s11, s21), s12, s22), s13, s23),
        \<lambda>(((s11, s21), s12, s22), s13, s23). (((s11, s12), s13), (s21, s22), s23))"

lemma 
  state_iso_fuse_par [simp]: "state_iso iso_trisplit"
  by(simp add: state_iso_def iso_trisplit_def; unfold_locales; simp add: split_def)


subsection \<open>Assocl-Swap State Isomorphism\<close>

definition 
  iso_swapar 
  where
    "iso_swapar = (\<lambda>((sm, s1), s2). (s1, sm, s2), \<lambda>(s1, sm, s2). ((sm, s1), s2))"

lemma 
  state_iso_swapar [simp]: "state_iso iso_swapar"
  by(simp add: state_iso_def iso_swapar_def; unfold_locales; simp add: split_def)

end