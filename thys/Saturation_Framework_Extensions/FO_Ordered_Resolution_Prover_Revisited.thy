(*  Title:       Application of the Saturation Framework to Bachmair and Ganzinger's RP
    Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2018-2020
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2020
*)

section \<open>Application of the Saturation Framework to Bachmair and Ganzinger's \textsf{RP}\<close>

theory FO_Ordered_Resolution_Prover_Revisited
  imports
    Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
    Saturation_Framework.Given_Clause_Architectures
    Clausal_Calculus
    Soundness
begin

text \<open>The main results about Bachmair and Ganzinger's \textsf{RP} prover, as established in
Section 4.3 of their \emph{Handbook} chapter and formalized by Schlichtkrull et al., are re-proved
here using the saturation framework of Waldmann et al.\<close>


subsection \<open>Setup\<close>

no_notation true_lit (infix "\<Turnstile>l" 50)
no_notation true_cls (infix "\<Turnstile>" 50)
no_notation true_clss (infix "\<Turnstile>s" 50)
no_notation true_cls_mset (infix "\<Turnstile>m" 50)

hide_type (open) Inference_System.inference

hide_const (open) Inference_System.Infer Inference_System.main_prem_of
  Inference_System.side_prems_of Inference_System.prems_of Inference_System.concl_of
  Inference_System.concls_of Inference_System.infer_from

type_synonym 'a old_inference = "'a Inference_System.inference"

abbreviation "old_Infer \<equiv> Inference_System.Infer"
abbreviation "old_side_prems_of \<equiv> Inference_System.side_prems_of"
abbreviation "old_main_prem_of \<equiv> Inference_System.main_prem_of"
abbreviation "old_concl_of \<equiv> Inference_System.concl_of"
abbreviation "old_prems_of \<equiv> Inference_System.prems_of"
abbreviation "old_concls_of \<equiv> Inference_System.concls_of"
abbreviation "old_infer_from \<equiv> Inference_System.infer_from"

lemmas old_infer_from_def = Inference_System.infer_from_def


subsection \<open>Library\<close>

lemma set_zip_replicate_right[simp]:
  "set (zip xs (replicate (length xs) y)) = (\<lambda>x. (x, y)) ` set xs"
  by (induct xs) auto


subsection \<open>Ground Layer\<close>

context FO_resolution_prover
begin

no_notation RP (infix "\<leadsto>" 50)
notation RP (infix "\<leadsto>RP" 50)

interpretation gr: ground_resolution_with_selection "S_M S M"
  using selection_axioms by unfold_locales (fact S_M_selects_subseteq S_M_selects_neg_lits)+

definition G_Inf :: "'a clause set \<Rightarrow> 'a clause inference set" where
  "G_Inf M = {Infer (CAs @ [DA]) E |CAs DA AAs As E. gr.ord_resolve M CAs DA AAs As E}"

lemma G_Inf_have_prems: "\<iota> \<in> G_Inf M \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding G_Inf_def by auto

lemma G_Inf_reductive: "\<iota> \<in> G_Inf M \<Longrightarrow> concl_of \<iota> < main_prem_of \<iota>"
  unfolding G_Inf_def by (auto dest: gr.ord_resolve_reductive)

interpretation G: sound_inference_system "G_Inf M" "{{#}}" "(\<TTurnstile>e)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> G_Inf M"
  moreover
  {
    fix I
    assume I_ent_prems: "I \<TTurnstile>s set (prems_of \<iota>)"
    obtain CAs AAs As where
      the_inf: "gr.ord_resolve M CAs (main_prem_of \<iota>) AAs As (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding G_Inf_def by auto
    then have "I \<TTurnstile> concl_of \<iota>"
      using gr.ord_resolve_sound[of M CAs "main_prem_of \<iota>" AAs As "concl_of \<iota>" I]
      by (metis I_ent_prems G_Inf_have_prems i_in insert_is_Un set_mset_mset set_prems_of
          true_clss_insert true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<TTurnstile>e {concl_of \<iota>}"
    by simp
qed

interpretation G: clausal_counterex_reducing_inference_system "G_Inf M" "gr.INTERP M"
proof
  fix N D
  assume
    "{#} \<notin> N" and
    "D \<in> N" and
    "\<not> gr.INTERP M N \<TTurnstile> D" and
    "\<And>C. C \<in> N \<Longrightarrow> \<not> gr.INTERP M N \<TTurnstile> C \<Longrightarrow> D \<le> C"
  then obtain CAs AAs As E where
    cas_in: "set CAs \<subseteq> N" and
    n_mod_cas: "gr.INTERP M N \<TTurnstile>m mset CAs" and
    ca_prod: "\<And>CA. CA \<in> set CAs \<Longrightarrow> gr.production M N CA \<noteq> {}" and
    e_res: "gr.ord_resolve M CAs D AAs As E" and
    n_nmod_e: "\<not> gr.INTERP M N \<TTurnstile> E" and
    e_lt_d: "E < D"
    using gr.ord_resolve_counterex_reducing by blast
  define \<iota> where
    "\<iota> = Infer (CAs @ [D]) E"

  have "\<iota> \<in> G_Inf M"
    unfolding \<iota>_def G_Inf_def using e_res by auto
  moreover have "prems_of \<iota> \<noteq> []"
    unfolding \<iota>_def by simp
  moreover have "main_prem_of \<iota> = D"
    unfolding \<iota>_def by simp
  moreover have "set (side_prems_of \<iota>) \<subseteq> N"
    unfolding \<iota>_def using cas_in by simp
  moreover have "gr.INTERP M N \<TTurnstile>s set (side_prems_of \<iota>)"
    unfolding \<iota>_def using n_mod_cas ca_prod by (simp add: gr.productive_imp_INTERP true_clss_def)
  moreover have "\<not> gr.INTERP M N \<TTurnstile> concl_of \<iota>"
    unfolding \<iota>_def using n_nmod_e by simp
  moreover have "concl_of \<iota> < D"
    unfolding \<iota>_def using e_lt_d by simp
  ultimately show "\<exists>\<iota> \<in> G_Inf M. prems_of \<iota> \<noteq> [] \<and> main_prem_of \<iota> = D \<and> set (side_prems_of \<iota>) \<subseteq> N \<and>
    gr.INTERP M N \<TTurnstile>s set (side_prems_of \<iota>) \<and> \<not> gr.INTERP M N \<TTurnstile> concl_of \<iota> \<and> concl_of \<iota> < D"
    by blast
qed

interpretation G: clausal_counterex_reducing_calculus_with_standard_redundancy "G_Inf M"
  "gr.INTERP M"
  by (unfold_locales, fact G_Inf_have_prems, fact G_Inf_reductive)

interpretation G: statically_complete_calculus "{{#}}" "G_Inf M" "(\<TTurnstile>e)" "G.Red_I M" G.Red_F
  by unfold_locales (use G.clausal_saturated_complete in blast)


subsection \<open>First-Order Layer\<close>

abbreviation \<G>_F :: \<open>'a clause \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_F \<equiv> grounding_of_cls\<close>

abbreviation \<G>_Fset :: \<open>'a clause set \<Rightarrow> 'a clause set\<close> where
  \<open>\<G>_Fset \<equiv> grounding_of_clss\<close>

lemmas \<G>_F_def = grounding_of_cls_def
lemmas \<G>_Fset_def = grounding_of_clss_def

definition \<G>_I :: \<open>'a clause set \<Rightarrow> 'a clause inference \<Rightarrow> 'a clause inference set\<close> where
  \<open>\<G>_I M \<iota> = {Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) |\<rho> \<rho>s.
     is_ground_subst_list \<rho>s \<and> is_ground_subst \<rho>
     \<and> Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> G_Inf M}\<close>

abbreviation
  \<G>_I_opt :: \<open>'a clause set \<Rightarrow> 'a clause inference \<Rightarrow> 'a clause inference set option\<close>
where
  \<open>\<G>_I_opt M \<iota> \<equiv> Some (\<G>_I M \<iota>)\<close>

definition F_Inf :: "'a clause inference set" where
  "F_Inf = {Infer (CAs @ [DA]) E | CAs DA AAs As \<sigma> E. ord_resolve_rename S CAs DA AAs As \<sigma> E}"

lemma F_Inf_have_prems: "\<iota> \<in> F_Inf \<Longrightarrow> prems_of \<iota> \<noteq> []"
  unfolding F_Inf_def by force

interpretation F: lifting_intersection F_Inf "{{#}}" UNIV G_Inf "\<lambda>N. (\<TTurnstile>e)" G.Red_I "\<lambda>N. G.Red_F"
  "{{#}}" "\<lambda>N. \<G>_F" \<G>_I_opt "\<lambda>D C C'. False"
proof (unfold_locales; (intro ballI)?)
  show "UNIV \<noteq> {}"
    by (rule UNIV_not_empty)
next
  show "consequence_relation {{#}} (\<TTurnstile>e)"
    by (fact consequence_relation_axioms)
next
  show "\<And>M. tiebreaker_lifting {{#}} F_Inf {{#}} (\<TTurnstile>e) (G_Inf M) (G.Red_I M) G.Red_F \<G>_F (\<G>_I_opt M)
    (\<lambda>D C C'. False)"
  proof
    fix M \<iota>
    show "the (\<G>_I_opt M \<iota>) \<subseteq> G.Red_I M (\<G>_F (concl_of \<iota>))"
      unfolding option.sel
    proof
      fix \<iota>'
      assume "\<iota>' \<in> \<G>_I M \<iota>"
      then obtain \<rho> \<rho>s where
        \<iota>': "\<iota>' = Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>)" and
        \<rho>_gr: "is_ground_subst \<rho>" and
        \<rho>_infer: "Infer (prems_of \<iota> \<cdot>\<cdot>cl \<rho>s) (concl_of \<iota> \<cdot> \<rho>) \<in> G_Inf M"
        unfolding \<G>_I_def by blast

      show "\<iota>' \<in> G.Red_I M (\<G>_F (concl_of \<iota>))"
        unfolding G.Red_I_def G.redundant_infer_def mem_Collect_eq using \<iota>' \<rho>_gr \<rho>_infer
        by (metis inference.sel(2) G_Inf_reductive empty_iff ground_subst_ground_cls
            grounding_of_cls_ground insert_iff subst_cls_eq_grounding_of_cls_subset_eq
            true_clss_union)
    qed
  qed (auto simp: \<G>_F_def ex_ground_subst)
qed

notation F.entails_\<G> (infix "\<TTurnstile>\<G>e" 50)

lemma F_entails_\<G>_iff: "N1 \<TTurnstile>\<G>e N2 \<longleftrightarrow> \<Union> (\<G>_F ` N1) \<TTurnstile>e \<Union> (\<G>_F ` N2)"
  unfolding F.entails_\<G>_def by simp

lemma true_Union_grounding_of_cls_iff:
  "I \<TTurnstile>s (\<Union>C \<in> N. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<longleftrightarrow> (\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>s N \<cdot>cs \<sigma>)"
  unfolding true_clss_def subst_clss_def by blast

interpretation F: sound_inference_system F_Inf "{{#}}" "(\<TTurnstile>\<G>e)"
proof
  fix \<iota>
  assume i_in: "\<iota> \<in> F_Inf"
  moreover
  {
    fix I \<eta>
    assume
      I_entails_prems: "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<TTurnstile>s set (prems_of \<iota>) \<cdot>cs \<sigma>" and
      \<eta>_gr: "is_ground_subst \<eta>"
    obtain CAs AAs As \<sigma> where
      the_inf: "ord_resolve_rename S CAs (main_prem_of \<iota>) AAs As \<sigma> (concl_of \<iota>)" and
      CAs: "CAs = side_prems_of \<iota>"
      using i_in unfolding F_Inf_def by auto
    have prems: "mset (prems_of \<iota>) = mset (side_prems_of \<iota>) + {#main_prem_of \<iota>#}"
      by (metis (no_types) F_Inf_have_prems[OF i_in] add.right_neutral append_Cons append_Nil2
          append_butlast_last_id mset.simps(2) mset_rev mset_single_iff_right rev_append
          rev_is_Nil_conv union_mset_add_mset_right)
    have "I \<TTurnstile> concl_of \<iota> \<cdot> \<eta>"
      using ord_resolve_rename_sound[OF the_inf, of I \<eta>, OF _ \<eta>_gr]
      unfolding CAs prems[symmetric] using I_entails_prems
      by (metis set_mset_mset set_mset_subst_cls_mset_subst_clss true_clss_set_mset)
  }
  ultimately show "set (inference.prems_of \<iota>) \<TTurnstile>\<G>e {concl_of \<iota>}"
    unfolding F.entails_\<G>_def \<G>_F_def true_Union_grounding_of_cls_iff by auto
qed

lemma G_Inf_overapprox_F_Inf: "\<iota>\<^sub>0 \<in> G.Inf_from M (\<Union> (\<G>_F ` M)) \<Longrightarrow> \<exists>\<iota> \<in> F.Inf_from M. \<iota>\<^sub>0 \<in> \<G>_I M \<iota>"
proof -
  assume \<iota>\<^sub>0_in: "\<iota>\<^sub>0 \<in> G.Inf_from M (\<Union> (\<G>_F ` M))"
  have prems_\<iota>\<^sub>0_in: "set (prems_of \<iota>\<^sub>0) \<subseteq> \<Union> (\<G>_F ` M)"
    using \<iota>\<^sub>0_in unfolding G.Inf_from_def by simp
  note \<iota>\<^sub>0_G_Inf = G.Inf_if_Inf_from[OF \<iota>\<^sub>0_in]
  then obtain CAs DA AAs As E where
    gr_res: \<open>gr.ord_resolve M CAs DA AAs As E\<close> and
    \<iota>\<^sub>0_is: \<open>\<iota>\<^sub>0 = Infer (CAs @ [DA]) E\<close>
    unfolding G_Inf_def by auto

  have CAs_in: \<open>set CAs \<subseteq> set (prems_of \<iota>\<^sub>0)\<close>
    by (simp add: \<iota>\<^sub>0_is subsetI)
  then have ground_CAs: \<open>is_ground_cls_list CAs\<close>
    using prems_\<iota>\<^sub>0_in union_grounding_of_cls_ground is_ground_cls_list_def is_ground_clss_def by auto
  have DA_in: \<open>DA \<in> set (prems_of \<iota>\<^sub>0)\<close>
    using \<iota>\<^sub>0_is by simp
  then have ground_DA: \<open>is_ground_cls DA\<close>
    using prems_\<iota>\<^sub>0_in union_grounding_of_cls_ground is_ground_clss_def by auto
  obtain \<sigma> where
    grounded_res: \<open>ord_resolve (S_M S M) CAs DA AAs As \<sigma> E\<close>
    using ground_ord_resolve_imp_ord_resolve[OF ground_DA ground_CAs
        gr.ground_resolution_with_selection_axioms gr_res] by auto
  have prems_ground: \<open>{DA} \<union> set CAs \<subseteq> \<G>_Fset M\<close>
    using prems_\<iota>\<^sub>0_in CAs_in DA_in unfolding \<G>_Fset_def by fast

  obtain \<eta>s \<eta> \<eta>2 CAs0 DA0 AAs0 As0 E0 \<tau> where
    ground_n: "is_ground_subst \<eta>" and
    ground_ns: "is_ground_subst_list \<eta>s" and
    ground_n2: "is_ground_subst \<eta>2" and
    ngr_res: "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0" and
    CAs0_is: "CAs0 \<cdot>\<cdot>cl \<eta>s = CAs" and
    DA0_is: "DA0 \<cdot> \<eta> = DA" and
    E0_is: "E0 \<cdot> \<eta>2 = E"  and
    prems_in: "{DA0} \<union> set CAs0 \<subseteq> M" and
    len_CAs0: "length CAs0 = length CAs" and
    len_ns: "length \<eta>s = length CAs"
    using ord_resolve_rename_lifting[OF _ grounded_res selection_axioms prems_ground] sel_stable
    by smt

  have "length CAs0 = length \<eta>s"
    using len_CAs0 len_ns by simp
  then have \<iota>\<^sub>0_is': "\<iota>\<^sub>0 = Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl (\<eta>s @ [\<eta>])) (E0 \<cdot> \<eta>2)"
    unfolding \<iota>\<^sub>0_is by (auto simp: CAs0_is[symmetric] DA0_is[symmetric] E0_is[symmetric])

  define \<iota> :: "'a clause inference" where
    "\<iota> = Infer (CAs0 @ [DA0]) E0"

  have i_F_Inf: \<open>\<iota> \<in> F_Inf\<close>
    unfolding \<iota>_def F_Inf_def using ngr_res by auto
  have "\<exists>\<rho> \<rho>s. \<iota>\<^sub>0 = Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl \<rho>s) (E0 \<cdot> \<rho>) \<and> is_ground_subst_list \<rho>s
    \<and> is_ground_subst \<rho> \<and> Infer ((CAs0 @ [DA0]) \<cdot>\<cdot>cl \<rho>s) (E0 \<cdot> \<rho>) \<in> G_Inf M"
    by (rule exI[of _ \<eta>2], rule exI[of _ "\<eta>s @ [\<eta>]"], use ground_ns in
        \<open>auto intro: ground_n ground_n2 \<iota>\<^sub>0_G_Inf[unfolded \<iota>\<^sub>0_is']
           simp: \<iota>\<^sub>0_is' is_ground_subst_list_def\<close>)
  then have \<open>\<iota>\<^sub>0 \<in> \<G>_I M \<iota>\<close>
    unfolding \<G>_I_def \<iota>_def CAs0_is[symmetric] DA0_is[symmetric] E0_is[symmetric] by simp
  moreover have \<open>\<iota> \<in> F.Inf_from M\<close>
    using prems_in i_F_Inf unfolding F.Inf_from_def \<iota>_def by simp
  ultimately show ?thesis
    by blast
qed

interpretation F: statically_complete_calculus "{{#}}" F_Inf "(\<TTurnstile>\<G>e)" F.Red_I_\<G> F.Red_F_\<G>_empty
proof (rule F.stat_ref_comp_to_non_ground_fam_inter; clarsimp; (intro exI)?)
  show "\<And>M. statically_complete_calculus {{#}} (G_Inf M) (\<TTurnstile>e) (G.Red_I M) G.Red_F"
    by (fact G.statically_complete_calculus_axioms)
next
  fix N
  assume "F.saturated N"
  show "F.ground.Inf_from_q N (\<Union> (\<G>_F ` N)) \<subseteq> {\<iota>. \<exists>\<iota>' \<in> F.Inf_from N. \<iota> \<in> \<G>_I N \<iota>'}
    \<union> G.Red_I N (\<Union> (\<G>_F ` N))"
    using G_Inf_overapprox_F_Inf unfolding F.ground.Inf_from_q_def \<G>_I_def by fastforce
qed


subsection \<open>Labeled First-Order or Given Clause Layer\<close>

datatype label = New | Processed | Old

definition FL_Infer_of :: "'a clause inference \<Rightarrow> ('a clause \<times> label) inference set" where
  "FL_Infer_of \<iota> = {Infer Cls (D, New) |Cls D. \<iota> = Infer (map fst Cls) D}"

definition FL_Inf :: "('a clause \<times> label) inference set" where
  "FL_Inf = (\<Union>\<iota> \<in> F_Inf. FL_Infer_of \<iota>)"

abbreviation F_Equiv :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<doteq>" 50) where
  "C \<doteq> D \<equiv> generalizes C D \<and> generalizes D C"

abbreviation F_Prec :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" (infix "\<prec>\<cdot>" 50) where
  "C \<prec>\<cdot> D \<equiv> strictly_generalizes C D"

fun L_Prec :: "label \<Rightarrow> label \<Rightarrow> bool" (infix "\<sqsubset>l" 50) where
  "Old \<sqsubset>l l \<longleftrightarrow> l \<noteq> Old"
| "Processed \<sqsubset>l l \<longleftrightarrow> l = New"
| "New \<sqsubset>l l \<longleftrightarrow> False"

lemma irrefl_L_Prec: "\<not> l \<sqsubset>l l"
  by (cases l) auto

lemma trans_L_Prec: "l1 \<sqsubset>l l2 \<Longrightarrow> l2 \<sqsubset>l l3 \<Longrightarrow> l1 \<sqsubset>l l3"
  by (cases l1; cases l2; cases l3) auto

lemma wf_L_Prec: "wfP (\<sqsubset>l)"
  by (metis L_Prec.elims(2) L_Prec.simps(3) not_accp_down wfP_accp_iff)

interpretation FL: given_clause "{{#}}" F_Inf "{{#}}" UNIV "\<lambda>N. (\<TTurnstile>e)" G_Inf G.Red_I
  "\<lambda>N. G.Red_F" "\<lambda>N. \<G>_F" \<G>_I_opt FL_Inf "(\<doteq>)" "(\<prec>\<cdot>)" "(\<sqsubset>l)" Old
proof (unfold_locales; (intro ballI)?)
  show "equivp (\<doteq>)"
    unfolding equivp_def by (meson generalizes_refl generalizes_trans)
next
  show "po_on (\<prec>\<cdot>) UNIV"
    unfolding po_on_def irreflp_on_def transp_on_def
    using strictly_generalizes_irrefl strictly_generalizes_trans by auto
next
  show "wfp_on (\<prec>\<cdot>) UNIV"
    unfolding wfp_on_UNIV by (metis wf_strictly_generalizes)
next
  show "po_on (\<sqsubset>l) UNIV"
    unfolding po_on_def irreflp_on_def transp_on_def using irrefl_L_Prec trans_L_Prec by blast
next
  show "wfp_on (\<sqsubset>l) UNIV"
    unfolding wfp_on_UNIV by (rule wf_L_Prec)
next
  fix C1 D1 C2 D2
  assume
    "C1 \<doteq> D1"
    "C2 \<doteq> D2"
    "C1 \<prec>\<cdot> C2"
  then show "D1 \<prec>\<cdot> D2"
    by (smt antisym size_mset_mono size_subst strictly_generalizes_def generalizes_def
        generalizes_trans)
next
  fix N C1 C2
  assume "C1 \<doteq> C2"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding generalizes_def \<G>_F_def by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  fix N C2 C1
  assume "C2 \<prec>\<cdot> C1"
  then show "\<G>_F C1 \<subseteq> \<G>_F C2"
    unfolding strictly_generalizes_def generalizes_def \<G>_F_def
    by clarsimp (metis is_ground_comp_subst subst_cls_comp_subst)
next
  show "\<exists>l. L_Prec Old l"
    using L_Prec.simps(1) by blast
qed (auto simp: FL_Inf_def FL_Infer_of_def F_Inf_have_prems)

notation FL.Prec_FL (infix "\<sqsubset>" 50)
notation FL.entails_\<G>_L (infix "\<TTurnstile>\<G>Le" 50)
notation FL.derive (infix "\<rhd>L" 50)
notation FL.step (infix "\<leadsto>GC" 50)

lemma FL_Red_F_eq:
  "FL.Red_F N =
   {C. \<forall>D \<in> \<G>_F (fst C). D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` N)) \<or> (\<exists>E \<in> N. E \<sqsubset> C \<and> D \<in> \<G>_F (fst E))}"
  unfolding FL.Red_F_def FL.Red_F_\<G>_q_def by auto

lemma mem_FL_Red_F_because_G_Red_F:
  "(\<forall>D \<in> \<G>_F (fst Cl). D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` N))) \<Longrightarrow> Cl \<in> FL.Red_F N"
  unfolding FL_Red_F_eq by auto

lemma mem_FL_Red_F_because_Prec_FL:
  "(\<forall>D \<in> \<G>_F (fst Cl). \<exists>El \<in> N. El \<sqsubset> Cl \<and> D \<in> \<G>_F (fst El)) \<Longrightarrow> Cl \<in> FL.Red_F N"
  unfolding FL_Red_F_eq by auto


subsection \<open>Resolution Prover Layer\<close>

interpretation sq: selection "S_Q Sts"
  unfolding S_Q_def using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms
  by unfold_locales auto

interpretation gd: ground_resolution_with_selection "S_Q Sts"
  by unfold_locales

interpretation src: standard_redundancy_criterion_counterex_reducing "gd.ord_\<Gamma> Sts"
  "ground_resolution_with_selection.INTERP (S_Q Sts)"
  by unfold_locales

definition lclss_of_state :: "'a state \<Rightarrow> ('a clause \<times> label) set" where
  "lclss_of_state St =
   (\<lambda>C. (C, New)) ` N_of_state St \<union> (\<lambda>C. (C, Processed)) ` P_of_state St
   \<union> (\<lambda>C. (C, Old)) ` Q_of_state St"

lemma image_hd_lclss_of_state[simp]: "fst ` lclss_of_state St = clss_of_state St"
  unfolding lclss_of_state_def by (auto simp: image_Un image_comp)

lemma insert_lclss_of_state[simp]:
  "insert (C, New) (lclss_of_state (N, P, Q)) = lclss_of_state (N \<union> {C}, P, Q)"
  "insert (C, Processed) (lclss_of_state (N, P, Q)) = lclss_of_state (N, P \<union> {C}, Q)"
  "insert (C, Old) (lclss_of_state (N, P, Q)) = lclss_of_state (N, P, Q \<union> {C})"
  unfolding lclss_of_state_def image_def by auto

lemma union_lclss_of_state[simp]:
  "lclss_of_state (N1, P1, Q1) \<union> lclss_of_state (N2, P2, Q2) =
   lclss_of_state (N1 \<union> N2, P1 \<union> P2, Q1 \<union> Q2)"
  unfolding lclss_of_state_def by auto

lemma mem_lclss_of_state[simp]:
  "(C, New) \<in> lclss_of_state (N, P, Q) \<longleftrightarrow> C \<in> N"
  "(C, Processed) \<in> lclss_of_state (N, P, Q) \<longleftrightarrow> C \<in> P"
  "(C, Old) \<in> lclss_of_state (N, P, Q) \<longleftrightarrow> C \<in> Q"
  unfolding lclss_of_state_def image_def by auto

lemma lclss_Liminf_commute:
  "Liminf_llist (lmap lclss_of_state Sts) = lclss_of_state (Liminf_state Sts)"
proof -
  have \<open>Liminf_llist (lmap lclss_of_state Sts) =
    (\<lambda>C. (C, New)) ` Liminf_llist (lmap N_of_state Sts) \<union>
    (\<lambda>C. (C, Processed)) ` Liminf_llist (lmap P_of_state Sts) \<union>
    (\<lambda>C. (C, Old)) ` Liminf_llist (lmap Q_of_state Sts)\<close>
    unfolding lclss_of_state_def using Liminf_llist_lmap_union Liminf_llist_lmap_image
    by (smt Pair_inject Un_iff disjoint_iff_not_equal imageE inj_onI label.simps(1,3,5)
        llist.map_cong)
 then show ?thesis
   unfolding lclss_of_state_def Liminf_state_def by auto
qed

lemma GC_tautology_step:
  assumes tauto: "Neg A \<in># C" "Pos A \<in># C"
  shows "lclss_of_state (N \<union> {C}, P, Q) \<leadsto>GC lclss_of_state (N, P, Q)"
proof -
  have c\<theta>_red: "C\<theta> \<in> G.Red_F (\<Union>D \<in> N'. \<G>_F (fst D))" if in_g: "C\<theta> \<in> \<G>_F C"
    for N' :: "('a clause \<times> label) set" and C\<theta>
  proof -
    obtain \<theta> where
      "C\<theta> = C \<cdot> \<theta>"
       using in_g unfolding \<G>_F_def by blast
    then have "Neg (A \<cdot>a \<theta>) \<in># C\<theta>" and "Pos (A \<cdot>a \<theta>) \<in># C\<theta>"
      using tauto Neg_Melem_subst_atm_subst_cls Pos_Melem_subst_atm_subst_cls by auto
    then have "{} \<TTurnstile>e {C\<theta>}"
      unfolding true_clss_def true_cls_def true_lit_def if_distrib_fun
      by (metis literal.disc literal.sel singletonD)
    then show ?thesis
      unfolding G.Red_F_def by auto
  qed

  show ?thesis
  proof (rule FL.step.process[of _ "lclss_of_state (N, P, Q)" "{(C, New)}" _ "{}"])
    show \<open>{(C, New)} \<subseteq> FL.Red_F_\<G> (lclss_of_state (N, P, Q) \<union> {})\<close>
      using mem_FL_Red_F_because_G_Red_F c\<theta>_red[of _ "lclss_of_state (N, P, Q)"]
      unfolding lclss_of_state_def by auto
  qed (auto simp: lclss_of_state_def FL.active_subset_def)
qed

lemma GC_subsumption_step:
  assumes
    d_in: "Dl \<in> N" and
    d_sub_c: "strictly_subsumes (fst Dl) (fst Cl) \<or> subsumes (fst Dl) (fst Cl) \<and> snd Dl \<sqsubset>l snd Cl"
  shows "N \<union> {Cl} \<leadsto>GC N"
proof -
  have d_sub'_c: "Cl \<in> FL.Red_F {Dl} \<or> Dl \<sqsubset> Cl"
  proof (cases "size (fst Dl) = size (fst Cl)")
    case True
      assume sizes_eq: \<open>size (fst Dl) = size (fst Cl)\<close>
      have \<open>size (fst Dl) = size (fst Cl) \<Longrightarrow>
        strictly_subsumes (fst Dl) (fst Cl) \<or> subsumes (fst Dl) (fst Cl) \<and> snd Dl \<sqsubset>l snd Cl \<Longrightarrow>
        Dl \<sqsubset> Cl\<close>
        unfolding FL.Prec_FL_def
        unfolding generalizes_def strictly_generalizes_def strictly_subsumes_def subsumes_def
        by (metis size_subst subset_mset.order_refl subseteq_mset_size_eql)
    then have "Dl \<sqsubset> Cl"
      using sizes_eq d_sub_c by auto
    then show ?thesis
      by (rule disjI2)
  next
    case False
    then have d_ssub_c: "strictly_subsumes (fst Dl) (fst Cl)"
      using d_sub_c unfolding strictly_subsumes_def subsumes_def
      by (metis size_subst strict_subset_subst_strictly_subsumes strictly_subsumes_antisym
          subset_mset.antisym_conv2)
    have "Cl \<in> FL.Red_F {Dl}"
    proof (rule mem_FL_Red_F_because_G_Red_F)
      show \<open>\<forall>D \<in> \<G>_F (fst Cl). D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` {Dl}))\<close>
        using d_ssub_c unfolding G.Red_F_def strictly_subsumes_def subsumes_def \<G>_F_def
      proof clarsimp
        fix \<sigma> \<sigma>'
        assume
          fst_not_in: \<open>\<forall>\<sigma>. \<not> fst Cl \<cdot> \<sigma> \<subseteq># fst Dl\<close> and
          fst_in: \<open>fst Dl \<cdot> \<sigma> \<subseteq># fst Cl\<close> and
          gr_sig: \<open>is_ground_subst \<sigma>'\<close>
        have \<open>{fst Dl \<cdot> \<sigma> \<cdot> \<sigma>'} \<subseteq> {fst Dl \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}\<close>
          using gr_sig
          by (metis (mono_tags, lifting) is_ground_comp_subst mem_Collect_eq singletonD subsetI
              subst_cls_comp_subst)
        moreover have \<open>\<forall>I. I \<TTurnstile>s {fst Dl \<cdot> \<sigma> \<cdot> \<sigma>'} \<longrightarrow> I \<TTurnstile> fst Cl \<cdot> \<sigma>'\<close>
          using fst_in
          by (meson subst_cls_mono_mset true_clss_insert true_clss_subclause)
        moreover have \<open>\<forall>D \<in> {fst Dl \<cdot> \<sigma> \<cdot> \<sigma>'}. D < fst Cl \<cdot> \<sigma>'\<close>
          using fst_not_in fst_in gr_sig
        proof clarify
          show \<open>\<forall>\<sigma>. \<not> fst Cl \<cdot> \<sigma> \<subseteq># fst Dl \<Longrightarrow> fst Dl \<cdot> \<sigma> \<subseteq># fst Cl \<Longrightarrow> is_ground_subst \<sigma>' \<Longrightarrow>
            fst Dl \<cdot> \<sigma> \<cdot> \<sigma>' < fst Cl \<cdot> \<sigma>'\<close>
            by (metis False size_subst subset_imp_less_mset subset_mset.le_less subst_subset_mono)
        qed
        ultimately show \<open>\<exists>DD \<subseteq> {fst Dl \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}.
           (\<forall>I. I \<TTurnstile>s DD \<longrightarrow> I \<TTurnstile> fst Cl \<cdot> \<sigma>') \<and> (\<forall>D \<in> DD. D < fst Cl \<cdot> \<sigma>')\<close>
          by blast
      qed
    qed
    then show ?thesis
      by (rule disjI1)
  qed
  show ?thesis
  proof (rule FL.step.process[of _ N "{Cl}" _ "{}"], simp+)
    show \<open>Cl \<in> FL.Red_F_\<G> N\<close>
      using d_sub'_c unfolding FL_Red_F_eq
    proof -
      have \<open>\<And>D. D \<in> \<G>_F (fst Cl) \<Longrightarrow> \<forall>E \<in> N. E \<sqsubset> Cl \<longrightarrow> D \<notin> \<G>_F (fst E) \<Longrightarrow>
        \<forall>D \<in> \<G>_F (fst Cl). D \<in> G.Red_F (\<G>_F (fst Dl)) \<or> Dl \<sqsubset> Cl \<and> D \<in> \<G>_F (fst Dl) \<Longrightarrow>
        D \<in> G.Red_F (\<Union>a \<in> N. \<G>_F (fst a))\<close>
        by (metis (no_types, lifting) G.Red_F_of_subset SUP_upper d_in subset_iff)
      moreover have \<open>\<And>D. D \<in> \<G>_F (fst Cl) \<Longrightarrow> \<forall>E \<in> N. E \<sqsubset> Cl \<longrightarrow> D \<notin> \<G>_F (fst E) \<Longrightarrow> Dl \<sqsubset> Cl \<Longrightarrow>
        D \<in> G.Red_F (\<Union>a \<in> N. \<G>_F (fst a))\<close>
        by (smt FL.Prec_FL_def FL.equiv_F_grounding FL.prec_F_grounding UNIV_witness d_in in_mono)
      ultimately show \<open>Cl \<in> {C. \<forall>D \<in> \<G>_F (fst C). D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` {Dl})) \<or>
        (\<exists>E \<in> {Dl}. E \<sqsubset> C \<and> D \<in> \<G>_F (fst E))} \<or> Dl \<sqsubset> Cl \<Longrightarrow>
        Cl \<in> {C. \<forall>D \<in> \<G>_F (fst C). D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` N)) \<or>
        (\<exists>E \<in> N. E \<sqsubset> C \<and> D \<in> \<G>_F (fst E))}\<close>
        by auto
    qed
  qed (simp add: FL.active_subset_def)
qed

lemma GC_reduction_step:
  assumes
    young: "snd Dl \<noteq> Old" and
    d_sub_c: "fst Dl \<subset># fst Cl"
  shows "N \<union> {Cl} \<leadsto>GC N \<union> {Dl}"
proof (rule FL.step.process[of _ N "{Cl}" _ "{Dl}"])
  have "Cl \<in> FL.Red_F {Dl}"
  proof (rule mem_FL_Red_F_because_G_Red_F)
    show \<open>\<forall>D \<in> \<G>_F (fst Cl). D \<in> G.Red_F (\<Union> (\<G>_F ` fst ` {Dl}))\<close>
      using d_sub_c unfolding G.Red_F_def strictly_subsumes_def subsumes_def \<G>_F_def
    proof clarsimp
      fix \<sigma>
      assume \<open>is_ground_subst \<sigma>\<close>
      then have \<open>{fst Dl \<cdot> \<sigma>} \<subseteq> {fst Dl \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}\<close>
        by blast
      moreover have \<open>fst Dl \<cdot> \<sigma> < fst Cl \<cdot> \<sigma>\<close>
        using subst_subset_mono[OF d_sub_c, of \<sigma>] by (simp add: subset_imp_less_mset)
      moreover have \<open>\<forall>I. I \<TTurnstile> fst Dl \<cdot> \<sigma> \<longrightarrow> I \<TTurnstile> fst Cl \<cdot> \<sigma>\<close>
        using subst_subset_mono[OF d_sub_c] true_clss_subclause by fast
      ultimately show \<open>\<exists>DD \<subseteq> {fst Dl \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}. (\<forall>I. I \<TTurnstile>s DD \<longrightarrow> I \<TTurnstile> fst Cl \<cdot> \<sigma>)
        \<and> (\<forall>D \<in> DD. D < fst Cl \<cdot> \<sigma>)\<close>
        by blast
    qed
  qed
  then show "{Cl} \<subseteq> FL.Red_F (N \<union> {Dl})"
    using FL.Red_F_of_subset by blast
qed (auto simp: FL.active_subset_def young)

lemma GC_processing_step: "N \<union> {(C, New)} \<leadsto>GC N \<union> {(C, Processed)}"
proof (rule FL.step.process[of _ N "{(C, New)}" _ "{(C, Processed)}"])
  have "(C, New) \<in> FL.Red_F {(C, Processed)}"
    by (rule mem_FL_Red_F_because_Prec_FL) (simp add: FL.Prec_FL_def generalizes_refl)
  then show "{(C, New)} \<subseteq> FL.Red_F (N \<union> {(C, Processed)})"
    using FL.Red_F_of_subset by blast
qed (auto simp: FL.active_subset_def)

lemma old_inferences_between_eq_new_inferences_between:
  "old_concl_of ` inference_system.inferences_between (ord_FO_\<Gamma> S) N C =
   concl_of ` F.Inf_between N {C}" (is "?rp = ?f")
proof (intro set_eqI iffI)
  fix E
  assume e_in: "E \<in> old_concl_of ` inference_system.inferences_between (ord_FO_\<Gamma> S) N C"

  obtain CAs DA AAs As \<sigma> where
    e_res: "ord_resolve_rename S CAs DA AAs As \<sigma> E" and
    cd_sub: "set CAs \<union> {DA} \<subseteq> N \<union> {C}" and
    c_in: "C \<in> set CAs \<union> {DA}"
    using e_in unfolding inference_system.inferences_between_def infer_from_def ord_FO_\<Gamma>_def by auto

  show "E \<in> concl_of ` F.Inf_between N {C}"
    unfolding F.Inf_between_alt F.Inf_from_def
  proof -
    have \<open>Infer (CAs @ [DA]) E \<in> F_Inf \<and> set (prems_of (Infer (CAs @ [DA]) E)) \<subseteq> insert C N \<and>
      C \<in> set (prems_of (Infer (CAs @ [DA]) E)) \<and> E = concl_of (Infer (CAs @ [DA]) E)\<close>
      using e_res cd_sub c_in F_Inf_def by auto
    then show \<open>E \<in> concl_of ` {\<iota> \<in> F_Inf. \<iota> \<in> {\<iota> \<in> F_Inf. set (prems_of \<iota>) \<subseteq> N \<union> {C}} \<and>
      set (prems_of \<iota>) \<inter> {C} \<noteq> {}}\<close>
      by (smt Un_insert_right boolean_algebra_cancel.sup0 disjoint_insert mem_Collect_eq image_def)
  qed
next
  fix E
  assume e_in: "E \<in> concl_of ` F.Inf_between N {C}"

  obtain CAs DA AAs As \<sigma> where
    e_res: "ord_resolve_rename S CAs DA AAs As \<sigma> E" and
    cd_sub: "set CAs \<union> {DA} \<subseteq> N \<union> {C}" and
    c_in: "C \<in> set CAs \<union> {DA}"
    using e_in unfolding F.Inf_between_alt F.Inf_from_def F_Inf_def inference_system.Inf_between_alt
      inference_system.Inf_from_def
    by (auto simp: image_def Bex_def)

  show "E \<in> old_concl_of ` inference_system.inferences_between (ord_FO_\<Gamma> S) N C"
    unfolding inference_system.inferences_between_def infer_from_def ord_FO_\<Gamma>_def
    using e_res cd_sub c_in
    by (clarsimp simp: image_def Bex_def, rule_tac x = "old_Infer (mset CAs) DA E" in exI, auto)
qed

lemma GC_inference_step:
  assumes
    young: "l \<noteq> Old" and
    no_active: "FL.active_subset M = {}" and
    m_sup: "fst ` M \<supseteq> old_concl_of ` inference_system.inferences_between (ord_FO_\<Gamma> S)
      (fst ` FL.active_subset N) C"
  shows "N \<union> {(C, l)} \<leadsto>GC N \<union> {(C, Old)} \<union> M"
proof (rule FL.step.infer[of _ N C l _ M])
  have m_sup': "fst ` M \<supseteq> concl_of ` F.Inf_between (fst ` FL.active_subset N) {C}"
    using m_sup unfolding old_inferences_between_eq_new_inferences_between .

  show "F.Inf_between (fst ` FL.active_subset N) {C} \<subseteq> F.Red_I (fst ` (N \<union> {(C, Old)} \<union> M))"
  proof
    fix \<iota>
    assume \<iota>_in_if2: "\<iota> \<in> F.Inf_between (fst ` FL.active_subset N) {C}"
    note \<iota>_in = F.Inf_if_Inf_between[OF \<iota>_in_if2]
    have "concl_of \<iota> \<in> fst ` M"
      using m_sup' \<iota>_in_if2 m_sup' by (auto simp: image_def Collect_mono_iff F.Inf_between_alt)
    then have "concl_of \<iota> \<in> fst ` (N \<union> {(C, Old)} \<union> M)"
      by auto
    then show "\<iota> \<in> F.Red_I_\<G> (fst ` (N \<union> {(C, Old)} \<union> M))"
      by (rule F.Red_I_of_Inf_to_N[OF \<iota>_in])
  qed
qed (use young no_active in auto)

lemma RP_step_imp_GC_step: "St \<leadsto>RP St' \<Longrightarrow> lclss_of_state St \<leadsto>GC lclss_of_state St'"
proof (induction rule: RP.induct)
  case (tautology_deletion A C N P Q)
  then show ?case
    by (rule GC_tautology_step)
next
  case (forward_subsumption D P Q C N)
  note d_in = this(1) and d_sub_c = this(2)
  show ?case
  proof (cases "D \<in> P")
    case True
    then show ?thesis
      using GC_subsumption_step[of "(D, Processed)" "lclss_of_state (N, P, Q)" "(C, New)"] d_sub_c
      by auto
  next
    case False
    then have "D \<in> Q"
      using d_in by simp
    then show ?thesis
      using GC_subsumption_step[of "(D, Old)" "lclss_of_state (N, P, Q)" "(C, New)"] d_sub_c by auto
  qed
next
  case (backward_subsumption_P D N C P Q)
  note d_in = this(1) and d_ssub_c = this(2)
  then show ?case
    using GC_subsumption_step[of "(D, New)" "lclss_of_state (N, P, Q)" "(C, Processed)"] d_ssub_c
    by auto
next
  case (backward_subsumption_Q D N C P Q)
  note d_in = this(1) and d_ssub_c = this(2)
  then show ?case
    using GC_subsumption_step[of "(D, New)" "lclss_of_state (N, P, Q)" "(C, Old)"] d_ssub_c by auto
next
  case (forward_reduction D L' P Q L \<sigma> C N)
  show ?case
    using GC_reduction_step[of "(C, New)" "(C + {#L#}, New)" "lclss_of_state (N, P, Q)"] by auto
next
  case (backward_reduction_P D L' N L \<sigma> C P Q)
  show ?case
    using GC_reduction_step[of "(C, Processed)" "(C + {#L#}, Processed)" "lclss_of_state (N, P, Q)"]
    by auto
next
  case (backward_reduction_Q D L' N L \<sigma> C P Q)
  show ?case
    using GC_reduction_step[of "(C, Processed)" "(C + {#L#}, Old)" "lclss_of_state (N, P, Q)"]
    by auto
next
  case (clause_processing N C P Q)
  show ?case
    using GC_processing_step[of "lclss_of_state (N, P, Q)" C] by auto
next
  case (inference_computation N Q C P)
  note n = this(1)
  show ?case
  proof -
    have \<open>FL.active_subset (lclss_of_state (N, {}, {})) = {}\<close>
      unfolding n by (auto simp: FL.active_subset_def)
    moreover have \<open>old_concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S)
      (fst ` FL.active_subset (lclss_of_state ({}, P, Q))) C) \<subseteq> N\<close>
      unfolding n inference_system.inferences_between_def image_def mem_Collect_eq
        lclss_of_state_def infer_from_def
      by (auto simp: FL.active_subset_def)
    ultimately have \<open>lclss_of_state ({}, insert C P, Q) \<leadsto>GC lclss_of_state (N, P, insert C Q)\<close>
      using GC_inference_step[of Processed "lclss_of_state (N, {}, {})"
        "lclss_of_state ({}, P, Q)" C, simplified] by blast
    then show ?case
      by (auto simp: FL.active_subset_def)
  qed
qed

lemma RP_derivation_imp_GC_derivation: "chain (\<leadsto>RP) Sts \<Longrightarrow> chain (\<leadsto>GC) (lmap lclss_of_state Sts)"
  using chain_lmap RP_step_imp_GC_step by blast

lemma RP_step_imp_derive_step: "St \<leadsto>RP St' \<Longrightarrow> lclss_of_state St \<rhd>L lclss_of_state St'"
  by (rule FL.one_step_equiv) (rule RP_step_imp_GC_step)

lemma RP_derivation_imp_derive_derivation:
  "chain (\<leadsto>RP) Sts \<Longrightarrow> chain (\<rhd>L) (lmap lclss_of_state Sts)"
  using chain_lmap RP_step_imp_derive_step by blast

theorem RP_sound_new_statement:
  assumes
    deriv: "chain (\<leadsto>RP) Sts" and
    bot_in: "{#} \<in> clss_of_state (Liminf_state Sts)"
  shows "clss_of_state (lhd Sts) \<TTurnstile>\<G>e {{#}}"
proof -
  have "clss_of_state (Liminf_state Sts) \<TTurnstile>\<G>e {{#}}"
    using F.subset_entailed bot_in by auto
  then have "fst ` Liminf_llist (lmap lclss_of_state Sts) \<TTurnstile>\<G>e {{#}}"
    by (metis image_hd_lclss_of_state lclss_Liminf_commute)
  then have "Liminf_llist (lmap lclss_of_state Sts) \<TTurnstile>\<G>Le FL.Bot_FL"
    using FL.labeled_entailment_lifting by simp
  then have "lhd (lmap lclss_of_state Sts) \<TTurnstile>\<G>Le FL.Bot_FL"
  proof -
    assume \<open>FL.entails_\<G> (Liminf_llist (lmap lclss_of_state Sts)) ({{#}} \<times> UNIV)\<close>
    moreover have \<open>chain (\<rhd>L) (lmap lclss_of_state Sts)\<close>
      using deriv RP_derivation_imp_derive_derivation by simp
    moreover have \<open>chain FL.entails_\<G> (lmap lclss_of_state Sts)\<close>
      by (smt F_entails_\<G>_iff FL.labeled_entailment_lifting RP_model chain_lmap deriv \<G>_Fset_def
        image_hd_lclss_of_state)
    ultimately show \<open>FL.entails_\<G> (lhd (lmap lclss_of_state Sts)) ({{#}} \<times> UNIV)\<close>
      using FL.unsat_limit_iff by blast
  qed
  then have "lclss_of_state (lhd Sts) \<TTurnstile>\<G>Le FL.Bot_FL"
    using chain_not_lnull deriv by fastforce
  then show ?thesis
    unfolding FL.entails_\<G>_L_def F.entails_\<G>_def lclss_of_state_def by auto
qed

theorem RP_saturated_if_fair_new_statement:
  assumes
    deriv: "chain (\<leadsto>RP) Sts" and
    init: "FL.active_subset (lclss_of_state (lhd Sts)) = {}" and
    final: "FL.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
  shows "FL.saturated (Liminf_llist (lmap lclss_of_state Sts))"
proof -
  note nnil = chain_not_lnull[OF deriv]
  have gc_deriv: "chain (\<leadsto>GC) (lmap lclss_of_state Sts)"
    by (rule RP_derivation_imp_GC_derivation[OF deriv])
  show ?thesis
    using nnil init final
      FL.fair_implies_Liminf_saturated[OF FL.gc_to_red[OF gc_deriv] FL.gc_fair[OF gc_deriv]] by simp
qed

corollary RP_complete_if_fair_new_statement:
  assumes
    deriv: "chain (\<leadsto>RP) Sts" and
    init: "FL.active_subset (lclss_of_state (lhd Sts)) = {}" and
    final: "FL.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}" and
    unsat: "grounding_of_state (lhd Sts) \<TTurnstile>e {{#}}"
  shows "{#} \<in> Q_of_state (Liminf_state Sts)"
proof -
  note nnil = chain_not_lnull[OF deriv]
  note len = chain_length_pos[OF deriv]
  have gc_deriv: "chain (\<leadsto>GC) (lmap lclss_of_state Sts)"
    by (rule RP_derivation_imp_GC_derivation[OF deriv])

  have hd_lcls: "fst ` lhd (lmap lclss_of_state Sts) = lhd (lmap clss_of_state Sts)"
    using len zero_enat_def by auto
  have hd_unsat: "fst ` lhd (lmap lclss_of_state Sts) \<TTurnstile>\<G>e {{#}}"
    unfolding hd_lcls F_entails_\<G>_iff unfolding true_clss_def using unsat unfolding \<G>_Fset_def
    by (metis (no_types, lifting) chain_length_pos gc_deriv gr.ex_min_counterex i0_less
        llength_eq_0 llength_lmap llength_lmap llist.map_sel(1) true_cls_empty true_clss_singleton)
  have "\<exists>BL \<in> {{#}} \<times> UNIV. BL \<in> Liminf_llist (lmap lclss_of_state Sts)"
    by (rule FL.gc_complete_Liminf[OF gc_deriv,of "{#}"])
      (use final hd_unsat in \<open>auto simp: init nnil\<close>)
  then show ?thesis
    unfolding Liminf_state_def lclss_Liminf_commute
    using final[unfolded FL.passive_subset_def] Liminf_state_def lclss_Liminf_commute by fastforce
qed


subsection \<open>Alternative Derivation of Previous \textsf{RP} Results\<close>

lemma old_fair_imp_new_fair:
  assumes
    nnul: "\<not> lnull Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}"
  shows
    "FL.active_subset (lclss_of_state (lhd Sts)) = {}" and
    "FL.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
proof -
  show "FL.active_subset (lclss_of_state (lhd Sts)) = {}"
    using nnul empty_Q0 unfolding FL.active_subset_def by (cases Sts) auto
next
  show "FL.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
    using fair
    unfolding fair_state_seq_def FL.passive_subset_def lclss_Liminf_commute lclss_of_state_def
    by auto
qed

lemma old_redundant_infer_iff:
  "src.redundant_infer N \<gamma> \<longleftrightarrow>
   (\<exists>DD. DD \<subseteq> N \<and> DD \<union> set_mset (old_side_prems_of \<gamma>) \<TTurnstile>e {old_concl_of \<gamma>}
      \<and> (\<forall>D \<in> DD. D < old_main_prem_of \<gamma>))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then obtain DD0 where
    "DD0 \<subseteq> N" and
    "DD0 \<union> set_mset (old_side_prems_of \<gamma>) \<TTurnstile>e {old_concl_of \<gamma>}" and
    "\<forall>D \<in> DD0. D < old_main_prem_of \<gamma>"
    by blast
  then obtain DD where
    fin_dd: "finite DD" and
    dd_in: "DD \<subseteq> N" and
    dd_un: "DD \<union> set_mset (old_side_prems_of \<gamma>) \<TTurnstile>e {old_concl_of \<gamma>}" and
    all_dd: "\<forall>D \<in> DD. D < old_main_prem_of \<gamma>"
    using entails_concl_compact_union[of "{old_concl_of \<gamma>}" DD0 "set_mset (old_side_prems_of \<gamma>)"]
    by fast
  show ?lhs
    unfolding src.redundant_infer_def using fin_dd dd_in dd_un all_dd
    by simp (metis finite_set_mset_mset_set true_clss_set_mset)
qed (auto simp: src.redundant_infer_def)

definition old_infer_of :: "'a clause inference \<Rightarrow> 'a old_inference" where
  "old_infer_of \<iota> = old_Infer (mset (side_prems_of \<iota>)) (main_prem_of \<iota>) (concl_of \<iota>)"

lemma new_redundant_infer_imp_old_redundant_infer:
  "G.redundant_infer N \<iota> \<Longrightarrow> src.redundant_infer N (old_infer_of \<iota>)"
  unfolding old_redundant_infer_iff G.redundant_infer_def old_infer_of_def by simp

lemma saturated_imp_saturated_RP:
  assumes
    satur: "FL.saturated (Liminf_llist (lmap lclss_of_state Sts))" and
    no_passive: "FL.passive_subset (Liminf_llist (lmap lclss_of_state Sts)) = {}"
  shows "src.saturated_upto Sts (grounding_of_state (Liminf_state Sts))"
proof -
  define Q where
    "Q = Liminf_llist (lmap Q_of_state Sts)"
  define Ql where
    "Ql = (\<lambda>C. (C, Old)) ` Q"
  define G where
    "G = \<Union> (\<G>_F ` Q)"

  have n_empty: "N_of_state (Liminf_state Sts) = {}" and
    p_empty: "P_of_state (Liminf_state Sts) = {}"
    using no_passive[unfolded FL.passive_subset_def] Liminf_state_def lclss_Liminf_commute
    by fastforce+
  then have limuls_eq: "Liminf_llist (lmap lclss_of_state Sts) = Ql"
    unfolding Ql_def Q_def using Liminf_state_def lclss_Liminf_commute lclss_of_state_def by auto
  have clst_eq: "clss_of_state (Liminf_state Sts) = Q"
    unfolding n_empty p_empty Q_def by (auto simp: Liminf_state_def)
  have gflimuls_eq: "(\<Union>Cl \<in> Ql. \<G>_F (fst Cl)) = G"
    unfolding Ql_def G_def by auto

  have "gd.inferences_from Sts G \<subseteq> src.Ri Sts G"
  proof
    fix \<gamma>
    assume \<gamma>_inf: "\<gamma> \<in> gd.inferences_from Sts G"

    obtain \<iota> where
      \<iota>_inff: "\<iota> \<in> G.Inf_from Q G" and
      \<gamma>: "\<gamma> = old_infer_of \<iota>"
      using \<gamma>_inf
      unfolding gd.inferences_from_def old_infer_from_def G.Inf_from_def old_infer_of_def
    proof (atomize_elim, clarify)
      assume
        g_is: \<open>\<gamma> \<in> gd.ord_\<Gamma> Sts\<close> and
        prems_in: \<open>set_mset (old_side_prems_of \<gamma> + {#old_main_prem_of \<gamma>#}) \<subseteq> G\<close>
      obtain CAs DA AAs As E where main_in: \<open>DA \<in> G\<close> and side_in: \<open>set CAs \<subseteq> G\<close> and
        g_is2: \<open>\<gamma> = old_Infer (mset CAs) DA E\<close> and
        ord_res: \<open>gd.ord_resolve Sts CAs DA AAs As E\<close>
        using g_is prems_in unfolding gd.ord_\<Gamma>_def by auto
      define \<iota>_\<gamma> where "\<iota>_\<gamma> = Infer (CAs @ [DA]) E"
      then have \<open>\<iota>_\<gamma> \<in> G_Inf Q\<close>  using Q_of_state.simps g_is g_is2 ord_res Liminf_state_def S_Q_def
        unfolding gd.ord_\<Gamma>_def G_Inf_def Q_def by auto
      moreover have \<open>set (prems_of \<iota>_\<gamma>) \<subseteq> G\<close>
        using g_is2 prems_in unfolding \<iota>_\<gamma>_def by simp
      moreover have \<open>\<gamma> = old_Infer (mset (side_prems_of \<iota>_\<gamma>)) (main_prem_of \<iota>_\<gamma>) (concl_of \<iota>_\<gamma>)\<close>
        using g_is2 unfolding \<iota>_\<gamma>_def by simp
      ultimately show
        \<open>\<exists>\<iota>. \<iota> \<in> {\<iota> \<in> G_Inf Q. set (prems_of \<iota>) \<subseteq> G} \<and> \<gamma> = old_Infer (mset (side_prems_of \<iota>))
         (main_prem_of \<iota>) (concl_of \<iota>)\<close>
        by blast
    qed
    obtain \<iota>' where
      \<iota>'_inff: "\<iota>' \<in> F.Inf_from Q" and
      \<iota>_in_\<iota>': "\<iota> \<in> \<G>_I Q \<iota>'"
      using G_Inf_overapprox_F_Inf \<iota>_inff unfolding G_def by blast

    note \<iota>'_inf = F.Inf_if_Inf_from[OF \<iota>'_inff]

    let ?olds = "replicate (length (prems_of \<iota>')) Old"

    obtain \<iota>'' and l0 where
      \<iota>'': "\<iota>'' = Infer (zip (prems_of \<iota>') ?olds) (concl_of \<iota>', l0)" and
      \<iota>''_inf: "\<iota>'' \<in> FL_Inf"
      using FL.Inf_F_to_Inf_FL[OF \<iota>'_inf, of ?olds, simplified] by blast

    have "set (prems_of \<iota>'') \<subseteq> Ql"
      using \<iota>'_inff[unfolded F.Inf_from_def, simplified] unfolding \<iota>'' Ql_def by auto
    then have "\<iota>'' \<in> FL.Inf_from Ql"
      unfolding FL.Inf_from_def using \<iota>''_inf by simp
    moreover have "\<iota>' = FL.to_F \<iota>''"
      unfolding \<iota>'' unfolding FL.to_F_def by simp
    ultimately have "\<iota> \<in> G.Red_I Q G"
      using \<iota>_in_\<iota>'
        FL.sat_inf_imp_ground_red_fam_inter[OF satur, unfolded limuls_eq gflimuls_eq, simplified]
      by blast
    then have "G.redundant_infer G \<iota>"
      unfolding G.Red_I_def by auto
    then have \<gamma>_red: "src.redundant_infer G \<gamma>"
      unfolding \<gamma> by (rule new_redundant_infer_imp_old_redundant_infer)
    moreover have "\<gamma> \<in> gd.ord_\<Gamma> Sts"
      using \<gamma>_inf gd.inferences_from_def by blast
    ultimately show "\<gamma> \<in> src.Ri Sts G"
      unfolding src.Ri_def by auto
  qed
  then show ?thesis
    unfolding G_def clst_eq src.saturated_upto_def
    by clarsimp (smt Diff_subset gd.inferences_from_mono subset_eq \<G>_Fset_def)
qed

theorem RP_sound_old_statement:
  assumes
    deriv: "chain (\<leadsto>RP) Sts" and
    bot_in: "{#} \<in> clss_of_state (Liminf_state Sts)"
  shows "\<not> satisfiable (grounding_of_state (lhd Sts))"
  using RP_sound_new_statement[OF deriv bot_in] unfolding F_entails_\<G>_iff \<G>_Fset_def by simp

text \<open>The theorem below is stated differently than the original theorem in \textsf{RP}:
The grounding of the limit might be a strict subset of the limit of the groundings. Because
saturation is neither monotone nor antimonotone, the two results are incomparable. See also
@{thm [source] grounding_of_state_Liminf_state_subseteq}.\<close>

theorem RP_saturated_if_fair_old_statement_altered:
  assumes
    deriv: "chain (\<leadsto>RP) Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}"
  shows "src.saturated_upto Sts (grounding_of_state (Liminf_state Sts))"
proof -
  note fair' = old_fair_imp_new_fair[OF chain_not_lnull[OF deriv] fair empty_Q0]
  show ?thesis
    by (rule saturated_imp_saturated_RP[OF _ fair'(2)], rule RP_saturated_if_fair_new_statement)
      (rule deriv fair')+
qed

corollary RP_complete_if_fair_old_statement:
  assumes
    deriv: "chain (\<leadsto>RP) Sts" and
    fair: "fair_state_seq Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}" and
    unsat: "\<not> satisfiable (grounding_of_state (lhd Sts))"
  shows "{#} \<in> Q_of_state (Liminf_state Sts)"
proof (rule RP_complete_if_fair_new_statement)
  show \<open>\<G>_Fset (N_of_state (lhd Sts) \<union> P_of_state (lhd Sts) \<union> Q_of_state (lhd Sts)) \<TTurnstile>e {{#}}\<close>
    using unsat unfolding F_entails_\<G>_iff by auto
qed (rule deriv old_fair_imp_new_fair[OF chain_not_lnull[OF deriv] fair empty_Q0])+

end

end
