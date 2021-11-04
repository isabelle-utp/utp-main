section \<open>Algorithms on Nondeterministic Generalized Büchi Automata\<close>

theory NGBA_Algorithms
imports
  NGBA_Graphs
  NGBA_Implement
  NBA_Combine
  NBA_Algorithms
  Degeneralization_Refine
begin

  subsection \<open>Operations\<close>

  definition op_language_empty where [simp]: "op_language_empty A \<equiv> NGBA.language A = {}"

  lemmas [autoref_op_pat] = op_language_empty_def[symmetric]

  subsection \<open>Implementations\<close>

  context
  begin

    interpretation autoref_syn by this

    lemma ngba_g_ahs: "ngba_g A = \<lparr> g_V = UNIV, g_E = E_of_succ (\<lambda> p. CAST
      ((\<Union> a \<in> ngba.alphabet A. ngba.transition A a p ::: \<langle>S\<rangle> list_set_rel) ::: \<langle>S\<rangle> ahs_rel bhc)),
      g_V0 = ngba.initial A \<rparr>"
      unfolding ngba_g_def ngba.successors_alt_def CAST_def id_apply autoref_tag_defs by rule

    schematic_goal ngbai_gi:
      notes [autoref_ga_rules] = map2set_to_list
      fixes S :: "('statei \<times> 'state) set"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel"
      shows "(?f :: ?'a, RETURN (ngba_g A)) \<in> ?A"
      unfolding ngba_g_ahs[where S = S and bhc = bhc] by (autoref_monadic (plain))
    concrete_definition ngbai_gi uses ngbai_gi
    lemma ngbai_gi_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      shows "(NGBA_Algorithms.ngbai_gi seq bhc hms, ngba_g) \<in>
        \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> \<langle>unit_rel, S\<rangle> g_impl_rel_ext"
      using ngbai_gi.refine[THEN RETURN_nres_relD] assms unfolding autoref_tag_defs by blast

    schematic_goal ngba_nodes:
      fixes S :: "('statei \<times> 'state) set"
      assumes [simp]: "finite ((g_E (ngba_g A))\<^sup>* `` g_V0 (ngba_g A))"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel"
      shows "(?f :: ?'a, op_reachable (ngba_g A)) \<in> ?R" by autoref
    concrete_definition ngba_nodes uses ngba_nodes
    lemma ngba_nodes_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (NGBA.nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel"
      shows "(NGBA_Algorithms.ngba_nodes seq bhc hms Ai,
        (OP NGBA.nodes ::: \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> \<langle>S\<rangle> ahs_rel bhc) $ A) \<in> \<langle>S\<rangle> ahs_rel bhc"
    proof -
      have 1: "NGBA.nodes A = op_reachable (ngba_g A)" by (auto simp: ngba_g_V0 ngba_g_E_rtrancl)
      have 2: "finite ((g_E (ngba_g A))\<^sup>* `` g_V0 (ngba_g A))" using assms(1) unfolding 1 by simp
      show ?thesis using ngba_nodes.refine assms 2 unfolding autoref_tag_defs 1 by blast
    qed

    lemma ngba_igbg_ahs: "ngba_igbg A = \<lparr> g_V = UNIV, g_E = E_of_succ (\<lambda> p. CAST
      ((\<Union> a \<in> NGBA.alphabet A. NGBA.transition A a p ::: \<langle>S\<rangle> list_set_rel) ::: \<langle>S\<rangle> ahs_rel bhc)), g_V0 = NGBA.initial A,
      igbg_num_acc = length (NGBA.accepting A), igbg_acc = ngba_acc (NGBA.accepting A) \<rparr>"
      unfolding ngba_g_def ngba_igbg_def ngba.successors_alt_def CAST_def id_apply autoref_tag_defs
      unfolding graph_rec.defs
      by simp

    definition "ngba_acc_bs cs p \<equiv> fold (\<lambda> (k, c) bs. if c p then bs_insert k bs else bs) (List.enumerate 0 cs) (bs_empty ())"

    lemma ngba_acc_bs_empty[simp]: "ngba_acc_bs [] p = bs_empty ()" unfolding ngba_acc_bs_def by simp
    lemma ngba_acc_bs_insert[simp]:
      assumes "c p"
      shows "ngba_acc_bs (cs @ [c]) p = bs_insert (length cs) (ngba_acc_bs cs p)"
      using assms unfolding ngba_acc_bs_def by (simp add: enumerate_append_eq)
    lemma ngba_acc_bs_skip[simp]:
      assumes "\<not> c p"
      shows "ngba_acc_bs (cs @ [c]) p = ngba_acc_bs cs p"
      using assms unfolding ngba_acc_bs_def by (simp add: enumerate_append_eq)

    lemma ngba_acc_bs_correct[simp]: "bs_\<alpha> (ngba_acc_bs cs p) = ngba_acc cs p"
    proof (induct cs rule: rev_induct)
      case Nil
      show ?case unfolding ngba_acc_def by simp
    next
      case (snoc c cs)
      show ?case using less_Suc_eq snoc by (cases "c p") (force simp: ngba_acc_def)+
    qed

    lemma ngba_acc_impl_bs[autoref_rules]: "(ngba_acc_bs, ngba_acc) \<in> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel \<rightarrow> S \<rightarrow> \<langle>nat_rel\<rangle> bs_set_rel"
    proof -
      have "(ngba_acc_bs, ngba_acc) \<in> \<langle>Id \<rightarrow> bool_rel\<rangle> list_rel \<rightarrow> Id \<rightarrow> \<langle>nat_rel\<rangle> bs_set_rel"
        by (auto simp: bs_set_rel_def in_br_conv)
      also have "(ngba_acc, ngba_acc) \<in> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel \<rightarrow> S \<rightarrow> \<langle>nat_rel\<rangle> set_rel" by parametricity
      finally show ?thesis by simp
    qed

    schematic_goal ngbai_igbgi:
      notes [autoref_ga_rules] = map2set_to_list
      fixes S :: "('statei \<times> 'state) set"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel"
      shows "(?f :: ?'a, RETURN (ngba_igbg A)) \<in> ?A"
      unfolding ngba_igbg_ahs[where S = S and bhc = bhc] by (autoref_monadic (plain))
    concrete_definition ngbai_igbgi uses ngbai_igbgi
    lemma ngbai_igbgi_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      shows "(NGBA_Algorithms.ngbai_igbgi seq bhc hms, ngba_igbg) \<in>
        \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> igbg_impl_rel_ext unit_rel S"
      using ngbai_igbgi.refine[THEN RETURN_nres_relD] assms unfolding autoref_tag_defs by blast

    schematic_goal ngba_language_empty:
      fixes S :: "('statei \<times> 'state) set"
      assumes [simp]: "igb_fr_graph (ngba_igbg A)"
      assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhs"
      assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
      assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel"
      shows "(?f :: ?'a, do { r \<leftarrow> op_find_lasso_spec (ngba_igbg A); RETURN (r = None)}) \<in> ?A"
      by (autoref_monadic (plain))
    concrete_definition ngba_language_empty uses ngba_language_empty
    lemma nba_language_empty_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (NGBA.nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel"
      shows "(NGBA_Algorithms.ngba_language_empty seq bhc hms Ai,
        (OP op_language_empty ::: \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> bool_rel) $ A) \<in> bool_rel"
    proof -
      have 1: "NGBA.nodes A = op_reachable (ngba_g A)" by (auto simp: ngba_g_V0 ngba_g_E_rtrancl)
      have 2: "finite ((g_E (ngba_g A))\<^sup>* `` g_V0 (ngba_g A))" using assms(1) unfolding 1 by simp
      interpret igb_fr_graph "ngba_igbg A"
        using 2 unfolding ngba_igbg_def ngba_g_def graph_rec.defs ngba_acc_def by unfold_locales auto
      have "(RETURN (NGBA_Algorithms.ngba_language_empty seq bhc hms Ai),
        do { r \<leftarrow> find_lasso_spec; RETURN (r = None) }) \<in> \<langle>bool_rel\<rangle> nres_rel"
        using ngba_language_empty.refine assms igb_fr_graph_axioms by simp
      also have "(do { r \<leftarrow> find_lasso_spec; RETURN (r = None) },
        RETURN (\<not> Ex is_lasso_prpl)) \<in> \<langle>bool_rel\<rangle> nres_rel"
        unfolding find_lasso_spec_def by (refine_vcg) (auto split: option.splits)
      finally have "NGBA_Algorithms.ngba_language_empty seq bhc hms Ai \<longleftrightarrow> \<not> Ex is_lasso_prpl"
        unfolding nres_rel_comp using RETURN_nres_relD by force
      also have "\<dots> \<longleftrightarrow> \<not> Ex is_acc_run" using lasso_prpl_acc_run_iff by auto
      also have "\<dots> \<longleftrightarrow> NGBA.language A = {}" using NGBA_Graphs.acc_run_language is_igb_graph by auto
      finally show ?thesis by simp
    qed

    lemma degeneralize_alt_def: "degeneralize A = nba
      (ngba.alphabet A)
      ((\<lambda> p. (p, 0)) ` ngba.initial A)
      (\<lambda> a (p, k). (\<lambda> q. (q, Degeneralization.count (ngba.accepting A) p k)) ` ngba.transition A a p)
      (degen (ngba.accepting A))"
      unfolding degeneralization.degeneralize_def by auto

    schematic_goal ngba_degeneralize: "(?f :: ?'a, degeneralize) \<in> ?R"
      unfolding degeneralize_alt_def
      using degen_param[autoref_rules] count_param[autoref_rules]
      by autoref
    concrete_definition ngba_degeneralize uses ngba_degeneralize
    lemmas ngba_degeneralize_refine[autoref_rules] = ngba_degeneralize.refine

    schematic_goal nba_intersect':
      assumes [autoref_rules]: "(seq, HOL.eq) \<in> L \<rightarrow> L \<rightarrow> bool_rel"
      shows "(?f, intersect') \<in> \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, T\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, S \<times>\<^sub>r T\<rangle> ngbai_ngba_rel"
      unfolding intersection.product_def by autoref
    concrete_definition nba_intersect' uses nba_intersect'
    lemma nba_intersect'_refine[autoref_rules]:
      assumes "GEN_OP seq HOL.eq (L \<rightarrow> L \<rightarrow> bool_rel)"
      shows "(nba_intersect' seq, intersect') \<in>
        \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, T\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, S \<times>\<^sub>r T\<rangle> ngbai_ngba_rel"
      using nba_intersect'.refine assms unfolding autoref_tag_defs by this

  end

end