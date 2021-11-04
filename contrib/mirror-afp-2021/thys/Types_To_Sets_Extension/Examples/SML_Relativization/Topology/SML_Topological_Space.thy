(* Title: Examples/SML_Relativization/Topology/SML_Topological_Space.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about simple topological spaces\<close>
theory SML_Topological_Space
  imports 
    "../Simple_Orders/SML_Simple_Orders"
    "HOL-Analysis.Elementary_Topology"
    "../Foundations/Transfer_Ext"
    "../Foundations/Lifting_Set_Ext"
begin



subsection\<open>Definitions and common properties\<close>


text\<open>
Some of the entities that are presented in this subsection were 
copied from the theory \<^text>\<open>HOL-Types_To_Sets/Examples/T2_Spaces\<close>.
\<close>

locale topological_space_ow = 
  fixes U :: "'at set" and \<tau> :: "'at set \<Rightarrow> bool"
  assumes open_UNIV[simp, intro]: "\<tau> U"
  assumes open_Int[intro]: 
    "\<lbrakk> S \<subseteq> U; T \<subseteq> U; \<tau> S; \<tau> T \<rbrakk> \<Longrightarrow> \<tau> (S \<inter> T)"
  assumes open_Union[intro]: 
    "\<lbrakk> K \<subseteq> Pow U; \<forall>S\<in>K. \<tau> S \<rbrakk> \<Longrightarrow> \<tau> (\<Union>K)"
begin

context
  includes lifting_syntax
begin

tts_register_sbts \<tau> | U
proof-
  assume dom_ATA: "Domainp ATA = (\<lambda>x. x \<in> U)" 
    and "bi_unique ATA" 
    and "right_total ATA"
  from \<open>bi_unique ATA\<close> \<open>right_total ATA\<close> 
  obtain Rep :: "'a \<Rightarrow> 'at" and Abs :: "'at \<Rightarrow> 'a" where 
    td: "type_definition Rep Abs (Collect (Domainp ATA))" and
    ATA_Rep: "ATA b b' = (b = Rep b')" for b b'
    by (blast dest: ex_type_definition)
  define \<tau>' where \<tau>': "\<tau>' = (image Rep ---> id) \<tau>"
  have Domainp_scr_S: "Domainp (rel_set ATA) = (\<lambda>x. x \<subseteq> U)"
    unfolding Domainp_set by (auto simp: dom_ATA)
  have scr_S_rep[intro, simp]: "rel_set ATA (image Rep a) a" for a 
    unfolding rel_set_def by (auto simp: ATA_Rep)
  have rel_set_eq_rep_set: "rel_set ATA x y \<longleftrightarrow> x = image Rep y" for x y
  proof -
    have "bi_unique (rel_set ATA)" 
      by (simp add: \<open>bi_unique ATA\<close> bi_unique_rel_set)
    from this show ?thesis by (auto dest: bi_uniqueDl)
  qed  
  have "(rel_set ATA ===> (=)) \<tau> \<tau>'"
    unfolding \<tau>' map_fun_apply id_def
    apply(intro rel_funI)
    unfolding rel_set_eq_rep_set
    apply(elim ssubst)
    ..  
  then show " \<exists>\<tau>'. (rel_set ATA ===> (=)) \<tau> \<tau>'" by auto
qed

end

end

locale topological_space_pair_ow = 
  ts\<^sub>1: topological_space_ow U\<^sub>1 \<tau>\<^sub>1 + ts\<^sub>2: topological_space_ow U\<^sub>2 \<tau>\<^sub>2 
  for U\<^sub>1 :: "'at set" and \<tau>\<^sub>1 and U\<^sub>2 :: "'bt set" and \<tau>\<^sub>2

locale topological_space_triple_ow = 
  ts\<^sub>1: topological_space_ow U\<^sub>1 \<tau>\<^sub>1 + 
  ts\<^sub>2: topological_space_ow U\<^sub>2 \<tau>\<^sub>2 +
  ts\<^sub>3: topological_space_ow U\<^sub>3 \<tau>\<^sub>3
  for U\<^sub>1 :: "'at set" and \<tau>\<^sub>1 
    and U\<^sub>2 :: "'bt set" and \<tau>\<^sub>2 
    and U\<^sub>3 :: "'ct set" and \<tau>\<^sub>3
begin

sublocale tsp\<^sub>1\<^sub>2: topological_space_pair_ow U\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 \<tau>\<^sub>2 ..
sublocale tsp\<^sub>1\<^sub>3: topological_space_pair_ow U\<^sub>1 \<tau>\<^sub>1 U\<^sub>3 \<tau>\<^sub>3 ..
sublocale tsp\<^sub>2\<^sub>3: topological_space_pair_ow U\<^sub>2 \<tau>\<^sub>2 U\<^sub>3 \<tau>\<^sub>3 ..
sublocale tsp\<^sub>2\<^sub>1: topological_space_pair_ow U\<^sub>2 \<tau>\<^sub>2 U\<^sub>1 \<tau>\<^sub>1 ..
sublocale tsp\<^sub>3\<^sub>1: topological_space_pair_ow U\<^sub>3 \<tau>\<^sub>3 U\<^sub>1 \<tau>\<^sub>1 ..
sublocale tsp\<^sub>3\<^sub>2: topological_space_pair_ow U\<^sub>3 \<tau>\<^sub>3 U\<^sub>2 \<tau>\<^sub>2 ..

end

inductive generate_topology_on :: "['at set set, 'at set, 'at set] \<Rightarrow> bool" 
  (
    \<open>(in'_topology'_generated'_by _ on _ : \<guillemotleft>open\<guillemotright> _)\<close> 
    [1000, 1000, 1000] 10
  )
  for S :: "'at set set" 
  where
    UNIV: "(in_topology_generated_by S on U : \<guillemotleft>open\<guillemotright> U)"
  | Int: "(in_topology_generated_by S on U : \<guillemotleft>open\<guillemotright> (a \<inter> b))" 
    if "(in_topology_generated_by S on U : \<guillemotleft>open\<guillemotright> a)" 
      and "(in_topology_generated_by S on U : \<guillemotleft>open\<guillemotright> b)" 
      and "a \<subseteq> U" 
      and "b \<subseteq> U"
  | UN: "(in_topology_generated_by S on U : \<guillemotleft>open\<guillemotright> (\<Union>K))"
    if "K \<subseteq> Pow U" 
      and "(\<And>k. k \<in> K \<Longrightarrow> (in_topology_generated_by S on U : \<guillemotleft>open\<guillemotright> k))"
  | Basis: "(in_topology_generated_by S on U : \<guillemotleft>open\<guillemotright> s)" 
      if "s \<in> S" and "s \<subseteq> U"

lemma gto_imp_ss: "(in_topology_generated_by S on U : \<guillemotleft>open\<guillemotright> A) \<Longrightarrow> A \<subseteq> U"
  by (induction rule: generate_topology_on.induct) auto

lemma gt_eq_gto: "generate_topology = (\<lambda>S. generate_topology_on S UNIV)"
proof(intro ext iffI)
  fix S and x :: "'a set"
  assume "generate_topology S x"
  then show "in_topology_generated_by S on UNIV : \<guillemotleft>open\<guillemotright> x"
    by (induction rule: generate_topology.induct)
      (simp_all add: UNIV Int UN Basis)
next
  fix S and x :: "'a set"
  assume gto: "in_topology_generated_by S on UNIV : \<guillemotleft>open\<guillemotright> x"
  define U where U: "U = (UNIV::'a set)"
  from gto have "generate_topology_on S U x" unfolding U .
  from this U show "generate_topology S x"
    by (induction rule: generate_topology_on.induct)
      (
        simp_all add: 
          generate_topology.UNIV 
          generate_topology.Int
          generate_topology.UN
          generate_topology.Basis
      )
qed 

ud \<open>topological_space.closed\<close> (\<open>(with _ : \<guillemotleft>closed\<guillemotright> _)\<close> [1000, 1000] 10)
ud closed' \<open>closed\<close>
ud \<open>topological_space.compact\<close> (\<open>(with _ : \<guillemotleft>compact\<guillemotright> _)\<close> [1000, 1000] 10)
ud compact' \<open>compact\<close>
ud \<open>topological_space.connected\<close> (\<open>(with _ : \<guillemotleft>connected\<guillemotright> _)\<close> [1000, 1000] 10)
ud connected' \<open>connected\<close>
ud \<open>topological_space.islimpt\<close> (\<open>(with _ : _ \<guillemotleft>islimpt\<guillemotright> _)\<close> [1000, 1000, 1000] 60)
ud islimpt' \<open>topological_space_class.islimpt\<close>
ud \<open>interior\<close> (\<open>(with _ : \<guillemotleft>interior\<guillemotright> _)\<close> [1000, 1000] 10)
ud \<open>closure\<close> (\<open>(with _ : \<guillemotleft>closure\<guillemotright> _)\<close> [1000, 1000] 10)
ud \<open>frontier\<close> (\<open>(with _ : \<guillemotleft>frontier\<guillemotright> _)\<close> [1000, 1000] 10)
ud \<open>countably_compact\<close> (\<open>(with _ : \<guillemotleft>countably'_compact\<guillemotright> _)\<close> [1000, 1000] 10)

definition topological_basis_with :: "['a set \<Rightarrow> bool, 'a set set] \<Rightarrow> bool"
  (\<open>(with _ : \<guillemotleft>topological'_basis\<guillemotright> _)\<close> [1000, 1000] 10)
  where
  "(with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B) = 
    (\<Union>B = UNIV \<and> (\<forall>b \<in> B. \<tau> b) \<and> (\<forall>q. \<tau> q \<longrightarrow> (\<exists>B'\<subseteq>B. \<Union>B' = q)))"

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule, transfer_rule]: "Domainp A = (\<lambda>x. x \<in> U)"
    and [transfer_rule]: "bi_unique A" "right_total A" 
  trp (?'a A)
  in closed_ow: closed.with_def 
    (\<open>(on _ with _ : \<guillemotleft>closed\<guillemotright> _)\<close> [1000, 1000] 10)
    and compact_ow: compact.with_def
      (\<open>(on _ with _ : \<guillemotleft>compact\<guillemotright> _)\<close> [1000, 1000, 1000] 10)
    and connected_ow: connected.with_def 
      (\<open>(on _ with _ : \<guillemotleft>connected\<guillemotright> _)\<close> [1000, 1000, 1000] 10)
    and islimpt_ow: islimpt.with_def 
      (\<open>(on _ with _ : _ \<guillemotleft>islimpt\<guillemotright> _)\<close> [1000, 1000, 1000, 1000] 10)
    and interior_ow: interior.with_def
      (\<open>(on _ with _ : \<guillemotleft>interior\<guillemotright> _)\<close> [1000, 1000, 1000] 10)
    and closure_ow: closure.with_def 
      (\<open>(on _ with _ : \<guillemotleft>closure\<guillemotright> _)\<close> [1000, 1000, 1000] 10)
    and frontier_ow: frontier.with_def 
      (\<open>(on _ with _ : \<guillemotleft>frontier\<guillemotright> _)\<close> [1000, 1000, 1000] 10)
    and countably_compact_ow: countably_compact.with_def
      (\<open>(on _ with _ : \<guillemotleft>countably'_compact\<guillemotright> _)\<close> [1000, 1000, 1000] 10)

context topological_space_ow
begin

abbreviation closed where "closed \<equiv> closed_ow U \<tau>"
abbreviation compact where "compact \<equiv> compact_ow U \<tau>"
abbreviation connected where "connected \<equiv> connected_ow U \<tau>"
abbreviation islimpt (infixr \<open>\<guillemotleft>islimpt\<guillemotright>\<close> 60) 
  where "x \<guillemotleft>islimpt\<guillemotright> S \<equiv> on U with \<tau> : x \<guillemotleft>islimpt\<guillemotright> S"
abbreviation interior where "interior \<equiv> interior_ow U \<tau>"
abbreviation closure where "closure \<equiv> closure_ow U \<tau>"
abbreviation frontier where "frontier \<equiv> frontier_ow U \<tau>"
abbreviation countably_compact 
  where "countably_compact \<equiv> countably_compact_ow U \<tau>"

end

context
  includes lifting_syntax
begin

private lemma Domainp_fun_rel_eq_subset:
  fixes A :: "['a, 'c] \<Rightarrow> bool"
  fixes B :: "['b, 'd] \<Rightarrow> bool"
  assumes "bi_unique A" "bi_unique B"
  shows 
    "Domainp (A ===> B) = 
      (\<lambda>f. f ` (Collect (Domainp A)) \<subseteq> (Collect (Domainp B)))"
proof(intro ext, standard)
  let ?sA = "Collect (Domainp A)" and ?sB = "(Collect (Domainp B))"  
  fix f assume "Domainp (A ===> B) f" show "f ` ?sA \<subseteq> ?sB"
  proof(clarsimp)
    fix x x' assume "A x x'"
    from \<open>Domainp (A ===> B) f\<close> obtain f' where f': 
      "A x x' \<Longrightarrow> B (f x) (f' x')" for x x'
      unfolding rel_fun_def by auto
    with \<open>A x x'\<close> have "B (f x) (f' x')" by simp
    thus "Domainp B (f x)" by auto
  qed
next
  let ?sA = "Collect (Domainp A)" and ?sB = "(Collect (Domainp B))"  
  fix f assume "f ` ?sA \<subseteq> ?sB"
  define f' where f': "f' = (\<lambda>x'. (THE y'. \<exists>x. A x x' \<and> B (f x) y'))"
  have "(A ===> B) f f'"
  proof(intro rel_funI)
    fix x x' assume "A x x'"
    then have "f x \<in> ?sB" using \<open>f ` ?sA \<subseteq> ?sB\<close> by auto
    then obtain y' where y': "B (f x) y'" by clarsimp
    have "f' x' = y'" unfolding f'
    proof 
      from \<open>A x x'\<close> y' show "\<exists>x. A x x' \<and> B (f x) y'" by auto
      {
        fix y'' assume "\<exists>x. A x x' \<and> B (f x) y''"
        then obtain x'' where x'': "A x'' x' \<and> B (f x'') y''" by clarsimp
        with assms(1) have "x'' = x" using \<open>A x x'\<close> by (auto dest: bi_uniqueDl)
        with y' x'' have "y'' = y'" using assms(2) by (auto dest: bi_uniqueDr)
      }
      thus "\<exists>x. A x x' \<and> B (f x) y'' \<Longrightarrow> y'' = y'" for y'' by simp
    qed
    thus "B (f x) (f' x')" using y' by simp 
  qed
  thus "Domainp (A ===> B) f" by auto
qed

private lemma Ex_rt_bu_transfer[transfer_rule]:
  fixes A :: "['a, 'c] \<Rightarrow> bool"
  fixes B :: "['b, 'd] \<Rightarrow> bool"
  assumes [transfer_rule]: "bi_unique A" "right_total A" "bi_unique B"
  shows 
    "(((B ===> A) ===> (=)) ===> (=)) 
      (Bex (Collect (\<lambda>f. f ` (Collect (Domainp B)) \<subseteq> (Collect (Domainp A))))) 
      Ex"
proof-
  from assms(3,1) have domainp_eq_ss:
    "Domainp (B ===> A) = 
      (\<lambda>f. f ` (Collect (Domainp B)) \<subseteq> (Collect (Domainp A)))"
    by (rule Domainp_fun_rel_eq_subset)
  have "right_total (B ===> A)" 
    using assms by (simp add: bi_unique_alt_def right_total_fun)
  then have     
    "(((B ===> A) ===> (=)) ===> (=)) (Bex (Collect (Domainp (B ===> A)))) Ex"
    by (simp add: right_total_Ex_transfer)
  thus ?thesis unfolding domainp_eq_ss by simp
qed

end

definition topological_basis_ow :: 
  "['a set, 'a set \<Rightarrow> bool, 'a set set] \<Rightarrow> bool"
  (\<open>(on _ with _ : \<guillemotleft>topological'_basis\<guillemotright> _)\<close> [1000, 1000, 1000] 10) 
  where
    "(on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B) =
      (\<Union>B = U \<and> (\<forall>b \<in> B. \<tau> b) \<and> (\<forall>q \<subseteq> U. \<tau> q \<longrightarrow> (\<exists>B'\<subseteq> B. \<Union>B' = q)))"

context topological_space
begin

lemma topological_basis_with[ud_with]: 
  "topological_basis = topological_basis_with open"
  unfolding topological_basis_def topological_basis_with_def Ball_def
  by (intro ext) (metis Union_mono open_UNIV top.extremum_uniqueI)

end



subsection\<open>Transfer rules\<close>


text\<open>Some of the entities that are presented in this subsectionwere 
copied from \<^text>\<open>HOL-Types_To_Sets/Examples/T2_Spaces\<close>.\<close>

context 
  includes lifting_syntax 
begin

lemmas vimage_transfer[transfer_rule] = vimage_transfer

lemma topological_space_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "((rel_set A ===> (=)) ===> (=)) 
      (topological_space_ow (Collect (Domainp A))) class.topological_space"
  unfolding topological_space_ow_def class.topological_space_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Pow_def Ball_Collect[symmetric]
  by auto

lemma generate_topology_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "((rel_set (rel_set A)) ===> (rel_set A ===> (=))) 
      (\<lambda>B. generate_topology_on B (Collect (Domainp A))) generate_topology"
proof(intro rel_funI, standard)
  fix BL BR xl xr
  assume 
    rsrsT_BLR: "rel_set (rel_set A) BL BR" and 
    rsT_xl_xr: "rel_set A xl xr" and 
    gto: "generate_topology_on BL (Collect (Domainp A)) xl" 
  define CDT where CDT: "CDT = (Collect (Domainp A))"
  with gto have gto_CDT: "generate_topology_on BL CDT xl" by simp
  from gto_CDT CDT rsrsT_BLR rsT_xl_xr show "generate_topology BR xr"
  proof(induction arbitrary: xr rule: generate_topology_on.induct)
    case (UNIV S) show ?case
    proof -
      from assms UNIV.prems have "xr = UNIV" 
        by (meson bi_uniqueDr bi_unique_rel_set right_total_UNIV_transfer)
      thus "generate_topology BR xr" by (simp add: generate_topology.UNIV)
    qed
  next
    case (Int S a b) show ?case 
    proof -
      from Int.hyps(3) Int.prems(1) obtain a' where a': "rel_set A a a'"
        by (metis Ball_Collect Domainp_iff Domainp_set)
      from Int.hyps(4) Int.prems(1) obtain b' where b': "rel_set A b b'" 
        by (metis Ball_Collect Domainp_iff Domainp_set)
      from Int.prems(1) Int.prems(2) a' have gt_a': "generate_topology BR a'" 
         by (rule Int.IH(1))
      from Int.prems(1) Int.prems(2) b' have gt_b': "generate_topology BR b'" 
        by (rule Int.IH(2))
      from gt_a' gt_b' have "generate_topology BR (a' \<inter> b')" 
        by (rule generate_topology.Int)
      also from assms(1) a' b' Int.prems(3) have "a' \<inter> b' = xr" 
        by (rule bi_unique_intersect_r)
      ultimately show "generate_topology BR xr" by simp      
    qed
  next
    case (UN K S) thus ?case
    proof -
      define K' where K': "K' = {(x, y). rel_set A x y} `` K" (is "K' = ?K'")
      have Union_ss_CDT: "\<Union>K \<subseteq> Collect (Domainp A)"
        by (metis CollectI Domainp.DomainI UN.prems(3) rel_setD1 subsetI)
      from assms(1) Union_ss_CDT UN.prems(3) have "\<Union>?K' = xr"
        by (rule bi_unique_Union_r)
      then have UK_eq_xr: "\<Union>K' = xr" unfolding K' .
      have "k' \<in> K' \<Longrightarrow> generate_topology BR k'" for k'
      proof -
        assume k'_in_K': "k' \<in> K'"
        then obtain k where k: "rel_set A k k'" unfolding K' by auto
        from assms(1) have "bi_unique (rel_set A)" by (rule bi_unique_rel_set)
        with k have "\<exists>!k. rel_set A k k'" by (meson bi_uniqueDl)
        with k'_in_K' k have k_in_K: "k \<in> K" unfolding K' by auto
        from k_in_K UN.prems(1,2) k show "generate_topology BR k'" 
          by (rule UN.IH)
      qed
      then have "generate_topology BR (\<Union>K')" by (rule generate_topology.UN)
      with UK_eq_xr show "generate_topology BR xr" by simp     
    qed
  next
    case (Basis xl S) thus ?case 
      using assms(1)
      by (metis Int_absorb1 bi_unique_intersect_r generate_topology.Basis 
          rel_setD1 subset_refl)
  qed
next
  fix BL BR xl xr
  assume rsrsT_BLR: "rel_set (rel_set A) BL BR" 
    and rsT_xl_xr: "rel_set A xl xr" 
    and gt: "generate_topology BR xr"  
  from gt rsrsT_BLR rsT_xl_xr show 
    "generate_topology_on BL (Collect (Domainp A)) xl"
  proof(induction arbitrary: xl rule: generate_topology.induct)
    case UNIV thus ?case using assms 
      by (metis bi_uniqueDl bi_unique_rel_set generate_topology_on.simps 
          right_total_UNIV_transfer)
  next
    case (Int a' b') show ?case
    proof -
      from assms(2) obtain a where a: "rel_set A a a'"
        by (meson right_totalE right_total_rel_set)
      from assms(2) obtain b where b: "rel_set A b b'" 
        by (meson right_totalE right_total_rel_set)
      from Int.prems(1) a have gto_a: 
        "generate_topology_on BL {x. Domainp A x} a"
        by (rule Int.IH(1))
      from Int.prems(1) b have gto_b: 
        "generate_topology_on BL {x. Domainp A x} b"
        by (rule Int.IH(2))
      from a have a_ss_DT: "a \<subseteq> {x. Domainp A x}"
        by auto (meson Domainp.DomainI rel_setD1)
      from b have b_ss_DT: "b \<subseteq> {x. Domainp A x}"
        by auto (meson Domainp.DomainI rel_setD1)
      from gto_a gto_b a_ss_DT b_ss_DT have 
        "generate_topology_on BL {x. Domainp A x} (a \<inter> b)" 
        by (rule generate_topology_on.Int)
      also from assms(1) a b Int.prems(2) have "a \<inter> b = xl" 
        by (rule bi_unique_intersect_l)
      ultimately show "generate_topology_on BL {a. Domainp A a} xl" by simp      
    qed
  next
    case (UN K') thus ?case
    proof -
      define K where K: "K = {(x, y). rel_set (\<lambda>y x. A x y) x y} `` K'" 
        (is "K = ?K")
      from assms(2) have Union_ss_CRT: "\<Union>K' \<subseteq> Collect (Rangep A)"
        by (auto simp add: Domainp_iff right_total_def)
      from assms(1) Union_ss_CRT UN.prems(2) have "\<Union>?K = xl"
        by (rule bi_unique_Union_l)
      then have UK_eq_xr: "\<Union>K = xl" unfolding K .
      then have "K \<subseteq> Pow xl" by blast
      moreover from UN.prems(2) have "xl \<subseteq> {x. Domainp A x}" 
        unfolding rel_set_def by blast
      ultimately have UN_prem_1: "K \<subseteq> Pow {x. Domainp A x}" by auto
      have UN_prem_2:
        "k \<in> K \<Longrightarrow> generate_topology_on BL {x. Domainp A x} k" for k
      proof -
        assume k_in_K: "k \<in> K"
        with UN_prem_1 have k_ss_DT: "k \<subseteq> {x. Domainp A x}" by auto
        with k_in_K obtain k' where k': "rel_set (\<lambda>y x. A x y) k' k"
          unfolding K Ball_Collect[symmetric] by blast
        from assms(1) have "bi_unique (\<lambda>y x. A x y)" 
          unfolding bi_unique_def by simp
        then have "bi_unique (rel_set (\<lambda>y x. A x y))" 
          by (rule bi_unique_rel_set)
        with k' have "\<exists>!k'. rel_set (\<lambda>y x. A x y) k' k" by (meson bi_uniqueDl)
        with k_in_K k' have k'_in_K': "k' \<in> K'" unfolding K by blast
        from k' have rsT_kk': "rel_set A k k'" unfolding rel_set_def by auto
        from k'_in_K' UN.prems(1) rsT_kk' show 
          "generate_topology_on BL {x. Domainp A x} k"
          by (rule UN.IH)
      qed
      from UN_prem_1 UN_prem_2 have 
        "generate_topology_on BL {x. Domainp A x} (\<Union>K)" 
        by (rule generate_topology_on.UN)
      with UK_eq_xr show "generate_topology_on BL {a. Domainp A a} xl" by simp           
    qed
  next
    case (Basis xr) thus ?case
    proof -
      assume xr_in_BR: "xr \<in> BR" 
        and rsrsT_BL_BR: "rel_set (rel_set A) BL BR" 
        and rsT_xl_xr: "rel_set A xl xr"
      with assms(1) have "xl \<in> BL"
        by (metis bi_uniqueDl bi_unique_rel_set rel_setD2)
      also with rsrsT_BL_BR  have "xl \<subseteq> {a. Domainp A a}" 
        unfolding Ball_Collect[symmetric] by (meson Domainp.DomainI rel_setD1)
      ultimately show "generate_topology_on BL {a. Domainp A a} xl"
        by (rule generate_topology_on.Basis)
    qed
  qed
qed

lemma topological_basis_with_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((rel_set A ===> (=)) ===> (rel_set (rel_set A)) ===> (=)) 
      (topological_basis_ow (Collect (Domainp A))) topological_basis_with"
  unfolding topological_basis_ow_def topological_basis_with_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Ball_Collect[symmetric]
  apply(clarsimp, intro ext iffI)
  subgoal by (metis UnionI)
  subgoal by metis
  done

end



subsection\<open>Relativization\<close>

tts_context
  tts: (?'a to \<open>U\<^sub>1::'a set\<close>) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
begin

tts_lemma generate_topology_Union:
  assumes "U\<^sub>1 \<noteq> {}"
    and "U\<^sub>2 \<noteq> {}"
    and "I \<subseteq> U\<^sub>1"
    and "S \<subseteq> Pow U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>1. K (x::'a) \<subseteq> U\<^sub>2"
    and 
      "\<And>k. \<lbrakk>k \<in> U\<^sub>1; k \<in> I\<rbrakk> \<Longrightarrow> 
        in_topology_generated_by S on U\<^sub>2 : \<guillemotleft>open\<guillemotright> (K k)"
  shows "in_topology_generated_by S on U\<^sub>2 : \<guillemotleft>open\<guillemotright> (\<Union> (K ` I))"
    is generate_topology_Union.

end

tts_context
  tts: (?'a to \<open>U::'a set\<close>)
  rewriting ctr_simps
  eliminating through
    (unfold topological_space_ow_def; auto intro: generate_topology_on.intros)
begin

tts_lemma topological_space_generate_topology:
  shows "topological_space_ow U (generate_topology_on S U)"
    is topological_space_generate_topology.

end

context topological_space_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating through (metis open_UNIV)
begin

tts_lemma open_empty[simp]:
  shows "\<tau> {}"
    is topological_space_class.open_empty.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating through 
    (
      unfold 
        closed_ow_def 
        compact_ow_def
        connected_ow_def 
        interior_ow_def 
        closure_ow_def
        frontier_ow_def, 
      auto
    )
begin

tts_lemma closed_empty[simp]: "closed {}"
  is topological_space_class.closed_empty.
    
tts_lemma closed_UNIV[simp]: "closed U"
  is topological_space_class.closed_UNIV.
    
tts_lemma compact_empty[simp]: "compact {}"
  is topological_space_class.compact_empty.
    
tts_lemma connected_empty[simp]: "connected {}"
  is topological_space_class.connected_empty.
    
tts_lemma interior_empty[simp]: "interior {} = {}"
  is interior_empty.
    
tts_lemma closure_empty[simp]: "closure {} = {}"
  is closure_empty.
    
tts_lemma closure_UNIV[simp]: "closure U = U"
  is closure_UNIV.
    
tts_lemma frontier_empty[simp]: "frontier {} = {}"
  is frontier_empty.
    
tts_lemma frontier_UNIV[simp]: "frontier U = {}"
  is frontier_UNIV.
    
end  

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating through (auto simp: UNIV inj_on_def)
begin

tts_lemma connected_Union:
  assumes "S \<subseteq> Pow U" and "\<And>s. s \<in> S \<Longrightarrow> connected s" and "\<Inter> S \<inter> U \<noteq> {}"
  shows "connected (\<Union> S)"
    given Topological_Spaces.connected_Union
    by simp

tts_lemma connected_Un:
  assumes "s \<subseteq> U"
    and "t \<subseteq> U"
    and "connected s"
    and "connected t"
    and "s \<inter> t \<noteq> {}"
  shows "connected (s \<union> t)"
    is Topological_Spaces.connected_Un.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> and \<open>?A \<subseteq> ?B\<close>
  through (auto simp: UNIV inj_on_def)
begin

tts_lemma connected_sing:
  assumes "x \<in> U"
  shows "connected {x}"
  is topological_space_class.connected_sing.
    
tts_lemma topological_basisE:
  assumes "B \<subseteq> Pow U"
    and "O' \<subseteq> U"
    and "x \<in> U"
    and "on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B"
    and "\<tau> O'"
    and "x \<in> O'"
    and "\<And>B'. \<lbrakk>B' \<subseteq> U; B' \<in> B; x \<in> B'; B' \<subseteq> O'\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
is topological_space_class.topological_basisE.
    
tts_lemma islimptE:
  assumes "x \<in> U"
    and "S \<subseteq> U"
    and "T \<subseteq> U"
    and "x \<guillemotleft>islimpt\<guillemotright> S"
    and "x \<in> T"
    and "\<tau> T"
    and "\<And>y. \<lbrakk>y \<in> U; y \<in> S; y \<in> T; y \<noteq> x\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is Elementary_Topology.islimptE.
    
tts_lemma islimpt_subset:
  assumes "x \<in> U" and "T \<subseteq> U" and "x \<guillemotleft>islimpt\<guillemotright> S" and "S \<subseteq> T"
  shows "x \<guillemotleft>islimpt\<guillemotright> T"
    is Elementary_Topology.islimpt_subset.
    
tts_lemma islimpt_UNIV_iff:
  assumes "x \<in> U"
  shows "x \<guillemotleft>islimpt\<guillemotright> U = (\<not> \<tau> {x})"
    is Elementary_Topology.islimpt_UNIV_iff.
    
tts_lemma islimpt_punctured:
  assumes "x \<in> U" and "S \<subseteq> U"
  shows "x \<guillemotleft>islimpt\<guillemotright> S = x \<guillemotleft>islimpt\<guillemotright> S - {x}"
    is Elementary_Topology.islimpt_punctured.
    
tts_lemma islimpt_EMPTY:
  assumes "x \<in> U"
  shows "\<not> x \<guillemotleft>islimpt\<guillemotright> {}"
    is Elementary_Topology.islimpt_EMPTY.
    
tts_lemma islimpt_Un:
  assumes "x \<in> U" and "S \<subseteq> U" and "T \<subseteq> U"
  shows "x \<guillemotleft>islimpt\<guillemotright> S \<union> T = (x \<guillemotleft>islimpt\<guillemotright> S \<or> x \<guillemotleft>islimpt\<guillemotright> T)"
    is Elementary_Topology.islimpt_Un.
    
tts_lemma interiorI:
  assumes "x \<in> U" and "S \<subseteq> U" and "\<tau> T" and "x \<in> T" and "T \<subseteq> S"
  shows "x \<in> interior S"
    is Elementary_Topology.interiorI.

tts_lemma islimpt_in_closure:
  assumes "x \<in> U" and "S \<subseteq> U"
  shows "x \<guillemotleft>islimpt\<guillemotright> S = (x \<in> closure (S - {x}))"
    is Elementary_Topology.islimpt_in_closure.

tts_lemma compact_sing:
  assumes "a \<in> U"
  shows "compact {a}"
    is Elementary_Topology.compact_sing.
    
tts_lemma compact_insert:
  assumes "s \<subseteq> U" and "x \<in> U" and "compact s"
  shows "compact (insert x s)"
    is Elementary_Topology.compact_insert.
    
tts_lemma open_Un:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "\<tau> S" and "\<tau> T"
  shows "\<tau> (S \<union> T)"
    is topological_space_class.open_Un.
    
tts_lemma open_Inter:
  assumes "S \<subseteq> Pow U" and "finite S" and "Ball S \<tau>"
  shows "\<tau> (\<Inter> S \<inter> U)"
    is topological_space_class.open_Inter.
    
tts_lemma openI:
  assumes "S \<subseteq> U" and "\<And>x. \<lbrakk>x \<in> U; x \<in> S\<rbrakk> \<Longrightarrow> \<exists>y\<subseteq>U. \<tau> y \<and> y \<subseteq> S \<and> x \<in> y"
  shows "\<tau> S"
    given topological_space_class.openI by (meson PowI)
    
tts_lemma closed_Un:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "closed S" and "closed T"
  shows "closed (S \<union> T)"
    is topological_space_class.closed_Un.

tts_lemma closed_Int:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "closed S" and "closed T"
  shows "closed (S \<inter> T)"
  is topological_space_class.closed_Int.

tts_lemma open_Collect_conj:
  assumes "\<tau> {x. P x \<and> x \<in> U}" and "\<tau> {x. Q x \<and> x \<in> U}"
  shows "\<tau> {x \<in> U. P x \<and> Q x}"
    is topological_space_class.open_Collect_conj.

tts_lemma open_Collect_disj:
  assumes "\<tau> {x. P x \<and> x \<in> U}"
    and "\<tau> {x. Q x \<and> x \<in> U}"
  shows "\<tau> {x \<in> U. P x \<or> Q x}"
    is topological_space_class.open_Collect_disj.

tts_lemma open_Collect_imp:
  assumes "closed {x. P x \<and> x \<in> U}"
    and "\<tau> {x. Q x \<and> x \<in> U}"
  shows "\<tau> {x \<in> U. P x \<longrightarrow> Q x}"
    is topological_space_class.open_Collect_imp.

tts_lemma open_Collect_const: "\<tau> {x. P \<and> x \<in> U}"
    is topological_space_class.open_Collect_const.
    
tts_lemma closed_Collect_conj:
  assumes "closed {x. P x \<and> x \<in> U}" and "closed {x. Q x \<and> x \<in> U}"
  shows "closed {x \<in> U. P x \<and> Q x}"
    is topological_space_class.closed_Collect_conj.

tts_lemma closed_Collect_disj:
  assumes "closed {x. P x \<and> x \<in> U}" and "closed {x. Q x \<and> x \<in> U}"
  shows "closed {x \<in> U. P x \<or> Q x}"
    is topological_space_class.closed_Collect_disj.

tts_lemma closed_Collect_imp:
  assumes "\<tau> {x. P x \<and> x \<in> U}" and "closed {x. Q x \<and> x \<in> U}"
  shows "closed {x \<in> U. P x \<longrightarrow> Q x}"
    is topological_space_class.closed_Collect_imp.
    
tts_lemma compact_Int_closed:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "compact S" and "closed T"
  shows "compact (S \<inter> T)"
  is topological_space_class.compact_Int_closed.
    
tts_lemma compact_diff:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "compact S" and "\<tau> T"
  shows "compact (S - T)"
  is topological_space_class.compact_diff.
    
tts_lemma connectedD:
  assumes "U \<subseteq> U"
    and "V \<subseteq> U"
    and "connected A"
    and "\<tau> U"
    and "\<tau> V"
    and "U \<inter> (V \<inter> A) = {}"
    and "A \<subseteq> U \<union> V"
  shows "U \<inter> A = {} \<or> V \<inter> A = {}"
  is topological_space_class.connectedD.

tts_lemma topological_basis_open:
  assumes "B \<subseteq> Pow U" and "on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B" and "X \<in> B"
  shows "\<tau> X"
    is topological_space_class.topological_basis_open.

tts_lemma topological_basis_imp_subbasis:
  assumes "B \<subseteq> Pow U" and "on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B"
  shows "\<forall>s\<subseteq>U. \<tau> s = (in_topology_generated_by B on U : \<guillemotleft>open\<guillemotright> s)"
  is topological_space_class.topological_basis_imp_subbasis.

tts_lemma connected_closedD:
  assumes "A \<subseteq> U"
    and "B \<subseteq> U"
    and "connected s"
    and "A \<inter> (B \<inter> s) = {}"
    and "s \<subseteq> A \<union> B"
    and "closed A"
    and "closed B"
  shows "A \<inter> s = {} \<or> B \<inter> s = {}"
    is Topological_Spaces.connected_closedD.
    
tts_lemma connected_diff_open_from_closed:
  assumes "u \<subseteq> U"
    and "s \<subseteq> t"
    and "t \<subseteq> u"
    and "\<tau> s"
    and "closed t"
    and "connected u"
    and "connected (t - s)"
  shows "connected (u - s)"
    is Topological_Spaces.connected_diff_open_from_closed.

tts_lemma interior_maximal:
  assumes "S \<subseteq> U" and "T \<subseteq> S" and "\<tau> T"
  shows "T \<subseteq> interior S"
    is Elementary_Topology.interior_maximal.

tts_lemma open_subset_interior:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "\<tau> S"
  shows "(S \<subseteq> interior T) = (S \<subseteq> T)"
    is Elementary_Topology.open_subset_interior.

tts_lemma interior_mono:
  assumes "T \<subseteq> U" and "S \<subseteq> T"
  shows "interior S \<subseteq> interior T"
    is Elementary_Topology.interior_mono.

tts_lemma interior_Int:
  assumes "S \<subseteq> U" and "T \<subseteq> U"
  shows "interior (S \<inter> T) = interior S \<inter> interior T"
    is Elementary_Topology.interior_Int.

tts_lemma interior_closed_Un_empty_interior:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "closed S" and "interior T = {}"
  shows "interior (S \<union> T) = interior S"
    is Elementary_Topology.interior_closed_Un_empty_interior.

tts_lemma countably_compact_imp_acc_point:
  assumes "local.countably_compact s"
    and "countable t"
    and "infinite t"
    and "t \<subseteq> s"
  shows "\<exists>x\<in>s. \<forall>U\<in>Pow U. \<tau> U \<and> x \<in> U \<longrightarrow> infinite (U \<inter> t)"
    is Elementary_Topology.countably_compact_imp_acc_point.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> 
    through (auto simp: UNIV inj_on_def)
begin

tts_lemma first_countableI:
  assumes "\<A> \<subseteq> Pow U"
    and "x \<in> U"
    and "countable \<A>"
    and "\<And>A. \<lbrakk>A \<in> \<A>\<rbrakk> \<Longrightarrow> x \<in> A"
    and "\<And>A. \<lbrakk>A \<in> \<A>\<rbrakk> \<Longrightarrow> \<tau> A"
    and "\<And>S. \<lbrakk>\<tau> S; x \<in> S\<rbrakk> \<Longrightarrow> \<exists>A\<in>\<A>. A \<subseteq> S"
  shows "\<exists>\<A>\<in>{f. range f \<subseteq> Pow U}. 
    (\<forall>i. \<tau> (\<A> (i::nat)) \<and> x \<in> \<A> i) \<and> 
    (\<forall>S\<in>Pow U. \<tau> S \<and> x \<in> S \<longrightarrow> (\<exists>i. \<A> i \<subseteq> S))"
    given topological_space_class.first_countableI by auto

tts_lemma islimptI:
  assumes "x \<in> U"
    and "S \<subseteq> U"
    and "\<And>T. \<lbrakk>x \<in> T; \<tau> T\<rbrakk> \<Longrightarrow> \<exists>y\<in>S. y \<in> T \<and> y \<noteq> x"
  shows "x \<guillemotleft>islimpt\<guillemotright> S"
    given Elementary_Topology.islimptI
  by simp
    
tts_lemma interiorE:
  assumes "x \<in> U"
    and "S \<subseteq> U"
    and "x \<in> interior S"
    and "\<And>T. \<lbrakk>T \<subseteq> U; \<tau> T; x \<in> T; T \<subseteq> S\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is Elementary_Topology.interiorE.
    
tts_lemma closure_iff_nhds_not_empty:
  assumes "x \<in> U" and "X \<subseteq> U"
  shows 
    "(x \<in> closure X) = 
      (\<forall>y\<subseteq>U. \<forall>z\<subseteq>U. z \<subseteq> y \<longrightarrow> \<tau> z \<longrightarrow> x \<in> z \<longrightarrow> X \<inter> y \<noteq> {})"
    given Elementary_Topology.closure_iff_nhds_not_empty by auto

tts_lemma basis_dense:
  assumes "B \<subseteq> Pow U"
    and "\<forall>x\<subseteq>U. f x \<in> U"
    and "on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B"
    and "\<And>B'. \<lbrakk>B' \<subseteq> U; B' \<noteq> {}\<rbrakk> \<Longrightarrow> f B' \<in> B'"
  shows "\<forall>x\<subseteq>U. \<tau> x \<longrightarrow> x \<noteq> {} \<longrightarrow> (\<exists>y\<in>B. f y \<in> x)"
    given topological_space_class.basis_dense by auto
    
tts_lemma inj_setminus:
  assumes "A \<subseteq> Pow U"
  shows "inj_on (\<lambda>S. - S \<inter> U) A"
    is topological_space_class.inj_setminus.
    
end


tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> and \<open>?S \<subseteq> U\<close> through
    (
      unfold 
        closed_ow_def 
        compact_ow_def   
        connected_ow_def 
        interior_ow_def
        topological_basis_ow_def
        closure_ow_def 
        frontier_ow_def
        countably_compact_ow_def,
      auto 
    )      
begin

tts_lemma closed_Inter:
  assumes "K \<subseteq> Pow U" and "Ball K closed"
  shows "closed (\<Inter> K \<inter> U)"
  is topological_space_class.closed_Inter.
    
tts_lemma closed_Union:
  assumes "S \<subseteq> Pow U" and "finite S" and "Ball S closed"
  shows "closed (\<Union> S)"
  is topological_space_class.closed_Union.
    
tts_lemma open_closed:
  assumes "S \<subseteq> U"
  shows "\<tau> S = closed (- S \<inter> U)"
    is topological_space_class.open_closed.
    
tts_lemma closed_open:
  shows "closed S = \<tau> (- S \<inter> U)"
    is topological_space_class.closed_open.
    
tts_lemma open_Diff:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "\<tau> S" and "closed T"
  shows "\<tau> (S - T)"
    is topological_space_class.open_Diff.
    
tts_lemma closed_Diff:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "closed S" and "\<tau> T"
  shows "closed (S - T)"
    is topological_space_class.closed_Diff.
    
tts_lemma open_Compl:
  assumes "closed S"
  shows "\<tau> (- S \<inter> U)"
    is topological_space_class.open_Compl.
    
tts_lemma closed_Compl:
  assumes "S \<subseteq> U" and "\<tau> S"
  shows "closed (- S \<inter> U)"
    is topological_space_class.closed_Compl.

tts_lemma open_Collect_neg:
  assumes "closed {x \<in> U. P x}"
  shows "\<tau> {x \<in> U. \<not> P x}"
    given topological_space_class.open_Collect_neg
  by (simp add: ctr_simps_conj_commute)

tts_lemma closed_Collect_neg:
  assumes "\<tau> {x\<in>U. P x}"
  shows "closed {x\<in>U. \<not> P x}"
    given topological_space_class.closed_Collect_neg
  by (simp add: ctr_simps_conj_commute)

tts_lemma closed_Collect_const: "closed {x \<in> U. P}"
  given topological_space_class.closed_Collect_const 
  by (simp add: ctr_simps_conj_commute)
    
tts_lemma connectedI:
  assumes 
    "\<And>A B. 
      \<lbrakk>
        A \<subseteq> U; 
        B \<subseteq> U; 
        \<tau> A; 
        \<tau> B; 
        A \<inter> U \<noteq> {}; 
        B \<inter> U \<noteq> {}; 
        A \<inter> (B \<inter> U) = {}; 
        U \<subseteq> A \<union> B
      \<rbrakk> \<Longrightarrow> False"
  shows "connected U"
    is topological_space_class.connectedI.

tts_lemma topological_basis:
  assumes "B \<subseteq> Pow U" 
  shows "(on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B) = 
    (\<forall>x\<in>Pow U. \<tau> x = (\<exists>B'\<in>Pow (Pow U). B' \<subseteq> B \<and> \<Union> B' = x))"
    is topological_space_class.topological_basis.

tts_lemma topological_basis_iff:
  assumes "B \<subseteq> Pow U" and "\<And>B'. \<lbrakk>B' \<subseteq> U; B' \<in> B\<rbrakk> \<Longrightarrow> \<tau> B'"
  shows "(on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B) = 
    (\<forall>O'\<in>Pow U. \<tau> O' \<longrightarrow> (\<forall>x\<in>O'. \<exists>B'\<in>B. B' \<subseteq> O' \<and> x \<in> B'))"
    is topological_space_class.topological_basis_iff.

tts_lemma topological_basisI:
  assumes "B \<subseteq> Pow U"
    and "\<And>B'. \<lbrakk>B' \<subseteq> U; B' \<in> B\<rbrakk> \<Longrightarrow> \<tau> B'"
    and "\<And>O' x. \<lbrakk>O' \<subseteq> U; x \<in> U; \<tau> O'; x \<in> O'\<rbrakk> \<Longrightarrow> \<exists>y\<in>B. y \<subseteq> O' \<and> x \<in> y"
  shows "on U with \<tau> : \<guillemotleft>topological_basis\<guillemotright> B"
    is topological_space_class.topological_basisI.
    
tts_lemma closed_closure:
  assumes "S \<subseteq> U"
  shows "closed (closure S)"
    is Elementary_Topology.closed_closure.
    
tts_lemma closure_subset: "S \<subseteq> closure S"
  is Elementary_Topology.closure_subset.
    
tts_lemma closure_eq:
  assumes "S \<subseteq> U"
  shows "(closure S = S) = closed S"
  is Elementary_Topology.closure_eq.
    
tts_lemma closure_closed:
  assumes "S \<subseteq> U" and "closed S"
  shows "closure S = S"
    is Elementary_Topology.closure_closed.
    
tts_lemma closure_closure:
  assumes "S \<subseteq> U"
  shows "closure (closure S) = closure S"
  is Elementary_Topology.closure_closure.
    
tts_lemma closure_mono:
  assumes "T \<subseteq> U" and "S \<subseteq> T"
  shows "closure S \<subseteq> closure T"
  is Elementary_Topology.closure_mono.
    
tts_lemma closure_minimal:
  assumes "T \<subseteq> U" and "S \<subseteq> T" and "closed T"
  shows "closure S \<subseteq> T"
  is Elementary_Topology.closure_minimal.
    
tts_lemma closure_unique:
  assumes "T \<subseteq> U"
    and "S \<subseteq> T"
    and "closed T"
    and "\<And>T'. \<lbrakk>T' \<subseteq> U; S \<subseteq> T'; closed T'\<rbrakk> \<Longrightarrow> T \<subseteq> T'"
  shows "closure S = T"
  is Elementary_Topology.closure_unique.
    
tts_lemma closure_Un:
  assumes "S \<subseteq> U" and "T \<subseteq> U"
  shows "closure (S \<union> T) = closure S \<union> closure T"
    is Elementary_Topology.closure_Un.
    
tts_lemma closure_eq_empty: "(closure S = {}) = (S = {})"
  is Elementary_Topology.closure_eq_empty.
    
tts_lemma closure_subset_eq:
  assumes "S \<subseteq> U"
  shows "(closure S \<subseteq> S) = closed S"
  is Elementary_Topology.closure_subset_eq.
    
tts_lemma open_Int_closure_eq_empty:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "\<tau> S"
  shows "(S \<inter> closure T = {}) = (S \<inter> T = {})"
    is Elementary_Topology.open_Int_closure_eq_empty.
    
tts_lemma open_Int_closure_subset:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "\<tau> S"
  shows "S \<inter> closure T \<subseteq> closure (S \<inter> T)"
    is Elementary_Topology.open_Int_closure_subset.

tts_lemma closure_Un_frontier: "closure S = S \<union> frontier S"
  is Elementary_Topology.closure_Un_frontier.

tts_lemma compact_imp_countably_compact:
  assumes "compact U"
  shows "countably_compact U"
    is Elementary_Topology.compact_imp_countably_compact.

end


tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating through auto
begin

tts_lemma Heine_Borel_imp_Bolzano_Weierstrass:
  assumes "s \<subseteq> U"
    and "local.compact s"
    and "infinite t"
    and "t \<subseteq> s"
  shows "\<exists>x\<in>s. x \<guillemotleft>islimpt\<guillemotright> t"
    is Elementary_Topology.Heine_Borel_imp_Bolzano_Weierstrass.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through
    (
      unfold 
        closed_ow_def 
        compact_ow_def   
        connected_ow_def 
        interior_ow_def
        topological_basis_ow_def
        closure_ow_def  
        frontier_ow_def
        countably_compact_ow_def, 
      auto simp: connected_iff_const
    )
begin

tts_lemma connected_closed:
  assumes "s \<subseteq> U"
  shows "connected s = 
    (
      \<not>(\<exists>A\<in>Pow U. \<exists>B\<in>Pow U. 
        closed A \<and> 
        closed B \<and> 
        s \<subseteq> A \<union> B \<and> 
        A \<inter> (B \<inter> s) = {} \<and> 
        A \<inter> s \<noteq> {} \<and> 
        B \<inter> s \<noteq> {})
    )"
    is Topological_Spaces.connected_closed.

tts_lemma closure_complement:
  assumes "S \<subseteq> U"
  shows "closure (- S \<inter> U) = - interior S \<inter> U"
    is Elementary_Topology.closure_complement.
    
tts_lemma interior_complement:
  assumes "S \<subseteq> U"
  shows "interior (- S \<inter> U) = - closure S \<inter> U"
  is Elementary_Topology.interior_complement.
    
tts_lemma interior_diff:
  assumes "S \<subseteq> U" and "T \<subseteq> U"
  shows "interior (S - T) = interior S - closure T"
  is Elementary_Topology.interior_diff.
    
tts_lemma connected_imp_connected_closure:
  assumes "S \<subseteq> U" and "connected S"
  shows "connected (closure S)"
    is Elementary_Topology.connected_imp_connected_closure.
    
tts_lemma frontier_closed:
  assumes "S \<subseteq> U"
  shows "closed (frontier S)"
    is Elementary_Topology.frontier_closed.
    
tts_lemma frontier_Int:
  assumes "S \<subseteq> U" and "T \<subseteq> U"
  shows "frontier (S \<inter> T) = closure (S \<inter> T) \<inter> (frontier S \<union> frontier T)"
    is Elementary_Topology.frontier_Int.
    
tts_lemma frontier_closures:
  assumes "S \<subseteq> U"
  shows "frontier S = closure S \<inter> closure (- S \<inter> U)"
    is Elementary_Topology.frontier_closures.
    
tts_lemma frontier_Int_subset:
  assumes "S \<subseteq> U" and "T \<subseteq> U"
  shows "frontier (S \<inter> T) \<subseteq> frontier S \<union> frontier T"
  is Elementary_Topology.frontier_Int_subset.
    
tts_lemma frontier_Int_closed:
  assumes "S \<subseteq> U" and "T \<subseteq> U" and "closed S" and "closed T"
  shows "frontier (S \<inter> T) = frontier S \<inter> T \<union> S \<inter> frontier T"
  is Elementary_Topology.frontier_Int_closed.
    
tts_lemma frontier_subset_closed:
  assumes "S \<subseteq> U" and "closed S"
  shows "frontier S \<subseteq> S"
  is Elementary_Topology.frontier_subset_closed.
    
tts_lemma frontier_subset_eq:
  assumes "S \<subseteq> U"
  shows "(frontier S \<subseteq> S) = closed S"
    is Elementary_Topology.frontier_subset_eq.

tts_lemma frontier_complement:
  assumes "S \<subseteq> U"
  shows "frontier (- S \<inter> U) = frontier S"
    is Elementary_Topology.frontier_complement.
    
tts_lemma frontier_Un_subset:
  assumes "S \<subseteq> U" and "T \<subseteq> U"
  shows "frontier (S \<union> T) \<subseteq> frontier S \<union> frontier T"
  is Elementary_Topology.frontier_Un_subset.
    
tts_lemma frontier_disjoint_eq:
  assumes "S \<subseteq> U"
  shows "(frontier S \<inter> S = {}) = \<tau> S"
  is Elementary_Topology.frontier_disjoint_eq.
    
tts_lemma frontier_interiors:
  assumes "s \<subseteq> U"
  shows "frontier s = - interior s \<inter> U - interior (- s \<inter> U)"
is Elementary_Topology.frontier_interiors.
    
tts_lemma frontier_interior_subset:
  assumes "S \<subseteq> U"
  shows "frontier (interior S) \<subseteq> frontier S"
  is Elementary_Topology.frontier_interior_subset.

tts_lemma compact_Un:
  assumes "s \<subseteq> U" and "t \<subseteq> U" and "compact s" and "compact t"
  shows "compact (s \<union> t)"
  is Elementary_Topology.compact_Un.
    
tts_lemma closed_Int_compact:
  assumes "s \<subseteq> U" and "t \<subseteq> U" and "closed s" and "compact t"
  shows "compact (s \<inter> t)"
    is Elementary_Topology.closed_Int_compact.
    
tts_lemma countably_compact_imp_compact:
  assumes "U \<subseteq> U"
    and "B \<subseteq> Pow U"
    and "countably_compact U"
    and "countable B"
    and "Ball B \<tau>"
    and "\<And>T x. \<lbrakk>T \<subseteq> U; x \<in> U; \<tau> T; x \<in> T; x \<in> U\<rbrakk> \<Longrightarrow> \<exists>y\<in>B. x \<in> y \<and> y \<inter> U \<subseteq> T"
  shows "compact U"
    is Elementary_Topology.countably_compact_imp_compact.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (insert closure_eq_empty, blast)
begin

tts_lemma closure_interior:
  assumes "S \<subseteq> U"
  shows "closure S = - interior (- S \<inter> U) \<inter> U"
    is Elementary_Topology.closure_interior.

end

tts_context  
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> 
    through (insert compact_empty, fastforce dest: subset_singletonD)
begin

tts_lemma compact_Union:
  assumes "S \<subseteq> Pow U"
    and "finite S"
    and "\<And>T. \<lbrakk>T \<subseteq> U; T \<in> S\<rbrakk> \<Longrightarrow> compact T"
  shows "compact (\<Union> S)"
    is Elementary_Topology.compact_Union.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through
    (
      insert 
        interior_empty 
        closure_ow_def 
        closed_UNIV 
        compact_empty
        compact_ow_def,
      auto
    )
begin

tts_lemma compactI:
  assumes "s \<subseteq> U"
    and "\<And>C. \<lbrakk>C \<subseteq> Pow U; Ball C \<tau>; s \<subseteq> \<Union> C\<rbrakk> \<Longrightarrow> 
      \<exists>x\<subseteq>Pow U. x \<subseteq> C \<and> finite x \<and> s \<subseteq> \<Union> x"
  shows "compact s"
  given topological_space_class.compactI by (meson PowI)
    
tts_lemma compactE:
  assumes "S \<subseteq> U"
    and "\<T> \<subseteq> Pow U"
    and "compact S"
    and "S \<subseteq> \<Union> \<T>"
    and "\<And>B. B \<in> \<T> \<Longrightarrow> \<tau> B"
    and "\<And>\<T>'. \<lbrakk>\<T>' \<subseteq> Pow U; \<T>' \<subseteq> \<T>; finite \<T>'; S \<subseteq> \<Union> \<T>'\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    given topological_space_class.compactE
    by metis

tts_lemma compact_fip:
  assumes "U \<subseteq> U"
  shows "compact U =
    (
      \<forall>x\<subseteq>Pow U.
        Ball x closed \<longrightarrow>
        (\<forall>y\<subseteq>Pow U. y \<subseteq> x \<longrightarrow> finite y \<longrightarrow> U \<inter> (\<Inter> y \<inter> U) \<noteq> {}) \<longrightarrow>
        U \<inter> (\<Inter> x \<inter> U) \<noteq> {}
    )"
    given topological_space_class.compact_fip by auto
    
tts_lemma compact_imp_fip:
  assumes "S \<subseteq> U"
    and "Fa \<subseteq> Pow U"
    and "compact S"
    and "\<And>T. \<lbrakk>T \<subseteq> U; T \<in> Fa\<rbrakk> \<Longrightarrow> closed T"
    and "\<And>F'. \<lbrakk>F' \<subseteq> Pow U; finite F'; F' \<subseteq> Fa\<rbrakk> \<Longrightarrow> S \<inter> (\<Inter> F' \<inter> U) \<noteq> {}"
  shows "S \<inter> (\<Inter> Fa \<inter> U) \<noteq> {}"
    is topological_space_class.compact_imp_fip.
    
tts_lemma closed_limpt:
  assumes "S \<subseteq> U"
  shows "closed S = (\<forall>x\<in>U. x \<guillemotleft>islimpt\<guillemotright> S \<longrightarrow> x \<in> S)"
    is Elementary_Topology.closed_limpt.
    
tts_lemma open_interior:
  assumes "S \<subseteq> U"
  shows "\<tau> (interior S)"
    is Elementary_Topology.open_interior.
    
tts_lemma interior_subset:
  assumes "S \<subseteq> U"
  shows "interior S \<subseteq> S"
    is Elementary_Topology.interior_subset.
    
tts_lemma interior_open:
  assumes "S \<subseteq> U" and "\<tau> S"
  shows "interior S = S"
    is Elementary_Topology.interior_open.
    
tts_lemma interior_eq:
  assumes "S \<subseteq> U"
  shows "(interior S = S) = \<tau> S"
    is Elementary_Topology.interior_eq.
    
tts_lemma interior_UNIV: "interior U = U"
  is Elementary_Topology.interior_UNIV.
    
tts_lemma interior_interior:
  assumes "S \<subseteq> U"
  shows "interior (interior S) = interior S"
    is Elementary_Topology.interior_interior.
    
tts_lemma interior_closure:
  assumes "S \<subseteq> U"
  shows "interior S = - closure (- S \<inter> U) \<inter> U"
    is Elementary_Topology.interior_closure.
    
tts_lemma finite_imp_compact:
  assumes "s \<subseteq> U" and "finite s"
  shows "compact s"
  is Elementary_Topology.finite_imp_compact.
    
tts_lemma countably_compactE:
  assumes "s \<subseteq> U"
    and "C \<subseteq> Pow U"
    and "countably_compact s"
    and "Ball C \<tau>"
    and "s \<subseteq> \<Union> C"
    and "countable C"
    and "\<And>C'. \<lbrakk>C' \<subseteq> Pow U; C' \<subseteq> C; finite C'; s \<subseteq> \<Union> C'\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is Elementary_Topology.countably_compactE.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> and \<open>?A \<subseteq> U\<close> through (insert interior_empty, auto)
begin

tts_lemma interior_unique:
  assumes "S \<subseteq> U"
    and "T \<subseteq> S"
    and "\<tau> T"
    and "\<And>T'. \<lbrakk>T' \<subseteq> S; \<tau> T'\<rbrakk> \<Longrightarrow> T' \<subseteq> T"
  shows "interior S = T"
    given Elementary_Topology.interior_unique
  by auto

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (simp add: subset_iff filterlim_iff)
begin

tts_lemma open_UN:
  assumes "A \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. B x \<subseteq> U"
    and "\<forall>x\<in>A. \<tau> (B x)"
  shows "\<tau> (\<Union> (B ` A))"
    is topological_space_class.open_UN.

tts_lemma open_Collect_ex:
  assumes "\<And>i. i \<in> U\<^sub>2 \<Longrightarrow> \<tau> {x. P i x \<and> x \<in> U}"
  shows "\<tau> {x \<in> U. \<exists>i\<in>U\<^sub>2. P i x}"
    is open_Collect_ex.

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (unfold closed_ow_def finite_def, auto)
begin

tts_lemma open_INT:
  assumes "A \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. B x \<subseteq> U" and "finite A" and "\<forall>x\<in>A. \<tau> (B x)"
  shows "\<tau> (\<Inter> (B ` A) \<inter> U)"
    is topological_space_class.open_INT.
    
tts_lemma closed_INT:
  assumes "A \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. B x \<subseteq> U" and "\<forall>x\<in>A. closed (B x)"
  shows "closed (\<Inter> (B ` A) \<inter> U)"
    is topological_space_class.closed_INT.
    
tts_lemma closed_UN:
  assumes "A \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. B x \<subseteq> U"
    and "finite A"
    and "\<forall>x\<in>A. closed (B x)"
  shows "closed (\<Union> (B ` A))"
    is topological_space_class.closed_UN.

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (insert closed_empty, auto)
begin

tts_lemma closed_Collect_all:
  assumes "\<And>i. i \<in> U\<^sub>2 \<Longrightarrow> local.closed {x. P i x \<and> x \<in> U}"
  shows "local.closed {x \<in> U. \<forall>i\<in>U\<^sub>2. P i x}"
    is topological_space_class.closed_Collect_all.
    
tts_lemma compactE_image:
  assumes "S \<subseteq> U"
    and "C \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<subseteq> U"
    and "compact S"
    and "\<And>T. \<lbrakk>T \<in> U\<^sub>2; T \<in> C\<rbrakk> \<Longrightarrow> \<tau> (f T)"
    and "S \<subseteq> \<Union> (f ` C)"
    and "\<And>C'. \<lbrakk>C' \<subseteq> U\<^sub>2; C' \<subseteq> C; finite C'; S \<subseteq> \<Union> (f ` C')\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is topological_space_class.compactE_image.

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (simp, blast | simp)
begin

tts_lemma ne_compact_imp_fip_image:
  assumes "s \<subseteq> U"
    and "I \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<subseteq> U"
    and "compact s"
    and "\<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> I\<rbrakk> \<Longrightarrow> closed (f i)"
    and "\<And>I'. \<lbrakk>I' \<subseteq> U\<^sub>2; finite I'; I' \<subseteq> I\<rbrakk> \<Longrightarrow> s \<inter> (\<Inter> (f ` I') \<inter> U) \<noteq> {}"
  shows "s \<inter> (\<Inter> (f ` I) \<inter> U) \<noteq> {}"
    is topological_space_class.compact_imp_fip_image.

end

end



subsection\<open>Further results\<close>

lemma topological_basis_closed:
  assumes "topological_basis_ow U \<tau> B"
  shows "B \<subseteq> Pow U"
  using assms unfolding topological_basis_ow_def by auto

lemma ts_open_eq_ts_open:
  assumes "topological_space_ow U \<tau>'" and "\<And>s. s \<subseteq> U \<Longrightarrow> \<tau>' s = \<tau> s"
  shows "topological_space_ow U \<tau>"
proof
  from assms(1) have "\<tau>' U" unfolding topological_space_ow_def by simp
  with assms(2) show "\<tau> U" by auto
  from assms(1) have "\<And>S T. \<lbrakk> S \<subseteq> U; T \<subseteq> U; \<tau>' S; \<tau>' T \<rbrakk> \<Longrightarrow> \<tau>' (S \<inter> T)" 
    unfolding topological_space_ow_def by simp
  with assms(2) show "\<And>S T. \<lbrakk> S \<subseteq> U; T \<subseteq> U; \<tau> S; \<tau> T \<rbrakk> \<Longrightarrow> \<tau> (S \<inter> T)"
    by (meson Int_lower1 order_trans)
  from assms(1) have "\<And>K. \<lbrakk> K \<subseteq> Pow U; \<forall>S\<in>K. \<tau>' S \<rbrakk> \<Longrightarrow> \<tau>' (\<Union>K)" 
    unfolding topological_space_ow_def by simp
  with assms(2) show "\<And>K. \<lbrakk> K \<subseteq> Pow U; \<forall>S\<in>K. \<tau> S \<rbrakk> \<Longrightarrow> \<tau> (\<Union>K)" 
    by (metis Union_Pow_eq Union_mono ctr_simps_subset_pow_iff)
qed

lemma (in topological_space_ow) topological_basis_closed:
  assumes "topological_basis_ow U \<tau> B" 
  shows "B \<subseteq> Pow U"
  using assms 
  unfolding topological_basis_with_def 
  by (rule topological_basis_closed)

text\<open>\newpage\<close>

end