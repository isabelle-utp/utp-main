(* Title: Designs_And_Graphs.thy
   Author: Chelsea Edmonds 
*)

section \<open>Graphs and Designs\<close>
text \<open>There are many links between graphs and design - most fundamentally that graphs are designs\<close>

theory Designs_And_Graphs imports Block_Designs Graph_Theory.Digraph Graph_Theory.Digraph_Component
begin

subsection \<open>Non-empty digraphs\<close>
text \<open>First, we define the concept of a non-empty digraph. This mirrors the idea of a "proper design"
in the design theory library\<close>
locale non_empty_digraph = wf_digraph + 
  assumes arcs_not_empty: "arcs G \<noteq> {}"

begin 

lemma verts_not_empty: "verts G \<noteq> {}"
  using wf arcs_not_empty head_in_verts by fastforce 

end

subsection \<open>Arcs to Blocks\<close>
text \<open>A digraph uses a pair of points to define an ordered edge. In the case of simple graphs, 
both possible orderings will be in the arcs set. Blocks are inherently unordered, and as such 
a method is required to convert between the two representations\<close>
context graph
begin

definition arc_to_block :: "'b \<Rightarrow> 'a set" where
  "arc_to_block e \<equiv> {tail G e, head G e}"

lemma arc_to_block_to_ends: "{fst (arc_to_ends G e), snd (arc_to_ends G e)} = arc_to_block e"
  by (simp add: arc_to_ends_def arc_to_block_def)

lemma arc_to_block_to_ends_swap: "{snd (arc_to_ends G e), fst (arc_to_ends G e)} = arc_to_block e"
  using arc_to_block_to_ends
  by (simp add: arc_to_block_to_ends insert_commute) 

lemma arc_to_ends_to_block: "arc_to_block e = {x, y} \<Longrightarrow> 
  arc_to_ends G e = (x, y) \<or> arc_to_ends G e = (y, x)"
  by (metis arc_to_block_def arc_to_ends_def doubleton_eq_iff)

lemma arc_to_block_sym: "arc_to_ends G e1 = (u, v) \<Longrightarrow> arc_to_ends G e2 = (v, u) \<Longrightarrow> 
  arc_to_block e1 = arc_to_block e2"
  by (simp add: arc_to_block_def arc_to_ends_def insert_commute)

definition arcs_blocks :: "'a set multiset" where
"arcs_blocks \<equiv> mset_set (arc_to_block ` (arcs G))"

lemma  arcs_blocks_ends: "(x, y) \<in> arcs_ends G \<Longrightarrow> {x, y} \<in># arcs_blocks"
proof (auto simp add: arcs_ends_def arcs_blocks_def )
  fix xa
  assume assm1: "(x, y) = arc_to_ends G xa" and assm2: "xa \<in> arcs G"
  obtain z where zin: "z \<in> (arc_to_block ` (arcs G))" and "z = arc_to_block xa"
    using assm2 by blast 
  thus "{x, y} \<in> arc_to_block ` (arcs G)" using assm1 arc_to_block_to_ends
    by (metis fst_conv snd_conv) 
qed

lemma arc_ends_blocks_subset: "E \<subseteq> arcs G \<Longrightarrow> (x, y) \<in> ((arc_to_ends G) ` E) \<Longrightarrow> 
  {x, y} \<in> (arc_to_block ` E)"
  by (auto simp add: arc_to_ends_def arc_to_block_def )

lemma arc_blocks_end_subset: assumes "E \<subseteq> arcs G"  and "{x, y} \<in> (arc_to_block ` E)"
  shows "(x, y) \<in> ((arc_to_ends G) ` E) \<or> (y, x) \<in> ((arc_to_ends G) ` E)"
proof -
  obtain e where "e \<in> E" and "arc_to_block e = {x,y}" using assms
    by fastforce 
  then have "arc_to_ends G e = (x, y) \<or> arc_to_ends G e = (y, x)" 
    using arc_to_ends_to_block by simp
  thus ?thesis
    by (metis \<open>e \<in> E\<close> image_iff) 
qed

lemma arcs_ends_blocks: "{x, y} \<in># arcs_blocks \<Longrightarrow> (x, y) \<in> arcs_ends G \<and> (y, x) \<in> arcs_ends G"
proof (auto simp add: arcs_ends_def arcs_blocks_def )
  fix xa
  assume assm1: "{x, y} = arc_to_block  xa" and assm2: "xa \<in> (arcs G)"
  obtain z where zin: "z \<in> (arc_to_ends G ` (arcs G))" and "z = arc_to_ends G xa"
    using assm2 by blast
  then have "z = (x, y) \<or> z = (y, x)" using arc_to_block_to_ends assm1
    by (metis arc_to_ends_def doubleton_eq_iff fst_conv snd_conv) (* Slow *)
  thus "(x, y) \<in> arc_to_ends G ` (arcs G)" using assm2
    by (metis arcs_ends_def arcs_ends_symmetric sym_arcs zin) 
next 
  fix xa
  assume assm1: "{x, y} = arc_to_block  xa" and assm2: "xa \<in> (arcs G)"
  thus "(y, x) \<in> arc_to_ends G ` arcs G" using arcs_ends_def
    by (metis (mono_tags, hide_lams) arc_blocks_end_subset graph_symmetric image_iff subset_refl)
qed

lemma arcs_blocks_iff: "{x, y} \<in># arcs_blocks \<longleftrightarrow> (x, y) \<in> arcs_ends G \<and> (y, x) \<in> arcs_ends G"
  using arcs_ends_blocks arcs_blocks_ends by blast 

lemma arcs_ends_wf: "(x, y) \<in> arcs_ends G \<Longrightarrow> x \<in> verts G \<and> y \<in> verts G"
  by auto

lemma arcs_blocks_elem: "bl \<in># arcs_blocks \<Longrightarrow> \<exists> x y . bl = {x, y}"
  apply (auto simp add: arcs_blocks_def)
  by (meson arc_to_block_def)

lemma arcs_ends_blocks_wf: 
  assumes "bl \<in># arcs_blocks" 
  shows "bl \<subseteq> verts G"
proof - 
  obtain x y where blpair: "bl = {x, y}" using arcs_blocks_elem assms
    by fastforce 
  then have "(x, y) \<in> arcs_ends G" using arcs_ends_blocks assms by simp
  thus ?thesis using arcs_ends_wf blpair by auto
qed

lemma arcs_blocks_simple: "bl \<in># arcs_blocks \<Longrightarrow> count (arcs_blocks) bl = 1"
  by (simp add: arcs_blocks_def)

lemma arcs_blocks_ne: "arcs G \<noteq> {} \<Longrightarrow> arcs_blocks \<noteq> {#}"
  by (simp add: arcs_blocks_iff arcs_blocks_def mset_set_empty_iff)

end

subsection \<open>Graphs are designs\<close>

text \<open>Prove that a graph is a number of different types of designs\<close>
sublocale graph \<subseteq> design "verts G" "arcs_blocks"
  using arcs_ends_blocks_wf arcs_blocks_elem by (unfold_locales) (auto)

sublocale graph \<subseteq> simple_design "verts G" "arcs_blocks"
  using arcs_ends_blocks_wf arcs_blocks_elem arcs_blocks_simple by (unfold_locales) (auto)

locale non_empty_graph = graph + non_empty_digraph

sublocale non_empty_graph \<subseteq> proper_design "verts G" "arcs_blocks"
  using arcs_blocks_ne arcs_not_empty by (unfold_locales) simp

lemma (in graph) graph_block_size: assumes "bl \<in># arcs_blocks" shows "card bl = 2"
proof -
  obtain x y where blrep: "bl = {x, y}" using assms arcs_blocks_elem
    by fastforce 
  then have "(x, y) \<in> arcs_ends G" using arcs_ends_blocks assms by simp
  then have "x \<noteq> y" using no_loops using adj_not_same by blast
  thus ?thesis using blrep by simp 
qed

sublocale non_empty_graph \<subseteq> block_design "verts G" "arcs_blocks" 2
  using arcs_not_empty graph_block_size arcs_blocks_ne by (unfold_locales) simp_all

subsection \<open>R-regular graphs\<close>
text \<open>To reason on r-regular graphs and their link to designs, we require a number of extensions to 
lemmas reasoning around the degrees of vertices\<close>
context sym_digraph
begin

lemma in_out_arcs_reflexive: "v \<in> verts G \<Longrightarrow> (e \<in> (in_arcs G v) \<Longrightarrow> 
    \<exists> e' . (e' \<in> (out_arcs G v) \<and> head G e' = tail G e))"
  using symmetric_conv sym_arcs by fastforce 

lemma out_in_arcs_reflexive: "v \<in> verts G \<Longrightarrow> (e \<in> (out_arcs G v) \<Longrightarrow> 
    \<exists> e' . (e' \<in> (in_arcs G v) \<and> tail G e' = head G e))"
  using symmetric_conv sym_arcs by fastforce 

end

context nomulti_digraph
begin

lemma in_arcs_single_per_vert: 
  assumes "v \<in> verts G" and "u \<in> verts G"
  assumes "e1 \<in> in_arcs G v" and " e2 \<in> in_arcs G v" 
  assumes "tail G e1 = u" and "tail G e2 = u"
  shows "e1 = e2"
proof -
  have in_arcs1: "e1 \<in> arcs G" and in_arcs2: "e2 \<in> arcs G" using assms by auto
  have "arc_to_ends G e1 = arc_to_ends G e2" using assms arc_to_ends_def
    by (metis in_in_arcs_conv) 
  thus ?thesis using in_arcs1 in_arcs2 no_multi_arcs by simp
qed

lemma out_arcs_single_per_vert: 
  assumes "v \<in> verts G" and "u \<in> verts G"
  assumes "e1 \<in> out_arcs G v" and " e2 \<in> out_arcs G v" 
  assumes "head G e1 = u" and "head G e2 = u"
  shows "e1 = e2"
proof -
  have in_arcs1: "e1 \<in> arcs G" and in_arcs2: "e2 \<in> arcs G" using assms by auto
  have "arc_to_ends G e1 = arc_to_ends G e2" using assms arc_to_ends_def
    by (metis in_out_arcs_conv) 
  thus ?thesis using in_arcs1 in_arcs2 no_multi_arcs by simp
qed

end

text \<open>Some helpers on the transformation arc definition\<close>
context graph
begin

lemma arc_to_block_is_inj_in_arcs: "inj_on arc_to_block (in_arcs G v)"
  apply (auto simp add: arc_to_block_def inj_on_def)
  by (metis arc_to_ends_def doubleton_eq_iff no_multi_arcs)

lemma arc_to_block_is_inj_out_arcs: "inj_on arc_to_block (out_arcs G v)"
  apply (auto simp add: arc_to_block_def inj_on_def)
  by (metis arc_to_ends_def doubleton_eq_iff no_multi_arcs)

lemma in_out_arcs_reflexive_uniq: "v \<in> verts G \<Longrightarrow> (e \<in> (in_arcs G v) \<Longrightarrow> 
    \<exists>! e' . (e' \<in> (out_arcs G v) \<and> head G e' = tail G e))"
  apply auto
    using symmetric_conv apply fastforce
  using out_arcs_single_per_vert by (metis head_in_verts in_out_arcs_conv) 

lemma out_in_arcs_reflexive_uniq: "v \<in> verts G \<Longrightarrow> e \<in> (out_arcs G v) \<Longrightarrow> 
    \<exists>! e' . (e' \<in> (in_arcs G v) \<and> tail G e' = head G e)"
  apply auto
    using symmetric_conv apply fastforce
  using in_arcs_single_per_vert by (metis tail_in_verts in_in_arcs_conv) 

lemma in_eq_out_arc_ends: "(u, v) \<in> ((arc_to_ends G) ` (in_arcs G v)) \<longleftrightarrow> 
    (v, u) \<in> ((arc_to_ends G) ` (out_arcs G v))"
  using arc_to_ends_def in_in_arcs_conv in_out_arcs_conv
  by (smt (z3) Pair_inject adj_in_verts(1) dominatesI image_iff out_in_arcs_reflexive_uniq)

lemma in_degree_eq_card_arc_ends: "in_degree G v = card ((arc_to_ends G) ` (in_arcs G v))"
  apply (simp add: in_degree_def)
  using  no_multi_arcs by (metis card_image in_arcs_in_arcs inj_onI)

lemma in_degree_eq_card_arc_blocks: "in_degree G v = card (arc_to_block ` (in_arcs G v))"
  apply (simp add: in_degree_def)
  using no_multi_arcs arc_to_block_is_inj_in_arcs by (simp add: card_image)

lemma out_degree_eq_card_arc_blocks: "out_degree G v = card (arc_to_block ` (out_arcs G v))"
  apply (simp add: out_degree_def)
  using no_multi_arcs arc_to_block_is_inj_out_arcs by (simp add: card_image) 

lemma out_degree_eq_card_arc_ends: "out_degree G v = card ((arc_to_ends G) ` (out_arcs G v))"
  apply (simp add: out_degree_def)
  using no_multi_arcs by (metis card_image out_arcs_in_arcs inj_onI)

lemma bij_betw_in_out_arcs: "bij_betw (\<lambda> (u, v) . (v, u)) ((arc_to_ends G) ` (in_arcs G v)) 
    ((arc_to_ends G) ` (out_arcs G v))"
  apply (auto simp add: bij_betw_def)
    apply (simp add: swap_inj_on)
   apply (metis Pair_inject arc_to_ends_def image_eqI in_eq_out_arc_ends in_in_arcs_conv)
  by (metis arc_to_ends_def imageI in_eq_out_arc_ends in_out_arcs_conv pair_imageI)

lemma in_eq_out_degree: "in_degree G v = out_degree G v"
  using bij_betw_in_out_arcs bij_betw_same_card in_degree_eq_card_arc_ends 
    out_degree_eq_card_arc_ends by auto 

lemma in_out_arcs_blocks: "arc_to_block ` (in_arcs G v) = arc_to_block ` (out_arcs G v)" 
proof (auto)
  fix xa 
  assume a1: "xa \<in> arcs G" and a2: "v = head G xa"
  then have "xa \<in> in_arcs G v" by simp 
  then obtain e where out: "e \<in> out_arcs G v" and "head G e = tail G xa"
    using out_in_arcs_reflexive_uniq by force 
  then have "arc_to_ends G e = (v, tail G xa)"
    by (simp add: arc_to_ends_def)
  then have "arc_to_block xa = arc_to_block e"
    using arc_to_block_sym by (metis a2 arc_to_ends_def) 
  then show "arc_to_block xa \<in> arc_to_block ` out_arcs G (head G xa)"
    using out a2 by blast 
next
  fix xa 
  assume a1: "xa \<in> arcs G" and a2: "v = tail G xa"
  then have "xa \<in> out_arcs G v" by simp 
  then obtain e where ina: "e \<in> in_arcs G v" and "tail G e = head G xa"
    using out_in_arcs_reflexive_uniq by force 
  then have "arc_to_ends G e = (head G xa, v)"
    by (simp add: arc_to_ends_def)
  then have "arc_to_block xa = arc_to_block e"
    using arc_to_block_sym by (metis a2 arc_to_ends_def) 
  then show "arc_to_block xa \<in> arc_to_block ` in_arcs G (tail G xa)"
    using ina a2 by blast 
qed

end

text \<open>A regular digraph is defined as one where the in degree equals the out degree which in turn 
equals some fixed integer $\mathrm{r}$\<close>
locale regular_digraph = wf_digraph + 
  fixes \<r> :: int
  assumes in_deg_r: "v \<in> verts G \<Longrightarrow> in_degree G v = \<r>"
  assumes out_deg_r: "v \<in> verts G \<Longrightarrow> out_degree G v = \<r>"

locale regular_graph = graph + regular_digraph
begin

lemma rep_vertices_in_blocks [simp]: 
  assumes "x \<in> verts G"
  shows "size {# e \<in># arcs_blocks . x \<in> e #} = \<r>"
proof - 
  have "\<And> e . e \<in> (arc_to_block ` (arcs G)) \<Longrightarrow> x \<in> e \<Longrightarrow> e \<in> (arc_to_block ` in_arcs G x)"
    using arc_to_block_def in_in_arcs_conv insert_commute insert_iff singleton_iff sym_arcs 
      symmetric_conv by fastforce
  then have "{ e \<in> (arc_to_block ` (arcs G)) . x \<in> e} =  (arc_to_block ` (in_arcs G x))" 
    using arc_to_block_def by auto
  then have "card { e \<in> (arc_to_block ` (arcs G)) . x \<in> e} = \<r>" 
    using in_deg_r in_degree_eq_card_arc_blocks assms by auto
  thus ?thesis
    using arcs_blocks_def finite_arcs by force 
qed

end

text \<open>Intro rules for regular graphs\<close>
lemma graph_in_degree_r_imp_reg[intro]: assumes "graph G"
  assumes "(\<And> v . v \<in> (verts G) \<Longrightarrow> in_degree G v = \<r>)"
  shows "regular_graph G \<r>"
proof -
  interpret g: graph G using assms by simp
  interpret wf: wf_digraph G by (simp add: g.wf_digraph_axioms)
  show ?thesis 
    using assms(2) g.in_eq_out_degree by (unfold_locales) simp_all
qed

lemma graph_out_degree_r_imp_reg[intro]: assumes "graph G"
  assumes "(\<And> v . v \<in> (verts G) \<Longrightarrow> out_degree G v = \<r>)"
  shows "regular_graph G \<r>"
proof -
  interpret g: graph G using assms by simp
  interpret wf: wf_digraph G by (simp add: g.wf_digraph_axioms)
  show ?thesis 
    using assms(2) g.in_eq_out_degree by (unfold_locales) simp_all
qed

text \<open>Regular graphs (non-empty) can be shown to be a constant rep design\<close>
locale non_empty_regular_graph = regular_graph + non_empty_digraph

sublocale non_empty_regular_graph \<subseteq> non_empty_graph
  by unfold_locales

sublocale non_empty_regular_graph \<subseteq> constant_rep_design "verts G" "arcs_blocks" \<r>
  using arcs_blocks_ne arcs_not_empty
  by (unfold_locales)(simp_all add: point_replication_number_def)

end