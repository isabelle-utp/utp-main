(***********************************************************************************
 * Copyright (c) 2016-2020 The University of Sheffield, UK
 *               2019-2020 University of Exeter, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section \<open>Core SC DOM Components II\<close>
theory Core_DOM_SC_DOM_Components
  imports
    Core_DOM_DOM_Components
begin
declare [[smt_timeout=2400]]

section \<open>Scope Components\<close>

subsection \<open>Definition\<close>

locale l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs +
  l_get_owner_document_defs get_owner_document +
  l_to_tree_order_defs to_tree_order
  for get_owner_document :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and to_tree_order :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
begin
definition a_get_scdom_component :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  where
    "a_get_scdom_component ptr = do {
      document \<leftarrow> get_owner_document ptr;
      disc_nodes \<leftarrow> get_disconnected_nodes document;
      tree_order \<leftarrow> to_tree_order (cast document);
      disconnected_tree_orders \<leftarrow> map_M (to_tree_order \<circ> cast) disc_nodes;
      return (tree_order @ (concat disconnected_tree_orders))
    }"

definition a_is_strongly_scdom_component_safe ::
  "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
  where
    "a_is_strongly_scdom_component_safe S\<^sub>a\<^sub>r\<^sub>g S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t h h' = (
      let removed_pointers = fset (object_ptr_kinds h) - fset (object_ptr_kinds h') in
      let added_pointers = fset (object_ptr_kinds h') - fset (object_ptr_kinds h) in
      let arg_components =
        (\<Union>ptr \<in> (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h \<turnstile> a_get_scdom_component ptr|\<^sub>r) \<inter>
        fset (object_ptr_kinds h).  set |h \<turnstile> a_get_scdom_component ptr|\<^sub>r) in
      let arg_components' =
        (\<Union>ptr \<in> (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h \<turnstile> a_get_scdom_component ptr|\<^sub>r) \<inter>
        fset (object_ptr_kinds h').  set |h' \<turnstile> a_get_scdom_component ptr|\<^sub>r) in
      removed_pointers \<subseteq> arg_components \<and>
      added_pointers \<subseteq> arg_components' \<and>
      S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t \<subseteq> arg_components' \<and>
      (\<forall>outside_ptr \<in> fset (object_ptr_kinds h) \<inter> fset (object_ptr_kinds h') -
        (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h  \<turnstile> a_get_scdom_component ptr|\<^sub>r). preserved (get_M outside_ptr id) h h'))"

definition a_is_weakly_scdom_component_safe ::
  "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
  where
    "a_is_weakly_scdom_component_safe S\<^sub>a\<^sub>r\<^sub>g S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t h h' = (
      let removed_pointers = fset (object_ptr_kinds h) - fset (object_ptr_kinds h') in
      let added_pointers = fset (object_ptr_kinds h') - fset (object_ptr_kinds h) in
      let arg_components =
        (\<Union>ptr \<in> (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h \<turnstile> a_get_scdom_component ptr|\<^sub>r) \<inter>
        fset (object_ptr_kinds h).  set |h \<turnstile> a_get_scdom_component ptr|\<^sub>r) in
      let arg_components' =
        (\<Union>ptr \<in> (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h \<turnstile> a_get_scdom_component ptr|\<^sub>r) \<inter>
        fset (object_ptr_kinds h').  set |h' \<turnstile> a_get_scdom_component ptr|\<^sub>r) in
      removed_pointers \<subseteq> arg_components \<and>
      S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t \<subseteq> arg_components' \<union> added_pointers  \<and>
      (\<forall>outside_ptr \<in> fset (object_ptr_kinds h) \<inter> fset (object_ptr_kinds h') -
        (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h  \<turnstile> a_get_scdom_component ptr|\<^sub>r). preserved (get_M outside_ptr id) h h'))"
end

global_interpretation l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_owner_document get_disconnected_nodes
  get_disconnected_nodes_locs to_tree_order
  defines get_scdom_component = "l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_scdom_component
get_owner_document get_disconnected_nodes to_tree_order"
    and is_strongly_scdom_component_safe = a_is_strongly_scdom_component_safe
    and is_weakly_scdom_component_safe = a_is_weakly_scdom_component_safe
  .

locale l_get_scdom_component_defs =
  fixes get_scdom_component :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  fixes is_strongly_scdom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
  fixes is_weakly_scdom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"


locale l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_scdom_component_defs +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  assumes get_scdom_component_impl: "get_scdom_component = a_get_scdom_component"
  assumes is_strongly_scdom_component_safe_impl:
    "is_strongly_scdom_component_safe = a_is_strongly_scdom_component_safe"
  assumes is_weakly_scdom_component_safe_impl:
    "is_weakly_scdom_component_safe = a_is_weakly_scdom_component_safe"
begin
lemmas get_scdom_component_def = a_get_scdom_component_def[folded get_scdom_component_impl]
lemmas is_strongly_scdom_component_safe_def =
  a_is_strongly_scdom_component_safe_def[folded is_strongly_scdom_component_safe_impl]
lemmas is_weakly_scdom_component_safe_def =
  a_is_weakly_scdom_component_safe_def[folded is_weakly_scdom_component_safe_impl]
end

interpretation i_get_scdom_component?: l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe
  get_owner_document get_disconnected_nodes get_disconnected_nodes_locs to_tree_order
  by(auto simp add: l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def get_scdom_component_def
      is_strongly_scdom_component_safe_def is_weakly_scdom_component_safe_def instances)
declare l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


locale l_get_dom_component_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed +
  l_get_owner_document +
  l_get_owner_document_wf +
  l_get_disconnected_nodes +
  l_to_tree_order +
  l_known_ptr +
  l_known_ptrs +
  l_get_owner_document_wf_get_root_node_wf +
  assumes known_ptr_impl: "known_ptr = DocumentClass.known_ptr"
begin

lemma known_ptr_node_or_document: "known_ptr ptr \<Longrightarrow> is_node_ptr_kind ptr \<or> is_document_ptr_kind ptr"
  by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
      CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
      split: option.splits)

lemma get_scdom_component_ptr_in_heap2:
  assumes "h \<turnstile> ok (get_scdom_component ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms get_root_node_ptr_in_heap
  apply(auto simp add: get_scdom_component_def elim!: bind_is_OK_E3 intro!: map_M_pure_I)[1]
  by (simp add: is_OK_returns_result_I local.get_owner_document_ptr_in_heap)

lemma get_scdom_component_subset_get_dom_component:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_dom_component ptr \<rightarrow>\<^sub>r c"
  shows "set c \<subseteq> set sc"
proof -
  obtain document disc_nodes tree_order disconnected_tree_orders where
    document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r document"
    and disc_nodes: "h \<turnstile> get_disconnected_nodes document \<rightarrow>\<^sub>r disc_nodes"
    and tree_order: "h \<turnstile> to_tree_order (cast document) \<rightarrow>\<^sub>r tree_order"
    and disconnected_tree_orders: "h \<turnstile> map_M (to_tree_order \<circ> cast) disc_nodes \<rightarrow>\<^sub>r disconnected_tree_orders"
    and sc: "sc = tree_order @ (concat disconnected_tree_orders)"
    using assms(4)
    by(auto simp add: get_scdom_component_def elim!: bind_returns_result_E
        elim!: bind_returns_result_E2[rotated, OF get_owner_document_pure, rotated]
        elim!: bind_returns_result_E2[rotated, OF get_disconnected_nodes_pure, rotated]
        elim!: bind_returns_result_E2[rotated, OF to_tree_order_pure, rotated]
        )

  obtain root_ptr where root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    and c: "h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c"
    using assms(5)
    by(auto simp add: get_dom_component_def elim!: bind_returns_result_E2[rotated, OF get_root_node_pure, rotated])

  show ?thesis
  proof (cases "is_document_ptr_kind root_ptr")
    case True
    then have "cast document = root_ptr"
      using get_root_node_document assms(1) assms(2) assms(3) root_ptr document
      by (metis document_ptr_casts_commute3 returns_result_eq)
    then have "c = tree_order"
      using tree_order c
      by auto
    then show ?thesis
      by(simp add: sc)
  next
    case False
    moreover have "root_ptr |\<in>| object_ptr_kinds h"
      using assms(1) assms(2) assms(3) local.get_root_node_root_in_heap root_ptr by blast
    ultimately have "is_node_ptr_kind root_ptr"
      using assms(3) known_ptrs_known_ptr known_ptr_node_or_document
      by auto
    then obtain root_node_ptr where root_node_ptr: "root_ptr = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_node_ptr"
      by (metis node_ptr_casts_commute3)
    then have "h \<turnstile> get_owner_document root_ptr \<rightarrow>\<^sub>r document"
      using get_root_node_same_owner_document
      using assms(1) assms(2) assms(3) document root_ptr by blast
    then have "root_node_ptr \<in> set disc_nodes"
      using assms(1) assms(2) assms(3) disc_nodes in_disconnected_nodes_no_parent root_node_ptr
      using local.get_root_node_same_no_parent root_ptr by blast
    then have "c \<in> set disconnected_tree_orders"
      using c root_node_ptr
      using map_M_pure_E[OF disconnected_tree_orders]
      by (metis (mono_tags, lifting) comp_apply local.to_tree_order_pure select_result_I2)
    then show ?thesis
      by(auto simp add: sc)
  qed
qed

lemma get_scdom_component_ptrs_same_owner_document:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "ptr' \<in> set sc"
  assumes "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
  shows "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r owner_document"
proof -
  obtain document disc_nodes tree_order disconnected_tree_orders where
    document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r document"
    and disc_nodes: "h \<turnstile> get_disconnected_nodes document \<rightarrow>\<^sub>r disc_nodes"
    and tree_order: "h \<turnstile> to_tree_order (cast document) \<rightarrow>\<^sub>r tree_order"
    and disconnected_tree_orders: "h \<turnstile> map_M (to_tree_order \<circ> cast) disc_nodes \<rightarrow>\<^sub>r disconnected_tree_orders"
    and sc: "sc = tree_order @ (concat disconnected_tree_orders)"
    using assms(4)
    by(auto simp add: get_scdom_component_def elim!: bind_returns_result_E
        elim!: bind_returns_result_E2[rotated, OF get_owner_document_pure, rotated]
        elim!: bind_returns_result_E2[rotated, OF get_disconnected_nodes_pure, rotated]
        elim!: bind_returns_result_E2[rotated, OF to_tree_order_pure, rotated]
        )
  show ?thesis
  proof (cases "ptr' \<in> set tree_order")
    case True
    have "owner_document = document"
      using assms(6) document by fastforce
    then show ?thesis
      by (metis (no_types) True assms(1) assms(2) assms(3) cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject document
          document_ptr_casts_commute3 document_ptr_document_ptr_cast document_ptr_kinds_commutes
          local.get_owner_document_owner_document_in_heap local.get_root_node_document
          local.get_root_node_not_node_same local.to_tree_order_same_root node_ptr_no_document_ptr_cast tree_order)
  next
    case False
    then obtain disconnected_tree_order where disconnected_tree_order:
      "ptr' \<in> set disconnected_tree_order" and "disconnected_tree_order \<in> set disconnected_tree_orders"
      using sc \<open>ptr' \<in> set sc\<close>
      by auto
    obtain root_ptr' where
      root_ptr': "root_ptr' \<in> set disc_nodes" and
      "h \<turnstile> to_tree_order (cast root_ptr') \<rightarrow>\<^sub>r disconnected_tree_order"
      using map_M_pure_E2[OF disconnected_tree_orders \<open>disconnected_tree_order \<in> set disconnected_tree_orders\<close>]
      by (metis comp_apply local.to_tree_order_pure)
    have "\<not>(\<exists>parent \<in> fset (object_ptr_kinds h). root_ptr' \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r)"
      using disc_nodes
      by (meson assms(1) assms(2) assms(3) disjoint_iff_not_equal local.get_child_nodes_ok
          local.heap_is_wellformed_children_disc_nodes_different local.known_ptrs_known_ptr notin_fset
          returns_result_select_result root_ptr')
    then
    have "h \<turnstile> get_parent root_ptr' \<rightarrow>\<^sub>r None"
      using disc_nodes
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) fmember.rep_eq local.get_parent_child_dual
          local.get_parent_ok local.get_parent_parent_in_heap local.heap_is_wellformed_disc_nodes_in_heap
          returns_result_select_result root_ptr' select_result_I2 split_option_ex)
    then have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r cast root_ptr'"
      using \<open>h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_ptr') \<rightarrow>\<^sub>r disconnected_tree_order\<close> assms(1)
        assms(2) assms(3) disconnected_tree_order local.get_root_node_no_parent
        local.to_tree_order_get_root_node local.to_tree_order_ptr_in_result
      by blast
    then have "h \<turnstile> get_owner_document (cast root_ptr') \<rightarrow>\<^sub>r document"
      using assms(1) assms(2) assms(3) disc_nodes local.get_owner_document_disconnected_nodes root_ptr'
      by blast

    then have "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r document"
      using \<open>h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_ptr'\<close> assms(1) assms(2) assms(3)
        local.get_root_node_same_owner_document
      by blast
    then show ?thesis
      using assms(6) document returns_result_eq by force
  qed
qed

lemma get_scdom_component_ptrs_same_scope_component:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "ptr' \<in> set sc"
  shows "h \<turnstile> get_scdom_component ptr' \<rightarrow>\<^sub>r sc"
proof -
  obtain document disc_nodes tree_order disconnected_tree_orders where
    document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r document"
    and disc_nodes: "h \<turnstile> get_disconnected_nodes document \<rightarrow>\<^sub>r disc_nodes"
    and tree_order: "h \<turnstile> to_tree_order (cast document) \<rightarrow>\<^sub>r tree_order"
    and disconnected_tree_orders: "h \<turnstile> map_M (to_tree_order \<circ> cast) disc_nodes \<rightarrow>\<^sub>r disconnected_tree_orders"
    and sc: "sc = tree_order @ (concat disconnected_tree_orders)"
    using assms(4)
    by(auto simp add: get_scdom_component_def elim!: bind_returns_result_E
        elim!: bind_returns_result_E2[rotated, OF get_owner_document_pure, rotated]
        elim!: bind_returns_result_E2[rotated, OF get_disconnected_nodes_pure, rotated]
        elim!: bind_returns_result_E2[rotated, OF to_tree_order_pure, rotated]
        )
  show ?thesis
  proof (cases "ptr' \<in> set tree_order")
    case True
    then have "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r document"
      by (metis assms(1) assms(2) assms(3) cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject document
          document_ptr_casts_commute3 document_ptr_kinds_commutes known_ptr_node_or_document
          local.get_owner_document_owner_document_in_heap local.get_root_node_document
          local.get_root_node_not_node_same local.known_ptrs_known_ptr local.to_tree_order_get_root_node
          local.to_tree_order_ptr_in_result node_ptr_no_document_ptr_cast tree_order)
    then show ?thesis
      using disc_nodes tree_order disconnected_tree_orders sc
      by(auto simp add: get_scdom_component_def intro!: bind_pure_returns_result_I map_M_pure_I)
  next
    case False
    then obtain disconnected_tree_order where disconnected_tree_order:
      "ptr' \<in> set disconnected_tree_order" and "disconnected_tree_order \<in> set disconnected_tree_orders"
      using sc \<open>ptr' \<in> set sc\<close>
      by auto
    obtain root_ptr' where
      root_ptr': "root_ptr' \<in> set disc_nodes" and
      "h \<turnstile> to_tree_order (cast root_ptr') \<rightarrow>\<^sub>r disconnected_tree_order"
      using map_M_pure_E2[OF disconnected_tree_orders \<open>disconnected_tree_order \<in> set disconnected_tree_orders\<close>]
      by (metis comp_apply local.to_tree_order_pure)
    have "\<not>(\<exists>parent \<in> fset (object_ptr_kinds h). root_ptr' \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r)"
      using disc_nodes
      by (meson assms(1) assms(2) assms(3) disjoint_iff_not_equal local.get_child_nodes_ok
          local.heap_is_wellformed_children_disc_nodes_different local.known_ptrs_known_ptr notin_fset
          returns_result_select_result root_ptr')
    then
    have "h \<turnstile> get_parent root_ptr' \<rightarrow>\<^sub>r None"
      using disc_nodes
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) fmember.rep_eq
          local.get_parent_child_dual local.get_parent_ok local.get_parent_parent_in_heap
          local.heap_is_wellformed_disc_nodes_in_heap returns_result_select_result root_ptr'
          select_result_I2 split_option_ex)
    then have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r cast root_ptr'"
      using \<open>h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_ptr') \<rightarrow>\<^sub>r disconnected_tree_order\<close> assms(1)
        assms(2) assms(3) disconnected_tree_order local.get_root_node_no_parent
        local.to_tree_order_get_root_node local.to_tree_order_ptr_in_result
      by blast
    then have "h \<turnstile> get_owner_document (cast root_ptr') \<rightarrow>\<^sub>r document"
      using assms(1) assms(2) assms(3) disc_nodes local.get_owner_document_disconnected_nodes root_ptr'
      by blast

    then have "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r document"
      using \<open>h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_ptr'\<close> assms(1) assms(2) assms(3)
        local.get_root_node_same_owner_document
      by blast
    then show ?thesis
      using disc_nodes tree_order disconnected_tree_orders sc
      by(auto simp add: get_scdom_component_def intro!: bind_pure_returns_result_I map_M_pure_I)
  qed
qed

lemma get_scdom_component_ok:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (get_scdom_component ptr)"
  using assms
  apply(auto simp add: get_scdom_component_def intro!: bind_is_OK_pure_I map_M_pure_I map_M_ok_I)[1]
  using get_owner_document_ok
     apply blast
    apply (simp add: local.get_disconnected_nodes_ok local.get_owner_document_owner_document_in_heap)
   apply (simp add: local.get_owner_document_owner_document_in_heap local.to_tree_order_ok)
  using local.heap_is_wellformed_disc_nodes_in_heap local.to_tree_order_ok node_ptr_kinds_commutes
  by blast

lemma get_scdom_component_ptr_in_heap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "ptr' \<in> set sc"
  shows "ptr' |\<in>| object_ptr_kinds h"
  apply(insert assms )
  apply(auto simp add: get_scdom_component_def elim!: bind_returns_result_E2 intro!: map_M_pure_I)[1]
  using local.to_tree_order_ptrs_in_heap apply blast
  by (metis (no_types, lifting) assms(4) assms(5) bind_returns_result_E
      get_scdom_component_ptrs_same_scope_component is_OK_returns_result_I get_scdom_component_def
      local.get_owner_document_ptr_in_heap)

lemma get_scdom_component_contains_get_dom_component:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "ptr' \<in> set sc"
  obtains c where "h \<turnstile> get_dom_component ptr' \<rightarrow>\<^sub>r c" and "set c \<subseteq> set sc"
proof -
  have "h \<turnstile> get_scdom_component ptr' \<rightarrow>\<^sub>r sc"
    using assms(1) assms(2) assms(3) assms(4) assms(5) get_scdom_component_ptrs_same_scope_component
    by blast
  then show ?thesis
    by (meson assms(1) assms(2) assms(3) assms(5) get_scdom_component_ptr_in_heap
        get_scdom_component_subset_get_dom_component is_OK_returns_result_E local.get_dom_component_ok that)
qed

lemma get_scdom_component_owner_document_same:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "ptr' \<in> set sc"
  obtains owner_document where "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r owner_document" and "cast owner_document \<in> set sc"
  using assms
  apply(auto simp add: get_scdom_component_def elim!: bind_returns_result_E2 intro!: map_M_pure_I)[1]
   apply (metis (no_types, lifting) assms(4) assms(5) document_ptr_casts_commute3
      document_ptr_document_ptr_cast get_scdom_component_contains_get_dom_component
      local.get_dom_component_ptr local.get_dom_component_root_node_same local.get_dom_component_to_tree_order
      local.get_root_node_document local.get_root_node_not_node_same local.to_tree_order_ptr_in_result
      local.to_tree_order_ptrs_in_heap node_ptr_no_document_ptr_cast)
  apply(rule map_M_pure_E2)
     apply(simp)
    apply(simp)
   apply(simp)
  by (smt assms(4) assms(5) comp_apply get_scdom_component_ptr_in_heap is_OK_returns_result_E
      local.get_owner_document_disconnected_nodes local.get_root_node_ok local.get_root_node_same_owner_document
      local.to_tree_order_get_root_node local.to_tree_order_ptr_in_result)

lemma get_scdom_component_different_owner_documents:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
  assumes "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r owner_document'"
  assumes "owner_document \<noteq> owner_document'"
  shows "set |h \<turnstile> get_scdom_component ptr|\<^sub>r \<inter> set |h \<turnstile> get_scdom_component ptr'|\<^sub>r = {}"
  using assms get_scdom_component_ptrs_same_owner_document
  by (smt disjoint_iff_not_equal get_scdom_component_ok is_OK_returns_result_I
      local.get_owner_document_ptr_in_heap returns_result_eq returns_result_select_result)


lemma get_scdom_component_ptr:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r c"
  shows "ptr \<in> set c"
  using assms
  by (meson get_scdom_component_ptr_in_heap2 get_scdom_component_subset_get_dom_component
      is_OK_returns_result_E is_OK_returns_result_I local.get_dom_component_ok local.get_dom_component_ptr
      subsetD)
end

locale l_get_dom_component_get_scdom_component = l_get_owner_document_defs + l_heap_is_wellformed_defs +
  l_type_wf + l_known_ptrs + l_get_scdom_component_defs + l_get_dom_component_defs +
  assumes get_scdom_component_subset_get_dom_component:
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc \<Longrightarrow>
h \<turnstile> get_dom_component ptr \<rightarrow>\<^sub>r c \<Longrightarrow> set c \<subseteq> set sc"
  assumes get_scdom_component_ptrs_same_scope_component:
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc \<Longrightarrow>
ptr' \<in> set sc \<Longrightarrow> h \<turnstile> get_scdom_component ptr' \<rightarrow>\<^sub>r sc"
  assumes get_scdom_component_ptrs_same_owner_document:
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc \<Longrightarrow>
ptr' \<in> set sc \<Longrightarrow> h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document \<Longrightarrow> h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r owner_document"
  assumes get_scdom_component_ok:
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> ptr |\<in>| object_ptr_kinds h \<Longrightarrow>
h \<turnstile> ok (get_scdom_component ptr)"
  assumes get_scdom_component_ptr_in_heap:
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc \<Longrightarrow>
ptr' \<in> set sc \<Longrightarrow> ptr' |\<in>| object_ptr_kinds h"
  assumes get_scdom_component_contains_get_dom_component:
    "(\<And>c. h \<turnstile> get_dom_component ptr' \<rightarrow>\<^sub>r c \<Longrightarrow> set c \<subseteq> set sc \<Longrightarrow> thesis) \<Longrightarrow> heap_is_wellformed h \<Longrightarrow>
type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc \<Longrightarrow> ptr' \<in> set sc \<Longrightarrow> thesis"
  assumes get_scdom_component_owner_document_same:
    "(\<And>owner_document. h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r owner_document \<Longrightarrow> cast owner_document \<in> set sc \<Longrightarrow> thesis) \<Longrightarrow>
    heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc \<Longrightarrow>
ptr' \<in> set sc \<Longrightarrow> thesis"
  assumes get_scdom_component_different_owner_documents:
    "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document \<Longrightarrow>
h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r owner_document' \<Longrightarrow> owner_document \<noteq> owner_document' \<Longrightarrow>
set |h \<turnstile> get_scdom_component ptr|\<^sub>r \<inter> set |h \<turnstile> get_scdom_component ptr'|\<^sub>r = {}"

interpretation i_get_dom_component_get_scdom_component?: l_get_dom_component_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_owner_document
  get_disconnected_nodes get_disconnected_nodes_locs to_tree_order heap_is_wellformed parent_child_rel
  type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors
  get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  by(auto simp add: l_get_dom_component_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_dom_component_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_get_dom_component_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_dom_component_get_scdom_component_is_l_get_dom_component_get_scdom_component [instances]:
  "l_get_dom_component_get_scdom_component get_owner_document heap_is_wellformed type_wf known_ptr
known_ptrs get_scdom_component get_dom_component"
  apply(auto simp add: l_get_dom_component_get_scdom_component_def l_get_dom_component_get_scdom_component_axioms_def instances)[1]
  using get_scdom_component_subset_get_dom_component apply fast
  using get_scdom_component_ptrs_same_scope_component apply fast
  using get_scdom_component_ptrs_same_owner_document apply fast
  using get_scdom_component_ok apply fast
  using get_scdom_component_ptr_in_heap apply fast
  using get_scdom_component_contains_get_dom_component apply blast
  using get_scdom_component_owner_document_same apply blast
  using get_scdom_component_different_owner_documents apply fast
  done


subsubsection \<open>get\_child\_nodes\<close>

locale l_get_scdom_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_child_nodes_is_strongly_scdom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
  assumes "child \<in> set children"
  shows "cast child \<in> set sc \<longleftrightarrow> ptr' \<in> set sc"
  apply(auto)[1]
   apply (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) contra_subsetD
      get_scdom_component_ptrs_same_scope_component get_scdom_component_subset_get_dom_component
      is_OK_returns_result_E local.get_child_nodes_is_strongly_dom_component_safe local.get_dom_component_ok
      local.get_dom_component_ptr local.heap_is_wellformed_children_in_heap node_ptr_kinds_commutes)
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6)
      get_scdom_component_contains_get_dom_component is_OK_returns_result_E is_OK_returns_result_I
      get_child_nodes_is_strongly_dom_component_safe local.get_child_nodes_ptr_in_heap
      local.get_dom_component_ok local.get_dom_component_ptr set_rev_mp)

lemma get_child_nodes_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {ptr} (cast ` set children) h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson local.get_child_nodes_pure pure_returns_heap_eq)
  then show ?thesis
    using assms
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def preserved_def)[1]
    by (smt Int_absorb2 finite_set_in get_child_nodes_is_strongly_scdom_component_safe_step in_mono
        is_OK_returns_result_I local.get_child_nodes_ptr_in_heap local.get_dom_component_ok
        local.get_dom_component_ptr local.get_scdom_component_impl local.get_scdom_component_ok
        local.get_scdom_component_ptr_in_heap local.get_scdom_component_subset_get_dom_component
        returns_result_select_result subsetI)
qed
end

interpretation i_get_scdom_component_get_child_nodes?: l_get_scdom_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe
  get_dom_component is_strongly_dom_component_safe is_weakly_dom_component_safe get_disconnected_nodes
  get_disconnected_nodes_locs to_tree_order get_parent get_parent_locs get_child_nodes
  get_child_nodes_locs get_root_node get_root_node_locs get_ancestors get_ancestors_locs get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_scdom_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_parent\<close>

locale l_get_scdom_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_parent_is_strongly_scdom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_parent ptr' \<rightarrow>\<^sub>r Some parent"
  shows "parent \<in> set sc \<longleftrightarrow> cast ptr' \<in> set sc"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) contra_subsetD
      get_scdom_component_contains_get_dom_component local.get_dom_component_ptr
      local.get_parent_is_strongly_dom_component_safe_step)

lemma get_parent_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some parent"
  assumes "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {cast node_ptr} {parent} h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson local.get_parent_pure pure_returns_heap_eq)
  then show ?thesis
    using assms
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def preserved_def)[1]
    by (smt IntI finite_set_in in_mono local.get_dom_component_ok local.get_dom_component_ptr
        local.get_parent_is_strongly_dom_component_safe_step local.get_parent_parent_in_heap
        local.get_scdom_component_impl local.get_scdom_component_ok local.get_scdom_component_subset_get_dom_component
        local.to_tree_order_ok local.to_tree_order_parent local.to_tree_order_ptr_in_result
        local.to_tree_order_ptrs_in_heap returns_result_select_result)
qed
end

interpretation i_get_scdom_component_get_parent?: l_get_scdom_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_disconnected_nodes
  get_disconnected_nodes_locs to_tree_order get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_root_node get_root_node_locs get_ancestors get_ancestors_locs get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_scdom_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_root\_node\<close>

locale l_get_scdom_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_root_node_is_strongly_scdom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root"
  shows "root \<in> set sc \<longleftrightarrow> ptr' \<in> set sc"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) contra_subsetD
      get_scdom_component_contains_get_dom_component local.get_dom_component_ptr
      local.get_root_node_is_strongly_dom_component_safe_step)

lemma get_root_node_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {ptr} {root} h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson local.get_root_node_pure pure_returns_heap_eq)
  then show ?thesis
    using assms
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def preserved_def)[1]
    by (smt Int_iff finite_set_in is_OK_returns_result_I local.get_dom_component_ok
        local.get_dom_component_ptr local.get_root_node_is_strongly_dom_component_safe_step
        local.get_root_node_ptr_in_heap local.get_scdom_component_impl local.get_scdom_component_ok
        local.get_scdom_component_subset_get_dom_component returns_result_select_result subset_eq)
qed
end

interpretation i_get_scdom_component_get_root_node?: l_get_scdom_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_disconnected_nodes
  get_disconnected_nodes_locs to_tree_order get_parent get_parent_locs get_child_nodes
  get_child_nodes_locs get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_element_by_id get_elements_by_class_name get_elements_by_tag_name first_in_tree_order
  get_attribute get_attribute_locs
  by(auto simp add: l_get_scdom_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_element\_by\_id\<close>

locale l_get_scdom_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_element_by_id_is_strongly_scdom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_element_by_id ptr' idd \<rightarrow>\<^sub>r Some result"
  shows "cast result \<in> set sc \<longleftrightarrow> ptr' \<in> set sc"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) contra_subsetD
      get_element_by_id_is_strongly_dom_component_safe_step get_scdom_component_contains_get_dom_component
      local.get_dom_component_ptr)

lemma get_element_by_id_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_element_by_id ptr idd \<rightarrow>\<^sub>r Some result"
  assumes "h \<turnstile> get_element_by_id ptr idd \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {ptr} {cast result} h h'"
proof -
  have "h = h'"
    using assms(5)
    by(auto simp add: preserved_def get_element_by_id_def first_in_tree_order_def
        elim!: bind_returns_heap_E2 intro!: map_filter_M_pure bind_pure_I
        split: option.splits list.splits)
  have "ptr |\<in>| object_ptr_kinds h"
    using assms(4)
    apply(auto simp add: get_element_by_id_def)[1]
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) bind_is_OK_E is_OK_returns_result_I
        local.first_in_tree_order_def local.to_tree_order_ptr_in_result local.to_tree_order_ptrs_in_heap)
  obtain to where to: "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
    by (meson \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) is_OK_returns_result_E
        local.to_tree_order_ok)
  then have "cast result \<in> set to"
    using assms(4) local.get_element_by_id_result_in_tree_order by auto
  obtain c where c: "h \<turnstile> a_get_scdom_component ptr \<rightarrow>\<^sub>r c"
    using \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) local.get_scdom_component_impl
      local.get_scdom_component_ok
    by blast

  then show ?thesis
    using assms \<open>h = h'\<close>
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def preserved_def
        get_element_by_id_def first_in_tree_order_def elim!: bind_returns_result_E2
        intro!: map_filter_M_pure bind_pure_I split: option.splits list.splits)[1]
    by (smt IntI \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(4) finite_set_in
        get_element_by_id_is_strongly_scdom_component_safe_step local.get_dom_component_ok
        local.get_dom_component_ptr local.get_scdom_component_impl
        local.get_scdom_component_subset_get_dom_component returns_result_select_result select_result_I2
        subsetD)
qed
end

interpretation i_get_scdom_component_get_element_by_id?: l_get_scdom_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_disconnected_nodes
  get_disconnected_nodes_locs to_tree_order get_parent get_parent_locs get_child_nodes
  get_child_nodes_locs get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_element_by_id get_elements_by_class_name get_elements_by_tag_name first_in_tree_order
  get_attribute get_attribute_locs
  by(auto simp add: l_get_scdom_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_elements\_by\_class\_name\<close>

locale l_get_scdom_component_get_elements_by_class_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_elements_by_class_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_elements_by_class_name_is_strongly_scdom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_elements_by_class_name ptr' idd \<rightarrow>\<^sub>r results"
  assumes "result \<in> set results"
  shows "cast result \<in> set sc \<longleftrightarrow> ptr' \<in> set sc"
  by (meson assms local.get_dom_component_ptr
      local.get_elements_by_class_name_is_strongly_dom_component_safe_step
      local.get_scdom_component_contains_get_dom_component subsetD)


lemma get_elements_by_class_name_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_elements_by_class_name ptr idd \<rightarrow>\<^sub>r results"
  assumes "h \<turnstile> get_elements_by_class_name ptr idd \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {ptr} (cast ` set results) h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson local.get_elements_by_class_name_pure pure_returns_heap_eq)
  have "ptr |\<in>| object_ptr_kinds h"
    using assms(4)
    apply(auto simp add: get_elements_by_class_name_def)[1]
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) bind_is_OK_E is_OK_returns_result_I
        local.first_in_tree_order_def local.to_tree_order_ptr_in_result local.to_tree_order_ptrs_in_heap)
  obtain to where to: "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
    by (meson \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) is_OK_returns_result_E
        local.to_tree_order_ok)
  then have "cast ` set results \<subseteq> set to"
    using assms(4) local.get_elements_by_class_name_result_in_tree_order by auto
  obtain c where c: "h \<turnstile> a_get_scdom_component ptr \<rightarrow>\<^sub>r c"
    using \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) local.get_scdom_component_impl
      local.get_scdom_component_ok by blast

  then show ?thesis
    using assms \<open>h = h'\<close>
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def preserved_def
        get_element_by_id_def first_in_tree_order_def elim!: bind_returns_result_E2 intro!: map_filter_M_pure
        bind_pure_I split: option.splits list.splits)[1]
    by (smt IntI \<open>ptr |\<in>| object_ptr_kinds h\<close> finite_set_in
        get_elements_by_class_name_is_strongly_scdom_component_safe_step local.get_dom_component_ok
        local.get_dom_component_ptr local.get_scdom_component_impl
        local.get_scdom_component_subset_get_dom_component returns_result_select_result select_result_I2 subsetD)
qed
end

interpretation i_get_scdom_component_get_elements_by_class_name?: l_get_scdom_component_get_elements_by_class_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_disconnected_nodes
  get_disconnected_nodes_locs to_tree_order get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_root_node get_root_node_locs get_ancestors get_ancestors_locs get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_scdom_component_get_elements_by_class_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_elements\_by\_tag\_name\<close>

locale l_get_scdom_component_get_elements_by_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_elements_by_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_elements_by_tag_name_is_strongly_scdom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_elements_by_tag_name ptr' idd \<rightarrow>\<^sub>r results"
  assumes "result \<in> set results"
  shows "cast result \<in> set sc \<longleftrightarrow> ptr' \<in> set sc"
  by (meson assms local.get_dom_component_ptr
      local.get_elements_by_tag_name_is_strongly_dom_component_safe_step
      local.get_scdom_component_contains_get_dom_component subsetD)


lemma get_elements_by_tag_name_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_elements_by_tag_name ptr idd \<rightarrow>\<^sub>r results"
  assumes "h \<turnstile> get_elements_by_tag_name ptr idd \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {ptr} (cast ` set results) h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson local.get_elements_by_tag_name_pure pure_returns_heap_eq)
  have "ptr |\<in>| object_ptr_kinds h"
    using assms(4)
    apply(auto simp add: get_elements_by_tag_name_def)[1]
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) bind_is_OK_E is_OK_returns_result_I
        local.first_in_tree_order_def local.to_tree_order_ptr_in_result local.to_tree_order_ptrs_in_heap)
  obtain to where to: "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
    by (meson \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) is_OK_returns_result_E
        local.to_tree_order_ok)
  then have "cast ` set results \<subseteq> set to"
    using assms(4) local.get_elements_by_tag_name_result_in_tree_order by auto
  obtain c where c: "h \<turnstile> a_get_scdom_component ptr \<rightarrow>\<^sub>r c"
    using \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) local.get_scdom_component_impl
      local.get_scdom_component_ok by blast

  then show ?thesis
    using assms \<open>h = h'\<close>
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def preserved_def
        get_element_by_id_def first_in_tree_order_def elim!: bind_returns_result_E2 intro!:
        map_filter_M_pure bind_pure_I split: option.splits list.splits)[1]
    by (smt IntI \<open>ptr |\<in>| object_ptr_kinds h\<close> finite_set_in
        get_elements_by_tag_name_is_strongly_scdom_component_safe_step local.get_dom_component_ok
        local.get_dom_component_ptr local.get_scdom_component_impl
        local.get_scdom_component_subset_get_dom_component returns_result_select_result select_result_I2
        subsetD)
qed
end

interpretation i_get_scdom_component_get_elements_by_tag_name?:
  l_get_scdom_component_get_elements_by_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe
  get_dom_component is_strongly_dom_component_safe is_weakly_dom_component_safe
  get_disconnected_nodes get_disconnected_nodes_locs to_tree_order get_parent get_parent_locs
  get_child_nodes get_child_nodes_locs get_root_node get_root_node_locs get_ancestors
  get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_scdom_component_get_elements_by_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>remove\_child\<close>

locale l_get_scdom_component_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_owner_document_wf +
  l_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs set_child_nodes set_child_nodes_locs
  get_parent get_parent_locs get_owner_document get_disconnected_nodes get_disconnected_nodes_locs
  set_disconnected_nodes set_disconnected_nodes_locs remove_child remove_child_locs remove type_wf
  known_ptr known_ptrs heap_is_wellformed parent_child_rel
begin
lemma remove_child_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove_child ptr' child \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component ptr'|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child)|\<^sub>r)|\<^sub>r"
    (* assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast child)|\<^sub>r" *)
  shows "preserved (get_M ptr getter) h h'"
proof -
  have "ptr \<noteq> ptr'"
    using assms(5)
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) is_OK_returns_heap_I
        is_OK_returns_result_E local.get_dom_component_ok local.get_dom_component_ptr
        local.remove_child_ptr_in_heap select_result_I2)

  obtain owner_document where owner_document: "h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r owner_document"
    by (meson assms(1) assms(2) assms(3) assms(4) is_OK_returns_result_E local.get_owner_document_ok
        local.remove_child_child_in_heap node_ptr_kinds_commutes)
  then
  obtain c where "h \<turnstile> get_dom_component (cast owner_document) \<rightarrow>\<^sub>r c"
    using get_dom_component_ok owner_document assms(1) assms(2) assms(3)
    by (meson document_ptr_kinds_commutes get_owner_document_owner_document_in_heap select_result_I)
  then
  have "ptr \<noteq> cast owner_document"
    using assms(6) assms(1) assms(2) assms(3) local.get_dom_component_ptr owner_document
    by auto

  show ?thesis
    using remove_child_writes assms(4)
    apply(rule reads_writes_preserved2)
    apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: option.splits)[1]
         apply (metis \<open>ptr \<noteq> ptr'\<close> document_ptr_casts_commute3 get_M_Mdocument_preserved3)
        apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
       apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
      apply (metis \<open>ptr \<noteq> ptr'\<close> element_ptr_casts_commute3 get_M_Element_preserved8)
     apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
    apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
    done
qed

lemma remove_child_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove_child ptr' child \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component ptr'|\<^sub>r"
    (* assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child)|\<^sub>r)|\<^sub>r" *)
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component (cast child)|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
proof -
  obtain sc where sc: "h \<turnstile> get_scdom_component ptr' \<rightarrow>\<^sub>r sc"
    using get_scdom_component_ok
    by (meson assms(1) assms(2) assms(3) assms(4) is_OK_returns_heap_I local.remove_child_ptr_in_heap
        returns_result_select_result)

  have "child |\<in>| node_ptr_kinds h"
    using assms(4) remove_child_child_in_heap by blast
  then
  obtain child_sc where child_sc: "h \<turnstile> get_scdom_component (cast child) \<rightarrow>\<^sub>r child_sc"
    using get_scdom_component_ok
    by (meson assms(1) assms(2) assms(3) node_ptr_kinds_commutes select_result_I)
  then obtain owner_document where owner_document: "h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r owner_document"
    by (meson \<open>child |\<in>| node_ptr_kinds h\<close> assms(1) assms(2) assms(3) contra_subsetD
        get_scdom_component_owner_document_same is_OK_returns_result_E
        get_scdom_component_subset_get_dom_component local.get_dom_component_ok local.get_dom_component_ptr
        node_ptr_kinds_commutes)
  then have "h \<turnstile> get_scdom_component (cast owner_document) \<rightarrow>\<^sub>r child_sc"
    using child_sc
    by (smt \<open>child |\<in>| node_ptr_kinds h\<close> assms(1) assms(2) assms(3) contra_subsetD
        get_scdom_component_subset_get_dom_component get_scdom_component_owner_document_same
        get_scdom_component_ptrs_same_scope_component local.get_dom_component_ok local.get_dom_component_ptr
        node_ptr_kinds_commutes returns_result_select_result select_result_I2)

  have "ptr \<notin> set |h \<turnstile> get_dom_component ptr'|\<^sub>r"
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) assms(5) contra_subsetD
        get_scdom_component_subset_get_dom_component is_OK_returns_heap_I local.get_dom_component_ok
        local.remove_child_ptr_in_heap returns_result_select_result sc select_result_I2)

  moreover have "ptr \<notin> set |h \<turnstile> get_scdom_component (cast |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child)|\<^sub>r)|\<^sub>r"
    using get_scdom_component_owner_document_same get_scdom_component_ptrs_same_scope_component
    by (metis (no_types, lifting)
        \<open>h \<turnstile> get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document) \<rightarrow>\<^sub>r child_sc\<close> assms(6) child_sc
        owner_document select_result_I2)
  have "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child)|\<^sub>r)|\<^sub>r"
    using get_scdom_component_owner_document_same
    by (metis (no_types, lifting)
        \<open>h \<turnstile> get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document) \<rightarrow>\<^sub>r child_sc\<close>
        \<open>ptr \<notin> set |h \<turnstile> get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child)|\<^sub>r)|\<^sub>r\<close>
        assms(1) assms(2) assms(3) contra_subsetD document_ptr_kinds_commutes get_scdom_component_subset_get_dom_component
        is_OK_returns_result_E local.get_dom_component_ok local.get_owner_document_owner_document_in_heap owner_document
        select_result_I2)
  ultimately show ?thesis
    using assms(1) assms(2) assms(3) assms(4) remove_child_is_component_unsafe by blast
qed



lemma remove_child_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {ptr, cast child} {} h h'"
proof -
  obtain owner_document children_h h2 disconnected_nodes_h where
    owner_document: "h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r owner_document" and
    children_h: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h" and
    child_in_children_h: "child \<in> set children_h" and
    disconnected_nodes_h: "h \<turnstile>  get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h" and
    h2: "h \<turnstile>  set_disconnected_nodes owner_document (child # disconnected_nodes_h) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> set_child_nodes ptr (remove1 child children_h) \<rightarrow>\<^sub>h h'"
    using assms(4)
    apply(auto simp add: remove_child_def elim!: bind_returns_heap_E
        dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure]
        pure_returns_heap_eq[rotated, OF get_child_nodes_pure] split: if_splits)[1]
    using pure_returns_heap_eq by fastforce

  have object_ptr_kinds_eq3: "object_ptr_kinds h = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF remove_child_writes assms(4)])
    unfolding remove_child_locs_def
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_eq: "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    unfolding object_ptr_kinds_M_defs by simp
  then have object_ptr_kinds_eq2: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    using select_result_eq by force
  then have node_ptr_kinds_eq2: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by auto
  then have node_ptr_kinds_eq3: "node_ptr_kinds h = node_ptr_kinds h'"
    using node_ptr_kinds_M_eq by auto
  have document_ptr_kinds_eq2: "|h \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_eq2 document_ptr_kinds_M_eq by auto
  then have document_ptr_kinds_eq3: "document_ptr_kinds h = document_ptr_kinds h'"
    using document_ptr_kinds_M_eq by auto
  have children_eq:
    "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    apply(rule reads_writes_preserved[OF get_child_nodes_reads remove_child_writes assms(4)])
    unfolding remove_child_locs_def
    using set_disconnected_nodes_get_child_nodes set_child_nodes_get_child_nodes_different_pointers
    by fast
  then have children_eq2:
    "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq: "\<And>document_ptr disconnected_nodes. document_ptr \<noteq> owner_document
         \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disconnected_nodes
             = h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disconnected_nodes"
    apply(rule reads_writes_preserved[OF get_disconnected_nodes_reads remove_child_writes assms(4)])
    unfolding remove_child_locs_def
    using set_child_nodes_get_disconnected_nodes set_disconnected_nodes_get_disconnected_nodes_different_pointers
    by (metis (no_types, lifting) Un_iff owner_document select_result_I2)
  then have disconnected_nodes_eq2:
    "\<And>document_ptr. document_ptr \<noteq> owner_document
    \<Longrightarrow> |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h"
    apply(rule reads_writes_separate_forwards[OF get_child_nodes_reads set_disconnected_nodes_writes h2 children_h] )
    by (simp add: set_disconnected_nodes_get_child_nodes)

  have "known_ptrs h'"
    using object_ptr_kinds_eq3 known_ptrs_preserved \<open>known_ptrs h\<close> by blast

  have "known_ptr ptr"
    using assms(3)
    using children_h get_child_nodes_ptr_in_heap local.known_ptrs_known_ptr by blast
  have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h2]
    using set_disconnected_nodes_types_preserved assms(2)
    by(auto simp add: reflp_def transp_def)
  then have "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_child_nodes_writes h']
    using  set_child_nodes_types_preserved
    by(auto simp add: reflp_def transp_def)

  have children_h': "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r remove1 child children_h"
    using assms(4) owner_document h2 disconnected_nodes_h children_h
    apply(auto simp add: remove_child_def split: if_splits)[1]
    apply(drule bind_returns_heap_E3)
      apply(auto split: if_splits)[1]
     apply(simp)
    apply(auto split: if_splits)[1]
    apply(drule bind_returns_heap_E3)
      apply(auto)[1]
     apply(simp)
    apply(drule bind_returns_heap_E3)
      apply(auto)[1]
     apply(simp)
    apply(drule bind_returns_heap_E4)
      apply(auto)[1]
     apply simp
    using \<open>type_wf h2\<close> set_child_nodes_get_child_nodes \<open>known_ptr ptr\<close> h'
    by blast

  have disconnected_nodes_h2: "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r child # disconnected_nodes_h"
    using owner_document assms(4) h2 disconnected_nodes_h
    apply (auto simp add: remove_child_def  split: if_splits)[1]
    apply(drule bind_returns_heap_E2)
      apply(auto split: if_splits)[1]
     apply(simp)
    by(auto simp add: local.set_disconnected_nodes_get_disconnected_nodes split: if_splits)
  then have disconnected_nodes_h': "h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r child # disconnected_nodes_h"
    apply(rule reads_writes_separate_forwards[OF get_disconnected_nodes_reads set_child_nodes_writes h'])
    by (simp add: set_child_nodes_get_disconnected_nodes)

  moreover have "a_acyclic_heap h"
    using assms(1)  by (simp add: heap_is_wellformed_def)
  have "parent_child_rel h' \<subseteq> parent_child_rel h"
  proof (standard, safe)
    fix parent child
    assume a1: "(parent, child) \<in> parent_child_rel h'"
    then show "(parent, child) \<in> parent_child_rel h"
    proof (cases "parent = ptr")
      case True
      then show ?thesis
        using a1 remove_child_removes_parent[OF assms(1) assms(4)] children_h children_h'
          get_child_nodes_ptr_in_heap
        apply(auto simp add: parent_child_rel_def object_ptr_kinds_eq )[1]
        by (metis imageI notin_set_remove1)
    next
      case False
      then show ?thesis
        using a1
        by(auto simp add: parent_child_rel_def object_ptr_kinds_eq3 children_eq2)
    qed
  qed
  then have "a_acyclic_heap h'"
    using \<open>a_acyclic_heap h\<close> acyclic_heap_def acyclic_subset by blast

  moreover have "a_all_ptrs_in_heap h"
    using assms(1)  by (simp add: heap_is_wellformed_def)
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def node_ptr_kinds_eq3 disconnected_nodes_eq)[1]
     apply (metis (no_types, lifting) \<open>type_wf h'\<close> assms local.get_child_nodes_ok local.known_ptrs_known_ptr
        local.remove_child_children_subset notin_fset object_ptr_kinds_eq3 returns_result_select_result subset_code(1))
    apply (metis (no_types, lifting) assms(4) disconnected_nodes_eq2 disconnected_nodes_h disconnected_nodes_h'
        document_ptr_kinds_eq3 finite_set_in local.remove_child_child_in_heap node_ptr_kinds_eq3 select_result_I2
        set_ConsD subset_code(1))
    done
  moreover have "a_owner_document_valid h"
    using assms(1)  by (simp add: heap_is_wellformed_def)
  then have "a_owner_document_valid h'"
    apply(auto simp add: a_owner_document_valid_def object_ptr_kinds_eq3 document_ptr_kinds_eq3
        node_ptr_kinds_eq3)[1]
  proof -
    fix node_ptr
    assume 0: "\<forall>node_ptr\<in>fset (node_ptr_kinds h'). (\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h' \<and>
node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) \<or> (\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h' \<and>
node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
      and 1: "node_ptr |\<in>| node_ptr_kinds h'"
      and 2: "\<forall>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h' \<longrightarrow> node_ptr \<notin> set |h' \<turnstile> get_child_nodes parent_ptr|\<^sub>r"
    then show "\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h'
                       \<and> node_ptr \<in> set |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    proof (cases "node_ptr = child")
      case True
      show ?thesis
        apply(rule exI[where x=owner_document])
        using children_eq2 disconnected_nodes_eq2 children_h children_h' disconnected_nodes_h' True
        by (metis (no_types, lifting) get_disconnected_nodes_ptr_in_heap is_OK_returns_result_I
            list.set_intros(1) select_result_I2)
    next
      case False
      then show ?thesis
        using 0 1 2 children_eq2 children_h children_h' disconnected_nodes_eq2 disconnected_nodes_h
          disconnected_nodes_h'
        apply(auto simp add: children_eq2 disconnected_nodes_eq2 dest!: select_result_I2)[1]
        by (metis children_eq2 disconnected_nodes_eq2 finite_set_in in_set_remove1 list.set_intros(2))
    qed
  qed

  moreover
  {
    have h0: "a_distinct_lists h"
      using assms(1)  by (simp add: heap_is_wellformed_def)
    moreover have ha1: "(\<Union>x\<in>set |h \<turnstile> object_ptr_kinds_M|\<^sub>r. set |h \<turnstile> get_child_nodes x|\<^sub>r)
                 \<inter> (\<Union>x\<in>set |h \<turnstile> document_ptr_kinds_M|\<^sub>r. set |h \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      using \<open>a_distinct_lists h\<close>
      unfolding a_distinct_lists_def
      by(auto)
    have ha2: "ptr |\<in>| object_ptr_kinds h"
      using children_h get_child_nodes_ptr_in_heap by blast
    have ha3: "child \<in> set |h \<turnstile> get_child_nodes ptr|\<^sub>r"
      using child_in_children_h children_h
      by(simp)
    have child_not_in: "\<And>document_ptr. document_ptr |\<in>| document_ptr_kinds h
                          \<Longrightarrow> child \<notin> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
      using ha1 ha2 ha3
      apply(simp)
      using IntI by fastforce
    moreover have "distinct |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
      apply(rule select_result_I)
      by(auto simp add: object_ptr_kinds_M_defs)
    moreover have "distinct |h \<turnstile> document_ptr_kinds_M|\<^sub>r"
      apply(rule select_result_I)
      by(auto simp add: document_ptr_kinds_M_defs)
    ultimately have "a_distinct_lists h'"
    proof(simp (no_asm) add: a_distinct_lists_def, safe)
      assume 1: "a_distinct_lists h"
        and 3: "distinct |h \<turnstile> object_ptr_kinds_M|\<^sub>r"

      assume 1: "a_distinct_lists h"
        and 3: "distinct |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
      have 4: "distinct (concat ((map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) |h \<turnstile> object_ptr_kinds_M|\<^sub>r)))"
        using 1 by(auto simp add: a_distinct_lists_def)
      show "distinct (concat (map (\<lambda>ptr. |h' \<turnstile> get_child_nodes ptr|\<^sub>r)
                     (sorted_list_of_set (fset (object_ptr_kinds h')))))"
      proof(rule distinct_concat_map_I[OF 3[unfolded object_ptr_kinds_eq2], simplified])
        fix x
        assume 5: "x |\<in>| object_ptr_kinds h'"
        then have 6: "distinct |h \<turnstile> get_child_nodes x|\<^sub>r"
          using 4 distinct_concat_map_E object_ptr_kinds_eq2 by fastforce
        obtain children where children: "h \<turnstile> get_child_nodes x \<rightarrow>\<^sub>r children"
          and distinct_children: "distinct children"
          by (metis "5" "6" assms get_child_nodes_ok local.known_ptrs_known_ptr
              object_ptr_kinds_eq3 select_result_I)
        obtain children' where children': "h' \<turnstile> get_child_nodes x \<rightarrow>\<^sub>r children'"
          using children children_eq children_h' by fastforce
        then have "distinct children'"
        proof (cases "ptr = x")
          case True
          then show ?thesis
            using children distinct_children children_h children_h'
            by (metis children' distinct_remove1 returns_result_eq)
        next
          case False
          then show ?thesis
            using children distinct_children children_eq[OF False]
            using children' distinct_lists_children h0
            using select_result_I2 by fastforce
        qed

        then show "distinct |h' \<turnstile> get_child_nodes x|\<^sub>r"
          using children' by(auto simp add: )
      next
        fix x y
        assume 5: "x |\<in>| object_ptr_kinds h'" and 6: "y |\<in>| object_ptr_kinds h'" and 7: "x \<noteq> y"
        obtain children_x where children_x: "h \<turnstile> get_child_nodes x \<rightarrow>\<^sub>r children_x"
          by (metis "5" assms get_child_nodes_ok is_OK_returns_result_E
              local.known_ptrs_known_ptr object_ptr_kinds_eq3)
        obtain children_y where children_y: "h \<turnstile> get_child_nodes y \<rightarrow>\<^sub>r children_y"
          by (metis "6" assms get_child_nodes_ok is_OK_returns_result_E
              local.known_ptrs_known_ptr object_ptr_kinds_eq3)
        obtain children_x' where children_x': "h' \<turnstile> get_child_nodes x \<rightarrow>\<^sub>r children_x'"
          using children_eq children_h' children_x by fastforce
        obtain children_y' where children_y': "h' \<turnstile> get_child_nodes y \<rightarrow>\<^sub>r children_y'"
          using children_eq children_h' children_y by fastforce
        have "distinct (concat (map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r) |h \<turnstile> object_ptr_kinds_M|\<^sub>r))"
          using h0 by(auto simp add: a_distinct_lists_def)
        then have 8: "set children_x \<inter> set children_y = {}"
          using "7" assms(1) children_x children_y local.heap_is_wellformed_one_parent by blast
        have "set children_x' \<inter> set children_y' = {}"
        proof (cases "ptr = x")
          case True
          then have "ptr \<noteq> y"
            by(simp add: 7)
          have "children_x' = remove1 child children_x"
            using children_h children_h' children_x children_x' True returns_result_eq by fastforce
          moreover have "children_y' = children_y"
            using children_y children_y' children_eq[OF \<open>ptr \<noteq> y\<close>] by auto
          ultimately show ?thesis
            using 8 set_remove1_subset by fastforce
        next
          case False
          then show ?thesis
          proof (cases "ptr = y")
            case True
            have "children_y' = remove1 child children_y"
              using children_h children_h' children_y children_y' True returns_result_eq by fastforce
            moreover have "children_x' = children_x"
              using children_x children_x' children_eq[OF \<open>ptr \<noteq> x\<close>] by auto
            ultimately show ?thesis
              using 8 set_remove1_subset by fastforce
          next
            case False
            have "children_x' = children_x"
              using children_x children_x' children_eq[OF \<open>ptr \<noteq> x\<close>] by auto
            moreover have "children_y' = children_y"
              using children_y children_y' children_eq[OF \<open>ptr \<noteq> y\<close>] by auto
            ultimately show ?thesis
              using 8 by simp
          qed
        qed
        then show "set |h' \<turnstile> get_child_nodes x|\<^sub>r \<inter> set |h' \<turnstile> get_child_nodes y|\<^sub>r = {}"
          using children_x' children_y'
          by (metis (no_types, lifting) select_result_I2)
      qed
    next
      assume 2: "distinct |h \<turnstile> document_ptr_kinds_M|\<^sub>r"
      then have 4: "distinct  (sorted_list_of_set (fset (document_ptr_kinds h')))"
        by simp
      have 3: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                        (sorted_list_of_set (fset (document_ptr_kinds h')))))"
        using h0
        by(simp add: a_distinct_lists_def document_ptr_kinds_eq3)

      show "distinct (concat (map (\<lambda>document_ptr. |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                         (sorted_list_of_set (fset (document_ptr_kinds h')))))"
      proof(rule distinct_concat_map_I[OF 4[unfolded document_ptr_kinds_eq3]])
        fix x
        assume 4: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
        have 5: "distinct |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
          using distinct_lists_disconnected_nodes[OF h0] 4 get_disconnected_nodes_ok
          by (simp add: assms document_ptr_kinds_eq3 select_result_I)
        show "distinct |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
        proof (cases "x = owner_document")
          case True
          have "child \<notin> set |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
            using child_not_in  document_ptr_kinds_eq2 "4" by fastforce
          moreover have "|h' \<turnstile> get_disconnected_nodes x|\<^sub>r = child # |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
            using disconnected_nodes_h' disconnected_nodes_h unfolding True
            by(simp)
          ultimately show ?thesis
            using 5 unfolding True
            by simp
        next
          case False
          show ?thesis
            using "5" False disconnected_nodes_eq2 by auto
        qed
      next
        fix x y
        assume 4: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
          and 5: "y \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))" and "x \<noteq> y"
        obtain disc_nodes_x where disc_nodes_x: "h \<turnstile> get_disconnected_nodes x \<rightarrow>\<^sub>r disc_nodes_x"
          using 4 get_disconnected_nodes_ok[OF \<open>type_wf h\<close>, of x] document_ptr_kinds_eq2
          by auto
        obtain disc_nodes_y where disc_nodes_y: "h \<turnstile> get_disconnected_nodes y \<rightarrow>\<^sub>r disc_nodes_y"
          using 5 get_disconnected_nodes_ok[OF \<open>type_wf h\<close>, of y] document_ptr_kinds_eq2
          by auto
        obtain disc_nodes_x' where disc_nodes_x': "h' \<turnstile> get_disconnected_nodes x \<rightarrow>\<^sub>r disc_nodes_x'"
          using 4 get_disconnected_nodes_ok[OF \<open>type_wf h'\<close>, of x] document_ptr_kinds_eq2
          by auto
        obtain disc_nodes_y' where disc_nodes_y': "h' \<turnstile> get_disconnected_nodes y \<rightarrow>\<^sub>r disc_nodes_y'"
          using 5 get_disconnected_nodes_ok[OF \<open>type_wf h'\<close>, of y] document_ptr_kinds_eq2
          by auto
        have "distinct
               (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) |h \<turnstile> document_ptr_kinds_M|\<^sub>r))"
          using h0 by (simp add: a_distinct_lists_def)
        then have 6: "set disc_nodes_x \<inter> set disc_nodes_y = {}"
          using \<open>x \<noteq> y\<close> assms(1) disc_nodes_x disc_nodes_y local.heap_is_wellformed_one_disc_parent
          by blast

        have "set disc_nodes_x' \<inter> set disc_nodes_y' = {}"
        proof (cases "x = owner_document")
          case True
          then have "y \<noteq> owner_document"
            using \<open>x \<noteq> y\<close> by simp
          then have "disc_nodes_y' = disc_nodes_y"
            using disconnected_nodes_eq[OF \<open>y \<noteq> owner_document\<close>] disc_nodes_y disc_nodes_y'
            by auto
          have "disc_nodes_x' = child # disc_nodes_x"
            using disconnected_nodes_h' disc_nodes_x disc_nodes_x' True disconnected_nodes_h returns_result_eq
            by fastforce
          have "child \<notin> set disc_nodes_y"
            using child_not_in  disc_nodes_y 5
            using document_ptr_kinds_eq2  by fastforce
          then show ?thesis
            apply(unfold \<open>disc_nodes_x' = child # disc_nodes_x\<close> \<open>disc_nodes_y' = disc_nodes_y\<close>)
            using 6 by auto
        next
          case False
          then show ?thesis
          proof (cases "y = owner_document")
            case True
            then have "disc_nodes_x' = disc_nodes_x"
              using disconnected_nodes_eq[OF \<open>x \<noteq> owner_document\<close>] disc_nodes_x disc_nodes_x' by auto
            have "disc_nodes_y' = child # disc_nodes_y"
              using disconnected_nodes_h' disc_nodes_y disc_nodes_y' True disconnected_nodes_h returns_result_eq
              by fastforce
            have "child \<notin> set disc_nodes_x"
              using child_not_in  disc_nodes_x 4
              using document_ptr_kinds_eq2  by fastforce
            then show ?thesis
              apply(unfold \<open>disc_nodes_y' = child # disc_nodes_y\<close> \<open>disc_nodes_x' = disc_nodes_x\<close>)
              using 6 by auto
          next
            case False
            have "disc_nodes_x' = disc_nodes_x"
              using disconnected_nodes_eq[OF \<open>x \<noteq> owner_document\<close>] disc_nodes_x disc_nodes_x' by auto
            have "disc_nodes_y' = disc_nodes_y"
              using disconnected_nodes_eq[OF \<open>y \<noteq> owner_document\<close>] disc_nodes_y disc_nodes_y' by auto
            then show ?thesis
              apply(unfold \<open>disc_nodes_y' = disc_nodes_y\<close> \<open>disc_nodes_x' = disc_nodes_x\<close>)
              using 6 by auto
          qed
        qed
        then show "set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
          using disc_nodes_x' disc_nodes_y' by auto
      qed
    next
      fix x xa xb
      assume 1: "xa \<in> fset (object_ptr_kinds h')"
        and 2: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
        and 3: "xb \<in> fset (document_ptr_kinds h')"
        and 4: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
      obtain disc_nodes where disc_nodes: "h \<turnstile> get_disconnected_nodes xb \<rightarrow>\<^sub>r disc_nodes"
        using 3 get_disconnected_nodes_ok[OF \<open>type_wf h\<close>, of xb] document_ptr_kinds_eq2 by auto
      obtain disc_nodes' where disc_nodes': "h' \<turnstile> get_disconnected_nodes xb \<rightarrow>\<^sub>r disc_nodes'"
        using 3 get_disconnected_nodes_ok[OF \<open>type_wf h'\<close>, of xb]  document_ptr_kinds_eq2 by auto

      obtain children where children: "h \<turnstile> get_child_nodes xa \<rightarrow>\<^sub>r children"
        by (metis "1" assms finite_set_in get_child_nodes_ok is_OK_returns_result_E
            local.known_ptrs_known_ptr object_ptr_kinds_eq3)
      obtain children' where children': "h' \<turnstile> get_child_nodes xa \<rightarrow>\<^sub>r children'"
        using children children_eq children_h' by fastforce
      have "\<And>x. x \<in> set |h \<turnstile> get_child_nodes xa|\<^sub>r \<Longrightarrow> x \<in> set |h \<turnstile> get_disconnected_nodes xb|\<^sub>r \<Longrightarrow> False"
        using 1 3
        apply(fold \<open> object_ptr_kinds h =  object_ptr_kinds h'\<close>)
        apply(fold \<open> document_ptr_kinds h =  document_ptr_kinds h'\<close>)
        using children disc_nodes h0 apply(auto simp add: a_distinct_lists_def)[1]
        by (metis (no_types, lifting) h0 local.distinct_lists_no_parent select_result_I2)
      then have 5: "\<And>x. x \<in> set children \<Longrightarrow> x \<in> set disc_nodes \<Longrightarrow> False"
        using children disc_nodes  by fastforce
      have 6: "|h' \<turnstile> get_child_nodes xa|\<^sub>r = children'"
        using children' by (simp add: )
      have 7: "|h' \<turnstile> get_disconnected_nodes xb|\<^sub>r = disc_nodes'"
        using disc_nodes' by (simp add: )
      have "False"
      proof (cases "xa = ptr")
        case True
        have "distinct children_h"
          using children_h distinct_lists_children h0 \<open>known_ptr ptr\<close> by blast
        have "|h' \<turnstile> get_child_nodes ptr|\<^sub>r = remove1 child children_h"
          using children_h'
          by(simp add: )
        have "children = children_h"
          using True children children_h by auto
        show ?thesis
          using disc_nodes' children' 5 2 4 children_h \<open>distinct children_h\<close> disconnected_nodes_h'
          apply(auto simp add: 6 7
              \<open>xa = ptr\<close> \<open>|h' \<turnstile> get_child_nodes ptr|\<^sub>r = remove1 child children_h\<close> \<open>children = children_h\<close>)[1]
          by (metis (no_types, lifting) disc_nodes disconnected_nodes_eq2 disconnected_nodes_h
              select_result_I2 set_ConsD)
      next
        case False
        have "children' = children"
          using children' children children_eq[OF False[symmetric]]
          by auto
        then show ?thesis
        proof (cases "xb = owner_document")
          case True
          then show ?thesis
            using disc_nodes disconnected_nodes_h disconnected_nodes_h'
            using "2" "4" "5" "6" "7" False \<open>children' = children\<close> assms(1) child_in_children_h
              child_parent_dual children children_h disc_nodes' get_child_nodes_ptr_in_heap
              list.set_cases list.simps(3) option.simps(1) returns_result_eq set_ConsD
            by (metis (no_types, hide_lams) assms)
        next
          case False
          then show ?thesis
            using "2" "4" "5" "6" "7" \<open>children' = children\<close> disc_nodes disc_nodes'
              disconnected_nodes_eq returns_result_eq
            by metis
        qed
      qed
      then show "x \<in> {}"
        by simp
    qed
  }

  ultimately have "heap_is_wellformed h'"
    using heap_is_wellformed_def by blast

  show ?thesis
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def object_ptr_kinds_eq3)[1]
    using assms(1) assms(2) assms(3) assms(4) local.get_scdom_component_impl
      remove_child_is_strongly_dom_component_safe_step
    by blast
qed
end

interpretation i_get_scdom_component_remove_child?: l_get_scdom_component_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_root_node get_root_node_locs get_ancestors
  get_ancestors_locs get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name set_child_nodes set_child_nodes_locs
  set_disconnected_nodes set_disconnected_nodes_locs remove_child remove_child_locs remove
  by(auto simp add: l_get_scdom_component_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsubsection \<open>adopt\_node\<close>

locale l_get_scdom_component_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node_wf +
  l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_owner_document_wf +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma adopt_node_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> adopt_node document_ptr node_ptr \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast document_ptr)|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast node_ptr)|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)|\<^sub>r)|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
proof -
  obtain owner_document where owner_document: "h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr) \<rightarrow>\<^sub>r owner_document"
    using assms(4) local.adopt_node_def by auto
  then
  obtain c where "h \<turnstile> get_dom_component (cast owner_document) \<rightarrow>\<^sub>r c"
    using get_dom_component_ok assms(1) assms(2) assms(3) get_owner_document_owner_document_in_heap
    by (meson document_ptr_kinds_commutes select_result_I)
  then
  have "ptr \<noteq> cast owner_document"
    using assms(6) assms(1) assms(2) assms(3) local.get_dom_component_ptr owner_document
    by (metis (no_types, lifting) assms(7) select_result_I2)

  have "document_ptr |\<in>| document_ptr_kinds h"
    using adopt_node_document_in_heap assms(1) assms(2) assms(3) assms(4) by auto
  then
  have "ptr \<noteq> cast document_ptr"
    using assms(5)
    using assms(1) assms(2) assms(3) local.get_dom_component_ptr get_dom_component_ok
    by (meson document_ptr_kinds_commutes returns_result_select_result)

  have "\<And>parent. |h \<turnstile> get_parent node_ptr|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr"
    by (metis assms(1) assms(2) assms(3) assms(6) is_OK_returns_result_I local.get_dom_component_ok
        local.get_dom_component_parent_inside local.get_dom_component_ptr local.get_owner_document_ptr_in_heap
        local.get_parent_ok node_ptr_kinds_commutes owner_document returns_result_select_result)

  show ?thesis
    using adopt_node_writes assms(4)
    apply(rule reads_writes_preserved2)
    apply(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_locs_def set_disconnected_nodes_locs_def all_args_def)[1]
                    apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr\<close> get_M_Mdocument_preserved3)
                   apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
                  apply(drule \<open>\<And>parent. |h \<turnstile> get_parent node_ptr|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr\<close>)[1] apply (metis element_ptr_casts_commute3 get_M_Element_preserved8 is_node_ptr_kind_none node_ptr_casts_commute3 option.case_eq_if)
                 apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
                apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr\<close> get_M_Mdocument_preserved3)
               apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
              apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr\<close> get_M_Mdocument_preserved3)
             apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
            apply(drule \<open>\<And>parent. |h \<turnstile> get_parent node_ptr|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr\<close>)[1] apply (metis document_ptr_casts_commute3 get_M_Mdocument_preserved3)
           apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
          apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr\<close> get_M_Mdocument_preserved3)
         apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
        apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr\<close> get_M_Mdocument_preserved3)
       apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
      apply(drule \<open>\<And>parent. |h \<turnstile> get_parent node_ptr|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr\<close>)[1]
      apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
     apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr\<close> get_M_Mdocument_preserved3)
    apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> get_M_Mdocument_preserved3 owner_document select_result_I2)
    done
qed

lemma adopt_node_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> adopt_node document_ptr node_ptr \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component (cast document_ptr)|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component (cast node_ptr)|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
proof -
  have "document_ptr |\<in>| document_ptr_kinds h"
    by (meson assms(1) assms(2) assms(3) assms(4) is_OK_returns_heap_I local.adopt_node_document_in_heap)
  then
  obtain sc where sc: "h \<turnstile> get_scdom_component (cast document_ptr) \<rightarrow>\<^sub>r sc"
    using get_scdom_component_ok
    by (meson assms(1) assms(2) assms(3) document_ptr_kinds_commutes returns_result_select_result)

  have "node_ptr |\<in>| node_ptr_kinds h"
    using assms(4)
    by (meson is_OK_returns_heap_I local.adopt_node_child_in_heap)
  then
  obtain child_sc where child_sc: "h \<turnstile> get_scdom_component (cast node_ptr) \<rightarrow>\<^sub>r child_sc"
    using get_scdom_component_ok
    by (meson assms(1) assms(2) assms(3) is_OK_returns_result_E node_ptr_kinds_commutes)

  then obtain owner_document where owner_document: "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r owner_document"
    by (meson \<open>node_ptr |\<in>| node_ptr_kinds h\<close> assms(1) assms(2) assms(3) contra_subsetD
        get_scdom_component_owner_document_same is_OK_returns_result_E
        get_scdom_component_subset_get_dom_component local.get_dom_component_ok local.get_dom_component_ptr
        node_ptr_kinds_commutes)
  then have "h \<turnstile> get_scdom_component (cast owner_document) \<rightarrow>\<^sub>r child_sc"
    using child_sc
    by (metis (no_types, lifting) \<open>node_ptr |\<in>| node_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        get_scdom_component_owner_document_same get_scdom_component_ptrs_same_scope_component
        get_scdom_component_subset_get_dom_component is_OK_returns_result_E local.get_dom_component_ok
        local.get_dom_component_ptr node_ptr_kinds_commutes select_result_I2 subset_code(1))

  have "ptr \<notin> set |h \<turnstile> get_dom_component (cast document_ptr)|\<^sub>r"
    by (metis (no_types, lifting) \<open>document_ptr |\<in>| document_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        assms(5) contra_subsetD document_ptr_kinds_commutes get_scdom_component_subset_get_dom_component
        local.get_dom_component_ok returns_result_select_result sc select_result_I2)

  moreover have "ptr \<notin> set |h \<turnstile> get_dom_component (cast node_ptr)|\<^sub>r"
    by (metis (no_types, lifting) \<open>node_ptr |\<in>| node_ptr_kinds h\<close> assms(1) assms(2) assms(3) assms(6)
        child_sc contra_subsetD get_scdom_component_subset_get_dom_component local.get_dom_component_ok
        node_ptr_kinds_commutes returns_result_select_result select_result_I2)

  moreover have "ptr \<notin> set |h \<turnstile> get_scdom_component (cast |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)|\<^sub>r)|\<^sub>r"
    using get_scdom_component_owner_document_same get_scdom_component_ptrs_same_scope_component
    by (metis (no_types, lifting)
        \<open>h \<turnstile> get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document) \<rightarrow>\<^sub>r child_sc\<close> assms(6) child_sc
        owner_document select_result_I2)
  have "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)|\<^sub>r)|\<^sub>r"
    using get_scdom_component_owner_document_same
    by (metis (no_types, hide_lams)
        \<open>\<And>thesis. (\<And>owner_document. h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr) \<rightarrow>\<^sub>r owner_document \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
        \<open>h \<turnstile> get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document) \<rightarrow>\<^sub>r child_sc\<close>
        \<open>ptr \<notin> set |h \<turnstile> get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r |h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)|\<^sub>r)|\<^sub>r\<close>
        assms(1) assms(2) assms(3) contra_subsetD document_ptr_kinds_commutes get_scdom_component_subset_get_dom_component
        is_OK_returns_result_E local.get_dom_component_ok local.get_owner_document_owner_document_in_heap owner_document
        returns_result_eq select_result_I2)
  ultimately show ?thesis
    using assms(1) assms(2) assms(3) assms(4) adopt_node_is_component_unsafe
    by blast
qed

lemma adopt_node_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and type_wf: "type_wf h" and known_ptrs: "known_ptrs h"
  assumes "h \<turnstile> adopt_node document_ptr child \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {cast document_ptr, cast child} {} h h'"
proof -

  obtain old_document parent_opt h2 where
    old_document: "h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r old_document"
    and
    parent_opt: "h \<turnstile> get_parent child \<rightarrow>\<^sub>r parent_opt"
    and
    h2: "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> remove_child parent child | None \<Rightarrow> return ()) \<rightarrow>\<^sub>h h2"
    and
    h': "h2 \<turnstile> (if document_ptr \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 child old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes document_ptr;
        set_disconnected_nodes document_ptr (child # disc_nodes)
      } else do {
        return ()
      }) \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: adopt_node_def elim!: bind_returns_heap_E
        dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure]
        pure_returns_heap_eq[rotated, OF get_parent_pure])

  have object_ptr_kinds_h_eq3: "object_ptr_kinds h = object_ptr_kinds h2"
    using h2 apply(simp split: option.splits)
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF remove_child_writes])
    using remove_child_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h:
    "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    unfolding object_ptr_kinds_M_defs by simp
  then have object_ptr_kinds_eq_h: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq_h: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast

  have wellformed_h2: "heap_is_wellformed h2"
    using h2 remove_child_heap_is_wellformed_preserved known_ptrs type_wf
    by (metis (no_types, lifting) assms(1) option.case_eq_if pure_returns_heap_eq return_pure)
  have "type_wf h2"
    using h2 remove_child_preserves_type_wf known_ptrs type_wf
    by (metis (no_types, lifting) assms(1) option.case_eq_if pure_returns_heap_eq return_pure)
  have "known_ptrs h2"
    using h2 remove_child_preserves_known_ptrs known_ptrs type_wf
    by (metis (no_types, lifting) assms(1) option.case_eq_if pure_returns_heap_eq return_pure)
  have "heap_is_wellformed h' \<and> known_ptrs h' \<and> type_wf h'"
  proof(cases "document_ptr = old_document")
    case True
    then show ?thesis
      using h' wellformed_h2 \<open>type_wf h2\<close> \<open>known_ptrs h2\<close> by auto
  next
    case False
    then obtain h3 old_disc_nodes disc_nodes_document_ptr_h3 where
      docs_neq: "document_ptr \<noteq> old_document" and
      old_disc_nodes: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r old_disc_nodes" and
      h3: "h2 \<turnstile> set_disconnected_nodes old_document (remove1 child old_disc_nodes) \<rightarrow>\<^sub>h h3" and
      disc_nodes_document_ptr_h3:
      "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_document_ptr_h3" and
      h': "h3 \<turnstile> set_disconnected_nodes document_ptr (child # disc_nodes_document_ptr_h3) \<rightarrow>\<^sub>h h'"
      using h'
      by(auto elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )

    have object_ptr_kinds_h2_eq3: "object_ptr_kinds h2 = object_ptr_kinds h3"
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
            OF set_disconnected_nodes_writes h3])
      using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
      by (auto simp add: reflp_def transp_def)
    then have object_ptr_kinds_M_eq_h2:
      "\<And>ptrs. h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
      by(simp add: object_ptr_kinds_M_defs)
    then have object_ptr_kinds_eq_h2: "|h2 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> object_ptr_kinds_M|\<^sub>r"
      by(simp)
    then have node_ptr_kinds_eq_h2: "|h2 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> node_ptr_kinds_M|\<^sub>r"
      using node_ptr_kinds_M_eq by blast
    then have node_ptr_kinds_eq3_h2: "node_ptr_kinds h2 = node_ptr_kinds h3"
      by auto
    have document_ptr_kinds_eq2_h2: "|h2 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> document_ptr_kinds_M|\<^sub>r"
      using object_ptr_kinds_eq_h2 document_ptr_kinds_M_eq by auto
    then have document_ptr_kinds_eq3_h2: "document_ptr_kinds h2 = document_ptr_kinds h3"
      using object_ptr_kinds_eq_h2 document_ptr_kinds_M_eq by auto
    have children_eq_h2:
      "\<And>ptr children. h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
      using get_child_nodes_reads set_disconnected_nodes_writes h3
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_child_nodes)
    then have children_eq2_h2: "\<And>ptr. |h2 \<turnstile> get_child_nodes ptr|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr|\<^sub>r"
      using select_result_eq by force

    have object_ptr_kinds_h3_eq3: "object_ptr_kinds h3 = object_ptr_kinds h'"
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
            OF set_disconnected_nodes_writes h'])
      using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
      by (auto simp add: reflp_def transp_def)
    then have object_ptr_kinds_M_eq_h3:
      "\<And>ptrs. h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
      by(simp add: object_ptr_kinds_M_defs)
    then have object_ptr_kinds_eq_h3: "|h3 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
      by(simp)
    then have node_ptr_kinds_eq_h3: "|h3 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
      using node_ptr_kinds_M_eq by blast
    then have node_ptr_kinds_eq3_h3: "node_ptr_kinds h3 = node_ptr_kinds h'"
      by auto
    have document_ptr_kinds_eq2_h3: "|h3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
      using object_ptr_kinds_eq_h3 document_ptr_kinds_M_eq by auto
    then have document_ptr_kinds_eq3_h3: "document_ptr_kinds h3 = document_ptr_kinds h'"
      using object_ptr_kinds_eq_h3 document_ptr_kinds_M_eq by auto
    have children_eq_h3:
      "\<And>ptr children. h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
      using get_child_nodes_reads set_disconnected_nodes_writes h'
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_child_nodes)
    then have children_eq2_h3: "\<And>ptr. |h3 \<turnstile> get_child_nodes ptr|\<^sub>r = |h' \<turnstile> get_child_nodes ptr|\<^sub>r"
      using select_result_eq by force

    have disconnected_nodes_eq_h2:
      "\<And>doc_ptr disc_nodes. old_document \<noteq> doc_ptr
      \<Longrightarrow> h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
      using get_disconnected_nodes_reads set_disconnected_nodes_writes h3
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
    then have disconnected_nodes_eq2_h2:
      "\<And>doc_ptr. old_document \<noteq> doc_ptr
       \<Longrightarrow> |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
      using select_result_eq by force
    obtain disc_nodes_old_document_h2 where disc_nodes_old_document_h2:
      "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disc_nodes_old_document_h2"
      using old_disc_nodes by blast
    then have disc_nodes_old_document_h3:
      "h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r remove1 child disc_nodes_old_document_h2"
      using h3 old_disc_nodes returns_result_eq set_disconnected_nodes_get_disconnected_nodes
      by fastforce
    have "distinct disc_nodes_old_document_h2"
      using disc_nodes_old_document_h2 local.heap_is_wellformed_disconnected_nodes_distinct wellformed_h2
      by blast


    have "type_wf h2"
    proof (insert h2, induct  parent_opt)
      case None
      then show ?case
        using type_wf by simp
    next
      case (Some option)
      then show ?case
        using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF remove_child_writes]
          type_wf remove_child_types_preserved
        by (simp add: reflp_def transp_def)
    qed
    then have "type_wf h3"
      using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h3]
      using  set_disconnected_nodes_types_preserved
      by(auto simp add: reflp_def transp_def)
    then have "type_wf h'"
      using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h']
      using  set_disconnected_nodes_types_preserved
      by(auto simp add: reflp_def transp_def)

    have "known_ptrs h3"
      using known_ptrs local.known_ptrs_preserved object_ptr_kinds_h2_eq3 object_ptr_kinds_h_eq3 by blast
    then have "known_ptrs h'"
      using local.known_ptrs_preserved object_ptr_kinds_h3_eq3 by blast

    have disconnected_nodes_eq_h3:
      "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr
       \<Longrightarrow> h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
      using get_disconnected_nodes_reads set_disconnected_nodes_writes h'
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
    then have disconnected_nodes_eq2_h3:
      "\<And>doc_ptr. document_ptr \<noteq> doc_ptr
      \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
      using select_result_eq by force
    have disc_nodes_document_ptr_h2:
      "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_document_ptr_h3"
      using disconnected_nodes_eq_h2 docs_neq disc_nodes_document_ptr_h3 by auto
    have disc_nodes_document_ptr_h': "
      h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r child # disc_nodes_document_ptr_h3"
      using h' disc_nodes_document_ptr_h3
      using set_disconnected_nodes_get_disconnected_nodes by blast

    have document_ptr_in_heap: "document_ptr |\<in>| document_ptr_kinds h2"
      using disc_nodes_document_ptr_h3 document_ptr_kinds_eq2_h2 get_disconnected_nodes_ok assms(1)
      unfolding heap_is_wellformed_def
      using disc_nodes_document_ptr_h2 get_disconnected_nodes_ptr_in_heap by blast
    have old_document_in_heap: "old_document |\<in>| document_ptr_kinds h2"
      using disc_nodes_old_document_h3 document_ptr_kinds_eq2_h2 get_disconnected_nodes_ok assms(1)
      unfolding heap_is_wellformed_def
      using get_disconnected_nodes_ptr_in_heap old_disc_nodes by blast

    have "child \<in> set disc_nodes_old_document_h2"
    proof (insert parent_opt h2, induct parent_opt)
      case None
      then have "h = h2"
        by(auto)
      moreover have "a_owner_document_valid h"
        using assms(1) heap_is_wellformed_def by(simp add: heap_is_wellformed_def)
      ultimately show ?case
        using old_document disc_nodes_old_document_h2 None(1) child_parent_dual[OF assms(1)]
          in_disconnected_nodes_no_parent assms(1) known_ptrs type_wf by blast
    next
      case (Some option)
      then show ?case
        apply(simp split: option.splits)
        using assms(1) disc_nodes_old_document_h2 old_document remove_child_in_disconnected_nodes known_ptrs
        by blast
    qed
    have "child \<notin> set (remove1 child disc_nodes_old_document_h2)"
      using disc_nodes_old_document_h3 h3 known_ptrs wellformed_h2 \<open>distinct disc_nodes_old_document_h2\<close>
      by auto
    have "child \<notin> set disc_nodes_document_ptr_h3"
    proof -
      have "a_distinct_lists h2"
        using heap_is_wellformed_def wellformed_h2 by blast
      then have 0: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                                          |h2 \<turnstile> document_ptr_kinds_M|\<^sub>r))"
        by(simp add: a_distinct_lists_def)
      show ?thesis
        using distinct_concat_map_E(1)[OF 0] \<open>child \<in> set disc_nodes_old_document_h2\<close>
          disc_nodes_old_document_h2 disc_nodes_document_ptr_h2
        by (meson \<open>type_wf h2\<close> docs_neq known_ptrs local.get_owner_document_disconnected_nodes
            local.known_ptrs_preserved object_ptr_kinds_h_eq3 returns_result_eq wellformed_h2)
    qed

    have child_in_heap: "child |\<in>| node_ptr_kinds h"
      using get_owner_document_ptr_in_heap[OF is_OK_returns_result_I[OF old_document]]
        node_ptr_kinds_commutes by blast
    have "a_acyclic_heap h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def)
    have "parent_child_rel h' \<subseteq> parent_child_rel h2"
    proof
      fix x
      assume "x \<in> parent_child_rel h'"
      then show "x \<in> parent_child_rel h2"
        using object_ptr_kinds_h2_eq3  object_ptr_kinds_h3_eq3 children_eq2_h2 children_eq2_h3
          mem_Collect_eq object_ptr_kinds_M_eq_h3 select_result_eq split_cong
        unfolding parent_child_rel_def
        by(simp)
    qed
    then have "a_acyclic_heap h'"
      using \<open>a_acyclic_heap h2\<close> acyclic_heap_def acyclic_subset by blast

    moreover have "a_all_ptrs_in_heap h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def)
    then have "a_all_ptrs_in_heap h3"
      apply(auto simp add: a_all_ptrs_in_heap_def node_ptr_kinds_eq3_h2 children_eq_h2)[1]
       apply (simp add: children_eq2_h2 object_ptr_kinds_h2_eq3 subset_code(1))
      by (metis (no_types, lifting) \<open>child \<in> set disc_nodes_old_document_h2\<close> \<open>type_wf h2\<close>
          disc_nodes_old_document_h2 disc_nodes_old_document_h3 disconnected_nodes_eq2_h2 document_ptr_kinds_eq3_h2
          in_set_remove1 local.get_disconnected_nodes_ok local.heap_is_wellformed_disc_nodes_in_heap node_ptr_kinds_eq3_h2
          returns_result_select_result select_result_I2 wellformed_h2)
    then have "a_all_ptrs_in_heap h'"
      apply(auto simp add: a_all_ptrs_in_heap_def node_ptr_kinds_eq3_h3 children_eq_h3)[1]
       apply (simp add: children_eq2_h3 object_ptr_kinds_h3_eq3 subset_code(1))
      by (metis (no_types, lifting) \<open>child \<in> set disc_nodes_old_document_h2\<close> disc_nodes_document_ptr_h'
          disc_nodes_document_ptr_h2 disc_nodes_old_document_h2 disconnected_nodes_eq2_h3 document_ptr_kinds_eq3_h3
          finite_set_in local.heap_is_wellformed_disc_nodes_in_heap node_ptr_kinds_eq3_h2 node_ptr_kinds_eq3_h3
          select_result_I2 set_ConsD subset_code(1) wellformed_h2)

    moreover have "a_owner_document_valid h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def)
    then have "a_owner_document_valid h'"
      apply(simp add: a_owner_document_valid_def node_ptr_kinds_eq_h2 node_ptr_kinds_eq3_h3
          object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 document_ptr_kinds_eq2_h2
          document_ptr_kinds_eq2_h3 children_eq2_h2 children_eq2_h3 )
      by (smt disc_nodes_document_ptr_h' disc_nodes_document_ptr_h2
          disc_nodes_old_document_h2 disc_nodes_old_document_h3
          disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 document_ptr_in_heap
          document_ptr_kinds_eq3_h2 document_ptr_kinds_eq3_h3 in_set_remove1
          list.set_intros(1) node_ptr_kinds_eq3_h2 node_ptr_kinds_eq3_h3
          object_ptr_kinds_h2_eq3 object_ptr_kinds_h3_eq3 select_result_I2
          set_subset_Cons subset_code(1))

    have a_distinct_lists_h2: "a_distinct_lists h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def)
    then have "a_distinct_lists h'"
      apply(auto simp add: a_distinct_lists_def object_ptr_kinds_eq_h3 object_ptr_kinds_eq_h2
          children_eq2_h2 children_eq2_h3)[1]
    proof -
      assume 1: "distinct (concat (map (\<lambda>ptr. |h' \<turnstile> get_child_nodes ptr|\<^sub>r)
                          (sorted_list_of_set (fset (object_ptr_kinds h')))))"
        and 2: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                             (sorted_list_of_set (fset (document_ptr_kinds h2)))))"
        and 3: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r)
                   \<inter> (\<Union>x\<in>fset (document_ptr_kinds h2). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      show "distinct (concat (map (\<lambda>document_ptr. |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                              (sorted_list_of_set (fset (document_ptr_kinds h')))))"
      proof(rule distinct_concat_map_I)
        show "distinct (sorted_list_of_set (fset (document_ptr_kinds h')))"
          by(auto simp add: document_ptr_kinds_M_def )
      next
        fix x
        assume a1: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
        have 4: "distinct |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r"
          using a_distinct_lists_h2 "2" a1 concat_map_all_distinct document_ptr_kinds_eq2_h2
            document_ptr_kinds_eq2_h3
          by fastforce
        then show "distinct |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
        proof (cases "old_document \<noteq> x")
          case True
          then show ?thesis
          proof (cases "document_ptr \<noteq> x")
            case True
            then show ?thesis
              using disconnected_nodes_eq2_h2[OF \<open>old_document \<noteq> x\<close>]
                disconnected_nodes_eq2_h3[OF \<open>document_ptr \<noteq> x\<close>] 4
              by(auto)
          next
            case False
            then show ?thesis
              using  disc_nodes_document_ptr_h3 disc_nodes_document_ptr_h' 4
                \<open>child \<notin> set disc_nodes_document_ptr_h3\<close>
              by(auto simp add: disconnected_nodes_eq2_h2[OF \<open>old_document \<noteq> x\<close>] )
          qed
        next
          case False
          then show ?thesis
            by (metis (no_types, hide_lams) \<open>distinct disc_nodes_old_document_h2\<close>
                disc_nodes_old_document_h3 disconnected_nodes_eq2_h3
                distinct_remove1 docs_neq select_result_I2)
        qed
      next
        fix x y
        assume a0: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
          and a1: "y \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
          and a2: "x \<noteq> y"

        moreover have 5: "set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
          using 2 calculation
          by (auto simp add: document_ptr_kinds_eq3_h2 document_ptr_kinds_eq3_h3 dest: distinct_concat_map_E(1))
        ultimately show "set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
        proof(cases "old_document = x")
          case True
          have "old_document \<noteq> y"
            using \<open>x \<noteq> y\<close> \<open>old_document = x\<close> by simp
          have "document_ptr \<noteq> x"
            using docs_neq \<open>old_document = x\<close> by auto
          show ?thesis
          proof(cases "document_ptr = y")
            case True
            then show ?thesis
              using 5 True select_result_I2[OF disc_nodes_document_ptr_h']
                select_result_I2[OF disc_nodes_document_ptr_h2]
                select_result_I2[OF disc_nodes_old_document_h2]
                select_result_I2[OF disc_nodes_old_document_h3] \<open>old_document = x\<close>
              by (metis (no_types, lifting) \<open>child \<notin> set (remove1 child disc_nodes_old_document_h2)\<close>
                  \<open>document_ptr \<noteq> x\<close> disconnected_nodes_eq2_h3 disjoint_iff_not_equal
                  notin_set_remove1 set_ConsD)
          next
            case False
            then show ?thesis
              using 5 select_result_I2[OF disc_nodes_document_ptr_h']
                select_result_I2[OF disc_nodes_document_ptr_h2]
                select_result_I2[OF disc_nodes_old_document_h2]
                select_result_I2[OF disc_nodes_old_document_h3]
                disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 \<open>old_document = x\<close>
                docs_neq \<open>old_document \<noteq> y\<close>
              by (metis (no_types, lifting) disjoint_iff_not_equal notin_set_remove1)
          qed
        next
          case False
          then show ?thesis
          proof(cases "old_document = y")
            case True
            then show ?thesis
            proof(cases "document_ptr = x")
              case True
              show ?thesis
                using 5 select_result_I2[OF disc_nodes_document_ptr_h']
                  select_result_I2[OF disc_nodes_document_ptr_h2]
                  select_result_I2[OF disc_nodes_old_document_h2]
                  select_result_I2[OF disc_nodes_old_document_h3]
                  \<open>old_document \<noteq> x\<close> \<open>old_document = y\<close> \<open>document_ptr = x\<close>
                apply(simp)
                by (metis (no_types, lifting) \<open>child \<notin> set (remove1 child disc_nodes_old_document_h2)\<close>
                    disconnected_nodes_eq2_h3 disjoint_iff_not_equal notin_set_remove1)
            next
              case False
              then show ?thesis
                using 5 select_result_I2[OF disc_nodes_document_ptr_h']
                  select_result_I2[OF disc_nodes_document_ptr_h2]
                  select_result_I2[OF disc_nodes_old_document_h2]
                  select_result_I2[OF disc_nodes_old_document_h3]
                  \<open>old_document \<noteq> x\<close> \<open>old_document = y\<close> \<open>document_ptr \<noteq> x\<close>
                by (metis (no_types, lifting) disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
                    disjoint_iff_not_equal docs_neq notin_set_remove1)
            qed
          next
            case False
            have "set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}"
              by (metis DocumentMonad.ptr_kinds_M_ok DocumentMonad.ptr_kinds_M_ptr_kinds False
                  \<open>type_wf h2\<close> a1 disc_nodes_old_document_h2 document_ptr_kinds_M_def
                  document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3
                  l_ptr_kinds_M.ptr_kinds_ptr_kinds_M local.get_disconnected_nodes_ok
                  local.heap_is_wellformed_one_disc_parent returns_result_select_result
                  wellformed_h2)
            then show ?thesis
            proof(cases "document_ptr = x")
              case True
              then have "document_ptr \<noteq> y"
                using \<open>x \<noteq> y\<close> by auto
              have "set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}"
                using \<open>set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}\<close>
                by blast
              then show ?thesis
                using 5 select_result_I2[OF disc_nodes_document_ptr_h']
                  select_result_I2[OF disc_nodes_document_ptr_h2]
                  select_result_I2[OF disc_nodes_old_document_h2]
                  select_result_I2[OF disc_nodes_old_document_h3]
                  \<open>old_document \<noteq> x\<close> \<open>old_document \<noteq> y\<close> \<open>document_ptr = x\<close> \<open>document_ptr \<noteq> y\<close>
                  \<open>child \<in> set disc_nodes_old_document_h2\<close> disconnected_nodes_eq2_h2
                  disconnected_nodes_eq2_h3
                  \<open>set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}\<close>
                by(auto)
            next
              case False
              then show ?thesis
              proof(cases "document_ptr = y")
                case True
                have f1: "set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set disc_nodes_document_ptr_h3 = {}"
                  using 2 a1 document_ptr_in_heap document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3
                    \<open>document_ptr \<noteq> x\<close> select_result_I2[OF disc_nodes_document_ptr_h3, symmetric]
                    disconnected_nodes_eq2_h2[OF docs_neq[symmetric], symmetric]
                  by (simp add: "5" True)
                moreover have f1:
                  "set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes old_document|\<^sub>r = {}"
                  using 2 a1 old_document_in_heap document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3
                    \<open>old_document \<noteq> x\<close>
                  by (metis (no_types, lifting) a0 distinct_concat_map_E(1) document_ptr_kinds_eq3_h2
                      document_ptr_kinds_eq3_h3 finite_fset fmember.rep_eq set_sorted_list_of_set)
                ultimately show ?thesis
                  using 5 select_result_I2[OF disc_nodes_document_ptr_h']
                    select_result_I2[OF disc_nodes_old_document_h2] \<open>old_document \<noteq> x\<close>
                    \<open>document_ptr \<noteq> x\<close> \<open>document_ptr = y\<close>
                    \<open>child \<in> set disc_nodes_old_document_h2\<close> disconnected_nodes_eq2_h2
                    disconnected_nodes_eq2_h3
                  by auto
              next
                case False
                then show ?thesis
                  using 5
                    select_result_I2[OF disc_nodes_old_document_h2] \<open>old_document \<noteq> x\<close>
                    \<open>document_ptr \<noteq> x\<close> \<open>document_ptr \<noteq> y\<close>
                    \<open>child \<in> set disc_nodes_old_document_h2\<close>
                    disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
                  by (metis \<open>set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}\<close>
                      empty_iff inf.idem)
              qed
            qed
          qed
        qed
      qed
    next
      fix x xa xb
      assume 0: "distinct (concat (map (\<lambda>ptr. |h' \<turnstile> get_child_nodes ptr|\<^sub>r)
                                  (sorted_list_of_set (fset (object_ptr_kinds h')))))"
        and 1: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                   (sorted_list_of_set (fset (document_ptr_kinds h2)))))"
        and 2: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r)
                    \<inter> (\<Union>x\<in>fset (document_ptr_kinds h2). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
        and 3: "xa |\<in>| object_ptr_kinds h'"
        and 4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
        and 5: "xb |\<in>| document_ptr_kinds h'"
        and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
      then show False
        using \<open>child \<in> set disc_nodes_old_document_h2\<close> disc_nodes_document_ptr_h'
          disc_nodes_document_ptr_h2 disc_nodes_old_document_h2 disc_nodes_old_document_h3
          disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 document_ptr_kinds_eq2_h2
          document_ptr_kinds_eq2_h3  old_document_in_heap
        apply(auto)[1]
        apply(cases "xb = old_document")
      proof -
        assume a1: "xb = old_document"
        assume a2: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disc_nodes_old_document_h2"
        assume a3: "h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r remove1 child disc_nodes_old_document_h2"
        assume a4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
        assume "document_ptr_kinds h2 = document_ptr_kinds h'"
        assume a5: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r)
                   \<inter> (\<Union>x\<in>fset (document_ptr_kinds h'). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
        have f6: "old_document |\<in>| document_ptr_kinds h'"
          using a1 \<open>xb |\<in>| document_ptr_kinds h'\<close> by blast
        have f7: "|h2 \<turnstile> get_disconnected_nodes old_document|\<^sub>r = disc_nodes_old_document_h2"
          using a2 by simp
        have "x \<in> set disc_nodes_old_document_h2"
          using f6 a3 a1 by (metis (no_types) \<open>type_wf h'\<close> \<open>x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r\<close>
              disconnected_nodes_eq_h3 docs_neq get_disconnected_nodes_ok returns_result_eq
              returns_result_select_result set_remove1_subset subsetCE)
        then have "set |h' \<turnstile> get_child_nodes xa|\<^sub>r \<inter>  set |h2 \<turnstile> get_disconnected_nodes xb|\<^sub>r = {}"
          using f7 f6 a5 a4 \<open>xa |\<in>| object_ptr_kinds h'\<close>
          by fastforce
        then show ?thesis
          using \<open>x \<in> set disc_nodes_old_document_h2\<close> a1 a4 f7 by blast
      next
        assume a1: "xb \<noteq> old_document"
        assume a2: "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_document_ptr_h3"
        assume a3: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disc_nodes_old_document_h2"
        assume a4: "xa |\<in>| object_ptr_kinds h'"
        assume a5: "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r child # disc_nodes_document_ptr_h3"
        assume a6: "old_document |\<in>| document_ptr_kinds h'"
        assume a7: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
        assume a8: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
        assume a9: "document_ptr_kinds h2 = document_ptr_kinds h'"
        assume a10: "\<And>doc_ptr. old_document \<noteq> doc_ptr
               \<Longrightarrow> |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
        assume a11: "\<And>doc_ptr. document_ptr \<noteq> doc_ptr
               \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
        assume a12: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r)
                    \<inter> (\<Union>x\<in>fset (document_ptr_kinds h'). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
        have f13: "\<And>d. d \<notin> set |h' \<turnstile> document_ptr_kinds_M|\<^sub>r \<or> h2 \<turnstile> ok get_disconnected_nodes d"
          using a9 \<open>type_wf h2\<close> get_disconnected_nodes_ok
          by simp
        then have f14: "|h2 \<turnstile> get_disconnected_nodes old_document|\<^sub>r = disc_nodes_old_document_h2"
          using a6 a3 by simp
        have "x \<notin> set |h2 \<turnstile> get_disconnected_nodes xb|\<^sub>r"
          using a12 a8 a4 \<open>xb |\<in>| document_ptr_kinds h'\<close>
          by (meson UN_I disjoint_iff_not_equal fmember.rep_eq)
        then have "x = child"
          using f13 a11 a10 a7 a5 a2 a1
          by (metis (no_types, lifting) select_result_I2 set_ConsD)
        then have "child \<notin> set disc_nodes_old_document_h2"
          using f14 a12 a8 a6 a4
          by (metis \<open>type_wf h'\<close> adopt_node_removes_child assms type_wf
              get_child_nodes_ok known_ptrs local.known_ptrs_known_ptr object_ptr_kinds_h2_eq3
              object_ptr_kinds_h3_eq3 object_ptr_kinds_h_eq3 returns_result_select_result)
        then show ?thesis
          using \<open>child \<in> set disc_nodes_old_document_h2\<close> by fastforce
      qed
    qed
    ultimately show ?thesis
      using \<open>type_wf h'\<close> \<open>known_ptrs h'\<close> \<open>a_owner_document_valid h'\<close> heap_is_wellformed_def by blast
  qed
  then have "heap_is_wellformed h'" and "known_ptrs h'" and "type_wf h'"
    by auto

  have object_ptr_kinds_eq3: "object_ptr_kinds h = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF adopt_node_writes assms(4)])
    unfolding adopt_node_locs_def
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
      remove_child_pointers_preserved
    by (auto simp add: reflp_def transp_def split: if_splits)
  show ?thesis
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def object_ptr_kinds_eq3 )[1]
    using adopt_node_is_strongly_dom_component_safe_step get_scdom_component_impl assms by blast
qed
end

interpretation i_get_scdom_component_adopt_node?: l_get_scdom_component_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_parent get_parent_locs remove_child
  remove_child_locs get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs adopt_node adopt_node_locs get_child_nodes get_child_nodes_locs
  set_child_nodes set_child_nodes_locs remove to_tree_order get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  by(auto simp add: l_get_scdom_component_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsubsection \<open>create\_element\<close>

locale l_get_scdom_component_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_dom_component_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_create_element_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma create_element_is_strongly_scdom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component (cast document_ptr)|\<^sub>r"
  assumes "ptr \<noteq> cast |h \<turnstile> create_element document_ptr tag|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
proof -
  obtain new_element_ptr h2 h3 disc_nodes where
    new_element_ptr: "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr" and
    h2: "h \<turnstile> new_element \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile>set_tag_name new_element_ptr tag \<rightarrow>\<^sub>h h3" and
    disc_nodes: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_element_ptr # disc_nodes) \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: create_element_def elim!: bind_returns_heap_E bind_returns_heap_E2[rotated,
          OF get_disconnected_nodes_pure, rotated])

  have object_ptr_kinds_eq_h: "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
    using new_element_new_ptr h2 new_element_ptr by blast
  then have node_ptr_kinds_eq_h: "node_ptr_kinds h2 = node_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h |\<union>| {|new_element_ptr|}"
    apply(simp add: element_ptr_kinds_def)
    by force
  have character_data_ptr_kinds_eq_h: "character_data_ptr_kinds h2 = character_data_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def character_data_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h2 = document_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: document_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h", OF set_tag_name_writes h3])
    using set_tag_name_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2
    by(auto simp add: node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_disconnected_nodes_writes h'])
    using set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)


  have "heap_is_wellformed h'"
    using assms(4)
    using assms(1) assms(2) assms(3) local.create_element_preserves_wellformedness(1) by blast
  have "type_wf h'"
    using assms(1) assms(2) assms(3) assms(4) local.create_element_preserves_wellformedness(2) by blast
  have "known_ptrs h'"
    using assms(1) assms(2) assms(3) assms(4) local.create_element_preserves_wellformedness(3) by blast

  have "document_ptr |\<in>| document_ptr_kinds h"
    by (meson assms(4) is_OK_returns_heap_I local.create_element_document_in_heap)
  then
  obtain sc where sc: "h \<turnstile> get_scdom_component (cast document_ptr) \<rightarrow>\<^sub>r sc"
    using get_scdom_component_ok
    by (meson assms(1) assms(2) assms(3) document_ptr_kinds_commutes returns_result_select_result)

  have "document_ptr |\<in>| document_ptr_kinds h'"
    using \<open>document_ptr |\<in>| document_ptr_kinds h\<close> document_ptr_kinds_eq_h
    using document_ptr_kinds_eq_h2 document_ptr_kinds_eq_h3 by blast
  then
  obtain sc' where sc': "h' \<turnstile> get_scdom_component (cast document_ptr) \<rightarrow>\<^sub>r sc'"
    using get_scdom_component_ok
    by (meson \<open>heap_is_wellformed h'\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> document_ptr_kinds_commutes
        returns_result_select_result)

  obtain c where c: "h \<turnstile> get_dom_component (cast document_ptr) \<rightarrow>\<^sub>r c"
    by (meson \<open>document_ptr |\<in>| document_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        document_ptr_kinds_commutes is_OK_returns_result_E local.get_dom_component_ok)

  have "set c \<subseteq> set sc"
    using assms(1) assms(2) assms(3) c get_scdom_component_subset_get_dom_component sc by blast

  have "ptr \<notin> set c"
    using \<open>set c \<subseteq> set sc\<close> assms(5) sc
    by auto
  then
  show ?thesis
    using create_element_is_weakly_dom_component_safe
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) assms(6) c
        local.create_element_is_weakly_dom_component_safe_step select_result_I2)
qed

lemma create_element_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r result"
  assumes "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {cast document_ptr} {cast result} h h'"
proof -
  obtain new_element_ptr h2 h3 disc_nodes_h3 where
    new_element_ptr: "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr" and
    h2: "h \<turnstile> new_element \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile> set_tag_name new_element_ptr tag \<rightarrow>\<^sub>h h3" and
    disc_nodes_h3: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_element_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'"
    using assms(5)
    by(auto simp add: create_element_def returns_result_heap_def
        elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )
  then have "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr"
    apply(auto simp add: create_element_def intro!: bind_returns_result_I)[1]
      apply (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
     apply (metis is_OK_returns_heap_E is_OK_returns_result_I local.get_disconnected_nodes_pure pure_returns_heap_eq)
    by (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
  then have "result = new_element_ptr"
    using assms(4) by auto


  have "new_element_ptr \<notin> set |h \<turnstile> element_ptr_kinds_M|\<^sub>r"
    using new_element_ptr ElementMonad.ptr_kinds_ptr_kinds_M h2
    using new_element_ptr_not_in_heap by blast
  then have "cast new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r"
    by simp
  then have "cast new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp

  have object_ptr_kinds_eq_h: "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
    using new_element_new_ptr h2 new_element_ptr by blast
  then have node_ptr_kinds_eq_h: "node_ptr_kinds h2 = node_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h |\<union>| {|new_element_ptr|}"
    apply(simp add: element_ptr_kinds_def)
    by force
  have character_data_ptr_kinds_eq_h: "character_data_ptr_kinds h2 = character_data_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def character_data_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h2 = document_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: document_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h", OF set_tag_name_writes h3])
    using set_tag_name_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2
    by(auto simp add: node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_disconnected_nodes_writes h'])
    using set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)

  have "known_ptr (cast new_element_ptr)"
    using \<open>h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr\<close> local.create_element_known_ptr by blast
  then
  have "known_ptrs h2"
    using known_ptrs_new_ptr object_ptr_kinds_eq_h \<open>known_ptrs h\<close> h2
    by blast
  then
  have "known_ptrs h3"
    using known_ptrs_preserved object_ptr_kinds_eq_h2 by blast
  then
  have "known_ptrs h'"
    using known_ptrs_preserved object_ptr_kinds_eq_h3 by blast


  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2
      get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>ptr' children. ptr' \<noteq> cast new_element_ptr
              \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h2 get_child_nodes_new_element[rotated, OF new_element_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h: "\<And>ptr'. ptr' \<noteq> cast new_element_ptr
                                    \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []"
    using new_element_ptr h2 new_element_ptr_in_heap[OF h2 new_element_ptr]
      new_element_is_element_ptr[OF new_element_ptr] new_element_no_child_nodes
    by blast
  have disconnected_nodes_eq_h:
    "\<And>doc_ptr disc_nodes. h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                             = h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads h2 get_disconnected_nodes_new_element[OF new_element_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have disconnected_nodes_eq2_h:
    "\<And>doc_ptr. |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_tag_name_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_tag_name_get_child_nodes)
  then have children_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h2:
    "\<And>doc_ptr disc_nodes. h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                               = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_tag_name_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_tag_name_get_disconnected_nodes)
  then have disconnected_nodes_eq2_h2:
    "\<And>doc_ptr. |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have "type_wf h2"
    using \<open>type_wf h\<close> new_element_types_preserved h2 by blast
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_tag_name_writes h3]
    using  set_tag_name_types_preserved
    by(auto simp add: reflp_def transp_def)
  then have "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h']
    using  set_disconnected_nodes_types_preserved
    by(auto simp add: reflp_def transp_def)

  have children_eq_h3:
    "\<And>ptr' children. h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_child_nodes)
  then have children_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h3:
    "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr
       \<Longrightarrow> h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                               = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then have disconnected_nodes_eq2_h3:
    "\<And>doc_ptr. document_ptr \<noteq> doc_ptr
                \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have disc_nodes_document_ptr_h2: "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h2 disc_nodes_h3 by auto
  then have disc_nodes_document_ptr_h: "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h by auto
  then have "cast new_element_ptr \<notin> set disc_nodes_h3"
    using \<open>heap_is_wellformed h\<close>
    using \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>
      a_all_ptrs_in_heap_def heap_is_wellformed_def
    using NodeMonad.ptr_kinds_ptr_kinds_M local.heap_is_wellformed_disc_nodes_in_heap by blast



  have "parent_child_rel h = parent_child_rel h'"
  proof -
    have "parent_child_rel h = parent_child_rel h2"
    proof(auto simp add: parent_child_rel_def)[1]
      fix a x
      assume 0: "a |\<in>| object_ptr_kinds h"
        and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      then show "a |\<in>| object_ptr_kinds h2"
        by (simp add: object_ptr_kinds_eq_h)
    next
      fix a x
      assume 0: "a |\<in>| object_ptr_kinds h"
        and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      then show "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
        by (metis ObjectMonad.ptr_kinds_ptr_kinds_M
            \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> children_eq2_h)
    next
      fix a x
      assume 0: "a |\<in>| object_ptr_kinds h2"
        and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
      then show "a |\<in>| object_ptr_kinds h"
        using object_ptr_kinds_eq_h \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close>
        by(auto)
    next
      fix a x
      assume 0: "a |\<in>| object_ptr_kinds h2"
        and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
      then show "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
        by (metis (no_types, lifting)
            \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close>
            children_eq2_h empty_iff empty_set image_eqI select_result_I2)
    qed
    also have "\<dots> = parent_child_rel h3"
      by(auto simp add: parent_child_rel_def object_ptr_kinds_eq_h2 children_eq2_h2)
    also have "\<dots> = parent_child_rel h'"
      by(auto simp add: parent_child_rel_def object_ptr_kinds_eq_h3 children_eq2_h3)
    finally show ?thesis
      by simp
  qed


  have "document_ptr |\<in>| document_ptr_kinds h'"
    by (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close> document_ptr_kinds_eq_h
        document_ptr_kinds_eq_h2 document_ptr_kinds_eq_h3)

  have "known_ptr (cast document_ptr)"
    using \<open>document_ptr |\<in>| document_ptr_kinds h\<close> assms(3) document_ptr_kinds_commutes
      local.known_ptrs_known_ptr by blast
  have "h \<turnstile> get_owner_document (cast document_ptr) \<rightarrow>\<^sub>r document_ptr"
    using \<open>known_ptr (cast document_ptr)\<close> \<open>document_ptr |\<in>| document_ptr_kinds h\<close>
    apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def)[1]
    apply(split invoke_splits, rule conjI)+
    by(auto simp add: known_ptr_impl known_ptr_defs CharacterDataClass.known_ptr_defs
        ElementClass.known_ptr_defs NodeClass.known_ptr_defs a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_pure_returns_result_I split: option.splits)
  have "h' \<turnstile> get_owner_document (cast document_ptr) \<rightarrow>\<^sub>r document_ptr"
    using \<open>known_ptr (cast document_ptr)\<close> \<open>document_ptr |\<in>| document_ptr_kinds h'\<close>
    apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def)[1]
    apply(split invoke_splits, rule conjI)+
    by(auto simp add: known_ptr_impl known_ptr_defs CharacterDataClass.known_ptr_defs
        ElementClass.known_ptr_defs NodeClass.known_ptr_defs a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_pure_returns_result_I split: option.splits)

  obtain to where to: "h \<turnstile> to_tree_order (cast document_ptr) \<rightarrow>\<^sub>r to"
    by (meson \<open>h \<turnstile> get_owner_document (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr) \<rightarrow>\<^sub>r document_ptr\<close> assms(1)
        assms(2) assms(3) is_OK_returns_result_E is_OK_returns_result_I local.get_owner_document_ptr_in_heap
        local.to_tree_order_ok)
  obtain to' where to': "h' \<turnstile> to_tree_order (cast document_ptr) \<rightarrow>\<^sub>r to'"
    by (metis \<open>document_ptr |\<in>| document_ptr_kinds h\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> assms(1) assms(2)
        assms(3) assms(5) document_ptr_kinds_commutes document_ptr_kinds_eq_h document_ptr_kinds_eq_h2
        document_ptr_kinds_eq_h3 is_OK_returns_result_E local.create_element_preserves_wellformedness(1)
        local.to_tree_order_ok)
  have "set to = set to'"
  proof safe
    fix x
    assume "x \<in> set to"
    show "x \<in> set to'"
      using to to'
      using to_tree_order_parent_child_rel \<open>parent_child_rel h = parent_child_rel h'\<close>
      by (metis \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> \<open>x \<in> set to\<close> assms(1) assms(2) assms(3) assms(5)
          local.create_element_preserves_wellformedness(1))
  next
    fix x
    assume "x \<in> set to'"
    show "x \<in> set to"
      using to to'
      using to_tree_order_parent_child_rel \<open>parent_child_rel h = parent_child_rel h'\<close>
      by (metis \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> \<open>x \<in> set to'\<close> assms(1) assms(2) assms(3) assms(5)
          local.create_element_preserves_wellformedness(1))
  qed

  have "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_element_ptr # disc_nodes_h3"
    using h' local.set_disconnected_nodes_get_disconnected_nodes by auto
  obtain disc_nodes_h' where disc_nodes_h': "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h'"
    and "cast new_element_ptr \<in> set disc_nodes_h'"
    and "disc_nodes_h' =  cast new_element_ptr # disc_nodes_h3"
    by (simp add: \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr # disc_nodes_h3\<close>)

  have "\<And>disc_ptr to to'. disc_ptr \<in> set disc_nodes_h3 \<Longrightarrow> h \<turnstile> to_tree_order (cast disc_ptr) \<rightarrow>\<^sub>r to \<Longrightarrow>
h' \<turnstile> to_tree_order (cast disc_ptr) \<rightarrow>\<^sub>r to' \<Longrightarrow> set to = set to'"
  proof safe
    fix disc_ptr to to' x
    assume "disc_ptr \<in> set disc_nodes_h3"
    assume "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to"
    assume "h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'"
    assume "x \<in> set to"
    show "x \<in> set to'"
      using to_tree_order_parent_child_rel \<open>parent_child_rel h = parent_child_rel h'\<close>
      by (metis \<open>h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to\<close>
          \<open>h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> \<open>x \<in> set to\<close>
          assms(1) assms(2) assms(3) assms(5) local.create_element_preserves_wellformedness(1))
  next
    fix disc_ptr to to' x
    assume "disc_ptr \<in> set disc_nodes_h3"
    assume "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to"
    assume "h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'"
    assume "x \<in> set to'"
    show "x \<in> set to"
      using to_tree_order_parent_child_rel \<open>parent_child_rel h = parent_child_rel h'\<close>
      by (metis \<open>h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to\<close>
          \<open>h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> \<open>x \<in> set to'\<close>
          assms(1) assms(2) assms(3) assms(5) local.create_element_preserves_wellformedness(1))
  qed

  have "heap_is_wellformed h'"
    using assms(1) assms(2) assms(3) assms(5) local.create_element_preserves_wellformedness(1)
    by blast

  have "cast new_element_ptr |\<in>| object_ptr_kinds h'"
    using \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<in> set disc_nodes_h'\<close> \<open>heap_is_wellformed h'\<close> disc_nodes_h'
      local.heap_is_wellformed_disc_nodes_in_heap node_ptr_kinds_commutes by blast
  then
  have "new_element_ptr |\<in>| element_ptr_kinds h'"
    by simp

  have "\<And>node_ptr. node_ptr \<in> set disc_nodes_h3 \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h'"
    by (meson \<open>heap_is_wellformed h'\<close> h' local.heap_is_wellformed_disc_nodes_in_heap
        local.set_disconnected_nodes_get_disconnected_nodes set_subset_Cons subset_code(1))

  have "h \<turnstile> ok (map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) disc_nodes_h3)"
    using assms(1) assms(2) assms(3) to_tree_order_ok
    apply(auto intro!: map_M_ok_I)[1]
    using disc_nodes_document_ptr_h local.heap_is_wellformed_disc_nodes_in_heap node_ptr_kinds_commutes
    by blast
  then
  obtain disc_tree_orders where disc_tree_orders:
    "h \<turnstile> map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) disc_nodes_h3 \<rightarrow>\<^sub>r disc_tree_orders"
    by auto

  have "h' \<turnstile> ok (map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) disc_nodes_h')"
    apply(auto intro!: map_M_ok_I)[1]
    apply(simp add: \<open>disc_nodes_h' =  cast new_element_ptr # disc_nodes_h3\<close>)
    using \<open>\<And>node_ptr. node_ptr \<in> set disc_nodes_h3 \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h'\<close>
      \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<in> set disc_nodes_h'\<close> \<open>heap_is_wellformed h'\<close> \<open>known_ptrs h'\<close>
      \<open>type_wf h'\<close> disc_nodes_h' local.heap_is_wellformed_disc_nodes_in_heap local.to_tree_order_ok
      node_ptr_kinds_commutes by blast
  then
  obtain disc_tree_orders' where disc_tree_orders':
    "h' \<turnstile> map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) disc_nodes_h' \<rightarrow>\<^sub>r disc_tree_orders'"
    by auto

  have "h' \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []"
    using \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close> children_eq_h2
      children_eq_h3 by auto

  obtain new_tree_order where new_tree_order:
    "h' \<turnstile> to_tree_order (cast new_element_ptr) \<rightarrow>\<^sub>r new_tree_order" and
    "new_tree_order \<in> set disc_tree_orders'"
    using map_M_pure_E[OF disc_tree_orders' \<open>cast new_element_ptr \<in> set disc_nodes_h'\<close>]
    by auto
  then have "new_tree_order = [cast new_element_ptr]"
    using \<open>h' \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []\<close>
    by(auto simp add: to_tree_order_def
        dest!: bind_returns_result_E3[rotated, OF \<open>h' \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []\<close>, rotated])

  obtain foo where foo: "h' \<turnstile> map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r)
(cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr # disc_nodes_h3) \<rightarrow>\<^sub>r [cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr] # foo"
    apply(auto intro!: bind_pure_returns_result_I map_M_pure_I)[1]
    using \<open>new_tree_order = [cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr]\<close> new_tree_order apply auto[1]
    by (smt \<open>disc_nodes_h' = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr # disc_nodes_h3\<close>
        bind_pure_returns_result_I bind_returns_result_E2 comp_apply disc_tree_orders'
        local.to_tree_order_pure map_M.simps(2) map_M_pure_I return_returns_result returns_result_eq)
  then have "set (concat foo) = set (concat disc_tree_orders)"
    apply(auto elim!: bind_returns_result_E2 intro!: map_M_pure_I)[1]
     apply (smt \<open>\<And>to' toa disc_ptr. \<lbrakk>disc_ptr \<in> set disc_nodes_h3;
h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r toa; h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'\<rbrakk>
\<Longrightarrow> set toa = set to'\<close> comp_apply disc_tree_orders local.to_tree_order_pure map_M_pure_E map_M_pure_E2)
    using \<open>\<And>to' toa disc_ptr. \<lbrakk>disc_ptr \<in> set disc_nodes_h3; h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r toa;
h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'\<rbrakk> \<Longrightarrow> set toa = set to'\<close> comp_apply
      disc_tree_orders local.to_tree_order_pure map_M_pure_E map_M_pure_E2
    by smt

  have "disc_tree_orders' = [cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr] # foo"
    using foo disc_tree_orders'
    by (simp add: \<open>disc_nodes_h' = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr # disc_nodes_h3\<close> returns_result_eq)

  have "set (concat disc_tree_orders') = {cast new_element_ptr} \<union> set (concat disc_tree_orders)"
    apply(auto simp add: \<open>disc_tree_orders' = [cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr] # foo\<close>)[1]
    using \<open>set (concat foo) = set (concat disc_tree_orders)\<close> by auto

  have "h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr) \<rightarrow>\<^sub>r to' @ concat disc_tree_orders'"
    using \<open>h' \<turnstile> get_owner_document (cast document_ptr) \<rightarrow>\<^sub>r document_ptr\<close> disc_nodes_h' to' disc_tree_orders'
    by(auto simp add: a_get_scdom_component_def intro!: bind_pure_returns_result_I map_M_pure_I)
  then
  have "set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to' \<union> set (concat disc_tree_orders')"
    by auto
  have "h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr) \<rightarrow>\<^sub>r to @ concat disc_tree_orders"
    using \<open>h \<turnstile> get_owner_document (cast document_ptr) \<rightarrow>\<^sub>r document_ptr\<close> disc_nodes_document_ptr_h
      to disc_tree_orders
    by(auto simp add: a_get_scdom_component_def intro!: bind_pure_returns_result_I map_M_pure_I)
  then
  have "set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r = set to \<union> set (concat disc_tree_orders)"
    by auto

  have "{cast new_element_ptr} \<union> set |h \<turnstile> local.a_get_scdom_component (cast document_ptr)|\<^sub>r =
set |h' \<turnstile> local.a_get_scdom_component (cast document_ptr)|\<^sub>r"
  proof(safe)
    show "cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr
         \<in> set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
      using \<open>h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr) \<rightarrow>\<^sub>r to' @ concat disc_tree_orders'\<close>
      apply(auto simp add: a_get_scdom_component_def)[1]
      by (meson \<open>\<And>thesis. (\<And>new_tree_order. \<lbrakk>h' \<turnstile> to_tree_order (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r new_tree_order;
new_tree_order \<in> set disc_tree_orders'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> local.to_tree_order_ptr_in_result)
  next
    fix x
    assume " x \<in> set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
    then
    show "x \<in> set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
      using \<open>set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to \<union>set (concat disc_tree_orders)\<close>
      using \<open>set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to' \<union> set (concat disc_tree_orders')\<close>
      using \<open>set to = set to'\<close>
      using \<open>set (concat disc_tree_orders') = {cast new_element_ptr} \<union> set (concat disc_tree_orders)\<close>
      by(auto)
  next
    fix x
    assume " x \<in> set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
    assume "x \<notin> set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
    show "x = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr"
      using \<open>set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to \<union> set (concat disc_tree_orders)\<close>
      using \<open>set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to' \<union> set (concat disc_tree_orders')\<close>
      using \<open>set to = set to'\<close>
      using \<open>set (concat disc_tree_orders') = {cast new_element_ptr} \<union> set (concat disc_tree_orders)\<close>
      using \<open>x \<in> set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r\<close>
        \<open>x \<notin> set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r\<close>
      by auto
  qed


  have "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
    using object_ptr_kinds_eq_h object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 by auto
  then
  show ?thesis
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def)[1]
       apply(rule bexI[where x="cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr"])
    using \<open>{cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr} \<union>
set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r\<close>
        apply auto[2]
    using \<open>set to = set to'\<close> \<open>set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to \<union> set (concat disc_tree_orders)\<close> local.to_tree_order_ptr_in_result to'
        apply auto[1]
    using \<open>document_ptr |\<in>| document_ptr_kinds h\<close>
       apply blast
      apply(rule bexI[where x="cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr"])
    using \<open>result = new_element_ptr\<close>
      \<open>{cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr} \<union> set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r\<close> apply auto[1]
      apply(auto)[1]
    using \<open>set to = set to'\<close> \<open>set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to \<union> set (concat disc_tree_orders)\<close> local.to_tree_order_ptr_in_result to' apply auto[1]
      apply (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close>)
    using \<open>\<And>thesis. (\<And>new_element_ptr h2 h3 disc_nodes_h3. \<lbrakk>h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr;
h \<turnstile> new_element \<rightarrow>\<^sub>h h2; h2 \<turnstile> set_tag_name new_element_ptr tag \<rightarrow>\<^sub>h h3;
h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3;
h3 \<turnstile> set_disconnected_nodes document_ptr (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
      new_element_ptr new_element_ptr_not_in_heap
     apply auto[1]
    using create_element_is_strongly_scdom_component_safe_step
    by (smt ObjectMonad.ptr_kinds_ptr_kinds_M \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>
        \<open>result = new_element_ptr\<close> assms(1) assms(2) assms(3) assms(4) assms(5) local.get_scdom_component_impl select_result_I2)
qed
end

interpretation i_get_scdom_component_remove_child?: l_get_scdom_component_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs get_scdom_component
  is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe to_tree_order get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_root_node get_root_node_locs get_ancestors get_ancestors_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_element_by_id get_elements_by_class_name get_elements_by_tag_name set_child_nodes set_child_nodes_locs
  set_disconnected_nodes set_disconnected_nodes_locs remove_child remove_child_locs remove
  by(auto simp add: l_get_scdom_component_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>create\_character\_data\<close>

locale l_get_scdom_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_dom_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_create_character_data_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma create_character_data_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component (cast document_ptr)|\<^sub>r"
  assumes "ptr \<noteq> cast |h \<turnstile> create_character_data document_ptr text|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
proof -
  have "document_ptr |\<in>| document_ptr_kinds h"
    by (meson assms(4) is_OK_returns_heap_I local.create_character_data_document_in_heap)
  then
  obtain sc where sc: "h \<turnstile> get_scdom_component (cast document_ptr) \<rightarrow>\<^sub>r sc"
    using get_scdom_component_ok
    by (meson assms(1) assms(2) assms(3) document_ptr_kinds_commutes returns_result_select_result)

  obtain c where c: "h \<turnstile> get_dom_component (cast document_ptr) \<rightarrow>\<^sub>r c"
    by (meson \<open>document_ptr |\<in>| document_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        document_ptr_kinds_commutes is_OK_returns_result_E local.get_dom_component_ok)

  have "set c \<subseteq> set sc"
    using assms(1) assms(2) assms(3) c get_scdom_component_subset_get_dom_component sc by blast

  have "ptr \<notin> set c"
    using \<open>set c \<subseteq> set sc\<close> assms(5) sc
    by auto
  then
  show ?thesis
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) assms(6) c
        local.create_character_data_is_weakly_dom_component_safe_step select_result_I2)
qed

lemma create_character_data_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r result"
  assumes "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {cast document_ptr} {cast result} h h'"
proof -

  obtain new_character_data_ptr h2 h3 disc_nodes_h3 where
    new_character_data_ptr: "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr" and
    h2: "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile> set_val new_character_data_ptr text \<rightarrow>\<^sub>h h3" and
    disc_nodes_h3: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_character_data_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'"
    using assms(5)
    by(auto simp add: create_character_data_def
        elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )
  then have "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr"
    apply(auto simp add: create_character_data_def intro!: bind_returns_result_I)[1]
      apply (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
     apply (metis is_OK_returns_heap_E is_OK_returns_result_I local.get_disconnected_nodes_pure
        pure_returns_heap_eq)
    by (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
  then have "result = new_character_data_ptr"
    using assms(4) by auto

  have "new_character_data_ptr \<notin> set |h \<turnstile> character_data_ptr_kinds_M|\<^sub>r"
    using new_character_data_ptr CharacterDataMonad.ptr_kinds_ptr_kinds_M h2
    using new_character_data_ptr_not_in_heap by blast
  then have "cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r"
    by simp
  then have "cast new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp



  have object_ptr_kinds_eq_h:
    "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    using new_character_data_new_ptr h2 new_character_data_ptr by blast
  then have node_ptr_kinds_eq_h:
    "node_ptr_kinds h2 = node_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have character_data_ptr_kinds_eq_h:
    "character_data_ptr_kinds h2 = character_data_ptr_kinds h |\<union>| {|new_character_data_ptr|}"
    apply(simp add: character_data_ptr_kinds_def)
    by force
  have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h2 = document_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: document_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_val_writes h3])
    using set_val_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2
    by(auto simp add: node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_disconnected_nodes_writes h'])
    using set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)


  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2
      get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>ptr' children. ptr' \<noteq> cast new_character_data_ptr
                  \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h2 get_child_nodes_new_character_data[rotated, OF new_character_data_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h:
    "\<And>ptr'. ptr' \<noteq> cast new_character_data_ptr
      \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have object_ptr_kinds_eq_h:
    "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    using new_character_data_new_ptr h2 new_character_data_ptr by blast
  then have node_ptr_kinds_eq_h:
    "node_ptr_kinds h2 = node_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have character_data_ptr_kinds_eq_h:
    "character_data_ptr_kinds h2 = character_data_ptr_kinds h |\<union>| {|new_character_data_ptr|}"
    apply(simp add: character_data_ptr_kinds_def)
    by force
  have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h2 = document_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: document_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_val_writes h3])
    using set_val_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2
    by(auto simp add: node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_disconnected_nodes_writes h'])
    using set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)


  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2
      get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>ptr' children. ptr' \<noteq> cast new_character_data_ptr
                \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h2 get_child_nodes_new_character_data[rotated, OF new_character_data_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h: "\<And>ptr'. ptr' \<noteq> cast new_character_data_ptr
                                 \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []"
    using new_character_data_ptr h2 new_character_data_ptr_in_heap[OF h2 new_character_data_ptr]
      new_character_data_is_character_data_ptr[OF new_character_data_ptr]
      new_character_data_no_child_nodes
    by blast
  have disconnected_nodes_eq_h:
    "\<And>doc_ptr disc_nodes. h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                             = h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads h2
      get_disconnected_nodes_new_character_data[OF new_character_data_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have disconnected_nodes_eq2_h:
    "\<And>doc_ptr. |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_val_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_val_get_child_nodes)
  then have children_eq2_h2:
    "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h2:
    "\<And>doc_ptr disc_nodes. h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                              = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_val_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_val_get_disconnected_nodes)
  then have disconnected_nodes_eq2_h2:
    "\<And>doc_ptr. |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have "type_wf h2"
    using \<open>type_wf h\<close> new_character_data_types_preserved h2 by blast
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_val_writes h3]
    using  set_val_types_preserved
    by(auto simp add: reflp_def transp_def)
  then have "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h']
    using  set_disconnected_nodes_types_preserved
    by(auto simp add: reflp_def transp_def)

  have children_eq_h3:
    "\<And>ptr' children. h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_child_nodes)
  then have children_eq2_h3:
    " \<And>ptr'. |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h3: "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr
    \<Longrightarrow> h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                            = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then have disconnected_nodes_eq2_h3: "\<And>doc_ptr. document_ptr \<noteq> doc_ptr
             \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have disc_nodes_document_ptr_h2: "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h2 disc_nodes_h3 by auto
  then have disc_nodes_document_ptr_h: "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h by auto
  then have "cast new_character_data_ptr \<notin> set disc_nodes_h3"
    using \<open>heap_is_wellformed h\<close> using \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>
      a_all_ptrs_in_heap_def heap_is_wellformed_def
    using NodeMonad.ptr_kinds_ptr_kinds_M local.heap_is_wellformed_disc_nodes_in_heap by blast





  have "parent_child_rel h = parent_child_rel h'"
  proof -
    have "parent_child_rel h = parent_child_rel h2"
    proof(auto simp add: parent_child_rel_def)[1]
      fix a x
      assume 0: "a |\<in>| object_ptr_kinds h"
        and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      then show "a |\<in>| object_ptr_kinds h2"
        by (simp add: object_ptr_kinds_eq_h)
    next
      fix a x
      assume 0: "a |\<in>| object_ptr_kinds h"
        and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      then show "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
        by (metis ObjectMonad.ptr_kinds_ptr_kinds_M
            \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> children_eq2_h)
    next
      fix a x
      assume 0: "a |\<in>| object_ptr_kinds h2"
        and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
      then show "a |\<in>| object_ptr_kinds h"
        using object_ptr_kinds_eq_h \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
        by(auto)
    next
      fix a x
      assume 0: "a |\<in>| object_ptr_kinds h2"
        and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
      then show "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
        by (metis (no_types, lifting) \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
            children_eq2_h empty_iff empty_set image_eqI select_result_I2)
    qed
    also have "\<dots> = parent_child_rel h3"
      by(auto simp add: parent_child_rel_def object_ptr_kinds_eq_h2 children_eq2_h2)
    also have "\<dots> = parent_child_rel h'"
      by(auto simp add: parent_child_rel_def object_ptr_kinds_eq_h3 children_eq2_h3)
    finally show ?thesis
      by simp
  qed

  have "known_ptr (cast new_character_data_ptr)"
    using \<open>h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr\<close>
      create_character_data_known_ptr by blast
  then
  have "known_ptrs h2"
    using known_ptrs_new_ptr object_ptr_kinds_eq_h \<open>known_ptrs h\<close> h2
    by blast
  then
  have "known_ptrs h3"
    using known_ptrs_preserved object_ptr_kinds_eq_h2 by blast
  then
  have "known_ptrs h'"
    using known_ptrs_preserved object_ptr_kinds_eq_h3 by blast




  have "document_ptr |\<in>| document_ptr_kinds h'"
    by (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close> document_ptr_kinds_eq_h
        document_ptr_kinds_eq_h2 document_ptr_kinds_eq_h3)

  have "known_ptr (cast document_ptr)"
    using \<open>document_ptr |\<in>| document_ptr_kinds h\<close> assms(3) document_ptr_kinds_commutes
      local.known_ptrs_known_ptr by blast
  have "h \<turnstile> get_owner_document (cast document_ptr) \<rightarrow>\<^sub>r document_ptr"
    using \<open>known_ptr (cast document_ptr)\<close> \<open>document_ptr |\<in>| document_ptr_kinds h\<close>
    apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def)[1]
    apply(split invoke_splits, rule conjI)+
    by(auto simp add: known_ptr_impl known_ptr_defs CharacterDataClass.known_ptr_defs
        ElementClass.known_ptr_defs NodeClass.known_ptr_defs a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        intro!: bind_pure_returns_result_I split: option.splits)
  have "h' \<turnstile> get_owner_document (cast document_ptr) \<rightarrow>\<^sub>r document_ptr"
    using \<open>known_ptr (cast document_ptr)\<close> \<open>document_ptr |\<in>| document_ptr_kinds h'\<close>
    apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def)[1]
    apply(split invoke_splits, rule conjI)+
    by(auto simp add: known_ptr_impl known_ptr_defs CharacterDataClass.known_ptr_defs
        ElementClass.known_ptr_defs NodeClass.known_ptr_defs a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        intro!: bind_pure_returns_result_I split: option.splits)

  obtain to where to: "h \<turnstile> to_tree_order (cast document_ptr) \<rightarrow>\<^sub>r to"
    by (meson \<open>h \<turnstile> get_owner_document (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr) \<rightarrow>\<^sub>r document_ptr\<close>
        assms(1) assms(2) assms(3) is_OK_returns_result_E is_OK_returns_result_I
        local.get_owner_document_ptr_in_heap local.to_tree_order_ok)
  obtain to' where to': "h' \<turnstile> to_tree_order (cast document_ptr) \<rightarrow>\<^sub>r to'"
    by (metis \<open>document_ptr |\<in>| document_ptr_kinds h\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> assms(1) assms(2)
        assms(3) assms(5) document_ptr_kinds_commutes document_ptr_kinds_eq_h document_ptr_kinds_eq_h2
        document_ptr_kinds_eq_h3 is_OK_returns_result_E local.create_character_data_preserves_wellformedness(1)
        local.to_tree_order_ok)
  have "set to = set to'"
  proof safe
    fix x
    assume "x \<in> set to"
    show "x \<in> set to'"
      using to to'
      using to_tree_order_parent_child_rel \<open>parent_child_rel h = parent_child_rel h'\<close>
      by (metis \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> \<open>x \<in> set to\<close> assms(1) assms(2) assms(3) assms(5)
          local.create_character_data_preserves_wellformedness(1))
  next
    fix x
    assume "x \<in> set to'"
    show "x \<in> set to"
      using to to'
      using to_tree_order_parent_child_rel \<open>parent_child_rel h = parent_child_rel h'\<close>
      by (metis \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> \<open>x \<in> set to'\<close> assms(1) assms(2) assms(3) assms(5)
          local.create_character_data_preserves_wellformedness(1))
  qed

  have "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_character_data_ptr # disc_nodes_h3"
    using h' local.set_disconnected_nodes_get_disconnected_nodes by auto
  obtain disc_nodes_h' where disc_nodes_h': "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h'"
    and "cast new_character_data_ptr \<in> set disc_nodes_h'"
    and "disc_nodes_h' =  cast new_character_data_ptr # disc_nodes_h3"
    by (simp add: \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_character_data_ptr # disc_nodes_h3\<close>)

  have "\<And>disc_ptr to to'. disc_ptr \<in> set disc_nodes_h3 \<Longrightarrow> h \<turnstile> to_tree_order (cast disc_ptr) \<rightarrow>\<^sub>r to \<Longrightarrow>
h' \<turnstile> to_tree_order (cast disc_ptr) \<rightarrow>\<^sub>r to' \<Longrightarrow> set to = set to'"
  proof safe
    fix disc_ptr to to' x
    assume "disc_ptr \<in> set disc_nodes_h3"
    assume "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to"
    assume "h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'"
    assume "x \<in> set to"
    show "x \<in> set to'"
      using to_tree_order_parent_child_rel \<open>parent_child_rel h = parent_child_rel h'\<close>
      by (metis \<open>h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to\<close>
          \<open>h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> \<open>x \<in> set to\<close>
          assms(1) assms(2) assms(3) assms(5) local.create_character_data_preserves_wellformedness(1))
  next
    fix disc_ptr to to' x
    assume "disc_ptr \<in> set disc_nodes_h3"
    assume "h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to"
    assume "h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'"
    assume "x \<in> set to'"
    show "x \<in> set to"
      using to_tree_order_parent_child_rel \<open>parent_child_rel h = parent_child_rel h'\<close>
      by (metis \<open>h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to\<close>
          \<open>h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> \<open>x \<in> set to'\<close>
          assms(1) assms(2) assms(3) assms(5) local.create_character_data_preserves_wellformedness(1))
  qed

  have "heap_is_wellformed h'"
    using assms(1) assms(2) assms(3) assms(5) local.create_character_data_preserves_wellformedness(1)
    by blast

  have "cast new_character_data_ptr |\<in>| object_ptr_kinds h'"
    using \<open>cast new_character_data_ptr \<in> set disc_nodes_h'\<close> \<open>heap_is_wellformed h'\<close> disc_nodes_h'
      local.heap_is_wellformed_disc_nodes_in_heap node_ptr_kinds_commutes by blast
  then
  have "new_character_data_ptr |\<in>| character_data_ptr_kinds h'"
    by simp

  have "\<And>node_ptr. node_ptr \<in> set disc_nodes_h3 \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h'"
    by (meson \<open>heap_is_wellformed h'\<close> h' local.heap_is_wellformed_disc_nodes_in_heap
        local.set_disconnected_nodes_get_disconnected_nodes set_subset_Cons subset_code(1))

  have "h \<turnstile> ok (map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) disc_nodes_h3)"
    using assms(1) assms(2) assms(3) to_tree_order_ok
    apply(auto intro!: map_M_ok_I)[1]
    using disc_nodes_document_ptr_h local.heap_is_wellformed_disc_nodes_in_heap node_ptr_kinds_commutes
    by blast
  then
  obtain disc_tree_orders where disc_tree_orders:
    "h \<turnstile> map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) disc_nodes_h3 \<rightarrow>\<^sub>r disc_tree_orders"
    by auto

  have "h' \<turnstile> ok (map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) disc_nodes_h')"
    apply(auto intro!: map_M_ok_I)[1]
    apply(simp add: \<open>disc_nodes_h' =  cast new_character_data_ptr # disc_nodes_h3\<close>)
    using \<open>\<And>node_ptr. node_ptr \<in> set disc_nodes_h3 \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h'\<close>
      \<open>cast new_character_data_ptr \<in> set disc_nodes_h'\<close> \<open>heap_is_wellformed h'\<close> \<open>known_ptrs h'\<close>
      \<open>type_wf h'\<close> disc_nodes_h' local.heap_is_wellformed_disc_nodes_in_heap local.to_tree_order_ok
      node_ptr_kinds_commutes by blast
  then
  obtain disc_tree_orders' where disc_tree_orders':
    "h' \<turnstile> map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) disc_nodes_h' \<rightarrow>\<^sub>r disc_tree_orders'"
    by auto

  have "h' \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []"
    using \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close> children_eq_h2 children_eq_h3 by auto

  obtain new_tree_order where new_tree_order:
    "h' \<turnstile> to_tree_order (cast new_character_data_ptr) \<rightarrow>\<^sub>r new_tree_order" and
    "new_tree_order \<in> set disc_tree_orders'"
    using map_M_pure_E[OF disc_tree_orders' \<open>cast new_character_data_ptr \<in> set disc_nodes_h'\<close>]
    by auto
  then have "new_tree_order = [cast new_character_data_ptr]"
    using \<open>h' \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
    by(auto simp add: to_tree_order_def
        dest!: bind_returns_result_E3[rotated, OF \<open>h' \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>, rotated])

  obtain foo where foo: "h' \<turnstile> map_M (to_tree_order \<circ> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r)
(cast new_character_data_ptr # disc_nodes_h3) \<rightarrow>\<^sub>r [cast new_character_data_ptr] # foo"
    apply(auto intro!: bind_pure_returns_result_I map_M_pure_I)[1]
    using \<open>new_tree_order = [cast new_character_data_ptr]\<close> new_tree_order apply auto[1]
    using \<open>disc_nodes_h' = cast new_character_data_ptr # disc_nodes_h3\<close> bind_pure_returns_result_I
      bind_returns_result_E2 comp_apply disc_tree_orders' local.to_tree_order_pure map_M.simps(2)
      map_M_pure_I return_returns_result returns_result_eq
    apply simp
    by (smt \<open>disc_nodes_h' = cast new_character_data_ptr # disc_nodes_h3\<close> bind_pure_returns_result_I
        bind_returns_result_E2 comp_apply disc_tree_orders' local.to_tree_order_pure map_M.simps(2) map_M_pure_I
        return_returns_result returns_result_eq)
  then have "set (concat foo) = set (concat disc_tree_orders)"
    apply(auto elim!: bind_returns_result_E2 intro!: map_M_pure_I)[1]
     apply (smt \<open>\<And>to' toa disc_ptr. \<lbrakk>disc_ptr \<in> set disc_nodes_h3;
h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r toa; h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'\<rbrakk> \<Longrightarrow>
set toa = set to'\<close> comp_apply disc_tree_orders local.to_tree_order_pure map_M_pure_E map_M_pure_E2)
    using \<open>\<And>to' toa disc_ptr. \<lbrakk>disc_ptr \<in> set disc_nodes_h3; h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r toa;
h' \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_ptr) \<rightarrow>\<^sub>r to'\<rbrakk> \<Longrightarrow> set toa = set to'\<close> comp_apply disc_tree_orders
      local.to_tree_order_pure map_M_pure_E map_M_pure_E2
    by smt

  have "disc_tree_orders' = [cast new_character_data_ptr] # foo"
    using foo disc_tree_orders'
    by (simp add: \<open>disc_nodes_h' = cast new_character_data_ptr # disc_nodes_h3\<close> returns_result_eq)

  have "set (concat disc_tree_orders') = {cast new_character_data_ptr} \<union> set (concat disc_tree_orders)"
    apply(auto simp add: \<open>disc_tree_orders' = [cast new_character_data_ptr] # foo\<close>)[1]
    using \<open>set (concat foo) = set (concat disc_tree_orders)\<close> by auto

  have "h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr) \<rightarrow>\<^sub>r to' @ concat disc_tree_orders'"
    using \<open>h' \<turnstile> get_owner_document (cast document_ptr) \<rightarrow>\<^sub>r document_ptr\<close> disc_nodes_h' to' disc_tree_orders'
    by(auto simp add: a_get_scdom_component_def intro!: bind_pure_returns_result_I map_M_pure_I)
  then
  have "set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r = set to' \<union> set (concat disc_tree_orders')"
    by auto
  have "h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr) \<rightarrow>\<^sub>r to @ concat disc_tree_orders"
    using \<open>h \<turnstile> get_owner_document (cast document_ptr) \<rightarrow>\<^sub>r document_ptr\<close> disc_nodes_document_ptr_h to disc_tree_orders
    by(auto simp add: a_get_scdom_component_def intro!: bind_pure_returns_result_I map_M_pure_I)
  then
  have "set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r = set to \<union> set (concat disc_tree_orders)"
    by auto

  have "{cast new_character_data_ptr} \<union> set |h \<turnstile> local.a_get_scdom_component (cast document_ptr)|\<^sub>r =
set |h' \<turnstile> local.a_get_scdom_component (cast document_ptr)|\<^sub>r"
  proof(safe)
    show "cast new_character_data_ptr
         \<in> set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
      using \<open>h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr) \<rightarrow>\<^sub>r to' @ concat disc_tree_orders'\<close>
      apply(auto simp add: a_get_scdom_component_def)[1]
      by (meson \<open>\<And>thesis. (\<And>new_tree_order. \<lbrakk>h' \<turnstile> to_tree_order (cast new_character_data_ptr) \<rightarrow>\<^sub>r new_tree_order;
new_tree_order \<in> set disc_tree_orders'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> local.to_tree_order_ptr_in_result)
  next
    fix x
    assume " x \<in> set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
    then
    show "x \<in> set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
      using \<open>set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to \<union> set (concat disc_tree_orders)\<close>
      using \<open>set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to' \<union> set (concat disc_tree_orders')\<close>
      using \<open>set to = set to'\<close>
      using \<open>set (concat disc_tree_orders') = {cast new_character_data_ptr} \<union> set (concat disc_tree_orders)\<close>
      by(auto)
  next
    fix x
    assume " x \<in> set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
    assume "x \<notin> set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r"
    show "x = cast new_character_data_ptr"
      using \<open>set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to \<union> set (concat disc_tree_orders)\<close>
      using \<open>set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to' \<union> set (concat disc_tree_orders')\<close>
      using \<open>set to = set to'\<close>
      using \<open>set (concat disc_tree_orders') = {cast new_character_data_ptr} \<union> set (concat disc_tree_orders)\<close>
      using \<open>x \<in> set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r\<close>
        \<open>x \<notin> set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r\<close>
      by auto
  qed


  have "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    using object_ptr_kinds_eq_h object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 by auto
  then
  show ?thesis
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def)[1]
       apply(rule bexI[where x="cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr"])
    using \<open>{cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr} \<union> set |h \<turnstile> local.a_get_scdom_component
(cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r = set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r\<close>
        apply auto[2]
    using \<open>set to = set to'\<close> \<open>set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to \<union> set (concat disc_tree_orders)\<close> local.to_tree_order_ptr_in_result to'
        apply auto[1]
    using \<open>document_ptr |\<in>| document_ptr_kinds h\<close>
       apply blast
      apply(rule bexI[where x="cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr"])
    using \<open>result = new_character_data_ptr\<close> \<open>{cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr} \<union>
set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set |h' \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r\<close>
       apply auto[1]
      apply(auto)[1]
    using \<open>set to = set to'\<close> \<open>set |h \<turnstile> local.a_get_scdom_component (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr)|\<^sub>r =
set to \<union> set (concat disc_tree_orders)\<close> local.to_tree_order_ptr_in_result to' apply auto[1]
      apply (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close>)
    using \<open>\<And>thesis. (\<And>new_character_data_ptr h2 h3 disc_nodes_h3. \<lbrakk>h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr;
h \<turnstile> new_character_data \<rightarrow>\<^sub>h h2; h2 \<turnstile> set_val new_character_data_ptr text \<rightarrow>\<^sub>h h3;
h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3;
h3 \<turnstile> set_disconnected_nodes document_ptr (cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
      new_character_data_ptr new_character_data_ptr_not_in_heap
     apply auto[1]
    using create_character_data_is_strongly_dom_component_safe_step
    by (smt ObjectMonad.ptr_kinds_ptr_kinds_M \<open>cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>
        \<open>result = new_character_data_ptr\<close> assms(1) assms(2) assms(3) assms(4) assms(5) local.get_scdom_component_impl select_result_I2)
qed
end

interpretation i_get_scdom_component_create_character_data?: l_get_scdom_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs get_scdom_component
  is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe to_tree_order get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_root_node get_root_node_locs get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name set_val set_val_locs get_disconnected_nodes get_disconnected_nodes_locs
  set_disconnected_nodes set_disconnected_nodes_locs create_character_data
  by(auto simp add: l_get_scdom_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>create\_document\<close>

lemma create_document_not_strongly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and new_document_ptr where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> create_document \<rightarrow>\<^sub>r new_document_ptr \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_scdom_component_safe {} {cast new_document_ptr} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap"
  let ?P = "create_document"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?document_ptr = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1"])
    by code_simp+
qed

locale l_get_scdom_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_dom_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma create_document_is_weakly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_document \<rightarrow>\<^sub>r result"
  assumes "h \<turnstile> create_document \<rightarrow>\<^sub>h h'"
  shows "is_weakly_scdom_component_safe {} {cast result} h h'"
proof -
  have "object_ptr_kinds h' = {|cast result|} |\<union>| object_ptr_kinds h"
    using assms(4) assms(5) local.create_document_def new_document_new_ptr by blast
  have "result |\<notin>| document_ptr_kinds h"
    using assms(4) assms(5) local.create_document_def new_document_ptr_not_in_heap by auto
  show ?thesis
    using assms
    apply(auto simp add: is_weakly_scdom_component_safe_def Let_def)[1]
    using \<open>object_ptr_kinds h' = {|cast result|} |\<union>| object_ptr_kinds h\<close> apply(auto)[1]
      apply (simp add: local.create_document_def new_document_ptr_in_heap)
    using \<open>result |\<notin>| document_ptr_kinds h\<close> apply auto[1]

    apply (metis (no_types, lifting) \<open>result |\<notin>| document_ptr_kinds h\<close> document_ptr_kinds_commutes
        local.create_document_is_weakly_dom_component_safe_step select_result_I2)
    done
qed
end

interpretation i_get_scdom_component_create_document?: l_get_scdom_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe to_tree_order get_parent get_parent_locs
  get_child_nodes get_child_nodes_locs get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_element_by_id get_elements_by_class_name get_elements_by_tag_name create_document
  get_disconnected_nodes get_disconnected_nodes_locs
  by(auto simp add: l_get_scdom_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>insert\_before\<close>

locale l_get_dom_component_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_owner_document_wf +
  l_get_dom_component_get_scdom_component +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_child_nodes_get_disconnected_nodes +
  l_remove_child +
  l_get_root_node_wf +
  l_set_disconnected_nodes_get_disconnected_nodes_wf +
  l_set_disconnected_nodes_get_ancestors +
  l_get_ancestors_wf +
  l_get_owner_document +
  l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma insert_before_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> insert_before ptr' child ref \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component ptr'|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast child)|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document ptr'|\<^sub>r)|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document (cast child)|\<^sub>r)|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
proof -
  obtain owner_document where owner_document: "h \<turnstile> get_owner_document (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r owner_document"
    using assms(4)
    by(auto simp add: local.adopt_node_def insert_before_def elim!:  bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF ensure_pre_insertion_validity_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated] bind_returns_heap_E2[rotated, OF next_sibling_pure, rotated] split: if_splits)
  then
  obtain c where "h \<turnstile> get_dom_component (cast owner_document) \<rightarrow>\<^sub>r c"
    using get_dom_component_ok assms(1) assms(2) assms(3) get_owner_document_owner_document_in_heap
    by (meson document_ptr_kinds_commutes select_result_I)
  then
  have "ptr \<noteq> cast owner_document"
    using assms(6) assms(1) assms(2) assms(3) local.get_dom_component_ptr owner_document
    by (metis (no_types, lifting) assms(8) select_result_I2)

  obtain owner_document' where owner_document': "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r owner_document'"
    using assms(4)
    by(auto simp add: local.adopt_node_def insert_before_def elim!:  bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF ensure_pre_insertion_validity_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated]
        bind_returns_heap_E2[rotated, OF next_sibling_pure, rotated] split: if_splits)
  then
  obtain c where "h \<turnstile> get_dom_component (cast owner_document') \<rightarrow>\<^sub>r c"
    using get_dom_component_ok assms(1) assms(2) assms(3) get_owner_document_owner_document_in_heap
    by (meson document_ptr_kinds_commutes select_result_I)
  then
  have "ptr \<noteq> cast owner_document'"
    using assms(1) assms(2) assms(3) assms(7) local.get_dom_component_ptr owner_document' by auto
  then
  have "ptr \<noteq> cast |h \<turnstile> get_owner_document ptr'|\<^sub>r"
    using owner_document' by auto

  have "ptr \<noteq> ptr'"
    by (metis (mono_tags, hide_lams) assms(1) assms(2) assms(3) assms(5) assms(7) is_OK_returns_result_I
        l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_dom_component_ok l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_dom_component_ptr
        l_get_owner_document.get_owner_document_ptr_in_heap local.l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms
        local.l_get_owner_document_axioms owner_document' return_returns_result returns_result_select_result)
  have "\<And>parent. h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent \<Longrightarrow> parent \<noteq> ptr"
    by (meson assms(1) assms(2) assms(3) assms(6) l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_dom_component_ptr
        local.get_dom_component_ok local.get_dom_component_to_tree_order local.get_parent_parent_in_heap
        local.l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms local.to_tree_order_ok local.to_tree_order_parent
        local.to_tree_order_ptr_in_result local.to_tree_order_ptrs_in_heap returns_result_select_result)
  then
  have "\<And>parent. |h \<turnstile> get_parent child|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr"
    by (metis assms(2) assms(3) assms(4) is_OK_returns_heap_I local.get_parent_ok
        local.insert_before_child_in_heap select_result_I)

  show ?thesis
    using insert_before_writes assms(4)
    apply(rule reads_writes_preserved2)
    apply(auto simp add: insert_before_locs_def adopt_node_locs_def all_args_def)[1]
            apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: if_splits)[1]
            apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r |h \<turnstile> get_owner_document ptr'|\<^sub>r\<close>
        get_M_Mdocument_preserved3)
           apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: if_splits)[1]
           apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
          apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: if_splits)[1]
           apply (metis \<open>ptr \<noteq> ptr'\<close> document_ptr_casts_commute3 get_M_Mdocument_preserved3)
          apply(auto split: option.splits)[1] 
          apply (metis \<open>ptr \<noteq> ptr'\<close> element_ptr_casts_commute3 get_M_Element_preserved8)
         apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def set_disconnected_nodes_locs_def
        all_args_def split: if_splits)[1]
         apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r |h \<turnstile> get_owner_document ptr'|\<^sub>r\<close> get_M_Mdocument_preserved3)
        apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: if_splits)[1]
            apply (metis (no_types, lifting) \<open>\<And>parent. |h \<turnstile> get_parent child|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr\<close>
        element_ptr_casts_commute3 get_M_Element_preserved8 node_ptr_casts_commute option.case_eq_if option.collapse)
           apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
          apply (metis \<open>\<And>parent. |h \<turnstile> get_parent child|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr\<close>
        document_ptr_casts_commute3 get_M_Mdocument_preserved3)
         apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
        apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
       apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: if_splits)[1]
       apply (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r |h \<turnstile> get_owner_document ptr'|\<^sub>r\<close>
        get_M_Mdocument_preserved3)
      apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: if_splits)[1]
      apply (metis (no_types, lifting) \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close>
        get_M_Mdocument_preserved3 owner_document select_result_I2)
     apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: if_splits)[1]
      apply (metis \<open>ptr \<noteq> ptr'\<close> document_ptr_casts_commute3 get_M_Mdocument_preserved3)
     apply (metis (no_types, lifting) \<open>ptr \<noteq> ptr'\<close> element_ptr_casts_commute3
        get_M_Element_preserved8 node_ptr_casts_commute option.case_eq_if option.collapse)
    apply(auto simp add: remove_child_locs_def set_child_nodes_locs_def
        set_disconnected_nodes_locs_def all_args_def split: if_splits)[1]
    by (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r |h \<turnstile> get_owner_document ptr'|\<^sub>r\<close> get_M_Mdocument_preserved3)
qed

lemma insert_before_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> insert_before ptr' child ref \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component ptr'|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component (cast child)|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
proof -
  have "ptr' |\<in>| object_ptr_kinds h"
    by (meson assms(4) is_OK_returns_heap_I local.insert_before_ptr_in_heap)
  then
  obtain sc' where sc': "h \<turnstile> get_scdom_component ptr' \<rightarrow>\<^sub>r sc'"
    by (meson assms(1) assms(2) assms(3) get_scdom_component_ok is_OK_returns_result_E)
  moreover
  obtain c' where c': "h \<turnstile> get_dom_component ptr' \<rightarrow>\<^sub>r c'"
    by (meson \<open>ptr' |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) is_OK_returns_result_E
        local.get_dom_component_ok)
  ultimately have "set c' \<subseteq> set sc'"
    using assms(1) assms(2) assms(3) get_scdom_component_subset_get_dom_component by blast

  have "child |\<in>| node_ptr_kinds h"
    by (meson assms(4) is_OK_returns_heap_I local.insert_before_child_in_heap)
  then
  obtain child_sc where child_sc: "h \<turnstile> get_scdom_component (cast child) \<rightarrow>\<^sub>r child_sc"
    by (meson assms(1) assms(2) assms(3) get_scdom_component_ok is_OK_returns_result_E
        node_ptr_kinds_commutes)
  moreover
  obtain child_c where child_c: "h \<turnstile> get_dom_component (cast child) \<rightarrow>\<^sub>r child_c"
    by (meson \<open>child |\<in>| node_ptr_kinds h\<close> assms(1) assms(2) assms(3) is_OK_returns_result_E
        local.get_dom_component_ok node_ptr_kinds_commutes)
  ultimately have "set child_c \<subseteq> set child_sc"
    using assms(1) assms(2) assms(3) get_scdom_component_subset_get_dom_component by blast

  obtain ptr'_owner_document where ptr'_owner_document: "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r ptr'_owner_document"
    by (meson \<open>set c' \<subseteq> set sc'\<close> assms(1) assms(2) assms(3) c' get_scdom_component_owner_document_same
        local.get_dom_component_ptr sc' subset_code(1))
  then
  have "h \<turnstile> get_scdom_component (cast ptr'_owner_document) \<rightarrow>\<^sub>r sc'"
    by (metis (no_types, lifting) \<open>set c' \<subseteq> set sc'\<close> assms(1) assms(2) assms(3) c'
        get_scdom_component_owner_document_same get_scdom_component_ptrs_same_scope_component
        local.get_dom_component_ptr sc' select_result_I2 subset_code(1))
  moreover
  obtain ptr'_owner_document_c where ptr'_owner_document_c:
    "h \<turnstile> get_dom_component (cast ptr'_owner_document) \<rightarrow>\<^sub>r ptr'_owner_document_c"
    by (meson assms(1) assms(2) assms(3) document_ptr_kinds_commutes is_OK_returns_result_E
        local.get_dom_component_ok local.get_owner_document_owner_document_in_heap ptr'_owner_document)
  ultimately have "set ptr'_owner_document_c \<subseteq> set sc'"
    using assms(1) assms(2) assms(3) get_scdom_component_subset_get_dom_component by blast

  obtain child_owner_document where child_owner_document: "h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r child_owner_document"
    by (meson \<open>set child_c \<subseteq> set child_sc\<close> assms(1) assms(2) assms(3) child_c child_sc
        get_scdom_component_owner_document_same local.get_dom_component_ptr subset_code(1))

  have "child_owner_document |\<in>| document_ptr_kinds h"
    using assms(1) assms(2) assms(3) child_owner_document local.get_owner_document_owner_document_in_heap
    by blast
  then
  have "h \<turnstile> get_scdom_component (cast child_owner_document) \<rightarrow>\<^sub>r child_sc"
    using get_scdom_component_ok assms(1) assms(2) assms(3) child_sc
    by (metis (no_types, lifting) \<open>set child_c \<subseteq> set child_sc\<close> child_c child_owner_document
        get_scdom_component_owner_document_same get_scdom_component_ptrs_same_scope_component
        local.get_dom_component_ptr returns_result_eq set_mp)
  moreover
  obtain child_owner_document_c where child_owner_document_c:
    "h \<turnstile> get_dom_component (cast child_owner_document) \<rightarrow>\<^sub>r child_owner_document_c"
    by (meson assms(1) assms(2) assms(3) child_owner_document document_ptr_kinds_commutes
        is_OK_returns_result_E local.get_dom_component_ok local.get_owner_document_owner_document_in_heap)
  ultimately have "set child_owner_document_c \<subseteq> set child_sc"
    using assms(1) assms(2) assms(3) get_scdom_component_subset_get_dom_component by blast


  have "ptr \<notin> set |h \<turnstile> get_dom_component ptr'|\<^sub>r"
    using \<open>set c' \<subseteq> set sc'\<close> assms(5) c' sc' by auto
  moreover have "ptr \<notin> set |h \<turnstile> get_dom_component (cast child)|\<^sub>r"
    using \<open>set child_c \<subseteq> set child_sc\<close> assms(6) child_c child_sc by auto
  moreover have "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document ptr'|\<^sub>r)|\<^sub>r"
    using \<open>set ptr'_owner_document_c \<subseteq> set sc'\<close> assms(5) ptr'_owner_document ptr'_owner_document_c sc'
    by auto
  moreover have "ptr \<notin> set |h \<turnstile> get_dom_component (cast |h \<turnstile> get_owner_document (cast child)|\<^sub>r)|\<^sub>r"
    using \<open>set child_owner_document_c \<subseteq> set child_sc\<close> assms(6) child_owner_document child_owner_document_c
      child_sc by auto

  ultimately show ?thesis
    using assms insert_before_is_component_unsafe
    by blast
qed

lemma insert_before_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> insert_before ptr node child \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe ({ptr, cast node} \<union> (case child of Some ref \<Rightarrow> {cast ref} | None \<Rightarrow> {} )) {} h h'"
proof -
  obtain ancestors reference_child owner_document h2 h3 disconnected_nodes_h2 where
    ancestors: "h \<turnstile> get_ancestors ptr \<rightarrow>\<^sub>r ancestors" and
    node_not_in_ancestors: "cast node \<notin> set ancestors" and
    reference_child:
    "h \<turnstile> (if Some node = child then a_next_sibling node else return child) \<rightarrow>\<^sub>r reference_child" and
    owner_document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document" and
    h2: "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h2" and
    disconnected_nodes_h2: "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h2" and
    h3: "h2 \<turnstile> set_disconnected_nodes owner_document (remove1 node disconnected_nodes_h2) \<rightarrow>\<^sub>h h3" and
    h': "h3 \<turnstile> a_insert_node ptr node reference_child \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: insert_before_def a_ensure_pre_insertion_validity_def
        elim!: bind_returns_heap_E bind_returns_result_E
        bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_ancestors_pure, rotated]
        bind_returns_heap_E2[rotated, OF next_sibling_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated]
        split: if_splits option.splits)

  have object_ptr_kinds_M_eq3_h: "object_ptr_kinds h = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF adopt_node_writes h2])
    using adopt_node_pointers_preserved
      apply blast
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h: "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs )
  then have object_ptr_kinds_M_eq2_h: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq2_h: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast

  have "known_ptrs h2"
    using assms(3) object_ptr_kinds_M_eq3_h known_ptrs_preserved by blast

  have wellformed_h2: "heap_is_wellformed h2"
    using adopt_node_preserves_wellformedness[OF assms(1) h2] assms(3) assms(2) .

  have object_ptr_kinds_M_eq3_h2: "object_ptr_kinds h2 = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF set_disconnected_nodes_writes h3])
    unfolding a_remove_child_locs_def
    using set_disconnected_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h2: "\<And>ptrs. h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs)
  then have object_ptr_kinds_M_eq2_h2: "|h2 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq2_h2: "|h2 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast
  have document_ptr_kinds_eq2_h2: "|h2 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h3 \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_M_eq2_h2 document_ptr_kinds_M_eq by auto

  have "known_ptrs h3"
    using object_ptr_kinds_M_eq3_h2 known_ptrs_preserved \<open>known_ptrs h2\<close> by blast

  have object_ptr_kinds_M_eq3_h': "object_ptr_kinds h3 = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF insert_node_writes h'])
    unfolding a_remove_child_locs_def
    using set_child_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h3:
    "\<And>ptrs. h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs)
  then have object_ptr_kinds_M_eq2_h3:
    "|h3 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq2_h3: "|h3 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast
  have document_ptr_kinds_eq2_h3: "|h3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_M_eq2_h3 document_ptr_kinds_M_eq by auto


  have "object_ptr_kinds h = object_ptr_kinds h'"
    by (simp add: object_ptr_kinds_M_eq3_h object_ptr_kinds_M_eq3_h' object_ptr_kinds_M_eq3_h2)
  then
  show ?thesis
    using assms
    apply(auto simp add: is_strongly_scdom_component_safe_def)[1]
    using insert_before_is_strongly_dom_component_safe_step local.get_scdom_component_impl by blast
qed

lemma append_child_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> append_child ptr' child \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component ptr'|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component (cast child)|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6)
      insert_before_is_strongly_dom_component_safe_step local.append_child_def)

lemma append_child_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> append_child ptr child \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {ptr, cast child} {} h h'"
  using assms unfolding append_child_def
  using insert_before_is_strongly_dom_component_safe
  by fastforce
end

interpretation i_get_dom_component_insert_before?: l_get_dom_component_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_dom_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name set_child_nodes set_child_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs
  get_owner_document remove_child remove_child_locs remove adopt_node adopt_node_locs insert_before
  insert_before_locs append_child get_scdom_component is_strongly_scdom_component_safe
  is_weakly_scdom_component_safe
  by(auto simp add: l_get_dom_component_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_dom_component_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_owner\_document\<close>

locale l_get_owner_document_scope_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_owner_document_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_scdom_component +
  l_get_owner_document_wf_get_root_node_wf
begin
lemma get_owner_document_is_strongly_scdom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_owner_document ptr' \<rightarrow>\<^sub>r owner_document"
  shows "cast owner_document \<in> set sc \<longleftrightarrow> ptr' \<in> set sc"
proof -
  have "h \<turnstile> get_owner_document (cast owner_document) \<rightarrow>\<^sub>r owner_document"
    by (metis assms(1) assms(2) assms(3) assms(5) cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject
        document_ptr_casts_commute3 document_ptr_document_ptr_cast document_ptr_kinds_commutes
        local.get_owner_document_owner_document_in_heap local.get_root_node_document
        local.get_root_node_not_node_same node_ptr_no_document_ptr_cast)
  then show ?thesis
    using assms
    using bind_returns_result_E contra_subsetD get_scdom_component_ok
      get_scdom_component_ptrs_same_scope_component get_scdom_component_subset_get_dom_component
      is_OK_returns_result_E is_OK_returns_result_I local.get_dom_component_ok local.get_dom_component_ptr
      local.get_owner_document_ptr_in_heap local.get_owner_document_pure local.get_scdom_component_def
      pure_returns_heap_eq returns_result_eq
    by (smt local.get_scdom_component_ptrs_same_owner_document subsetD)
qed


lemma get_owner_document_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
  assumes "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>h h'"
  shows "is_strongly_scdom_component_safe {ptr} {cast owner_document} h h'"
proof -
  have "h = h'"
    by (meson assms(5) local.get_owner_document_pure pure_returns_heap_eq)
  then show ?thesis
    using assms
    apply(auto simp add: is_strongly_scdom_component_safe_def Let_def preserved_def)[1]
    by (smt get_owner_document_is_strongly_scdom_component_safe_step inf.orderE is_OK_returns_result_I
        local.get_dom_component_ok local.get_dom_component_to_tree_order_subset local.get_owner_document_ptr_in_heap
        local.get_scdom_component_impl local.get_scdom_component_ok local.get_scdom_component_ptr_in_heap
        local.get_scdom_component_subset_get_dom_component local.to_tree_order_ok
        local.to_tree_order_ptr_in_result notin_fset returns_result_select_result subset_eq)
qed
end

interpretation i_get_owner_document_scope_component?: l_get_owner_document_scope_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe
  get_owner_document get_disconnected_nodes get_disconnected_nodes_locs to_tree_order known_ptr
  known_ptrs type_wf heap_is_wellformed parent_child_rel get_child_nodes get_child_nodes_locs
  get_parent get_parent_locs get_ancestors get_ancestors_locs get_root_node get_root_node_locs
  get_dom_component is_strongly_dom_component_safe is_weakly_dom_component_safe get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name
  by(auto simp add: l_get_owner_document_scope_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_owner_document_scope_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

end
