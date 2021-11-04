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

section \<open>Shadow SC DOM Components II\<close>
theory Shadow_DOM_SC_DOM_Components
  imports
    Core_DOM_SC_DOM_Components
    Shadow_DOM_DOM_Components
begin

section \<open>Shadow root scope components\<close>


subsection \<open>get\_scope\_component\<close>

global_interpretation l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_owner_document get_disconnected_nodes
  get_disconnected_nodes_locs to_tree_order
  defines get_scdom_component = a_get_scdom_component
    and is_strongly_scdom_component_safe = a_is_strongly_scdom_component_safe
    and is_weakly_scdom_component_safe = a_is_weakly_scdom_component_safe
  .
interpretation i_get_scdom_component?: l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe
  get_owner_document get_disconnected_nodes get_disconnected_nodes_locs to_tree_order
  by(auto simp add: l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def get_scdom_component_def
      is_strongly_scdom_component_safe_def is_weakly_scdom_component_safe_def instances)
declare l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_component\<close>

locale l_get_dom_component_get_scdom_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
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
  assumes known_ptr_impl: "known_ptr = ShadowRootClass.known_ptr"
begin

lemma known_ptr_node_or_document: "known_ptr ptr \<Longrightarrow> is_node_ptr_kind ptr \<or> is_document_ptr_kind ptr"
  by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs CharacterDataClass.known_ptr_defs
      ElementClass.known_ptr_defs NodeClass.known_ptr_defs split: option.splits)

lemma get_scdom_component_subset_get_dom_component:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_dom_component ptr \<rightarrow>\<^sub>r c"
  shows "set c \<subseteq> set sc"
proof -
  obtain document disc_nodes tree_order disconnected_tree_orders where document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r document"
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
  obtain document disc_nodes tree_order disconnected_tree_orders where document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r document"
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
          local.get_root_node_not_node_same local.to_tree_order_same_root node_ptr_no_document_ptr_cast
          tree_order)
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
        assms(2) assms(3) disconnected_tree_order local.get_root_node_no_parent local.to_tree_order_get_root_node
        local.to_tree_order_ptr_in_result
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
  obtain document disc_nodes tree_order disconnected_tree_orders where document:
    "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r document"
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
      by (metis assms(1) assms(2) assms(3) cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject document document_ptr_casts_commute3
          document_ptr_kinds_commutes known_ptr_node_or_document local.get_owner_document_owner_document_in_heap
          local.get_root_node_document local.get_root_node_not_node_same local.known_ptrs_known_ptr
          local.to_tree_order_get_root_node local.to_tree_order_ptr_in_result node_ptr_no_document_ptr_cast tree_order)
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
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) fmember.rep_eq local.get_parent_child_dual
          local.get_parent_ok local.get_parent_parent_in_heap local.heap_is_wellformed_disc_nodes_in_heap
          returns_result_select_result root_ptr' select_result_I2 split_option_ex)
    then have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r cast root_ptr'"
      using \<open>h \<turnstile> to_tree_order (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_ptr') \<rightarrow>\<^sub>r disconnected_tree_order\<close> assms(1)
        assms(2) assms(3) disconnected_tree_order local.get_root_node_no_parent local.to_tree_order_get_root_node
        local.to_tree_order_ptr_in_result
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
  using assms
  apply(auto simp add: get_scdom_component_def elim!: bind_returns_result_E2 intro!: map_M_pure_I)[1]
  using local.to_tree_order_ptrs_in_heap apply blast
  by (metis (no_types, lifting) assms(4) assms(5) bind_returns_result_E get_scdom_component_impl
      get_scdom_component_ptrs_same_scope_component is_OK_returns_result_I
      l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_scdom_component_def local.get_owner_document_ptr_in_heap)

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
      document_ptr_document_ptr_cast get_scdom_component_contains_get_dom_component local.get_dom_component_ptr
      local.get_dom_component_root_node_same local.get_dom_component_to_tree_order local.get_root_node_document
      local.get_root_node_not_node_same local.to_tree_order_ptr_in_result local.to_tree_order_ptrs_in_heap
      node_ptr_no_document_ptr_cast)
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
end

interpretation i_get_dom_component_get_scdom_component?: l_get_dom_component_get_scdom_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_owner_document
  get_disconnected_nodes get_disconnected_nodes_locs to_tree_order heap_is_wellformed parent_child_rel
  type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_dom_component is_strongly_dom_component_safe is_weakly_dom_component_safe get_root_node
  get_root_node_locs get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name
  by(auto simp add: l_get_dom_component_get_scdom_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_dom_component_get_scdom_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_get_dom_component_get_scdom_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_dom_component_get_scdom_component_is_l_get_dom_component_get_scdom_component [instances]:
  "l_get_dom_component_get_scdom_component get_owner_document heap_is_wellformed type_wf known_ptr known_ptrs get_scdom_component get_dom_component"
  apply(auto simp add: l_get_dom_component_get_scdom_component_def
      l_get_dom_component_get_scdom_component_axioms_def instances)[1]
  using get_scdom_component_subset_get_dom_component apply fast
  using get_scdom_component_ptrs_same_scope_component apply fast
  using get_scdom_component_ptrs_same_owner_document apply fast
  using get_scdom_component_ok apply fast
  using get_scdom_component_ptr_in_heap apply fast
  using get_scdom_component_contains_get_dom_component apply blast
  using get_scdom_component_owner_document_same apply blast
  using get_scdom_component_different_owner_documents apply fast
  done


subsection \<open>attach\_shadow\_root\<close>

lemma attach_shadow_root_not_strongly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'ShadowRoot::{equal,linorder}) heap" and
    h' and host and new_shadow_root_ptr where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> attach_shadow_root host m \<rightarrow>\<^sub>r new_shadow_root_ptr \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_scdom_component_safe {cast host} {cast new_shadow_root_ptr} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder},
'ShadowRoot::{equal,linorder}) heap"
  let ?P = "do {
    doc \<leftarrow> create_document;
    create_element doc ''div''
}"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e1 = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and host="?e1"])
    by code_simp+
qed

locale l_get_scdom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_dom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_scdom_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma attach_shadow_root_is_weakly_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>h h'"
  assumes "ptr \<noteq> cast |h \<turnstile> attach_shadow_root element_ptr shadow_root_mode|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_scdom_component (cast element_ptr)|\<^sub>r"
  shows "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
proof -
  have "element_ptr |\<in>| element_ptr_kinds h"
    by (meson assms(4) is_OK_returns_heap_I local.attach_shadow_root_element_ptr_in_heap)
  obtain sc where sc: "h \<turnstile> get_scdom_component (cast element_ptr) \<rightarrow>\<^sub>r sc"
    using get_scdom_component_ok
    by (meson assms(1) assms(2) assms(3) assms(4) element_ptr_kinds_commutes is_OK_returns_heap_I
        local.attach_shadow_root_element_ptr_in_heap node_ptr_kinds_commutes select_result_I)
  then have "ptr \<notin> set |h \<turnstile> get_dom_component (cast element_ptr)|\<^sub>r"
    by (metis (no_types, lifting) \<open>element_ptr |\<in>| element_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        assms(6) element_ptr_kinds_commutes local.get_dom_component_ok
        local.get_scdom_component_subset_get_dom_component node_ptr_kinds_commutes
        returns_result_select_result select_result_I2 set_rev_mp)
  then show ?thesis
    using assms(1) assms(2) assms(3) assms(4) assms(5) local.attach_shadow_root_is_weakly_dom_component_safe
    by blast
qed

lemma attach_shadow_root_is_weakly_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>r result"
  assumes "h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>h h'"
  shows "is_weakly_scdom_component_safe {cast element_ptr} {cast result} h h'"
proof -

  obtain h2 h3 new_shadow_root_ptr where
    h2: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h2" and
    new_shadow_root_ptr: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr" and
    h3: "h2 \<turnstile> set_mode new_shadow_root_ptr shadow_root_mode \<rightarrow>\<^sub>h h3" and
    h': "h3 \<turnstile> set_shadow_root element_ptr (Some new_shadow_root_ptr) \<rightarrow>\<^sub>h h'"
    using assms(5)
    by(auto simp add: attach_shadow_root_def elim!:  bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_tag_name_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_shadow_root_pure, rotated] split: if_splits)
  have "h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>r new_shadow_root_ptr"
    using new_shadow_root_ptr h2 h3 h'
    using assms(5)
    by(auto simp add: attach_shadow_root_def intro!: bind_returns_result_I
        bind_pure_returns_result_I[OF get_tag_name_pure] bind_pure_returns_result_I[OF get_shadow_root_pure]
        elim!:  bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_tag_name_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_shadow_root_pure, rotated] split: if_splits)
  then
  have "object_ptr_kinds h2 = {|cast result|} |\<union>| object_ptr_kinds h"
    using h2 new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_new_ptr
    using new_shadow_root_ptr
    using assms(4) by auto
  moreover
  have object_ptr_kinds_eq_h2: "object_ptr_kinds h2 = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF set_mode_writes h3])
    using set_mode_pointers_preserved
      apply blast
    by (auto simp add: reflp_def transp_def)
  moreover
  have object_ptr_kinds_eq_h3: "object_ptr_kinds h3 = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF set_shadow_root_writes h'])
    using set_shadow_root_pointers_preserved
      apply blast
    by (auto simp add: reflp_def transp_def)
  ultimately have "object_ptr_kinds h' = {|cast result|} |\<union>| object_ptr_kinds h"
    by simp
  moreover
  have "result |\<notin>| shadow_root_ptr_kinds h"
    using h2 new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_not_in_heap new_shadow_root_ptr
    using \<open>h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>r new_shadow_root_ptr\<close> assms(4)
      returns_result_eq by metis
  ultimately
  show ?thesis
    using assms
    apply(auto simp add: is_weakly_scdom_component_safe_def Let_def)[1]
    using attach_shadow_root_is_weakly_component_safe_step
    by (smt document_ptr_kinds_commutes local.get_scdom_component_impl select_result_I2
        shadow_root_ptr_kinds_commutes)
qed
end

interpretation i_get_scdom_component_attach_shadow_root?: l_get_scdom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe
  get_dom_component is_strongly_dom_component_safe is_weakly_dom_component_safe to_tree_order
  get_parent get_parent_locs get_child_nodes get_child_nodes_locs get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  set_shadow_root set_shadow_root_locs set_mode set_mode_locs attach_shadow_root get_disconnected_nodes
  get_disconnected_nodes_locs get_tag_name get_tag_name_locs get_shadow_root get_shadow_root_locs
  by(auto simp add: l_get_scdom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_shadow\_root\<close>

lemma get_shadow_root_not_weakly_scdom_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder}, 'CharacterData::{equal,linorder},
'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    element_ptr and shadow_root_ptr_opt and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> get_shadow_root_safe element_ptr \<rightarrow>\<^sub>r shadow_root_ptr_opt \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_scdom_component_safe {cast element_ptr} (cast ` set_option shadow_root_ptr_opt) h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder}, 'CharacterData::{equal,linorder},
'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap"
  let ?P = "do {
        document_ptr \<leftarrow> create_document;
        html \<leftarrow> create_element document_ptr ''html'';
        append_child (cast document_ptr) (cast html);
        head \<leftarrow> create_element document_ptr ''head'';
        append_child (cast html) (cast head);
        body \<leftarrow> create_element document_ptr ''body'';
        append_child (cast html) (cast body);
        e1 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast body) (cast e1);
        e2 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast e1) (cast e2);
        s1 \<leftarrow> attach_shadow_root e1 Open;
        e3 \<leftarrow> create_element document_ptr ''slot'';
        append_child (cast s1) (cast e3);
        return e1
      }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e1 = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and element_ptr="?e1"])
    by code_simp+
qed

locale l_get_shadow_root_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_scdom_component +
  l_get_shadow_root_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_create_document +
  l_get_owner_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_mode +
  l_get_scdom_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  assumes known_ptrs_impl: "known_ptrs = a_known_ptrs"
begin
lemma get_shadow_root_components_disjunct:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
  shows "set |h \<turnstile> get_scdom_component (cast host)|\<^sub>r \<inter> set |  h \<turnstile> get_scdom_component (cast shadow_root_ptr)|\<^sub>r = {}"
proof -
  obtain owner_document where owner_document: "h \<turnstile> get_owner_document (cast host) \<rightarrow>\<^sub>r owner_document"
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(5) element_ptr_kinds_commutes
        is_OK_returns_result_E is_OK_returns_result_I local.get_dom_component_ok local.get_dom_component_ptr
        local.get_scdom_component_ok local.get_scdom_component_owner_document_same
        local.get_scdom_component_subset_get_dom_component local.get_shadow_root_ptr_in_heap node_ptr_kinds_commutes
        subset_code(1))
  have "owner_document \<noteq> cast shadow_root_ptr"
  proof
    assume "owner_document = cast shadow_root_ptr"
    then have "(cast owner_document, cast host) \<in>
(parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
      using get_owner_document_rel owner_document
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) cast_document_ptr_not_node_ptr(2)
          in_rtrancl_UnI inf_sup_aci(6) inf_sup_aci(7))
    then have "(cast shadow_root_ptr, cast host) \<in>
(parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
      by (simp add: \<open>owner_document = cast shadow_root_ptr\<close>)
    moreover have "(cast host, cast shadow_root_ptr) \<in> a_host_shadow_root_rel h"
      by (metis (mono_tags, lifting) assms(5) is_OK_returns_result_I local.get_shadow_root_ptr_in_heap
          local.a_host_shadow_root_rel_def mem_Collect_eq pair_imageI prod.simps(2) select_result_I2)
    then have "(cast host, cast shadow_root_ptr) \<in>
(parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
      by (simp)
    ultimately show False
      using assms(1)
      unfolding heap_is_wellformed_def \<open>owner_document = cast shadow_root_ptr\<close> acyclic_def
      by (meson rtrancl_into_trancl1)
  qed
  moreover
  have "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
    using assms(1) assms(5) local.get_shadow_root_shadow_root_ptr_in_heap by blast
  then
  have "cast shadow_root_ptr \<in> fset (object_ptr_kinds h)"
    by auto
  have "is_shadow_root_ptr shadow_root_ptr"
    using assms(3)[unfolded known_ptrs_impl ShadowRootClass.known_ptrs_defs
        ShadowRootClass.known_ptr_defs DocumentClass.known_ptr_defs CharacterDataClass.known_ptr_defs
        ElementClass.known_ptr_defs NodeClass.known_ptr_defs, simplified, rule_format, OF
        \<open>cast shadow_root_ptr \<in> fset (object_ptr_kinds h)\<close>]
    by(auto simp add: is_document_ptr\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        split: option.splits document_ptr.splits)
  then
  have "h \<turnstile> get_owner_document (cast shadow_root_ptr) \<rightarrow>\<^sub>r cast shadow_root_ptr"
    using \<open>shadow_root_ptr |\<in>| shadow_root_ptr_kinds h\<close>
    apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
        CD.a_get_owner_document_tups_def)[1]
    apply(split invoke_splits, (rule conjI | rule impI)+)+
    by(auto simp add: is_node_ptr_kind_none a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)
  ultimately show ?thesis
    using assms(1) assms(2) assms(3) get_scdom_component_different_owner_documents owner_document
    by blast
qed

lemma get_shadow_root_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_shadow_root_safe element_ptr \<rightarrow>\<^sub>r shadow_root_ptr_opt \<rightarrow>\<^sub>h h'"
  assumes "\<forall>shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h). h \<turnstile> get_mode shadow_root_ptr \<rightarrow>\<^sub>r Closed"
  shows "is_strongly_scdom_component_safe {cast element_ptr} (cast ` set_option shadow_root_ptr_opt) h h'"
proof -
  have "h = h'"
    using assms(4)
    by(auto simp add: returns_result_heap_def pure_returns_heap_eq)
  moreover have "shadow_root_ptr_opt = None"
    using assms(4)
    apply(auto simp add: returns_result_heap_def get_shadow_root_safe_def elim!: bind_returns_result_E2
        split: option.splits if_splits)[1]
    using get_shadow_root_shadow_root_ptr_in_heap
    by (meson assms(5) is_OK_returns_result_I local.get_mode_ptr_in_heap notin_fset returns_result_eq
        shadow_root_mode.distinct(1))
  ultimately show ?thesis
    by(simp add: is_strongly_scdom_component_safe_def preserved_def)
qed
end

interpretation i_get_shadow_root_scope_component?: l_get_shadow_root_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe get_dom_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_shadow_root get_shadow_root_locs
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs get_tag_name
  get_tag_name_locs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs to_tree_order get_parent get_parent_locs get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  remove_shadow_root remove_shadow_root_locs create_document DocumentClass.known_ptr DocumentClass.type_wf
  CD.a_get_owner_document  get_mode get_mode_locs get_shadow_root_safe get_shadow_root_safe_locs
  by(auto simp add: l_get_shadow_root_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_shadow_root_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_get_shadow_root_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_host\<close>

lemma get_host_not_weakly_scdom_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    shadow_root_ptr and element_ptr and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r element_ptr \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_scdom_component_safe {cast shadow_root_ptr} {cast element_ptr} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder},
'Shadowroot::{equal,linorder}) heap"
  let ?P = "do {
        document_ptr \<leftarrow> create_document;
        html \<leftarrow> create_element document_ptr ''html'';
        append_child (cast document_ptr) (cast html);
        head \<leftarrow> create_element document_ptr ''head'';
        append_child (cast html) (cast head);
        body \<leftarrow> create_element document_ptr ''body'';
        append_child (cast html) (cast body);
        e1 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast body) (cast e1);
        e2 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast e1) (cast e2);
        s1 \<leftarrow> attach_shadow_root e1 Open;
        e3 \<leftarrow> create_element document_ptr ''slot'';
        append_child (cast s1) (cast e3);
        return s1
      }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?s1 = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and shadow_root_ptr="?s1"])
    by code_simp+
qed

locale l_get_host_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_host_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_host_components_disjunct:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_scdom_component ptr \<rightarrow>\<^sub>r sc"
  assumes "h \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host"
  shows "set |h \<turnstile> get_scdom_component (cast host)|\<^sub>r \<inter> set |  h \<turnstile> get_scdom_component (cast shadow_root_ptr)|\<^sub>r = {}"
  using assms get_shadow_root_components_disjunct local.shadow_root_host_dual
  by blast
end

interpretation i_get_host_scope_component?: l_get_host_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document heap_is_wellformed parent_child_rel type_wf known_ptr
  known_ptrs get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe
  get_dom_component is_strongly_dom_component_safe is_weakly_dom_component_safe get_shadow_root
  get_shadow_root_locs get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_tag_name get_tag_name_locs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs to_tree_order get_parent get_parent_locs get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  remove_shadow_root remove_shadow_root_locs create_document DocumentClass.known_ptr DocumentClass.type_wf
  CD.a_get_owner_document get_mode get_mode_locs get_shadow_root_safe get_shadow_root_safe_locs
  by(auto simp add: l_get_host_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_host_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_root\_node\_si\<close>

lemma get_composed_root_node_not_weakly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    ptr and root and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> get_root_node_si ptr \<rightarrow>\<^sub>r root \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_scdom_component_safe {ptr} {root} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder},
'Shadowroot::{equal,linorder}) heap"
  let ?P = "do {
        document_ptr \<leftarrow> create_document;
        html \<leftarrow> create_element document_ptr ''html'';
        append_child (cast document_ptr) (cast html);
        head \<leftarrow> create_element document_ptr ''head'';
        append_child (cast html) (cast head);
        body \<leftarrow> create_element document_ptr ''body'';
        append_child (cast html) (cast body);
        e1 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast body) (cast e1);
        e2 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast e1) (cast e2);
        s1 \<leftarrow> attach_shadow_root e1 Closed;
        e3 \<leftarrow> create_element document_ptr ''slot'';
        append_child (cast s1) (cast e3);
        return e3
      }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e3 = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and ptr="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e3"])
    by code_simp+
qed

locale l_get_scdom_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_dom_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_dom_component_get_scdom_component
begin

lemma get_root_node_si_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node_si ptr' \<rightarrow>\<^sub>r root"
  shows "set |h \<turnstile> get_scdom_component ptr'|\<^sub>r = set |h \<turnstile> get_scdom_component root|\<^sub>r \<or>
set |h \<turnstile> get_scdom_component ptr'|\<^sub>r \<inter> set |h \<turnstile> get_scdom_component root|\<^sub>r = {}"
proof -
  have "ptr' |\<in>| object_ptr_kinds h"
    using get_ancestors_si_ptr_in_heap assms(4)
    by(auto simp add: get_root_node_si_def elim!: bind_returns_result_E2)
  then
  obtain sc where "h \<turnstile> get_scdom_component ptr' \<rightarrow>\<^sub>r sc"
    by (meson assms(1) assms(2) assms(3) local.get_scdom_component_ok select_result_I)
  moreover
  have "root |\<in>| object_ptr_kinds h"
    using get_ancestors_si_ptr assms(4)
    apply(auto simp add: get_root_node_si_def elim!: bind_returns_result_E2)[1]
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) empty_iff empty_set
        get_ancestors_si_ptrs_in_heap last_in_set)
  then
  obtain sc' where "h \<turnstile> get_scdom_component root \<rightarrow>\<^sub>r sc'"
    by (meson assms(1) assms(2) assms(3) local.get_scdom_component_ok select_result_I)
  ultimately show ?thesis
    by (metis (no_types, hide_lams) IntE \<open>\<And>thesis. (\<And>sc'. h \<turnstile> get_scdom_component root \<rightarrow>\<^sub>r sc' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
        \<open>\<And>thesis. (\<And>sc. h \<turnstile> get_scdom_component ptr' \<rightarrow>\<^sub>r sc \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> assms(1) assms(2) assms(3) empty_subsetI
        local.get_scdom_component_ptrs_same_scope_component returns_result_eq select_result_I2 subsetI subset_antisym)
qed
end

interpretation i_get_scdom_component_get_root_node_si?: l_get_scdom_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs get_host
  get_host_locs get_ancestors_si get_ancestors_si_locs get_root_node_si get_root_node_si_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs heap_is_wellformed
  parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_document get_disconnected_document_locs to_tree_order
  get_dom_component is_strongly_dom_component_safe is_weakly_dom_component_safe get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  get_owner_document get_scdom_component is_strongly_scdom_component_safe
  by(auto simp add: l_get_scdom_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_scdom_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_assigned\_nodes\<close>

lemma assigned_nodes_not_weakly_scdom_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    node_ptr and nodes and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> assigned_nodes node_ptr \<rightarrow>\<^sub>r nodes \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_scdom_component_safe {cast node_ptr} (cast ` set nodes) h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap"
  let ?P = "do {
        document_ptr \<leftarrow> create_document;
        html \<leftarrow> create_element document_ptr ''html'';
        append_child (cast document_ptr) (cast html);
        head \<leftarrow> create_element document_ptr ''head'';
        append_child (cast html) (cast head);
        body \<leftarrow> create_element document_ptr ''body'';
        append_child (cast html) (cast body);
        e1 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast body) (cast e1);
        e2 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast e1) (cast e2);
        s1 \<leftarrow> attach_shadow_root e1 Closed;
        e3 \<leftarrow> create_element document_ptr ''slot'';
        append_child (cast s1) (cast e3);
        return e3
      }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e3 = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and node_ptr="?e3"])
    by code_simp+
qed

lemma assigned_slot_not_weakly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    node_ptr and slot_opt and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> assigned_slot node_ptr \<rightarrow>\<^sub>r slot_opt \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_scdom_component_safe {cast node_ptr} (cast ` set_option slot_opt) h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder},
'Shadowroot::{equal,linorder}) heap"
  let ?P = "do {
        document_ptr \<leftarrow> create_document;
        html \<leftarrow> create_element document_ptr ''html'';
        append_child (cast document_ptr) (cast html);
        head \<leftarrow> create_element document_ptr ''head'';
        append_child (cast html) (cast head);
        body \<leftarrow> create_element document_ptr ''body'';
        append_child (cast html) (cast body);
        e1 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast body) (cast e1);
        e2 \<leftarrow> create_element document_ptr ''div'';
        append_child (cast e1) (cast e2);
        s1 \<leftarrow> attach_shadow_root e1 Open;
        e3 \<leftarrow> create_element document_ptr ''slot'';
        append_child (cast s1) (cast e3);
        return e2
      }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e2 = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and node_ptr="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e2"])
    by code_simp+
qed

locale l_assigned_nodes_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_assigned_nodes_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_shadow_root_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma find_slot_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> find_slot open_flag node_ptr \<rightarrow>\<^sub>r Some slot"
  shows "set |h \<turnstile> get_scdom_component (cast node_ptr)|\<^sub>r \<inter> set |h \<turnstile> get_scdom_component (cast slot)|\<^sub>r = {}"
proof -
  obtain host shadow_root_ptr to where
    "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some (cast host)" and
    "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr" and
    "h \<turnstile> to_tree_order (cast shadow_root_ptr) \<rightarrow>\<^sub>r to" and
    "cast slot \<in> set to"
    using assms(4)
    apply(auto simp add: find_slot_def first_in_tree_order_def elim!: bind_returns_result_E2
        map_filter_M_pure_E[where y=slot] split: option.splits if_splits list.splits
        intro!: map_filter_M_pure bind_pure_I)[1]
    by (metis element_ptr_casts_commute3)+

  have "node_ptr |\<in>| node_ptr_kinds h"
    using assms(4) find_slot_ptr_in_heap by blast
  then obtain node_ptr_c where node_ptr_c: "h \<turnstile> get_scdom_component (cast node_ptr) \<rightarrow>\<^sub>r node_ptr_c"
    using assms(1) assms(2) assms(3) get_scdom_component_ok is_OK_returns_result_E
      node_ptr_kinds_commutes[symmetric]
    by metis

  then have "cast host \<in> set node_ptr_c"
    using \<open>h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some (cast host)\<close> assms(1) assms(2) assms(3)
    by (meson assms(4) is_OK_returns_result_E local.find_slot_ptr_in_heap local.get_dom_component_ok
        local.get_dom_component_parent_inside local.get_dom_component_ptr
        local.get_scdom_component_subset_get_dom_component node_ptr_kinds_commutes subsetCE)

  then have "h \<turnstile> get_scdom_component (cast host) \<rightarrow>\<^sub>r node_ptr_c"
    using \<open>h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some (cast host)\<close> a_heap_is_wellformed_def assms(1) assms(2)
      assms(3) node_ptr_c
    using local.get_scdom_component_ptrs_same_scope_component by blast

  moreover have "slot |\<in>| element_ptr_kinds h"
    using assms(4) find_slot_slot_in_heap by blast
  then obtain slot_c where slot_c: "h \<turnstile> get_scdom_component (cast slot) \<rightarrow>\<^sub>r slot_c"
    using a_heap_is_wellformed_def assms(1) assms(2) assms(3) get_scdom_component_ok
      is_OK_returns_result_E node_ptr_kinds_commutes[symmetric] element_ptr_kinds_commutes[symmetric]
    by smt
  then have "cast shadow_root_ptr \<in> set slot_c"
    using \<open>h \<turnstile> to_tree_order (cast shadow_root_ptr) \<rightarrow>\<^sub>r to\<close> \<open>cast slot \<in> set to\<close> assms(1) assms(2) assms(3)
    by (meson is_OK_returns_result_E local.get_dom_component_ok local.get_dom_component_ptr
        local.get_dom_component_to_tree_order local.get_scdom_component_subset_get_dom_component local.to_tree_order_ptrs_in_heap subsetCE)
  then have "h \<turnstile> get_scdom_component (cast shadow_root_ptr) \<rightarrow>\<^sub>r slot_c"
    using  \<open>h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr\<close> assms(1) assms(2) assms(3) slot_c
    using local.get_scdom_component_ptrs_same_scope_component by blast

  ultimately show ?thesis
    using get_shadow_root_components_disjunct assms \<open>h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr\<close>
      node_ptr_c slot_c
    by (metis (no_types, lifting) select_result_I2)
qed


lemma assigned_nodes_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> assigned_nodes element_ptr \<rightarrow>\<^sub>r nodes"
  assumes "node_ptr \<in> set nodes"
  shows "set |h \<turnstile> get_scdom_component (cast element_ptr)|\<^sub>r \<inter> set |h \<turnstile> get_scdom_component (cast node_ptr)|\<^sub>r = {}"
  using assms
proof -
  have "h \<turnstile> find_slot False node_ptr \<rightarrow>\<^sub>r Some element_ptr"
    using assms(4) assms(5)
    by(auto simp add: assigned_nodes_def elim!: bind_returns_result_E2
        dest!: filter_M_holds_for_result[where x=node_ptr] intro!: bind_pure_I split: if_splits)
  then show ?thesis
    using assms find_slot_is_component_unsafe
    by blast
qed

lemma assigned_slot_is_strongly_scdom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> assigned_slot element_ptr \<rightarrow>\<^sub>r slot_opt \<rightarrow>\<^sub>h h'"
  assumes "\<forall>shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h). h \<turnstile> get_mode shadow_root_ptr \<rightarrow>\<^sub>r Closed"
  shows "is_strongly_scdom_component_safe {cast element_ptr} (cast ` set_option slot_opt) h h'"
proof -
  have "h = h'"
    using assms(4) find_slot_pure
    by(auto simp add: assigned_slot_def returns_result_heap_def pure_returns_heap_eq find_slot_impl)
  moreover have "slot_opt = None"
    using assms(4) assms(5)
    apply(auto simp add: returns_result_heap_def assigned_slot_def a_find_slot_def
        elim!: bind_returns_result_E2 split: option.splits if_splits
        dest!: get_shadow_root_shadow_root_ptr_in_heap[OF assms(1)])[1]
     apply (meson finite_set_in returns_result_eq shadow_root_mode.distinct(1))
    apply (meson finite_set_in returns_result_eq shadow_root_mode.distinct(1))
    done
  ultimately show ?thesis
    by(auto simp add: is_strongly_scdom_component_safe_def preserved_def)
qed
end

interpretation i_assigned_nodes_scope_component?: l_assigned_nodes_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf get_tag_name get_tag_name_locs known_ptr get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs
  heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs
  get_disconnected_document get_disconnected_document_locs get_parent get_parent_locs
  get_mode get_mode_locs get_attribute get_attribute_locs first_in_tree_order find_slot
  assigned_slot known_ptrs to_tree_order assigned_nodes assigned_nodes_flatten flatten_dom
  get_root_node get_root_node_locs remove insert_before insert_before_locs append_child
  remove_shadow_root remove_shadow_root_locs set_shadow_root set_shadow_root_locs remove_child
  remove_child_locs get_dom_component is_strongly_dom_component_safe is_weakly_dom_component_safe
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  get_owner_document set_disconnected_nodes set_disconnected_nodes_locs get_ancestors_di get_ancestors_di_locs
  adopt_node adopt_node_locs adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_child_nodes set_child_nodes_locs
  get_scdom_component is_strongly_scdom_component_safe is_weakly_scdom_component_safe create_document
  DocumentClass.known_ptr DocumentClass.type_wf CD.a_get_owner_document get_shadow_root_safe
  get_shadow_root_safe_locs
  by(auto simp add: l_assigned_nodes_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_assigned_nodes_scope_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]
end
