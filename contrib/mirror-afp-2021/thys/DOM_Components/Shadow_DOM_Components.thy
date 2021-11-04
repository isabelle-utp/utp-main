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

section \<open>Shadow Root Components\<close>

theory Shadow_DOM_Components
  imports
    Shadow_DOM.Shadow_DOM
    Core_DOM_Components
begin

subsection \<open>get\_component\<close>

global_interpretation l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_root_node get_root_node_locs to_tree_order
  defines get_component = a_get_component
    and is_strongly_dom_component_safe = a_is_strongly_dom_component_safe
    and is_weakly_dom_component_safe = a_is_weakly_dom_component_safe
  .

interpretation i_get_component?: l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name
  by(auto simp add: l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def get_component_def
      is_strongly_dom_component_safe_def is_weakly_dom_component_safe_def instances)
declare l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



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
    "\<not> is_strongly_dom_component_safe {cast host} {cast new_shadow_root_ptr} h h'"
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

locale l_get_dom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order
  get_parent get_parent_locs get_child_nodes get_child_nodes_locs get_dom_component
  is_strongly_component_safe is_weakly_component_safe get_root_node get_root_node_locs get_ancestors
  get_ancestors_locs get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name +
  l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr set_shadow_root set_shadow_root_locs set_mode set_mode_locs
  attach_shadow_root type_wf get_tag_name get_tag_name_locs get_shadow_root get_shadow_root_locs +
  l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_mode set_mode_locs +
  l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_shadow_root set_shadow_root_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
    and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
    and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and known_ptrs :: "(_) heap \<Rightarrow> bool"
    and to_tree_order :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_dom_component :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
    and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_ancestors :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and get_ancestors_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_element_by_id ::
    "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
    and get_elements_by_class_name ::
    "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr list) prog"
    and get_elements_by_tag_name ::
    "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr list) prog"
    and set_shadow_root ::
    "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_mode :: "(_) shadow_root_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and attach_shadow_root ::
    "(_) element_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr) prog"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and is_strongly_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
    and is_weakly_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin

lemma attach_shadow_root_is_weakly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>h h'"
  assumes "ptr \<noteq> cast |h \<turnstile> attach_shadow_root element_ptr shadow_root_mode|\<^sub>r"
  assumes "ptr \<notin> set |h \<turnstile> get_dom_component (cast element_ptr)|\<^sub>r"
  shows "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
proof -
  obtain h2 h3 new_shadow_root_ptr where
    h2: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h2" and
    new_shadow_root_ptr: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr" and
    h3: "h2 \<turnstile> set_mode new_shadow_root_ptr shadow_root_mode \<rightarrow>\<^sub>h h3" and
    h': "h3 \<turnstile> set_shadow_root element_ptr (Some new_shadow_root_ptr) \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: attach_shadow_root_def elim!:  bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_tag_name_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_shadow_root_pure, rotated]
        split: if_splits)
  have "h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>r new_shadow_root_ptr"
    using new_shadow_root_ptr h2 h3 h'
    using assms(4)
    by(auto simp add: attach_shadow_root_def intro!: bind_returns_result_I
        bind_pure_returns_result_I[OF get_tag_name_pure] bind_pure_returns_result_I[OF get_shadow_root_pure]
        elim!:  bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_tag_name_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_shadow_root_pure, rotated] split: if_splits)
  have "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h2"
    using h2 new_shadow_root_ptr
    by (metis (no_types, lifting)
        \<open>h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>r new_shadow_root_ptr\<close> assms(5)
        new_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t select_result_I2)

  have "ptr \<noteq> cast new_shadow_root_ptr"
    using \<open>h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>r new_shadow_root_ptr\<close> assms(5)
    by auto

  have "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h2 h3"
    using set_mode_writes h3
    apply(rule reads_writes_preserved2)
    apply(auto simp add: set_mode_locs_def all_args_def)[1]
    using \<open>ptr \<noteq> cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr\<close>
    by (metis get_M_Mshadow_root_preserved3)

  have "element_ptr |\<in>| element_ptr_kinds h"
    using \<open>h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>r new_shadow_root_ptr\<close>
      attach_shadow_root_element_ptr_in_heap
    by blast
  have "ptr \<noteq> cast element_ptr"
    by (metis (no_types, lifting) \<open>element_ptr |\<in>| element_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        assms(6) element_ptr_kinds_commutes is_OK_returns_result_E get_component_ok local.get_dom_component_ptr
        node_ptr_kinds_commutes select_result_I2)

  have "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h3 h'"
    using set_shadow_root_writes h'
    apply(rule reads_writes_preserved2)
    apply(auto simp add: set_shadow_root_locs_def all_args_def)[1]
    by (metis \<open>ptr \<noteq> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr\<close> get_M_Element_preserved8)

  show ?thesis
    using \<open>preserved (get_M ptr getter) h h2\<close> \<open>preserved (get_M ptr getter) h2 h3\<close>
      \<open>preserved (get_M ptr getter) h3 h'\<close>
    by(auto simp add: preserved_def)
qed
end

interpretation i_get_dom_component_attach_shadow_root?: l_get_dom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr heap_is_wellformed parent_child_rel type_wf known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  set_shadow_root set_shadow_root_locs set_mode set_mode_locs attach_shadow_root get_disconnected_nodes
  get_disconnected_nodes_locs is_strongly_dom_component_safe is_weakly_dom_component_safe get_tag_name
  get_tag_name_locs get_shadow_root get_shadow_root_locs
  by(auto simp add: l_get_dom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_dom_component_attach_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_shadow\_root\<close>

lemma get_shadow_root_not_weakly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    element_ptr and shadow_root_ptr_opt and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r shadow_root_ptr_opt \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_dom_component_safe {cast element_ptr} (cast ` set_option shadow_root_ptr_opt) h h'"
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
        return e1
      }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e1 = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and element_ptr="?e1"])
    by code_simp+
qed

locale l_get_shadow_root_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_shadow_root_get_child_nodes
begin
lemma get_shadow_root_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
  shows "set |h \<turnstile> get_component (cast host)|\<^sub>r \<inter> set |h \<turnstile> get_component (cast shadow_root_ptr)|\<^sub>r = {}"
proof -
  have "cast host |\<in>| object_ptr_kinds h"
    using assms(4) get_shadow_root_ptr_in_heap by auto
  then obtain host_c where host_c: "h \<turnstile> get_component (cast host) \<rightarrow>\<^sub>r host_c"
    by (meson  assms(1) assms(2) assms(3) get_component_ok is_OK_returns_result_E)
  obtain host_root where host_root: "h \<turnstile> get_root_node (cast host) \<rightarrow>\<^sub>r host_root"
    by (metis (no_types, lifting) bind_returns_heap_E get_component_def host_c is_OK_returns_result_I
        pure_def pure_eq_iff)

  have "cast shadow_root_ptr |\<in>| object_ptr_kinds h"
    using get_shadow_root_shadow_root_ptr_in_heap assms shadow_root_ptr_kinds_commutes
    using document_ptr_kinds_commutes by blast
  then obtain shadow_root_ptr_c where shadow_root_ptr_c:
    "h \<turnstile> get_component (cast shadow_root_ptr) \<rightarrow>\<^sub>r shadow_root_ptr_c"
    by (meson  assms(1) assms(2) assms(3) get_component_ok is_OK_returns_result_E)
  have "h \<turnstile> get_root_node (cast shadow_root_ptr) \<rightarrow>\<^sub>r cast shadow_root_ptr"
    using \<open>cast shadow_root_ptr |\<in>| object_ptr_kinds h\<close>
    by(auto simp add: get_root_node_def get_ancestors_def intro!: bind_pure_returns_result_I
        split: option.splits)

  have "host_root \<noteq> cast shadow_root_ptr"
  proof (rule ccontr, simp)
    assume "host_root = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr"

    have "(cast shadow_root_ptr, host_root) \<in> (parent_child_rel h)\<^sup>*"
      using \<open>host_root = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr\<close> by auto
    moreover have "(host_root, cast host) \<in> (parent_child_rel h)\<^sup>*"
      using get_root_node_parent_child_rel host_root assms
      by blast
    moreover have "(cast host, cast shadow_root_ptr) \<in> (a_host_shadow_root_rel h)"
      using assms(4) apply(auto simp add: a_host_shadow_root_rel_def)[1]
      by (metis (mono_tags, lifting) get_shadow_root_ptr_in_heap image_eqI is_OK_returns_result_I
          mem_Collect_eq prod.simps(2) select_result_I2)
    moreover have " acyclic (parent_child_rel h \<union> local.a_host_shadow_root_rel h)"
      using assms(1)[unfolded heap_is_wellformed_def]
      by auto
    ultimately show False
      using local.parent_child_rel_node_ptr
      by (metis (no_types, lifting) Un_iff \<open>host_root = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr\<close>
          acyclic_def in_rtrancl_UnI rtrancl_into_trancl1)
  qed
  then have "host_c \<noteq> shadow_root_ptr_c"
    by (metis \<open>h \<turnstile> get_root_node (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) \<rightarrow>\<^sub>r cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r
shadow_root_ptr\<close> assms(1) assms(2) assms(3) get_dom_component_ptr get_component_root_node_same
        host_c host_root local.get_root_node_parent_child_rel local.get_root_node_same_no_parent_parent_child_rel
        rtranclE shadow_root_ptr_c)
  then have "set host_c \<inter> set shadow_root_ptr_c = {}"
    using assms get_dom_component_no_overlap Shadow_DOM.a_heap_is_wellformed_def host_c
      shadow_root_ptr_c
    by blast
  then show ?thesis
    using host_c shadow_root_ptr_c
    by auto
qed
end

interpretation i_get_shadow_root_component?: l_get_shadow_root_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf get_shadow_root get_shadow_root_locs get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_tag_name get_tag_name_locs known_ptr
  heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs
  get_disconnected_document get_disconnected_document_locs known_ptrs to_tree_order get_parent
  get_parent_locs get_component is_strongly_dom_component_safe is_weakly_dom_component_safe
  get_root_node get_root_node_locs get_ancestors get_ancestors_locs get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name remove_shadow_root remove_shadow_root_locs
  by(auto simp add: l_get_shadow_root_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_shadow_root_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_host\<close>

lemma get_host_not_weakly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    shadow_root_ptr and host and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_dom_component_safe {cast shadow_root_ptr} {cast host} h h'"
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

locale l_get_host_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_host +
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M  +
  l_get_shadow_root_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_host_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host"
  shows "set |h \<turnstile> get_component (cast host)|\<^sub>r \<inter> set |h \<turnstile> get_component (cast shadow_root_ptr)|\<^sub>r = {}"
proof -
  have "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
    using assms(1) assms(2) assms(4) local.shadow_root_host_dual by blast
  then show ?thesis
    using assms(1) assms(2) assms(3) local.get_shadow_root_is_component_unsafe by blast
qed
end

interpretation i_get_host_component?: l_get_host_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs known_ptr type_wf heap_is_wellformed
  parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs known_ptrs to_tree_order get_parent get_parent_locs get_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  remove_shadow_root remove_shadow_root_locs
  by(auto simp add: l_get_host_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_host_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsection \<open>get\_root\_node\_si\<close>

locale l_get_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_root_node_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_root_node_si_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node_si ptr' \<rightarrow>\<^sub>r root"
  shows "set |h \<turnstile> get_component ptr'|\<^sub>r = set |h \<turnstile> get_component root|\<^sub>r \<or>
set |h \<turnstile> get_component ptr'|\<^sub>r \<inter> set |h \<turnstile> get_component root|\<^sub>r = {}"
proof -
  have "ptr' |\<in>| object_ptr_kinds h"
    using get_ancestors_si_ptr_in_heap assms(4)
    by(auto simp add: get_root_node_si_def elim!: bind_returns_result_E2)
  then
  obtain c where "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
    by (meson assms(1) assms(2) assms(3) local.get_component_ok select_result_I)
  moreover
  have "root |\<in>| object_ptr_kinds h"
    using get_ancestors_si_ptr assms(4)
    apply(auto simp add: get_root_node_si_def elim!: bind_returns_result_E2)[1]
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) empty_iff empty_set
        get_ancestors_si_ptrs_in_heap last_in_set)
  then
  obtain c' where "h \<turnstile> get_component root \<rightarrow>\<^sub>r c'"
    by (meson assms(1) assms(2) assms(3) local.get_component_ok select_result_I)
  ultimately show ?thesis
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) local.get_dom_component_no_overlap
        select_result_I2)
qed
end

interpretation i_get_component_get_root_node_si?: l_get_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_host get_host_locs get_ancestors_si get_ancestors_si_locs get_root_node_si get_root_node_si_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs get_tag_name
  get_tag_name_locs heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_document
  get_disconnected_document_locs to_tree_order get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_element_by_id get_elements_by_class_name get_elements_by_tag_name
  by(auto simp add: l_get_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsection \<open>get\_assigned\_nodes\<close>

lemma assigned_nodes_not_weakly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    node_ptr and nodes and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> assigned_nodes node_ptr \<rightarrow>\<^sub>r nodes \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_dom_component_safe {cast node_ptr} (cast ` set nodes) h h'"
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
    apply(rule that[where h="?h1" and node_ptr="?e3"])
    by code_simp+
qed

lemma get_composed_root_node_not_weakly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    ptr and root and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> get_root_node_si ptr \<rightarrow>\<^sub>r root \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_dom_component_safe {ptr} {root} h h'"
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

lemma assigned_slot_not_weakly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}, 'Shadowroot::{equal,linorder}) heap" and
    node_ptr and slot_opt and h' where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> assigned_slot node_ptr \<rightarrow>\<^sub>r slot_opt \<rightarrow>\<^sub>h h'" and
    "\<not> is_weakly_dom_component_safe {cast node_ptr} (cast ` set_option slot_opt) h h'"
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

locale l_assigned_nodes_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_tag_name +
  l_get_child_nodes +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_assigned_nodes_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_child_wf2 +
  l_insert_before_wf +
  l_insert_before_wf2 +
  l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ _ _ _ _ _ get_ancestors_si get_ancestors_si_locs +
  l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_append_child_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ get_ancestors_si get_ancestors_si_locs +
  l_set_disconnected_nodes_get_tag_name +
  l_set_shadow_root_get_child_nodes +
  l_set_child_nodes_get_tag_name +
  l_get_shadow_root_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_shadow_root_get_tag_name +
  l_set_disconnected_nodes_get_shadow_root +
  l_set_child_nodes_get_shadow_root +
  l_remove_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma find_slot_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> find_slot open_flag node_ptr \<rightarrow>\<^sub>r Some slot"
  shows "set |h \<turnstile> get_component (cast node_ptr)|\<^sub>r \<inter> set |h \<turnstile> get_component (cast slot)|\<^sub>r = {}"
proof -
  obtain host shadow_root_ptr to where
    "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some (cast host)" and
    "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr" and
    "h \<turnstile> to_tree_order (cast shadow_root_ptr) \<rightarrow>\<^sub>r to" and
    "cast slot \<in> set to"
    using assms(4)
    apply(auto simp add: find_slot_def first_in_tree_order_def elim!: bind_returns_result_E2
        map_filter_M_pure_E[where y=slot]
        split: option.splits if_splits list.splits intro!: map_filter_M_pure bind_pure_I)[1]
    by (metis element_ptr_casts_commute3)+

  have "node_ptr |\<in>| node_ptr_kinds h"
    using assms(4) find_slot_ptr_in_heap by blast
  then obtain node_ptr_c where node_ptr_c: "h \<turnstile> get_component (cast node_ptr) \<rightarrow>\<^sub>r node_ptr_c"
    using assms(1) assms(2) assms(3) get_component_ok is_OK_returns_result_E
      node_ptr_kinds_commutes[symmetric]
    by metis

  then have "cast host \<in> set node_ptr_c"
    using \<open>h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some (cast host)\<close> get_component_parent_inside assms(1)
      assms(2) assms(3) get_dom_component_ptr
    by blast

  then have "h \<turnstile> get_component (cast host) \<rightarrow>\<^sub>r node_ptr_c"
    using \<open>h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some (cast host)\<close> get_component_subset a_heap_is_wellformed_def
      assms(1) assms(2) assms(3) node_ptr_c
    by blast

  moreover have "slot |\<in>| element_ptr_kinds h"
    using assms(4) find_slot_slot_in_heap by blast
  then obtain slot_c where slot_c: "h \<turnstile> get_component (cast slot) \<rightarrow>\<^sub>r slot_c"
    using a_heap_is_wellformed_def assms(1) assms(2) assms(3) get_component_ok is_OK_returns_result_E
      node_ptr_kinds_commutes[symmetric] element_ptr_kinds_commutes[symmetric]
    by metis
  then have "cast shadow_root_ptr \<in> set slot_c"
    using \<open>h \<turnstile> to_tree_order (cast shadow_root_ptr) \<rightarrow>\<^sub>r to\<close> \<open>cast slot \<in> set to\<close>
      get_component_to_tree_order assms(1) assms(2) assms(3) get_dom_component_ptr
    by blast
  then have "h \<turnstile> get_component (cast shadow_root_ptr) \<rightarrow>\<^sub>r slot_c"
    using  \<open>h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr\<close> get_component_subset assms(1) assms(2)
      assms(3) slot_c
    by blast

  ultimately show ?thesis
    using get_shadow_root_is_component_unsafe assms \<open>h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr\<close>
      node_ptr_c slot_c
    by fastforce
qed

lemma assigned_slot_pure:
  "pure (assigned_slot node_ptr) h"
  apply(auto simp add: assigned_slot_def a_find_slot_def intro!: bind_pure_I  split: option.splits)[1]
  by(auto simp add: first_in_tree_order_def intro!: bind_pure_I map_filter_M_pure split: list.splits)

lemma assigned_slot_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> assigned_slot node_ptr \<rightarrow>\<^sub>r slot_opt \<rightarrow>\<^sub>h h'"
  assumes "\<forall>shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h). h \<turnstile> get_mode shadow_root_ptr \<rightarrow>\<^sub>r Closed"
  shows "is_strongly_dom_component_safe {cast node_ptr} (cast ` set_option slot_opt) h h'"
proof -
  have "h = h'"
    using assms(5) assigned_slot_pure
    by (meson assms(4) pure_returns_heap_eq returns_result_heap_def)
  obtain parent_opt where parent_opt: "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r parent_opt"
    using assms(4)
    by (auto simp add: assigned_slot_def a_find_slot_def returns_result_heap_def
        elim!: bind_returns_result_E2 split: option.splits split: if_splits)
  then
  have "slot_opt = None"
  proof (induct parent_opt)
    case None
    then show ?case
      using assms(4)
      apply(auto simp add: assigned_slot_def a_find_slot_def returns_result_heap_def
          elim!: bind_returns_result_E2 split: option.splits split: if_splits)[1]
      by (meson option.distinct(1) returns_result_eq)+
  next
    case (Some parent)
    then show ?case
    proof (cases "is_element_ptr_kind parent")
      case True
      then obtain host where host: "parent = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host"
        by (metis (no_types, lifting) case_optionE element_ptr_casts_commute3 node_ptr_casts_commute)
      moreover have "host |\<in>| element_ptr_kinds h"
        using Some.prems element_ptr_kinds_commutes host local.get_parent_parent_in_heap
          node_ptr_kinds_commutes
        by blast
      ultimately obtain shadow_root_opt where shadow_root_opt:
        "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r shadow_root_opt"
        using get_shadow_root_ok
        by (meson assms(2) is_OK_returns_result_E)
      then show ?thesis
      proof (induct shadow_root_opt)
        case None
        then show ?case
          using assms(4)
          apply(auto dest!: returns_result_eq[OF \<open>h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some parent\<close>]
              simp add: assigned_slot_def a_find_slot_def returns_result_heap_def elim!: bind_returns_result_E2
              split: option.splits split: if_splits)[1]
          using host select_result_I2 by fastforce+
      next
        case (Some shadow_root_ptr)
        have "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
          using Some.prems assms(1) local.get_shadow_root_shadow_root_ptr_in_heap by blast
        then
        have "h \<turnstile> get_mode shadow_root_ptr \<rightarrow>\<^sub>r Closed"
          using assms by simp
        have "\<not>h \<turnstile> get_mode shadow_root_ptr \<rightarrow>\<^sub>r Open"
        proof (rule ccontr, simp)
          assume "h \<turnstile> get_mode shadow_root_ptr \<rightarrow>\<^sub>r Open"
          then have "Open = Closed"
            using returns_result_eq  \<open>h \<turnstile> get_mode shadow_root_ptr \<rightarrow>\<^sub>r Closed\<close>
            by fastforce
          then show False
            by simp
        qed
        then show ?case
          using assms(4) Some parent_opt host
          by(auto dest!: returns_result_eq[OF \<open>h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some parent\<close>]
              returns_result_eq[OF \<open>h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr\<close>]
              simp add: assigned_slot_def a_find_slot_def returns_result_heap_def
              elim!: bind_returns_result_E2 split: option.splits split: if_splits)
      qed
    next
      case False
      then show ?thesis
        using assms(4)
        by(auto dest!: returns_result_eq[OF \<open>h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some parent\<close>]
            simp add: assigned_slot_def a_find_slot_def returns_result_heap_def
            elim!: bind_returns_result_E2 split: option.splits split: if_splits)
    qed
  qed
  then show ?thesis
    using \<open>h = h'\<close>
    by(auto simp add: is_strongly_dom_component_safe_def preserved_def)
qed

lemma assigned_nodes_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> assigned_nodes element_ptr \<rightarrow>\<^sub>r nodes"
  assumes "node_ptr \<in> set nodes"
  shows "set |h \<turnstile> get_component (cast element_ptr)|\<^sub>r \<inter> set |h \<turnstile> get_component (cast node_ptr)|\<^sub>r = {}"
proof -
  have "h \<turnstile> find_slot False node_ptr \<rightarrow>\<^sub>r Some element_ptr"
    using assms(4) assms(5)
    by(auto simp add: assigned_nodes_def elim!: bind_returns_result_E2
        dest!: filter_M_holds_for_result[where x=node_ptr] intro!: bind_pure_I split: if_splits)
  then show ?thesis
    using assms find_slot_is_component_unsafe
    by blast
qed

lemma flatten_dom_assigned_nodes_become_children:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> flatten_dom \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> assigned_nodes slot \<rightarrow>\<^sub>r nodes"
  assumes "nodes \<noteq> []"
  shows "h' \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes"
proof -
  obtain tups h2 element_ptrs shadow_root_ptrs where
    "h \<turnstile> element_ptr_kinds_M \<rightarrow>\<^sub>r element_ptrs" and
    tups: "h \<turnstile> map_filter_M2 (\<lambda>element_ptr. do {
      tag \<leftarrow> get_tag_name element_ptr;
      assigned_nodes \<leftarrow> assigned_nodes element_ptr;
      (if tag = ''slot'' \<and> assigned_nodes \<noteq> [] then return (Some (element_ptr, assigned_nodes))
else return None)}) element_ptrs \<rightarrow>\<^sub>r tups" (is "h \<turnstile> map_filter_M2 ?f element_ptrs \<rightarrow>\<^sub>r tups") and
    h2: "h \<turnstile> forall_M (\<lambda>(slot, assigned_nodes). do {
      get_child_nodes (cast slot) \<bind> forall_M remove;
      forall_M (append_child (cast slot)) assigned_nodes
    }) tups \<rightarrow>\<^sub>h h2" and
    "h2 \<turnstile> shadow_root_ptr_kinds_M \<rightarrow>\<^sub>r shadow_root_ptrs" and
    h': "h2 \<turnstile> forall_M (\<lambda>shadow_root_ptr. do {
      host \<leftarrow> get_host shadow_root_ptr;
      get_child_nodes (cast host) \<bind> forall_M remove;
      get_child_nodes (cast shadow_root_ptr) \<bind> forall_M (append_child (cast host));
      remove_shadow_root host
    }) shadow_root_ptrs \<rightarrow>\<^sub>h h'"
    using \<open>h \<turnstile> flatten_dom \<rightarrow>\<^sub>h h'\<close>
    apply(auto simp add: flatten_dom_def elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF ElementMonad.ptr_kinds_M_pure, rotated]
        bind_returns_heap_E2[rotated, OF ShadowRootMonad.ptr_kinds_M_pure, rotated])[1]
    apply(drule pure_returns_heap_eq)
    by(auto intro!: map_filter_M2_pure bind_pure_I)

  have all_tups_slot: "\<And>slot assigned_nodes. (slot, assigned_nodes) \<in> set tups \<Longrightarrow>
h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
    using tups
    apply(induct element_ptrs arbitrary: tups)
    by(auto elim!: bind_returns_result_E2 split: if_splits intro!: map_filter_M2_pure bind_pure_I)

  have "distinct element_ptrs"
    using \<open>h \<turnstile> element_ptr_kinds_M \<rightarrow>\<^sub>r element_ptrs\<close>
    by auto
  then
  have "distinct tups"
    using tups
    apply(induct element_ptrs arbitrary: tups)
    by(auto elim!: bind_returns_result_E2 intro!: map_filter_M2_pure bind_pure_I
        split: option.splits if_splits intro: map_filter_pure_foo[rotated] )


  have "slot \<in> set element_ptrs"
    using assms(5) assigned_nodes_ptr_in_heap \<open>h \<turnstile> element_ptr_kinds_M \<rightarrow>\<^sub>r element_ptrs\<close>
    by auto
  then
  have "(slot, nodes) \<in> set tups"
    apply(rule map_filter_M2_in_result[OF tups])
    apply(auto intro!: bind_pure_I)[1]
    apply(intro bind_pure_returns_result_I)
    using assms assigned_nodes_slot_is_slot
    by(auto intro!: bind_pure_returns_result_I)

  have "\<And>slot nodes. (slot, nodes) \<in> set tups \<Longrightarrow> h \<turnstile> assigned_nodes slot \<rightarrow>\<^sub>r nodes"
    using tups
    apply(induct element_ptrs arbitrary: tups)
    by(auto elim!: bind_returns_result_E2 intro!: map_filter_M2_pure bind_pure_I split: if_splits)
  then
  have elementwise_eq: "\<And>slot slot' nodes nodes'. (slot, nodes) \<in> set tups \<Longrightarrow>
(slot', nodes') \<in> set tups \<Longrightarrow> slot = slot' \<Longrightarrow> nodes = nodes'"
    by (meson returns_result_eq)

  have "\<And>slot nodes. (slot, nodes) \<in> set tups \<Longrightarrow> distinct nodes"
    using \<open>\<And>slot nodes. (slot, nodes) \<in> set tups \<Longrightarrow> h \<turnstile> assigned_nodes slot \<rightarrow>\<^sub>r nodes\<close>
      assigned_nodes_distinct
    using assms(1) by blast

  have "\<And>slot slot' nodes nodes'. (slot, nodes) \<in> set tups \<Longrightarrow> (slot', nodes') \<in> set tups \<Longrightarrow>
slot \<noteq> slot' \<Longrightarrow> set nodes \<inter> set nodes' = {}"
    using \<open>\<And>slot nodes. (slot, nodes) \<in> set tups \<Longrightarrow> h \<turnstile> assigned_nodes slot \<rightarrow>\<^sub>r nodes\<close>
      assigned_nodes_different_ptr assms(1) assms(2) assms(3) by blast

  have "h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
    using \<open>(slot, nodes) \<in> set tups\<close> all_tups_slot by blast
  then have "h2 \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
    using h2
  proof(induct tups arbitrary: h, simp)
    case (Cons x xs)
    obtain xc ha hb slot' nodes' where
      "x = (slot', nodes')" and
      "h \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot') \<rightarrow>\<^sub>r xc" and
      ha: "h \<turnstile> forall_M remove xc \<rightarrow>\<^sub>h ha" and
      hb: "ha \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot')) nodes' \<rightarrow>\<^sub>h hb" and
      remainder: "hb \<turnstile> forall_M (\<lambda>(slot, assigned_nodes). Heap_Error_Monad.bind
(get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot)) (\<lambda>x. Heap_Error_Monad.bind (forall_M remove x)
(\<lambda>_. forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot)) assigned_nodes))) xs \<rightarrow>\<^sub>h h2"
      using Cons(3)
      by (auto elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated] bind_returns_result_E
          bind_returns_result_E2[rotated, OF get_child_nodes_pure, rotated] split: prod.splits)

    have "ha \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
      using \<open>h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''\<close> ha
    proof(induct xc arbitrary: h, simp)
      case (Cons a yc)
      obtain hb1 where
        hb1: "h \<turnstile> remove a \<rightarrow>\<^sub>h hb1" and
        hba: "hb1 \<turnstile> forall_M remove yc \<rightarrow>\<^sub>h ha"
        using Cons
        by (auto elim!: bind_returns_heap_E)
      have "hb1 \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
        using \<open>h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''\<close> hb1
        by(auto simp add: remove_child_locs_def set_child_nodes_get_tag_name
            set_disconnected_nodes_get_tag_name
            dest!: reads_writes_separate_forwards[OF get_tag_name_reads remove_writes])
      then show ?case
        using hba Cons(1) by simp
    qed
    then
    have "hb \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
      using hb
    proof (induct nodes' arbitrary: ha, simp)
      case (Cons a nodes')
      obtain ha1 where
        ha1: "ha \<turnstile> append_child (cast slot') a \<rightarrow>\<^sub>h ha1" and
        hb: "ha1 \<turnstile> forall_M (append_child (cast slot')) nodes' \<rightarrow>\<^sub>h hb"
        using Cons
        by (auto elim!: bind_returns_heap_E)
      have "ha1 \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
        using \<open>ha \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''\<close> ha1
        by(auto simp add: append_child_def insert_before_locs_def adopt_node_locs_def
            adopt_node_locs_def remove_child_locs_def set_child_nodes_get_tag_name
            set_disconnected_nodes_get_tag_name
            dest!: reads_writes_separate_forwards[OF get_tag_name_reads insert_before_writes]
            split: if_splits)
      then show ?case
        using ha1 hb Cons(1)
        by simp
    qed
    then
    show ?case
      using Cons(1) remainder by simp
  qed

  have "h2 \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes \<and> heap_is_wellformed h2 \<and> type_wf h2 \<and> known_ptrs h2"
    using \<open>(slot, nodes) \<in> set tups\<close>
    using h2 assms(1) assms(2) assms(3) \<open>distinct tups\<close> all_tups_slot elementwise_eq
    using \<open>\<And>slot slot' assigned_nodes nodes'. (slot, assigned_nodes) \<in> set tups \<Longrightarrow>
(slot', nodes') \<in> set tups \<Longrightarrow> slot \<noteq> slot' \<Longrightarrow> set assigned_nodes \<inter> set nodes' = {}\<close>
    using \<open>\<And>slot assigned_nodes. (slot, assigned_nodes) \<in> set tups \<Longrightarrow> distinct assigned_nodes\<close>
  proof(induct tups arbitrary: h, simp)
    case (Cons x xs)
    obtain xc ha hb slot' nodes' where
      "x = (slot', nodes')" and
      "h \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot') \<rightarrow>\<^sub>r xc" and
      ha: "h \<turnstile> forall_M remove xc \<rightarrow>\<^sub>h ha" and
      hb: "ha \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot')) nodes' \<rightarrow>\<^sub>h hb" and
      remainder: "hb \<turnstile> forall_M (\<lambda>(slot, assigned_nodes). Heap_Error_Monad.bind
(get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot)) (\<lambda>x. Heap_Error_Monad.bind (forall_M remove x)
(\<lambda>_. forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot)) assigned_nodes))) xs \<rightarrow>\<^sub>h h2"
      using Cons(3)
      by (auto elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated] bind_returns_result_E
          bind_returns_result_E2[rotated, OF get_child_nodes_pure, rotated] split: prod.splits)

    have "\<And>slot assigned_nodes. (slot, assigned_nodes) \<in> set xs \<Longrightarrow> h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
      using Cons by auto

    have "heap_is_wellformed ha" and "type_wf ha" and "known_ptrs ha"
      using Cons(4) Cons(5) Cons(6) \<open>h \<turnstile> forall_M remove xc \<rightarrow>\<^sub>h ha\<close>
      apply(induct xc arbitrary: h)
      apply(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
          simp add: remove_def split: option.splits)[1]
      apply(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
          simp add: remove_def split: option.splits)[1]
      apply(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
          simp add: remove_def split: option.splits)[1]
      apply(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
          simp add: remove_def split: option.splits)[1]
      apply (meson local.remove_child_heap_is_wellformed_preserved local.remove_child_preserves_known_ptrs
          local.remove_child_preserves_type_wf)
      apply(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
          simp add: remove_def split: option.splits)[1]
      apply (meson local.remove_child_heap_is_wellformed_preserved local.remove_child_preserves_known_ptrs
          local.remove_child_preserves_type_wf)
      apply(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
          simp add: remove_def split: option.splits)[1]
      using remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
        remove_child_preserves_known_ptrs apply metis
      done
    then
    have "heap_is_wellformed hb" and "type_wf hb" and "known_ptrs hb"
      using \<open>ha \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot')) nodes' \<rightarrow>\<^sub>h hb\<close>
      apply(induct nodes' arbitrary: ha)
      apply(auto elim!: bind_returns_heap_E simp add: append_child_def)[1]
      apply(auto elim!: bind_returns_heap_E simp add: append_child_def)[1]
      apply(auto elim!: bind_returns_heap_E simp add: append_child_def)[1]
      apply(auto elim!: bind_returns_heap_E simp add: append_child_def)[1]
      apply (metis insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
          insert_before_preserves_known_ptrs)
      apply(auto elim!: bind_returns_heap_E simp add: append_child_def)[1]
      apply (metis insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
          insert_before_preserves_known_ptrs)
      apply(auto elim!: bind_returns_heap_E simp add: append_child_def)[1]
      apply (metis insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
          insert_before_preserves_known_ptrs)
      done

    {
      fix slot assigned_nodes
      assume "(slot, assigned_nodes) \<in> set xs"
      then have "h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
        using \<open>\<And>slot assigned_nodes. (slot, assigned_nodes) \<in> set xs \<Longrightarrow>
h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''\<close>
        by auto
      then have "ha \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
        using \<open>h \<turnstile> forall_M remove xc \<rightarrow>\<^sub>h ha\<close>
        apply(induct xc arbitrary: h)
        by(auto simp add: remove_child_locs_def set_child_nodes_get_tag_name
            set_disconnected_nodes_get_tag_name
            dest!: reads_writes_separate_forwards[OF get_tag_name_reads remove_writes]
            elim!: bind_returns_heap_E)
      then have "hb \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
        using \<open>ha \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot')) nodes' \<rightarrow>\<^sub>h hb\<close>
        apply(induct nodes' arbitrary: ha)
        by(auto simp add: append_child_def insert_before_locs_def adopt_node_locs_def adopt_node_locs_def
            remove_child_locs_def set_child_nodes_get_tag_name set_disconnected_nodes_get_tag_name
            dest!: reads_writes_separate_forwards[OF get_tag_name_reads insert_before_writes]
            elim!: bind_returns_heap_E
            split: if_splits)
    } note tag_names_same = this

    show ?case
    proof(cases "slot' = slot")
      case True
      then
      have "nodes' = nodes"
        using Cons.prems(1) Cons.prems(8) \<open>x = (slot', nodes')\<close>
        by (metis list.set_intros(1))
      then
      have "(slot, nodes) \<notin> set xs"
        using Cons.prems(6) True \<open>x = (slot', nodes')\<close> by auto

      have "ha \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r []"
        using remove_for_all_empty_children Cons.prems(3) Cons.prems(4) Cons.prems(5) True
          \<open>h \<turnstile> forall_M remove xc \<rightarrow>\<^sub>h ha\<close>
        using \<open>h \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot') \<rightarrow>\<^sub>r xc\<close>
        by blast
      then
      have "hb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes"
        using  append_child_for_all_on_no_children[OF \<open>heap_is_wellformed hb\<close> \<open>type_wf hb\<close> \<open>known_ptrs hb\<close>]
          True \<open>nodes' = nodes\<close>
        using \<open>ha \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot')) nodes' \<rightarrow>\<^sub>h hb\<close>
        using \<open>(slot, nodes) \<in> set tups\<close> \<open>\<And>slot assigned_nodes. (slot, assigned_nodes) \<in> set tups \<Longrightarrow>
distinct assigned_nodes\<close> \<open>heap_is_wellformed ha\<close> \<open>known_ptrs ha\<close> \<open>type_wf ha\<close>
          local.append_child_for_all_on_no_children
        by blast
      with \<open>heap_is_wellformed hb\<close> and \<open>type_wf hb\<close> and \<open>known_ptrs hb\<close>
      show ?thesis
        using \<open>(slot, nodes) \<notin> set xs\<close> remainder
        using \<open>\<And>slot slot' assigned_nodes nodes'. (slot, assigned_nodes) \<in> set (x#xs) \<Longrightarrow>
(slot', nodes') \<in> set (x#xs) \<Longrightarrow> slot = slot' \<Longrightarrow> assigned_nodes = nodes'\<close>
        using \<open>(slot, nodes) \<in> set (x # xs)\<close>
        using \<open>\<And>slot slot' assigned_nodes nodes'. (slot, assigned_nodes) \<in> set (x#xs) \<Longrightarrow>
(slot', nodes') \<in> set (x#xs) \<Longrightarrow> slot \<noteq> slot' \<Longrightarrow> set assigned_nodes \<inter> set nodes' = {}\<close>
      proof(induct xs arbitrary: hb, simp)
        case (Cons y ys)
        obtain yc hba hbb slot'' nodes'' where
          "y = (slot'', nodes'')" and
          "hb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot'') \<rightarrow>\<^sub>r yc" and
          "hb \<turnstile> forall_M remove yc \<rightarrow>\<^sub>h hba" and
          "hba \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot'')) nodes'' \<rightarrow>\<^sub>h hbb" and
          remainder: "hbb \<turnstile> forall_M (\<lambda>(slot, assigned_nodes). Heap_Error_Monad.bind
(get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot)) (\<lambda>x. Heap_Error_Monad.bind (forall_M remove x)
(\<lambda>_. forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot)) assigned_nodes))) ys \<rightarrow>\<^sub>h h2"
          using Cons(7)
          by (auto elim!: bind_returns_heap_E
              bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated] split: prod.splits)

        have "slot \<noteq> slot''"
          by (metis Cons.prems(5) Cons.prems(7) Cons.prems(8) \<open>y = (slot'', nodes'')\<close>
              list.set_intros(1) list.set_intros(2))
        then have "set nodes \<inter> set nodes'' = {}"
          by (metis Cons.prems(8) Cons.prems(9) \<open>y = (slot'', nodes'')\<close> list.set_intros(1)
              list.set_intros(2))

        have "hba \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes \<and>
heap_is_wellformed hba \<and> type_wf hba \<and> known_ptrs hba"
          using \<open>hb \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes\<close>
          using \<open>hb \<turnstile> forall_M remove yc \<rightarrow>\<^sub>h hba\<close>
          using \<open>hb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot'') \<rightarrow>\<^sub>r yc\<close>
          using \<open>heap_is_wellformed hb\<close> \<open>type_wf hb\<close> \<open>known_ptrs hb\<close>
        proof(induct yc arbitrary: hb, simp)
          case (Cons a yc)
          obtain hb1 where
            hb1: "hb \<turnstile> remove a \<rightarrow>\<^sub>h hb1" and
            hba: "hb1 \<turnstile> forall_M remove yc \<rightarrow>\<^sub>h hba"
            using Cons
            by (auto elim!: bind_returns_heap_E)
          have "hb \<turnstile> get_parent a \<rightarrow>\<^sub>r Some (cast slot'')"
            using Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) local.child_parent_dual
            by auto

          moreover
          have "heap_is_wellformed hb1" and "type_wf hb1" and "known_ptrs hb1"
            using \<open>hb \<turnstile> remove a \<rightarrow>\<^sub>h hb1\<close>
            apply(auto simp add: remove_def elim!: bind_returns_heap_E
                bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
            using \<open>heap_is_wellformed hb\<close> and \<open>type_wf hb\<close> and \<open>known_ptrs hb\<close>
              remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
              remove_child_preserves_known_ptrs
            apply blast
            using \<open>heap_is_wellformed hb\<close> and \<open>type_wf hb\<close> and \<open>known_ptrs hb\<close>
              remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
              remove_child_preserves_known_ptrs
            apply blast
            using \<open>hb \<turnstile> remove a \<rightarrow>\<^sub>h hb1\<close>
            apply(auto simp add: remove_def elim!: bind_returns_heap_E
                bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
            using \<open>heap_is_wellformed hb\<close> and \<open>type_wf hb\<close> and \<open>known_ptrs hb\<close>
              remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
              remove_child_preserves_known_ptrs
            apply blast
            using \<open>heap_is_wellformed hb\<close> and \<open>type_wf hb\<close> and \<open>known_ptrs hb\<close>
              remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
              remove_child_preserves_known_ptrs
            apply blast
            using \<open>hb \<turnstile> remove a \<rightarrow>\<^sub>h hb1\<close>
            apply(auto simp add: remove_def elim!: bind_returns_heap_E
                bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
            using \<open>heap_is_wellformed hb\<close> and \<open>type_wf hb\<close> and \<open>known_ptrs hb\<close>
              remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
              remove_child_preserves_known_ptrs
            apply blast
            using \<open>heap_is_wellformed hb\<close> and \<open>type_wf hb\<close> and \<open>known_ptrs hb\<close>
              remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
              remove_child_preserves_known_ptrs
            apply blast
            done
          moreover have "hb1 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot'') \<rightarrow>\<^sub>r yc"
            using \<open>hb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot'') \<rightarrow>\<^sub>r a # yc\<close> hb1
            using remove_removes_child \<open>heap_is_wellformed hb\<close> \<open>type_wf hb\<close> \<open>known_ptrs hb\<close>
            by simp
          moreover have "hb1 \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes"
            using Cons(2) hb1 set_child_nodes_get_child_nodes_different_pointers
              \<open>hb \<turnstile> get_parent a \<rightarrow>\<^sub>r Some (cast slot'')\<close> \<open>slot \<noteq> slot''\<close>
            apply(auto simp add: remove_child_locs_def elim!: bind_returns_heap_E
                dest!: reads_writes_separate_forwards[OF get_child_nodes_reads remove_writes])[1]
            by (metis cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject)
          ultimately show ?thesis
            using \<open>hb1 \<turnstile> forall_M remove (yc) \<rightarrow>\<^sub>h hba\<close> Cons
            by auto
        qed


        then have "hbb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes \<and>
heap_is_wellformed hbb \<and> type_wf hbb \<and> known_ptrs hbb"
          using \<open>hba \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot'')) nodes'' \<rightarrow>\<^sub>h hbb\<close>
          using \<open>set nodes \<inter> set nodes'' = {}\<close>
        proof(induct nodes'' arbitrary: hba, simp)
          case (Cons a nodes'')
          then have "hba \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes" and
            "heap_is_wellformed hba" and
            "type_wf hba" and
            "known_ptrs hba"
            by auto
          obtain hba1 where
            hba1: "hba \<turnstile> append_child (cast slot'') a \<rightarrow>\<^sub>h hba1" and
            "hba1 \<turnstile> forall_M (append_child (cast slot'')) nodes'' \<rightarrow>\<^sub>h hbb"
            using Cons(3)
            by (auto elim!: bind_returns_heap_E)

          have "heap_is_wellformed hba1" and "type_wf hba1" and "known_ptrs hba1"
            using \<open>hba \<turnstile> append_child (cast slot'') a \<rightarrow>\<^sub>h hba1\<close>
            apply(auto simp add: append_child_def)[1]
            using \<open>heap_is_wellformed hba\<close> and \<open>type_wf hba\<close> and \<open>known_ptrs hba\<close>
              insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
              insert_before_preserves_known_ptrs
            apply blast
            using \<open>hba \<turnstile> append_child (cast slot'') a \<rightarrow>\<^sub>h hba1\<close>
            apply(auto simp add: append_child_def)[1]
            using \<open>heap_is_wellformed hba\<close> and \<open>type_wf hba\<close> and \<open>known_ptrs hba\<close>
              insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
              insert_before_preserves_known_ptrs
            apply blast
            using \<open>hba \<turnstile> append_child (cast slot'') a \<rightarrow>\<^sub>h hba1\<close>
            apply(auto simp add: append_child_def)[1]
            using \<open>heap_is_wellformed hba\<close> and \<open>type_wf hba\<close> and \<open>known_ptrs hba\<close>
              insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
              insert_before_preserves_known_ptrs
            apply blast
            done

          moreover
          have "a \<notin> set nodes"
            using \<open>set nodes \<inter> set (a # nodes'') = {}\<close>
            by auto


          moreover
          obtain parent_opt where "hba \<turnstile> get_parent a \<rightarrow>\<^sub>r parent_opt"
            using insert_before_child_in_heap hba1 get_parent_ok unfolding append_child_def
            by (meson Cons.prems(1) is_OK_returns_heap_I is_OK_returns_result_E)
          then
          have "hba1 \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes"
          proof (induct parent_opt)
            case None
            then show ?case
              using \<open>hba \<turnstile> append_child (cast slot'') a \<rightarrow>\<^sub>h hba1\<close>
              using \<open>hba \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes\<close>
              using \<open>slot \<noteq> slot''\<close>
              apply(auto simp add: append_child_def insert_before_locs_def adopt_node_locs_def
                  adopt_node_locs_def remove_child_locs_def
                  elim!: reads_writes_separate_forwards[OF get_child_nodes_reads insert_before_writes])[1]
              by (metis cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject
                  set_child_nodes_get_child_nodes_different_pointers)
          next
            case (Some parent)
            have "parent \<noteq> cast slot"
              apply(rule ccontr, simp)
              using Cons(2)
              apply -
              apply(rule get_parent_child_dual[OF \<open>hba \<turnstile> get_parent a \<rightarrow>\<^sub>r Some parent\<close>])
              apply(auto)[1]
              using \<open>a \<notin> set nodes\<close> returns_result_eq
              by fastforce
            show ?case
              apply(rule reads_writes_separate_forwards)
              apply(fact get_child_nodes_reads)
              apply(fact insert_before_writes)
              apply(fact \<open>hba \<turnstile> append_child (cast slot'') a \<rightarrow>\<^sub>h hba1\<close>[unfolded append_child_def])
              apply(fact \<open>hba \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes\<close>)
              using \<open>hba \<turnstile> get_parent a \<rightarrow>\<^sub>r Some parent\<close> \<open>parent \<noteq> cast slot\<close> \<open>slot \<noteq> slot''\<close>
              apply(auto simp add: insert_before_locs_def adopt_node_locs_def adopt_node_locs_def
                  remove_child_locs_def)[1]
              apply (simp_all add: set_child_nodes_get_child_nodes_different_pointers
                  set_disconnected_nodes_get_child_nodes)
              by (metis cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject
                  set_child_nodes_get_child_nodes_different_pointers)
          qed
          moreover
          have "set nodes \<inter> set nodes'' = {}"
            using Cons.prems(3) by auto
          ultimately show ?case
            using Cons.hyps  \<open>hba1 \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot'')) nodes'' \<rightarrow>\<^sub>h hbb\<close>
            by blast
        qed
        show ?case
          apply(rule Cons(1))
          using \<open>hbb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes \<and>
heap_is_wellformed hbb \<and> type_wf hbb \<and> known_ptrs hbb\<close>
          apply(auto)[1]
          using \<open>hbb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes \<and>
heap_is_wellformed hbb \<and> type_wf hbb \<and> known_ptrs hbb\<close>
          apply(auto)[1]
          using \<open>hbb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes \<and>
heap_is_wellformed hbb \<and> type_wf hbb \<and> known_ptrs hbb\<close>
          apply(auto)[1]
          using \<open>hbb \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes \<and>
heap_is_wellformed hbb \<and> type_wf hbb \<and> known_ptrs hbb\<close>
          apply(auto)[1]
          using Cons.prems(5) apply auto[1]
          apply (simp add: remainder)
          using Cons.prems(7) apply auto[1]
          apply (simp add: True \<open>nodes' = nodes\<close> \<open>x = (slot', nodes')\<close>)
          by (metis Cons.prems(9) insert_iff list.simps(15))
      qed
    next
      case False
      then have "nodes' \<noteq> nodes"
        using Cons.prems(1) Cons.prems(9) \<open>x = (slot', nodes')\<close>
        by (metis assms(6) inf.idem list.set_intros(1) set_empty2)
      then
      have "(slot, nodes) \<in> set xs"
        using Cons.prems(1) \<open>x = (slot', nodes')\<close>
        by auto
      then show ?thesis
        using Cons(1)[simplified, OF \<open>(slot, nodes) \<in> set xs\<close> remainder
            \<open>heap_is_wellformed hb\<close> \<open>type_wf hb\<close> \<open>known_ptrs hb\<close>]
        using Cons.prems(6) tag_names_same  Cons.prems(8) Cons.prems(9)
        by (smt Cons.prems(10) distinct.simps(2) list.set_intros(2))
    qed
  qed
  then
  show ?thesis
    using h' \<open>h2 \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''\<close>
  proof(induct shadow_root_ptrs arbitrary: h2, simp)
    case (Cons shadow_root_ptr shadow_root_ptrs)
    then have "h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes" and
      "heap_is_wellformed h2" and
      "type_wf h2" and
      "known_ptrs h2"
      by auto
    obtain host h2a h2b h2c host_children shadow_root_children where
      "h2 \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host" and
      "h2 \<turnstile> get_child_nodes (cast host) \<rightarrow>\<^sub>r host_children" and
      h2a: "h2 \<turnstile> forall_M remove host_children \<rightarrow>\<^sub>h h2a" and
      "h2a \<turnstile> get_child_nodes (cast shadow_root_ptr) \<rightarrow>\<^sub>r shadow_root_children" and
      h2b: "h2a \<turnstile> forall_M (append_child (cast host)) shadow_root_children \<rightarrow>\<^sub>h h2b" and
      "h2b \<turnstile> remove_shadow_root host \<rightarrow>\<^sub>h h2c" and
      remainder: "h2c \<turnstile> forall_M(\<lambda>shadow_root_ptr. Heap_Error_Monad.bind (get_host shadow_root_ptr)
        (\<lambda>host. Heap_Error_Monad.bind (get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host))
             (\<lambda>x. Heap_Error_Monad.bind (forall_M remove x)
               (\<lambda>_. Heap_Error_Monad.bind (get_child_nodes (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr))
                    (\<lambda>x. Heap_Error_Monad.bind (forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host)) x)
                           (\<lambda>_. remove_shadow_root host))))))
           shadow_root_ptrs
       \<rightarrow>\<^sub>h h'"
      using Cons(3)
      by(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_host_pure, rotated]
          bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated])


    have "h2 \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
      using \<open>h2 \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host\<close> shadow_root_host_dual
      using \<open>heap_is_wellformed h2\<close> \<open>type_wf h2\<close> by blast
    then have "h2a \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
      using \<open>h2 \<turnstile> forall_M remove host_children \<rightarrow>\<^sub>h h2a\<close>
      apply(induct host_children arbitrary: h2)
      by(auto simp add: set_disconnected_nodes_get_shadow_root set_child_nodes_get_shadow_root
          remove_child_locs_def elim!: bind_returns_heap_E
          dest!: reads_writes_separate_forwards[OF get_shadow_root_reads remove_writes])
    then have "h2b \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
      using \<open>h2a \<turnstile> forall_M (append_child (cast host)) shadow_root_children \<rightarrow>\<^sub>h h2b\<close>
      apply(induct shadow_root_children arbitrary: h2a)
      by(auto simp add: set_disconnected_nodes_get_shadow_root set_child_nodes_get_shadow_root
          append_child_def insert_before_locs_def adopt_node_locs_def adopt_node_locs_def remove_child_locs_def
          elim!: bind_returns_heap_E dest!: reads_writes_separate_forwards[OF get_shadow_root_reads insert_before_writes]
          split: if_splits)

    have "host \<noteq> slot"
    proof (rule ccontr, simp)
      assume "host = slot"
      show False
        using get_host_valid_tag_name[OF \<open>heap_is_wellformed h2\<close> \<open>type_wf h2\<close>
            \<open>h2 \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host\<close>[unfolded \<open>host = slot\<close>] \<open>h2 \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''\<close>]
        by(simp)
    qed

    have "heap_is_wellformed h2a" and "type_wf h2a" and "known_ptrs h2a"
      using \<open>heap_is_wellformed h2\<close> and \<open>type_wf h2\<close> and \<open>known_ptrs h2\<close>
        \<open>h2 \<turnstile> forall_M remove host_children \<rightarrow>\<^sub>h h2a\<close>
      apply(induct host_children arbitrary: h2)
      apply(auto simp add: remove_def elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
      apply(auto simp add: remove_def elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
      apply(auto simp add: remove_def elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
      apply(auto simp add: remove_def elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
      using remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
        remove_child_preserves_known_ptrs apply metis
      apply(auto simp add: remove_def elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
      using remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
        remove_child_preserves_known_ptrs apply metis
      apply(auto simp add: remove_def elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
      using remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
        remove_child_preserves_known_ptrs apply metis
      done
    then
    have "heap_is_wellformed h2b" and "type_wf h2b" and "known_ptrs h2b"
      using \<open>h2a \<turnstile> forall_M (append_child (cast host)) shadow_root_children \<rightarrow>\<^sub>h h2b\<close>
      apply(induct shadow_root_children arbitrary: h2a)
      apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
      apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
      apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
      apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
      using insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
        insert_before_preserves_known_ptrs apply metis
      apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
      using insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
        insert_before_preserves_known_ptrs apply metis
      apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
      using insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
        insert_before_preserves_known_ptrs apply metis
      done
    then
    have "heap_is_wellformed h2c" and "type_wf h2c" and "known_ptrs h2c"
      using remove_shadow_root_preserves \<open>h2b \<turnstile> remove_shadow_root host \<rightarrow>\<^sub>h h2c\<close>
      by blast+

    moreover
    have "h2a \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes"
      using \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes\<close>
      using \<open>h2 \<turnstile> forall_M remove host_children \<rightarrow>\<^sub>h h2a\<close>
      using \<open>h2 \<turnstile> get_child_nodes (cast host) \<rightarrow>\<^sub>r host_children\<close>
      using \<open>heap_is_wellformed h2\<close> \<open>type_wf h2\<close> \<open>known_ptrs h2\<close>
    proof (induct host_children arbitrary: h2, simp)
      case (Cons a host_children)
      obtain h21 where "h2 \<turnstile> remove a \<rightarrow>\<^sub>h h21" and
        "h21 \<turnstile> forall_M remove host_children \<rightarrow>\<^sub>h h2a"
        using Cons(3)
        by(auto elim!: bind_returns_heap_E)

      have "heap_is_wellformed h21" and "type_wf h21" and "known_ptrs h21"
        using \<open>heap_is_wellformed h2\<close> and \<open>type_wf h2\<close> and \<open>known_ptrs h2\<close> \<open>h2 \<turnstile> remove a \<rightarrow>\<^sub>h h21\<close>
        apply(auto simp add: remove_def elim!: bind_returns_heap_E
            bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
        using remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
          remove_child_preserves_known_ptrs apply (metis)
        using \<open>heap_is_wellformed h2\<close> and \<open>type_wf h2\<close> and \<open>known_ptrs h2\<close> \<open>h2 \<turnstile> remove a \<rightarrow>\<^sub>h h21\<close>
        apply(auto simp add: remove_def elim!: bind_returns_heap_E
            bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
        using remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
          remove_child_preserves_known_ptrs apply (metis)
        using \<open>heap_is_wellformed h2\<close> and \<open>type_wf h2\<close> and \<open>known_ptrs h2\<close> \<open>h2 \<turnstile> remove a \<rightarrow>\<^sub>h h21\<close>
        apply(auto simp add: remove_def elim!: bind_returns_heap_E
            bind_returns_heap_E2[rotated, OF get_parent_pure, rotated] split: option.splits)[1]
        using remove_child_heap_is_wellformed_preserved remove_child_preserves_type_wf
          remove_child_preserves_known_ptrs apply (metis)
        done
      have "h2 \<turnstile> get_parent a \<rightarrow>\<^sub>r Some (cast host)"
        using \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) \<rightarrow>\<^sub>r a # host_children\<close>
        using \<open>heap_is_wellformed h2\<close> \<open>type_wf h2\<close> \<open>known_ptrs h2\<close> child_parent_dual
        using heap_is_wellformed_def by auto
      then have "h21 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes"
        using \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes\<close> \<open>host \<noteq> slot\<close>
        using \<open>h2 \<turnstile> remove a \<rightarrow>\<^sub>h h21\<close>
        apply(auto simp add: remove_child_locs_def set_disconnected_nodes_get_child_nodes
            dest!: reads_writes_preserved[OF get_child_nodes_reads remove_writes])[1]
        by (meson cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject
            set_child_nodes_get_child_nodes_different_pointers)
      moreover have "h21 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) \<rightarrow>\<^sub>r host_children"
        using \<open>h2 \<turnstile> remove a \<rightarrow>\<^sub>h h21\<close>  remove_removes_child[OF \<open>heap_is_wellformed h2\<close> \<open>type_wf h2\<close>
            \<open>known_ptrs h2\<close> \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) \<rightarrow>\<^sub>r a # host_children\<close>]
        by blast
      ultimately show ?case
        using \<open>heap_is_wellformed h21\<close> and \<open>type_wf h21\<close> and \<open>known_ptrs h21\<close>
          \<open>h21 \<turnstile> forall_M remove host_children \<rightarrow>\<^sub>h h2a\<close> Cons(1)
        using Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) heap_is_wellformed_def
          \<open>h2 \<turnstile> remove a \<rightarrow>\<^sub>h h21\<close> remove_removes_child
        by blast
    qed

    then
    have "h2b \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes"
      using \<open>h2a \<turnstile> forall_M (append_child (cast host)) shadow_root_children \<rightarrow>\<^sub>h h2b\<close>
      using \<open>h2a \<turnstile> get_child_nodes (cast shadow_root_ptr) \<rightarrow>\<^sub>r shadow_root_children\<close>
      using \<open>heap_is_wellformed h2a\<close> \<open>type_wf h2a\<close> \<open>known_ptrs h2a\<close>
    proof(induct shadow_root_children arbitrary: h2a, simp)
      case (Cons a shadow_root_children)
      obtain h2a1 where "h2a \<turnstile> append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) a \<rightarrow>\<^sub>h h2a1" and
        "h2a1 \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host)) (shadow_root_children) \<rightarrow>\<^sub>h h2b"
        using Cons(3)
        by(auto elim!: bind_returns_heap_E)

      have "heap_is_wellformed h2a1" and "type_wf h2a1" and "known_ptrs h2a1"
        using \<open>heap_is_wellformed h2a\<close> and \<open>type_wf h2a\<close> and \<open>known_ptrs h2a\<close>
          \<open>h2a \<turnstile> append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) a \<rightarrow>\<^sub>h h2a1\<close>
        apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
        using insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
          insert_before_preserves_known_ptrs apply metis
        using \<open>heap_is_wellformed h2a\<close> and \<open>type_wf h2a\<close> and \<open>known_ptrs h2a\<close>
          \<open>h2a \<turnstile> append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) a \<rightarrow>\<^sub>h h2a1\<close>
        apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
        using insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
          insert_before_preserves_known_ptrs apply metis
        using \<open>heap_is_wellformed h2a\<close> and \<open>type_wf h2a\<close> and \<open>known_ptrs h2a\<close>
          \<open>h2a \<turnstile> append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) a \<rightarrow>\<^sub>h h2a1\<close>
        apply(auto simp add: append_child_def elim!: bind_returns_heap_E)[1]
        using insert_before_heap_is_wellformed_preserved insert_before_preserves_type_wf
          insert_before_preserves_known_ptrs apply metis
        done
      moreover have "h2a1 \<turnstile> get_child_nodes (cast shadow_root_ptr) \<rightarrow>\<^sub>r shadow_root_children"
        using \<open>h2a \<turnstile> get_child_nodes (cast shadow_root_ptr) \<rightarrow>\<^sub>r a # shadow_root_children\<close>
        using insert_before_removes_child
          \<open>h2a \<turnstile> append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) a \<rightarrow>\<^sub>h h2a1\<close>[unfolded append_child_def]
        using \<open>heap_is_wellformed h2a\<close> \<open>type_wf h2a\<close> \<open>known_ptrs h2a\<close>
        using cast_document_ptr_not_node_ptr(2)
        using cast_shadow_root_ptr_not_node_ptr(2) by blast
      moreover have "h2a \<turnstile> get_parent a \<rightarrow>\<^sub>r Some (cast shadow_root_ptr)"
        using \<open>h2a \<turnstile> get_child_nodes (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) \<rightarrow>\<^sub>r a # shadow_root_children\<close>
        using \<open>heap_is_wellformed h2a\<close> \<open>type_wf h2a\<close> \<open>known_ptrs h2a\<close> child_parent_dual
        using heap_is_wellformed_def by auto
      then have "h2a1 \<turnstile> get_child_nodes (cast slot) \<rightarrow>\<^sub>r nodes"
        using \<open>h2a \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes\<close>
        using \<open>h2a \<turnstile> append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) a \<rightarrow>\<^sub>h h2a1\<close> \<open>host \<noteq> slot\<close>
        apply(auto simp add:  set_disconnected_nodes_get_child_nodes append_child_def
            insert_before_locs_def adopt_node_locs_def adopt_node_locs_def remove_child_locs_def
            elim!: bind_returns_heap_E dest!: reads_writes_preserved[OF get_child_nodes_reads
              insert_before_writes])[1]
        using set_child_nodes_get_child_nodes_different_pointers cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject
          cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject cast_document_ptr_not_node_ptr(2)
        by (metis cast_shadow_root_ptr_not_node_ptr(2))+
      ultimately
      show ?case
        using Cons(1) \<open>h2a1 \<turnstile> forall_M (append_child (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host)) shadow_root_children \<rightarrow>\<^sub>h h2b\<close>
        by blast
    qed
    then
    have "h2c \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r slot) \<rightarrow>\<^sub>r nodes"
      using \<open>h2b \<turnstile> remove_shadow_root host \<rightarrow>\<^sub>h h2c\<close>
      apply(auto simp add: remove_shadow_root_get_child_nodes_different_pointers
          dest!: reads_writes_separate_forwards[OF get_child_nodes_reads remove_shadow_root_writes])[1]
      by (meson cast_shadow_root_ptr_not_node_ptr(2)
          local.remove_shadow_root_get_child_nodes_different_pointers)

    moreover
    have "h2a \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
      using h2a \<open>h2 \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''\<close>
      apply(induct host_children arbitrary: h2)
      by(auto simp add: remove_child_locs_def set_disconnected_nodes_get_tag_name
          set_child_nodes_get_tag_name dest!: reads_writes_separate_forwards[OF get_tag_name_reads remove_writes]
          elim!: bind_returns_heap_E)
    then
    have "h2b \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
      using h2b
      apply(induct shadow_root_children arbitrary: h2a)
      by(auto simp add: append_child_def insert_before_locs_def adopt_node_locs_def adopt_node_locs_def
          remove_child_locs_def set_disconnected_nodes_get_tag_name set_child_nodes_get_tag_name
          dest!: reads_writes_separate_forwards[OF get_tag_name_reads insert_before_writes]
          elim!: bind_returns_heap_E split: if_splits)
    then
    have "h2c \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
      using \<open>h2b \<turnstile> remove_shadow_root host \<rightarrow>\<^sub>h h2c\<close>
      by(auto simp add: remove_shadow_root_get_tag_name
          dest!: reads_writes_separate_forwards[OF get_tag_name_reads remove_shadow_root_writes])

    ultimately show ?case
      using Cons(1) remainder
      by auto
  qed
qed
end
interpretation i_assigned_nodes_component?: l_assigned_nodes_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf get_tag_name get_tag_name_locs known_ptr get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs
  heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs
  get_disconnected_document get_disconnected_document_locs get_parent get_parent_locs
  get_mode get_mode_locs get_attribute get_attribute_locs first_in_tree_order find_slot
  assigned_slot known_ptrs to_tree_order assigned_nodes assigned_nodes_flatten flatten_dom
  get_root_node get_root_node_locs remove insert_before insert_before_locs append_child
  remove_shadow_root remove_shadow_root_locs set_shadow_root set_shadow_root_locs remove_child
  remove_child_locs get_component is_strongly_dom_component_safe is_weakly_dom_component_safe
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name get_owner_document set_disconnected_nodes set_disconnected_nodes_locs
  adopt_node adopt_node_locs set_child_nodes set_child_nodes_locs
  by(auto simp add: l_assigned_nodes_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_assigned_nodes_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_owner\_document\<close>

locale l_get_owner_document_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_owner_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_owner_document_is_component_unsafe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
  assumes "\<not>is_document_ptr_kind |h \<turnstile> get_root_node ptr|\<^sub>r"
  shows "set |h \<turnstile> get_component ptr|\<^sub>r \<inter> set |h \<turnstile> get_component (cast owner_document)|\<^sub>r = {}"
proof -
  have "owner_document |\<in>| document_ptr_kinds h"
    using assms(1) assms(2) assms(3) assms(4) get_owner_document_owner_document_in_heap by blast
  have "ptr |\<in>| object_ptr_kinds h"
    by (meson assms(4) is_OK_returns_result_I local.get_owner_document_ptr_in_heap)
  obtain root where root: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
    by (meson assms(1) assms(2) assms(3) assms(4) is_OK_returns_result_I
        local.get_owner_document_ptr_in_heap local.get_root_node_ok returns_result_select_result)
  then obtain to where to: "h \<turnstile> to_tree_order root \<rightarrow>\<^sub>r to"
    by (meson assms(1) assms(2) assms(3) is_OK_returns_result_E local.get_root_node_root_in_heap
        local.to_tree_order_ok)
  then have "\<forall>p \<in> set to. \<not>is_document_ptr_kind p"
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(5) document_ptr_casts_commute3
        local.to_tree_order_node_ptrs node_ptr_no_document_ptr_cast root select_result_I2)
  then have "cast owner_document \<notin> set |h \<turnstile> get_component ptr|\<^sub>r"
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(5) document_ptr_document_ptr_cast
        is_OK_returns_result_I l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_component_ok local.get_component_root_node_same
        local.get_root_node_not_node_same local.get_root_node_ptr_in_heap local.l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms
        node_ptr_no_document_ptr_cast returns_result_select_result root select_result_I2)
  then have "|h \<turnstile> get_component ptr|\<^sub>r \<noteq> |h \<turnstile> get_component (cast owner_document)|\<^sub>r"
    by (metis (no_types, lifting) \<open>owner_document |\<in>| document_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        document_ptr_kinds_commutes l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_component_ok local.get_dom_component_ptr
        local.l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms returns_result_select_result)
  then show ?thesis
    by (meson \<open>owner_document |\<in>| document_ptr_kinds h\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1)
        assms(2) assms(3) document_ptr_kinds_commutes l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_dom_component_no_overlap
        l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_component_ok local.l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms returns_result_select_result)
qed

end
interpretation i_get_owner_document_component?: l_get_owner_document_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf get_disconnected_nodes get_disconnected_nodes_locs known_ptr get_child_nodes
  get_child_nodes_locs DocumentClass.known_ptr get_parent get_parent_locs get_root_node_si
  get_root_node_si_locs CD.a_get_owner_document get_host get_host_locs get_owner_document
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs heap_is_wellformed
  parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_document get_disconnected_document_locs
  known_ptrs get_ancestors_si get_ancestors_si_locs to_tree_order get_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name
  by(auto simp add: l_get_owner_document_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_owner_document_component\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

definition is_shadow_root_component :: "(_) object_ptr list \<Rightarrow> bool"
  where
    "is_shadow_root_component c = is_shadow_root_ptr_kind (hd c)"

end
