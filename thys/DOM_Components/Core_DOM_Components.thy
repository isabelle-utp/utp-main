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


section \<open>DOM Components\<close>

theory Core_DOM_Components
  imports Core_DOM.Core_DOM
begin


locale l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_root_node_defs get_root_node get_root_node_locs +
  l_to_tree_order_defs to_tree_order
  for get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
    and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and to_tree_order :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
begin

definition a_get_component :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  where
    "a_get_component ptr = do {
      root \<leftarrow> get_root_node ptr;
      to_tree_order root
    }"

definition a_is_strongly_dom_component_safe ::
  "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
  where
    "a_is_strongly_dom_component_safe S\<^sub>a\<^sub>r\<^sub>g S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t h h' = (
      let removed_pointers = fset (object_ptr_kinds h) - fset (object_ptr_kinds h') in
      let added_pointers = fset (object_ptr_kinds h') - fset (object_ptr_kinds h) in
      let arg_components =
        (\<Union>ptr \<in> (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h \<turnstile> a_get_component ptr|\<^sub>r) \<inter> fset (object_ptr_kinds h).
        set |h \<turnstile> a_get_component ptr|\<^sub>r) in
      let arg_components' =
        (\<Union>ptr \<in> (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h \<turnstile> a_get_component ptr|\<^sub>r) \<inter> fset (object_ptr_kinds h').
        set |h' \<turnstile> a_get_component ptr|\<^sub>r) in
      removed_pointers \<subseteq> arg_components \<and>
      added_pointers \<subseteq> arg_components' \<and>
      S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t \<subseteq> arg_components' \<and>
      (\<forall>outside_ptr \<in> fset (object_ptr_kinds h) \<inter> fset (object_ptr_kinds h') -
        (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h  \<turnstile> a_get_component ptr|\<^sub>r). preserved (get_M outside_ptr id) h h'))"

definition a_is_weakly_dom_component_safe ::
  "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
  where
    "a_is_weakly_dom_component_safe S\<^sub>a\<^sub>r\<^sub>g S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t h h' = (
      let removed_pointers = fset (object_ptr_kinds h) - fset (object_ptr_kinds h') in
      let added_pointers = fset (object_ptr_kinds h') - fset (object_ptr_kinds h) in
      let arg_components =
        (\<Union>ptr \<in> (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h \<turnstile> a_get_component ptr|\<^sub>r) \<inter> fset (object_ptr_kinds h).
        set |h \<turnstile> a_get_component ptr|\<^sub>r) in
      let arg_components' =
        (\<Union>ptr \<in> (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h \<turnstile> a_get_component ptr|\<^sub>r) \<inter> fset (object_ptr_kinds h').
        set |h' \<turnstile> a_get_component ptr|\<^sub>r) in
      removed_pointers \<subseteq> arg_components \<and>
      S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t \<subseteq> arg_components' \<union> added_pointers  \<and>
      (\<forall>outside_ptr \<in> fset (object_ptr_kinds h) \<inter> fset (object_ptr_kinds h') -
        (\<Union>ptr \<in> S\<^sub>a\<^sub>r\<^sub>g. set |h  \<turnstile> a_get_component ptr|\<^sub>r). preserved (get_M outside_ptr id) h h'))"

lemma "a_is_strongly_dom_component_safe S\<^sub>a\<^sub>r\<^sub>g S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t h h' \<Longrightarrow> a_is_weakly_dom_component_safe S\<^sub>a\<^sub>r\<^sub>g S\<^sub>r\<^sub>e\<^sub>s\<^sub>u\<^sub>l\<^sub>t h h'"
  by(auto simp add: a_is_strongly_dom_component_safe_def a_is_weakly_dom_component_safe_def Let_def)

definition is_document_component :: "(_) object_ptr list \<Rightarrow> bool"
  where
    "is_document_component c = is_document_ptr_kind (hd c)"

definition is_disconnected_component :: "(_) object_ptr list \<Rightarrow> bool"
  where
    "is_disconnected_component c = is_node_ptr_kind (hd c)"
end

global_interpretation l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_root_node get_root_node_locs to_tree_order
  defines get_component = a_get_component
    and is_strongly_dom_component_safe = a_is_strongly_dom_component_safe
    and is_weakly_dom_component_safe = a_is_weakly_dom_component_safe
  .


locale l_get_component_defs =
  fixes get_component :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  fixes is_strongly_dom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
  fixes is_weakly_dom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"

locale l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_to_tree_order_wf +
  l_get_component_defs +
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_ancestors +
  l_get_ancestors_wf +
  l_get_root_node +
  l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent +
  l_get_parent_wf +
  l_get_element_by +
  l_to_tree_order_wf_get_root_node_wf +
  (* l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ _ _ get_child_nodes +
  l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ _ get_child_nodes+
  l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ _ "l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.a_to_tree_order get_child_nodes"
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog" *)
  assumes get_component_impl: "get_component = a_get_component"
  assumes is_strongly_dom_component_safe_impl:
    "is_strongly_dom_component_safe = a_is_strongly_dom_component_safe"
  assumes is_weakly_dom_component_safe_impl:
    "is_weakly_dom_component_safe = a_is_weakly_dom_component_safe"
begin
lemmas get_component_def = a_get_component_def[folded get_component_impl]
lemmas is_strongly_dom_component_safe_def =
  a_is_strongly_dom_component_safe_def[folded is_strongly_dom_component_safe_impl]
lemmas is_weakly_dom_component_safe_def =
  a_is_weakly_dom_component_safe_def[folded is_weakly_dom_component_safe_impl]

lemma get_dom_component_ptr_in_heap:
  assumes "h \<turnstile> ok (get_component ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms get_root_node_ptr_in_heap
  by(auto simp add: get_component_def)

lemma get_component_ok:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (get_component ptr)"
  using assms
  apply(auto simp add: get_component_def a_get_root_node_def intro!: bind_is_OK_pure_I)[1]
  using get_root_node_ok  to_tree_order_ok get_root_node_ptr_in_heap
   apply blast
  by (simp add: local.get_root_node_root_in_heap local.to_tree_order_ok)

lemma get_dom_component_ptr:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  shows "ptr \<in> set c"
proof(insert assms(1) assms(4), induct ptr rule: heap_wellformed_induct_rev )
  case (step child)
  then show ?case
  proof (cases "is_node_ptr_kind child")
    case True
    obtain node_ptr where
      node_ptr: "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr = child"
      using \<open>is_node_ptr_kind child\<close> node_ptr_casts_commute3 by blast
    have "child |\<in>| object_ptr_kinds h"
      using \<open>h \<turnstile> get_component child \<rightarrow>\<^sub>r c\<close> get_dom_component_ptr_in_heap by fast
    with node_ptr have "node_ptr |\<in>| node_ptr_kinds h"
      by auto
    then obtain parent_opt where
      parent: "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r parent_opt"
      using get_parent_ok \<open>type_wf h\<close> \<open>known_ptrs h\<close>
      by fast
    then show ?thesis
    proof (induct parent_opt)
      case None
      then have "h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r cast node_ptr"
        by (simp add: local.get_root_node_no_parent)
      then show ?case
        using \<open>type_wf h\<close> \<open>known_ptrs h\<close> node_ptr step(2)
        apply(auto simp add: get_component_def a_get_root_node_def elim!: bind_returns_result_E2)[1]
        using to_tree_order_ptr_in_result returns_result_eq by fastforce
    next
      case (Some parent_ptr)
      then have "h \<turnstile> get_component parent_ptr \<rightarrow>\<^sub>r c"
        using step(2) node_ptr \<open>type_wf h\<close> \<open>known_ptrs h\<close> \<open>heap_is_wellformed h\<close>
          get_root_node_parent_same
        by(auto simp add: get_component_def elim!: bind_returns_result_E2 intro!: bind_pure_returns_result_I)
      then have "parent_ptr \<in> set c"
        using step node_ptr Some by blast
      then show ?case
        using  \<open>type_wf h\<close> \<open>known_ptrs h\<close> \<open>heap_is_wellformed h\<close> step(2) node_ptr Some
        apply(auto simp add: get_component_def elim!: bind_returns_result_E2)[1]
        using to_tree_order_parent by blast
    qed
  next
    case False
    then show ?thesis
      using \<open>type_wf h\<close> \<open>known_ptrs h\<close> step(2)
      apply(auto simp add: get_component_def elim!: bind_returns_result_E2)[1]
      by (metis is_OK_returns_result_I local.get_root_node_not_node_same
          local.get_root_node_ptr_in_heap local.to_tree_order_ptr_in_result returns_result_eq)
  qed
qed

lemma get_component_parent_inside:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "cast node_ptr \<in> set c"
  assumes "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some parent"
  shows "parent \<in> set c"
proof -
  have "parent |\<in>| object_ptr_kinds h"
    using assms(6) get_parent_parent_in_heap by blast

  obtain root_ptr where root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr" and
    c: "h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c"
    using assms(4)
    by (metis (no_types, hide_lams) bind_returns_result_E2 get_component_def get_root_node_pure)
  then have "h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r root_ptr"
    using assms(1) assms(2) assms(3) assms(5) to_tree_order_same_root by blast
  then have "h \<turnstile> get_root_node parent \<rightarrow>\<^sub>r root_ptr"
    using assms(6)  get_root_node_parent_same by blast
  then have "h \<turnstile> get_component parent \<rightarrow>\<^sub>r c"
    using c get_component_def by auto
  then show ?thesis
    using assms(1) assms(2) assms(3) get_dom_component_ptr by blast
qed

lemma get_component_subset:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "ptr' \<in> set c"
  shows "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
proof(insert assms(1) assms(5), induct ptr' rule: heap_wellformed_induct_rev )
  case (step child)
  then show ?case
  proof (cases "is_node_ptr_kind child")
    case True
    obtain node_ptr where
      node_ptr: "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr = child"
      using \<open>is_node_ptr_kind child\<close> node_ptr_casts_commute3 by blast
    have "child |\<in>| object_ptr_kinds h"
      using to_tree_order_ptrs_in_heap assms(1) assms(2) assms(3) assms(4) step(2)
      unfolding get_component_def
      by (meson bind_returns_result_E2 get_root_node_pure)
    with node_ptr have "node_ptr |\<in>| node_ptr_kinds h"
      by auto
    then obtain parent_opt where
      parent: "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r parent_opt"
      using get_parent_ok \<open>type_wf h\<close> \<open>known_ptrs h\<close>
      by fast
    then show ?thesis
    proof (induct parent_opt)
      case None
      then have "h \<turnstile> get_root_node child \<rightarrow>\<^sub>r child"
        using assms(1) get_root_node_no_parent node_ptr by blast
      then show ?case
        using \<open>type_wf h\<close> \<open>known_ptrs h\<close> node_ptr step(2) assms(4) assms(1)
        by (metis (no_types) bind_pure_returns_result_I2 bind_returns_result_E2 get_component_def
            get_root_node_pure is_OK_returns_result_I returns_result_eq to_tree_order_same_root)
    next
      case (Some parent_ptr)
      then have "h \<turnstile> get_component parent_ptr \<rightarrow>\<^sub>r c"
        using step get_component_parent_inside assms node_ptr by blast
      then show ?case
        using Some node_ptr
        apply(auto simp add: get_component_def elim!: bind_returns_result_E2
            del: bind_pure_returns_result_I intro!: bind_pure_returns_result_I)[1]
        using get_root_node_parent_same by blast
    qed
  next
    case False
    then have "child |\<in>| object_ptr_kinds h"
      using assms(1) assms(4) step(2)
      by (metis (no_types, lifting) assms(2) assms(3) bind_returns_result_E2 get_root_node_pure
          get_component_def to_tree_order_ptrs_in_heap)
    then have "h \<turnstile> get_root_node child \<rightarrow>\<^sub>r child"
      using assms(1) False get_root_node_not_node_same by blast
    then show ?thesis
      using assms(1) assms(2) assms(3) assms(4) step.prems
      by (metis (no_types) False \<open>child |\<in>| object_ptr_kinds h\<close> bind_pure_returns_result_I2
          bind_returns_result_E2 get_component_def get_root_node_ok get_root_node_pure returns_result_eq
          to_tree_order_node_ptrs)
  qed
qed

lemma get_component_to_tree_order_subset:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r nodes"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  shows "set nodes \<subseteq> set c"
  using assms
  apply(auto simp add: get_component_def elim!: bind_returns_result_E2)[1]
  by (meson to_tree_order_subset  assms(5) contra_subsetD get_dom_component_ptr)

lemma get_component_to_tree_order:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to"
  assumes "ptr \<in> set to"
  shows "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
  by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) assms(4) assms(5) assms(6)
      get_component_ok get_component_subset get_component_to_tree_order_subset is_OK_returns_result_E
      local.to_tree_order_ptr_in_result local.to_tree_order_ptrs_in_heap select_result_I2 subsetCE)

lemma get_component_root_node_same:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
  assumes "x \<in> set c"
  shows "h \<turnstile> get_root_node x \<rightarrow>\<^sub>r root_ptr"
proof(insert assms(1) assms(6), induct x rule: heap_wellformed_induct_rev )
  case (step child)
  then show ?case
  proof (cases "is_node_ptr_kind child")
    case True
    obtain node_ptr where
      node_ptr: "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr = child"
      using \<open>is_node_ptr_kind child\<close> node_ptr_casts_commute3 by blast
    have "child |\<in>| object_ptr_kinds h"
      using to_tree_order_ptrs_in_heap assms(1) assms(2) assms(3) assms(4) step(2)
      unfolding get_component_def
      by (meson bind_returns_result_E2 get_root_node_pure)
    with node_ptr have "node_ptr |\<in>| node_ptr_kinds h"
      by auto
    then obtain parent_opt where
      parent: "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r parent_opt"
      using get_parent_ok \<open>type_wf h\<close> \<open>known_ptrs h\<close>
      by fast
    then show ?thesis
    proof (induct parent_opt)
      case None
      then have "h \<turnstile> get_root_node child \<rightarrow>\<^sub>r child"
        using assms(1) get_root_node_no_parent  node_ptr by blast
      then show ?case
        using \<open>type_wf h\<close> \<open>known_ptrs h\<close> node_ptr step(2) assms(4) assms(1) assms(5)
        by (metis (no_types) \<open>child |\<in>| object_ptr_kinds h\<close> bind_pure_returns_result_I
            get_component_def get_dom_component_ptr get_component_subset get_root_node_pure is_OK_returns_result_E
            returns_result_eq to_tree_order_ok to_tree_order_same_root)
    next
      case (Some parent_ptr)
      then have "h \<turnstile> get_component parent_ptr \<rightarrow>\<^sub>r c"
        using step get_component_parent_inside assms node_ptr
        by (meson get_component_subset)
      then show ?case
        using Some node_ptr
        apply(auto simp add: get_component_def elim!: bind_returns_result_E2)[1]
        using get_root_node_parent_same
        using \<open>h \<turnstile> get_component parent_ptr \<rightarrow>\<^sub>r c\<close> assms(1) assms(2) assms(3) get_dom_component_ptr
          step.hyps
        by blast
    qed
  next
    case False
    then have "child |\<in>| object_ptr_kinds h"
      using assms(1) assms(4) step(2)
      by (metis (no_types, lifting) assms(2) assms(3) bind_returns_result_E2 get_root_node_pure
          get_component_def to_tree_order_ptrs_in_heap)
    then have "h \<turnstile> get_root_node child \<rightarrow>\<^sub>r child"
      using assms(1) False get_root_node_not_node_same by auto
    then show ?thesis
      using assms(1) assms(2) assms(3) assms(4) step.prems assms(5)
      by (metis (no_types, hide_lams) bind_returns_result_E2 get_component_def get_root_node_pure
          returns_result_eq to_tree_order_same_root)
  qed
qed


lemma get_dom_component_no_overlap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c'"
  shows "set c \<inter> set c' = {} \<or> c = c'"
proof (rule ccontr, auto)
  fix x
  assume 1: "c \<noteq> c'" and 2: "x \<in> set c" and 3: "x \<in> set c'"
  obtain root_ptr where root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    using assms(4) unfolding get_component_def
    by (meson bind_is_OK_E is_OK_returns_result_I)
  moreover obtain root_ptr' where root_ptr': "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr'"
    using assms(5) unfolding get_component_def
    by (meson bind_is_OK_E is_OK_returns_result_I)
  ultimately have "root_ptr \<noteq> root_ptr'"
    using 1 assms
    unfolding get_component_def
    by (meson bind_returns_result_E3 get_root_node_pure returns_result_eq)

  moreover have "h \<turnstile> get_root_node x \<rightarrow>\<^sub>r root_ptr"
    using 2 root_ptr get_component_root_node_same assms by blast
  moreover have "h \<turnstile> get_root_node x \<rightarrow>\<^sub>r root_ptr'"
    using 3 root_ptr' get_component_root_node_same assms by blast
  ultimately show False
    using select_result_I2 by force
qed

lemma get_component_separates_tree_order:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
  assumes "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c'"
  assumes "ptr' \<notin> set c"
  shows "set to \<inter> set c' = {}"
proof -
  have "c \<noteq> c'"
    using assms get_dom_component_ptr by blast
  then have "set c \<inter> set c' = {}"
    using assms get_dom_component_no_overlap by blast
  moreover have "set to \<subseteq> set c"
    using assms get_component_to_tree_order_subset by blast
  ultimately show ?thesis
    by blast
qed

lemma get_component_separates_tree_order_general:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> to_tree_order ptr'' \<rightarrow>\<^sub>r to''"
  assumes "ptr'' \<in> set c"
  assumes "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c'"
  assumes "ptr' \<notin> set c"
  shows "set to'' \<inter> set c' = {}"
proof -
  obtain root_ptr where root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    using assms(4)
    by (metis bind_is_OK_E get_component_def is_OK_returns_result_I)
  then have c: "h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c"
    using assms(4) unfolding get_component_def
    by (simp add: bind_returns_result_E3)
  with root_ptr show ?thesis
    using assms get_component_separates_tree_order get_component_subset
    by meson
qed
end

interpretation i_get_component?: l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name
  by(auto simp add: l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def get_component_def
      is_strongly_dom_component_safe_def is_weakly_dom_component_safe_def instances)
declare l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_child\_nodes\<close>

locale l_get_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_dom_component_get_child_nodes:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
  assumes "child \<in> set children"
  shows "cast child \<in> set c \<longleftrightarrow> ptr' \<in> set c"
proof
  assume 1: "cast child \<in> set c"
  obtain root_ptr where
    root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    by (metis assms(4) bind_is_OK_E get_component_def is_OK_returns_result_I)
  have "h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root_ptr"
    using "1" assms(1) assms(2) assms(3) assms(4) get_component_root_node_same root_ptr
    by blast
  then have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
    using assms(1) assms(2) assms(3) assms(5) assms(6) local.child_parent_dual
      local.get_root_node_parent_same
    by blast
  then have "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
    using "1" assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) local.child_parent_dual
      local.get_component_parent_inside local.get_component_subset
    by blast
  then show "ptr' \<in> set c"
    using assms(1) assms(2) assms(3) get_dom_component_ptr
    by blast
next
  assume 1: "ptr' \<in> set c"
  obtain root_ptr where
    root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    by (metis assms(4) bind_is_OK_E get_component_def is_OK_returns_result_I)
  have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
    using "1" assms(1) assms(2) assms(3) assms(4) get_component_root_node_same root_ptr
    by blast
  then have "h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root_ptr"
    using assms(1) assms(2) assms(3) assms(5) assms(6) local.child_parent_dual local.get_root_node_parent_same
    by blast
  then have "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
    using "1" assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) local.child_parent_dual
      local.get_component_parent_inside local.get_component_subset
    by blast
  then show "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child \<in> set c"
    by (smt \<open>h \<turnstile> get_root_node (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<rightarrow>\<^sub>r root_ptr\<close> assms(1) assms(2) assms(3)
        assms(5) assms(6) disjoint_iff_not_equal is_OK_returns_result_E is_OK_returns_result_I
        l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_dom_component_no_overlap local.child_parent_dual local.get_component_ok
        local.get_component_parent_inside local.get_dom_component_ptr local.get_root_node_ptr_in_heap
        local.l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms)
qed


lemma get_child_nodes_get_component:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  shows "cast ` set children \<subseteq> set c"
  using assms get_dom_component_get_child_nodes
  using local.get_dom_component_ptr by auto


lemma get_child_nodes_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>h h'"
  shows "is_strongly_dom_component_safe {ptr} (cast ` set children) h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson local.get_child_nodes_pure pure_returns_heap_eq)
  then show ?thesis
    using assms
    apply(auto simp add: is_strongly_dom_component_safe_def Let_def preserved_def)[1]
    by (smt IntI finite_set_in get_dom_component_get_child_nodes is_OK_returns_result_E
        is_OK_returns_result_I local.get_child_nodes_ptr_in_heap local.get_component_impl
        local.get_component_ok local.get_dom_component_ptr select_result_I2)
qed
end

interpretation i_get_component_get_child_nodes?: l_get_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_parent\<close>

locale l_get_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_parent_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_parent ptr' \<rightarrow>\<^sub>r Some parent"
  shows "parent \<in> set c \<longleftrightarrow> cast ptr' \<in> set c"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) is_OK_returns_result_E
      l_to_tree_order_wf.to_tree_order_parent local.get_component_parent_inside local.get_component_subset
      local.get_component_to_tree_order_subset local.get_parent_parent_in_heap local.l_to_tree_order_wf_axioms
      local.to_tree_order_ok local.to_tree_order_ptr_in_result subsetCE)


lemma get_parent_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r Some parent"
  assumes "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>h h'"
  shows "is_strongly_dom_component_safe {cast node_ptr} {parent} h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson local.get_parent_pure pure_returns_heap_eq)
  then show ?thesis
    using assms
    apply(auto simp add: is_strongly_dom_component_safe_def Let_def preserved_def)[1]
    using get_dom_component_get_child_nodes local.get_component_impl local.get_dom_component_ptr
    by (metis (no_types, hide_lams) Int_iff finite_set_in get_parent_is_strongly_dom_component_safe_step
        local.get_component_ok local.get_parent_parent_in_heap local.to_tree_order_ok local.to_tree_order_parent
        local.to_tree_order_ptr_in_result local.to_tree_order_ptrs_in_heap returns_result_select_result)
qed
end

interpretation i_get_component_get_parent?: l_get_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_root\_node\<close>

locale l_get_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_root_node_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root"
  shows "root \<in> set c \<longleftrightarrow> ptr' \<in> set c"
proof
  assume 1: "root \<in> set c"
  obtain root_ptr where
    root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    by (metis assms(4) bind_is_OK_E get_component_def is_OK_returns_result_I)
  have "h \<turnstile> get_root_node root \<rightarrow>\<^sub>r root_ptr"
    using "1" assms(1) assms(2) assms(3) assms(4) get_component_root_node_same root_ptr
    by blast
  moreover have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
    by (metis (no_types, lifting) calculation assms(1) assms(2) assms(3) assms(5)
        is_OK_returns_result_E local.get_root_node_root_in_heap local.to_tree_order_ok
        local.to_tree_order_ptr_in_result local.to_tree_order_same_root select_result_I2)
  ultimately have "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
    apply(auto simp add: get_component_def)[1]
    by (smt "1" assms(1) assms(2) assms(3) assms(4) bind_pure_returns_result_I bind_returns_result_E3
        local.get_component_def local.get_component_subset local.get_root_node_pure)
  then show "ptr' \<in> set c"
    using assms(1) assms(2) assms(3) get_dom_component_ptr by blast
next
  assume 1: "ptr' \<in> set c"
  obtain root_ptr where
    root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    by (metis assms(4) bind_is_OK_E get_component_def is_OK_returns_result_I)
  have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
    using "1" assms(1) assms(2) assms(3) assms(4) get_component_root_node_same root_ptr
    by blast
  then have "h \<turnstile> get_root_node root \<rightarrow>\<^sub>r root_ptr"
    by (metis assms(1) assms(2) assms(3) assms(5) is_OK_returns_result_E local.get_root_node_root_in_heap
        local.to_tree_order_ok local.to_tree_order_ptr_in_result local.to_tree_order_same_root returns_result_eq)
  then have "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
    using "1" assms(1) assms(2) assms(3) assms(4) local.get_component_subset by blast
  then show "root \<in> set c"
    using assms(5) bind_returns_result_E3 local.get_component_def local.to_tree_order_ptr_in_result
    by fastforce
qed

lemma get_root_node_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>h h'"
  shows "is_strongly_dom_component_safe {ptr} {root} h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson local.get_root_node_pure pure_returns_heap_eq)
  then show ?thesis
    using assms
    apply(auto simp add: is_strongly_dom_component_safe_def Let_def preserved_def)[1]
    by (metis (no_types, lifting) IntI get_root_node_is_strongly_dom_component_safe_step is_OK_returns_result_I
        local.get_component_impl local.get_component_ok local.get_dom_component_ptr
        local.get_root_node_ptr_in_heap notin_fset returns_result_select_result)
qed
end

interpretation i_get_component_get_root_node?: l_get_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_element\_by\_id\<close>

locale l_get_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_element_by_id_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_element_by_id ptr' idd \<rightarrow>\<^sub>r Some result"
  shows "cast result \<in> set c \<longleftrightarrow> ptr' \<in> set c"
proof
  assume 1: "cast result \<in> set c"
  obtain root_ptr where
    root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    by (metis assms(4) bind_is_OK_E get_component_def is_OK_returns_result_I)
  then have "h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c"
    using \<open>h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c\<close>
    by (simp add: get_component_def bind_returns_result_E3)

  obtain to' where to': "h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'"
    using \<open>h \<turnstile> get_element_by_id ptr' idd \<rightarrow>\<^sub>r Some result\<close>
    apply(simp add: get_element_by_id_def first_in_tree_order_def)
    by (meson bind_is_OK_E is_OK_returns_result_I)
  then have "cast result \<in> set to'"
    using \<open>h \<turnstile> get_element_by_id ptr' idd \<rightarrow>\<^sub>r Some result\<close> get_element_by_id_result_in_tree_order
    by blast

  have "h \<turnstile> get_root_node (cast result) \<rightarrow>\<^sub>r root_ptr"
    using "1" assms(1) assms(2) assms(3) assms(4) get_component_root_node_same root_ptr
    by blast
  then have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
    using \<open>cast result \<in> set to'\<close> \<open>h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'\<close>
    using "1" assms(1) assms(2) assms(3) assms(4) get_dom_component_ptr get_component_root_node_same
      get_component_subset get_component_to_tree_order
    by blast
  then have "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
    using \<open>h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c\<close>
    using get_component_def by auto
  then show "ptr' \<in> set c"
    using assms(1) assms(2) assms(3) get_dom_component_ptr by blast
next
  assume "ptr' \<in> set c"
  moreover obtain to' where to': "h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'"
    by (meson assms(1) assms(2) assms(3) assms(4) calculation get_dom_component_ptr_in_heap
        get_component_subset is_OK_returns_result_E is_OK_returns_result_I to_tree_order_ok)
  ultimately have "set to' \<subseteq> set c"
    using assms(1) assms(2) assms(3) assms(4) get_component_subset get_component_to_tree_order_subset
    by blast
  moreover have "cast result \<in> set to'"
    using assms(5) get_element_by_id_result_in_tree_order to' by blast
  ultimately show "cast result \<in> set c"
    by blast
qed


lemma get_element_by_id_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_element_by_id ptr idd \<rightarrow>\<^sub>r Some result"
  assumes "h \<turnstile> get_element_by_id ptr idd \<rightarrow>\<^sub>h h'"
  shows "is_strongly_dom_component_safe {ptr} {cast result} h h'"
proof -
  have "h = h'"
    using assms(5)
    by(auto simp add: preserved_def get_element_by_id_def first_in_tree_order_def
        elim!: bind_returns_heap_E2 intro!: map_filter_M_pure bind_pure_I split: option.splits list.splits)
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
  obtain c where c: "h \<turnstile> a_get_component ptr \<rightarrow>\<^sub>r c"
    using \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) local.get_component_impl
      local.get_component_ok
    by blast

  then show ?thesis
    using assms \<open>h = h'\<close>
    apply(auto simp add: is_strongly_dom_component_safe_def Let_def preserved_def get_element_by_id_def
        first_in_tree_order_def elim!: bind_returns_result_E2 intro!: map_filter_M_pure bind_pure_I
        split: option.splits list.splits)[1]
    by (metis (no_types, lifting) Int_iff \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(4) finite_set_in
        get_element_by_id_is_strongly_dom_component_safe_step local.get_component_impl local.get_dom_component_ptr
        select_result_I2)
qed
end

interpretation i_get_component_get_element_by_id?: l_get_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_get_element_by_id\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>get\_elements\_by\_class\_name\<close>

locale l_get_component_get_elements_by_class_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_elements_by_class_name_result_in_tree_order:
  assumes "h \<turnstile> get_elements_by_class_name ptr name \<rightarrow>\<^sub>r results"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
  assumes "result \<in> set results"
  shows "cast result \<in> set to"
  using assms
  by(auto simp add: get_elements_by_class_name_def first_in_tree_order_def
      elim!: map_filter_M_pure_E[where y=result]  bind_returns_result_E2
      dest!: bind_returns_result_E3[rotated, OF assms(2), rotated]
      intro!: map_filter_M_pure map_M_pure_I bind_pure_I
      split: option.splits list.splits if_splits)

lemma get_elements_by_class_name_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_elements_by_class_name ptr' name \<rightarrow>\<^sub>r results"
  assumes "result \<in> set results"
  shows "cast result \<in> set c \<longleftrightarrow> ptr' \<in> set c"
proof
  assume 1: "cast result \<in> set c"
  obtain root_ptr where
    root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    by (metis assms(4) bind_is_OK_E get_component_def is_OK_returns_result_I)
  then have "h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c"
    using \<open>h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c\<close>
    by (simp add: get_component_def bind_returns_result_E3)

  obtain to' where to': "h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'"
    using \<open>h \<turnstile> get_elements_by_class_name ptr' name \<rightarrow>\<^sub>r results\<close>
    apply(simp add: get_elements_by_class_name_def first_in_tree_order_def)
    by (meson bind_is_OK_E is_OK_returns_result_I)
  then have "cast result \<in> set to'"
    using get_elements_by_class_name_result_in_tree_order assms by blast

  have "h \<turnstile> get_root_node (cast result) \<rightarrow>\<^sub>r root_ptr"
    using "1" assms(1) assms(2) assms(3) assms(4) get_component_root_node_same root_ptr
    by blast
  then have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
    using \<open>cast result \<in> set to'\<close> \<open>h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'\<close>
    using "1" assms(1) assms(2) assms(3) assms(4) get_dom_component_ptr get_component_root_node_same
      get_component_subset get_component_to_tree_order
    by blast
  then have "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
    using \<open>h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c\<close>
    using get_component_def by auto
  then show "ptr' \<in> set c"
    using assms(1) assms(2) assms(3) get_dom_component_ptr by blast
next
  assume "ptr' \<in> set c"
  moreover obtain to' where to': "h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'"
    by (meson assms(1) assms(2) assms(3) assms(4) calculation get_dom_component_ptr_in_heap
        get_component_subset is_OK_returns_result_E is_OK_returns_result_I to_tree_order_ok)
  ultimately have "set to' \<subseteq> set c"
    using assms(1) assms(2) assms(3) assms(4) get_component_subset get_component_to_tree_order_subset
    by blast
  moreover have "cast result \<in> set to'"
    using assms get_elements_by_class_name_result_in_tree_order to' by blast
  ultimately show "cast result \<in> set c"
    by blast
qed

lemma get_elements_by_class_name_pure [simp]:
  "pure (get_elements_by_class_name ptr name) h"
  by(auto simp add: get_elements_by_class_name_def intro!: bind_pure_I map_filter_M_pure
      split: option.splits)

lemma get_elements_by_class_name_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_elements_by_class_name ptr name \<rightarrow>\<^sub>r results"
  assumes "h \<turnstile> get_elements_by_class_name ptr name \<rightarrow>\<^sub>h h'"
  shows "is_strongly_dom_component_safe {ptr} (cast ` set results) h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson get_elements_by_class_name_pure pure_returns_heap_eq)
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
  obtain c where c: "h \<turnstile> a_get_component ptr \<rightarrow>\<^sub>r c"
    using \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) local.get_component_impl local.get_component_ok
    by blast

  then show ?thesis
    using assms \<open>h = h'\<close>
    apply(auto simp add: is_strongly_dom_component_safe_def Let_def preserved_def
        get_elements_by_class_name_def first_in_tree_order_def elim!: bind_returns_result_E2
        intro!: map_filter_M_pure bind_pure_I split: option.splits list.splits)[1]
    by (metis (no_types, lifting) Int_iff \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(4) finite_set_in
        get_elements_by_class_name_is_strongly_dom_component_safe_step local.get_component_impl
        local.get_dom_component_ptr select_result_I2)
qed
end

interpretation i_get_component_get_elements_by_class_name?: l_get_component_get_elements_by_class_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_component_get_elements_by_class_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_get_elements_by_class_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsection \<open>get\_elements\_by\_tag\_name\<close>

locale l_get_component_get_elements_by_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma get_elements_by_tag_name_result_in_tree_order:
  assumes "h \<turnstile> get_elements_by_tag_name ptr name \<rightarrow>\<^sub>r results"
  assumes "h \<turnstile> to_tree_order ptr \<rightarrow>\<^sub>r to"
  assumes "result \<in> set results"
  shows "cast result \<in> set to"
  using assms
  by(auto simp add: get_elements_by_tag_name_def first_in_tree_order_def
      elim!: map_filter_M_pure_E[where y=result]  bind_returns_result_E2
      dest!: bind_returns_result_E3[rotated, OF assms(2), rotated]
      intro!: map_filter_M_pure map_M_pure_I bind_pure_I
      split: option.splits list.splits if_splits)

lemma get_elements_by_tag_name_is_strongly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c"
  assumes "h \<turnstile> get_elements_by_tag_name ptr' name \<rightarrow>\<^sub>r results"
  assumes "result \<in> set results"
  shows "cast result \<in> set c \<longleftrightarrow> ptr' \<in> set c"
proof
  assume 1: "cast result \<in> set c"
  obtain root_ptr where
    root_ptr: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root_ptr"
    by (metis assms(4) bind_is_OK_E get_component_def is_OK_returns_result_I)
  then have "h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c"
    using \<open>h \<turnstile> get_component ptr \<rightarrow>\<^sub>r c\<close>
    by (simp add: get_component_def bind_returns_result_E3)

  obtain to' where to': "h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'"
    using \<open>h \<turnstile> get_elements_by_tag_name ptr' name \<rightarrow>\<^sub>r results\<close>
    apply(simp add: get_elements_by_tag_name_def first_in_tree_order_def)
    by (meson bind_is_OK_E is_OK_returns_result_I)
  then have "cast result \<in> set to'"
    using get_elements_by_tag_name_result_in_tree_order assms by blast

  have "h \<turnstile> get_root_node (cast result) \<rightarrow>\<^sub>r root_ptr"
    using "1" assms(1) assms(2) assms(3) assms(4) get_component_root_node_same root_ptr
    by blast
  then have "h \<turnstile> get_root_node ptr' \<rightarrow>\<^sub>r root_ptr"
    using \<open>cast result \<in> set to'\<close> \<open>h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'\<close>
    using "1" assms(1) assms(2) assms(3) assms(4) get_dom_component_ptr get_component_root_node_same
      get_component_subset get_component_to_tree_order
    by blast
  then have "h \<turnstile> get_component ptr' \<rightarrow>\<^sub>r c"
    using \<open>h \<turnstile> to_tree_order root_ptr \<rightarrow>\<^sub>r c\<close>
    using get_component_def by auto
  then show "ptr' \<in> set c"
    using assms(1) assms(2) assms(3) get_dom_component_ptr by blast
next
  assume "ptr' \<in> set c"
  moreover obtain to' where to': "h \<turnstile> to_tree_order ptr' \<rightarrow>\<^sub>r to'"
    by (meson assms(1) assms(2) assms(3) assms(4) calculation get_dom_component_ptr_in_heap
        get_component_subset is_OK_returns_result_E is_OK_returns_result_I to_tree_order_ok)
  ultimately have "set to' \<subseteq> set c"
    using assms(1) assms(2) assms(3) assms(4) get_component_subset get_component_to_tree_order_subset
    by blast
  moreover have "cast result \<in> set to'"
    using assms get_elements_by_tag_name_result_in_tree_order to' by blast
  ultimately show "cast result \<in> set c"
    by blast
qed

lemma get_elements_by_tag_name_is_strongly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_elements_by_tag_name ptr name \<rightarrow>\<^sub>r results"
  assumes "h \<turnstile> get_elements_by_tag_name ptr name \<rightarrow>\<^sub>h h'"
  shows "is_strongly_dom_component_safe {ptr} (cast ` set results) h h'"
proof -
  have "h = h'"
    using assms(5)
    by (meson get_elements_by_tag_name_pure pure_returns_heap_eq)
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
  obtain c where c: "h \<turnstile> a_get_component ptr \<rightarrow>\<^sub>r c"
    using \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) local.get_component_impl local.get_component_ok
    by blast

  then show ?thesis
    using assms \<open>h = h'\<close>
    apply(auto simp add: is_strongly_dom_component_safe_def Let_def preserved_def
        get_elements_by_class_name_def first_in_tree_order_def elim!: bind_returns_result_E2
        intro!: map_filter_M_pure bind_pure_I split: option.splits list.splits)[1]
    by (metis (no_types, lifting) IntI \<open>ptr |\<in>| object_ptr_kinds h\<close> finite_set_in
        get_elements_by_tag_name_is_strongly_dom_component_safe_step local.get_component_impl
        local.get_dom_component_ptr select_result_I2)
qed
end

interpretation i_get_component_get_elements_by_tag_name?: l_get_component_get_elements_by_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name first_in_tree_order get_attribute get_attribute_locs
  by(auto simp add: l_get_component_get_elements_by_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_get_elements_by_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>remove\_child\<close>

lemma remove_child_not_strongly_dom_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and ptr and child where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_dom_component_safe { ptr, cast child} {} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap"
  let ?P = "do {
      document_ptr \<leftarrow> create_document;
      e1 \<leftarrow> create_element document_ptr ''div'';
      e2 \<leftarrow> create_element document_ptr ''div'';
      append_child (cast e1) (cast e2);
      return (e1, e2)
  }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e1 = "fst |?h0 \<turnstile> ?P|\<^sub>r"
  let ?e2 = "snd |?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and ptr="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e1" and child="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e2"])
    by code_simp+
qed


subsection \<open>adopt\_node\<close>

lemma adopt_node_not_strongly_dom_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and document_ptr and child where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> adopt_node document_ptr child \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_dom_component_safe {cast document_ptr, cast child} {} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap"
  let ?P = "do {
      document_ptr \<leftarrow> create_document;
      document_ptr2 \<leftarrow> create_document;
      e1 \<leftarrow> create_element document_ptr ''div'';
      adopt_node document_ptr2 (cast e1);
      return (document_ptr, e1)
  }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?document_ptr = "fst |?h0 \<turnstile> ?P|\<^sub>r"
  let ?e1 = "snd |?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and document_ptr="?document_ptr" and child="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e1"])
    by code_simp+
qed

subsection \<open>create\_element\<close>

lemma create_element_not_strongly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and document_ptr and new_element_ptr and tag where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_dom_component_safe {cast document_ptr} {cast new_element_ptr} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap"
  let ?P = "create_document"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?document_ptr = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and document_ptr="?document_ptr"])
    by code_simp+
qed


locale l_get_component_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order
  get_parent get_parent_locs get_child_nodes get_child_nodes_locs get_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name +
  l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs set_tag_name set_tag_name_locs type_wf create_element known_ptr +
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_disconnected_nodes set_disconnected_nodes_locs +
  l_set_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_tag_name set_tag_name_locs +
  l_new_element_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs +
  l_new_element_get_disconnected_nodes get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_tag_name_get_child_nodes type_wf set_tag_name set_tag_name_locs known_ptr
  get_child_nodes get_child_nodes_locs +
  l_set_tag_name_get_disconnected_nodes type_wf set_tag_name set_tag_name_locs
  get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_disconnected_nodes type_wf set_disconnected_nodes set_disconnected_nodes_locs +
  l_set_disconnected_nodes_get_child_nodes set_disconnected_nodes set_disconnected_nodes_locs
  get_child_nodes get_child_nodes_locs +
  l_set_disconnected_nodes_get_disconnected_nodes  type_wf get_disconnected_nodes
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs +
  l_new_element type_wf +
  l_create_element_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M  known_ptr known_ptrs type_wf get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs heap_is_wellformed parent_child_rel set_tag_name
  set_tag_name_locs set_disconnected_nodes set_disconnected_nodes_locs
  create_element
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
    and get_component :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and is_strongly_dom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
    and is_weakly_dom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
    and get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
    and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_ancestors :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and get_ancestors_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_element_by_id :: "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
    and get_elements_by_class_name :: "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr list) prog"
    and get_elements_by_tag_name :: "(_) object_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr list) prog"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_tag_name :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and create_element :: "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
begin

lemma create_element_is_weakly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_component (cast document_ptr)|\<^sub>r"
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
    by(auto simp add: create_element_def elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated])
  have "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr"
    using new_element_ptr h2 h3 disc_nodes h'
    apply(auto simp add: create_element_def intro!: bind_returns_result_I
        bind_pure_returns_result_I[OF get_disconnected_nodes_pure])[1]
     apply (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
    by (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
  have "preserved (get_M ptr getter) h h2"
    using h2 new_element_ptr
    apply(rule new_element_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t)
    using new_element_ptr assms(6) \<open>h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr\<close>
    by simp

  have "preserved (get_M ptr getter) h2 h3"
    using set_tag_name_writes h3
    apply(rule reads_writes_preserved2)
    apply(auto simp add: set_tag_name_locs_impl a_set_tag_name_locs_def all_args_def)[1]
    by (metis (no_types, lifting) \<open>h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr\<close> assms(6)
        get_M_Element_preserved8 select_result_I2)

  have "document_ptr |\<in>| document_ptr_kinds h"
    using create_element_document_in_heap
    using assms(4)
    by blast
  then
  have "ptr \<noteq> (cast document_ptr)"
    using assms(5) assms(1) assms(2) assms(3) local.get_component_ok local.get_dom_component_ptr
    by auto
  have "preserved (get_M ptr getter) h3 h'"
    using set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved2)
    apply(auto simp add: set_disconnected_nodes_locs_def all_args_def)[1]
    by (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr\<close> get_M_Mdocument_preserved3)

  show ?thesis
    using \<open>preserved (get_M ptr getter) h h2\<close> \<open>preserved (get_M ptr getter) h2 h3\<close>
      \<open>preserved (get_M ptr getter) h3 h'\<close>
    by(auto simp add: preserved_def)
qed


lemma create_element_is_weakly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r result \<rightarrow>\<^sub>h h'"
  shows "is_weakly_dom_component_safe {cast document_ptr} {cast result} h h'"
proof -
  obtain new_element_ptr h2 h3 disc_nodes_h3 where
    new_element_ptr: "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr" and
    h2: "h \<turnstile> new_element \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile> set_tag_name new_element_ptr tag \<rightarrow>\<^sub>h h3" and
    disc_nodes_h3: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_element_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: create_element_def returns_result_heap_def
        elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )
  then have "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr"
    apply(auto simp add: create_element_def intro!: bind_returns_result_I)[1]
      apply (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
     apply (metis is_OK_returns_heap_E is_OK_returns_result_I local.get_disconnected_nodes_pure
        pure_returns_heap_eq)
    by (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
  have "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>h h'"
    by (meson assms(4) returns_result_heap_def)


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
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_tag_name_writes h3])
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
    using \<open>h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr\<close> local.create_element_known_ptr
    by blast
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

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_element_ptr
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
  have root: "h \<turnstile> get_root_node (cast document_ptr) \<rightarrow>\<^sub>r cast document_ptr"
    by (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close> local.get_root_node_not_node_same)
  then
  have root': "h' \<turnstile> get_root_node (cast document_ptr) \<rightarrow>\<^sub>r cast document_ptr"
    by (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close> document_ptr_kinds_eq_h
        local.get_root_node_not_node_same object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3)


  have "heap_is_wellformed h'"
    using create_element_preserves_wellformedness assms returns_result_heap_def
    by metis

  have "cast result |\<notin>| object_ptr_kinds h"
    using \<open>cast new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> returns_result_heap_def
    by (metis (full_types) ObjectMonad.ptr_kinds_ptr_kinds_M
        \<open>h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr\<close> assms(4) returns_result_eq)

  obtain to where to: "h \<turnstile> to_tree_order (cast document_ptr) \<rightarrow>\<^sub>r to"
    by (meson \<open>document_ptr |\<in>| document_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        document_ptr_kinds_commutes is_OK_returns_result_E local.to_tree_order_ok)
  then
  have "h \<turnstile> a_get_component (cast document_ptr) \<rightarrow>\<^sub>r to"
    using root
    by(auto simp add: a_get_component_def)
  moreover
  obtain to' where to': "h' \<turnstile> to_tree_order (cast document_ptr) \<rightarrow>\<^sub>r to'"
    by (meson \<open>heap_is_wellformed h'\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> is_OK_returns_result_E
        local.get_root_node_root_in_heap local.to_tree_order_ok root')
  then
  have "h' \<turnstile> a_get_component (cast document_ptr) \<rightarrow>\<^sub>r to'"
    using root'
    by(auto simp add: a_get_component_def)
  moreover
  have "\<And>child. child \<in> set to \<longleftrightarrow> child \<in> set to'"
    by (metis \<open>heap_is_wellformed h'\<close> \<open>known_ptrs h'\<close> \<open>parent_child_rel h = parent_child_rel h'\<close>
        \<open>type_wf h'\<close> assms(1) assms(2) assms(3) local.to_tree_order_parent_child_rel to to')
  ultimately
  have "set |h \<turnstile> local.a_get_component (cast document_ptr)|\<^sub>r = set |h' \<turnstile> local.a_get_component (cast document_ptr)|\<^sub>r"
    by(auto simp add: a_get_component_def)

  show ?thesis
    apply(auto simp add: is_weakly_dom_component_safe_def Let_def)[1]
       apply (metis \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close> assms(2) assms(3)
        children_eq_h local.get_child_nodes_ok local.get_child_nodes_ptr_in_heap local.known_ptrs_known_ptr
        object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 returns_result_select_result)
      apply (metis \<open>h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr\<close> assms(4)
        element_ptr_kinds_commutes h2 new_element_ptr new_element_ptr_in_heap node_ptr_kinds_eq_h2
        node_ptr_kinds_eq_h3 returns_result_eq returns_result_heap_def)
    using \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r result |\<notin>| object_ptr_kinds h\<close> element_ptr_kinds_commutes
      node_ptr_kinds_commutes apply blast
    using assms(1) assms(2) assms(3) \<open>h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>h h'\<close>
    apply(rule create_element_is_weakly_dom_component_safe_step)
     apply (simp add: local.get_component_impl)
    using \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>
      \<open>h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr\<close> by auto
qed
end

interpretation i_get_component_create_element?: l_get_component_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr heap_is_wellformed parent_child_rel type_wf known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_element_by_id get_elements_by_class_name get_elements_by_tag_name get_disconnected_nodes
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs set_tag_name
  set_tag_name_locs create_element
  by(auto simp add: l_get_component_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsection \<open>create\_character\_data\<close>

lemma create_character_data_not_strongly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and document_ptr and new_character_data_ptr and val where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> create_character_data document_ptr val \<rightarrow>\<^sub>r new_character_data_ptr \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_dom_component_safe {cast document_ptr} {cast new_character_data_ptr} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap"
  let ?P = "create_document"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?document_ptr = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and document_ptr="?document_ptr"])
    by code_simp+
qed

locale l_get_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order
  get_parent get_parent_locs get_child_nodes get_child_nodes_locs get_component
  is_strongly_dom_component_safe is_weakly_dom_component_safe get_root_node get_root_node_locs
  get_ancestors get_ancestors_locs get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id
  get_elements_by_class_name get_elements_by_tag_name +
  l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs set_val set_val_locs  type_wf create_character_data known_ptr +
  l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_disconnected_nodes set_disconnected_nodes_locs +
  l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_val set_val_locs +
  l_create_character_data_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs heap_is_wellformed parent_child_rel set_val
  set_val_locs set_disconnected_nodes set_disconnected_nodes_locs
  create_character_data known_ptrs
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
    and get_component :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and is_strongly_dom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
    and is_weakly_dom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
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
    and set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_val_locs :: "(_) character_data_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and create_character_data ::
    "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) character_data_ptr) prog"
begin

lemma create_character_data_is_weakly_dom_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>h h'"
  assumes "ptr \<notin> set |h \<turnstile> get_component (cast document_ptr)|\<^sub>r"
  assumes "ptr \<noteq> cast |h \<turnstile> create_character_data document_ptr text|\<^sub>r"
  shows "preserved (get_M ptr getter) h h'"
proof -
  obtain new_character_data_ptr h2 h3 disc_nodes where
    new_character_data_ptr: "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr" and
    h2: "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile> set_val new_character_data_ptr text \<rightarrow>\<^sub>h h3" and
    disc_nodes: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_character_data_ptr # disc_nodes) \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: create_character_data_def
        elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated])

  have "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr"
    using new_character_data_ptr h2 h3 disc_nodes h'
    apply(auto simp add: create_character_data_def
        intro!: bind_returns_result_I bind_pure_returns_result_I[OF get_disconnected_nodes_pure])[1]
     apply (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
    by (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
  have "preserved (get_M ptr getter) h h2"
    using h2 new_character_data_ptr
    apply(rule new_character_data_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t)
    using new_character_data_ptr assms(6)
      \<open>h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr\<close>
    by simp

  have "preserved (get_M ptr getter) h2 h3"
    using set_val_writes h3
    apply(rule reads_writes_preserved2)
    apply(auto simp add: set_val_locs_impl a_set_val_locs_def all_args_def)[1]
    by (metis (mono_tags) CharacterData_simp11
        \<open>h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr\<close> assms(4) assms(6)
        is_OK_returns_heap_I is_OK_returns_result_E returns_result_eq select_result_I2)

  have "document_ptr |\<in>| document_ptr_kinds h"
    using create_character_data_document_in_heap
    using assms(4)
    by blast
  then
  have "ptr \<noteq> (cast document_ptr)"
    using assms(5) assms(1) assms(2) assms(3) local.get_component_ok local.get_dom_component_ptr
    by auto
  have "preserved (get_M ptr getter) h3 h'"
    using set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved2)
    apply(auto simp add: set_disconnected_nodes_locs_def all_args_def)[1]
    by (metis \<open>ptr \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr\<close> get_M_Mdocument_preserved3)

  show ?thesis
    using \<open>preserved (get_M ptr getter) h h2\<close> \<open>preserved (get_M ptr getter) h2 h3\<close>
      \<open>preserved (get_M ptr getter) h3 h'\<close>
    by(auto simp add: preserved_def)
qed

lemma create_character_data_is_weakly_dom_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r result"
  assumes "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>h h'"
  shows "is_weakly_dom_component_safe {cast document_ptr} {cast result} h h'"
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
  then
  have "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr"
    apply(auto simp add: create_character_data_def intro!: bind_returns_result_I)[1]
      apply (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
     apply (metis is_OK_returns_heap_E is_OK_returns_result_I local.get_disconnected_nodes_pure
        pure_returns_heap_eq)
    by (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)

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

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_character_data_ptr
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

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_character_data_ptr
                \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h2
      get_child_nodes_new_character_data[rotated, OF new_character_data_ptr h2]
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
  have root: "h \<turnstile> get_root_node (cast document_ptr) \<rightarrow>\<^sub>r cast document_ptr"
    by (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close> local.get_root_node_not_node_same)
  then
  have root': "h' \<turnstile> get_root_node (cast document_ptr) \<rightarrow>\<^sub>r cast document_ptr"
    by (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close> document_ptr_kinds_eq_h
        local.get_root_node_not_node_same object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3)


  have "heap_is_wellformed h'" and "known_ptrs h'"
    using create_character_data_preserves_wellformedness assms
    by blast+

  have "cast result |\<notin>| object_ptr_kinds h"
    using \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>
    by (metis (full_types) ObjectMonad.ptr_kinds_ptr_kinds_M
        \<open>h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr\<close> assms(4) returns_result_eq)

  obtain to where to: "h \<turnstile> to_tree_order (cast document_ptr) \<rightarrow>\<^sub>r to"
    by (meson \<open>document_ptr |\<in>| document_ptr_kinds h\<close> assms(1) assms(2) assms(3)
        document_ptr_kinds_commutes is_OK_returns_result_E local.to_tree_order_ok)
  then
  have "h \<turnstile> a_get_component (cast document_ptr) \<rightarrow>\<^sub>r to"
    using root
    by(auto simp add: a_get_component_def)
  moreover
  obtain to' where to': "h' \<turnstile> to_tree_order (cast document_ptr) \<rightarrow>\<^sub>r to'"
    by (meson \<open>heap_is_wellformed h'\<close> \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> is_OK_returns_result_E
        local.get_root_node_root_in_heap local.to_tree_order_ok root')
  then
  have "h' \<turnstile> a_get_component (cast document_ptr) \<rightarrow>\<^sub>r to'"
    using root'
    by(auto simp add: a_get_component_def)
  moreover
  have "\<And>child. child \<in> set to \<longleftrightarrow> child \<in> set to'"
    by (metis \<open>heap_is_wellformed h'\<close> \<open>known_ptrs h'\<close> \<open>parent_child_rel h = parent_child_rel h'\<close>
        \<open>type_wf h'\<close> assms(1) assms(2) assms(3) local.to_tree_order_parent_child_rel to to')
  ultimately
  have "set |h \<turnstile> local.a_get_component (cast document_ptr)|\<^sub>r =
set |h' \<turnstile> local.a_get_component (cast document_ptr)|\<^sub>r"
    by(auto simp add: a_get_component_def)

  show ?thesis
    apply(auto simp add: is_weakly_dom_component_safe_def Let_def)[1]
    using  assms(2) assms(3) children_eq_h local.get_child_nodes_ok local.get_child_nodes_ptr_in_heap
      local.known_ptrs_known_ptr object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 returns_result_select_result
       apply (metis \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
        is_OK_returns_result_I)

      apply (metis \<open>h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr\<close> assms(4)
        character_data_ptr_kinds_commutes h2 new_character_data_ptr new_character_data_ptr_in_heap
        node_ptr_kinds_eq_h2 node_ptr_kinds_eq_h3 returns_result_eq)
    using \<open>h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr\<close>
      \<open>new_character_data_ptr \<notin> set |h \<turnstile> character_data_ptr_kinds_M|\<^sub>r\<close> assms(4) returns_result_eq
     apply fastforce
    using  assms(2) assms(3) children_eq_h local.get_child_nodes_ok local.get_child_nodes_ptr_in_heap
      local.known_ptrs_known_ptr object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 returns_result_select_result
    apply (smt ObjectMonad.ptr_kinds_ptr_kinds_M
        \<open>cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>
        \<open>h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr\<close> assms(1) assms(5)
        create_character_data_is_weakly_dom_component_safe_step local.get_component_impl select_result_I2)
    done
qed
end

interpretation i_get_component_create_character_data?: l_get_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr heap_is_wellformed parent_child_rel type_wf known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_element_by_id get_elements_by_class_name get_elements_by_tag_name set_val set_val_locs
  get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs
  create_character_data
  by(auto simp add: l_get_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>create\_document\<close>

lemma create_document_not_strongly_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and new_document_ptr where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> create_document \<rightarrow>\<^sub>r new_document_ptr \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_dom_component_safe {} {cast new_document_ptr} h h'"
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

locale l_get_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_component\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs to_tree_order
  get_parent get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name +
  l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M create_document
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
    and get_component :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and is_strongly_dom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
    and is_weakly_dom_component_safe ::
    "(_) object_ptr set \<Rightarrow> (_) object_ptr set \<Rightarrow> (_) heap \<Rightarrow> (_) heap \<Rightarrow> bool"
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
    and create_document :: "((_) heap, exception, (_) document_ptr) prog"
begin

lemma create_document_is_weakly_component_safe_step:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_document \<rightarrow>\<^sub>h h'"
  assumes "ptr \<noteq> cast |h \<turnstile> create_document|\<^sub>r"
  shows "preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
  using assms
  apply(auto simp add: create_document_def)[1]
  by (metis assms(4) assms(5) is_OK_returns_heap_I local.create_document_def new_document_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      select_result_I)

lemma create_document_is_weakly_component_safe:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> create_document \<rightarrow>\<^sub>r result"
  assumes "h \<turnstile> create_document \<rightarrow>\<^sub>h h'"
  shows "is_weakly_dom_component_safe {} {cast result} h h'"
proof -
  have "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast result|}"
    using assms(4) assms(5) local.create_document_def new_document_new_ptr by auto
  moreover have "result |\<notin>| document_ptr_kinds h"
    using assms(4) assms(5) local.create_document_def new_document_ptr_not_in_heap by auto
  ultimately show ?thesis
    using assms
    apply(auto simp add: is_weakly_dom_component_safe_def Let_def local.create_document_def
        new_document_ptr_not_in_heap)[1]
    by (metis \<open>result |\<notin>| document_ptr_kinds h\<close> document_ptr_kinds_commutes new_document_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t)
qed
end

interpretation i_get_component_create_document?: l_get_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr heap_is_wellformed parent_child_rel type_wf known_ptrs to_tree_order get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_component is_strongly_dom_component_safe
  is_weakly_dom_component_safe get_root_node get_root_node_locs get_ancestors get_ancestors_locs
  get_element_by_id get_elements_by_class_name get_elements_by_tag_name create_document
  by(auto simp add: l_get_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_component_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsection \<open>insert\_before\<close>

lemma insert_before_not_strongly_dom_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and ptr and child and ref where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> insert_before ptr child ref \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_dom_component_safe ({ptr, cast child} \<union> (cast ` set_option ref)) {} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap"
  let ?P = "do {
      document_ptr \<leftarrow> create_document;
      e1 \<leftarrow> create_element document_ptr ''div'';
      e2 \<leftarrow> create_element document_ptr ''div'';
      return (e1, e2)
  }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e1 = "fst |?h0 \<turnstile> ?P|\<^sub>r"
  let ?e2 = "snd |?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and ptr="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e1" and
          child="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e2" and ref=None])
    by code_simp+
qed


lemma append_child_not_strongly_dom_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and ptr and child where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> append_child ptr child \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_dom_component_safe {ptr, cast child} {} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap"
  let ?P = "do {
      document_ptr \<leftarrow> create_document;
      e1 \<leftarrow> create_element document_ptr ''div'';
      e2 \<leftarrow> create_element document_ptr ''div'';
      return (e1, e2)
  }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e1 = "fst |?h0 \<turnstile> ?P|\<^sub>r"
  let ?e2 = "snd |?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and ptr="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e1" and child="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e2"])
    by code_simp+
qed


subsection \<open>get\_owner\_document\<close>

lemma get_owner_document_not_strongly_dom_component_safe:
  obtains
    h :: "('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder}, 'element_ptr::{equal,linorder},
'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder}, 'shadow_root_ptr::{equal,linorder},
'Object::{equal,linorder}, 'Node::{equal,linorder}, 'Element::{equal,linorder},
'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap" and
    h' and ptr and owner_document where
    "heap_is_wellformed h" and "type_wf h" and "known_ptrs h" and
    "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document \<rightarrow>\<^sub>h h'" and
    "\<not> is_strongly_dom_component_safe {ptr} {cast owner_document} h h'"
proof -
  let ?h0 = "Heap fmempty ::('object_ptr::{equal,linorder}, 'node_ptr::{equal,linorder},
'element_ptr::{equal,linorder}, 'character_data_ptr::{equal,linorder}, 'document_ptr::{equal,linorder},
'shadow_root_ptr::{equal,linorder}, 'Object::{equal,linorder}, 'Node::{equal,linorder},
'Element::{equal,linorder}, 'CharacterData::{equal,linorder}, 'Document::{equal,linorder}) heap"
  let ?P = "do {
    doc \<leftarrow> create_document;
    create_element doc ''div''
  }"
  let ?h1 = "|?h0 \<turnstile> ?P|\<^sub>h"
  let ?e1 = "|?h0 \<turnstile> ?P|\<^sub>r"

  show thesis
    apply(rule that[where h="?h1" and ptr="cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ?e1"])
    by code_simp+
qed


end
