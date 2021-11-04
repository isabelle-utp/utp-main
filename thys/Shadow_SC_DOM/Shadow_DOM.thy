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

section\<open>The Shadow DOM\<close>
theory Shadow_DOM
  imports
    "monads/ShadowRootMonad"
    Core_SC_DOM.Core_DOM
begin



abbreviation "safe_shadow_root_element_types \<equiv> {''article'', ''aside'', ''blockquote'', ''body'',
  ''div'', ''footer'', ''h1'', ''h2'', ''h3'', ''h4'', ''h5'', ''h6'', ''header'', ''main'',
  ''nav'', ''p'', ''section'', ''span''}"


subsection \<open>Function Definitions\<close>



subsubsection \<open>get\_child\_nodes\<close>

locale l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  CD: l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition get_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) shadow_root_ptr \<Rightarrow> unit
    \<Rightarrow> (_, (_) node_ptr list) dom_prog" where
  "get_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr _ = get_M shadow_root_ptr RShadowRoot.child_nodes"

definition a_get_child_nodes_tups :: "(((_) object_ptr \<Rightarrow> bool) \<times> ((_) object_ptr \<Rightarrow> unit
    \<Rightarrow> (_, (_) node_ptr list) dom_prog)) list" where
  "a_get_child_nodes_tups \<equiv> [(is_shadow_root_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r, get_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast)]"

definition a_get_child_nodes :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog" where
  "a_get_child_nodes ptr = invoke (CD.a_get_child_nodes_tups @ a_get_child_nodes_tups) ptr ()"

definition a_get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" where
  "a_get_child_nodes_locs ptr \<equiv>
    (if is_shadow_root_ptr_kind ptr
    then {preserved (get_M (the (cast ptr)) RShadowRoot.child_nodes)} else {}) \<union>
    CD.a_get_child_nodes_locs ptr"

definition first_child :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr option) dom_prog"
  where
    "first_child ptr = do {
      children \<leftarrow> a_get_child_nodes ptr;
      return (case children of [] \<Rightarrow> None | child#_ \<Rightarrow> Some child)}"
end

global_interpretation l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  get_child_nodes = l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_child_nodes and
  get_child_nodes_locs = l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_child_nodes_locs
  .

locale l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_known_ptr known_ptr +
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs +
  CD: l_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
    and get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes known_ptr_impl: "known_ptr = ShadowRootClass.known_ptr"
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
  assumes get_child_nodes_impl: "get_child_nodes = a_get_child_nodes"
  assumes get_child_nodes_locs_impl: "get_child_nodes_locs = a_get_child_nodes_locs"
begin
lemmas get_child_nodes_def = get_child_nodes_impl[unfolded a_get_child_nodes_def get_child_nodes_def]
lemmas get_child_nodes_locs_def = get_child_nodes_locs_impl[unfolded a_get_child_nodes_locs_def
    get_child_nodes_locs_def, folded CD.get_child_nodes_locs_impl]

lemma get_child_nodes_ok:
  assumes "known_ptr ptr"
  assumes "type_wf h"
  assumes "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (get_child_nodes ptr)"
  using assms[unfolded known_ptr_impl type_wf_impl]
  apply(auto simp add: get_child_nodes_def)[1]
  apply(split CD.get_child_nodes_splits, rule conjI)+
  using ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t CD.get_child_nodes_ok CD.known_ptr_impl CD.type_wf_impl
   apply blast
  apply(auto simp add: CD.known_ptr_impl a_get_child_nodes_tups_def get_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
      get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ok
      dest!: known_ptr_new_shadow_root_ptr intro!: bind_is_OK_I2)[1]
  by(auto dest: get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ok split: option.splits)

lemma get_child_nodes_ptr_in_heap:
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms
  by(auto simp add: get_child_nodes_def invoke_ptr_in_heap dest: is_OK_returns_result_I)

lemma get_child_nodes_pure [simp]:
  "pure (get_child_nodes ptr) h"
  apply (auto simp add: get_child_nodes_def a_get_child_nodes_tups_def)[1]
  apply(split CD.get_child_nodes_splits, rule conjI)+
   apply(simp)
  apply(split invoke_splits, rule conjI)+
   apply(simp)
  by(auto simp add: get_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_pure_I)

lemma get_child_nodes_reads: "reads (get_child_nodes_locs ptr) (get_child_nodes ptr) h h'"
  apply (simp add: get_child_nodes_def a_get_child_nodes_tups_def get_child_nodes_locs_def
      CD.get_child_nodes_locs_def)
  apply(split CD.get_child_nodes_splits, rule conjI)+
   apply(auto intro!: reads_subset[OF CD.get_child_nodes_reads[unfolded  CD.get_child_nodes_locs_def]]
      split: if_splits)[1]
  apply(split invoke_splits, rule conjI)+
   apply(auto)[1]
  apply(auto simp add: get_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
      intro: reads_subset[OF reads_singleton] reads_subset[OF check_in_heap_reads]
      intro!: reads_bind_pure reads_subset[OF return_reads] split: option.splits)[1]
  done
end

interpretation i_get_child_nodes?: l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr DocumentClass.type_wf
  DocumentClass.known_ptr get_child_nodes get_child_nodes_locs Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs
  by(simp add: l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_child_nodes_is_l_get_child_nodes [instances]: "l_get_child_nodes type_wf known_ptr
    get_child_nodes get_child_nodes_locs"
  apply(auto simp add: l_get_child_nodes_def instances)[1]
  using get_child_nodes_reads get_child_nodes_ok get_child_nodes_ptr_in_heap get_child_nodes_pure
  by blast+


paragraph \<open>new\_document\<close>

locale l_new_document_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  CD: l_new_document_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  + l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes
  get_child_nodes_locs get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool"
    and get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_child_nodes_new_document:
  "ptr' \<noteq> cast new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr
     \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
  apply(auto simp add: get_child_nodes_locs_def)[1]
  using CD.get_child_nodes_new_document
   apply (metis document_ptr_casts_commute3 empty_iff is_document_ptr_kind_none
      new_document_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t option.case_eq_if shadow_root_ptr_casts_commute3 singletonD)
  by (simp add: CD.get_child_nodes_new_document)

lemma new_document_no_child_nodes:
  "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h'
     \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []"
  apply(auto simp add: get_child_nodes_def)[1]
  apply(split CD.get_child_nodes_splits, rule conjI)+
  using CD.new_document_no_child_nodes apply auto[1]
  by(auto simp add: DocumentClass.a_known_ptr_def CD.known_ptr_impl known_ptr_def
      dest!: new_document_is_document_ptr)
end
interpretation i_new_document_get_child_nodes?:
  l_new_document_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  DocumentClass.type_wf DocumentClass.known_ptr Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs
  by(unfold_locales)
declare l_new_document_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma new_document_get_child_nodes_is_l_new_document_get_child_nodes [instances]:
  "l_new_document_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs"
  using new_document_is_l_new_document get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_new_document_get_child_nodes_def l_new_document_get_child_nodes_axioms_def)
  using get_child_nodes_new_document new_document_no_child_nodes
  by fast

paragraph \<open>new\_shadow\_root\<close>

locale l_new_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes
  get_child_nodes_locs get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool"
    and get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_child_nodes_new_shadow_root:
  "ptr' \<noteq> cast new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
     \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
  apply(auto simp add: get_child_nodes_locs_def)[1]
   apply (metis document_ptr_casts_commute3 insert_absorb insert_not_empty is_document_ptr_kind_none
      new_shadow_root_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t option.case_eq_if shadow_root_ptr_casts_commute3 singletonD)
  apply(auto simp add: CD.get_child_nodes_locs_def)[1]
  using new_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t apply blast
   apply (smt insertCI new_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t singleton_iff)
  apply (metis document_ptr_casts_commute3 empty_iff new_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t singletonD)
  done

lemma new_shadow_root_no_child_nodes:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
     \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []"
  apply(auto simp add: get_child_nodes_def )[1]
  apply(split CD.get_child_nodes_splits, rule conjI)+
   apply(auto simp add: CD.get_child_nodes_def CD.a_get_child_nodes_tups_def)[1]
   apply(split invoke_splits, rule conjI)+
  using NodeClass.a_known_ptr_def known_ptr_not_character_data_ptr known_ptr_not_document_ptr
    known_ptr_not_element_ptr local.CD.known_ptr_impl apply blast
     apply(auto simp add: is_document_ptr_def cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
      split: option.splits document_ptr.splits)[1]
    apply(auto simp add: is_character_data_ptr_def cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
      split: option.splits document_ptr.splits)[1]
   apply(auto simp add: is_element_ptr_def cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
      split: option.splits document_ptr.splits)[1]
  apply(auto simp add: a_get_child_nodes_tups_def)[1]
  apply(split invoke_splits, rule conjI)+
   apply(auto simp add: is_shadow_root_ptr_def split: shadow_root_ptr.splits
      dest!: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_is_shadow_root_ptr)[1]
  apply(auto intro!: bind_pure_returns_result_I)[1]
   apply(drule(1) new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_in_heap)
   apply(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)[1]
   apply (metis check_in_heap_ptr_in_heap is_OK_returns_result_E old.unit.exhaust)
  using  new_shadow_root_children
  by (simp add: new_shadow_root_children get_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)
end
interpretation i_new_shadow_root_get_child_nodes?:
  l_new_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr get_child_nodes get_child_nodes_locs
  DocumentClass.type_wf DocumentClass.known_ptr Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs
  by(unfold_locales)
declare l_new_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def[instances]

locale l_new_shadow_root_get_child_nodes = l_get_child_nodes +
  assumes get_child_nodes_new_shadow_root:
    "ptr' \<noteq> cast new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
     \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
  assumes new_shadow_root_no_child_nodes:
    "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
     \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []"

lemma new_shadow_root_get_child_nodes_is_l_new_shadow_root_get_child_nodes [instances]:
  "l_new_shadow_root_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs"
  apply(simp add: l_new_shadow_root_get_child_nodes_def l_new_shadow_root_get_child_nodes_axioms_def instances)
  using get_child_nodes_new_shadow_root new_shadow_root_no_child_nodes
  by fast

paragraph \<open>new\_element\<close>

locale l_new_element_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_new_element_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_child_nodes_new_element:
  "ptr' \<noteq> cast new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
     \<Longrightarrow> r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: get_child_nodes_locs_def CD.get_child_nodes_locs_def new_element_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_element_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      new_element_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t new_element_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t split: prod.splits if_splits option.splits
      elim!: bind_returns_result_E bind_returns_heap_E intro: is_element_ptr_kind_obtains)

lemma new_element_no_child_nodes:
  "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
   \<Longrightarrow> h' \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []"
  apply(auto simp add: get_child_nodes_def a_get_child_nodes_tups_def
      split: prod.splits elim!: bind_returns_result_E bind_returns_heap_E)[1]
  apply(split CD.get_child_nodes_splits, rule conjI)+
  using local.new_element_no_child_nodes apply auto[1]
  apply(auto simp add: invoke_def)[1]
  using case_optionE apply fastforce
  apply(auto simp add: new_element_ptr_in_heap get_child_nodes\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def check_in_heap_def
      new_element_child_nodes intro!: bind_pure_returns_result_I
      intro: new_element_is_element_ptr elim!: new_element_ptr_in_heap)[1]
proof -
  assume " h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
  assume "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
  assume "\<not> is_shadow_root_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr)"
  assume "\<not> known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr)"
  moreover
  have "known_ptr (cast new_element_ptr)"
    using new_element_is_element_ptr \<open>h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr\<close>
    by(auto simp add: known_ptr_impl ShadowRootClass.a_known_ptr_def DocumentClass.a_known_ptr_def
        CharacterDataClass.a_known_ptr_def ElementClass.a_known_ptr_def)
  ultimately show "False"
    by(simp add: known_ptr_impl CD.known_ptr_impl ShadowRootClass.a_known_ptr_def is_document_ptr_kind_none)
qed
end

interpretation i_new_element_get_child_nodes?:
  l_new_element_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr DocumentClass.type_wf
  DocumentClass.known_ptr get_child_nodes get_child_nodes_locs Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs
  by(unfold_locales)
declare l_new_element_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma new_element_get_child_nodes_is_l_new_element_get_child_nodes [instances]:
  "l_new_element_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs"
  using new_element_is_l_new_element get_child_nodes_is_l_get_child_nodes
  apply(auto simp add: l_new_element_get_child_nodes_def l_new_element_get_child_nodes_axioms_def)[1]
  using get_child_nodes_new_element new_element_no_child_nodes
  by fast+


subsubsection \<open>delete\_shadow\_root\<close>

locale l_delete_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_child_nodes_delete_shadow_root:
  "ptr' \<noteq> cast shadow_root_ptr \<Longrightarrow> h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow>
r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: get_child_nodes_locs_def CD.get_child_nodes_locs_def delete_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      delete_shadow_root_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t delete_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t delete_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      split: if_splits  intro: is_shadow_root_ptr_kind_obtains
      intro: is_shadow_root_ptr_kind_obtains delete_shadow_root_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t delete_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      simp add: shadow_root_ptr_casts_commute3 delete_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      intro!: delete_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t dest: document_ptr_casts_commute3
      split: option.splits)
end

locale l_delete_shadow_root_get_child_nodes = l_get_child_nodes_defs +
  assumes get_child_nodes_delete_shadow_root:
    "ptr' \<noteq> cast shadow_root_ptr \<Longrightarrow> h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow>
r \<in> get_child_nodes_locs ptr' \<Longrightarrow> r h h'"

interpretation l_delete_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr DocumentClass.type_wf
  DocumentClass.known_ptr get_child_nodes get_child_nodes_locs Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs
  by(auto simp add: l_delete_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)

lemma l_delete_shadow_root_get_child_nodes_get_child_nodes_locs [instances]: "l_delete_shadow_root_get_child_nodes get_child_nodes_locs"
  apply(auto simp add: l_delete_shadow_root_get_child_nodes_def)[1]
  using get_child_nodes_delete_shadow_root apply fast
  done


subsubsection \<open>set\_child\_nodes\<close>

locale l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  CD: l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition set_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) shadow_root_ptr \<Rightarrow> (_) node_ptr list
    \<Rightarrow> (_, unit) dom_prog" where
  "set_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr = put_M shadow_root_ptr RShadowRoot.child_nodes_update"

definition a_set_child_nodes_tups :: "(((_) object_ptr \<Rightarrow> bool) \<times> ((_) object_ptr \<Rightarrow> (_) node_ptr list
    \<Rightarrow> (_, unit) dom_prog)) list" where
  "a_set_child_nodes_tups \<equiv> [(is_shadow_root_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r, set_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast)]"

definition a_set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
  where
    "a_set_child_nodes ptr children = invoke (CD.a_set_child_nodes_tups @ a_set_child_nodes_tups) ptr children"

definition a_set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> (_, unit) dom_prog set"
  where
    "a_set_child_nodes_locs ptr \<equiv>
      (if is_shadow_root_ptr_kind ptr then all_args (put_M (the (cast ptr)) RShadowRoot.child_nodes_update) else {}) \<union>
      CD.a_set_child_nodes_locs ptr"
end

global_interpretation l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs defines
  set_child_nodes = l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_child_nodes and
  set_child_nodes_locs = l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_set_child_nodes_locs
  .

locale l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_known_ptr known_ptr +
  l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_set_child_nodes_defs set_child_nodes set_child_nodes_locs +
  CD: l_set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool"
    and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
    and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> (_, unit) dom_prog set"
    and set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> (_, unit) dom_prog"
    and set_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> (_, unit) dom_prog set" +
  assumes known_ptr_impl: "known_ptr = ShadowRootClass.known_ptr"
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
  assumes set_child_nodes_impl: "set_child_nodes = a_set_child_nodes"
  assumes set_child_nodes_locs_impl: "set_child_nodes_locs = a_set_child_nodes_locs"
begin
lemmas set_child_nodes_def = set_child_nodes_impl[unfolded a_set_child_nodes_def set_child_nodes_def]
lemmas set_child_nodes_locs_def =set_child_nodes_locs_impl[unfolded a_set_child_nodes_locs_def
    set_child_nodes_locs_def, folded CD.set_child_nodes_locs_impl]

lemma set_child_nodes_writes: "writes (set_child_nodes_locs ptr) (set_child_nodes ptr children) h h'"
  apply (simp add: set_child_nodes_def a_set_child_nodes_tups_def set_child_nodes_locs_def)
  apply(split CD.set_child_nodes_splits, rule conjI)+
   apply (simp add: CD.set_child_nodes_writes writes_union_right_I)
  apply(split invoke_splits, rule conjI)+
   apply(auto simp add: a_set_child_nodes_def)[1]
  apply(auto simp add: set_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: writes_bind_pure
      intro: writes_union_right_I writes_union_left_I split: list.splits)[1]
  by (metis is_shadow_root_ptr_implies_kind option.case_eq_if)

lemma set_child_nodes_pointers_preserved:
  assumes "w \<in> set_child_nodes_locs object_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms(1) object_ptr_kinds_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_child_nodes_locs_def CD.set_child_nodes_locs_def split: if_splits)

lemma set_child_nodes_types_preserved:
  assumes "w \<in> set_child_nodes_locs object_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)] type_wf_impl
  by(auto simp add: all_args_def a_set_child_nodes_tups_def set_child_nodes_locs_def CD.set_child_nodes_locs_def
      split: if_splits option.splits)
end

interpretation
  i_set_child_nodes?: l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr DocumentClass.type_wf
  DocumentClass.known_ptr set_child_nodes set_child_nodes_locs Core_DOM_Functions.set_child_nodes
  Core_DOM_Functions.set_child_nodes_locs
  apply(unfold_locales)
  by (auto simp add: set_child_nodes_def set_child_nodes_locs_def)
declare l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_child_nodes_is_l_set_child_nodes [instances]: "l_set_child_nodes type_wf
set_child_nodes set_child_nodes_locs"
  apply(auto simp add: l_set_child_nodes_def instances)[1]
  using  set_child_nodes_writes apply fast
  using set_child_nodes_pointers_preserved apply(fast, fast)
  using set_child_nodes_types_preserved apply(fast, fast)
  done



paragraph \<open>get\_child\_nodes\<close>

locale l_set_child_nodes_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs
  get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  + l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_child_nodes set_child_nodes_locs
  set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  + CD: l_set_child_nodes_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
begin

lemma set_child_nodes_get_child_nodes:
  assumes "known_ptr ptr"
  assumes "type_wf h"
  assumes "h \<turnstile> set_child_nodes ptr children \<rightarrow>\<^sub>h h'"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
proof -
  have "h \<turnstile> check_in_heap ptr \<rightarrow>\<^sub>r ()"
    using assms set_child_nodes_def invoke_ptr_in_heap
    by (metis (full_types) check_in_heap_ptr_in_heap is_OK_returns_heap_I is_OK_returns_result_E
        old.unit.exhaust)
  then have ptr_in_h: "ptr |\<in>| object_ptr_kinds h"
    by (simp add: check_in_heap_ptr_in_heap is_OK_returns_result_I)

  have "type_wf h'"
    apply(unfold type_wf_impl)
    apply(rule subst[where P=id, OF type_wf_preserved[OF set_child_nodes_writes assms(3),
            unfolded all_args_def], simplified])
    by(auto simp add: all_args_def assms(2)[unfolded type_wf_impl] set_child_nodes_locs_def
        CD.set_child_nodes_locs_def split: if_splits)
  have "h' \<turnstile> check_in_heap ptr \<rightarrow>\<^sub>r ()"
    using check_in_heap_reads set_child_nodes_writes assms(3) \<open>h \<turnstile> check_in_heap ptr \<rightarrow>\<^sub>r ()\<close>
    apply(rule reads_writes_separate_forwards)
    apply(auto simp add: all_args_def set_child_nodes_locs_def CD.set_child_nodes_locs_def)[1]
    done
  then have "ptr |\<in>| object_ptr_kinds h'"
    using check_in_heap_ptr_in_heap by blast
  with assms ptr_in_h \<open>type_wf h'\<close> show ?thesis
    apply(auto simp add: type_wf_impl known_ptr_impl  get_child_nodes_def a_get_child_nodes_tups_def
        set_child_nodes_def a_set_child_nodes_tups_def del: bind_pure_returns_result_I2 intro!: bind_pure_returns_result_I2)[1]
    apply(split CD.get_child_nodes_splits, (rule conjI impI)+)+
     apply(split CD.set_child_nodes_splits)+
      apply(auto simp add: CD.set_child_nodes_get_child_nodes type_wf_impl CD.type_wf_impl
        dest: ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)[1]
     apply(auto simp add: CD.set_child_nodes_get_child_nodes type_wf_impl CD.type_wf_impl
        dest: ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)[1]
    apply(split CD.set_child_nodes_splits)+
    by(auto simp add: known_ptr_impl CD.known_ptr_impl set_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        get_child_nodes\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.type_wf_impl ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t dest: known_ptr_new_shadow_root_ptr)[2]
qed

lemma set_child_nodes_get_child_nodes_different_pointers:
  assumes "ptr \<noteq> ptr'"
  assumes "w \<in> set_child_nodes_locs ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  assumes "r \<in> get_child_nodes_locs ptr'"
  shows "r h h'"
  using assms
  apply(auto simp add: set_child_nodes_locs_def CD.set_child_nodes_locs_def
      get_child_nodes_locs_def CD.get_child_nodes_locs_def)[1]
  by(auto simp add: all_args_def elim!: is_document_ptr_kind_obtains is_shadow_root_ptr_kind_obtains
      is_element_ptr_kind_obtains split: if_splits option.splits)

end

interpretation
  i_set_child_nodes_get_child_nodes?: l_set_child_nodes_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr
  DocumentClass.type_wf DocumentClass.known_ptr get_child_nodes get_child_nodes_locs
  Core_DOM_Functions.get_child_nodes Core_DOM_Functions.get_child_nodes_locs set_child_nodes
  set_child_nodes_locs Core_DOM_Functions.set_child_nodes Core_DOM_Functions.set_child_nodes_locs
  using instances
  by(auto simp add: l_set_child_nodes_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def )
declare l_set_child_nodes_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_child_nodes_get_child_nodes_is_l_set_child_nodes_get_child_nodes [instances]:
  "l_set_child_nodes_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs set_child_nodes set_child_nodes_locs"
  apply(auto simp add: instances l_set_child_nodes_get_child_nodes_def l_set_child_nodes_get_child_nodes_axioms_def)[1]
  using set_child_nodes_get_child_nodes apply fast
  using set_child_nodes_get_child_nodes_different_pointers apply fast
  done


subsubsection \<open>set\_tag\_type\<close>

locale l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  CD: l_set_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_tag_name set_tag_name_locs +
  l_type_wf type_wf
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and set_tag_name :: "(_) element_ptr \<Rightarrow> tag_name \<Rightarrow> (_, unit) dom_prog"
    and set_tag_name_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
begin
lemmas set_tag_name_def = CD.set_tag_name_impl[unfolded CD.a_set_tag_name_def set_tag_name_def]
lemmas set_tag_name_locs_def = CD.set_tag_name_locs_impl[unfolded CD.a_set_tag_name_locs_def
    set_tag_name_locs_def]

lemma set_tag_name_ok:
  "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_tag_name element_ptr tag)"
  apply(unfold type_wf_impl)
  unfolding set_tag_name_impl[unfolded a_set_tag_name_def] using get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok
  using CD.set_tag_name_ok CD.type_wf_impl ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t by blast

lemma set_tag_name_writes:
  "writes (set_tag_name_locs element_ptr) (set_tag_name element_ptr tag) h h'"
  using CD.set_tag_name_writes .

lemma set_tag_name_pointers_preserved:
  assumes "w \<in> set_tag_name_locs element_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms
  by(simp add: CD.set_tag_name_pointers_preserved)

lemma set_tag_name_typess_preserved:
  assumes "w \<in> set_tag_name_locs element_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  apply(unfold type_wf_impl)
  apply(rule type_wf_preserved[OF writes_singleton2 assms(2)])
  using assms(1) set_tag_name_locs_def
  by(auto simp add: all_args_def set_tag_name_locs_def
      split: if_splits)
end

interpretation i_set_tag_name?: l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf set_tag_name
  set_tag_name_locs
  by(auto simp add: l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma set_tag_name_is_l_set_tag_name [instances]: "l_set_tag_name type_wf set_tag_name set_tag_name_locs"
  apply(auto simp add: l_set_tag_name_def)[1]

  using set_tag_name_writes apply fast
  using set_tag_name_ok apply fast
  using set_tag_name_pointers_preserved apply (fast, fast)
  using set_tag_name_typess_preserved apply (fast, fast)
  done

paragraph \<open>get\_child\_nodes\<close>

locale l_set_tag_name_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  CD: l_set_tag_name_get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_tag_name set_tag_name_locs
  known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_tag_name_get_child_nodes:
  "\<forall>w \<in> set_tag_name_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"
  apply(auto simp add: get_child_nodes_locs_def)[1]
    apply(auto simp add: set_tag_name_locs_def all_args_def)[1]
  using CD.set_tag_name_get_child_nodes apply(blast)
  using CD.set_tag_name_get_child_nodes apply(blast)
  done
end

interpretation
  i_set_tag_name_get_child_nodes?: l_set_tag_name_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf
  set_tag_name set_tag_name_locs known_ptr DocumentClass.known_ptr get_child_nodes
  get_child_nodes_locs Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs
  by unfold_locales
declare l_set_tag_name_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_tag_name_get_child_nodes_is_l_set_tag_name_get_child_nodes [instances]:
  "l_set_tag_name_get_child_nodes type_wf set_tag_name set_tag_name_locs known_ptr get_child_nodes
                                         get_child_nodes_locs"
  using set_tag_name_is_l_set_tag_name get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_set_tag_name_get_child_nodes_def
      l_set_tag_name_get_child_nodes_axioms_def)
  using set_tag_name_get_child_nodes
  by fast


subsubsection \<open>get\_shadow\_root\<close>

locale l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition a_get_shadow_root :: "(_) element_ptr \<Rightarrow> (_, (_) shadow_root_ptr option) dom_prog"
  where
    "a_get_shadow_root element_ptr = get_M element_ptr shadow_root_opt"

definition a_get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  where
    "a_get_shadow_root_locs element_ptr \<equiv> {preserved (get_M element_ptr shadow_root_opt)}"
end

global_interpretation l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  defines get_shadow_root = a_get_shadow_root
    and get_shadow_root_locs = a_get_shadow_root_locs
  .

locale l_get_shadow_root_defs =
  fixes get_shadow_root :: "(_) element_ptr \<Rightarrow> (_, (_) shadow_root_ptr option) dom_prog"
  fixes get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_shadow_root_defs get_shadow_root get_shadow_root_locs +
  l_type_wf type_wf
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
  assumes get_shadow_root_impl: "get_shadow_root = a_get_shadow_root"
  assumes get_shadow_root_locs_impl: "get_shadow_root_locs = a_get_shadow_root_locs"
begin
lemmas get_shadow_root_def = get_shadow_root_impl[unfolded get_shadow_root_def a_get_shadow_root_def]
lemmas get_shadow_root_locs_def = get_shadow_root_locs_impl[unfolded get_shadow_root_locs_def a_get_shadow_root_locs_def]

lemma get_shadow_root_ok: "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_shadow_root element_ptr)"
  unfolding get_shadow_root_def type_wf_impl
  using ShadowRootMonad.get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok by blast

lemma get_shadow_root_pure [simp]: "pure (get_shadow_root element_ptr) h"
  unfolding get_shadow_root_def by simp

lemma get_shadow_root_ptr_in_heap:
  assumes "h \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r children"
  shows "element_ptr |\<in>| element_ptr_kinds h"
  using assms
  by(auto simp add: get_shadow_root_def get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_in_heap dest: is_OK_returns_result_I)

lemma get_shadow_root_reads: "reads (get_shadow_root_locs element_ptr) (get_shadow_root element_ptr) h h'"
  by(simp add: get_shadow_root_def get_shadow_root_locs_def reads_bind_pure reads_insert_writes_set_right)
end

interpretation i_get_shadow_root?: l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf  get_shadow_root get_shadow_root_locs
  using instances
  by (auto simp add: l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_get_shadow_root = l_type_wf + l_get_shadow_root_defs +
  assumes get_shadow_root_reads: "reads (get_shadow_root_locs element_ptr) (get_shadow_root element_ptr) h h'"
  assumes get_shadow_root_ok: "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_shadow_root element_ptr)"
  assumes get_shadow_root_ptr_in_heap: "h \<turnstile> ok (get_shadow_root element_ptr) \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h"
  assumes get_shadow_root_pure [simp]: "pure (get_shadow_root element_ptr) h"

lemma get_shadow_root_is_l_get_shadow_root [instances]: "l_get_shadow_root type_wf get_shadow_root get_shadow_root_locs"
  using instances
  apply(auto simp add: l_get_shadow_root_def)[1]
  using get_shadow_root_reads apply blast
  using get_shadow_root_ok apply blast
  using get_shadow_root_ptr_in_heap apply blast
  done


paragraph \<open>set\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_disconnected_nodes set_disconnected_nodes_locs +
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma set_disconnected_nodes_get_shadow_root:
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"
  by(auto simp add: set_disconnected_nodes_locs_def get_shadow_root_locs_def all_args_def)
end

locale l_set_disconnected_nodes_get_shadow_root = l_set_disconnected_nodes_defs + l_get_shadow_root_defs +
  assumes set_disconnected_nodes_get_shadow_root: "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"

interpretation
  i_set_disconnected_nodes_get_shadow_root?: l_set_disconnected_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  DocumentClass.type_wf set_disconnected_nodes set_disconnected_nodes_locs get_shadow_root get_shadow_root_locs
  by(auto simp add: l_set_disconnected_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_disconnected_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_get_shadow_root_is_l_set_disconnected_nodes_get_shadow_root [instances]:
  "l_set_disconnected_nodes_get_shadow_root set_disconnected_nodes_locs get_shadow_root_locs"
  apply(auto simp add: l_set_disconnected_nodes_get_shadow_root_def)[1]
  using set_disconnected_nodes_get_shadow_root apply fast
  done



paragraph \<open>set\_tag\_type\<close>

locale l_set_tag_name_get_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_tag_name_get_shadow_root:
  "\<forall>w \<in> set_tag_name_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"
  by(auto simp add: set_tag_name_locs_def
      get_shadow_root_locs_def all_args_def
      intro: element_put_get_preserved[where setter=tag_name_update and getter=shadow_root_opt])
end

locale l_set_tag_name_get_shadow_root = l_set_tag_name + l_get_shadow_root +
  assumes set_tag_name_get_shadow_root:
    "\<forall>w \<in> set_tag_name_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"

interpretation
  i_set_tag_name_get_shadow_root?: l_set_tag_name_get_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf
  set_tag_name set_tag_name_locs
  get_shadow_root get_shadow_root_locs
  apply(auto simp add: l_set_tag_name_get_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)[1]
  using l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms
  by unfold_locales
declare l_set_tag_name_get_shadow_root\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_tag_name_get_shadow_root_is_l_set_tag_name_get_shadow_root [instances]:
  "l_set_tag_name_get_shadow_root type_wf set_tag_name set_tag_name_locs get_shadow_root
                                  get_shadow_root_locs"
  using set_tag_name_is_l_set_tag_name get_shadow_root_is_l_get_shadow_root
  apply(simp add: l_set_tag_name_get_shadow_root_def l_set_tag_name_get_shadow_root_axioms_def)
  using set_tag_name_get_shadow_root
  by fast


paragraph \<open>set\_child\_nodes\<close>

locale l_set_child_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_child_nodes
  set_child_nodes_locs set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool"
    and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma set_child_nodes_get_shadow_root: "\<forall>w \<in> set_child_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"
  apply(auto simp add: set_child_nodes_locs_def get_shadow_root_locs_def CD.set_child_nodes_locs_def all_args_def)[1]
  by(auto intro!: element_put_get_preserved[where getter=shadow_root_opt and setter=RElement.child_nodes_update])
end

locale l_set_child_nodes_get_shadow_root = l_set_child_nodes_defs + l_get_shadow_root_defs +
  assumes set_child_nodes_get_shadow_root: "\<forall>w \<in> set_child_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"

interpretation
  i_set_child_nodes_get_shadow_root?: l_set_child_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr
  DocumentClass.type_wf DocumentClass.known_ptr set_child_nodes set_child_nodes_locs
  Core_DOM_Functions.set_child_nodes Core_DOM_Functions.set_child_nodes_locs get_shadow_root
  get_shadow_root_locs
  by(auto simp add: l_set_child_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_child_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_child_nodes_get_shadow_root_is_l_set_child_nodes_get_shadow_root [instances]:
  "l_set_child_nodes_get_shadow_root set_child_nodes_locs get_shadow_root_locs"
  apply(auto simp add: l_set_child_nodes_get_shadow_root_def)[1]
  using set_child_nodes_get_shadow_root apply fast
  done


paragraph \<open>delete\_shadow\_root\<close>

locale l_delete_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_shadow_root_delete_shadow_root:  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: get_shadow_root_locs_def delete_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
end

locale l_delete_shadow_root_get_shadow_root = l_get_shadow_root_defs +
  assumes get_shadow_root_delete_shadow_root:  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"
interpretation l_delete_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  by(auto simp add: l_delete_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)

lemma l_delete_shadow_root_get_shadow_root_get_shadow_root_locs [instances]: "l_delete_shadow_root_get_shadow_root get_shadow_root_locs"
  apply(auto simp add: l_delete_shadow_root_get_shadow_root_def)[1]
  using get_shadow_root_delete_shadow_root apply fast
  done



paragraph \<open>new\_character\_data\<close>

locale l_new_character_data_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_shadow_root_new_character_data:
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'
     \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: get_shadow_root_locs_def new_character_data_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_character_data_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      split: prod.splits if_splits option.splits
      elim!: bind_returns_result_E bind_returns_heap_E intro: is_element_ptr_kind_obtains)
end

locale l_new_character_data_get_shadow_root = l_new_character_data + l_get_shadow_root +
  assumes get_shadow_root_new_character_data:
    "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr
            \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"


interpretation i_new_character_data_get_shadow_root?:
  l_new_character_data_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  by(unfold_locales)
declare l_new_character_data_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma new_character_data_get_shadow_root_is_l_new_character_data_get_shadow_root [instances]:
  "l_new_character_data_get_shadow_root type_wf get_shadow_root get_shadow_root_locs"
  using new_character_data_is_l_new_character_data get_shadow_root_is_l_get_shadow_root
  apply(auto simp add: l_new_character_data_get_shadow_root_def
      l_new_character_data_get_shadow_root_axioms_def instances)[1]
  using get_shadow_root_new_character_data
  by fast






paragraph \<open>new\_document\<close>

locale l_new_document_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_shadow_root_new_document:
  "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h'
     \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: get_shadow_root_locs_def new_document_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_document_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      split: prod.splits if_splits option.splits
      elim!: bind_returns_result_E bind_returns_heap_E intro: is_element_ptr_kind_obtains)
end

locale l_new_document_get_shadow_root = l_new_document + l_get_shadow_root +
  assumes get_shadow_root_new_document:
    "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr
            \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"


interpretation i_new_document_get_shadow_root?:
  l_new_document_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  by(unfold_locales)
declare l_new_document_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma new_document_get_shadow_root_is_l_new_document_get_shadow_root [instances]:
  "l_new_document_get_shadow_root type_wf get_shadow_root get_shadow_root_locs"
  using new_document_is_l_new_document get_shadow_root_is_l_get_shadow_root
  apply(auto simp add: l_new_document_get_shadow_root_def l_new_document_get_shadow_root_axioms_def instances)[1]
  using get_shadow_root_new_document
  by fast




paragraph \<open>new\_element\<close>

locale l_new_element_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_shadow_root_new_element:
  "ptr' \<noteq> new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
     \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: get_shadow_root_locs_def new_element_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_element_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      new_element_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t split: prod.splits if_splits option.splits
      elim!: bind_returns_result_E bind_returns_heap_E intro: is_element_ptr_kind_obtains)

lemma new_element_no_shadow_root:
  "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
   \<Longrightarrow> h' \<turnstile> get_shadow_root new_element_ptr \<rightarrow>\<^sub>r None"
  by(simp add: get_shadow_root_def new_element_shadow_root_opt)
end

locale l_new_element_get_shadow_root = l_new_element + l_get_shadow_root +
  assumes get_shadow_root_new_element:
    "ptr' \<noteq> new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr
            \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"
  assumes new_element_no_shadow_root:
    "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
            \<Longrightarrow> h' \<turnstile> get_shadow_root new_element_ptr \<rightarrow>\<^sub>r None"


interpretation i_new_element_get_shadow_root?:
  l_new_element_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  by(unfold_locales)
declare l_new_element_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma new_element_get_shadow_root_is_l_new_element_get_shadow_root [instances]:
  "l_new_element_get_shadow_root type_wf get_shadow_root get_shadow_root_locs"
  using new_element_is_l_new_element get_shadow_root_is_l_get_shadow_root
  apply(auto simp add: l_new_element_get_shadow_root_def l_new_element_get_shadow_root_axioms_def instances)[1]
  using get_shadow_root_new_element new_element_no_shadow_root
  by fast+

paragraph \<open>new\_shadow\_root\<close>

locale l_new_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_shadow_root_new_shadow_root:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
     \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: get_shadow_root_locs_def new_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      split: prod.splits if_splits option.splits
      elim!: bind_returns_result_E bind_returns_heap_E intro: is_element_ptr_kind_obtains)
end

locale l_new_shadow_root_get_shadow_root = l_get_shadow_root +
  assumes get_shadow_root_new_shadow_root:
    "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
            \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow> r h h'"

interpretation i_new_shadow_root_get_shadow_root?:
  l_new_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  by(unfold_locales)
declare l_new_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma new_shadow_root_get_shadow_root_is_l_new_shadow_root_get_shadow_root [instances]:
  "l_new_shadow_root_get_shadow_root type_wf get_shadow_root get_shadow_root_locs"
  using get_shadow_root_is_l_get_shadow_root
  apply(auto simp add: l_new_shadow_root_get_shadow_root_def l_new_shadow_root_get_shadow_root_axioms_def instances)[1]
  using get_shadow_root_new_shadow_root
  by fast


subsubsection \<open>set\_shadow\_root\<close>

locale l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition a_set_shadow_root :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> (_, unit) dom_prog"
  where
    "a_set_shadow_root element_ptr = put_M element_ptr shadow_root_opt_update"

definition a_set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_, unit) dom_prog) set"
  where
    "a_set_shadow_root_locs element_ptr \<equiv> all_args (put_M element_ptr shadow_root_opt_update)"
end

global_interpretation l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  defines set_shadow_root = a_set_shadow_root
    and set_shadow_root_locs = a_set_shadow_root_locs
  .

locale l_set_shadow_root_defs =
  fixes set_shadow_root :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> (_, unit) dom_prog"
  fixes set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set"


locale l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_set_shadow_root_defs set_shadow_root set_shadow_root_locs +
  l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and set_shadow_root :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> (_, unit) dom_prog"
    and set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
  assumes set_shadow_root_impl: "set_shadow_root = a_set_shadow_root"
  assumes set_shadow_root_locs_impl: "set_shadow_root_locs = a_set_shadow_root_locs"
begin
lemmas set_shadow_root_def = set_shadow_root_impl[unfolded set_shadow_root_def a_set_shadow_root_def]
lemmas set_shadow_root_locs_def = set_shadow_root_locs_impl[unfolded set_shadow_root_locs_def a_set_shadow_root_locs_def]

lemma set_shadow_root_ok: "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_shadow_root element_ptr tag)"
  apply(unfold type_wf_impl)
  unfolding set_shadow_root_def using get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok
  by (simp add: ShadowRootMonad.put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ok)

lemma set_shadow_root_ptr_in_heap:
  "h \<turnstile> ok (set_shadow_root element_ptr shadow_root) \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h"
  by(simp add: set_shadow_root_def ElementMonad.put_M_ptr_in_heap)

lemma set_shadow_root_writes: "writes (set_shadow_root_locs element_ptr) (set_shadow_root element_ptr tag) h h'"
  by(auto simp add: set_shadow_root_def set_shadow_root_locs_def intro: writes_bind_pure)

lemma set_shadow_root_pointers_preserved:
  assumes "w \<in> set_shadow_root_locs element_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms(1) object_ptr_kinds_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_shadow_root_locs_def split: if_splits)

lemma set_shadow_root_types_preserved:
  assumes "w \<in> set_shadow_root_locs element_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  apply(unfold type_wf_impl)
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_shadow_root_locs_def split: if_splits)
end

interpretation i_set_shadow_root?: l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_shadow_root set_shadow_root_locs
  by (auto simp add: l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_set_shadow_root = l_type_wf +l_set_shadow_root_defs +
  assumes set_shadow_root_writes:
    "writes (set_shadow_root_locs element_ptr) (set_shadow_root element_ptr disc_nodes) h h'"
  assumes set_shadow_root_ok:
    "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_shadow_root element_ptr shadow_root)"
  assumes set_shadow_root_ptr_in_heap:
    "h \<turnstile> ok (set_shadow_root element_ptr shadow_root) \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h"
  assumes set_shadow_root_pointers_preserved:
    "w \<in> set_shadow_root_locs element_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
  assumes set_shadow_root_types_preserved:
    "w \<in> set_shadow_root_locs element_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"

lemma set_shadow_root_is_l_set_shadow_root [instances]: "l_set_shadow_root type_wf set_shadow_root set_shadow_root_locs"
  apply(auto simp add: l_set_shadow_root_def instances)[1]
  using set_shadow_root_writes apply blast
  using set_shadow_root_ok apply (blast)
  using set_shadow_root_ptr_in_heap apply blast
  using set_shadow_root_pointers_preserved apply(blast, blast)
  using set_shadow_root_types_preserved apply(blast, blast)
  done

paragraph \<open>get\_shadow\_root\<close>

locale l_set_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_shadow_root_get_shadow_root:
  "type_wf h \<Longrightarrow> h \<turnstile> set_shadow_root ptr shadow_root_ptr_opt \<rightarrow>\<^sub>h h' \<Longrightarrow>
h' \<turnstile> get_shadow_root ptr \<rightarrow>\<^sub>r shadow_root_ptr_opt"
  by(auto simp add: set_shadow_root_def get_shadow_root_def)

lemma set_shadow_root_get_shadow_root_different_pointers:
  "ptr \<noteq> ptr' \<Longrightarrow> \<forall>w \<in> set_shadow_root_locs ptr.
(h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"
  by(auto simp add: set_shadow_root_locs_def get_shadow_root_locs_def all_args_def)
end

interpretation
  i_set_shadow_root_get_shadow_root?: l_set_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  set_shadow_root set_shadow_root_locs get_shadow_root get_shadow_root_locs
  apply(auto simp add: l_set_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)[1]
  by(unfold_locales)
declare l_set_shadow_root_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_set_shadow_root_get_shadow_root = l_type_wf + l_set_shadow_root_defs + l_get_shadow_root_defs +
  assumes set_shadow_root_get_shadow_root:
    "type_wf h \<Longrightarrow> h \<turnstile> set_shadow_root ptr shadow_root_ptr_opt \<rightarrow>\<^sub>h h' \<Longrightarrow>
h' \<turnstile> get_shadow_root ptr \<rightarrow>\<^sub>r shadow_root_ptr_opt"
  assumes set_shadow_root_get_shadow_root_different_pointers:
    "ptr \<noteq> ptr' \<Longrightarrow> w \<in> set_shadow_root_locs ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_shadow_root_locs ptr' \<Longrightarrow>
r h h'"

lemma set_shadow_root_get_shadow_root_is_l_set_shadow_root_get_shadow_root [instances]:
  "l_set_shadow_root_get_shadow_root type_wf set_shadow_root set_shadow_root_locs get_shadow_root
get_shadow_root_locs"
  apply(auto simp add: l_set_shadow_root_get_shadow_root_def instances)[1]
  using set_shadow_root_get_shadow_root apply fast
  using set_shadow_root_get_shadow_root_different_pointers apply fast
  done


subsubsection \<open>set\_mode\<close>

locale l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition a_set_mode :: "(_) shadow_root_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> (_, unit) dom_prog"
  where
    "a_set_mode shadow_root_ptr = put_M shadow_root_ptr mode_update"

definition a_set_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_, unit) dom_prog) set"
  where
    "a_set_mode_locs shadow_root_ptr \<equiv> all_args (put_M shadow_root_ptr mode_update)"
end

global_interpretation l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  defines set_mode = a_set_mode
    and set_mode_locs = a_set_mode_locs
  .

locale l_set_mode_defs =
  fixes set_mode :: "(_) shadow_root_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> (_, unit) dom_prog"
  fixes set_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> (_, unit) dom_prog set"


locale l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_type_wf type_wf +
  l_set_mode_defs set_mode set_mode_locs +
  l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and set_mode :: "(_) shadow_root_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> (_, unit) dom_prog"
    and set_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> (_, unit) dom_prog set" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
  assumes set_mode_impl: "set_mode = a_set_mode"
  assumes set_mode_locs_impl: "set_mode_locs = a_set_mode_locs"
begin
lemmas set_mode_def = set_mode_impl[unfolded set_mode_def a_set_mode_def]
lemmas set_mode_locs_def = set_mode_locs_impl[unfolded set_mode_locs_def a_set_mode_locs_def]

lemma set_mode_ok: "type_wf h \<Longrightarrow> shadow_root_ptr |\<in>| shadow_root_ptr_kinds h \<Longrightarrow>
h \<turnstile> ok (set_mode shadow_root_ptr shadow_root_mode)"
  apply(unfold type_wf_impl)
  unfolding set_mode_def using get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ok put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ok
  by (simp add: ShadowRootMonad.put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ok)

lemma set_mode_ptr_in_heap:
  "h \<turnstile> ok (set_mode shadow_root_ptr shadow_root_mode) \<Longrightarrow> shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  by(simp add: set_mode_def put_M_ptr_in_heap)

lemma set_mode_writes: "writes (set_mode_locs shadow_root_ptr) (set_mode shadow_root_ptr shadow_root_mode) h h'"
  by(auto simp add: set_mode_def set_mode_locs_def intro: writes_bind_pure)

lemma set_mode_pointers_preserved:
  assumes "w \<in> set_mode_locs element_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms(1) object_ptr_kinds_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_mode_locs_def split: if_splits)

lemma set_mode_types_preserved:
  assumes "w \<in> set_mode_locs element_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  apply(unfold type_wf_impl)
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def set_mode_locs_def split: if_splits)
end

interpretation i_set_mode?: l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_mode set_mode_locs
  by (auto simp add: l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_set_mode = l_type_wf +l_set_mode_defs +
  assumes set_mode_writes:
    "writes (set_mode_locs shadow_root_ptr) (set_mode shadow_root_ptr shadow_root_mode) h h'"
  assumes set_mode_ok:
    "type_wf h \<Longrightarrow> shadow_root_ptr |\<in>| shadow_root_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_mode shadow_root_ptr shadow_root_mode)"
  assumes set_mode_ptr_in_heap:
    "h \<turnstile> ok (set_mode shadow_root_ptr shadow_root_mode) \<Longrightarrow> shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  assumes set_mode_pointers_preserved:
    "w \<in> set_mode_locs shadow_root_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
  assumes set_mode_types_preserved:
    "w \<in> set_mode_locs shadow_root_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"

lemma set_mode_is_l_set_mode [instances]: "l_set_mode type_wf set_mode set_mode_locs"
  apply(auto simp add: l_set_mode_def instances)[1]
  using set_mode_writes apply blast
  using set_mode_ok apply (blast)
  using set_mode_ptr_in_heap apply blast
  using set_mode_pointers_preserved apply(blast, blast)
  using set_mode_types_preserved apply(blast, blast)
  done


paragraph \<open>get\_child\_nodes\<close>

locale l_set_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_shadow_root_get_child_nodes:
  "\<forall>w \<in> set_shadow_root_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"
  by(auto simp add: get_child_nodes_locs_def set_shadow_root_locs_def CD.get_child_nodes_locs_def
      all_args_def intro: element_put_get_preserved[where setter=shadow_root_opt_update])
end

interpretation i_set_shadow_root_get_child_nodes?:
  l_set_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr DocumentClass.type_wf
  DocumentClass.known_ptr get_child_nodes get_child_nodes_locs Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs set_shadow_root set_shadow_root_locs
  by(unfold_locales)
declare l_set_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_set_shadow_root_get_child_nodes = l_set_shadow_root + l_get_child_nodes +
  assumes set_shadow_root_get_child_nodes:
    "\<forall>w \<in> set_shadow_root_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"

lemma set_shadow_root_get_child_nodes_is_l_set_shadow_root_get_child_nodes [instances]:
  "l_set_shadow_root_get_child_nodes type_wf set_shadow_root set_shadow_root_locs known_ptr
get_child_nodes get_child_nodes_locs"
  apply(auto simp add: l_set_shadow_root_get_child_nodes_def l_set_shadow_root_get_child_nodes_axioms_def
      instances)[1]
  using set_shadow_root_get_child_nodes apply blast
  done

paragraph \<open>get\_shadow\_root\<close>

locale l_set_mode_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_mode_get_shadow_root:
  "\<forall>w \<in> set_mode_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"
  by(auto simp add: set_mode_locs_def get_shadow_root_locs_def all_args_def)
end

interpretation
  i_set_mode_get_shadow_root?: l_set_mode_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  set_mode set_mode_locs get_shadow_root
  get_shadow_root_locs
  by unfold_locales
declare l_set_mode_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_set_mode_get_shadow_root = l_set_mode + l_get_shadow_root +
  assumes set_mode_get_shadow_root:
    "\<forall>w \<in> set_mode_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"

lemma set_mode_get_shadow_root_is_l_set_mode_get_shadow_root [instances]:
  "l_set_mode_get_shadow_root type_wf set_mode set_mode_locs get_shadow_root
                                         get_shadow_root_locs"
  using set_mode_is_l_set_mode get_shadow_root_is_l_get_shadow_root
  apply(simp add: l_set_mode_get_shadow_root_def
      l_set_mode_get_shadow_root_axioms_def)
  using set_mode_get_shadow_root
  by fast

paragraph \<open>get\_child\_nodes\<close>

locale l_set_mode_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_mode_get_child_nodes:
  "\<forall>w \<in> set_mode_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"
  by(auto simp add: get_child_nodes_locs_def CD.get_child_nodes_locs_def set_mode_locs_def all_args_def)[1]
end

interpretation
  i_set_mode_get_child_nodes?: l_set_mode_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_mode set_mode_locs known_ptr DocumentClass.type_wf
  DocumentClass.known_ptr get_child_nodes
  get_child_nodes_locs Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs
  by unfold_locales
declare l_set_mode_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_set_mode_get_child_nodes = l_set_mode + l_get_child_nodes +
  assumes set_mode_get_child_nodes:
    "\<forall>w \<in> set_mode_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"

lemma set_mode_get_child_nodes_is_l_set_mode_get_child_nodes [instances]:
  "l_set_mode_get_child_nodes type_wf set_mode set_mode_locs known_ptr get_child_nodes
                                         get_child_nodes_locs"
  using set_mode_is_l_set_mode get_child_nodes_is_l_get_child_nodes
  apply(simp add: l_set_mode_get_child_nodes_def
      l_set_mode_get_child_nodes_axioms_def)
  using set_mode_get_child_nodes
  by fast


subsubsection \<open>get\_host\<close>

locale l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_shadow_root_defs get_shadow_root get_shadow_root_locs
  for get_shadow_root :: "(_::linorder) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_get_host :: "(_) shadow_root_ptr \<Rightarrow> (_, (_) element_ptr) dom_prog"
  where
    "a_get_host shadow_root_ptr = do {
      host_ptrs \<leftarrow> element_ptr_kinds_M \<bind> filter_M (\<lambda>element_ptr. do {
        shadow_root_opt \<leftarrow> get_shadow_root element_ptr;
        return (shadow_root_opt = Some shadow_root_ptr)
      });
      (case host_ptrs of host_ptr#[] \<Rightarrow> return host_ptr | _ \<Rightarrow> error HierarchyRequestError)
    }"
definition "a_get_host_locs \<equiv> (\<Union>element_ptr. (get_shadow_root_locs element_ptr)) \<union>
(\<Union>ptr. {preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr RObject.nothing)})"

end

global_interpretation l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_shadow_root get_shadow_root_locs
  defines get_host = "a_get_host"
    and get_host_locs = "a_get_host_locs"
  .

locale l_get_host_defs =
  fixes get_host :: "(_) shadow_root_ptr \<Rightarrow> (_, (_) element_ptr) dom_prog"
  fixes get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_host_defs +
  l_get_shadow_root +
  assumes get_host_impl: "get_host = a_get_host"
  assumes get_host_locs_impl: "get_host_locs = a_get_host_locs"
begin
lemmas get_host_def = get_host_impl[unfolded a_get_host_def]
lemmas get_host_locs_def = get_host_locs_impl[unfolded a_get_host_locs_def]

lemma get_host_pure [simp]: "pure (get_host element_ptr) h"
  by(auto simp add: get_host_def intro!: bind_pure_I filter_M_pure_I split: list.splits)

lemma get_host_reads: "reads get_host_locs (get_host element_ptr) h h'"
  using get_shadow_root_reads[unfolded reads_def]
  by(auto simp add: get_host_def get_host_locs_def intro!: reads_bind_pure
      reads_subset[OF check_in_heap_reads] reads_subset[OF error_reads] reads_subset[OF get_shadow_root_reads]
      reads_subset[OF return_reads] reads_subset[OF element_ptr_kinds_M_reads] filter_M_reads filter_M_pure_I
      bind_pure_I split: list.splits)
end

locale l_get_host = l_get_host_defs +
  assumes get_host_pure [simp]: "pure (get_host element_ptr) h"
  assumes get_host_reads: "reads get_host_locs (get_host node_ptr) h h'"


interpretation i_get_host?: l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_shadow_root get_shadow_root_locs get_host
  get_host_locs type_wf
  using instances
  by (simp add: l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def get_host_def get_host_locs_def)
declare l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_host_is_l_get_host [instances]: "l_get_host get_host get_host_locs"
  apply(auto simp add: l_get_host_def)[1]
  using get_host_reads apply fast
  done



subsubsection \<open>get\_mode\<close>

locale l_get_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
begin
definition a_get_mode :: "(_) shadow_root_ptr \<Rightarrow> (_, shadow_root_mode) dom_prog"
  where
    "a_get_mode shadow_root_ptr = get_M shadow_root_ptr mode"

definition a_get_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  where
    "a_get_mode_locs shadow_root_ptr \<equiv> {preserved (get_M shadow_root_ptr mode)}"
end

global_interpretation l_get_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  defines get_mode = a_get_mode
    and get_mode_locs = a_get_mode_locs
  .

locale l_get_mode_defs =
  fixes get_mode :: "(_) shadow_root_ptr \<Rightarrow> (_, shadow_root_mode) dom_prog"
  fixes get_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_mode_defs get_mode get_mode_locs +
  l_type_wf type_wf
  for get_mode :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, shadow_root_mode) prog"
    and get_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and type_wf :: "(_) heap \<Rightarrow> bool" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
  assumes get_mode_impl: "get_mode = a_get_mode"
  assumes get_mode_locs_impl: "get_mode_locs = a_get_mode_locs"
begin
lemmas get_mode_def = get_mode_impl[unfolded get_mode_def a_get_mode_def]
lemmas get_mode_locs_def = get_mode_locs_impl[unfolded get_mode_locs_def a_get_mode_locs_def]

lemma get_mode_ok: "type_wf h \<Longrightarrow> shadow_root_ptr |\<in>| shadow_root_ptr_kinds h \<Longrightarrow>
h \<turnstile> ok (get_mode shadow_root_ptr)"
  unfolding get_mode_def type_wf_impl
  using ShadowRootMonad.get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ok by blast

lemma get_mode_pure [simp]: "pure (get_mode element_ptr) h"
  unfolding get_mode_def by simp

lemma get_mode_ptr_in_heap:
  assumes "h \<turnstile> get_mode shadow_root_ptr \<rightarrow>\<^sub>r children"
  shows "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  using assms
  by(auto simp add: get_mode_def get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ptr_in_heap dest: is_OK_returns_result_I)

lemma get_mode_reads: "reads (get_mode_locs element_ptr) (get_mode element_ptr) h h'"
  by(simp add: get_mode_def get_mode_locs_def reads_bind_pure reads_insert_writes_set_right)
end

interpretation i_get_mode?: l_get_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_mode get_mode_locs type_wf
  using instances
  by (auto simp add: l_get_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_get_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_get_mode = l_type_wf + l_get_mode_defs +
  assumes get_mode_reads: "reads (get_mode_locs shadow_root_ptr) (get_mode shadow_root_ptr) h h'"
  assumes get_mode_ok: "type_wf h \<Longrightarrow> shadow_root_ptr |\<in>| shadow_root_ptr_kinds h \<Longrightarrow>
h \<turnstile> ok (get_mode shadow_root_ptr)"
  assumes get_mode_ptr_in_heap: "h \<turnstile> ok (get_mode shadow_root_ptr) \<Longrightarrow> shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  assumes get_mode_pure [simp]: "pure (get_mode shadow_root_ptr) h"

lemma get_mode_is_l_get_mode [instances]: "l_get_mode type_wf get_mode get_mode_locs"
  apply(auto simp add: l_get_mode_def instances)[1]
  using get_mode_reads apply blast
  using get_mode_ok apply blast
  using get_mode_ptr_in_heap apply blast
  done



subsubsection \<open>get\_shadow\_root\_safe\<close>

locale l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_shadow_root_defs get_shadow_root get_shadow_root_locs +
  l_get_mode_defs get_mode get_mode_locs
  for get_shadow_root :: "(_) element_ptr \<Rightarrow> (_, (_) shadow_root_ptr option) dom_prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_mode :: "(_) shadow_root_ptr \<Rightarrow> (_, shadow_root_mode) dom_prog"
    and get_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_get_shadow_root_safe :: "(_) element_ptr \<Rightarrow> (_, (_) shadow_root_ptr option) dom_prog"
  where
    "a_get_shadow_root_safe element_ptr = do {
      shadow_root_ptr_opt \<leftarrow> get_shadow_root element_ptr;
      (case shadow_root_ptr_opt of
        Some shadow_root_ptr \<Rightarrow> do {
          mode \<leftarrow> get_mode shadow_root_ptr;
          (if mode = Open then
            return (Some shadow_root_ptr)
          else
            return None
          )
        } | None \<Rightarrow> return None)
    }"

definition a_get_shadow_root_safe_locs ::
  "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  where
    "a_get_shadow_root_safe_locs element_ptr shadow_root_ptr \<equiv>
(get_shadow_root_locs element_ptr) \<union> (get_mode_locs shadow_root_ptr)"
end

global_interpretation l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_shadow_root get_shadow_root_locs get_mode get_mode_locs
  defines get_shadow_root_safe = a_get_shadow_root_safe
    and get_shadow_root_safe_locs = a_get_shadow_root_safe_locs
  .

locale l_get_shadow_root_safe_defs =
  fixes get_shadow_root_safe :: "(_) element_ptr \<Rightarrow> (_, (_) shadow_root_ptr option) dom_prog"
  fixes get_shadow_root_safe_locs ::
    "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_shadow_root get_shadow_root_locs get_mode get_mode_locs +
  l_get_shadow_root_safe_defs get_shadow_root_safe get_shadow_root_safe_locs +
  l_get_shadow_root  type_wf get_shadow_root get_shadow_root_locs +
  l_get_mode  type_wf get_mode get_mode_locs +
  l_type_wf type_wf
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and get_shadow_root_safe :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_safe_locs :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> (_, (_) shadow_root_ptr option) dom_prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_mode :: "(_) shadow_root_ptr \<Rightarrow> (_, shadow_root_mode) dom_prog"
    and get_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
  assumes get_shadow_root_safe_impl: "get_shadow_root_safe = a_get_shadow_root_safe"
  assumes get_shadow_root_safe_locs_impl: "get_shadow_root_safe_locs = a_get_shadow_root_safe_locs"
begin
lemmas get_shadow_root_safe_def = get_shadow_root_safe_impl[unfolded get_shadow_root_safe_def
    a_get_shadow_root_safe_def]
lemmas get_shadow_root_safe_locs_def = get_shadow_root_safe_locs_impl[unfolded get_shadow_root_safe_locs_def
    a_get_shadow_root_safe_locs_def]

lemma get_shadow_root_safe_pure [simp]: "pure (get_shadow_root_safe element_ptr) h"
  apply(auto simp add: get_shadow_root_safe_def)[1]
  by (smt bind_returns_heap_E is_OK_returns_heap_E local.get_mode_pure local.get_shadow_root_pure
      option.case_eq_if pure_def pure_returns_heap_eq return_pure)
end

interpretation i_get_shadow_root_safe?: l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M  type_wf get_shadow_root_safe
  get_shadow_root_safe_locs get_shadow_root get_shadow_root_locs get_mode get_mode_locs
  using instances
  by (auto simp add: l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      get_shadow_root_safe_def get_shadow_root_safe_locs_def)
declare l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_get_shadow_root_safe = l_get_shadow_root_safe_defs +
  assumes get_shadow_root_safe_pure [simp]: "pure (get_shadow_root_safe element_ptr) h"

lemma get_shadow_root_safe_is_l_get_shadow_root_safe [instances]: "l_get_shadow_root_safe get_shadow_root_safe"
  using instances
  apply(auto simp add: l_get_shadow_root_safe_def)[1]
  done


subsubsection \<open>set\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  CD: l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_disconnected_nodes set_disconnected_nodes_locs +
  l_type_wf type_wf
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
begin
lemma set_disconnected_nodes_ok:
  "type_wf h \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (set_disconnected_nodes document_ptr node_ptrs)"
  using CD.set_disconnected_nodes_ok CD.type_wf_impl ShadowRootClass.type_wf_defs local.type_wf_impl
  by blast

lemma set_disconnected_nodes_typess_preserved:
  assumes "w \<in> set_disconnected_nodes_locs object_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)]
  apply(unfold type_wf_impl)
  by(auto simp add: all_args_def CD.set_disconnected_nodes_locs_def
      intro: put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_disconnected_nodes_type_wf_preserved split: if_splits)
end

interpretation i_set_disconnected_nodes?: l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf
  set_disconnected_nodes set_disconnected_nodes_locs
  by(auto simp add: l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma set_disconnected_nodes_is_l_set_disconnected_nodes [instances]:
  "l_set_disconnected_nodes type_wf set_disconnected_nodes set_disconnected_nodes_locs"
  apply(auto simp add: l_set_disconnected_nodes_def)[1]
        apply (simp add: i_set_disconnected_nodes.set_disconnected_nodes_writes)
  using set_disconnected_nodes_ok apply blast
      apply (simp add: i_set_disconnected_nodes.set_disconnected_nodes_ptr_in_heap)
  using i_set_disconnected_nodes.set_disconnected_nodes_pointers_preserved apply (blast, blast)
  using set_disconnected_nodes_typess_preserved apply(blast, blast)
  done


paragraph \<open>get\_child\_nodes\<close>

locale l_set_disconnected_nodes_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_disconnected_nodes set_disconnected_nodes_locs +
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes
  get_child_nodes_locs get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin

lemma set_disconnected_nodes_get_child_nodes:
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_child_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_disconnected_nodes_locs_def get_child_nodes_locs_def CD.get_child_nodes_locs_def
      all_args_def)
end

interpretation i_set_disconnected_nodes_get_child_nodes?: l_set_disconnected_nodes_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf set_disconnected_nodes set_disconnected_nodes_locs known_ptr DocumentClass.type_wf
  DocumentClass.known_ptr get_child_nodes get_child_nodes_locs Core_DOM_Functions.get_child_nodes
  Core_DOM_Functions.get_child_nodes_locs
  by(auto simp add: l_set_disconnected_nodes_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_disconnected_nodes_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_get_child_nodes_is_l_set_disconnected_nodes_get_child_nodes [instances]:
  "l_set_disconnected_nodes_get_child_nodes set_disconnected_nodes_locs get_child_nodes_locs"
  apply(auto simp add: l_set_disconnected_nodes_get_child_nodes_def)[1]
  using set_disconnected_nodes_get_child_nodes apply fast
  done


paragraph \<open>get\_host\<close>

locale l_set_disconnected_nodes_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_disconnected_nodes_get_host:
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_host_locs. r h h'))"
  by(auto simp add: CD.set_disconnected_nodes_locs_def get_shadow_root_locs_def get_host_locs_def all_args_def)
end

interpretation i_set_disconnected_nodes_get_host?: l_set_disconnected_nodes_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf DocumentClass.type_wf set_disconnected_nodes set_disconnected_nodes_locs get_shadow_root
  get_shadow_root_locs get_host get_host_locs
  by(auto simp add: l_set_disconnected_nodes_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_disconnected_nodes_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_set_disconnected_nodes_get_host = l_set_disconnected_nodes_defs + l_get_host_defs +
  assumes set_disconnected_nodes_get_host:
    "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_host_locs. r h h'))"

lemma set_disconnected_nodes_get_host_is_l_set_disconnected_nodes_get_host [instances]:
  "l_set_disconnected_nodes_get_host set_disconnected_nodes_locs get_host_locs"
  apply(auto simp add: l_set_disconnected_nodes_get_host_def instances)[1]
  using set_disconnected_nodes_get_host
  by fast



subsubsection \<open>get\_tag\_name\<close>

locale l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  CD: l_get_tag_name\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_tag_name get_tag_name_locs +
  l_type_wf type_wf
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> (_, tag_name) dom_prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
begin

lemma get_tag_name_ok:
  "type_wf h \<Longrightarrow> element_ptr |\<in>| element_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_tag_name element_ptr)"
  apply(unfold type_wf_impl get_tag_name_impl[unfolded a_get_tag_name_def])
  using CD.get_tag_name_ok CD.type_wf_impl ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t
  by blast
end

interpretation i_get_tag_name?: l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf get_tag_name get_tag_name_locs
  by(auto simp add: l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_tag_name_is_l_get_tag_name [instances]: "l_get_tag_name type_wf get_tag_name get_tag_name_locs"
  apply(auto simp add: l_get_tag_name_def)[1]
  using get_tag_name_reads apply fast
  using get_tag_name_ok apply fast
  done


paragraph \<open>set\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_disconnected_nodes_get_tag_name:
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"
  by(auto simp add: CD.set_disconnected_nodes_locs_def CD.get_tag_name_locs_def all_args_def)
end

interpretation i_set_disconnected_nodes_get_tag_name?: l_set_disconnected_nodes_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf DocumentClass.type_wf set_disconnected_nodes set_disconnected_nodes_locs get_tag_name
  get_tag_name_locs
  by(auto simp add: l_set_disconnected_nodes_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_disconnected_nodes_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma set_disconnected_nodes_get_tag_name_is_l_set_disconnected_nodes_get_tag_name [instances]:
  "l_set_disconnected_nodes_get_tag_name type_wf set_disconnected_nodes set_disconnected_nodes_locs
get_tag_name get_tag_name_locs"
  apply(auto simp add: l_set_disconnected_nodes_get_tag_name_def
      l_set_disconnected_nodes_get_tag_name_axioms_def instances)[1]
  using set_disconnected_nodes_get_tag_name
  by fast


paragraph \<open>set\_child\_nodes\<close>

locale l_set_child_nodes_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_child_nodes_get_tag_name:
  "\<forall>w \<in> set_child_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"
  by(auto simp add: CD.set_child_nodes_locs_def set_child_nodes_locs_def CD.get_tag_name_locs_def
      all_args_def intro: element_put_get_preserved[where getter=tag_name and setter=RElement.child_nodes_update])
end

interpretation i_set_child_nodes_get_tag_name?: l_set_child_nodes_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr
  DocumentClass.type_wf DocumentClass.known_ptr set_child_nodes set_child_nodes_locs
  Core_DOM_Functions.set_child_nodes Core_DOM_Functions.set_child_nodes_locs get_tag_name get_tag_name_locs
  by(auto simp add: l_set_child_nodes_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_child_nodes_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma set_child_nodes_get_tag_name_is_l_set_child_nodes_get_tag_name [instances]:
  "l_set_child_nodes_get_tag_name type_wf set_child_nodes set_child_nodes_locs get_tag_name get_tag_name_locs"
  apply(auto simp add: l_set_child_nodes_get_tag_name_def l_set_child_nodes_get_tag_name_axioms_def instances)[1]
  using set_child_nodes_get_tag_name
  by fast


paragraph \<open>delete\_shadow\_root\<close>

locale l_delete_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_tag_name_delete_shadow_root:  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: CD.get_tag_name_locs_def delete_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
end

locale l_delete_shadow_root_get_tag_name = l_get_tag_name_defs +
  assumes get_tag_name_delete_shadow_root:  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"
interpretation l_delete_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf get_tag_name
  get_tag_name_locs
  by(auto simp add: l_delete_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)

lemma l_delete_shadow_root_get_tag_name_get_tag_name_locs [instances]: "l_delete_shadow_root_get_tag_name get_tag_name_locs"
  apply(auto simp add: l_delete_shadow_root_get_tag_name_def)[1]
  using get_tag_name_delete_shadow_root apply fast
  done


paragraph \<open>set\_shadow\_root\<close>

locale l_set_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_shadow_root_get_tag_name:
  "\<forall>w \<in> set_shadow_root_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"
  by(auto simp add: set_shadow_root_locs_def CD.get_tag_name_locs_def all_args_def element_put_get_preserved[where setter=shadow_root_opt_update])
end

interpretation
  i_set_shadow_root_get_tag_name?: l_set_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_shadow_root
  set_shadow_root_locs DocumentClass.type_wf get_tag_name get_tag_name_locs
  apply(auto simp add: l_set_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)[1]
  by(unfold_locales)
declare l_set_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_set_shadow_root_get_tag_name = l_set_shadow_root_defs + l_get_tag_name_defs +
  assumes set_shadow_root_get_tag_name: "\<forall>w \<in> set_shadow_root_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"

lemma set_shadow_root_get_tag_name_is_l_set_shadow_root_get_tag_name [instances]:
  "l_set_shadow_root_get_tag_name set_shadow_root_locs get_tag_name_locs"
  using set_shadow_root_is_l_set_shadow_root get_tag_name_is_l_get_tag_name
  apply(simp add: l_set_shadow_root_get_tag_name_def )
  using set_shadow_root_get_tag_name
  by fast



paragraph \<open>new\_element\<close>

locale l_new_element_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_tag_name get_tag_name_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> (_, tag_name) dom_prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_tag_name_new_element:
  "ptr' \<noteq> new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
     \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: CD.get_tag_name_locs_def new_element_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_element_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      new_element_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t split: prod.splits if_splits option.splits
      elim!: bind_returns_result_E bind_returns_heap_E intro: is_element_ptr_kind_obtains)

lemma new_element_empty_tag_name:
  "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
   \<Longrightarrow> h' \<turnstile> get_tag_name new_element_ptr \<rightarrow>\<^sub>r ''''"
  by(simp add: CD.get_tag_name_def new_element_tag_name)
end

locale l_new_element_get_tag_name = l_new_element + l_get_tag_name +
  assumes get_tag_name_new_element:
    "ptr' \<noteq> new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr
            \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"
  assumes new_element_empty_tag_name:
    "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr \<Longrightarrow> h \<turnstile> new_element \<rightarrow>\<^sub>h h'
            \<Longrightarrow> h' \<turnstile> get_tag_name new_element_ptr \<rightarrow>\<^sub>r ''''"


interpretation i_new_element_get_tag_name?:
  l_new_element_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf get_tag_name get_tag_name_locs
  by(auto simp add: l_new_element_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_new_element_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma new_element_get_tag_name_is_l_new_element_get_tag_name [instances]:
  "l_new_element_get_tag_name type_wf get_tag_name get_tag_name_locs"
  using new_element_is_l_new_element get_tag_name_is_l_get_tag_name
  apply(auto simp add: l_new_element_get_tag_name_def l_new_element_get_tag_name_axioms_def instances)[1]
  using get_tag_name_new_element new_element_empty_tag_name
  by fast+

paragraph \<open>get\_shadow\_root\<close>

locale l_set_mode_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_mode_get_tag_name:
  "\<forall>w \<in> set_mode_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"
  by(auto simp add: set_mode_locs_def CD.get_tag_name_locs_def all_args_def)
end

interpretation
  i_set_mode_get_tag_name?: l_set_mode_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  set_mode set_mode_locs  DocumentClass.type_wf get_tag_name
  get_tag_name_locs
  by unfold_locales
declare l_set_mode_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_set_mode_get_tag_name = l_set_mode + l_get_tag_name +
  assumes set_mode_get_tag_name:
    "\<forall>w \<in> set_mode_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"

lemma set_mode_get_tag_name_is_l_set_mode_get_tag_name [instances]:
  "l_set_mode_get_tag_name type_wf set_mode set_mode_locs get_tag_name
                                         get_tag_name_locs"
  using set_mode_is_l_set_mode get_tag_name_is_l_get_tag_name
  apply(simp add: l_set_mode_get_tag_name_def
      l_set_mode_get_tag_name_axioms_def)
  using set_mode_get_tag_name
  by fast

paragraph \<open>new\_document\<close>

locale l_new_document_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_tag_name get_tag_name_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, tag_name) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_tag_name_new_document:
  "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h'
       \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: CD.get_tag_name_locs_def new_document_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
end

locale l_new_document_get_tag_name = l_get_tag_name_defs +
  assumes get_tag_name_new_document:
    "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h'
       \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"

interpretation i_new_document_get_tag_name?:
  l_new_document_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf get_tag_name
  get_tag_name_locs
  by unfold_locales
declare l_new_document_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def[instances]

lemma new_document_get_tag_name_is_l_new_document_get_tag_name [instances]:
  "l_new_document_get_tag_name get_tag_name_locs"
  unfolding l_new_document_get_tag_name_def
  unfolding get_tag_name_locs_def
  using new_document_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t by blast

paragraph \<open>new\_shadow\_root\<close>

locale l_new_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_tag_name_new_shadow_root:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
     \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"
  by (auto simp add: CD.get_tag_name_locs_def new_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t new_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      split: prod.splits if_splits option.splits
      elim!: bind_returns_result_E bind_returns_heap_E intro: is_element_ptr_kind_obtains)
end

locale l_new_shadow_root_get_tag_name = l_get_tag_name +
  assumes get_tag_name_new_shadow_root:
    "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
            \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"

interpretation i_new_shadow_root_get_tag_name?:
  l_new_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf get_tag_name get_tag_name_locs
  by(unfold_locales)
declare l_new_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma new_shadow_root_get_tag_name_is_l_new_shadow_root_get_tag_name [instances]:
  "l_new_shadow_root_get_tag_name type_wf get_tag_name get_tag_name_locs"
  using get_tag_name_is_l_get_tag_name
  apply(auto simp add: l_new_shadow_root_get_tag_name_def l_new_shadow_root_get_tag_name_axioms_def instances)[1]
  using get_tag_name_new_shadow_root
  by fast

paragraph \<open>new\_character\_data\<close>

locale l_new_character_data_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_tag_name get_tag_name_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, tag_name) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_tag_name_new_character_data:
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'
       \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: CD.get_tag_name_locs_def new_character_data_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
end

locale l_new_character_data_get_tag_name = l_get_tag_name_defs +
  assumes get_tag_name_new_character_data:
    "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr \<Longrightarrow> h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'
       \<Longrightarrow> r \<in> get_tag_name_locs ptr' \<Longrightarrow> r h h'"

interpretation i_new_character_data_get_tag_name?:
  l_new_character_data_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf get_tag_name
  get_tag_name_locs
  by unfold_locales
declare l_new_character_data_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def[instances]

lemma new_character_data_get_tag_name_is_l_new_character_data_get_tag_name [instances]:
  "l_new_character_data_get_tag_name get_tag_name_locs"
  unfolding l_new_character_data_get_tag_name_def
  unfolding get_tag_name_locs_def
  using new_character_data_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t by blast

paragraph \<open>get\_tag\_type\<close>

locale l_set_tag_name_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M = l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  + l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_tag_name_get_tag_name:
  assumes "h \<turnstile> CD.a_set_tag_name element_ptr tag \<rightarrow>\<^sub>h h'"
  shows "h' \<turnstile> CD.a_get_tag_name element_ptr \<rightarrow>\<^sub>r tag"
  using assms
  by(auto simp add: CD.a_get_tag_name_def CD.a_set_tag_name_def)

lemma set_tag_name_get_tag_name_different_pointers:
  assumes "ptr \<noteq> ptr'"
  assumes "w \<in> CD.a_set_tag_name_locs ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  assumes "r \<in> CD.a_get_tag_name_locs ptr'"
  shows "r h h'"
  using assms
  by(auto simp add: all_args_def CD.a_set_tag_name_locs_def CD.a_get_tag_name_locs_def
      split: if_splits option.splits )
end

interpretation i_set_tag_name_get_tag_name?:
  l_set_tag_name_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf get_tag_name
  get_tag_name_locs set_tag_name set_tag_name_locs
  by unfold_locales
declare l_set_tag_name_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_tag_name_get_tag_name_is_l_set_tag_name_get_tag_name [instances]:
  "l_set_tag_name_get_tag_name  type_wf get_tag_name get_tag_name_locs
                                                    set_tag_name set_tag_name_locs"
  using set_tag_name_is_l_set_tag_name get_tag_name_is_l_get_tag_name
  apply(simp add: l_set_tag_name_get_tag_name_def
      l_set_tag_name_get_tag_name_axioms_def)
  using set_tag_name_get_tag_name
    set_tag_name_get_tag_name_different_pointers
  by fast+


subsubsection \<open>attach\_shadow\_root\<close>

locale l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_set_shadow_root_defs set_shadow_root set_shadow_root_locs +
  l_set_mode_defs set_mode set_mode_locs +
  l_get_tag_name_defs get_tag_name get_tag_name_locs +
  l_get_shadow_root_defs get_shadow_root get_shadow_root_locs
  for set_shadow_root :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_mode :: "(_) shadow_root_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> (_, char list) dom_prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_attach_shadow_root :: "(_) element_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> (_, (_) shadow_root_ptr) dom_prog"
  where
    "a_attach_shadow_root element_ptr shadow_root_mode = do {
      tag \<leftarrow> get_tag_name element_ptr;
      (if tag \<notin> safe_shadow_root_element_types then error HierarchyRequestError else return ());
      prev_shadow_root \<leftarrow> get_shadow_root element_ptr;
      (if prev_shadow_root \<noteq> None then error HierarchyRequestError else return ());
      new_shadow_root_ptr \<leftarrow> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M;
      set_mode new_shadow_root_ptr shadow_root_mode;
      set_shadow_root element_ptr (Some new_shadow_root_ptr);
      return new_shadow_root_ptr
    }"
end

locale l_attach_shadow_root_defs =
  fixes attach_shadow_root :: "(_) element_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> (_, (_) shadow_root_ptr) dom_prog"

global_interpretation l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs set_shadow_root set_shadow_root_locs set_mode
  set_mode_locs get_tag_name get_tag_name_locs get_shadow_root get_shadow_root_locs
  defines attach_shadow_root = a_attach_shadow_root
  .

locale l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs set_shadow_root set_shadow_root_locs set_mode set_mode_locs get_tag_name get_tag_name_locs get_shadow_root get_shadow_root_locs +
  l_attach_shadow_root_defs attach_shadow_root +
  l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf set_shadow_root set_shadow_root_locs +
  l_set_mode type_wf set_mode set_mode_locs +
  l_get_tag_name type_wf get_tag_name get_tag_name_locs +
  l_get_shadow_root type_wf get_shadow_root get_shadow_root_locs +
  l_known_ptr known_ptr
  for known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and set_shadow_root :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_mode :: "(_) shadow_root_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and attach_shadow_root :: "(_) element_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr) prog"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> (_, char list) dom_prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes known_ptr_impl: "known_ptr = a_known_ptr"
  assumes attach_shadow_root_impl: "attach_shadow_root = a_attach_shadow_root"
begin
lemmas attach_shadow_root_def = a_attach_shadow_root_def[folded attach_shadow_root_impl]

lemma attach_shadow_root_element_ptr_in_heap:
  assumes "h \<turnstile> ok (attach_shadow_root element_ptr shadow_root_mode)"
  shows "element_ptr |\<in>| element_ptr_kinds h"
proof -
  obtain h' where "h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>h h'"
    using assms by auto
  then
  obtain h2 h3 new_shadow_root_ptr where
    h2: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h2" and
    new_shadow_root_ptr: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr" and
    h3: "h2 \<turnstile> set_mode new_shadow_root_ptr shadow_root_mode \<rightarrow>\<^sub>h h3" and
    "h3 \<turnstile> set_shadow_root element_ptr (Some new_shadow_root_ptr) \<rightarrow>\<^sub>h h'"
    by(auto simp add: attach_shadow_root_def elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_tag_name_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_shadow_root_pure, rotated] split: if_splits)

  then have "element_ptr |\<in>| element_ptr_kinds h3"
    using set_shadow_root_ptr_in_heap by blast

  moreover
  have "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_shadow_root_ptr|}"
    using h2 new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_new_ptr new_shadow_root_ptr by auto

  moreover
  have "object_ptr_kinds h2 = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF set_mode_writes h3])
    using set_mode_pointers_preserved
      apply blast
    by (auto simp add: reflp_def transp_def)
  ultimately
  show ?thesis
    by (metis (no_types, lifting) cast_document_ptr_not_node_ptr(2) element_ptr_kinds_commutes
        finsertE funion_finsert_right node_ptr_kinds_commutes sup_bot.right_neutral)
qed

lemma create_shadow_root_known_ptr:
  assumes "h \<turnstile> attach_shadow_root element_ptr shadow_root_mode \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "known_ptr (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr)"
  using assms
  by(auto simp add: attach_shadow_root_def known_ptr_impl ShadowRootClass.a_known_ptr_def
      new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def Let_def elim!: bind_returns_result_E)
end

locale l_attach_shadow_root = l_attach_shadow_root_defs

interpretation
  i_attach_shadow_root?: l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr set_shadow_root set_shadow_root_locs
  set_mode set_mode_locs attach_shadow_root type_wf get_tag_name get_tag_name_locs get_shadow_root get_shadow_root_locs
  by(auto simp add: l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      attach_shadow_root_def instances)
declare l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_parent\<close>

global_interpretation l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs
  defines get_parent = "l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_parent get_child_nodes"
    and get_parent_locs = "l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_parent_locs get_child_nodes_locs"
  .

interpretation i_get_parent?: l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes
  get_child_nodes_locs known_ptrs get_parent get_parent_locs
  by(simp add: l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def get_parent_def
      get_parent_locs_def instances)
declare l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_parent_is_l_get_parent [instances]: "l_get_parent type_wf known_ptr known_ptrs get_parent
get_parent_locs get_child_nodes get_child_nodes_locs"
  apply(simp add: l_get_parent_def l_get_parent_axioms_def instances)
  using get_parent_reads get_parent_ok get_parent_ptr_in_heap get_parent_pure get_parent_parent_in_heap get_parent_child_dual
  using get_parent_reads_pointers
  by blast



paragraph \<open>set\_disconnected\_nodes\<close>

locale l_set_disconnected_nodes_get_parent\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes_get_child_nodes
  + l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  + l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_disconnected_nodes_get_parent [simp]: "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_parent_locs. r h h'))"
  by(auto simp add: get_parent_locs_def CD.set_disconnected_nodes_locs_def all_args_def)
end
interpretation i_set_disconnected_nodes_get_parent?:
  l_set_disconnected_nodes_get_parent\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_disconnected_nodes set_disconnected_nodes_locs
  get_child_nodes get_child_nodes_locs type_wf DocumentClass.type_wf known_ptr known_ptrs get_parent
  get_parent_locs
  by (simp add: l_set_disconnected_nodes_get_parent\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_disconnected_nodes_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_get_parent_is_l_set_disconnected_nodes_get_parent [instances]:
  "l_set_disconnected_nodes_get_parent set_disconnected_nodes_locs get_parent_locs"
  by(simp add: l_set_disconnected_nodes_get_parent_def)



subsubsection \<open>get\_root\_node\<close>

global_interpretation l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_parent get_parent_locs
  defines get_root_node = "l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_root_node get_parent"
    and get_root_node_locs = "l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_root_node_locs get_parent_locs"
    and get_ancestors = "l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_ancestors get_parent"
    and get_ancestors_locs = "l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_ancestors_locs get_parent_locs"
  .
declare a_get_ancestors.simps [code]

interpretation i_get_root_node?: l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr known_ptrs get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_ancestors get_ancestors_locs get_root_node
  get_root_node_locs
  by(simp add: l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def get_root_node_def
      get_root_node_locs_def get_ancestors_def get_ancestors_locs_def instances)
declare l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_ancestors_is_l_get_ancestors [instances]: "l_get_ancestors get_ancestors"
  apply(auto simp add: l_get_ancestors_def)[1]
  using get_ancestors_ptr_in_heap apply fast
  using get_ancestors_ptr apply fast
  done

lemma get_root_node_is_l_get_root_node [instances]: "l_get_root_node get_root_node get_parent"
  by (simp add: l_get_root_node_def Shadow_DOM.i_get_root_node.get_root_node_no_parent)



subsubsection \<open>get\_root\_node\_si\<close>

locale l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_parent_defs get_parent get_parent_locs +
  l_get_host_defs get_host get_host_locs
  for get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_::linorder) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
partial_function (dom_prog) a_get_ancestors_si :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  where
    "a_get_ancestors_si ptr = do {
      check_in_heap ptr;
      ancestors \<leftarrow> (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr of
        Some node_ptr \<Rightarrow> do {
          parent_ptr_opt \<leftarrow> get_parent node_ptr;
          (case parent_ptr_opt of
            Some parent_ptr \<Rightarrow> a_get_ancestors_si parent_ptr
          | None \<Rightarrow> return [])
        }
      | None \<Rightarrow> (case cast ptr of
          Some shadow_root_ptr \<Rightarrow> do {
            host \<leftarrow> get_host shadow_root_ptr;
            a_get_ancestors_si (cast host)
          } |
          None \<Rightarrow> return []));
      return (ptr # ancestors)
    }"

definition "a_get_ancestors_si_locs = get_parent_locs \<union> get_host_locs"

definition a_get_root_node_si :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr) dom_prog"
  where
    "a_get_root_node_si ptr = do {
      ancestors \<leftarrow> a_get_ancestors_si ptr;
      return (last ancestors)
    }"
definition "a_get_root_node_si_locs = a_get_ancestors_si_locs"
end

locale l_get_ancestors_si_defs =
  fixes get_ancestors_si :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  fixes get_ancestors_si_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_root_node_si_defs =
  fixes get_root_node_si :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr) dom_prog"
  fixes get_root_node_si_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_parent +
  l_get_host +
  l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_ancestors_si_defs +
  l_get_root_node_si_defs +
  assumes get_ancestors_si_impl: "get_ancestors_si = a_get_ancestors_si"
  assumes get_ancestors_si_locs_impl: "get_ancestors_si_locs = a_get_ancestors_si_locs"
  assumes get_root_node_si_impl: "get_root_node_si = a_get_root_node_si"
  assumes get_root_node_si_locs_impl: "get_root_node_si_locs = a_get_root_node_si_locs"
begin
lemmas get_ancestors_si_def = a_get_ancestors_si.simps[folded get_ancestors_si_impl]
lemmas get_ancestors_si_locs_def = a_get_ancestors_si_locs_def[folded get_ancestors_si_locs_impl]
lemmas get_root_node_si_def = a_get_root_node_si_def[folded get_root_node_si_impl get_ancestors_si_impl]
lemmas get_root_node_si_locs_def =
  a_get_root_node_si_locs_def[folded get_root_node_si_locs_impl get_ancestors_si_locs_impl]

lemma get_ancestors_si_pure [simp]:
  "pure (get_ancestors_si ptr) h"
proof -
  have "\<forall>ptr h h' x. h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r x \<longrightarrow> h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>h h' \<longrightarrow> h = h'"
  proof (induct rule: a_get_ancestors_si.fixp_induct[folded get_ancestors_si_impl])
    case 1
    then show ?case
      by(rule admissible_dom_prog)
  next
    case 2
    then show ?case
      by simp
  next
    case (3 f)
    then show ?case
      using get_parent_pure get_host_pure
      apply(auto simp add: pure_returns_heap_eq pure_def split: option.splits
          elim!: bind_returns_heap_E bind_returns_result_E
          dest!: pure_returns_heap_eq[rotated, OF check_in_heap_pure])[1]
        apply (meson option.simps(3) returns_result_eq)
       apply(metis get_parent_pure pure_returns_heap_eq)
      apply(metis get_host_pure pure_returns_heap_eq)
      done
  qed
  then show ?thesis
    by (meson pure_eq_iff)
qed


lemma get_root_node_si_pure [simp]: "pure (get_root_node_si ptr) h"
  by(auto simp add: get_root_node_si_def bind_pure_I)


lemma get_ancestors_si_ptr_in_heap:
  assumes "h \<turnstile> ok (get_ancestors_si ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms
  by(auto simp add: get_ancestors_si_def check_in_heap_ptr_in_heap elim!: bind_is_OK_E
      dest: is_OK_returns_result_I)

lemma get_ancestors_si_ptr:
  assumes "h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r ancestors"
  shows "ptr \<in> set ancestors"
  using assms
  by(simp add: get_ancestors_si_def) (auto  elim!: bind_returns_result_E2 split: option.splits
      intro!: bind_pure_I)


lemma get_ancestors_si_never_empty:
  assumes "h \<turnstile> get_ancestors_si child \<rightarrow>\<^sub>r ancestors"
  shows "ancestors \<noteq> []"
  using assms
  apply(simp add: get_ancestors_si_def)
  by(auto elim!: bind_returns_result_E2 split: option.splits)
    (*
lemma get_ancestors_si_not_node:
  assumes "h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r ancestors"
  assumes "\<not>is_node_ptr_kind ptr"
  shows "ancestors = [ptr]"
  using assms
  by (simp add: get_ancestors_si_def) (auto elim!: bind_returns_result_E2 split: option.splits)
 *)

lemma get_root_node_si_no_parent:
  "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None \<Longrightarrow> h \<turnstile> get_root_node_si (cast node_ptr) \<rightarrow>\<^sub>r cast node_ptr"
  apply(auto simp add: check_in_heap_def get_root_node_si_def get_ancestors_si_def
      intro!: bind_pure_returns_result_I )[1]
  using get_parent_ptr_in_heap by blast


lemma get_root_node_si_root_not_shadow_root:
  assumes "h \<turnstile> get_root_node_si ptr \<rightarrow>\<^sub>r root"
  shows "\<not> is_shadow_root_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root"
  using assms
proof(auto simp add: get_root_node_si_def elim!: bind_returns_result_E2)
  fix y
  assume "h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r y"
    and "is_shadow_root_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (last y)"
    and "root = last y"
  then
  show False
  proof(induct y arbitrary: ptr)
    case Nil
    then show ?case
      using assms(1) get_ancestors_si_never_empty by blast
  next
    case (Cons a x)
    then show ?case
      apply(auto simp add: get_ancestors_si_def[of ptr] elim!: bind_returns_result_E2
          split: option.splits if_splits)[1]
      using get_ancestors_si_never_empty apply blast
      using Cons.prems(2) apply auto[1]
      using \<open>is_shadow_root_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (last y)\<close> \<open>root = last y\<close> by auto
  qed
qed
end

global_interpretation l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_parent get_parent_locs get_host get_host_locs
  defines get_root_node_si = a_get_root_node_si
    and get_root_node_si_locs = a_get_root_node_si_locs
    and get_ancestors_si = a_get_ancestors_si
    and get_ancestors_si_locs = a_get_ancestors_si_locs
  .
declare a_get_ancestors_si.simps [code]

interpretation
  i_get_root_node_si?: l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr known_ptrs get_parent
  get_parent_locs get_child_nodes get_child_nodes_locs get_host get_host_locs get_ancestors_si
  get_ancestors_si_locs get_root_node_si get_root_node_si_locs
  apply(auto simp add: l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)[1]
  by(auto simp add: get_root_node_si_def get_root_node_si_locs_def get_ancestors_si_def get_ancestors_si_locs_def)
declare l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_ancestors_si_is_l_get_ancestors [instances]: "l_get_ancestors get_ancestors_si"
  unfolding l_get_ancestors_def
  using get_ancestors_si_pure get_ancestors_si_ptr get_ancestors_si_ptr_in_heap
  by blast

lemma get_root_node_si_is_l_get_root_node [instances]: "l_get_root_node get_root_node_si get_parent"
  apply(simp add: l_get_root_node_def)
  using get_root_node_si_no_parent
  by fast


paragraph \<open>set\_disconnected\_nodes\<close>


locale l_set_disconnected_nodes_get_ancestors_si\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes_get_parent
  + l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  + l_set_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  + l_set_disconnected_nodes_get_host
begin
lemma set_disconnected_nodes_get_ancestors_si:
  "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_ancestors_si_locs. r h h'))"
  by(auto simp add: get_parent_locs_def set_disconnected_nodes_locs_def
      set_disconnected_nodes_get_host get_ancestors_si_locs_def all_args_def)
end

locale l_set_disconnected_nodes_get_ancestors_si = l_set_disconnected_nodes_defs + l_get_ancestors_si_defs +
  assumes set_disconnected_nodes_get_ancestors_si:
    "\<forall>w \<in> set_disconnected_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_ancestors_si_locs. r h h'))"

interpretation
  i_set_disconnected_nodes_get_ancestors_si?: l_set_disconnected_nodes_get_ancestors_si\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  set_disconnected_nodes set_disconnected_nodes_locs get_parent get_parent_locs type_wf known_ptr
  known_ptrs get_child_nodes get_child_nodes_locs get_host get_host_locs get_ancestors_si
  get_ancestors_si_locs get_root_node_si get_root_node_si_locs DocumentClass.type_wf

  by (auto simp add: l_set_disconnected_nodes_get_ancestors_si\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_set_disconnected_nodes_get_ancestors_si\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


lemma set_disconnected_nodes_get_ancestors_si_is_l_set_disconnected_nodes_get_ancestors_si [instances]:
  "l_set_disconnected_nodes_get_ancestors_si set_disconnected_nodes_locs get_ancestors_si_locs"
  using instances
  apply(simp add: l_set_disconnected_nodes_get_ancestors_si_def)
  using set_disconnected_nodes_get_ancestors_si
  by fast



subsubsection \<open>get\_attribute\<close>

lemma get_attribute_is_l_get_attribute [instances]: "l_get_attribute type_wf get_attribute get_attribute_locs"
  apply(auto simp add: l_get_attribute_def)[1]
  using i_get_attribute.get_attribute_reads apply fast
  using type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t i_get_attribute.get_attribute_ok apply blast
  using i_get_attribute.get_attribute_ptr_in_heap apply fast
  done



subsubsection \<open>to\_tree\_order\<close>

global_interpretation l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs defines
  to_tree_order = "l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_to_tree_order get_child_nodes" .
declare a_to_tree_order.simps [code]

interpretation i_to_tree_order?: l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M ShadowRootClass.known_ptr
  ShadowRootClass.type_wf Shadow_DOM.get_child_nodes Shadow_DOM.get_child_nodes_locs to_tree_order
  by(auto simp add: l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def to_tree_order_def instances)
declare l_to_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsubsection \<open>to\_tree\_order\_si\<close>


locale l_to_tree_order_si\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs +
  l_get_shadow_root_defs get_shadow_root get_shadow_root_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
partial_function (dom_prog) a_to_tree_order_si :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  where
    "a_to_tree_order_si ptr = (do {
      children \<leftarrow> get_child_nodes ptr;
      shadow_root_part \<leftarrow> (case cast ptr of
        Some element_ptr \<Rightarrow> do {
          shadow_root_opt \<leftarrow> get_shadow_root element_ptr;
          (case shadow_root_opt of
            Some shadow_root_ptr \<Rightarrow> return [cast shadow_root_ptr]
            | None \<Rightarrow> return [])
        } |
        None \<Rightarrow> return []);
      treeorders \<leftarrow> map_M a_to_tree_order_si ((map (cast) children) @ shadow_root_part);
      return (ptr # concat treeorders)
    })"
end

locale l_to_tree_order_si_defs =
  fixes to_tree_order_si :: "(_) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"

global_interpretation l_to_tree_order_si\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs
  get_shadow_root get_shadow_root_locs
  defines to_tree_order_si = "a_to_tree_order_si" .
declare a_to_tree_order_si.simps [code]


locale l_to_tree_order_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_to_tree_order_si_defs +
  l_to_tree_order_si\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_child_nodes +
  l_get_shadow_root +
  assumes to_tree_order_si_impl: "to_tree_order_si = a_to_tree_order_si"
begin
lemmas to_tree_order_si_def = a_to_tree_order_si.simps[folded to_tree_order_si_impl]

lemma to_tree_order_si_pure [simp]: "pure (to_tree_order_si ptr) h"
proof -
  have "\<forall>ptr h h' x. h \<turnstile> to_tree_order_si ptr \<rightarrow>\<^sub>r x \<longrightarrow> h \<turnstile> to_tree_order_si ptr \<rightarrow>\<^sub>h h' \<longrightarrow> h = h'"
  proof (induct rule: a_to_tree_order_si.fixp_induct[folded to_tree_order_si_impl])
    case 1
    then show ?case
      by (rule admissible_dom_prog)
  next
    case 2
    then show ?case
      by simp
  next
    case (3 f)
    then have "\<And>x h. pure (f x) h"
      by (metis is_OK_returns_heap_E is_OK_returns_result_E pure_def)
    then have "\<And>xs h. pure (map_M f xs) h"
      by(rule map_M_pure_I)
    then show ?case
      by(auto elim!: bind_returns_heap_E2 split: option.splits)
  qed
  then show ?thesis
    unfolding pure_def
    by (metis is_OK_returns_heap_E is_OK_returns_result_E)
qed
end

interpretation i_to_tree_order_si?: l_to_tree_order_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M to_tree_order_si get_child_nodes
  get_child_nodes_locs get_shadow_root get_shadow_root_locs type_wf known_ptr
  by(auto simp add: l_to_tree_order_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_to_tree_order_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      to_tree_order_si_def instances)
declare l_to_tree_order_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>first\_in\_tree\_order\<close>

global_interpretation l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs to_tree_order defines
  first_in_tree_order = "l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_first_in_tree_order to_tree_order" .

interpretation i_first_in_tree_order?: l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M to_tree_order first_in_tree_order
  by(auto simp add: l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def first_in_tree_order_def)
declare l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma to_tree_order_is_l_to_tree_order [instances]: "l_to_tree_order to_tree_order"
  by(auto simp add: l_to_tree_order_def)



subsubsection \<open>first\_in\_tree\_order\<close>

global_interpretation l_dummy defines
  first_in_tree_order_si = "l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_first_in_tree_order to_tree_order_si"
  .


subsubsection \<open>get\_element\_by\<close>

global_interpretation l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs to_tree_order first_in_tree_order get_attribute get_attribute_locs defines
  get_element_by_id = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_element_by_id first_in_tree_order get_attribute" and
  get_elements_by_class_name = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_elements_by_class_name to_tree_order get_attribute" and
  get_elements_by_tag_name = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_elements_by_tag_name to_tree_order" .

interpretation
  i_get_element_by?: l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M to_tree_order first_in_tree_order get_attribute
  get_attribute_locs get_element_by_id get_elements_by_class_name
  get_elements_by_tag_name type_wf
  by(auto simp add: l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def get_element_by_id_def
      get_elements_by_class_name_def get_elements_by_tag_name_def instances)
declare l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


lemma get_element_by_is_l_get_element_by [instances]: "l_get_element_by get_element_by_id get_elements_by_tag_name to_tree_order"
  apply(auto simp add: l_get_element_by_def)[1]
  using get_element_by_id_result_in_tree_order apply fast
  done


subsubsection \<open>get\_element\_by\_si\<close>

global_interpretation l_dummy defines
  get_element_by_id_si = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_element_by_id first_in_tree_order_si get_attribute" and
  get_elements_by_class_name_si = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_elements_by_class_name to_tree_order_si get_attribute" and
  get_elements_by_tag_name_si = "l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_elements_by_tag_name to_tree_order_si"
  .



subsubsection \<open>find\_slot\<close>

locale l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_parent_defs get_parent get_parent_locs +
  l_get_shadow_root_defs get_shadow_root get_shadow_root_locs +
  l_get_mode_defs get_mode get_mode_locs +
  l_get_attribute_defs get_attribute get_attribute_locs +
  l_get_tag_name_defs get_tag_name get_tag_name_locs +
  l_first_in_tree_order_defs first_in_tree_order
  for get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_::linorder) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_mode :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, shadow_root_mode) prog"
    and get_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_attribute :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, char list option) prog"
    and get_attribute_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and first_in_tree_order ::
    "(_) object_ptr \<Rightarrow> ((_) object_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog) \<Rightarrow>
((_) heap, exception, (_) element_ptr option) prog"
begin
definition a_find_slot :: "bool \<Rightarrow> (_) node_ptr \<Rightarrow> (_, (_) element_ptr option) dom_prog"
  where
    "a_find_slot open_flag slotable = do {
      parent_opt \<leftarrow> get_parent slotable;
      (case parent_opt of
        Some parent \<Rightarrow>
          if is_element_ptr_kind parent
          then do {
            shadow_root_ptr_opt \<leftarrow> get_shadow_root (the (cast parent));
            (case shadow_root_ptr_opt of
              Some shadow_root_ptr \<Rightarrow> do {
                shadow_root_mode \<leftarrow> get_mode shadow_root_ptr;
                if open_flag \<and> shadow_root_mode \<noteq> Open
                then return None
                else first_in_tree_order (cast shadow_root_ptr) (\<lambda>ptr. if is_element_ptr_kind ptr
                  then do {
                    tag \<leftarrow> get_tag_name (the (cast ptr));
                    name_attr \<leftarrow> get_attribute (the (cast ptr)) ''name'';
                    slotable_name_attr \<leftarrow> (if is_element_ptr_kind slotable
                      then get_attribute (the (cast slotable)) ''slot'' else return None);
                    (if (tag = ''slot'' \<and> (name_attr = slotable_name_attr \<or>
                      (name_attr = None \<and> slotable_name_attr = Some '''') \<or>
                      (name_attr = Some '''' \<and> slotable_name_attr = None)))
                    then return (Some (the (cast ptr)))
                    else return None)}
                  else return None)}
              | None \<Rightarrow> return None)}
          else return None
    | _ \<Rightarrow> return None)}"

definition a_assigned_slot :: "(_) node_ptr \<Rightarrow> (_, (_) element_ptr option) dom_prog"
  where
    "a_assigned_slot = a_find_slot True"
end

global_interpretation l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_parent get_parent_locs get_shadow_root
  get_shadow_root_locs get_mode get_mode_locs get_attribute get_attribute_locs get_tag_name
  get_tag_name_locs first_in_tree_order
  defines find_slot = a_find_slot
    and assigned_slot = a_assigned_slot
  .

locale l_find_slot_defs =
  fixes find_slot :: "bool \<Rightarrow> (_) node_ptr \<Rightarrow> (_, (_) element_ptr option) dom_prog"
    and assigned_slot :: "(_) node_ptr \<Rightarrow> (_, (_) element_ptr option) dom_prog"

locale l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_find_slot_defs +
  l_get_parent +
  l_get_shadow_root +
  l_get_mode +
  l_get_attribute +
  l_get_tag_name +
  l_to_tree_order +
  l_first_in_tree_order\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  assumes find_slot_impl: "find_slot = a_find_slot"
  assumes assigned_slot_impl: "assigned_slot = a_assigned_slot"
begin
lemmas find_slot_def = find_slot_impl[unfolded a_find_slot_def]
lemmas assigned_slot_def = assigned_slot_impl[unfolded a_assigned_slot_def]

lemma find_slot_ptr_in_heap:
  assumes "h \<turnstile> find_slot open_flag slotable \<rightarrow>\<^sub>r slot_opt"
  shows "slotable |\<in>| node_ptr_kinds h"
  using assms
  apply(auto simp add: find_slot_def elim!: bind_returns_result_E2)[1]
  using get_parent_ptr_in_heap by blast

lemma find_slot_slot_in_heap:
  assumes "h \<turnstile> find_slot open_flag slotable \<rightarrow>\<^sub>r Some slot"
  shows "slot |\<in>| element_ptr_kinds h"
  using assms
  apply(auto simp add: find_slot_def first_in_tree_order_def elim!: bind_returns_result_E2
      map_filter_M_pure_E[where y=slot] split: option.splits if_splits list.splits intro!: map_filter_M_pure
      bind_pure_I)[1]
  using get_tag_name_ptr_in_heap by blast+

lemma find_slot_pure [simp]: "pure (find_slot open_flag slotable) h"
  by(auto simp add: find_slot_def first_in_tree_order_def  intro!: bind_pure_I map_filter_M_pure
      split: option.splits list.splits)
end

interpretation i_find_slot?: l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_parent get_parent_locs get_shadow_root
  get_shadow_root_locs get_mode get_mode_locs get_attribute get_attribute_locs get_tag_name
  get_tag_name_locs first_in_tree_order find_slot assigned_slot type_wf known_ptr known_ptrs
  get_child_nodes get_child_nodes_locs to_tree_order
  by (auto simp add: find_slot_def assigned_slot_def l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def
      l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_find_slot\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_find_slot = l_find_slot_defs +
  assumes find_slot_ptr_in_heap: "h \<turnstile> find_slot open_flag slotable \<rightarrow>\<^sub>r slot_opt \<Longrightarrow> slotable |\<in>| node_ptr_kinds h"
  assumes find_slot_slot_in_heap: "h \<turnstile> find_slot open_flag slotable \<rightarrow>\<^sub>r Some slot \<Longrightarrow> slot |\<in>| element_ptr_kinds h"
  assumes find_slot_pure [simp]: "pure (find_slot open_flag slotable) h"

lemma find_slot_is_l_find_slot [instances]: "l_find_slot find_slot"
  apply(auto simp add: l_find_slot_def)[1]
  using find_slot_ptr_in_heap apply fast
  using find_slot_slot_in_heap apply fast
  done



subsubsection \<open>get\_disconnected\_nodes\<close>

locale l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  CD: l_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs +
  l_type_wf type_wf
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
begin

lemma get_disconnected_nodes_ok:
  "type_wf h \<Longrightarrow> document_ptr |\<in>| document_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_disconnected_nodes document_ptr)"
  apply(unfold type_wf_impl get_disconnected_nodes_impl[unfolded a_get_disconnected_nodes_def])
  using CD.get_disconnected_nodes_ok CD.type_wf_impl ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t
  by blast
end

interpretation i_get_disconnected_nodes?: l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  DocumentClass.type_wf get_disconnected_nodes get_disconnected_nodes_locs
  by(auto simp add: l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_disconnected_nodes_is_l_get_disconnected_nodes [instances]:
  "l_get_disconnected_nodes type_wf get_disconnected_nodes get_disconnected_nodes_locs"
  apply(auto simp add: l_get_disconnected_nodes_def)[1]
  using i_get_disconnected_nodes.get_disconnected_nodes_reads apply fast
  using get_disconnected_nodes_ok apply fast
  using i_get_disconnected_nodes.get_disconnected_nodes_ptr_in_heap apply fast
  done


paragraph \<open>set\_child\_nodes\<close>

locale l_set_child_nodes_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_child_nodes_get_disconnected_nodes:
  "\<forall>w \<in> set_child_nodes_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_child_nodes_locs_def CD.set_child_nodes_locs_def
      CD.get_disconnected_nodes_locs_def all_args_def elim: get_M_document_put_M_shadow_root
      split: option.splits)
end

interpretation
  i_set_child_nodes_get_disconnected_nodes?: l_set_child_nodes_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  known_ptr DocumentClass.type_wf DocumentClass.known_ptr set_child_nodes set_child_nodes_locs
  Core_DOM_Functions.set_child_nodes Core_DOM_Functions.set_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs
  apply(auto simp add: l_set_child_nodes_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)[1]
  by(unfold_locales)
declare l_set_child_nodes_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_child_nodes_get_disconnected_nodes_is_l_set_child_nodes_get_disconnected_nodes [instances]:
  "l_set_child_nodes_get_disconnected_nodes type_wf set_child_nodes set_child_nodes_locs
get_disconnected_nodes get_disconnected_nodes_locs"
  using set_child_nodes_is_l_set_child_nodes get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_child_nodes_get_disconnected_nodes_def l_set_child_nodes_get_disconnected_nodes_axioms_def )
  using set_child_nodes_get_disconnected_nodes
  by fast


paragraph \<open>set\_disconnected\_nodes\<close>

lemma set_disconnected_nodes_get_disconnected_nodes_l_set_disconnected_nodes_get_disconnected_nodes [instances]:
  "l_set_disconnected_nodes_get_disconnected_nodes ShadowRootClass.type_wf get_disconnected_nodes
get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs"
  apply(auto simp add: l_set_disconnected_nodes_get_disconnected_nodes_def
      l_set_disconnected_nodes_get_disconnected_nodes_axioms_def instances)[1]
  using i_set_disconnected_nodes_get_disconnected_nodes.set_disconnected_nodes_get_disconnected_nodes
   apply fast
  using i_set_disconnected_nodes_get_disconnected_nodes.set_disconnected_nodes_get_disconnected_nodes_different_pointers
  apply fast
  done


paragraph \<open>delete\_shadow\_root\<close>

locale l_delete_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_disconnected_nodes_delete_shadow_root:
  "cast shadow_root_ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: CD.get_disconnected_nodes_locs_def delete_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)
end

locale l_delete_shadow_root_get_disconnected_nodes = l_get_disconnected_nodes_defs +
  assumes get_disconnected_nodes_delete_shadow_root:
    "cast shadow_root_ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"
interpretation l_delete_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf
  get_disconnected_nodes get_disconnected_nodes_locs
  by(auto simp add: l_delete_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)

lemma l_delete_shadow_root_get_disconnected_nodes_get_disconnected_nodes_locs [instances]: "l_delete_shadow_root_get_disconnected_nodes get_disconnected_nodes_locs"
  apply(auto simp add: l_delete_shadow_root_get_disconnected_nodes_def)[1]
  using get_disconnected_nodes_delete_shadow_root apply fast
  done


paragraph \<open>set\_shadow\_root\<close>

locale l_set_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_shadow_root_get_disconnected_nodes:
  "\<forall>w \<in> set_shadow_root_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_shadow_root_locs_def CD.get_disconnected_nodes_locs_def all_args_def)
end

interpretation
  i_set_shadow_root_get_disconnected_nodes?: l_set_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  set_shadow_root set_shadow_root_locs DocumentClass.type_wf get_disconnected_nodes get_disconnected_nodes_locs
  apply(auto simp add: l_set_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)[1]
  by(unfold_locales)
declare l_set_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_set_shadow_root_get_disconnected_nodes = l_set_shadow_root_defs + l_get_disconnected_nodes_defs +
  assumes set_shadow_root_get_disconnected_nodes:
    "\<forall>w \<in> set_shadow_root_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"

lemma set_shadow_root_get_disconnected_nodes_is_l_set_shadow_root_get_disconnected_nodes [instances]:
  "l_set_shadow_root_get_disconnected_nodes set_shadow_root_locs get_disconnected_nodes_locs"
  using set_shadow_root_is_l_set_shadow_root get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_shadow_root_get_disconnected_nodes_def )
  using set_shadow_root_get_disconnected_nodes
  by fast

paragraph \<open>set\_mode\<close>

locale l_set_mode_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_mode\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_mode_get_disconnected_nodes:
  "\<forall>w \<in> set_mode_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"
  by(auto simp add: set_mode_locs_def
      CD.get_disconnected_nodes_locs_impl[unfolded CD.a_get_disconnected_nodes_locs_def]
      all_args_def)
end

interpretation
  i_set_mode_get_disconnected_nodes?: l_set_mode_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  set_mode set_mode_locs DocumentClass.type_wf  get_disconnected_nodes
  get_disconnected_nodes_locs
  by unfold_locales
declare l_set_mode_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_set_mode_get_disconnected_nodes = l_set_mode + l_get_disconnected_nodes +
  assumes set_mode_get_disconnected_nodes:
    "\<forall>w \<in> set_mode_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"

lemma set_mode_get_disconnected_nodes_is_l_set_mode_get_disconnected_nodes [instances]:
  "l_set_mode_get_disconnected_nodes type_wf set_mode set_mode_locs get_disconnected_nodes
                                         get_disconnected_nodes_locs"
  using set_mode_is_l_set_mode get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_mode_get_disconnected_nodes_def
      l_set_mode_get_disconnected_nodes_axioms_def)
  using set_mode_get_disconnected_nodes
  by fast

paragraph \<open>new\_shadow\_root\<close>

locale l_new_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma get_disconnected_nodes_new_shadow_root_different_pointers:
  "cast new_shadow_root_ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"
  by(auto simp add: CD.get_disconnected_nodes_locs_def new_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t)

lemma new_shadow_root_no_disconnected_nodes:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
     \<Longrightarrow> h' \<turnstile> get_disconnected_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []"
  by(simp add: CD.get_disconnected_nodes_def new_shadow_root_disconnected_nodes)

end

interpretation i_new_shadow_root_get_disconnected_nodes?:
  l_new_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf get_disconnected_nodes
  get_disconnected_nodes_locs
  by unfold_locales
declare l_new_shadow_root_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

locale l_new_shadow_root_get_disconnected_nodes = l_get_disconnected_nodes_defs +
  assumes get_disconnected_nodes_new_shadow_root_different_pointers:
    "cast new_shadow_root_ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
    \<Longrightarrow> r \<in> get_disconnected_nodes_locs ptr' \<Longrightarrow> r h h'"
  assumes new_shadow_root_no_disconnected_nodes:
    "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
    \<Longrightarrow> h' \<turnstile> get_disconnected_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []"

lemma new_shadow_root_get_disconnected_nodes_is_l_new_shadow_root_get_disconnected_nodes [instances]:
  "l_new_shadow_root_get_disconnected_nodes get_disconnected_nodes get_disconnected_nodes_locs"
  apply (auto simp add: l_new_shadow_root_get_disconnected_nodes_def)[1]
  using get_disconnected_nodes_new_shadow_root_different_pointers apply fast
  using new_shadow_root_no_disconnected_nodes apply blast
  done


subsubsection \<open>remove\_shadow\_root\<close>

locale l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs +
  l_get_shadow_root_defs get_shadow_root get_shadow_root_locs +
  l_set_shadow_root_defs set_shadow_root set_shadow_root_locs +
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs
  for get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and set_shadow_root :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin

definition a_remove_shadow_root :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog" where
  "a_remove_shadow_root element_ptr = do {
    shadow_root_ptr_opt \<leftarrow> get_shadow_root element_ptr;
    (case shadow_root_ptr_opt of
      Some shadow_root_ptr \<Rightarrow> do {
        children \<leftarrow> get_child_nodes (cast shadow_root_ptr);
        disconnected_nodes \<leftarrow> get_disconnected_nodes (cast shadow_root_ptr);
        (if children = [] \<and> disconnected_nodes = []
        then do {
          set_shadow_root element_ptr None;
          delete_M shadow_root_ptr
        } else do {
          error HierarchyRequestError
        })
      } |
      None \<Rightarrow> error HierarchyRequestError)
    }"

definition a_remove_shadow_root_locs :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr \<Rightarrow> ((_, unit) dom_prog) set"
  where
    "a_remove_shadow_root_locs element_ptr shadow_root_ptr \<equiv> set_shadow_root_locs element_ptr \<union> {delete_M shadow_root_ptr}"
end

global_interpretation l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs
  get_shadow_root get_shadow_root_locs set_shadow_root set_shadow_root_locs get_disconnected_nodes
  get_disconnected_nodes_locs
  defines remove_shadow_root = "a_remove_shadow_root"
    and remove_shadow_root_locs = a_remove_shadow_root_locs
  .

locale l_remove_shadow_root_defs =
  fixes remove_shadow_root :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog"
  fixes remove_shadow_root_locs :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr \<Rightarrow> ((_, unit) dom_prog) set"


locale l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_remove_shadow_root_defs +
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_child_nodes +
  l_get_disconnected_nodes +
  assumes remove_shadow_root_impl: "remove_shadow_root = a_remove_shadow_root"
  assumes remove_shadow_root_locs_impl: "remove_shadow_root_locs = a_remove_shadow_root_locs"
begin
lemmas remove_shadow_root_def =
  remove_shadow_root_impl[unfolded remove_shadow_root_def a_remove_shadow_root_def]
lemmas remove_shadow_root_locs_def =
  remove_shadow_root_locs_impl[unfolded remove_shadow_root_locs_def a_remove_shadow_root_locs_def]

lemma remove_shadow_root_writes:
  "writes (remove_shadow_root_locs element_ptr (the |h \<turnstile> get_shadow_root element_ptr|\<^sub>r))
(remove_shadow_root element_ptr) h h'"
  apply(auto simp add: remove_shadow_root_locs_def remove_shadow_root_def all_args_def
      writes_union_right_I writes_union_left_I set_shadow_root_writes
      intro!: writes_bind writes_bind_pure[OF get_shadow_root_pure] writes_bind_pure[OF get_child_nodes_pure]
      intro: writes_subset[OF set_shadow_root_writes] writes_subset[OF writes_singleton2] split: option.splits)[1]
  using  writes_union_left_I[OF set_shadow_root_writes]
   apply (metis inf_sup_aci(5) insert_is_Un)
  using writes_union_right_I[OF writes_singleton[of delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M]]
  by (smt insert_is_Un writes_singleton2 writes_union_left_I)
end

interpretation i_remove_shadow_root?: l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs
  get_shadow_root get_shadow_root_locs set_shadow_root set_shadow_root_locs get_disconnected_nodes
  get_disconnected_nodes_locs remove_shadow_root remove_shadow_root_locs type_wf known_ptr
  by(auto simp add: l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      remove_shadow_root_def remove_shadow_root_locs_def instances)
declare l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


paragraph \<open>get\_child\_nodes\<close>

locale l_remove_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma remove_shadow_root_get_child_nodes_different_pointers:
  assumes "ptr \<noteq> cast shadow_root_ptr"
  assumes "w \<in> remove_shadow_root_locs element_ptr shadow_root_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  assumes "r \<in> get_child_nodes_locs ptr"
  shows "r h h'"
  using assms
  by(auto simp add: all_args_def get_child_nodes_locs_def CD.get_child_nodes_locs_def
      remove_shadow_root_locs_def set_shadow_root_locs_def
      delete_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t delete_shadow_root_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t
      intro: is_shadow_root_ptr_kind_obtains
      simp add: delete_shadow_root_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t delete_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      delete_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t[rotated] element_put_get_preserved[where setter=shadow_root_opt_update]
      elim: is_document_ptr_kind_obtains is_shadow_root_ptr_kind_obtains
      split: if_splits option.splits)[1]
end

locale l_remove_shadow_root_get_child_nodes = l_get_child_nodes_defs + l_remove_shadow_root_defs +
  assumes remove_shadow_root_get_child_nodes_different_pointers:
    "ptr \<noteq> cast shadow_root_ptr \<Longrightarrow> w \<in> remove_shadow_root_locs element_ptr shadow_root_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow>
r \<in> get_child_nodes_locs ptr \<Longrightarrow> r h h'"

interpretation
  i_remove_shadow_root_get_child_nodes?: l_remove_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  known_ptr DocumentClass.type_wf DocumentClass.known_ptr get_child_nodes get_child_nodes_locs
  Core_DOM_Functions.get_child_nodes Core_DOM_Functions.get_child_nodes_locs get_shadow_root
  get_shadow_root_locs set_shadow_root set_shadow_root_locs get_disconnected_nodes get_disconnected_nodes_locs
  remove_shadow_root remove_shadow_root_locs
  by(auto simp add: l_remove_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_remove_shadow_root_get_child_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma remove_shadow_root_get_child_nodes_is_l_remove_shadow_root_get_child_nodes [instances]:
  "l_remove_shadow_root_get_child_nodes get_child_nodes_locs remove_shadow_root_locs"
  apply(auto simp add: l_remove_shadow_root_get_child_nodes_def instances )[1]
  using remove_shadow_root_get_child_nodes_different_pointers apply fast
  done

paragraph \<open>get\_tag\_name\<close>

locale l_remove_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma remove_shadow_root_get_tag_name:
  assumes "w \<in> remove_shadow_root_locs element_ptr shadow_root_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  assumes "r \<in> get_tag_name_locs ptr"
  shows "r h h'"
  using assms
  by(auto simp add: all_args_def remove_shadow_root_locs_def set_shadow_root_locs_def
      CD.get_tag_name_locs_def delete_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      element_put_get_preserved[where setter=shadow_root_opt_update] split: if_splits option.splits)
end

locale l_remove_shadow_root_get_tag_name = l_get_tag_name_defs + l_remove_shadow_root_defs +
  assumes remove_shadow_root_get_tag_name:
    "w \<in> remove_shadow_root_locs element_ptr shadow_root_ptr \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> r \<in> get_tag_name_locs ptr \<Longrightarrow>
r h h'"

interpretation
  i_remove_shadow_root_get_tag_name?: l_remove_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf
  DocumentClass.type_wf get_tag_name get_tag_name_locs get_child_nodes get_child_nodes_locs
  get_shadow_root get_shadow_root_locs set_shadow_root set_shadow_root_locs get_disconnected_nodes
  get_disconnected_nodes_locs remove_shadow_root remove_shadow_root_locs known_ptr
  by(auto simp add: l_remove_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_remove_shadow_root_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma remove_shadow_root_get_tag_name_is_l_remove_shadow_root_get_tag_name [instances]:
  "l_remove_shadow_root_get_tag_name get_tag_name_locs remove_shadow_root_locs"
  apply(auto simp add: l_remove_shadow_root_get_tag_name_def instances )[1]
  using remove_shadow_root_get_tag_name apply fast
  done


subsubsection \<open>get\_owner\_document\<close>

locale l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_host_defs get_host get_host_locs +
  CD: l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_root_node get_root_node_locs get_disconnected_nodes get_disconnected_nodes_locs
  for get_root_node :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
    and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) shadow_root_ptr \<Rightarrow> unit \<Rightarrow> (_, (_) document_ptr) dom_prog"
  where
    "a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr = CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (cast shadow_root_ptr)"

definition a_get_owner_document_tups :: "(((_) object_ptr \<Rightarrow> bool) \<times> ((_) object_ptr \<Rightarrow> unit
  \<Rightarrow> (_, (_) document_ptr) dom_prog)) list"
  where
    "a_get_owner_document_tups = [(is_shadow_root_ptr, a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast)]"

definition a_get_owner_document :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) document_ptr) dom_prog"
  where
    "a_get_owner_document ptr = invoke (CD.a_get_owner_document_tups @ a_get_owner_document_tups) ptr ()"
end

global_interpretation l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_root_node get_root_node_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_host get_host_locs
  defines get_owner_document_tups = "l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_owner_document_tups"
    and get_owner_document =
    "l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_owner_document get_root_node get_disconnected_nodes"
    and get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r =
    "l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r"
    and get_owner_document_tups\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
    "l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_owner_document_tups get_root_node get_disconnected_nodes"
    and get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r =
    "l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r get_root_node get_disconnected_nodes"
  .

locale l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_root_node get_root_node_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_host get_host_locs +
  l_get_owner_document_defs get_owner_document +
  l_get_host get_host get_host_locs +
  CD: l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_parent get_parent_locs known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes
  get_disconnected_nodes_locs get_root_node get_root_node_locs get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  for known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_::linorder) object_ptr \<Rightarrow> bool"
    and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
    and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_owner_document :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes get_owner_document_impl: "get_owner_document = a_get_owner_document"
begin
lemmas get_owner_document_def = a_get_owner_document_def[folded get_owner_document_impl]

lemma get_owner_document_pure [simp]:
  "pure (get_owner_document ptr) h"
proof -
  have "\<And>shadow_root_ptr. pure (a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr ()) h"
    apply(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_pure_I filter_M_pure_I
        split: option.splits)[1]
    by(auto simp add: CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_pure_I filter_M_pure_I
        split: option.splits)
  then show ?thesis
    apply(auto simp add: get_owner_document_def)[1]
    apply(split CD.get_owner_document_splits, rule conjI)+
     apply(simp)
    apply(auto simp add: a_get_owner_document_tups_def)[1]
    apply(split invoke_splits, rule conjI)+
     apply simp
    by(auto intro!: bind_pure_I)
qed

lemma get_owner_document_ptr_in_heap:
  assumes "h \<turnstile> ok (get_owner_document ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms
  by(auto simp add: get_owner_document_def invoke_ptr_in_heap dest: is_OK_returns_heap_I)
end

interpretation
  i_get_owner_document?: l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M DocumentClass.known_ptr get_parent get_parent_locs
  DocumentClass.type_wf get_disconnected_nodes get_disconnected_nodes_locs get_root_node get_root_node_locs CD.a_get_owner_document get_host get_host_locs get_owner_document get_child_nodes get_child_nodes_locs
  using get_child_nodes_is_l_get_child_nodes[unfolded ShadowRootClass.known_ptr_defs]
  by(auto simp add:  instances l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_owner_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def get_owner_document_def Core_DOM_Functions.get_owner_document_def)
declare l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_owner_document_is_l_get_owner_document [instances]: "l_get_owner_document get_owner_document"
  apply(auto simp add: l_get_owner_document_def)[1]
  using get_owner_document_ptr_in_heap apply fast
  done




subsubsection \<open>remove\_child\<close>

global_interpretation l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs set_child_nodes
  set_child_nodes_locs get_parent get_parent_locs get_owner_document get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs
  defines remove = "l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_remove get_child_nodes set_child_nodes get_parent
get_owner_document get_disconnected_nodes set_disconnected_nodes"
    and remove_child = "l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_remove_child get_child_nodes set_child_nodes
get_owner_document get_disconnected_nodes set_disconnected_nodes"
    and remove_child_locs = "l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_remove_child_locs set_child_nodes_locs
set_disconnected_nodes_locs"
  .

interpretation i_remove_child?: l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M Shadow_DOM.get_child_nodes
  Shadow_DOM.get_child_nodes_locs Shadow_DOM.set_child_nodes Shadow_DOM.set_child_nodes_locs
  Shadow_DOM.get_parent Shadow_DOM.get_parent_locs
  Shadow_DOM.get_owner_document get_disconnected_nodes get_disconnected_nodes_locs
  set_disconnected_nodes set_disconnected_nodes_locs remove_child remove_child_locs remove
  ShadowRootClass.type_wf
  ShadowRootClass.known_ptr ShadowRootClass.known_ptrs
  by(auto simp add: l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def remove_child_def
      remove_child_locs_def remove_def instances)
declare l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsubsection \<open>get\_disconnected\_document\<close>

locale l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_disconnected_nodes_defs get_disconnected_nodes get_disconnected_nodes_locs
  for get_disconnected_nodes :: "(_::linorder) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_get_disconnected_document :: "(_) node_ptr \<Rightarrow> (_, (_) document_ptr) dom_prog"
  where
    "a_get_disconnected_document node_ptr = do {
      check_in_heap (cast node_ptr);
      ptrs \<leftarrow> document_ptr_kinds_M;
      candidates \<leftarrow> filter_M (\<lambda>document_ptr. do {
        disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
        return (node_ptr \<in> set disconnected_nodes)
      }) ptrs;
      (case candidates of
        Cons document_ptr [] \<Rightarrow> return document_ptr |
        _ \<Rightarrow> error HierarchyRequestError
      )
    }"
definition "a_get_disconnected_document_locs =
(\<Union>document_ptr. get_disconnected_nodes_locs document_ptr) \<union> (\<Union>ptr. {preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr RObject.nothing)})"
end

locale l_get_disconnected_document_defs =
  fixes get_disconnected_document :: "(_) node_ptr \<Rightarrow> (_, (_::linorder) document_ptr) dom_prog"
  fixes get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_disconnected_document_defs +
  l_get_disconnected_nodes +
  assumes get_disconnected_document_impl: "get_disconnected_document = a_get_disconnected_document"
  assumes get_disconnected_document_locs_impl: "get_disconnected_document_locs = a_get_disconnected_document_locs"
begin
lemmas get_disconnected_document_def =
  get_disconnected_document_impl[unfolded a_get_disconnected_document_def]
lemmas get_disconnected_document_locs_def =
  get_disconnected_document_locs_impl[unfolded a_get_disconnected_document_locs_def]


lemma get_disconnected_document_pure [simp]: "pure (get_disconnected_document ptr) h"
  using get_disconnected_nodes_pure
  by(auto simp add: get_disconnected_document_def intro!: bind_pure_I filter_M_pure_I split: list.splits)

lemma get_disconnected_document_ptr_in_heap [simp]:
  "h \<turnstile> ok (get_disconnected_document node_ptr) \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h"
  using get_disconnected_document_def is_OK_returns_result_I check_in_heap_ptr_in_heap
  by (metis (no_types, lifting) bind_returns_heap_E get_disconnected_document_pure
      node_ptr_kinds_commutes pure_pure)

lemma get_disconnected_document_disconnected_document_in_heap:
  assumes "h \<turnstile> get_disconnected_document child_node \<rightarrow>\<^sub>r disconnected_document"
  shows "disconnected_document |\<in>| document_ptr_kinds h"
  using assms get_disconnected_nodes_pure
  by(auto simp add: get_disconnected_document_def elim!: bind_returns_result_E2
      dest!: filter_M_not_more_elements[where x=disconnected_document]
      intro!: filter_M_pure_I bind_pure_I
      split: if_splits list.splits)

lemma get_disconnected_document_reads:
  "reads get_disconnected_document_locs (get_disconnected_document node_ptr) h h'"
  using get_disconnected_nodes_reads[unfolded reads_def]
  by(auto simp add: get_disconnected_document_def get_disconnected_document_locs_def
      intro!: reads_bind_pure reads_subset[OF check_in_heap_reads]
      reads_subset[OF error_reads]
      reads_subset[OF get_disconnected_nodes_reads] reads_subset[OF return_reads]
      reads_subset[OF document_ptr_kinds_M_reads] filter_M_reads filter_M_pure_I bind_pure_I
      split: list.splits)

end

locale l_get_disconnected_document = l_get_disconnected_document_defs +
  assumes get_disconnected_document_reads:
    "reads get_disconnected_document_locs (get_disconnected_document node_ptr) h h'"
  assumes get_disconnected_document_ptr_in_heap:
    "h \<turnstile> ok (get_disconnected_document node_ptr) \<Longrightarrow> node_ptr |\<in>| node_ptr_kinds h"
  assumes get_disconnected_document_pure [simp]:
    "pure (get_disconnected_document node_ptr) h"
  assumes get_disconnected_document_disconnected_document_in_heap:
    "h \<turnstile> get_disconnected_document child_node \<rightarrow>\<^sub>r disconnected_document \<Longrightarrow>
disconnected_document |\<in>| document_ptr_kinds h"

global_interpretation l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_disconnected_nodes
  get_disconnected_nodes_locs defines
  get_disconnected_document = "l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_disconnected_document
get_disconnected_nodes" and
  get_disconnected_document_locs = "l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_get_disconnected_document_locs
get_disconnected_nodes_locs" .

interpretation i_get_disconnected_document?: l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_disconnected_nodes get_disconnected_nodes_locs get_disconnected_document get_disconnected_document_locs type_wf
  by(auto simp add: l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      get_disconnected_document_def get_disconnected_document_locs_def instances)
declare l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_disconnected_document_is_l_get_disconnected_document [instances]:
  "l_get_disconnected_document get_disconnected_document get_disconnected_document_locs"
  apply(auto simp add: l_get_disconnected_document_def instances)[1]
  using get_disconnected_document_ptr_in_heap get_disconnected_document_pure
    get_disconnected_document_disconnected_document_in_heap get_disconnected_document_reads
  by blast+

paragraph \<open>get\_disconnected\_nodes\<close>

locale l_set_tag_name_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_tag_name_get_disconnected_nodes:
  "\<forall>w \<in> set_tag_name_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_disconnected_nodes_locs ptr'. r h h'))"
  by(auto simp add: CD.set_tag_name_locs_impl[unfolded CD.a_set_tag_name_locs_def]
      CD.get_disconnected_nodes_locs_impl[unfolded CD.a_get_disconnected_nodes_locs_def]
      all_args_def)
end

interpretation
  i_set_tag_name_get_disconnected_nodes?: l_set_tag_name_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf
  set_tag_name set_tag_name_locs get_disconnected_nodes
  get_disconnected_nodes_locs
  by unfold_locales
declare l_set_tag_name_get_disconnected_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_tag_name_get_disconnected_nodes_is_l_set_tag_name_get_disconnected_nodes [instances]:
  "l_set_tag_name_get_disconnected_nodes type_wf set_tag_name set_tag_name_locs get_disconnected_nodes
                                         get_disconnected_nodes_locs"
  using set_tag_name_is_l_set_tag_name get_disconnected_nodes_is_l_get_disconnected_nodes
  apply(simp add: l_set_tag_name_get_disconnected_nodes_def
      l_set_tag_name_get_disconnected_nodes_axioms_def)
  using set_tag_name_get_disconnected_nodes
  by fast


subsubsection \<open>get\_ancestors\_di\<close>

locale l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_parent_defs get_parent get_parent_locs +
  l_get_host_defs get_host get_host_locs +
  l_get_disconnected_document_defs get_disconnected_document get_disconnected_document_locs
  for get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_::linorder) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_document :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
partial_function (dom_prog) a_get_ancestors_di :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  where
    "a_get_ancestors_di ptr = do {
      check_in_heap ptr;
      ancestors \<leftarrow> (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr of
        Some node_ptr \<Rightarrow> do {
          parent_ptr_opt \<leftarrow> get_parent node_ptr;
          (case parent_ptr_opt of
            Some parent_ptr \<Rightarrow> a_get_ancestors_di parent_ptr
          | None \<Rightarrow> do {
              document_ptr \<leftarrow> get_disconnected_document node_ptr;
              a_get_ancestors_di (cast document_ptr)
            })
        }
      | None \<Rightarrow> (case cast ptr of
          Some shadow_root_ptr \<Rightarrow> do {
            host \<leftarrow> get_host shadow_root_ptr;
            a_get_ancestors_di (cast host)
          } |
          None \<Rightarrow> return []));
      return (ptr # ancestors)
    }"

definition "a_get_ancestors_di_locs = get_parent_locs \<union> get_host_locs \<union> get_disconnected_document_locs"
end

locale l_get_ancestors_di_defs =
  fixes get_ancestors_di :: "(_::linorder) object_ptr \<Rightarrow> (_, (_) object_ptr list) dom_prog"
  fixes get_ancestors_di_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"

locale l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_parent +
  l_get_host +
  l_get_disconnected_document +
  l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs +
  l_get_ancestors_di_defs +
  assumes get_ancestors_di_impl: "get_ancestors_di = a_get_ancestors_di"
  assumes get_ancestors_di_locs_impl: "get_ancestors_di_locs = a_get_ancestors_di_locs"
begin
lemmas get_ancestors_di_def = a_get_ancestors_di.simps[folded get_ancestors_di_impl]
lemmas get_ancestors_di_locs_def = a_get_ancestors_di_locs_def[folded get_ancestors_di_locs_impl]


lemma get_ancestors_di_pure [simp]:
  "pure (get_ancestors_di ptr) h"
proof -
  have "\<forall>ptr h h' x. h \<turnstile> get_ancestors_di ptr \<rightarrow>\<^sub>r x \<longrightarrow> h \<turnstile> get_ancestors_di ptr \<rightarrow>\<^sub>h h' \<longrightarrow> h = h'"
  proof (induct rule: a_get_ancestors_di.fixp_induct[folded get_ancestors_di_impl])
    case 1
    then show ?case
      by(rule admissible_dom_prog)
  next
    case 2
    then show ?case
      by simp
  next
    case (3 f)
    then show ?case
      using get_parent_pure get_host_pure get_disconnected_document_pure
      apply(auto simp add: pure_returns_heap_eq pure_def split: option.splits elim!: bind_returns_heap_E
          bind_returns_result_E dest!: pure_returns_heap_eq[rotated, OF check_in_heap_pure])[1]
          apply (metis is_OK_returns_result_I returns_heap_eq returns_result_eq)
         apply (meson option.simps(3) returns_result_eq)
        apply (meson option.simps(3) returns_result_eq)
       apply(metis get_parent_pure pure_returns_heap_eq)
      apply(metis get_host_pure pure_returns_heap_eq)
      done
  qed
  then show ?thesis
    by (meson pure_eq_iff)
qed

lemma get_ancestors_di_ptr:
  assumes "h \<turnstile> get_ancestors_di ptr \<rightarrow>\<^sub>r ancestors"
  shows "ptr \<in> set ancestors"
  using assms
  by(simp add: get_ancestors_di_def) (auto  elim!: bind_returns_result_E2 split: option.splits
      intro!: bind_pure_I)

lemma get_ancestors_di_ptr_in_heap:
  assumes "h \<turnstile> ok (get_ancestors_di ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms
  by(auto simp add: get_ancestors_di_def check_in_heap_ptr_in_heap elim!: bind_is_OK_E
      dest: is_OK_returns_result_I)

lemma get_ancestors_di_never_empty:
  assumes "h \<turnstile> get_ancestors_di child \<rightarrow>\<^sub>r ancestors"
  shows "ancestors \<noteq> []"
  using assms
  apply(simp add: get_ancestors_di_def)
  by(auto elim!: bind_returns_result_E2 split: option.splits intro!: bind_pure_I)
end

global_interpretation l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_parent get_parent_locs get_host get_host_locs
  get_disconnected_document get_disconnected_document_locs
  defines get_ancestors_di = a_get_ancestors_di
    and get_ancestors_di_locs = a_get_ancestors_di_locs .
declare a_get_ancestors_di.simps [code]

interpretation i_get_ancestors_di?: l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_host get_host_locs get_disconnected_document get_disconnected_document_locs get_ancestors_di get_ancestors_di_locs
  by(auto simp add: l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      get_ancestors_di_def get_ancestors_di_locs_def instances)
declare l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_ancestors_di_is_l_get_ancestors [instances]: "l_get_ancestors get_ancestors_di"
  apply(auto simp add: l_get_ancestors_def)[1]
  using get_ancestors_di_ptr_in_heap apply fast
  using get_ancestors_di_ptr apply fast
  done

subsubsection \<open>adopt\_node\<close>

locale l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w_\<^sub>D\<^sub>O\<^sub>M_defs =
  CD: l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_owner_document get_parent get_parent_locs remove_child
  remove_child_locs get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs +
  l_get_ancestors_di_defs get_ancestors_di get_ancestors_di_locs
  for get_owner_document :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and remove_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and remove_child_locs :: "(_) object_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_ancestors_di :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and get_ancestors_di_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_adopt_node :: "(_) document_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_, unit) dom_prog"
  where
    "a_adopt_node document node = do {
      ancestors \<leftarrow> get_ancestors_di (cast document);
      (if cast node \<in> set ancestors
        then error HierarchyRequestError
        else CD.a_adopt_node document node)}"

definition a_adopt_node_locs ::
  "(_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"
  where "a_adopt_node_locs = CD.a_adopt_node_locs"
end

locale l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w_\<^sub>D\<^sub>O\<^sub>M_defs get_owner_document get_parent get_parent_locs remove_child
  remove_child_locs get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs get_ancestors_di get_ancestors_di_locs +
  l_adopt_node_defs adopt_node adopt_node_locs +
  l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf known_ptr known_ptrs get_parent get_parent_locs
  get_child_nodes get_child_nodes_locs get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs get_ancestors_di get_ancestors_di_locs +
  CD: l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_owner_document get_parent get_parent_locs remove_child
  remove_child_locs get_disconnected_nodes get_disconnected_nodes_locs
  set_disconnected_nodes set_disconnected_nodes_locs adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs set_child_nodes
  set_child_nodes_locs remove
  for get_owner_document :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and remove_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and remove_child_locs :: "(_) object_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_ancestors_di :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog"
    and get_ancestors_di_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and adopt_node :: "(_) document_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and adopt_node_locs ::
    "(_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) document_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M ::
    "(_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and known_ptrs :: "(_) heap \<Rightarrow> bool"
    and set_child_nodes :: "(_) object_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_document :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and remove :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog" +
  assumes adopt_node_impl: "adopt_node = a_adopt_node"
  assumes adopt_node_locs_impl: "adopt_node_locs = a_adopt_node_locs"
begin
lemmas adopt_node_def = a_adopt_node_def[folded adopt_node_impl CD.adopt_node_impl]
lemmas adopt_node_locs_def = a_adopt_node_locs_def[folded adopt_node_locs_impl CD.adopt_node_locs_impl]

lemma adopt_node_writes:
  "writes (adopt_node_locs |h \<turnstile> get_parent node|\<^sub>r
           |h \<turnstile> get_owner_document (cast node)|\<^sub>r document_ptr) (adopt_node document_ptr node) h h'"
  by(auto simp add: CD.adopt_node_writes adopt_node_def CD.adopt_node_impl[symmetric]
      adopt_node_locs_def CD.adopt_node_locs_impl[symmetric]
      intro!: writes_bind_pure[OF get_ancestors_di_pure])

lemma adopt_node_pointers_preserved:
  "w \<in> adopt_node_locs parent owner_document document_ptr
   \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> object_ptr_kinds h = object_ptr_kinds h'"
  using CD.adopt_node_locs_impl CD.adopt_node_pointers_preserved local.adopt_node_locs_def by blast
lemma adopt_node_types_preserved:
  "w \<in> adopt_node_locs parent owner_document document_ptr
   \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  using CD.adopt_node_locs_impl CD.adopt_node_types_preserved local.adopt_node_locs_def by blast
lemma adopt_node_child_in_heap:
  "h \<turnstile> ok (adopt_node document_ptr child) \<Longrightarrow> child |\<in>| node_ptr_kinds h"
  by (smt CD.adopt_node_child_in_heap CD.adopt_node_impl bind_is_OK_E error_returns_heap
      is_OK_returns_heap_E l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M.adopt_node_def l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms
      local.get_ancestors_di_pure pure_returns_heap_eq)
lemma adopt_node_children_subset:
  "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children
     \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children'
     \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h \<Longrightarrow> set children' \<subseteq> set children"
  by (smt CD.adopt_node_children_subset CD.adopt_node_impl bind_returns_heap_E error_returns_heap
      local.adopt_node_def local.get_ancestors_di_pure pure_returns_heap_eq)
end

global_interpretation l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w_\<^sub>D\<^sub>O\<^sub>M_defs get_owner_document get_parent get_parent_locs
  remove_child remove_child_locs get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs get_ancestors_di get_ancestors_di_locs
  defines adopt_node = "a_adopt_node"
    and adopt_node_locs = "a_adopt_node_locs"
    and adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = "CD.a_adopt_node"
    and adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = "CD.a_adopt_node_locs"
  .
interpretation i_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M: l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document get_parent get_parent_locs remove_child remove_child_locs
  get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs
  adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes get_child_nodes_locs
  known_ptrs set_child_nodes set_child_nodes_locs remove
  by(auto simp add: l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def
      adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare i_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

interpretation i_adopt_node?: l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document get_parent get_parent_locs remove_child remove_child_locs get_disconnected_nodes
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs get_ancestors_di
  get_ancestors_di_locs adopt_node adopt_node_locs CD.a_adopt_node CD.a_adopt_node_locs known_ptr
  type_wf get_child_nodes get_child_nodes_locs known_ptrs set_child_nodes set_child_nodes_locs
  get_host get_host_locs get_disconnected_document get_disconnected_document_locs remove
  by(auto simp add: l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def adopt_node_def
      adopt_node_locs_def instances)
declare l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma adopt_node_is_l_adopt_node [instances]: "l_adopt_node type_wf known_ptr known_ptrs get_parent
adopt_node adopt_node_locs get_child_nodes get_owner_document"
  apply(auto simp add: l_adopt_node_def l_adopt_node_axioms_def instances)[1]
  using adopt_node_writes apply fast
  using adopt_node_pointers_preserved apply (fast, fast)
  using adopt_node_types_preserved apply (fast, fast)
  using adopt_node_child_in_heap apply fast
  using adopt_node_children_subset apply fast
  done



paragraph \<open>get\_shadow\_root\<close>

locale l_adopt_node_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_child_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_disconnected_nodes_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma adopt_node_get_shadow_root:
  "\<forall>w \<in> adopt_node_locs parent owner_document document_ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow>
(\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"
  by(auto simp add: adopt_node_locs_def CD.adopt_node_locs_def CD.remove_child_locs_def
      all_args_def set_disconnected_nodes_get_shadow_root set_child_nodes_get_shadow_root)
end

locale l_adopt_node_get_shadow_root = l_adopt_node_defs + l_get_shadow_root_defs +
  assumes adopt_node_get_shadow_root:
    "\<forall>w \<in> adopt_node_locs parent owner_document document_ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow>
(\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"

interpretation i_adopt_node_get_shadow_root?: l_adopt_node_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr DocumentClass.type_wf DocumentClass.known_ptr set_child_nodes set_child_nodes_locs
  Core_DOM_Functions.set_child_nodes Core_DOM_Functions.set_child_nodes_locs get_shadow_root
  get_shadow_root_locs set_disconnected_nodes set_disconnected_nodes_locs get_owner_document
  get_parent get_parent_locs remove_child remove_child_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_ancestors_di get_ancestors_di_locs adopt_node adopt_node_locs
  adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs known_ptrs get_host
  get_host_locs get_disconnected_document get_disconnected_document_locs remove
  by(auto simp add: l_adopt_node_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_adopt_node_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

interpretation i_adopt_node_get_shadow_root?: l_adopt_node_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr DocumentClass.type_wf DocumentClass.known_ptr set_child_nodes
  set_child_nodes_locs Core_DOM_Functions.set_child_nodes Core_DOM_Functions.set_child_nodes_locs
  get_shadow_root get_shadow_root_locs set_disconnected_nodes set_disconnected_nodes_locs
  get_owner_document get_parent get_parent_locs remove_child remove_child_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_ancestors_di get_ancestors_di_locs adopt_node adopt_node_locs
  adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs known_ptrs get_host
  get_host_locs get_disconnected_document get_disconnected_document_locs remove
  by(auto simp add: l_adopt_node_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_adopt_node_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma adopt_node_get_shadow_root_is_l_adopt_node_get_shadow_root [instances]:
  "l_adopt_node_get_shadow_root adopt_node_locs get_shadow_root_locs"
  apply(auto simp add: l_adopt_node_get_shadow_root_def)[1]
  using adopt_node_get_shadow_root apply fast
  done



subsubsection \<open>insert\_before\<close>

global_interpretation l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_parent get_parent_locs get_child_nodes
  get_child_nodes_locs set_child_nodes set_child_nodes_locs get_ancestors_di get_ancestors_di_locs
  adopt_node adopt_node_locs set_disconnected_nodes set_disconnected_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_owner_document
  defines
    next_sibling = a_next_sibling and
    insert_node = a_insert_node and
    ensure_pre_insertion_validity = a_ensure_pre_insertion_validity and
    insert_before = a_insert_before and
    insert_before_locs = a_insert_before_locs
  .
global_interpretation l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs insert_before
  defines append_child = "l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_append_child insert_before"
  .

interpretation i_insert_before?: l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_parent get_parent_locs get_child_nodes
  get_child_nodes_locs set_child_nodes set_child_nodes_locs get_ancestors_di get_ancestors_di_locs
  adopt_node adopt_node_locs set_disconnected_nodes set_disconnected_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_owner_document insert_before insert_before_locs append_child type_wf
  known_ptr known_ptrs
  by(auto simp add: l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def insert_before_def
      insert_before_locs_def instances)
declare l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

interpretation i_append_child?: l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M append_child insert_before insert_before_locs
  by(simp add: l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances append_child_def)
declare l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


subsubsection \<open>get\_assigned\_nodes\<close>

fun map_filter_M2 :: "('x \<Rightarrow> ('heap, 'e, 'y option) prog) \<Rightarrow> 'x list
  \<Rightarrow> ('heap, 'e, 'y list) prog"
  where
    "map_filter_M2 f [] = return []" |
    "map_filter_M2 f (x # xs) = do {
      res \<leftarrow> f x;
      remainder \<leftarrow> map_filter_M2 f xs;
      return ((case res of  Some r \<Rightarrow> [r] | None \<Rightarrow> []) @ remainder)
    }"
lemma map_filter_M2_pure [simp]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> pure (f x) h"
  shows "pure (map_filter_M2 f xs) h"
  using assms
  apply(induct xs arbitrary: h)
  by(auto elim!: bind_returns_result_E2 intro!: bind_pure_I)

lemma map_filter_pure_no_monad:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> pure (f x) h"
  assumes "h \<turnstile> map_filter_M2 f xs \<rightarrow>\<^sub>r ys"
  shows
    "ys = map the (filter (\<lambda>x. x \<noteq> None) (map (\<lambda>x. |h \<turnstile> f x|\<^sub>r) xs))" and
    "\<And>x. x \<in> set xs \<Longrightarrow> h \<turnstile> ok (f x)"
  using assms
   apply(induct xs arbitrary: h ys)
  by(auto elim!: bind_returns_result_E2)

lemma map_filter_pure_foo:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> pure (f x) h"
  assumes "h \<turnstile> map_filter_M2 f xs \<rightarrow>\<^sub>r ys"
  assumes "y \<in> set ys"
  obtains x where "h \<turnstile> f x \<rightarrow>\<^sub>r Some y" and "x \<in> set xs"
  using assms
  apply(induct xs arbitrary: ys)
  by(auto elim!: bind_returns_result_E2)


lemma map_filter_M2_in_result:
  assumes "h \<turnstile> map_filter_M2 P xs \<rightarrow>\<^sub>r ys"
  assumes "a \<in> set xs"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h"
  assumes "h \<turnstile> P a \<rightarrow>\<^sub>r Some b"
  shows "b \<in> set ys"
  using assms
  apply(induct xs arbitrary: h ys)
  by(auto elim!: bind_returns_result_E2 )


locale l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  l_get_tag_name_defs get_tag_name get_tag_name_locs +
  l_get_root_node_defs get_root_node get_root_node_locs +
  l_get_host_defs get_host get_host_locs +
  l_get_child_nodes_defs get_child_nodes get_child_nodes_locs +
  l_find_slot_defs find_slot assigned_slot +
  l_remove_defs remove +
  l_insert_before_defs insert_before insert_before_locs +
  l_append_child_defs append_child +
  l_remove_shadow_root_defs remove_shadow_root remove_shadow_root_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
    and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and find_slot :: "bool \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
    and assigned_slot :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
    and remove :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and insert_before ::
    "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_) node_ptr option \<Rightarrow> ((_) heap, exception, unit) prog"
    and insert_before_locs ::
    "(_) object_ptr \<Rightarrow> (_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"
    and append_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and remove_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and remove_shadow_root_locs ::
    "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
begin
definition a_assigned_nodes :: "(_) element_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  where
    "a_assigned_nodes slot = do {
      tag \<leftarrow> get_tag_name slot;
      (if tag \<noteq> ''slot''
      then error HierarchyRequestError
      else return ());
      root \<leftarrow> get_root_node (cast slot);
      if is_shadow_root_ptr_kind root
      then do {
        host \<leftarrow> get_host (the (cast root));
        children \<leftarrow> get_child_nodes (cast host);
        filter_M (\<lambda>slotable. do {
          found_slot \<leftarrow> find_slot False slotable;
          return (found_slot = Some slot)}) children}
      else return []}"

partial_function (dom_prog) a_assigned_nodes_flatten ::
  "(_) element_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  where
    "a_assigned_nodes_flatten slot = do {
      tag \<leftarrow> get_tag_name slot;
      (if tag \<noteq> ''slot''
      then error HierarchyRequestError
      else return ());
      root \<leftarrow> get_root_node (cast slot);
      (if is_shadow_root_ptr_kind root
      then do {
        slotables \<leftarrow> a_assigned_nodes slot;
        slotables_or_child_nodes \<leftarrow> (if slotables = []
        then do {
          get_child_nodes (cast slot)
        } else do {
          return slotables
        });
        list_of_lists \<leftarrow> map_M (\<lambda>node_ptr. do {
          (case cast node_ptr of
            Some element_ptr \<Rightarrow> do {
              tag \<leftarrow> get_tag_name element_ptr;
              (if tag = ''slot''
              then do {
                root \<leftarrow> get_root_node (cast element_ptr);
                (if is_shadow_root_ptr_kind root
                then do {
                  a_assigned_nodes_flatten element_ptr
                } else do {
                  return [node_ptr]
                })
              } else do {
                return [node_ptr]
              })
            }
            | None \<Rightarrow> return [node_ptr])
        }) slotables_or_child_nodes;
        return (concat list_of_lists)
      } else return [])
    }"

definition a_flatten_dom :: "(_, unit) dom_prog" where
  "a_flatten_dom = do {
    tups \<leftarrow> element_ptr_kinds_M \<bind> map_filter_M2 (\<lambda>element_ptr. do {
      tag \<leftarrow> get_tag_name element_ptr;
      assigned_nodes \<leftarrow> a_assigned_nodes element_ptr;
      (if tag = ''slot'' \<and> assigned_nodes \<noteq> []
      then return (Some (element_ptr, assigned_nodes)) else return None)});
    forall_M (\<lambda>(slot, assigned_nodes). do {
      get_child_nodes (cast slot) \<bind> forall_M remove;
      forall_M (append_child (cast slot)) assigned_nodes
    }) tups;
    shadow_root_ptr_kinds_M \<bind> forall_M (\<lambda>shadow_root_ptr. do {
      host \<leftarrow> get_host shadow_root_ptr;
      get_child_nodes (cast host) \<bind> forall_M remove;
      get_child_nodes (cast shadow_root_ptr) \<bind> forall_M (append_child (cast host));
      remove_shadow_root host
    });
    return ()
  }"
end

global_interpretation l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs
  get_tag_name get_tag_name_locs get_root_node get_root_node_locs get_host get_host_locs
  find_slot assigned_slot remove insert_before insert_before_locs append_child remove_shadow_root
  remove_shadow_root_locs
  defines assigned_nodes =
    "l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_assigned_nodes get_child_nodes get_tag_name get_root_node get_host
find_slot"
    and assigned_nodes_flatten =
    "l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_assigned_nodes_flatten get_child_nodes get_tag_name get_root_node
get_host find_slot"
    and flatten_dom =
    "l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_flatten_dom get_child_nodes get_tag_name get_root_node get_host
find_slot remove append_child remove_shadow_root"
  .

declare a_assigned_nodes_flatten.simps [code]

locale l_assigned_nodes_defs =
  fixes assigned_nodes :: "(_) element_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  fixes assigned_nodes_flatten :: "(_) element_ptr \<Rightarrow> (_, (_) node_ptr list) dom_prog"
  fixes flatten_dom :: "(_, unit) dom_prog"

locale l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_assigned_nodes_defs
  assigned_nodes assigned_nodes_flatten flatten_dom
  + l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  get_child_nodes get_child_nodes_locs get_tag_name get_tag_name_locs get_root_node
  get_root_node_locs get_host get_host_locs find_slot assigned_slot remove insert_before
  insert_before_locs append_child remove_shadow_root remove_shadow_root_locs
  (* + l_get_element_by\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M *)
  + l_get_shadow_root
  type_wf get_shadow_root get_shadow_root_locs
  + l_set_shadow_root
  type_wf set_shadow_root set_shadow_root_locs
  + l_remove
  + l_insert_before
  insert_before insert_before_locs
  + l_find_slot
  find_slot assigned_slot
  + l_get_tag_name
  type_wf get_tag_name get_tag_name_locs
  + l_get_root_node
  get_root_node get_root_node_locs get_parent get_parent_locs
  + l_get_host
  get_host get_host_locs
  + l_get_child_nodes
  type_wf known_ptr get_child_nodes get_child_nodes_locs
  + l_to_tree_order
  to_tree_order
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
    and assigned_nodes :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and assigned_nodes_flatten :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and flatten_dom :: "((_) heap, exception, unit) prog"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_root_node :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr) prog"
    and get_root_node_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and find_slot :: "bool \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
    and assigned_slot :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr option) prog"
    and remove :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and insert_before :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> (_) node_ptr option \<Rightarrow> ((_) heap, exception, unit) prog"
    and insert_before_locs ::
    "(_) object_ptr \<Rightarrow> (_) object_ptr option \<Rightarrow> (_) document_ptr \<Rightarrow> (_) document_ptr \<Rightarrow> (_, unit) dom_prog set"
    and append_child :: "(_) object_ptr \<Rightarrow> (_) node_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and remove_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog"
    and remove_shadow_root_locs :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and set_shadow_root :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and to_tree_order :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr list) prog" +
  assumes assigned_nodes_impl: "assigned_nodes = a_assigned_nodes"
  assumes flatten_dom_impl: "flatten_dom = a_flatten_dom"
begin
lemmas assigned_nodes_def = assigned_nodes_impl[unfolded a_assigned_nodes_def]
lemmas flatten_dom_def = flatten_dom_impl[unfolded a_flatten_dom_def, folded assigned_nodes_impl]

lemma assigned_nodes_pure [simp]: "pure (assigned_nodes slot) h"
  by(auto simp add: assigned_nodes_def intro!: bind_pure_I filter_M_pure_I)

lemma assigned_nodes_ptr_in_heap:
  assumes "h \<turnstile> ok (assigned_nodes slot)"
  shows "slot |\<in>| element_ptr_kinds h"
  using assms
  apply(auto simp add: assigned_nodes_def)[1]
  by (meson bind_is_OK_E is_OK_returns_result_I local.get_tag_name_ptr_in_heap)

lemma assigned_nodes_slot_is_slot:
  assumes "h \<turnstile> ok (assigned_nodes slot)"
  shows "h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
  using assms
  by(auto simp add: assigned_nodes_def elim!: bind_is_OK_E split: if_splits)

lemma assigned_nodes_different_ptr:
  assumes "h \<turnstile> assigned_nodes slot \<rightarrow>\<^sub>r nodes"
  assumes "h \<turnstile> assigned_nodes slot' \<rightarrow>\<^sub>r nodes'"
  assumes "slot \<noteq> slot'"
  shows "set nodes \<inter> set nodes' = {}"
proof (rule ccontr)
  assume "set nodes \<inter> set nodes' \<noteq> {} "
  then obtain common_ptr where "common_ptr \<in> set nodes" and "common_ptr \<in> set nodes'"
    by auto

  have "h \<turnstile> find_slot False common_ptr \<rightarrow>\<^sub>r Some slot"
    using \<open>common_ptr \<in> set nodes\<close>
    using assms(1)
    by(auto simp add: assigned_nodes_def elim!: bind_returns_result_E2 split: if_splits
        dest!: filter_M_holds_for_result[where x=common_ptr] intro!: bind_pure_I)
  moreover
  have "h \<turnstile> find_slot False common_ptr \<rightarrow>\<^sub>r Some slot'"
    using \<open>common_ptr \<in> set nodes'\<close>
    using assms(2)
    by(auto simp add: assigned_nodes_def elim!: bind_returns_result_E2 split: if_splits
        dest!: filter_M_holds_for_result[where x=common_ptr] intro!: bind_pure_I)
  ultimately
  show False
    using assms(3)
    by (meson option.inject returns_result_eq)
qed
end

interpretation i_assigned_nodes?: l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr assigned_nodes
  assigned_nodes_flatten flatten_dom get_child_nodes get_child_nodes_locs get_tag_name
  get_tag_name_locs get_root_node get_root_node_locs get_host get_host_locs find_slot assigned_slot
  remove insert_before insert_before_locs append_child remove_shadow_root remove_shadow_root_locs
  type_wf get_shadow_root get_shadow_root_locs set_shadow_root set_shadow_root_locs get_parent
  get_parent_locs to_tree_order
  by(auto simp add: instances l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      assigned_nodes_def flatten_dom_def)
declare l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_assigned_nodes = l_assigned_nodes_defs +
  assumes assigned_nodes_pure [simp]: "pure (assigned_nodes slot) h"
  assumes assigned_nodes_ptr_in_heap: "h \<turnstile> ok (assigned_nodes slot) \<Longrightarrow> slot |\<in>| element_ptr_kinds h"
  assumes assigned_nodes_slot_is_slot: "h \<turnstile> ok (assigned_nodes slot) \<Longrightarrow> h \<turnstile> get_tag_name slot \<rightarrow>\<^sub>r ''slot''"
  assumes assigned_nodes_different_ptr:
    "h \<turnstile> assigned_nodes slot \<rightarrow>\<^sub>r nodes \<Longrightarrow> h \<turnstile> assigned_nodes slot' \<rightarrow>\<^sub>r nodes' \<Longrightarrow> slot \<noteq> slot' \<Longrightarrow>
set nodes \<inter> set nodes' = {}"

lemma assigned_nodes_is_l_assigned_nodes [instances]: "l_assigned_nodes assigned_nodes"
  apply(auto simp add: l_assigned_nodes_def)[1]
  using assigned_nodes_ptr_in_heap apply fast
  using assigned_nodes_slot_is_slot apply fast
  using assigned_nodes_different_ptr apply fast
  done


subsubsection \<open>set\_val\<close>

locale l_set_val\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  CD: l_set_val\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M set_val set_val_locs +
  l_type_wf type_wf
  for type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> (_, unit) dom_prog"
    and set_val_locs :: "(_) character_data_ptr \<Rightarrow> (_, unit) dom_prog set"  +
  assumes type_wf_impl: "type_wf = ShadowRootClass.type_wf"
begin

lemma set_val_ok:
  "type_wf h \<Longrightarrow> character_data_ptr |\<in>| character_data_ptr_kinds h \<Longrightarrow>
h \<turnstile> ok (set_val character_data_ptr tag)"
  using CD.set_val_ok CD.type_wf_impl ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t local.type_wf_impl by blast

lemma set_val_writes: "writes (set_val_locs character_data_ptr) (set_val character_data_ptr tag) h h'"
  using CD.set_val_writes .

lemma set_val_pointers_preserved:
  assumes "w \<in> set_val_locs character_data_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h'"
  using assms CD.set_val_pointers_preserved by simp

lemma set_val_typess_preserved:
  assumes "w \<in> set_val_locs character_data_ptr"
  assumes "h \<turnstile> w \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  apply(unfold type_wf_impl)
  using assms(1) type_wf_preserved[OF writes_singleton2 assms(2)]
  by(auto simp add: all_args_def CD.set_val_locs_impl[unfolded CD.a_set_val_locs_def] split: if_splits)
end

interpretation
  i_set_val?: l_set_val\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf set_val set_val_locs
  apply(unfold_locales)
  by (auto simp add: set_val_def set_val_locs_def)
declare l_set_val\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_val_is_l_set_val [instances]: "l_set_val type_wf set_val set_val_locs"
  apply(simp add: l_set_val_def)
  using set_val_ok set_val_writes set_val_pointers_preserved set_val_typess_preserved
  by blast

paragraph \<open>get\_shadow\_root\<close>

locale l_set_val_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_val\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_val_get_shadow_root:
  "\<forall>w \<in> set_val_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"
  by(auto simp add: CD.set_val_locs_impl[unfolded CD.a_set_val_locs_def]
      get_shadow_root_locs_def all_args_def)
end

locale l_set_val_get_shadow_root = l_set_val + l_get_shadow_root +
  assumes set_val_get_shadow_root:
    "\<forall>w \<in> set_val_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_shadow_root_locs ptr'. r h h'))"

interpretation
  i_set_val_get_shadow_root?: l_set_val_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf
  set_val set_val_locs
  get_shadow_root get_shadow_root_locs
  apply(auto simp add: l_set_val_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def  instances)[1]
  using l_set_val\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms
  by unfold_locales
declare l_set_val_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_val_get_shadow_root_is_l_set_val_get_shadow_root [instances]:
  "l_set_val_get_shadow_root type_wf set_val set_val_locs get_shadow_root
                                  get_shadow_root_locs"
  using set_val_is_l_set_val get_shadow_root_is_l_get_shadow_root
  apply(simp add: l_set_val_get_shadow_root_def l_set_val_get_shadow_root_axioms_def)
  using set_val_get_shadow_root
  by fast

paragraph \<open>get\_tag\_type\<close>

locale l_set_val_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_val\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma set_val_get_tag_name:
  "\<forall>w \<in> set_val_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"
  by(auto simp add: CD.set_val_locs_impl[unfolded CD.a_set_val_locs_def]
      CD.get_tag_name_locs_impl[unfolded CD.a_get_tag_name_locs_def]
      all_args_def)
end

locale l_set_val_get_tag_name = l_set_val + l_get_tag_name +
  assumes set_val_get_tag_name:
    "\<forall>w \<in> set_val_locs ptr. (h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> get_tag_name_locs ptr'. r h h'))"

interpretation
  i_set_val_get_tag_name?: l_set_val_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf DocumentClass.type_wf set_val
  set_val_locs get_tag_name get_tag_name_locs
  by unfold_locales
declare l_set_val_get_tag_name\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_val_get_tag_name_is_l_set_val_get_tag_name [instances]:
  "l_set_val_get_tag_name type_wf set_val set_val_locs get_tag_name get_tag_name_locs"
  using set_val_is_l_set_val get_tag_name_is_l_get_tag_name
  apply(simp add: l_set_val_get_tag_name_def l_set_val_get_tag_name_axioms_def)
  using set_val_get_tag_name
  by fast

subsubsection \<open>create\_character\_data\<close>


locale l_create_character_data\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  CD: l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ _ _ _ _ _ type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_known_ptr known_ptr
  for known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool" +
  assumes known_ptr_impl: "known_ptr = a_known_ptr"
begin

lemma create_character_data_document_in_heap:
  assumes "h \<turnstile> ok (create_character_data document_ptr text)"
  shows "document_ptr |\<in>| document_ptr_kinds h"
  using assms CD.create_character_data_document_in_heap by simp

lemma create_character_data_known_ptr:
  assumes "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr"
  shows "known_ptr (cast new_character_data_ptr)"
  using assms CD.create_character_data_known_ptr
  by(simp add: known_ptr_impl CD.known_ptr_impl ShadowRootClass.a_known_ptr_def)
end

locale l_create_character_data = l_create_character_data_defs

interpretation
  i_create_character_data?: l_create_character_data\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs set_val
  set_val_locs create_character_data known_ptr DocumentClass.type_wf DocumentClass.known_ptr
  by(auto simp add: l_create_character_data\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_create_character_data\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_create_character_data\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

subsubsection \<open>create\_element\<close>

locale l_create_element\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  CD: l_create_element\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs set_tag_name set_tag_name_locs type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M create_element known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_known_ptr known_ptr
  for get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_tag_name :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and create_element :: "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) object_ptr \<Rightarrow> bool" +
  assumes known_ptr_impl: "known_ptr = a_known_ptr"
begin
lemmas create_element_def = CD.create_element_def

lemma create_element_document_in_heap:
  assumes "h \<turnstile> ok (create_element document_ptr tag)"
  shows "document_ptr |\<in>| document_ptr_kinds h"
  using CD.create_element_document_in_heap assms .

lemma create_element_known_ptr:
  assumes "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr"
  shows "known_ptr (cast new_element_ptr)"
proof -
  have "is_element_ptr new_element_ptr"
    using assms
    apply(auto simp add: create_element_def elim!: bind_returns_result_E)[1]
    using new_element_is_element_ptr
    by blast
  then show ?thesis
    by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
        CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs)
qed
end

interpretation
  i_create_element?: l_create_element\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs
  set_disconnected_nodes set_disconnected_nodes_locs set_tag_name set_tag_name_locs type_wf
  create_element known_ptr DocumentClass.type_wf DocumentClass.known_ptr
  by(auto simp add: l_create_element\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_create_element\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_create_element\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]


subsection \<open>A wellformed heap (Core DOM)\<close>

subsubsection \<open>wellformed\_heap\<close>


locale l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs =
  CD: l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs +
  l_get_shadow_root_defs get_shadow_root get_shadow_root_locs +
  l_get_tag_name_defs get_tag_name get_tag_name_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
definition a_host_shadow_root_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  where
    "a_host_shadow_root_rel h = (\<lambda>(x, y). (cast x, cast y)) ` {(host, shadow_root).
      host |\<in>| element_ptr_kinds h \<and> |h \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root}"

lemma a_host_shadow_root_rel_code [code]: "a_host_shadow_root_rel h = set (concat (map
  (\<lambda>host. (case |h \<turnstile> get_shadow_root host|\<^sub>r of
    Some shadow_root \<Rightarrow> [(cast host, cast shadow_root)] |
    None \<Rightarrow> []))
  (sorted_list_of_fset (element_ptr_kinds h)))
)"
  by(auto simp add: a_host_shadow_root_rel_def)

definition a_ptr_disconnected_node_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  where
    "a_ptr_disconnected_node_rel h = (\<lambda>(x, y). (cast x, cast y)) ` {(document_ptr, disconnected_node).
      document_ptr |\<in>| document_ptr_kinds h \<and> disconnected_node \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r}"

lemma a_ptr_disconnected_node_rel_code [code]: "a_ptr_disconnected_node_rel h = set (concat (map
  (\<lambda>ptr. map
    (\<lambda>node. (cast ptr, cast node))
    |h \<turnstile> get_disconnected_nodes ptr|\<^sub>r)
  (sorted_list_of_fset (document_ptr_kinds h)))
)"
  by(auto simp add: a_ptr_disconnected_node_rel_def)

definition a_all_ptrs_in_heap :: "(_) heap \<Rightarrow> bool" where
  "a_all_ptrs_in_heap h = ((\<forall>host shadow_root_ptr.
    (h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr) \<longrightarrow>
      shadow_root_ptr |\<in>| shadow_root_ptr_kinds h))"

definition a_distinct_lists :: "(_) heap \<Rightarrow> bool"
  where
    "a_distinct_lists h = distinct (concat (
      map (\<lambda>element_ptr. (case |h \<turnstile> get_shadow_root element_ptr|\<^sub>r of
 Some shadow_root_ptr \<Rightarrow> [shadow_root_ptr] | None \<Rightarrow> []))
        |h \<turnstile> element_ptr_kinds_M|\<^sub>r
    ))"

definition a_shadow_root_valid :: "(_) heap \<Rightarrow> bool" where
  "a_shadow_root_valid h = (\<forall>shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h).
     (\<exists>host \<in> fset(element_ptr_kinds h).
       |h \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types \<and>
       |h \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr))"

definition a_heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  where
    "a_heap_is_wellformed h \<longleftrightarrow> CD.a_heap_is_wellformed h \<and>
      acyclic (CD.a_parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h) \<and>
      a_all_ptrs_in_heap h \<and>
      a_distinct_lists h \<and>
      a_shadow_root_valid h"
end

global_interpretation l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs
  get_tag_name get_tag_name_locs
  defines heap_is_wellformed = a_heap_is_wellformed
    and parent_child_rel = CD.a_parent_child_rel
    and host_shadow_root_rel = a_host_shadow_root_rel
    and ptr_disconnected_node_rel = a_ptr_disconnected_node_rel
    and all_ptrs_in_heap = a_all_ptrs_in_heap
    and distinct_lists = a_distinct_lists
    and shadow_root_valid = a_shadow_root_valid
    and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = CD.a_heap_is_wellformed
    and parent_child_rel\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = CD.a_parent_child_rel
    and acyclic_heap\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = CD.a_acyclic_heap
    and all_ptrs_in_heap\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = CD.a_all_ptrs_in_heap
    and distinct_lists\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = CD.a_distinct_lists
    and owner_document_valid\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M = CD.a_owner_document_valid
  .

interpretation i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M: l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel
  by (auto simp add: l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def parent_child_rel_def instances)
declare i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_is_l_heap_is_wellformed [instances]:
  "l_heap_is_wellformed type_wf known_ptr heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel get_child_nodes
get_disconnected_nodes"
  apply(auto simp add: l_heap_is_wellformed_def)[1]
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_is_wellformed_children_in_heap apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_is_wellformed_disc_nodes_in_heap apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_is_wellformed_one_parent apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_is_wellformed_one_disc_parent apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_is_wellformed_children_disc_nodes_different apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_is_wellformed_disconnected_nodes_distinct apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_is_wellformed_children_distinct apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_is_wellformed_children_disc_nodes apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_child apply (blast, blast)
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_finite apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_acyclic apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_node_ptr apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_parent_in_heap apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_child_in_heap apply blast
  done


locale l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs
  + CD: l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr type_wf get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel
  + l_heap_is_wellformed_defs
  heap_is_wellformed parent_child_rel
  + l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_shadow_root get_shadow_root_locs get_host get_host_locs type_wf
  + l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs
  get_disconnected_document get_disconnected_document_locs type_wf
  + l_get_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root get_shadow_root_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
    and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
    and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_document :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set" +
  assumes heap_is_wellformed_impl: "heap_is_wellformed = a_heap_is_wellformed"
begin
lemmas heap_is_wellformed_def = heap_is_wellformed_impl[unfolded a_heap_is_wellformed_def,
    folded CD.heap_is_wellformed_impl CD.parent_child_rel_impl]

lemma a_distinct_lists_code [code]: "a_all_ptrs_in_heap h = ((\<forall>host \<in> fset (element_ptr_kinds h).
h \<turnstile> ok (get_shadow_root host) \<longrightarrow> (case |h \<turnstile> get_shadow_root host|\<^sub>r of
    Some shadow_root_ptr \<Rightarrow> shadow_root_ptr |\<in>| shadow_root_ptr_kinds h |
    None \<Rightarrow> True)))"
  apply(auto simp add: a_all_ptrs_in_heap_def split: option.splits)[1]
  by (meson is_OK_returns_result_I local.get_shadow_root_ptr_in_heap notin_fset select_result_I2)

lemma get_shadow_root_shadow_root_ptr_in_heap:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
  shows "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  using assms
  by(auto simp add: heap_is_wellformed_def a_all_ptrs_in_heap_def)

lemma get_host_ptr_in_heap:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host"
  shows "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  using assms get_shadow_root_shadow_root_ptr_in_heap
  by(auto simp add: get_host_def elim!: bind_returns_result_E2 dest!: filter_M_holds_for_result
      intro!: bind_pure_I split: list.splits)

lemma shadow_root_same_host:
  assumes "heap_is_wellformed h" and "type_wf h"
  assumes "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
  assumes "h \<turnstile> get_shadow_root host' \<rightarrow>\<^sub>r Some shadow_root_ptr"
  shows "host = host'"
proof (rule ccontr)
  assume " host \<noteq> host'"
  have "host |\<in>| element_ptr_kinds h"
    using assms(3)
    by (meson is_OK_returns_result_I local.get_shadow_root_ptr_in_heap)
  moreover
  have "host' |\<in>| element_ptr_kinds h"
    using assms(4)
    by (meson is_OK_returns_result_I local.get_shadow_root_ptr_in_heap)
  ultimately show False
    using assms
    apply(auto simp add: heap_is_wellformed_def a_distinct_lists_def)[1]
    apply(drule distinct_concat_map_E(1)[where x=host and y=host'])
       apply(simp)
      apply(simp)
    using \<open>host \<noteq> host'\<close> apply(simp)
    apply(auto)[1]
    done
qed

lemma shadow_root_host_dual:
  assumes "h \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host"
  shows "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
  using assms
  by(auto simp add: get_host_def dest: filter_M_holds_for_result elim!: bind_returns_result_E2
      intro!: bind_pure_I split: list.splits)

lemma disc_doc_disc_node_dual:
  assumes "h \<turnstile> get_disconnected_document disc_node \<rightarrow>\<^sub>r disc_doc"
  obtains disc_nodes where "h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes" and
    "disc_node \<in> set disc_nodes"
  using assms get_disconnected_nodes_pure
  by(auto simp add: get_disconnected_document_def bind_pure_I
      dest!: filter_M_holds_for_result
      elim!: bind_returns_result_E2
      intro!: filter_M_pure_I
      split: if_splits list.splits)

lemma get_host_valid_tag_name:
  assumes "heap_is_wellformed h" and "type_wf h"
  assumes "h \<turnstile> get_host shadow_root_ptr \<rightarrow>\<^sub>r host"
  assumes "h \<turnstile> get_tag_name host \<rightarrow>\<^sub>r tag"
  shows "tag \<in> safe_shadow_root_element_types"
proof -
  obtain host' where "host' |\<in>| element_ptr_kinds h" and
    "|h \<turnstile> get_tag_name host'|\<^sub>r \<in> safe_shadow_root_element_types"
    and "h \<turnstile> get_shadow_root host' \<rightarrow>\<^sub>r Some shadow_root_ptr"
    using assms
    apply(auto simp add: heap_is_wellformed_def a_shadow_root_valid_def)[1]
    by (smt assms(1) finite_set_in get_host_ptr_in_heap local.get_shadow_root_ok returns_result_select_result)
  then have "host = host'"
    by (meson assms(1) assms(2) assms(3) shadow_root_host_dual shadow_root_same_host)
  then show ?thesis
    by (smt \<open>\<And>thesis. (\<And>host'. \<lbrakk>host' |\<in>| element_ptr_kinds h; |h \<turnstile> get_tag_name host'|\<^sub>r \<in>
safe_shadow_root_element_types; h \<turnstile> get_shadow_root host' \<rightarrow>\<^sub>r Some shadow_root_ptr\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow>
thesis\<close> \<open>h \<turnstile> get_shadow_root host' \<rightarrow>\<^sub>r Some shadow_root_ptr\<close> assms(1) assms(2) assms(4)
        select_result_I2 shadow_root_same_host)
qed


lemma a_host_shadow_root_rel_finite: "finite (a_host_shadow_root_rel h)"
proof -
  have "a_host_shadow_root_rel h = (\<Union>host \<in> fset (element_ptr_kinds h).
(case |h \<turnstile> get_shadow_root host|\<^sub>r of Some shadow_root \<Rightarrow> {(cast host, cast shadow_root)} | None \<Rightarrow> {}))"
    by(auto simp add: a_host_shadow_root_rel_def split: option.splits)
  moreover have "finite (\<Union>host \<in> fset (element_ptr_kinds h). (case |h \<turnstile> get_shadow_root host|\<^sub>r of
Some shadow_root \<Rightarrow> {(cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host, cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root)} | None \<Rightarrow> {}))"
    by(auto split: option.splits)
  ultimately show ?thesis
    by auto
qed

lemma a_ptr_disconnected_node_rel_finite: "finite (a_ptr_disconnected_node_rel h)"
proof -
  have "a_ptr_disconnected_node_rel h = (\<Union>owner_document \<in> set |h \<turnstile> document_ptr_kinds_M|\<^sub>r.
                 (\<Union>disconnected_node \<in> set |h \<turnstile> get_disconnected_nodes owner_document|\<^sub>r.
{(cast owner_document, cast disconnected_node)}))"
    by(auto simp add: a_ptr_disconnected_node_rel_def)
  moreover have "finite (\<Union>owner_document \<in> set |h \<turnstile> document_ptr_kinds_M|\<^sub>r.
                    (\<Union>disconnected_node \<in> set |h \<turnstile> get_disconnected_nodes owner_document|\<^sub>r.
{(cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disconnected_node)}))"
    by simp
  ultimately show ?thesis
    by simp
qed


lemma heap_is_wellformed_children_in_heap:
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> child \<in> set children \<Longrightarrow>
child |\<in>| node_ptr_kinds h"
  using CD.heap_is_wellformed_children_in_heap local.heap_is_wellformed_def by blast
lemma heap_is_wellformed_disc_nodes_in_heap:
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow>
node \<in> set disc_nodes \<Longrightarrow> node |\<in>| node_ptr_kinds h"
  using CD.heap_is_wellformed_disc_nodes_in_heap local.heap_is_wellformed_def by blast
lemma heap_is_wellformed_one_parent: "heap_is_wellformed h \<Longrightarrow>
h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children' \<Longrightarrow>
set children \<inter> set children' \<noteq> {} \<Longrightarrow> ptr = ptr'"
  using CD.heap_is_wellformed_one_parent local.heap_is_wellformed_def by blast
lemma heap_is_wellformed_one_disc_parent: "heap_is_wellformed h \<Longrightarrow>
h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow>
h \<turnstile> get_disconnected_nodes document_ptr' \<rightarrow>\<^sub>r disc_nodes' \<Longrightarrow> set disc_nodes \<inter> set disc_nodes' \<noteq> {} \<Longrightarrow>
document_ptr = document_ptr'"
  using CD.heap_is_wellformed_one_disc_parent local.heap_is_wellformed_def by blast
lemma heap_is_wellformed_children_disc_nodes_different: "heap_is_wellformed h \<Longrightarrow>
h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow>
set children \<inter> set disc_nodes = {}"
  using CD.heap_is_wellformed_children_disc_nodes_different local.heap_is_wellformed_def by blast
lemma heap_is_wellformed_disconnected_nodes_distinct: "heap_is_wellformed h \<Longrightarrow>
h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow> distinct disc_nodes"
  using CD.heap_is_wellformed_disconnected_nodes_distinct local.heap_is_wellformed_def by blast
lemma heap_is_wellformed_children_distinct: "heap_is_wellformed h \<Longrightarrow>
h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> distinct children"
  using CD.heap_is_wellformed_children_distinct local.heap_is_wellformed_def by blast
lemma heap_is_wellformed_children_disc_nodes: "heap_is_wellformed h \<Longrightarrow>
node_ptr |\<in>| node_ptr_kinds h \<Longrightarrow>  \<not>(\<exists>parent \<in> fset (object_ptr_kinds h).
node_ptr \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r) \<Longrightarrow> (\<exists>document_ptr \<in> fset (document_ptr_kinds h).
node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)"
  using CD.heap_is_wellformed_children_disc_nodes local.heap_is_wellformed_def by blast
lemma parent_child_rel_finite: "heap_is_wellformed h \<Longrightarrow> finite (parent_child_rel h)"
  using CD.parent_child_rel_finite by blast
lemma parent_child_rel_acyclic: "heap_is_wellformed h \<Longrightarrow> acyclic (parent_child_rel h)"
  using CD.parent_child_rel_acyclic heap_is_wellformed_def by blast
lemma parent_child_rel_child_in_heap: "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptr parent \<Longrightarrow>
(parent, child_ptr) \<in> parent_child_rel h \<Longrightarrow> child_ptr |\<in>| object_ptr_kinds h"
  using CD.parent_child_rel_child_in_heap local.heap_is_wellformed_def by blast
end

interpretation i_heap_is_wellformed?: l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs get_tag_name
  get_tag_name_locs known_ptr type_wf heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_host get_host_locs get_disconnected_document get_disconnected_document_locs
  by(auto simp add: l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def
      l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def
      parent_child_rel_def heap_is_wellformed_def instances)
declare l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma heap_is_wellformed_is_l_heap_is_wellformed [instances]: "l_heap_is_wellformed
ShadowRootClass.type_wf ShadowRootClass.known_ptr Shadow_DOM.heap_is_wellformed
Shadow_DOM.parent_child_rel Shadow_DOM.get_child_nodes get_disconnected_nodes"
  apply(auto simp add: l_heap_is_wellformed_def instances)[1]
  using heap_is_wellformed_children_in_heap apply metis
  using heap_is_wellformed_disc_nodes_in_heap apply metis
  using heap_is_wellformed_one_parent apply blast
  using heap_is_wellformed_one_disc_parent apply blast
  using heap_is_wellformed_children_disc_nodes_different apply blast
  using heap_is_wellformed_disconnected_nodes_distinct apply metis
  using heap_is_wellformed_children_distinct apply metis
  using heap_is_wellformed_children_disc_nodes apply metis
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_child apply(blast, blast)
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_finite apply blast
  using parent_child_rel_acyclic apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_node_ptr apply blast
  using i_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_parent_in_heap apply blast
  using parent_child_rel_child_in_heap apply metis
  done


subsubsection \<open>get\_parent\<close>

interpretation i_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M: l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes
  get_child_nodes_locs known_ptrs get_parent get_parent_locs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel
  get_disconnected_nodes
  by(simp add: l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare i_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

interpretation i_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M: l_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes
  get_child_nodes_locs known_ptrs get_parent get_parent_locs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel
  get_disconnected_nodes get_disconnected_nodes_locs
  by(auto simp add: l_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare i_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_is_l_get_parent_wf [instances]: "l_get_parent_wf type_wf known_ptr
known_ptrs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel get_child_nodes get_parent"
  apply(auto simp add: l_get_parent_wf_def l_get_parent_wf_axioms_def instances)[1]
  using i_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.child_parent_dual apply fast
  using i_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_wellformed_induct apply metis
  using i_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.heap_wellformed_induct_rev apply metis
  using i_get_parent_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_parent apply fast
  done


subsubsection \<open>get\_disconnected\_nodes\<close>


subsubsection \<open>set\_disconnected\_nodes\<close>


paragraph \<open>get\_disconnected\_nodes\<close>

interpretation i_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M:
  l_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_disconnected_nodes
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel get_child_nodes
  by (simp add: l_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare i_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_is_l_set_disconnected_nodes_get_disconnected_nodes_wf [instances]:
  "l_set_disconnected_nodes_get_disconnected_nodes_wf type_wf known_ptr heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
parent_child_rel get_child_nodes get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
      set_disconnected_nodes_locs"
  apply(auto simp add: l_set_disconnected_nodes_get_disconnected_nodes_wf_def
      l_set_disconnected_nodes_get_disconnected_nodes_wf_axioms_def instances)[1]
  using i_set_disconnected_nodes_get_disconnected_nodes_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.remove_from_disconnected_nodes_removes
  apply fast
  done


paragraph \<open>get\_root\_node\<close>

interpretation i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M:
  l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf known_ptrs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs get_parent
  get_parent_locs get_ancestors get_ancestors_locs get_root_node get_root_node_locs
  by(simp add: l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_ancestors_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_is_l_get_ancestors_wf [instances]:
  "l_get_ancestors_wf heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel known_ptr known_ptrs type_wf
get_ancestors get_ancestors_locs get_child_nodes get_parent"
  apply(auto simp add: l_get_ancestors_wf_def l_get_ancestors_wf_axioms_def instances)[1]
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_never_empty apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_ok apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_reads apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_ptrs_in_heap apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_remains_not_in_ancestors apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_also_parent apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_obtains_children apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_parent_child_rel apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_parent_child_rel apply blast
  done

lemma get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_is_l_get_root_node_wf [instances]:
  "l_get_root_node_wf heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_root_node type_wf known_ptr known_ptrs
get_ancestors get_parent"
  apply(auto simp add: l_get_root_node_wf_def l_get_root_node_wf_axioms_def instances)[1]
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_root_node_ok apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_root_node_ptr_in_heap apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_root_node_root_in_heap apply blast
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_same_root_node apply(blast, blast)
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_root_node_same_no_parent apply blast
    (* using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_root_node_not_node_same apply blast *)
  using i_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_root_node_parent_same apply (blast, blast)
  done


subsubsection \<open>to\_tree\_order\<close>

interpretation i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M: l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes
  get_child_nodes_locs to_tree_order known_ptrs get_parent get_parent_locs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  parent_child_rel get_disconnected_nodes get_disconnected_nodes_locs
  apply(simp add: l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
  done
declare i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_is_l_to_tree_order_wf [instances]:
  "l_to_tree_order_wf heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel type_wf known_ptr known_ptrs
to_tree_order get_parent get_child_nodes"
  apply(auto simp add: l_to_tree_order_wf_def l_to_tree_order_wf_axioms_def instances)[1]
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_ok apply blast
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_ptrs_in_heap apply blast
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_parent_child_rel apply(blast, blast)
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_child2 apply blast
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_node_ptrs apply blast
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_child apply blast
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_ptr_in_result apply blast
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_parent apply blast
  using i_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_subset apply blast
  done

paragraph \<open>get\_root\_node\<close>

interpretation i_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M: l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr type_wf known_ptrs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M parent_child_rel get_child_nodes
  get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs get_parent get_parent_locs
  get_ancestors get_ancestors_locs get_root_node get_root_node_locs to_tree_order
  by(auto simp add: l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare i_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_is_l_to_tree_order_wf_get_root_node_wf [instances]:
  "l_to_tree_order_wf_get_root_node_wf type_wf known_ptr known_ptrs to_tree_order get_root_node heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M"
  apply(auto simp add: l_to_tree_order_wf_get_root_node_wf_def l_to_tree_order_wf_get_root_node_wf_axioms_def instances)[1]
  using i_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_get_root_node apply blast
  using i_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.to_tree_order_same_root apply blast
  done

subsubsection \<open>remove\_child\<close>

interpretation i_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M: l_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs
  set_child_nodes set_child_nodes_locs get_parent
  get_parent_locs get_owner_document get_disconnected_nodes get_disconnected_nodes_locs
  set_disconnected_nodes
  set_disconnected_nodes_locs remove_child remove_child_locs remove type_wf known_ptr known_ptrs
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  parent_child_rel
  by unfold_locales
declare i_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_is_l_remove_child_wf2 [instances]:
  "l_remove_child_wf2 type_wf known_ptr known_ptrs remove_child heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes remove"
  apply(auto simp add: l_remove_child_wf2_def l_remove_child_wf2_axioms_def instances)[1]
  using i_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.remove_child_heap_is_wellformed_preserved apply(fast, fast, fast)
  using i_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.remove_heap_is_wellformed_preserved apply(fast, fast, fast)
  using i_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.remove_child_removes_child apply fast
  using i_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.remove_child_removes_first_child apply fast
  using i_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.remove_removes_child apply fast
  using i_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.remove_for_all_empty_children apply fast
  done


subsection \<open>A wellformed heap\<close>

subsubsection \<open>get\_parent\<close>

interpretation i_get_parent_wf?: l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes
  get_child_nodes_locs known_ptrs get_parent get_parent_locs heap_is_wellformed parent_child_rel
  get_disconnected_nodes
  using instances
  by(simp add: l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def)
declare l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_parent_wf_is_l_get_parent_wf [instances]: "l_get_parent_wf ShadowRootClass.type_wf
ShadowRootClass.known_ptr ShadowRootClass.known_ptrs heap_is_wellformed parent_child_rel
Shadow_DOM.get_child_nodes Shadow_DOM.get_parent"
  apply(auto simp add: l_get_parent_wf_def l_get_parent_wf_axioms_def instances)[1]
  using child_parent_dual apply blast
  using heap_wellformed_induct apply metis
  using heap_wellformed_induct_rev apply metis
  using parent_child_rel_parent apply metis
  done



subsubsection \<open>remove\_shadow\_root\<close>

locale l_remove_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_tag_name +
  l_get_disconnected_nodes  +
  l_set_shadow_root_get_tag_name +
  l_get_child_nodes  +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_delete_shadow_root_get_disconnected_nodes +
  l_delete_shadow_root_get_child_nodes +
  l_set_shadow_root_get_disconnected_nodes +
  l_set_shadow_root_get_child_nodes +
  l_delete_shadow_root_get_tag_name +
  l_set_shadow_root_get_shadow_root +
  l_delete_shadow_root_get_shadow_root +
  l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma remove_shadow_root_preserves:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove_shadow_root ptr \<rightarrow>\<^sub>h h'"
  shows "known_ptrs h'" and "type_wf h'" "heap_is_wellformed h'"
proof -
  obtain shadow_root_ptr h2 where
    "h \<turnstile> get_shadow_root ptr \<rightarrow>\<^sub>r Some shadow_root_ptr" and
    "h \<turnstile> get_child_nodes (cast shadow_root_ptr) \<rightarrow>\<^sub>r []" and
    "h \<turnstile>  get_disconnected_nodes (cast shadow_root_ptr) \<rightarrow>\<^sub>r []" and
    h2: "h \<turnstile> set_shadow_root ptr None \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> delete_M shadow_root_ptr \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: remove_shadow_root_def elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_shadow_root_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated]
        split: option.splits if_splits)

  have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_shadow_root_writes h2]
    using \<open>type_wf h\<close> set_shadow_root_types_preserved
    by(auto simp add: reflp_def transp_def)
  then show "type_wf h'"
    using h' delete_shadow_root_type_wf_preserved local.type_wf_impl
    by blast

  have object_ptr_kinds_eq_h: "object_ptr_kinds h = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF set_shadow_root_writes h2])
    using set_shadow_root_pointers_preserved
      apply blast
    by (auto simp add: reflp_def transp_def)
  have node_ptr_kinds_eq_h: "node_ptr_kinds h = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h
    by (simp add: node_ptr_kinds_def)
  have element_ptr_kinds_eq_h: "element_ptr_kinds h = element_ptr_kinds h2"
    using node_ptr_kinds_eq_h
    by (simp add: element_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h = document_ptr_kinds h2"
    using object_ptr_kinds_eq_h
    by (simp add: document_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_h: "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h2"
    using object_ptr_kinds_eq_h
    by (simp add: document_ptr_kinds_eq_h shadow_root_ptr_kinds_def)

  have "known_ptrs h2"
    using \<open>known_ptrs h\<close> object_ptr_kinds_eq_h known_ptrs_subset
    by blast

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h' |\<subseteq>| object_ptr_kinds h2"
    using h' delete_shadow_root_pointers
    by auto
  have object_ptr_kinds_eq2_h2: "object_ptr_kinds h2 = object_ptr_kinds h' |\<union>| {|cast shadow_root_ptr|}"
    using h' delete_shadow_root_pointers
    by auto
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h2 = node_ptr_kinds h'"
    using object_ptr_kinds_eq_h2
    by(auto simp add: node_ptr_kinds_def delete_shadow_root_pointers[OF h'])
  have element_ptr_kinds_eq_h2: "element_ptr_kinds h2 = element_ptr_kinds h'"
    using node_ptr_kinds_eq_h2
    by (simp add: element_ptr_kinds_def)
  have document_ptr_kinds_eq_h2: "document_ptr_kinds h2 = document_ptr_kinds h' |\<union>| {|cast shadow_root_ptr|}"
    using object_ptr_kinds_eq_h2
    apply(auto simp add: document_ptr_kinds_def delete_shadow_root_pointers[OF h'])[1]
    using document_ptr_kinds_def by fastforce
  then
  have document_ptr_kinds_eq2_h2: "document_ptr_kinds h' |\<subseteq>| document_ptr_kinds h2"
    using h' delete_shadow_root_pointers
    by auto
  have shadow_root_ptr_kinds_eq_h2: "shadow_root_ptr_kinds h' |\<subseteq>| shadow_root_ptr_kinds h2"
    using object_ptr_kinds_eq_h2
    apply(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)[1]
    by auto
  have shadow_root_ptr_kinds_eq2_h2: "shadow_root_ptr_kinds h2 = shadow_root_ptr_kinds h' |\<union>| {|shadow_root_ptr|}"
    using object_ptr_kinds_eq2_h2
    apply (auto simp add: shadow_root_ptr_kinds_def)[1]
    using document_ptr_kinds_eq_h2 apply auto[1]
     apply (metis \<open>h \<turnstile> get_shadow_root ptr \<rightarrow>\<^sub>r Some shadow_root_ptr\<close> assms(1) document_ptr_kinds_eq_h
        fset.map_comp local.get_shadow_root_shadow_root_ptr_in_heap shadow_root_ptr_kinds_def)
    using document_ptr_kinds_eq_h2 by auto

  show "known_ptrs h'"
    using object_ptr_kinds_eq_h2 \<open>known_ptrs h2\<close> known_ptrs_subset
    by blast


  have disconnected_nodes_eq_h:
    "\<And>doc_ptr disc_nodes. h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes =
h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_shadow_root_writes h2 set_shadow_root_get_disconnected_nodes
    by(rule reads_writes_preserved)
  then have disconnected_nodes_eq2_h:
    "\<And>doc_ptr. |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have disconnected_nodes_eq_h2:
    "\<And>doc_ptr disc_nodes. doc_ptr \<noteq> cast shadow_root_ptr \<Longrightarrow> h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes =
h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads get_disconnected_nodes_delete_shadow_root[rotated, OF h']
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by(metis (no_types, lifting))+
  then have disconnected_nodes_eq2_h2:
    "\<And>doc_ptr. doc_ptr \<noteq> cast shadow_root_ptr \<Longrightarrow> |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r =
|h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have tag_name_eq_h:
    "\<And>doc_ptr disc_nodes. h \<turnstile> get_tag_name doc_ptr \<rightarrow>\<^sub>r disc_nodes =
h2 \<turnstile> get_tag_name doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads set_shadow_root_writes h2 set_shadow_root_get_tag_name
    by(rule reads_writes_preserved)
  then have tag_name_eq2_h: "\<And>doc_ptr. |h \<turnstile> get_tag_name doc_ptr|\<^sub>r = |h2 \<turnstile> get_tag_name doc_ptr|\<^sub>r"
    using select_result_eq by force

  have tag_name_eq_h2:
    "\<And>doc_ptr disc_nodes. h2 \<turnstile> get_tag_name doc_ptr \<rightarrow>\<^sub>r disc_nodes = h' \<turnstile> get_tag_name doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads get_tag_name_delete_shadow_root[OF h']
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have tag_name_eq2_h2: "\<And>doc_ptr. |h2 \<turnstile> get_tag_name doc_ptr|\<^sub>r = |h' \<turnstile> get_tag_name doc_ptr|\<^sub>r"
    using select_result_eq by force


  have children_eq_h:
    "\<And>ptr' children. h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_shadow_root_writes h2 set_shadow_root_get_child_nodes
    by(rule reads_writes_preserved)

  then have children_eq2_h: "\<And>ptr'. |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force


  have children_eq_h2:
    "\<And>ptr' children. ptr' \<noteq> cast shadow_root_ptr \<Longrightarrow> h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children =
h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads h' get_child_nodes_delete_shadow_root
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h2:
    "\<And>ptr'. ptr' \<noteq> cast shadow_root_ptr \<Longrightarrow> |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force

  have "cast shadow_root_ptr |\<notin>| object_ptr_kinds h'"
    using h' delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_not_in_heap
    by auto

  have get_shadow_root_eq_h:
    "\<And>shadow_root_opt ptr'. ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_opt =
h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_opt"
    using get_shadow_root_reads set_shadow_root_writes h2
    apply(rule reads_writes_preserved)
    using set_shadow_root_get_shadow_root_different_pointers
    by fast

  have get_shadow_root_eq_h2:
    "\<And>shadow_root_opt ptr'. h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_opt =
h' \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_opt"
    using get_shadow_root_reads get_shadow_root_delete_shadow_root[OF h']
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then
  have get_shadow_root_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_shadow_root ptr'|\<^sub>r = |h' \<turnstile> get_shadow_root ptr'|\<^sub>r"
    using select_result_eq by force



  have "acyclic (parent_child_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def)
  moreover
  have "parent_child_rel h = parent_child_rel h2"
    by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq_h children_eq2_h)
  moreover
  have "parent_child_rel h' \<subseteq> parent_child_rel h2"
    using object_ptr_kinds_eq_h2
    apply(auto simp add: CD.parent_child_rel_def)[1]
    by (metis \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> children_eq2_h2)
  ultimately
  have "CD.a_acyclic_heap h'"
    using acyclic_subset
    by (auto simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def)

  moreover
  have "CD.a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_all_ptrs_in_heap h2"
    apply(auto simp add: CD.a_all_ptrs_in_heap_def object_ptr_kinds_eq_h node_ptr_kinds_def
        children_eq_h disconnected_nodes_eq_h)[1]
     apply (metis (no_types, lifting) children_eq2_h finite_set_in subsetD)
    by (metis (no_types, lifting) disconnected_nodes_eq2_h document_ptr_kinds_eq_h
        finite_set_in in_mono)
  then have "CD.a_all_ptrs_in_heap h'"
    apply(auto simp add: CD.a_all_ptrs_in_heap_def node_ptr_kinds_eq_h2 children_eq_h2
        disconnected_nodes_eq_h2)[1]
     apply(case_tac "ptr = cast shadow_root_ptr")
    using object_ptr_kinds_eq_h2 children_eq_h2
      apply (meson \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close>
        is_OK_returns_result_I local.get_child_nodes_ptr_in_heap)
     apply(auto dest!: children_eq_h2)[1]
    using assms(1) children_eq_h local.heap_is_wellformed_children_in_heap node_ptr_kinds_eq_h
      node_ptr_kinds_eq_h2 apply blast
     apply (meson \<open>known_ptrs h'\<close> \<open>type_wf h'\<close> local.get_child_nodes_ok local.known_ptrs_known_ptr
        returns_result_select_result)
    by (metis (no_types, lifting) \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close>
        \<open>type_wf h2\<close> assms(1) disconnected_nodes_eq2_h2 disconnected_nodes_eq_h document_ptr_kinds_commutes
        document_ptr_kinds_eq2_h2 fin_mono local.get_disconnected_nodes_ok
        local.heap_is_wellformed_disc_nodes_in_heap node_ptr_kinds_eq_h node_ptr_kinds_eq_h2
        returns_result_select_result)

  moreover
  have "CD.a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_distinct_lists h2"
    by(auto simp add: CD.a_distinct_lists_def object_ptr_kinds_eq_h document_ptr_kinds_eq_h
        children_eq2_h disconnected_nodes_eq2_h)
  then have "CD.a_distinct_lists h'"
    apply(auto simp add: CD.a_distinct_lists_def document_ptr_kinds_eq_h2 disconnected_nodes_eq2_h2)[1]
      apply(auto simp add:  intro!: distinct_concat_map_I)[1]
       apply(case_tac "x = cast shadow_root_ptr")
    using \<open>cast shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> apply simp
    using children_eq_h2 concat_map_all_distinct[of "(\<lambda>ptr. |h2 \<turnstile> get_child_nodes ptr|\<^sub>r)"]
       apply (metis (no_types, lifting) children_eq2_h2 finite_fset fmember.rep_eq fset_mp
        object_ptr_kinds_eq_h2 set_sorted_list_of_set)
      apply(case_tac "x = cast shadow_root_ptr")
    using \<open>cast shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> apply simp
      apply(case_tac "y = cast shadow_root_ptr")
    using \<open>cast shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> apply simp
    using children_eq_h2 distinct_concat_map_E(1)[of "(\<lambda>ptr. |h2 \<turnstile> get_child_nodes ptr|\<^sub>r)"]
      apply (smt IntI children_eq2_h2 empty_iff finite_fset fmember.rep_eq fset_mp
        object_ptr_kinds_eq_h2 set_sorted_list_of_set)

     apply(auto simp add:  intro!: distinct_concat_map_I)[1]
      apply(case_tac "x = cast shadow_root_ptr")
    using \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> document_ptr_kinds_commutes
       apply blast
      apply (metis (mono_tags, lifting) \<open>local.CD.a_distinct_lists h2\<close> \<open>type_wf h'\<close>
        disconnected_nodes_eq_h2 is_OK_returns_result_E local.CD.distinct_lists_disconnected_nodes
        local.get_disconnected_nodes_ok select_result_I2)
     apply(case_tac "x = cast shadow_root_ptr")
    using \<open>cast shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> apply simp
     apply(case_tac "y = cast shadow_root_ptr")
    using \<open>cast shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> apply simp
  proof -
    fix x  and y and xa
    assume a1: "x |\<in>| document_ptr_kinds h'"
    assume a2: "y |\<in>| document_ptr_kinds h'"
    assume a3: "x \<noteq> y"
    assume a4: "x \<noteq> cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr"
    assume a5: "y \<noteq> cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr"
    assume a6: "xa \<in> set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
    assume a7: "xa \<in> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r"
    assume "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
(insort (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) (sorted_list_of_set (fset (document_ptr_kinds h') -
{cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr})))))"
    then show False
      using a7 a6 a5 a4 a3 a2 a1 by (metis (no_types) IntI
          distinct_concat_map_E(1)[of "(\<lambda>ptr. |h2 \<turnstile> get_disconnected_nodes ptr|\<^sub>r)"] disconnected_nodes_eq2_h2
          empty_iff finite_fset finsert.rep_eq fmember.rep_eq insert_iff set_sorted_list_of_set
          sorted_list_of_set.insert_remove)
  next
    fix x xa xb
    assume 0: "distinct (concat (map (\<lambda>ptr. |h2 \<turnstile> get_child_nodes ptr|\<^sub>r)
(sorted_list_of_set (fset (object_ptr_kinds h2)))))"
      and 1: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
(insort (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) (sorted_list_of_set (fset (document_ptr_kinds h') -
{cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr})))))"
      and 2: "(\<Union>x\<in>fset (object_ptr_kinds h2). set |h2 \<turnstile> get_child_nodes x|\<^sub>r) \<inter>
(\<Union>x\<in>set (insort (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) (sorted_list_of_set (fset (document_ptr_kinds h') -
{cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr}))). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 3: "xa |\<in>| object_ptr_kinds h'"
      and 4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
      and 5: "xb |\<in>| document_ptr_kinds h'"
      and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
    then show "False"
      apply(cases "xa = cast shadow_root_ptr")
      using \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> apply blast
      apply(cases "xb = cast shadow_root_ptr")
      using \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close> document_ptr_kinds_commutes
       apply blast
      by (metis (no_types, hide_lams) \<open>local.CD.a_distinct_lists h2\<close> \<open>type_wf h'\<close> children_eq2_h2
          disconnected_nodes_eq_h2 fset_rev_mp is_OK_returns_result_E local.CD.distinct_lists_no_parent
          local.get_disconnected_nodes_ok object_ptr_kinds_eq_h2 select_result_I2)
  qed
  moreover
  have "CD.a_owner_document_valid h"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_owner_document_valid h2"
    by(auto simp add: CD.a_owner_document_valid_def object_ptr_kinds_eq_h document_ptr_kinds_eq_h
        node_ptr_kinds_eq_h children_eq2_h disconnected_nodes_eq2_h)
  then have "CD.a_owner_document_valid h'"
    apply(auto simp add: CD.a_owner_document_valid_def  document_ptr_kinds_eq_h2 node_ptr_kinds_eq_h2
        disconnected_nodes_eq2_h2)[1]
    by (smt \<open>h \<turnstile> get_child_nodes (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
        \<open>h \<turnstile> get_disconnected_nodes (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) \<rightarrow>\<^sub>r []\<close> \<open>local.CD.a_distinct_lists h\<close>
        children_eq2_h children_eq2_h2 disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 finite_set_in finsert_iff
        funion_finsert_right local.CD.distinct_lists_no_parent object_ptr_kinds_eq2_h2 object_ptr_kinds_eq_h
        select_result_I2 sup_bot.comm_neutral)

  ultimately have "heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M h'"
    by(simp add: CD.heap_is_wellformed_def)

  moreover
  have "acyclic (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by(simp add: heap_is_wellformed_def)
  then
  have "acyclic (parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2)"
  proof -
    have "a_host_shadow_root_rel h2 \<subseteq> a_host_shadow_root_rel h"
      apply(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h)[1]
      apply(case_tac "aa = ptr")
       apply(simp)
       apply (metis (no_types, lifting) \<open>type_wf h2\<close> assms(2) h2 local.get_shadow_root_ok
          local.type_wf_impl option.distinct(1) returns_result_eq returns_result_select_result
          set_shadow_root_get_shadow_root)
      using get_shadow_root_eq_h
      by (metis (mono_tags, lifting) \<open>type_wf h2\<close> image_eqI is_OK_returns_result_E
          local.get_shadow_root_ok mem_Collect_eq prod.simps(2) select_result_I2)
    moreover have "a_ptr_disconnected_node_rel h = a_ptr_disconnected_node_rel h2"
      by (simp add: a_ptr_disconnected_node_rel_def disconnected_nodes_eq2_h document_ptr_kinds_eq_h)
    ultimately show ?thesis
      using \<open>parent_child_rel h = parent_child_rel h2\<close>
      by (smt \<open>acyclic (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union>
local.a_ptr_disconnected_node_rel h)\<close> acyclic_subset subset_refl sup_mono)
  qed
  then
  have "acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')"
  proof -
    have "a_host_shadow_root_rel h' \<subseteq> a_host_shadow_root_rel h2"
      by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h2 get_shadow_root_eq2_h2)
    moreover have "a_ptr_disconnected_node_rel h2 = a_ptr_disconnected_node_rel h'"
      apply(simp add: a_ptr_disconnected_node_rel_def disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2)
      by (metis (no_types, lifting) \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close>
          \<open>h \<turnstile> get_child_nodes (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
          \<open>h \<turnstile> get_disconnected_nodes (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr) \<rightarrow>\<^sub>r []\<close> \<open>local.CD.a_distinct_lists h\<close>
          disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 document_ptr_kinds_commutes is_OK_returns_result_I
          local.CD.distinct_lists_no_parent local.get_disconnected_nodes_ptr_in_heap select_result_I2)
    ultimately show ?thesis
      using \<open>parent_child_rel h' \<subseteq> parent_child_rel h2\<close>
        \<open>acyclic (parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2)\<close>
      using acyclic_subset order_refl sup_mono
      by (metis (no_types, hide_lams))
  qed

  moreover
  have "a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>
    by(simp add: heap_is_wellformed_def)
  then
  have "a_all_ptrs_in_heap h2"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h)[1]
    apply(case_tac "host = ptr")
     apply(simp)
     apply (metis assms(2) h2 local.type_wf_impl option.distinct(1) returns_result_eq
        set_shadow_root_get_shadow_root)
    using get_shadow_root_eq_h
    by fastforce
  then
  have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def get_shadow_root_eq_h2)[1]
    apply(auto simp add: shadow_root_ptr_kinds_eq2_h2)[1]
    by (metis (no_types, lifting) \<open>h \<turnstile> get_shadow_root ptr \<rightarrow>\<^sub>r Some shadow_root_ptr\<close> assms(1) assms(2)
        get_shadow_root_eq_h get_shadow_root_eq_h2 h2 local.shadow_root_same_host local.type_wf_impl
        option.distinct(1) select_result_I2 set_shadow_root_get_shadow_root)

  moreover
  have "a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close>
    by(simp add: heap_is_wellformed_def)
  then
  have "a_distinct_lists h2"
    apply(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h)[1]
    apply(auto intro!: distinct_concat_map_I split: option.splits)[1]
    apply(case_tac "x = ptr")
     apply(simp)
     apply (metis (no_types, hide_lams) assms(2) h2 is_OK_returns_result_I
        l_set_shadow_root_get_shadow_root.set_shadow_root_get_shadow_root
        l_set_shadow_root_get_shadow_root_axioms local.type_wf_impl option.discI returns_result_eq
        returns_result_select_result)

    apply(case_tac "y = ptr")
     apply(simp)
     apply (metis (no_types, hide_lams) assms(2) h2 is_OK_returns_result_I
        l_set_shadow_root_get_shadow_root.set_shadow_root_get_shadow_root
        l_set_shadow_root_get_shadow_root_axioms local.type_wf_impl option.discI returns_result_eq
        returns_result_select_result)
    by (metis \<open>type_wf h2\<close> assms(1) assms(2) get_shadow_root_eq_h local.get_shadow_root_ok
        local.shadow_root_same_host returns_result_select_result)

  then
  have "a_distinct_lists h'"
    by(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h2 get_shadow_root_eq2_h2)

  moreover
  have "a_shadow_root_valid h"
    using \<open>heap_is_wellformed h\<close>
    by(simp add: heap_is_wellformed_def)
  then
  have "a_shadow_root_valid h'"
    apply(auto simp add: a_shadow_root_valid_def shadow_root_ptr_kinds_eq_h element_ptr_kinds_eq_h
        tag_name_eq2_h)[1]
    apply(simp add: shadow_root_ptr_kinds_eq2_h2 element_ptr_kinds_eq_h2 tag_name_eq2_h2)
    using get_shadow_root_eq_h get_shadow_root_eq_h2
    by (smt \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr |\<notin>| object_ptr_kinds h'\<close>
        \<open>h \<turnstile> get_shadow_root ptr \<rightarrow>\<^sub>r Some shadow_root_ptr\<close> assms(2) document_ptr_kinds_commutes
        element_ptr_kinds_eq_h element_ptr_kinds_eq_h2 finite_set_in local.get_shadow_root_ok
        option.inject returns_result_select_result select_result_I2 shadow_root_ptr_kinds_commutes)

  ultimately show "heap_is_wellformed h'"
    by(simp add: heap_is_wellformed_def)
qed
end
interpretation i_remove_shadow_root_wf?: l_remove_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf get_tag_name get_tag_name_locs get_disconnected_nodes get_disconnected_nodes_locs
  set_shadow_root set_shadow_root_locs known_ptr get_child_nodes get_child_nodes_locs get_shadow_root
  get_shadow_root_locs heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host
  get_host_locs get_disconnected_document get_disconnected_document_locs remove_shadow_root
  remove_shadow_root_locs known_ptrs get_parent get_parent_locs
  by(auto simp add: l_remove_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_remove_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsubsection \<open>get\_root\_node\<close>

interpretation i_get_root_node_wf?:
  l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf known_ptrs heap_is_wellformed parent_child_rel
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs get_parent
  get_parent_locs get_ancestors get_ancestors_locs get_root_node get_root_node_locs
  by(simp add: l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms[instances]

lemma get_ancestors_wf_is_l_get_ancestors_wf [instances]:
  "l_get_ancestors_wf heap_is_wellformed parent_child_rel known_ptr known_ptrs type_wf get_ancestors
get_ancestors_locs get_child_nodes get_parent"
  apply(auto simp add: l_get_ancestors_wf_def l_get_ancestors_wf_axioms_def instances)[1]
  using get_ancestors_never_empty apply blast
  using get_ancestors_ok apply blast
  using get_ancestors_reads apply blast
  using get_ancestors_ptrs_in_heap apply blast
  using get_ancestors_remains_not_in_ancestors apply blast
  using get_ancestors_also_parent apply blast
  using get_ancestors_obtains_children apply blast
  using get_ancestors_parent_child_rel apply blast
  using get_ancestors_parent_child_rel apply blast
  done

lemma get_root_node_wf_is_l_get_root_node_wf [instances]:
  "l_get_root_node_wf heap_is_wellformed get_root_node type_wf known_ptr known_ptrs get_ancestors get_parent"
  using known_ptrs_is_l_known_ptrs
  apply(auto simp add: l_get_root_node_wf_def l_get_root_node_wf_axioms_def)[1]
  using get_root_node_ok apply blast
  using get_root_node_ptr_in_heap apply blast
  using get_root_node_root_in_heap apply blast
  using get_ancestors_same_root_node apply(blast, blast)
  using get_root_node_same_no_parent apply blast
    (* using get_root_node_not_node_same apply blast *)
  using get_root_node_parent_same apply (blast, blast)
  done

subsubsection \<open>get\_parent\_get\_host\_get\_disconnected\_document\<close>

locale l_get_parent_get_host_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs
  known_ptr type_wf heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs
  get_disconnected_document get_disconnected_document_locs +
  l_get_disconnected_document get_disconnected_document get_disconnected_document_locs +
  l_get_disconnected_nodes type_wf get_disconnected_nodes get_disconnected_nodes_locs +
  l_get_parent_wf type_wf known_ptr known_ptrs heap_is_wellformed parent_child_rel get_child_nodes
  get_child_nodes_locs get_parent get_parent_locs +
  l_get_shadow_root type_wf get_shadow_root get_shadow_root_locs +
  l_get_host get_host get_host_locs +
  l_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs
  for get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and known_ptr :: "(_) object_ptr \<Rightarrow> bool"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
    and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
    and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_document :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and known_ptrs :: "(_) heap \<Rightarrow> bool"
    and get_parent :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) object_ptr option) prog"
    and get_parent_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
begin
lemma a_host_shadow_root_rel_shadow_root:
  "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r shadow_root_option \<Longrightarrow> shadow_root_option = Some shadow_root \<longleftrightarrow>
((cast host, cast shadow_root) \<in> a_host_shadow_root_rel h)"
  apply(auto simp add: a_host_shadow_root_rel_def)[1]
  by(metis (mono_tags, lifting) case_prodI is_OK_returns_result_I
      l_get_shadow_root.get_shadow_root_ptr_in_heap local.l_get_shadow_root_axioms mem_Collect_eq
      pair_imageI select_result_I2)

lemma a_host_shadow_root_rel_host:
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host \<Longrightarrow>
((cast host, cast shadow_root) \<in> a_host_shadow_root_rel h)"
  apply(auto simp add: a_host_shadow_root_rel_def)[1]
  using shadow_root_host_dual
  by (metis (no_types, lifting) Collect_cong a_host_shadow_root_rel_shadow_root
      local.a_host_shadow_root_rel_def split_cong)

lemma a_ptr_disconnected_node_rel_disconnected_node:
  "h \<turnstile> get_disconnected_nodes document \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow> node_ptr \<in> set disc_nodes \<longleftrightarrow>
(cast document, cast node_ptr) \<in> a_ptr_disconnected_node_rel h"
  apply(auto simp add: a_ptr_disconnected_node_rel_def)[1]
  by (smt CD.get_disconnected_nodes_ptr_in_heap case_prodI is_OK_returns_result_I mem_Collect_eq
      pair_imageI select_result_I2)

lemma a_ptr_disconnected_node_rel_document:
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> get_disconnected_document node_ptr \<rightarrow>\<^sub>r document \<Longrightarrow>
(cast document, cast node_ptr) \<in> a_ptr_disconnected_node_rel h"
  apply(auto simp add: a_ptr_disconnected_node_rel_def)[1]
  using disc_doc_disc_node_dual
  by (metis (no_types, lifting) local.a_ptr_disconnected_node_rel_def
      a_ptr_disconnected_node_rel_disconnected_node)

lemma heap_wellformed_induct_si [consumes 1, case_names step]:
  assumes "heap_is_wellformed h"
  assumes "\<And>parent. (\<And>children child. h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children \<Longrightarrow> child \<in> set children \<Longrightarrow>
P (cast child))
        \<Longrightarrow> (\<And>shadow_root host. parent = cast host \<Longrightarrow> h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root \<Longrightarrow>
 P (cast shadow_root))
        \<Longrightarrow> (\<And>owner_document disc_nodes node_ptr. parent = cast owner_document \<Longrightarrow>
h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow> node_ptr \<in> set disc_nodes \<Longrightarrow> P (cast node_ptr))
      \<Longrightarrow> P parent"
  shows "P ptr"
proof -
  fix ptr
  have "finite (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using a_host_shadow_root_rel_finite a_ptr_disconnected_node_rel_finite
    using local.CD.parent_child_rel_finite local.CD.parent_child_rel_impl
    by auto
  then
  have "wf ((parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<inverse>)"
    using assms(1)
    apply(simp add: heap_is_wellformed_def)
    by (simp add: finite_acyclic_wf_converse local.CD.parent_child_rel_impl)
  then show "?thesis"
  proof (induct rule: wf_induct_rule)
    case (less parent)
    then show ?case
      apply(auto)[1]
      using assms a_ptr_disconnected_node_rel_disconnected_node a_host_shadow_root_rel_shadow_root
        local.CD.parent_child_rel_child
      by blast
  qed
qed

lemma heap_wellformed_induct_rev_si [consumes 1, case_names step]:
  assumes "heap_is_wellformed h"
  assumes "\<And>child. (\<And>parent child_node. child = cast child_node \<Longrightarrow>
h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent \<Longrightarrow> P parent)
      \<Longrightarrow> (\<And>host shadow_root. child = cast shadow_root \<Longrightarrow> h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host \<Longrightarrow>
P (cast host))
      \<Longrightarrow> (\<And>disc_doc disc_node. child = cast disc_node \<Longrightarrow>
h \<turnstile> get_disconnected_document disc_node \<rightarrow>\<^sub>r disc_doc\<Longrightarrow> P (cast disc_doc))
      \<Longrightarrow> P child"
  shows "P ptr"
proof -
  fix ptr
  have "finite (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using a_host_shadow_root_rel_finite a_ptr_disconnected_node_rel_finite
    using local.CD.parent_child_rel_finite local.CD.parent_child_rel_impl
    by auto
  then
  have "wf (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using assms(1)
    apply(simp add: heap_is_wellformed_def)
    by (simp add: finite_acyclic_wf)
  then show "?thesis"
  proof (induct rule: wf_induct_rule)
    case (less parent)
    then show ?case
      apply(auto)[1]
      using parent_child_rel_parent a_host_shadow_root_rel_host a_ptr_disconnected_node_rel_document
      using assms(1) assms(2) by auto
  qed
qed
end

interpretation i_get_parent_get_host_get_disconnected_document_wf?:
  l_get_parent_get_host_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs known_ptr type_wf heap_is_wellformed
  parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs known_ptrs get_parent get_parent_locs
  by(auto simp add: l_get_parent_get_host_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_parent_get_host_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


locale l_get_parent_get_host_wf =
  l_heap_is_wellformed_defs +
  l_get_parent_defs +
  l_get_shadow_root_defs +
  l_get_host_defs +
  l_get_child_nodes_defs +
  l_get_disconnected_document_defs +
  l_get_disconnected_nodes_defs +
  assumes heap_wellformed_induct_si [consumes 1, case_names step]:
    "heap_is_wellformed h
    \<Longrightarrow> (\<And>parent. (\<And>children child. h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children \<Longrightarrow>
child \<in> set children \<Longrightarrow> P (cast child))
        \<Longrightarrow> (\<And>shadow_root host. parent = cast host \<Longrightarrow>
h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root \<Longrightarrow>  P (cast shadow_root))
        \<Longrightarrow> (\<And>owner_document disc_nodes node_ptr. parent = cast owner_document \<Longrightarrow>
h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes \<Longrightarrow> node_ptr \<in> set disc_nodes \<Longrightarrow>
P (cast node_ptr))
      \<Longrightarrow> P parent)
    \<Longrightarrow> P ptr"
  assumes heap_wellformed_induct_rev_si [consumes 1, case_names step]:
    "heap_is_wellformed h
    \<Longrightarrow> (\<And>child. (\<And>parent child_node. child = cast child_node \<Longrightarrow>
h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent \<Longrightarrow> P parent)
      \<Longrightarrow> (\<And>host shadow_root. child = cast shadow_root \<Longrightarrow>
h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host \<Longrightarrow> P (cast host))
      \<Longrightarrow> (\<And>disc_doc disc_node. child = cast disc_node \<Longrightarrow>
h \<turnstile> get_disconnected_document disc_node \<rightarrow>\<^sub>r disc_doc \<Longrightarrow> P (cast disc_doc))
      \<Longrightarrow> P child)
    \<Longrightarrow> P ptr"

lemma l_get_parent_get_host_wf_is_get_parent_get_host_wf [instances]:
  "l_get_parent_get_host_wf heap_is_wellformed get_parent get_shadow_root get_host get_child_nodes
get_disconnected_document get_disconnected_nodes"
  using heap_wellformed_induct_si heap_wellformed_induct_rev_si
  using l_get_parent_get_host_wf_def by blast


subsubsection \<open>get\_host\<close>

locale l_get_host_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M  get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs
  known_ptr type_wf heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs +
  l_type_wf type_wf +
  l_get_host\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_shadow_root get_shadow_root_locs get_host get_host_locs type_wf +
  l_get_shadow_root type_wf get_shadow_root get_shadow_root_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
    and known_ptrs :: "(_) heap \<Rightarrow> bool"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
    and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
    and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
begin

lemma get_host_ok [simp]:
  assumes "heap_is_wellformed h"
  assumes "type_wf h"
  assumes "known_ptrs h"
  assumes "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  shows "h \<turnstile> ok (get_host shadow_root_ptr)"
proof -
  obtain host where host: "host |\<in>| element_ptr_kinds h"
    and "|h \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types"
    and shadow_root: "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root_ptr"
    using assms(1) assms(4) get_shadow_root_ok assms(2)
    apply(auto simp add: heap_is_wellformed_def a_shadow_root_valid_def)[1]
    by (smt finite_set_in returns_result_select_result)


  obtain host_candidates where
    host_candidates: "h \<turnstile> filter_M (\<lambda>element_ptr. Heap_Error_Monad.bind (get_shadow_root element_ptr)
(\<lambda>shadow_root_opt. return (shadow_root_opt = Some shadow_root_ptr)))
                (sorted_list_of_set (fset (element_ptr_kinds h)))
          \<rightarrow>\<^sub>r host_candidates"
    apply(drule is_OK_returns_result_E[rotated])
    using get_shadow_root_ok assms(2)
    by(auto intro!: filter_M_is_OK_I bind_pure_I bind_is_OK_I2)
  then have "host_candidates = [host]"
    apply(rule filter_M_ex1)
    using host apply(auto)[1]
       apply (smt assms(1) assms(2) bind_pure_returns_result_I2 bind_returns_result_E finite_set_in host
        local.get_shadow_root_ok local.get_shadow_root_pure local.shadow_root_same_host return_returns_result
        returns_result_eq shadow_root sorted_list_of_fset.rep_eq sorted_list_of_fset_simps(1))
      apply (simp add: bind_pure_I)
     apply(auto intro!: bind_pure_returns_result_I)[1]
    apply (smt assms(2) bind_pure_returns_result_I2 host local.get_shadow_root_ok
        local.get_shadow_root_pure return_returns_result returns_result_eq shadow_root)
    done

  then
  show ?thesis
    using host_candidates host assms(1) get_shadow_root_ok
    apply(auto simp add: get_host_def known_ptrs_known_ptr
        intro!: bind_is_OK_pure_I filter_M_pure_I filter_M_is_OK_I bind_pure_I split: list.splits)[1]
    using assms(2) apply blast
     apply (meson list.distinct(1) returns_result_eq)
    by (meson list.distinct(1) list.inject returns_result_eq)
qed
end

interpretation i_get_host_wf?: l_get_host_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_disconnected_document get_disconnected_document_locs known_ptr known_ptrs type_wf get_host
  get_host_locs get_shadow_root get_shadow_root_locs get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_tag_name get_tag_name_locs heap_is_wellformed
  parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  by(auto simp add: l_get_host_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_host_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

locale l_get_host_wf = l_heap_is_wellformed_defs + l_known_ptrs + l_type_wf + l_get_host_defs +
  assumes get_host_ok: "heap_is_wellformed h \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h \<Longrightarrow>
shadow_root_ptr |\<in>| shadow_root_ptr_kinds h \<Longrightarrow> h \<turnstile> ok (get_host shadow_root_ptr)"

lemma get_host_wf_is_l_get_host_wf [instances]: "l_get_host_wf heap_is_wellformed known_ptr
known_ptrs type_wf get_host"
  by(auto simp add: l_get_host_wf_def l_get_host_wf_axioms_def instances)


subsubsection \<open>get\_root\_node\_si\<close>

locale l_get_root_node_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_root_node_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_wf +
  l_get_parent_get_host_wf +
  l_get_host_wf
begin
lemma get_root_node_ptr_in_heap:
  assumes "h \<turnstile> ok (get_root_node_si ptr)"
  shows "ptr |\<in>| object_ptr_kinds h"
  using assms
  unfolding get_root_node_si_def
  using get_ancestors_si_ptr_in_heap
  by auto


lemma get_ancestors_si_ok:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
    and "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (get_ancestors_si ptr)"
proof (insert assms(1) assms(4), induct rule: heap_wellformed_induct_rev_si)
  case (step child)
  then show ?case
    using assms(2) assms(3)
    apply(auto simp add: get_ancestors_si_def[of child] assms(1) get_parent_parent_in_heap
        intro!: bind_is_OK_pure_I split: option.splits)[1]
    using local.get_parent_ok apply blast
    using get_host_ok assms(1) apply blast
    by (meson assms(1) is_OK_returns_result_I local.get_shadow_root_ptr_in_heap
        local.shadow_root_host_dual)
qed

lemma get_ancestors_si_remains_not_in_ancestors:
  assumes "heap_is_wellformed h"
    and "heap_is_wellformed h'"
    and "h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r ancestors"
    and "h' \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r ancestors'"
    and "\<And>p children children'. h \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children
        \<Longrightarrow> h' \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children' \<Longrightarrow> set children' \<subseteq> set children"
    and "\<And>p shadow_root_option shadow_root_option'. h \<turnstile> get_shadow_root p \<rightarrow>\<^sub>r shadow_root_option \<Longrightarrow>
h' \<turnstile> get_shadow_root p \<rightarrow>\<^sub>r shadow_root_option' \<Longrightarrow> (if shadow_root_option = None
then shadow_root_option' = None else shadow_root_option' = None \<or> shadow_root_option' = shadow_root_option)"
    and "node \<notin> set ancestors"
    and object_ptr_kinds_eq3: "object_ptr_kinds h = object_ptr_kinds h'"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
    and type_wf': "type_wf h'"
  shows "node \<notin> set ancestors'"
proof -
  have object_ptr_kinds_M_eq:
    "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    using object_ptr_kinds_eq3
    by(simp add: object_ptr_kinds_M_defs)
  then have object_ptr_kinds_eq: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by(simp)

  show ?thesis
  proof (insert assms(1) assms(3) assms(4) assms(7), induct ptr arbitrary: ancestors ancestors'
      rule: heap_wellformed_induct_rev_si)
    case (step child)

    obtain ancestors_remains where ancestors_remains:
      "ancestors = child # ancestors_remains"
      using \<open>h \<turnstile> get_ancestors_si child \<rightarrow>\<^sub>r ancestors\<close> get_ancestors_si_never_empty
      by(auto simp add: get_ancestors_si_def[of child] elim!: bind_returns_result_E2 split: option.splits)
    obtain ancestors_remains' where ancestors_remains':
      "ancestors' = child # ancestors_remains'"
      using \<open>h' \<turnstile> get_ancestors_si child \<rightarrow>\<^sub>r ancestors'\<close> get_ancestors_si_never_empty
      by(auto simp add: get_ancestors_si_def[of child] elim!: bind_returns_result_E2 split: option.splits)
    have "child |\<in>| object_ptr_kinds h"
      using local.get_ancestors_si_ptr_in_heap object_ptr_kinds_eq3 step.prems(2) by fastforce

    have "node \<noteq> child"
      using ancestors_remains step.prems(3) by auto

    have 1: "\<And>p parent. h' \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent \<Longrightarrow> h \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent"
    proof -
      fix p parent
      assume "h' \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent"
      then obtain children' where
        children': "h' \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children'" and
        p_in_children': "p \<in> set children'"
        using get_parent_child_dual by blast
      obtain children where children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
        using get_child_nodes_ok assms(1) get_child_nodes_ptr_in_heap object_ptr_kinds_eq children'
          known_ptrs
        using  type_wf type_wf'
        by (metis \<open>h' \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent\<close> get_parent_parent_in_heap is_OK_returns_result_E
            local.known_ptrs_known_ptr object_ptr_kinds_eq3)
      have "p \<in> set children"
        using assms(5) children children' p_in_children'
        by blast
      then show "h \<turnstile> get_parent p \<rightarrow>\<^sub>r Some parent"
        using child_parent_dual assms(1) children known_ptrs  type_wf  by blast
    qed

    have 2: "\<And>p host. h' \<turnstile> get_host p \<rightarrow>\<^sub>r host \<Longrightarrow> h \<turnstile> get_host p \<rightarrow>\<^sub>r host"
    proof -
      fix p host
      assume "h' \<turnstile> get_host p \<rightarrow>\<^sub>r host"
      then have "h' \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some p"
        using local.shadow_root_host_dual by blast
      then have "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some p"
        by (metis assms(6) element_ptr_kinds_commutes is_OK_returns_result_I local.get_shadow_root_ok
            local.get_shadow_root_ptr_in_heap node_ptr_kinds_commutes object_ptr_kinds_eq3 option.distinct(1)
            returns_result_select_result type_wf)
      then show "h \<turnstile> get_host p \<rightarrow>\<^sub>r host"
        by (metis assms(1) is_OK_returns_result_E known_ptrs local.get_host_ok
            local.get_shadow_root_shadow_root_ptr_in_heap local.shadow_root_host_dual local.shadow_root_same_host
            type_wf)

    qed


    show ?case
    proof (cases "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
      case None
      then show ?thesis
        using step(4) step(5) \<open>node \<noteq> child\<close>
        apply(auto simp add: get_ancestors_si_def[of child] elim!: bind_returns_result_E2
            split: option.splits)[1]
        by (metis "2" assms(1) shadow_root_same_host list.set_intros(2) shadow_root_host_dual
            step.hyps(2) step.prems(3) type_wf)
    next
      case (Some node_child)
      then
      show ?thesis
        using step(4) step(5) \<open>node \<noteq> child\<close>
        apply(auto simp add: get_ancestors_si_def[of child] elim!: bind_returns_result_E2
            split: option.splits)[1]
         apply (meson "1" option.distinct(1) returns_result_eq)
        by (metis "1" list.set_intros(2) option.inject returns_result_eq step.hyps(1) step.prems(3))
    qed
  qed
qed


lemma get_ancestors_si_ptrs_in_heap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r ancestors"
  assumes "ptr' \<in> set ancestors"
  shows "ptr' |\<in>| object_ptr_kinds h"
proof (insert assms(4) assms(5), induct ancestors arbitrary: ptr)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons a ancestors)
  then obtain x where x: "h \<turnstile> get_ancestors_si x \<rightarrow>\<^sub>r a # ancestors"
    by(auto simp add: get_ancestors_si_def[of a] elim!: bind_returns_result_E2 split: option.splits)
  then have "x = a"
    by(auto simp add: get_ancestors_si_def[of x] elim!: bind_returns_result_E2 split: option.splits)
  then show ?case
  proof (cases "ptr' = a")
    case True
    then show ?thesis
      using Cons.hyps Cons.prems(2) get_ancestors_si_ptr_in_heap x
      using \<open>x = a\<close> by blast
  next
    case False
    obtain ptr'' where ptr'': "h \<turnstile> get_ancestors_si ptr'' \<rightarrow>\<^sub>r ancestors"
      using \<open> h \<turnstile> get_ancestors_si x \<rightarrow>\<^sub>r a # ancestors\<close> Cons.prems(2) False
      apply(auto simp add: get_ancestors_si_def elim!: bind_returns_result_E2)[1]
       apply(auto elim!: bind_returns_result_E2 split: option.splits intro!: bind_pure_I)[1]
      apply(auto elim!: bind_returns_result_E2 split: option.splits intro!: bind_pure_I)[1]
       apply (metis local.get_ancestors_si_def)
      by (simp add: local.get_ancestors_si_def)
    then show ?thesis
      using Cons.hyps Cons.prems(2) False by auto
  qed
qed

lemma get_ancestors_si_reads:
  assumes "heap_is_wellformed h"
  shows "reads get_ancestors_si_locs (get_ancestors_si node_ptr) h h'"
proof (insert assms(1), induct rule: heap_wellformed_induct_rev_si)
  case (step child)
  then show ?case
    using [[simproc del: Product_Type.unit_eq]] get_parent_reads[unfolded reads_def]
      get_host_reads[unfolded reads_def]
    apply(simp (no_asm) add: get_ancestors_si_def)
    by(auto simp add: get_ancestors_si_locs_def get_parent_reads_pointers
        intro!: reads_bind_pure reads_subset[OF check_in_heap_reads] reads_subset[OF return_reads]
        reads_subset[OF get_parent_reads] reads_subset[OF get_child_nodes_reads]
        reads_subset[OF get_host_reads]
        split: option.splits)
qed


lemma get_ancestors_si_subset:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r ancestors"
    and "ancestor \<in> set ancestors"
    and "h \<turnstile> get_ancestors_si ancestor \<rightarrow>\<^sub>r ancestor_ancestors"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
  shows "set ancestor_ancestors \<subseteq> set ancestors"
proof (insert assms(1) assms(2) assms(3), induct ptr arbitrary: ancestors
    rule: heap_wellformed_induct_rev_si)
  case (step child)
  have "child |\<in>| object_ptr_kinds h"
    using get_ancestors_si_ptr_in_heap step(4) by auto
      (*  then have "h \<turnstile> check_in_heap child \<rightarrow>\<^sub>r ()"
    using returns_result_select_result by force *)


  obtain tl_ancestors where tl_ancestors: "ancestors = child # tl_ancestors"
    using step(4)
    by(auto simp add: get_ancestors_si_def[of child] intro!: bind_pure_I
        elim!: bind_returns_result_E2 split: option.splits)
  show ?case
  proof (induct "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
    case None
    show ?case
    proof (induct "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
      case None
      then show ?case
        using step(4) \<open>None = cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child\<close>
        apply(auto simp add: get_ancestors_si_def[of child] elim!: bind_returns_result_E2)[1]
        by (metis (no_types, lifting) assms(4) empty_iff empty_set select_result_I2 set_ConsD
            step.prems(1) step.prems(2))
    next
      case (Some shadow_root_child)
      then
      have "cast shadow_root_child |\<in>| document_ptr_kinds h"
        using  \<open>child |\<in>| object_ptr_kinds h\<close>
        apply(auto simp add: document_ptr_kinds_def split: option.splits)[1]
        by (metis (mono_tags, lifting) document_ptr_casts_commute3 document_ptr_kinds_commutes
            document_ptr_kinds_def fset.map_comp shadow_root_ptr_casts_commute)
      then
      have "shadow_root_child |\<in>| shadow_root_ptr_kinds h"
        using shadow_root_ptr_kinds_commutes by blast
      obtain host where host: "h \<turnstile> get_host shadow_root_child \<rightarrow>\<^sub>r host"
        using get_host_ok assms
        by (meson \<open>shadow_root_child |\<in>| shadow_root_ptr_kinds h\<close> is_OK_returns_result_E)
      then
      have "h \<turnstile> get_ancestors_si (cast host) \<rightarrow>\<^sub>r tl_ancestors"
        using Some step(4) tl_ancestors None
        by(auto simp add: get_ancestors_si_def[of child] intro!: bind_pure_returns_result_I
            elim!: bind_returns_result_E2 split: option.splits dest: returns_result_eq)
      then
      show ?case
        using step(2) Some host step(5) tl_ancestors
        using assms(4) dual_order.trans eq_iff returns_result_eq set_ConsD set_subset_Cons
          shadow_root_ptr_casts_commute document_ptr_casts_commute step.prems(1)
        by (smt case_optionE local.shadow_root_host_dual option.case_distrib option.distinct(1))
    qed
  next
    case (Some child_node)
    note s1 = Some
    obtain parent_opt where parent_opt: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r parent_opt"
      using \<open>child |\<in>| object_ptr_kinds h\<close> assms(1) Some[symmetric] get_parent_ok[OF type_wf known_ptrs]
      by (metis (no_types, lifting) is_OK_returns_result_E known_ptrs get_parent_ok
          l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms node_ptr_casts_commute node_ptr_kinds_commutes)
    then show ?case
    proof (induct parent_opt)
      case None
      then have "ancestors = [child]"
        using step(4) s1
        apply(simp add: get_ancestors_si_def)
        by(auto elim!: bind_returns_result_E2 split: option.splits dest: returns_result_eq)
      show ?case
        using step(4) step(5)
        apply(auto simp add: \<open>ancestors = [child]\<close>)[1]
        using assms(4) returns_result_eq by fastforce
    next
      case (Some parent)
      then
      have "h \<turnstile> get_ancestors_si parent \<rightarrow>\<^sub>r tl_ancestors"
        using s1 tl_ancestors step(4)
        by(auto simp add: get_ancestors_si_def[of child] elim!: bind_returns_result_E2
            split: option.splits dest: returns_result_eq)
      show ?case
        by (metis (no_types, lifting) Some.prems \<open>h \<turnstile> get_ancestors_si parent \<rightarrow>\<^sub>r tl_ancestors\<close>
            assms(4) eq_iff node_ptr_casts_commute order_trans s1 select_result_I2 set_ConsD set_subset_Cons
            step.hyps(1) step.prems(1) step.prems(2) tl_ancestors)
    qed
  qed
qed

lemma get_ancestors_si_also_parent:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors_si some_ptr \<rightarrow>\<^sub>r ancestors"
    and "cast child \<in> set ancestors"
    and "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
  shows "parent \<in> set ancestors"
proof -
  obtain child_ancestors where child_ancestors: "h \<turnstile> get_ancestors_si (cast child) \<rightarrow>\<^sub>r child_ancestors"
    by (meson assms(1) assms(4) get_ancestors_si_ok is_OK_returns_result_I known_ptrs
        local.get_parent_ptr_in_heap node_ptr_kinds_commutes returns_result_select_result
        type_wf)
  then have "parent \<in> set child_ancestors"
    apply(simp add: get_ancestors_si_def)
    by(auto elim!: bind_returns_result_E2 split: option.splits dest!: returns_result_eq[OF assms(4)]
        get_ancestors_si_ptr)
  then show ?thesis
    using assms child_ancestors get_ancestors_si_subset by blast
qed

lemma get_ancestors_si_also_host:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors_si some_ptr \<rightarrow>\<^sub>r ancestors"
    and "cast shadow_root \<in> set ancestors"
    and "h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
  shows "cast host \<in> set ancestors"
proof -
  obtain child_ancestors where child_ancestors: "h \<turnstile> get_ancestors_si (cast shadow_root) \<rightarrow>\<^sub>r child_ancestors"
    by (meson assms(1) assms(2) assms(3) get_ancestors_si_ok get_ancestors_si_ptrs_in_heap
        is_OK_returns_result_E known_ptrs type_wf)
  then have "cast host \<in> set child_ancestors"
    apply(simp add: get_ancestors_si_def)
    by(auto elim!: bind_returns_result_E2 split: option.splits dest!: returns_result_eq[OF assms(4)]
        get_ancestors_si_ptr)
  then show ?thesis
    using assms child_ancestors get_ancestors_si_subset by blast
qed


lemma get_ancestors_si_obtains_children_or_shadow_root:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
    and "h \<turnstile> get_ancestors_si ptr \<rightarrow>\<^sub>r ancestors"
    and "ancestor \<noteq> ptr"
    and "ancestor \<in> set ancestors"
  shows "((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast ancestor_child \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)
      \<or> ((\<forall>ancestor_element shadow_root. ancestor = cast ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow> cast shadow_root \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow>
thesis)"
proof (insert assms(4) assms(5) assms(6), induct ptr arbitrary: ancestors
    rule: heap_wellformed_induct_rev_si[OF assms(1)])
  case (1 child)
  then show ?case
  proof (cases "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
    case None
    then obtain shadow_root where shadow_root: "child = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root"
      using 1(4) 1(5) 1(6)
      by(auto simp add: get_ancestors_si_def[of child] elim!: bind_returns_result_E2
          split: option.splits)
    then obtain host where host: "h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host"
      by (metis "1.prems"(1) assms(1) assms(2) assms(3) document_ptr_kinds_commutes
          get_ancestors_si_ptrs_in_heap is_OK_returns_result_E local.get_ancestors_si_ptr local.get_host_ok
          shadow_root_ptr_kinds_commutes)
    then obtain host_ancestors where host_ancestors: "h \<turnstile> get_ancestors_si (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) \<rightarrow>\<^sub>r host_ancestors"
      by (metis "1.prems"(1) assms(1) assms(2) assms(3) get_ancestors_si_also_host get_ancestors_si_ok
          get_ancestors_si_ptrs_in_heap is_OK_returns_result_E local.get_ancestors_si_ptr shadow_root)
    then have "ancestors = cast shadow_root # host_ancestors"
      using 1(4) 1(5) 1(3) None shadow_root host
      by(auto simp add: get_ancestors_si_def[of child, simplified shadow_root]
          elim!: bind_returns_result_E2 dest!: returns_result_eq[OF host] split: option.splits)
    then show ?thesis
    proof (cases "ancestor = cast host")
      case True
      then show ?thesis
        using "1.prems"(1) host local.get_ancestors_si_ptr local.shadow_root_host_dual shadow_root
        by blast
    next
      case False
      have "ancestor \<in> set ancestors"
        using host host_ancestors 1(3) get_ancestors_si_also_host assms(1) assms(2) assms(3)
        using "1.prems"(3) by blast
      then have "((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_child \<in> set host_ancestors \<longrightarrow> thesis) \<longrightarrow>
thesis) \<or>
          ((\<forall>ancestor_element shadow_root. ancestor = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow>
cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root \<in> set host_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)"
        using "1.hyps"(2) "1.prems"(2) False \<open>ancestors = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root # host_ancestors\<close>
          host host_ancestors shadow_root
        by auto
      then show ?thesis
        using \<open>ancestors = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root # host_ancestors\<close> by auto
    qed
  next
    case (Some child_node)
    then obtain parent where parent: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent"
      using 1(4) 1(5) 1(6)
      by(auto simp add: get_ancestors_si_def[of child] elim!: bind_returns_result_E2
          split: option.splits)
    then obtain parent_ancestors where parent_ancestors: "h \<turnstile> get_ancestors_si parent \<rightarrow>\<^sub>r parent_ancestors"
      by (meson assms(1) assms(2) assms(3) get_ancestors_si_ok is_OK_returns_result_E
          local.get_parent_parent_in_heap)
    then have "ancestors = cast child_node # parent_ancestors"
      using 1(4) 1(5) 1(3) Some
      by(auto simp add: get_ancestors_si_def[of child, simplified Some]
          elim!: bind_returns_result_E2 dest!: returns_result_eq[OF parent] split: option.splits)
    then show ?thesis
    proof (cases "ancestor = parent")
      case True
      then show ?thesis
        by (metis (no_types, lifting) "1.prems"(1) Some local.get_ancestors_si_ptr
            local.get_parent_child_dual node_ptr_casts_commute parent)
    next
      case False
      have "ancestor \<in> set ancestors"
        by (simp add: "1.prems"(3))
      then have "((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_child \<in> set parent_ancestors \<longrightarrow> thesis) \<longrightarrow>
thesis) \<or>
         ((\<forall>ancestor_element shadow_root. ancestor = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow>
cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root \<in> set parent_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)"
        using "1.hyps"(1) "1.prems"(2) False Some \<open>ancestors = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node # parent_ancestors\<close>
          parent parent_ancestors
        by auto
      then show ?thesis
        using \<open>ancestors = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node # parent_ancestors\<close> by auto
    qed
  qed
qed

lemma a_host_shadow_root_rel_shadow_root:
  "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root \<Longrightarrow> (cast host, cast shadow_root) \<in> a_host_shadow_root_rel h"
  by(auto simp add: is_OK_returns_result_I get_shadow_root_ptr_in_heap a_host_shadow_root_rel_def)

lemma get_ancestors_si_parent_child_a_host_shadow_root_rel:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
  assumes "h \<turnstile> get_ancestors_si child \<rightarrow>\<^sub>r ancestors"
  shows "(ptr, child) \<in> (parent_child_rel h \<union> a_host_shadow_root_rel h)\<^sup>* \<longleftrightarrow> ptr \<in> set ancestors"
proof
  assume "(ptr, child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h)\<^sup>* "
  then show "ptr \<in> set ancestors"
  proof (induct ptr rule: heap_wellformed_induct_si[OF assms(1)])
    case (1 ptr)
    then show ?case
    proof (cases "ptr = child")
      case True
      then show ?thesis
        using assms(4) local.get_ancestors_si_ptr by blast
    next
      case False
      obtain ptr_child where
        ptr_child: "(ptr, ptr_child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h) \<and>
(ptr_child, child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h)\<^sup>*"
        using converse_rtranclE[OF 1(4)] \<open>ptr \<noteq> child\<close>
        by metis
      then show ?thesis
      proof(cases "(ptr, ptr_child) \<in> parent_child_rel h")
        case True

        then obtain ptr_child_node
          where ptr_child_ptr_child_node: "ptr_child = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node"
          using ptr_child node_ptr_casts_commute3 CD.parent_child_rel_node_ptr
          by (metis)
        then obtain children where
          children: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children" and
          ptr_child_node: "ptr_child_node \<in> set children"
        proof -
          assume a1: "\<And>children. \<lbrakk>h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children; ptr_child_node \<in> set children\<rbrakk>
                   \<Longrightarrow> thesis"

          have "ptr |\<in>| object_ptr_kinds h"
            using CD.parent_child_rel_parent_in_heap True by blast
          moreover have "ptr_child_node \<in> set |h \<turnstile> get_child_nodes ptr|\<^sub>r"
            by (metis True assms(2) assms(3) calculation local.CD.parent_child_rel_child
                local.get_child_nodes_ok local.known_ptrs_known_ptr ptr_child_ptr_child_node
                returns_result_select_result)
          ultimately show ?thesis
            using a1 get_child_nodes_ok \<open>type_wf h\<close> \<open>known_ptrs h\<close>
            by (meson local.known_ptrs_known_ptr returns_result_select_result)
        qed
        moreover have "(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node, child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h)\<^sup>*"
          using ptr_child True ptr_child_ptr_child_node by auto
        ultimately have "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node \<in> set ancestors"
          using 1 by auto
        moreover have "h \<turnstile> get_parent ptr_child_node \<rightarrow>\<^sub>r Some ptr"
          using assms(1) children ptr_child_node child_parent_dual
          using \<open>known_ptrs h\<close> \<open>type_wf h\<close> by blast
        ultimately show ?thesis
          using get_ancestors_si_also_parent assms \<open>type_wf h\<close> by blast
      next
        case False
        then
        obtain host where host: "ptr = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host"
          using ptr_child
          by(auto simp add: a_host_shadow_root_rel_def)
        then obtain shadow_root where shadow_root: "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root"
          and ptr_child_shadow_root: "ptr_child = cast shadow_root"
          using ptr_child False
          apply(auto simp add: a_host_shadow_root_rel_def)[1]
          by (metis (no_types, lifting) assms(3) local.get_shadow_root_ok select_result_I)

        moreover have "(cast shadow_root, child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h)\<^sup>*"
          using ptr_child ptr_child_shadow_root by blast
        ultimately have "cast shadow_root \<in> set ancestors"
          using "1.hyps"(2) host by blast
        moreover have "h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host"
          by (metis assms(1) assms(2) assms(3) is_OK_returns_result_E local.get_host_ok
              local.get_shadow_root_shadow_root_ptr_in_heap local.shadow_root_host_dual local.shadow_root_same_host
              shadow_root)
        ultimately show ?thesis
          using get_ancestors_si_also_host assms(1) assms(2) assms(3) assms(4) host
          by blast
      qed
    qed
  qed
next
  assume "ptr \<in> set ancestors"
  then show "(ptr, child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h)\<^sup>*"
  proof (induct ptr rule: heap_wellformed_induct_si[OF assms(1)])
    case (1 ptr)
    then show ?case
    proof (cases "ptr = child")
      case True
      then show ?thesis
        by simp
    next
      case False
      have "\<And>thesis. ((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast ancestor_child \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)
      \<or> ((\<forall>ancestor_element shadow_root. ptr = cast ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow> cast shadow_root \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow>
thesis)"
        using "1.prems" False assms(1) assms(2) assms(3) assms(4) get_ancestors_si_obtains_children_or_shadow_root
        by blast
      then show ?thesis
      proof (cases "\<forall>thesis. ((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast ancestor_child \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)")
        case True
        then obtain children ancestor_child
          where "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
            and "ancestor_child \<in> set children"
            and "cast ancestor_child \<in> set ancestors"
          by blast
        then show ?thesis
          by (meson "1.hyps"(1) in_rtrancl_UnI local.CD.parent_child_rel_child r_into_rtrancl rtrancl_trans)
      next
        case False
        obtain ancestor_element shadow_root
          where "ptr = cast ancestor_element"
            and "h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root"
            and "cast shadow_root \<in> set ancestors"
          using False \<open>\<And>thesis. ((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_child \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis) \<or>
((\<forall>ancestor_element shadow_root. ptr = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow>
cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)\<close>
          by blast

        then show ?thesis
          using 1(2) a_host_shadow_root_rel_shadow_root
          apply(simp)
          by (meson Un_iff converse_rtrancl_into_rtrancl)
      qed
    qed
  qed
qed

lemma get_root_node_si_root_in_heap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node_si ptr \<rightarrow>\<^sub>r root"
  shows "root |\<in>| object_ptr_kinds h"
  using assms
  apply(auto simp add: get_root_node_si_def elim!: bind_returns_result_E2)[1]
  by (simp add: get_ancestors_si_never_empty get_ancestors_si_ptrs_in_heap)

lemma get_root_node_si_same_no_parent:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node_si ptr \<rightarrow>\<^sub>r cast child"
  shows "h \<turnstile> get_parent child \<rightarrow>\<^sub>r None"
proof (insert assms(1) assms(4), induct ptr rule: heap_wellformed_induct_rev_si)
  case (step c)
  then show ?case
  proof (cases "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r c")
    case None
    then show ?thesis
      using step(4)
      by(auto simp add: get_root_node_si_def get_ancestors_si_def[of c] elim!: bind_returns_result_E2
          split: if_splits option.splits intro!: step(2) bind_pure_returns_result_I)
  next
    case (Some child_node)
    note s = this
    then obtain parent_opt where parent_opt: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r parent_opt"
      using step(4)
      apply(auto simp add: get_root_node_si_def get_ancestors_si_def intro!: bind_pure_I
          elim!: bind_returns_result_E2)[1]
      by(auto split: option.splits)
    then show ?thesis
    proof(induct parent_opt)
      case None
      then show ?case
        using Some get_root_node_si_no_parent returns_result_eq step.prems by fastforce
    next
      case (Some parent)
      then show ?case
        using step(4) s
        apply(auto simp add: get_root_node_si_def get_ancestors_si_def[of c]
            elim!: bind_returns_result_E2 split: option.splits list.splits if_splits)[1]
        using assms(1) get_ancestors_si_never_empty apply blast
        by(auto simp add: get_root_node_si_def dest: returns_result_eq
            intro!: step(1) bind_pure_returns_result_I)
    qed
  qed
qed

lemma get_root_node_si_parent_child_a_host_shadow_root_rel:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
  assumes "h \<turnstile> get_root_node_si ptr \<rightarrow>\<^sub>r root"
  shows "(root, ptr) \<in> (parent_child_rel h \<union> a_host_shadow_root_rel h)\<^sup>*"
  using assms
  using get_ancestors_si_parent_child_a_host_shadow_root_rel get_ancestors_si_never_empty
  by(auto simp add: get_root_node_si_def elim!: bind_returns_result_E2 intro!: bind_pure_returns_result_I)
end

interpretation i_get_root_node_si_wf?: l_get_root_node_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_host get_host_locs get_ancestors_si get_ancestors_si_locs get_root_node_si get_root_node_si_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs get_tag_name
  get_tag_name_locs heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_document
  get_disconnected_document_locs
  by(auto simp add: l_get_root_node_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_root_node_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_disconnected\_document\<close>

locale l_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_wf +
  l_get_parent
begin

lemma get_disconnected_document_ok:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None"
  shows "h \<turnstile> ok (get_disconnected_document node_ptr)"
proof -
  have "node_ptr |\<in>| node_ptr_kinds h"
    by (meson assms(4) is_OK_returns_result_I local.get_parent_ptr_in_heap)
  have "\<not>(\<exists>parent \<in> fset (object_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r)"
    apply(auto)[1]
    using assms(4) child_parent_dual[OF assms(1)]
      assms(1) assms(2) assms(3) known_ptrs_known_ptr option.simps(3)
      returns_result_eq returns_result_select_result
    by (metis (no_types, lifting) CD.get_child_nodes_ok)
  then
  have "(\<exists>document_ptr \<in> fset (document_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)"
    using heap_is_wellformed_children_disc_nodes
    using \<open>node_ptr |\<in>| node_ptr_kinds h\<close> assms(1) by blast
  then obtain some_owner_document where
    "some_owner_document \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))" and
    "node_ptr \<in> set |h \<turnstile> get_disconnected_nodes some_owner_document|\<^sub>r"
    by auto

  have h5: "\<exists>!x. x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h))) \<and> h \<turnstile> Heap_Error_Monad.bind (get_disconnected_nodes x)
                  (\<lambda>children. return (node_ptr \<in> set children)) \<rightarrow>\<^sub>r True"
    apply(auto intro!: bind_pure_returns_result_I)[1]
     apply (smt CD.get_disconnected_nodes_ok CD.get_disconnected_nodes_pure
        \<open>\<exists>document_ptr\<in>fset (document_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r\<close>
        assms(2) bind_pure_returns_result_I2 notin_fset return_returns_result select_result_I2)

    apply(auto elim!: bind_returns_result_E2 intro!: bind_pure_returns_result_I)[1]
    using heap_is_wellformed_one_disc_parent assms(1)
    by blast
  let ?filter_M = "filter_M
             (\<lambda>document_ptr.
                 Heap_Error_Monad.bind (get_disconnected_nodes document_ptr)
                  (\<lambda>disconnected_nodes. return (node_ptr \<in> set disconnected_nodes)))
             (sorted_list_of_set (fset (document_ptr_kinds h)))"
  have "h \<turnstile> ok (?filter_M)"
    using CD.get_disconnected_nodes_ok
    by (smt CD.get_disconnected_nodes_pure DocumentMonad.ptr_kinds_M_ptr_kinds
        DocumentMonad.ptr_kinds_ptr_kinds_M assms(2) bind_is_OK_pure_I bind_pure_I document_ptr_kinds_M_def
        filter_M_is_OK_I l_ptr_kinds_M.ptr_kinds_M_ok return_ok return_pure returns_result_select_result)
  then
  obtain candidates where candidates: "h \<turnstile> filter_M
             (\<lambda>document_ptr.
                 Heap_Error_Monad.bind (get_disconnected_nodes document_ptr)
                  (\<lambda>disconnected_nodes. return (node_ptr \<in> set disconnected_nodes)))
             (sorted_list_of_set (fset (document_ptr_kinds h)))
       \<rightarrow>\<^sub>r candidates"
    by auto
  have "candidates = [some_owner_document]"
    apply(rule filter_M_ex1[OF candidates \<open>some_owner_document \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))\<close> h5])
    using \<open>node_ptr \<in> set |h \<turnstile> get_disconnected_nodes some_owner_document|\<^sub>r\<close>
      \<open>some_owner_document \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))\<close>
    by(auto simp add: CD.get_disconnected_nodes_ok assms(2) intro!: bind_pure_I
        intro!: bind_pure_returns_result_I)
  then show ?thesis
    using candidates  \<open>node_ptr |\<in>| node_ptr_kinds h\<close>
    apply(auto simp add: get_disconnected_document_def intro!: bind_is_OK_pure_I filter_M_pure_I bind_pure_I
        split: list.splits)[1]
     apply (meson not_Cons_self2 returns_result_eq)
    by (meson list.distinct(1) list.inject returns_result_eq)
qed
end

interpretation i_get_disconnected_document_wf?: l_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs known_ptr type_wf
  heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs
  get_disconnected_document get_disconnected_document_locs known_ptrs get_parent get_parent_locs
  by(auto simp add: l_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]



subsubsection \<open>get\_ancestors\_di\<close>

locale l_get_ancestors_di_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_wf +
  l_get_parent_get_host_wf +
  l_get_host_wf +
  l_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_get_host_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma get_ancestors_di_ok:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
    and "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (get_ancestors_di ptr)"
proof (insert assms(1) assms(4), induct rule: heap_wellformed_induct_rev_si)
  case (step child)
  then show ?case
    using assms(2) assms(3)
    apply(auto simp add: get_ancestors_di_def[of child] assms(1) get_parent_parent_in_heap
        intro!: bind_is_OK_pure_I bind_pure_I split: option.splits)[1]
    using local.get_parent_ok apply blast
    using assms(1) get_disconnected_document_ok apply blast
      apply(simp add: get_ancestors_di_def )
      apply(auto intro!: bind_is_OK_pure_I split: option.splits)[1]
         apply (metis (no_types, lifting) bind_is_OK_E document_ptr_kinds_commutes is_OK_returns_heap_I
        local.get_ancestors_di_def local.get_disconnected_document_disconnected_document_in_heap step.hyps(3))
        apply (metis (no_types, lifting) bind_is_OK_E document_ptr_kinds_commutes is_OK_returns_heap_I
        local.get_ancestors_di_def local.get_disconnected_document_disconnected_document_in_heap step.hyps(3))
    using assms(1) local.get_disconnected_document_disconnected_document_in_heap local.get_host_ok
      shadow_root_ptr_kinds_commutes apply blast
      apply (smt assms(1) bind_returns_heap_E document_ptr_casts_commute2 is_OK_returns_heap_E
        is_OK_returns_heap_I l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M.shadow_root_same_host
        local.get_disconnected_document_disconnected_document_in_heap local.get_host_pure
        local.l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms local.shadow_root_host_dual option.simps(4) option.simps(5)
        pure_returns_heap_eq shadow_root_ptr_casts_commute2)
    using get_host_ok assms(1) apply blast
    by (meson assms(1) is_OK_returns_result_I local.get_shadow_root_ptr_in_heap local.shadow_root_host_dual)
qed

lemma get_ancestors_di_ptrs_in_heap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_ancestors_di ptr \<rightarrow>\<^sub>r ancestors"
  assumes "ptr' \<in> set ancestors"
  shows "ptr' |\<in>| object_ptr_kinds h"
proof (insert assms(4) assms(5), induct ancestors arbitrary: ptr)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons a ancestors)
  then obtain x where x: "h \<turnstile> get_ancestors_di x \<rightarrow>\<^sub>r a # ancestors"
    by(auto simp add: get_ancestors_di_def[of a] elim!: bind_returns_result_E2 split: option.splits)
  then have "x = a"
    by(auto simp add: get_ancestors_di_def[of x] intro!: bind_pure_I elim!: bind_returns_result_E2
        split: option.splits)
  then show ?case
  proof (cases "ptr' = a")
    case True
    then show ?thesis
      using Cons.hyps Cons.prems(2) get_ancestors_di_ptr_in_heap x
      using \<open>x = a\<close> by blast
  next
    case False
    obtain ptr'' where ptr'': "h \<turnstile> get_ancestors_di ptr'' \<rightarrow>\<^sub>r ancestors"
      using \<open> h \<turnstile> get_ancestors_di x \<rightarrow>\<^sub>r a # ancestors\<close> Cons.prems(2) False
      apply(auto simp add: get_ancestors_di_def elim!: bind_returns_result_E2)[1]
       apply(auto elim!: bind_returns_result_E2 split: option.splits intro!: bind_pure_I)[1]
      apply(auto elim!: bind_returns_result_E2 split: option.splits intro!: bind_pure_I)[1]
        apply (metis (no_types, lifting) local.get_ancestors_di_def)
       apply (metis (no_types, lifting) local.get_ancestors_di_def)
      by (simp add: local.get_ancestors_di_def)
    then show ?thesis
      using Cons.hyps Cons.prems(2) False by auto
  qed
qed

lemma get_ancestors_di_reads:
  assumes "heap_is_wellformed h"
  shows "reads get_ancestors_di_locs (get_ancestors_di node_ptr) h h'"
proof (insert assms(1), induct rule: heap_wellformed_induct_rev_si)
  case (step child)
  then show ?case
    using (* [[simproc del: Product_Type.unit_eq]] *) get_parent_reads[unfolded reads_def]
      get_host_reads[unfolded reads_def] get_disconnected_document_reads[unfolded reads_def]
    apply(auto simp add: get_ancestors_di_def[of child])[1]
    by(auto simp add: get_ancestors_di_locs_def get_parent_reads_pointers
        intro!: bind_pure_I reads_bind_pure reads_subset[OF check_in_heap_reads] reads_subset[OF return_reads]
        reads_subset[OF get_parent_reads] reads_subset[OF get_child_nodes_reads]
        reads_subset[OF get_host_reads] reads_subset[OF get_disconnected_document_reads]
        split: option.splits list.splits
        )

qed

lemma get_ancestors_di_subset:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors_di ptr \<rightarrow>\<^sub>r ancestors"
    and "ancestor \<in> set ancestors"
    and "h \<turnstile> get_ancestors_di ancestor \<rightarrow>\<^sub>r ancestor_ancestors"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
  shows "set ancestor_ancestors \<subseteq> set ancestors"
proof (insert assms(1) assms(2) assms(3), induct ptr arbitrary: ancestors
    rule: heap_wellformed_induct_rev_si)
  case (step child)
  have "child |\<in>| object_ptr_kinds h"
    using get_ancestors_di_ptr_in_heap step(4) by auto
      (*  then have "h \<turnstile> check_in_heap child \<rightarrow>\<^sub>r ()"
    using returns_result_select_result by force *)


  obtain tl_ancestors where tl_ancestors: "ancestors = child # tl_ancestors"
    using step(4)
    by(auto simp add: get_ancestors_di_def[of child] intro!: bind_pure_I
        elim!: bind_returns_result_E2 split: option.splits)
  show ?case
  proof (induct "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
    case None
    show ?case
    proof (induct "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
      case None
      then show ?case
        using step(4) \<open>None = cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child\<close>
        apply(auto simp add: get_ancestors_di_def[of child] elim!: bind_returns_result_E2)[1]
        by (metis (no_types, lifting) assms(4) empty_iff empty_set select_result_I2 set_ConsD
            step.prems(1) step.prems(2))
    next
      case (Some shadow_root_child)
      then
      have "cast shadow_root_child |\<in>| document_ptr_kinds h"
        using  \<open>child |\<in>| object_ptr_kinds h\<close>
        apply(auto simp add: document_ptr_kinds_def split: option.splits)[1]
        by (metis (mono_tags, lifting) document_ptr_casts_commute3 document_ptr_kinds_commutes
            document_ptr_kinds_def fset.map_comp shadow_root_ptr_casts_commute)
      then
      have "shadow_root_child |\<in>| shadow_root_ptr_kinds h"
        using shadow_root_ptr_kinds_commutes by blast
      obtain host where host: "h \<turnstile> get_host shadow_root_child \<rightarrow>\<^sub>r host"
        using get_host_ok assms
        by (meson \<open>shadow_root_child |\<in>| shadow_root_ptr_kinds h\<close> is_OK_returns_result_E)
      then
      have "h \<turnstile> get_ancestors_di (cast host) \<rightarrow>\<^sub>r tl_ancestors"
        using Some step(4) tl_ancestors None
        by(auto simp add: get_ancestors_di_def[of child] intro!: bind_pure_returns_result_I
            elim!: bind_returns_result_E2 split: option.splits dest: returns_result_eq)
      then
      show ?case
        using step(2) Some host step(5) tl_ancestors
        using assms(4) dual_order.trans eq_iff returns_result_eq set_ConsD set_subset_Cons
          shadow_root_ptr_casts_commute document_ptr_casts_commute step.prems(1)
        by (smt case_optionE local.shadow_root_host_dual option.case_distrib option.distinct(1))
    qed
  next
    case (Some child_node)
    note s1 = Some
    obtain parent_opt where parent_opt: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r parent_opt"
      using \<open>child |\<in>| object_ptr_kinds h\<close> assms(1) Some[symmetric] get_parent_ok[OF type_wf known_ptrs]
      by (metis (no_types, lifting) is_OK_returns_result_E known_ptrs get_parent_ok
          l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms node_ptr_casts_commute node_ptr_kinds_commutes)
    then show ?case
    proof (induct parent_opt)
      case None
      then obtain disc_doc where disc_doc: "h \<turnstile> get_disconnected_document child_node \<rightarrow>\<^sub>r disc_doc"
        and "h \<turnstile> get_ancestors_di (cast disc_doc) \<rightarrow>\<^sub>r tl_ancestors"
        using step(4) s1 tl_ancestors
        apply(simp add: get_ancestors_di_def[of child])
        by(auto elim!: bind_returns_result_E2 intro!: bind_pure_I split: option.splits dest: returns_result_eq)
      then show ?thesis
        using step(3) step(4) step(5)
        by (metis (no_types, lifting) assms(4) dual_order.trans eq_iff node_ptr_casts_commute s1
            select_result_I2 set_ConsD set_subset_Cons tl_ancestors)
    next
      case (Some parent)
      then
      have "h \<turnstile> get_ancestors_di parent \<rightarrow>\<^sub>r tl_ancestors"
        using s1 tl_ancestors step(4)
        by(auto simp add: get_ancestors_di_def[of child] elim!: bind_returns_result_E2
            split: option.splits dest: returns_result_eq)
      show ?case
        by (metis (no_types, lifting) Some.prems \<open>h \<turnstile> get_ancestors_di parent \<rightarrow>\<^sub>r tl_ancestors\<close>
            assms(4) eq_iff node_ptr_casts_commute order_trans s1 select_result_I2 set_ConsD set_subset_Cons
            step.hyps(1) step.prems(1) step.prems(2) tl_ancestors)
    qed
  qed
qed

lemma get_ancestors_di_also_parent:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors_di some_ptr \<rightarrow>\<^sub>r ancestors"
    and "cast child \<in> set ancestors"
    and "h \<turnstile> get_parent child \<rightarrow>\<^sub>r Some parent"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
  shows "parent \<in> set ancestors"
proof -
  obtain child_ancestors where child_ancestors: "h \<turnstile> get_ancestors_di (cast child) \<rightarrow>\<^sub>r child_ancestors"
    by (meson assms(1) assms(4) get_ancestors_di_ok is_OK_returns_result_I known_ptrs
        local.get_parent_ptr_in_heap node_ptr_kinds_commutes returns_result_select_result
        type_wf)
  then have "parent \<in> set child_ancestors"
    apply(simp add: get_ancestors_di_def)
    by(auto elim!: bind_returns_result_E2 split: option.splits dest!: returns_result_eq[OF assms(4)]
        get_ancestors_di_ptr)
  then show ?thesis
    using assms child_ancestors get_ancestors_di_subset by blast
qed

lemma get_ancestors_di_also_host:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors_di some_ptr \<rightarrow>\<^sub>r ancestors"
    and "cast shadow_root \<in> set ancestors"
    and "h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
  shows "cast host \<in> set ancestors"
proof -
  obtain child_ancestors where child_ancestors: "h \<turnstile> get_ancestors_di (cast shadow_root) \<rightarrow>\<^sub>r child_ancestors"
    by (meson assms(1) assms(2) assms(3) get_ancestors_di_ok get_ancestors_di_ptrs_in_heap
        is_OK_returns_result_E known_ptrs type_wf)
  then have "cast host \<in> set child_ancestors"
    apply(simp add: get_ancestors_di_def)
    by(auto elim!: bind_returns_result_E2 split: option.splits dest!: returns_result_eq[OF assms(4)]
        get_ancestors_di_ptr)
  then show ?thesis
    using assms child_ancestors get_ancestors_di_subset by blast
qed

lemma get_ancestors_di_also_disconnected_document:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> get_ancestors_di some_ptr \<rightarrow>\<^sub>r ancestors"
    and "cast disc_node \<in> set ancestors"
    and "h \<turnstile> get_disconnected_document disc_node \<rightarrow>\<^sub>r disconnected_document"
    and type_wf: "type_wf h"
    and known_ptrs: "known_ptrs h"
    and "h \<turnstile> get_parent disc_node \<rightarrow>\<^sub>r None"
  shows "cast disconnected_document \<in> set ancestors"
proof -
  obtain child_ancestors where child_ancestors: "h \<turnstile> get_ancestors_di (cast disc_node) \<rightarrow>\<^sub>r child_ancestors"
    by (meson assms(1) assms(2) assms(3) get_ancestors_di_ok get_ancestors_di_ptrs_in_heap
        is_OK_returns_result_E known_ptrs type_wf)
  then have "cast disconnected_document \<in> set child_ancestors"
    apply(simp add: get_ancestors_di_def)
    by(auto elim!: bind_returns_result_E2 intro!: bind_pure_I split: option.splits
        dest!: returns_result_eq[OF assms(4)] returns_result_eq[OF assms(7)]
        get_ancestors_di_ptr)
  then show ?thesis
    using assms child_ancestors get_ancestors_di_subset by blast
qed

lemma disc_node_disc_doc_dual:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None"
  assumes "h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes"
  assumes "node_ptr \<in> set disc_nodes"
  shows "h \<turnstile> get_disconnected_document node_ptr \<rightarrow>\<^sub>r disc_doc"
proof -
  have "node_ptr |\<in>| node_ptr_kinds h"
    by (meson assms(4) is_OK_returns_result_I local.get_parent_ptr_in_heap)
  then
  have "\<not>(\<exists>parent \<in> fset (object_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r)"
    apply(auto)[1]
    using child_parent_dual[OF assms(1)]
      assms known_ptrs_known_ptr option.simps(3)
      returns_result_eq returns_result_select_result
    by (metis (no_types, lifting) get_child_nodes_ok)
  then
  have "(\<exists>document_ptr \<in> fset (document_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)"
    using heap_is_wellformed_children_disc_nodes
    using \<open>node_ptr |\<in>| node_ptr_kinds h\<close> assms(1) by blast
      (* then obtain some_owner_document where
    "some_owner_document \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))" and
    "node_ptr \<in> set |h \<turnstile> get_disconnected_nodes some_owner_document|\<^sub>r"
    by auto *)
  then have "disc_doc \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))" and
    "node_ptr \<in> set |h \<turnstile> get_disconnected_nodes disc_doc|\<^sub>r"
    using CD.get_disconnected_nodes_ptr_in_heap assms(5)
      assms(6) by auto


  have h5: "\<exists>!x. x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h))) \<and>
h \<turnstile> Heap_Error_Monad.bind (get_disconnected_nodes x)
                  (\<lambda>children. return (node_ptr \<in> set children)) \<rightarrow>\<^sub>r True"
    apply(auto intro!: bind_pure_returns_result_I)[1]
     apply (smt CD.get_disconnected_nodes_ok CD.get_disconnected_nodes_pure
        \<open>\<exists>document_ptr\<in>fset (document_ptr_kinds h). node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r\<close>
        assms(2) bind_pure_returns_result_I2 notin_fset return_returns_result select_result_I2)

    apply(auto elim!: bind_returns_result_E2 intro!: bind_pure_returns_result_I)[1]
    using heap_is_wellformed_one_disc_parent assms(1)
    by blast
  let ?filter_M = "filter_M
             (\<lambda>document_ptr.
                 Heap_Error_Monad.bind (get_disconnected_nodes document_ptr)
                  (\<lambda>disconnected_nodes. return (node_ptr \<in> set disconnected_nodes)))
             (sorted_list_of_set (fset (document_ptr_kinds h)))"
  have "h \<turnstile> ok (?filter_M)"
    using CD.get_disconnected_nodes_ok
    by (smt CD.get_disconnected_nodes_pure DocumentMonad.ptr_kinds_M_ptr_kinds
        DocumentMonad.ptr_kinds_ptr_kinds_M assms(2) bind_is_OK_pure_I bind_pure_I document_ptr_kinds_M_def
        filter_M_is_OK_I l_ptr_kinds_M.ptr_kinds_M_ok return_ok return_pure returns_result_select_result)
  then
  obtain candidates where candidates: "h \<turnstile> ?filter_M \<rightarrow>\<^sub>r candidates"
    by auto
  have "candidates = [disc_doc]"
    apply(rule filter_M_ex1[OF candidates \<open>disc_doc \<in>
set (sorted_list_of_set (fset (document_ptr_kinds h)))\<close> h5])
    using \<open>node_ptr \<in> set |h \<turnstile> get_disconnected_nodes disc_doc|\<^sub>r\<close>
      \<open>disc_doc \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))\<close>
    by(auto simp add: CD.get_disconnected_nodes_ok assms(2) intro!: bind_pure_I
        intro!: bind_pure_returns_result_I)

  then
  show ?thesis
    using \<open>node_ptr |\<in>| node_ptr_kinds h\<close> candidates
    by(auto simp add: bind_pure_I get_disconnected_document_def
        elim!: bind_returns_result_E2
        intro!: bind_pure_returns_result_I filter_M_pure_I)
qed

lemma get_ancestors_di_obtains_children_or_shadow_root_or_disconnected_node:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
    and "h \<turnstile> get_ancestors_di ptr \<rightarrow>\<^sub>r ancestors"
    and "ancestor \<noteq> ptr"
    and "ancestor \<in> set ancestors"
  shows "((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast ancestor_child \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)
      \<or> ((\<forall>ancestor_element shadow_root. ancestor = cast ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow> cast shadow_root \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow>
thesis)
      \<or> ((\<forall>disc_doc disc_nodes disc_node. ancestor = cast disc_doc \<longrightarrow>
h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes \<longrightarrow> disc_node \<in> set disc_nodes \<longrightarrow>
cast disc_node \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)"
proof (insert assms(4) assms(5) assms(6), induct ptr arbitrary: ancestors
    rule: heap_wellformed_induct_rev_si[OF assms(1)])
  case (1 child)
  then show ?case
  proof (cases "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child")
    case None
    then obtain shadow_root where shadow_root: "child = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root"
      using 1(4) 1(5) 1(6)
      by(auto simp add: get_ancestors_di_def[of child] elim!: bind_returns_result_E2
          split: option.splits)
    then obtain host where host: "h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host"
      by (metis "1.prems"(1) assms(1) assms(2) assms(3) document_ptr_kinds_commutes
          get_ancestors_di_ptrs_in_heap is_OK_returns_result_E local.get_ancestors_di_ptr local.get_host_ok
          shadow_root_ptr_kinds_commutes)
    then obtain host_ancestors where host_ancestors:
      "h \<turnstile> get_ancestors_di (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host) \<rightarrow>\<^sub>r host_ancestors"
      by (metis "1.prems"(1) assms(1) assms(2) assms(3) get_ancestors_di_also_host get_ancestors_di_ok
          get_ancestors_di_ptrs_in_heap is_OK_returns_result_E local.get_ancestors_di_ptr shadow_root)
    then have "ancestors = cast shadow_root # host_ancestors"
      using 1(4) 1(5) 1(3) None shadow_root host
      by(auto simp add: get_ancestors_di_def[of child, simplified shadow_root]
          elim!: bind_returns_result_E2 dest!: returns_result_eq[OF host] split: option.splits)
    then show ?thesis
    proof (cases "ancestor = cast host")
      case True
      then show ?thesis
        using "1.prems"(1) host local.get_ancestors_di_ptr local.shadow_root_host_dual shadow_root
        by blast
    next
      case False
      have "ancestor \<in> set ancestors"
        using host host_ancestors 1(3) get_ancestors_di_also_host assms(1) assms(2) assms(3)
        using "1.prems"(3) by blast
      then have "((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_child \<in> set host_ancestors \<longrightarrow> thesis) \<longrightarrow>
thesis) \<or>
          ((\<forall>ancestor_element shadow_root. ancestor = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow>
cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root \<in> set host_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)
  \<or> ((\<forall>disc_doc disc_nodes disc_node. ancestor = cast disc_doc \<longrightarrow>
h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes \<longrightarrow> disc_node \<in> set disc_nodes \<longrightarrow>
cast disc_node \<in> set host_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)"
        using "1.hyps"(2) "1.prems"(2) False \<open>ancestors = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root # host_ancestors\<close>
          host host_ancestors shadow_root
        by auto
      then show ?thesis
        using \<open>ancestors = cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root # host_ancestors\<close>
        by auto
    qed
  next
    case (Some child_node)
    then obtain parent_opt where parent_opt: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r parent_opt"
      by (metis (no_types, lifting) "1.prems"(1) assms(1) assms(2) assms(3)
          get_ancestors_di_ptrs_in_heap is_OK_returns_result_E local.get_ancestors_di_ptr
          local.get_parent_ok node_ptr_casts_commute node_ptr_kinds_commutes)
    then show ?thesis
    proof (induct parent_opt)
      case None
      then obtain disc_doc where disc_doc: "h \<turnstile> get_disconnected_document child_node \<rightarrow>\<^sub>r disc_doc"
        by (meson assms(1) assms(2) assms(3) is_OK_returns_result_E local.get_disconnected_document_ok)
      then obtain parent_ancestors where parent_ancestors: "h \<turnstile> get_ancestors_di (cast disc_doc) \<rightarrow>\<^sub>r parent_ancestors"
        by (meson assms(1) assms(2) assms(3) document_ptr_kinds_commutes is_OK_returns_result_E
            l_get_ancestors_di_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M.get_ancestors_di_ok l_get_ancestors_di_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms
            local.get_disconnected_document_disconnected_document_in_heap)
      then have "ancestors = cast child_node # parent_ancestors"
        using 1(4) 1(5) 1(6) Some \<open>cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child = Some child_node\<close>
        apply(auto simp add: get_ancestors_di_def[of child,
              simplified \<open>cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child = Some child_node\<close>] intro!: bind_pure_I
            elim!: bind_returns_result_E2 dest!: returns_result_eq[OF disc_doc] split: option.splits)[1]
         apply (simp add: returns_result_eq)
        by (meson None.prems option.distinct(1) returns_result_eq)
      then show ?thesis
      proof (cases "ancestor = cast disc_doc")
        case True
        then show ?thesis
          by (metis \<open>ancestors = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node # parent_ancestors\<close> disc_doc
              list.set_intros(1) local.disc_doc_disc_node_dual)
      next
        case False
        have "ancestor \<in> set ancestors"
          by (simp add: "1.prems"(3))
        then have "((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_child \<in> set parent_ancestors \<longrightarrow> thesis) \<longrightarrow>
thesis) \<or>
          ((\<forall>ancestor_element shadow_root. ancestor = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow>
cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root \<in> set parent_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)
  \<or> ((\<forall>disc_doc disc_nodes disc_node. ancestor = cast disc_doc \<longrightarrow>
h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes \<longrightarrow> disc_node \<in> set disc_nodes \<longrightarrow>
cast disc_node \<in> set parent_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)"
          using "1.hyps"(3) "1.prems"(2) False Some \<open>cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child = Some child_node\<close>
            \<open>ancestors = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node # parent_ancestors\<close> disc_doc parent_ancestors
          by auto
        then show ?thesis
          using \<open>ancestors = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node # parent_ancestors\<close> by auto
      qed
    next
      case (Some option)
      then obtain parent where parent: "h \<turnstile> get_parent child_node \<rightarrow>\<^sub>r Some parent"
        using 1(4) 1(5) 1(6)
        by(auto simp add: get_ancestors_di_def[of child] intro!: bind_pure_I
            elim!: bind_returns_result_E2 split: option.splits)
      then obtain parent_ancestors where parent_ancestors:
        "h \<turnstile> get_ancestors_di parent \<rightarrow>\<^sub>r parent_ancestors"
        by (meson assms(1) assms(2) assms(3) get_ancestors_di_ok is_OK_returns_result_E
            local.get_parent_parent_in_heap)
      then have "ancestors = cast child_node # parent_ancestors"
        using 1(4) 1(5) 1(6) Some \<open>cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child = Some child_node\<close>
        by(auto simp add: get_ancestors_di_def[of child, simplified
              \<open>cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child = Some child_node\<close>] dest!:  elim!: bind_returns_result_E2
            dest!: returns_result_eq[OF parent] split: option.splits)
      then show ?thesis
      proof (cases "ancestor = parent")
        case True
        then show ?thesis
          by (metis \<open>ancestors = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node # parent_ancestors\<close>
              list.set_intros(1) local.get_parent_child_dual parent)
      next
        case False
        have "ancestor \<in> set ancestors"
          by (simp add: "1.prems"(3))
        then have "((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ancestor \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_child \<in> set parent_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis) \<or>
          ((\<forall>ancestor_element shadow_root. ancestor = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow> cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root \<in> set parent_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)
  \<or> ((\<forall>disc_doc disc_nodes disc_node. ancestor = cast disc_doc \<longrightarrow>
h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes \<longrightarrow> disc_node \<in> set disc_nodes \<longrightarrow>
cast disc_node \<in> set parent_ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)"
          using "1.hyps"(1) "1.prems"(2) False Some \<open>cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child = Some child_node\<close>
            \<open>ancestors = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node # parent_ancestors\<close> parent parent_ancestors
          by auto
        then show ?thesis
          using \<open>ancestors = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child_node # parent_ancestors\<close>
          by auto
      qed
    qed
  qed
qed

lemma get_ancestors_di_parent_child_a_host_shadow_root_rel:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
  assumes "h \<turnstile> get_ancestors_di child \<rightarrow>\<^sub>r ancestors"
  shows "(ptr, child) \<in> (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>* \<longleftrightarrow> ptr \<in> set ancestors"
proof
  assume "(ptr, child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>* "
  then show "ptr \<in> set ancestors"
  proof (induct ptr rule: heap_wellformed_induct_si[OF assms(1)])
    case (1 ptr)
    then show ?case
    proof (cases "ptr = child")
      case True
      then show ?thesis
        using assms(4) get_ancestors_di_ptr by blast
    next
      case False
      obtain ptr_child where
        ptr_child: "(ptr, ptr_child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h) \<and>
(ptr_child, child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
        using converse_rtranclE[OF 1(4)] \<open>ptr \<noteq> child\<close>
        by metis
      then show ?thesis
      proof(cases "(ptr, ptr_child) \<in> parent_child_rel h")
        case True

        then obtain ptr_child_node
          where ptr_child_ptr_child_node: "ptr_child = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node"
          using ptr_child node_ptr_casts_commute3 CD.parent_child_rel_node_ptr
          by (metis)
        then obtain children where
          children: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children" and
          ptr_child_node: "ptr_child_node \<in> set children"
        proof -
          assume a1: "\<And>children. \<lbrakk>h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children; ptr_child_node \<in> set children\<rbrakk>
                   \<Longrightarrow> thesis"

          have "ptr |\<in>| object_ptr_kinds h"
            using CD.parent_child_rel_parent_in_heap True by blast
          moreover have "ptr_child_node \<in> set |h \<turnstile> get_child_nodes ptr|\<^sub>r"
            by (metis True assms(2) assms(3) calculation local.CD.parent_child_rel_child
                local.get_child_nodes_ok local.known_ptrs_known_ptr ptr_child_ptr_child_node
                returns_result_select_result)
          ultimately show ?thesis
            using a1 get_child_nodes_ok \<open>type_wf h\<close> \<open>known_ptrs h\<close>
            by (meson local.known_ptrs_known_ptr returns_result_select_result)
        qed
        moreover have "(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node, child) \<in>
(parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
          using ptr_child True ptr_child_ptr_child_node by auto
        ultimately have "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr_child_node \<in> set ancestors"
          using 1 by auto
        moreover have "h \<turnstile> get_parent ptr_child_node \<rightarrow>\<^sub>r Some ptr"
          using assms(1) children ptr_child_node child_parent_dual
          using \<open>known_ptrs h\<close> \<open>type_wf h\<close> by blast
        ultimately show ?thesis
          using get_ancestors_di_also_parent assms \<open>type_wf h\<close> by blast
      next
        case False
        then show ?thesis
        proof (cases "(ptr, ptr_child) \<in> a_host_shadow_root_rel h")
          case True
          then
          obtain host where host: "ptr = cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r host"
            using ptr_child
            by(auto simp add: a_host_shadow_root_rel_def)
          then obtain shadow_root where shadow_root: "h \<turnstile> get_shadow_root host \<rightarrow>\<^sub>r Some shadow_root"
            and ptr_child_shadow_root: "ptr_child = cast shadow_root"
            using False True
            apply(auto simp add: a_host_shadow_root_rel_def)[1]
            by (metis (no_types, lifting) assms(3) local.get_shadow_root_ok select_result_I)

          moreover have "(cast shadow_root, child) \<in>
(parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
            using ptr_child ptr_child_shadow_root by blast
          ultimately have "cast shadow_root \<in> set ancestors"
            using "1.hyps"(2) host by blast
          moreover have "h \<turnstile> get_host shadow_root \<rightarrow>\<^sub>r host"
            by (metis assms(1) assms(2) assms(3) is_OK_returns_result_E local.get_host_ok
                local.get_shadow_root_shadow_root_ptr_in_heap local.shadow_root_host_dual local.shadow_root_same_host
                shadow_root)
          ultimately show ?thesis
            using get_ancestors_di_also_host assms(1) assms(2) assms(3) assms(4) host
            by blast
        next
          case False
          then
          obtain disc_doc where disc_doc: "ptr = cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r disc_doc"
            using ptr_child \<open>(ptr, ptr_child) \<notin> parent_child_rel h\<close>
            by(auto simp add: a_ptr_disconnected_node_rel_def)
          then obtain disc_node disc_nodes where disc_nodes:
            "h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes"
            and disc_node: "disc_node \<in> set disc_nodes"
            and ptr_child_disc_node: "ptr_child = cast disc_node"
            using False \<open>(ptr, ptr_child) \<notin> parent_child_rel h\<close> ptr_child
            apply(auto simp add: a_ptr_disconnected_node_rel_def)[1]
            by (metis (no_types, lifting) CD.get_disconnected_nodes_ok assms(3)
                returns_result_select_result)

          moreover have "(cast disc_node, child) \<in>
(parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
            using ptr_child ptr_child_disc_node by blast
          ultimately have "cast disc_node \<in> set ancestors"
            using "1.hyps"(3) disc_doc by blast
          moreover have "h \<turnstile> get_parent disc_node \<rightarrow>\<^sub>r None"
            using \<open>(ptr, ptr_child) \<notin> parent_child_rel h\<close>
            apply(auto simp add: parent_child_rel_def ptr_child_disc_node)[1]
            by (smt assms(1) assms(2) assms(3) assms(4) calculation disc_node disc_nodes
                get_ancestors_di_ptrs_in_heap is_OK_returns_result_E local.CD.a_heap_is_wellformed_def
                local.CD.distinct_lists_no_parent local.CD.heap_is_wellformed_impl local.get_parent_child_dual
                local.get_parent_ok local.get_parent_parent_in_heap local.heap_is_wellformed_def
                node_ptr_kinds_commutes select_result_I2 split_option_ex)
          then
          have "h \<turnstile> get_disconnected_document disc_node \<rightarrow>\<^sub>r disc_doc"
            using disc_node_disc_doc_dual disc_nodes disc_node assms(1) assms(2) assms(3)
            by blast
          ultimately show ?thesis
            using \<open>h \<turnstile> get_parent disc_node \<rightarrow>\<^sub>r None\<close> assms(1) assms(2) assms(3) assms(4)
              disc_doc get_ancestors_di_also_disconnected_document
            by blast
        qed
      qed
    qed
  qed
next
  assume "ptr \<in> set ancestors"
  then show "(ptr, child) \<in> (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
  proof (induct ptr rule: heap_wellformed_induct_si[OF assms(1)])
    case (1 ptr)
    then show ?case
    proof (cases "ptr = child")
      case True
      then show ?thesis
        by simp
    next
      case False
      have 2: "\<And>thesis. ((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast ancestor_child \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)
      \<or> ((\<forall>ancestor_element shadow_root. ptr = cast ancestor_element \<longrightarrow>
h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root \<longrightarrow> cast shadow_root \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow>
thesis)
      \<or> ((\<forall>disc_doc disc_nodes disc_node. ptr = cast disc_doc \<longrightarrow>
h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes \<longrightarrow> disc_node \<in> set disc_nodes \<longrightarrow>
cast disc_node \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)"
        using "1.prems" False assms(1) assms(2) assms(3) assms(4)
          get_ancestors_di_obtains_children_or_shadow_root_or_disconnected_node by blast
      then show ?thesis
      proof (cases "\<forall>thesis. ((\<forall>children ancestor_child. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<longrightarrow>
ancestor_child \<in> set children \<longrightarrow> cast ancestor_child \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)")
        case True
        then obtain children ancestor_child
          where "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
            and "ancestor_child \<in> set children"
            and "cast ancestor_child \<in> set ancestors"
          by blast
        then show ?thesis
          by (meson "1.hyps"(1) in_rtrancl_UnI local.CD.parent_child_rel_child r_into_rtrancl
              rtrancl_trans)
      next
        case False
        note f1 = this
        then show ?thesis
        proof (cases "\<forall>thesis. ((\<forall>disc_doc disc_nodes disc_node. ptr = cast disc_doc \<longrightarrow>
h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes \<longrightarrow> disc_node \<in> set disc_nodes \<longrightarrow>
cast disc_node \<in> set ancestors \<longrightarrow> thesis) \<longrightarrow> thesis)")
          case True
          then obtain disc_doc disc_nodes disc_node
            where "ptr = cast disc_doc"
              and "h \<turnstile> get_disconnected_nodes disc_doc \<rightarrow>\<^sub>r disc_nodes"
              and "disc_node \<in> set disc_nodes"
              and "cast disc_node \<in> set ancestors"
            by blast
          then show ?thesis
            by (meson "1.hyps"(3) in_rtrancl_UnI
                local.a_ptr_disconnected_node_rel_disconnected_node r_into_rtrancl rtrancl_trans)
        next
          case False
          then
          obtain ancestor_element shadow_root
            where "ptr = cast ancestor_element"
              and "h \<turnstile> get_shadow_root ancestor_element \<rightarrow>\<^sub>r Some shadow_root"
              and "cast shadow_root \<in> set ancestors"
            using f1 2 by smt
          then show ?thesis
            by (meson "1.hyps"(2) in_rtrancl_UnI local.a_host_shadow_root_rel_shadow_root
                r_into_rtrancl rtrancl_trans)
        qed
      qed
    qed
  qed
qed
end
interpretation i_get_ancestors_di_wf?: l_get_ancestors_di_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr known_ptrs get_parent get_parent_locs get_child_nodes get_child_nodes_locs
  get_host get_host_locs get_disconnected_document get_disconnected_document_locs get_ancestors_di
  get_ancestors_di_locs get_disconnected_nodes get_disconnected_nodes_locs get_shadow_root
  get_shadow_root_locs get_tag_name get_tag_name_locs heap_is_wellformed parent_child_rel
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  by(auto simp add: l_get_ancestors_di_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_get_ancestors_di_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_owner\_document\<close>

locale l_get_owner_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes +
  l_get_child_nodes +
  l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_wf +
  l_known_ptrs +
  l_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  assumes known_ptr_impl: "known_ptr = ShadowRootClass.known_ptr"
begin
lemma get_owner_document_disconnected_nodes:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
  assumes "node_ptr \<in> set disc_nodes"
  assumes known_ptrs: "known_ptrs h"
  assumes type_wf: "type_wf h"
  shows "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r document_ptr"
proof -
  have 2: "node_ptr |\<in>| node_ptr_kinds h"
    using assms
    apply(auto simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.a_all_ptrs_in_heap_def)[1]
    using assms(1) local.heap_is_wellformed_disc_nodes_in_heap by blast
  have 3: "document_ptr |\<in>| document_ptr_kinds h"
    using assms(2) get_disconnected_nodes_ptr_in_heap by blast
  then have 4: "\<not>(\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h \<and> node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
    using CD.distinct_lists_no_parent assms  unfolding heap_is_wellformed_def CD.heap_is_wellformed_def
    by simp
  moreover have "(\<exists>document_ptr. document_ptr |\<in>| document_ptr_kinds h \<and>
node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r) \<or>
       (\<exists>parent_ptr. parent_ptr |\<in>| object_ptr_kinds h \<and> node_ptr \<in> set |h \<turnstile> get_child_nodes parent_ptr|\<^sub>r)"
    using assms(1) 2 "3" assms(2) assms(3) by auto
  ultimately have 0: "\<exists>!document_ptr\<in>set |h \<turnstile> document_ptr_kinds_M|\<^sub>r.
node_ptr \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    using concat_map_distinct assms(1)  known_ptrs_implies
    by (smt CD.heap_is_wellformed_one_disc_parent DocumentMonad.ptr_kinds_ptr_kinds_M
        disjoint_iff_not_equal local.get_disconnected_nodes_ok local.heap_is_wellformed_def
        returns_result_select_result type_wf)


  have "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None"
    using 4 2
    apply(auto simp add: get_parent_def intro!: bind_pure_returns_result_I filter_M_pure_I bind_pure_I )[1]
    apply(auto intro!:  filter_M_empty_I bind_pure_I bind_pure_returns_result_I)[1]
    using get_child_nodes_ok assms(4)  type_wf
    by (metis get_child_nodes_ok known_ptrs_known_ptr returns_result_select_result)


  then have 4: "h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r cast node_ptr"
    using get_root_node_no_parent
    by simp
  obtain document_ptrs where document_ptrs: "h \<turnstile> document_ptr_kinds_M \<rightarrow>\<^sub>r document_ptrs"
    by simp
  then have "h \<turnstile> ok (filter_M (\<lambda>document_ptr. do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (((cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)) \<in> cast ` set disconnected_nodes)
        }) document_ptrs)"
    using assms(1) get_disconnected_nodes_ok type_wf
    by(auto intro!: bind_is_OK_I2 filter_M_is_OK_I bind_pure_I)
  then obtain candidates where
    candidates: "h \<turnstile> filter_M (\<lambda>document_ptr. do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (((cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)) \<in> cast ` set disconnected_nodes)
        }) document_ptrs \<rightarrow>\<^sub>r candidates"
    by auto

  have filter: "filter (\<lambda>document_ptr. |h \<turnstile> do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr \<in> cast ` set disconnected_nodes)
        }|\<^sub>r) document_ptrs = [document_ptr]"
    apply(rule filter_ex1)
    using 0 document_ptrs apply(simp)[1]
       apply (smt "0" "3" assms bind_is_OK_pure_I bind_pure_returns_result_I bind_pure_returns_result_I2
        bind_returns_result_E2 bind_returns_result_E3 document_ptr_kinds_M_def get_disconnected_nodes_ok
        get_disconnected_nodes_pure image_eqI is_OK_returns_result_E l_ptr_kinds_M.ptr_kinds_ptr_kinds_M return_ok
        return_returns_result returns_result_eq select_result_E select_result_I select_result_I2 select_result_I2)
    using assms(2) assms(3)
      apply (smt bind_is_OK_I2 bind_returns_result_E3 get_disconnected_nodes_pure image_eqI
        is_OK_returns_result_I return_ok return_returns_result select_result_E)
    using document_ptrs  3 apply(simp)
    using document_ptrs
    by simp
  have "h \<turnstile> filter_M (\<lambda>document_ptr. do {
          disconnected_nodes \<leftarrow> get_disconnected_nodes document_ptr;
          return (((cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)) \<in> cast ` set disconnected_nodes)
        }) document_ptrs \<rightarrow>\<^sub>r [document_ptr]"
    apply(rule filter_M_filter2)
    using get_disconnected_nodes_ok document_ptrs 3  assms(1)  type_wf filter
    by(auto intro: bind_pure_I bind_is_OK_I2)

  with 4 document_ptrs have "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r document_ptr"
    by(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!:  bind_pure_returns_result_I
        filter_M_pure_I bind_pure_I split: option.splits)
  moreover have "known_ptr (cast node_ptr)"
    using known_ptrs_known_ptr[OF known_ptrs, where ptr="cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr"] 2
      known_ptrs_implies by(simp)
  ultimately show ?thesis
    using 2
    apply(auto simp add: CD.a_get_owner_document_tups_def get_owner_document_def
        a_get_owner_document_tups_def known_ptr_impl)[1]
    apply(split invoke_splits, (rule conjI | rule impI)+)+
        apply(drule(1) known_ptr_not_shadow_root_ptr)
        apply(drule(1) known_ptr_not_document_ptr)
        apply(drule(1)  known_ptr_not_character_data_ptr)
        apply(drule(1)  known_ptr_not_element_ptr)
        apply(simp add: NodeClass.known_ptr_defs)
    by(auto split: option.splits intro!: bind_pure_returns_result_I)
qed

lemma in_disconnected_nodes_no_parent:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r None"
  assumes "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r owner_document"
  assumes "h \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes"
  assumes "known_ptrs h"
  assumes "type_wf h"
  shows "node_ptr \<in> set disc_nodes"
proof -
  have "\<And>parent. parent |\<in>| object_ptr_kinds h \<Longrightarrow> node_ptr \<notin> set |h \<turnstile> get_child_nodes parent|\<^sub>r"
    using assms(2)
    by (meson get_child_nodes_ok assms(1) assms(5) assms(6) local.child_parent_dual
        local.known_ptrs_known_ptr option.distinct(1) returns_result_eq returns_result_select_result)
  then show ?thesis
    by (smt assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) finite_set_in
        is_OK_returns_result_I local.get_disconnected_nodes_ok local.get_owner_document_disconnected_nodes
        local.get_parent_ptr_in_heap local.heap_is_wellformed_children_disc_nodes returns_result_select_result
        select_result_I2)
qed


lemma get_owner_document_owner_document_in_heap_node:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document"
  shows "owner_document |\<in>| document_ptr_kinds h"
proof -
  obtain root where
    root: "h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r root"
    using assms(4)
    by(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2
        split: option.splits)

  then show ?thesis
  proof (cases "is_document_ptr root")
    case True
    then show ?thesis
      using assms(4) root
      apply(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!:  bind_returns_result_E2
          intro!: filter_M_pure_I bind_pure_I split: option.splits)[1]
       apply(drule(1) returns_result_eq) apply(auto)[1]
      using assms document_ptr_kinds_commutes get_root_node_root_in_heap
      by blast
  next
    case False
    have "known_ptr root"
      using assms local.get_root_node_root_in_heap local.known_ptrs_known_ptr root by blast
    have "root |\<in>| object_ptr_kinds h"
      using root
      using assms local.get_root_node_root_in_heap
      by blast

    show ?thesis
    proof (cases "is_shadow_root_ptr root")
      case True
      then show ?thesis
        using assms(4) root
        apply(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!:  bind_returns_result_E2
            intro!: filter_M_pure_I bind_pure_I split: option.splits)[1]
         apply(drule(1) returns_result_eq) apply(auto)[1]
        using assms document_ptr_kinds_commutes get_root_node_root_in_heap
        by blast
    next
      case False
      then have "is_node_ptr_kind root"
        using \<open>\<not> is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root\<close> \<open>known_ptr root\<close> \<open>root |\<in>| object_ptr_kinds h\<close>
        apply(simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
            CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs)
        using is_node_ptr_kind_none
        by force
      then
      have "(\<exists>document_ptr \<in> fset (document_ptr_kinds h). root \<in> cast ` set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)"
        using local.child_parent_dual local.get_child_nodes_ok local.get_root_node_same_no_parent
          local.heap_is_wellformed_children_disc_nodes local.known_ptrs_known_ptr node_ptr_casts_commute3
          node_ptr_inclusion node_ptr_kinds_commutes notin_fset option.distinct(1) returns_result_eq
          returns_result_select_result root
        by (metis (no_types, lifting) assms \<open>root |\<in>| object_ptr_kinds h\<close>)
      then obtain some_owner_document where
        "some_owner_document |\<in>| document_ptr_kinds h" and
        "root \<in> cast ` set |h \<turnstile> get_disconnected_nodes some_owner_document|\<^sub>r"
        by auto
      then
      obtain candidates where
        candidates: "h \<turnstile> filter_M
               (\<lambda>document_ptr.
                   Heap_Error_Monad.bind (get_disconnected_nodes document_ptr)
                    (\<lambda>disconnected_nodes. return (root \<in> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ` set disconnected_nodes)))
               (sorted_list_of_set (fset (document_ptr_kinds h)))
         \<rightarrow>\<^sub>r candidates"
        by (metis (no_types, lifting) assms bind_is_OK_I2 bind_pure_I filter_M_is_OK_I finite_fset
            is_OK_returns_result_E local.get_disconnected_nodes_ok local.get_disconnected_nodes_pure notin_fset
            return_ok return_pure sorted_list_of_set(1))
      then have "some_owner_document \<in> set candidates"
        apply(rule filter_M_in_result_if_ok)
        using \<open>some_owner_document |\<in>| document_ptr_kinds h\<close>
          \<open>root \<in> cast ` set |h \<turnstile> get_disconnected_nodes some_owner_document|\<^sub>r\<close>
          apply(auto intro!: bind_pure_I bind_pure_returns_result_I)[1]
        using \<open>some_owner_document |\<in>| document_ptr_kinds h\<close>
          \<open>root \<in> cast ` set |h \<turnstile> get_disconnected_nodes some_owner_document|\<^sub>r\<close>
         apply(auto intro!: bind_pure_I bind_pure_returns_result_I)[1]
        using \<open>some_owner_document |\<in>| document_ptr_kinds h\<close>
          \<open>root \<in> cast ` set |h \<turnstile> get_disconnected_nodes some_owner_document|\<^sub>r\<close>
        apply(auto simp add: assms local.get_disconnected_nodes_ok
            intro!: bind_pure_I bind_pure_returns_result_I)[1]
        done

      then have "candidates \<noteq> []"
        by auto
      then have "owner_document \<in> set candidates"
        using assms(4) root
        apply(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!:  bind_returns_result_E2
            intro!: filter_M_pure_I bind_pure_I split: option.splits)[1]
         apply (metis candidates list.set_sel(1) returns_result_eq)
        by (metis \<open>is_node_ptr_kind root\<close> node_ptr_no_document_ptr_cast returns_result_eq)

      then show ?thesis
        using candidates
        by (meson bind_pure_I bind_returns_result_E2 filter_M_holds_for_result is_OK_returns_result_I
            local.get_disconnected_nodes_ptr_in_heap local.get_disconnected_nodes_pure return_pure)
    qed
  qed
qed

lemma get_owner_document_owner_document_in_heap:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
  shows "owner_document |\<in>| document_ptr_kinds h"
  using assms
  apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
      CD.a_get_owner_document_tups_def)[1]
  apply(split invoke_split_asm)+
proof -
  assume "h \<turnstile> invoke [] ptr () \<rightarrow>\<^sub>r owner_document"
  then show "owner_document |\<in>| document_ptr_kinds h"
    by (meson invoke_empty is_OK_returns_result_I)
next
  assume "h \<turnstile> Heap_Error_Monad.bind (check_in_heap ptr)
          (\<lambda>_. (CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) ptr ())
    \<rightarrow>\<^sub>r owner_document"
  then show "owner_document |\<in>| document_ptr_kinds h"
    by(auto simp add: CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2
        split: if_splits)
next
  assume 0: "heap_is_wellformed h"
    and 1: "type_wf h"
    and 2: "known_ptrs h"
    and 3: "\<not> is_element_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr"
    and 4: "is_character_data_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr"
    and 5: "h \<turnstile> Heap_Error_Monad.bind (check_in_heap ptr)
(\<lambda>_. (CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r) ptr ()) \<rightarrow>\<^sub>r owner_document"
  then show ?thesis
    by (metis bind_returns_result_E2 check_in_heap_pure comp_apply
        get_owner_document_owner_document_in_heap_node)
next
  assume 0: "heap_is_wellformed h"
    and 1: "type_wf h"
    and 2: "known_ptrs h"
    and 3: "is_element_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr"
    and 4: "h \<turnstile> Heap_Error_Monad.bind (check_in_heap ptr)
(\<lambda>_. (CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r) ptr ()) \<rightarrow>\<^sub>r owner_document"
  then show ?thesis
    by (metis bind_returns_result_E2 check_in_heap_pure comp_apply get_owner_document_owner_document_in_heap_node)
next
  assume 0: "heap_is_wellformed h"
    and 1: "type_wf h"
    and 2: "known_ptrs h"
    and 3: "\<not> is_element_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr"
    and 4: "\<not> is_character_data_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr"
    and 5: "\<not> is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr"
    and 6: "is_shadow_root_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr"
    and 7: "h \<turnstile> Heap_Error_Monad.bind (check_in_heap ptr)
(\<lambda>_. (local.a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r \<circ> the \<circ> cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r) ptr ()) \<rightarrow>\<^sub>r owner_document"
  then show "owner_document |\<in>| document_ptr_kinds h"
    by(auto simp add: CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        elim!: bind_returns_result_E2 split: if_splits)
qed

lemma get_owner_document_ok:
  assumes "heap_is_wellformed h"  "known_ptrs h" "type_wf h"
  assumes "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (get_owner_document ptr)"
proof -
  have "known_ptr ptr"
    using assms(2) assms(4) local.known_ptrs_known_ptr
    by blast
  then show ?thesis
    apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def CD.a_get_owner_document_tups_def)[1]
    apply(split invoke_splits, (rule conjI | rule impI)+)+
        apply(auto simp add: known_ptr_impl)[1]
    using NodeClass.a_known_ptr_def known_ptr_not_character_data_ptr known_ptr_not_document_ptr
      known_ptr_not_shadow_root_ptr known_ptr_not_element_ptr apply blast
    using assms(4)
       apply(auto simp add: get_root_node_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        intro!: bind_is_OK_pure_I filter_M_pure_I bind_pure_I filter_M_is_OK_I
        split: option.splits)[1]
    using assms(4)
      apply(auto simp add: get_root_node_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_is_OK_pure_I
        filter_M_pure_I bind_pure_I filter_M_is_OK_I split: option.splits)[1]
    using assms(4)
     apply(auto simp add: assms(1) assms(2) assms(3) local.get_ancestors_ok get_disconnected_nodes_ok
        get_root_node_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_is_OK_pure_I filter_M_pure_I bind_pure_I
        filter_M_is_OK_I split: option.splits)[1]
    using assms(4)
    apply(auto simp add: assms(1) assms(2) assms(3) local.get_ancestors_ok get_disconnected_nodes_ok
        get_root_node_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def intro!: bind_is_OK_pure_I filter_M_pure_I bind_pure_I
        filter_M_is_OK_I split: option.splits)[1]
    done
qed

lemma get_owner_document_child_same:
  assumes "heap_is_wellformed h"  "known_ptrs h" "type_wf h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  assumes "child \<in> set children"
  shows "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document \<longleftrightarrow> h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r owner_document"
proof -
  have "ptr |\<in>| object_ptr_kinds h"
    by (meson assms(4) is_OK_returns_result_I local.get_child_nodes_ptr_in_heap)
  then have "known_ptr ptr"
    using assms(2) local.known_ptrs_known_ptr by blast

  have "cast child |\<in>| object_ptr_kinds h"
    using assms(1) assms(4) assms(5) local.heap_is_wellformed_children_in_heap node_ptr_kinds_commutes
    by blast
  then
  have "known_ptr (cast child)"
    using assms(2) local.known_ptrs_known_ptr by blast
  then have "is_character_data_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (cast child) \<or> is_element_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (cast child)"
    by(auto simp add: known_ptr_impl NodeClass.a_known_ptr_def ElementClass.a_known_ptr_def
        CharacterDataClass.a_known_ptr_def DocumentClass.a_known_ptr_def a_known_ptr_def
        split: option.splits)
  obtain root where root: "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
    by (meson \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(1) assms(2) assms(3) is_OK_returns_result_E
        local.get_root_node_ok)
  then have "h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root"
    using assms(1) assms(2) assms(3) assms(4) assms(5) local.child_parent_dual local.get_root_node_parent_same
    by blast

  have "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document \<longleftrightarrow> h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child () \<rightarrow>\<^sub>r owner_document"
  proof (cases "is_document_ptr ptr")
    case True
    then obtain document_ptr where document_ptr: "cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr = ptr"
      using case_optionE document_ptr_casts_commute by blast
    then have "root = cast document_ptr"
      using root
      by(auto simp add: get_root_node_def get_ancestors_def elim!: bind_returns_result_E2
          split: option.splits)

    then have "h \<turnstile> CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr () \<rightarrow>\<^sub>r owner_document \<longleftrightarrow>
h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child () \<rightarrow>\<^sub>r owner_document"
      using document_ptr \<open>h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root\<close>[simplified \<open>root = cast document_ptr\<close>
          document_ptr]
      apply(auto simp add:  CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
          elim!: bind_returns_result_E2 dest!: bind_returns_result_E3[rotated, OF
            \<open>h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root\<close>[simplified \<open>root = cast document_ptr\<close> document_ptr], rotated]
          intro!: bind_pure_returns_result_I filter_M_pure_I bind_pure_I split: if_splits option.splits)[1]
      using \<open>ptr |\<in>| object_ptr_kinds h\<close> document_ptr_kinds_commutes by blast
    then show ?thesis
      using \<open>known_ptr ptr\<close>
      apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
          CD.a_get_owner_document_tups_def known_ptr_impl)[1]
       apply(split invoke_splits, ((rule conjI | rule impI)+)?)+
           apply(drule(1) known_ptr_not_shadow_root_ptr[folded known_ptr_impl])
           apply(drule(1) known_ptr_not_document_ptr)
           apply(drule(1)  known_ptr_not_character_data_ptr)
           apply(drule(1)  known_ptr_not_element_ptr)
           apply(simp add: NodeClass.known_ptr_defs)
      using \<open>ptr |\<in>| object_ptr_kinds h\<close> True
      by(auto simp add: document_ptr[symmetric] intro!: bind_pure_returns_result_I
          split: option.splits)
  next
    case False
    then show ?thesis
    proof (cases "is_shadow_root_ptr ptr")
      case True
      then obtain shadow_root_ptr where shadow_root_ptr: "cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr = ptr"
        using case_optionE shadow_root_ptr_casts_commute
        by (metis (no_types, lifting) document_ptr_casts_commute3 is_document_ptr_kind_none option.case_eq_if)
      then have "root = cast shadow_root_ptr"
        using root
        by(auto simp add: get_root_node_def get_ancestors_def elim!: bind_returns_result_E2
            split: option.splits)

      then have "h \<turnstile> a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r shadow_root_ptr () \<rightarrow>\<^sub>r owner_document \<longleftrightarrow>
h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child () \<rightarrow>\<^sub>r owner_document"
        using shadow_root_ptr \<open>h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root\<close>[simplified \<open>root = cast shadow_root_ptr\<close>
            shadow_root_ptr]
        apply(auto simp add:  CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
            CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2
            dest!: bind_returns_result_E3[rotated, OF \<open>h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root\<close>[simplified
                \<open>root = cast shadow_root_ptr\<close> shadow_root_ptr], rotated] intro!: bind_pure_returns_result_I
            filter_M_pure_I bind_pure_I split: if_splits option.splits)[1]
        using \<open>ptr |\<in>| object_ptr_kinds h\<close> shadow_root_ptr_kinds_commutes document_ptr_kinds_commutes
        by blast
      then show ?thesis
        using \<open>known_ptr ptr\<close>
        apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
            CD.a_get_owner_document_tups_def known_ptr_impl)[1]
         apply(split invoke_splits, ((rule conjI | rule impI)+)?)+
             apply(drule(1) known_ptr_not_shadow_root_ptr[folded known_ptr_impl])
             apply(drule(1) known_ptr_not_document_ptr)
             apply(drule(1)  known_ptr_not_character_data_ptr)
             apply(drule(1)  known_ptr_not_element_ptr)
             apply(simp add: NodeClass.known_ptr_defs)
        using \<open>ptr |\<in>| object_ptr_kinds h\<close> True
        using False
        by(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def shadow_root_ptr[symmetric]
            intro!: bind_pure_returns_result_I split: option.splits)
    next
      case False
      then obtain node_ptr where node_ptr: "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr = ptr"
        using \<open>known_ptr ptr\<close> \<open>\<not> is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr\<close>
        by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
            CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs split: option.splits)
      then have "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document \<longleftrightarrow>
h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r child () \<rightarrow>\<^sub>r owner_document"
        using root \<open>h \<turnstile> get_root_node (cast child) \<rightarrow>\<^sub>r root\<close>
        unfolding CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        by (meson bind_pure_returns_result_I bind_returns_result_E3 local.get_root_node_pure)
      then show ?thesis
        using \<open>known_ptr ptr\<close>
        apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
            CD.a_get_owner_document_tups_def known_ptr_impl)[1]
         apply(split invoke_splits, ((rule conjI | rule impI)+)?)+
             apply(drule(1) known_ptr_not_shadow_root_ptr[folded known_ptr_impl])
             apply(drule(1) known_ptr_not_document_ptr[folded known_ptr_impl])
             apply(drule(1)  known_ptr_not_character_data_ptr)
             apply(drule(1)  known_ptr_not_element_ptr)
             apply(simp add: NodeClass.known_ptr_defs)
        using \<open>cast child |\<in>| object_ptr_kinds h\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close> False \<open>\<not> is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr\<close>
            apply(auto simp add: node_ptr[symmetric] intro!: bind_pure_returns_result_I split: )[1]
        using \<open>cast child |\<in>| object_ptr_kinds h\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close> False \<open>\<not> is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr\<close>
           apply(auto simp add: node_ptr[symmetric] intro!: bind_pure_returns_result_I split: )[1]
        using \<open>cast child |\<in>| object_ptr_kinds h\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close> False \<open>\<not> is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr\<close>
          apply(auto simp add: node_ptr[symmetric] intro!: bind_pure_returns_result_I split: )[1]
        using \<open>cast child |\<in>| object_ptr_kinds h\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close> False \<open>\<not> is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr\<close>
         apply(auto simp add: node_ptr[symmetric] intro!: bind_pure_returns_result_I split: )[1]
        using \<open>cast child |\<in>| object_ptr_kinds h\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close> False \<open>\<not> is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr\<close>
        apply(auto simp add: node_ptr[symmetric] intro!: bind_pure_returns_result_I split: )[1]
        apply(split invoke_splits, ((rule conjI | rule impI)+)?)+
        by(auto simp add: node_ptr[symmetric] intro!: bind_pure_returns_result_I dest!: is_OK_returns_result_I)
    qed
  qed
  then show ?thesis
    using \<open>is_character_data_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child) \<or> is_element_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child)\<close>
    using \<open>cast child |\<in>| object_ptr_kinds h\<close>
    by(auto simp add: get_owner_document_def[of "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r child"]
        a_get_owner_document_tups_def CD.a_get_owner_document_tups_def split: invoke_splits)
qed

lemma get_owner_document_rel:
  assumes "heap_is_wellformed h"  "known_ptrs h" "type_wf h"
  assumes "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
  assumes "ptr \<noteq> cast owner_document"
  shows "(cast owner_document, ptr) \<in> (parent_child_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
proof -
  have "ptr |\<in>| object_ptr_kinds h"
    using assms
    by (meson is_OK_returns_result_I local.get_owner_document_ptr_in_heap)
  then
  have "known_ptr ptr"
    using known_ptrs_known_ptr[OF assms(2)] by simp
  have "is_node_ptr_kind ptr"
  proof (rule ccontr)
    assume "\<not> is_node_ptr_kind ptr"
    then
    show False
      using assms(4) \<open>known_ptr ptr\<close>
      apply(auto simp add: known_ptr_impl get_owner_document_def a_get_owner_document_tups_def
          CD.a_get_owner_document_tups_def)[1]
      apply(split invoke_splits)+
          apply(drule(1) known_ptr_not_shadow_root_ptr)
          apply(drule(1) known_ptr_not_document_ptr)
          apply(drule(1)  known_ptr_not_character_data_ptr)
          apply(drule(1)  known_ptr_not_element_ptr)
          apply(simp add: NodeClass.known_ptr_defs)
      using \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(5)
      by(auto simp add: CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
          elim!: bind_returns_result_E2 split: if_splits option.splits)
  qed
  then obtain node_ptr where node_ptr: "ptr = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr"
    by (metis node_ptr_casts_commute3)
  then have "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document"
    using assms(4) \<open>known_ptr ptr\<close>
    apply(auto simp add: known_ptr_impl get_owner_document_def a_get_owner_document_tups_def
        CD.a_get_owner_document_tups_def)[1]
    apply(split invoke_splits)+
        apply(drule(1) known_ptr_not_shadow_root_ptr)
        apply(drule(1) known_ptr_not_document_ptr)
        apply(drule(1)  known_ptr_not_character_data_ptr)
        apply(drule(1)  known_ptr_not_element_ptr)
        apply(simp add: NodeClass.known_ptr_defs)
    using \<open>ptr |\<in>| object_ptr_kinds h\<close>
    by (auto simp add: is_document_ptr_kind_none)
  then obtain root where root: "h \<turnstile> get_root_node (cast node_ptr) \<rightarrow>\<^sub>r root"
    by(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2)
  then have "root |\<in>| object_ptr_kinds h"
    using assms(1) assms(2) assms(3) local.get_root_node_root_in_heap by blast
  then
  have "known_ptr root"
    using \<open>known_ptrs h\<close> local.known_ptrs_known_ptr by blast

  have "(root, cast node_ptr) \<in> (parent_child_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
    using root
    by (simp add: assms(1) assms(2) assms(3) in_rtrancl_UnI local.get_root_node_parent_child_rel)

  show ?thesis
  proof (cases "is_document_ptr_kind root")
    case True
    then have "root = cast owner_document"
      using \<open>h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document\<close> root
      by(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def is_document_ptr_kind_def
          dest!: bind_returns_result_E3[rotated, OF root, rotated] split: option.splits)
    then have "(root, cast node_ptr) \<in> (parent_child_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
      using assms(1) assms(2) assms(3) in_rtrancl_UnI local.get_root_node_parent_child_rel root
      by blast
    then show ?thesis
      using \<open>root = cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r owner_document\<close> node_ptr by blast
  next
    case False
    then obtain root_node where root_node: "root = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_node"
      using assms(2)   \<open>root |\<in>| object_ptr_kinds h\<close>
      by(auto simp add: known_ptr_impl ShadowRootClass.known_ptr_defs DocumentClass.known_ptr_defs
          CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
          dest!: known_ptrs_known_ptr split: option.splits)
    have "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_node () \<rightarrow>\<^sub>r owner_document"
      using \<open>h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document\<close> root  False
      apply(auto simp add: root_node CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2
          dest!: bind_returns_result_E3[rotated, OF root, rotated] split: option.splits
          intro!: bind_pure_returns_result_I filter_M_pure_I bind_pure_I)[1]
      by (simp add: assms(1) assms(2) assms(3) local.get_root_node_no_parent local.get_root_node_same_no_parent)
    then
    have "h \<turnstile> get_owner_document root \<rightarrow>\<^sub>r owner_document"
      using \<open>known_ptr root\<close>
      apply(auto simp add: get_owner_document_def CD.a_get_owner_document_tups_def
          a_get_owner_document_tups_def known_ptr_impl)[1]
      apply(split invoke_splits, ((rule conjI | rule impI)+)?)+
          apply(drule(1) known_ptr_not_shadow_root_ptr[folded known_ptr_impl])
          apply(drule(1) known_ptr_not_document_ptr)
          apply(drule(1)  known_ptr_not_character_data_ptr)
          apply(drule(1)  known_ptr_not_element_ptr)
          apply(simp add: NodeClass.known_ptr_defs)
      using \<open>h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document\<close> root
        False \<open>root |\<in>| object_ptr_kinds h\<close>
         apply(auto intro!: bind_pure_returns_result_I split: option.splits)[1]
      using \<open>h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document\<close> root
        False \<open>root |\<in>| object_ptr_kinds h\<close>
        apply(auto intro!: bind_pure_returns_result_I split: option.splits)[1]
      using \<open>h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document\<close> root
        False \<open>root |\<in>| object_ptr_kinds h\<close>
       apply(auto simp add: root_node intro!: bind_pure_returns_result_I split: option.splits)[1]
      using \<open>h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document\<close> root
        False \<open>root |\<in>| object_ptr_kinds h\<close>
      apply(auto simp add: root_node intro!: bind_pure_returns_result_I split: option.splits)[1]
      done
    have "\<not> (\<exists>parent\<in>fset (object_ptr_kinds h). root_node \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r)"
      using root_node
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) local.child_parent_dual
          local.get_child_nodes_ok local.get_root_node_same_no_parent local.known_ptrs_known_ptr
          notin_fset option.distinct(1) returns_result_eq returns_result_select_result root)
    have "root_node |\<in>| node_ptr_kinds h"
      using assms(1) assms(2) assms(3) local.get_root_node_root_in_heap node_ptr_kinds_commutes root root_node
      by blast
    then have "\<exists>document_ptr\<in>fset (document_ptr_kinds h). root_node \<in> set |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
      using \<open>\<not> (\<exists>parent\<in>fset (object_ptr_kinds h). root_node \<in> set |h \<turnstile> get_child_nodes parent|\<^sub>r)\<close> assms(1)
        local.heap_is_wellformed_children_disc_nodes by blast
    then obtain disc_nodes document_ptr where "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
      and "root_node \<in> set disc_nodes"
      by (meson assms(3) local.get_disconnected_nodes_ok notin_fset returns_result_select_result)
    then have "document_ptr |\<in>| document_ptr_kinds h"
      by (meson is_OK_returns_result_I local.get_disconnected_nodes_ptr_in_heap)
    then have "document_ptr = owner_document"
      by (metis \<open>h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes\<close>
          \<open>h \<turnstile> get_owner_document root \<rightarrow>\<^sub>r owner_document\<close> \<open>root_node \<in> set disc_nodes\<close> assms(1) assms(2)
          assms(3) local.get_owner_document_disconnected_nodes returns_result_eq root_node)
    then have "(cast owner_document, cast root_node) \<in> a_ptr_disconnected_node_rel h"
      apply(auto simp add: a_ptr_disconnected_node_rel_def)[1]
      using \<open>h \<turnstile> local.CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document\<close> assms(1)
        assms(2) assms(3) get_owner_document_owner_document_in_heap_node
      by (metis (no_types, lifting) \<open>h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes\<close>
          \<open>root_node \<in> set disc_nodes\<close> case_prodI mem_Collect_eq pair_imageI select_result_I2)
    moreover have "(cast root_node, cast node_ptr) \<in>
(parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
      by (metis assms(1) assms(2) assms(3) in_rtrancl_UnI local.get_root_node_parent_child_rel
          root root_node)
    ultimately show ?thesis
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) in_rtrancl_UnI
          local.get_root_node_parent_child_rel node_ptr r_into_rtrancl root root_node rtrancl_trans)
  qed
qed
end

interpretation i_get_owner_document_wf?: l_get_owner_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf get_disconnected_nodes get_disconnected_nodes_locs known_ptr get_child_nodes
  get_child_nodes_locs DocumentClass.known_ptr get_parent get_parent_locs DocumentClass.type_wf
  get_root_node get_root_node_locs CD.a_get_owner_document get_host get_host_locs get_owner_document
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs heap_is_wellformed
  parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_document get_disconnected_document_locs
  known_ptrs get_ancestors get_ancestors_locs
  by(auto simp add: l_get_owner_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def l_get_owner_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_get_owner_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


lemma get_owner_document_wf_is_l_get_owner_document_wf [instances]:
  "l_get_owner_document_wf heap_is_wellformed type_wf known_ptr known_ptrs get_disconnected_nodes
get_owner_document get_parent get_child_nodes"
  apply(auto simp add: l_get_owner_document_wf_def l_get_owner_document_wf_axioms_def instances)[1]
  using get_owner_document_disconnected_nodes apply fast
  using in_disconnected_nodes_no_parent apply fast
  using get_owner_document_owner_document_in_heap apply fast
  using get_owner_document_ok apply fast
  using get_owner_document_child_same apply (fast, fast)
  done

paragraph \<open>get\_owner\_document\<close>

locale l_get_owner_document_wf_get_root_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_owner_document\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_root_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_root_node_wf +
  l_get_owner_document_wf +
  assumes known_ptr_impl: "known_ptr = a_known_ptr"
begin

lemma get_root_node_document:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
  assumes "is_document_ptr_kind root"
  shows "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r the (cast root)"
proof -
  have "ptr |\<in>| object_ptr_kinds h"
    using assms(4)
    by (meson is_OK_returns_result_I local.get_root_node_ptr_in_heap)
  then have "known_ptr ptr"
    using assms(3) local.known_ptrs_known_ptr by blast
  {
    assume "is_document_ptr_kind ptr"
    then have "ptr = root"
      using assms(4)
      by(auto simp add: get_root_node_def get_ancestors_def elim!: bind_returns_result_E2
          split: option.splits)
    then have ?thesis
      using \<open>is_document_ptr_kind ptr\<close> \<open>known_ptr ptr\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close>
      apply(auto simp add: known_ptr_impl get_owner_document_def a_get_owner_document_tups_def
          CD.a_get_owner_document_tups_def)[1]
      apply(split invoke_splits, (rule conjI | rule impI)+)+
          apply(drule(1) known_ptr_not_shadow_root_ptr[folded known_ptr_impl])
          apply(drule(1) known_ptr_not_document_ptr[folded known_ptr_impl])
          apply(drule(1) known_ptr_not_character_data_ptr)
          apply(drule(1) known_ptr_not_element_ptr)
          apply(simp add: NodeClass.known_ptr_defs)
      by(auto simp add: CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
          intro!: bind_pure_returns_result_I split: option.splits)
  }
  moreover
  {
    assume "is_node_ptr_kind ptr"
    then have ?thesis
      using \<open>known_ptr ptr\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close>
      apply(auto simp add: known_ptr_impl get_owner_document_def a_get_owner_document_tups_def
          CD.a_get_owner_document_tups_def)[1]
      apply(split invoke_splits, (rule conjI | rule impI)+)+
          apply(drule(1) known_ptr_not_shadow_root_ptr[folded known_ptr_impl])
          apply(drule(1) known_ptr_not_document_ptr[folded known_ptr_impl])
          apply(drule(1) known_ptr_not_character_data_ptr)
          apply(drule(1) known_ptr_not_element_ptr)
          apply(simp add: NodeClass.known_ptr_defs)
         apply(auto split: option.splits)[1]
      using \<open>h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root\<close> assms(5)
      by(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def is_document_ptr_kind_def
          intro!: bind_pure_returns_result_I  split: option.splits)
  }
  ultimately
  show ?thesis
    using \<open>known_ptr ptr\<close>
    by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
        CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
        split: option.splits)
qed

lemma get_root_node_same_owner_document:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_root_node ptr \<rightarrow>\<^sub>r root"
  shows "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document \<longleftrightarrow> h \<turnstile> get_owner_document root \<rightarrow>\<^sub>r owner_document"
proof -
  have "ptr |\<in>| object_ptr_kinds h"
    by (meson assms(4) is_OK_returns_result_I local.get_root_node_ptr_in_heap)
  have "root |\<in>| object_ptr_kinds h"
    using assms(1) assms(2) assms(3) assms(4) local.get_root_node_root_in_heap by blast
  have "known_ptr ptr"
    using \<open>ptr |\<in>| object_ptr_kinds h\<close> assms(3) local.known_ptrs_known_ptr by blast
  have "known_ptr root"
    using \<open>root |\<in>| object_ptr_kinds h\<close> assms(3) local.known_ptrs_known_ptr by blast
  show ?thesis
  proof (cases "is_document_ptr_kind ptr")
    case True
    then
    have "ptr = root"
      using assms(4)
      apply(auto simp add: get_root_node_def elim!: bind_returns_result_E2)[1]
      by (metis document_ptr_casts_commute3 last_ConsL local.get_ancestors_not_node node_ptr_no_document_ptr_cast)
    then show ?thesis
      by auto
  next
    case False
    then have "is_node_ptr_kind ptr"
      using \<open>known_ptr ptr\<close>
      by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
          CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
          split: option.splits)
    then obtain node_ptr where node_ptr: "ptr = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr"
      by (metis node_ptr_casts_commute3)
    show ?thesis
    proof
      assume "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
      then have "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document"
        using node_ptr
        apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
            CD.a_get_owner_document_tups_def)[1]
        apply(split invoke_splits)+
            apply (meson invoke_empty is_OK_returns_result_I)
        by(auto  elim!: bind_returns_result_E2 split: option.splits)

      show "h \<turnstile> get_owner_document root \<rightarrow>\<^sub>r owner_document"
      proof (cases "is_document_ptr_kind root")
        case True
        then show ?thesis
        proof (cases "is_shadow_root_ptr root")
          case True
          then
          have "is_shadow_root_ptr root"
            using True \<open>known_ptr root\<close>
            by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
                CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
                split: option.splits)
          have "root = cast owner_document"
            using \<open>is_document_ptr_kind root\<close>
            by (smt \<open>h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document\<close> assms(1) assms(2) assms(3) assms(4)
                document_ptr_casts_commute3 get_root_node_document returns_result_eq)
          then show ?thesis
            apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
                CD.a_get_owner_document_tups_def)[1]
            apply(split invoke_splits, (rule conjI | rule impI)+)+
            using \<open>is_shadow_root_ptr root\<close> apply blast
            using \<open>root |\<in>| object_ptr_kinds h\<close>
               apply(simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
                is_node_ptr_kind_none)
               apply (metis \<open>h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document\<close> assms(1) assms(2) assms(3)
                case_optionE document_ptr_kinds_def is_shadow_root_ptr_kind_none l_get_owner_document_wf.get_owner_document_owner_document_in_heap local.l_get_owner_document_wf_axioms not_None_eq return_bind shadow_root_ptr_casts_commute3 shadow_root_ptr_kinds_commutes shadow_root_ptr_kinds_def)
            using \<open>root |\<in>| object_ptr_kinds h\<close> document_ptr_kinds_commutes
              apply(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
                is_node_ptr_kind_none intro!: bind_pure_returns_result_I)[1]
            using \<open>root |\<in>| object_ptr_kinds h\<close> document_ptr_kinds_commutes
             apply(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
                is_node_ptr_kind_none intro!: bind_pure_returns_result_I)[1]
            using \<open>root |\<in>| object_ptr_kinds h\<close> document_ptr_kinds_commutes
            apply(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
                is_node_ptr_kind_none intro!: bind_pure_returns_result_I)[1]
            done
        next
          case False
          then
          have "is_document_ptr root"
            using True \<open>known_ptr root\<close>
            by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
                CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs split: option.splits)
          have "root = cast owner_document"
            using True
            by (smt \<open>h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document\<close> assms(1) assms(2) assms(3) assms(4)
                document_ptr_casts_commute3 get_root_node_document returns_result_eq)
          then show ?thesis
            apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
                CD.a_get_owner_document_tups_def)[1]
            apply(split invoke_splits, (rule conjI | rule impI)+)+
            using \<open>is_document_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root\<close> apply blast
            using \<open>root |\<in>| object_ptr_kinds h\<close>
               apply(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
                is_node_ptr_kind_none)[1]
               apply (metis \<open>h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document\<close> assms(1) assms(2) assms(3)
                case_optionE document_ptr_kinds_def is_shadow_root_ptr_kind_none
                l_get_owner_document_wf.get_owner_document_owner_document_in_heap local.l_get_owner_document_wf_axioms
                not_None_eq return_bind shadow_root_ptr_casts_commute3 shadow_root_ptr_kinds_commutes shadow_root_ptr_kinds_def)
            using \<open>root |\<in>| object_ptr_kinds h\<close> document_ptr_kinds_commutes
              apply(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
                is_node_ptr_kind_none intro!: bind_pure_returns_result_I)[1]
            using \<open>root |\<in>| object_ptr_kinds h\<close> document_ptr_kinds_commutes
             apply(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
                is_node_ptr_kind_none intro!: bind_pure_returns_result_I)[1]
            using \<open>root |\<in>| object_ptr_kinds h\<close> document_ptr_kinds_commutes
            apply(auto simp add: a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
                is_node_ptr_kind_none intro!: bind_pure_returns_result_I)[1]
            done
        qed
      next
        case False
        then have "is_node_ptr_kind root"
          using \<open>known_ptr root\<close>
          by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
              CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
              split: option.splits)
        then obtain root_node_ptr where root_node_ptr: "root = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_node_ptr"
          by (metis node_ptr_casts_commute3)
        then have "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_node_ptr () \<rightarrow>\<^sub>r owner_document"
          using \<open>h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document\<close> assms(4)
          apply(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2
              intro!: bind_pure_returns_result_I filter_M_pure_I bind_pure_I split: option.splits)[1]
           apply (metis assms(1) assms(2) assms(3) local.get_root_node_no_parent
              local.get_root_node_same_no_parent node_ptr returns_result_eq)
          using \<open>is_node_ptr_kind root\<close> node_ptr returns_result_eq by fastforce
        then show ?thesis
          apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
              CD.a_get_owner_document_tups_def)[1]
          apply(split invoke_splits, (rule conjI | rule impI)+)+
          using \<open>is_node_ptr_kind root\<close> \<open>known_ptr root\<close>
              apply(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
              CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
              split: option.splits)[1]
          using \<open>is_node_ptr_kind root\<close> \<open>known_ptr root\<close>
             apply(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
              CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
              split: option.splits)[1]
          using \<open>is_node_ptr_kind root\<close> \<open>known_ptr root\<close>
            apply(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
              CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
              split: option.splits)[1]
          using \<open>root |\<in>| object_ptr_kinds h\<close>
          by(auto simp add: root_node_ptr)
      qed
    next
      assume "h \<turnstile> get_owner_document root \<rightarrow>\<^sub>r owner_document"
      show "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
      proof (cases "is_document_ptr_kind root")
        case True
        have "root = cast owner_document"
          using \<open>h \<turnstile> get_owner_document root \<rightarrow>\<^sub>r owner_document\<close>
          apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
              CD.a_get_owner_document_tups_def)[1]
          apply(split invoke_splits)+
              apply (meson invoke_empty is_OK_returns_result_I)
             apply(auto simp add: True CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
              a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2 split: if_splits option.splits)[1]
            apply(auto simp add: True CD.a_get_owner_document\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
              a_get_owner_document\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2 split: if_splits option.splits)[1]
           apply (metis True cast_document_ptr_not_node_ptr(2) is_document_ptr_kind_obtains
              is_node_ptr_kind_none node_ptr_casts_commute3 option.case_eq_if)
          by (metis True cast_document_ptr_not_node_ptr(1) document_ptr_casts_commute3
              is_node_ptr_kind_none node_ptr_casts_commute3 option.case_eq_if)
        then show ?thesis
          using assms(1) assms(2) assms(3) assms(4) get_root_node_document
          by fastforce
      next
        case False
        then have "is_node_ptr_kind root"
          using \<open>known_ptr root\<close>
          by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
              CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs split: option.splits)
        then obtain root_node_ptr where root_node_ptr: "root = cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_node_ptr"
          by (metis node_ptr_casts_commute3)
        then have "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r root_node_ptr () \<rightarrow>\<^sub>r owner_document"
          using \<open>h \<turnstile> get_owner_document root \<rightarrow>\<^sub>r owner_document\<close>
          apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
              CD.a_get_owner_document_tups_def)[1]
          apply(split invoke_splits)+
              apply (meson invoke_empty is_OK_returns_result_I)
          by(auto simp add: is_document_ptr_kind_none elim!: bind_returns_result_E2)
        then have "h \<turnstile> CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr () \<rightarrow>\<^sub>r owner_document"
          apply(auto simp add: CD.a_get_owner_document\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def elim!: bind_returns_result_E2
              intro!: bind_pure_returns_result_I filter_M_pure_I bind_pure_I split: option.splits)[1]
          using assms(1) assms(2) assms(3) assms(4) local.get_root_node_no_parent
            local.get_root_node_same_no_parent node_ptr returns_result_eq root_node_ptr
          by fastforce+
        then show ?thesis
          apply(auto simp add: get_owner_document_def a_get_owner_document_tups_def
              CD.a_get_owner_document_tups_def)[1]
          apply(split invoke_splits, (rule conjI | rule impI)+)+
          using node_ptr  \<open>known_ptr ptr\<close> \<open>ptr |\<in>| object_ptr_kinds h\<close>

          by(auto simp add: known_ptr_impl known_ptr_defs DocumentClass.known_ptr_defs
              CharacterDataClass.known_ptr_defs ElementClass.known_ptr_defs NodeClass.known_ptr_defs
              intro!: bind_pure_returns_result_I split: option.splits)
      qed
    qed
  qed
qed
end

interpretation i_get_owner_document_wf_get_root_node_wf?: l_get_owner_document_wf_get_root_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  DocumentClass.known_ptr get_parent get_parent_locs DocumentClass.type_wf get_disconnected_nodes
  get_disconnected_nodes_locs get_root_node get_root_node_locs CD.a_get_owner_document
  get_host get_host_locs get_owner_document get_child_nodes get_child_nodes_locs type_wf known_ptr
  known_ptrs get_ancestors get_ancestors_locs heap_is_wellformed parent_child_rel
  by(auto simp add: l_get_owner_document_wf_get_root_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def
      l_get_owner_document_wf_get_root_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms_def instances)
declare l_get_owner_document_wf_get_root_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma get_owner_document_wf_get_root_node_wf_is_l_get_owner_document_wf_get_root_node_wf [instances]:
  "l_get_owner_document_wf_get_root_node_wf heap_is_wellformed type_wf known_ptr known_ptrs get_root_node get_owner_document"
  apply(auto simp add: l_get_owner_document_wf_get_root_node_wf_def l_get_owner_document_wf_get_root_node_wf_axioms_def instances)[1]
  using get_root_node_document apply blast
  using get_root_node_same_owner_document apply (blast, blast)
  done


subsubsection \<open>remove\_child\<close>

locale l_remove_child_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_set_disconnected_nodes_get_disconnected_nodes +
  l_get_child_nodes +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_owner_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_set_child_nodes_get_shadow_root +
  l_set_disconnected_nodes_get_shadow_root +
  l_set_child_nodes_get_tag_name +
  l_set_disconnected_nodes_get_tag_name +
  CD: l_remove_child_wf2\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma remove_child_preserves_type_wf:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'"
  shows "type_wf h'"
  using CD.remove_child_heap_is_wellformed_preserved(1) assms
  unfolding heap_is_wellformed_def
  by auto

lemma remove_child_preserves_known_ptrs:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'"
  shows "known_ptrs h'"
  using CD.remove_child_heap_is_wellformed_preserved(2) assms
  unfolding heap_is_wellformed_def
  by auto


lemma remove_child_heap_is_wellformed_preserved:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove_child ptr child \<rightarrow>\<^sub>h h'"
  shows "heap_is_wellformed h'"
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

  have "heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M h'"
    using CD.remove_child_heap_is_wellformed_preserved(3) assms
    unfolding heap_is_wellformed_def
    by auto

  have "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document"
    using owner_document children_h child_in_children_h
    using local.get_owner_document_child_same assms by blast

  have shadow_root_eq: "\<And>ptr' shadow_root_ptr_opt. h \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt =
h' \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt"
    using get_shadow_root_reads remove_child_writes assms(4)
    apply(rule reads_writes_preserved)
    by(auto simp add: remove_child_locs_def set_child_nodes_get_shadow_root
        set_disconnected_nodes_get_shadow_root)
  then
  have shadow_root_eq2: "\<And>ptr'. |h \<turnstile> get_shadow_root ptr'|\<^sub>r = |h' \<turnstile> get_shadow_root ptr'|\<^sub>r"
    by (meson select_result_eq)

  have tag_name_eq: "\<And>ptr' tag. h \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag = h' \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag"
    using get_tag_name_reads remove_child_writes assms(4)
    apply(rule reads_writes_preserved)
    by(auto simp add: remove_child_locs_def set_child_nodes_get_tag_name
        set_disconnected_nodes_get_tag_name)
  then
  have tag_name_eq2: "\<And>ptr'. |h \<turnstile> get_tag_name ptr'|\<^sub>r = |h' \<turnstile> get_tag_name ptr'|\<^sub>r"
    by (meson select_result_eq)

  have object_ptr_kinds_eq: "object_ptr_kinds h = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
          OF remove_child_writes assms(4)])
    unfolding remove_child_locs_def
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)

  have document_ptr_kinds_eq: "document_ptr_kinds h = document_ptr_kinds h'"
    using object_ptr_kinds_eq
    by(auto simp add: document_ptr_kinds_def document_ptr_kinds_def)

  have shadow_root_ptr_kinds_eq: "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    using object_ptr_kinds_eq
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  have element_ptr_kinds_eq: "element_ptr_kinds h = element_ptr_kinds h'"
    using object_ptr_kinds_eq
    by(auto simp add: element_ptr_kinds_def node_ptr_kinds_def)

  have "parent_child_rel h' \<subseteq> parent_child_rel h"
    using \<open>heap_is_wellformed h\<close> heap_is_wellformed_def
    using CD.remove_child_parent_child_rel_subset
    using \<open>known_ptrs h\<close> \<open>type_wf h\<close> assms(4)
    by simp

  have "known_ptr ptr"
    using assms(3)
    using children_h get_child_nodes_ptr_in_heap local.known_ptrs_known_ptr by blast
  have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'",
        OF set_disconnected_nodes_writes h2]
    using set_disconnected_nodes_types_preserved \<open>type_wf h\<close>
    by(auto simp add: reflp_def transp_def)

  have children_eq:
    "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children =
h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    apply(rule reads_writes_preserved[OF get_child_nodes_reads remove_child_writes assms(4)])
    unfolding remove_child_locs_def
    using set_disconnected_nodes_get_child_nodes set_child_nodes_get_child_nodes_different_pointers
    by fast
  then have children_eq2:
    "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h"
    apply(rule reads_writes_separate_forwards[OF get_child_nodes_reads
          set_disconnected_nodes_writes h2 children_h] )
    by (simp add: set_disconnected_nodes_get_child_nodes)

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

  have disconnected_nodes_eq: "\<And>ptr' disc_nodes. ptr' \<noteq> owner_document \<Longrightarrow>
h \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes = h2 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes"
    using local.get_disconnected_nodes_reads set_disconnected_nodes_writes h2
    apply(rule reads_writes_preserved)
    by (metis local.set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then
  have disconnected_nodes_eq2: "\<And>ptr'. ptr' \<noteq> owner_document \<Longrightarrow>
|h \<turnstile> get_disconnected_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r"
    by (meson select_result_eq)
  have "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r child # disconnected_nodes_h"
    using h2 local.set_disconnected_nodes_get_disconnected_nodes
    by blast

  have disconnected_nodes_eq_h2:
    "\<And>ptr' disc_nodes. h2 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes = h' \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes"
    using local.get_disconnected_nodes_reads set_child_nodes_writes h'
    apply(rule reads_writes_preserved)
    using local.set_child_nodes_get_disconnected_nodes by blast
  then
  have disconnected_nodes_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r = |h' \<turnstile> get_disconnected_nodes ptr'|\<^sub>r"
    by (meson select_result_eq)

  have "a_host_shadow_root_rel h' = a_host_shadow_root_rel h"
    by(auto simp add: a_host_shadow_root_rel_def shadow_root_eq2 element_ptr_kinds_eq)
  moreover
  have "(ptr, cast child) \<in> parent_child_rel h"
    using child_in_children_h children_h local.CD.parent_child_rel_child by blast
  moreover
  have "a_ptr_disconnected_node_rel h' = insert (cast owner_document, cast child) (a_ptr_disconnected_node_rel h)"
    using \<open>h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r child # disconnected_nodes_h\<close> disconnected_nodes_eq2 disconnected_nodes_h
    apply(auto simp add: a_ptr_disconnected_node_rel_def disconnected_nodes_eq2_h2[symmetric] document_ptr_kinds_eq[symmetric])[1]
      apply(case_tac "aa = owner_document")
       apply(auto)[1]
      apply(auto)[1]
     apply (metis (no_types, lifting) assms(4) case_prodI disconnected_nodes_eq_h2 h2
        is_OK_returns_heap_I local.remove_child_in_disconnected_nodes
        local.set_disconnected_nodes_ptr_in_heap mem_Collect_eq owner_document pair_imageI select_result_I2)
    by (metis (no_types, lifting) case_prodI list.set_intros(2) mem_Collect_eq pair_imageI select_result_I2)
  then
  have "a_ptr_disconnected_node_rel h' = a_ptr_disconnected_node_rel h \<union> {(cast owner_document, cast child)}"
    by auto
  moreover have "acyclic (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using assms(1) local.heap_is_wellformed_def by blast
  moreover have "parent_child_rel h' = parent_child_rel h - {(ptr, cast child)}"
    apply(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq children_eq2)[1]
      apply (metis (no_types, lifting) children_eq2 children_h children_h' notin_set_remove1 select_result_I2)
    using \<open>h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r child # disconnected_nodes_h\<close>
      \<open>heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M h'\<close> disconnected_nodes_eq_h2 local.CD.distinct_lists_no_parent
      local.CD.heap_is_wellformed_def apply auto[1]
    by (metis (no_types, lifting) children_eq2 children_h children_h' in_set_remove1 select_result_I2)

  moreover have "(cast owner_document, ptr) \<in> (parent_child_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
    using \<open>h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document\<close> get_owner_document_rel
    using assms(1) assms(2) assms(3) by blast
  then have "(cast owner_document, ptr) \<in> (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
    by (metis (no_types, lifting) in_rtrancl_UnI inf_sup_aci(5) inf_sup_aci(7))
  ultimately
  have "acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')"
    by (smt Un_assoc Un_insert_left Un_insert_right acyclic_insert insert_Diff_single
        insert_absorb2 mk_disjoint_insert prod.inject rtrancl_Un_separator_converseE rtrancl_trans
        singletonD sup_bot.comm_neutral)

  show ?thesis
    using \<open>heap_is_wellformed h\<close>
    using \<open>heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M h'\<close>
    using \<open>acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')\<close>
    apply(auto simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def
        host_shadow_root_rel_def a_all_ptrs_in_heap_def a_distinct_lists_def a_shadow_root_valid_def)[1]
    by(auto simp add: object_ptr_kinds_eq element_ptr_kinds_eq shadow_root_ptr_kinds_eq
        shadow_root_eq shadow_root_eq2 tag_name_eq tag_name_eq2)
qed

lemma remove_preserves_type_wf:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove child \<rightarrow>\<^sub>h h'"
  shows "type_wf h'"
  using CD.remove_heap_is_wellformed_preserved(1) assms
  unfolding heap_is_wellformed_def
  by auto

lemma remove_preserves_known_ptrs:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove child \<rightarrow>\<^sub>h h'"
  shows "known_ptrs h'"
  using CD.remove_heap_is_wellformed_preserved(2) assms
  unfolding heap_is_wellformed_def
  by auto


lemma remove_heap_is_wellformed_preserved:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> remove child \<rightarrow>\<^sub>h h'"
  shows "heap_is_wellformed h'"
  using assms
  by(auto simp add: remove_def elim!: bind_returns_heap_E2
      intro: remove_child_heap_is_wellformed_preserved split: option.splits)

lemma remove_child_removes_child:
  "heap_is_wellformed h \<Longrightarrow> h \<turnstile> remove_child ptr' child \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children
    \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h
    \<Longrightarrow> child \<notin> set children"
  using CD.remove_child_removes_child local.heap_is_wellformed_def by blast
lemma remove_child_removes_first_child:
  "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r node_ptr # children \<Longrightarrow>
h \<turnstile> remove_child ptr node_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  using CD.remove_child_removes_first_child local.heap_is_wellformed_def by blast
lemma remove_removes_child:
  "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r node_ptr # children \<Longrightarrow>
h \<turnstile> remove node_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
  using CD.remove_removes_child local.heap_is_wellformed_def by blast
lemma remove_for_all_empty_children:
  "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow>
h \<turnstile> forall_M remove children \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r []"
  using CD.remove_for_all_empty_children local.heap_is_wellformed_def by blast

end

interpretation i_remove_child_wf2?: l_remove_child_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs known_ptr get_child_nodes get_child_nodes_locs get_shadow_root
  get_shadow_root_locs get_tag_name get_tag_name_locs heap_is_wellformed parent_child_rel
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document get_disconnected_document_locs
  DocumentClass.known_ptr get_parent get_parent_locs DocumentClass.type_wf get_root_node get_root_node_locs
  CD.a_get_owner_document get_owner_document known_ptrs get_ancestors get_ancestors_locs set_child_nodes
  set_child_nodes_locs remove_child remove_child_locs remove
  by(auto simp add: l_remove_child_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_remove_child_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


lemma remove_child_wf2_is_l_remove_child_wf2 [instances]:
  "l_remove_child_wf2 type_wf known_ptr known_ptrs remove_child heap_is_wellformed get_child_nodes remove"
  apply(auto simp add: l_remove_child_wf2_def l_remove_child_wf2_axioms_def instances)[1]
  using remove_child_preserves_type_wf apply fast
  using remove_child_preserves_known_ptrs apply fast
  using remove_child_heap_is_wellformed_preserved apply (fast)
  using remove_preserves_type_wf apply fast
  using remove_preserves_known_ptrs apply fast
  using remove_heap_is_wellformed_preserved apply (fast)
  using remove_child_removes_child apply fast
  using remove_child_removes_first_child apply fast
  using remove_removes_child apply fast
  using remove_for_all_empty_children apply fast
  done



subsubsection \<open>adopt\_node\<close>

locale l_adopt_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  CD: l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ _ _ _ _ _ _ _ _ adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma adopt_node_removes_first_child: "heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h
                         \<Longrightarrow> h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h'
                         \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r node # children
                         \<Longrightarrow> h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
  by (smt CD.adopt_node_removes_first_child bind_returns_heap_E error_returns_heap
      l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M.adopt_node_def local.CD.adopt_node_impl local.get_ancestors_di_pure
      local.l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms pure_returns_heap_eq)
lemma adopt_node_document_in_heap: "heap_is_wellformed h \<Longrightarrow> known_ptrs h \<Longrightarrow> type_wf h
                        \<Longrightarrow> h \<turnstile> ok (adopt_node owner_document node)
                        \<Longrightarrow> owner_document |\<in>| document_ptr_kinds h"
  by (metis (no_types, lifting) bind_returns_heap_E document_ptr_kinds_commutes is_OK_returns_heap_E
      is_OK_returns_result_I local.adopt_node_def local.get_ancestors_di_ptr_in_heap)
end

locale l_adopt_node_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes +
  l_get_disconnected_nodes +
  l_set_child_nodes_get_shadow_root +
  l_set_disconnected_nodes_get_shadow_root +
  l_set_child_nodes_get_tag_name +
  l_set_disconnected_nodes_get_tag_name +
  l_get_owner_document  +
  l_remove_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M+
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_root_node +
  l_set_disconnected_nodes_get_child_nodes +
  l_get_owner_document_wf +
  l_remove_child_wf2 +
  l_adopt_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_parent_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_disconnected_document +
  l_get_ancestors_di\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_get_ancestors_di_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma adopt_node_removes_child:
  assumes wellformed: "heap_is_wellformed h"
    and adopt_node: "h \<turnstile> adopt_node owner_document node_ptr \<rightarrow>\<^sub>h h2"
    and children: "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "node_ptr \<notin> set children"
proof -
  obtain old_document parent_opt h' where
    old_document: "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r old_document" and
    parent_opt: "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r parent_opt" and
    h': "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> remove_child parent node_ptr | None \<Rightarrow> return () ) \<rightarrow>\<^sub>h h'"
    using adopt_node
    by(auto simp add: adopt_node_def CD.adopt_node_def elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_ancestors_di_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated]
        split: if_splits)

  then have "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
    using adopt_node
    apply(auto simp add: adopt_node_def CD.adopt_node_def
        dest!: bind_returns_heap_E3[rotated, OF old_document, rotated]
        bind_returns_heap_E3[rotated, OF parent_opt, rotated]
        elim!: bind_returns_heap_E2[rotated, OF get_ancestors_di_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated]
        bind_returns_heap_E4[rotated, OF h', rotated] split: if_splits)[1]
     apply(auto split: if_splits elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_ancestors_di_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated])[1]
     apply (simp add: set_disconnected_nodes_get_child_nodes children
        reads_writes_preserved[OF get_child_nodes_reads set_disconnected_nodes_writes])
    using children by blast
  show ?thesis
  proof(insert parent_opt h', induct parent_opt)
    case None
    then show ?case
      using child_parent_dual wellformed known_ptrs type_wf \<open>h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children\<close>
        returns_result_eq by fastforce
  next
    case (Some option)
    then show ?case
      using remove_child_removes_child \<open>h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children\<close> known_ptrs type_wf wellformed
      by auto
  qed
qed

lemma adopt_node_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> adopt_node document_ptr child \<rightarrow>\<^sub>h h'"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "heap_is_wellformed h'"
proof -
  obtain old_document parent_opt h2 ancestors where
    "h \<turnstile> get_ancestors_di (cast document_ptr) \<rightarrow>\<^sub>r ancestors" and
    "cast child \<notin>  set ancestors" and
    old_document: "h \<turnstile> get_owner_document (cast child) \<rightarrow>\<^sub>r old_document" and
    parent_opt: "h \<turnstile> get_parent child \<rightarrow>\<^sub>r parent_opt" and
    h2: "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> remove_child parent child | None \<Rightarrow> return ()) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> (if document_ptr \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 child old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes document_ptr;
        set_disconnected_nodes document_ptr (child # disc_nodes)
      } else do {
        return ()
      }) \<rightarrow>\<^sub>h h'"
    using assms(2)
    apply(auto simp add:  adopt_node_def[unfolded CD.adopt_node_def] elim!: bind_returns_heap_E
        dest!: pure_returns_heap_eq[rotated, OF get_ancestors_di_pure])[1]
    apply(split if_splits)
    by(auto simp add:  elim!: bind_returns_heap_E
        dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure]
        pure_returns_heap_eq[rotated, OF get_parent_pure])

  have object_ptr_kinds_h_eq3: "object_ptr_kinds h = object_ptr_kinds h2"
    using h2 apply(simp split: option.splits)
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF remove_child_writes])
    using remove_child_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h: "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    unfolding object_ptr_kinds_M_defs by simp
  then have object_ptr_kinds_eq_h: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq_h: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast

  have wellformed_h2: "heap_is_wellformed h2"
    using h2 remove_child_heap_is_wellformed_preserved known_ptrs type_wf
    by (metis (no_types, lifting) assms(1) option.case_eq_if pure_returns_heap_eq return_pure)
  then show "heap_is_wellformed h'"
  proof(cases "document_ptr = old_document")
    case True
    then show "heap_is_wellformed h'"
      using h' wellformed_h2 by auto
  next
    case False
    then obtain h3 old_disc_nodes disc_nodes_document_ptr_h3 where
      docs_neq: "document_ptr \<noteq> old_document" and
      old_disc_nodes: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r old_disc_nodes" and
      h3: "h2 \<turnstile> set_disconnected_nodes old_document (remove1 child old_disc_nodes) \<rightarrow>\<^sub>h h3" and
      disc_nodes_document_ptr_h3: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_document_ptr_h3" and
      h': "h3 \<turnstile> set_disconnected_nodes document_ptr (child # disc_nodes_document_ptr_h3) \<rightarrow>\<^sub>h h'"
      using h'
      by(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )

    have object_ptr_kinds_h2_eq3: "object_ptr_kinds h2 = object_ptr_kinds h3"
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF set_disconnected_nodes_writes h3])
      using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
      by (auto simp add: reflp_def transp_def)
    then have object_ptr_kinds_M_eq_h2: "\<And>ptrs. h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
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
    have children_eq_h2: "\<And>ptr children. h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
      using get_child_nodes_reads set_disconnected_nodes_writes h3
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_child_nodes)
    then have children_eq2_h2: "\<And>ptr. |h2 \<turnstile> get_child_nodes ptr|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr|\<^sub>r"
      using select_result_eq by force

    have object_ptr_kinds_h3_eq3: "object_ptr_kinds h3 = object_ptr_kinds h'"
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF set_disconnected_nodes_writes h'])
      using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
      by (auto simp add: reflp_def transp_def)
    then have object_ptr_kinds_M_eq_h3: "\<And>ptrs. h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
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
    have children_eq_h3: "\<And>ptr children. h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
      using get_child_nodes_reads set_disconnected_nodes_writes h'
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_child_nodes)
    then have children_eq2_h3: "\<And>ptr. |h3 \<turnstile> get_child_nodes ptr|\<^sub>r = |h' \<turnstile> get_child_nodes ptr|\<^sub>r"
      using select_result_eq by force

    have disconnected_nodes_eq_h2:
      "\<And>doc_ptr disc_nodes. old_document \<noteq> doc_ptr \<Longrightarrow>
h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
      using get_disconnected_nodes_reads set_disconnected_nodes_writes h3
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
    then have disconnected_nodes_eq2_h2:
      "\<And>doc_ptr. old_document \<noteq> doc_ptr \<Longrightarrow>
|h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
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

    have disconnected_nodes_eq_h3:
      "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr \<Longrightarrow>
h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
      using get_disconnected_nodes_reads set_disconnected_nodes_writes h'
      apply(rule reads_writes_preserved)
      by (simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
    then have disconnected_nodes_eq2_h3:
      "\<And>doc_ptr. document_ptr \<noteq> doc_ptr \<Longrightarrow>
|h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
      using select_result_eq by force
    have disc_nodes_document_ptr_h2:
      "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_document_ptr_h3"
      using disconnected_nodes_eq_h2 docs_neq disc_nodes_document_ptr_h3 by auto
    have disc_nodes_document_ptr_h':
      "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r child # disc_nodes_document_ptr_h3"
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
      moreover have "CD.a_owner_document_valid h"
        using assms(1)  by(simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
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
      have "CD.a_distinct_lists h2"
        using heap_is_wellformed_def CD.heap_is_wellformed_def wellformed_h2 by blast
      then have 0: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
|h2 \<turnstile> document_ptr_kinds_M|\<^sub>r))"
        by(simp add: CD.a_distinct_lists_def)
      show ?thesis
        using distinct_concat_map_E(1)[OF 0] \<open>child \<in> set disc_nodes_old_document_h2\<close>
          disc_nodes_old_document_h2 disc_nodes_document_ptr_h2
        by (meson \<open>type_wf h2\<close> docs_neq known_ptrs local.get_owner_document_disconnected_nodes
            local.known_ptrs_preserved object_ptr_kinds_h_eq3 returns_result_eq wellformed_h2)
    qed

    have child_in_heap: "child |\<in>| node_ptr_kinds h"
      using get_owner_document_ptr_in_heap[OF is_OK_returns_result_I[OF old_document]] node_ptr_kinds_commutes
      by blast
    have "CD.a_acyclic_heap h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
    have "parent_child_rel h' \<subseteq> parent_child_rel h2"
    proof
      fix x
      assume "x \<in> parent_child_rel h'"
      then show "x \<in> parent_child_rel h2"
        using object_ptr_kinds_h2_eq3  object_ptr_kinds_h3_eq3 children_eq2_h2 children_eq2_h3
          mem_Collect_eq object_ptr_kinds_M_eq_h3 select_result_eq split_cong
        unfolding CD.parent_child_rel_def
        by(simp)
    qed
    then have " CD.a_acyclic_heap h'"
      using \<open> CD.a_acyclic_heap h2\<close>  CD.acyclic_heap_def acyclic_subset by blast

    moreover have " CD.a_all_ptrs_in_heap h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
    then have "CD.a_all_ptrs_in_heap h3"
      apply(auto simp add: CD.a_all_ptrs_in_heap_def node_ptr_kinds_eq3_h2 children_eq_h2)[1]
       apply (metis CD.l_heap_is_wellformed_axioms \<open>type_wf h2\<close> children_eq2_h2 known_ptrs
          l_heap_is_wellformed.heap_is_wellformed_children_in_heap local.get_child_nodes_ok
          local.known_ptrs_known_ptr node_ptr_kinds_eq3_h2 object_ptr_kinds_h2_eq3 object_ptr_kinds_h_eq3
          returns_result_select_result wellformed_h2)
      by (metis (no_types, lifting) disc_nodes_old_document_h2 disc_nodes_old_document_h3
          disconnected_nodes_eq2_h2 document_ptr_kinds_eq3_h2 finite_set_in select_result_I2 set_remove1_subset
          subsetD)
    then have "CD.a_all_ptrs_in_heap h'"
      by (smt \<open>child \<in> set disc_nodes_old_document_h2\<close> children_eq2_h3 disc_nodes_document_ptr_h'
          disc_nodes_document_ptr_h2 disc_nodes_old_document_h2 disconnected_nodes_eq2_h3 document_ptr_kinds_eq3_h3
          finite_set_in local.CD.a_all_ptrs_in_heap_def local.heap_is_wellformed_disc_nodes_in_heap
          node_ptr_kinds_eq3_h2 node_ptr_kinds_eq3_h3 object_ptr_kinds_h3_eq3 select_result_I2 set_ConsD
          subset_code(1) wellformed_h2)

    moreover have "CD.a_owner_document_valid h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
    then have "CD.a_owner_document_valid h'"
      apply(simp add: CD.a_owner_document_valid_def node_ptr_kinds_eq_h2 node_ptr_kinds_eq3_h3
          object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3
          children_eq2_h2 children_eq2_h3 )
      by (metis (no_types) disc_nodes_document_ptr_h' disc_nodes_document_ptr_h2
          disc_nodes_old_document_h2 disc_nodes_old_document_h3 disconnected_nodes_eq2_h2
          disconnected_nodes_eq2_h3 document_ptr_in_heap document_ptr_kinds_eq3_h2 document_ptr_kinds_eq3_h3
          in_set_remove1 list.set_intros(1) list.set_intros(2) node_ptr_kinds_eq3_h2 node_ptr_kinds_eq3_h3
          object_ptr_kinds_h2_eq3 object_ptr_kinds_h3_eq3 select_result_I2)

    have a_distinct_lists_h2: "CD.a_distinct_lists h2"
      using wellformed_h2 by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
    then have "CD.a_distinct_lists h'"
      apply(auto simp add: CD.a_distinct_lists_def object_ptr_kinds_eq_h3 object_ptr_kinds_eq_h2
          children_eq2_h2 children_eq2_h3)[1]
    proof -
      assume 1: "distinct (concat (map (\<lambda>ptr. |h' \<turnstile> get_child_nodes ptr|\<^sub>r) (sorted_list_of_set
(fset (object_ptr_kinds h')))))"
        and 2: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
(sorted_list_of_set (fset (document_ptr_kinds h2)))))"
        and 3: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r) \<inter>
(\<Union>x\<in>fset (document_ptr_kinds h2). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
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
                disc_nodes_old_document_h3 disconnected_nodes_eq2_h3 distinct_remove1 docs_neq select_result_I2)
        qed
      next
        fix x y
        assume a0: "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
          and a1: "y \<in> set (sorted_list_of_set (fset (document_ptr_kinds h')))"
          and a2: "x \<noteq> y"

        moreover have 5: "set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
          using 2 calculation by (auto simp add: document_ptr_kinds_eq3_h2 document_ptr_kinds_eq3_h3
              dest: distinct_concat_map_E(1))
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
                select_result_I2[OF disc_nodes_old_document_h2] select_result_I2[OF disc_nodes_old_document_h3]
                \<open>old_document = x\<close>
              by (metis (no_types, lifting) \<open>child \<notin> set (remove1 child disc_nodes_old_document_h2)\<close>
                  \<open>document_ptr \<noteq> x\<close> disconnected_nodes_eq2_h3 disjoint_iff_not_equal notin_set_remove1 set_ConsD)
          next
            case False
            then show ?thesis
              using 5 select_result_I2[OF disc_nodes_document_ptr_h']
                select_result_I2[OF disc_nodes_document_ptr_h2]
                select_result_I2[OF disc_nodes_old_document_h2] select_result_I2[OF disc_nodes_old_document_h3]
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
                  select_result_I2[OF disc_nodes_old_document_h3] \<open>old_document \<noteq> x\<close> \<open>old_document = y\<close> \<open>document_ptr = x\<close>
                apply(simp)
                by (metis (no_types, lifting) \<open>child \<notin> set (remove1 child disc_nodes_old_document_h2)\<close>
                    disconnected_nodes_eq2_h3 disjoint_iff_not_equal notin_set_remove1)
            next
              case False
              then show ?thesis
                using 5 select_result_I2[OF disc_nodes_document_ptr_h']
                  select_result_I2[OF disc_nodes_document_ptr_h2]
                  select_result_I2[OF disc_nodes_old_document_h2]
                  select_result_I2[OF disc_nodes_old_document_h3] \<open>old_document \<noteq> x\<close> \<open>old_document = y\<close>
                  \<open>document_ptr \<noteq> x\<close>
                by (metis (no_types, lifting) disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
                    disjoint_iff_not_equal docs_neq notin_set_remove1)
            qed
          next
            case False
            have "set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}"
              by (metis DocumentMonad.ptr_kinds_M_ok DocumentMonad.ptr_kinds_M_ptr_kinds False
                  \<open>type_wf h2\<close> a1 disc_nodes_old_document_h2 document_ptr_kinds_M_def document_ptr_kinds_eq2_h2
                  document_ptr_kinds_eq2_h3 l_ptr_kinds_M.ptr_kinds_ptr_kinds_M local.get_disconnected_nodes_ok
                  local.heap_is_wellformed_one_disc_parent returns_result_select_result wellformed_h2)
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
                  select_result_I2[OF disc_nodes_old_document_h3] \<open>old_document \<noteq> x\<close> \<open>old_document \<noteq> y\<close>
                  \<open>document_ptr = x\<close> \<open>document_ptr \<noteq> y\<close>
                  \<open>child \<in> set disc_nodes_old_document_h2\<close> disconnected_nodes_eq2_h2
                  disconnected_nodes_eq2_h3 \<open>set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r \<inter> set disc_nodes_old_document_h2 = {}\<close>
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
                moreover have f1: "set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes old_document|\<^sub>r = {}"
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
                    \<open>child \<in> set disc_nodes_old_document_h2\<close> disconnected_nodes_eq2_h2
                    disconnected_nodes_eq2_h3
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
        and 2: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r) \<inter>
(\<Union>x\<in>fset (document_ptr_kinds h2). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
        and 3: "xa |\<in>| object_ptr_kinds h'"
        and 4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
        and 5: "xb |\<in>| document_ptr_kinds h'"
        and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
      then show False
        using \<open>child \<in> set disc_nodes_old_document_h2\<close> disc_nodes_document_ptr_h'
          disc_nodes_document_ptr_h2 disc_nodes_old_document_h2 disc_nodes_old_document_h3
          disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3
          old_document_in_heap
        apply(auto)[1]
        apply(cases "xb = old_document")
      proof -
        assume a1: "xb = old_document"
        assume a2: "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disc_nodes_old_document_h2"
        assume a3: "h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r remove1 child disc_nodes_old_document_h2"
        assume a4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
        assume "document_ptr_kinds h2 = document_ptr_kinds h'"
        assume a5: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r) \<inter>
(\<Union>x\<in>fset (document_ptr_kinds h'). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
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
        assume a10: "\<And>doc_ptr. old_document \<noteq> doc_ptr \<Longrightarrow>
|h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
        assume a11: "\<And>doc_ptr. document_ptr \<noteq> doc_ptr \<Longrightarrow>
|h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
        assume a12: "(\<Union>x\<in>fset (object_ptr_kinds h'). set |h' \<turnstile> get_child_nodes x|\<^sub>r) \<inter>
(\<Union>x\<in>fset (document_ptr_kinds h'). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
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
          by (metis \<open>type_wf h'\<close> adopt_node_removes_child assms(1) assms(2) type_wf
              get_child_nodes_ok known_ptrs local.known_ptrs_known_ptr object_ptr_kinds_h2_eq3
              object_ptr_kinds_h3_eq3 object_ptr_kinds_h_eq3 returns_result_select_result)
        then show ?thesis
          using \<open>child \<in> set disc_nodes_old_document_h2\<close> by fastforce
      qed
    qed
    ultimately have "heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M h'"
      using \<open>type_wf h'\<close> \<open>CD.a_owner_document_valid h'\<close> CD.heap_is_wellformed_def by blast



    have shadow_root_eq_h2: "\<And>ptr' shadow_root_ptr_opt. h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt =
h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt"
      using get_shadow_root_reads set_disconnected_nodes_writes h3
      apply(rule reads_writes_preserved)
      by(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_get_shadow_root
          set_disconnected_nodes_get_shadow_root)
    then
    have shadow_root_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_shadow_root ptr'|\<^sub>r = |h3 \<turnstile> get_shadow_root ptr'|\<^sub>r"
      by (meson select_result_eq)

    have shadow_root_eq_h3: "\<And>ptr' shadow_root_ptr_opt. h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt =
h' \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt"
      using get_shadow_root_reads set_disconnected_nodes_writes h'
      apply(rule reads_writes_preserved)
      by(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_get_shadow_root
          set_disconnected_nodes_get_shadow_root)
    then
    have shadow_root_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_shadow_root ptr'|\<^sub>r = |h' \<turnstile> get_shadow_root ptr'|\<^sub>r"
      by (meson select_result_eq)

    have tag_name_eq_h2: "\<And>ptr' tag. h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag = h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag"
      using get_tag_name_reads set_disconnected_nodes_writes h3
      apply(rule reads_writes_preserved)
      by(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_get_tag_name
          set_disconnected_nodes_get_tag_name)
    then
    have tag_name_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_tag_name ptr'|\<^sub>r = |h3 \<turnstile> get_tag_name ptr'|\<^sub>r"
      by (meson select_result_eq)

    have tag_name_eq_h3: "\<And>ptr' tag. h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag = h' \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag"
      using get_tag_name_reads set_disconnected_nodes_writes h'
      apply(rule reads_writes_preserved)
      by(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_get_tag_name
          set_disconnected_nodes_get_tag_name)
    then
    have tag_name_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_tag_name ptr'|\<^sub>r = |h' \<turnstile> get_tag_name ptr'|\<^sub>r"
      by (meson select_result_eq)

    have object_ptr_kinds_eq_h2: "object_ptr_kinds h2 = object_ptr_kinds h3"
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
            OF set_disconnected_nodes_writes h3])
      unfolding adopt_node_locs_def remove_child_locs_def
      using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
      by (auto simp add: reflp_def transp_def  split: if_splits)

    have object_ptr_kinds_eq_h3: "object_ptr_kinds h3 = object_ptr_kinds h'"
      apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
            OF set_disconnected_nodes_writes h'])
      unfolding adopt_node_locs_def remove_child_locs_def
      using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
      by (auto simp add: reflp_def transp_def  split: if_splits)

    have document_ptr_kinds_eq_h2: "document_ptr_kinds h2 = document_ptr_kinds h3"
      using object_ptr_kinds_eq_h2
      by(auto simp add: document_ptr_kinds_def)

    have shadow_root_ptr_kinds_eq_h2: "shadow_root_ptr_kinds h2 = shadow_root_ptr_kinds h3"
      using object_ptr_kinds_eq_h2
      by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
    have element_ptr_kinds_eq_h2: "element_ptr_kinds h2 = element_ptr_kinds h3"
      using object_ptr_kinds_eq_h2
      by(auto simp add: element_ptr_kinds_def node_ptr_kinds_def)

    have document_ptr_kinds_eq_h3: "document_ptr_kinds h3 = document_ptr_kinds h'"
      using object_ptr_kinds_eq_h3
      by(auto simp add: document_ptr_kinds_def)
    have shadow_root_ptr_kinds_eq_h3: "shadow_root_ptr_kinds h3 = shadow_root_ptr_kinds h'"
      using object_ptr_kinds_eq_h3
      by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
    have element_ptr_kinds_eq_h3: "element_ptr_kinds h3 = element_ptr_kinds h'"
      using object_ptr_kinds_eq_h3
      by(auto simp add: element_ptr_kinds_def node_ptr_kinds_def)

    have "a_host_shadow_root_rel h' = a_host_shadow_root_rel h3" and
      "a_host_shadow_root_rel h3 = a_host_shadow_root_rel h2"
      by(auto simp add: a_host_shadow_root_rel_def shadow_root_eq2_h2 shadow_root_eq2_h3
          element_ptr_kinds_eq_h2 element_ptr_kinds_eq_h3)
    have "parent_child_rel h' = parent_child_rel h3" and "parent_child_rel h3 = parent_child_rel h2"
      by(auto simp add: CD.parent_child_rel_def children_eq2_h2 children_eq2_h3
          object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3)


    have "parent_child_rel h2 \<subseteq> parent_child_rel h"
      using h2 parent_opt
    proof (induct parent_opt)
      case None
      then show ?case
        by simp
    next
      case (Some parent)
      then
      have h2: "h \<turnstile> remove_child parent child \<rightarrow>\<^sub>h h2"
        by auto
      have child_nodes_eq_h: "\<And>ptr children. parent \<noteq> ptr \<Longrightarrow>
h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
        using get_child_nodes_reads remove_child_writes h2
        apply(rule reads_writes_preserved)
        apply(auto simp add: remove_child_locs_def)[1]
        by (simp add: set_child_nodes_get_child_nodes_different_pointers)
      moreover obtain children where children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
        using Some local.get_parent_child_dual by blast
      ultimately show ?thesis
        using object_ptr_kinds_eq_h h2
        apply(auto simp add: CD.parent_child_rel_def split: option.splits)[1]
        apply(case_tac "parent = a")
         apply (metis (no_types, lifting) \<open>type_wf h3\<close> children_eq2_h2 children_eq_h2 known_ptrs
            local.get_child_nodes_ok local.known_ptrs_known_ptr local.remove_child_children_subset
            object_ptr_kinds_h2_eq3 returns_result_select_result subset_code(1) type_wf)
        apply (metis (no_types, lifting) known_ptrs local.get_child_nodes_ok local.known_ptrs_known_ptr
            returns_result_select_result select_result_I2 type_wf)
        done
    qed

    have "a_host_shadow_root_rel h2 = a_host_shadow_root_rel h"
      using h2
    proof (induct parent_opt)
      case None
      then show ?case
        by simp
    next
      case (Some parent)
      then
      have h2: "h \<turnstile> remove_child parent child \<rightarrow>\<^sub>h h2"
        by auto
      have "\<And>ptr shadow_root. h \<turnstile> get_shadow_root ptr \<rightarrow>\<^sub>r shadow_root = h2 \<turnstile> get_shadow_root ptr \<rightarrow>\<^sub>r shadow_root"
        using get_shadow_root_reads remove_child_writes h2
        apply(rule reads_writes_preserved)
        apply(auto simp add: remove_child_locs_def)[1]
        by (auto simp add: set_disconnected_nodes_get_shadow_root set_child_nodes_get_shadow_root)
      then show ?case
        apply(auto simp add: a_host_shadow_root_rel_def)[1]
         apply (metis (mono_tags, lifting) Collect_cong \<open>type_wf h2\<close> case_prodE case_prodI
            l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_host_shadow_root_rel_def local.get_shadow_root_ok
            local.a_host_shadow_root_rel_shadow_root returns_result_select_result)
        by (metis (no_types, lifting) Collect_cong case_prodE case_prodI local.get_shadow_root_ok
            local.a_host_shadow_root_rel_def local.a_host_shadow_root_rel_shadow_root returns_result_select_result type_wf)
    qed

    have "a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h2 - {(cast old_document, cast child)}"
      apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h2 disconnected_nodes_eq2_h2)[1]
      using disconnected_nodes_eq2_h2  disc_nodes_old_document_h2 disc_nodes_old_document_h3
      using \<open>distinct disc_nodes_old_document_h2\<close>
        apply (metis (no_types, lifting) \<open>child \<notin> set (remove1 child disc_nodes_old_document_h2)\<close>
          case_prodI in_set_remove1 mem_Collect_eq pair_imageI select_result_I2)
      using \<open>child \<notin> set (remove1 child disc_nodes_old_document_h2)\<close> disc_nodes_old_document_h3
       apply auto[1]
      by (metis (no_types, lifting) case_prodI disc_nodes_old_document_h2 disc_nodes_old_document_h3
          disconnected_nodes_eq2_h2 in_set_remove1 mem_Collect_eq pair_imageI select_result_I2)

    have "a_ptr_disconnected_node_rel h3 \<subseteq> a_ptr_disconnected_node_rel h"
      using h2 parent_opt
    proof (induct parent_opt)
      case None
      then show ?case
        by(auto simp add: \<open>a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h2 - {(cast old_document, cast child)}\<close>)
    next
      case (Some parent)
      then
      have h2: "h \<turnstile> remove_child parent child \<rightarrow>\<^sub>h h2"
        by auto
      then
      obtain children_h h'2 disconnected_nodes_h where
        children_h: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children_h" and
        child_in_children_h: "child \<in> set children_h" and
        disconnected_nodes_h: "h \<turnstile>  get_disconnected_nodes old_document \<rightarrow>\<^sub>r disconnected_nodes_h" and
        h'2: "h \<turnstile>  set_disconnected_nodes old_document (child # disconnected_nodes_h) \<rightarrow>\<^sub>h h'2" and
        h': "h'2 \<turnstile> set_child_nodes parent (remove1 child children_h) \<rightarrow>\<^sub>h h2"
        using old_document
        apply(auto simp add: remove_child_def elim!: bind_returns_heap_E
            dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure]
            pure_returns_heap_eq[rotated, OF get_child_nodes_pure]
            pure_returns_heap_eq[rotated, OF get_disconnected_nodes_pure] split: if_splits)[1]
        using select_result_I2 by fastforce

      have "|h3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h \<turnstile> document_ptr_kinds_M|\<^sub>r"
        using object_ptr_kinds_eq_h object_ptr_kinds_eq_h2
        by(auto simp add: document_ptr_kinds_def)
      have disconnected_nodes_eq_h: "\<And>ptr disc_nodes. old_document \<noteq> ptr \<Longrightarrow>
h \<turnstile> get_disconnected_nodes ptr \<rightarrow>\<^sub>r disc_nodes = h2 \<turnstile> get_disconnected_nodes ptr \<rightarrow>\<^sub>r disc_nodes"
        using get_disconnected_nodes_reads remove_child_writes h2
        apply(rule reads_writes_preserved)
        apply(auto simp add: remove_child_locs_def)[1]
        using old_document
        by (auto simp add:set_child_nodes_get_disconnected_nodes set_disconnected_nodes_get_disconnected_nodes_different_pointers)
      then
      have foo: "\<And>ptr disc_nodes. old_document \<noteq> ptr \<Longrightarrow>
h \<turnstile> get_disconnected_nodes ptr \<rightarrow>\<^sub>r disc_nodes = h3 \<turnstile> get_disconnected_nodes ptr \<rightarrow>\<^sub>r disc_nodes"
        using disconnected_nodes_eq_h2 by simp
      then
      have foo2: "\<And>ptr. old_document \<noteq> ptr \<Longrightarrow> |h \<turnstile> get_disconnected_nodes ptr|\<^sub>r =
|h3 \<turnstile> get_disconnected_nodes ptr|\<^sub>r"
        by (meson select_result_eq)
      have "h'2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r child # disconnected_nodes_h"
        using h'2
        using local.set_disconnected_nodes_get_disconnected_nodes by blast

      have "h2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r child # disconnected_nodes_h"
        using get_disconnected_nodes_reads set_child_nodes_writes h'
          \<open>h'2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r child # disconnected_nodes_h\<close>
        apply(rule reads_writes_separate_forwards)
        using local.set_child_nodes_get_disconnected_nodes by blast
      then have "h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disconnected_nodes_h"
        using h3
        using disc_nodes_old_document_h2 disc_nodes_old_document_h3 returns_result_eq
        by fastforce
      have "a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h"
        using \<open>|h3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h \<turnstile> document_ptr_kinds_M|\<^sub>r\<close>
        apply(auto simp add: a_ptr_disconnected_node_rel_def )[1]
         apply(case_tac "old_document = aa")
        using disconnected_nodes_h \<open>h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disconnected_nodes_h\<close>
        using foo2
          apply(auto)[1]
        using disconnected_nodes_h \<open>h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disconnected_nodes_h\<close>
        using foo2
         apply(auto)[1]
        apply(case_tac "old_document = aa")
        using disconnected_nodes_h \<open>h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disconnected_nodes_h\<close>
        using foo2
         apply(auto)[1]
        using disconnected_nodes_h \<open>h3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r disconnected_nodes_h\<close>
        using foo2
        apply(auto)[1]
        done
      then show ?thesis
        by auto
    qed

    have "acyclic (parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2)"
      using local.heap_is_wellformed_def wellformed_h2 by blast
    then have "acyclic (parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)"
      using \<open>a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h2 - {(cast old_document, cast child)}\<close>
      by(auto simp add: \<open>parent_child_rel h3 = parent_child_rel h2\<close> \<open>a_host_shadow_root_rel h3 = a_host_shadow_root_rel h2\<close> elim!: acyclic_subset)
    moreover
    have "a_ptr_disconnected_node_rel h' = insert (cast document_ptr, cast child) (a_ptr_disconnected_node_rel h3)"
      using disconnected_nodes_eq2_h3[symmetric] disc_nodes_document_ptr_h3 disc_nodes_document_ptr_h' document_ptr_in_heap[unfolded document_ptr_kinds_eq_h2]
      apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h3[symmetric])[1]
       apply(case_tac "document_ptr = aa")
        apply(auto)[1]
       apply(auto)[1]
      apply(case_tac "document_ptr = aa")
       apply(auto)[1]
      apply(auto)[1]
      done
    moreover have "(cast child, cast document_ptr) \<notin> (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
      using \<open>h \<turnstile> get_ancestors_di (cast document_ptr) \<rightarrow>\<^sub>r ancestors\<close>
        \<open>cast child \<notin>  set ancestors\<close> get_ancestors_di_parent_child_a_host_shadow_root_rel
      using assms(1) known_ptrs type_wf by blast
    moreover have "(cast child, cast document_ptr) \<notin> (parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)\<^sup>*"
    proof -
      have "(parent_child_rel h3 \<union> local.a_host_shadow_root_rel h3 \<union> local.a_ptr_disconnected_node_rel h3) \<subseteq> (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> local.a_ptr_disconnected_node_rel h)"
        apply(simp add: \<open>parent_child_rel h3 = parent_child_rel h2\<close> \<open>a_host_shadow_root_rel h3 = a_host_shadow_root_rel h2\<close> \<open>a_host_shadow_root_rel h2 = a_host_shadow_root_rel h\<close>)
        using \<open>local.a_ptr_disconnected_node_rel h3 \<subseteq> local.a_ptr_disconnected_node_rel h\<close> \<open>parent_child_rel h2 \<subseteq> parent_child_rel h\<close>
        by blast
      then show ?thesis
        using calculation(3) rtrancl_mono by blast
    qed
    ultimately have "acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')"
      by(auto simp add: \<open>parent_child_rel h' = parent_child_rel h3\<close> \<open>a_host_shadow_root_rel h' = a_host_shadow_root_rel h3\<close>)

    show "heap_is_wellformed h'"
      using \<open>heap_is_wellformed h2\<close>
      using \<open>heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M h'\<close>
      using \<open>acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')\<close>
      apply(auto simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def
          a_all_ptrs_in_heap_def a_distinct_lists_def a_shadow_root_valid_def)[1]
      by(auto simp add: object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 element_ptr_kinds_eq_h2
          element_ptr_kinds_eq_h3 shadow_root_ptr_kinds_eq_h2 shadow_root_ptr_kinds_eq_h3  shadow_root_eq_h2
          shadow_root_eq_h3 shadow_root_eq2_h2 shadow_root_eq2_h3 tag_name_eq_h2 tag_name_eq_h3 tag_name_eq2_h2
          tag_name_eq2_h3)
  qed
qed


lemma adopt_node_node_in_disconnected_nodes:
  assumes wellformed: "heap_is_wellformed h"
    and adopt_node: "h \<turnstile> adopt_node owner_document node_ptr \<rightarrow>\<^sub>h h'"
    and "h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "node_ptr \<in> set disc_nodes"
proof -
  obtain old_document parent_opt h2 where
    old_document: "h \<turnstile> get_owner_document (cast node_ptr) \<rightarrow>\<^sub>r old_document" and
    parent_opt: "h \<turnstile> get_parent node_ptr \<rightarrow>\<^sub>r parent_opt" and
    h2: "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> remove_child parent node_ptr | None \<Rightarrow> return ()) \<rightarrow>\<^sub>h h2" and
    h': "h2 \<turnstile> (if owner_document \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 node_ptr old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes owner_document;
        set_disconnected_nodes owner_document (node_ptr # disc_nodes)
      } else do {
        return ()
      }) \<rightarrow>\<^sub>h h'"
    using assms(2)[unfolded adopt_node_def CD.adopt_node_def]
    by(auto elim!: bind_returns_heap_E dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure]
        pure_returns_heap_eq[rotated, OF get_parent_pure] pure_returns_heap_eq[rotated, OF get_ancestors_di_pure]
        split: option.splits if_splits)

  show ?thesis
  proof (cases "owner_document = old_document")
    case True
    then show ?thesis
    proof (insert parent_opt h2, induct parent_opt)
      case None
      then have "h = h'"
        using h2 h' by(auto)
      then show ?case
        using in_disconnected_nodes_no_parent assms None old_document by blast
    next
      case (Some parent)
      then show ?case
        using remove_child_in_disconnected_nodes known_ptrs True h' assms(3) old_document
        by auto
    qed
  next
    case False
    then show ?thesis
      using assms(3)  h' list.set_intros(1) select_result_I2
        set_disconnected_nodes_get_disconnected_nodes
      apply(auto elim!: bind_returns_heap_E
          bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated])[1]
    proof -
      fix x  and h'a and xb
      assume a1: "h' \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes"
      assume a2: "\<And>h document_ptr disc_nodes h'. h \<turnstile> set_disconnected_nodes document_ptr disc_nodes \<rightarrow>\<^sub>h h' \<Longrightarrow>
h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes"
      assume "h'a \<turnstile> set_disconnected_nodes owner_document (node_ptr # xb) \<rightarrow>\<^sub>h h'"
      then have "node_ptr # xb = disc_nodes"
        using a2 a1 by (meson returns_result_eq)
      then show ?thesis
        by (meson list.set_intros(1))
    qed
  qed
qed
end

interpretation i_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M: l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document get_parent get_parent_locs remove_child remove_child_locs get_disconnected_nodes
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes get_child_nodes_locs known_ptrs set_child_nodes
  set_child_nodes_locs remove heap_is_wellformed parent_child_rel
  by(auto simp add: l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare i_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.l_adopt_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


interpretation i_adopt_node_wf?: l_adopt_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_owner_document get_parent get_parent_locs remove_child remove_child_locs get_disconnected_nodes
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs get_ancestors_di
  get_ancestors_di_locs adopt_node adopt_node_locs adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf
  get_child_nodes get_child_nodes_locs known_ptrs set_child_nodes set_child_nodes_locs get_host
  get_host_locs get_disconnected_document get_disconnected_document_locs remove heap_is_wellformed
  parent_child_rel
  by(auto simp add: l_adopt_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_adopt_node_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


interpretation i_adopt_node_wf2?: l_adopt_node_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  set_child_nodes set_child_nodes_locs get_shadow_root get_shadow_root_locs set_disconnected_nodes
  set_disconnected_nodes_locs get_tag_name get_tag_name_locs get_owner_document get_parent get_parent_locs
  remove_child remove_child_locs remove known_ptrs heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_host get_host_locs get_disconnected_document get_disconnected_document_locs get_root_node
  get_root_node_locs get_ancestors_di get_ancestors_di_locs adopt_node adopt_node_locs adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  by(auto simp add: l_adopt_node_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_adopt_node_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


lemma adopt_node_wf_is_l_adopt_node_wf [instances]:
  "l_adopt_node_wf type_wf known_ptr heap_is_wellformed parent_child_rel get_child_nodes
get_disconnected_nodes known_ptrs adopt_node"
  apply(auto simp add: l_adopt_node_wf_def l_adopt_node_wf_axioms_def instances)[1]
  using adopt_node_preserves_wellformedness apply blast
  using adopt_node_removes_child apply blast
  using adopt_node_node_in_disconnected_nodes apply blast
  using adopt_node_removes_first_child apply blast
  using adopt_node_document_in_heap apply blast
  done


subsubsection \<open>insert\_before\<close>

locale l_insert_before_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes +
  l_get_disconnected_nodes +
  l_set_child_nodes_get_shadow_root +
  l_set_disconnected_nodes_get_shadow_root +
  l_set_child_nodes_get_tag_name +
  l_set_disconnected_nodes_get_tag_name +
  l_set_disconnected_nodes_get_disconnected_nodes +
  l_set_child_nodes_get_disconnected_nodes +
  l_set_disconnected_nodes_get_disconnected_nodes_wf +
  (* l_set_disconnected_nodes_get_ancestors_si + *)
  l_insert_before\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M _ _ _ _ _ _ get_ancestors_di get_ancestors_di_locs +
  (* l_get_root_node_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M  + *)
  l_get_owner_document  +
  l_adopt_node\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node_wf  +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_adopt_node_get_shadow_root +
  l_get_ancestors_di_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_remove_child_wf2
begin
lemma insert_before_child_preserves:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> insert_before ptr node child \<rightarrow>\<^sub>h h'"
  shows "type_wf h'" and "known_ptrs h'" and "heap_is_wellformed h'"
proof -
  obtain ancestors reference_child owner_document h2 h3 disconnected_nodes_h2 where
    ancestors: "h \<turnstile> get_ancestors_di ptr \<rightarrow>\<^sub>r ancestors" and
    node_not_in_ancestors: "cast node \<notin> set ancestors" and
    reference_child: "h \<turnstile> (if Some node = child then a_next_sibling node else return child) \<rightarrow>\<^sub>r reference_child" and
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

  obtain old_document parent_opt h'2 (* ancestors *) where
    (*    "h \<turnstile> get_ancestors_di (cast owner_document) \<rightarrow>\<^sub>r ancestors" and
    "cast child \<notin>  set ancestors" and *)
    old_document: "h \<turnstile> get_owner_document (cast node) \<rightarrow>\<^sub>r old_document" and
    parent_opt: "h \<turnstile> get_parent node \<rightarrow>\<^sub>r parent_opt" and
    h'2: "h \<turnstile> (case parent_opt of Some parent \<Rightarrow> remove_child parent node | None \<Rightarrow> return ()) \<rightarrow>\<^sub>h h'2" and
    h2': "h'2 \<turnstile> (if owner_document \<noteq> old_document then do {
        old_disc_nodes \<leftarrow> get_disconnected_nodes old_document;
        set_disconnected_nodes old_document (remove1 node old_disc_nodes);
        disc_nodes \<leftarrow> get_disconnected_nodes owner_document;
        set_disconnected_nodes owner_document (node # disc_nodes)
      } else do {
        return ()
      }) \<rightarrow>\<^sub>h h2"
    using h2
    apply(auto simp add:  adopt_node_def[unfolded CD.adopt_node_def] elim!: bind_returns_heap_E
        dest!: pure_returns_heap_eq[rotated, OF get_ancestors_di_pure])[1]
    apply(split if_splits)
    by(auto simp add:  elim!: bind_returns_heap_E
        dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure] pure_returns_heap_eq[rotated, OF get_parent_pure])

  have "type_wf h2"
    using \<open>type_wf h\<close>
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF adopt_node_writes h2]
    using adopt_node_types_preserved
    by(auto simp add: reflp_def transp_def)
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h3]
    using set_disconnected_nodes_types_preserved
    by(auto simp add: reflp_def transp_def)
  then show "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF insert_node_writes h']
    using set_child_nodes_types_preserved
    by(auto simp add: reflp_def transp_def)

  have "object_ptr_kinds h = object_ptr_kinds h2"
    using adopt_node_writes h2
    apply(rule writes_small_big)
    using adopt_node_pointers_preserved
    by(auto simp add: reflp_def transp_def)
  moreover have "\<dots> = object_ptr_kinds h3"
    using set_disconnected_nodes_writes h3
    apply(rule writes_small_big)
    using set_disconnected_nodes_pointers_preserved
    by(auto simp add: reflp_def transp_def)
  moreover have "\<dots> = object_ptr_kinds h'"
    using insert_node_writes h'
    apply(rule writes_small_big)
    using set_child_nodes_pointers_preserved
    by(auto simp add: reflp_def transp_def)

  ultimately
  show "known_ptrs h'"
    using \<open>known_ptrs h\<close> known_ptrs_preserved
    by blast

  have "known_ptrs h2"
    using \<open>known_ptrs h\<close> known_ptrs_preserved \<open>object_ptr_kinds h = object_ptr_kinds h2\<close>
    by blast
  then
  have "known_ptrs h3"
    using known_ptrs_preserved \<open>object_ptr_kinds h2 = object_ptr_kinds h3\<close>
    by blast

  have "known_ptr ptr"
    by (meson get_owner_document_ptr_in_heap is_OK_returns_result_I \<open>known_ptrs h\<close>
        l_known_ptrs.known_ptrs_known_ptr l_known_ptrs_axioms owner_document)

  have object_ptr_kinds_M_eq3_h: "object_ptr_kinds h = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF adopt_node_writes h2])
    using adopt_node_pointers_preserved
      apply blast
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h: "\<And>ptrs. h \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs )
  then have object_ptr_kinds_M_eq2_h: "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq2_h: "|h \<turnstile> node_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast

  have wellformed_h2: "heap_is_wellformed h2"
    using adopt_node_preserves_wellformedness[OF \<open>heap_is_wellformed h\<close> h2] \<open>known_ptrs h\<close> \<open>type_wf h\<close>
    .

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

  have object_ptr_kinds_M_eq3_h': "object_ptr_kinds h3 = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF insert_node_writes h'])
    unfolding a_remove_child_locs_def
    using set_child_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have object_ptr_kinds_M_eq_h3: "\<And>ptrs. h3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h' \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
    by(simp add: object_ptr_kinds_M_defs)
  then have object_ptr_kinds_M_eq2_h3: "|h3 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp
  then have node_ptr_kinds_eq2_h3: "|h3 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
    using node_ptr_kinds_M_eq by blast
  have document_ptr_kinds_eq2_h3: "|h3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h' \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using object_ptr_kinds_M_eq2_h3 document_ptr_kinds_M_eq by auto


  have shadow_root_eq_h2: "\<And>ptr' shadow_root. h \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root =
h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root"
    using get_shadow_root_reads adopt_node_writes h2
    apply(rule reads_writes_preserved)
    using local.adopt_node_get_shadow_root by blast

  have disconnected_nodes_eq_h2: "\<And>doc_ptr disc_nodes. owner_document \<noteq> doc_ptr \<Longrightarrow>
h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_disconnected_nodes_writes h3
    apply(rule reads_writes_preserved)
    by (auto simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then have disconnected_nodes_eq2_h2: "\<And>doc_ptr. doc_ptr \<noteq> owner_document \<Longrightarrow>
|h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_h3: "h3 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r remove1 node disconnected_nodes_h2"
    using h3 set_disconnected_nodes_get_disconnected_nodes
    by blast

  have disconnected_nodes_eq_h3:
    "\<And>doc_ptr disc_nodes. h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads insert_node_writes  h'
    apply(rule reads_writes_preserved)
    using set_child_nodes_get_disconnected_nodes by fast
  then have disconnected_nodes_eq2_h3:
    "\<And>doc_ptr. |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads set_disconnected_nodes_writes h3
    apply(rule reads_writes_preserved)
    by (auto simp add: set_disconnected_nodes_get_child_nodes)
  then have children_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force

  have children_eq_h3:
    "\<And>ptr' children. ptr \<noteq> ptr' \<Longrightarrow> h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using get_child_nodes_reads insert_node_writes h'
    apply(rule reads_writes_preserved)
    by (auto simp add: set_child_nodes_get_child_nodes_different_pointers)
  then have children_eq2_h3: "\<And>ptr'. ptr \<noteq> ptr' \<Longrightarrow> |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  obtain children_h3 where children_h3: "h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children_h3"
    using h' a_insert_node_def by auto
  have children_h': "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r insert_before_list node reference_child children_h3"
    using h' \<open>type_wf h3\<close> \<open>known_ptr ptr\<close>
    by(auto simp add: a_insert_node_def elim!: bind_returns_heap_E2
        dest!: set_child_nodes_get_child_nodes returns_result_eq[OF children_h3])


  have shadow_root_eq_h: "\<And>ptr' shadow_root_ptr_opt. h \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt =
h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt"
    using get_shadow_root_reads adopt_node_writes h2
    apply(rule reads_writes_preserved)
    by(auto simp add: adopt_node_locs_def CD.adopt_node_locs_def CD.remove_child_locs_def
        set_child_nodes_get_shadow_root set_disconnected_nodes_get_shadow_root)
  then
  have shadow_root_eq2_h: "\<And>ptr'. |h \<turnstile> get_shadow_root ptr'|\<^sub>r = |h2 \<turnstile> get_shadow_root ptr'|\<^sub>r"
    by (meson select_result_eq)

  have shadow_root_eq_h2: "\<And>ptr' shadow_root_ptr_opt. h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt =
h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt"
    using get_shadow_root_reads set_disconnected_nodes_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_get_shadow_root
        set_disconnected_nodes_get_shadow_root)
  then
  have shadow_root_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_shadow_root ptr'|\<^sub>r = |h3 \<turnstile> get_shadow_root ptr'|\<^sub>r"
    by (meson select_result_eq)

  have shadow_root_eq_h3: "\<And>ptr' shadow_root_ptr_opt. h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt =
h' \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r shadow_root_ptr_opt"
    using get_shadow_root_reads insert_node_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_get_shadow_root
        set_disconnected_nodes_get_shadow_root)
  then
  have shadow_root_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_shadow_root ptr'|\<^sub>r = |h' \<turnstile> get_shadow_root ptr'|\<^sub>r"
    by (meson select_result_eq)

  have tag_name_eq_h2: "\<And>ptr' tag. h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag = h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag"
    using get_tag_name_reads set_disconnected_nodes_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_get_tag_name
        set_disconnected_nodes_get_tag_name)
  then
  have tag_name_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_tag_name ptr'|\<^sub>r = |h3 \<turnstile> get_tag_name ptr'|\<^sub>r"
    by (meson select_result_eq)

  have tag_name_eq_h3: "\<And>ptr' tag. h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag = h' \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r tag"
    using get_tag_name_reads insert_node_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: adopt_node_locs_def remove_child_locs_def set_child_nodes_get_tag_name
        set_disconnected_nodes_get_tag_name)
  then
  have tag_name_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_tag_name ptr'|\<^sub>r = |h' \<turnstile> get_tag_name ptr'|\<^sub>r"
    by (meson select_result_eq)

  have object_ptr_kinds_eq_hx: "object_ptr_kinds h = object_ptr_kinds h'2"
    using h'2 apply(simp split: option.splits)
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF CD.remove_child_writes])
    using CD.remove_child_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  have document_ptr_kinds_eq_hx: "document_ptr_kinds h = document_ptr_kinds h'2"
    using object_ptr_kinds_eq_hx
    by(auto simp add: document_ptr_kinds_def document_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_hx: "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'2"
    using object_ptr_kinds_eq_hx
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  have element_ptr_kinds_eq_hx: "element_ptr_kinds h = element_ptr_kinds h'2"
    using object_ptr_kinds_eq_hx
    by(auto simp add: element_ptr_kinds_def node_ptr_kinds_def)

  have object_ptr_kinds_eq_h: "object_ptr_kinds h = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF adopt_node_writes h2])
    unfolding adopt_node_locs_def CD.adopt_node_locs_def CD.remove_child_locs_def
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def  split: if_splits)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h = document_ptr_kinds h2"
    using object_ptr_kinds_eq_h
    by(auto simp add: document_ptr_kinds_def document_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_h: "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h2"
    using object_ptr_kinds_eq_h
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  have element_ptr_kinds_eq_h: "element_ptr_kinds h = element_ptr_kinds h2"
    using object_ptr_kinds_eq_h
    by(auto simp add: element_ptr_kinds_def node_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h2 = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF set_disconnected_nodes_writes h3])
    unfolding adopt_node_locs_def remove_child_locs_def
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def  split: if_splits)
  have document_ptr_kinds_eq_h2: "document_ptr_kinds h2 = document_ptr_kinds h3"
    using object_ptr_kinds_eq_h2
    by(auto simp add: document_ptr_kinds_def document_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_h2: "shadow_root_ptr_kinds h2 = shadow_root_ptr_kinds h3"
    using object_ptr_kinds_eq_h2
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  have element_ptr_kinds_eq_h2: "element_ptr_kinds h2 = element_ptr_kinds h3"
    using object_ptr_kinds_eq_h2
    by(auto simp add: element_ptr_kinds_def node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h3 = object_ptr_kinds h'"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'", OF insert_node_writes h'])
    using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
    by (auto simp add: reflp_def transp_def  split: if_splits)
  have document_ptr_kinds_eq_h3: "document_ptr_kinds h3 = document_ptr_kinds h'"
    using object_ptr_kinds_eq_h3
    by(auto simp add: document_ptr_kinds_def document_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_h3: "shadow_root_ptr_kinds h3 = shadow_root_ptr_kinds h'"
    using object_ptr_kinds_eq_h3
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  have element_ptr_kinds_eq_h3: "element_ptr_kinds h3 = element_ptr_kinds h'"
    using object_ptr_kinds_eq_h3
    by(auto simp add: element_ptr_kinds_def node_ptr_kinds_def)


  have wellformed_h'2: "heap_is_wellformed h'2"
    using h'2 remove_child_heap_is_wellformed_preserved assms
    by (metis (no_types, lifting) assms(1) option.case_eq_if pure_returns_heap_eq return_pure)

  have "known_ptrs h'2"
    using \<open>known_ptrs h\<close> known_ptrs_preserved \<open>object_ptr_kinds h = object_ptr_kinds h'2\<close>
    by blast

  have "type_wf h'2"
    using \<open>type_wf h\<close> h'2
    apply(auto split: option.splits)[1]
    apply(drule writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF CD.remove_child_writes])
    using CD.remove_child_types_preserved
    by(auto simp add: reflp_def transp_def )


  have ptr_in_heap: "ptr |\<in>| object_ptr_kinds h3"
    using children_h3 get_child_nodes_ptr_in_heap by blast
  have node_in_heap: "node |\<in>| node_ptr_kinds h"
    using h2 adopt_node_child_in_heap by fast
  have child_not_in_any_children: "\<And>p children. h2 \<turnstile> get_child_nodes p \<rightarrow>\<^sub>r children \<Longrightarrow> node \<notin> set children"
    using \<open>heap_is_wellformed h\<close> h2 adopt_node_removes_child \<open>type_wf h\<close> \<open>known_ptrs h\<close> by auto
  have "node \<in> set disconnected_nodes_h2"
    using disconnected_nodes_h2 h2 adopt_node_node_in_disconnected_nodes assms(1) \<open>type_wf h\<close> \<open>known_ptrs h\<close> by blast
  have node_not_in_disconnected_nodes: "\<And>d. d |\<in>| document_ptr_kinds h3 \<Longrightarrow> node \<notin> set |h3 \<turnstile> get_disconnected_nodes d|\<^sub>r"
  proof -
    fix d
    assume "d |\<in>| document_ptr_kinds h3"
    show "node \<notin> set |h3 \<turnstile> get_disconnected_nodes d|\<^sub>r"
    proof (cases "d = owner_document")
      case True
      then show ?thesis
        using disconnected_nodes_h2 wellformed_h2 h3 remove_from_disconnected_nodes_removes wellformed_h2
          \<open>d |\<in>| document_ptr_kinds h3\<close> disconnected_nodes_h3
        by fastforce
    next
      case False
      then have "set |h2 \<turnstile> get_disconnected_nodes d|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes owner_document|\<^sub>r = {}"
        using distinct_concat_map_E(1) wellformed_h2
        by (metis (no_types, lifting) \<open>d |\<in>| document_ptr_kinds h3\<close> \<open>type_wf h2\<close> disconnected_nodes_h2
            document_ptr_kinds_M_def document_ptr_kinds_eq2_h2 l_ptr_kinds_M.ptr_kinds_ptr_kinds_M
            local.get_disconnected_nodes_ok local.heap_is_wellformed_one_disc_parent returns_result_select_result
            select_result_I2)
      then show ?thesis
        using disconnected_nodes_eq2_h2[OF False] \<open>node \<in> set disconnected_nodes_h2\<close> disconnected_nodes_h2 by fastforce
    qed
  qed

  have "cast node \<noteq> ptr"
    using ancestors node_not_in_ancestors get_ancestors_ptr
    by fast

  have "a_host_shadow_root_rel h = a_host_shadow_root_rel h2"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h shadow_root_eq2_h)
  have "a_host_shadow_root_rel h2 = a_host_shadow_root_rel h3"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h2 shadow_root_eq2_h2)
  have "a_host_shadow_root_rel h3 = a_host_shadow_root_rel h'"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h3 shadow_root_eq2_h3)

  have "parent_child_rel h2 \<subseteq> parent_child_rel h"
  proof -
    have "parent_child_rel h'2 \<subseteq> parent_child_rel h"
      using h'2 parent_opt
    proof (induct parent_opt)
      case None
      then show ?case
        by simp
    next
      case (Some parent)
      then
      have h'2: "h \<turnstile> remove_child parent node \<rightarrow>\<^sub>h h'2"
        by auto
      then
      have "parent |\<in>| object_ptr_kinds h"
        using CD.remove_child_ptr_in_heap
        by blast
      have child_nodes_eq_h: "\<And>ptr children. parent \<noteq> ptr \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children =
h'2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
        using get_child_nodes_reads CD.remove_child_writes h'2
        apply(rule reads_writes_preserved)
        apply(auto simp add: CD.remove_child_locs_def)[1]
        by (simp add: set_child_nodes_get_child_nodes_different_pointers)
      moreover obtain children where children: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children"
        using Some local.get_parent_child_dual by blast
      moreover obtain children_h'2 where children_h'2: "h'2 \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children_h'2"
        using object_ptr_kinds_eq_hx calculation(2) \<open>parent |\<in>| object_ptr_kinds h\<close> get_child_nodes_ok
        by (metis \<open>type_wf h'2\<close> assms(3) is_OK_returns_result_E local.known_ptrs_known_ptr)
      ultimately show ?thesis
        using object_ptr_kinds_eq_h h2
        apply(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq_hx split: option.splits)[1]
        apply(case_tac "parent = a")
        using CD.remove_child_children_subset
         apply (metis (no_types, lifting) assms(2) assms(3) contra_subsetD h'2 select_result_I2)
        by (metis select_result_eq)
    qed
    moreover have "parent_child_rel h2 = parent_child_rel h'2"
    proof(cases "owner_document = old_document")
      case True
      then show ?thesis
        using h2' by simp
    next
      case False
      then obtain h'3 old_disc_nodes disc_nodes_document_ptr_h'3 where
        docs_neq: "owner_document \<noteq> old_document" and
        old_disc_nodes: "h'2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r old_disc_nodes" and
        h'3: "h'2 \<turnstile> set_disconnected_nodes old_document (remove1 node old_disc_nodes) \<rightarrow>\<^sub>h h'3" and
        disc_nodes_document_ptr_h3: "h'3 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes_document_ptr_h'3" and
        h2': "h'3 \<turnstile> set_disconnected_nodes owner_document (node # disc_nodes_document_ptr_h'3) \<rightarrow>\<^sub>h h2"
        using h2'
        by(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )

      have object_ptr_kinds_h'2_eq3: "object_ptr_kinds h'2 = object_ptr_kinds h'3"
        apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
              OF set_disconnected_nodes_writes h'3])
        using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
        by (auto simp add: reflp_def transp_def)
      then have object_ptr_kinds_M_eq_h'2: "\<And>ptrs. h'2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h'3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
        by(simp add: object_ptr_kinds_M_defs)
      then have object_ptr_kinds_eq_h'2: "|h'2 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h'3 \<turnstile> object_ptr_kinds_M|\<^sub>r"
        by(simp)
      then have node_ptr_kinds_eq_h'2: "|h'2 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h'3 \<turnstile> node_ptr_kinds_M|\<^sub>r"
        using node_ptr_kinds_M_eq by blast
      then have node_ptr_kinds_eq3_h'2: "node_ptr_kinds h'2 = node_ptr_kinds h'3"
        by auto
      have document_ptr_kinds_eq2_h'2: "|h'2 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h'3 \<turnstile> document_ptr_kinds_M|\<^sub>r"
        using object_ptr_kinds_eq_h'2 document_ptr_kinds_M_eq by auto
      then have document_ptr_kinds_eq3_h'2: "document_ptr_kinds h'2 = document_ptr_kinds h'3"
        using object_ptr_kinds_eq_h'2 document_ptr_kinds_M_eq by auto
      have children_eq_h'2: "\<And>ptr children. h'2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children = h'3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
        using get_child_nodes_reads set_disconnected_nodes_writes h'3
        apply(rule reads_writes_preserved)
        by (simp add: set_disconnected_nodes_get_child_nodes)
      then have children_eq2_h'2: "\<And>ptr. |h'2 \<turnstile> get_child_nodes ptr|\<^sub>r = |h'3 \<turnstile> get_child_nodes ptr|\<^sub>r"
        using select_result_eq by force

      have object_ptr_kinds_h'3_eq3: "object_ptr_kinds h'3 = object_ptr_kinds h2"
        apply(rule writes_small_big[where P="\<lambda>h h2. object_ptr_kinds h = object_ptr_kinds h2",
              OF set_disconnected_nodes_writes h2'])
        using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
        by (auto simp add: reflp_def transp_def)
      then have object_ptr_kinds_M_eq_h'3: "\<And>ptrs. h'3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
        by(simp add: object_ptr_kinds_M_defs)
      then have object_ptr_kinds_eq_h'3: "|h'3 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
        by(simp)
      then have node_ptr_kinds_eq_h'3: "|h'3 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> node_ptr_kinds_M|\<^sub>r"
        using node_ptr_kinds_M_eq by blast
      then have node_ptr_kinds_eq3_h'3: "node_ptr_kinds h'3 = node_ptr_kinds h2"
        by auto
      have document_ptr_kinds_eq2_h'3: "|h'3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> document_ptr_kinds_M|\<^sub>r"
        using object_ptr_kinds_eq_h'3 document_ptr_kinds_M_eq by auto
      then have document_ptr_kinds_eq3_h'3: "document_ptr_kinds h'3 = document_ptr_kinds h2"
        using object_ptr_kinds_eq_h'3 document_ptr_kinds_M_eq by auto
      have children_eq_h'3: "\<And>ptr children. h'3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children =
h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children"
        using get_child_nodes_reads set_disconnected_nodes_writes h2'
        apply(rule reads_writes_preserved)
        by (simp add: set_disconnected_nodes_get_child_nodes)
      then have children_eq2_h'3: "\<And>ptr. |h'3 \<turnstile> get_child_nodes ptr|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr|\<^sub>r"
        using select_result_eq by force

      show ?thesis
        by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_h'2_eq3 object_ptr_kinds_h'3_eq3
            children_eq2_h'3 children_eq2_h'2)
    qed
    ultimately
    show ?thesis
      by simp
  qed

  have "parent_child_rel h2 = parent_child_rel h3"
    by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_M_eq3_h2 children_eq2_h2)
  have "parent_child_rel h' = insert (ptr, cast node) ((parent_child_rel h3))"
    using children_h3 children_h' ptr_in_heap
    apply(auto simp add: CD.parent_child_rel_def object_ptr_kinds_M_eq3_h' children_eq2_h3
        insert_before_list_node_in_set)[1]
     apply (metis (no_types, lifting) children_eq2_h3 insert_before_list_in_set select_result_I2)
    by (metis (no_types, lifting) children_eq2_h3 imageI insert_before_list_in_set select_result_I2)

  have "a_ptr_disconnected_node_rel h3 \<subseteq> a_ptr_disconnected_node_rel h"
  proof -
    have "a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h2 - {(cast owner_document, cast node)}"
      apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h2)[1]
         apply(case_tac "aa = owner_document")
      using disconnected_nodes_h2 disconnected_nodes_h3 notin_set_remove1 apply fastforce
      using disconnected_nodes_eq2_h2 apply auto[1]
      using node_not_in_disconnected_nodes apply blast
       apply(case_tac "aa = owner_document")
      using disconnected_nodes_h2 disconnected_nodes_h3 notin_set_remove1 apply fastforce
      using disconnected_nodes_eq2_h2 apply auto[1]
      apply(case_tac "aa = owner_document")
      using disconnected_nodes_h2 disconnected_nodes_h3 notin_set_remove1 apply fastforce
      using disconnected_nodes_eq2_h2 apply auto[1]
      done
    then have "a_ptr_disconnected_node_rel h'2 \<subseteq> a_ptr_disconnected_node_rel h \<union> {(cast old_document, cast node)}"
      using h'2 parent_opt
    proof (induct parent_opt)
      case None
      then show ?case
        by auto
    next
      case (Some parent)
      then
      have h'2: "h \<turnstile> remove_child parent node \<rightarrow>\<^sub>h h'2"
        by auto
      then
      have "parent |\<in>| object_ptr_kinds h"
        using CD.remove_child_ptr_in_heap
        by blast
      obtain children_h h''2 disconnected_nodes_h where
        owner_document: "h \<turnstile> get_owner_document (cast node) \<rightarrow>\<^sub>r old_document" and
        children_h: "h \<turnstile> get_child_nodes parent \<rightarrow>\<^sub>r children_h" and
        child_in_children_h: "node \<in> set children_h" and
        disconnected_nodes_h: "h \<turnstile>  get_disconnected_nodes old_document \<rightarrow>\<^sub>r disconnected_nodes_h" and
        h''2: "h \<turnstile>  set_disconnected_nodes old_document (node # disconnected_nodes_h) \<rightarrow>\<^sub>h h''2" and
        h'2: "h''2 \<turnstile> set_child_nodes parent (remove1 node children_h) \<rightarrow>\<^sub>h h'2"
        using h'2 old_document
        apply(auto simp add: CD.remove_child_def elim!: bind_returns_heap_E
            dest!: pure_returns_heap_eq[rotated, OF get_owner_document_pure]
            pure_returns_heap_eq[rotated, OF get_child_nodes_pure] split: if_splits)[1]
        using pure_returns_heap_eq returns_result_eq by fastforce

      have disconnected_nodes_eq: "\<And>ptr' disc_nodes. ptr' \<noteq> old_document \<Longrightarrow>
h \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes = h''2 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes"
        using local.get_disconnected_nodes_reads set_disconnected_nodes_writes h''2
        apply(rule reads_writes_preserved)
        by (metis local.set_disconnected_nodes_get_disconnected_nodes_different_pointers)
      then
      have disconnected_nodes_eq2: "\<And>ptr'. ptr' \<noteq> old_document \<Longrightarrow>
|h \<turnstile> get_disconnected_nodes ptr'|\<^sub>r = |h''2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r"
        by (meson select_result_eq)
      have "h''2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r node # disconnected_nodes_h"
        using h''2 local.set_disconnected_nodes_get_disconnected_nodes
        by blast

      have disconnected_nodes_eq_h2:
        "\<And>ptr' disc_nodes. h''2 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes = h'2 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes"
        using local.get_disconnected_nodes_reads set_child_nodes_writes h'2
        apply(rule reads_writes_preserved)
        by (metis local.set_child_nodes_get_disconnected_nodes)
      then
      have disconnected_nodes_eq2_h2:
        "\<And>ptr'. |h''2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r = |h'2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r"
        by (meson select_result_eq)
      show ?case
        apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_hx
            \<open>\<And>ptr'. |h''2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r = |h'2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r\<close>[symmetric])[1]
         apply(case_tac "aa = old_document")
        using disconnected_nodes_h
          \<open>h''2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r node # disconnected_nodes_h\<close>
          apply(auto)[1]
         apply(auto dest!: disconnected_nodes_eq2)[1]
        apply(case_tac "aa = old_document")
        using disconnected_nodes_h
          \<open>h''2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r node # disconnected_nodes_h\<close>
         apply(auto)[1]
        apply(auto dest!: disconnected_nodes_eq2)[1]
        done
    qed
    show ?thesis
    proof(cases "owner_document = old_document")
      case True
      then have "a_ptr_disconnected_node_rel h'2 = a_ptr_disconnected_node_rel h2"
        using h2'
        by(auto simp add: a_ptr_disconnected_node_rel_def)
      then
      show ?thesis
        using \<open>a_ptr_disconnected_node_rel h3 =
a_ptr_disconnected_node_rel h2 - {(cast owner_document, cast node)}\<close>
        using True \<open>local.a_ptr_disconnected_node_rel h'2 \<subseteq> local.a_ptr_disconnected_node_rel h \<union>
{(cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r old_document, cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node)}\<close> by auto
    next
      case False
      then obtain h'3 old_disc_nodes disc_nodes_document_ptr_h'3 where
        docs_neq: "owner_document \<noteq> old_document" and
        old_disc_nodes: "h'2 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r old_disc_nodes" and
        h'3: "h'2 \<turnstile> set_disconnected_nodes old_document (remove1 node old_disc_nodes) \<rightarrow>\<^sub>h h'3" and
        disc_nodes_document_ptr_h3: "h'3 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disc_nodes_document_ptr_h'3" and
        h2': "h'3 \<turnstile> set_disconnected_nodes owner_document (node # disc_nodes_document_ptr_h'3) \<rightarrow>\<^sub>h h2"
        using h2'
        by(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated] )

      have object_ptr_kinds_h'2_eq3: "object_ptr_kinds h'2 = object_ptr_kinds h'3"
        apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h = object_ptr_kinds h'",
              OF set_disconnected_nodes_writes h'3])
        using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
        by (auto simp add: reflp_def transp_def)
      then have object_ptr_kinds_M_eq_h'2:
        "\<And>ptrs. h'2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h'3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
        by(simp add: object_ptr_kinds_M_defs)
      then have object_ptr_kinds_eq_h'2: "|h'2 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h'3 \<turnstile> object_ptr_kinds_M|\<^sub>r"
        by(simp)
      then have node_ptr_kinds_eq_h'2: "|h'2 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h'3 \<turnstile> node_ptr_kinds_M|\<^sub>r"
        using node_ptr_kinds_M_eq by blast
      then have node_ptr_kinds_eq3_h'2: "node_ptr_kinds h'2 = node_ptr_kinds h'3"
        by auto
      have document_ptr_kinds_eq2_h'2: "|h'2 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h'3 \<turnstile> document_ptr_kinds_M|\<^sub>r"
        using object_ptr_kinds_eq_h'2 document_ptr_kinds_M_eq by auto
      then have document_ptr_kinds_eq3_h'2: "document_ptr_kinds h'2 = document_ptr_kinds h'3"
        using object_ptr_kinds_eq_h'2 document_ptr_kinds_M_eq by auto

      have disconnected_nodes_eq: "\<And>ptr' disc_nodes. ptr' \<noteq> old_document \<Longrightarrow>
h'2 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes = h'3 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes"
        using local.get_disconnected_nodes_reads set_disconnected_nodes_writes h'3
        apply(rule reads_writes_preserved)
        by (metis local.set_disconnected_nodes_get_disconnected_nodes_different_pointers)
      then
      have disconnected_nodes_eq2: "\<And>ptr'. ptr' \<noteq> old_document \<Longrightarrow>
|h'2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r = |h'3 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r"
        by (meson select_result_eq)
      have "h'3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r (remove1 node old_disc_nodes)"
        using h'3 local.set_disconnected_nodes_get_disconnected_nodes
        by blast

      have object_ptr_kinds_h'3_eq3: "object_ptr_kinds h'3 = object_ptr_kinds h2"
        apply(rule writes_small_big[where P="\<lambda>h h2. object_ptr_kinds h = object_ptr_kinds h2",
              OF set_disconnected_nodes_writes h2'])
        using set_disconnected_nodes_pointers_preserved set_child_nodes_pointers_preserved
        by (auto simp add: reflp_def transp_def)
      then have object_ptr_kinds_M_eq_h'3: "\<And>ptrs. h'3 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs = h2 \<turnstile> object_ptr_kinds_M \<rightarrow>\<^sub>r ptrs"
        by(simp add: object_ptr_kinds_M_defs)
      then have object_ptr_kinds_eq_h'3: "|h'3 \<turnstile> object_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> object_ptr_kinds_M|\<^sub>r"
        by(simp)
      then have node_ptr_kinds_eq_h'3: "|h'3 \<turnstile> node_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> node_ptr_kinds_M|\<^sub>r"
        using node_ptr_kinds_M_eq by blast
      then have node_ptr_kinds_eq3_h'3: "node_ptr_kinds h'3 = node_ptr_kinds h2"
        by auto
      have document_ptr_kinds_eq2_h'3: "|h'3 \<turnstile> document_ptr_kinds_M|\<^sub>r = |h2 \<turnstile> document_ptr_kinds_M|\<^sub>r"
        using object_ptr_kinds_eq_h'3 document_ptr_kinds_M_eq by auto
      then have document_ptr_kinds_eq3_h'3: "document_ptr_kinds h'3 = document_ptr_kinds h2"
        using object_ptr_kinds_eq_h'3 document_ptr_kinds_M_eq by auto
      have disc_nodes_eq_h'3:
        "\<And>ptr disc_nodes. h'3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r disc_nodes = h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r disc_nodes"
        using get_child_nodes_reads set_disconnected_nodes_writes h2'
        apply(rule reads_writes_preserved)
        by (simp add: set_disconnected_nodes_get_child_nodes)
      then have disc_nodes_eq2_h'3: "\<And>ptr. |h'3 \<turnstile> get_child_nodes ptr|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr|\<^sub>r"
        using select_result_eq by force

      have disconnected_nodes_eq: "\<And>ptr' disc_nodes. ptr' \<noteq> owner_document \<Longrightarrow>
h'3 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes = h2 \<turnstile> get_disconnected_nodes ptr' \<rightarrow>\<^sub>r disc_nodes"
        using local.get_disconnected_nodes_reads set_disconnected_nodes_writes h2'
        apply(rule reads_writes_preserved)
        by (metis local.set_disconnected_nodes_get_disconnected_nodes_different_pointers)
      then
      have disconnected_nodes_eq2': "\<And>ptr'. ptr' \<noteq> owner_document \<Longrightarrow>
|h'3 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes ptr'|\<^sub>r"
        by (meson select_result_eq)
      have "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r (node # disc_nodes_document_ptr_h'3)"
        using h2' local.set_disconnected_nodes_get_disconnected_nodes
        by blast

      have "a_ptr_disconnected_node_rel h'3 = a_ptr_disconnected_node_rel h'2 - {(cast old_document, cast node)}"
        apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq2_h'2[simplified])[1]
           apply(case_tac "aa = old_document")
        using \<open>h'3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r (remove1 node old_disc_nodes)\<close>
          notin_set_remove1 old_disc_nodes
            apply fastforce
           apply(auto dest!: disconnected_nodes_eq2)[1]
        using \<open>h'3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r remove1 node old_disc_nodes\<close> h'3
          local.remove_from_disconnected_nodes_removes old_disc_nodes wellformed_h'2
          apply auto[1]
         defer
         apply(case_tac "aa = old_document")
        using \<open>h'3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r (remove1 node old_disc_nodes)\<close>
          notin_set_remove1 old_disc_nodes
          apply fastforce
         apply(auto dest!: disconnected_nodes_eq2)[1]
        apply(case_tac "aa = old_document")
        using \<open>h'3 \<turnstile> get_disconnected_nodes old_document \<rightarrow>\<^sub>r (remove1 node old_disc_nodes)\<close>
          notin_set_remove1 old_disc_nodes
         apply fastforce
        apply(auto dest!: disconnected_nodes_eq2)[1]
        done
      moreover
      have "a_ptr_disconnected_node_rel h2 = a_ptr_disconnected_node_rel h'3 \<union>
{(cast owner_document, cast node)}"
        apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq2_h'3[simplified])[1]
           apply(case_tac "aa = owner_document")
            apply(simp)
           apply(auto dest!: disconnected_nodes_eq2')[1]
          apply(case_tac "aa = owner_document")
        using \<open>h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r node # disc_nodes_document_ptr_h'3\<close>
          disc_nodes_document_ptr_h3 apply auto[1]
          apply(auto dest!: disconnected_nodes_eq2')[1]
        using \<open>node \<in> set disconnected_nodes_h2\<close> disconnected_nodes_h2 local.a_ptr_disconnected_node_rel_def
          local.a_ptr_disconnected_node_rel_disconnected_node apply blast
        defer
        apply(case_tac "aa = owner_document")
        using \<open>h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r node # disc_nodes_document_ptr_h'3\<close>
          disc_nodes_document_ptr_h3 apply auto[1]
        apply(auto dest!: disconnected_nodes_eq2')[1]
        done
      ultimately show ?thesis
        using \<open>a_ptr_disconnected_node_rel h3 =
a_ptr_disconnected_node_rel h2 - {(cast owner_document, cast node)}\<close>
        using \<open>a_ptr_disconnected_node_rel h'2 \<subseteq>
a_ptr_disconnected_node_rel h \<union> {(cast old_document, cast node)}\<close>
        by blast
    qed
  qed

  have "(cast node, ptr) \<notin> (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)\<^sup>*"
    using h2
    apply(auto simp add: adopt_node_def elim!: bind_returns_heap_E2 split: if_splits)[1]
    using ancestors assms(1) assms(2) assms(3) local.get_ancestors_di_parent_child_a_host_shadow_root_rel node_not_in_ancestors
    by blast
  then
  have "(cast node, ptr) \<notin> (parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)\<^sup>*"
    apply(simp add: \<open>a_host_shadow_root_rel h = a_host_shadow_root_rel h2\<close> \<open>a_host_shadow_root_rel h2 = a_host_shadow_root_rel h3\<close>)
    apply(simp add: \<open>parent_child_rel h2 = parent_child_rel h3\<close>[symmetric])
    using \<open>parent_child_rel h2 \<subseteq> parent_child_rel h\<close> \<open>a_ptr_disconnected_node_rel h3 \<subseteq> a_ptr_disconnected_node_rel h\<close>
    by (smt Un_assoc in_rtrancl_UnI sup.orderE sup_left_commute)

  have "CD.a_acyclic_heap h'"
  proof -
    have "acyclic (parent_child_rel h2)"
      using wellformed_h2  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def)
    then have "acyclic (parent_child_rel h3)"
      by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_M_eq3_h2 children_eq2_h2)
    moreover have "cast node \<notin> {x. (x, ptr) \<in> (parent_child_rel h3)\<^sup>*}"
      by (meson \<open>(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r node, ptr) \<notin> (parent_child_rel h3 \<union> local.a_host_shadow_root_rel h3 \<union>
local.a_ptr_disconnected_node_rel h3)\<^sup>*\<close> in_rtrancl_UnI mem_Collect_eq)
    ultimately show ?thesis
      using \<open>parent_child_rel h' = insert (ptr, cast node) ((parent_child_rel h3))\<close>
      by(auto simp add: CD.acyclic_heap_def)
  qed


  moreover have "CD.a_all_ptrs_in_heap h2"
    using wellformed_h2  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  have "CD.a_all_ptrs_in_heap h'"
  proof -
    have "CD.a_all_ptrs_in_heap h3"
      using \<open>CD.a_all_ptrs_in_heap h2\<close>
      apply(auto simp add: CD.a_all_ptrs_in_heap_def object_ptr_kinds_M_eq2_h2 node_ptr_kinds_eq2_h2
          children_eq_h2)[1]
       apply (metis \<open>known_ptrs h3\<close> \<open>type_wf h3\<close> children_eq_h2
          l_heap_is_wellformed.heap_is_wellformed_children_in_heap local.get_child_nodes_ok
          local.known_ptrs_known_ptr local.l_heap_is_wellformed_axioms node_ptr_kinds_commutes
          object_ptr_kinds_eq_h2 returns_result_select_result wellformed_h2)
      by (metis (mono_tags, hide_lams) disconnected_nodes_eq2_h2 disconnected_nodes_h2
          disconnected_nodes_h3 document_ptr_kinds_eq_h2 finite_set_in node_ptr_kinds_commutes
          object_ptr_kinds_eq_h2 select_result_I2 set_remove1_subset subsetD)
    have "set children_h3  \<subseteq> set |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
      using children_h3 \<open>CD.a_all_ptrs_in_heap h3\<close>
      apply(auto simp add: CD.a_all_ptrs_in_heap_def node_ptr_kinds_eq2_h3)[1]
      using children_eq_h2 local.heap_is_wellformed_children_in_heap node_ptr_kinds_eq2_h2
        node_ptr_kinds_eq2_h3 wellformed_h2 by auto
    then have "set (insert_before_list node reference_child children_h3) \<subseteq> set |h' \<turnstile> node_ptr_kinds_M|\<^sub>r"
      using node_in_heap
      apply(auto simp add: node_ptr_kinds_eq2_h node_ptr_kinds_eq2_h2 node_ptr_kinds_eq2_h3)[1]
      by (metis (no_types, hide_lams) contra_subsetD finite_set_in insert_before_list_in_set
          node_ptr_kinds_commutes object_ptr_kinds_M_eq3_h object_ptr_kinds_M_eq3_h' object_ptr_kinds_M_eq3_h2)
    then show ?thesis
      using \<open>CD.a_all_ptrs_in_heap h3\<close>
      apply(auto simp add: object_ptr_kinds_M_eq3_h' CD.a_all_ptrs_in_heap_def node_ptr_kinds_def
          node_ptr_kinds_eq2_h3 disconnected_nodes_eq_h3)[1]
       apply (metis (no_types, lifting) children_eq2_h3 children_h' finite_set_in select_result_I2 subsetD)
      by (metis (no_types, lifting) disconnected_nodes_eq2_h3 document_ptr_kinds_eq_h3 in_mono notin_fset)
  qed


  moreover have "CD.a_distinct_lists h2"
    using wellformed_h2  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def )
  then have "CD.a_distinct_lists h3"
  proof(auto simp add: CD.a_distinct_lists_def object_ptr_kinds_M_eq2_h2 document_ptr_kinds_eq2_h2
      children_eq2_h2 intro!: distinct_concat_map_I)
    fix x
    assume 1: "x |\<in>| document_ptr_kinds h3"
      and 2: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
(sorted_list_of_set (fset (document_ptr_kinds h3)))))"
    show "distinct |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using distinct_concat_map_E(2)[OF 2] select_result_I2[OF disconnected_nodes_h3]
        disconnected_nodes_eq2_h2 select_result_I2[OF disconnected_nodes_h2] 1
      by (metis (full_types) distinct_remove1 finite_fset fmember.rep_eq set_sorted_list_of_set)
  next
    fix x y xa
    assume 1: "distinct (concat (map (\<lambda>document_ptr. |h2 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
(sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and 2: "x |\<in>| document_ptr_kinds h3"
      and 3: "y |\<in>| document_ptr_kinds h3"
      and 4: "x \<noteq> y"
      and 5: "xa \<in> set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r"
      and 6: "xa \<in> set |h3 \<turnstile> get_disconnected_nodes y|\<^sub>r"
    show False
    proof (cases "x = owner_document")
      case True
      then have "y \<noteq> owner_document"
        using 4 by simp
      show ?thesis
        using distinct_concat_map_E(1)[OF 1]
        using 2 3 4 5 6 select_result_I2[OF disconnected_nodes_h3]  select_result_I2[OF disconnected_nodes_h2]
        apply(auto simp add: True disconnected_nodes_eq2_h2[OF \<open>y \<noteq> owner_document\<close>])[1]
        by (metis (no_types, hide_lams) disconnected_nodes_eq2_h2 disjoint_iff_not_equal notin_set_remove1)
    next
      case False
      then show ?thesis
      proof (cases "y = owner_document")
        case True
        then show ?thesis
          using distinct_concat_map_E(1)[OF 1]
          using 2 3 4 5 6 select_result_I2[OF disconnected_nodes_h3]  select_result_I2[OF disconnected_nodes_h2]
          apply(auto simp add: True disconnected_nodes_eq2_h2[OF \<open>x \<noteq> owner_document\<close>])[1]
          by (metis (no_types, hide_lams) disconnected_nodes_eq2_h2 disjoint_iff_not_equal notin_set_remove1)
      next
        case False
        then show ?thesis
          using distinct_concat_map_E(1)[OF 1, simplified, OF 2 3 4] 5 6
          using disconnected_nodes_eq2_h2 disconnected_nodes_h2 disconnected_nodes_h3
            disjoint_iff_not_equal finite_fset fmember.rep_eq notin_set_remove1 select_result_I2
            set_sorted_list_of_set
          by (metis (no_types, lifting))
      qed
    qed
  next
    fix x xa xb
    assume 1: "(\<Union>x\<in>fset (object_ptr_kinds h3). set |h3 \<turnstile> get_child_nodes x|\<^sub>r) \<inter>
(\<Union>x\<in>fset (document_ptr_kinds h3). set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 2: "xa |\<in>| object_ptr_kinds h3"
      and 3: "x \<in> set |h3 \<turnstile> get_child_nodes xa|\<^sub>r"
      and 4: "xb |\<in>| document_ptr_kinds h3"
      and 5: "x \<in> set |h3 \<turnstile> get_disconnected_nodes xb|\<^sub>r"
    have 6: "set |h3 \<turnstile> get_child_nodes xa|\<^sub>r \<inter> set |h2 \<turnstile> get_disconnected_nodes xb|\<^sub>r = {}"
      using 1 2 4
      by (metis \<open>type_wf h2\<close> children_eq2_h2 document_ptr_kinds_commutes \<open>known_ptrs h\<close>
          local.get_child_nodes_ok local.get_disconnected_nodes_ok local.heap_is_wellformed_children_disc_nodes_different
          local.known_ptrs_known_ptr object_ptr_kinds_M_eq3_h object_ptr_kinds_M_eq3_h2 returns_result_select_result wellformed_h2)
    show False
    proof (cases "xb = owner_document")
      case True
      then show ?thesis
        using select_result_I2[OF disconnected_nodes_h3,folded select_result_I2[OF disconnected_nodes_h2]]
        by (metis (no_types, lifting) "3" "5" "6" disjoint_iff_not_equal notin_set_remove1)
    next
      case False
      show ?thesis
        using 2 3 4 5 6 unfolding disconnected_nodes_eq2_h2[OF False] by auto
    qed
  qed
  then have "CD.a_distinct_lists h'"
  proof(auto simp add: CD.a_distinct_lists_def document_ptr_kinds_eq2_h3 object_ptr_kinds_M_eq2_h3
      disconnected_nodes_eq2_h3 intro!: distinct_concat_map_I)
    fix x
    assume 1: "distinct (concat (map (\<lambda>ptr. |h3 \<turnstile> get_child_nodes ptr|\<^sub>r) (sorted_list_of_set (fset (object_ptr_kinds h')))))" and
      2: "x |\<in>| object_ptr_kinds h'"
    have 3: "\<And>p. p |\<in>| object_ptr_kinds h' \<Longrightarrow> distinct |h3 \<turnstile> get_child_nodes p|\<^sub>r"
      using 1  by (auto elim: distinct_concat_map_E)
    show "distinct |h' \<turnstile> get_child_nodes x|\<^sub>r"
    proof(cases "ptr = x")
      case True
      show ?thesis
        using 3[OF 2] children_h3 children_h'
        by(auto simp add: True  insert_before_list_distinct dest: child_not_in_any_children[unfolded children_eq_h2])
    next
      case False
      show ?thesis
        using children_eq2_h3[OF False] 3[OF 2] by auto
    qed
  next
    fix x y xa
    assume 1: "distinct (concat (map (\<lambda>ptr. |h3 \<turnstile> get_child_nodes ptr|\<^sub>r) (sorted_list_of_set (fset (object_ptr_kinds h')))))"
      and 2: "x |\<in>| object_ptr_kinds h'"
      and 3: "y |\<in>| object_ptr_kinds h'"
      and 4: "x \<noteq> y"
      and 5: "xa \<in> set |h' \<turnstile> get_child_nodes x|\<^sub>r"
      and 6: "xa \<in> set |h' \<turnstile> get_child_nodes y|\<^sub>r"
    have 7:"set |h3 \<turnstile> get_child_nodes x|\<^sub>r \<inter> set |h3 \<turnstile> get_child_nodes y|\<^sub>r = {}"
      using distinct_concat_map_E(1)[OF 1] 2 3 4 by auto
    show False
    proof (cases "ptr = x")
      case True
      then have "ptr \<noteq> y"
        using 4 by simp
      then show ?thesis
        using  children_h3 children_h' child_not_in_any_children[unfolded children_eq_h2] 5 6
        apply(auto simp add:  True children_eq2_h3[OF \<open>ptr \<noteq> y\<close>])[1]
        by (metis (no_types, hide_lams) "3" "7" \<open>type_wf h3\<close> children_eq2_h3 disjoint_iff_not_equal
            get_child_nodes_ok insert_before_list_in_set \<open>known_ptrs h\<close> local.known_ptrs_known_ptr
            object_ptr_kinds_M_eq3_h object_ptr_kinds_M_eq3_h' object_ptr_kinds_M_eq3_h2
            returns_result_select_result select_result_I2)
    next
      case False
      then show ?thesis
      proof (cases "ptr = y")
        case True
        then show ?thesis
          using  children_h3 children_h' child_not_in_any_children[unfolded children_eq_h2] 5 6
          apply(auto simp add:  True children_eq2_h3[OF \<open>ptr \<noteq> x\<close>])[1]
          by (metis (no_types, hide_lams) "2" "4" "7" IntI \<open>known_ptrs h3\<close> \<open>type_wf h'\<close>
              children_eq_h3 empty_iff insert_before_list_in_set local.get_child_nodes_ok local.known_ptrs_known_ptr
              object_ptr_kinds_M_eq3_h' returns_result_select_result select_result_I2)
      next
        case False
        then show ?thesis
          using children_eq2_h3[OF \<open>ptr \<noteq> x\<close>] children_eq2_h3[OF \<open>ptr \<noteq> y\<close>] 5 6 7 by auto
      qed
    qed
  next
    fix x xa xb
    assume 1: " (\<Union>x\<in>fset (object_ptr_kinds h'). set |h3 \<turnstile> get_child_nodes x|\<^sub>r) \<inter> (\<Union>x\<in>fset (document_ptr_kinds h'). set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r) = {} "
      and 2: "xa |\<in>| object_ptr_kinds h'"
      and 3: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
      and 4: "xb |\<in>| document_ptr_kinds h'"
      and 5: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
    have 6: "set |h3 \<turnstile> get_child_nodes xa|\<^sub>r \<inter> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r = {}"
      using 1 2 3 4 5
    proof -
      have "\<forall>h d. \<not> type_wf h \<or> d |\<notin>| document_ptr_kinds h \<or> h \<turnstile> ok get_disconnected_nodes d"
        using local.get_disconnected_nodes_ok by satx
      then have "h' \<turnstile> ok get_disconnected_nodes xb"
        using "4" \<open>type_wf h'\<close> by fastforce
      then have f1: "h3 \<turnstile> get_disconnected_nodes xb \<rightarrow>\<^sub>r |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
        by (simp add: disconnected_nodes_eq_h3)
      have "xa |\<in>| object_ptr_kinds h3"
        using "2" object_ptr_kinds_M_eq3_h' by blast
      then show ?thesis
        using f1 \<open>local.CD.a_distinct_lists h3\<close> CD.distinct_lists_no_parent by fastforce
    qed
    show False
    proof (cases "ptr = xa")
      case True
      show ?thesis
        using 6 node_not_in_disconnected_nodes  3 4 5  select_result_I2[OF children_h']
          select_result_I2[OF children_h3] True disconnected_nodes_eq2_h3
        by (metis (no_types, lifting) "2" DocumentMonad.ptr_kinds_ptr_kinds_M \<open>CD.a_distinct_lists h3\<close>
            \<open>type_wf h'\<close> disconnected_nodes_eq_h3 CD.distinct_lists_no_parent document_ptr_kinds_eq2_h3
            get_disconnected_nodes_ok insert_before_list_in_set object_ptr_kinds_M_eq3_h' returns_result_select_result)

    next
      case False
      then show ?thesis
        using 1 2 3 4 5 children_eq2_h3[OF False] by fastforce
    qed
  qed

  moreover have "CD.a_owner_document_valid h2"
    using wellformed_h2  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_owner_document_valid h'"
    apply(auto simp add: CD.a_owner_document_valid_def object_ptr_kinds_M_eq2_h2 object_ptr_kinds_M_eq2_h3
        node_ptr_kinds_eq2_h2 node_ptr_kinds_eq2_h3 document_ptr_kinds_eq2_h2 document_ptr_kinds_eq2_h3 children_eq2_h2 )[1]
    apply(auto simp add: document_ptr_kinds_eq2_h2[simplified]  document_ptr_kinds_eq2_h3[simplified]
        object_ptr_kinds_M_eq2_h2[simplified] object_ptr_kinds_M_eq2_h3[simplified] node_ptr_kinds_eq2_h2[simplified]
        node_ptr_kinds_eq2_h3[simplified])[1]
    apply(auto simp add: disconnected_nodes_eq2_h3[symmetric])[1]
    by (smt Core_DOM_Functions.i_insert_before.insert_before_list_in_set children_eq2_h3 children_h'
        children_h3 disconnected_nodes_eq2_h2 disconnected_nodes_h2 disconnected_nodes_h3 finite_set_in in_set_remove1
        object_ptr_kinds_eq_h3 ptr_in_heap select_result_I2)

  ultimately have "heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M h'"
    by (simp add: CD.heap_is_wellformed_def)

  have "a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h2 - {(cast owner_document, cast node)}"
    apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h2 disconnected_nodes_eq2_h2)[1]
      apply(case_tac "aa = owner_document")
       apply (metis (no_types, lifting) case_prodI disconnected_nodes_h2 disconnected_nodes_h3
        in_set_remove1 mem_Collect_eq node_not_in_disconnected_nodes pair_imageI select_result_I2)
    using disconnected_nodes_eq2_h2 apply auto[1]
    using node_not_in_disconnected_nodes apply blast
    by (metis (no_types, lifting) case_prodI disconnected_nodes_eq2_h2 disconnected_nodes_h2
        disconnected_nodes_h3 in_set_remove1 mem_Collect_eq pair_imageI select_result_I2)
  have "a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h'"
    by(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h3 disconnected_nodes_eq2_h3)

  have "acyclic (parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)"
    using \<open>heap_is_wellformed h2\<close>
    by(auto simp add: \<open>a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h2 - {(cast owner_document, cast node)}\<close>
        heap_is_wellformed_def \<open>parent_child_rel h2 = parent_child_rel h3\<close> \<open>a_host_shadow_root_rel h2 = a_host_shadow_root_rel h3\<close> elim!: acyclic_subset)
  then
  have "acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> local.a_ptr_disconnected_node_rel h')"
    using \<open>(cast node, ptr) \<notin> (parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)\<^sup>*\<close>
    by(auto simp add: \<open>a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h'\<close> \<open>a_host_shadow_root_rel h3 =
a_host_shadow_root_rel h'\<close> \<open>parent_child_rel h' = insert (ptr, cast node) ((parent_child_rel h3))\<close>)
  then
  show "heap_is_wellformed h'"
    using \<open>heap_is_wellformed h2\<close>
    using \<open>heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M h'\<close>
    apply(auto simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def
        a_all_ptrs_in_heap_def a_distinct_lists_def a_shadow_root_valid_def)[1]
    by(auto simp add: object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 element_ptr_kinds_eq_h2
        element_ptr_kinds_eq_h3 shadow_root_ptr_kinds_eq_h2 shadow_root_ptr_kinds_eq_h3  shadow_root_eq_h2
        shadow_root_eq_h3 shadow_root_eq2_h2 shadow_root_eq2_h3 tag_name_eq_h2 tag_name_eq_h3 tag_name_eq2_h2
        tag_name_eq2_h3)

qed
end

interpretation i_insert_before_wf?: l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_parent get_parent_locs get_child_nodes
  get_child_nodes_locs set_child_nodes set_child_nodes_locs get_ancestors_di get_ancestors_di_locs adopt_node
  adopt_node_locs set_disconnected_nodes set_disconnected_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_owner_document insert_before insert_before_locs append_child type_wf known_ptr known_ptrs heap_is_wellformed
  parent_child_rel
  by(simp add: l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_insert_before_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma insert_before_wf_is_l_insert_before_wf [instances]: "l_insert_before_wf Shadow_DOM.heap_is_wellformed
ShadowRootClass.type_wf ShadowRootClass.known_ptr ShadowRootClass.known_ptrs
     Shadow_DOM.insert_before Shadow_DOM.get_child_nodes"
  apply(auto simp add: l_insert_before_wf_def l_insert_before_wf_axioms_def instances)[1]
  using insert_before_removes_child apply fast
  done

lemma l_set_disconnected_nodes_get_disconnected_nodes_wf [instances]: "l_set_disconnected_nodes_get_disconnected_nodes_wf ShadowRootClass.type_wf
ShadowRootClass.known_ptr Shadow_DOM.heap_is_wellformed Shadow_DOM.parent_child_rel Shadow_DOM.get_child_nodes
     get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs"
  apply(auto simp add: l_set_disconnected_nodes_get_disconnected_nodes_wf_def l_set_disconnected_nodes_get_disconnected_nodes_wf_axioms_def instances)[1]
  by (metis Diff_iff Shadow_DOM.i_heap_is_wellformed.heap_is_wellformed_disconnected_nodes_distinct Shadow_DOM.i_remove_child.set_disconnected_nodes_get_disconnected_nodes insert_iff returns_result_eq set_remove1_eq)

interpretation i_insert_before_wf2?: l_insert_before_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  set_child_nodes set_child_nodes_locs get_shadow_root get_shadow_root_locs set_disconnected_nodes
  set_disconnected_nodes_locs get_tag_name get_tag_name_locs heap_is_wellformed parent_child_rel get_parent
  get_parent_locs adopt_node adopt_node_locs get_owner_document insert_before insert_before_locs append_child
  known_ptrs remove_child remove_child_locs get_ancestors_di get_ancestors_di_locs adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document get_disconnected_document_locs
  remove heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  by(auto simp add: l_insert_before_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_insert_before_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


lemma insert_before_wf2_is_l_insert_before_wf2 [instances]:
  "l_insert_before_wf2 ShadowRootClass.type_wf ShadowRootClass.known_ptr ShadowRootClass.known_ptrs Shadow_DOM.insert_before
     Shadow_DOM.heap_is_wellformed"
  apply(auto simp add: l_insert_before_wf2_def l_insert_before_wf2_axioms_def instances)[1]
  using insert_before_child_preserves apply(fast, fast, fast)
  done


subsubsection \<open>append\_child\<close>

locale l_append_child_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_insert_before_wf2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_append_child\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma append_child_heap_is_wellformed_preserved:
  assumes wellformed: "heap_is_wellformed h"
    and append_child: "h \<turnstile> append_child ptr node \<rightarrow>\<^sub>h h'"
    and known_ptrs: "known_ptrs h"
    and type_wf: "type_wf h"
  shows "heap_is_wellformed h'" and "type_wf h'" and "known_ptrs h'"
  using assms
  by(auto simp add: append_child_def intro: insert_before_child_preserves)

lemma append_child_children:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
  assumes "h \<turnstile> append_child ptr node \<rightarrow>\<^sub>h h'"
  assumes "node \<notin> set xs"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs @ [node]"
proof -

  obtain ancestors owner_document h2 h3 disconnected_nodes_h2 where
    ancestors: "h \<turnstile> get_ancestors_di ptr \<rightarrow>\<^sub>r ancestors" and
    node_not_in_ancestors: "cast node \<notin> set ancestors" and
    owner_document: "h \<turnstile> get_owner_document ptr \<rightarrow>\<^sub>r owner_document" and
    h2: "h \<turnstile> adopt_node owner_document node \<rightarrow>\<^sub>h h2" and
    disconnected_nodes_h2: "h2 \<turnstile> get_disconnected_nodes owner_document \<rightarrow>\<^sub>r disconnected_nodes_h2" and
    h3: "h2 \<turnstile> set_disconnected_nodes owner_document (remove1 node disconnected_nodes_h2) \<rightarrow>\<^sub>h h3" and
    h': "h3 \<turnstile> a_insert_node ptr node None \<rightarrow>\<^sub>h h'"
    using assms(5)
    by(auto simp add: append_child_def insert_before_def a_ensure_pre_insertion_validity_def
        elim!: bind_returns_heap_E bind_returns_result_E
        bind_returns_heap_E2[rotated, OF get_parent_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_disconnected_nodes_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_ancestors_pure, rotated]
        bind_returns_heap_E2[rotated, OF next_sibling_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_owner_document_pure, rotated]
        split: if_splits option.splits)

  have "\<And>parent. |h \<turnstile> get_parent node|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr"
    using assms(1) assms(4) assms(6)
    by (metis (no_types, lifting) assms(2) assms(3) h2 is_OK_returns_heap_I is_OK_returns_result_E
        local.adopt_node_child_in_heap local.get_parent_child_dual local.get_parent_ok
        select_result_I2)
  have "h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
    using get_child_nodes_reads adopt_node_writes h2 assms(4)
    apply(rule reads_writes_separate_forwards)
    using \<open>\<And>parent. |h \<turnstile> get_parent node|\<^sub>r = Some parent \<Longrightarrow> parent \<noteq> ptr\<close>
    apply(auto simp add: adopt_node_locs_def CD.adopt_node_locs_def CD.remove_child_locs_def)[1]
    by (meson local.set_child_nodes_get_child_nodes_different_pointers)

  have "h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
    using get_child_nodes_reads set_disconnected_nodes_writes h3 \<open>h2 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs\<close>
    apply(rule reads_writes_separate_forwards)
    by(auto)

  have "ptr |\<in>| object_ptr_kinds h"
    by (meson ancestors is_OK_returns_result_I local.get_ancestors_ptr_in_heap)
  then
  have "known_ptr ptr"
    using assms(3)
    using local.known_ptrs_known_ptr by blast

  have "type_wf h2"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF adopt_node_writes h2]
    using adopt_node_types_preserved  \<open>type_wf h\<close>
    by(auto simp add: adopt_node_locs_def remove_child_locs_def reflp_def transp_def split: if_splits)
  then
  have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h3]
    using  set_disconnected_nodes_types_preserved
    by(auto simp add: reflp_def transp_def)

  show "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs@[node]"
    using h'
    apply(auto simp add: a_insert_node_def
        dest!: bind_returns_heap_E3[rotated, OF \<open>h3 \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs\<close>
          get_child_nodes_pure, rotated])[1]
    using \<open>type_wf h3\<close> set_child_nodes_get_child_nodes \<open>known_ptr ptr\<close>
    by metis
qed

lemma append_child_for_all_on_children:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
  assumes "h \<turnstile> forall_M (append_child ptr) nodes \<rightarrow>\<^sub>h h'"
  assumes "set nodes \<inter> set xs = {}"
  assumes "distinct nodes"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs@nodes"
  using assms
  apply(induct nodes arbitrary: h xs)
   apply(simp)
proof(auto elim!: bind_returns_heap_E)[1]fix a nodes h xs h'a
  assume 0: "(\<And>h xs. heap_is_wellformed h \<Longrightarrow> type_wf h \<Longrightarrow> known_ptrs h
              \<Longrightarrow> h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs \<Longrightarrow> h \<turnstile> forall_M (append_child ptr) nodes \<rightarrow>\<^sub>h h'
              \<Longrightarrow> set nodes \<inter> set xs = {} \<Longrightarrow> h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs @ nodes)"
    and 1: "heap_is_wellformed h"
    and 2: "type_wf h"
    and 3: "known_ptrs h"
    and 4: "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs"
    and 5: "h \<turnstile> append_child ptr a \<rightarrow>\<^sub>r ()"
    and 6: "h \<turnstile> append_child ptr a \<rightarrow>\<^sub>h h'a"
    and 7: "h'a \<turnstile> forall_M (append_child ptr) nodes \<rightarrow>\<^sub>h h'"
    and 8: "a \<notin> set xs"
    and 9: "set nodes \<inter> set xs = {}"
    and 10: "a \<notin> set nodes"
    and 11: "distinct nodes"
  then have "h'a \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs @ [a]"
    using append_child_children 6
    using "1" "2" "3" "4" "8" by blast

  moreover have "heap_is_wellformed h'a" and "type_wf h'a" and "known_ptrs h'a"
    using insert_before_child_preserves 1 2 3 6 append_child_def
    by metis+
  moreover have "set nodes \<inter> set (xs @ [a]) = {}"
    using 9 10
    by auto
  ultimately show "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r xs @ a # nodes"
    using 0 7
    by fastforce
qed


lemma append_child_for_all_on_no_children:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r []"
  assumes "h \<turnstile> forall_M (append_child ptr) nodes \<rightarrow>\<^sub>h h'"
  assumes "distinct nodes"
  shows "h' \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r nodes"
  using assms append_child_for_all_on_children
  by force
end

interpretation i_append_child_wf?: l_append_child_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs set_child_nodes set_child_nodes_locs get_shadow_root get_shadow_root_locs
  set_disconnected_nodes set_disconnected_nodes_locs get_tag_name get_tag_name_locs heap_is_wellformed
  parent_child_rel get_parent get_parent_locs adopt_node adopt_node_locs get_owner_document insert_before
  insert_before_locs append_child known_ptrs remove_child remove_child_locs get_ancestors_di
  get_ancestors_di_locs adopt_node\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M adopt_node_locs\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs remove heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  by(auto simp add: l_append_child_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_append_child_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma append_child_wf_is_l_append_child_wf [instances]:
  "l_append_child_wf type_wf known_ptr known_ptrs append_child heap_is_wellformed"
  apply(auto simp add: l_append_child_wf_def l_append_child_wf_axioms_def instances)[1]
  using append_child_heap_is_wellformed_preserved by fast+


subsubsection \<open>to\_tree\_order\<close>

interpretation i_to_tree_order_wf?: l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf get_child_nodes
  get_child_nodes_locs to_tree_order known_ptrs get_parent get_parent_locs heap_is_wellformed
  parent_child_rel get_disconnected_nodes get_disconnected_nodes_locs
  apply(auto simp add: l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)[1]
  done
declare l_to_tree_order_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma to_tree_order_wf_is_l_to_tree_order_wf [instances]:
  "l_to_tree_order_wf heap_is_wellformed parent_child_rel type_wf known_ptr known_ptrs
to_tree_order get_parent get_child_nodes"
  apply(auto simp add: l_to_tree_order_wf_def l_to_tree_order_wf_axioms_def instances)[1]
  using to_tree_order_ok apply fast
  using to_tree_order_ptrs_in_heap apply fast
  using to_tree_order_parent_child_rel apply(fast, fast)
  using to_tree_order_child2 apply blast
  using to_tree_order_node_ptrs apply fast
  using to_tree_order_child apply fast
  using to_tree_order_ptr_in_result apply fast
  using to_tree_order_parent apply fast
  using to_tree_order_subset apply fast
  done


paragraph \<open>get\_root\_node\<close>

interpretation i_to_tree_order_wf_get_root_node_wf?: l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr type_wf known_ptrs heap_is_wellformed parent_child_rel get_child_nodes get_child_nodes_locs
  get_disconnected_nodes get_disconnected_nodes_locs get_parent get_parent_locs get_ancestors
  get_ancestors_locs get_root_node get_root_node_locs to_tree_order
  by(auto simp add: l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_to_tree_order_wf_get_root_node_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

lemma to_tree_order_wf_get_root_node_wf_is_l_to_tree_order_wf_get_root_node_wf [instances]:
  "l_to_tree_order_wf_get_root_node_wf ShadowRootClass.type_wf ShadowRootClass.known_ptr
ShadowRootClass.known_ptrs to_tree_order Shadow_DOM.get_root_node
     Shadow_DOM.heap_is_wellformed"
  apply(auto simp add: l_to_tree_order_wf_get_root_node_wf_def
      l_to_tree_order_wf_get_root_node_wf_axioms_def instances)[1]
  using to_tree_order_get_root_node apply fast
  using to_tree_order_same_root apply fast
  done


subsubsection \<open>to\_tree\_order\_si\<close>

locale l_to_tree_order_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_child_nodes +
  l_get_parent_get_host_get_disconnected_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_to_tree_order_si\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin
lemma to_tree_order_si_ok:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
    and "ptr |\<in>| object_ptr_kinds h"
  shows "h \<turnstile> ok (to_tree_order_si ptr)"
proof(insert assms(1) assms(4), induct rule: heap_wellformed_induct_si)
  case (step parent)
  have "known_ptr parent"
    using assms(2) local.known_ptrs_known_ptr step.prems
    by blast
  then show ?case
    using step
    using assms(1) assms(2) assms(3)
    using local.heap_is_wellformed_children_in_heap local.get_shadow_root_shadow_root_ptr_in_heap
    by(auto simp add: to_tree_order_si_def[of parent] intro: get_child_nodes_ok get_shadow_root_ok
        intro!: bind_is_OK_pure_I map_M_pure_I bind_pure_I map_M_ok_I split: option.splits)
qed
end
interpretation i_to_tree_order_si_wf?: l_to_tree_order_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  type_wf known_ptr get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document get_disconnected_document_locs known_ptrs get_parent get_parent_locs to_tree_order_si
  by(auto simp add: l_to_tree_order_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_to_tree_order_si_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_assigned\_nodes\<close>

lemma forall_M_small_big: "h \<turnstile> forall_M f xs \<rightarrow>\<^sub>h h' \<Longrightarrow> P h \<Longrightarrow>
(\<And>h h' x. x \<in> set xs \<Longrightarrow> h \<turnstile> f x \<rightarrow>\<^sub>h h' \<Longrightarrow> P h \<Longrightarrow> P h') \<Longrightarrow> P h'"
  by(induct xs arbitrary: h) (auto elim!: bind_returns_heap_E)

locale l_assigned_nodes_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_assigned_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_heap_is_wellformed +
  l_remove_child_wf2 +
  l_append_child_wf +
  l_remove_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
begin

lemma assigned_nodes_distinct:
  assumes "heap_is_wellformed h"
  assumes "h \<turnstile> assigned_nodes slot \<rightarrow>\<^sub>r nodes"
  shows "distinct nodes"
proof -
  have "\<And>ptr children. h \<turnstile> get_child_nodes ptr \<rightarrow>\<^sub>r children \<Longrightarrow> distinct children"
    using assms(1) local.heap_is_wellformed_children_distinct by blast
  then show ?thesis
    using assms
    apply(auto simp add: assigned_nodes_def elim!: bind_returns_result_E2 split: if_splits)[1]
    by (simp add: filter_M_distinct)
qed


lemma flatten_dom_preserves:
  assumes "heap_is_wellformed h" and "known_ptrs h" and "type_wf h"
  assumes "h \<turnstile> flatten_dom \<rightarrow>\<^sub>h h'"
  shows "heap_is_wellformed h'" and "known_ptrs h'" and "type_wf h'"
proof -
  obtain tups h2 element_ptrs shadow_root_ptrs where
    "h \<turnstile> element_ptr_kinds_M \<rightarrow>\<^sub>r element_ptrs" and
    tups: "h \<turnstile> map_filter_M2 (\<lambda>element_ptr. do {
      tag \<leftarrow> get_tag_name element_ptr;
      assigned_nodes \<leftarrow> assigned_nodes element_ptr;
      (if tag = ''slot'' \<and> assigned_nodes \<noteq> []
then return (Some (element_ptr, assigned_nodes)) else return None)}) element_ptrs \<rightarrow>\<^sub>r tups"
    (is "h \<turnstile> map_filter_M2 ?f element_ptrs \<rightarrow>\<^sub>r tups") and
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
  have "heap_is_wellformed h2 \<and> known_ptrs h2 \<and> type_wf h2"
    using h2 \<open>heap_is_wellformed h\<close> \<open>known_ptrs h\<close> \<open>type_wf h\<close>
    by(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated]
        elim!: forall_M_small_big[where P = "\<lambda>h. heap_is_wellformed h \<and> known_ptrs h \<and> type_wf h", simplified]
        intro: remove_preserves_known_ptrs remove_heap_is_wellformed_preserved remove_preserves_type_wf
        append_child_preserves_known_ptrs append_child_heap_is_wellformed_preserved append_child_preserves_type_wf)
  then
  show "heap_is_wellformed h'" and "known_ptrs h'" and "type_wf h'"
    using h'
    by(auto elim!: bind_returns_heap_E bind_returns_heap_E2[rotated, OF get_host_pure, rotated] bind_returns_heap_E2[rotated, OF get_child_nodes_pure, rotated]
        dest!: forall_M_small_big[where P = "\<lambda>h. heap_is_wellformed h \<and> known_ptrs h \<and> type_wf h", simplified]
        intro: remove_preserves_known_ptrs remove_heap_is_wellformed_preserved remove_preserves_type_wf
        append_child_preserves_known_ptrs append_child_heap_is_wellformed_preserved append_child_preserves_type_wf
        remove_shadow_root_preserves
        )
qed
end

interpretation i_assigned_nodes_wf?: l_assigned_nodes_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  known_ptr assigned_nodes assigned_nodes_flatten flatten_dom get_child_nodes get_child_nodes_locs
  get_tag_name get_tag_name_locs get_root_node get_root_node_locs get_host get_host_locs find_slot
  assigned_slot remove insert_before insert_before_locs append_child remove_shadow_root
  remove_shadow_root_locs type_wf get_shadow_root get_shadow_root_locs set_shadow_root
  set_shadow_root_locs get_parent get_parent_locs to_tree_order heap_is_wellformed parent_child_rel
  get_disconnected_nodes get_disconnected_nodes_locs known_ptrs remove_child remove_child_locs
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_document get_disconnected_document_locs
  by(auto simp add: l_assigned_nodes_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_assigned_nodes_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>get\_shadow\_root\_safe\<close>

locale l_get_shadow_root_safe_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M  get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs
  known_ptr type_wf heap_is_wellformed parent_child_rel heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs +
  l_type_wf type_wf +
  l_get_shadow_root_safe\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf get_shadow_root_safe get_shadow_root_safe_locs get_shadow_root
  get_shadow_root_locs get_mode get_mode_locs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
    and known_ptrs :: "(_) heap \<Rightarrow> bool"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root_safe :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_safe_locs :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_child_nodes :: "(_::linorder) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
    and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
    and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
begin


end


subsubsection \<open>create\_element\<close>

locale l_create_element_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes type_wf get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_tag_name type_wf set_tag_name set_tag_name_locs +
  l_create_element_defs create_element +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M  get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs known_ptr type_wf
  heap_is_wellformed parent_child_rel
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs +
  l_new_element_get_disconnected_nodes get_disconnected_nodes get_disconnected_nodes_locs +
  l_set_tag_name_get_disconnected_nodes type_wf set_tag_name set_tag_name_locs
  get_disconnected_nodes get_disconnected_nodes_locs +
  l_create_element\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
  set_disconnected_nodes_locs set_tag_name set_tag_name_locs type_wf
  create_element known_ptr type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M +
  l_new_element_get_child_nodes type_wf known_ptr get_child_nodes get_child_nodes_locs +
  l_set_tag_name_get_child_nodes type_wf set_tag_name set_tag_name_locs known_ptr
  get_child_nodes get_child_nodes_locs +
  l_set_tag_name_get_tag_name type_wf get_tag_name get_tag_name_locs set_tag_name set_tag_name_locs +
  l_new_element_get_tag_name type_wf get_tag_name get_tag_name_locs +
  l_set_disconnected_nodes_get_child_nodes set_disconnected_nodes set_disconnected_nodes_locs
  get_child_nodes get_child_nodes_locs +
  l_set_disconnected_nodes_get_shadow_root set_disconnected_nodes set_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs +
  l_set_disconnected_nodes_get_tag_name type_wf set_disconnected_nodes set_disconnected_nodes_locs
  get_tag_name get_tag_name_locs +
  l_set_disconnected_nodes type_wf set_disconnected_nodes set_disconnected_nodes_locs +
  l_set_disconnected_nodes_get_disconnected_nodes  type_wf get_disconnected_nodes
  get_disconnected_nodes_locs set_disconnected_nodes set_disconnected_nodes_locs +
  l_new_element_get_shadow_root type_wf get_shadow_root get_shadow_root_locs +
  l_set_tag_name_get_shadow_root type_wf set_tag_name set_tag_name_locs get_shadow_root get_shadow_root_locs +
  l_new_element type_wf +
  l_known_ptrs known_ptr known_ptrs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
    and known_ptrs :: "(_) heap \<Rightarrow> bool"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
    and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
    and set_tag_name :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and create_element :: "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_document :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_::linorder) object_ptr \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
begin
lemma create_element_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>h h'"
    and "type_wf h"
    and "known_ptrs h"
  shows "heap_is_wellformed h'" and "type_wf h'" and "known_ptrs h'"
proof -
  obtain new_element_ptr h2 h3 disc_nodes_h3 where
    new_element_ptr: "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr" and
    h2: "h \<turnstile> new_element \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile> set_tag_name new_element_ptr tag \<rightarrow>\<^sub>h h3" and
    disc_nodes_h3: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_element_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'"
    using assms(2)
    by(auto simp add: create_element_def
        elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF CD.get_disconnected_nodes_pure, rotated] )
  then have "h \<turnstile> create_element document_ptr tag \<rightarrow>\<^sub>r new_element_ptr"
    apply(auto simp add: create_element_def intro!: bind_returns_result_I)[1]
      apply (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
     apply (metis is_OK_returns_heap_E is_OK_returns_result_I CD.get_disconnected_nodes_pure
        pure_returns_heap_eq)
    by (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)

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
  then have element_ptr_kinds_eq_h2: "element_ptr_kinds h3 = element_ptr_kinds h2"
    by(simp add: element_ptr_kinds_def)

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
  then have element_ptr_kinds_eq_h3: "element_ptr_kinds h' = element_ptr_kinds h3"
    by(simp add: element_ptr_kinds_def)

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
  show "known_ptrs h'"
    using known_ptrs_preserved object_ptr_kinds_eq_h3 by blast


  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2
      CD.get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_element_ptr
              \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads h2 get_child_nodes_new_element[rotated, OF new_element_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h: "\<And>ptr'. ptr' \<noteq> cast new_element_ptr
                                    \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have "h2 \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []"
    using new_element_ptr h2 new_element_ptr_in_heap[OF h2 new_element_ptr]
      new_element_is_element_ptr[OF new_element_ptr] new_element_no_child_nodes
    by blast
  have tag_name_eq_h:
    "\<And>ptr' disc_nodes. ptr' \<noteq>  new_element_ptr
              \<Longrightarrow> h \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads h2 get_tag_name_new_element[rotated, OF new_element_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by(blast)+
  then have tag_name_eq2_h: "\<And>ptr'. ptr' \<noteq> new_element_ptr
                                    \<Longrightarrow> |h \<turnstile> get_tag_name ptr'|\<^sub>r = |h2 \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force
  have "h2 \<turnstile> get_tag_name new_element_ptr \<rightarrow>\<^sub>r ''''"
    using new_element_ptr h2 new_element_ptr_in_heap[OF h2 new_element_ptr]
      new_element_is_element_ptr[OF new_element_ptr] new_element_empty_tag_name
    by blast


  have disconnected_nodes_eq_h:
    "\<And>doc_ptr disc_nodes. h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                             = h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using CD.get_disconnected_nodes_reads h2 get_disconnected_nodes_new_element[OF new_element_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have disconnected_nodes_eq2_h:
    "\<And>doc_ptr. |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads set_tag_name_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_tag_name_get_child_nodes)
  then have children_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h2:
    "\<And>doc_ptr disc_nodes. h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                               = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using CD.get_disconnected_nodes_reads set_tag_name_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_tag_name_get_disconnected_nodes)
  then have disconnected_nodes_eq2_h2:
    "\<And>doc_ptr. |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have tag_name_eq_h2:
    "\<And>ptr' disc_nodes. ptr' \<noteq>  new_element_ptr
              \<Longrightarrow> h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    apply(rule reads_writes_preserved[OF get_tag_name_reads set_tag_name_writes h3])
    by (metis local.set_tag_name_get_tag_name_different_pointers)
  then have tag_name_eq2_h2: "\<And>ptr'. ptr' \<noteq> new_element_ptr
                                    \<Longrightarrow> |h2 \<turnstile> get_tag_name ptr'|\<^sub>r = |h3 \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force
  have "h2 \<turnstile> get_tag_name new_element_ptr \<rightarrow>\<^sub>r ''''"
    using new_element_ptr h2 new_element_ptr_in_heap[OF h2 new_element_ptr]
      new_element_is_element_ptr[OF new_element_ptr] new_element_empty_tag_name
    by blast

  have "type_wf h2"
    using \<open>type_wf h\<close> new_element_types_preserved h2 by blast
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_tag_name_writes h3]
    using  set_tag_name_types_preserved
    by(auto simp add: reflp_def transp_def)
  then show "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h']
    using  set_disconnected_nodes_types_preserved
    by(auto simp add: reflp_def transp_def)

  have children_eq_h3:
    "\<And>ptr' children. h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_child_nodes)
  then have children_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h3:
    "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr
       \<Longrightarrow> h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                               = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using CD.get_disconnected_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then have disconnected_nodes_eq2_h3:
    "\<And>doc_ptr. document_ptr \<noteq> doc_ptr
                \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have tag_name_eq_h2:
    "\<And>ptr' disc_nodes. ptr' \<noteq>  new_element_ptr
              \<Longrightarrow> h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    apply(rule reads_writes_preserved[OF get_tag_name_reads set_tag_name_writes h3])
    by (metis local.set_tag_name_get_tag_name_different_pointers)
  then have tag_name_eq2_h2: "\<And>ptr'. ptr' \<noteq> new_element_ptr
                                    \<Longrightarrow> |h2 \<turnstile> get_tag_name ptr'|\<^sub>r = |h3 \<turnstile> get_tag_name ptr'|\<^sub>r"
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

  have tag_name_eq_h3:
    "\<And>ptr' disc_nodes. h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h' \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    apply(rule reads_writes_preserved[OF get_tag_name_reads set_disconnected_nodes_writes h'])
    using set_disconnected_nodes_get_tag_name
    by blast
  then have tag_name_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_tag_name ptr'|\<^sub>r = |h' \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force


  have "acyclic (parent_child_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def)
  also have "parent_child_rel h = parent_child_rel h2"
  proof(auto simp add: CD.parent_child_rel_def)[1]
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
    by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq_h2 children_eq2_h2)
  also have "\<dots> = parent_child_rel h'"
    by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq_h3 children_eq2_h3)
  finally have "CD.a_acyclic_heap h'"
    by (simp add: CD.acyclic_heap_def)

  have "CD.a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_all_ptrs_in_heap h2"
    apply(auto simp add: CD.a_all_ptrs_in_heap_def)[1]
     apply (metis \<open>known_ptrs h2\<close> \<open>parent_child_rel h = parent_child_rel h2\<close> \<open>type_wf h2\<close> assms(1)
        assms(3) funion_iff CD.get_child_nodes_ok local.known_ptrs_known_ptr
        local.parent_child_rel_child_in_heap CD.parent_child_rel_child_nodes2 node_ptr_kinds_commutes
        node_ptr_kinds_eq_h returns_result_select_result)
    by (metis (no_types, lifting) CD.get_child_nodes_ok CD.get_child_nodes_ptr_in_heap
        \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close> assms(3) assms(4) children_eq_h
        disconnected_nodes_eq2_h document_ptr_kinds_eq_h finite_set_in is_OK_returns_result_I
        local.known_ptrs_known_ptr node_ptr_kinds_commutes returns_result_select_result subsetD)
  then have "CD.a_all_ptrs_in_heap h3"
    by (simp add: children_eq2_h2 disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2
        CD.a_all_ptrs_in_heap_def node_ptr_kinds_eq_h2 object_ptr_kinds_eq_h2)
  then have "CD.a_all_ptrs_in_heap h'"
    by (smt children_eq2_h3 disc_nodes_h3 disconnected_nodes_eq2_h3 document_ptr_kinds_eq_h3
        element_ptr_kinds_commutes h' h2 local.CD.a_all_ptrs_in_heap_def
        local.set_disconnected_nodes_get_disconnected_nodes new_element_ptr new_element_ptr_in_heap
        node_ptr_kinds_eq_h2 node_ptr_kinds_eq_h3 notin_fset object_ptr_kinds_eq_h3 select_result_I2
        set_ConsD subset_code(1))

  have "\<And>p. p |\<in>| object_ptr_kinds h \<Longrightarrow> cast new_element_ptr \<notin> set |h \<turnstile> get_child_nodes p|\<^sub>r"
    using \<open>heap_is_wellformed h\<close> \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>
      heap_is_wellformed_children_in_heap
    by (meson NodeMonad.ptr_kinds_ptr_kinds_M CD.a_all_ptrs_in_heap_def assms(3) assms(4) fset_mp
        fset_of_list_elem CD.get_child_nodes_ok known_ptrs_known_ptr returns_result_select_result)
  then have "\<And>p. p |\<in>| object_ptr_kinds h2 \<Longrightarrow> cast new_element_ptr \<notin> set |h2 \<turnstile> get_child_nodes p|\<^sub>r"
    using children_eq2_h
    apply(auto simp add: object_ptr_kinds_eq_h)[1]
    using \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr) \<rightarrow>\<^sub>r []\<close> apply auto[1]
    by (metis ObjectMonad.ptr_kinds_ptr_kinds_M
        \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>)
  then have "\<And>p. p |\<in>| object_ptr_kinds h3 \<Longrightarrow> cast new_element_ptr \<notin> set |h3 \<turnstile> get_child_nodes p|\<^sub>r"
    using object_ptr_kinds_eq_h2 children_eq2_h2 by auto
  then have new_element_ptr_not_in_any_children:
    "\<And>p. p |\<in>| object_ptr_kinds h' \<Longrightarrow> cast new_element_ptr \<notin> set |h' \<turnstile> get_child_nodes p|\<^sub>r"
    using object_ptr_kinds_eq_h3 children_eq2_h3 by auto

  have "CD.a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: CD.heap_is_wellformed_def heap_is_wellformed_def)
  then have "CD.a_distinct_lists h2"
    using \<open>h2 \<turnstile> get_child_nodes (cast new_element_ptr) \<rightarrow>\<^sub>r []\<close>
    apply(auto simp add: CD.a_distinct_lists_def object_ptr_kinds_eq_h document_ptr_kinds_eq_h
        disconnected_nodes_eq2_h intro!: distinct_concat_map_I)[1]
       apply (metis distinct_sorted_list_of_set finite_fset sorted_list_of_set_insert)
      apply(case_tac "x=cast new_element_ptr")
       apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
      apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
     apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
     apply (metis IntI assms(1) assms(3) assms(4) empty_iff  CD.get_child_nodes_ok
        local.heap_is_wellformed_one_parent local.known_ptrs_known_ptr returns_result_select_result)
    apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
    by (metis \<open> CD.a_distinct_lists h\<close> \<open>type_wf h2\<close> disconnected_nodes_eq_h document_ptr_kinds_eq_h
        CD.distinct_lists_no_parent  get_disconnected_nodes_ok returns_result_select_result)

  then have " CD.a_distinct_lists h3"
    by(auto simp add:  CD.a_distinct_lists_def disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2
        children_eq2_h2 object_ptr_kinds_eq_h2)
  then have " CD.a_distinct_lists h'"
  proof(auto simp add:  CD.a_distinct_lists_def disconnected_nodes_eq2_h3 children_eq2_h3
      object_ptr_kinds_eq_h3 document_ptr_kinds_eq_h3
      intro!: distinct_concat_map_I)[1]
    fix x
    assume "distinct (concat (map (\<lambda>document_ptr. |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                              (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and "x |\<in>| document_ptr_kinds h3"
    then show "distinct |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using document_ptr_kinds_eq_h3 disconnected_nodes_eq_h3 h' set_disconnected_nodes_get_disconnected_nodes
      by (metis (no_types, lifting) \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set disc_nodes_h3\<close>
          \<open> CD.a_distinct_lists h3\<close> \<open>type_wf h'\<close> disc_nodes_h3 distinct.simps(2)
          CD.distinct_lists_disconnected_nodes  get_disconnected_nodes_ok returns_result_eq
          returns_result_select_result)
  next
    fix x y xa
    assume "distinct (concat (map (\<lambda>document_ptr. |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                            (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and "x |\<in>| document_ptr_kinds h3"
      and "y |\<in>| document_ptr_kinds h3"
      and "x \<noteq> y"
      and "xa \<in> set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
      and "xa \<in> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r"
    moreover have "set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h3 \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
      using calculation by(auto dest: distinct_concat_map_E(1))
    ultimately show "False"
      apply(-)
      apply(cases "x = document_ptr")
       apply(smt NodeMonad.ptr_kinds_ptr_kinds_M \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> \<open>CD.a_all_ptrs_in_heap h\<close>
          disc_nodes_h3 disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
          disjoint_iff_not_equal document_ptr_kinds_eq_h document_ptr_kinds_eq_h2 finite_set_in h'
          set_disconnected_nodes_get_disconnected_nodes
          CD.a_all_ptrs_in_heap_def
          select_result_I2 set_ConsD subsetD)
      by (smt NodeMonad.ptr_kinds_ptr_kinds_M \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> \<open>CD.a_all_ptrs_in_heap h\<close>
          disc_nodes_document_ptr_h2 disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
          disjoint_iff_not_equal document_ptr_kinds_eq_h document_ptr_kinds_eq_h2 finite_set_in h'
          l_set_disconnected_nodes_get_disconnected_nodes.set_disconnected_nodes_get_disconnected_nodes
          CD.a_all_ptrs_in_heap_def local.l_set_disconnected_nodes_get_disconnected_nodes_axioms
          select_result_I2 set_ConsD subsetD)
  next
    fix x xa xb
    assume 2: "(\<Union>x\<in>fset (object_ptr_kinds h3). set |h' \<turnstile> get_child_nodes x|\<^sub>r)
                   \<inter> (\<Union>x\<in>fset (document_ptr_kinds h3). set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 3: "xa |\<in>| object_ptr_kinds h3"
      and 4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
      and 5: "xb |\<in>| document_ptr_kinds h3"
      and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
    show "False"
      using disc_nodes_document_ptr_h disconnected_nodes_eq2_h3
      apply -
      apply(cases "xb = document_ptr")
       apply (metis (no_types, hide_lams) "3" "4" "6"
          \<open>\<And>p. p |\<in>| object_ptr_kinds h3
                      \<Longrightarrow> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h3 \<turnstile> get_child_nodes p|\<^sub>r\<close>
          \<open> CD.a_distinct_lists h3\<close> children_eq2_h3 disc_nodes_h3 CD.distinct_lists_no_parent h'
          select_result_I2 set_ConsD  set_disconnected_nodes_get_disconnected_nodes)
      by (metis "3" "4" "5" "6" \<open> CD.a_distinct_lists h3\<close> \<open>type_wf h3\<close> children_eq2_h3
          CD.distinct_lists_no_parent  get_disconnected_nodes_ok returns_result_select_result)
  qed

  have "CD.a_owner_document_valid h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_owner_document_valid h'"
    using disc_nodes_h3 \<open>document_ptr |\<in>| document_ptr_kinds h\<close>
    apply(auto simp add: CD.a_owner_document_valid_def)[1]
    apply(auto simp add:  object_ptr_kinds_eq_h object_ptr_kinds_eq_h3 )[1]
    apply(auto simp add: object_ptr_kinds_eq_h2)[1]
    apply(auto simp add:  document_ptr_kinds_eq_h document_ptr_kinds_eq_h3 )[1]
    apply(auto simp add: document_ptr_kinds_eq_h2)[1]
    apply(auto simp add:  node_ptr_kinds_eq_h node_ptr_kinds_eq_h3 )[1]
    apply(auto simp add: node_ptr_kinds_eq_h2 node_ptr_kinds_eq_h )[1]
     apply(auto simp add: children_eq2_h2[symmetric] children_eq2_h3[symmetric]
        disconnected_nodes_eq2_h disconnected_nodes_eq2_h2
        disconnected_nodes_eq2_h3)[1]
     apply (metis (no_types, lifting) document_ptr_kinds_eq_h h' list.set_intros(1)
        local.set_disconnected_nodes_get_disconnected_nodes select_result_I2)
    apply(simp add: object_ptr_kinds_eq_h)
    by(metis (no_types, lifting) NodeMonad.ptr_kinds_ptr_kinds_M
        \<open>cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close> children_eq2_h children_eq2_h2
        children_eq2_h3 disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
        document_ptr_kinds_eq_h finite_set_in h'
        l_set_disconnected_nodes_get_disconnected_nodes.set_disconnected_nodes_get_disconnected_nodes
        list.set_intros(2) local.l_set_disconnected_nodes_get_disconnected_nodes_axioms node_ptr_kinds_commutes
        select_result_I2)

  have "CD.a_heap_is_wellformed h'"
    using \<open>CD.a_acyclic_heap h'\<close> \<open>CD.a_all_ptrs_in_heap h'\<close> \<open>CD.a_distinct_lists h'\<close> \<open>CD.a_owner_document_valid h'\<close>
    by(simp add: CD.a_heap_is_wellformed_def)





  have shadow_root_ptr_kinds_eq_h: "shadow_root_ptr_kinds h2 = shadow_root_ptr_kinds h"
    using document_ptr_kinds_eq_h
    by(auto simp add: shadow_root_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_h2: "shadow_root_ptr_kinds h3 = shadow_root_ptr_kinds h2"
    using document_ptr_kinds_eq_h2
    by(auto simp add: shadow_root_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_h3: "shadow_root_ptr_kinds h' = shadow_root_ptr_kinds h3"
    using document_ptr_kinds_eq_h3
    by(auto simp add: shadow_root_ptr_kinds_def)



  have shadow_root_eq_h: "\<And>element_ptr shadow_root_opt. element_ptr \<noteq> new_element_ptr
              \<Longrightarrow> h \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r shadow_root_opt = h2 \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r shadow_root_opt"
  proof -
    fix element_ptr shadow_root_opt
    assume "element_ptr \<noteq> new_element_ptr "
    have "\<forall>P \<in> get_shadow_root_locs element_ptr. P h h2"
      using get_shadow_root_new_element new_element_ptr h2
      using \<open>element_ptr \<noteq> new_element_ptr\<close> by blast
    then
    have "preserved (get_shadow_root element_ptr) h h2"
      using get_shadow_root_new_element[rotated, OF new_element_ptr h2]
      using get_shadow_root_reads
      by(simp add: reads_def)
    then show "h \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r shadow_root_opt = h2 \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r shadow_root_opt"
      by (simp add: preserved_def)
  qed
  have shadow_root_none: "h2 \<turnstile> get_shadow_root (new_element_ptr) \<rightarrow>\<^sub>r None"
    using new_element_ptr h2 new_element_ptr_in_heap[OF h2 new_element_ptr]
      new_element_is_element_ptr[OF new_element_ptr] new_element_no_shadow_root
    by blast

  have shadow_root_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children"
    using get_shadow_root_reads set_tag_name_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_tag_name_get_shadow_root)
  have shadow_root_eq_h3:
    "\<And>ptr' children. h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children"
    using get_shadow_root_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    using set_disconnected_nodes_get_shadow_root
    by(auto simp add: set_disconnected_nodes_get_shadow_root)


  have "a_all_ptrs_in_heap h"
    by (simp add: assms(1) local.a_all_ptrs_in_heap_def local.get_shadow_root_shadow_root_ptr_in_heap)
  then have "a_all_ptrs_in_heap h2"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h)[1]
    using returns_result_eq shadow_root_eq_h shadow_root_none by fastforce
  then have "a_all_ptrs_in_heap h3"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h2)[1]
    using shadow_root_eq_h2 by blast
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h3)[1]
    by (simp add: shadow_root_eq_h3)

  have "a_distinct_lists h"
    using assms(1)
    by (simp add: heap_is_wellformed_def)
  then have "a_distinct_lists h2"
    apply(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h)[1]
    apply(auto simp add: distinct_insort intro!: distinct_concat_map_I split: option.splits)[1]
    apply(case_tac "x = new_element_ptr")
    using shadow_root_none apply auto[1]
    using shadow_root_eq_h
    by (smt Diff_empty Diff_insert0 ElementMonad.ptr_kinds_M_ptr_kinds
        ElementMonad.ptr_kinds_ptr_kinds_M assms(1) assms(3) finite_set_in h2 insort_split
        local.get_shadow_root_ok local.shadow_root_same_host new_element_ptr new_element_ptr_not_in_heap
        option.distinct(1) returns_result_select_result select_result_I2 shadow_root_none)
  then have "a_distinct_lists h3"
    by(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h2 select_result_eq[OF shadow_root_eq_h2])
  then have "a_distinct_lists h'"
    by(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h3 select_result_eq[OF shadow_root_eq_h3])


  have "a_shadow_root_valid h"
    using assms(1)
    by (simp add: heap_is_wellformed_def)
  then have "a_shadow_root_valid h2"
  proof (unfold a_shadow_root_valid_def; safe)
    fix shadow_root_ptr
    assume "\<forall>shadow_root_ptr\<in>fset (shadow_root_ptr_kinds h). \<exists>host\<in>fset (element_ptr_kinds h).
|h \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types \<and> |h \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr"
    assume "shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h2)"

    obtain previous_host where
      "previous_host \<in> fset (element_ptr_kinds h)" and
      "|h \<turnstile> get_tag_name previous_host|\<^sub>r \<in> safe_shadow_root_element_types" and
      "|h \<turnstile> get_shadow_root previous_host|\<^sub>r = Some shadow_root_ptr"
      by (metis \<open>local.a_shadow_root_valid h\<close> \<open>shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h2)\<close>
          local.a_shadow_root_valid_def shadow_root_ptr_kinds_eq_h)
    moreover have "previous_host \<noteq> new_element_ptr"
      using calculation(1) h2 new_element_ptr new_element_ptr_not_in_heap by auto
    ultimately have "|h2 \<turnstile> get_tag_name previous_host|\<^sub>r \<in> safe_shadow_root_element_types" and
      "|h2 \<turnstile> get_shadow_root previous_host|\<^sub>r = Some shadow_root_ptr"
      using shadow_root_eq_h
       apply (simp add: tag_name_eq2_h)
      by (metis \<open>previous_host \<noteq> new_element_ptr\<close> \<open>|h \<turnstile> get_shadow_root previous_host|\<^sub>r = Some shadow_root_ptr\<close>
          select_result_eq shadow_root_eq_h)
    then
    show "\<exists>host\<in>fset (element_ptr_kinds h2). |h2 \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types \<and>
|h2 \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr"
      by (meson \<open>previous_host \<in> fset (element_ptr_kinds h)\<close> \<open>previous_host \<noteq> new_element_ptr\<close> assms(3)
          local.get_shadow_root_ok local.get_shadow_root_ptr_in_heap notin_fset returns_result_select_result shadow_root_eq_h)
  qed
  then have "a_shadow_root_valid h3"
  proof (unfold a_shadow_root_valid_def; safe)
    fix shadow_root_ptr
    assume "\<forall>shadow_root_ptr\<in>fset (shadow_root_ptr_kinds h2). \<exists>host\<in>fset (element_ptr_kinds h2).
|h2 \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types \<and> |h2 \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr"
    assume "shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h3)"

    obtain previous_host where
      "previous_host \<in> fset (element_ptr_kinds h2)" and
      "|h2 \<turnstile> get_tag_name previous_host|\<^sub>r \<in> safe_shadow_root_element_types" and
      "|h2 \<turnstile> get_shadow_root previous_host|\<^sub>r = Some shadow_root_ptr"
      by (metis \<open>local.a_shadow_root_valid h2\<close> \<open>shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h3)\<close>
          local.a_shadow_root_valid_def shadow_root_ptr_kinds_eq_h2)
    moreover have "previous_host \<noteq> new_element_ptr"
      using calculation(1) h3 new_element_ptr new_element_ptr_not_in_heap
      using calculation(3) shadow_root_none by auto
    ultimately have "|h2 \<turnstile> get_tag_name previous_host|\<^sub>r \<in> safe_shadow_root_element_types" and
      "|h2 \<turnstile> get_shadow_root previous_host|\<^sub>r = Some shadow_root_ptr"
      using shadow_root_eq_h2
       apply (simp add: tag_name_eq2_h2)
      by (metis \<open>previous_host \<noteq> new_element_ptr\<close> \<open>|h2 \<turnstile> get_shadow_root previous_host|\<^sub>r = Some shadow_root_ptr\<close>
          select_result_eq shadow_root_eq_h)
    then
    show "\<exists>host\<in>fset (element_ptr_kinds h3). |h3 \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types \<and>
|h3 \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr"
      by (smt \<open>previous_host \<in> fset (element_ptr_kinds h2)\<close> \<open>previous_host \<noteq> new_element_ptr\<close> \<open>type_wf h2\<close>
          \<open>type_wf h3\<close> element_ptr_kinds_eq_h2 finite_set_in local.get_shadow_root_ok returns_result_eq
          returns_result_select_result shadow_root_eq_h2 tag_name_eq2_h2)
  qed
  then have "a_shadow_root_valid h'"
    apply(auto simp add: a_shadow_root_valid_def element_ptr_kinds_eq_h3 shadow_root_eq_h3
        shadow_root_ptr_kinds_eq_h3 tag_name_eq2_h3)[1]
    by (smt \<open>type_wf h3\<close> finite_set_in local.get_shadow_root_ok returns_result_select_result
        select_result_I2 shadow_root_eq_h3)



  have "a_host_shadow_root_rel h = a_host_shadow_root_rel h2"
    apply(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h shadow_root_eq_h)[1]
      apply (smt assms(3) case_prod_conv h2 image_iff local.get_shadow_root_ok mem_Collect_eq new_element_ptr
        new_element_ptr_not_in_heap returns_result_select_result select_result_I2 shadow_root_eq_h)
    using shadow_root_none apply auto[1]
    apply (metis (no_types, lifting) Collect_cong assms(3) case_prodE case_prodI h2 host_shadow_root_rel_def
        i_get_parent_get_host_get_disconnected_document_wf.a_host_shadow_root_rel_shadow_root
        local.a_host_shadow_root_rel_def local.get_shadow_root_impl local.get_shadow_root_ok new_element_ptr
        new_element_ptr_not_in_heap returns_result_select_result select_result_I2 shadow_root_eq_h)
    done
  have "a_host_shadow_root_rel h2 = a_host_shadow_root_rel h3"
    apply(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h2 shadow_root_eq_h2)[1]
     apply (smt Collect_cong \<open>type_wf h2\<close> case_prodE case_prodI element_ptr_kinds_eq_h2 host_shadow_root_rel_def
        i_get_root_node_si_wf.a_host_shadow_root_rel_shadow_root local.a_host_shadow_root_rel_def local.get_shadow_root_impl
        local.get_shadow_root_ok returns_result_select_result shadow_root_eq_h2)
    by (metis (no_types, lifting) Collect_cong \<open>type_wf h3\<close> case_prodI2 case_prod_conv element_ptr_kinds_eq_h2
        host_shadow_root_rel_def i_get_root_node_si_wf.a_host_shadow_root_rel_shadow_root local.a_host_shadow_root_rel_def
        local.get_shadow_root_impl local.get_shadow_root_ok returns_result_select_result shadow_root_eq_h2)
  have "a_host_shadow_root_rel h3 = a_host_shadow_root_rel h'"
    apply(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h2 shadow_root_eq_h2)[1]
     apply (smt Collect_cong Shadow_DOM.a_host_shadow_root_rel_def \<open>type_wf h3\<close> case_prodD case_prodI2
        element_ptr_kinds_eq_h2 i_get_root_node_si_wf.a_host_shadow_root_rel_shadow_root local.get_shadow_root_impl
        local.get_shadow_root_ok returns_result_select_result shadow_root_eq_h3)
    apply (smt Collect_cong \<open>type_wf h'\<close> case_prodE case_prodI element_ptr_kinds_eq_h2 host_shadow_root_rel_def
        i_get_root_node_si_wf.a_host_shadow_root_rel_shadow_root l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_defs.a_host_shadow_root_rel_def
        local.get_shadow_root_impl local.get_shadow_root_ok returns_result_select_result shadow_root_eq_h3)
    done


  have "a_ptr_disconnected_node_rel h = a_ptr_disconnected_node_rel h2"
    by(simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h disconnected_nodes_eq2_h)
  have "a_ptr_disconnected_node_rel h2 = a_ptr_disconnected_node_rel h3"
    by(simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h2 disconnected_nodes_eq2_h2)

  have "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_element_ptr # disc_nodes_h3"
    using h' local.set_disconnected_nodes_get_disconnected_nodes by auto
  have " document_ptr |\<in>| document_ptr_kinds h3"
    by (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close> document_ptr_kinds_eq_h document_ptr_kinds_eq_h2)
  have "cast new_element_ptr \<in> set |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    using \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr # disc_nodes_h3\<close>
    by auto

  have "a_ptr_disconnected_node_rel h' = {(cast document_ptr, cast new_element_ptr)} \<union> a_ptr_disconnected_node_rel h3"
    apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h3 disconnected_nodes_eq2_h3)[1]
      apply(case_tac "aa = document_ptr")
    using disc_nodes_h3 h' \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_element_ptr # disc_nodes_h3\<close>
       apply(auto)[1]
    using disconnected_nodes_eq2_h3 apply auto[1]
    using \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_element_ptr # disc_nodes_h3\<close>
    using \<open>cast new_element_ptr \<in> set |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r\<close>
    using \<open>document_ptr |\<in>| document_ptr_kinds h3\<close> apply auto[1]
    apply(case_tac "document_ptr = aa")
    using \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr # disc_nodes_h3\<close> disc_nodes_h3
     apply auto[1]
    using disconnected_nodes_eq_h3[THEN select_result_eq, simplified] by auto

  have "acyclic (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def)
  have "parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h =
parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2"
    using \<open>local.a_host_shadow_root_rel h = local.a_host_shadow_root_rel h2\<close>
      \<open>local.a_ptr_disconnected_node_rel h = local.a_ptr_disconnected_node_rel h2\<close> \<open>parent_child_rel h = parent_child_rel h2\<close>
    by auto
  have "parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2 =
parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3"
    using \<open>local.a_host_shadow_root_rel h2 = local.a_host_shadow_root_rel h3\<close>
      \<open>local.a_ptr_disconnected_node_rel h2 = local.a_ptr_disconnected_node_rel h3\<close> \<open>parent_child_rel h2 = parent_child_rel h3\<close>
    by auto
  have "parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h' =
{(cast document_ptr, cast new_element_ptr)} \<union> parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3"
    by (simp add: \<open>local.a_host_shadow_root_rel h3 = local.a_host_shadow_root_rel h'\<close>
        \<open>local.a_ptr_disconnected_node_rel h' = {(cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr, cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr)} \<union>
local.a_ptr_disconnected_node_rel h3\<close> \<open>parent_child_rel h3 = parent_child_rel h'\<close>)

  have "\<And>a b. (a, b) \<in> parent_child_rel h3 \<Longrightarrow> a \<noteq> cast new_element_ptr"
    using CD.parent_child_rel_parent_in_heap \<open>parent_child_rel h = parent_child_rel h2\<close>
      \<open>parent_child_rel h2 = parent_child_rel h3\<close> element_ptr_kinds_commutes h2 new_element_ptr
      new_element_ptr_not_in_heap node_ptr_kinds_commutes
    by blast
  moreover
  have "\<And>a b. (a, b) \<in> a_host_shadow_root_rel h3 \<Longrightarrow> a \<noteq> cast new_element_ptr"
    using shadow_root_eq_h2 shadow_root_none
    by(auto simp add: a_host_shadow_root_rel_def)
  moreover
  have "\<And>a b. (a, b) \<in> a_ptr_disconnected_node_rel h3 \<Longrightarrow> a \<noteq> cast new_element_ptr"
    by(auto simp add: a_ptr_disconnected_node_rel_def)
  moreover
  have "cast new_element_ptr \<notin> {x. (x, cast document_ptr) \<in>
(parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)\<^sup>*}"
    by (smt Un_iff \<open>\<And>b a. (a, b) \<in> local.a_host_shadow_root_rel h3 \<Longrightarrow>
a \<noteq> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr\<close> \<open>\<And>b a. (a, b) \<in> local.a_ptr_disconnected_node_rel h3 \<Longrightarrow>
a \<noteq> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr\<close> \<open>\<And>b a. (a, b) \<in> parent_child_rel h3 \<Longrightarrow>
a \<noteq> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_element_ptr\<close> cast_document_ptr_not_node_ptr(1) converse_rtranclE mem_Collect_eq)
  moreover
  have "acyclic (parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)"
    using \<open>acyclic (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> local.a_ptr_disconnected_node_rel h)\<close>
      \<open>parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> local.a_ptr_disconnected_node_rel h =
parent_child_rel h2 \<union> local.a_host_shadow_root_rel h2 \<union> local.a_ptr_disconnected_node_rel h2\<close>
      \<open>parent_child_rel h2 \<union> local.a_host_shadow_root_rel h2 \<union> local.a_ptr_disconnected_node_rel h2 =
parent_child_rel h3 \<union> local.a_host_shadow_root_rel h3 \<union> local.a_ptr_disconnected_node_rel h3\<close>
    by auto
  ultimately have "acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')"
    by(simp add: \<open>parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h' =
{(cast document_ptr, cast new_element_ptr)} \<union> parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3\<close>)


  show " heap_is_wellformed h' "
    using \<open>acyclic (parent_child_rel h' \<union> local.a_host_shadow_root_rel h' \<union> local.a_ptr_disconnected_node_rel h')\<close>
    by(simp add: heap_is_wellformed_def CD.heap_is_wellformed_impl \<open>local.CD.a_heap_is_wellformed h'\<close>
        \<open>local.a_all_ptrs_in_heap h'\<close> \<open>local.a_distinct_lists h'\<close> \<open>local.a_shadow_root_valid h'\<close>)
qed
end

interpretation i_create_element_wf?: l_create_element_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr known_ptrs type_wf
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs heap_is_wellformed
  parent_child_rel set_tag_name set_tag_name_locs set_disconnected_nodes
  set_disconnected_nodes_locs create_element get_shadow_root get_shadow_root_locs get_tag_name
  get_tag_name_locs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs DocumentClass.known_ptr DocumentClass.type_wf
  by(auto simp add: l_create_element_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_create_element_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]


subsubsection \<open>create\_character\_data\<close>

locale l_create_character_data_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes type_wf get_disconnected_nodes get_disconnected_nodes_locs +
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs known_ptr type_wf
  heap_is_wellformed parent_child_rel
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs +
  l_create_character_data\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs
  set_disconnected_nodes set_disconnected_nodes_locs set_val set_val_locs create_character_data known_ptr
  type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  + l_new_character_data_get_disconnected_nodes
  get_disconnected_nodes get_disconnected_nodes_locs

+ l_set_val_get_disconnected_nodes
type_wf set_val set_val_locs get_disconnected_nodes get_disconnected_nodes_locs
+ l_new_character_data_get_child_nodes
type_wf known_ptr get_child_nodes get_child_nodes_locs
+ l_set_val_get_child_nodes
type_wf set_val set_val_locs known_ptr get_child_nodes get_child_nodes_locs
+ l_set_disconnected_nodes_get_child_nodes
set_disconnected_nodes set_disconnected_nodes_locs get_child_nodes get_child_nodes_locs
+ l_set_disconnected_nodes
type_wf set_disconnected_nodes set_disconnected_nodes_locs
+ l_set_disconnected_nodes_get_disconnected_nodes
type_wf get_disconnected_nodes get_disconnected_nodes_locs set_disconnected_nodes
set_disconnected_nodes_locs
+ l_set_val_get_shadow_root type_wf set_val set_val_locs get_shadow_root get_shadow_root_locs
+ l_set_disconnected_nodes_get_shadow_root set_disconnected_nodes set_disconnected_nodes_locs
get_shadow_root get_shadow_root_locs
+ l_new_character_data_get_tag_name
get_tag_name get_tag_name_locs
+ l_set_val_get_tag_name type_wf set_val set_val_locs get_tag_name get_tag_name_locs
+ l_get_tag_name type_wf get_tag_name get_tag_name_locs
+ l_set_disconnected_nodes_get_tag_name type_wf set_disconnected_nodes set_disconnected_nodes_locs
get_tag_name get_tag_name_locs
+ l_new_character_data
type_wf
+ l_known_ptrs
known_ptr known_ptrs
for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and set_tag_name :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and create_element :: "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
  and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
  and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
  and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
  and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
  and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_document :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
  and get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_val_locs :: "(_) character_data_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and create_character_data ::
  "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) character_data_ptr) prog"
  and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
begin
lemma create_character_data_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>h h'"
    and "type_wf h"
    and "known_ptrs h"
  shows "heap_is_wellformed h'" and "type_wf h'" and "known_ptrs h'"
proof -
  obtain new_character_data_ptr h2 h3 disc_nodes_h3 where
    new_character_data_ptr: "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr" and
    h2: "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h2" and
    h3: "h2 \<turnstile> set_val new_character_data_ptr text \<rightarrow>\<^sub>h h3" and
    disc_nodes_h3: "h3 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3" and
    h': "h3 \<turnstile> set_disconnected_nodes document_ptr (cast new_character_data_ptr # disc_nodes_h3) \<rightarrow>\<^sub>h h'"
    using assms(2)
    by(auto simp add: CD.create_character_data_def
        elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF CD.get_disconnected_nodes_pure, rotated] )
  then have "h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr"
    apply(auto simp add: CD.create_character_data_def intro!: bind_returns_result_I)[1]
      apply (metis is_OK_returns_heap_I is_OK_returns_result_E old.unit.exhaust)
     apply (metis is_OK_returns_heap_E is_OK_returns_result_I local.CD.get_disconnected_nodes_pure
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
          OF CD.set_val_writes h3])
    using CD.set_val_pointers_preserved
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

  have "known_ptr (cast new_character_data_ptr)"
    using \<open>h \<turnstile> create_character_data document_ptr text \<rightarrow>\<^sub>r new_character_data_ptr\<close>
      local.create_character_data_known_ptr by blast
  then
  have "known_ptrs h2"
    using known_ptrs_new_ptr object_ptr_kinds_eq_h \<open>known_ptrs h\<close> h2
    by blast
  then
  have "known_ptrs h3"
    using known_ptrs_preserved object_ptr_kinds_eq_h2 by blast
  then
  show "known_ptrs h'"
    using known_ptrs_preserved object_ptr_kinds_eq_h3 by blast

  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2
      CD.get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_character_data_ptr
                  \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads h2 get_child_nodes_new_character_data[rotated, OF new_character_data_ptr h2]
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
          OF CD.set_val_writes h3])
    using CD.set_val_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2
    by(auto simp add: node_ptr_kinds_def)
  then have character_data_ptr_kinds_eq_h2: "character_data_ptr_kinds h3 = character_data_ptr_kinds h2"
    by(simp add: character_data_ptr_kinds_def)
  have element_ptr_kinds_eq_h2: "element_ptr_kinds h3 = element_ptr_kinds h2"
    using node_ptr_kinds_eq_h2
    by(simp add: element_ptr_kinds_def)

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
  then have character_data_ptr_kinds_eq_h3: "character_data_ptr_kinds h' = character_data_ptr_kinds h3"
    by(simp add: character_data_ptr_kinds_def)
  have element_ptr_kinds_eq_h3: "element_ptr_kinds h' = element_ptr_kinds h3"
    using node_ptr_kinds_eq_h3
    by(simp add: element_ptr_kinds_def)


  have "document_ptr |\<in>| document_ptr_kinds h"
    using disc_nodes_h3 document_ptr_kinds_eq_h object_ptr_kinds_eq_h2
      CD.get_disconnected_nodes_ptr_in_heap \<open>type_wf h\<close> document_ptr_kinds_def
    by (metis is_OK_returns_result_I)

  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_character_data_ptr
                \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads h2 get_child_nodes_new_character_data[rotated, OF new_character_data_ptr h2]
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
    using CD.get_disconnected_nodes_reads h2
      get_disconnected_nodes_new_character_data[OF new_character_data_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have disconnected_nodes_eq2_h:
    "\<And>doc_ptr. |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have tag_name_eq_h:
    "\<And>ptr' disc_nodes. h \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads h2
      get_tag_name_new_character_data[OF new_character_data_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have tag_name_eq2_h: "\<And>ptr'. |h \<turnstile> get_tag_name ptr'|\<^sub>r = |h2 \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads CD.set_val_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_val_get_child_nodes)
  then have children_eq2_h2:
    "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h2:
    "\<And>doc_ptr disc_nodes. h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                              = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using CD.get_disconnected_nodes_reads CD.set_val_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_val_get_disconnected_nodes)
  then have disconnected_nodes_eq2_h2:
    "\<And>doc_ptr. |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have tag_name_eq_h2:
    "\<And>ptr' disc_nodes. h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads CD.set_val_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_val_get_tag_name)
  then have tag_name_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_tag_name ptr'|\<^sub>r = |h3 \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force

  have "type_wf h2"
    using \<open>type_wf h\<close> new_character_data_types_preserved h2 by blast
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF CD.set_val_writes h3]
    using  set_val_types_preserved
    by(auto simp add: reflp_def transp_def)
  then show "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_disconnected_nodes_writes h']
    using  set_disconnected_nodes_types_preserved
    by(auto simp add: reflp_def transp_def)

  have children_eq_h3:
    "\<And>ptr' children. h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_child_nodes)
  then have children_eq2_h3:
    " \<And>ptr'. |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h3: "\<And>doc_ptr disc_nodes. document_ptr \<noteq> doc_ptr
    \<Longrightarrow> h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                            = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using CD.get_disconnected_nodes_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_disconnected_nodes_different_pointers)
  then have disconnected_nodes_eq2_h3: "\<And>doc_ptr. document_ptr \<noteq> doc_ptr
             \<Longrightarrow> |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have tag_name_eq_h3:
    "\<And>ptr' disc_nodes. h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h' \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_disconnected_nodes_get_tag_name)
  then have tag_name_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_tag_name ptr'|\<^sub>r = |h' \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force

  have disc_nodes_document_ptr_h2: "h2 \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h2 disc_nodes_h3 by auto
  then have disc_nodes_document_ptr_h: "h \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r disc_nodes_h3"
    using disconnected_nodes_eq_h by auto
  then have "cast new_character_data_ptr \<notin> set disc_nodes_h3"
    using \<open>heap_is_wellformed h\<close> using \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>
      a_all_ptrs_in_heap_def heap_is_wellformed_def
    using NodeMonad.ptr_kinds_ptr_kinds_M local.heap_is_wellformed_disc_nodes_in_heap by blast

  have "acyclic (parent_child_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def)
  also have "parent_child_rel h = parent_child_rel h2"
  proof(auto simp add: CD.parent_child_rel_def)[1]
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
    by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq_h2 children_eq2_h2)
  also have "\<dots> = parent_child_rel h'"
    by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq_h3 children_eq2_h3)
  finally have "CD.a_acyclic_heap h'"
    by (simp add: CD.acyclic_heap_def)

  have "CD.a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_all_ptrs_in_heap h2"
    apply(auto simp add: CD.a_all_ptrs_in_heap_def)[1]
    using node_ptr_kinds_eq_h \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>
      \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
     apply (metis (no_types, lifting) NodeMonad.ptr_kinds_ptr_kinds_M \<open>parent_child_rel h = parent_child_rel h2\<close>
        children_eq2_h finite_set_in finsert_iff funion_finsert_right CD.parent_child_rel_child
        CD.parent_child_rel_parent_in_heap node_ptr_kinds_commutes object_ptr_kinds_eq_h
        select_result_I2 subsetD sup_bot.right_neutral)
    by (metis (no_types, lifting) CD.get_child_nodes_ok CD.get_child_nodes_ptr_in_heap
        \<open>h2 \<turnstile> get_child_nodes (cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr) \<rightarrow>\<^sub>r []\<close> assms(3) assms(4)
        children_eq_h disconnected_nodes_eq2_h document_ptr_kinds_eq_h finite_set_in is_OK_returns_result_I
        local.known_ptrs_known_ptr node_ptr_kinds_commutes returns_result_select_result subset_code(1))
  then have "CD.a_all_ptrs_in_heap h3"
    by (simp add: children_eq2_h2 disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2
        CD.a_all_ptrs_in_heap_def node_ptr_kinds_eq_h2 object_ptr_kinds_eq_h2)
  then have "CD.a_all_ptrs_in_heap h'"
    by (smt character_data_ptr_kinds_commutes character_data_ptr_kinds_eq_h2 children_eq2_h3
        disc_nodes_h3 disconnected_nodes_eq2_h3 document_ptr_kinds_eq_h3 h' h2 local.CD.a_all_ptrs_in_heap_def
        local.set_disconnected_nodes_get_disconnected_nodes new_character_data_ptr new_character_data_ptr_in_heap
        node_ptr_kinds_eq_h3 notin_fset object_ptr_kinds_eq_h3 select_result_I2 set_ConsD subset_code(1))

  have "\<And>p. p |\<in>| object_ptr_kinds h \<Longrightarrow> cast new_character_data_ptr \<notin> set |h \<turnstile> get_child_nodes p|\<^sub>r"
    using \<open>heap_is_wellformed h\<close> \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>
      heap_is_wellformed_children_in_heap
    by (meson NodeMonad.ptr_kinds_ptr_kinds_M CD.a_all_ptrs_in_heap_def assms(3) assms(4) fset_mp
        fset_of_list_elem CD.get_child_nodes_ok known_ptrs_known_ptr returns_result_select_result)
  then have "\<And>p. p |\<in>| object_ptr_kinds h2 \<Longrightarrow> cast new_character_data_ptr \<notin> set |h2 \<turnstile> get_child_nodes p|\<^sub>r"
    using children_eq2_h
    apply(auto simp add: object_ptr_kinds_eq_h)[1]
    using \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close> apply auto[1]
    by (metis ObjectMonad.ptr_kinds_ptr_kinds_M \<open>cast new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>)
  then have "\<And>p. p |\<in>| object_ptr_kinds h3 \<Longrightarrow> cast new_character_data_ptr \<notin> set |h3 \<turnstile> get_child_nodes p|\<^sub>r"
    using object_ptr_kinds_eq_h2 children_eq2_h2 by auto
  then have new_character_data_ptr_not_in_any_children:
    "\<And>p. p |\<in>| object_ptr_kinds h' \<Longrightarrow> cast new_character_data_ptr \<notin> set |h' \<turnstile> get_child_nodes p|\<^sub>r"
    using object_ptr_kinds_eq_h3 children_eq2_h3 by auto

  have "CD.a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_distinct_lists h2"
    using \<open>h2 \<turnstile> get_child_nodes (cast new_character_data_ptr) \<rightarrow>\<^sub>r []\<close>
    apply(auto simp add: CD.a_distinct_lists_def object_ptr_kinds_eq_h document_ptr_kinds_eq_h
        disconnected_nodes_eq2_h intro!: distinct_concat_map_I)[1]
       apply (metis distinct_sorted_list_of_set finite_fset sorted_list_of_set_insert)
      apply(case_tac "x=cast new_character_data_ptr")
       apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
      apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
     apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
     apply (metis IntI assms(1) assms(3) assms(4) empty_iff CD.get_child_nodes_ok
        local.heap_is_wellformed_one_parent local.known_ptrs_known_ptr
        returns_result_select_result)
    apply(auto simp add: children_eq2_h[symmetric] insort_split dest: distinct_concat_map_E(2))[1]
    thm children_eq2_h

    using \<open>CD.a_distinct_lists h\<close> \<open>type_wf h2\<close> disconnected_nodes_eq_h document_ptr_kinds_eq_h
      CD.distinct_lists_no_parent get_disconnected_nodes_ok returns_result_select_result
    by metis
  then have "CD.a_distinct_lists h3"
    by(auto simp add: CD.a_distinct_lists_def disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2
        children_eq2_h2 object_ptr_kinds_eq_h2)[1]
  then have "CD.a_distinct_lists h'"
  proof(auto simp add: CD.a_distinct_lists_def disconnected_nodes_eq2_h3 children_eq2_h3
      object_ptr_kinds_eq_h3 document_ptr_kinds_eq_h3 intro!: distinct_concat_map_I)[1]
    fix x
    assume "distinct (concat (map (\<lambda>document_ptr. |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                      (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and "x |\<in>| document_ptr_kinds h3"
    then show "distinct |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using document_ptr_kinds_eq_h3 disconnected_nodes_eq_h3 h' set_disconnected_nodes_get_disconnected_nodes
      by (metis (no_types, hide_lams) \<open>cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr \<notin> set disc_nodes_h3\<close>
          \<open>type_wf h2\<close> assms(1) disc_nodes_document_ptr_h disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
          disconnected_nodes_eq_h distinct.simps(2) document_ptr_kinds_eq_h2 local.get_disconnected_nodes_ok
          local.heap_is_wellformed_disconnected_nodes_distinct returns_result_select_result select_result_I2)
  next
    fix x y xa
    assume "distinct (concat (map (\<lambda>document_ptr. |h3 \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                            (sorted_list_of_set (fset (document_ptr_kinds h3)))))"
      and "x |\<in>| document_ptr_kinds h3"
      and "y |\<in>| document_ptr_kinds h3"
      and "x \<noteq> y"
      and "xa \<in> set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
      and "xa \<in> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r"
    moreover have "set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r \<inter> set |h3 \<turnstile> get_disconnected_nodes y|\<^sub>r = {}"
      using calculation by(auto dest: distinct_concat_map_E(1))
    ultimately show "False"
      using  NodeMonad.ptr_kinds_ptr_kinds_M \<open>cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr \<notin> set |h \<turnstile> node_ptr_kinds_M|\<^sub>r\<close>

      by (smt local.CD.a_all_ptrs_in_heap_def \<open>CD.a_all_ptrs_in_heap h\<close> disc_nodes_document_ptr_h2
          disconnected_nodes_eq2_h
          disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3 disjoint_iff_not_equal
          document_ptr_kinds_eq_h document_ptr_kinds_eq_h2 finite_set_in h'
          l_set_disconnected_nodes_get_disconnected_nodes.set_disconnected_nodes_get_disconnected_nodes
          local.a_all_ptrs_in_heap_def local.l_set_disconnected_nodes_get_disconnected_nodes_axioms
          select_result_I2 set_ConsD subsetD)
  next
    fix x xa xb
    assume 2: "(\<Union>x\<in>fset (object_ptr_kinds h3). set |h' \<turnstile> get_child_nodes x|\<^sub>r)
                  \<inter> (\<Union>x\<in>fset (document_ptr_kinds h3). set |h3 \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 3: "xa |\<in>| object_ptr_kinds h3"
      and 4: "x \<in> set |h' \<turnstile> get_child_nodes xa|\<^sub>r"
      and 5: "xb |\<in>| document_ptr_kinds h3"
      and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
    show "False"
      using disc_nodes_document_ptr_h disconnected_nodes_eq2_h3
      apply(cases "document_ptr = xb")
       apply (metis (no_types, lifting) "3" "4" "5" "6" CD.distinct_lists_no_parent
          \<open>local.CD.a_distinct_lists h2\<close> \<open>type_wf h'\<close> children_eq2_h2 children_eq2_h3 disc_nodes_document_ptr_h2
          document_ptr_kinds_eq_h3 h' local.get_disconnected_nodes_ok local.set_disconnected_nodes_get_disconnected_nodes
          new_character_data_ptr_not_in_any_children object_ptr_kinds_eq_h2 object_ptr_kinds_eq_h3 returns_result_eq
          returns_result_select_result set_ConsD)
      by (metis "3" "4" "5" "6" CD.distinct_lists_no_parent \<open>local.CD.a_distinct_lists h3\<close> \<open>type_wf h3\<close>
          children_eq2_h3 local.get_disconnected_nodes_ok returns_result_select_result)
  qed

  have "CD.a_owner_document_valid h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_owner_document_valid h'"
    using disc_nodes_h3 \<open>document_ptr |\<in>| document_ptr_kinds h\<close>
    apply(simp add: CD.a_owner_document_valid_def)
    apply(simp add: object_ptr_kinds_eq_h object_ptr_kinds_eq_h3 )
    apply(simp add: object_ptr_kinds_eq_h2)
    apply(simp add: document_ptr_kinds_eq_h document_ptr_kinds_eq_h3 )
    apply(simp add: document_ptr_kinds_eq_h2)
    apply(simp add: node_ptr_kinds_eq_h node_ptr_kinds_eq_h3 )
    apply(simp add: node_ptr_kinds_eq_h2 node_ptr_kinds_eq_h )
    apply(auto simp add: children_eq2_h2[symmetric] children_eq2_h3[symmetric] disconnected_nodes_eq2_h
        disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3)[1]
     apply (metis (no_types, lifting) document_ptr_kinds_eq_h h' list.set_intros(1)
        local.set_disconnected_nodes_get_disconnected_nodes select_result_I2)
    apply(simp add: object_ptr_kinds_eq_h)
    by (metis (mono_tags, lifting) \<open>cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_character_data_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>
        children_eq2_h disconnected_nodes_eq2_h3 document_ptr_kinds_eq_h finite_set_in h'
        l_ptr_kinds_M.ptr_kinds_ptr_kinds_M
        l_set_disconnected_nodes_get_disconnected_nodes.set_disconnected_nodes_get_disconnected_nodes
        list.set_intros(2) local.l_set_disconnected_nodes_get_disconnected_nodes_axioms
        object_ptr_kinds_M_def
        select_result_I2)






  have shadow_root_ptr_kinds_eq_h: "shadow_root_ptr_kinds h2 = shadow_root_ptr_kinds h"
    using document_ptr_kinds_eq_h
    by(auto simp add: shadow_root_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_h2: "shadow_root_ptr_kinds h3 = shadow_root_ptr_kinds h2"
    using document_ptr_kinds_eq_h2
    by(auto simp add: shadow_root_ptr_kinds_def)
  have shadow_root_ptr_kinds_eq_h3: "shadow_root_ptr_kinds h' = shadow_root_ptr_kinds h3"
    using document_ptr_kinds_eq_h3
    by(auto simp add: shadow_root_ptr_kinds_def)



  have shadow_root_eq_h: "\<And>character_data_ptr shadow_root_opt.
h \<turnstile> get_shadow_root character_data_ptr \<rightarrow>\<^sub>r shadow_root_opt =
h2 \<turnstile> get_shadow_root character_data_ptr \<rightarrow>\<^sub>r shadow_root_opt"
    using get_shadow_root_reads h2 get_shadow_root_new_character_data[rotated, OF h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    using local.get_shadow_root_locs_impl new_character_data_ptr apply blast
    using local.get_shadow_root_locs_impl new_character_data_ptr by blast


  have shadow_root_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children"
    using get_shadow_root_reads set_val_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_val_get_shadow_root)
  have shadow_root_eq_h3:
    "\<And>ptr' children. h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children"
    using get_shadow_root_reads set_disconnected_nodes_writes h'
    apply(rule reads_writes_preserved)
    using set_disconnected_nodes_get_shadow_root
    by(auto simp add: set_disconnected_nodes_get_shadow_root)


  have "a_all_ptrs_in_heap h"
    by (simp add: assms(1) local.a_all_ptrs_in_heap_def local.get_shadow_root_shadow_root_ptr_in_heap)
  then have "a_all_ptrs_in_heap h2"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h)[1]
    using returns_result_eq shadow_root_eq_h by fastforce
  then have "a_all_ptrs_in_heap h3"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h2)[1]
    using shadow_root_eq_h2 by blast
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h3)[1]
    by (simp add: shadow_root_eq_h3)

  have "a_distinct_lists h"
    using assms(1)
    by (simp add: heap_is_wellformed_def)
  then have "a_distinct_lists h2"
    apply(auto simp add: a_distinct_lists_def character_data_ptr_kinds_eq_h)[1]
    apply(auto simp add: distinct_insort intro!: distinct_concat_map_I split: option.splits)[1]
    by (metis \<open>type_wf h2\<close> assms(1) assms(3) local.get_shadow_root_ok local.shadow_root_same_host
        returns_result_select_result shadow_root_eq_h)
  then have "a_distinct_lists h3"
    by(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h2 select_result_eq[OF shadow_root_eq_h2])
  then have "a_distinct_lists h'"
    by(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h3 select_result_eq[OF shadow_root_eq_h3])


  have "a_shadow_root_valid h"
    using assms(1)
    by (simp add: heap_is_wellformed_def)
  then have "a_shadow_root_valid h2"
    by(auto simp add: a_shadow_root_valid_def shadow_root_ptr_kinds_eq_h element_ptr_kinds_eq_h
        select_result_eq[OF shadow_root_eq_h] tag_name_eq2_h)
  then have "a_shadow_root_valid h3"
    by(auto simp add: a_shadow_root_valid_def shadow_root_ptr_kinds_eq_h2 element_ptr_kinds_eq_h2
        select_result_eq[OF shadow_root_eq_h2] tag_name_eq2_h2)
  then have "a_shadow_root_valid h'"
    by(auto simp add: a_shadow_root_valid_def shadow_root_ptr_kinds_eq_h3 element_ptr_kinds_eq_h3
        select_result_eq[OF shadow_root_eq_h3] tag_name_eq2_h3)



  have "a_host_shadow_root_rel h = a_host_shadow_root_rel h2"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h select_result_eq[OF shadow_root_eq_h])
  have "a_host_shadow_root_rel h2 = a_host_shadow_root_rel h3"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h2 select_result_eq[OF shadow_root_eq_h2])
  have "a_host_shadow_root_rel h3 = a_host_shadow_root_rel h'"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h3 select_result_eq[OF shadow_root_eq_h3])

  have "a_ptr_disconnected_node_rel h = a_ptr_disconnected_node_rel h2"
    by(simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h disconnected_nodes_eq2_h)
  have "a_ptr_disconnected_node_rel h2 = a_ptr_disconnected_node_rel h3"
    by(simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h2 disconnected_nodes_eq2_h2)

  have "h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_character_data_ptr # disc_nodes_h3"
    using h' local.set_disconnected_nodes_get_disconnected_nodes by auto
  have " document_ptr |\<in>| document_ptr_kinds h3"
    by (simp add: \<open>document_ptr |\<in>| document_ptr_kinds h\<close> document_ptr_kinds_eq_h document_ptr_kinds_eq_h2)
  have "cast new_character_data_ptr \<in> set |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r"
    using \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_character_data_ptr # disc_nodes_h3\<close> by auto

  have "a_ptr_disconnected_node_rel h' = {(cast document_ptr, cast new_character_data_ptr)} \<union> a_ptr_disconnected_node_rel h3"
    apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h3 disconnected_nodes_eq2_h3)[1]
      apply(case_tac "aa = document_ptr")
    using disc_nodes_h3 h' \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_character_data_ptr # disc_nodes_h3\<close>
       apply(auto)[1]
    using disconnected_nodes_eq2_h3 apply auto[1]
    using \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_character_data_ptr # disc_nodes_h3\<close>
    using \<open>cast new_character_data_ptr \<in> set |h' \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r\<close>
    using \<open>document_ptr |\<in>| document_ptr_kinds h3\<close> apply auto[1]
    apply(case_tac "document_ptr = aa")
    using \<open>h' \<turnstile> get_disconnected_nodes document_ptr \<rightarrow>\<^sub>r cast new_character_data_ptr # disc_nodes_h3\<close> disc_nodes_h3 apply auto[1]
    using disconnected_nodes_eq_h3[THEN select_result_eq, simplified] by auto

  have "acyclic (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def)
  have "parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h =
parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2"
    using \<open>local.a_host_shadow_root_rel h = local.a_host_shadow_root_rel h2\<close>
      \<open>local.a_ptr_disconnected_node_rel h = local.a_ptr_disconnected_node_rel h2\<close> \<open>parent_child_rel h = parent_child_rel h2\<close> by auto
  have "parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2 =
parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3"
    using \<open>local.a_host_shadow_root_rel h2 = local.a_host_shadow_root_rel h3\<close>
      \<open>local.a_ptr_disconnected_node_rel h2 = local.a_ptr_disconnected_node_rel h3\<close> \<open>parent_child_rel h2 = parent_child_rel h3\<close> by auto
  have "parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h' =
{(cast document_ptr, cast new_character_data_ptr)} \<union> parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3"
    by (simp add: \<open>local.a_host_shadow_root_rel h3 = local.a_host_shadow_root_rel h'\<close>
        \<open>local.a_ptr_disconnected_node_rel h' = {(cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr, cast new_character_data_ptr)} \<union>
local.a_ptr_disconnected_node_rel h3\<close> \<open>parent_child_rel h3 = parent_child_rel h'\<close>)

  have "\<And>a b. (a, b) \<in> parent_child_rel h3 \<Longrightarrow> a \<noteq> cast new_character_data_ptr"
    using CD.parent_child_rel_parent_in_heap \<open>parent_child_rel h = parent_child_rel h2\<close>
      \<open>parent_child_rel h2 = parent_child_rel h3\<close> character_data_ptr_kinds_commutes h2 new_character_data_ptr
      new_character_data_ptr_not_in_heap node_ptr_kinds_commutes by blast
  moreover
  have "\<And>a b. (a, b) \<in> a_host_shadow_root_rel h3 \<Longrightarrow> a \<noteq> cast new_character_data_ptr"
    using shadow_root_eq_h2
    by(auto simp add: a_host_shadow_root_rel_def)
  moreover
  have "\<And>a b. (a, b) \<in> a_ptr_disconnected_node_rel h3 \<Longrightarrow> a \<noteq> cast new_character_data_ptr"
    by(auto simp add: a_ptr_disconnected_node_rel_def)
  moreover
  have "cast new_character_data_ptr \<notin> {x. (x, cast document_ptr) \<in>
(parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)\<^sup>*}"
    by (smt Un_iff calculation(1) calculation(2) calculation(3) cast_document_ptr_not_node_ptr(2)
        converse_rtranclE mem_Collect_eq)
  moreover
  have "acyclic (parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)"
    using \<open>acyclic (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> local.a_ptr_disconnected_node_rel h)\<close>
      \<open>parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> local.a_ptr_disconnected_node_rel h =
parent_child_rel h2 \<union> local.a_host_shadow_root_rel h2 \<union> local.a_ptr_disconnected_node_rel h2\<close>
      \<open>parent_child_rel h2 \<union> local.a_host_shadow_root_rel h2 \<union> local.a_ptr_disconnected_node_rel h2 =
parent_child_rel h3 \<union> local.a_host_shadow_root_rel h3 \<union> local.a_ptr_disconnected_node_rel h3\<close>
    by auto
  ultimately have "acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')"
    by(simp add: \<open>parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h' =
{(cast document_ptr, cast new_character_data_ptr)} \<union> parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3\<close>)


  have "CD.a_heap_is_wellformed h'"
    apply(simp add: CD.a_heap_is_wellformed_def)
    by (simp add: \<open>local.CD.a_acyclic_heap h'\<close> \<open>local.CD.a_all_ptrs_in_heap h'\<close>
        \<open>local.CD.a_distinct_lists h'\<close> \<open>local.CD.a_owner_document_valid h'\<close>)

  show " heap_is_wellformed h' "
    using \<open>acyclic (parent_child_rel h' \<union> local.a_host_shadow_root_rel h' \<union> local.a_ptr_disconnected_node_rel h')\<close>
    by(simp add: heap_is_wellformed_def CD.heap_is_wellformed_impl \<open>local.CD.a_heap_is_wellformed h'\<close>
        \<open>local.a_all_ptrs_in_heap h'\<close> \<open>local.a_distinct_lists h'\<close> \<open>local.a_shadow_root_valid h'\<close>)
qed
end

subsubsection \<open>create\_document\<close>

locale l_create_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_child_nodes get_child_nodes_locs get_disconnected_nodes
  get_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs known_ptr type_wf
  heap_is_wellformed parent_child_rel
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document get_disconnected_document_locs
  + l_new_document_get_disconnected_nodes
  get_disconnected_nodes get_disconnected_nodes_locs
  + l_create_document\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  create_document
  + l_new_document_get_child_nodes
  type_wf known_ptr get_child_nodes get_child_nodes_locs
  + l_get_tag_name type_wf get_tag_name get_tag_name_locs
  + l_new_document_get_tag_name get_tag_name get_tag_name_locs
  + l_get_disconnected_nodes\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M type_wf type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_disconnected_nodes get_disconnected_nodes_locs
  + l_new_document
  type_wf
  + l_known_ptrs
  known_ptr known_ptrs
  for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
    and type_wf :: "(_) heap \<Rightarrow> bool"
    and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
    and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
    and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
    and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
    and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
    and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and get_disconnected_document :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
    and get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
    and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
    and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
    and set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_val_locs :: "(_) character_data_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
    and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
    and create_document :: "((_) heap, exception, (_) document_ptr) prog"
    and known_ptrs :: "(_) heap \<Rightarrow> bool"
begin

lemma create_document_preserves_wellformedness:
  assumes "heap_is_wellformed h"
    and "h \<turnstile> create_document \<rightarrow>\<^sub>h h'"
    and "type_wf h"
    and "known_ptrs h"
  shows "heap_is_wellformed h'"
proof -
  obtain new_document_ptr where
    new_document_ptr: "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr" and
    h': "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
    using assms(2)
    apply(simp add: create_document_def)
    using new_document_ok by blast

  have "new_document_ptr \<notin> set |h \<turnstile> document_ptr_kinds_M|\<^sub>r"
    using new_document_ptr DocumentMonad.ptr_kinds_ptr_kinds_M
    using new_document_ptr_not_in_heap h' by blast
  then have "cast new_document_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp

  have "new_document_ptr |\<notin>| document_ptr_kinds h"
    using new_document_ptr DocumentMonad.ptr_kinds_ptr_kinds_M
    using new_document_ptr_not_in_heap h' by blast
  then have "cast new_document_ptr |\<notin>| object_ptr_kinds h"
    by simp

  have object_ptr_kinds_eq: "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_document_ptr|}"
    using new_document_new_ptr h' new_document_ptr by blast
  then have node_ptr_kinds_eq: "node_ptr_kinds h' = node_ptr_kinds h"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have character_data_ptr_kinds_eq_h: "character_data_ptr_kinds h' = character_data_ptr_kinds h"
    by(simp add: character_data_ptr_kinds_def)
  have element_ptr_kinds_eq_h: "element_ptr_kinds h' = element_ptr_kinds h"
    using object_ptr_kinds_eq
    by(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h' = document_ptr_kinds h |\<union>| {|new_document_ptr|}"
    using object_ptr_kinds_eq
    apply(auto simp add: document_ptr_kinds_def)[1]
    by (metis (no_types, lifting) document_ptr_kinds_commutes document_ptr_kinds_def finsertI1 fset.map_comp)


  have children_eq:
    "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_document_ptr
             \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads h' get_child_nodes_new_document[rotated, OF new_document_ptr h']
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2: "\<And>ptr'. ptr' \<noteq> cast new_document_ptr
                                    \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force


  have "h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []"
    using new_document_ptr h' new_document_ptr_in_heap[OF h' new_document_ptr]
      new_document_is_document_ptr[OF new_document_ptr] new_document_no_child_nodes
    by blast
  have disconnected_nodes_eq_h:
    "\<And>doc_ptr disc_nodes. doc_ptr \<noteq> new_document_ptr
    \<Longrightarrow> h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using CD.get_disconnected_nodes_reads h' get_disconnected_nodes_new_document_different_pointers new_document_ptr
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by (metis(full_types) \<open>\<And>thesis. (\<And>new_document_ptr.
             \<lbrakk>h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr; h \<turnstile> new_document \<rightarrow>\<^sub>h h'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
        local.get_disconnected_nodes_new_document_different_pointers new_document_ptr)+
  then have disconnected_nodes_eq2_h: "\<And>doc_ptr. doc_ptr \<noteq> new_document_ptr
                 \<Longrightarrow> |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have "h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []"
    using h' local.new_document_no_disconnected_nodes new_document_ptr by blast

  have "type_wf h'"
    using \<open>type_wf h\<close> new_document_types_preserved h' by blast

  have "acyclic (parent_child_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (auto simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def)
  also have "parent_child_rel h = parent_child_rel h'"
  proof(auto simp add: CD.parent_child_rel_def)[1]
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h"
      and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h'"
      by (simp add: object_ptr_kinds_eq)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h"
      and 1: "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h' \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis ObjectMonad.ptr_kinds_ptr_kinds_M
          \<open>cast new_document_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> children_eq2)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h'"
      and 1: "x \<in> set |h' \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h"
      using object_ptr_kinds_eq \<open>h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []\<close>
      by(auto)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h'"
      and 1: "x \<in> set |h' \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis (no_types, lifting) \<open>h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []\<close>
          children_eq2 empty_iff empty_set image_eqI select_result_I2)
  qed
  finally have "CD.a_acyclic_heap h'"
    by (simp add: CD.acyclic_heap_def)

  have "CD.a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def )
  then have "CD.a_all_ptrs_in_heap h'"
    apply(auto simp add: CD.a_all_ptrs_in_heap_def)[1]
    using  ObjectMonad.ptr_kinds_ptr_kinds_M
      \<open>cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close>
      \<open>parent_child_rel h = parent_child_rel h'\<close> assms(1) children_eq fset_of_list_elem
      local.heap_is_wellformed_children_in_heap CD.parent_child_rel_child
      CD.parent_child_rel_parent_in_heap node_ptr_kinds_eq
     apply (metis (no_types, lifting) \<open>h' \<turnstile> get_child_nodes (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr) \<rightarrow>\<^sub>r []\<close>
        children_eq2 finite_set_in finsert_iff funion_finsert_right object_ptr_kinds_eq
        select_result_I2 subsetD sup_bot.right_neutral)
    by (metis (no_types, lifting) \<open>h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []\<close> \<open>type_wf h'\<close>
        assms(1) disconnected_nodes_eq_h empty_iff empty_set local.get_disconnected_nodes_ok
        local.heap_is_wellformed_disc_nodes_in_heap node_ptr_kinds_eq returns_result_select_result select_result_I2)

  have "CD.a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_distinct_lists h'"
    using \<open>h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []\<close>
      \<open>h' \<turnstile> get_child_nodes (cast new_document_ptr) \<rightarrow>\<^sub>r []\<close>

    apply(auto simp add: children_eq2[symmetric] CD.a_distinct_lists_def insort_split object_ptr_kinds_eq
        document_ptr_kinds_eq_h  disconnected_nodes_eq2_h intro!: distinct_concat_map_I)[1]
          apply (metis distinct_sorted_list_of_set finite_fset sorted_list_of_set_insert)

         apply(auto simp add:  dest: distinct_concat_map_E)[1]
        apply(auto simp add:  dest: distinct_concat_map_E)[1]
    using \<open>new_document_ptr |\<notin>| document_ptr_kinds h\<close>
       apply(auto simp add: distinct_insort dest: distinct_concat_map_E)[1]
      apply (metis assms(1) assms(3) disconnected_nodes_eq2_h get_disconnected_nodes_ok
        local.heap_is_wellformed_disconnected_nodes_distinct
        returns_result_select_result)
  proof -
    fix x :: "(_) document_ptr" and y :: "(_) document_ptr" and xa :: "(_) node_ptr"
    assume a1: "x \<noteq> y"
    assume a2: "x |\<in>| document_ptr_kinds h"
    assume a3: "x \<noteq> new_document_ptr"
    assume a4: "y |\<in>| document_ptr_kinds h"
    assume a5: "y \<noteq> new_document_ptr"
    assume a6: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                              (sorted_list_of_set (fset (document_ptr_kinds h)))))"
    assume a7: "xa \<in> set |h' \<turnstile> get_disconnected_nodes x|\<^sub>r"
    assume a8: "xa \<in> set |h' \<turnstile> get_disconnected_nodes y|\<^sub>r"
    have f9: "xa \<in> set |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using a7 a3 disconnected_nodes_eq2_h by presburger
    have f10: "xa \<in> set |h \<turnstile> get_disconnected_nodes y|\<^sub>r"
      using a8 a5 disconnected_nodes_eq2_h by presburger
    have f11: "y \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))"
      using a4 by simp
    have "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))"
      using a2 by simp
    then show False
      using f11 f10 f9 a6 a1 by (meson disjoint_iff_not_equal distinct_concat_map_E(1))
  next
    fix x xa xb
    assume 0: "h' \<turnstile> get_disconnected_nodes new_document_ptr \<rightarrow>\<^sub>r []"
      and 1: "h' \<turnstile> get_child_nodes (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr) \<rightarrow>\<^sub>r []"
      and 2: "distinct (concat (map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r)
                                                  (sorted_list_of_set (fset (object_ptr_kinds h)))))"
      and 3: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                              (sorted_list_of_set (fset (document_ptr_kinds h)))))"
      and 4: "(\<Union>x\<in>fset (object_ptr_kinds h). set |h \<turnstile> get_child_nodes x|\<^sub>r)
                      \<inter> (\<Union>x\<in>fset (document_ptr_kinds h). set |h \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 5: "x \<in> set |h \<turnstile> get_child_nodes xa|\<^sub>r"
      and 6: "x \<in> set |h' \<turnstile> get_disconnected_nodes xb|\<^sub>r"
      and 7: "xa |\<in>| object_ptr_kinds h"
      and 8: "xa \<noteq> cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr"
      and 9: "xb |\<in>| document_ptr_kinds h"
      and 10: "xb \<noteq> new_document_ptr"
    then show "False"

      by (metis \<open>CD.a_distinct_lists h\<close> assms(3) disconnected_nodes_eq2_h
          CD.distinct_lists_no_parent get_disconnected_nodes_ok
          returns_result_select_result)
  qed

  have "CD.a_owner_document_valid h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_owner_document_valid h'"
    apply(auto simp add: CD.a_owner_document_valid_def)[1]
    by (metis \<open>cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_document_ptr |\<notin>| object_ptr_kinds h\<close>
        children_eq2 disconnected_nodes_eq2_h document_ptr_kinds_commutes finite_set_in funion_iff
        node_ptr_kinds_eq object_ptr_kinds_eq)

  have shadow_root_eq_h: "\<And>character_data_ptr shadow_root_opt. h \<turnstile> get_shadow_root character_data_ptr \<rightarrow>\<^sub>r shadow_root_opt =
h' \<turnstile> get_shadow_root character_data_ptr \<rightarrow>\<^sub>r shadow_root_opt"
    using get_shadow_root_reads assms(2) get_shadow_root_new_document[rotated, OF h']
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    using local.get_shadow_root_locs_impl new_document_ptr apply blast
    using local.get_shadow_root_locs_impl new_document_ptr by blast


  have "a_all_ptrs_in_heap h"
    by (simp add: assms(1) local.a_all_ptrs_in_heap_def local.get_shadow_root_shadow_root_ptr_in_heap)
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_def document_ptr_kinds_eq_h)[1]
    using shadow_root_eq_h by fastforce

  have "a_distinct_lists h"
    using assms(1)
    by (simp add: heap_is_wellformed_def)
  then have "a_distinct_lists h'"
    apply(auto simp add: a_distinct_lists_def character_data_ptr_kinds_eq_h)[1]
    apply(auto simp add: distinct_insort intro!: distinct_concat_map_I split: option.splits)[1]
    by (metis \<open>type_wf h'\<close> assms(1) assms(3) local.get_shadow_root_ok local.shadow_root_same_host
        returns_result_select_result shadow_root_eq_h)


  have tag_name_eq_h:
    "\<And>ptr' disc_nodes. h \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h' \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads h'
      get_tag_name_new_document[OF new_document_ptr h']
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+

  have "a_shadow_root_valid h"
    using assms(1)
    by (simp add: heap_is_wellformed_def)
  then have "a_shadow_root_valid h'"
    using new_document_is_document_ptr[OF new_document_ptr]
    by(auto simp add: a_shadow_root_valid_def element_ptr_kinds_eq_h document_ptr_kinds_eq_h
        shadow_root_ptr_kinds_def select_result_eq[OF shadow_root_eq_h] select_result_eq[OF tag_name_eq_h]
        is_shadow_root_ptr_kind\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def is_document_ptr\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
        split: option.splits)


  have "a_host_shadow_root_rel h = a_host_shadow_root_rel h'"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h select_result_eq[OF shadow_root_eq_h])

  have "a_ptr_disconnected_node_rel h = a_ptr_disconnected_node_rel h'"
    apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h disconnected_nodes_eq2_h)[1]
    using \<open>new_document_ptr |\<notin>| document_ptr_kinds h\<close> disconnected_nodes_eq2_h apply fastforce
    using new_document_disconnected_nodes[OF h' new_document_ptr]
     apply(simp add: CD.get_disconnected_nodes_impl CD.a_get_disconnected_nodes_def)
    using \<open>new_document_ptr |\<notin>| document_ptr_kinds h\<close> disconnected_nodes_eq2_h apply fastforce
    done

  have "acyclic (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def)
  moreover
  have "parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h =
parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h'"
    by (simp add: \<open>local.a_host_shadow_root_rel h = local.a_host_shadow_root_rel h'\<close>
        \<open>local.a_ptr_disconnected_node_rel h = local.a_ptr_disconnected_node_rel h'\<close>
        \<open>parent_child_rel h = parent_child_rel h'\<close>)
  ultimately have "acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')"
    by simp

  have "CD.a_heap_is_wellformed h'"
    apply(simp add: CD.a_heap_is_wellformed_def)
    by (simp add: \<open>local.CD.a_acyclic_heap h'\<close> \<open>local.CD.a_all_ptrs_in_heap h'\<close>
        \<open>local.CD.a_distinct_lists h'\<close> \<open>local.CD.a_owner_document_valid h'\<close>)

  show "heap_is_wellformed h'"
    using CD.heap_is_wellformed_impl \<open>acyclic (parent_child_rel h' \<union> local.a_host_shadow_root_rel h' \<union>
local.a_ptr_disconnected_node_rel h')\<close> \<open>local.CD.a_heap_is_wellformed h'\<close> \<open>local.a_all_ptrs_in_heap h'\<close>
      \<open>local.a_distinct_lists h'\<close> \<open>local.a_shadow_root_valid h'\<close> local.heap_is_wellformed_def by auto
qed
end

interpretation l_create_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr type_wf DocumentClass.type_wf get_child_nodes
  get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs get_shadow_root
  get_shadow_root_locs get_tag_name get_tag_name_locs
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document get_disconnected_document_locs
  heap_is_wellformed parent_child_rel set_val set_val_locs set_disconnected_nodes set_disconnected_nodes_locs
  create_document known_ptrs
  by(auto simp add: l_create_document_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)


subsubsection \<open>attach\_shadow\_root\<close>

locale l_attach_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M =
  l_get_disconnected_nodes
  type_wf get_disconnected_nodes get_disconnected_nodes_locs
  + l_heap_is_wellformed\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  get_shadow_root get_shadow_root_locs get_tag_name get_tag_name_locs known_ptr type_wf
  heap_is_wellformed parent_child_rel
  heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document get_disconnected_document_locs
  + l_attach_shadow_root\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr set_shadow_root set_shadow_root_locs set_mode set_mode_locs
  attach_shadow_root type_wf get_tag_name get_tag_name_locs get_shadow_root get_shadow_root_locs
  + l_new_shadow_root_get_disconnected_nodes
  get_disconnected_nodes get_disconnected_nodes_locs

+ l_set_mode_get_disconnected_nodes
type_wf set_mode set_mode_locs get_disconnected_nodes get_disconnected_nodes_locs
+ l_new_shadow_root_get_child_nodes
type_wf known_ptr get_child_nodes get_child_nodes_locs
+ l_new_shadow_root_get_tag_name
type_wf get_tag_name get_tag_name_locs
+ l_set_mode_get_child_nodes
type_wf set_mode set_mode_locs known_ptr get_child_nodes get_child_nodes_locs
+ l_set_shadow_root_get_child_nodes
type_wf set_shadow_root set_shadow_root_locs known_ptr get_child_nodes get_child_nodes_locs
+ l_set_shadow_root
type_wf set_shadow_root set_shadow_root_locs
+ l_set_shadow_root_get_disconnected_nodes
set_shadow_root set_shadow_root_locs get_disconnected_nodes get_disconnected_nodes_locs
+ l_set_mode_get_shadow_root type_wf set_mode set_mode_locs get_shadow_root get_shadow_root_locs
+ l_set_shadow_root_get_shadow_root type_wf set_shadow_root set_shadow_root_locs
get_shadow_root get_shadow_root_locs
+ l_new_character_data_get_tag_name
get_tag_name get_tag_name_locs
+ l_set_mode_get_tag_name type_wf set_mode set_mode_locs get_tag_name get_tag_name_locs
+ l_get_tag_name type_wf get_tag_name get_tag_name_locs
+ l_set_shadow_root_get_tag_name set_shadow_root set_shadow_root_locs get_tag_name get_tag_name_locs
+ l_new_shadow_root
type_wf
+ l_known_ptrs
known_ptr known_ptrs
for known_ptr :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and known_ptrs :: "(_) heap \<Rightarrow> bool"
  and type_wf :: "(_) heap \<Rightarrow> bool"
  and get_child_nodes :: "(_) object_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_child_nodes_locs :: "(_) object_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_nodes :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, (_) node_ptr list) prog"
  and get_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed :: "(_) heap \<Rightarrow> bool"
  and parent_child_rel :: "(_) heap \<Rightarrow> ((_) object_ptr \<times> (_) object_ptr) set"
  and set_tag_name :: "(_) element_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and set_disconnected_nodes :: "(_) document_ptr \<Rightarrow> (_) node_ptr list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_disconnected_nodes_locs :: "(_) document_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and create_element :: "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
  and get_shadow_root :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, (_) shadow_root_ptr option) prog"
  and get_shadow_root_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_tag_name :: "(_) element_ptr \<Rightarrow> ((_) heap, exception, char list) prog"
  and get_tag_name_locs :: "(_) element_ptr \<Rightarrow> ((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
  and get_host :: "(_) shadow_root_ptr \<Rightarrow> ((_) heap, exception, (_) element_ptr) prog"
  and get_host_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and get_disconnected_document :: "(_) node_ptr \<Rightarrow> ((_) heap, exception, (_) document_ptr) prog"
  and get_disconnected_document_locs :: "((_) heap \<Rightarrow> (_) heap \<Rightarrow> bool) set"
  and set_val :: "(_) character_data_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, unit) prog"
  and set_val_locs :: "(_) character_data_ptr \<Rightarrow> ((_) heap, exception, unit) prog set"
  and create_character_data ::
  "(_) document_ptr \<Rightarrow> char list \<Rightarrow> ((_) heap, exception, (_) character_data_ptr) prog"
  and known_ptr\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_::linorder) object_ptr \<Rightarrow> bool"
  and type_wf\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M :: "(_) heap \<Rightarrow> bool"
  and set_shadow_root :: "(_) element_ptr \<Rightarrow> (_) shadow_root_ptr option \<Rightarrow> (_, unit) dom_prog"
  and set_shadow_root_locs :: "(_) element_ptr \<Rightarrow> (_, unit) dom_prog set"
  and set_mode :: "(_) shadow_root_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> (_, unit) dom_prog"
  and set_mode_locs :: "(_) shadow_root_ptr \<Rightarrow> (_, unit) dom_prog set"
  and attach_shadow_root :: "(_) element_ptr \<Rightarrow> shadow_root_mode \<Rightarrow> (_, (_) shadow_root_ptr) dom_prog"
begin
lemma attach_shadow_root_child_preserves:
  assumes "heap_is_wellformed h" and "type_wf h" and "known_ptrs h"
  assumes "h \<turnstile> attach_shadow_root element_ptr new_mode \<rightarrow>\<^sub>h h'"
  shows "type_wf h'" and "known_ptrs h'" and "heap_is_wellformed h'"
proof -
  obtain h2 h3 new_shadow_root_ptr element_tag_name where
    element_tag_name: "h \<turnstile> get_tag_name element_ptr \<rightarrow>\<^sub>r element_tag_name" and
    "element_tag_name \<in> safe_shadow_root_element_types" and
    prev_shadow_root: "h \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r None" and
    h2: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h2" and
    new_shadow_root_ptr: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr" and
    h3: "h2 \<turnstile> set_mode new_shadow_root_ptr new_mode \<rightarrow>\<^sub>h h3" and
    h': "h3 \<turnstile> set_shadow_root element_ptr (Some new_shadow_root_ptr) \<rightarrow>\<^sub>h h'"
    using assms(4)
    by(auto simp add: attach_shadow_root_def elim!: bind_returns_heap_E
        bind_returns_heap_E2[rotated, OF get_tag_name_pure, rotated]
        bind_returns_heap_E2[rotated, OF get_shadow_root_pure, rotated] split: if_splits)

  have "h \<turnstile> attach_shadow_root element_ptr new_mode \<rightarrow>\<^sub>r new_shadow_root_ptr"
    thm  bind_pure_returns_result_I[OF get_tag_name_pure]
    apply(unfold attach_shadow_root_def)[1]
    using element_tag_name
    apply(rule bind_pure_returns_result_I[OF get_tag_name_pure])
    apply(rule bind_pure_returns_result_I)
    using \<open>element_tag_name \<in> safe_shadow_root_element_types\<close> apply(simp)
    using \<open>element_tag_name \<in> safe_shadow_root_element_types\<close> apply(simp)
    using prev_shadow_root
    apply(rule bind_pure_returns_result_I[OF get_shadow_root_pure])
    apply(rule bind_pure_returns_result_I)
      apply(simp)
     apply(simp)
    using h2 new_shadow_root_ptr h3 h'
    by(auto intro!: bind_returns_result_I intro: is_OK_returns_result_E[OF is_OK_returns_heap_I[OF h3]]
        is_OK_returns_result_E[OF is_OK_returns_heap_I[OF h']])

  have "new_shadow_root_ptr \<notin> set |h \<turnstile> shadow_root_ptr_kinds_M|\<^sub>r"
    using new_shadow_root_ptr ShadowRootMonad.ptr_kinds_ptr_kinds_M h2
    using new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_not_in_heap by blast
  then have "cast new_shadow_root_ptr \<notin> set |h \<turnstile> document_ptr_kinds_M|\<^sub>r"
    by simp
  then have "cast new_shadow_root_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r"
    by simp



  have object_ptr_kinds_eq_h:
    "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_shadow_root_ptr|}"
    using new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_new_ptr h2 new_shadow_root_ptr by blast
  then have document_ptr_kinds_eq_h:
    "document_ptr_kinds h2 = document_ptr_kinds h |\<union>| {|cast new_shadow_root_ptr|}"
    apply(simp add: document_ptr_kinds_def)
    by force
  then have shadow_root_ptr_kinds_eq_h:
    "shadow_root_ptr_kinds h2 = shadow_root_ptr_kinds h |\<union>| {|new_shadow_root_ptr|}"
    apply(simp add: shadow_root_ptr_kinds_def)
    by force
  have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_mode_writes h3])
    using set_mode_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  then have shadow_root_ptr_kinds_eq_h2: "shadow_root_ptr_kinds h3 = shadow_root_ptr_kinds h2"
    by (auto simp add: shadow_root_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2
    by(auto simp add: node_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_shadow_root_writes h'])
    using set_shadow_root_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  then have shadow_root_ptr_kinds_eq_h3: "shadow_root_ptr_kinds h' = shadow_root_ptr_kinds h3"
    by (auto simp add: shadow_root_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)

  have "known_ptr (cast new_shadow_root_ptr)"
    using \<open>h \<turnstile> attach_shadow_root element_ptr new_mode \<rightarrow>\<^sub>r new_shadow_root_ptr\<close> create_shadow_root_known_ptr
    by blast
  then
  have "known_ptrs h2"
    using known_ptrs_new_ptr object_ptr_kinds_eq_h \<open>known_ptrs h\<close> h2
    by blast
  then
  have "known_ptrs h3"
    using known_ptrs_preserved object_ptr_kinds_eq_h2 by blast
  then
  show "known_ptrs h'"
    using known_ptrs_preserved object_ptr_kinds_eq_h3 by blast

  have "element_ptr |\<in>| element_ptr_kinds h"
    by (meson \<open>h \<turnstile> attach_shadow_root element_ptr new_mode \<rightarrow>\<^sub>r new_shadow_root_ptr\<close> is_OK_returns_result_I
        local.attach_shadow_root_element_ptr_in_heap)


  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_shadow_root_ptr
                  \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads h2 get_child_nodes_new_shadow_root[rotated, OF new_shadow_root_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h:
    "\<And>ptr'. ptr' \<noteq> cast new_shadow_root_ptr
      \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have object_ptr_kinds_eq_h:
    "object_ptr_kinds h2 = object_ptr_kinds h |\<union>| {|cast new_shadow_root_ptr|}"
    using new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_new_ptr h2 new_shadow_root_ptr object_ptr_kinds_eq_h by blast
  then have node_ptr_kinds_eq_h:
    "node_ptr_kinds h2 = node_ptr_kinds h"
    apply(simp add: node_ptr_kinds_def)
    by force
  then have character_data_ptr_kinds_eq_h:
    "character_data_ptr_kinds h2 = character_data_ptr_kinds h"
    apply(simp add: character_data_ptr_kinds_def)
    done
  have element_ptr_kinds_eq_h: "element_ptr_kinds h2 = element_ptr_kinds h"
    using object_ptr_kinds_eq_h
    by(auto simp add: node_ptr_kinds_def element_ptr_kinds_def)
  have document_ptr_kinds_eq_h: "document_ptr_kinds h2 = document_ptr_kinds h |\<union>| {|cast new_shadow_root_ptr|}"
    using object_ptr_kinds_eq_h
    apply(auto simp add: document_ptr_kinds_def)[1]
    by (metis (full_types) document_ptr_kinds_def document_ptr_kinds_eq_h finsert_fsubset fset.map_comp funion_upper2)

  have object_ptr_kinds_eq_h2: "object_ptr_kinds h3 = object_ptr_kinds h2"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_mode_writes h3])
    using set_mode_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h2: "document_ptr_kinds h3 = document_ptr_kinds h2"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h2: "node_ptr_kinds h3 = node_ptr_kinds h2"
    using object_ptr_kinds_eq_h2
    by(auto simp add: node_ptr_kinds_def)
  then have character_data_ptr_kinds_eq_h2: "character_data_ptr_kinds h3 = character_data_ptr_kinds h2"
    by(simp add: character_data_ptr_kinds_def)
  have element_ptr_kinds_eq_h2: "element_ptr_kinds h3 = element_ptr_kinds h2"
    using node_ptr_kinds_eq_h2
    by(simp add: element_ptr_kinds_def)

  have object_ptr_kinds_eq_h3: "object_ptr_kinds h' = object_ptr_kinds h3"
    apply(rule writes_small_big[where P="\<lambda>h h'. object_ptr_kinds h' = object_ptr_kinds h",
          OF set_shadow_root_writes h'])
    using set_shadow_root_pointers_preserved
    by (auto simp add: reflp_def transp_def)
  then have document_ptr_kinds_eq_h3: "document_ptr_kinds h' = document_ptr_kinds h3"
    by (auto simp add: document_ptr_kinds_def)
  have node_ptr_kinds_eq_h3: "node_ptr_kinds h' = node_ptr_kinds h3"
    using object_ptr_kinds_eq_h3
    by(auto simp add: node_ptr_kinds_def)
  then have character_data_ptr_kinds_eq_h3: "character_data_ptr_kinds h' = character_data_ptr_kinds h3"
    by(simp add: character_data_ptr_kinds_def)
  have element_ptr_kinds_eq_h3: "element_ptr_kinds h' = element_ptr_kinds h3"
    using node_ptr_kinds_eq_h3
    by(simp add: element_ptr_kinds_def)


  have children_eq_h: "\<And>(ptr'::(_) object_ptr) children. ptr' \<noteq> cast new_shadow_root_ptr
                \<Longrightarrow> h \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads h2 get_child_nodes_new_shadow_root[rotated, OF new_shadow_root_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have children_eq2_h: "\<And>ptr'. ptr' \<noteq> cast new_shadow_root_ptr
                                 \<Longrightarrow> |h \<turnstile> get_child_nodes ptr'|\<^sub>r = |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_child_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []"
    using h2 local.new_shadow_root_no_child_nodes new_shadow_root_ptr by auto

  have disconnected_nodes_eq_h:
    "\<And>doc_ptr disc_nodes. doc_ptr \<noteq> cast new_shadow_root_ptr
                \<Longrightarrow> h \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                             = h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads h2
      get_disconnected_nodes_new_shadow_root_different_pointers[rotated, OF new_shadow_root_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by (metis (no_types, lifting))+
  then have disconnected_nodes_eq2_h:
    "\<And>doc_ptr. doc_ptr \<noteq> cast new_shadow_root_ptr
                \<Longrightarrow> |h \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force

  have "h2 \<turnstile> get_disconnected_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []"
    using h2 new_shadow_root_no_disconnected_nodes new_shadow_root_ptr by auto

  have tag_name_eq_h:
    "\<And>ptr' disc_nodes. h \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads h2
      get_tag_name_new_shadow_root[OF new_shadow_root_ptr h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    by blast+
  then have tag_name_eq2_h: "\<And>ptr'. |h \<turnstile> get_tag_name ptr'|\<^sub>r = |h2 \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force

  have children_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads set_mode_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_mode_get_child_nodes)
  then have children_eq2_h2:
    "\<And>ptr'. |h2 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h2:
    "\<And>doc_ptr disc_nodes. h2 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                                              = h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_mode_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_mode_get_disconnected_nodes)
  then have disconnected_nodes_eq2_h2:
    "\<And>doc_ptr. |h2 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have tag_name_eq_h2:
    "\<And>ptr' disc_nodes. h2 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads set_mode_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_mode_get_tag_name)
  then have tag_name_eq2_h2: "\<And>ptr'. |h2 \<turnstile> get_tag_name ptr'|\<^sub>r = |h3 \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force

  have "type_wf h2"
    using \<open>type_wf h\<close> new_shadow_root_types_preserved h2 by blast
  then have "type_wf h3"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_mode_writes h3]
    using  set_mode_types_preserved
    by(auto simp add: reflp_def transp_def)
  then show "type_wf h'"
    using writes_small_big[where P="\<lambda>h h'. type_wf h \<longrightarrow> type_wf h'", OF set_shadow_root_writes h']
    using  set_shadow_root_types_preserved
    by(auto simp add: reflp_def transp_def)

  have children_eq_h3:
    "\<And>ptr' children. h3 \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_child_nodes ptr' \<rightarrow>\<^sub>r children"
    using CD.get_child_nodes_reads set_shadow_root_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_shadow_root_get_child_nodes)
  then have children_eq2_h3:
    " \<And>ptr'. |h3 \<turnstile> get_child_nodes ptr'|\<^sub>r = |h' \<turnstile> get_child_nodes ptr'|\<^sub>r"
    using select_result_eq by force
  have disconnected_nodes_eq_h3: "\<And>doc_ptr disc_nodes. h3 \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes
                            = h' \<turnstile> get_disconnected_nodes doc_ptr \<rightarrow>\<^sub>r disc_nodes"
    using get_disconnected_nodes_reads set_shadow_root_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_shadow_root_get_disconnected_nodes)
  then have disconnected_nodes_eq2_h3: "\<And>doc_ptr. |h3 \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r = |h' \<turnstile> get_disconnected_nodes doc_ptr|\<^sub>r"
    using select_result_eq by force
  have tag_name_eq_h3:
    "\<And>ptr' disc_nodes. h3 \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes
                                             = h' \<turnstile> get_tag_name ptr' \<rightarrow>\<^sub>r disc_nodes"
    using get_tag_name_reads set_shadow_root_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_shadow_root_get_tag_name)
  then have tag_name_eq2_h3: "\<And>ptr'. |h3 \<turnstile> get_tag_name ptr'|\<^sub>r = |h' \<turnstile> get_tag_name ptr'|\<^sub>r"
    using select_result_eq by force

  have "acyclic (parent_child_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def CD.acyclic_heap_def)
  also have "parent_child_rel h = parent_child_rel h2"
  proof(auto simp add: CD.parent_child_rel_def)[1]
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
          \<open>cast new_shadow_root_ptr \<notin> set |h \<turnstile> object_ptr_kinds_M|\<^sub>r\<close> children_eq2_h)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h2"
      and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
    then show "a |\<in>| object_ptr_kinds h"
      using object_ptr_kinds_eq_h \<open>h2 \<turnstile> get_child_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
      by(auto)
  next
    fix a x
    assume 0: "a |\<in>| object_ptr_kinds h2"
      and 1: "x \<in> set |h2 \<turnstile> get_child_nodes a|\<^sub>r"
    then show "x \<in> set |h \<turnstile> get_child_nodes a|\<^sub>r"
      by (metis (no_types, lifting) \<open>h2 \<turnstile> get_child_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
          children_eq2_h empty_iff empty_set image_eqI select_result_I2)
  qed
  also have "\<dots> = parent_child_rel h3"
    by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq_h2 children_eq2_h2)
  also have "\<dots> = parent_child_rel h'"
    by(auto simp add: CD.parent_child_rel_def object_ptr_kinds_eq_h3 children_eq2_h3)
  finally have "CD.a_acyclic_heap h'"
    by (simp add: CD.acyclic_heap_def)

  have "CD.a_all_ptrs_in_heap h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_all_ptrs_in_heap h2"
    apply(auto simp add: CD.a_all_ptrs_in_heap_def)[1]
    using node_ptr_kinds_eq_h
      \<open>h2 \<turnstile> get_child_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
     apply (metis (no_types, lifting) CD.get_child_nodes_ok CD.l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms \<open>known_ptrs h2\<close>
        \<open>parent_child_rel h = parent_child_rel h2\<close> \<open>type_wf h2\<close> assms(1) assms(2) l_heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M.parent_child_rel_child
        local.known_ptrs_known_ptr local.parent_child_rel_child_in_heap node_ptr_kinds_commutes returns_result_select_result)
    by (metis (no_types, hide_lams) \<open>h2 \<turnstile> get_disconnected_nodes (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
        \<open>type_wf h2\<close> disconnected_nodes_eq_h empty_iff finite_set_in is_OK_returns_result_E is_OK_returns_result_I
        local.get_disconnected_nodes_ok local.get_disconnected_nodes_ptr_in_heap node_ptr_kinds_eq_h select_result_I2
        set_empty subset_code(1))
  then have "CD.a_all_ptrs_in_heap h3"
    by (simp add: children_eq2_h2 disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2
        CD.a_all_ptrs_in_heap_def node_ptr_kinds_eq_h2 object_ptr_kinds_eq_h2)
  then have "CD.a_all_ptrs_in_heap h'"
    by (simp add: children_eq2_h3 disconnected_nodes_eq2_h3 document_ptr_kinds_eq_h3
        CD.a_all_ptrs_in_heap_def node_ptr_kinds_eq_h3 object_ptr_kinds_eq_h3)

  have "cast new_shadow_root_ptr |\<notin>| document_ptr_kinds h"
    using h2 new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_not_in_heap new_shadow_root_ptr shadow_root_ptr_kinds_commutes by blast

  have "CD.a_distinct_lists h"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_distinct_lists h2"
    using \<open>h2 \<turnstile> get_disconnected_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
      \<open>h2 \<turnstile> get_child_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>

    apply(auto simp add: children_eq2_h[symmetric] CD.a_distinct_lists_def insort_split object_ptr_kinds_eq_h
        document_ptr_kinds_eq_h  disconnected_nodes_eq2_h intro!: distinct_concat_map_I)[1]
          apply (metis distinct_sorted_list_of_set finite_fset sorted_list_of_set_insert)

         apply(auto simp add:  dest: distinct_concat_map_E)[1]
        apply(auto simp add:  dest: distinct_concat_map_E)[1]
    using \<open>cast new_shadow_root_ptr |\<notin>| document_ptr_kinds h\<close>
       apply(auto simp add: distinct_insort dest: distinct_concat_map_E)[1]

      apply (metis (no_types) DocumentMonad.ptr_kinds_M_ptr_kinds DocumentMonad.ptr_kinds_ptr_kinds_M
        concat_map_all_distinct disconnected_nodes_eq2_h select_result_I2)
  proof -
    fix x :: "(_) document_ptr" and y :: "(_) document_ptr" and xa :: "(_) node_ptr"
    assume a1: "x \<noteq> y"
    assume a2: "x |\<in>| document_ptr_kinds h"
    assume a3: "x \<noteq> cast new_shadow_root_ptr"
    assume a4: "y |\<in>| document_ptr_kinds h"
    assume a5: "y \<noteq> cast new_shadow_root_ptr"
    assume a6: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                              (sorted_list_of_set (fset (document_ptr_kinds h)))))"
    assume a7: "xa \<in> set |h2 \<turnstile> get_disconnected_nodes x|\<^sub>r"
    assume a8: "xa \<in> set |h2 \<turnstile> get_disconnected_nodes y|\<^sub>r"
    have f9: "xa \<in> set |h \<turnstile> get_disconnected_nodes x|\<^sub>r"
      using a7 a3 disconnected_nodes_eq2_h
      by (simp add: disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3)
    have f10: "xa \<in> set |h \<turnstile> get_disconnected_nodes y|\<^sub>r"
      using a8 a5 disconnected_nodes_eq2_h
      by (simp add: disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3)
    have f11: "y \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))"
      using a4 by simp
    have "x \<in> set (sorted_list_of_set (fset (document_ptr_kinds h)))"
      using a2 by simp
    then show False
      using f11 f10 f9 a6 a1 by (meson disjoint_iff_not_equal distinct_concat_map_E(1))
  next
    fix x xa xb
    assume 0: "h2 \<turnstile> get_disconnected_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []"
      and 1: "h2 \<turnstile> get_child_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []"
      and 2: "distinct (concat (map (\<lambda>ptr. |h \<turnstile> get_child_nodes ptr|\<^sub>r)
                                                  (sorted_list_of_set (fset (object_ptr_kinds h)))))"
      and 3: "distinct (concat (map (\<lambda>document_ptr. |h \<turnstile> get_disconnected_nodes document_ptr|\<^sub>r)
                                              (sorted_list_of_set (fset (document_ptr_kinds h)))))"
      and 4: "(\<Union>x\<in>fset (object_ptr_kinds h). set |h \<turnstile> get_child_nodes x|\<^sub>r)
                      \<inter> (\<Union>x\<in>fset (document_ptr_kinds h). set |h \<turnstile> get_disconnected_nodes x|\<^sub>r) = {}"
      and 5: "x \<in> set |h \<turnstile> get_child_nodes xa|\<^sub>r"
      and 6: "x \<in> set |h2 \<turnstile> get_disconnected_nodes xb|\<^sub>r"
      and 7: "xa |\<in>| object_ptr_kinds h"
      and 8: "xa \<noteq> cast new_shadow_root_ptr"
      and 9: "xb |\<in>| document_ptr_kinds h"
      and 10: "xb \<noteq> cast new_shadow_root_ptr"
    then show "False"
      by (metis CD.distinct_lists_no_parent \<open>local.CD.a_distinct_lists h\<close> assms(2) disconnected_nodes_eq2_h
          local.get_disconnected_nodes_ok returns_result_select_result)
  qed
  then have "CD.a_distinct_lists h3"
    by(auto simp add: CD.a_distinct_lists_def disconnected_nodes_eq2_h2 document_ptr_kinds_eq_h2
        children_eq2_h2 object_ptr_kinds_eq_h2)[1]
  then have "CD.a_distinct_lists h'"
    by(auto simp add: CD.a_distinct_lists_def disconnected_nodes_eq2_h3 children_eq2_h3
        object_ptr_kinds_eq_h3 document_ptr_kinds_eq_h3 intro!: distinct_concat_map_I)

  have "CD.a_owner_document_valid h"
    using \<open>heap_is_wellformed h\<close>  by (simp add: heap_is_wellformed_def CD.heap_is_wellformed_def)
  then have "CD.a_owner_document_valid h'"
    (* using disc_nodes_h3 \<open>document_ptr |\<in>| document_ptr_kinds h\<close> *)
    apply(simp add: CD.a_owner_document_valid_def)
    apply(simp add: object_ptr_kinds_eq_h object_ptr_kinds_eq_h3 )
    apply(simp add: object_ptr_kinds_eq_h2)
    apply(simp add: document_ptr_kinds_eq_h document_ptr_kinds_eq_h3 )
    apply(simp add: document_ptr_kinds_eq_h2)
    apply(simp add: node_ptr_kinds_eq_h node_ptr_kinds_eq_h3 )
    apply(simp add: node_ptr_kinds_eq_h2 node_ptr_kinds_eq_h )
    apply(auto simp add: children_eq2_h2[symmetric] children_eq2_h3[symmetric] disconnected_nodes_eq2_h
        disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3)[1]
    by (metis CD.get_child_nodes_ok CD.get_child_nodes_ptr_in_heap
        \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr |\<notin>| document_ptr_kinds h\<close> assms(2) assms(3) children_eq2_h
        children_eq_h disconnected_nodes_eq2_h disconnected_nodes_eq2_h2 disconnected_nodes_eq2_h3
        document_ptr_kinds_commutes finite_set_in is_OK_returns_result_I local.known_ptrs_known_ptr
        returns_result_select_result)









  have shadow_root_eq_h: "\<And>character_data_ptr shadow_root_opt. h \<turnstile> get_shadow_root character_data_ptr \<rightarrow>\<^sub>r shadow_root_opt =
h2 \<turnstile> get_shadow_root character_data_ptr \<rightarrow>\<^sub>r shadow_root_opt"
    using get_shadow_root_reads h2 get_shadow_root_new_shadow_root[rotated, OF h2]
    apply(auto simp add: reads_def reflp_def transp_def preserved_def)[1]
    using local.get_shadow_root_locs_impl new_shadow_root_ptr apply blast
    using local.get_shadow_root_locs_impl new_shadow_root_ptr by blast


  have shadow_root_eq_h2:
    "\<And>ptr' children. h2 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children = h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children"
    using get_shadow_root_reads set_mode_writes h3
    apply(rule reads_writes_preserved)
    by(auto simp add: set_mode_get_shadow_root)
  have shadow_root_eq_h3:
    "\<And>ptr' children. element_ptr \<noteq> ptr' \<Longrightarrow> h3 \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children = h' \<turnstile> get_shadow_root ptr' \<rightarrow>\<^sub>r children"
    using get_shadow_root_reads set_shadow_root_writes h'
    apply(rule reads_writes_preserved)
    by(auto simp add: set_shadow_root_get_shadow_root_different_pointers)
  have shadow_root_h3: "h' \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r Some new_shadow_root_ptr"
    using \<open>type_wf h3\<close> h' local.set_shadow_root_get_shadow_root by blast


  have "a_all_ptrs_in_heap h"
    by (simp add: assms(1) local.a_all_ptrs_in_heap_def local.get_shadow_root_shadow_root_ptr_in_heap)
  then have "a_all_ptrs_in_heap h2"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h)[1]
    using returns_result_eq shadow_root_eq_h by fastforce
  then have "a_all_ptrs_in_heap h3"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h2)[1]
    using shadow_root_eq_h2 by blast
  then have "a_all_ptrs_in_heap h'"
    apply(auto simp add: a_all_ptrs_in_heap_def shadow_root_ptr_kinds_eq_h3)[1]
    apply(case_tac "shadow_root_ptr = new_shadow_root_ptr")
    using h2 new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_in_heap new_shadow_root_ptr shadow_root_ptr_kinds_eq_h2
     apply blast
    using \<open>type_wf h3\<close> h' local.set_shadow_root_get_shadow_root returns_result_eq shadow_root_eq_h3
    apply fastforce
    done

  have "a_distinct_lists h"
    using assms(1)
    by (simp add: heap_is_wellformed_def)
  then have "a_distinct_lists h2"
    apply(auto simp add: a_distinct_lists_def character_data_ptr_kinds_eq_h)[1]
    apply(auto simp add: distinct_insort intro!: distinct_concat_map_I split: option.splits)[1]
    by (metis \<open>type_wf h2\<close> assms(1) assms(2) local.get_shadow_root_ok local.shadow_root_same_host
        returns_result_select_result shadow_root_eq_h)
  then have "a_distinct_lists h3"
    by(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h2 select_result_eq[OF shadow_root_eq_h2])
  then have "a_distinct_lists h'"
    apply(auto simp add: a_distinct_lists_def element_ptr_kinds_eq_h3 select_result_eq[OF shadow_root_eq_h3])[1]
    apply(auto simp add: distinct_insort intro!: distinct_concat_map_I split: option.splits)[1]
    by (smt \<open>type_wf h3\<close> assms(1) assms(2) h' h2 local.get_shadow_root_ok
        local.get_shadow_root_shadow_root_ptr_in_heap local.set_shadow_root_get_shadow_root local.shadow_root_same_host
        new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_not_in_heap new_shadow_root_ptr returns_result_select_result select_result_I2 shadow_root_eq_h
        shadow_root_eq_h2 shadow_root_eq_h3)


  have "a_shadow_root_valid h"
    using assms(1)
    by (simp add: heap_is_wellformed_def)
  then
  have "a_shadow_root_valid h'"
  proof(unfold a_shadow_root_valid_def; safe)
    fix shadow_root_ptr
    assume "\<forall>shadow_root_ptr\<in>fset (shadow_root_ptr_kinds h). \<exists>host\<in>fset (element_ptr_kinds h).
|h \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types \<and> |h \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr"
    assume "a_shadow_root_valid h"
    assume "shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h')"
    show "\<exists>host\<in>fset (element_ptr_kinds h'). |h' \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types \<and>
|h' \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr"
    proof (cases "shadow_root_ptr = new_shadow_root_ptr")
      case True
      have "element_ptr \<in> fset (element_ptr_kinds h')"
        by (simp add: \<open>element_ptr |\<in>| element_ptr_kinds h\<close> element_ptr_kinds_eq_h element_ptr_kinds_eq_h2
            element_ptr_kinds_eq_h3)
      moreover have "|h' \<turnstile> get_tag_name element_ptr|\<^sub>r \<in> safe_shadow_root_element_types"
        by (smt \<open>\<And>thesis. (\<And>h2 h3 new_shadow_root_ptr element_tag_name. \<lbrakk>h \<turnstile> get_tag_name element_ptr \<rightarrow>\<^sub>r element_tag_name;
element_tag_name \<in> safe_shadow_root_element_types; h \<turnstile> get_shadow_root element_ptr \<rightarrow>\<^sub>r None; h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h2;
h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr; h2 \<turnstile> set_mode new_shadow_root_ptr new_mode \<rightarrow>\<^sub>h h3;
h3 \<turnstile> set_shadow_root element_ptr (Some new_shadow_root_ptr) \<rightarrow>\<^sub>h h'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
            select_result_I2 tag_name_eq2_h tag_name_eq2_h2 tag_name_eq2_h3)
      moreover have "|h' \<turnstile> get_shadow_root element_ptr|\<^sub>r = Some shadow_root_ptr"
        using shadow_root_h3
        by (simp add: True)
      ultimately
      show ?thesis
        by meson
    next
      case False
      then obtain host where host: "host \<in> fset (element_ptr_kinds h)" and
        "|h \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types" and
        "|h \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr"
        using \<open>shadow_root_ptr \<in> fset (shadow_root_ptr_kinds h')\<close>
        using \<open>\<forall>shadow_root_ptr\<in>fset (shadow_root_ptr_kinds h). \<exists>host\<in>fset (element_ptr_kinds h).
|h \<turnstile> get_tag_name host|\<^sub>r \<in> safe_shadow_root_element_types \<and> |h \<turnstile> get_shadow_root host|\<^sub>r = Some shadow_root_ptr\<close>
        apply(simp add: shadow_root_ptr_kinds_eq_h3 shadow_root_ptr_kinds_eq_h2 shadow_root_ptr_kinds_eq_h)
        by (meson finite_set_in)
      moreover have "host \<noteq> element_ptr"
        using calculation(3) prev_shadow_root by auto
      ultimately show ?thesis
        using element_ptr_kinds_eq_h3 element_ptr_kinds_eq_h2 element_ptr_kinds_eq_h
        by (smt \<open>type_wf h'\<close> assms(2) finite_set_in local.get_shadow_root_ok returns_result_eq
            returns_result_select_result shadow_root_eq_h shadow_root_eq_h2 shadow_root_eq_h3 tag_name_eq2_h
            tag_name_eq2_h2 tag_name_eq2_h3)
    qed
  qed


  have "a_host_shadow_root_rel h = a_host_shadow_root_rel h2"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h select_result_eq[OF shadow_root_eq_h])
  have "a_host_shadow_root_rel h2 = a_host_shadow_root_rel h3"
    by(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h2 select_result_eq[OF shadow_root_eq_h2])
  have "a_host_shadow_root_rel h' = {(cast element_ptr, cast new_shadow_root_ptr)} \<union> a_host_shadow_root_rel h3"
    apply(auto simp add: a_host_shadow_root_rel_def element_ptr_kinds_eq_h3 )[1]
       apply(case_tac "element_ptr \<noteq> aa")
    using select_result_eq[OF shadow_root_eq_h3] apply (simp add: image_iff)
    using select_result_eq[OF shadow_root_eq_h3]
       apply (metis (no_types, lifting) \<open>local.a_host_shadow_root_rel h = local.a_host_shadow_root_rel h2\<close>
        \<open>local.a_host_shadow_root_rel h2 = local.a_host_shadow_root_rel h3\<close> \<open>type_wf h3\<close> host_shadow_root_rel_def
        i_get_parent_get_host_get_disconnected_document_wf.a_host_shadow_root_rel_shadow_root local.get_shadow_root_impl
        local.get_shadow_root_ok option.distinct(1) prev_shadow_root returns_result_select_result)
      apply (metis (mono_tags, lifting) \<open>\<And>ptr'. (\<And>x. element_ptr \<noteq> ptr') \<Longrightarrow>
|h3 \<turnstile> get_shadow_root ptr'|\<^sub>r = |h' \<turnstile> get_shadow_root ptr'|\<^sub>r\<close> case_prod_conv image_iff
        is_OK_returns_result_I mem_Collect_eq option.inject returns_result_eq returns_result_select_result
        shadow_root_h3)
    using element_ptr_kinds_eq_h3 local.get_shadow_root_ptr_in_heap shadow_root_h3 apply fastforce
    apply (smt Shadow_DOM.a_host_shadow_root_rel_def \<open>\<And>ptr'. (\<And>x. element_ptr \<noteq> ptr') \<Longrightarrow>
|h3 \<turnstile> get_shadow_root ptr'|\<^sub>r = |h' \<turnstile> get_shadow_root ptr'|\<^sub>r\<close> \<open>type_wf h3\<close> case_prodE case_prodI
        i_get_root_node_si_wf.a_host_shadow_root_rel_shadow_root image_iff local.get_shadow_root_impl
        local.get_shadow_root_ok mem_Collect_eq option.distinct(1) prev_shadow_root returns_result_eq
        returns_result_select_result shadow_root_eq_h shadow_root_eq_h2)
    done

  have "a_ptr_disconnected_node_rel h = a_ptr_disconnected_node_rel h2"
    apply(auto simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h)[1]
      apply (metis (no_types, lifting) \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr |\<notin>| document_ptr_kinds h\<close>
        case_prodI disconnected_nodes_eq2_h mem_Collect_eq pair_imageI)
    using \<open>h2 \<turnstile> get_disconnected_nodes (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
     apply auto[1]
    apply(case_tac "cast new_shadow_root_ptr \<noteq> aa")
     apply (simp add: disconnected_nodes_eq2_h image_iff)
    using \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr |\<notin>| document_ptr_kinds h\<close>
    apply blast
    done
  have "a_ptr_disconnected_node_rel h2 = a_ptr_disconnected_node_rel h3"
    by(simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h2 disconnected_nodes_eq2_h2)
  have "a_ptr_disconnected_node_rel h3 = a_ptr_disconnected_node_rel h'"
    by(simp add: a_ptr_disconnected_node_rel_def document_ptr_kinds_eq_h3 disconnected_nodes_eq2_h3)

  have "acyclic (parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h)"
    using \<open>heap_is_wellformed h\<close>
    by (simp add: heap_is_wellformed_def)
  have "parent_child_rel h \<union> a_host_shadow_root_rel h \<union> a_ptr_disconnected_node_rel h =
parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2"
    using \<open>local.a_host_shadow_root_rel h = local.a_host_shadow_root_rel h2\<close>
      \<open>local.a_ptr_disconnected_node_rel h = local.a_ptr_disconnected_node_rel h2\<close> \<open>parent_child_rel h = parent_child_rel h2\<close>
    by auto
  have "parent_child_rel h2 \<union> a_host_shadow_root_rel h2 \<union> a_ptr_disconnected_node_rel h2 =
parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3"
    using \<open>local.a_host_shadow_root_rel h2 = local.a_host_shadow_root_rel h3\<close>
      \<open>local.a_ptr_disconnected_node_rel h2 = local.a_ptr_disconnected_node_rel h3\<close> \<open>parent_child_rel h2 = parent_child_rel h3\<close>
    by auto
  have "parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h' =
{(cast element_ptr, cast new_shadow_root_ptr)} \<union> parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3"
    by (simp add: \<open>local.a_host_shadow_root_rel h' =
{(cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr, cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr)} \<union> local.a_host_shadow_root_rel h3\<close>
        \<open>local.a_ptr_disconnected_node_rel h3 = local.a_ptr_disconnected_node_rel h'\<close> \<open>parent_child_rel h3 = parent_child_rel h'\<close>)

  have "\<And>a b. (a, b) \<in> parent_child_rel h3 \<Longrightarrow> a \<noteq> cast new_shadow_root_ptr"
    using CD.parent_child_rel_parent_in_heap \<open>cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr |\<notin>| document_ptr_kinds h\<close>
      \<open>parent_child_rel h = parent_child_rel h2\<close> \<open>parent_child_rel h2 = parent_child_rel h3\<close> document_ptr_kinds_commutes
    by blast
  moreover
  have "\<And>a b. (a, b) \<in> a_host_shadow_root_rel h3 \<Longrightarrow> a \<noteq> cast new_shadow_root_ptr"
    using shadow_root_eq_h2
    by(auto simp add: a_host_shadow_root_rel_def)
  moreover
  have "\<And>a b. (a, b) \<in> a_ptr_disconnected_node_rel h3 \<Longrightarrow> a \<noteq> cast new_shadow_root_ptr"
    using \<open>h2 \<turnstile> get_disconnected_nodes (cast new_shadow_root_ptr) \<rightarrow>\<^sub>r []\<close>
    by(auto simp add: a_ptr_disconnected_node_rel_def disconnected_nodes_eq_h2)
  moreover
  have "cast new_shadow_root_ptr \<notin> {x. (x, cast element_ptr) \<in>
(parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)\<^sup>*}"
    by (smt Un_iff calculation(1) calculation(2) calculation(3) cast_document_ptr_not_node_ptr(2) converse_rtranclE mem_Collect_eq)
  moreover
  have "acyclic (parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3)"
    using \<open>acyclic (parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> local.a_ptr_disconnected_node_rel h)\<close>
      \<open>parent_child_rel h \<union> local.a_host_shadow_root_rel h \<union> local.a_ptr_disconnected_node_rel h =
parent_child_rel h2 \<union> local.a_host_shadow_root_rel h2 \<union> local.a_ptr_disconnected_node_rel h2\<close>
      \<open>parent_child_rel h2 \<union> local.a_host_shadow_root_rel h2 \<union> local.a_ptr_disconnected_node_rel h2 =
parent_child_rel h3 \<union> local.a_host_shadow_root_rel h3 \<union> local.a_ptr_disconnected_node_rel h3\<close> by auto
  ultimately have "acyclic (parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h')"
    by(simp add: \<open>parent_child_rel h' \<union> a_host_shadow_root_rel h' \<union> a_ptr_disconnected_node_rel h' =
{(cast element_ptr, cast new_shadow_root_ptr)} \<union>
parent_child_rel h3 \<union> a_host_shadow_root_rel h3 \<union> a_ptr_disconnected_node_rel h3\<close>)

  have "CD.a_heap_is_wellformed h'"
    apply(simp add: CD.a_heap_is_wellformed_def)
    by (simp add: \<open>local.CD.a_acyclic_heap h'\<close> \<open>local.CD.a_all_ptrs_in_heap h'\<close> \<open>local.CD.a_distinct_lists h'\<close>
        \<open>local.CD.a_owner_document_valid h'\<close>)

  show "heap_is_wellformed h' "
    using \<open>acyclic (parent_child_rel h' \<union> local.a_host_shadow_root_rel h' \<union> local.a_ptr_disconnected_node_rel h')\<close>
    by(simp add: heap_is_wellformed_def CD.heap_is_wellformed_impl \<open>local.CD.a_heap_is_wellformed h'\<close>
        \<open>local.a_all_ptrs_in_heap h'\<close> \<open>local.a_distinct_lists h'\<close> \<open>local.a_shadow_root_valid h'\<close>)
qed
end

interpretation l_attach_shadow_root_wf?: l_attach_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M known_ptr known_ptrs type_wf
  get_child_nodes get_child_nodes_locs get_disconnected_nodes get_disconnected_nodes_locs
  heap_is_wellformed parent_child_rel set_tag_name set_tag_name_locs set_disconnected_nodes
  set_disconnected_nodes_locs create_element get_shadow_root get_shadow_root_locs get_tag_name
  get_tag_name_locs heap_is_wellformed\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M get_host get_host_locs get_disconnected_document
  get_disconnected_document_locs set_val set_val_locs create_character_data DocumentClass.known_ptr
  DocumentClass.type_wf set_shadow_root set_shadow_root_locs set_mode set_mode_locs attach_shadow_root
  by(auto simp add: l_attach_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_def instances)
declare l_attach_shadow_root_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>D\<^sub>O\<^sub>M_axioms [instances]

end
