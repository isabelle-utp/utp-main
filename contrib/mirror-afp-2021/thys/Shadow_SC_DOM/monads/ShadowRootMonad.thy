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

section\<open>Shadow Root Monad\<close>
theory ShadowRootMonad
  imports
    "Core_SC_DOM.DocumentMonad"
    "../classes/ShadowRootClass"
begin


type_synonym ('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr,
    'shadow_root_ptr, 'Object, 'Node, 'Element, 'CharacterData, 'Document, 'ShadowRoot, 'result) dom_prog
  = "((_) heap, exception, 'result) prog"
register_default_tvars "('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr, 'document_ptr,
'shadow_root_ptr, 'Object, 'Node, 'Element, 'CharacterData, 'Document, 'ShadowRoot, 'result) dom_prog"



global_interpretation l_ptr_kinds_M shadow_root_ptr_kinds defines shadow_root_ptr_kinds_M = a_ptr_kinds_M .
lemmas shadow_root_ptr_kinds_M_defs = a_ptr_kinds_M_def

lemma shadow_root_ptr_kinds_M_eq:
  assumes "|h \<turnstile> object_ptr_kinds_M|\<^sub>r = |h' \<turnstile> object_ptr_kinds_M|\<^sub>r"
  shows "|h \<turnstile> shadow_root_ptr_kinds_M|\<^sub>r = |h' \<turnstile> shadow_root_ptr_kinds_M|\<^sub>r"
  using assms
  by(auto simp add: shadow_root_ptr_kinds_M_defs document_ptr_kinds_def object_ptr_kinds_M_defs
      shadow_root_ptr_kinds_def)



global_interpretation l_dummy defines get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t = "l_get_M.a_get_M get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t" .
lemma get_M_is_l_get_M: "l_get_M get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t type_wf shadow_root_ptr_kinds"
  apply(simp add: get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_type_wf l_get_M_def)
  apply(auto simp add: get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def shadow_root_ptr_kinds_def)[1]
  by (metis (no_types, lifting) DocumentMonad.l_get_M_axioms bind_eq_None_conv fset.map_comp
      l_get_M_def option.discI shadow_root_ptr_kinds_commutes shadow_root_ptr_kinds_def)
lemmas get_M_defs = get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def[unfolded l_get_M.a_get_M_def[OF get_M_is_l_get_M]]

adhoc_overloading get_M get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t

locale l_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_lemmas = l_type_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t
begin
sublocale l_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas by unfold_locales

interpretation l_get_M get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t type_wf shadow_root_ptr_kinds
  apply(unfold_locales)
   apply (simp add: get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_type_wf local.type_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t)
  by (meson ShadowRootMonad.get_M_is_l_get_M l_get_M_def)
lemmas get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ok = get_M_ok[folded get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def]
lemmas get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ptr_in_heap = get_M_ptr_in_heap[folded get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def]
end

global_interpretation l_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_lemmas type_wf by unfold_locales


global_interpretation l_put_M type_wf shadow_root_ptr_kinds get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t rewrites
  "a_get_M = get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t" defines put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t = a_put_M
   apply (simp add: get_M_is_l_get_M l_put_M_def)
  by (simp add: get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def)

lemmas put_M_defs = a_put_M_def
adhoc_overloading put_M put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t


locale l_put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_lemmas = l_type_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t
begin
sublocale l_put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_lemmas by unfold_locales

interpretation l_put_M type_wf shadow_root_ptr_kinds get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t
  apply(unfold_locales)
   apply (simp add: get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_type_wf local.type_wf\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t)
  by (meson ShadowRootMonad.get_M_is_l_get_M l_get_M_def)
lemmas put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ok = put_M_ok[folded put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def]
end

global_interpretation l_put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_lemmas type_wf by unfold_locales


lemma shadow_root_put_get [simp]: "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
  \<Longrightarrow> (\<And>x. getter (setter (\<lambda>_. v) x) = v)
  \<Longrightarrow> h' \<turnstile> get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter \<rightarrow>\<^sub>r v"
  by(auto simp add: put_M_defs get_M_defs split: option.splits)
lemma get_M_Mshadow_root_preserved1 [simp]:
  "shadow_root_ptr \<noteq> shadow_root_ptr'
    \<Longrightarrow> h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
    \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr' getter) h h'"
  by(auto simp add: put_M_defs get_M_defs preserved_def split: option.splits dest: get_heap_E)
lemma shadow_root_put_get_preserved [simp]:
  "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> (\<And>x. getter (setter (\<lambda>_. v) x) = getter x)
   \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr' getter) h h'"
  apply(cases "shadow_root_ptr = shadow_root_ptr'")
  by(auto simp add: put_M_defs get_M_defs preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mshadow_root_preserved2 [simp]:
  "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs NodeMonad.get_M_defs
      put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mshadow_root_preserved3 [simp]:
  "cast shadow_root_ptr \<noteq> document_ptr
   \<Longrightarrow> h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def DocumentMonad.get_M_defs
      preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mshadow_root_preserved4  [simp]:
  "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x))
   \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter) h h'"
  apply(cases "cast shadow_root_ptr \<noteq> document_ptr")[1]
  by(auto simp add: put_M_defs get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      DocumentMonad.get_M_defs preserved_def
      split: option.splits bind_splits dest: get_heap_E)

lemma get_M_Mshadow_root_preserved3a [simp]:
  "cast shadow_root_ptr \<noteq> object_ptr
   \<Longrightarrow> h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def ObjectMonad.get_M_defs
      preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mshadow_root_preserved4a  [simp]:
  "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x))
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast shadow_root_ptr \<noteq> object_ptr")[1]
  by(auto simp add: put_M_defs get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      ObjectMonad.get_M_defs preserved_def
      split: option.splits bind_splits dest: get_heap_E)

lemma get_M_Mshadow_root_preserved5 [simp]:
  "cast shadow_root_ptr \<noteq> object_ptr
  \<Longrightarrow> h \<turnstile> put_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr setter v \<rightarrow>\<^sub>h h'
  \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter) h h'"
  by(auto simp add: ObjectMonad.put_M_defs get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def ObjectMonad.get_M_defs
      preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mshadow_root_preserved6 [simp]:
  "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr getter) h h'"
  by(auto simp add: put_M_defs ElementMonad.get_M_defs preserved_def
      split: option.splits dest: get_heap_E)
lemma get_M_Mshadow_root_preserved7 [simp]:
  "h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter) h h'"
  by(auto simp add: ElementMonad.put_M_defs get_M_defs preserved_def
      split: option.splits dest: get_heap_E)
lemma get_M_Mshadow_root_preserved8 [simp]:
  "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
    \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr getter) h h'"
  by(auto simp add: put_M_defs CharacterDataMonad.get_M_defs preserved_def
      split: option.splits dest: get_heap_E)
lemma get_M_Mshadow_root_preserved9 [simp]:
  "h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h'
    \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter) h h'"
  by(auto simp add: CharacterDataMonad.put_M_defs get_M_defs preserved_def
      split: option.splits dest: get_heap_E)

lemma get_M_shadow_root_put_M_document_different_pointers [simp]:
  "cast shadow_root_ptr \<noteq> document_ptr
    \<Longrightarrow> h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h'
    \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter) h h'"
  by(auto simp add: DocumentMonad.put_M_defs get_M_defs DocumentMonad.get_M_defs preserved_def
      split: option.splits dest: get_heap_E)
lemma get_M_shadow_root_put_M_document [simp]:
  "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> (\<And>x. is_shadow_root_kind x \<longleftrightarrow> is_shadow_root_kind (setter (\<lambda>_. v) x))
   \<Longrightarrow> (\<And>x. getter (the (cast (((setter (\<lambda>_. v) (cast x)))))) = getter ((x)))
   \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter) h h'"
  apply(cases "cast shadow_root_ptr \<noteq> document_ptr ")
   apply(auto simp add: preserved_def is_shadow_root_kind_def DocumentMonad.put_M_defs
      get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def get_M_defs DocumentMonad.get_M_defs split: option.splits)[1]
  apply(auto simp add: preserved_def is_shadow_root_kind_def DocumentMonad.put_M_defs
      get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def get_M_defs DocumentMonad.get_M_defs split: option.splits)[1]
   apply(metis cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_inv option.sel)
  apply(metis cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_inv option.sel)
  done

lemma get_M_document_put_M_shadow_root_different_pointers [simp]:
  "document_ptr \<noteq> cast shadow_root_ptr
    \<Longrightarrow> h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
    \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs DocumentMonad.get_M_defs preserved_def
      split: option.splits dest: get_heap_E)
lemma get_M_document_put_M_shadow_root [simp]:
  "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> (\<And>x. is_shadow_root_kind x \<Longrightarrow>  getter ((cast (((setter (\<lambda>_. v) (the (cast x))))))) = getter ((x)))
   \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter) h h'"
  apply(cases "document_ptr \<noteq> cast shadow_root_ptr ")
   apply(auto simp add: preserved_def is_document_kind_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put_M_defs
      get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def DocumentMonad.get_M_defs ShadowRootMonad.get_M_defs
      split: option.splits Option.bind_splits)[1]
  apply(auto simp add: preserved_def is_document_kind_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put_M_defs
      get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def DocumentMonad.get_M_defs ShadowRootMonad.get_M_defs
      split: option.splits Option.bind_splits)[1]
  using is_shadow_root_kind\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def apply force
  by (metis cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_inv is_shadow_root_kind\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def option.distinct(1) option.sel)

lemma cast_shadow_root_child_nodes_document_disconnected_nodes [simp]:
  "RShadowRoot.child_nodes (the (cast (cast x\<lparr>disconnected_nodes := y\<rparr>))) = RShadowRoot.child_nodes x"
  apply(auto simp add: cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def RDocument.extend_def RDocument.truncate_def
      split: option.splits)[1]
  by (metis RDocument.ext_inject RDocument.surjective RObject.ext_inject RShadowRoot.ext_inject
      RShadowRoot.surjective)
lemma cast_shadow_root_child_nodes_document_doctype [simp]:
  "RShadowRoot.child_nodes (the (cast (cast x\<lparr>doctype := y\<rparr>))) = RShadowRoot.child_nodes x"
  apply(auto simp add: cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def RDocument.extend_def RDocument.truncate_def
      split: option.splits)[1]
  by (metis RDocument.ext_inject RDocument.surjective RObject.ext_inject RShadowRoot.ext_inject RShadowRoot.surjective)
lemma cast_shadow_root_child_nodes_document_document_element [simp]:
  "RShadowRoot.child_nodes (the (cast (cast x\<lparr>document_element := y\<rparr>))) = RShadowRoot.child_nodes x"
  apply(auto simp add: cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def RDocument.extend_def RDocument.truncate_def
      split: option.splits)[1]
  by (metis RDocument.ext_inject RDocument.surjective RObject.ext_inject RShadowRoot.ext_inject
      RShadowRoot.surjective)

lemma cast_shadow_root_mode_document_disconnected_nodes [simp]:
  "RShadowRoot.mode (the (cast (cast x\<lparr>disconnected_nodes := y\<rparr>))) = RShadowRoot.mode x"
  apply(auto simp add: cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def RDocument.extend_def
      RDocument.truncate_def split: option.splits)[1]
  by (metis RDocument.ext_inject RDocument.surjective RObject.ext_inject RShadowRoot.ext_inject
      RShadowRoot.surjective)
lemma cast_shadow_root_mode_document_doctype [simp]:
  "RShadowRoot.mode (the (cast (cast x\<lparr>doctype := y\<rparr>))) = RShadowRoot.mode x"
  apply(auto simp add: cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def RDocument.extend_def RDocument.truncate_def
      split: option.splits)[1]
  by (metis RDocument.ext_inject RDocument.surjective RObject.ext_inject RShadowRoot.ext_inject RShadowRoot.surjective)
lemma cast_shadow_root_mode_document_document_element [simp]:
  "RShadowRoot.mode (the (cast (cast x\<lparr>document_element := y\<rparr>))) = RShadowRoot.mode x"
  apply(auto simp add: cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def RDocument.extend_def RDocument.truncate_def
      split: option.splits)[1]
  by (metis RDocument.ext_inject RDocument.surjective RObject.ext_inject RShadowRoot.ext_inject RShadowRoot.surjective)

lemma cast_document_disconnected_nodes_shadow_root_child_nodes [simp]:
  "is_shadow_root_kind x \<Longrightarrow>
disconnected_nodes (cast (the (cast x)\<lparr>RShadowRoot.child_nodes := arg\<rparr>)) = disconnected_nodes x"
  by(auto simp add: is_shadow_root_kind_def cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      RDocument.extend_def RDocument.truncate_def split: option.splits sum.splits)
lemma cast_document_doctype_shadow_root_child_nodes [simp]:
  "is_shadow_root_kind x \<Longrightarrow> doctype (cast (the (cast x)\<lparr>RShadowRoot.child_nodes := arg\<rparr>)) = doctype x"
  by(auto simp add: is_shadow_root_kind_def cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      RDocument.extend_def RDocument.truncate_def split: option.splits sum.splits)
lemma cast_document_document_element_shadow_root_child_nodes [simp]:
  "is_shadow_root_kind x \<Longrightarrow>
document_element (cast (the (cast x)\<lparr>RShadowRoot.child_nodes := arg\<rparr>)) = document_element x"
  by(auto simp add: is_shadow_root_kind_def cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      RDocument.extend_def RDocument.truncate_def split: option.splits sum.splits)
lemma cast_document_disconnected_nodes_shadow_root_mode [simp]:
  "is_shadow_root_kind x \<Longrightarrow>
disconnected_nodes (cast (the (cast x)\<lparr>RShadowRoot.mode := arg\<rparr>)) = disconnected_nodes x"
  by(auto simp add: is_shadow_root_kind_def cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      RDocument.extend_def RDocument.truncate_def split: option.splits sum.splits)
lemma cast_document_doctype_shadow_root_mode [simp]:
  "is_shadow_root_kind x \<Longrightarrow>
doctype (cast (the (cast x)\<lparr>RShadowRoot.mode := arg\<rparr>)) = doctype x"
  by(auto simp add: is_shadow_root_kind_def cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      RDocument.extend_def RDocument.truncate_def split: option.splits sum.splits)
lemma cast_document_document_element_shadow_root_mode [simp]:
  "is_shadow_root_kind x \<Longrightarrow>
document_element (cast (the (cast x)\<lparr>RShadowRoot.mode := arg\<rparr>)) = document_element x"
  by(auto simp add: is_shadow_root_kind_def cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      RDocument.extend_def RDocument.truncate_def split: option.splits sum.splits)


lemma new_element_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t:
  "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t ptr getter) h h'"
  by(auto simp add: new_element_def get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_character_data_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t:
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t ptr getter) h h'"
  by(auto simp add: new_character_data_def get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_document_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t:
  "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr \<Longrightarrow> h \<turnstile> new_document \<rightarrow>\<^sub>h h'
    \<Longrightarrow> cast ptr \<noteq> new_document_ptr \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t ptr getter) h h'"
  by(auto simp add: new_document_def get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)


definition delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M :: "(_) shadow_root_ptr \<Rightarrow> (_, unit) dom_prog" where
  "delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr = do {
    h \<leftarrow> get_heap;
    (case delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr h of
      Some h \<Rightarrow> return_heap h |
      None \<Rightarrow> error HierarchyRequestError)
  }"
adhoc_overloading delete_M delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M

lemma delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ok [simp]:
  assumes "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  shows "h \<turnstile> ok (delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr)"
  using assms
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: prod.splits)

lemma delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_in_heap:
  assumes "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'"
  shows "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
  using assms
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: if_splits)

lemma delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_not_in_heap:
  assumes "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'"
  shows "shadow_root_ptr |\<notin>| shadow_root_ptr_kinds h'"
  using assms
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def shadow_root_ptr_kinds_def
      document_ptr_kinds_def object_ptr_kinds_def split: if_splits)

lemma delete_shadow_root_pointers:
  assumes "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h' |\<union>| {|cast shadow_root_ptr|}"
  using assms
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def shadow_root_ptr_kinds_def
      document_ptr_kinds_def object_ptr_kinds_def split: if_splits)

lemma delete_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t:
  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> ptr \<noteq> cast shadow_root_ptr \<Longrightarrow>
preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def ObjectMonad.get_M_defs preserved_def
      split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e:
  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def NodeMonad.get_M_defs ObjectMonad.get_M_defs
      preserved_def
      split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t:
  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def ElementMonad.get_M_defs NodeMonad.get_M_defs
      ObjectMonad.get_M_defs preserved_def
      split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a:
  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def CharacterDataMonad.get_M_defs NodeMonad.get_M_defs
      ObjectMonad.get_M_defs preserved_def
      split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t:
  "cast shadow_root_ptr \<noteq> ptr \<Longrightarrow> h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def DocumentMonad.get_M_defs ObjectMonad.get_M_defs
      preserved_def
      split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t:
  "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow> shadow_root_ptr \<noteq> shadow_root_ptr' \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr' getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def get_M_defs ObjectMonad.get_M_defs preserved_def
      split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)



subsection \<open>new\_M\<close>

definition new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M :: "(_, (_) shadow_root_ptr) dom_prog"
  where
    "new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M = do {
      h \<leftarrow> get_heap;
      (new_ptr, h') \<leftarrow> return (new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t h);
      return_heap h';
      return new_ptr
    }"

lemma new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ok [simp]:
  "h \<turnstile> ok new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M"
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def split: prod.splits)

lemma new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_in_heap:
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "new_shadow_root_ptr |\<in>| shadow_root_ptr_kinds h'"
  using assms
  unfolding new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def Let_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ptr_in_heap is_OK_returns_result_I
      elim!: bind_returns_result_E bind_returns_heap_E)

lemma new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_ptr_not_in_heap:
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "new_shadow_root_ptr |\<notin>| shadow_root_ptr_kinds h"
  using assms new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ptr_not_in_heap
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def split: prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_new_ptr:
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'"
    and "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_shadow_root_ptr|}"
  using assms new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_new_ptr
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def split: prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_is_shadow_root_ptr:
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "is_shadow_root_ptr new_shadow_root_ptr"
  using assms new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_is_shadow_root_ptr
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def elim!: bind_returns_result_E split: prod.splits)

lemma new_shadow_root_mode:
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "h' \<turnstile> get_M new_shadow_root_ptr mode \<rightarrow>\<^sub>r Open"
  using assms
  by(auto simp add: get_M_defs new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def Let_def
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_shadow_root_children:
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "h' \<turnstile> get_M new_shadow_root_ptr child_nodes \<rightarrow>\<^sub>r []"
  using assms
  by(auto simp add: get_M_defs new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def Let_def
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_shadow_root_disconnected_nodes:
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "h' \<turnstile> get_M (cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r new_shadow_root_ptr) disconnected_nodes \<rightarrow>\<^sub>r []"
  using assms
  by(auto simp add: DocumentMonad.get_M_defs put_M_defs put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def Let_def
      cast\<^sub>s\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>_\<^sub>r\<^sub>o\<^sub>o\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def RDocument.extend_def RDocument.truncate_def
      split: option.splits prod.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
    \<Longrightarrow> ptr \<noteq> cast new_shadow_root_ptr \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def ObjectMonad.get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_shadow_root_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
    \<Longrightarrow> preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr getter) h h'"
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def NodeMonad.get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
     \<Longrightarrow> preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def ElementMonad.get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_shadow_root_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
    \<Longrightarrow> preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr getter) h h'"
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def CharacterDataMonad.get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
     \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> ptr \<noteq> cast new_shadow_root_ptr
     \<Longrightarrow> preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def DocumentMonad.get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)
lemma new_shadow_root_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t:
  "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h'
     \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr \<Longrightarrow> ptr \<noteq> new_shadow_root_ptr
     \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t ptr getter) h h'"
  by(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)


subsection \<open>modified heaps\<close>

lemma shadow_root_get_put_1 [simp]: "get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) =
(if ptr = cast shadow_root_ptr then cast obj else get shadow_root_ptr h)"
  by(auto simp add: get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def split: option.splits Option.bind_splits)

lemma shadow_root_ptr_kinds_new [simp]: "shadow_root_ptr_kinds (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) =
shadow_root_ptr_kinds h |\<union>| (if is_shadow_root_ptr_kind ptr then {|the (cast ptr)|} else {||})"
  by(auto simp add: shadow_root_ptr_kinds_def is_document_ptr_kind_def split: option.splits)

lemma type_wf_put_I:
  assumes "type_wf h"
  assumes "DocumentClass.type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "is_shadow_root_ptr_kind ptr \<Longrightarrow> is_shadow_root_kind obj"
  shows "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  using assms
  by(auto simp add: type_wf_defs is_shadow_root_kind_def split: option.splits)

lemma type_wf_put_ptr_not_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<notin>| object_ptr_kinds h"
  shows "type_wf h"
  using assms
  by (metis (no_types, lifting) DocumentMonad.type_wf_put_ptr_not_in_heap_E ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf
      ObjectMonad.type_wf_put_ptr_not_in_heap_E ShadowRootClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ShadowRootClass.type_wf_defs
      document_ptr_kinds_commutes get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def get_document_ptr_simp get_object_ptr_simp2 notin_fset
      shadow_root_ptr_kinds_commutes)


lemma type_wf_put_ptr_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<in>| object_ptr_kinds h"
  assumes "DocumentClass.type_wf h"
  assumes "is_shadow_root_ptr_kind ptr \<Longrightarrow> is_shadow_root_kind (the (get ptr h))"
  shows "type_wf h"
  using assms
  apply(auto simp add: type_wf_defs elim!: DocumentMonad.type_wf_put_ptr_in_heap_E
      split: option.splits if_splits)[1]
  by (metis (no_types, lifting) DocumentClass.l_get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas_axioms assms(2) bind.bind_lunit
      cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_inv cast\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>2\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_inv finite_set_in get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def l_get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_lemmas.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf option.collapse)


subsection \<open>type\_wf\<close>

lemma new_element_type_wf_preserved [simp]:
  assumes "h \<turnstile> new_element \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  obtain new_element_ptr where "h \<turnstile> new_element \<rightarrow>\<^sub>r new_element_ptr"
    using assms
    by (meson is_OK_returns_heap_I is_OK_returns_result_E)
  with assms have "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_element_ptr|}"
    using new_element_new_ptr by auto
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)

  with assms show ?thesis
    by(auto simp add: ElementMonad.new_element_def type_wf_defs Let_def elim!: bind_returns_heap_E
        split: prod.splits)
qed

lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_tag_name_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M element_ptr tag_name_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "object_ptr_kinds h = object_ptr_kinds h'"
    using writes_singleton assms object_ptr_kinds_preserved unfolding all_args_def by fastforce
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  with assms show ?thesis
    by(auto simp add: ElementMonad.put_M_defs type_wf_defs)
qed
lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_child_nodes_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M element_ptr RElement.child_nodes_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "object_ptr_kinds h = object_ptr_kinds h'"
    using writes_singleton assms object_ptr_kinds_preserved unfolding all_args_def by fastforce
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  with assms show ?thesis
    by(auto simp add: ElementMonad.put_M_defs type_wf_defs)
qed
lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_attrs_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M element_ptr attrs_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "object_ptr_kinds h = object_ptr_kinds h'"
    using writes_singleton assms object_ptr_kinds_preserved unfolding all_args_def by fastforce
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  with assms show ?thesis
    by(auto simp add: ElementMonad.put_M_defs type_wf_defs)
qed
lemma put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t_shadow_root_opt_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M element_ptr shadow_root_opt_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "object_ptr_kinds h = object_ptr_kinds h'"
    using writes_singleton assms object_ptr_kinds_preserved unfolding all_args_def by fastforce
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  with assms show ?thesis
    by(auto simp add: ElementMonad.put_M_defs type_wf_defs)
qed

lemma new_character_data_type_wf_preserved [simp]:
  assumes "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  obtain new_character_data_ptr where "h \<turnstile> new_character_data \<rightarrow>\<^sub>r new_character_data_ptr"
    using assms
    by (meson is_OK_returns_heap_I is_OK_returns_result_E)
  with assms have "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_character_data_ptr|}"
    using new_character_data_new_ptr by auto
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  with assms show ?thesis
    by(auto simp add: CharacterDataMonad.new_character_data_def type_wf_defs Let_def
        elim!: bind_returns_heap_E split: prod.splits)
qed
lemma put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a_val_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M character_data_ptr val_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "object_ptr_kinds h = object_ptr_kinds h'"
    using writes_singleton assms object_ptr_kinds_preserved unfolding all_args_def by fastforce
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def)
  with assms show ?thesis
    by(auto simp add: CharacterDataMonad.put_M_defs type_wf_defs)
qed

lemma new_document_type_wf_preserved [simp]:
  "h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: new_document_def new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def Let_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a  type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_ptr_kind_none
      elim!: bind_returns_heap_E type_wf_put_ptr_not_in_heap_E
      intro!: type_wf_put_I DocumentMonad.type_wf_put_I ElementMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I
      split: if_splits)[1]
     apply(auto simp add: type_wf_defs ElementClass.type_wf_defs CharacterDataClass.type_wf_defs
      NodeClass.type_wf_defs ObjectClass.type_wf_defs is_document_kind_def
      split: option.splits)[1]
    apply (metis fMax_finsert fimage_is_fempty new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def new\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_ptr_not_in_heap)
   apply(auto simp add: type_wf_defs ElementClass.type_wf_defs CharacterDataClass.type_wf_defs
      NodeClass.type_wf_defs ObjectClass.type_wf_defs is_document_kind_def
      split: option.splits)[1]
  apply(metis Suc_n_not_le_n document_ptr.sel(1) document_ptrs_def fMax_ge ffmember_filter fimage_eqI is_document_ptr_ref)
  done

lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_doctype_type_wf_preserved [simp]:
  "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr doctype_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: DocumentMonad.put_M_defs put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def dest!: get_heap_E
      elim!: bind_returns_heap_E2
      intro!: type_wf_put_I DocumentMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I
      ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
           apply(auto simp add: is_document_kind_def type_wf_defs DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
          apply(auto simp add: is_document_kind_def type_wf_defs DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
         apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
        apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
       apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
      apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
     apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
    apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
proof -
  fix x
  assume 0: "h \<turnstile> get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr id \<rightarrow>\<^sub>r x"
    and 1: "h' = put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>doctype := v\<rparr>)) h"
    and 2: "ShadowRootClass.type_wf h"
    and 3: "is_shadow_root_ptr_kind document_ptr"
  obtain shadow_root_ptr where shadow_root_ptr: "document_ptr = cast shadow_root_ptr" and
    "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
    by (metis "0" "3" DocumentMonad.get_M_ptr_in_heap is_OK_returns_result_I
        is_shadow_root_ptr_kind_obtains shadow_root_ptr_kinds_commutes)

  then have "is_shadow_root_kind x"
    using 0 2
    apply(auto simp add: is_document_kind_def type_wf_defs is_shadow_root_kind_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
        split: option.splits Option.bind_splits)[1]
    by (metis (no_types, lifting) DocumentMonad.get_M_defs finite_set_in get_heap_returns_result
        id_apply option.simps(5) return_returns_result)


  then show "\<exists>y. cast y = x\<lparr>doctype := v\<rparr>"
    using cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_none is_shadow_root_kind_doctype is_shadow_root_kind\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def by blast
next
  fix x
  assume 0: "h \<turnstile> get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr id \<rightarrow>\<^sub>r x"
    and 1: "h' = put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>doctype := v\<rparr>)) h"
    and 2: "ShadowRootClass.type_wf (put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>doctype := v\<rparr>)) h)"
  have 3: "\<And>document_ptr'. document_ptr' \<noteq> document_ptr \<Longrightarrow> get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr') h = get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr') h'"
    by (simp add: "1")
  have "document_ptr |\<in>| document_ptr_kinds h"
    by (meson "0" DocumentMonad.get_M_ptr_in_heap is_OK_returns_result_I)
  show "ShadowRootClass.type_wf h"
  proof (cases "is_shadow_root_ptr_kind document_ptr")
    case True
    then obtain shadow_root_ptr where shadow_root_ptr: "document_ptr = cast shadow_root_ptr"
      using is_shadow_root_ptr_kind_obtains by blast
    then
    have "is_shadow_root_kind (x\<lparr>doctype := v\<rparr>)"
      using 2 True
      by(simp add: type_wf_defs is_shadow_root_kind\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def split: if_splits option.splits)
    then
    have "is_shadow_root_kind x"
      using is_shadow_root_kind_doctype by blast
    then
    have "is_shadow_root_kind (the (get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr) h))"
      using 0
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def is_shadow_root_kind_def
          split: option.splits Option.bind_splits)
    show ?thesis
      using 0 2 \<open>is_shadow_root_kind x\<close> shadow_root_ptr
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def is_shadow_root_kind_def
          is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
          NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
          CharacterDataClass.type_wf_defs split: option.splits if_splits)
  next
    case False
    then show ?thesis
      using 0 1 2
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def is_shadow_root_kind_def
          is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
          NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
          CharacterDataClass.type_wf_defs split: option.splits if_splits)
  qed
qed

lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_document_element_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr document_element_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
  using assms
  apply(auto simp add: DocumentMonad.put_M_defs put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def dest!: get_heap_E
      elim!: bind_returns_heap_E2
      intro!: type_wf_put_I DocumentMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I
      ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
           apply(auto simp add: is_document_kind_def type_wf_defs DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
          apply(auto simp add: is_document_kind_def type_wf_defs DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
         apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
        apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
       apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
      apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
     apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
    apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
proof -
  fix x
  assume 0: "h \<turnstile> get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr id \<rightarrow>\<^sub>r x"
    and 1: "h' = put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>document_element := v\<rparr>)) h"
    and 2: "ShadowRootClass.type_wf h"
    and 3: "is_shadow_root_ptr_kind document_ptr"
  obtain shadow_root_ptr where shadow_root_ptr: "document_ptr = cast shadow_root_ptr" and
    "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
    by (metis "0" "3" DocumentMonad.get_M_ptr_in_heap is_OK_returns_result_I
        is_shadow_root_ptr_kind_obtains shadow_root_ptr_kinds_commutes)

  then have "is_shadow_root_kind x"
    using 0 2
    apply(auto simp add: is_document_kind_def type_wf_defs is_shadow_root_kind_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
        split: option.splits Option.bind_splits)[1]
    by (metis (no_types, lifting) DocumentMonad.get_M_defs finite_set_in get_heap_returns_result id_def
        option.simps(5) return_returns_result)

  then show "\<exists>y. cast y = x\<lparr>document_element := v\<rparr>"
    using cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_none is_shadow_root_kind_document_element is_shadow_root_kind\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
    by blast
next
  fix x
  assume 0: "h \<turnstile> get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr id \<rightarrow>\<^sub>r x"
    and 1: "h' = put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>document_element := v\<rparr>)) h"
    and 2: "ShadowRootClass.type_wf (put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>document_element := v\<rparr>)) h)"
  have 3: "\<And>document_ptr'. document_ptr' \<noteq> document_ptr \<Longrightarrow> get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr') h = get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr') h'"
    by (simp add: "1")
  have "document_ptr |\<in>| document_ptr_kinds h"
    by (meson "0" DocumentMonad.get_M_ptr_in_heap is_OK_returns_result_I)
  show "ShadowRootClass.type_wf h"
  proof (cases "is_shadow_root_ptr_kind document_ptr")
    case True
    then obtain shadow_root_ptr where shadow_root_ptr: "document_ptr = cast shadow_root_ptr"
      using is_shadow_root_ptr_kind_obtains by blast
    then
    have "is_shadow_root_kind (x\<lparr>document_element := v\<rparr>)"
      using 2 True
      by(simp add: type_wf_defs is_shadow_root_kind\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def split: if_splits option.splits)
    then
    have "is_shadow_root_kind x"
      using is_shadow_root_kind_document_element by blast
    then
    have "is_shadow_root_kind (the (get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr) h))"
      using 0
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def is_shadow_root_kind_def
          split: option.splits Option.bind_splits)
    show ?thesis
      using 0 2 \<open>is_shadow_root_kind x\<close> shadow_root_ptr
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def is_shadow_root_kind_def
          is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
          NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
          CharacterDataClass.type_wf_defs split: option.splits if_splits)
  next
    case False
    then show ?thesis
      using 0 1 2
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def is_shadow_root_kind_def
          is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
          NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
          CharacterDataClass.type_wf_defs split: option.splits if_splits)
  qed
qed

lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_disconnected_nodes_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr disconnected_nodes_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"

  using assms
  apply(auto simp add: DocumentMonad.put_M_defs put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def dest!: get_heap_E
      elim!: bind_returns_heap_E2
      intro!: type_wf_put_I DocumentMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I
      ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I)[1]
           apply(auto simp add: is_document_kind_def type_wf_defs DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
          apply(auto simp add: is_document_kind_def type_wf_defs DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
         apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
        apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
       apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
      apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
     apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
    apply(auto simp add: is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs split: option.splits)[1]
proof -
  fix x
  assume 0: "h \<turnstile> get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr id \<rightarrow>\<^sub>r x"
    and 1: "h' = put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>disconnected_nodes := v\<rparr>)) h"
    and 2: "ShadowRootClass.type_wf h"
    and 3: "is_shadow_root_ptr_kind document_ptr"
  obtain shadow_root_ptr where shadow_root_ptr: "document_ptr = cast shadow_root_ptr" and
    "shadow_root_ptr |\<in>| shadow_root_ptr_kinds h"
    by (metis "0" "3" DocumentMonad.get_M_ptr_in_heap is_OK_returns_result_I is_shadow_root_ptr_kind_obtains
        shadow_root_ptr_kinds_commutes)

  then have "is_shadow_root_kind x"
    using 0 2
    apply(auto simp add: is_document_kind_def type_wf_defs is_shadow_root_kind_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
        split: option.splits Option.bind_splits)[1]
    by (metis (no_types, lifting) DocumentMonad.get_M_defs finite_set_in get_heap_returns_result
        id_def option.simps(5) return_returns_result)

  then show "\<exists>y. cast y = x\<lparr>disconnected_nodes := v\<rparr>"
    using cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_none is_shadow_root_kind_disconnected_nodes is_shadow_root_kind\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
    by blast
next
  fix x
  assume 0: "h \<turnstile> get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr id \<rightarrow>\<^sub>r x"
    and 1: "h' = put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>disconnected_nodes := v\<rparr>)) h"
    and 2: "ShadowRootClass.type_wf (put (cast document_ptr) (cast\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>2\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (x\<lparr>disconnected_nodes := v\<rparr>)) h)"
  have 3: "\<And>document_ptr'. document_ptr' \<noteq> document_ptr \<Longrightarrow> get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr') h = get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr') h'"
    by (simp add: "1")
  have "document_ptr |\<in>| document_ptr_kinds h"
    by (meson "0" DocumentMonad.get_M_ptr_in_heap is_OK_returns_result_I)
  show "ShadowRootClass.type_wf h"
  proof (cases "is_shadow_root_ptr_kind document_ptr")
    case True
    then obtain shadow_root_ptr where shadow_root_ptr: "document_ptr = cast shadow_root_ptr"
      using is_shadow_root_ptr_kind_obtains by blast
    then
    have "is_shadow_root_kind (x\<lparr>disconnected_nodes := v\<rparr>)"
      using 2 True
      by(simp add: type_wf_defs is_shadow_root_kind\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def split: if_splits option.splits)
    then
    have "is_shadow_root_kind x"
      using is_shadow_root_kind_disconnected_nodes by blast
    then
    have "is_shadow_root_kind (the (get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (cast document_ptr) h))"
      using 0
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def is_shadow_root_kind_def
          split: option.splits Option.bind_splits)
    show ?thesis
      using 0 2 \<open>is_shadow_root_kind x\<close> shadow_root_ptr
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def is_shadow_root_kind_def
          is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
          NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
          CharacterDataClass.type_wf_defs split: option.splits if_splits)
  next
    case False
    then show ?thesis
      using 0 1 2
      by(auto simp add: DocumentMonad.a_get_M_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def is_shadow_root_kind_def
          is_document_kind_def type_wf_defs  DocumentClass.type_wf_defs ElementClass.type_wf_defs
          NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
          CharacterDataClass.type_wf_defs split: option.splits if_splits)
  qed
qed

lemma put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_mode_type_wf_preserved [simp]:
  "h \<turnstile> put_M shadow_root_ptr mode_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  by(auto simp add: get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def DocumentMonad.get_M_defs put_M_defs put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
      put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def dest!: get_heap_E  elim!: bind_returns_heap_E2 intro!: type_wf_put_I DocumentMonad.type_wf_put_I
      CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I
      simp add: is_shadow_root_kind_def is_document_kind_def type_wf_defs  ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs CharacterDataClass.type_wf_defs DocumentClass.type_wf_defs split: option.splits)[1]

lemma put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_child_nodes_type_wf_preserved [simp]:
  "h \<turnstile> put_M shadow_root_ptr RShadowRoot.child_nodes_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  by(auto simp add: get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def DocumentMonad.get_M_defs put_M_defs put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
      put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def dest!: get_heap_E  elim!: bind_returns_heap_E2 intro!: type_wf_put_I
      DocumentMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I ElementMonad.type_wf_put_I
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I
      simp add: is_shadow_root_kind_def is_document_kind_def type_wf_defs  ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs CharacterDataClass.type_wf_defs
      DocumentClass.type_wf_defs split: option.splits)[1]

lemma shadow_root_ptr_kinds_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  shows "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
  by(auto simp add: shadow_root_ptr_kinds_def document_ptr_kinds_def preserved_def
      object_ptr_kinds_preserved_small[OF assms])

lemma shadow_root_ptr_kinds_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h')"
  shows "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
  using writes_small_big[OF assms]
  apply(simp add: reflp_def transp_def preserved_def shadow_root_ptr_kinds_def document_ptr_kinds_def)
  by (metis assms object_ptr_kinds_preserved)


lemma new_shadow_root_known_ptr:
  assumes "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr"
  shows "known_ptr (cast new_shadow_root_ptr)"
  using assms
  apply(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def Let_def a_known_ptr_def
      elim!: bind_returns_result_E2 split: prod.splits)[1]
  using assms new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_is_shadow_root_ptr by blast


lemma new_shadow_root_type_wf_preserved [simp]: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  apply(auto simp add: new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def Let_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      ShadowRootClass.type_wf\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t ShadowRootClass.type_wf\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a  ShadowRootClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t
      ShadowRootClass.type_wf\<^sub>N\<^sub>o\<^sub>d\<^sub>e ShadowRootClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t
      is_node_ptr_kind_none new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_ptr_not_in_heap
      elim!: bind_returns_heap_E type_wf_put_ptr_not_in_heap_E
      intro!: type_wf_put_I DocumentMonad.type_wf_put_I ElementMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I
      split: if_splits)[1]
  by(auto simp add: type_wf_defs DocumentClass.type_wf_defs ElementClass.type_wf_defs CharacterDataClass.type_wf_defs
      NodeClass.type_wf_defs ObjectClass.type_wf_defs is_shadow_root_kind_def is_document_kind_def
      split: option.splits)[1]


locale l_new_shadow_root = l_type_wf +
  assumes new_shadow_root_types_preserved: "h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"

lemma new_shadow_root_is_l_new_shadow_root  [instances]: "l_new_shadow_root type_wf"
  using l_new_shadow_root.intro new_shadow_root_type_wf_preserved
  by blast

lemma type_wf_preserved_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  assumes "\<And>element_ptr. preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr RElement.nothing) h h'"
  assumes "\<And>character_data_ptr. preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr RCharacterData.nothing) h h'"
  assumes "\<And>document_ptr. preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr RDocument.nothing) h h'"
  assumes "\<And>shadow_root_ptr. preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr RShadowRoot.nothing) h h'"
  shows "type_wf h = type_wf h'"
  using type_wf_preserved_small[OF assms(1) assms(2) assms(3) assms(4) assms(5)]
    allI[OF assms(6), of id, simplified] shadow_root_ptr_kinds_small[OF assms(1)]
  apply(auto simp add: type_wf_defs )[1]
   apply(auto simp add: preserved_def get_M_defs shadow_root_ptr_kinds_small[OF assms(1)]
      split: option.splits)[1]
   apply(force)
  apply(auto simp add: preserved_def get_M_defs shadow_root_ptr_kinds_small[OF assms(1)]
      split: option.splits)[1]
  apply(force)
  done

lemma type_wf_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> \<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> \<forall>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> \<forall>element_ptr. preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr RElement.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> \<forall>character_data_ptr. preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr RCharacterData.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> \<forall>document_ptr. preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr RDocument.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> \<forall>shadow_root_ptr. preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr RShadowRoot.nothing) h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
    using assms type_wf_preserved_small by fast
  with assms(1) assms(2) show ?thesis
    apply(rule writes_small_big)
    by(auto simp add: reflp_def transp_def)
qed

lemma type_wf_drop: "type_wf h \<Longrightarrow> type_wf (Heap (fmdrop ptr (the_heap h)))"
  apply(auto simp add: type_wf_defs)[1]
  using type_wf_drop
   apply blast
  by (metis (no_types, lifting) DocumentClass.type_wf\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t DocumentMonad.type_wf_drop
      ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf document_ptr_kinds_commutes finite_set_in fmlookup_drop get\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_def
      get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def heap.sel shadow_root_ptr_kinds_commutes)

lemma delete_shadow_root_type_wf_preserved [simp]:
  assumes "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'"
  assumes "type_wf h"
  shows "type_wf h'"
  using assms
  using type_wf_drop
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: if_splits)



lemma new_element_is_l_new_element [instances]:
  "l_new_element type_wf"
  using l_new_element.intro new_element_type_wf_preserved
  by blast

lemma new_character_data_is_l_new_character_data [instances]:
  "l_new_character_data type_wf"
  using l_new_character_data.intro new_character_data_type_wf_preserved
  by blast

lemma new_document_is_l_new_document [instances]:
  "l_new_document type_wf"
  using l_new_document.intro new_document_type_wf_preserved
  by blast
end
