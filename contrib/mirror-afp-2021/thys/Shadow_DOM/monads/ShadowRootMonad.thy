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
    "Core_DOM.DocumentMonad"
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
  by(auto simp add: shadow_root_ptr_kinds_M_defs object_ptr_kinds_M_defs shadow_root_ptr_kinds_def)



global_interpretation l_dummy defines get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t = "l_get_M.a_get_M get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t" .
lemma get_M_is_l_get_M: "l_get_M get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t type_wf shadow_root_ptr_kinds"
  apply(simp add: get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_type_wf l_get_M_def)
  by (metis ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf ObjectClass.type_wf_defs bind_eq_None_conv
      shadow_root_ptr_kinds_commutes get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def option.simps(3))
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
  by(auto simp add: put_M_defs get_M_defs NodeMonad.get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
      put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def split: option.splits dest: get_heap_E)

lemma get_M_Mshadow_root_preserved3 [simp]:
  "cast shadow_root_ptr \<noteq> object_ptr
   \<Longrightarrow> h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  by(auto simp add: put_M_defs get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def ObjectMonad.get_M_defs
      preserved_def split: option.splits dest: get_heap_E)
lemma get_M_Mshadow_root_preserved4  [simp]:
  "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h'
   \<Longrightarrow> (\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x))
   \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast shadow_root_ptr \<noteq> object_ptr")[1]
  by(auto simp add: put_M_defs get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
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
lemma get_M_Mshadow_root_preserved10 [simp]:
  "(\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x))
    \<Longrightarrow> h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  apply(cases "cast shadow_root_ptr = object_ptr")
  by(auto simp add: put_M_defs get_M_defs ObjectMonad.get_M_defs NodeMonad.get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
      get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def bind_eq_Some_conv
      split: option.splits)

lemma new_element_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t:
  "h \<turnstile> new_element \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t ptr getter) h h'"
  by(auto simp add: new_element_def get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_character_data_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t:
  "h \<turnstile> new_character_data \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t ptr getter) h h'"
  by(auto simp add: new_character_data_def get_M_defs preserved_def
      split: prod.splits option.splits elim!: bind_returns_result_E bind_returns_heap_E)

lemma new_document_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t:
  "h \<turnstile> new_document \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t ptr getter) h h'"
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
  apply(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: if_splits)[1]
  by (metis comp_apply fmdom_notI fmdrop_lookup heap.sel object_ptr_kinds_def shadow_root_ptr_kinds_commutes)

lemma delete_shadow_root_pointers:
  assumes "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'"
  shows "object_ptr_kinds h = object_ptr_kinds h' |\<union>| {|cast shadow_root_ptr|}"
  using assms
  apply(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def split: option.splits)[1]
    apply (metis (no_types, lifting) ObjectClass.a_type_wf_def ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def
      delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_pointer_ptr_in_heap fmlookup_drop get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def heap.sel option.sel
      shadow_root_ptr_kinds_commutes)
  using delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_pointer_ptr_in_heap apply blast
  by (metis (no_types, lifting) ObjectClass.a_type_wf_def ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def
      delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_pointer_ptr_in_heap fmlookup_drop get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def heap.sel option.sel
      shadow_root_ptr_kinds_commutes)

lemma delete_shadow_root_get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t: "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow>
ptr \<noteq> cast shadow_root_ptr \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def ObjectMonad.get_M_defs preserved_def
      split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e: "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def NodeMonad.get_M_defs ObjectMonad.get_M_defs
      preserved_def split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t: "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def ElementMonad.get_M_defs NodeMonad.get_M_defs
      ObjectMonad.get_M_defs preserved_def split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a: "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def CharacterDataMonad.get_M_defs
      NodeMonad.get_M_defs ObjectMonad.get_M_defs preserved_def split: prod.splits option.splits if_splits
      elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t: "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t ptr getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def DocumentMonad.get_M_defs ObjectMonad.get_M_defs
      preserved_def split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)
lemma delete_shadow_root_get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t: "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h' \<Longrightarrow>
shadow_root_ptr \<noteq> shadow_root_ptr' \<Longrightarrow> preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr' getter) h h'"
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def get_M_defs ObjectMonad.get_M_defs
      preserved_def split: prod.splits option.splits if_splits elim!: bind_returns_heap_E)


lemma shadow_root_put_get_1 [simp]: "shadow_root_ptr \<noteq> shadow_root_ptr' \<Longrightarrow>
h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr' getter) h h'"
  by(auto simp add: put_M_defs get_M_defs preserved_def split: option.splits dest: get_heap_E)
lemma shadow_root_put_get_2 [simp]: "(\<And>x. getter (setter (\<lambda>_. v) x) = getter x) \<Longrightarrow>
h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr' getter) h h'"
  by (cases "shadow_root_ptr = shadow_root_ptr'") (auto simp add: put_M_defs get_M_defs preserved_def
      split: option.splits dest: get_heap_E)
lemma shadow_root_put_get_3 [simp]: "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr getter) h h'"
  by(auto simp add: put_M_defs ElementMonad.get_M_defs preserved_def split: option.splits
      dest: get_heap_E)
lemma shadow_root_put_get_4 [simp]: "h \<turnstile> put_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter) h h'"
  by(auto simp add: ElementMonad.put_M_defs get_M_defs preserved_def split: option.splits
      dest: get_heap_E)
lemma shadow_root_put_get_5 [simp]: "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr getter) h h'"
  by(auto simp add: put_M_defs CharacterDataMonad.get_M_defs preserved_def split: option.splits
      dest: get_heap_E)
lemma shadow_root_put_get_6 [simp]: "h \<turnstile> put_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter) h h'"
  by(auto simp add: CharacterDataMonad.put_M_defs get_M_defs preserved_def split: option.splits
      dest: get_heap_E)
lemma shadow_root_put_get_7 [simp]: "h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr getter) h h'"
  by(auto simp add: put_M_defs DocumentMonad.get_M_defs preserved_def split: option.splits
      dest: get_heap_E)
lemma shadow_root_put_get_8 [simp]: "h \<turnstile> put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow>
preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr getter) h h'"
  by(auto simp add: DocumentMonad.put_M_defs get_M_defs preserved_def split: option.splits
      dest: get_heap_E)
lemma shadow_root_put_get_9 [simp]: "(\<And>x. getter (cast (setter (\<lambda>_. v) x)) = getter (cast x)) \<Longrightarrow>
h \<turnstile> put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr setter v \<rightarrow>\<^sub>h h' \<Longrightarrow> preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr getter) h h'"
  by (cases "cast shadow_root_ptr = object_ptr") (auto simp add: put_M_defs get_M_defs
      ObjectMonad.get_M_defs NodeMonad.get_M_defs get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def get\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def preserved_def put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
      put\<^sub>N\<^sub>o\<^sub>d\<^sub>e_def bind_eq_Some_conv split: option.splits)

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
     \<Longrightarrow> h \<turnstile> new\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M \<rightarrow>\<^sub>r new_shadow_root_ptr
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

lemma shadow_root_get_put_1 [simp]: "get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) = (if ptr = cast shadow_root_ptr
then cast obj else get shadow_root_ptr h)"
  by(auto simp add: get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def split: option.splits Option.bind_splits)

lemma shadow_root_ptr_kinds_new[simp]: "shadow_root_ptr_kinds (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h) = shadow_root_ptr_kinds h |\<union>|
(if is_shadow_root_ptr_kind ptr then {|the (cast ptr)|} else {||})"
  by(auto simp add: shadow_root_ptr_kinds_def split: option.splits)

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
  by(auto simp add: type_wf_defs elim!: DocumentMonad.type_wf_put_ptr_not_in_heap_E
      split: option.splits if_splits)

lemma type_wf_put_ptr_in_heap_E:
  assumes "type_wf (put\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t ptr obj h)"
  assumes "ptr |\<in>| object_ptr_kinds h"
  assumes "DocumentClass.type_wf h"
  assumes "is_shadow_root_ptr_kind ptr \<Longrightarrow> is_shadow_root_kind (the (get ptr h))"
  shows "type_wf h"
  using assms
  apply(auto simp add: type_wf_defs elim!: DocumentMonad.type_wf_put_ptr_in_heap_E
      split: option.splits if_splits)[1]
  by (metis (no_types, hide_lams) ObjectClass.a_type_wf_def ObjectClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf
      bind.bind_lunit finite_set_in get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def is_shadow_root_kind_def option.exhaust_sel)


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
    unfolding shadow_root_ptr_kinds_def by auto
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
    unfolding shadow_root_ptr_kinds_def by simp
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
    unfolding shadow_root_ptr_kinds_def by simp
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
    unfolding shadow_root_ptr_kinds_def by simp
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
    unfolding shadow_root_ptr_kinds_def by simp
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
    unfolding shadow_root_ptr_kinds_def by auto
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
    unfolding shadow_root_ptr_kinds_def by simp
  with assms show ?thesis
    by(auto simp add: CharacterDataMonad.put_M_defs type_wf_defs)
qed

lemma new_document_type_wf_preserved [simp]:
  assumes "h \<turnstile> new_document \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  obtain new_document_ptr where "h \<turnstile> new_document \<rightarrow>\<^sub>r new_document_ptr"
    using assms
    by (meson is_OK_returns_heap_I is_OK_returns_result_E)
  with assms have "object_ptr_kinds h' = object_ptr_kinds h |\<union>| {|cast new_document_ptr|}"
    using new_document_new_ptr by auto
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    unfolding shadow_root_ptr_kinds_def by auto
  with assms show ?thesis
    by(auto simp add: DocumentMonad.new_document_def type_wf_defs Let_def elim!: bind_returns_heap_E
        split: prod.splits)
qed

lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_doctype_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M document_ptr doctype_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "object_ptr_kinds h = object_ptr_kinds h'"
    using writes_singleton assms object_ptr_kinds_preserved unfolding all_args_def by fastforce
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    unfolding shadow_root_ptr_kinds_def by simp
  with assms show ?thesis
    by(auto simp add: DocumentMonad.put_M_defs type_wf_defs)
qed
lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_document_element_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M document_ptr document_element_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "object_ptr_kinds h = object_ptr_kinds h'"
    using writes_singleton assms object_ptr_kinds_preserved unfolding all_args_def by fastforce
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    unfolding shadow_root_ptr_kinds_def by simp
  with assms show ?thesis
    by(auto simp add: DocumentMonad.put_M_defs type_wf_defs)
qed
lemma put_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t_disconnected_nodes_type_wf_preserved [simp]:
  assumes "h \<turnstile> put_M document_ptr disconnected_nodes_update v \<rightarrow>\<^sub>h h'"
  shows "type_wf h = type_wf h'"
proof -
  have "object_ptr_kinds h = object_ptr_kinds h'"
    using writes_singleton assms object_ptr_kinds_preserved unfolding all_args_def by fastforce
  then have "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
    unfolding shadow_root_ptr_kinds_def by simp
  with assms show ?thesis
    by(auto simp add: DocumentMonad.put_M_defs type_wf_defs)
qed

lemma put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_mode_type_wf_preserved [simp]:
  "h \<turnstile> put_M shadow_root_ptr mode_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  by(auto simp add: get_M_defs is_shadow_root_kind_def type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs DocumentClass.type_wf_defs put_M_defs
      put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
      dest!: get_heap_E
      elim!: bind_returns_heap_E2
      intro!: type_wf_put_I DocumentMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I
      ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I
      split: option.splits)


lemma put_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_child_nodes_type_wf_preserved [simp]:
  "h \<turnstile> put_M shadow_root_ptr RShadowRoot.child_nodes_update v \<rightarrow>\<^sub>h h' \<Longrightarrow> type_wf h = type_wf h'"
  by(auto simp add: get_M_defs is_shadow_root_kind_def type_wf_defs ElementClass.type_wf_defs
      NodeClass.type_wf_defs ElementMonad.get_M_defs ObjectClass.type_wf_defs
      CharacterDataClass.type_wf_defs DocumentClass.type_wf_defs put_M_defs
      put\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
      dest!: get_heap_E
      elim!: bind_returns_heap_E2
      intro!: type_wf_put_I DocumentMonad.type_wf_put_I CharacterDataMonad.type_wf_put_I
      ElementMonad.type_wf_put_I NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I
      split: option.splits)


lemma shadow_root_ptr_kinds_small:
  assumes "\<And>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  shows "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
  by(simp add: shadow_root_ptr_kinds_def preserved_def object_ptr_kinds_preserved_small[OF assms])

lemma shadow_root_ptr_kinds_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow>
(\<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h')"
  shows "shadow_root_ptr_kinds h = shadow_root_ptr_kinds h'"
  using writes_small_big[OF assms]
  apply(simp add: reflp_def transp_def preserved_def shadow_root_ptr_kinds_def)
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
      intro!: type_wf_put_I DocumentMonad.type_wf_put_I ElementMonad.type_wf_put_I
      CharacterDataMonad.type_wf_put_I
      NodeMonad.type_wf_put_I ObjectMonad.type_wf_put_I
      split: if_splits)[1]
  by(auto simp add: type_wf_defs DocumentClass.type_wf_defs ElementClass.type_wf_defs
      CharacterDataClass.type_wf_defs
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
  apply(auto simp add: type_wf_defs preserved_def get_M_defs shadow_root_ptr_kinds_small[OF assms(1)]
      split: option.splits)[1]
   apply(force)
  apply(force)
  done

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

lemma type_wf_preserved:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow>
\<forall>object_ptr. preserved (get_M\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t object_ptr RObject.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow>
\<forall>node_ptr. preserved (get_M\<^sub>N\<^sub>o\<^sub>d\<^sub>e node_ptr RNode.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow>
\<forall>element_ptr. preserved (get_M\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t element_ptr RElement.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow>
\<forall>character_data_ptr. preserved (get_M\<^sub>C\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>D\<^sub>a\<^sub>t\<^sub>a character_data_ptr RCharacterData.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow>
\<forall>document_ptr. preserved (get_M\<^sub>D\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t document_ptr RDocument.nothing) h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow> h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow>
\<forall>shadow_root_ptr. preserved (get_M\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t shadow_root_ptr RShadowRoot.nothing) h h'"
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
  by (metis (no_types, lifting) DocumentClass.type_wf\<^sub>E\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t ElementClass.get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_type_wf
      ElementMonad.type_wf_drop fmember.rep_eq fmlookup_drop get\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def get\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def
      object_ptr_kinds_code5 shadow_root_ptr_kinds_commutes)

lemma delete_shadow_root_type_wf_preserved [simp]:
  assumes "h \<turnstile> delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M shadow_root_ptr \<rightarrow>\<^sub>h h'"
  assumes "type_wf h"
  shows "type_wf h'"
  using assms
  using type_wf_drop
  by(auto simp add: delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_M_def delete\<^sub>S\<^sub>h\<^sub>a\<^sub>d\<^sub>o\<^sub>w\<^sub>R\<^sub>o\<^sub>o\<^sub>t_def delete\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: if_splits)
end
