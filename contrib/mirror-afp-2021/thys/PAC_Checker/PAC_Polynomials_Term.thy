(*
  File:         PAC_Polynomials_Term.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Polynomials_Term
  imports PAC_Polynomials
    Refine_Imperative_HOL.IICF
begin


section \<open>Terms\<close>

text \<open>We define some helper functions.\<close>

subsection \<open>Ordering\<close>

(*Taken from WB_More_Refinement*)
lemma fref_to_Down_curry_left:
  fixes f:: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c nres\<close> and
    A::\<open>(('a \<times> 'b) \<times> 'd) set\<close>
  shows
    \<open>(uncurry f, g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
      (\<And>a b x'. P x' \<Longrightarrow> ((a, b), x') \<in> A \<Longrightarrow> f a b \<le> \<Down> B (g x'))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

lemma fref_to_Down_curry_right:
  fixes g :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c nres\<close> and f :: \<open>'d \<Rightarrow> _ nres\<close> and
    A::\<open>('d \<times> ('a \<times> 'b)) set\<close>
  shows
    \<open>(f, uncurry g) \<in> [P]\<^sub>f A \<rightarrow> \<langle>B\<rangle>nres_rel \<Longrightarrow>
      (\<And>a b x'. P (a,b) \<Longrightarrow> (x', (a, b)) \<in> A \<Longrightarrow> f x' \<le> \<Down> B (g a b))\<close>
  unfolding fref_def uncurry_def nres_rel_def
  by auto

type_synonym term_poly_list = \<open>string list\<close>
type_synonym llist_polynomial = \<open>(term_poly_list \<times> int) list\<close>


text \<open>We instantiate the characters with typeclass linorder to be able to talk abourt sorted and
  so on.\<close>

definition less_eq_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close> where
  \<open>less_eq_char c d = (((of_char c) :: nat) \<le> of_char d)\<close>

definition less_char :: \<open>char \<Rightarrow> char \<Rightarrow> bool\<close> where
  \<open>less_char c d = (((of_char c) :: nat) < of_char d)\<close>

global_interpretation char: linorder less_eq_char less_char
  using linorder_char
  unfolding linorder_class_def class.linorder_def
    less_eq_char_def[symmetric] less_char_def[symmetric]
    class.order_def order_class_def
    class.preorder_def preorder_class_def
    ord_class_def
  apply auto
  done

abbreviation less_than_char :: \<open>(char \<times> char) set\<close> where
  \<open>less_than_char \<equiv> p2rel less_char\<close>

lemma less_than_char_def:
  \<open>(x,y) \<in> less_than_char \<longleftrightarrow> less_char x y\<close>
  by (auto simp: p2rel_def)

lemma trans_less_than_char[simp]:
    \<open>trans less_than_char\<close> and
  irrefl_less_than_char:
    \<open>irrefl less_than_char\<close> and
  antisym_less_than_char:
    \<open>antisym less_than_char\<close>
  by (auto simp: less_than_char_def trans_def irrefl_def antisym_def)


subsection \<open>Polynomials\<close>

definition var_order_rel :: \<open>(string \<times> string) set\<close> where
  \<open>var_order_rel \<equiv> lexord less_than_char\<close>

abbreviation var_order :: \<open>string \<Rightarrow> string \<Rightarrow> bool\<close> where
  \<open>var_order \<equiv> rel2p var_order_rel\<close>

abbreviation term_order_rel :: \<open>(term_poly_list \<times> term_poly_list) set\<close> where
  \<open>term_order_rel \<equiv> lexord var_order_rel\<close>

abbreviation term_order :: \<open>term_poly_list \<Rightarrow> term_poly_list \<Rightarrow> bool\<close> where
  \<open>term_order \<equiv> rel2p term_order_rel\<close>

definition term_poly_list_rel :: \<open>(term_poly_list \<times> term_poly) set\<close> where
  \<open>term_poly_list_rel = {(xs, ys).
     ys = mset xs \<and>
     distinct xs \<and>
     sorted_wrt (rel2p var_order_rel) xs}\<close>

definition unsorted_term_poly_list_rel :: \<open>(term_poly_list \<times> term_poly) set\<close> where
  \<open>unsorted_term_poly_list_rel = {(xs, ys).
     ys = mset xs \<and> distinct xs}\<close>

definition poly_list_rel :: \<open>_ \<Rightarrow> (('a \<times> int) list \<times> mset_polynomial) set\<close> where
  \<open>poly_list_rel R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<and>
     0 \<notin># snd `# ys}\<close>

definition sorted_poly_list_rel_wrt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool)
     \<Rightarrow> ('a \<times> string multiset) set \<Rightarrow> (('a \<times> int) list \<times> mset_polynomial) set\<close> where
  \<open>sorted_poly_list_rel_wrt S R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<and>
     sorted_wrt S (map fst xs) \<and>
     distinct (map fst xs) \<and>
     0 \<notin># snd `# ys}\<close>

abbreviation sorted_poly_list_rel where
  \<open>sorted_poly_list_rel R \<equiv> sorted_poly_list_rel_wrt R term_poly_list_rel\<close>

abbreviation sorted_poly_rel where
  \<open>sorted_poly_rel \<equiv> sorted_poly_list_rel term_order\<close>


definition sorted_repeat_poly_list_rel_wrt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool)
     \<Rightarrow> ('a \<times> string multiset) set \<Rightarrow> (('a \<times> int) list \<times> mset_polynomial) set\<close> where
  \<open>sorted_repeat_poly_list_rel_wrt S R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<and>
     sorted_wrt S (map fst xs) \<and>
     0 \<notin># snd `# ys}\<close>

abbreviation sorted_repeat_poly_list_rel where
  \<open>sorted_repeat_poly_list_rel R \<equiv> sorted_repeat_poly_list_rel_wrt R term_poly_list_rel\<close>

abbreviation sorted_repeat_poly_rel where
  \<open>sorted_repeat_poly_rel \<equiv> sorted_repeat_poly_list_rel (rel2p (Id \<union> lexord var_order_rel))\<close>


abbreviation unsorted_poly_rel where
  \<open>unsorted_poly_rel \<equiv> poly_list_rel term_poly_list_rel\<close>

lemma sorted_poly_list_rel_empty_l[simp]:
  \<open>([], s') \<in> sorted_poly_list_rel_wrt S T \<longleftrightarrow> s' = {#}\<close>
  by (cases s')
    (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def)


definition fully_unsorted_poly_list_rel :: \<open>_ \<Rightarrow> (('a \<times> int) list \<times> mset_polynomial) set\<close> where
  \<open>fully_unsorted_poly_list_rel R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel}\<close>

abbreviation fully_unsorted_poly_rel where
  \<open>fully_unsorted_poly_rel \<equiv> fully_unsorted_poly_list_rel unsorted_term_poly_list_rel\<close>


lemma fully_unsorted_poly_list_rel_empty_iff[simp]:
  \<open>(p, {#}) \<in> fully_unsorted_poly_list_rel R \<longleftrightarrow> p = []\<close>
  \<open>([], p') \<in> fully_unsorted_poly_list_rel R \<longleftrightarrow> p' = {#}\<close>
  by (auto simp: fully_unsorted_poly_list_rel_def list_mset_rel_def br_def)

definition poly_list_rel_with0 :: \<open>_ \<Rightarrow> (('a \<times> int) list \<times> mset_polynomial) set\<close> where
  \<open>poly_list_rel_with0 R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel}\<close>

abbreviation unsorted_poly_rel_with0 where
  \<open>unsorted_poly_rel_with0 \<equiv> fully_unsorted_poly_list_rel term_poly_list_rel\<close>

lemma poly_list_rel_with0_empty_iff[simp]:
  \<open>(p, {#}) \<in> poly_list_rel_with0 R \<longleftrightarrow> p = []\<close>
  \<open>([], p') \<in> poly_list_rel_with0 R \<longleftrightarrow> p' = {#}\<close>
  by (auto simp: poly_list_rel_with0_def list_mset_rel_def br_def)


definition sorted_repeat_poly_list_rel_with0_wrt :: \<open>('a \<Rightarrow> 'a \<Rightarrow> bool)
     \<Rightarrow> ('a \<times> string multiset) set \<Rightarrow> (('a \<times> int) list \<times> mset_polynomial) set\<close> where
  \<open>sorted_repeat_poly_list_rel_with0_wrt S R = {(xs, ys).
     (xs, ys) \<in> \<langle>R \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel \<and>
     sorted_wrt S (map fst xs)}\<close>

abbreviation sorted_repeat_poly_list_rel_with0 where
  \<open>sorted_repeat_poly_list_rel_with0 R \<equiv> sorted_repeat_poly_list_rel_with0_wrt R term_poly_list_rel\<close>

abbreviation sorted_repeat_poly_rel_with0 where
  \<open>sorted_repeat_poly_rel_with0 \<equiv> sorted_repeat_poly_list_rel_with0 (rel2p (Id \<union> lexord var_order_rel))\<close>

lemma term_poly_list_relD:
  \<open>(xs, ys) \<in> term_poly_list_rel \<Longrightarrow> distinct xs\<close>
  \<open>(xs, ys) \<in> term_poly_list_rel \<Longrightarrow> ys = mset xs\<close>
  \<open>(xs, ys) \<in> term_poly_list_rel \<Longrightarrow> sorted_wrt (rel2p var_order_rel) xs\<close>
  \<open>(xs, ys) \<in> term_poly_list_rel \<Longrightarrow> sorted_wrt (rel2p (Id \<union> var_order_rel)) xs\<close>
  apply (auto simp: term_poly_list_rel_def; fail)+
  by (metis (mono_tags, lifting) CollectD UnI2 rel2p_def sorted_wrt_mono_rel split_conv
    term_poly_list_rel_def)

end
