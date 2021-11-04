(* Copyright 2020 (C) Mihails Milehins *)

section\<open>Smallness for orders\<close>
theory CZH_ECAT_Small_Order
  imports 
    CZH_ECAT_Order
    CZH_ECAT_Small_Functor
begin



subsection\<open>Background\<close>

named_theorems cat_small_order_cs_simps
named_theorems cat_small_order_cs_intros



subsection\<open>Tiny preorder category\<close>

locale cat_tiny_preorder = tiny_category \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_tiny_peo:
    "\<lbrakk> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> 
      (\<exists>f. Hom \<CC> a b = set {f}) \<or> (Hom \<CC> a b = 0)"


text\<open>Rules.\<close>

lemma (in cat_tiny_preorder) cat_tiny_preorder_axioms'[cat_order_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "cat_tiny_preorder \<alpha>' \<CC>"
  unfolding assms by (rule cat_tiny_preorder_axioms)

mk_ide rf cat_tiny_preorder_def[unfolded cat_tiny_preorder_axioms_def]
  |intro cat_tiny_preorderI|
  |dest cat_tiny_preorderD[dest]|
  |elim cat_tiny_preorderE[elim]|

lemmas [cat_small_order_cs_intros] = cat_tiny_preorderD(1)


text\<open>Tiny preorder is a preorder.\<close>

sublocale cat_tiny_preorder \<subseteq> cat_preorder
  by (intro cat_preorderI cat_tiny_peo category_axioms) simp_all

lemmas (in cat_tiny_preorder) cat_tiny_peo_is_cat_preoder = cat_preorder_axioms

lemmas [cat_small_order_cs_intros] = 
  cat_tiny_preorder.cat_tiny_peo_is_cat_preoder



subsection\<open>Tiny partial order category\<close>

locale cat_tiny_partial_order = cat_tiny_preorder \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_tiny_po:
    "\<lbrakk> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b; b \<le>\<^sub>O\<^bsub>\<CC>\<^esub> a \<rbrakk> \<Longrightarrow> a = b"


text\<open>Rules.\<close>

lemma (in cat_tiny_partial_order) 
  cat_tiny_partial_order_axioms'[cat_order_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "cat_tiny_partial_order \<alpha>' \<CC>"
  unfolding assms by (rule cat_tiny_partial_order_axioms)

mk_ide rf cat_tiny_partial_order_def[unfolded cat_tiny_partial_order_axioms_def]
  |intro cat_tiny_partial_orderI|
  |dest cat_tiny_partial_orderD[dest]|
  |elim cat_tiny_partial_orderE[elim]|

lemmas [cat_small_order_cs_intros] = cat_tiny_partial_orderD(1)


text\<open>Tiny partial order is a partial order.\<close>

sublocale cat_tiny_partial_order \<subseteq> cat_partial_order
  by (intro cat_partial_orderI cat_tiny_po cat_preorder_axioms) simp_all

lemmas (in cat_tiny_preorder) cat_tiny_po_is_cat_preoder = cat_preorder_axioms

lemmas [cat_small_order_cs_intros] = 
  cat_tiny_preorder.cat_tiny_peo_is_cat_preoder

lemma cat_tiny_partial_orderI':
  assumes "tiny_category \<alpha> \<CC>"
    and "cat_partial_order \<alpha> \<CC>"
  shows "cat_tiny_partial_order \<alpha> \<CC>"
proof-
  interpret tiny_category \<alpha> \<CC> by (rule assms(1))
  interpret cat_partial_order \<alpha> \<CC> by (rule assms(2))
  show ?thesis
    by (intro cat_tiny_partial_orderI cat_tiny_preorderI assms(1) cat_po cat_peo)
qed



subsection\<open>Tiny linear order category\<close>

locale cat_tiny_linear_order = cat_tiny_partial_order \<alpha> \<CC> for \<alpha> \<CC> + 
  assumes cat_tiny_lo: "\<lbrakk> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow> a \<le>\<^sub>O\<^bsub>\<CC>\<^esub> b \<or> b \<le>\<^sub>O\<^bsub>\<CC>\<^esub> a"


text\<open>Rules.\<close>

lemma (in cat_tiny_linear_order) 
  cat_tiny_linear_order_axioms'[cat_order_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "cat_tiny_linear_order \<alpha>' \<CC>"
  unfolding assms by (rule cat_tiny_linear_order_axioms)

mk_ide rf cat_tiny_linear_order_def[unfolded cat_tiny_linear_order_axioms_def]
  |intro cat_tiny_linear_orderI|
  |dest cat_tiny_linear_orderD[dest]|
  |elim cat_tiny_linear_orderE[elim]|

lemmas [cat_small_order_cs_intros] = cat_tiny_linear_orderD(1)


text\<open>Tiny linear order is a partial order.\<close>

sublocale cat_tiny_linear_order \<subseteq> cat_linear_order
  by (intro cat_linear_orderI cat_tiny_lo cat_partial_order_axioms) simp_all

lemmas (in cat_tiny_linear_order) cat_tiny_lo_is_cat_partial_order = 
  cat_linear_order_axioms

lemmas [cat_small_order_cs_intros] = 
  cat_tiny_linear_order.cat_tiny_lo_is_cat_partial_order

lemma cat_tiny_linear_orderI':
  assumes "tiny_category \<alpha> \<CC>" and "cat_linear_order \<alpha> \<CC>"
  shows "cat_tiny_linear_order \<alpha> \<CC>"
proof-
  interpret tiny_category \<alpha> \<CC> by (rule assms(1))
  interpret cat_linear_order \<alpha> \<CC> by (rule assms(2))
  show ?thesis
    by 
      (
        intro 
          assms(1) 
          cat_tiny_linear_orderI 
          cat_tiny_partial_orderI' 
          cat_partial_order_axioms 
          cat_lo
      )  
qed



subsection\<open>Tiny preorder functor\<close>

locale is_tiny_preorder_functor =
  is_functor \<alpha> \<AA> \<BB> \<FF> +
  HomDom: cat_tiny_preorder \<alpha> \<AA> +
  HomCod: cat_tiny_preorder \<alpha> \<BB>
  for \<alpha> \<AA> \<BB> \<FF> 

syntax "_is_tiny_preorder_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> 
  "CONST is_tiny_preorder_functor \<alpha> \<AA> \<BB> \<FF>"


text\<open>Rules.\<close>

lemma (in is_tiny_preorder_functor) 
  is_tiny_preorder_functor_axioms'[cat_order_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"  
  shows "\<FF> : \<AA>' \<le>\<^sub>C\<^sub>.\<^sub>P\<^sub>E\<^sub>O\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tiny_preorder_functor_axioms)

mk_ide rf is_tiny_preorder_functor_def
  |intro is_tiny_preorder_functorI|
  |dest is_tiny_preorder_functorD[dest]|
  |elim is_tiny_preorder_functorE[elim]|

lemmas [cat_small_order_cs_intros] = is_tiny_preorder_functorD(1)


text\<open>Tiny preorder functor is a tiny functor\<close>

sublocale is_tiny_preorder_functor \<subseteq> is_tiny_functor
  by
    (
      intro
        is_tiny_functorI'
        is_functor_axioms
        HomDom.tiny_category_axioms
        HomCod.tiny_category_axioms
    )

end