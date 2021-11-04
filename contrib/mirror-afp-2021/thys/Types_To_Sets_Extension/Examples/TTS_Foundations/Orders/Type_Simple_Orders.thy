(* Title: Examples/TTS_Foundations/Orders/Type_Simple_Orders.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Abstract orders on types\<close>
theory Type_Simple_Orders
  imports
    "../Foundations/FNDS_Definite_Description"
    FNDS_Auxiliary
begin



subsection\<open>Background\<close>


text\<open>
The results presented in this section were ported 
(with amendments and additions) from the theories \<^text>\<open>Orderings\<close> 
and \<^text>\<open>Set_Interval\<close> in the main library of Isabelle/HOL.
\<close>



subsection\<open>Order operations\<close>


text\<open>Abstract order operations.\<close>

locale ord = 
  fixes le ls :: "['a, 'a] \<Rightarrow> bool"

locale ord_syntax = ord le ls for le ls :: "['a, 'a] \<Rightarrow> bool"
begin

notation
  le ("'(\<le>\<^sub>a')") and
  le (infix "\<le>\<^sub>a" 50) and
  ls ("'(<\<^sub>a')") and
  ls (infix "<\<^sub>a" 50)

abbreviation (input) ge (infix "\<ge>\<^sub>a" 50)
  where "x \<ge>\<^sub>a y \<equiv> y \<le>\<^sub>a x"
abbreviation (input) gt (infix ">\<^sub>a" 50)
  where "x >\<^sub>a y \<equiv> y <\<^sub>a x"

notation
  ge ("'(\<ge>\<^sub>a')") and
  ge (infix "\<ge>\<^sub>a" 50) and
  gt ("'(>\<^sub>a')") and
  gt (infix ">\<^sub>a" 50)

end

locale ord_dual = ord le ls for le ls :: "['a, 'a] \<Rightarrow> bool"
begin

interpretation ord_syntax .
sublocale dual: ord ge gt .

end


text\<open>Pairs.\<close>

locale ord_pair = ord\<^sub>a: ord le\<^sub>a ls\<^sub>a + ord\<^sub>b: ord le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool"
begin

sublocale rev: ord_pair le\<^sub>b ls\<^sub>b le\<^sub>a ls\<^sub>a .

end

locale ord_pair_syntax = ord_pair le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b 
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool"
begin

sublocale ord\<^sub>a: ord_syntax le\<^sub>a ls\<^sub>a + ord\<^sub>b: ord_syntax le\<^sub>b ls\<^sub>b .

notation le\<^sub>a (\<open>'(\<le>\<^sub>a')\<close>)
  and le\<^sub>a (infix \<open>\<le>\<^sub>a\<close> 50) 
  and ls\<^sub>a (\<open>'(<\<^sub>a')\<close>) 
  and ls\<^sub>a (infix \<open><\<^sub>a\<close> 50)
  and le\<^sub>b (\<open>'(\<le>\<^sub>b')\<close>)
  and le\<^sub>b (infix \<open>\<le>\<^sub>b\<close> 50) 
  and ls\<^sub>b (\<open>'(<\<^sub>b')\<close>) 
  and ls\<^sub>b (infix \<open><\<^sub>b\<close> 50)

notation ord\<^sub>a.ge (\<open>'(\<ge>\<^sub>a')\<close>) 
  and ord\<^sub>a.ge (infix \<open>\<ge>\<^sub>a\<close> 50) 
  and ord\<^sub>a.gt (\<open>'(>\<^sub>a')\<close>) 
  and ord\<^sub>a.gt (infix \<open>>\<^sub>a\<close> 50)
  and ord\<^sub>b.ge (\<open>'(\<ge>\<^sub>b')\<close>) 
  and ord\<^sub>b.ge (infix \<open>\<ge>\<^sub>b\<close> 50) 
  and ord\<^sub>b.gt (\<open>'(>\<^sub>b')\<close>) 
  and ord\<^sub>b.gt (infix \<open>>\<^sub>b\<close> 50)

end

locale ord_pair_dual = ord_pair le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b 
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool"
begin

interpretation ord_pair_syntax .

sublocale ord_dual: ord_pair \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> .
sublocale dual_ord: ord_pair \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> .
sublocale dual_dual: ord_pair \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> .

end



subsection\<open>Preorders\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract preorders.\<close>

locale preorder = ord le ls for le ls :: "['a, 'a] \<Rightarrow> bool" +
  assumes less_le_not_le: "ls x y \<longleftrightarrow> le x y \<and> \<not> (le y x)"
    and order_refl[iff]: "le x x"
    and order_trans: "le x y \<Longrightarrow> le y z \<Longrightarrow> le x z"

locale preorder_dual = preorder le ls for le ls :: "['a, 'a] \<Rightarrow> bool"
begin

interpretation ord_syntax .

sublocale ord_dual .

sublocale dual: preorder ge gt 
  by standard (auto simp: less_le_not_le intro: order_trans)

end


text\<open>Pairs.\<close>

locale ord_preorder = ord_pair le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>b: preorder le\<^sub>b ls\<^sub>b 
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool"

locale ord_preorder_dual = ord_preorder le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool"
begin

interpretation ord_pair_syntax .

sublocale ord_pair_dual .
sublocale ord_dual: ord_preorder \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by unfold_locales (auto simp: ord\<^sub>b.less_le_not_le intro: ord\<^sub>b.order_trans)
sublocale dual_ord: ord_preorder \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by (rule ord_preorder_axioms)
sublocale dual_dual: ord_preorder \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by (rule ord_dual.ord_preorder_axioms)

end

locale preorder_pair = ord_preorder le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>a: preorder le\<^sub>a ls\<^sub>a
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool"
begin

sublocale rev: preorder_pair le\<^sub>b ls\<^sub>b le\<^sub>a ls\<^sub>a ..

end

locale preorder_pair_dual = preorder_pair le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool"
begin

interpretation ord_pair_syntax .

sublocale ord_preorder_dual ..
sublocale ord_dual: preorder_pair \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: preorder_pair \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by unfold_locales (auto intro: ord\<^sub>a.order_trans simp: ord\<^sub>a.less_le_not_le)
sublocale dual_dual: preorder_pair \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end


subsubsection\<open>Results\<close>

context preorder
begin

interpretation ord_syntax .


text\<open>Reflexivity.\<close>

lemma eq_refl: 
  assumes "x = y"
  shows "x \<le>\<^sub>a y" 
  using assms by (rule ssubst) (rule order_refl)  
  
lemma less_irrefl[iff]: "\<not> x <\<^sub>a x" by (simp add: less_le_not_le)

lemma less_imp_le: 
  assumes "x <\<^sub>a y"
  shows "x \<le>\<^sub>a y" 
  using assms by (simp add: less_le_not_le)

lemma strict_implies_not_eq: 
  assumes "a <\<^sub>a b"
  shows "a \<noteq> b" 
  using assms by blast


text\<open>Asymmetry.\<close>

lemma less_not_sym: 
  assumes "x <\<^sub>a y"
  shows "\<not> (y <\<^sub>a x)"
  using assms by (simp add: less_le_not_le)

lemma asym: 
  assumes "a <\<^sub>a b" and "b <\<^sub>a a" 
  shows False
  using assms by (simp add: less_not_sym)

lemma less_asym: 
  assumes "x <\<^sub>a y" and "(\<not> P \<Longrightarrow> y <\<^sub>a x)" 
  shows P
  using assms by (auto dest: asym)
 

text\<open>Transitivity.\<close>

lemma less_trans: 
  assumes "x <\<^sub>a y" and "y <\<^sub>a z" 
  shows "x <\<^sub>a z"
  using assms by (auto simp: less_le_not_le intro: order_trans)

lemma le_less_trans: 
  assumes "x \<le>\<^sub>a y" and "y <\<^sub>a z" 
  shows "x <\<^sub>a z"  
  using assms by (auto simp: less_le_not_le intro: order_trans)

lemma less_le_trans: 
  assumes "x <\<^sub>a y" and "y \<le>\<^sub>a z" 
  shows "x <\<^sub>a z"
  using assms by (auto simp: less_le_not_le intro: order_trans)

lemma less_imp_not_less: 
  assumes "x <\<^sub>a y"
  shows "(\<not> y <\<^sub>a x) \<longleftrightarrow> True"
  using assms by (elim less_asym) simp

lemma less_imp_triv: 
  assumes "x <\<^sub>a y"
  shows "(y <\<^sub>a x \<longrightarrow> P) \<longleftrightarrow> True"
  using assms by (elim less_asym) simp

lemma less_asym': 
  assumes "a <\<^sub>a b" and "b <\<^sub>a a" 
  shows P 
  using assms by (rule less_asym)

end



subsection\<open>Partial orders\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract partial orders.\<close>

locale order = preorder le ls for le ls :: "['a, 'a] \<Rightarrow> bool" +
  assumes antisym: "le x y \<Longrightarrow> le y x \<Longrightarrow> x = y"

locale order_dual = order le ls for le ls :: "['a, 'a] \<Rightarrow> bool"
begin

interpretation ord_syntax .

sublocale preorder_dual ..

sublocale dual: order ge gt 
  unfolding order_def order_axioms_def
  apply unfold_locales
  apply(rule conjI)
  subgoal by (rule dual.preorder_axioms)
  subgoal by (simp add: antisym)
  done

end


text\<open>Pairs.\<close>

locale ord_order = ord_preorder le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>b: order le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"

locale ord_order_dual = ord_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

interpretation ord_pair_syntax .

sublocale ord_preorder_dual ..
sublocale ord_dual: ord_order \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by unfold_locales (simp add: ord\<^sub>b.antisym)
sublocale dual_ord: ord_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by (rule ord_order_axioms)
sublocale dual_dual: ord_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by (rule ord_dual.ord_order_axioms)

end

locale preorder_order = ord_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>a: preorder le\<^sub>a ls\<^sub>a
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool"
begin

sublocale preorder_pair ..

end

locale preorder_order_dual = preorder_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool" 
begin

interpretation ord_pair_syntax .

sublocale ord_order_dual ..
sublocale preorder_pair_dual ..
sublocale ord_dual: preorder_order \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> .. 
sublocale dual_ord: preorder_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> .. 
sublocale dual_dual: preorder_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end

locale order_pair = preorder_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>a: order le\<^sub>a ls\<^sub>a
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool" 
begin

sublocale rev: order_pair le\<^sub>b ls\<^sub>b le\<^sub>a ls\<^sub>a ..

end

locale order_pair_dual = order_pair le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "['a, 'a] \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "['b, 'b] \<Rightarrow> bool" 
begin

interpretation ord_pair_syntax .

sublocale preorder_order_dual ..
sublocale ord_dual: order_pair \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: order_pair \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by unfold_locales (simp add: ord\<^sub>a.antisym)
sublocale dual_dual: order_pair \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end


subsubsection\<open>Results\<close>

context order
begin

interpretation ord_syntax .


text\<open>Reflexivity.\<close>

lemma less_le: "x <\<^sub>a y \<longleftrightarrow> x \<le>\<^sub>a y \<and> x \<noteq> y"
  by (auto simp: less_le_not_le intro: antisym)

lemma le_less: "x \<le>\<^sub>a y \<longleftrightarrow> x <\<^sub>a y \<or> x = y" by (auto simp: less_le)

lemma le_imp_less_or_eq: 
  assumes "x \<le>\<^sub>a y"
  shows "x <\<^sub>a y \<or> x = y" 
  using assms by (simp add: le_less)

lemma less_imp_not_eq: 
  assumes "x <\<^sub>a y"
  shows "(x = y) \<longleftrightarrow> False" 
  using assms by auto

lemma less_imp_not_eq2: 
  assumes "x <\<^sub>a y"
  shows "(y = x) \<longleftrightarrow> False"
  using assms by auto


text\<open>Transitivity.\<close>

lemma neq_le_trans: 
  assumes "a \<noteq> b" and "a \<le>\<^sub>a b" 
  shows "a <\<^sub>a b" 
  using assms by (simp add: less_le)

lemma le_neq_trans: 
  assumes "a \<le>\<^sub>a b" and "a \<noteq> b" 
  shows "a <\<^sub>a b" 
  using assms by (simp add: less_le)

text\<open>Asymmetry.\<close>

lemma eq_iff: "x = y \<longleftrightarrow> x \<le>\<^sub>a y \<and> y \<le>\<^sub>a x" by (blast intro: antisym)

lemma antisym_conv: 
  assumes "y \<le>\<^sub>a x"
  shows "x \<le>\<^sub>a y \<longleftrightarrow> x = y" 
  using assms by (blast intro: antisym)


text\<open>Other results.\<close>

lemma antisym_conv1: 
  assumes "\<not> x <\<^sub>a y"
  shows "x \<le>\<^sub>a y \<longleftrightarrow> x = y"
  using assms by (simp add: le_less)

lemma antisym_conv2: 
  assumes "x \<le>\<^sub>a y"
  shows "\<not> x <\<^sub>a y \<longleftrightarrow> x = y"
  using assms le_less by auto

lemma leD: 
  assumes "y \<le>\<^sub>a x"
  shows "\<not> x <\<^sub>a y"
  using assms by (simp add: less_le_not_le)

end



subsection\<open>Dense orders\<close>


text\<open>Abstract dense orders.\<close>

locale dense_order = order le ls for le ls :: "['a, 'a] \<Rightarrow> bool" +
  assumes dense: "ls x y \<Longrightarrow> (\<exists>z. ls x z \<and> ls z y)"

locale dense_order_dual = dense_order le ls for le ls :: "['a, 'a] \<Rightarrow> bool"
begin

interpretation ord_syntax .

sublocale order_dual ..

sublocale dual: dense_order ge gt 
  using dense by unfold_locales auto

end


text\<open>Pairs.\<close>

locale ord_dense_order = ord_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>b: dense_order le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"

locale ord_dense_order_dual = ord_dense_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

interpretation ord_pair_syntax .

sublocale ord_order_dual ..
sublocale ord_dual: ord_dense_order \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  using ord\<^sub>b.dense by unfold_locales blast
sublocale dual_ord: ord_dense_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by (rule ord_dense_order_axioms)
sublocale dual_dual: ord_dense_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by (rule ord_dual.ord_dense_order_axioms)

end

locale preorder_dense_order = 
  ord_dense_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>a: preorder le\<^sub>a ls\<^sub>a
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

sublocale preorder_order ..

end

locale preorder_dense_order_dual = preorder_dense_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

interpretation ord_pair_syntax .

sublocale ord_dense_order_dual ..
sublocale preorder_order_dual ..
sublocale ord_dual: preorder_dense_order \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: preorder_dense_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> ..    
sublocale dual_dual: preorder_dense_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end

locale order_dense_order = 
  preorder_dense_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>a: order le\<^sub>a ls\<^sub>a
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

sublocale order_pair ..

end

locale order_dense_order_dual = order_dense_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

interpretation ord_pair_syntax .

sublocale preorder_dense_order_dual ..
sublocale order_pair_dual ..
sublocale ord_dual: order_dense_order \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: order_dense_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> ..    
sublocale dual_dual: order_dense_order \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end

locale dense_order_pair = 
  order_dense_order le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b + ord\<^sub>a: dense_order le\<^sub>a ls\<^sub>a
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"

locale dense_order_pair_dual = dense_order_pair le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b
  for le\<^sub>a ls\<^sub>a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and le\<^sub>b ls\<^sub>b :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

interpretation ord_pair_syntax .

sublocale order_dense_order_dual ..
sublocale ord_dual: dense_order_pair \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: dense_order_pair \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  using ord\<^sub>a.dense by unfold_locales auto
sublocale dual_dual: dense_order_pair \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end



subsection\<open>(Unique) top and bottom elements\<close>


text\<open>Abstract extremum.\<close>

locale extremum =
  fixes extremum :: 'a 

locale ord_extremum = ord le ls + extremum extremum 
  for le ls :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and extremum :: 'a


text\<open>Concrete syntax.\<close>

locale bot = extremum bot for bot :: 'a
begin

notation bot ("\<bottom>")

end

locale top = extremum top for top :: 'a
begin

notation top ("\<top>")

end



subsection\<open>(Unique) top and bottom elements for partial orders\<close>


subsubsection\<open>Definitions\<close>


text\<open>Abstract partial order with extremum.\<close>

locale order_extremum = ord_extremum le ls extremum + order le ls
  for le ls :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and extremum :: 'a  +
  assumes extremum[simp]: "le a extremum"


text\<open>Concrete syntax.\<close>

locale order_bot = 
  order_dual le ls + 
  dual: order_extremum \<open>\<lambda>x y. le y x\<close> \<open>\<lambda>x y. ls y x\<close> bot + 
  bot bot 
  for le ls :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and bot :: 'a 

locale order_top = order_dual le ls + order_extremum le ls top + top top
  for le ls :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and top :: 'a 


subsubsection\<open>Results\<close>

context order_extremum
begin

interpretation ord_syntax .

lemma extremum_uniqueI: 
  assumes "extremum \<le>\<^sub>a a"
  shows "a = extremum"
  using assms by (simp add: antisym)

lemma extremum_unique: "extremum \<le>\<^sub>a a \<longleftrightarrow> a = extremum"
  by (auto intro: antisym)

lemma extremum_strict[simp]: "\<not> (extremum <\<^sub>a a)"
  by (fastforce simp: less_le_not_le)

lemma not_eq_extremum: "a \<noteq> extremum \<longleftrightarrow> a <\<^sub>a extremum"
  using le_imp_less_or_eq by (auto intro: extremum)

end



subsection\<open>Partial orders without top or bottom elements\<close>


text\<open>Abstract partial orders without top or bottom elements.\<close>

locale no_extremum = order le ls for le ls :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  assumes gt_ex: "\<exists>y. ls x y"


text\<open>Concrete syntax.\<close>

locale no_top = order_dual le ls + no_extremum le ls 
  for le ls :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

locale no_bot = 
  order_dual le ls + 
  dual: no_extremum \<open>\<lambda>x y. le y x\<close> \<open>\<lambda>x y. ls y x\<close> 
  for le ls :: "'a \<Rightarrow> 'a \<Rightarrow> bool"



subsection\<open>Least and greatest operators\<close>

definition Least :: "['a set, ['a, 'a] \<Rightarrow> bool, 'a \<Rightarrow> bool] \<Rightarrow> 'a option" 
  (\<open>(on _ with _ : \<guillemotleft>Least\<guillemotright> _)\<close> [1000, 1000, 1000] 10) 
  where 
    "on U with op : \<guillemotleft>Least\<guillemotright> P \<equiv> (THE x on U. P x \<and> (\<forall>y\<in>U. P y \<longrightarrow> op x y))"

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule, transfer_rule]: "Domainp A = (\<lambda>x. x \<in> U)"
    and [transfer_rule]: "bi_unique A" "right_total A" 
  trp (?'a A)
  in Least_def

context ord_syntax
begin

abbreviation Least where "Least \<equiv> Type_Simple_Orders.Least UNIV (\<le>\<^sub>a)"
abbreviation Greatest where "Greatest \<equiv> Type_Simple_Orders.Least UNIV (\<ge>\<^sub>a)"

lemmas Least_def = Least_def[of UNIV \<open>(\<le>\<^sub>a)\<close>]

end

context order
begin

interpretation ord_syntax .
                  
lemma Least_equality:
  assumes "P x" and "\<And>y. P y \<Longrightarrow> x \<le>\<^sub>a y"
  shows "Least P = Some x"
  unfolding Least_def by (rule The_on_Some_equality) (auto simp: assms antisym)

lemma LeastI2_order:
  assumes "P x" 
    and "\<And>y. P y \<Longrightarrow> x \<le>\<^sub>a y"
    and "\<And>x. P x \<Longrightarrow> \<forall>y. P y \<longrightarrow> x \<le>\<^sub>a y \<Longrightarrow> Q x"
  obtains z where "Least P = Some z" and "Q z"
  unfolding Least_def using assms by (clarsimp simp: that Least_equality)

lemma Least_ex1:
  assumes "\<exists>!x. P x \<and> (\<forall>y. P y \<longrightarrow> x \<le>\<^sub>a y)"
  obtains x where "Least P = Some x" and "P x" and "P z \<Longrightarrow> x \<le>\<^sub>a z"
  using assms unfolding Least_def by (clarsimp simp: that Least_equality)

end



subsection\<open>min and max\<close>

definition min :: "[['a, 'a] \<Rightarrow> bool, 'a, 'a] \<Rightarrow> 'a" where
  "min le a b = (if le a b then a else b)"

ctr parametricity
  in min_def  

context ord_syntax
begin

abbreviation min where "min \<equiv> Type_Simple_Orders.min (\<le>\<^sub>a)"
abbreviation max where "max \<equiv> Type_Simple_Orders.min (\<ge>\<^sub>a)"

end

context ord
begin

interpretation ord_syntax .

lemma min_absorb1: "x \<le>\<^sub>a y \<Longrightarrow> min x y = x"
  unfolding min_def by simp

end


context order
begin

interpretation ord_syntax .

lemma min_absorb2: 
  assumes "y \<le>\<^sub>a x"
  shows "min x y = y"
  using assms unfolding min_def by (simp add: eq_iff)

end

context order_extremum
begin

interpretation ord_syntax .

lemma max_top[simp]: "max extremum x = extremum"
  by (simp add: ord.min_absorb1)

lemma max_top2[simp]: "max x extremum = extremum"
  unfolding min_def by (simp add: extremum_uniqueI)

lemma min_top[simp]: "min extremum x = x" by (simp add: min_absorb2)

lemma min_top2[simp]: "min x extremum = x"  by (simp add: min_def top_unique)

end



subsection\<open>Monotonicity\<close>

definition mono :: 
  "['a set, ['a, 'a] \<Rightarrow> bool, ['b, 'b] \<Rightarrow> bool, 'a \<Rightarrow> 'b] \<Rightarrow> bool" 
  (\<open>(on _ with _ _ : \<guillemotleft>mono\<guillemotright> _)\<close> [1000, 1000, 999, 1000] 10) 
  where
    "on U\<^sub>a with op\<^sub>1 op\<^sub>2 : \<guillemotleft>mono\<guillemotright> f \<equiv> \<forall>x\<in>U\<^sub>a. \<forall>y\<in>U\<^sub>a. op\<^sub>1 x y \<longrightarrow> op\<^sub>2 (f x) (f y)"

ctr parametricity
  in mono_def

context ord_pair_syntax
begin

abbreviation mono\<^sub>a\<^sub>b 
  where "mono\<^sub>a\<^sub>b \<equiv> Type_Simple_Orders.mono UNIV (\<le>\<^sub>a) (\<le>\<^sub>b)"
abbreviation mono\<^sub>b\<^sub>a 
  where "mono\<^sub>b\<^sub>a \<equiv> Type_Simple_Orders.mono UNIV (\<le>\<^sub>b) (\<le>\<^sub>a)"
abbreviation antimono\<^sub>a\<^sub>b 
  where "antimono\<^sub>a\<^sub>b \<equiv> Type_Simple_Orders.mono UNIV (\<le>\<^sub>a) (\<ge>\<^sub>b)"
abbreviation antimono\<^sub>b\<^sub>a 
  where "antimono\<^sub>b\<^sub>a \<equiv> Type_Simple_Orders.mono UNIV (\<le>\<^sub>b) (\<ge>\<^sub>a)"
abbreviation strict_mono\<^sub>a\<^sub>b 
  where "strict_mono\<^sub>a\<^sub>b \<equiv> Type_Simple_Orders.mono UNIV (<\<^sub>a) (<\<^sub>b)"
abbreviation strict_mono\<^sub>b\<^sub>a 
  where "strict_mono\<^sub>b\<^sub>a \<equiv> Type_Simple_Orders.mono UNIV (<\<^sub>b) (<\<^sub>a)"
abbreviation strict_antimono\<^sub>a\<^sub>b 
  where "strict_antimono\<^sub>a\<^sub>b \<equiv> Type_Simple_Orders.mono UNIV (<\<^sub>a) (>\<^sub>b)"
abbreviation strict_antimono\<^sub>b\<^sub>a 
  where "strict_antimono\<^sub>b\<^sub>a \<equiv> Type_Simple_Orders.mono UNIV (<\<^sub>b) (>\<^sub>a)"

end

context ord_pair
begin

interpretation ord_pair_syntax .

lemma monoI[intro?]: 
  assumes "\<And>x y. x \<le>\<^sub>a y \<Longrightarrow> f x \<le>\<^sub>b f y" 
  shows "mono\<^sub>a\<^sub>b f"
  unfolding mono_def using assms by simp

lemma monoD[dest?]:
  assumes "mono\<^sub>a\<^sub>b f" and "x \<le>\<^sub>a y" 
  shows "f x \<le>\<^sub>b f y"
  using assms unfolding mono_def by simp

lemma monoE:
  assumes "mono\<^sub>a\<^sub>b f" and "x \<le>\<^sub>a y"
  obtains "f x \<le>\<^sub>b f y"
  using assms unfolding mono_def by simp

lemma strict_monoI[intro?]: 
  assumes "\<And>x y. x <\<^sub>a y \<Longrightarrow> f x <\<^sub>b f y" 
  shows "strict_mono\<^sub>a\<^sub>b f"
  unfolding mono_def using assms by simp

lemma strict_monoD[dest?]:
  assumes "strict_mono\<^sub>a\<^sub>b f" and "x <\<^sub>a y" 
  shows "f x <\<^sub>b f y"
  using assms unfolding mono_def by simp

lemma strict_monoE:
  assumes "strict_mono\<^sub>a\<^sub>b f" and "x <\<^sub>a y"
  obtains "f x <\<^sub>b f y"
  using assms unfolding mono_def by simp

end

context order_pair
begin

interpretation ord_pair_syntax .

lemma strict_mono_mono[dest?]: 
  assumes "strict_mono\<^sub>a\<^sub>b f"
  shows "mono\<^sub>a\<^sub>b f"
proof(rule monoI)
  fix x y
  assume "x \<le>\<^sub>a y"
  show "f x \<le>\<^sub>b f y"
  proof (cases "x = y")
    case True then show ?thesis by simp
  next
    case False with \<open>x \<le>\<^sub>a y\<close> have "x <\<^sub>a y" by (simp add: ord\<^sub>a.neq_le_trans)
    with assms strict_monoD have "f x <\<^sub>b f y" by simp
    then show ?thesis by (simp add: ord\<^sub>b.le_less)
  qed
qed

end



subsection\<open>Set intervals\<close>

definition ray :: "['a set, ['a, 'a] \<Rightarrow> bool, 'a] \<Rightarrow> 'a set" 
  (\<open>(on _ with _ : {..\<sqsubset>_})\<close> [1000, 1000, 1000] 10) 
  where "on U with op : {..\<sqsubset>u} \<equiv> {x \<in> U. op x u}" 
definition interval :: 
  "['a set, ['a, 'a] \<Rightarrow> bool, ['a, 'a] \<Rightarrow> bool, 'a, 'a] \<Rightarrow> 'a set"
  (\<open>(on _ with _ _ : {_\<sqsubset>..\<sqsubset>_})\<close> [1000, 1000, 999, 1000, 1000] 10) 
  where "on U with op\<^sub>1 op\<^sub>2 : {l\<sqsubset>..\<sqsubset>u} \<equiv> 
    (on U with (\<lambda>x y. op\<^sub>1 y x) : {..\<sqsubset>l}) \<inter> (on U with op\<^sub>2 : {..\<sqsubset>u})"

lemma ray_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows "(rel_set A ===> (A ===> A ===> (=)) ===> A ===> rel_set A) ray ray"
  unfolding ray_def
proof(intro rel_funI)
  fix S :: "'a set" and S' :: "'b set" 
    and le :: "['a, 'a] \<Rightarrow> bool" and le' :: "['b, 'b] \<Rightarrow> bool" 
    and u u'
  assume [transfer_rule]: "rel_set A S S'"
    and [transfer_rule]: "(A ===> A ===> (=)) le le'"
    and [transfer_rule]: "A u u'"
  show "rel_set A {xc \<in> S. le xc u} {x \<in> S'. le' x u'}"
  proof(intro rel_setI)
    show "x \<in> {xc \<in> S. le xc u} \<Longrightarrow> \<exists>x'\<in>{x \<in> S'. le' x u'}. A x x'" for x
    proof-
      assume x: "x \<in> {xc \<in> S. le xc u}"
      then obtain x' where [transfer_rule]: "A x x'"  
        using \<open>rel_set A S S'\<close> rel_setD1 by fastforce
      from x have "x' \<in> {x \<in> S'. le' x u'}" 
        apply transfer using \<open>A x x'\<close> by auto
      then show ?thesis by (auto simp: \<open>A x x'\<close>)
    qed
    show "x' \<in> {x \<in> S'. le' x u'} \<Longrightarrow> \<exists>x\<in>{xc \<in> S. le xc u}. A x x'" for x'
    proof-
      assume x': "x' \<in> {x \<in> S'. le' x u'}"
      then obtain x where [transfer_rule]: "A x x'"   
        using assms(2) by (auto elim: right_totalE)
      from x' have "x \<in> {xc \<in> S. le xc u}" by transfer auto
      then show ?thesis by (auto simp: \<open>A x x'\<close>)
    qed  
  qed
qed

ctr relativization
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  trp (?'a A)
  in interval_def

lemma interval_ge_le:
  "(on UNIV with (\<lambda>x y. le\<^sub>a y x) (\<lambda>x y. le\<^sub>b y x) : {l\<sqsubset>..\<sqsubset>h}) = 
    (on UNIV with le\<^sub>b le\<^sub>a : {h\<sqsubset>..\<sqsubset>l})"
  unfolding interval_def by auto

context ord_syntax  
begin

abbreviation lessThan (\<open>{..<\<^sub>a_}\<close>) 
  where "{..<\<^sub>au} \<equiv> on UNIV with (<\<^sub>a) : {..\<sqsubset>u}"
abbreviation atMost (\<open>{..\<le>\<^sub>a_}\<close>) 
  where "{..\<le>\<^sub>au} \<equiv> on UNIV with (\<le>\<^sub>a) : {..\<sqsubset>u}"
abbreviation greaterThan (\<open>{_<\<^sub>a..}\<close>) 
  where "{l<\<^sub>a..} \<equiv> on UNIV with (>\<^sub>a) : {..\<sqsubset>l}"
abbreviation atLeast (\<open>{_\<le>\<^sub>a..}\<close>) 
  where "{l\<le>\<^sub>a..} \<equiv> on UNIV with (\<ge>\<^sub>a) : {..\<sqsubset>l}"
abbreviation greaterThanLessThan (\<open>{_<\<^sub>a..<\<^sub>a_}\<close>) 
  where "{l<\<^sub>a..<\<^sub>au} \<equiv> on UNIV with (<\<^sub>a) (<\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation atLeastLessThan (\<open>{_\<le>\<^sub>a..<\<^sub>a_}\<close>) 
  where "{l\<le>\<^sub>a..<\<^sub>au} \<equiv> on UNIV with (\<le>\<^sub>a) (<\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation greaterThanAtMost (\<open>{_<\<^sub>a..\<le>\<^sub>a_}\<close>) 
  where "{l<\<^sub>a..\<le>\<^sub>au} \<equiv> on UNIV with (<\<^sub>a) (\<le>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation atLeastAtMost (\<open>{_\<le>\<^sub>a..\<le>\<^sub>a_}\<close>) 
  where "{l\<le>\<^sub>a..\<le>\<^sub>au} \<equiv> on UNIV with (\<le>\<^sub>a) (\<le>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation lessThanGreaterThan (\<open>{_>\<^sub>a..>\<^sub>a_}\<close>) 
  where "{l>\<^sub>a..>\<^sub>au} \<equiv> on UNIV with (>\<^sub>a) (>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation lessThanAtLeast (\<open>{_\<ge>\<^sub>a..>\<^sub>a_}\<close>) 
  where "{l\<ge>\<^sub>a..>\<^sub>au} \<equiv> on UNIV with (\<ge>\<^sub>a) (>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation atMostGreaterThan (\<open>{_>\<^sub>a..\<ge>\<^sub>a_}\<close>) 
  where "{l>\<^sub>a..\<ge>\<^sub>au} \<equiv> on UNIV with (>\<^sub>a) (\<ge>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation atMostAtLeast (\<open>{_\<ge>\<^sub>a..\<ge>\<^sub>a_}\<close>) 
  where "{l\<ge>\<^sub>a..\<ge>\<^sub>au} \<equiv> on UNIV with (\<ge>\<^sub>a) (\<ge>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"

end

context ord
begin

interpretation ord_syntax .

lemma lessThan_iff[iff]: "(i \<in> {..<\<^sub>ak}) = (i <\<^sub>a k)"
  unfolding ray_def by simp

lemma atLeast_iff[iff]: "(i \<in> {k\<le>\<^sub>a..}) = (k \<le>\<^sub>a i)"
  unfolding ray_def by simp

lemma greaterThanLessThan_iff[simp]: "(i \<in> {l<\<^sub>a..<\<^sub>au}) = (l <\<^sub>a i \<and> i <\<^sub>a u)"
  unfolding interval_def ray_def by simp

lemma atLeastLessThan_iff[simp]: "(i \<in> {l\<le>\<^sub>a..<\<^sub>au}) = (l \<le>\<^sub>a i \<and> i <\<^sub>a u)"
  unfolding interval_def ray_def by simp

lemma greaterThanAtMost_iff[simp]: "(i \<in> {l<\<^sub>a..\<le>\<^sub>au}) = (l <\<^sub>a i \<and> i \<le>\<^sub>a u)"
  unfolding interval_def ray_def by simp

lemma atLeastAtMost_iff[simp]: "(i \<in> {l\<le>\<^sub>a..\<le>\<^sub>au}) = (l \<le>\<^sub>a i \<and> i \<le>\<^sub>a u)"
  unfolding interval_def ray_def by simp

lemma greaterThanLessThan_eq: "{a<\<^sub>a..<\<^sub>ab} = {a<\<^sub>a..} \<inter> {..<\<^sub>ab}"
  unfolding interval_def ray_def by simp

end

context ord_pair_syntax
begin

notation ord\<^sub>a.lessThan (\<open>{..<\<^sub>a_}\<close>) 
  and ord\<^sub>a.atMost (\<open>{..\<le>\<^sub>a_}\<close>) 
  and ord\<^sub>a.greaterThan (\<open>{_<\<^sub>a..}\<close>) 
  and ord\<^sub>a.atLeast (\<open>{_\<le>\<^sub>a..}\<close>) 
  and ord\<^sub>a.greaterThanLessThan (\<open>{_<\<^sub>a..<\<^sub>a_}\<close>) 
  and ord\<^sub>a.atLeastLessThan (\<open>{_\<le>\<^sub>a..<\<^sub>a_}\<close>) 
  and ord\<^sub>a.greaterThanAtMost (\<open>{_<\<^sub>a..\<le>\<^sub>a_}\<close>) 
  and ord\<^sub>a.atLeastAtMost (\<open>{_\<le>\<^sub>a..\<le>\<^sub>a_}\<close>) 
  and ord\<^sub>a.lessThanGreaterThan (\<open>{_>\<^sub>a..>\<^sub>a_}\<close>)
  and ord\<^sub>a.lessThanAtLeast (\<open>{_\<ge>\<^sub>a..>\<^sub>a_}\<close>) 
  and ord\<^sub>a.atMostGreaterThan (\<open>{_>\<^sub>a..\<ge>\<^sub>a_}\<close>) 
  and ord\<^sub>a.atMostAtLeast (\<open>{_\<ge>\<^sub>a..\<ge>\<^sub>a_}\<close>) 
  and ord\<^sub>b.lessThan (\<open>{..<\<^sub>b_}\<close>) 
  and ord\<^sub>b.atMost (\<open>{..\<le>\<^sub>b_}\<close>) 
  and ord\<^sub>b.greaterThan (\<open>{_<\<^sub>b..}\<close>) 
  and ord\<^sub>b.atLeast (\<open>{_\<le>\<^sub>b..}\<close>) 
  and ord\<^sub>b.greaterThanLessThan (\<open>{_<\<^sub>b..<\<^sub>b_}\<close>) 
  and ord\<^sub>b.atLeastLessThan (\<open>{_\<le>\<^sub>b..<\<^sub>b_}\<close>) 
  and ord\<^sub>b.greaterThanAtMost (\<open>{_<\<^sub>b..\<le>\<^sub>b_}\<close>) 
  and ord\<^sub>b.atLeastAtMost (\<open>{_\<le>\<^sub>b..\<le>\<^sub>b_}\<close>)
  and ord\<^sub>b.lessThanGreaterThan (\<open>{_>\<^sub>b..>\<^sub>b_}\<close>)
  and ord\<^sub>b.lessThanAtLeast (\<open>{_\<ge>\<^sub>b..>\<^sub>b_}\<close>) 
  and ord\<^sub>b.atMostGreaterThan (\<open>{_>\<^sub>b..\<ge>\<^sub>b_}\<close>) 
  and ord\<^sub>b.atMostAtLeast (\<open>{_\<ge>\<^sub>b..\<ge>\<^sub>b_}\<close>)

end

context preorder
begin

interpretation ord_syntax .

lemma Ioi_le_Ico: "{a<\<^sub>a..} \<subseteq> {a\<le>\<^sub>a..}"
  unfolding ray_def by (fastforce simp: less_le_not_le)

end

context preorder
begin

interpretation ord_syntax .

interpretation preorder_dual le ls
  by (rule preorder_dual.intro[OF preorder_axioms])

lemma single_Diff_lessThan[simp]: "{k} - {..<\<^sub>ak} = {k}" by auto

lemma atLeast_subset_iff[iff]: "({x\<le>\<^sub>a..} \<subseteq> {y\<le>\<^sub>a..}) = (y \<le>\<^sub>a x)"
  by (auto intro: order_trans)

lemma atLeastatMost_empty[simp]: 
  assumes "b <\<^sub>a a"
  shows "{a\<le>\<^sub>a..\<le>\<^sub>ab} = {}"
  unfolding interval_def 
  using less_le_not_le assms
  by (metis Int_emptyI ord.lessThan_iff atLeast_iff order_trans)

lemma atLeastatMost_empty_iff[simp]: "{a\<le>\<^sub>a..\<le>\<^sub>ab} = {} \<longleftrightarrow> (\<not> a \<le>\<^sub>a b)"
  by auto (blast intro: order_trans)

lemma atLeastatMost_empty_iff2[simp]: "{} = {a\<le>\<^sub>a..\<le>\<^sub>ab} \<longleftrightarrow> (\<not> a \<le>\<^sub>a b)"
  by auto (blast intro: order_trans)

lemma atLeastLessThan_empty[simp]: 
  assumes "b \<le>\<^sub>a a" 
  shows "{a\<le>\<^sub>a..<\<^sub>ab} = {}"
  unfolding interval_def 
  using assms less_le_not_le 
  by (blast intro: order_trans)

lemma atLeastLessThan_empty_iff[simp]: "{a\<le>\<^sub>a..<\<^sub>ab} = {} \<longleftrightarrow> (\<not> a <\<^sub>a b)"
  unfolding interval_def by (auto simp: le_less_trans ord.lessThan_iff)

lemma atLeastLessThan_empty_iff2[simp]: "{} = {a\<le>\<^sub>a..<\<^sub>ab} \<longleftrightarrow> (\<not> a <\<^sub>a b)"
  unfolding interval_def by (auto simp: le_less_trans ord.lessThan_iff)

lemma greaterThanAtMost_empty[simp]: 
  assumes "l \<le>\<^sub>a k" 
  shows "{k<\<^sub>a..\<le>\<^sub>al} = {}" 
  using assms atLeastLessThan_empty[OF assms]
  unfolding 
    greaterThanAtMost_eq_atLeastAtMost_diff 
    atLeastLessThan_eq_atLeastAtMost_diff
  using le_less_trans by auto blast

lemma greaterThanAtMost_empty_iff[simp]: "{k<\<^sub>a..\<le>\<^sub>al} = {} \<longleftrightarrow> \<not> k <\<^sub>a l"
  by (auto simp: dual.le_less_trans)

lemma greaterThanAtMost_empty_iff2[simp]: "{} = {k<\<^sub>a..\<le>\<^sub>al} \<longleftrightarrow> \<not> k <\<^sub>a l"
  unfolding interval_def ray_def by (blast intro: less_le_trans)

lemma greaterThanLessThan_empty[simp]: 
  assumes "l \<le>\<^sub>a k" 
  shows "{k<\<^sub>a..<\<^sub>al} = {}"
  using assms by auto (blast intro: le_less_trans asym equals0I)

lemma atLeastatMost_subset_iff[simp]:
  "{a\<le>\<^sub>a..\<le>\<^sub>ab} \<le> {c\<le>\<^sub>a..\<le>\<^sub>ad} \<longleftrightarrow> (\<not> a \<le>\<^sub>a b) \<or> c \<le>\<^sub>a a \<and> b \<le>\<^sub>a d"
  by auto (blast intro: order_trans)+

lemma atLeastatMost_psubset_iff:
  "{a\<le>\<^sub>a..\<le>\<^sub>ab} < {c\<le>\<^sub>a..\<le>\<^sub>ad} \<longleftrightarrow>
    ((\<not> a \<le>\<^sub>a b) \<or> c \<le>\<^sub>a a \<and> b \<le>\<^sub>a d \<and> (c <\<^sub>a a \<or> b <\<^sub>a d)) \<and> c \<le>\<^sub>a d"
  by (simp add: psubset_eq set_eq_iff less_le_not_le) 
    (blast intro: order_trans)

lemma Icc_subset_Ici_iff[simp]: 
  "{l\<le>\<^sub>a..\<le>\<^sub>ah} \<subseteq> {l'\<le>\<^sub>a..} = (\<not> l \<le>\<^sub>a h \<or> l \<ge>\<^sub>a l')"
  by (auto simp: subset_eq intro: order_trans)

lemma Icc_subset_Iic_iff[simp]: 
  "{l\<le>\<^sub>a..\<le>\<^sub>ah} \<subseteq> {..\<le>\<^sub>ah'} = (\<not> l \<le>\<^sub>a h \<or> h \<le>\<^sub>a h')"
  unfolding interval_def ray_def by (blast intro: order_trans)+

lemma not_Ici_eq_empty[simp]: "{l\<le>\<^sub>a..} \<noteq> {}" by (auto simp: set_eq_iff)

lemmas not_empty_eq_Ici_eq_empty[simp] = not_Ici_eq_empty[symmetric]

lemma Iio_Int_singleton: "{..<\<^sub>ak} \<inter> {x} = (if x <\<^sub>a k then {x} else {})" by simp

lemma ivl_disj_int_one:
  "{..\<le>\<^sub>al} \<inter> {l<\<^sub>a..<\<^sub>au} = {}"
  "{..<\<^sub>al} \<inter> {l\<le>\<^sub>a..<\<^sub>au} = {}"
  "{..\<le>\<^sub>al} \<inter> {l<\<^sub>a..\<le>\<^sub>au} = {}"
  "{..<\<^sub>al} \<inter> {l\<le>\<^sub>a..\<le>\<^sub>au} = {}"
  "{l<\<^sub>a..\<le>\<^sub>au} \<inter> {u<\<^sub>a..} = {}"
  "{l<\<^sub>a..<\<^sub>au} \<inter> {u\<le>\<^sub>a..} = {}"
  "{l\<le>\<^sub>a..\<le>\<^sub>au} \<inter> {u<\<^sub>a..} = {}"
  "{l\<le>\<^sub>a..<\<^sub>au} \<inter> {u\<le>\<^sub>a..} = {}"
  using lessThan_iff dual.lessThan_iff by (auto simp: less_le_not_le)

lemma ivl_disj_int_two:
  "{l<\<^sub>a..<\<^sub>am} \<inter> {m\<le>\<^sub>a..<\<^sub>au} = {}"
  "{l<\<^sub>a..\<le>\<^sub>am} \<inter> {m<\<^sub>a..<\<^sub>au} = {}"
  "{l\<le>\<^sub>a..<\<^sub>am} \<inter> {m\<le>\<^sub>a..<\<^sub>au} = {}"
  "{l\<le>\<^sub>a..\<le>\<^sub>am} \<inter> {m<\<^sub>a..<\<^sub>au} = {}"
  "{l<\<^sub>a..<\<^sub>am} \<inter> {m\<le>\<^sub>a..\<le>\<^sub>au} = {}"
  "{l<\<^sub>a..\<le>\<^sub>am} \<inter> {m<\<^sub>a..\<le>\<^sub>au} = {}"
  "{l\<le>\<^sub>a..<\<^sub>am} \<inter> {m\<le>\<^sub>a..\<le>\<^sub>au} = {}"
  "{l\<le>\<^sub>a..\<le>\<^sub>am} \<inter> {m<\<^sub>a..\<le>\<^sub>au} = {}"
  using lessThan_iff by (auto simp: less_le_not_le)

end

context order
begin     

interpretation ord_syntax .

interpretation order_dual le ls
  by (rule order_dual.intro[OF order_axioms])

lemma atMost_Int_atLeast: "{..\<le>\<^sub>an} \<inter> {n\<le>\<^sub>a..} = {n}"
  unfolding ray_def by (auto simp: eq_iff)

lemma atLeast_eq_iff[iff]: "({x\<le>\<^sub>a..} = {y\<le>\<^sub>a..}) = (x = y)" 
  unfolding ray_def using antisym by auto

lemma atLeastLessThan_eq_atLeastAtMost_diff: "{a\<le>\<^sub>a..<\<^sub>ab} = {a\<le>\<^sub>a..\<le>\<^sub>ab} - {b}"
  unfolding interval_def ray_def by (auto simp: less_imp_le le_less)

lemma greaterThanAtMost_eq_atLeastAtMost_diff: "{a<\<^sub>a..\<le>\<^sub>ab} = {a\<le>\<^sub>a..\<le>\<^sub>ab} - {a}"
  unfolding interval_def ray_def by (auto simp: less_imp_le le_less)

lemma atLeastAtMost_singleton[simp]: "{a\<le>\<^sub>a..\<le>\<^sub>aa} = {a}"
  using atMost_Int_atLeast by (fastforce simp: ray_def) 

lemma atLeastAtMost_singleton': 
  assumes "a = b"
  shows "{a\<le>\<^sub>a..\<le>\<^sub>ab} = {a}" 
  using assms by simp

lemma Icc_eq_Icc[simp]:
  "{l\<le>\<^sub>a..\<le>\<^sub>ah} = {l'\<le>\<^sub>a..\<le>\<^sub>ah'} = (l = l' \<and> h = h' \<or> \<not> l \<le>\<^sub>a h \<and> \<not> l' \<le>\<^sub>a h')"
  apply(rule iffI)
  subgoal by (metis antisym atLeastatMost_subset_iff eq_refl)
  subgoal using atLeastatMost_empty_iff by blast
  done

lemma atLeastAtMost_singleton_iff[simp]: "{a\<le>\<^sub>a..\<le>\<^sub>ab} = {c} \<longleftrightarrow> a = b \<and> b = c"
proof
  assume "{a\<le>\<^sub>a..\<le>\<^sub>ab} = {c}"
  hence *: "\<not> (\<not> a \<le>\<^sub>a b)" unfolding atLeastatMost_empty_iff[symmetric] by simp
  with \<open>{a\<le>\<^sub>a..\<le>\<^sub>ab} = {c}\<close> have "c \<le>\<^sub>a a \<and> b \<le>\<^sub>a c" by auto
  with * show "a = b \<and> b = c" by (auto intro: antisym order_trans) 
qed simp

end

context order_extremum
begin

interpretation ord_syntax .

lemma atMost_eq_UNIV_iff: "{..\<le>\<^sub>ax} = UNIV \<longleftrightarrow> x = extremum"
  by (metis ord.lessThan_iff eq_iff UNIV_I UNIV_eq_I extremum)

end

context no_extremum
begin

interpretation ord_syntax .

interpretation order_dual le ls
  by (rule order_dual.intro[OF order_axioms])

lemma not_UNIV_le_Icc[simp]: "\<not> UNIV \<subseteq> {l\<le>\<^sub>a..\<le>\<^sub>ah}"
  using gt_ex[of h] by (auto simp: subset_eq less_le_not_le)

lemma not_UNIV_le_Iic[simp]: "\<not> UNIV \<subseteq> {..\<le>\<^sub>ah}"
  using gt_ex[of h] by (auto simp: less_le_not_le)

lemma not_Ici_le_Icc[simp]: "\<not> {l\<le>\<^sub>a..} \<subseteq> {l'\<le>\<^sub>a..\<le>\<^sub>ah'}"
  using gt_ex[of h']
  by (auto simp: subset_eq less_le) 
    (blast dest: antisym_conv intro: order_trans)

lemma not_Ici_le_Iic[simp]: "\<not> {l\<le>\<^sub>a..} \<subseteq> {..\<le>\<^sub>ah'}"
proof
  assume "{l\<le>\<^sub>a..} \<subseteq> {..\<le>\<^sub>ah'}"
  then have x: "l \<le>\<^sub>a x \<Longrightarrow> x \<le>\<^sub>a h'" for x by auto
  from gt_ex obtain x where "h' <\<^sub>a x" by auto
  show False
  proof(cases \<open>l \<le>\<^sub>a x\<close>)
    case True show ?thesis 
      using x[OF True] less_le_not_le by (force simp: \<open>h' <\<^sub>a x\<close>)
  next
    case False
    obtain y where "x \<le>\<^sub>a y" and "y <\<^sub>a l"
      using \<open>h' <\<^sub>a x\<close> dual.less_le_trans by (blast intro: x less_imp_le)
    then have "x <\<^sub>a l" by (rule le_less_trans)
    then show ?thesis 
      using \<open>h' <\<^sub>a x\<close> less_le_not_le by (blast intro: x dual.less_trans)
  qed
qed

lemma not_UNIV_eq_Icc[simp]: "UNIV \<noteq> {l'\<le>\<^sub>a..\<le>\<^sub>ah'}"
  using gt_ex by (auto simp: set_eq_iff less_le_not_le)
  
lemmas not_Icc_eq_UNIV[simp] = not_UNIV_eq_Icc[symmetric]

lemma not_UNIV_eq_Iic[simp]: "UNIV \<noteq> {..\<le>\<^sub>ah'}"
  using gt_ex[of h'] not_UNIV_le_Iic by blast

lemmas not_Iic_eq_UNIV[simp] = not_UNIV_eq_Iic[symmetric]

lemma not_Icc_eq_Ici[simp]: "{l\<le>\<^sub>a..\<le>\<^sub>ah} \<noteq> {l'\<le>\<^sub>a..}"
  using not_Ici_le_Icc by blast

lemmas not_Ici_eq_Icc[simp] = not_Icc_eq_Ici[symmetric]

lemma not_Iic_eq_Ici[simp]: "{..\<le>\<^sub>ah} \<noteq> {l'\<le>\<^sub>a..}"
  using not_Ici_le_Iic[of l' h] by blast

lemmas not_Ici_eq_Iic[simp] = not_Iic_eq_Ici[symmetric]

lemma greaterThan_non_empty[simp]: "{x<\<^sub>a..} \<noteq> {}"
  using gt_ex[of x] unfolding ray_def by simp

end

context order
begin

interpretation ord_syntax .
interpretation order_pair le ls le ls ..
interpretation ord_pair_syntax le ls le ls .

lemma mono_image_least:
  assumes f_mono: "mono\<^sub>a\<^sub>b f" 
    and f_img: "f ` {m\<le>\<^sub>a..<\<^sub>an} = {m'\<le>\<^sub>a..<\<^sub>an'}" 
    and "m <\<^sub>a n"
  shows "f m = m'"
proof -
  from f_img have "{m'\<le>\<^sub>a..<\<^sub>an'} \<noteq> {}" by (force simp: assms(3))
  with f_img have "m' \<in> f ` {m\<le>\<^sub>a..<\<^sub>an}" by auto
  then obtain k where "f k = m'" "m \<le>\<^sub>a k" by auto
  moreover have "m' \<le>\<^sub>a f m" 
    unfolding interval_def using f_img by (auto simp: assms(3))
  ultimately show "f m = m'"
    using f_mono by (auto dest: monoD intro: antisym)
qed

end



subsection\<open>Bounded sets\<close>

definition bdd :: "['a set, ['a, 'a] \<Rightarrow> bool, 'a set] \<Rightarrow> bool"
  (\<open>(on _ with _ : \<guillemotleft>bdd\<guillemotright> _)\<close> [1000, 1000, 1000] 10) 
  where "bdd U op A \<longleftrightarrow> (\<exists>M\<in>U. \<forall>x \<in> A. op x M)"

ctr parametricity
  in bdd_def

context ord_syntax  
begin

abbreviation bdd_above where "bdd_above \<equiv> bdd UNIV (\<le>\<^sub>a)"
abbreviation bdd_below where "bdd_below \<equiv> bdd UNIV (\<ge>\<^sub>a)"

end

context preorder
begin

interpretation ord_syntax .

interpretation preorder_dual ..

lemma bdd_aboveI[intro]: 
  assumes "\<And>x. x \<in> A \<Longrightarrow> x \<le>\<^sub>a M"
  shows "bdd_above A"
  using assms unfolding bdd_def by auto

lemma bdd_belowI[intro]: 
  assumes "\<And>x. x \<in> A \<Longrightarrow> m \<le>\<^sub>a x"
  shows "bdd_below A"
  using assms unfolding bdd_def by auto

lemma bdd_aboveI2: 
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le>\<^sub>a M"
  shows "bdd_above (f ` A)" 
  using assms by force

lemma bdd_belowI2: 
  assumes "\<And>x. x \<in> A \<Longrightarrow> m \<le>\<^sub>a f x"
  shows "bdd_below (f ` A)" 
  using assms by force

lemma bdd_above_empty[simp, intro]: "bdd_above {}"
  unfolding bdd_above_def by auto

lemma bdd_below_empty[simp, intro]: "bdd_below {}"
  unfolding bdd_below_def by auto

lemma bdd_above_mono: 
  assumes "bdd_above B" and "A \<subseteq> B" 
  shows "bdd_above A"
  using assms unfolding bdd_def by auto

lemma bdd_below_mono: 
  assumes "bdd_below B" and "A \<subseteq> B"
  shows "bdd_below A"
  using assms unfolding bdd_def by auto

lemma bdd_above_Int1[simp]: 
  assumes "bdd_above A"
  shows "bdd_above (A \<inter> B)"
  using assms by (auto simp: bdd_above_mono)

lemma bdd_above_Int2[simp]: 
  assumes "bdd_above B"
  shows "bdd_above (A \<inter> B)"
  using assms by (auto simp: bdd_above_mono)

lemma bdd_below_Int1[simp]: 
  assumes "bdd_below A"
  shows "bdd_below (A \<inter> B)"
  using assms by (auto simp: bdd_below_mono)

lemma bdd_below_Int2[simp]: 
  assumes "bdd_below B"
  shows "bdd_below (A \<inter> B)"
  using assms by (auto simp: bdd_below_mono)

lemma bdd_above_Ioo[simp, intro]: "bdd_above {a<\<^sub>a..<\<^sub>ab}" 
  by (auto intro!: less_imp_le)

lemma bdd_above_Ico[simp, intro]: "bdd_above {a\<le>\<^sub>a..<\<^sub>ab}" 
  by (auto intro!: less_imp_le)

lemma bdd_above_Iio[simp, intro]: "bdd_above {..<\<^sub>ab}"
  by (auto intro: less_imp_le)

lemma bdd_above_Ioc[simp, intro]: "bdd_above {a<\<^sub>a..\<le>\<^sub>ab}" by auto

lemma bdd_above_Icc[simp, intro]: "bdd_above {a\<le>\<^sub>a..\<le>\<^sub>ab}"
  by (auto intro: less_imp_le)

lemma bdd_above_Iic[simp, intro]: "bdd_above {..\<le>\<^sub>ab}"
  by (auto intro: less_imp_le)

lemma bdd_below_Ioo[simp, intro]: "bdd_below {a<\<^sub>a..<\<^sub>ab}"
  by (auto intro!: less_imp_le)

lemma bdd_below_Ioc[simp, intro]: "bdd_below {a<\<^sub>a..\<le>\<^sub>ab}"
  by (auto intro!: less_imp_le)

lemma bdd_below_Ioi[simp, intro]: "bdd_below {a<\<^sub>a..}"
  by (auto intro: less_imp_le)

lemma bdd_below_Ico[simp, intro]: "bdd_below {a\<le>\<^sub>a..<\<^sub>ab}" by auto

lemma bdd_below_Icc[simp, intro]: "bdd_below {a\<le>\<^sub>a..\<le>\<^sub>ab}" by auto

lemma bdd_below_Ici[simp, intro]: "bdd_below {a\<le>\<^sub>a..}"
  by (auto intro: less_imp_le)

end

context order_pair
begin

interpretation ord_pair_syntax .

lemma bdd_above_image_mono: 
  assumes "mono\<^sub>a\<^sub>b f" and "ord\<^sub>a.bdd_above A"
  shows "ord\<^sub>b.bdd_above (f ` A)"
  using assms by (auto simp: bdd_def mono_def)

lemma bdd_below_image_mono: 
  assumes "mono\<^sub>a\<^sub>b f" and "ord\<^sub>a.bdd_below A" 
  shows "ord\<^sub>b.bdd_below (f ` A)"
  using assms by (auto simp: bdd_def mono_def)

lemma bdd_above_image_antimono:
  assumes "antimono\<^sub>a\<^sub>b f" and "ord\<^sub>a.bdd_below A" 
  shows "ord\<^sub>b.bdd_above (f ` A)"
  using assms by (auto simp: bdd_def mono_def)

lemma bdd_below_image_antimono: 
  assumes "antimono\<^sub>a\<^sub>b f" and "ord\<^sub>a.bdd_above A"   
  shows "ord\<^sub>b.bdd_below (f ` A)"
  using assms by (auto simp: bdd_def mono_def)

end

context order_extremum
begin

interpretation ord_syntax .
interpretation order_dual ..

lemma bdd_above_top[simp, intro!]: "bdd_above A"
  by (rule bdd_aboveI[of _ extremum]) simp

end

text\<open>\newpage\<close>

end