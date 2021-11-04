(* Title: Examples/TTS_Foundations/Orders/Set_Simple_Orders.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Abstract orders on explicit sets\<close>
theory Set_Simple_Orders
  imports 
    Type_Simple_Orders 
    "../Foundations/FNDS_Set_Ext"
begin



subsection\<open>Background\<close>


text\<open>
Some of the results presented in this section were ported 
(with amendments and additions) from the theories \<^text>\<open>Orderings\<close> 
and \<^text>\<open>Set_Interval\<close> in the main library of Isabelle/HOL.
\<close>



subsection\<open>Order operations\<close>

locale ord_ow =
  fixes U :: "'a set" and le ls :: "['a, 'a] \<Rightarrow> bool" 
begin

tts_register_sbts le | U
proof-
  assume "Domainp AB = (\<lambda>x. x \<in> U)" "bi_unique AB" "right_total AB" 
  from tts_AA_eq_transfer[OF this] show ?thesis by auto
qed

tts_register_sbts ls | U
proof-
  assume "Domainp AB = (\<lambda>x. x \<in> U)" "bi_unique AB" "right_total AB" 
  from tts_AA_eq_transfer[OF this] show ?thesis by auto
qed

end

locale ord_syntax_ow = ord_ow U le ls
  for U :: "'a set" and le ls :: "['a, 'a] \<Rightarrow> bool" 
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

abbreviation Least where "Least \<equiv> Type_Simple_Orders.Least U (\<le>\<^sub>a)"
abbreviation Greatest where "Greatest \<equiv> Type_Simple_Orders.Least U (\<ge>\<^sub>a)"

abbreviation min where "min \<equiv> Type_Simple_Orders.min (\<le>\<^sub>a)"
abbreviation max where "max \<equiv> Type_Simple_Orders.min (\<ge>\<^sub>a)"

abbreviation lessThan (\<open>{..<\<^sub>a_}\<close>) where "{..<\<^sub>au} \<equiv> on U with (<\<^sub>a) : {..\<sqsubset>u}"
abbreviation atMost (\<open>{..\<le>\<^sub>a_}\<close>) where "{..\<le>\<^sub>au} \<equiv> on U with (\<le>\<^sub>a) : {..\<sqsubset>u}"
abbreviation greaterThan (\<open>{_<\<^sub>a..}\<close>) where "{l<\<^sub>a..} \<equiv> on U with (>\<^sub>a) : {..\<sqsubset>l}"
abbreviation atLeast (\<open>{_\<le>\<^sub>a..}\<close>) where "{l\<le>\<^sub>a..} \<equiv> on U with (\<ge>\<^sub>a) : {..\<sqsubset>l}"
abbreviation greaterThanLessThan (\<open>{_<\<^sub>a..<\<^sub>a_}\<close>) 
  where "{l<\<^sub>a..<\<^sub>au} \<equiv> on U with (<\<^sub>a) (<\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation atLeastLessThan (\<open>{_\<le>\<^sub>a..<\<^sub>a_}\<close>) 
  where "{l\<le>\<^sub>a..<\<^sub>au} \<equiv> on U with (\<le>\<^sub>a) (<\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation greaterThanAtMost (\<open>{_<\<^sub>a..\<le>\<^sub>a_}\<close>) 
  where "{l<\<^sub>a..\<le>\<^sub>au} \<equiv> on U with (<\<^sub>a) (\<le>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation atLeastAtMost (\<open>{_\<le>\<^sub>a..\<le>\<^sub>a_}\<close>) 
  where "{l\<le>\<^sub>a..\<le>\<^sub>au} \<equiv> on U with (\<le>\<^sub>a) (\<le>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation lessThanGreaterThan (\<open>{_>\<^sub>a..>\<^sub>a_}\<close>) 
  where "{l>\<^sub>a..>\<^sub>au} \<equiv> on U with (>\<^sub>a) (>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation lessThanAtLeast (\<open>{_\<ge>\<^sub>a..>\<^sub>a_}\<close>) 
  where "{l\<ge>\<^sub>a..>\<^sub>au} \<equiv> on U with (\<ge>\<^sub>a) (>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation atMostGreaterThan (\<open>{_>\<^sub>a..\<ge>\<^sub>a_}\<close>) 
  where "{l>\<^sub>a..\<ge>\<^sub>au} \<equiv> on U with (>\<^sub>a) (\<ge>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"
abbreviation atMostAtLeast (\<open>{_\<ge>\<^sub>a..\<ge>\<^sub>a_}\<close>) 
  where "{l\<ge>\<^sub>a..\<ge>\<^sub>au} \<equiv> on U with (\<ge>\<^sub>a) (\<ge>\<^sub>a) : {l\<sqsubset>..\<sqsubset>u}"

abbreviation bdd_above where "bdd_above \<equiv> bdd U (\<le>\<^sub>a)"
abbreviation bdd_below where "bdd_below \<equiv> bdd U (\<ge>\<^sub>a)"

end

locale ord_dual_ow = ord_syntax_ow U le ls
  for U :: "'a set" and le ls :: "['a, 'a] \<Rightarrow> bool"
begin

sublocale dual: ord_ow U ge gt .

end

locale ord_pair_ow = ord\<^sub>a: ord_ow U\<^sub>a le\<^sub>a ls\<^sub>a + ord\<^sub>b: ord_ow U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale rev: ord_pair_ow U\<^sub>b le\<^sub>b ls\<^sub>b U\<^sub>a le\<^sub>a ls\<^sub>a .

end

locale ord_pair_syntax_ow = ord_pair_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale ord\<^sub>a: ord_syntax_ow U\<^sub>a le\<^sub>a ls\<^sub>a + ord\<^sub>b: ord_syntax_ow U\<^sub>b le\<^sub>b ls\<^sub>b .

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

abbreviation mono\<^sub>a\<^sub>b 
  where "mono\<^sub>a\<^sub>b \<equiv> Type_Simple_Orders.mono U\<^sub>a (\<le>\<^sub>a) (\<le>\<^sub>b)"
abbreviation mono\<^sub>b\<^sub>a 
  where "mono\<^sub>b\<^sub>a \<equiv> Type_Simple_Orders.mono U\<^sub>b (\<le>\<^sub>b) (\<le>\<^sub>a)"
abbreviation antimono\<^sub>a\<^sub>b 
  where "antimono\<^sub>a\<^sub>b \<equiv> Type_Simple_Orders.mono U\<^sub>a (\<le>\<^sub>a) (\<ge>\<^sub>b)"
abbreviation antimono\<^sub>b\<^sub>a 
  where "antimono\<^sub>b\<^sub>a \<equiv> Type_Simple_Orders.mono U\<^sub>b (\<le>\<^sub>b) (\<ge>\<^sub>a)"
abbreviation strict_mono\<^sub>a\<^sub>b 
  where "strict_mono\<^sub>a\<^sub>b \<equiv> Type_Simple_Orders.mono U\<^sub>a (<\<^sub>a) (<\<^sub>b)"
abbreviation strict_mono\<^sub>b\<^sub>a 
  where "strict_mono\<^sub>b\<^sub>a \<equiv> Type_Simple_Orders.mono U\<^sub>b (<\<^sub>b) (<\<^sub>a)"
abbreviation strict_antimono\<^sub>a\<^sub>b 
  where "strict_antimono\<^sub>a\<^sub>b \<equiv> Type_Simple_Orders.mono U\<^sub>a (<\<^sub>a) (>\<^sub>b)"
abbreviation strict_antimono\<^sub>b\<^sub>a 
  where "strict_antimono\<^sub>b\<^sub>a \<equiv> Type_Simple_Orders.mono U\<^sub>b (<\<^sub>b) (>\<^sub>a)"

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

locale ord_pair_dual_ow = ord_pair_syntax_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b

context ord_pair_dual_ow
begin

sublocale ord_dual: ord_pair_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> .
sublocale dual_ord: ord_pair_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> .
sublocale dual_dual: ord_pair_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> .

end


subsubsection\<open>Relativization\<close>

context ord_ow
begin

interpretation ord_syntax_ow .

tts_context
  tts: (?'a to U)
  sbterms: (\<open>?ls::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to ls)
  rewriting ctr_simps
  eliminating through auto
begin

tts_lemma lessThan_iff:
  assumes "i \<in> U" and "k \<in> U"
  shows "(i \<in> {..<\<^sub>ak}) = (i <\<^sub>a k)"
    is ord.lessThan_iff.
    
tts_lemma greaterThanLessThan_iff:
  assumes "i \<in> U" and "l \<in> U" and "u \<in> U"
  shows "(i \<in> {l<\<^sub>a..<\<^sub>au}) = (i <\<^sub>a u \<and> l <\<^sub>a i)"
  is ord.greaterThanLessThan_iff.
    
tts_lemma greaterThanLessThan_eq:
  assumes "a \<in> U" and "b \<in> U"
  shows "{a<\<^sub>a..<\<^sub>ab} = {a<\<^sub>a..} \<inter> {..<\<^sub>ab}"
    is ord.greaterThanLessThan_eq.

end

tts_context
  tts: (?'a to U)
  sbterms: (\<open>?le::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to le)
  rewriting ctr_simps
  eliminating through auto
begin

tts_lemma min_absorb1:
  assumes "x \<in> U" and "y \<in> U" and "x \<le>\<^sub>a y"
  shows "min x y = x"
  is ord.min_absorb1.
    
tts_lemma atLeast_iff:
  assumes "i \<in> U" and "k \<in> U"
  shows "(i \<in> {k\<le>\<^sub>a..}) = (k \<le>\<^sub>a i)"
  is ord.atLeast_iff.

tts_lemma atLeastAtMost_iff:
  assumes "i \<in> U" and "l \<in> U" and "u \<in> U"
  shows "(i \<in> {l\<le>\<^sub>a..\<le>\<^sub>au}) = (i \<le>\<^sub>a u \<and> l \<le>\<^sub>a i)"
  is ord.atLeastAtMost_iff.

end

tts_context
  tts: (?'a to U)
  sbterms: (\<open>?le::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to le)
    and (\<open>?ls::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to ls)
   rewriting ctr_simps
 eliminating through auto
begin

tts_lemma atLeastLessThan_iff:
  assumes "i \<in> U" and "l \<in> U" and "u \<in> U"
  shows "(i \<in> {l\<le>\<^sub>a..<\<^sub>au}) = (l \<le>\<^sub>a i \<and> i <\<^sub>a u)"
    is ord.atLeastLessThan_iff.
    
tts_lemma greaterThanAtMost_iff:
  assumes "i \<in> U" and "l \<in> U" and "u \<in> U"
  shows "(i \<in> {l<\<^sub>a..\<le>\<^sub>au}) = (i \<le>\<^sub>a u \<and> l <\<^sub>a i)"
  is ord.greaterThanAtMost_iff.

end

end

context ord_pair_ow
begin

interpretation ord_pair_syntax_ow .

tts_context
  tts: (?'a to U\<^sub>a) and (?'b to U\<^sub>b)
  sbterms: (\<open>?le\<^sub>a::?'a\<Rightarrow>?'a\<Rightarrow>bool\<close> to le\<^sub>a) and (\<open>?le\<^sub>b::?'b\<Rightarrow>?'b\<Rightarrow>bool\<close> to le\<^sub>b)
  rewriting ctr_simps
  eliminating through (simp add: Type_Simple_Orders.mono_def)
begin

tts_lemma monoD:
  assumes "x \<in> U\<^sub>a" and "y \<in> U\<^sub>a" and "mono\<^sub>a\<^sub>b f" and "x \<le>\<^sub>a y"
  shows "f x \<le>\<^sub>b f y"
  is ord_pair.monoD.
    
tts_lemma monoI:
  assumes "\<And>x y. \<lbrakk>x \<in> U\<^sub>a; y \<in> U\<^sub>a; x \<le>\<^sub>a y\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>b f y"
  shows "mono\<^sub>a\<^sub>b f"
    is ord_pair.monoI.
    
tts_lemma monoE:
  assumes "x \<in> U\<^sub>a"
    and "y \<in> U\<^sub>a"
    and "mono\<^sub>a\<^sub>b f"
    and "x \<le>\<^sub>a y"
    and "f x \<le>\<^sub>b f y \<Longrightarrow> thesis"
  shows thesis
    is ord_pair.monoE.

end

tts_context
  tts: (?'a to U\<^sub>a) and (?'b to U\<^sub>b)
  sbterms: (\<open>?ls\<^sub>a::?'a\<Rightarrow>?'a\<Rightarrow>bool\<close> to le\<^sub>a) and (\<open>?ls\<^sub>b::?'b\<Rightarrow>?'b\<Rightarrow>bool\<close> to le\<^sub>b)
  rewriting ctr_simps
  eliminating through (simp add: Type_Simple_Orders.mono_def)
begin

tts_lemma strict_monoD:
  assumes "x \<in> U\<^sub>a"
    and "y \<in> U\<^sub>a"
    and "mono\<^sub>a\<^sub>b f"
    and "x \<le>\<^sub>a y"
  shows "f x \<le>\<^sub>b f y"
    is ord_pair.strict_monoD.
    
tts_lemma strict_monoI:
  assumes "\<And>x y. \<lbrakk>x \<in> U\<^sub>a; y \<in> U\<^sub>a; x \<le>\<^sub>a y\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>b f y"
  shows "mono\<^sub>a\<^sub>b f"
    is ord_pair.strict_monoI.
    
tts_lemma strict_monoE:
  assumes "x \<in> U\<^sub>a"
    and "y \<in> U\<^sub>a"
    and "mono\<^sub>a\<^sub>b f"
    and "x \<le>\<^sub>a y"
    and "f x \<le>\<^sub>b f y \<Longrightarrow> thesis"
  shows thesis
    is ord_pair.strict_monoE.

end

end



subsection\<open>Preorders\<close>


subsubsection\<open>Definitions and common properties\<close>

locale preorder_ow = ord_ow U le ls 
  for U :: "'a set" and le ls +
  assumes less_le_not_le: "\<lbrakk> x \<in> U; y \<in> U \<rbrakk> \<Longrightarrow> ls x y \<longleftrightarrow> le x y \<and> \<not> (le y x)"
    and order_refl[iff]: "x \<in> U \<Longrightarrow> le x x"
    and order_trans: "\<lbrakk> x \<in> U; y \<in> U; z \<in> U; le x y; le y z \<rbrakk> \<Longrightarrow> le x z"

locale preorder_dual_ow = preorder_ow U le ls for U :: "'a set" and le ls
begin

sublocale ord_dual_ow .

sublocale dual: preorder_ow U ge gt 
  by standard (auto simp: less_le_not_le intro: order_trans)

end

locale ord_preorder_ow = 
  ord_pair_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>b: preorder_ow U\<^sub>b le\<^sub>b ls\<^sub>b 
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b

locale ord_preorder_dual_ow = ord_preorder_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale ord_pair_dual_ow .
sublocale ord_dual: ord_preorder_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by unfold_locales (auto simp: ord\<^sub>b.less_le_not_le intro: ord\<^sub>b.order_trans)
sublocale dual_ord: ord_preorder_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by (rule ord_preorder_ow_axioms)
sublocale dual_dual: ord_preorder_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by (rule ord_dual.ord_preorder_ow_axioms)

end

locale preorder_pair_ow = 
  ord_preorder_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>a: preorder_ow U\<^sub>a le\<^sub>a ls\<^sub>a
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale rev: preorder_pair_ow U\<^sub>b le\<^sub>b ls\<^sub>b U\<^sub>a le\<^sub>a ls\<^sub>a ..

end

locale preorder_pair_dual_ow = preorder_pair_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale ord_preorder_dual_ow ..
sublocale ord_dual: preorder_pair_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: preorder_pair_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by unfold_locales (auto intro: ord\<^sub>a.order_trans simp: ord\<^sub>a.less_le_not_le)
sublocale dual_dual: preorder_pair_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end


subsubsection\<open>Transfer rules\<close>

lemma preorder_ow[ud_with]: "preorder = preorder_ow UNIV"
  unfolding preorder_def preorder_ow_def by simp

lemma ord_preorder_ow[ud_with]: "ord_preorder = ord_preorder_ow UNIV"
  unfolding ord_preorder_def ord_preorder_ow_def ud_with by simp

lemma preorder_pair_ow[ud_with]: 
  "preorder_pair = 
    (\<lambda>le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b. preorder_pair_ow UNIV le\<^sub>a ls\<^sub>a UNIV le\<^sub>b ls\<^sub>b)"
  unfolding preorder_pair_def preorder_pair_ow_def ud_with by simp

context
  includes lifting_syntax
begin

lemma preorder_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A"
  shows 
    "(rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      preorder_ow preorder_ow"
  by (ow_locale_transfer locale_defs: preorder_ow_def)

lemma ord_preorder_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A"
  shows 
    "(rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      ord_preorder_ow ord_preorder_ow"
  by (ow_locale_transfer locale_defs: ord_preorder_ow_def)

lemma preorder_pair_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> 
      rel_set B ===> (B ===> B ===> (=)) ===> (B ===> B ===> (=)) ===> 
      (=)
    ) preorder_pair_ow preorder_pair_ow"
  by (ow_locale_transfer locale_defs: preorder_pair_ow_def)

end


subsubsection\<open>Relativization\<close>

context preorder_ow
begin

interpretation ord_syntax_ow .

tts_context
  tts: (?'a to U) 
  sbterms: (\<open>?ls::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to ls)
    and (\<open>?le::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to le)
  rewriting ctr_simps
  substituting preorder_ow_axioms
  eliminating through auto
begin

tts_lemma less_irrefl:
  assumes "x \<in> U"
  shows "\<not> x <\<^sub>a x"
    is preorder.less_irrefl.

tts_lemma eq_refl:
  assumes "y \<in> U" and "x = y"
  shows "x \<le>\<^sub>a y"
  is preorder.eq_refl.

tts_lemma less_imp_le:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>a y"
  shows "x \<le>\<^sub>a y"
    is preorder.less_imp_le.

tts_lemma strict_implies_not_eq:
  assumes "b \<in> U" and "a <\<^sub>a b"
  shows "a \<noteq> b"
    is preorder.strict_implies_not_eq.

tts_lemma less_not_sym:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>a y"
  shows "\<not> y <\<^sub>a x"
    is preorder.less_not_sym.

tts_lemma not_empty_eq_Ici_eq_empty:
  assumes "l \<in> U"
  shows "{} \<noteq> {l\<le>\<^sub>a..}"
    is preorder.not_empty_eq_Ici_eq_empty.

tts_lemma not_Ici_eq_empty:
  assumes "l \<in> U"
  shows "{l\<le>\<^sub>a..} \<noteq> {}"
    is preorder.not_Ici_eq_empty.

tts_lemma asym:
  assumes "a \<in> U" and "b \<in> U" and "a <\<^sub>a b" and "b <\<^sub>a a"
  shows False
    is preorder.asym.

tts_lemma less_asym':
  assumes "a \<in> U" and "b \<in> U" and "a <\<^sub>a b" and "b <\<^sub>a a"
  shows P
    is preorder.less_asym'.

tts_lemma less_imp_not_less:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>a y"
  shows "(\<not> y <\<^sub>a x) = True"
    is preorder.less_imp_not_less.

tts_lemma single_Diff_lessThan:
  assumes "k \<in> U"
  shows "{k} - {..<\<^sub>ak} = {k}"
    is preorder.single_Diff_lessThan.

tts_lemma less_imp_triv:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>a y"
  shows "(y <\<^sub>a x \<longrightarrow> P) = True"
    is preorder.less_imp_triv.

tts_lemma ivl_disj_int_one:
  assumes "l \<in> U" and "u \<in> U"
  shows 
    "{..\<le>\<^sub>al} \<inter> {l<\<^sub>a..<\<^sub>au} = {}"
    "{..<\<^sub>al} \<inter> {l\<le>\<^sub>a..<\<^sub>au} = {}"
    "{..\<le>\<^sub>al} \<inter> {l<\<^sub>a..\<le>\<^sub>au} = {}"
    "{..<\<^sub>al} \<inter> {l\<le>\<^sub>a..\<le>\<^sub>au} = {}"
    "{l<\<^sub>a..\<le>\<^sub>au} \<inter> {u<\<^sub>a..} = {}"
    "{l<\<^sub>a..<\<^sub>au} \<inter> {u\<le>\<^sub>a..} = {}"
    "{l\<le>\<^sub>a..\<le>\<^sub>au} \<inter> {u<\<^sub>a..} = {}"
    "{l\<le>\<^sub>a..<\<^sub>au} \<inter> {u\<le>\<^sub>a..} = {}"
    is preorder.ivl_disj_int_one.

tts_lemma atLeastatMost_empty_iff2:
  assumes "a \<in> U" and "b \<in> U"
  shows "({} = {a\<le>\<^sub>a..\<le>\<^sub>ab}) = (\<not> a \<le>\<^sub>a b)"
    is preorder.atLeastatMost_empty_iff2.

tts_lemma atLeastLessThan_empty_iff2:
  assumes "a \<in> U" and "b \<in> U"
  shows "({} = {a\<le>\<^sub>a..<\<^sub>ab}) = (\<not> a <\<^sub>a b)"
    is preorder.atLeastLessThan_empty_iff2.

tts_lemma greaterThanAtMost_empty_iff2:
  assumes "k \<in> U" and "l \<in> U"
  shows "({} = {k<\<^sub>a..\<le>\<^sub>al}) = (\<not> k <\<^sub>a l)"
    is preorder.greaterThanAtMost_empty_iff2.

tts_lemma atLeastatMost_empty_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "({a\<le>\<^sub>a..\<le>\<^sub>ab} = {}) = (\<not> a \<le>\<^sub>a b)"
    is preorder.atLeastatMost_empty_iff.

tts_lemma atLeastLessThan_empty_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "({a\<le>\<^sub>a..<\<^sub>ab} = {}) = (\<not> a <\<^sub>a b)"
    is preorder.atLeastLessThan_empty_iff.

tts_lemma greaterThanAtMost_empty_iff:
  assumes "k \<in> U" and "l \<in> U"
  shows "({k<\<^sub>a..\<le>\<^sub>al} = {}) = (\<not> k <\<^sub>a l)"
    is preorder.greaterThanAtMost_empty_iff.

tts_lemma atLeastLessThan_empty:
  assumes "b \<in> U" and "a \<in> U" and "b \<le>\<^sub>a a"
  shows "{a\<le>\<^sub>a..<\<^sub>ab} = {}"
    is preorder.atLeastLessThan_empty.

tts_lemma greaterThanAtMost_empty:
  assumes "l \<in> U" and "k \<in> U" and "l \<le>\<^sub>a k"
  shows "{k<\<^sub>a..\<le>\<^sub>al} = {}"
    is preorder.greaterThanAtMost_empty.

tts_lemma greaterThanLessThan_empty:
  assumes "l \<in> U" and "k \<in> U" and "l \<le>\<^sub>a k"
  shows "{k<\<^sub>a..<\<^sub>al} = {}"
    is preorder.greaterThanLessThan_empty.

tts_lemma le_less_trans:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U" and "x \<le>\<^sub>a y" and "y <\<^sub>a z"
  shows "x <\<^sub>a z"
    is preorder.le_less_trans.

tts_lemma atLeastatMost_empty:
  assumes "b \<in> U" and "a \<in> U" and "b <\<^sub>a a"
  shows "{a\<le>\<^sub>a..\<le>\<^sub>ab} = {}"
    is preorder.atLeastatMost_empty.

tts_lemma less_le_trans:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U" and "x <\<^sub>a y" and "y \<le>\<^sub>a z"
  shows "x <\<^sub>a z"
    is preorder.less_le_trans.

tts_lemma less_trans:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U" and "x <\<^sub>a y" and "y <\<^sub>a z"
  shows "x <\<^sub>a z"
    is preorder.less_trans.

tts_lemma ivl_disj_int_two:
  assumes "l \<in> U" and "m \<in> U" and "u \<in> U"
  shows 
    "{l<\<^sub>a..<\<^sub>am} \<inter> {m\<le>\<^sub>a..<\<^sub>au} = {}"
    "{l<\<^sub>a..\<le>\<^sub>am} \<inter> {m<\<^sub>a..<\<^sub>au} = {}"
    "{l\<le>\<^sub>a..<\<^sub>am} \<inter> {m\<le>\<^sub>a..<\<^sub>au} = {}"
    "{l\<le>\<^sub>a..\<le>\<^sub>am} \<inter> {m<\<^sub>a..<\<^sub>au} = {}"
    "{l<\<^sub>a..<\<^sub>am} \<inter> {m\<le>\<^sub>a..\<le>\<^sub>au} = {}"
    "{l<\<^sub>a..\<le>\<^sub>am} \<inter> {m<\<^sub>a..\<le>\<^sub>au} = {}"
    "{l\<le>\<^sub>a..<\<^sub>am} \<inter> {m\<le>\<^sub>a..\<le>\<^sub>au} = {}"
    "{l\<le>\<^sub>a..\<le>\<^sub>am} \<inter> {m<\<^sub>a..\<le>\<^sub>au} = {}"
    is preorder.ivl_disj_int_two.

tts_lemma less_asym:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>a y" and "\<not> P \<Longrightarrow> y <\<^sub>a x"
  shows P
    is preorder.less_asym.

tts_lemma Iio_Int_singleton:
  assumes "k \<in> U" and "x \<in> U"
  shows "{..<\<^sub>ak} \<inter> {x} = (if x <\<^sub>a k then {x} else {})"
    is preorder.Iio_Int_singleton.

tts_lemma Ioi_le_Ico:
  assumes "a \<in> U"
  shows "{a<\<^sub>a..} \<subseteq> {a\<le>\<^sub>a..}"
    is preorder.Ioi_le_Ico.

tts_lemma Icc_subset_Iic_iff:
  assumes "l \<in> U" and "h \<in> U" and "h' \<in> U"
  shows "({l\<le>\<^sub>a..\<le>\<^sub>ah} \<subseteq> {..\<le>\<^sub>ah'}) = (\<not> l \<le>\<^sub>a h \<or> h \<le>\<^sub>a h')"
    is preorder.Icc_subset_Iic_iff.

tts_lemma atLeast_subset_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "({x\<le>\<^sub>a..} \<subseteq> {y\<le>\<^sub>a..}) = (y \<le>\<^sub>a x)"
    is preorder.atLeast_subset_iff.

tts_lemma Icc_subset_Ici_iff:
  assumes "l \<in> U" and "h \<in> U" and "l' \<in> U"
  shows "({l\<le>\<^sub>a..\<le>\<^sub>ah} \<subseteq> {l'\<le>\<^sub>a..}) = (\<not> l \<le>\<^sub>a h \<or> l' \<le>\<^sub>a l)"
    is preorder.Icc_subset_Ici_iff.

tts_lemma atLeastatMost_subset_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a\<le>\<^sub>a..\<le>\<^sub>ab} \<subseteq> {c\<le>\<^sub>a..\<le>\<^sub>ad}) = (\<not> a \<le>\<^sub>a b \<or> b \<le>\<^sub>a d \<and> c \<le>\<^sub>a a)"
    is preorder.atLeastatMost_subset_iff.

tts_lemma atLeastatMost_psubset_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a\<le>\<^sub>a..\<le>\<^sub>ab} \<subset> {c\<le>\<^sub>a..\<le>\<^sub>ad}) = 
    (c \<le>\<^sub>a d \<and> (\<not> a \<le>\<^sub>a b \<or> c \<le>\<^sub>a a \<and> b \<le>\<^sub>a d \<and> (c <\<^sub>a a \<or> b <\<^sub>a d)))"
    is preorder.atLeastatMost_psubset_iff.

tts_lemma bdd_above_empty:
  assumes "U \<noteq> {}"
  shows "bdd_above {}"
    is preorder.bdd_above_empty.

tts_lemma bdd_above_Iic:
  assumes "b \<in> U"
  shows "bdd_above {..\<le>\<^sub>ab}"
    is preorder.bdd_above_Iic.

tts_lemma bdd_above_Iio:
  assumes "b \<in> U"
  shows "bdd_above {..<\<^sub>ab}"
    is preorder.bdd_above_Iio.

tts_lemma bdd_below_empty:
  assumes "U \<noteq> {}"
  shows "bdd_below {}"
    is preorder.bdd_below_empty.

tts_lemma bdd_above_Icc:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_above {a\<le>\<^sub>a..\<le>\<^sub>ab}"
    is preorder.bdd_above_Icc.

tts_lemma bdd_above_Ico:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_above {a\<le>\<^sub>a..<\<^sub>ab}"
    is preorder.bdd_above_Ico.

tts_lemma bdd_above_Ioc:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_above {a<\<^sub>a..\<le>\<^sub>ab}"
    is preorder.bdd_above_Ioc.

tts_lemma bdd_above_Ioo:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_above {a<\<^sub>a..<\<^sub>ab}"
    is preorder.bdd_above_Ioo.

tts_lemma bdd_above_Int1:
  assumes "A \<subseteq> U" and "B \<subseteq> U" and "bdd_above A"
  shows "bdd_above (A \<inter> B)"
    is preorder.bdd_above_Int1.

tts_lemma bdd_above_Int2:
  assumes "B \<subseteq> U" and "A \<subseteq> U" and "bdd_above B"
  shows "bdd_above (A \<inter> B)"
    is preorder.bdd_above_Int2.

tts_lemma bdd_below_Icc:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_below {a\<le>\<^sub>a..\<le>\<^sub>ab}"
    is preorder.bdd_below_Icc.

tts_lemma bdd_below_Ico:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_below {a\<le>\<^sub>a..<\<^sub>ab}"
    is preorder.bdd_below_Ico.

tts_lemma bdd_below_Ioc:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_below {a<\<^sub>a..\<le>\<^sub>ab}"
    is preorder.bdd_below_Ioc.

tts_lemma bdd_below_Ioo:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_below {a<\<^sub>a..<\<^sub>ab}"
    is preorder.bdd_below_Ioo.

tts_lemma bdd_below_Ici:
  assumes "a \<in> U"
  shows "bdd_below {a\<le>\<^sub>a..}"
    is preorder.bdd_below_Ici.

tts_lemma bdd_below_Ioi:
  assumes "a \<in> U"
  shows "bdd_below {a<\<^sub>a..}"
    is preorder.bdd_below_Ioi.

tts_lemma bdd_above_mono:
  assumes "B \<subseteq> U" and "bdd_above B" and "A \<subseteq> B"
  shows "bdd_above A"
    is preorder.bdd_above_mono.

tts_lemma bdd_aboveI:
  assumes "A \<subseteq> U" and "M \<in> U" and "\<And>x. \<lbrakk>x \<in> U; x \<in> A\<rbrakk> \<Longrightarrow> x \<le>\<^sub>a M"
  shows "bdd_above A"
    is preorder.bdd_aboveI.

tts_lemma bdd_aboveI2:
  assumes "range f \<subseteq> U" and "M \<in> U" and "\<And>x. x \<in> A \<Longrightarrow> f x \<le>\<^sub>a M"
  shows "bdd_above (f ` A)"
    is preorder.bdd_aboveI2.

tts_lemma bdd_below_Int1:
  assumes "A \<subseteq> U" and "B \<subseteq> U" and "bdd_below A" 
  shows "bdd_below (A \<inter> B)"
    is preorder.bdd_below_Int1.

tts_lemma bdd_below_Int2:
  assumes "B \<subseteq> U" and "A \<subseteq> U" and "bdd_below B"
  shows "bdd_below (A \<inter> B)"
    is preorder.bdd_below_Int2.

tts_lemma bdd_belowI:
  assumes "A \<subseteq> U" and "m \<in> U" and "\<And>x. \<lbrakk>x \<in> U; x \<in> A\<rbrakk> \<Longrightarrow> m \<le>\<^sub>a x"
  shows "bdd_below A"
    is preorder.bdd_belowI.

tts_lemma bdd_below_mono:
  assumes "B \<subseteq> U" and "bdd_below B" and "A \<subseteq> B"
  shows "bdd_below A"
    is preorder.bdd_below_mono.

tts_lemma bdd_belowI2:
  assumes "m \<in> U" and "range f \<subseteq> U" and "\<And>x. x \<in> A \<Longrightarrow> m \<le>\<^sub>a f x"
  shows "bdd_below (f ` A)"
    is preorder.bdd_belowI2[where 'b='d].

end
    
end



subsection\<open>Partial orders\<close>

locale order_ow = preorder_ow U le ls 
  for U :: "'a set" and le ls +
  assumes antisym: "x \<in> U \<Longrightarrow> y \<in> U \<Longrightarrow> le x y \<Longrightarrow> le y x \<Longrightarrow> x = y"

locale order_dual_ow = order_ow U le ls 
  for U :: "'a set" and le ls
begin

sublocale preorder_dual_ow ..

sublocale dual: order_ow U ge gt 
  unfolding order_ow_def order_ow_axioms_def
  apply unfold_locales
  apply(rule conjI)
  subgoal by (rule dual.preorder_ow_axioms)
  subgoal by (simp add: antisym)
  done

end

locale ord_order_ow = 
  ord_preorder_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>b: order_ow U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b

locale ord_order_dual_ow = ord_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale ord_preorder_dual_ow ..
sublocale ord_dual: ord_order_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by unfold_locales (simp add: ord\<^sub>b.antisym)
sublocale dual_ord: ord_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by (rule ord_order_ow_axioms)
sublocale dual_dual: ord_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by (rule ord_dual.ord_order_ow_axioms)

end

locale preorder_order_ow = 
  ord_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>a: preorder_ow U\<^sub>a le\<^sub>a ls\<^sub>a
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale preorder_pair_ow ..

end

locale preorder_order_dual_ow = preorder_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale ord_order_dual_ow ..
sublocale preorder_pair_dual_ow ..
sublocale ord_dual: preorder_order_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> .. 
sublocale dual_ord: preorder_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> .. 
sublocale dual_dual: preorder_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end

locale order_pair_ow = 
  preorder_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>a: order_ow U\<^sub>a le\<^sub>a ls\<^sub>a
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale rev: order_pair_ow U\<^sub>b le\<^sub>b ls\<^sub>b U\<^sub>a le\<^sub>a ls\<^sub>a ..

end

locale order_pair_dual_ow = order_pair_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale preorder_order_dual_ow ..
sublocale ord_dual: order_pair_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: order_pair_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by unfold_locales (simp add: ord\<^sub>a.antisym)
sublocale dual_dual: order_pair_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end


subsubsection\<open>Transfer rules\<close>

lemma order_ow[ud_with]: "order = order_ow UNIV"
  unfolding 
    order_def order_ow_def order_axioms_def order_ow_axioms_def ud_with 
  by simp

lemma ord_order_ow[ud_with]: "ord_order = ord_order_ow UNIV"
  unfolding ord_order_def ord_order_ow_def ud_with by simp

lemma preorder_order_ow[ud_with]: 
  "preorder_order = 
    (\<lambda>le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b. preorder_order_ow UNIV le\<^sub>a ls\<^sub>a UNIV le\<^sub>b ls\<^sub>b)"
  unfolding preorder_order_def preorder_order_ow_def ud_with by simp

lemma order_pair_ow[ud_with]: 
  "order_pair = (\<lambda>le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b. order_pair_ow UNIV le\<^sub>a ls\<^sub>a UNIV le\<^sub>b ls\<^sub>b)"
  unfolding order_pair_def order_pair_ow_def ud_with by simp

context
  includes lifting_syntax
begin

lemma order_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "(rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      order_ow order_ow"
  by (ow_locale_transfer locale_defs: order_ow_def order_ow_axioms_def)

lemma ord_order_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===>
      (=)
    ) ord_order_ow ord_order_ow"
  by (ow_locale_transfer locale_defs: ord_order_ow_def)

lemma preorder_order_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> 
      rel_set B ===> (B ===> B ===> (=)) ===> (B ===> B ===> (=)) ===> 
      (=)
    ) preorder_order_ow preorder_order_ow"
  by (ow_locale_transfer locale_defs: preorder_order_ow_def)

lemma order_pair_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: 
    "bi_unique A" "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> 
      rel_set B ===> (B ===> B ===> (=)) ===> (B ===> B ===> (=)) ===> 
      (=)
    ) order_pair_ow order_pair_ow"
  by (ow_locale_transfer locale_defs: order_pair_ow_def)

end


subsubsection\<open>Relativization\<close>

context order_ow
begin

interpretation ord_syntax_ow .

tts_context
  tts: (?'a to U)
  sbterms: (\<open>?ls::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to ls)
    and (\<open>?le::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to le)
  rewriting ctr_simps
  substituting order_ow_axioms
  eliminating through auto
begin

tts_lemma atLeastAtMost_singleton:
  assumes "a \<in> U"
  shows "{a\<le>\<^sub>a..\<le>\<^sub>aa} = {a}"
  is order.atLeastAtMost_singleton.
    
tts_lemma less_imp_not_eq:
  assumes "y \<in> U" and "x <\<^sub>a y"
  shows "(x = y) = False"
  is order.less_imp_not_eq.
    
tts_lemma less_imp_not_eq2:
  assumes "y \<in> U" and "x <\<^sub>a y"
  shows "(y = x) = False"
    is order.less_imp_not_eq2.

tts_lemma eq_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x = y) = (x \<le>\<^sub>a y \<and> y \<le>\<^sub>a x)"
    is order.eq_iff.

tts_lemma le_less:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x \<le>\<^sub>a y) = (x <\<^sub>a y \<or> x = y)"
    is order.le_less.

tts_lemma min_absorb2:
  assumes "y \<in> U" and "x \<in> U" and "y \<le>\<^sub>a x"
  shows "min x y = y"
    is order.min_absorb2.

tts_lemma less_le:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x <\<^sub>a y) = (x \<le>\<^sub>a y \<and> x \<noteq> y)"
    is order.less_le.

tts_lemma le_imp_less_or_eq:
  assumes "x \<in> U" and "y \<in> U" and "x \<le>\<^sub>a y"
  shows "x <\<^sub>a y \<or> x = y"
    is order.le_imp_less_or_eq.

tts_lemma antisym_conv:
  assumes "y \<in> U" and "x \<in> U" and "y \<le>\<^sub>a x"
  shows "(x \<le>\<^sub>a y) = (x = y)"
    is order.antisym_conv.

tts_lemma le_neq_trans:
  assumes "a \<in> U" and "b \<in> U" and "a \<le>\<^sub>a b" and "a \<noteq> b"
  shows "a <\<^sub>a b"
    is order.le_neq_trans.

tts_lemma neq_le_trans:
  assumes "a \<in> U" and "b \<in> U" and "a \<noteq> b" and "a \<le>\<^sub>a b"
  shows "a <\<^sub>a b"
    is order.neq_le_trans.

tts_lemma atLeastAtMost_singleton':
  assumes "b \<in> U" and "a = b"
  shows "{a\<le>\<^sub>a..\<le>\<^sub>ab} = {a}"
    is order.atLeastAtMost_singleton'.

tts_lemma atLeastLessThan_eq_atLeastAtMost_diff:
  assumes "a \<in> U" and "b \<in> U"
  shows "{a\<le>\<^sub>a..<\<^sub>ab} = {a\<le>\<^sub>a..\<le>\<^sub>ab} - {b}"
    is order.atLeastLessThan_eq_atLeastAtMost_diff.

tts_lemma greaterThanAtMost_eq_atLeastAtMost_diff:
  assumes "a \<in> U" and "b \<in> U"
  shows "{a<\<^sub>a..\<le>\<^sub>ab} = {a\<le>\<^sub>a..\<le>\<^sub>ab} - {a}"
    is order.greaterThanAtMost_eq_atLeastAtMost_diff.

tts_lemma atMost_Int_atLeast:
  assumes "n \<in> U"
  shows "{..\<le>\<^sub>an} \<inter> {n\<le>\<^sub>a..} = {n}"
    is order.atMost_Int_atLeast.

tts_lemma atLeast_eq_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "({x\<le>\<^sub>a..} = {y\<le>\<^sub>a..}) = (x = y)"
    is order.atLeast_eq_iff.

tts_lemma Least_equality:
  assumes "x \<in> U" and "P x" 
    and "\<And>y. \<lbrakk>y \<in> U; P y\<rbrakk> \<Longrightarrow> x \<le>\<^sub>a y"
  shows "Least P = Some x"
    is order.Least_equality.

tts_lemma Icc_eq_Icc:
  assumes "l \<in> U" and "h \<in> U" and "l' \<in> U" and "h' \<in> U"
  shows "({l\<le>\<^sub>a..\<le>\<^sub>ah} = {l'\<le>\<^sub>a..\<le>\<^sub>ah'}) = 
    (h = h' \<and> l = l' \<or> \<not> l' \<le>\<^sub>a h' \<and> \<not> l \<le>\<^sub>a h)"
    is order.Icc_eq_Icc.

tts_lemma LeastI2_order:
  assumes "x \<in> U"
    and "P x"
    and "\<And>y. \<lbrakk>y \<in> U; P y\<rbrakk> \<Longrightarrow> x \<le>\<^sub>a y"
    and "\<And>x. \<lbrakk>x \<in> U; P x; \<forall>y\<in>U. P y \<longrightarrow> x \<le>\<^sub>a y\<rbrakk> \<Longrightarrow> Q x"
    and "\<And>z. \<lbrakk>z \<in> U; Least P = Some z; Q z\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is order.LeastI2_order.

tts_lemma mono_image_least:
  assumes "\<forall>x\<in>U. f x \<in> U"
    and "m \<in> U"
    and "n \<in> U"
    and "m' \<in> U"
    and "n' \<in> U"
    and "on U with (\<le>\<^sub>a) (\<le>\<^sub>a) : \<guillemotleft>mono\<guillemotright> f"
    and "f ` {m\<le>\<^sub>a..<\<^sub>an} = {m'\<le>\<^sub>a..<\<^sub>an'}"
    and "m <\<^sub>a n"
  shows "f m = m'"
    is order.mono_image_least.

tts_lemma antisym_conv1:
  assumes "x \<in> U" and "y \<in> U" and "\<not> x <\<^sub>a y"
  shows "(x \<le>\<^sub>a y) = (x = y)"
    is order.antisym_conv1.

tts_lemma antisym_conv2:
  assumes "x \<in> U" and "y \<in> U" and "x \<le>\<^sub>a y"
  shows "(\<not> x <\<^sub>a y) = (x = y)"
    is order.antisym_conv2.

tts_lemma leD:
  assumes "y \<in> U" and "x \<in> U" and "y \<le>\<^sub>a x"
  shows "\<not> x <\<^sub>a y"
    is order.leD.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting order_ow_axioms
  eliminating \<open>?A \<noteq> {}\<close> through auto
begin

tts_lemma atLeastAtMost_singleton_iff:
  assumes "a \<in> U"
    and "b \<in> U"
    and "c \<in> U"
  shows "({a\<le>\<^sub>a..\<le>\<^sub>ab} = {c}) = (a = b \<and> b = c)"
    is order.atLeastAtMost_singleton_iff.

end

tts_context
  tts: (?'a to U)
  sbterms: (\<open>?ls::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to ls)
    and (\<open>?le::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to le)
  rewriting ctr_simps
  substituting order_ow_axioms
  eliminating through auto
begin

tts_lemma Least_ex1:
  assumes "z \<in> U"
    and "\<exists>!x. x \<in> U \<and> P x \<and> (\<forall>y\<in>U. P y \<longrightarrow> x \<le>\<^sub>a y)"
    and "\<And>x. \<lbrakk>x \<in> U; Least P = Some x; P x; P z \<Longrightarrow> x \<le>\<^sub>a z\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is order.Least_ex1.
    
end    

end

context order_pair_ow
begin

interpretation ord_pair_syntax_ow .

tts_context
  tts: (?'a to U\<^sub>a) and (?'b to U\<^sub>b)
  sbterms: (\<open>?ls\<^sub>a::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to ls\<^sub>a)
    and (\<open>?le\<^sub>a::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to le\<^sub>a)
    and (\<open>?ls\<^sub>b::?'b \<Rightarrow> ?'b \<Rightarrow> bool\<close> to ls\<^sub>b)
    and (\<open>?le\<^sub>b::?'b \<Rightarrow> ?'b \<Rightarrow> bool\<close> to le\<^sub>b)
  rewriting ctr_simps
  substituting order_pair_ow_axioms
  eliminating through (auto simp: mono_def bdd_def)
begin

tts_lemma strict_mono_mono:
  assumes "\<forall>x\<in>U\<^sub>a. f x \<in> U\<^sub>b" and "strict_mono\<^sub>a\<^sub>b f"
  shows "mono\<^sub>a\<^sub>b f"
    is order_pair.strict_mono_mono.

tts_lemma bdd_above_image_mono:
  assumes "\<forall>x\<in>U\<^sub>a. f x \<in> U\<^sub>b" and "A \<subseteq> U\<^sub>a" and "mono\<^sub>a\<^sub>b f" and "ord\<^sub>a.bdd_above A"
  shows "ord\<^sub>b.bdd_above (f ` A)"
    is order_pair.bdd_above_image_mono.

tts_lemma bdd_below_image_mono:
  assumes "\<forall>x\<in>U\<^sub>a. f x \<in> U\<^sub>b" and "A \<subseteq> U\<^sub>a" and "mono\<^sub>a\<^sub>b f" and "ord\<^sub>a.bdd_below A"
  shows "ord\<^sub>b.bdd_below (f ` A)"
    is order_pair.bdd_below_image_mono.

tts_lemma bdd_below_image_antimono:
  assumes "\<forall>x\<in>U\<^sub>a. f x \<in> U\<^sub>b" 
    and "A \<subseteq> U\<^sub>a" 
    and "antimono\<^sub>a\<^sub>b f" 
    and "ord\<^sub>a.bdd_above A"
  shows "ord\<^sub>b.bdd_below (f ` A)"
    is order_pair.bdd_below_image_antimono.

tts_lemma bdd_above_image_antimono:
  assumes "\<forall>x\<in>U\<^sub>a. f x \<in> U\<^sub>b"
    and "A \<subseteq> U\<^sub>a"
    and "antimono\<^sub>a\<^sub>b f"
    and "ord\<^sub>a.bdd_below A"
  shows "ord\<^sub>b.bdd_above (f ` A)"
    is order_pair.bdd_above_image_antimono.

end

end



subsection\<open>Dense orders\<close>


subsubsection\<open>Definitions and common properties\<close>

locale dense_order_ow = order_ow U le ls
  for U :: "'a set" and le ls +
  assumes dense: "\<lbrakk> x \<in> U; y \<in> U; ls x y \<rbrakk> \<Longrightarrow> (\<exists>z\<in>U. ls x z \<and> ls z y)"

locale dense_order_dual_ow = dense_order_ow U le ls
  for U :: "'a set" and le ls
begin

interpretation ord_syntax_ow .

sublocale order_dual_ow ..

sublocale dual: dense_order_ow U ge gt 
  using dense by unfold_locales auto

end

locale ord_dense_order_ow = 
  ord_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>b: dense_order_ow U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b

locale ord_dense_order_dual_ow = ord_dense_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b  
begin

sublocale ord_order_dual_ow ..
sublocale ord_dual: ord_dense_order_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  using ord\<^sub>b.dense by unfold_locales blast
sublocale dual_ord: ord_dense_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  by (rule ord_dense_order_ow_axioms)
sublocale dual_dual: ord_dense_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close>
  by (rule ord_dual.ord_dense_order_ow_axioms)

end

locale preorder_dense_order_ow = 
  ord_dense_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>a: preorder_ow U\<^sub>a le\<^sub>a ls\<^sub>a
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale preorder_order_ow ..

end

locale preorder_dense_order_dual_ow = 
  preorder_dense_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale ord_dense_order_dual_ow ..
sublocale preorder_order_dual_ow ..
sublocale ord_dual: preorder_dense_order_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> 
  ..
sublocale dual_ord: preorder_dense_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  ..    
sublocale dual_dual: preorder_dense_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> 
  ..

end

locale order_dense_order_ow = 
  preorder_dense_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>a: order_ow U\<^sub>a le\<^sub>a ls\<^sub>a
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale order_pair_ow ..

end

locale order_dense_order_dual_ow = order_dense_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale preorder_dense_order_dual_ow ..
sublocale order_pair_dual_ow ..
sublocale ord_dual: order_dense_order_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: order_dense_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> ..    
sublocale dual_dual: order_dense_order_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end

locale dense_order_pair_ow = 
  order_dense_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b + ord\<^sub>a: dense_order_ow U\<^sub>a le\<^sub>a ls\<^sub>a
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b

locale dense_order_pair_dual_ow = dense_order_pair_ow U\<^sub>a le\<^sub>a ls\<^sub>a U\<^sub>b le\<^sub>b ls\<^sub>b
  for U\<^sub>a :: "'a set" and le\<^sub>a ls\<^sub>a and U\<^sub>b :: "'b set" and le\<^sub>b ls\<^sub>b
begin

sublocale order_dense_order_dual_ow ..
sublocale ord_dual: dense_order_pair_ow U\<^sub>a \<open>(\<le>\<^sub>a)\<close> \<open>(<\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..
sublocale dual_ord: dense_order_pair_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<le>\<^sub>b)\<close> \<open>(<\<^sub>b)\<close> 
  using ord\<^sub>a.dense by unfold_locales auto
sublocale dual_dual: dense_order_pair_ow U\<^sub>a \<open>(\<ge>\<^sub>a)\<close> \<open>(>\<^sub>a)\<close> U\<^sub>b \<open>(\<ge>\<^sub>b)\<close> \<open>(>\<^sub>b)\<close> ..

end


subsubsection\<open>Transfer rules\<close>

lemma dense_order_ow[ud_with]: "dense_order = dense_order_ow UNIV"
  unfolding 
    dense_order_def dense_order_ow_def 
    dense_order_axioms_def dense_order_ow_axioms_def 
    ud_with 
  by simp

lemma ord_dense_order_ow[ud_with]: "ord_dense_order = ord_dense_order_ow UNIV"
  unfolding ord_dense_order_def ord_dense_order_ow_def ud_with by simp

lemma preorder_dense_order_ow[ud_with]: 
  "preorder_dense_order = 
    (\<lambda>le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b. preorder_dense_order_ow UNIV le\<^sub>a ls\<^sub>a UNIV le\<^sub>b ls\<^sub>b)"
  unfolding preorder_dense_order_def preorder_dense_order_ow_def ud_with 
  by simp

lemma order_dense_order_ow[ud_with]: 
  "order_dense_order = 
    (\<lambda>le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b. order_dense_order_ow UNIV le\<^sub>a ls\<^sub>a UNIV le\<^sub>b ls\<^sub>b)"
  unfolding order_dense_order_def order_dense_order_ow_def ud_with by simp

lemma dense_order_pair_ow[ud_with]: 
  "dense_order_pair = 
    (\<lambda>le\<^sub>a ls\<^sub>a le\<^sub>b ls\<^sub>b. dense_order_pair_ow UNIV le\<^sub>a ls\<^sub>a UNIV le\<^sub>b ls\<^sub>b)"
  unfolding dense_order_pair_def dense_order_pair_ow_def ud_with by simp

context
  includes lifting_syntax
begin

lemma desne_order_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "(rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      dense_order_ow dense_order_ow"
  by 
    (
      ow_locale_transfer locale_defs: 
        dense_order_ow_def dense_order_ow_axioms_def
    )

lemma ord_dense_order_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===>
      (=)
    ) ord_dense_order_ow ord_dense_order_ow"
  by (ow_locale_transfer locale_defs: ord_dense_order_ow_def)

lemma preorder_dense_order_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> 
      rel_set B ===> (B ===> B ===> (=)) ===> (B ===> B ===> (=)) ===> 
      (=)
    ) preorder_dense_order_ow preorder_dense_order_ow"
  by (ow_locale_transfer locale_defs: preorder_dense_order_ow_def)

lemma order_dense_order_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: 
    "bi_unique A" "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> 
      rel_set B ===> (B ===> B ===> (=)) ===> (B ===> B ===> (=)) ===> 
      (=)
    ) order_dense_order_ow order_dense_order_ow"
  by (ow_locale_transfer locale_defs: order_dense_order_ow_def)

lemma dense_order_pair_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: 
    "bi_unique A" "right_total A" "bi_unique B" "right_total B"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> 
      rel_set B ===> (B ===> B ===> (=)) ===> (B ===> B ===> (=)) ===> 
      (=)
    ) dense_order_pair_ow dense_order_pair_ow"
  by (ow_locale_transfer locale_defs: dense_order_pair_ow_def)

end



subsection\<open>(Unique) top and bottom elements\<close>

locale extremum_ow =
  fixes U :: "'a set" and extremum 
  assumes extremum_closed[simp]: "extremum \<in> U"

locale bot_ow = extremum_ow U bot for U :: "'a set" and bot
begin

notation bot ("\<bottom>")

end

locale top_ow = extremum_ow U top for U :: "'a set" and top
begin

notation top ("\<top>")

end

locale ord_extremum_ow = ord_ow U le ls + extremum_ow U extremum 
  for U :: "'a set" and le ls extremum

locale order_extremum_ow = ord_extremum_ow U le ls extremum + order_ow U le ls
  for U :: "'a set" and le ls extremum +
  assumes extremum[simp]: "a \<in> U \<Longrightarrow> le a extremum"

locale order_bot_ow = 
  order_dual_ow U le ls + dual: order_extremum_ow U ge gt bot + bot_ow U bot 
  for U :: "'a set" and le ls bot

locale order_top = 
  order_dual_ow U le ls + order_extremum_ow U le ls top + top_ow U top
  for U :: "'a set" and le ls top


subsubsection\<open>Transfer rules\<close>

lemma order_extremum_ow[ud_with]: "order_extremum = order_extremum_ow UNIV"
  unfolding 
    order_extremum_def order_extremum_axioms_def 
    order_extremum_ow_def order_extremum_ow_axioms_def
    ord_extremum_ow_def extremum_ow_def
    ud_with 
  by simp

context
  includes lifting_syntax
begin

lemma extremum_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(rel_set A ===> A ===> (=)) extremum_ow extremum_ow"
  by (ow_locale_transfer locale_defs: extremum_ow_def)

lemma ord_extremum_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(rel_set A ===> A ===> (=)) ord_extremum_ow ord_extremum_ow"
  by (ow_locale_transfer locale_defs: ord_extremum_ow_def)

lemma order_extremum_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "(
      rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> A ===> 
      (=)
    ) order_extremum_ow order_extremum_ow"
  by 
    (
      ow_locale_transfer locale_defs: 
        order_extremum_ow_def order_extremum_ow_axioms_def
    )

end


subsubsection\<open>Relativization\<close>

context order_extremum_ow
begin

interpretation ord_syntax_ow .

tts_context
  tts: (?'a to U)
  sbterms: (\<open>?le::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to le)
    and (\<open>?ls::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to ls)
  rewriting ctr_simps
  substituting order_extremum_ow_axioms
  eliminating through force
begin

tts_lemma extremum_strict:
  assumes "a \<in> U"
  shows "\<not> extremum <\<^sub>a a"
    is order_extremum.extremum_strict.
    
tts_lemma bdd_above_top:
  assumes "A \<subseteq> U"
  shows "bdd_above A"
    is order_extremum.bdd_above_top.
    
tts_lemma min_top:
  assumes "x \<in> U"
  shows "min extremum x = x"
  is order_extremum.min_top.

tts_lemma min_top2:
  assumes "x \<in> U"
  shows "min x extremum = x"
  is order_extremum.min_top2.
    
tts_lemma extremum_unique:
  assumes "a \<in> U"
  shows "(extremum \<le>\<^sub>a a) = (a = extremum)"
is order_extremum.extremum_unique.
    
tts_lemma not_eq_extremum:
  assumes "a \<in> U"
  shows "(a \<noteq> extremum) = (a <\<^sub>a extremum)"
  is order_extremum.not_eq_extremum.
    
tts_lemma extremum_uniqueI:
  assumes "a \<in> U" and "extremum \<le>\<^sub>a a"
  shows "a = extremum"
    is order_extremum.extremum_uniqueI.
    
tts_lemma max_top:
  assumes "x \<in> U"
  shows "max extremum x = extremum"
    is order_extremum.max_top.

tts_lemma max_top2:
  assumes "x \<in> U"
  shows "max x extremum = extremum"
    is order_extremum.max_top2.

tts_lemma atMost_eq_UNIV_iff:
  assumes "x \<in> U"
  shows "({..\<le>\<^sub>ax} = U) = (x = extremum)"
    is order_extremum.atMost_eq_UNIV_iff.

end

end



subsection\<open>Absence of top or bottom elements\<close>

locale no_extremum_ow = order_ow U le ls for U :: "'a set" and le ls +
  assumes gt_ex: "x \<in> U \<Longrightarrow> \<exists>y\<in>U. ls x y"

locale no_top_ow = order_dual_ow U le ls + no_extremum_ow U le ls 
  for U :: "'a set" and le ls

locale no_bot_ow = order_dual_ow U le ls + dual: no_extremum_ow U ge gt 
  for U :: "'a set" and le ls

subsubsection\<open>Transfer rules\<close>

lemma no_extremum_ow[ud_with]: "no_extremum = no_extremum_ow UNIV"
  unfolding 
    no_extremum_def no_extremum_ow_def 
    no_extremum_axioms_def no_extremum_ow_axioms_def
    ud_with
  by simp

context
  includes lifting_syntax
begin

lemma no_extremum_ow_axioms_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "(rel_set A ===> (A ===> A ===> (=)) ===> (=)) 
      no_extremum_ow_axioms no_extremum_ow_axioms"
  by (ow_locale_transfer locale_defs:  no_extremum_ow_axioms_def)

lemma no_extremum_ow_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "(rel_set A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      no_extremum_ow no_extremum_ow"
  by (ow_locale_transfer locale_defs: no_extremum_ow_def)

end


subsubsection\<open>Relativization\<close>

lemma right_total_UNIV_transfer'[transfer_rule]: 
  assumes "right_total A" and "Domainp A = (\<lambda>x. x \<in> U)"
  shows "rel_set A U UNIV"
  using assms right_total_UNIV_transfer by fastforce

context no_extremum_ow
begin

interpretation ord_syntax_ow .

tts_context
  tts: (?'a to U)
  sbterms: (\<open>?le::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to le)
    and (\<open>?ls::?'a \<Rightarrow> ?'a \<Rightarrow> bool\<close> to ls)
  rewriting ctr_simps
  substituting no_extremum_ow_axioms
  eliminating through force
begin

tts_lemma not_UNIV_eq_Iic:
  assumes "h' \<in> U"
  shows "U \<noteq> {..\<le>\<^sub>ah'}"
  is no_extremum.not_UNIV_eq_Iic.

tts_lemma not_Iic_eq_UNIV:
  assumes "h' \<in> U"
  shows "{..\<le>\<^sub>ah'} \<noteq> U"
    is no_extremum.not_Iic_eq_UNIV.

tts_lemma not_UNIV_le_Iic:
  assumes "h \<in> U"
  shows "\<not> U \<subseteq> {..\<le>\<^sub>ah}"
    is no_extremum.not_UNIV_le_Iic.

tts_lemma not_UNIV_eq_Icc:
  assumes "l' \<in> U" and "h' \<in> U"
  shows "U \<noteq> {l'\<le>\<^sub>a..\<le>\<^sub>ah'}"
    is no_extremum.not_UNIV_eq_Icc.

tts_lemma not_Icc_eq_UNIV:
  assumes "l' \<in> U" and "h' \<in> U"
  shows "{l'\<le>\<^sub>a..\<le>\<^sub>ah'} \<noteq> U"
    is no_extremum.not_Icc_eq_UNIV.

tts_lemma not_UNIV_le_Icc:
  assumes "l \<in> U" and "h \<in> U"
  shows "\<not> U \<subseteq> {l\<le>\<^sub>a..\<le>\<^sub>ah}"
    is no_extremum.not_UNIV_le_Icc.

tts_lemma greaterThan_non_empty:
  assumes "x \<in> U"
  shows "{x<\<^sub>a..} \<noteq> {}"
    is no_extremum.greaterThan_non_empty.

tts_lemma not_Iic_eq_Ici:
  assumes "h \<in> U" and "l' \<in> U"
  shows "{..\<le>\<^sub>ah} \<noteq> {l'\<le>\<^sub>a..}"
    is no_extremum.not_Iic_eq_Ici.

tts_lemma not_Ici_eq_Iic:
  assumes "l' \<in> U" and "h \<in> U"
  shows "{l'\<le>\<^sub>a..} \<noteq> {..\<le>\<^sub>ah}"
    is no_extremum.not_Ici_eq_Iic.

tts_lemma not_Ici_le_Iic:
  assumes "l \<in> U" and "h' \<in> U"
  shows "\<not> {l\<le>\<^sub>a..} \<subseteq> {..\<le>\<^sub>ah'}"
    is no_extremum.not_Ici_le_Iic.

tts_lemma not_Icc_eq_Ici:
  assumes "l \<in> U" and "h \<in> U" and "l' \<in> U"
  shows "{l\<le>\<^sub>a..\<le>\<^sub>ah} \<noteq> {l'\<le>\<^sub>a..}"
    is no_extremum.not_Icc_eq_Ici.

tts_lemma not_Ici_eq_Icc:
  assumes "l' \<in> U" and "l \<in> U" and "h \<in> U"
  shows "{l'\<le>\<^sub>a..} \<noteq> {l\<le>\<^sub>a..\<le>\<^sub>ah}"
    is no_extremum.not_Ici_eq_Icc.

tts_lemma not_Ici_le_Icc:
  assumes "l \<in> U" and "l' \<in> U" and "h' \<in> U"
  shows "\<not> {l\<le>\<^sub>a..} \<subseteq> {l'\<le>\<^sub>a..\<le>\<^sub>ah'}"
    is no_extremum.not_Ici_le_Icc.

end

end

declare right_total_UNIV_transfer'[transfer_rule del]

text\<open>\newpage\<close>

end