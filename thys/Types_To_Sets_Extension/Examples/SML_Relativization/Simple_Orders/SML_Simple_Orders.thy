(* Title: Examples/SML_Relativization/Simple_Orders/SML_Simple_Orders.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about orders\<close>
theory SML_Simple_Orders
  imports 
    "../../Introduction"
    "../Foundations/SML_Relations"
    Complex_Main
begin



subsection\<open>Class \<^class>\<open>ord\<close>\<close>


subsubsection\<open>Definitions and common properties\<close>

locale ord_ow =
  fixes U :: "'ao set"
    and le :: "['ao, 'ao] \<Rightarrow> bool" (infix \<open>\<le>\<^sub>o\<^sub>w\<close> 50) 
    and ls :: "['ao, 'ao] \<Rightarrow> bool" (infix \<open><\<^sub>o\<^sub>w\<close> 50)
begin

notation le (\<open>'(\<le>\<^sub>o\<^sub>w')\<close>)
  and le (infix \<open>\<le>\<^sub>o\<^sub>w\<close> 50) 
  and ls (\<open>'(<\<^sub>o\<^sub>w')\<close>) 
  and ls (infix \<open><\<^sub>o\<^sub>w\<close> 50)

abbreviation (input) ge (infix \<open>\<ge>\<^sub>o\<^sub>w\<close> 50) where "x \<ge>\<^sub>o\<^sub>w y \<equiv> y \<le>\<^sub>o\<^sub>w x"
abbreviation (input) gt (infix \<open>>\<^sub>o\<^sub>w\<close> 50) where "x >\<^sub>o\<^sub>w y \<equiv> y <\<^sub>o\<^sub>w x"

notation ge (\<open>'(\<ge>\<^sub>o\<^sub>w')\<close>) 
  and ge (infix \<open>\<ge>\<^sub>o\<^sub>w\<close> 50) 
  and gt (\<open>'(>\<^sub>o\<^sub>w')\<close>) 
  and gt (infix \<open>>\<^sub>o\<^sub>w\<close> 50)

tts_register_sbts \<open>(\<le>\<^sub>o\<^sub>w)\<close> | U
proof-
  assume "Domainp AOA = (\<lambda>x. x \<in> U)" "bi_unique AOA" "right_total AOA" 
  from tts_AA_eq_transfer[OF this] show ?thesis by auto
qed

tts_register_sbts \<open>(<\<^sub>o\<^sub>w)\<close> | U
proof-
  assume "Domainp AOA = (\<lambda>x. x \<in> U)" "bi_unique AOA" "right_total AOA" 
  from tts_AA_eq_transfer[OF this] show ?thesis by auto
qed

end

locale ord_pair_ow = ord\<^sub>1: ord_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + ord\<^sub>2: ord_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2
begin

notation le\<^sub>1 (\<open>'(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1')\<close>)
  and le\<^sub>1 (infix \<open>\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close> 50) 
  and ls\<^sub>1 (\<open>'(<\<^sub>o\<^sub>w\<^sub>.\<^sub>1')\<close>) 
  and ls\<^sub>1 (infix \<open><\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close> 50)
  and le\<^sub>2 (\<open>'(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2')\<close>)
  and le\<^sub>2 (infix \<open>\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close> 50) 
  and ls\<^sub>2 (\<open>'(<\<^sub>o\<^sub>w\<^sub>.\<^sub>2')\<close>) 
  and ls\<^sub>2 (infix \<open><\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close> 50)

notation ord\<^sub>1.ge (\<open>'(\<ge>\<^sub>o\<^sub>w\<^sub>.\<^sub>1')\<close>) 
  and ord\<^sub>1.ge (infix \<open>\<ge>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close> 50) 
  and ord\<^sub>1.gt (\<open>'(>\<^sub>o\<^sub>w\<^sub>.\<^sub>1')\<close>) 
  and ord\<^sub>1.gt (infix \<open>>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close> 50)
  and ord\<^sub>2.ge (\<open>'(\<ge>\<^sub>o\<^sub>w\<^sub>.\<^sub>2')\<close>) 
  and ord\<^sub>2.ge (infix \<open>\<ge>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close> 50) 
  and ord\<^sub>2.gt (\<open>'(>\<^sub>o\<^sub>w\<^sub>.\<^sub>2')\<close>) 
  and ord\<^sub>2.gt (infix \<open>>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close> 50)

end

ud \<open>ord.lessThan\<close> (\<open>(with _ : ({..<_}))\<close> [1000] 10)
ud lessThan' \<open>lessThan\<close> 
ud \<open>ord.atMost\<close> (\<open>(with _ : ({.._}))\<close> [1000] 10) 
ud atMost' \<open>atMost\<close> 
ud \<open>ord.greaterThan\<close> (\<open>(with _ : ({_<..}))\<close> [1000] 10) 
ud greaterThan' \<open>greaterThan\<close> 
ud \<open>ord.atLeast\<close> (\<open>(with _ : ({_..}))\<close> [1000] 10) 
ud atLeast' \<open>atLeast\<close> 
ud \<open>ord.greaterThanLessThan\<close> (\<open>(with _ : ({_<..<_}))\<close> [1000, 999, 1000] 10) 
ud greaterThanLessThan' \<open>greaterThanLessThan\<close> 
ud \<open>ord.atLeastLessThan\<close> (\<open>(with _ _ : ({_..<_}))\<close> [1000, 999, 1000, 1000] 10)
ud atLeastLessThan' \<open>atLeastLessThan\<close> 
ud \<open>ord.greaterThanAtMost\<close> (\<open>(with _ _ : ({_<.._}))\<close> [1000, 999, 1000, 999] 10) 
ud greaterThanAtMost' \<open>greaterThanAtMost\<close> 
ud \<open>ord.atLeastAtMost\<close> (\<open>(with _ : ({_.._}))\<close> [1000, 1000, 1000] 10) 
ud atLeastAtMost' \<open>atLeastAtMost\<close> 
ud \<open>ord.min\<close> (\<open>(with _ : \<guillemotleft>min\<guillemotright> _ _)\<close> [1000, 1000, 999] 10)
ud min' \<open>min\<close> 
ud \<open>ord.max\<close> (\<open>(with _ : \<guillemotleft>max\<guillemotright> _ _)\<close> [1000, 1000, 999] 10)
ud max' \<open>max\<close>

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule, transfer_rule]: "Domainp A = (\<lambda>x. x \<in> U)"
    and [transfer_rule]: "right_total A" 
  trp (?'a A)
  in lessThan_ow: lessThan.with_def 
    (\<open>(on _ with _ : ({..<_}))\<close> [1000, 1000, 1000] 10) 
    and atMost_ow: atMost.with_def 
      (\<open>(on _ with _ : ({.._}))\<close> [1000, 1000, 1000] 10) 
    and greaterThan_ow: greaterThan.with_def
      (\<open>(on _ with _: ({_<..}))\<close> [1000, 1000, 1000] 10) 
    and atLeast_ow: atLeast.with_def
      (\<open>(on _ with _ : ({_..}))\<close> [1000, 1000, 1000] 10) 

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule, transfer_rule]: "Domainp A = (\<lambda>x. x \<in> U)"
    and [transfer_rule]: "bi_unique A" "right_total A" 
  trp (?'a A)
  in greaterThanLessThan_ow: greaterThanLessThan.with_def 
      (\<open>(on _ with _ : ({_<..<_}))\<close> [1000, 1000, 1000, 1000] 10) 
    and atLeastLessThan_ow: atLeastLessThan.with_def 
      (\<open>(on _ with _ _ : ({_..<_}))\<close> [1000, 1000, 999, 1000, 1000] 10)
    and greaterThanAtMost_ow: greaterThanAtMost.with_def 
      (\<open>(on _ with _ _ : ({_<.._}))\<close> [1000, 1000, 999, 1000, 1000] 10) 
    and atLeastAtMost_ow: atLeastAtMost.with_def 
      (\<open>(on _ with _ : ({_.._}))\<close> [1000, 1000, 1000, 1000] 10)

ctr parametricity
  in min_ow: min.with_def
    and max_ow: max.with_def

context ord_ow
begin

abbreviation lessThan :: "'ao \<Rightarrow> 'ao set" ("(1{..<\<^sub>o\<^sub>w_})") 
  where "{..<\<^sub>o\<^sub>w u} \<equiv> on U with (<\<^sub>o\<^sub>w) : {..<u}"
abbreviation atMost :: "'ao \<Rightarrow> 'ao set" ("(1{..\<^sub>o\<^sub>w_})") 
  where "{..\<^sub>o\<^sub>w u} \<equiv> on U with (\<le>\<^sub>o\<^sub>w) : {..u}"
abbreviation greaterThan :: "'ao \<Rightarrow> 'ao set" ("(1{_<\<^sub>o\<^sub>w..})")  
  where "{l<\<^sub>o\<^sub>w..} \<equiv> on U with (<\<^sub>o\<^sub>w) : {l<..}"
abbreviation atLeast :: "'ao \<Rightarrow> 'ao set" ("(1{_..\<^sub>o\<^sub>w})") 
  where "atLeast l \<equiv> on U with (\<le>\<^sub>o\<^sub>w) : {l..}"
abbreviation greaterThanLessThan :: "'ao \<Rightarrow> 'ao \<Rightarrow> 'ao set" ("(1{_<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>w_})")
  where "{l<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wu} \<equiv> on U with (<\<^sub>o\<^sub>w) : {l<..<u}"
abbreviation atLeastLessThan :: "'ao \<Rightarrow> 'ao \<Rightarrow> 'ao set" ("(1{_..<\<^sub>o\<^sub>w_})")
  where "{l..<\<^sub>o\<^sub>w u} \<equiv> on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {l<..u}"
abbreviation greaterThanAtMost :: "'ao \<Rightarrow> 'ao \<Rightarrow> 'ao set" ("(1{_<\<^sub>o\<^sub>w.._})")
  where "{l<\<^sub>o\<^sub>w..u}  \<equiv> on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {l<..u}"
abbreviation atLeastAtMost :: "'ao \<Rightarrow> 'ao \<Rightarrow> 'ao set" ("(1{_..\<^sub>o\<^sub>w_})")
  where "{l..\<^sub>o\<^sub>wu} \<equiv> on U with (\<le>\<^sub>o\<^sub>w) : {l..u}"
abbreviation min :: "'ao \<Rightarrow> 'ao \<Rightarrow> 'ao" where "min \<equiv> min.with (\<le>\<^sub>o\<^sub>w)"
abbreviation max :: "'ao \<Rightarrow> 'ao \<Rightarrow> 'ao" where "max \<equiv> max.with (\<le>\<^sub>o\<^sub>w)"

end

context ord_pair_ow
begin

notation ord\<^sub>1.lessThan ("(1{..<\<^sub>o\<^sub>w\<^sub>.\<^sub>1_})") 
notation ord\<^sub>1.atMost ("(1{..\<^sub>o\<^sub>w\<^sub>.\<^sub>1_})") 
notation ord\<^sub>1.greaterThan ("(1{_<\<^sub>o\<^sub>w\<^sub>.\<^sub>1..})")  
notation ord\<^sub>1.atLeast ("(1{_..\<^sub>o\<^sub>w\<^sub>.\<^sub>1})") 
notation ord\<^sub>1.greaterThanLessThan ("(1{_<\<^sub>o\<^sub>w\<^sub>.\<^sub>1..<\<^sub>o\<^sub>w\<^sub>.\<^sub>1_})")
notation ord\<^sub>1.atLeastLessThan ("(1{_..<\<^sub>o\<^sub>w\<^sub>.\<^sub>1_})")
notation ord\<^sub>1.greaterThanAtMost ("(1{_<\<^sub>o\<^sub>w\<^sub>.\<^sub>1.._})")
notation ord\<^sub>1.atLeastAtMost ("(1{_..\<^sub>o\<^sub>w\<^sub>.\<^sub>1_})")

notation ord\<^sub>2.lessThan ("(1{..<\<^sub>o\<^sub>w\<^sub>.\<^sub>2_})") 
notation ord\<^sub>2.atMost ("(1{..\<^sub>o\<^sub>w\<^sub>.\<^sub>2_})") 
notation ord\<^sub>2.greaterThan ("(1{_<\<^sub>o\<^sub>w\<^sub>.\<^sub>2..})")  
notation ord\<^sub>2.atLeast ("(1{_..\<^sub>o\<^sub>w\<^sub>.\<^sub>2})") 
notation ord\<^sub>2.greaterThanLessThan ("(1{_<\<^sub>o\<^sub>w\<^sub>.\<^sub>2..<\<^sub>o\<^sub>w\<^sub>.\<^sub>2_})")
notation ord\<^sub>2.atLeastLessThan ("(1{_..<\<^sub>o\<^sub>w\<^sub>.\<^sub>2_})")
notation ord\<^sub>2.greaterThanAtMost ("(1{_<\<^sub>o\<^sub>w\<^sub>.\<^sub>2.._})")
notation ord\<^sub>2.atLeastAtMost ("(1{_..\<^sub>o\<^sub>w\<^sub>.\<^sub>2_})")

end



subsection\<open>Preorders\<close>


subsubsection\<open>Definitions and common properties\<close>

locale preorder_ow = ord_ow U le ls 
  for U :: "'ao set" and le ls +
  assumes less_le_not_le: 
    "\<lbrakk> x \<in> U; y \<in> U \<rbrakk> \<Longrightarrow> x <\<^sub>o\<^sub>w y \<longleftrightarrow> x \<le>\<^sub>o\<^sub>w y \<and> \<not> (y \<le>\<^sub>o\<^sub>w x)"
    and order_refl[iff]: "x \<in> U \<Longrightarrow> x \<le>\<^sub>o\<^sub>w x"
    and order_trans: "\<lbrakk> x \<in> U; y \<in> U; z \<in> U; x \<le>\<^sub>o\<^sub>w y; y \<le>\<^sub>o\<^sub>w z \<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w z"

locale ord_preorder_ow = 
  ord\<^sub>1: ord_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + ord\<^sub>2: preorder_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2
begin

sublocale ord_pair_ow .

end

locale preorder_pair_ow = 
  ord\<^sub>1: preorder_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + ord\<^sub>2: preorder_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 and ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 and ls\<^sub>2
begin

sublocale ord_preorder_ow ..

end

ud \<open>preorder.bdd_above\<close> (\<open>(with _ : \<guillemotleft>bdd'_above\<guillemotright> _)\<close> [1000, 1000] 10)
ud bdd_above' \<open>bdd_above\<close> 
ud \<open>preorder.bdd_below\<close> (\<open>(with _ : \<guillemotleft>bdd'_below\<guillemotright> _)\<close> [1000, 1000] 10)
ud bdd_below' \<open>bdd_below\<close> 

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule, transfer_rule]: "Domainp A = (\<lambda>x. x \<in> U)"
    and [transfer_rule]: "right_total A" 
  trp (?'a A)
  in bdd_above_ow: bdd_above.with_def
    (\<open>(on _ with _ : \<guillemotleft>bdd'_above\<guillemotright> _)\<close> [1000, 1000, 1000] 10)
    and bdd_below_ow: bdd_below.with_def
    (\<open>(on _ with _ : \<guillemotleft>bdd'_below\<guillemotright> _)\<close> [1000, 1000, 1000] 10)

context preorder_ow
begin

abbreviation bdd_above :: "'ao set \<Rightarrow> bool" 
  where "bdd_above \<equiv> bdd_above_ow U (\<le>\<^sub>o\<^sub>w)"
abbreviation bdd_below :: "'ao set \<Rightarrow> bool" 
  where "bdd_below \<equiv> bdd_below_ow U (\<le>\<^sub>o\<^sub>w)"

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma preorder_transfer[transfer_rule]:
  assumes [transfer_rule]: "right_total A"
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=))  ===> (=)) 
      (preorder_ow (Collect (Domainp A))) class.preorder"
  unfolding preorder_ow_def class.preorder_def
  apply transfer_prover_start
  apply transfer_step+
  by blast

end


subsubsection\<open>Relativization\<close>

context preorder_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting preorder_ow_axioms
  eliminating through auto
begin

tts_lemma less_irrefl:
  assumes "x \<in> U"
  shows "\<not> x <\<^sub>o\<^sub>w x"
  is preorder_class.less_irrefl.
    
tts_lemma bdd_below_Ioc:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_below {a<\<^sub>o\<^sub>w..b}"
  is preorder_class.bdd_below_Ioc.
    
tts_lemma bdd_above_Ioc:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_above {a<\<^sub>o\<^sub>w..b}"
    is preorder_class.bdd_above_Ioc.

tts_lemma bdd_above_Iic:
  assumes "b \<in> U"
  shows "bdd_above {..\<^sub>o\<^sub>wb}"
    is preorder_class.bdd_above_Iic.

tts_lemma bdd_above_Iio:
  assumes "b \<in> U"
  shows "bdd_above {..<\<^sub>o\<^sub>wb}"
    is preorder_class.bdd_above_Iio.

tts_lemma bdd_below_Ici:
  assumes "a \<in> U"
  shows "bdd_below {a..\<^sub>o\<^sub>w}"
    is preorder_class.bdd_below_Ici.

tts_lemma bdd_below_Ioi:
  assumes "a \<in> U"
  shows "bdd_below {a<\<^sub>o\<^sub>w..}"
    is preorder_class.bdd_below_Ioi.

tts_lemma bdd_above_Icc:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_above {a..\<^sub>o\<^sub>wb}"
    is preorder_class.bdd_above_Icc.

tts_lemma bdd_above_Ioo:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_above {a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb}"
    is preorder_class.bdd_above_Ioo.

tts_lemma bdd_below_Icc:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_below {a..\<^sub>o\<^sub>wb}"
    is preorder_class.bdd_below_Icc.

tts_lemma bdd_below_Ioo:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_below {a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb}"
    is preorder_class.bdd_below_Ioo.

tts_lemma bdd_above_Ico:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_above (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b})"
    is preorder_class.bdd_above_Ico.

tts_lemma bdd_below_Ico:
  assumes "a \<in> U" and "b \<in> U"
  shows "bdd_below (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b})"
    is preorder_class.bdd_below_Ico.

tts_lemma Ioi_le_Ico:
  assumes "a \<in> U"
  shows "{a<\<^sub>o\<^sub>w..} \<subseteq> {a..\<^sub>o\<^sub>w}"
    is preorder_class.Ioi_le_Ico.

tts_lemma eq_refl:
  assumes "y \<in> U" and "x = y"
  shows "x \<le>\<^sub>o\<^sub>w y"
    is preorder_class.eq_refl.

tts_lemma less_imp_le:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "x \<le>\<^sub>o\<^sub>w y"
    is preorder_class.less_imp_le.

tts_lemma less_not_sym:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "\<not> y <\<^sub>o\<^sub>w x"
    is preorder_class.less_not_sym.

tts_lemma less_imp_not_less:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "(\<not> y <\<^sub>o\<^sub>w x) = True"
    is preorder_class.less_imp_not_less.

tts_lemma less_asym':
  assumes "a \<in> U" and "b \<in> U" and "a <\<^sub>o\<^sub>w b" and "b <\<^sub>o\<^sub>w a"
  shows P
    is preorder_class.less_asym'.

tts_lemma less_imp_triv:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "(y <\<^sub>o\<^sub>w x \<longrightarrow> P) = True"
    is preorder_class.less_imp_triv.

tts_lemma less_trans:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U" and "x <\<^sub>o\<^sub>w y" and "y <\<^sub>o\<^sub>w z"
  shows "x <\<^sub>o\<^sub>w z"
    is preorder_class.less_trans.

tts_lemma less_le_trans:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U" and "x <\<^sub>o\<^sub>w y" and "y \<le>\<^sub>o\<^sub>w z"
  shows "x <\<^sub>o\<^sub>w z"
    is preorder_class.less_le_trans.

tts_lemma le_less_trans:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U" and "x \<le>\<^sub>o\<^sub>w y" and "y <\<^sub>o\<^sub>w z"
  shows "x <\<^sub>o\<^sub>w z"
    is preorder_class.le_less_trans.

tts_lemma bdd_aboveI:
  assumes "A \<subseteq> U" and "M \<in> U" and "\<And>x. \<lbrakk>x \<in> U; x \<in> A\<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w M"
  shows "bdd_above A"
    is preorder_class.bdd_aboveI.

tts_lemma bdd_belowI:
  assumes "A \<subseteq> U" and "m \<in> U" and "\<And>x. \<lbrakk>x \<in> U; x \<in> A\<rbrakk> \<Longrightarrow> m \<le>\<^sub>o\<^sub>w x"
  shows "bdd_below A"
    is preorder_class.bdd_belowI.

tts_lemma less_asym:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>o\<^sub>w y" and "\<not> P \<Longrightarrow> y <\<^sub>o\<^sub>w x"
  shows P
    is preorder_class.less_asym.

tts_lemma transp_less: "transp_on U (<\<^sub>o\<^sub>w)"
  is preorder_class.transp_less.

tts_lemma transp_le: "transp_on U (\<le>\<^sub>o\<^sub>w)"
  is preorder_class.transp_le.

tts_lemma transp_gr: "transp_on U (\<lambda>x y. y <\<^sub>o\<^sub>w x)"
  is preorder_class.transp_gr.

tts_lemma transp_ge: "transp_on U (\<lambda>x y. y \<le>\<^sub>o\<^sub>w x)"
  is preorder_class.transp_ge.

tts_lemma bdd_above_Int1:
  assumes "A \<subseteq> U" and "B \<subseteq> U" and "bdd_above A"
  shows "bdd_above (A \<inter> B)"
    is preorder_class.bdd_above_Int1.

tts_lemma bdd_above_Int2:
  assumes "B \<subseteq> U" and "A \<subseteq> U" and "bdd_above B"
  shows "bdd_above (A \<inter> B)"
    is preorder_class.bdd_above_Int2.

tts_lemma bdd_below_Int1:
  assumes "A \<subseteq> U" and "B \<subseteq> U" and "bdd_below A"
  shows "bdd_below (A \<inter> B)"
    is preorder_class.bdd_below_Int1.

tts_lemma bdd_below_Int2:
  assumes "B \<subseteq> U" and "A \<subseteq> U" and "bdd_below B"
  shows "bdd_below (A \<inter> B)"
    is preorder_class.bdd_below_Int2.

tts_lemma bdd_above_mono:
  assumes "B \<subseteq> U" and "bdd_above B" and "A \<subseteq> B"
  shows "bdd_above A"
    is preorder_class.bdd_above_mono.

tts_lemma bdd_below_mono:
  assumes "B \<subseteq> U" and "bdd_below B" and "A \<subseteq> B"
  shows "bdd_below A"
    is preorder_class.bdd_below_mono.

tts_lemma atLeastAtMost_subseteq_atLeastLessThan_iff:
  assumes "a \<in> U"
    and "b \<in> U"
    and "c \<in> U"
    and "d \<in> U"
  shows "({a..\<^sub>o\<^sub>wb} \<subseteq> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {c..<d})) = 
    (a \<le>\<^sub>o\<^sub>w b \<longrightarrow> b <\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is preorder_class.atLeastAtMost_subseteq_atLeastLessThan_iff.

tts_lemma atMost_subset_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "({..\<^sub>o\<^sub>wx} \<subseteq> {..\<^sub>o\<^sub>wy}) = (x \<le>\<^sub>o\<^sub>w y)"
    is Set_Interval.atMost_subset_iff.

tts_lemma single_Diff_lessThan:
  assumes "k \<in> U"
  shows "{k} - {..<\<^sub>o\<^sub>wk} = {k}"
  is Set_Interval.single_Diff_lessThan.

tts_lemma atLeast_subset_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "({x..\<^sub>o\<^sub>w} \<subseteq> {y..\<^sub>o\<^sub>w}) = (y \<le>\<^sub>o\<^sub>w x)"
    is Set_Interval.atLeast_subset_iff.

tts_lemma atLeastatMost_psubset_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows 
    "({a..\<^sub>o\<^sub>wb} \<subset> {c..\<^sub>o\<^sub>wd}) = 
      (c \<le>\<^sub>o\<^sub>w d \<and> (\<not> a \<le>\<^sub>o\<^sub>w b \<or> c \<le>\<^sub>o\<^sub>w a \<and> b \<le>\<^sub>o\<^sub>w d \<and> (c <\<^sub>o\<^sub>w a \<or> b <\<^sub>o\<^sub>w d)))"
    is preorder_class.atLeastatMost_psubset_iff.

tts_lemma not_empty_eq_Iic_eq_empty:
  assumes "h \<in> U"
  shows "{} \<noteq> {..\<^sub>o\<^sub>wh}"
    is preorder_class.not_empty_eq_Iic_eq_empty.
    
tts_lemma atLeastatMost_subset_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "d \<in> U"
  shows "({a..\<^sub>o\<^sub>wb} \<subseteq> {c..\<^sub>o\<^sub>wd}) = (\<not> a \<le>\<^sub>o\<^sub>w b \<or> b \<le>\<^sub>o\<^sub>w d \<and> c \<le>\<^sub>o\<^sub>w a)"
    is preorder_class.atLeastatMost_subset_iff.

tts_lemma Icc_subset_Ici_iff:
  assumes "l \<in> U" and "h \<in> U" and "l' \<in> U"
  shows "({l..\<^sub>o\<^sub>wh} \<subseteq> {l'..\<^sub>o\<^sub>w}) = (\<not> l \<le>\<^sub>o\<^sub>w h \<or> l' \<le>\<^sub>o\<^sub>w l)"
    is preorder_class.Icc_subset_Ici_iff.
    
tts_lemma Icc_subset_Iic_iff:
  assumes "l \<in> U" and "h \<in> U" and "h' \<in> U"
  shows "({l..\<^sub>o\<^sub>wh} \<subseteq> {..\<^sub>o\<^sub>wh'}) = (\<not> l \<le>\<^sub>o\<^sub>w h \<or> h \<le>\<^sub>o\<^sub>w h')"
    is preorder_class.Icc_subset_Iic_iff.

tts_lemma not_empty_eq_Ici_eq_empty:
  assumes "l \<in> U"
  shows "{} \<noteq> {l..\<^sub>o\<^sub>w}"
  is preorder_class.not_empty_eq_Ici_eq_empty.
    
tts_lemma not_Ici_eq_empty:
  assumes "l \<in> U"
  shows "{l..\<^sub>o\<^sub>w} \<noteq> {}"
is preorder_class.not_Ici_eq_empty.
    
tts_lemma not_Iic_eq_empty:
  assumes "h \<in> U"
  shows "{..\<^sub>o\<^sub>wh} \<noteq> {}"
    is preorder_class.not_Iic_eq_empty.

tts_lemma atLeastatMost_empty_iff2:
  assumes "a \<in> U" and "b \<in> U"
  shows "({} = {a..\<^sub>o\<^sub>wb}) = (\<not> a \<le>\<^sub>o\<^sub>w b)"
    is preorder_class.atLeastatMost_empty_iff2.
    
tts_lemma atLeastLessThan_empty_iff2:
  assumes "a \<in> U" and "b \<in> U"
  shows "({} = (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b})) = (\<not> a <\<^sub>o\<^sub>w b)"
    is preorder_class.atLeastLessThan_empty_iff2.
    
tts_lemma greaterThanAtMost_empty_iff2:
  assumes "k \<in> U" and "l \<in> U"
  shows "({} = {k<\<^sub>o\<^sub>w..l}) = (\<not> k <\<^sub>o\<^sub>w l)"
    is preorder_class.greaterThanAtMost_empty_iff2.
    
tts_lemma atLeastatMost_empty_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "({a..\<^sub>o\<^sub>wb} = {}) = (\<not> a \<le>\<^sub>o\<^sub>w b)"
    is preorder_class.atLeastatMost_empty_iff.
    
tts_lemma atLeastLessThan_empty_iff:
  assumes "a \<in> U" and "b \<in> U"
  shows "((on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b}) = {}) = (\<not> a <\<^sub>o\<^sub>w b)"
    is preorder_class.atLeastLessThan_empty_iff.
    
tts_lemma greaterThanAtMost_empty_iff:
  assumes "k \<in> U" and "l \<in> U"
  shows "({k<\<^sub>o\<^sub>w..l} = {}) = (\<not> k <\<^sub>o\<^sub>w l)"
    is preorder_class.greaterThanAtMost_empty_iff.

end


tts_context
  tts: (?'a to U)
  substituting preorder_ow_axioms
begin

tts_lemma bdd_above_empty:
  assumes "U \<noteq> {}"
  shows "bdd_above {}"
    is preorder_class.bdd_above_empty.
    
tts_lemma bdd_below_empty:
  assumes "U \<noteq> {}"
  shows "bdd_below {}"
    is preorder_class.bdd_below_empty.
    
end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'a set\<close>)
  rewriting ctr_simps
  substituting preorder_ow_axioms
  eliminating through (auto intro: bdd_above_empty bdd_below_empty)
begin

tts_lemma bdd_belowI2:
  assumes "A \<subseteq> U\<^sub>2"
    and "m \<in> U"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "\<And>x. x \<in> A \<Longrightarrow> m \<le>\<^sub>o\<^sub>w f x"
  shows "bdd_below (f ` A)"
    given preorder_class.bdd_belowI2
  by blast

tts_lemma bdd_aboveI2:
  assumes "A \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "M \<in> U"
    and "\<And>x. x \<in> A \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w M"
  shows "bdd_above (f ` A)"
    given preorder_class.bdd_aboveI2
  by blast
    
end

end



subsection\<open>Partial orders\<close>


subsubsection\<open>Definitions and common properties\<close>

locale ordering_ow =
  fixes U :: "'ao set"
    and le :: "'ao \<Rightarrow> 'ao \<Rightarrow> bool" (infix "\<^bold>\<le>\<^sub>o\<^sub>w" 50)
    and ls :: "'ao \<Rightarrow> 'ao \<Rightarrow> bool" (infix "\<^bold><\<^sub>o\<^sub>w" 50)
  assumes strict_iff_order: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<^bold><\<^sub>o\<^sub>w b \<longleftrightarrow> a \<^bold>\<le>\<^sub>o\<^sub>w b \<and> a \<noteq> b"
    and refl: "a \<in> U \<Longrightarrow> a \<^bold>\<le>\<^sub>o\<^sub>w a"
    and antisym: "\<lbrakk> a \<in> U; b \<in> U; a \<^bold>\<le>\<^sub>o\<^sub>w b; b \<^bold>\<le>\<^sub>o\<^sub>w a \<rbrakk> \<Longrightarrow> a = b"
    and trans: "\<lbrakk> a \<in> U; b \<in> U; c \<in> U; a \<^bold>\<le>\<^sub>o\<^sub>w b; b \<^bold>\<le>\<^sub>o\<^sub>w c \<rbrakk> \<Longrightarrow> a \<^bold>\<le>\<^sub>o\<^sub>w c"
begin

notation le (infix "\<^bold>\<le>\<^sub>o\<^sub>w" 50)
  and ls (infix "\<^bold><\<^sub>o\<^sub>w" 50)

end

locale order_ow = preorder_ow U le ls for U :: "'ao set" and le ls +
  assumes antisym: "\<lbrakk> x \<in> U; y \<in> U; x \<le>\<^sub>o\<^sub>w y; y \<le>\<^sub>o\<^sub>w x \<rbrakk> \<Longrightarrow> x = y" 
begin

sublocale 
  order: ordering_ow U \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> + 
  dual_order: ordering_ow U \<open>(\<ge>\<^sub>o\<^sub>w)\<close> \<open>(>\<^sub>o\<^sub>w)\<close>
  apply unfold_locales
  subgoal by (force simp: less_le_not_le antisym)
  subgoal by simp 
  subgoal by (simp add: antisym)
  subgoal by (metis order_trans)
  subgoal by (force simp: less_le_not_le antisym)
  subgoal by (simp add: antisym)
  subgoal by (metis order_trans)
  done

no_notation le (infix "\<^bold>\<le>\<^sub>o\<^sub>w" 50)
  and ls (infix "\<^bold><\<^sub>o\<^sub>w" 50)

end

locale ord_order_ow = ord\<^sub>1: ord_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + ord\<^sub>2: order_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2

sublocale ord_order_ow \<subseteq> ord_preorder_ow ..

locale preorder_order_ow =
  ord\<^sub>1: preorder_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + ord\<^sub>2: order_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2

sublocale preorder_order_ow \<subseteq> preorder_pair_ow ..

locale order_pair_ow = ord\<^sub>1: order_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 + ord\<^sub>2: order_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2

sublocale order_pair_ow \<subseteq> preorder_order_ow ..

ud \<open>order.mono\<close> (\<open>(with _ _ : \<guillemotleft>mono\<guillemotright> _)\<close> [1000, 999, 1000] 10)
ud mono' \<open>mono\<close> 
ud \<open>order.strict_mono\<close> (\<open>(with _ _ : \<guillemotleft>strict'_mono\<guillemotright> _)\<close> [1000, 999, 1000] 10)
ud strict_mono' \<open>strict_mono\<close> 
ud \<open>order.antimono\<close> (\<open>(with _ _ : \<guillemotleft>strict'_mono\<guillemotright> _)\<close> [1000, 999, 1000] 10)
ud antimono' \<open>antimono\<close> 
ud \<open>monoseq\<close> (\<open>(with _ : \<guillemotleft>monoseq\<guillemotright> _)\<close> [1000, 1000] 10)

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule, transfer_rule]: 
    "Domainp (B::'c\<Rightarrow>'d\<Rightarrow>bool) = (\<lambda>x. x \<in> U\<^sub>2)"
    and [transfer_rule]: "right_total B" 
  trp (?'b \<open>A::'a\<Rightarrow>'b\<Rightarrow>bool\<close>) and (?'a B)
  in mono_ow: mono.with_def 
    (\<open>(on _ with _ _ : \<guillemotleft>mono\<guillemotright> _)\<close> [1000, 1000, 999, 1000] 10)
    and strict_mono_ow: strict_mono.with_def 
      (\<open>(on _ with _ _ : \<guillemotleft>strict'_mono\<guillemotright> _)\<close> [1000, 1000, 999, 1000] 10)
    and antimono_ow: antimono.with_def
      (\<open>(on _ with _ _ : \<guillemotleft>antimono\<guillemotright> _)\<close> [1000, 1000, 999, 1000] 10)
    and monoseq_ow: monoseq.with_def


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma ordering_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      (ordering_ow (Collect (Domainp A))) ordering"
  unfolding ordering_ow_def ordering_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Ball_Collect[symmetric]
  by (intro ext HOL.arg_cong2[where f="(\<and>)"]) auto

lemma order_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      (order_ow (Collect (Domainp A))) class.order"
  unfolding 
    order_ow_def class.order_def order_ow_axioms_def class.order_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

end


subsubsection\<open>Relativization\<close>

context ordering_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting ordering_ow_axioms
  eliminating through simp
begin

tts_lemma irrefl:
  assumes "a \<in> U"
  shows "\<not> a \<^bold><\<^sub>o\<^sub>w a"
    is ordering.irrefl.
    
tts_lemma strict_implies_order:
  assumes "a \<in> U" and "b \<in> U" and "a \<^bold><\<^sub>o\<^sub>w b"
  shows "a \<^bold>\<le>\<^sub>o\<^sub>w b"
  is ordering.strict_implies_order.
    
tts_lemma strict_implies_not_eq:
  assumes "a \<in> U" and "b \<in> U" and "a \<^bold><\<^sub>o\<^sub>w b"
  shows "a \<noteq> b"
    is ordering.strict_implies_not_eq.
    
tts_lemma order_iff_strict:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a \<^bold>\<le>\<^sub>o\<^sub>w b) = (a \<^bold><\<^sub>o\<^sub>w b \<or> a = b)"
    is ordering.order_iff_strict.
    
tts_lemma asym:
  assumes "a \<in> U" and "b \<in> U" and "a \<^bold><\<^sub>o\<^sub>w b" and "b \<^bold><\<^sub>o\<^sub>w a"
  shows False
    is ordering.asym.
    
tts_lemma strict_trans:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<^bold><\<^sub>o\<^sub>w b" and "b \<^bold><\<^sub>o\<^sub>w c"
  shows "a \<^bold><\<^sub>o\<^sub>w c"
    is ordering.strict_trans.
    
tts_lemma strict_trans2:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<^bold><\<^sub>o\<^sub>w b" and "b \<^bold>\<le>\<^sub>o\<^sub>w c"
  shows "a \<^bold><\<^sub>o\<^sub>w c"
    is ordering.strict_trans2.
    
tts_lemma strict_trans1:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<^bold>\<le>\<^sub>o\<^sub>w b" and "b \<^bold><\<^sub>o\<^sub>w c"
  shows "a \<^bold><\<^sub>o\<^sub>w c"
    is ordering.strict_trans1.
    
tts_lemma not_eq_order_implies_strict:
  assumes "a \<in> U" and "b \<in> U" and "a \<noteq> b" and "a \<^bold>\<le>\<^sub>o\<^sub>w b"
  shows "a \<^bold><\<^sub>o\<^sub>w b"
    is ordering.not_eq_order_implies_strict.

end

end

context order_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting order_ow_axioms
  eliminating through clarsimp
begin

tts_lemma atLeastAtMost_singleton:
  assumes "a \<in> U"
  shows "{a..\<^sub>o\<^sub>wa} = {a}"
  is order_class.atLeastAtMost_singleton.
    
tts_lemma less_imp_neq:
  assumes "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "x \<noteq> y"
    is order_class.less_imp_neq.
    
tts_lemma atLeastatMost_empty:
  assumes "b \<in> U" and "a \<in> U" and "b <\<^sub>o\<^sub>w a"
  shows "{a..\<^sub>o\<^sub>wb} = {}"
    is order_class.atLeastatMost_empty.
    
tts_lemma less_imp_not_eq:
  assumes "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "(x = y) = False"
    is order_class.less_imp_not_eq.
    
tts_lemma less_imp_not_eq2:
  assumes "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "(y = x) = False"
    is order_class.less_imp_not_eq2.
    
tts_lemma atLeastLessThan_empty:
  assumes "b \<in> U" and "a \<in> U" and "b \<le>\<^sub>o\<^sub>w a"
  shows "(on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b}) = {}"
    is order_class.atLeastLessThan_empty.
    
tts_lemma greaterThanAtMost_empty:
  assumes "l \<in> U" and "k \<in> U" and "l \<le>\<^sub>o\<^sub>w k"
  shows "{k<\<^sub>o\<^sub>w..l} = {}"
    is order_class.greaterThanAtMost_empty.

tts_lemma antisym_conv1:
  assumes "x \<in> U" and "y \<in> U" and "\<not> x <\<^sub>o\<^sub>w y"
  shows "(x \<le>\<^sub>o\<^sub>w y) = (x = y)"
    is order_class.antisym_conv1.

tts_lemma antisym_conv2:
  assumes "x \<in> U" and "y \<in> U" and "x \<le>\<^sub>o\<^sub>w y"
  shows "(\<not> x <\<^sub>o\<^sub>w y) = (x = y)"
    is order_class.antisym_conv2.
    
tts_lemma greaterThanLessThan_empty:
  assumes "l \<in> U" and "k \<in> U" and "l \<le>\<^sub>o\<^sub>w k"
  shows "{k<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wl} = {}"
    is order_class.greaterThanLessThan_empty.
    
tts_lemma atLeastLessThan_eq_atLeastAtMost_diff:
  assumes "a \<in> U" and "b \<in> U"
  shows "(on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {a..<b}) = {a..\<^sub>o\<^sub>wb} - {b}"
    is order_class.atLeastLessThan_eq_atLeastAtMost_diff.
    
tts_lemma greaterThanAtMost_eq_atLeastAtMost_diff:
  assumes "a \<in> U" and "b \<in> U"
  shows "{a<\<^sub>o\<^sub>w..b} = {a..\<^sub>o\<^sub>wb} - {a}"
    is order_class.greaterThanAtMost_eq_atLeastAtMost_diff.

tts_lemma less_separate:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows 
    "\<exists>x'\<in>U. \<exists>y'\<in>U. x \<in> {..<\<^sub>o\<^sub>wx'} \<and> y \<in> {y'<\<^sub>o\<^sub>w..} \<and> {..<\<^sub>o\<^sub>wx'} \<inter> {y'<\<^sub>o\<^sub>w..} = {}"
    is order_class.less_separate.

tts_lemma eq_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x = y) = (x \<le>\<^sub>o\<^sub>w y \<and> y \<le>\<^sub>o\<^sub>w x)"
    is order_class.eq_iff.

tts_lemma order_iff_strict:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a \<le>\<^sub>o\<^sub>w b) = (a <\<^sub>o\<^sub>w b \<or> a = b)"
    is order_class.order.order_iff_strict.
    
tts_lemma le_less:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x \<le>\<^sub>o\<^sub>w y) = (x <\<^sub>o\<^sub>w y \<or> x = y)"
    is order_class.le_less.

tts_lemma asym:
  assumes "a \<in> U" and "b \<in> U" and "a <\<^sub>o\<^sub>w b" and "b <\<^sub>o\<^sub>w a"
  shows False
    is order_class.order.asym.
    
tts_lemma strict_iff_order:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a <\<^sub>o\<^sub>w b) = (a \<le>\<^sub>o\<^sub>w b \<and> a \<noteq> b)"
    is order_class.order.strict_iff_order.
    
tts_lemma less_le:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x <\<^sub>o\<^sub>w y) = (x \<le>\<^sub>o\<^sub>w y \<and> x \<noteq> y)"
    is order_class.less_le.

tts_lemma atLeastAtMost_singleton':
  assumes "b \<in> U" and "a = b"
  shows "{a..\<^sub>o\<^sub>wb} = {a}"
    is order_class.atLeastAtMost_singleton'.
    
tts_lemma le_imp_less_or_eq:
  assumes "x \<in> U" and "y \<in> U" and "x \<le>\<^sub>o\<^sub>w y"
  shows "x <\<^sub>o\<^sub>w y \<or> x = y"
    is order_class.le_imp_less_or_eq.
  
tts_lemma antisym_conv:
  assumes "y \<in> U" and "x \<in> U" and "y \<le>\<^sub>o\<^sub>w x"
  shows "(x \<le>\<^sub>o\<^sub>w y) = (x = y)"
    is order_class.antisym_conv.

tts_lemma strict_trans:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a <\<^sub>o\<^sub>w b" and "b <\<^sub>o\<^sub>w c"
  shows "a <\<^sub>o\<^sub>w c"
    is order_class.order.strict_trans.

tts_lemma strict_trans2:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a <\<^sub>o\<^sub>w b" and "b \<le>\<^sub>o\<^sub>w c"
  shows "a <\<^sub>o\<^sub>w c"
    is order_class.order.strict_trans2.

tts_lemma strict_trans1:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<le>\<^sub>o\<^sub>w b" and "b <\<^sub>o\<^sub>w c"
  shows "a <\<^sub>o\<^sub>w c"
    is order_class.order.strict_trans1.
    
tts_lemma le_neq_trans:
  assumes "a \<in> U" and "b \<in> U" and "a \<le>\<^sub>o\<^sub>w b" and "a \<noteq> b"
  shows "a <\<^sub>o\<^sub>w b"
    is order_class.le_neq_trans.

tts_lemma neq_le_trans:
  assumes "a \<in> U" and "b \<in> U" and "a \<noteq> b" and "a \<le>\<^sub>o\<^sub>w b"
  shows "a <\<^sub>o\<^sub>w b"
    is order_class.neq_le_trans.
    
tts_lemma Iio_Int_singleton:
  assumes "k \<in> U" and "x \<in> U"
  shows "{..<\<^sub>o\<^sub>wk} \<inter> {x} = (if x <\<^sub>o\<^sub>w k then {x} else {})"
    is order_class.Iio_Int_singleton.
    
tts_lemma atLeastAtMost_singleton_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "({a..\<^sub>o\<^sub>wb} = {c}) = (a = b \<and> b = c)"
    is order_class.atLeastAtMost_singleton_iff.
    
tts_lemma Icc_eq_Icc:
  assumes "l \<in> U" and "h \<in> U" and "l' \<in> U" and "h' \<in> U"
  shows "({l..\<^sub>o\<^sub>wh} = {l'..\<^sub>o\<^sub>wh'}) = (h = h' \<and> l = l' \<or> \<not> l' \<le>\<^sub>o\<^sub>w h' \<and> \<not> l \<le>\<^sub>o\<^sub>w h)"
    is order_class.Icc_eq_Icc.
    
tts_lemma lift_Suc_mono_less_iff:
  assumes "range f \<subseteq> U" and "\<And>n. f n <\<^sub>o\<^sub>w f (Suc n)"
  shows "(f n <\<^sub>o\<^sub>w f m) = (n < m)"
    is order_class.lift_Suc_mono_less_iff.

tts_lemma lift_Suc_mono_less:
  assumes "range f \<subseteq> U" and "\<And>n. f n <\<^sub>o\<^sub>w f (Suc n)" and "n < n'"
  shows "f n <\<^sub>o\<^sub>w f n'"
    is order_class.lift_Suc_mono_less.
  
tts_lemma lift_Suc_mono_le:
  assumes "range f \<subseteq> U" and "\<And>n. f n \<le>\<^sub>o\<^sub>w f (Suc n)" and "n \<le> n'"
  shows "f n \<le>\<^sub>o\<^sub>w f n'"
    is order_class.lift_Suc_mono_le.
    
tts_lemma lift_Suc_antimono_le:
  assumes "range f \<subseteq> U" and "\<And>n. f (Suc n) \<le>\<^sub>o\<^sub>w f n" and "n \<le> n'"
  shows "f n' \<le>\<^sub>o\<^sub>w f n"
    is order_class.lift_Suc_antimono_le.

tts_lemma ivl_disj_int_two:
  assumes "l \<in> U" and "m \<in> U" and "u \<in> U"
  shows 
    "{l<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wm} \<inter> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {m..<u}) = {}"
    "{l<\<^sub>o\<^sub>w..m} \<inter> {m<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wu} = {}"
    "(on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {l..<m}) \<inter> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {m..<u}) = {}"
    "{l..\<^sub>o\<^sub>wm} \<inter> {m<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wu} = {}"
    "{l<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wm} \<inter> {m..\<^sub>o\<^sub>wu} = {}"
    "{l<\<^sub>o\<^sub>w..m} \<inter> {m<\<^sub>o\<^sub>w..u} = {}"
    "(on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {l..<m}) \<inter> {m..\<^sub>o\<^sub>wu} = {}"
    "{l..\<^sub>o\<^sub>wm} \<inter> {m<\<^sub>o\<^sub>w..u} = {}"
    is Set_Interval.ivl_disj_int_two.
  
tts_lemma ivl_disj_int_one:
  assumes "l \<in> U" and "u \<in> U"
  shows 
    "{..\<^sub>o\<^sub>wl} \<inter> {l<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wu} = {}"
    "{..<\<^sub>o\<^sub>wl} \<inter> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {l..<u}) = {}"
    "{..\<^sub>o\<^sub>wl} \<inter> {l<\<^sub>o\<^sub>w..u} = {}"
    "{..<\<^sub>o\<^sub>wl} \<inter> {l..\<^sub>o\<^sub>wu} = {}"
    "{l<\<^sub>o\<^sub>w..u} \<inter> {u<\<^sub>o\<^sub>w..} = {}"
    "{l<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wu} \<inter> {u..\<^sub>o\<^sub>w} = {}"
    "{l..\<^sub>o\<^sub>wu} \<inter> {u<\<^sub>o\<^sub>w..} = {}"
    "(on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {l..<u}) \<inter> {u..\<^sub>o\<^sub>w} = {}"
    is Set_Interval.ivl_disj_int_one.

tts_lemma min_absorb2:
  assumes "y \<in> U" and "x \<in> U" and "y \<le>\<^sub>o\<^sub>w x"
  shows "local.min x y = y"
    is Orderings.min_absorb2.
    
tts_lemma max_absorb1:
  assumes "y \<in> U" and "x \<in> U" and "y \<le>\<^sub>o\<^sub>w x"
  shows "local.max x y = x"
    is Orderings.max_absorb1.

tts_lemma finite_mono_remains_stable_implies_strict_prefix:
  assumes "range f \<subseteq> U"
    and "finite (range f)"
    and "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> f"
    and "\<forall>n. f n = f (Suc n) \<longrightarrow> f (Suc n) = f (Suc (Suc n))"
  shows "\<exists>N. (\<forall>n\<ge>N. f N = f n) \<and> (\<forall>n\<le>N. \<forall>m\<le>N. m < n \<longrightarrow> f m <\<^sub>o\<^sub>w f n)"
    is Hilbert_Choice.finite_mono_remains_stable_implies_strict_prefix.
    
tts_lemma incseq_imp_monoseq:
  assumes "range X \<subseteq> U" and "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> X"
  shows "with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>monoseq\<guillemotright> X"
    is Topological_Spaces.incseq_imp_monoseq.
    
tts_lemma decseq_imp_monoseq:
  assumes "range X \<subseteq> U" and "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>antimono\<guillemotright> X"
  shows "with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>monoseq\<guillemotright> X"
    is Topological_Spaces.decseq_imp_monoseq.
    
tts_lemma irrefl:
  assumes "a \<in> U"
  shows "\<not> a <\<^sub>o\<^sub>w a"
    is order_class.order.irrefl.
    
tts_lemma incseq_Suc_iff:
  assumes "range f \<subseteq> U"
  shows "(on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> f) = (\<forall>x. f x \<le>\<^sub>o\<^sub>w f (Suc x))"
    is Topological_Spaces.incseq_Suc_iff.
    
tts_lemma decseq_Suc_iff:
  assumes "range f \<subseteq> U"
  shows "(on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>antimono\<guillemotright> f) = (\<forall>x. f (Suc x) \<le>\<^sub>o\<^sub>w f x)"
    is Topological_Spaces.decseq_Suc_iff.

tts_lemma incseq_const:
  assumes "k \<in> U"
  shows "on (UNIV::nat set) with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> (\<lambda>x. k)"
    is Topological_Spaces.incseq_const.

tts_lemma decseq_const:
  assumes "k \<in> U"
  shows "on (UNIV::nat set) with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>antimono\<guillemotright> (\<lambda>x. k)"
    is Topological_Spaces.decseq_const.

tts_lemma atMost_Int_atLeast:
  assumes "n \<in> U"
  shows "{..\<^sub>o\<^sub>wn} \<inter> {n..\<^sub>o\<^sub>w} = {n}"
    is Set_Interval.atMost_Int_atLeast.

tts_lemma monoseq_iff:
  assumes "range X \<subseteq> U"
  shows 
    "(with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>monoseq\<guillemotright> X) = 
      (
        (on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> X) \<or> 
        (on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>antimono\<guillemotright> X)
      )"
    is Topological_Spaces.monoseq_iff.

tts_lemma monoseq_Suc:
  assumes "range X \<subseteq> U"
  shows 
    "(with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>monoseq\<guillemotright> X) = 
      ((\<forall>x. X x \<le>\<^sub>o\<^sub>w X (Suc x)) \<or> (\<forall>x. X (Suc x) \<le>\<^sub>o\<^sub>w X x))"
    is Topological_Spaces.monoseq_Suc.

tts_lemma incseq_SucI:
  assumes "range X \<subseteq> U" and "\<And>n. X n \<le>\<^sub>o\<^sub>w X (Suc n)"
  shows "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> X"
    is Topological_Spaces.incseq_SucI.

tts_lemma incseq_SucD:
  assumes "range A \<subseteq> U" and "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> A"
  shows "A i \<le>\<^sub>o\<^sub>w A (Suc i)"
    is Topological_Spaces.incseq_SucD.

tts_lemma decseq_SucI:
  assumes "range X \<subseteq> U" and "\<And>n. X (Suc n) \<le>\<^sub>o\<^sub>w X n"
  shows "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>antimono\<guillemotright> X"
    is Topological_Spaces.decseq_SucI.

tts_lemma decseq_SucD:
  assumes "range A \<subseteq> U" and "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>antimono\<guillemotright> A"
  shows "A (Suc i) \<le>\<^sub>o\<^sub>w A i"
    is Topological_Spaces.decseq_SucD.

tts_lemma mono_SucI2:
  assumes "range X \<subseteq> U" and "\<forall>x. X (Suc x) \<le>\<^sub>o\<^sub>w X x"
  shows "with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>monoseq\<guillemotright> X"
    is Topological_Spaces.mono_SucI2.

tts_lemma mono_SucI1:
  assumes "range X \<subseteq> U" and "\<forall>x. X x \<le>\<^sub>o\<^sub>w X (Suc x)"
  shows "with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>monoseq\<guillemotright> X"
    is Topological_Spaces.mono_SucI1.

tts_lemma incseqD:
  assumes "range f \<subseteq> U" 
    and "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> f" 
    and "(i::nat) \<le> j"
  shows "f i \<le>\<^sub>o\<^sub>w f j"
    is Topological_Spaces.incseqD.

tts_lemma decseqD:
  assumes "range f \<subseteq> U"
    and "on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>antimono\<guillemotright> f"
    and "(i::nat) \<le> j"
  shows "f j \<le>\<^sub>o\<^sub>w f i"
    is Topological_Spaces.decseqD.

tts_lemma monoI2:
  assumes "range X \<subseteq> U" and "\<forall>x y. x \<le> y \<longrightarrow> X y \<le>\<^sub>o\<^sub>w X x"
  shows "with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>monoseq\<guillemotright> X"
    is Topological_Spaces.monoI2.

tts_lemma monoI1:
  assumes "range X \<subseteq> U" and "\<forall>x y. x \<le> y \<longrightarrow> X x \<le>\<^sub>o\<^sub>w X y"
  shows "with (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>monoseq\<guillemotright> X"
    is Topological_Spaces.monoI1.

tts_lemma antimono_iff_le_Suc:
  assumes "range f \<subseteq> U"
  shows "(on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>antimono\<guillemotright> f) = (\<forall>x. f (Suc x) \<le>\<^sub>o\<^sub>w f x)"
    is Nat.antimono_iff_le_Suc.

tts_lemma mono_iff_le_Suc:
  assumes "range f \<subseteq> U"
  shows "(on UNIV with (\<le>\<^sub>o\<^sub>w) (\<le>) : \<guillemotleft>mono\<guillemotright> f) = (\<forall>x. f x \<le>\<^sub>o\<^sub>w f (Suc x))"
    is Nat.mono_iff_le_Suc.

tts_lemma funpow_mono2:
  assumes "\<forall>x\<in>U. f x \<in> U"
    and "x \<in> U"
    and "y \<in> U"
    and "on U with (\<le>\<^sub>o\<^sub>w) (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>mono\<guillemotright> f"
    and "i \<le> j"
    and "x \<le>\<^sub>o\<^sub>w y"
    and "x \<le>\<^sub>o\<^sub>w f x"
  shows "(f ^^ i) x \<le>\<^sub>o\<^sub>w (f ^^ j) y"
    is Nat.funpow_mono2.

tts_lemma funpow_mono:
  assumes "\<forall>x\<in>U. f x \<in> U"
    and "A \<in> U"
    and "B \<in> U"
    and "on U with (\<le>\<^sub>o\<^sub>w) (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>mono\<guillemotright> f"
    and "A \<le>\<^sub>o\<^sub>w B"
  shows "(f ^^ n) A \<le>\<^sub>o\<^sub>w (f ^^ n) B"
    is Nat.funpow_mono.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting order_ow_axioms
  eliminating through clarsimp
begin

tts_lemma ex_min_if_finite:
  assumes "S \<subseteq> U"
    and "finite S"
    and "S \<noteq> {}"
  shows "\<exists>x\<in>S. \<not> (\<exists>y\<in>S. y <\<^sub>o\<^sub>w x)"
    is Lattices_Big.ex_min_if_finite.
    
end

tts_context
  tts: (?'a to U)
  sbterms: (\<open>(\<le>)::['a::order, 'a::order] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w)\<close>) 
    and (\<open>(<)::['a::order, 'a::order] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w)\<close>)
  substituting order_ow_axioms
  eliminating through clarsimp
begin

tts_lemma xt1:
  shows 
    "\<lbrakk>a = b; c <\<^sub>o\<^sub>w b\<rbrakk> \<Longrightarrow> c <\<^sub>o\<^sub>w a"
    "\<lbrakk>b <\<^sub>o\<^sub>w a; b = c\<rbrakk> \<Longrightarrow> c <\<^sub>o\<^sub>w a"
    "\<lbrakk>a = b; c \<le>\<^sub>o\<^sub>w b\<rbrakk> \<Longrightarrow> c \<le>\<^sub>o\<^sub>w a"
    "\<lbrakk>b \<le>\<^sub>o\<^sub>w a; b = c\<rbrakk> \<Longrightarrow> c \<le>\<^sub>o\<^sub>w a"
    "\<lbrakk>y \<in> U; x \<in> U; y \<le>\<^sub>o\<^sub>w x; x \<le>\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> x = y"
    "\<lbrakk>y \<in> U; x \<in> U; z \<in> U; y \<le>\<^sub>o\<^sub>w x; z \<le>\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> z \<le>\<^sub>o\<^sub>w x"
    "\<lbrakk>y \<in> U; x \<in> U; z \<in> U; y <\<^sub>o\<^sub>w x; z \<le>\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> z <\<^sub>o\<^sub>w x"
    "\<lbrakk>y \<in> U; x \<in> U; z \<in> U; y \<le>\<^sub>o\<^sub>w x; z <\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> z <\<^sub>o\<^sub>w x"
    "\<lbrakk>b \<in> U; a \<in> U; b <\<^sub>o\<^sub>w a; a <\<^sub>o\<^sub>w b\<rbrakk> \<Longrightarrow> P"
    "\<lbrakk>y \<in> U; x \<in> U; z \<in> U; y <\<^sub>o\<^sub>w x; z <\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> z <\<^sub>o\<^sub>w x"
    "\<lbrakk>b \<in> U; a \<in> U; b \<le>\<^sub>o\<^sub>w a; a \<noteq> b\<rbrakk> \<Longrightarrow> b <\<^sub>o\<^sub>w a"
    "\<lbrakk>a \<in> U; b \<in> U; a \<noteq> b; b \<le>\<^sub>o\<^sub>w a\<rbrakk> \<Longrightarrow> b <\<^sub>o\<^sub>w a"
    "\<lbrakk>
      b \<in> U;
      c \<in> U;
      a = f b;
      c <\<^sub>o\<^sub>w b;
      \<And>x y. \<lbrakk>x \<in> U; y \<in> U; y <\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> f y <\<^sub>o\<^sub>w f x
     \<rbrakk> \<Longrightarrow> f c <\<^sub>o\<^sub>w a"
    "\<lbrakk>
      b \<in> U;
      a \<in> U;
      b <\<^sub>o\<^sub>w a;
      f b = c;
      \<And>x y. \<lbrakk>x \<in> U; y \<in> U; y <\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> f y <\<^sub>o\<^sub>w f x
      \<rbrakk> \<Longrightarrow> c <\<^sub>o\<^sub>w f a"
    "\<lbrakk>
      b \<in> U;
      c \<in> U;
      a = f b;
      c \<le>\<^sub>o\<^sub>w b;
      \<And>x y. \<lbrakk>x \<in> U; y \<in> U; y \<le>\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> f y \<le>\<^sub>o\<^sub>w f x
     \<rbrakk> \<Longrightarrow> f c \<le>\<^sub>o\<^sub>w a"
    "\<lbrakk>
      b \<in> U; 
      a \<in> U; 
      b \<le>\<^sub>o\<^sub>w a; 
      f b = c; 
      \<And>x y. \<lbrakk>x \<in> U; y \<in> U; y \<le>\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> f y \<le>\<^sub>o\<^sub>w f x
     \<rbrakk> \<Longrightarrow> c \<le>\<^sub>o\<^sub>w f a"
    is Orderings.xt1.

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting order_ow_axioms
  eliminating through (simp add: mono_ow_def)
begin

tts_lemma coinduct3_mono_lemma:
  assumes "\<forall>x\<in>U. f x \<subseteq> U\<^sub>2"
    and "X \<subseteq> U\<^sub>2"
    and "B \<subseteq> U\<^sub>2"
    and "on U with (\<subseteq>) (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>mono\<guillemotright> f"
  shows "on U with (\<subseteq>) (\<le>\<^sub>o\<^sub>w) : \<guillemotleft>mono\<guillemotright> (\<lambda>x. f x \<union> (X \<union> B))"
    is Inductive.coinduct3_mono_lemma.

end

end

context ord_order_ow 
begin

tts_context
  tts: (?'a to U\<^sub>2) and (?'b to U\<^sub>1)
  sbterms: (\<open>(\<le>)::[?'a::order, ?'a::order] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2)\<close>) 
    and (\<open>(<)::[?'a::order, ?'a::order] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w\<^sub>.\<^sub>2)\<close>) 
    and (\<open>(\<le>)::[?'b::ord, ?'b::ord] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1)\<close>) 
    and (\<open>(<)::[?'b::ord, ?'b::ord] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w\<^sub>.\<^sub>1)\<close>) 
  rewriting ctr_simps
  substituting ord\<^sub>2.order_ow_axioms
  eliminating through clarsimp
begin

tts_lemma xt2:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "b \<in> U\<^sub>1"
    and "a \<in> U\<^sub>2"
    and "c \<in> U\<^sub>1"
    and "f b \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 a"
    and "c \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 b"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 x\<rbrakk> \<Longrightarrow> f y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x"
  shows "f c \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 a"
  is Orderings.xt2.
    
tts_lemma xt6:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "b \<in> U\<^sub>1"
    and "a \<in> U\<^sub>2"
    and "c \<in> U\<^sub>1"
    and "f b \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 a"
    and "c <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 b"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; y <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 x\<rbrakk> \<Longrightarrow> f y <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x"
  shows "f c <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 a"
    is Orderings.xt6.

end

end

context order_pair_ow 
begin

tts_context
  tts: (?'a to U\<^sub>1) and (?'b to U\<^sub>2)
  rewriting ctr_simps
  substituting ord\<^sub>1.order_ow_axioms and ord\<^sub>2.order_ow_axioms
  eliminating through
    (
      unfold
        strict_mono_ow_def
        mono_ow_def
        antimono_ow_def
        bdd_above_ow_def
        bdd_below_ow_def,
      clarsimp
    )
begin

tts_lemma antimonoD:
  assumes "x \<in> U\<^sub>1"
    and "y \<in> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>antimono\<guillemotright> f"
    and "x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y"
  shows "f y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x"
    is Orderings.antimonoD.
    
tts_lemma monoD:
  assumes "x \<in> U\<^sub>1"
    and "y \<in> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
    and "x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y"
  shows "f x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y"
    is Orderings.monoD.
    
tts_lemma strict_monoD:
  assumes "x \<in> U\<^sub>1"
    and "y \<in> U\<^sub>1"
    and "on U\<^sub>1 with (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>strict_mono\<guillemotright> f"
    and "x <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y"
  shows "f x <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y"
    is Orderings.strict_monoD.
    
tts_lemma strict_monoI:
  assumes "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; x <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y\<rbrakk> \<Longrightarrow> f x <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y"
  shows "on U\<^sub>1 with (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>strict_mono\<guillemotright> f"
    is Orderings.strict_monoI.
    
tts_lemma antimonoI:
  assumes "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y\<rbrakk> \<Longrightarrow> f y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x"
  shows "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>antimono\<guillemotright> f"
    is Orderings.antimonoI.
    
tts_lemma monoI:
  assumes "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y"
  shows "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
    is Orderings.monoI.
    
tts_lemma antimonoE:
  assumes "x \<in> U\<^sub>1"
    and "y \<in> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>antimono\<guillemotright> f"
    and "x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y"
    and "f y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x \<Longrightarrow> thesis"
  shows thesis
    is Orderings.antimonoE.

tts_lemma monoE:
  assumes "x \<in> U\<^sub>1"
    and "y \<in> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
    and "x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y"
    and "f x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y \<Longrightarrow> thesis"
  shows thesis
    is Orderings.monoE.

tts_lemma strict_mono_mono:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "on U\<^sub>1 with (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>strict_mono\<guillemotright> f"
  shows "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
    is Orderings.strict_mono_mono.
    
tts_lemma bdd_below_image_antimono:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "A \<subseteq> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>antimono\<guillemotright> f"
    and "ord\<^sub>1.bdd_above A"
  shows "ord\<^sub>2.bdd_below (f ` A)"
    is Conditionally_Complete_Lattices.bdd_below_image_antimono.

tts_lemma bdd_above_image_antimono:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "A \<subseteq> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>antimono\<guillemotright> f"
    and "ord\<^sub>1.bdd_below A"
  shows "ord\<^sub>2.bdd_above (f ` A)"
    is Conditionally_Complete_Lattices.bdd_above_image_antimono.

tts_lemma bdd_below_image_mono:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "A \<subseteq> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
    and "ord\<^sub>1.bdd_below A"
  shows "ord\<^sub>2.bdd_below (f ` A)"
    is Conditionally_Complete_Lattices.bdd_below_image_mono.
    
tts_lemma bdd_above_image_mono:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "A \<subseteq> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
    and "ord\<^sub>1.bdd_above A"
  shows "ord\<^sub>2.bdd_above (f ` A)"
    is Conditionally_Complete_Lattices.bdd_above_image_mono.

tts_lemma strict_mono_leD:
  assumes "\<forall>x\<in>U\<^sub>1. r x \<in> U\<^sub>2"
    and "m \<in> U\<^sub>1"
    and "n \<in> U\<^sub>1"
    and "on U\<^sub>1 with (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>strict_mono\<guillemotright> r"
    and "m \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 n"
  shows "r m \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 r n"
    is Topological_Spaces.strict_mono_leD.

tts_lemma mono_image_least:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "m \<in> U\<^sub>1"
    and "n \<in> U\<^sub>1"
    and "m' \<in> U\<^sub>2"
    and "n' \<in> U\<^sub>2"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
    and "f ` (on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : {m..<n}) = 
      (on U\<^sub>2 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (<\<^sub>o\<^sub>w\<^sub>.\<^sub>2) : {m'..<n'})"
    and "m <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 n"
  shows "f m = m'"
    is Set_Interval.mono_image_least.

end

tts_context
  tts: (?'a to U\<^sub>1) and (?'b to U\<^sub>2)
  sbterms: (\<open>(\<le>)::[?'a::order, ?'a::order] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1)\<close>) 
    and (\<open>(<)::[?'a::order, ?'a::order] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w\<^sub>.\<^sub>1)\<close>) 
    and (\<open>(\<le>)::[?'b::order, ?'b::order] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2)\<close>) 
    and (\<open>(<)::[?'b::order, ?'b::order] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w\<^sub>.\<^sub>2)\<close>)
  rewriting ctr_simps
  substituting ord\<^sub>1.order_ow_axioms and ord\<^sub>2.order_ow_axioms
  eliminating through clarsimp
begin

tts_lemma xt3:
  assumes "b \<in> U\<^sub>1"
    and "a \<in> U\<^sub>1"
    and "c \<in> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "b \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 a"
    and "c \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f b"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 x\<rbrakk> \<Longrightarrow> f y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x"
  shows "c \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f a"
    is Orderings.xt3.
    
tts_lemma xt4:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "b \<in> U\<^sub>2"
    and "a \<in> U\<^sub>1"
    and "c \<in> U\<^sub>2"
    and "f b <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 a"
    and "c \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 b"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>2; y \<in> U\<^sub>2; y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 x\<rbrakk> \<Longrightarrow> f y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f x"
  shows "f c <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 a"
    is Orderings.xt4.
    
tts_lemma xt5:
  assumes "b \<in> U\<^sub>1"
    and "a \<in> U\<^sub>1"
    and "c \<in> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "b <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 a"
    and "c \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f b"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; y <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 x\<rbrakk> \<Longrightarrow> f y <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x"
  shows "c <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f a"
    is Orderings.xt5.
    
tts_lemma xt7:
  assumes "b \<in> U\<^sub>1"
    and "a \<in> U\<^sub>1"
    and "c \<in> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "b \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 a"
    and "c <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f b"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 x\<rbrakk> \<Longrightarrow> f y \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x"
  shows "c <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f a"
    is Orderings.xt7.

tts_lemma xt8:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "b \<in> U\<^sub>2"
    and "a \<in> U\<^sub>1"
    and "c \<in> U\<^sub>2"
    and "f b <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 a"
    and "c <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 b"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>2; y \<in> U\<^sub>2; y <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 x\<rbrakk> \<Longrightarrow> f y <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f x"
  shows "f c <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 a"
    is Orderings.xt8.

tts_lemma xt9:
  assumes "b \<in> U\<^sub>1"
    and "a \<in> U\<^sub>1"
    and "c \<in> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "b <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 a"
    and "c <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f b"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; y <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 x\<rbrakk> \<Longrightarrow> f y <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f x"
  shows "c <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f a"
    is Orderings.xt9.

end

tts_context
  tts: (?'a to U\<^sub>1) and (?'b to U\<^sub>2)
  sbterms: (\<open>(\<le>)::[?'a::order, ?'a::order] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1)\<close>) 
    and (\<open>(<)::[?'a::order, ?'a::order] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w\<^sub>.\<^sub>1)\<close>)  
    and (\<open>(\<le>)::[?'b::order, ?'b::order] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2)\<close>) 
    and (\<open>(<)::[?'b::order, ?'b::order] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w\<^sub>.\<^sub>2)\<close>)
  rewriting ctr_simps
  substituting ord\<^sub>1.order_ow_axioms and ord\<^sub>2.order_ow_axioms
  eliminating through simp
begin

tts_lemma order_less_subst1:
  assumes "a \<in> U\<^sub>1"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "b \<in> U\<^sub>2"
    and "c \<in> U\<^sub>2"
    and "a <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f b"
    and "b <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>2; y \<in> U\<^sub>2; x <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 y\<rbrakk> \<Longrightarrow> f x <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f y"
  shows "a <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f c"
    is Orderings.order_less_subst1.
    
tts_lemma order_subst1:
  assumes "a \<in> U\<^sub>1"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U\<^sub>1"
    and "b \<in> U\<^sub>2"
    and "c \<in> U\<^sub>2"
    and "a \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f b"
    and "b \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>2; y \<in> U\<^sub>2; x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 y\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f y"
  shows "a \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 f c"
    is Orderings.order_subst1.

end

tts_context
  tts: (?'a to U\<^sub>1) and (?'c to U\<^sub>2)
  sbterms: (\<open>(\<le>)::[?'a::order, ?'a::order] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1)\<close>) 
    and (\<open>(<)::[?'a::order, ?'a::order] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w\<^sub>.\<^sub>1)\<close>) 
    and (\<open>(\<le>)::[?'c::order, ?'c::order] \<Rightarrow> bool\<close> to \<open>(\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2)\<close>) 
    and (\<open>(<)::[?'c::order, ?'c::order] \<Rightarrow> bool\<close> to \<open>(<\<^sub>o\<^sub>w\<^sub>.\<^sub>2)\<close>)
  rewriting ctr_simps
  substituting ord\<^sub>1.order_ow_axioms and ord\<^sub>2.order_ow_axioms
  eliminating through simp
begin

tts_lemma order_less_le_subst2:
  assumes "a \<in> U\<^sub>1"
    and "b \<in> U\<^sub>1"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "c \<in> U\<^sub>2"
    and "a <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 b"
    and "f b \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; x <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y\<rbrakk> \<Longrightarrow> f x <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y"
  shows "f a <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    is Orderings.order_less_le_subst2.
    
tts_lemma order_le_less_subst2:
  assumes "a \<in> U\<^sub>1"
    and "b \<in> U\<^sub>1"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "c \<in> U\<^sub>2"
    and "a \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 b"
    and "f b <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y"
  shows "f a <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    is Orderings.order_le_less_subst2.
    
tts_lemma order_less_subst2:
  assumes "a \<in> U\<^sub>1"
    and "b \<in> U\<^sub>1"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "c \<in> U\<^sub>2"
    and "a <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 b"
    and "f b <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; x <\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y\<rbrakk> \<Longrightarrow> f x <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y"
  shows "f a <\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    is Orderings.order_less_subst2.

tts_lemma order_subst2:
  assumes "a \<in> U\<^sub>1"
    and "b \<in> U\<^sub>1"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "c \<in> U\<^sub>2"
    and "a \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 b"
    and "f b \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>1; y \<in> U\<^sub>1; x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 y\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f y"
  shows "f a \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 c"
    is Orderings.order_subst2.

end

end



subsection\<open>Dense orders\<close>


subsubsection\<open>Definitions and common properties\<close>

locale dense_order_ow = order_ow U le ls
  for U :: "'ao set" and le ls +
  assumes dense: "\<lbrakk> x \<in> U; y \<in> U; x <\<^sub>o\<^sub>w y \<rbrakk> \<Longrightarrow> (\<exists>z\<in>U. x <\<^sub>o\<^sub>w z \<and> z <\<^sub>o\<^sub>w y)"


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma dense_order_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      (dense_order_ow (Collect (Domainp A))) class.dense_order"
  unfolding 
    dense_order_ow_def class.dense_order_def
    dense_order_ow_axioms_def class.dense_order_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp
  
end



subsection\<open>
Partial orders with the greatest element and 
partial orders with the least elements
\<close>


subsubsection\<open>Definitions and common properties\<close>

locale ordering_top_ow = ordering_ow U le ls 
  for U :: "'ao set" and le ls  +
  fixes top :: "'ao" ("\<^bold>\<top>\<^sub>o\<^sub>w")
  assumes top_closed[simp]: "\<^bold>\<top>\<^sub>o\<^sub>w \<in> U"
  assumes extremum[simp]: "a \<in> U \<Longrightarrow> a \<^bold>\<le>\<^sub>o\<^sub>w \<^bold>\<top>\<^sub>o\<^sub>w"
begin

notation top ("\<^bold>\<top>\<^sub>o\<^sub>w")

end

locale bot_ow = 
  fixes U :: "'ao set" and bot (\<open>\<bottom>\<^sub>o\<^sub>w\<close>)
  assumes bot_closed[simp]: "\<bottom>\<^sub>o\<^sub>w \<in> U"
begin

notation bot (\<open>\<bottom>\<^sub>o\<^sub>w\<close>)

end

locale bot_pair_ow = ord\<^sub>1: bot_ow U\<^sub>1 bot\<^sub>1 + ord\<^sub>2: bot_ow U\<^sub>2 bot\<^sub>2
  for U\<^sub>1 :: "'ao set" and bot\<^sub>1 and U\<^sub>2 :: "'bo set" and bot\<^sub>2
begin

notation bot\<^sub>1 (\<open>\<bottom>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close>)
notation bot\<^sub>2 (\<open>\<bottom>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close>)

end

locale order_bot_ow = order_ow U le ls + bot_ow U bot
  for U :: "'ao set" and bot le ls  +
  assumes bot_least: "a \<in> U \<Longrightarrow> \<bottom>\<^sub>o\<^sub>w \<le>\<^sub>o\<^sub>w a"
begin

sublocale bot: ordering_top_ow U \<open>(\<ge>\<^sub>o\<^sub>w)\<close> \<open>(>\<^sub>o\<^sub>w)\<close> \<open>\<bottom>\<^sub>o\<^sub>w\<close>
  apply unfold_locales
  subgoal by simp
  subgoal by (simp add: bot_least)
  done

no_notation le (infix "\<^bold>\<le>\<^sub>o\<^sub>w" 50)
  and ls (infix "\<^bold><\<^sub>o\<^sub>w" 50)
  and top ("\<^bold>\<top>\<^sub>o\<^sub>w")

end

locale order_bot_pair_ow = 
  ord\<^sub>1: order_bot_ow U\<^sub>1 bot\<^sub>1 le\<^sub>1 ls\<^sub>1 + ord\<^sub>2: order_bot_ow U\<^sub>2 bot\<^sub>2 le\<^sub>2 ls\<^sub>2 
  for U\<^sub>1 :: "'ao set" and bot\<^sub>1 le\<^sub>1 ls\<^sub>1 and U\<^sub>2 :: "'bo set" and bot\<^sub>2 le\<^sub>2 ls\<^sub>2  
begin

sublocale bot_pair_ow ..
sublocale order_pair_ow ..

end


locale top_ow = 
  fixes U :: "'ao set" and top (\<open>\<top>\<^sub>o\<^sub>w\<close>)
  assumes top_closed[simp]: "\<top>\<^sub>o\<^sub>w \<in> U"
begin

notation top (\<open>\<top>\<^sub>o\<^sub>w\<close>)

end

locale top_pair_ow = ord\<^sub>1: top_ow U\<^sub>1 top\<^sub>1 + ord\<^sub>2: top_ow U\<^sub>2 top\<^sub>2
  for U\<^sub>1 :: "'ao set" and top\<^sub>1 and U\<^sub>2 :: "'bo set" and top\<^sub>2
begin

notation top\<^sub>1 (\<open>\<top>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close>)
notation top\<^sub>2 (\<open>\<top>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close>)

end

locale order_top_ow = order_ow U le ls + top_ow U top
  for U :: "'ao set" and le ls top  +
  assumes top_greatest: "a \<in> U \<Longrightarrow> a \<le>\<^sub>o\<^sub>w \<top>\<^sub>o\<^sub>w"
begin

sublocale top: ordering_top_ow U \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> \<open>\<top>\<^sub>o\<^sub>w\<close>
  apply unfold_locales
  subgoal by simp
  subgoal by (simp add: top_greatest)
  done

no_notation le (infix "\<^bold>\<le>\<^sub>o\<^sub>w" 50)
  and ls (infix "\<^bold><\<^sub>o\<^sub>w" 50)
  and top ("\<^bold>\<top>\<^sub>o\<^sub>w")

end

locale order_top_pair_ow = 
  ord\<^sub>1: order_top_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 top\<^sub>1 + ord\<^sub>2: order_top_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2 top\<^sub>2
  for U\<^sub>1 :: "'ao set" and le\<^sub>1 ls\<^sub>1 top\<^sub>1 and U\<^sub>2 :: "'bo set" and le\<^sub>2 ls\<^sub>2 top\<^sub>2 
begin

sublocale top_pair_ow ..
sublocale order_pair_ow ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma ordering_top_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> A ===> (=)) 
      (ordering_top_ow (Collect (Domainp A))) ordering_top"
proof-
  let ?P = "((A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> A ===> (=))"
  let ?ordering_top_ow = "ordering_top_ow (Collect (Domainp A))"
  have 
    "?P ?ordering_top_ow (\<lambda>le ls ext. ext \<in> UNIV \<and> ordering_top le ls ext)"
    unfolding 
      ordering_top_ow_def ordering_top_def
      ordering_top_ow_axioms_def ordering_top_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by blast 
  thus ?thesis by simp
qed

lemma order_bot_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A"
  shows 
    "(A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=)) 
      (order_bot_ow (Collect (Domainp A))) class.order_bot"
proof-
  let ?P = "(A ===> (A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> (=))"
  let ?order_bot_ow = "order_bot_ow (Collect (Domainp A))"
  have 
    "?P ?order_bot_ow (\<lambda>bot le ls. bot \<in> UNIV \<and> class.order_bot bot le ls)"
    unfolding 
      class.order_bot_def order_bot_ow_def 
      class.order_bot_axioms_def order_bot_ow_axioms_def
      bot_ow_def
    apply transfer_prover_start
    apply transfer_step+
    by blast 
  thus ?thesis by simp
qed

lemma order_top_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> A ===> (=)) 
      (order_top_ow (Collect (Domainp A))) class.order_top"
proof-
  let ?P = "((A ===> A ===> (=)) ===> (A ===> A ===> (=)) ===> A ===> (=))"
  let ?order_top_ow = "order_top_ow (Collect (Domainp A))"
  have 
    "?P ?order_top_ow (\<lambda>le ls top. top \<in> UNIV \<and> class.order_top le ls top)"
    unfolding 
      class.order_top_def order_top_ow_def 
      class.order_top_axioms_def order_top_ow_axioms_def
      top_ow_def
    apply transfer_prover_start
    apply transfer_step+
    by blast 
  thus ?thesis by simp
qed
  
end


subsubsection\<open>Relativization\<close>

context ordering_top_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting ordering_top_ow_axioms
  eliminating through simp
  applying [OF top_closed]
begin

tts_lemma extremum_uniqueI:
  assumes "\<^bold>\<top>\<^sub>o\<^sub>w \<^bold>\<le>\<^sub>o\<^sub>w \<^bold>\<top>\<^sub>o\<^sub>w"
  shows "\<^bold>\<top>\<^sub>o\<^sub>w = \<^bold>\<top>\<^sub>o\<^sub>w"
    is ordering_top.extremum_uniqueI.
    
tts_lemma extremum_unique:
  shows "(\<^bold>\<top>\<^sub>o\<^sub>w \<^bold>\<le>\<^sub>o\<^sub>w \<^bold>\<top>\<^sub>o\<^sub>w) = (\<^bold>\<top>\<^sub>o\<^sub>w = \<^bold>\<top>\<^sub>o\<^sub>w)"
    is ordering_top.extremum_unique.
    
tts_lemma extremum_strict:
  shows "\<not> \<^bold>\<top>\<^sub>o\<^sub>w \<^bold><\<^sub>o\<^sub>w \<^bold>\<top>\<^sub>o\<^sub>w"
    is ordering_top.extremum_strict.
    
tts_lemma not_eq_extremum:
  shows "(\<^bold>\<top>\<^sub>o\<^sub>w \<noteq> \<^bold>\<top>\<^sub>o\<^sub>w) = (\<^bold>\<top>\<^sub>o\<^sub>w \<^bold><\<^sub>o\<^sub>w \<^bold>\<top>\<^sub>o\<^sub>w)"
    is ordering_top.not_eq_extremum.

end
  
end

context order_bot_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting order_bot_ow_axioms
  eliminating through simp
begin

tts_lemma bdd_above_bot:
  assumes "A \<subseteq> U"
  shows "bdd_below A"
    is order_bot_class.bdd_above_bot.

tts_lemma not_less_bot:
  assumes "a \<in> U"
  shows "\<not> a <\<^sub>o\<^sub>w \<bottom>\<^sub>o\<^sub>w"
  is order_bot_class.not_less_bot.
    
tts_lemma max_bot:
  assumes "x \<in> U"
  shows "max \<bottom>\<^sub>o\<^sub>w x = x"
    is order_bot_class.max_bot.

tts_lemma max_bot2:
  assumes "x \<in> U"
  shows "max x \<bottom>\<^sub>o\<^sub>w = x"
    is order_bot_class.max_bot2.

tts_lemma min_bot:
  assumes "x \<in> U"
  shows "min \<bottom>\<^sub>o\<^sub>w x = \<bottom>\<^sub>o\<^sub>w"
    is order_bot_class.min_bot.

tts_lemma min_bot2:
  assumes "x \<in> U"
  shows "min x \<bottom>\<^sub>o\<^sub>w = \<bottom>\<^sub>o\<^sub>w"
    is order_bot_class.min_bot2.

tts_lemma bot_unique:
  assumes "a \<in> U"
  shows "(a \<le>\<^sub>o\<^sub>w \<bottom>\<^sub>o\<^sub>w) = (a = \<bottom>\<^sub>o\<^sub>w)"
    is order_bot_class.bot_unique.

tts_lemma bot_less:
  assumes "a \<in> U"
  shows "(a \<noteq> \<bottom>\<^sub>o\<^sub>w) = (\<bottom>\<^sub>o\<^sub>w <\<^sub>o\<^sub>w a)"
    is order_bot_class.bot_less.

tts_lemma atLeast_eq_UNIV_iff:
  assumes "x \<in> U"
  shows "({x..\<^sub>o\<^sub>w} = U) = (x = \<bottom>\<^sub>o\<^sub>w)"
    is order_bot_class.atLeast_eq_UNIV_iff.

tts_lemma le_bot:
  assumes "a \<in> U" and "a \<le>\<^sub>o\<^sub>w \<bottom>\<^sub>o\<^sub>w"
  shows "a = \<bottom>\<^sub>o\<^sub>w"
    is order_bot_class.le_bot.

end

end

context order_top_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting order_top_ow_axioms
  eliminating through simp
begin

tts_lemma bdd_above_top:
  assumes "A \<subseteq> U"
  shows "bdd_above A"
  is order_top_class.bdd_above_top.

tts_lemma not_top_less:
  assumes "a \<in> U"
  shows "\<not> \<top>\<^sub>o\<^sub>w <\<^sub>o\<^sub>w a"
    is order_top_class.not_top_less.

tts_lemma max_top:
  assumes "x \<in> U"
  shows "max \<top>\<^sub>o\<^sub>w x = \<top>\<^sub>o\<^sub>w"
    is order_top_class.max_top.

tts_lemma max_top2:
  assumes "x \<in> U"
  shows "max x \<top>\<^sub>o\<^sub>w = \<top>\<^sub>o\<^sub>w"
    is order_top_class.max_top2.

tts_lemma min_top:
  assumes "x \<in> U"
  shows "min \<top>\<^sub>o\<^sub>w x = x"
    is order_top_class.min_top.

tts_lemma min_top2:
  assumes "x \<in> U"
  shows "min x \<top>\<^sub>o\<^sub>w = x"
    is order_top_class.min_top2.

tts_lemma top_unique:
  assumes "a \<in> U"
  shows "(\<top>\<^sub>o\<^sub>w \<le>\<^sub>o\<^sub>w a) = (a = \<top>\<^sub>o\<^sub>w)"
    is order_top_class.top_unique.

tts_lemma less_top:
  assumes "a \<in> U"
  shows "(a \<noteq> \<top>\<^sub>o\<^sub>w) = (a <\<^sub>o\<^sub>w \<top>\<^sub>o\<^sub>w)"
    is order_top_class.less_top.

tts_lemma atMost_eq_UNIV_iff:
  assumes "x \<in> U"
  shows "({..\<^sub>o\<^sub>wx} = U) = (x = \<top>\<^sub>o\<^sub>w)"
    is order_top_class.atMost_eq_UNIV_iff.

tts_lemma top_le:
  assumes "a \<in> U" and "\<top>\<^sub>o\<^sub>w \<le>\<^sub>o\<^sub>w a"
  shows "a = \<top>\<^sub>o\<^sub>w"
    is order_top_class.top_le.

end

end

text\<open>\newpage\<close>

end