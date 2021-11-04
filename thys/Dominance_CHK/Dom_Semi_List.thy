(* Author: Nan Jiang *)

section \<open>A semilattice of reversed-ordered list\<close>

theory Dom_Semi_List
imports Main Semilat Sorted_List_Operations2 Sorted_Less2 Cfg
begin

type_synonym node = nat

context cfg_doms
begin 

definition nodes :: "nat list" 
  where "nodes \<equiv> (g_V G)"

definition nodes_le :: "node list \<Rightarrow> node list \<Rightarrow> bool" where
"nodes_le xs ys \<equiv> (sorted (rev ys) \<and> sorted (rev xs) \<and> (set ys) \<subseteq> (set xs)) \<or> xs = ys"

definition nodes_sup ::"node list  \<Rightarrow> node list   \<Rightarrow>node list " where
"nodes_sup = (\<lambda>x y. inter_sorted_rev x y)"

definition nodes_semi :: "node list sl" where
"nodes_semi  \<equiv> ((rev \<circ> sorted_list_of_set) ` (Pow (set (nodes))), nodes_le, nodes_sup )"

lemma subset_nodes_inpow: 
  assumes "sorted (rev xs)"
      and "set xs \<subseteq> set nodes"
    shows "xs \<in> (rev \<circ> sorted_list_of_set) ` (Pow (set nodes))"   
proof -
  from assms(1) have "(sorted_list_of_set (set xs)) = rev xs" by (auto intro:sorted_less_rev_set_eq)
  then have "rev (rev xs) = rev (sorted_list_of_set (set xs))" by simp
  with assms(2) show ?thesis by auto
qed

lemma nil_in_A: "[] \<in> (rev \<circ> sorted_list_of_set) ` (Pow (set nodes))"  
proof(simp add: Pow_def image_def)
  have "sorted_list_of_set {} = []" by auto
  then show "\<exists>x\<subseteq>set nodes. sorted_list_of_set x = []" by blast
qed

lemma single_n_in_A: "p < length nodes \<Longrightarrow> [p] \<in> (rev \<circ> sorted_list_of_set) ` (Pow (set nodes))"
proof (unfold nodes_def)
  let ?S = "(rev \<circ> sorted_list_of_set) ` (Pow (set (g_V G)))"
  assume "p < length (g_V G)"  
  then have p: "{p} \<in> Pow (set (g_V G))" by (auto simp add:Pow_def verts_set)
  then have "[p] \<in>?S" by (unfold image_def) force
  then show "[p] \<in> ?S" by auto
qed
    
lemma inpow_subset_nodes: 
  assumes "xs \<in> (rev \<circ> sorted_list_of_set) ` (Pow (set nodes))"
    shows "set xs \<subseteq> set nodes"
proof -
  from assms obtain x where x: "x \<in> Pow (set nodes)" and "xs = (rev \<circ> sorted_list_of_set) x" by auto
  then have eq: "set xs = set (sorted_list_of_set x)" by auto
  have "\<forall>x \<in> Pow (set nodes). finite x"  by (auto intro: rev_finite_subset)
  with x eq show "set xs \<subseteq> set nodes" by auto
qed

lemma inter_in_pow_nodes: 
  assumes "xs \<in> (rev \<circ> sorted_list_of_set) ` (Pow (set nodes))"
    shows "(rev \<circ> sorted_list_of_set)(set xs \<inter> set ys) \<in> (rev \<circ> (sorted_list_of_set)) ` (Pow (set nodes))"
  using assms
proof -  
  let ?res = "set xs \<inter> set ys"
  from assms have "set xs \<subseteq> set nodes" using inpow_subset_nodes by auto
  then have "?res \<subseteq> set nodes" by auto
  then show ?thesis using subset_nodes_inpow by auto
qed
  

lemma nodes_le_order: "order nodes_le ((rev \<circ> sorted_list_of_set) ` (Pow (set nodes)))"
proof -
  let ?A = "(rev \<circ> sorted_list_of_set) ` (Pow (set nodes))"

  have "\<forall>x \<in> ?A. sorted (rev x)" by (auto intro: sorted_less_sorted_list_of_set)
  then have "\<forall>x\<in>?A. nodes_le x x" by (auto simp add:nodes_le_def) 

  moreover have "\<forall>x\<in>?A. \<forall>y\<in>?A. (nodes_le x y \<and> nodes_le y x \<longrightarrow> x = y)" 
  proof (intro strip)
    fix x y   
    assume "x \<in> ?A" and "y \<in> ?A" and "nodes_le x y \<and> nodes_le y x"
    then have "sorted (rev x) \<and> sorted (rev (y::nat list)) \<and>  set x = set y \<or> x = y" 
      by (auto simp add: nodes_le_def intro:subset_antisym sorted_less_sorted_list_of_set)
   then show "x = y" by (auto dest: sorted_less_rev_set_unique)     
 qed

  moreover have "\<forall>x\<in> ?A.   \<forall>y\<in> ?A. \<forall>z\<in> ?A . nodes_le x y \<and> nodes_le y  z \<longrightarrow> nodes_le x z" 
    by (auto simp add: nodes_le_def) 

  ultimately show ?thesis by (unfold order_def lesub_def lesssub_def) fastforce
qed

lemma nodes_semi_auxi: 
  "let A = (rev \<circ> sorted_list_of_set) ` (Pow (set (nodes)));
       r = nodes_le;
       f = (\<lambda>x y.  (inter_sorted_rev x y))
    in semilat(A, r, f)"
proof -
  let ?A = "(rev \<circ> sorted_list_of_set) ` (Pow (set (nodes)))"
  let ?r = "nodes_le" 
  let ?f = "(\<lambda>x y. (inter_sorted_rev x y))"

  have "order ?r ?A" by (rule nodes_le_order)

  moreover have "closed ?A ?f" 
  proof (unfold closed_def, intro strip)
    fix xs ys assume xs_in: "xs \<in> ?A" and ys_in: "ys \<in> ?A"
    then have sorted_xs: "sorted (rev xs)" 
          and sorted_ys: "sorted (rev ys)" 
      by (auto intro: sorted_less_sorted_list_of_set)
    then have inter_xs_ys: "set (?f xs ys) = set xs \<inter> set ys" and 
              sorted_res: "sorted (rev (?f xs ys))"
      using inter_sorted_correct by auto

    from xs_in have "set xs \<subseteq> set nodes" using inpow_subset_nodes by auto
    with inter_xs_ys have "set (?f xs ys) \<subseteq> set nodes" by auto
    with sorted_res show "xs \<squnion>\<^bsub>?f\<^esub> ys\<in> ?A" using subset_nodes_inpow by (auto simp add:plussub_def)   
  qed

  moreover have "(\<forall>x\<in>?A. \<forall>y\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub> x \<squnion>\<^bsub>?f\<^esub> y) \<and> (\<forall>x\<in>?A. \<forall>y\<in>?A. y \<sqsubseteq>\<^bsub>?r\<^esub> x \<squnion>\<^bsub>?f\<^esub> y)" 
  proof(rule conjI, intro strip)   
    fix xs ys 
    assume xs_in: "xs \<in> ?A" and ys_in: "ys \<in> ?A"
    then have sorted_xs: "sorted (rev xs)" and sorted_ys: "sorted (rev ys)" 
      by (auto intro: sorted_less_sorted_list_of_set)
    then have "set (?f xs ys) \<subseteq> set xs" and sorted_f_xs_ys: "sorted (rev (?f xs ys))" 
      by (auto simp add: inter_sorted_correct)
    then show "xs \<sqsubseteq>\<^bsub>?r\<^esub> xs \<squnion>\<^bsub>?f\<^esub> ys"  by (simp add: lesub_def sorted_xs sorted_ys sorted_f_xs_ys nodes_le_def plussub_def)
  next
    show "\<forall>x\<in>?A. \<forall>y\<in>?A. y \<sqsubseteq>\<^bsub>?r\<^esub> x \<squnion>\<^bsub>?f\<^esub> y"
    proof (intro strip)
      fix xs ys 
      assume xs_in: "xs \<in> ?A" and ys_in: "ys \<in> ?A"
      then have sorted_xs: "sorted (rev xs)" and sorted_ys: "sorted (rev ys)" 
        by (auto intro: sorted_less_sorted_list_of_set)
      then have "set (?f xs ys) \<subseteq> set ys" and sorted_f_xs_ys: "sorted (rev (?f xs ys))" by (auto simp add: inter_sorted_correct)
      then show "ys \<sqsubseteq>\<^bsub>?r\<^esub> xs \<squnion>\<^bsub>?f\<^esub> ys" by (simp add: lesub_def sorted_ys sorted_xs sorted_f_xs_ys nodes_le_def plussub_def)
    qed
  qed

  moreover have "\<forall>x\<in>?A. \<forall>y\<in>?A. \<forall>z\<in>?A. x \<sqsubseteq>\<^bsub>?r\<^esub> z \<and> y  \<sqsubseteq>\<^bsub>?r\<^esub> z \<longrightarrow> x \<squnion>\<^bsub>?f\<^esub> y \<sqsubseteq>\<^bsub>?r\<^esub>z" 
  proof (intro strip)
    fix xs ys zs
    assume xin: "xs \<in> ?A" and yin: "ys \<in> ?A" and zin: "zs \<in> ?A" and "xs \<sqsubseteq>\<^bsub>?r\<^esub> zs \<and> ys \<sqsubseteq>\<^bsub>?r\<^esub> zs"
    then have xs_zs: "xs \<sqsubseteq>\<^bsub>?r\<^esub> zs" and ys_zs: "ys \<sqsubseteq>\<^bsub>?r\<^esub> zs" and sorted_xs: "sorted (rev xs)" and sorted_ys: "sorted (rev ys)" by (auto simp add: sorted_less_sorted_list_of_set)
    then have inter_xs_ys: "set (?f xs ys) = (set xs \<inter> set ys)" and sorted_f_xs_ys: "sorted (rev (?f xs ys))" 
      by (auto simp add: inter_sorted_correct)

    from xs_zs ys_zs sorted_xs have sorted_zs: "sorted (rev zs)"
                                and "set zs \<subseteq> set xs"
                                and "set zs \<subseteq> set ys" by (auto simp add: lesub_def nodes_le_def)
    then have zs: "set zs \<subseteq> set xs \<inter> set ys" by auto
    with inter_xs_ys sorted_zs sorted_f_xs_ys show "xs \<squnion>\<^bsub>?f\<^esub> ys \<sqsubseteq>\<^bsub>?r\<^esub> zs" 
      by (auto simp add:plussub_def lesub_def  sorted_xs sorted_ys sorted_f_xs_ys sorted_zs nodes_le_def)
  qed
  ultimately show ?thesis  by (unfold semilat_def) simp
qed

lemma nodes_semi_is_semilat: "semilat (nodes_semi)"
  using nodes_semi_auxi 
  by (auto simp add: nodes_sup_def nodes_semi_def)

lemma sorted_rev_subset_len_lt:
  assumes "sorted (rev a)"
      and "sorted (rev b)"
      and "set a \<subset> set b"
    shows "length a < length b" 
  using assms
proof-
  from assms(1) assms(2) have dist_a: "distinct a" and dist_b: "distinct b" by (auto dest: distinct_sorted_rev)
  from assms(3)  have "card (set a) < card (set b)" by (auto intro: psubset_card_mono)
  with dist_a dist_b show ?thesis by (auto simp add: distinct_card)
qed

lemma wf_nodes_le_auxi: "wf {(y, x). (sorted (rev y) \<and> sorted (rev x) \<and> set y \<subset> set x) \<and> x \<noteq> y}"
  apply(rule wf_measure [THEN wf_subset])
  apply(simp only: measure_def inv_image_def)
  apply clarify
  apply(frule sorted_rev_subset_len_lt)
    defer
    defer
    apply fastforce
  by (auto intro:sorted_less_rev_set_unique)

lemma wf_nodes_le_auxi2: 
  "wf {(y, x). sorted (rev y) \<and> sorted (rev x) \<and> set y \<subset> set x \<and> rev x \<noteq> rev y}" 
  using wf_nodes_le_auxi by auto
  
lemma  wf_nodes_le: "wf {(y, x). nodes_le x y \<and> x \<noteq> y}"
proof -
  have eq_set: "{(y, x). (sorted (rev y) \<and> sorted (rev x) \<and> set y \<subseteq> set x) \<and> x \<noteq> y} = 
                {(y, x). nodes_le x y \<and> x \<noteq> y}" by (unfold nodes_le_def) auto
  have "{(y, x). (sorted (rev y) \<and> sorted (rev x) \<and> set y \<subset> set x) \<and> x \<noteq> y} =
        {(y, x). (sorted (rev y) \<and> sorted (rev x) \<and> set y \<subseteq> set x) \<and> x \<noteq> y}"
    by (auto simp add:sorted_less_rev_set_unique)
  from this wf_nodes_le_auxi have "wf {(y, x). (sorted (rev y) \<and> sorted (rev x) \<and> set y \<subseteq> set x) \<and> x \<noteq> y}" by (rule subst)
  with eq_set show ?thesis by (rule subst)
qed

lemma acc_nodes_le: "acc nodes_le" 
  apply (unfold acc_def lesssub_def lesub_def)
  apply (rule wf_nodes_le)
  done

lemma acc_nodes_le2: "acc (fst (snd nodes_semi))"
  apply (unfold nodes_semi_def)
  apply (auto simp add: lesssub_def lesub_def intro: acc_nodes_le)
  done

lemma "top nodes_le [] (fst nodes_semi)"
  by(auto simp add: top_def nodes_semi_def nodes_le_def lesssub_def lesub_def sorted_less_sorted_list_of_set)

end 

end



