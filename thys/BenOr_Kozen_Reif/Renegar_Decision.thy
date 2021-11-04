theory Renegar_Decision
  imports "Renegar_Proofs"
    "BKR_Decision"
begin

(* Note that there is significant overlap between Renegar and BKR in general, so there is some
  similarity between this file and BKR_Decision.thy.  However, there are also notable differences
  as Renegar and BKR use different auxiliary polynomials in their decision procedures.

  In general, the _R's on definition and lemma names in this file are to emphasize that we are 
  working with Renegar style.

*)

section "Algorithm"

(* The set of all rational sign vectors for qs wrt the set S
  When S = UNIV, then this quantifies over all reals *)
definition consistent_sign_vectors_R::"real poly list \<Rightarrow> real set \<Rightarrow> rat list set"
  where "consistent_sign_vectors_R qs S = (consistent_sign_vec qs) ` S"

primrec prod_list_var:: "real poly list \<Rightarrow> real poly"
  where "prod_list_var  [] = 1"
  | "prod_list_var (h#T) = (if h = 0 then (prod_list_var T) else (h* prod_list_var T))"

primrec check_all_const_deg:: "real poly list \<Rightarrow> bool"
  where "check_all_const_deg  [] = True"
  | "check_all_const_deg (h#T) = (if degree h = 0 then (check_all_const_deg T) else False)"

definition poly_f :: "real poly list \<Rightarrow> real poly"
  where
    "poly_f ps = 
  (if (check_all_const_deg ps = True) then  [:0, 1:] else 
  (pderiv (prod_list_var ps)) * (prod_list_var ps)* ([:-(crb (prod_list_var ps)),1:]) * ([:(crb (prod_list_var ps)),1:]))"

definition find_consistent_signs_R :: "real poly list \<Rightarrow> rat list list"
  where
    "find_consistent_signs_R ps = find_consistent_signs_at_roots_R (poly_f ps) ps"

definition decide_universal_R :: "real poly fml \<Rightarrow> bool"
  where [code]:
    "decide_universal_R fml = (
    let (fml_struct,polys) = convert fml;
        conds = find_consistent_signs_R polys
    in
     list_all (lookup_sem fml_struct) conds
  )"

definition decide_existential_R :: "real poly fml \<Rightarrow> bool"
  where [code]:
    "decide_existential_R fml = (
    let (fml_struct,polys) = convert fml;
        conds = find_consistent_signs_R polys
    in
      find (lookup_sem fml_struct) conds \<noteq> None
  )"

subsection "Proofs"
definition roots_of_poly_f:: "real poly list \<Rightarrow> real set"
  where "roots_of_poly_f qs = {x. poly (poly_f qs) x = 0}"

lemma prod_list_var_nonzero:
  shows "prod_list_var qs \<noteq> 0"
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then show ?case by auto
qed

lemma q_dvd_prod_list_var_prop:
  assumes "q \<in> set qs"
  assumes "q \<noteq> 0"
  shows "q dvd prod_list_var qs" using assms
proof (induct qs)
  case Nil
  then show ?case by auto
next
  case (Cons a qs)
  then have eo: "q = a \<or>q \<in> set qs" by auto
  have c1: "q = a \<Longrightarrow> q dvd prod_list_var (a#qs)"
  proof - 
    assume "q = a"
    then have "prod_list_var (a#qs) = q*(prod_list_var qs)" using Cons.prems
      unfolding prod_list_var_def by auto
    then show ?thesis using prod_list_var_nonzero[of qs] by auto
  qed
  have c2: "q \<in> set qs \<longrightarrow> q dvd prod_list_var qs"
    using Cons.prems Cons.hyps unfolding prod_list_var_def by auto
  show ?case using eo c1 c2 by auto
qed


lemma check_all_const_deg_prop: 
  shows "check_all_const_deg l = True \<longleftrightarrow> (\<forall>p \<in> set(l). degree p = 0)"
proof (induct l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by auto
qed

(* lemma prod_zero shows that the product of the polynomial list is 0 at x iff there is a polynomial 
  in the list that is 0 at x *)
lemma poly_f_nonzero:
  fixes qs :: "real poly list"
  shows "(poly_f qs) \<noteq> 0"
proof - 
  have eo: "(\<forall>p \<in> set qs. degree p = 0) \<or> (\<exists>p \<in> set qs. degree p > 0)"
    by auto
  have c1: "(\<forall>p \<in> set qs. degree p = 0) \<longrightarrow> (poly_f qs) \<noteq> 0"
    unfolding poly_f_def using check_all_const_deg_prop by auto
  have c2: "(\<exists>p \<in> set qs. degree p > 0) \<longrightarrow> (poly_f qs) \<noteq> 0"
  proof clarsimp 
    fix q
    assume q_in: "q \<in> set qs"
    assume deg_q: "0 < degree q"
    assume contrad: "poly_f qs = 0"
    have nonconst: "check_all_const_deg qs = False" using deg_q check_all_const_deg_prop
        q_in by auto
    have h1: "prod_list_var qs \<noteq> 0" using prod_list_var_nonzero by auto
    then have "degree (prod_list_var qs) > 0" using q_in deg_q h1
    proof (induct qs)
      case Nil
      then show ?case by auto
    next
      case (Cons a qs)
      have q_nonz: "q \<noteq> 0" using Cons.prems by auto
      have q_ins: "q \<in> set (a # qs) " using Cons.prems by auto
      then have "q = a \<or> q \<in> set qs" by auto
      then have eo: " q = a \<or> List.member qs q" using in_set_member[of q qs]
        by auto
      have degq: "degree q > 0" using Cons.prems by auto
      have h2: "(prod_list (a # qs)) = a* (prod_list qs)"
        by auto
      have isa: "q = a \<longrightarrow> 0 < degree (prod_list_var (a # qs))" 
        using h2 degree_mult_eq_0[where p = "q", where q = "prod_list_var qs"]
          Cons.prems by auto
      have inl: "List.member qs q \<longrightarrow> 0 < degree (prod_list_var (a # qs))"
      proof - 
        have nonzprod: "prod_list_var (a # qs) \<noteq> 0" using prod_list_var_nonzero by auto
        have "q dvd prod_list_var (a # qs)"
          using q_dvd_prod_list_var_prop[where q = "q", where qs = "(a#qs)"] q_nonz q_ins
          by auto
        then show ?thesis using divides_degree[where p = "q", where q = "prod_list_var (a # qs)"] nonzprod degq
          by auto
      qed
      then show ?case using eo isa by auto
    qed
    then have h2: "pderiv (prod_list_var qs) \<noteq> 0" using pderiv_eq_0_iff[where p = "prod_list_var qs"] 
      by auto
    then have "pderiv (prod_list_var qs) * prod_list_var qs \<noteq> 0" 
      using prod_list_var_nonzero h2 by auto
    then show "False" using contrad nonconst unfolding poly_f_def deg_q
      by (smt (z3) mult_eq_0_iff pCons_eq_0_iff) 
  qed
  show ?thesis using eo c1 c2 by auto
qed

lemma poly_f_roots_prop_1: 
  fixes qs:: "real poly list"
  assumes non_const: "check_all_const_deg qs = False"
  shows "\<forall>x1. \<forall>x2. ((x1 < x2 \<and> (\<exists>q1 \<in> set (qs). q1 \<noteq> 0 \<and> (poly q1 x1) = 0) \<and> (\<exists>q2\<in> set(qs). q2 \<noteq> 0 \<and> (poly q2 x2) = 0)) \<longrightarrow> (\<exists>q. x1 < q \<and> q < x2 \<and> poly (poly_f qs) q = 0))"
proof clarsimp
  fix x1:: "real"
  fix x2:: "real"
  fix q1:: "real poly"
  fix q2:: "real poly"
  assume "x1 < x2"
  assume q1_in: "q1 \<in> set qs"
  assume q1_0: "poly q1 x1 = 0"
  assume q1_nonz: "q1 \<noteq> 0"
  assume q2_in: "q2 \<in> set qs"
  assume q2_0: "poly q2 x2 = 0"
  assume q2_nonz: "q2 \<noteq> 0"
  have prod_z_x1: "poly (prod_list_var qs) x1 = 0" using q1_in q1_0
    using q1_nonz q_dvd_prod_list_var_prop[of q1 qs] by auto
  have prod_z_x2: "poly (prod_list_var qs) x2 = 0" using q2_in q2_0 
    using q2_nonz q_dvd_prod_list_var_prop[of q2 qs] by auto 
  have "\<exists>w>x1. w < x2 \<and> poly (pderiv (prod_list_var qs)) w = 0" 
    using Rolle_pderiv[where q = "prod_list_var qs"] prod_z_x1 prod_z_x2
    using \<open>x1 < x2\<close> by blast
  then obtain w where w_def: "w > x1 \<and>w < x2 \<and> poly (pderiv (prod_list_var qs)) w = 0"
    by auto
  then have "poly (poly_f qs) w = 0"
    unfolding poly_f_def using non_const
    by simp
  then show "\<exists>q>x1. q < x2 \<and> poly (poly_f qs) q = 0"
    using w_def by blast 
qed 

lemma main_step_aux1_R:
  fixes qs:: "real poly list"
  assumes non_const: "check_all_const_deg qs = True"
  shows "set (find_consistent_signs_R qs) =  consistent_sign_vectors_R qs UNIV"
proof - 
  have poly_f_is: "poly_f qs = [:0, 1:]" unfolding poly_f_def using assms 

    by auto
  have same: "set (find_consistent_signs_at_roots_R [:0, 1:] qs) =
  set (characterize_consistent_signs_at_roots [:0, 1:] qs)" using find_consistent_signs_at_roots_R[of "[:0, 1:]" qs] 
    by auto 
  have rech: "(sorted_list_of_set {x. poly ([:0, 1:]::real poly) x = 0}) = [0]" by auto
  have alldeg0: "(\<forall>p \<in> set qs. degree p = 0)" using non_const check_all_const_deg_prop
    by auto
  then have allconst: "\<forall>p \<in> set qs. (\<exists>(k::real). p = [:k:])"
    apply (auto)
    by (meson degree_eq_zeroE) 
  then have allconstvar: "\<forall>p \<in> set qs. \<forall>(x::real). \<forall>(y::real). poly p x = poly p y"
    by fastforce
  have e1: "set (remdups (map (signs_at qs) [0])) \<subseteq>
    consistent_sign_vectors_R qs UNIV"
    unfolding signs_at_def squash_def consistent_sign_vectors_R_def consistent_sign_vec_def apply (simp)
    by (smt (verit, best) class_ring.ring_simprules(2) comp_def image_iff length_map map_nth_eq_conv)
  have e2: "consistent_sign_vectors_R qs UNIV \<subseteq> set (remdups (map (signs_at qs) [0])) "
    unfolding signs_at_def squash_def consistent_sign_vectors_R_def consistent_sign_vec_def apply (simp)
    using allconstvar
    by (smt (verit, best) comp_apply image_iff insert_iff map_eq_conv subsetI) 
  have "set (remdups (map (signs_at qs) [0])) =
    consistent_sign_vectors_R qs UNIV" 
    using e1 e2 by auto
  then have "set (characterize_consistent_signs_at_roots [:0, 1:] qs) = consistent_sign_vectors_R qs UNIV"
    unfolding characterize_consistent_signs_at_roots_def characterize_root_list_p_def 
    using rech by auto
  then show ?thesis using same poly_f_is unfolding find_consistent_signs_R_def 
    by auto
qed

lemma sorted_list_lemma_var:
  fixes l:: "real list"
  fixes x:: "real"
  assumes "length l > 1"
  assumes strict_sort: "strict_sorted l"
  assumes x_not_in: "\<not> (List.member l x)"
  assumes lt_a: "x > (l ! 0)"
  assumes b_lt: "x < (l ! (length l - 1))"
  shows "(\<exists>n. n < length l - 1 \<and> x > l ! n \<and> x < l !(n+1))" using assms 
proof (induct l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  have len_gteq: "length l \<ge> 1" using Cons.prems(1)
    by (metis One_nat_def Suc_eq_plus1 list.size(4) not_le not_less_eq) 
  have len_one: "length l = 1 \<Longrightarrow> (\<exists>n. n < length (a#l) - 1 \<and> x > (a#l) ! n \<and> x < (a#l) !(n+1))" 
  proof -
    assume len_is: "length l = 1"
    then have "x > (a#l) ! 0 \<and> x < (a#l) !1 " using Cons.prems(4) Cons.prems(5)
      by auto
    then show "(\<exists>n. n < length (a#l) - 1 \<and> x > (a#l) ! n \<and> x < (a#l) !(n+1))"  
      using len_is by auto
  qed
  have len_gt: "length l > 1 \<Longrightarrow> (\<exists>n. n < length (a#l) - 1 \<and> x > (a#l) ! n \<and> x < (a#l) !(n+1))"
  proof - 
    assume len_gt_one: "length l > 1"
    have eo: "x \<noteq> l ! 0" using Cons.prems(3) apply (auto)
      by (metis One_nat_def Suc_lessD in_set_member len_gt_one member_rec(1) nth_mem) 
    have c1: "x < l ! 0 \<Longrightarrow> (\<exists>n. n < length (a#l) - 1 \<and> x > (a#l) ! n \<and> x < (a#l) !(n+1)) "
    proof - 
      assume xlt: "x < l !0"
      then have "x < (a#l) ! 1 "
        by simp
      then show ?thesis  using  Cons.prems(4) len_gt_one apply (auto)
        using Cons.prems(4) Suc_lessD by blast 
    qed
    have c2: "x > l ! 0 \<Longrightarrow> (\<exists>n. n < length (a#l) - 1 \<and> x > (a#l) ! n \<and> x < (a#l) !(n+1)) "
    proof - 
      assume asm: "x > l ! 0"
      have xlt_1: " x < l ! (length l - 1)"
        using Cons.prems(5)
        by (metis Cons.prems(1) One_nat_def add_diff_cancel_right' list.size(4) nth_Cons_pos zero_less_diff) 
      have ssl: "strict_sorted l " using Cons.prems(2)
        using strict_sorted.simps(2) by blast  
      have " \<not> List.member l x" using Cons.prems(3)
        by (meson member_rec(1)) 
      then have " \<exists>n<length l - 1. l ! n < x \<and> x < l ! (n + 1)"
        using asm xlt_1 len_gt_one ssl Cons.hyps 
        by auto
      then show ?thesis
        by (metis One_nat_def Suc_eq_plus1 diff_Suc_1 less_diff_conv list.size(4) nth_Cons_Suc) 
    qed
    show "(\<exists>n. n < length (a#l) - 1 \<and> x > (a#l) ! n \<and> x < (a#l) !(n+1))"
      using eo c1 c2
      by (meson linorder_neqE_linordered_idom) 
  qed
  then show ?case 
    using len_gteq len_one len_gt 
    apply (auto)
    by (metis One_nat_def less_numeral_extra(1) linorder_neqE_nat not_less nth_Cons_0) 
qed

(* We want to show that our auxiliary polynomial has roots in all relevant intervals:
 so it captures all of the zeros, and also it captures all of the points in between! *)
lemma all_sample_points_prop:
  assumes is_not_const: "check_all_const_deg qs = False"
  assumes s_is: "S = (characterize_root_list_p (pderiv (prod_list_var qs) * (prod_list_var qs) * ([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])))"(* properties about S*)
  shows "consistent_sign_vectors_R qs UNIV = consistent_sign_vectors_R qs (set S)"
proof - 
  let ?zer_list = "sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (q \<noteq> 0 \<and> poly q x = 0))} :: real list"
  have strict_sorted_h: "strict_sorted ?zer_list" using sorted_sorted_list_of_set
      strict_sorted_iff by auto
  have poly_f_is: "poly_f qs  = (pderiv (prod_list_var qs) * prod_list_var qs)* ([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])"
    unfolding poly_f_def using is_not_const by auto
  then have set_S_char: "set S = ({x. poly (poly_f qs) x = 0}::real set)"
    using poly_roots_finite[of "poly_f qs"] set_sorted_list_of_set poly_f_nonzero[of qs] 
    using s_is unfolding characterize_root_list_p_def by auto
  have difficult_direction: "consistent_sign_vectors_R qs UNIV \<subseteq> consistent_sign_vectors_R qs (set S)"
  proof clarsimp
    fix x
    assume "x \<in> consistent_sign_vectors_R qs UNIV "
    then have "\<exists>y. x  = (consistent_sign_vec qs y)" unfolding consistent_sign_vectors_R_def by auto
    then obtain y where y_prop: "x = consistent_sign_vec qs y" by auto
    then have "\<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y" 
    proof - 
      have c1: "(\<exists>q \<in> (set qs). q \<noteq> 0 \<and> poly q y = 0) \<Longrightarrow> (\<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y)"
      proof - 
        assume "(\<exists>q \<in> (set qs). q \<noteq> 0 \<and> poly q y = 0)"
        then obtain q where "q \<in> (set qs) \<and> q \<noteq> 0 \<and> poly q y = 0" by auto
        then have "poly (prod_list_var qs) y = 0"
          using q_dvd_prod_list_var_prop[of q qs] by auto
        then have "poly (pderiv (prod_list_var qs) * (prod_list_var qs)*([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])) y = 0"
          by auto
        then have "y \<in> (set S)"
          using s_is unfolding characterize_root_list_p_def
        proof -
          have "y \<in> {r. poly (pderiv (prod_list_var qs) * (prod_list_var qs)*([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])) r = 0}"
            using \<open>poly (pderiv (prod_list_var qs) * (prod_list_var qs)*([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])) y = 0\<close> by force
          then show ?thesis 
            by (metis characterize_root_list_p_def is_not_const poly_f_def poly_f_nonzero poly_roots_finite s_is set_sorted_list_of_set)
        qed
        then show "\<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y" 
          by auto
      qed
      have len_gtz_prop: "length ?zer_list > 0 \<longrightarrow>
            ((\<exists>w. w < length ?zer_list \<and> y = ?zer_list ! w) \<or>
             (y < ?zer_list ! 0) \<or> 
             (y > ?zer_list ! (length ?zer_list - 1)) \<or> 
             (\<exists>k < (length ?zer_list - 1). y > ?zer_list ! k  \<and> y < ?zer_list ! (k+1)))"
      proof - 
        let ?c = "(\<exists>w. w < length ?zer_list \<and> y = ?zer_list ! w) \<or>
             (y < ?zer_list ! 0) \<or> 
             (y > ?zer_list ! (length ?zer_list - 1)) \<or> 
             (\<exists>k < (length ?zer_list - 1). y > ?zer_list ! k  \<and> y < ?zer_list ! (k+1))"
        have lis1: "length ?zer_list = 1 \<Longrightarrow> ?c"
          by auto
        have h1: "\<not>(\<exists>w. w < length ?zer_list \<and> y = ?zer_list ! w) \<Longrightarrow> \<not> (List.member ?zer_list y)"
          by (metis (no_types, lifting) in_set_conv_nth in_set_member)
        have h2: "(length ?zer_list > 0 \<and> \<not>(\<exists>w. w < length ?zer_list \<and> y = ?zer_list ! w) \<and> \<not> (y < ?zer_list ! 0)) \<Longrightarrow> y > ?zer_list ! 0"
          by auto
        have h3: "(length ?zer_list > 1 \<and> \<not>(\<exists>w. w < length ?zer_list \<and> y = ?zer_list ! w) \<and>  \<not> (y > ?zer_list ! (length ?zer_list - 1))) \<Longrightarrow>
          y < ?zer_list ! (length ?zer_list - 1)"
          apply (auto)
          by (smt (z3) diff_Suc_less gr_implies_not0 not_gr_zero) 
        have "length ?zer_list > 1 \<and> \<not>(\<exists>w. w < length ?zer_list \<and> y = ?zer_list ! w) \<and> \<not> (y < ?zer_list ! 0) \<and> \<not> (y > ?zer_list ! (length ?zer_list - 1))
              \<Longrightarrow>  (\<exists>k < (length ?zer_list - 1). y > ?zer_list ! k  \<and> y < ?zer_list ! (k+1))"
          using h1 h2 h3 strict_sorted_h sorted_list_lemma_var[of ?zer_list y]
          using One_nat_def Suc_lessD by presburger
        then have lgt1: "length ?zer_list > 1 \<Longrightarrow> ?c" 
          by auto
        then show ?thesis using lis1 lgt1
          by (smt (z3) diff_is_0_eq' not_less) 
      qed
      have neg_crb_in: "(- crb (prod_list_var qs)) \<in> set S"
        using set_S_char poly_f_is by auto
      have pos_crb_in: "(crb (prod_list_var qs)) \<in> set S" 
        using set_S_char poly_f_is by auto
      have set_S_nonempty: "set S \<noteq> {}" using neg_crb_in by auto
      have finset: "finite  {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}" 
      proof - 
        have "\<forall>q \<in> set qs.  q\<noteq> 0 \<longrightarrow> finite {x. poly q x = 0} "
          using poly_roots_finite by auto
        then show ?thesis by auto
      qed
      have c2: "\<not>(\<exists>q \<in> (set qs). q \<noteq> 0 \<and> poly q y = 0) \<Longrightarrow> \<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y"
      proof -  
        assume "\<not>(\<exists>q \<in> (set qs). q \<noteq> 0 \<and> poly q y = 0)"
        have c_c1: "length ?zer_list = 0 \<Longrightarrow>  \<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y"
        proof - 
          assume "length ?zer_list = 0"
          then have "\<forall>q \<in> set (qs). \<forall> (x:: real). \<forall>(y::real). squash (poly q x) = squash (poly q y)"          
          proof clarsimp
            fix q x y
            assume czer: "card {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0} = 0"
            assume qin: "q \<in> set qs"
            have fin_means_empty: "{x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0} = {}"
              using finset czer
              by auto
            have qzer: "q = 0 \<Longrightarrow> squash (poly q x) = squash (poly q y)" by auto
            have qnonz: "q \<noteq> 0 \<Longrightarrow> squash (poly q x) = squash (poly q y)"
            proof - 
              assume qnonz: "q \<noteq> 0"
              then have noroots: "{x. poly q x = 0} = {}" using qin finset
                using Collect_empty_eq fin_means_empty by auto 
              have nonzsq1: "squash (poly q x) \<noteq> 0" using fin_means_empty qnonz czer qin
                unfolding squash_def by auto
              then have  eo: "(poly q x) > 0 \<or> (poly q x) < 0" unfolding squash_def 
                apply (auto)
                by presburger 
              have eo1: "poly q x > 0 \<Longrightarrow> poly q y > 0" 
                using noroots poly_IVT_pos[of y x q] poly_IVT_neg[of x y q]
                apply (auto)
                by (metis linorder_neqE_linordered_idom) 
              have eo2: "poly q x < 0 \<Longrightarrow> poly q y < 0"
                using noroots poly_IVT_pos[of x y q] poly_IVT_neg[of y x q]
                apply (auto) by (metis linorder_neqE_linordered_idom) 
              then show "squash (poly q x) = squash (poly q y)" 
                using eo eo1 eo2 unfolding squash_def by auto
            qed
            show "squash (poly q x) = squash (poly q y)" 
              using qzer qnonz
              by blast 
          qed
          then have "\<forall>q \<in> set (qs). squash (poly q y) = squash (poly q (- crb (prod_list_var qs)))"
            by auto
          then show "\<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y"
            using neg_crb_in unfolding consistent_sign_vec_def squash_def  
            apply (auto)
            by (metis (no_types, hide_lams) antisym_conv3 class_field.neg_1_not_0 equal_neg_zero less_irrefl of_int_minus) 
        qed
        have c_c2: "length ?zer_list > 0 \<Longrightarrow>  \<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y"
        proof - 
          assume lengt: "length ?zer_list > 0"
          let ?t = " \<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y"
          have sg1: "(\<exists>w. w < length ?zer_list \<and> y = ?zer_list ! w) \<Longrightarrow> ?t"
          proof - 
            assume "(\<exists>w. w < length ?zer_list \<and> y = ?zer_list ! w)"
            then obtain w where w_prop: "w < length ?zer_list \<and> y = ?zer_list ! w" by auto
            then have " y \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}"
              using finset set_sorted_list_of_set[of "{x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}"]
              by (smt (verit, best) nth_mem)
            then have "y \<in> {x. poly (poly_f qs) x = 0}" using poly_f_is
              using \<open>\<not> (\<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q y = 0)\<close> by blast 
            then show ?thesis using set_S_char
              by blast  
          qed
          have sg2: "(y < ?zer_list ! 0) \<Longrightarrow> ?t" 
          proof - 
            assume ylt: "y < ?zer_list ! 0"
            have ynonzat_some_qs: "\<forall>q \<in> (set qs). q \<noteq> 0 \<longrightarrow> poly q y \<noteq> 0" 
            proof clarsimp 
              fix q
              assume q_in: "q \<in> set qs"
              assume qnonz: "q \<noteq> 0"
              assume "poly q y = 0"
              then have "y \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}" 
                using q_in qnonz by auto
              then have "List.member ?zer_list y"
                by (smt (verit, best) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
              then have "y \<ge> ?zer_list ! 0" using strict_sorted_h
                using \<open>\<not> (\<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q y = 0)\<close> \<open>poly q y = 0\<close> q_in qnonz by blast
              then show "False" using ylt 
                by auto
            qed
            let ?ncrb = "(- crb (prod_list_var qs))"
            have "\<forall>x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}. poly (prod_list_var qs) x = 0"
              using q_dvd_prod_list_var_prop
              by fastforce 
            then have "poly (prod_list_var qs) (sorted_list_of_set {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0} ! 0) = 0"
              using finset set_sorted_list_of_set
              by (metis (no_types, lifting) lengt nth_mem) 
            then have ncrblt: "?ncrb < ?zer_list ! 0" using prod_list_var_nonzero crb_lem_neg[of "prod_list_var qs" "?zer_list ! 0"] 
              by auto
            have qzerh: "\<forall>q \<in> (set qs). q = 0 \<longrightarrow> squash (poly q ?ncrb) = squash (poly q y)"
              by auto
            have "\<forall>q \<in> (set qs). q \<noteq> 0 \<longrightarrow> squash (poly q ?ncrb) = squash (poly q y)"
            proof clarsimp 
              fix q
              assume q_in: "q \<in> set qs"
              assume qnonz: "q \<noteq> 0"
              have nonzylt:"\<not>(\<exists>x \<le> y. poly q x = 0)" 
              proof clarsimp 
                fix x
                assume xlt: "x \<le> y" 
                assume "poly q x = 0"
                then have "x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}" 
                  using q_in qnonz by auto
                then have "List.member ?zer_list x"
                  by (smt (verit, best) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
                then have "x \<ge> ?zer_list ! 0" using strict_sorted_h
                  by (metis (no_types, lifting) gr_implies_not0 in_set_conv_nth in_set_member not_less sorted_iff_nth_mono sorted_list_of_set(2))     
                then show "False" using xlt ylt
                  by auto
              qed
              have nonzncrb:"\<not>(\<exists>x \<le> (real_of_int ?ncrb). poly q x = 0)" 
              proof clarsimp 
                fix x
                assume xlt: "x \<le> - real_of_int (crb (prod_list_var qs))" 
                assume "poly q x = 0"
                then have "x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}" 
                  using q_in qnonz by auto
                then have "List.member ?zer_list x"
                  by (smt (verit, best) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
                then have "x \<ge> ?zer_list ! 0" using strict_sorted_h
                  by (metis (no_types, lifting) gr_implies_not0 in_set_conv_nth in_set_member not_less sorted_iff_nth_mono sorted_list_of_set(2))
                then show "False" using xlt ncrblt 
                  by auto
              qed
              have c1: " (poly q ?ncrb) > 0 \<Longrightarrow> (poly q y) > 0"
              proof - 
                assume qncrbgt: "(poly q ?ncrb) > 0"
                then have eq: "?ncrb = y \<Longrightarrow> poly q y > 0 " by auto
                have gt: " ?ncrb > y \<Longrightarrow> poly q y > 0" using qncrbgt qnonz poly_IVT_pos[of y ?ncrb q] poly_IVT_neg[of ?ncrb y q] nonzncrb nonzylt
                  apply (auto)
                  by (meson less_eq_real_def linorder_neqE_linordered_idom) 
                have lt: "?ncrb < y \<Longrightarrow> poly q y > 0" using qncrbgt
                  using qnonz poly_IVT_pos[of y ?ncrb q] poly_IVT_neg[of ?ncrb y q] nonzncrb nonzylt
                  apply (auto)
                  by (meson less_eq_real_def linorder_neqE_linordered_idom) 
                then show ?thesis using eq gt lt apply (auto)
                  by (meson linorder_neqE_linordered_idom) 
              qed
              have c2: "(poly q ?ncrb) < 0 \<Longrightarrow>  (poly q y) < 0"
                using poly_IVT_pos[of ?ncrb y q] poly_IVT_neg[of y ?ncrb q] nonzncrb nonzylt
                apply (auto)
                by (metis less_eq_real_def linorder_neqE_linordered_idom) 
              have eo: "(poly q ?ncrb) > 0 \<or>  (poly q ?ncrb) < 0"
                using nonzncrb
                by auto 
              then  show "squash (poly q (- real_of_int (crb (prod_list_var qs)))) = squash (poly q y)"
                using   c1 c2
                by (smt (verit, ccfv_SIG) of_int_minus squash_def)  
            qed
            then have "\<forall>q \<in> (set qs). squash (poly q ?ncrb) = squash (poly q y)"
              using qzerh by auto 
            then have "consistent_sign_vec qs ?ncrb = consistent_sign_vec qs y"
              unfolding consistent_sign_vec_def squash_def
              by (smt (z3) map_eq_conv) 
            then show ?thesis using neg_crb_in by auto
          qed
          have sg3: " (y > ?zer_list ! (length ?zer_list - 1)) \<Longrightarrow> ?t" 
          proof - 
            assume ygt: "y  > ?zer_list ! (length ?zer_list - 1)"
            have ynonzat_some_qs: "\<forall>q \<in> (set qs). q \<noteq> 0 \<longrightarrow> poly q y \<noteq> 0" 
            proof clarsimp 
              fix q
              assume q_in: "q \<in> set qs"
              assume qnonz: "q \<noteq> 0"
              assume "poly q y = 0"
              then have "y \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}" 
                using q_in qnonz by auto
              then have "List.member ?zer_list y"
                by (smt (verit, best) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
              then have "y \<le> ?zer_list ! (length ?zer_list - 1)" using strict_sorted_h
                using \<open>\<not> (\<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q y = 0)\<close> \<open>poly q y = 0\<close> q_in qnonz by blast
              then show "False" using ygt 
                by auto
            qed
            let ?crb = "crb (prod_list_var qs)"
            have "\<forall>x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}. poly (prod_list_var qs) x = 0"
              using q_dvd_prod_list_var_prop
              by fastforce 
            then have "poly (prod_list_var qs) (sorted_list_of_set {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0} ! 0) = 0"
              using finset set_sorted_list_of_set
              by (metis (no_types, lifting) lengt nth_mem) 
            then have crbgt: "?crb > ?zer_list ! (length ?zer_list - 1)" using prod_list_var_nonzero crb_lem_pos[of "prod_list_var qs" "?zer_list ! (length ?zer_list - 1)"]
              by (metis (no_types, lifting) \<open>\<forall>x\<in>{x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}. poly (prod_list_var qs) x = 0\<close> diff_less finset lengt less_numeral_extra(1) nth_mem set_sorted_list_of_set) 
            have qzerh: "\<forall>q \<in> (set qs). q = 0 \<longrightarrow> squash (poly q ?crb) = squash (poly q y)"
              by auto
            have "\<forall>q \<in> (set qs). q \<noteq> 0 \<longrightarrow> squash (poly q ?crb) = squash (poly q y)"
            proof clarsimp 
              fix q
              assume q_in: "q \<in> set qs"
              assume qnonz: "q \<noteq> 0"
              have nonzylt:"\<not>(\<exists>x \<ge> y. poly q x = 0)" 
              proof clarsimp 
                fix x
                assume xgt: "x \<ge> y" 
                assume "poly q x = 0"
                then have "x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}" 
                  using q_in qnonz by auto
                then have "List.member ?zer_list x"
                  by (smt (verit, best) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
                then have "x \<le> ?zer_list ! (length ?zer_list - 1)" using strict_sorted_h
                  by (metis (no_types, lifting) One_nat_def Suc_leI Suc_pred diff_Suc_less in_set_conv_nth in_set_member lengt not_less sorted_iff_nth_mono sorted_list_of_set(2))      
                then show "False" using xgt ygt
                  by auto
              qed
              have nonzcrb:"\<not>(\<exists>x \<ge> (real_of_int ?crb). poly q x = 0)" 
              proof clarsimp 
                fix x
                assume xgt: "x \<ge> real_of_int (crb (prod_list_var qs))" 
                assume "poly q x = 0"
                then have "x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}" 
                  using q_in qnonz by auto
                then have "List.member ?zer_list x"
                  by (smt (verit, best) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
                then have "x \<le> ?zer_list ! (length ?zer_list - 1)" using strict_sorted_h
                  by (meson \<open>\<forall>x\<in>{x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}. poly (prod_list_var qs) x = 0\<close> \<open>x \<in> {x. \<exists>q\<in>set qs. q \<noteq> 0 \<and> poly q x = 0}\<close> crb_lem_pos not_less prod_list_var_nonzero xgt)           
                then show "False" using xgt crbgt 
                  by auto
              qed
              have c1: " (poly q ?crb) > 0 \<Longrightarrow> (poly q y) > 0"
              proof - 
                assume qcrbgt: "(poly q ?crb) > 0"
                then have eq: "?crb = y \<Longrightarrow> poly q y > 0 " by auto
                have gt: " ?crb > y \<Longrightarrow> poly q y > 0" using qcrbgt qnonz poly_IVT_pos[of y ?crb q] poly_IVT_neg[of ?crb y q] nonzcrb nonzylt
                  apply (auto)
                  by (meson less_eq_real_def linorder_neqE_linordered_idom) 
                have lt: "?crb < y \<Longrightarrow> poly q y > 0" using qcrbgt
                  using qnonz poly_IVT_pos[of y ?crb q] poly_IVT_neg[of ?crb y q] nonzcrb nonzylt
                  apply (auto)
                  by (meson less_eq_real_def linorder_neqE_linordered_idom) 
                then show ?thesis using eq gt lt apply (auto)
                  by (meson linorder_neqE_linordered_idom) 
              qed
              have c2: "(poly q ?crb) < 0 \<Longrightarrow>  (poly q y) < 0"
                using poly_IVT_pos[of ?crb y q] poly_IVT_neg[of y ?crb q] nonzcrb nonzylt
                apply (auto)
                by (metis less_eq_real_def linorder_neqE_linordered_idom) 
              have eo: "(poly q ?crb) > 0 \<or>  (poly q ?crb) < 0"
                using nonzcrb
                by auto 
              then show "squash (poly q (real_of_int (crb (prod_list_var qs)))) = squash (poly q y)"
                using   c1 c2
                by (smt (verit, ccfv_SIG) of_int_minus squash_def)  
            qed
            then have "\<forall>q \<in> (set qs). squash (poly q ?crb) = squash (poly q y)"
              using qzerh by auto 
            then have "consistent_sign_vec qs ?crb = consistent_sign_vec qs y"
              unfolding consistent_sign_vec_def squash_def
              by (smt (z3) map_eq_conv) 
            then show ?thesis using pos_crb_in by auto
          qed
          have sg4: " (\<exists>k < (length ?zer_list - 1). y > ?zer_list ! k  \<and> y < ?zer_list ! (k+1)) \<Longrightarrow> ?t"
          proof - 
            assume " (\<exists>k < (length ?zer_list - 1). y > ?zer_list ! k  \<and> y < ?zer_list ! (k+1))"
            then obtain k where k_prop: "k < (length ?zer_list - 1) \<and> y > ?zer_list ! k  \<and> y < ?zer_list ! (k+1)" 
              by auto
            have ltk: "(?zer_list ! k) < (?zer_list ! (k+1)) "
              using strict_sorted_h
              using k_prop by linarith 
            have q1e: "(\<exists>q1\<in>set qs. q1 \<noteq> 0 \<and> poly q1 (?zer_list ! k) = 0)"
              by (smt (z3) One_nat_def Suc_lessD add.right_neutral add_Suc_right finset k_prop less_diff_conv mem_Collect_eq nth_mem set_sorted_list_of_set) 
            have q2e: "(\<exists>q2\<in>set qs. q2 \<noteq> 0 \<and> poly q2 (?zer_list ! (k + 1)) = 0)"
              by (smt (verit, del_insts) finset k_prop less_diff_conv mem_Collect_eq nth_mem set_sorted_list_of_set) 
            then have "(\<exists>q>(?zer_list ! k). q < (?zer_list ! (k + 1)) \<and> poly (poly_f qs) q = 0)"
              using poly_f_roots_prop_1[of qs] q1e q2e ltk is_not_const 
              by auto
            then have "\<exists>s \<in> set S. s > ?zer_list ! k  \<and> s < ?zer_list ! (k+1)"
              using poly_f_is
              by (smt (z3) k_prop mem_Collect_eq set_S_char) 
            then obtain s where s_prop: "s \<in> set S \<and> s > ?zer_list ! k  \<and> s < ?zer_list ! (k+1)" by auto
            have qnon: "\<forall>q \<in> set qs. q\<noteq> 0 \<longrightarrow> squash (poly q s) = squash (poly q y)" 
            proof clarsimp 
              fix q
              assume q_in: "q \<in> set qs"
              assume qnonz: "q \<noteq> 0"
              have sgt: "s > y \<Longrightarrow> squash (poly q s) = squash (poly q y)" 
              proof - 
                assume "s > y"
                then have "\<nexists>x. List.member ?zer_list x \<and> y \<le> x \<and> x \<le> s"   
                  using sorted_list_lemma[of y s k ?zer_list] k_prop strict_sorted_h s_prop y_prop
                  using less_diff_conv by blast
                then have nox: "\<nexists>x. poly q x = 0 \<and> y \<le> x \<and> x \<le> s" using q_in qnonz
                  by (metis (mono_tags, lifting) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
                then  have c1: "poly q s \<noteq> 0" using s_prop q_in qnonz
                  by (metis (mono_tags, lifting) \<open>y < s\<close> less_eq_real_def )
                have c2: "poly q s > 0 \<Longrightarrow> poly q y > 0"
                  using poly_IVT_pos poly_IVT_neg nox
                  by (meson \<open>y < s\<close> less_eq_real_def linorder_neqE_linordered_idom) 
                have c3: "poly q s < 0 \<Longrightarrow> poly q y < 0"  using poly_IVT_pos poly_IVT_neg nox
                  by (meson \<open>y < s\<close> less_eq_real_def linorder_neqE_linordered_idom) 
                show ?thesis using c1 c2 c3 unfolding squash_def
                  by auto 
              qed
              have slt: "s < y \<Longrightarrow> squash (poly q s) = squash (poly q y)"              
              proof - 
                assume slt: "s < y"
                then have "\<nexists>x. List.member ?zer_list x \<and> s \<le> x \<and> x \<le> y"   
                  using sorted_list_lemma[of s y k ?zer_list] k_prop strict_sorted_h s_prop y_prop
                  using less_diff_conv by blast
                then have nox: "\<nexists>x. poly q x = 0 \<and> s \<le> x \<and> x \<le> y" using q_in qnonz
                  by (metis (mono_tags, lifting) finset in_set_member mem_Collect_eq set_sorted_list_of_set) 
                then  have c1: "poly q s \<noteq> 0" using s_prop q_in qnonz
                  by (metis (mono_tags, lifting) \<open>s < y\<close> less_eq_real_def )
                have c2: "poly q s > 0 \<Longrightarrow> poly q y > 0"
                  using poly_IVT_pos poly_IVT_neg nox
                  by (meson \<open>s < y\<close> less_eq_real_def linorder_neqE_linordered_idom) 
                have c3: "poly q s < 0 \<Longrightarrow> poly q y < 0"  using poly_IVT_pos poly_IVT_neg nox
                  by (meson \<open>s < y\<close> less_eq_real_def linorder_neqE_linordered_idom) 
                show ?thesis using c1 c2 c3 unfolding squash_def
                  by auto 
              qed
              have "s = y \<Longrightarrow> squash (poly q s) = squash (poly q y)" 
                by auto
              then show "squash (poly q s) = squash (poly q y)"
                using sgt slt
                by (meson linorder_neqE_linordered_idom) 
            qed
            have "\<forall>q \<in> set qs. q= 0 \<longrightarrow> squash (poly q s) = squash (poly q y)" by auto
            then have "\<forall>q \<in> set qs. squash (poly q s) = squash (poly q y)" 
              using qnon
              by fastforce 
            then show ?thesis 
              using s_prop unfolding squash_def consistent_sign_vec_def apply (auto)
              by (metis (no_types, hide_lams) class_field.neg_1_not_0 equal_neg_zero less_irrefl linorder_neqE_linordered_idom) 
          qed
          show ?thesis
            using lengt sg1 sg2 sg3 sg4 len_gtz_prop is_not_const
            by fastforce 
        qed
        show "\<exists> k \<in> (set S). consistent_sign_vec qs k = consistent_sign_vec qs y"
          using c_c1 c_c2 by auto
      qed
      show ?thesis
        using c1 c2 by auto
    qed
    then show "x \<in> consistent_sign_vectors_R qs (set S)"
      using y_prop unfolding consistent_sign_vectors_R_def
      by (metis imageI) 
  qed
  have easy_direction: "consistent_sign_vectors_R qs (set S) \<subseteq> consistent_sign_vectors_R qs UNIV "
    using consistent_sign_vectors_R_def by auto
  then show ?thesis using difficult_direction easy_direction by auto
qed

lemma main_step_aux2_R:
  fixes qs:: "real poly list"
  assumes is_not_const: "check_all_const_deg qs = False"
  shows "set (find_consistent_signs_R qs) =  consistent_sign_vectors_R qs UNIV"
proof - 
  have poly_f_is: "poly_f qs = (pderiv (prod_list_var qs)) * (prod_list_var qs)* ([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])"
    using is_not_const unfolding poly_f_def by auto
  let ?p = "(pderiv (prod_list_var qs)) * (prod_list_var qs)*  ([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:])"
  let ?S = "characterize_root_list_p (pderiv (prod_list_var qs) * (prod_list_var qs) *  ([:-(crb (prod_list_var qs)),1:]) * ([:(crb (prod_list_var qs)),1:]))"
  have "set (remdups
          (map (signs_at qs) ?S)) 
      = consistent_sign_vectors_R qs (set ?S)"
    unfolding signs_at_def squash_def consistent_sign_vectors_R_def consistent_sign_vec_def
    by (smt (verit, best) comp_apply map_eq_conv set_map set_remdups)
  then have "set (characterize_consistent_signs_at_roots ?p qs) = consistent_sign_vectors_R qs UNIV"
    unfolding characterize_consistent_signs_at_roots_def using assms all_sample_points_prop[of qs]
    by auto
  then show ?thesis
    unfolding find_consistent_signs_R_def using find_consistent_signs_at_roots_R poly_f_is poly_f_nonzero[of qs] 
    by auto
qed

lemma main_step_R:
  fixes qs:: "real poly list"
  shows "set (find_consistent_signs_R qs) =  consistent_sign_vectors_R qs UNIV"
  using main_step_aux1_R main_step_aux2_R by auto

(* The universal and existential decision procedure for real polys are easy 
   if we know the consistent sign vectors *)
lemma consistent_sign_vec_semantics_R:
  assumes "\<And>i. i \<in> set_fml fml \<Longrightarrow> i < length ls"
  shows "lookup_sem fml (map (\<lambda>p. poly p x) ls) = lookup_sem fml (consistent_sign_vec ls x)"
  using assms apply (induction)
  by (auto simp add: consistent_sign_vec_def)

lemma universal_lookup_sem_R:
  assumes "\<And>i. i \<in> set_fml fml \<Longrightarrow> i < length qs"
  assumes "set signs = consistent_sign_vectors_R qs UNIV"
  shows "(\<forall>x::real. lookup_sem fml (map (\<lambda>p. poly p x) qs)) \<longleftrightarrow>
    list_all (lookup_sem fml) signs"
  using assms(2) unfolding consistent_sign_vectors_R_def list_all_iff
  by (simp add: assms(1) consistent_sign_vec_semantics_R)

lemma existential_lookup_sem_R:
  assumes "\<And>i. i \<in> set_fml fml \<Longrightarrow> i < length qs"
  assumes "set signs = consistent_sign_vectors_R qs UNIV"
  shows "(\<exists>x::real. lookup_sem fml (map (\<lambda>p. poly p x) qs)) \<longleftrightarrow>
    find (lookup_sem fml) signs \<noteq> None"
  using assms(2) unfolding consistent_sign_vectors_R_def find_None_iff
  by (simp add: assms(1) consistent_sign_vec_semantics_R)

lemma decide_univ_lem_helper_R:
  fixes fml:: "real poly fml"
  assumes "(fml_struct,polys) = convert fml"
  shows "(\<forall>x::real. lookup_sem fml_struct (map (\<lambda>p. poly p x) polys)) \<longleftrightarrow> (decide_universal_R fml)"
  using assms universal_lookup_sem_R main_step_R unfolding decide_universal_R_def apply (auto)
  apply (metis assms convert_closed fst_conv snd_conv)
  by (metis (full_types) assms convert_closed fst_conv snd_conv)

lemma decide_exis_lem_helper_R:
  fixes fml:: "real poly fml"
  assumes "(fml_struct,polys) = convert fml"
  shows "(\<exists>x::real. lookup_sem fml_struct (map (\<lambda>p. poly p x) polys)) \<longleftrightarrow> (decide_existential_R fml)"
  using assms existential_lookup_sem_R main_step_R unfolding decide_existential_R_def apply (auto)
  apply (metis assms convert_closed fst_conv snd_conv)
  by (metis (full_types) assms convert_closed fst_conv snd_conv)

lemma convert_semantics_lem_R:
  assumes "\<And>p. p \<in> set (poly_list fml) \<Longrightarrow>
    ls ! (index_of ps p) = poly p x"
  shows "real_sem fml x = lookup_sem (map_fml (index_of ps) fml) ls"
  using assms apply (induct fml)
  by auto

lemma convert_semantics_R:
  shows "real_sem fml x = lookup_sem (fst (convert fml)) (map (\<lambda>p. poly p x) (snd (convert fml)))"
  unfolding convert_def Let_def apply simp
  apply (intro convert_semantics_lem_R)
  by (simp add: index_of_lookup(1) index_of_lookup(2))

(* Main result *)
theorem decision_procedure_R:
  shows "(\<forall>x::real. real_sem fml x) \<longleftrightarrow> (decide_universal_R fml)"
    "\<exists>x::real. real_sem fml x \<longleftrightarrow> (decide_existential_R fml)" 
  using  convert_semantics_lem_R decide_univ_lem_helper_R apply (auto)
  apply (simp add: convert_semantics_R)   
  apply (metis convert_def convert_semantics_R fst_conv snd_conv)  
  using convert_semantics_lem_R
  by (metis convert_def convert_semantics_R decide_exis_lem_helper_R fst_conv snd_conv)

end
