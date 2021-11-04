theory PAC_Polynomials_Operations
  imports PAC_Polynomials_Term PAC_Checker_Specification
begin

subsection \<open>Addition\<close>

text \<open>In this section, we refine the polynomials to list. These lists will be used in our checker
to represent the polynomials and execute operations.

There is one \<^emph>\<open>key\<close> difference between the list representation and the usual representation: in the
former, coefficients can be zero and monomials can appear several times. This makes it easier to
reason on intermediate representation where this has not yet been sanitized.
\<close>

fun add_poly_l' :: \<open>llist_polynomial \<times> llist_polynomial \<Rightarrow> llist_polynomial\<close> where
  \<open>add_poly_l' (p, []) = p\<close> |
  \<open>add_poly_l' ([], q) = q\<close> |
  \<open>add_poly_l' ((xs, n) # p, (ys, m) # q) =
            (if xs = ys then if n + m = 0 then add_poly_l' (p, q) else
                 let pq = add_poly_l' (p, q) in
                 ((xs, n + m) # pq)
            else if (xs, ys) \<in> term_order_rel
              then
                 let pq = add_poly_l' (p, (ys, m) # q) in
                 ((xs, n) # pq)
            else
                 let pq = add_poly_l' ((xs, n) # p, q) in
                 ((ys, m) # pq)
            )\<close>

definition add_poly_l :: \<open>llist_polynomial \<times> llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
  \<open>add_poly_l = REC\<^sub>T
      (\<lambda>add_poly_l (p, q).
        case (p,q) of
          (p, []) \<Rightarrow> RETURN p
        | ([], q) \<Rightarrow> RETURN q
        | ((xs, n) # p, (ys, m) # q) \<Rightarrow>
            (if xs = ys then if n + m = 0 then add_poly_l (p, q) else
               do {
                 pq \<leftarrow> add_poly_l (p, q);
                 RETURN ((xs, n + m) # pq)
             }
            else if (xs, ys) \<in> term_order_rel
              then do {
                 pq \<leftarrow> add_poly_l (p, (ys, m) # q);
                 RETURN ((xs, n) # pq)
            }
            else do {
                 pq \<leftarrow> add_poly_l ((xs, n) # p, q);
                 RETURN ((ys, m) # pq)
            }))\<close>

definition nonzero_coeffs where
  \<open>nonzero_coeffs a \<longleftrightarrow> 0 \<notin># snd `# a\<close>

lemma nonzero_coeffs_simps[simp]:
  \<open>nonzero_coeffs {#}\<close>
  \<open>nonzero_coeffs (add_mset (xs, n) a) \<longleftrightarrow> nonzero_coeffs a \<and> n \<noteq> 0\<close>
  by (auto simp: nonzero_coeffs_def)

lemma nonzero_coeffsD:
  \<open>nonzero_coeffs a \<Longrightarrow> (x, n) \<in># a \<Longrightarrow> n \<noteq> 0\<close>
  by (auto simp: nonzero_coeffs_def)

lemma sorted_poly_list_rel_ConsD:
  \<open>((ys, n) # p, a) \<in> sorted_poly_list_rel S \<Longrightarrow> (p, remove1_mset (mset ys, n) a) \<in> sorted_poly_list_rel S \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p var_order_rel) ys \<and>
    distinct ys \<and> ys \<notin> set (map fst p) \<and> n \<noteq> 0 \<and> nonzero_coeffs a\<close>
  unfolding sorted_poly_list_rel_wrt_def prod.case mem_Collect_eq
    list_rel_def
  apply (clarsimp)
  apply (subst (asm) list.rel_sel)
  apply (intro conjI)
  apply (rename_tac y, rule_tac b = \<open>tl y\<close> in relcompI)
  apply (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
    list.tl_def term_poly_list_rel_def nonzero_coeffs_def split: list.splits)
  done

lemma sorted_poly_list_rel_Cons_iff:
  \<open>((ys, n) # p, a) \<in> sorted_poly_list_rel S \<longleftrightarrow> (p, remove1_mset (mset ys, n) a) \<in> sorted_poly_list_rel S \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p var_order_rel) ys \<and>
    distinct ys \<and> ys \<notin> set (map fst p) \<and> n \<noteq> 0 \<and> nonzero_coeffs a\<close>
  apply (rule iffI)
  subgoal
    by (auto dest!: sorted_poly_list_rel_ConsD)
  subgoal
    unfolding sorted_poly_list_rel_wrt_def prod.case mem_Collect_eq
      list_rel_def
    apply (clarsimp)
    apply (intro conjI)
    apply (rename_tac y; rule_tac b = \<open>(mset ys, n) # y\<close> in relcompI)
    by (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
        term_poly_list_rel_def add_mset_eq_add_mset eq_commute[of _ \<open>mset _\<close>]
        nonzero_coeffs_def
      dest!: multi_member_split)
    done



lemma sorted_repeat_poly_list_rel_ConsD:
  \<open>((ys, n) # p, a) \<in> sorted_repeat_poly_list_rel S \<Longrightarrow> (p, remove1_mset (mset ys, n) a) \<in> sorted_repeat_poly_list_rel S \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p var_order_rel) ys \<and>
    distinct ys \<and> n \<noteq> 0 \<and> nonzero_coeffs a\<close>
  unfolding sorted_repeat_poly_list_rel_wrt_def prod.case mem_Collect_eq
    list_rel_def
  apply (clarsimp)
  apply (subst (asm) list.rel_sel)
  apply (intro conjI)
  apply (rename_tac y, rule_tac b = \<open>tl y\<close> in relcompI)
  apply (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
    list.tl_def term_poly_list_rel_def nonzero_coeffs_def split: list.splits)
  done

lemma sorted_repeat_poly_list_rel_Cons_iff:
  \<open>((ys, n) # p, a) \<in> sorted_repeat_poly_list_rel S \<longleftrightarrow> (p, remove1_mset (mset ys, n) a) \<in> sorted_repeat_poly_list_rel S \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p var_order_rel) ys \<and>
    distinct ys \<and> n \<noteq> 0 \<and> nonzero_coeffs a\<close>
  apply (rule iffI)
  subgoal
    by (auto dest!: sorted_repeat_poly_list_rel_ConsD)
  subgoal
    unfolding sorted_repeat_poly_list_rel_wrt_def prod.case mem_Collect_eq
      list_rel_def
    apply (clarsimp)
    apply (intro conjI)
    apply (rename_tac y, rule_tac b = \<open>(mset ys, n) # y\<close> in relcompI)
    by (auto simp: sorted_repeat_poly_list_rel_wrt_def list_mset_rel_def br_def
        term_poly_list_rel_def add_mset_eq_add_mset eq_commute[of _ \<open>mset _\<close>]
        nonzero_coeffs_def
      dest!: multi_member_split)
    done


lemma add_poly_p_add_mset_sum_0:
   \<open>n + m = 0 \<Longrightarrow>add_poly_p\<^sup>*\<^sup>* (A, Aa, {#}) ({#}, {#}, r) \<Longrightarrow>
           add_poly_p\<^sup>*\<^sup>*
            (add_mset (mset ys, n) A, add_mset (mset ys, m) Aa, {#})
            ({#}, {#}, r)\<close>
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_new_coeff_r)
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_same_coeff_l)
  apply (rule converse_rtranclp_into_rtranclp)
  apply (auto intro: add_poly_p.rem_0_coeff)
  done

lemma monoms_add_poly_l'D:
  \<open>(aa, ba) \<in> set (add_poly_l' x) \<Longrightarrow> aa \<in> fst ` set (fst x) \<or> aa \<in> fst ` set (snd x)\<close>
  by (induction x rule: add_poly_l'.induct)
    (auto split: if_splits)

lemma add_poly_p_add_to_result:
  \<open>add_poly_p\<^sup>*\<^sup>* (A, B, r) (A', B', r') \<Longrightarrow>
       add_poly_p\<^sup>*\<^sup>*
        (A, B, p + r) (A', B', p + r')\<close>
  apply (induction rule: rtranclp_induct[of add_poly_p \<open>(_, _, _)\<close> \<open>(_, _, _)\<close>, split_format(complete), of for r])
  subgoal by auto
  by (elim add_poly_pE)
   (metis (no_types, lifting) Pair_inject add_poly_p.intros rtranclp.simps union_mset_add_mset_right)+

lemma add_poly_p_add_mset_comb:
  \<open>add_poly_p\<^sup>*\<^sup>* (A, Aa, {#}) ({#}, {#}, r) \<Longrightarrow>
       add_poly_p\<^sup>*\<^sup>*
        (add_mset (xs, n) A, Aa, {#})
        ({#}, {#}, add_mset (xs, n) r)\<close>
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_new_coeff_l)
  using add_poly_p_add_to_result[of A Aa \<open>{#}\<close> \<open>{#}\<close> \<open>{#}\<close> r \<open>{#(xs, n)#}\<close>]
  by auto

lemma add_poly_p_add_mset_comb2:
  \<open>add_poly_p\<^sup>*\<^sup>* (A, Aa, {#}) ({#}, {#}, r) \<Longrightarrow>
       add_poly_p\<^sup>*\<^sup>*
        (add_mset (ys, n) A, add_mset (ys, m) Aa, {#})
        ({#}, {#}, add_mset (ys, n + m) r)\<close>
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_new_coeff_r)
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_same_coeff_l)
  using add_poly_p_add_to_result[of A Aa \<open>{#}\<close> \<open>{#}\<close> \<open>{#}\<close> r \<open>{#(ys, n+m)#}\<close>]
  by auto


lemma add_poly_p_add_mset_comb3:
  \<open>add_poly_p\<^sup>*\<^sup>* (A, Aa, {#}) ({#}, {#}, r) \<Longrightarrow>
       add_poly_p\<^sup>*\<^sup>*
        (A, add_mset (ys, m) Aa, {#})
        ({#}, {#}, add_mset (ys, m) r)\<close>
  apply (rule converse_rtranclp_into_rtranclp)
  apply (rule add_poly_p.add_new_coeff_r)
  using add_poly_p_add_to_result[of A Aa \<open>{#}\<close> \<open>{#}\<close> \<open>{#}\<close> r \<open>{#(ys, m)#}\<close>]
  by auto

lemma total_on_lexord:
  \<open>Relation.total_on UNIV R \<Longrightarrow> Relation.total_on UNIV (lexord R)\<close>
  apply (auto simp: Relation.total_on_def)
  by (meson lexord_linear)

lemma antisym_lexord:
  \<open>antisym R \<Longrightarrow> irrefl R \<Longrightarrow> antisym (lexord R)\<close>
  by (auto simp: antisym_def lexord_def irrefl_def
    elim!: list_match_lel_lel)

lemma less_than_char_linear:
  \<open>(a, b) \<in> less_than_char \<or>
           a = b \<or> (b, a) \<in> less_than_char\<close>
  by (auto simp: less_than_char_def)

lemma total_on_lexord_less_than_char_linear:
  \<open>xs \<noteq> ys \<Longrightarrow> (xs, ys) \<notin> lexord (lexord less_than_char) \<longleftrightarrow>
       (ys, xs) \<in> lexord (lexord less_than_char)\<close>
   using lexord_linear[of \<open>lexord less_than_char\<close> xs ys]
   using lexord_linear[of \<open>less_than_char\<close>] less_than_char_linear
   using lexord_irrefl[OF irrefl_less_than_char]
     antisym_lexord[OF antisym_lexord[OF antisym_less_than_char irrefl_less_than_char]]
   apply (auto simp: antisym_def Relation.total_on_def)
   done

lemma sorted_poly_list_rel_nonzeroD:
  \<open>(p, r) \<in> sorted_poly_list_rel term_order \<Longrightarrow>
       nonzero_coeffs (r)\<close>
  \<open>(p, r) \<in> sorted_poly_list_rel (rel2p (lexord (lexord less_than_char))) \<Longrightarrow>
       nonzero_coeffs (r)\<close>
  by (auto simp: sorted_poly_list_rel_wrt_def nonzero_coeffs_def)


lemma add_poly_l'_add_poly_p:
  assumes \<open>(pq, pq') \<in> sorted_poly_rel \<times>\<^sub>r sorted_poly_rel\<close>
  shows \<open>\<exists>r. (add_poly_l' pq, r) \<in> sorted_poly_rel \<and>
                        add_poly_p\<^sup>*\<^sup>* (fst pq', snd pq', {#}) ({#}, {#}, r)\<close>
  supply [[goals_limit=1]]
  using assms
  apply (induction \<open>pq\<close> arbitrary: pq' rule: add_poly_l'.induct)
  subgoal for p pq'
    using add_poly_p_empty_l[of \<open>fst pq'\<close> \<open>{#}\<close> \<open>{#}\<close>]
    by (cases pq') (auto intro!: exI[of _ \<open>fst pq'\<close>])
  subgoal for x p pq'
    using add_poly_p_empty_r[of  \<open>{#}\<close> \<open>snd pq'\<close> \<open>{#}\<close>]
    by (cases pq')  (auto intro!: exI[of _ \<open>snd pq'\<close>])
  subgoal premises p for xs n p ys m q pq'
    apply (cases pq') \<comment> \<open>Isabelle does a completely stupid case distinction here\<close>
    apply (cases \<open>xs = ys\<close>)
    subgoal
      apply (cases \<open>n + m = 0\<close>)
      subgoal
        using p(1)[of \<open>(remove1_mset (mset xs, n) (fst pq'), remove1_mset (mset ys, m)  (snd pq'))\<close>] p(5-)
        apply (auto dest!: sorted_poly_list_rel_ConsD multi_member_split
           )
      using add_poly_p_add_mset_sum_0 by blast
    subgoal
        using p(2)[of \<open>(remove1_mset (mset xs, n) (fst pq'), remove1_mset (mset ys, m)  (snd pq'))\<close>] p(5-)
        apply (auto dest!: sorted_poly_list_rel_ConsD multi_member_split)
        apply (rule_tac x = \<open>add_mset (mset ys, n + m) r\<close> in exI)
        apply (fastforce dest!: monoms_add_poly_l'D simp: sorted_poly_list_rel_Cons_iff rel2p_def
           sorted_poly_list_rel_nonzeroD var_order_rel_def
          intro: add_poly_p_add_mset_comb2)
        done
     done
    subgoal
      apply (cases \<open>(xs, ys) \<in> term_order_rel\<close>)
      subgoal
        using p(3)[of \<open>(remove1_mset (mset xs, n) (fst pq'), (snd pq'))\<close>] p(5-)
        apply (auto dest!: multi_member_split simp: sorted_poly_list_rel_Cons_iff rel2p_def)
        apply (rule_tac x = \<open>add_mset (mset xs, n) r\<close> in exI)
        apply (auto dest!: monoms_add_poly_l'D)
        apply (auto intro: lexord_trans add_poly_p_add_mset_comb simp: lexord_transI var_order_rel_def)
        apply (rule lexord_trans)
        apply assumption
        apply (auto intro: lexord_trans add_poly_p_add_mset_comb simp: lexord_transI
          sorted_poly_list_rel_nonzeroD var_order_rel_def)
        using total_on_lexord_less_than_char_linear by fastforce

      subgoal
        using p(4)[of \<open>(fst pq', remove1_mset (mset ys, m) (snd pq'))\<close>] p(5-)
        apply (auto dest!: multi_member_split simp: sorted_poly_list_rel_Cons_iff rel2p_def
           var_order_rel_def)
        apply (rule_tac x = \<open>add_mset (mset ys, m) r\<close> in exI)
        apply (auto dest!: monoms_add_poly_l'D
          simp: total_on_lexord_less_than_char_linear)
        apply (auto intro: lexord_trans add_poly_p_add_mset_comb  simp: lexord_transI
          total_on_lexord_less_than_char_linear var_order_rel_def)
        apply (rule lexord_trans)
        apply assumption
        apply (auto intro: lexord_trans add_poly_p_add_mset_comb3 simp: lexord_transI
          sorted_poly_list_rel_nonzeroD var_order_rel_def)
        using total_on_lexord_less_than_char_linear by fastforce
      done
   done
  done


lemma add_poly_l_add_poly:
  \<open>add_poly_l x = RETURN (add_poly_l' x)\<close>
  unfolding add_poly_l_def
  by (induction x rule: add_poly_l'.induct)
    (solves \<open>subst RECT_unfold, refine_mono, simp split: list.split\<close>)+

lemma add_poly_l_spec:
  \<open>(add_poly_l, uncurry (\<lambda>p q. SPEC(\<lambda>r. add_poly_p\<^sup>*\<^sup>* (p, q, {#}) ({#}, {#}, r)))) \<in>
    sorted_poly_rel \<times>\<^sub>r sorted_poly_rel \<rightarrow>\<^sub>f \<langle>sorted_poly_rel\<rangle>nres_rel\<close>
  unfolding add_poly_l_add_poly
  apply (intro nres_relI frefI)
  apply (drule add_poly_l'_add_poly_p)
  apply (auto simp: conc_fun_RES)
  done

definition sort_poly_spec :: \<open>llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
\<open>sort_poly_spec p =
  SPEC(\<lambda>p'. mset p = mset p' \<and> sorted_wrt (rel2p (Id \<union> term_order_rel)) (map fst p'))\<close>

lemma sort_poly_spec_id:
  assumes \<open>(p, p') \<in> unsorted_poly_rel\<close>
  shows \<open>sort_poly_spec p \<le> \<Down> (sorted_repeat_poly_rel) (RETURN p')\<close>
proof -
  obtain y where
    py: \<open>(p, y) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
    p'_y: \<open>p' = mset y\<close> and
    zero: \<open>0 \<notin># snd `# p'\<close>
    using assms
    unfolding sort_poly_spec_def poly_list_rel_def sorted_poly_list_rel_wrt_def
    by (auto simp: list_mset_rel_def br_def)
  then have [simp]: \<open>length y = length p\<close>
    by (auto simp: list_rel_def list_all2_conv_all_nth)
  have H: \<open>(x, p')
        \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel\<close>
     if px: \<open>mset p = mset x\<close> and \<open>sorted_wrt (rel2p (Id \<union> lexord var_order_rel)) (map fst x)\<close>
     for x :: \<open>llist_polynomial\<close>
  proof -
    obtain f where
      f: \<open>bij_betw f {..<length x} {..<length p}\<close> and
      [simp]: \<open>\<And>i. i<length x \<Longrightarrow> x ! i = p ! (f i)\<close>
      using px apply - apply (subst (asm)(2) eq_commute)  unfolding mset_eq_perm
      by (auto dest!: permutation_Ex_bij)
    let ?y = \<open>map (\<lambda>i. y ! f i) [0 ..< length x]\<close>
    have \<open>i < length y \<Longrightarrow> (p ! f i, y ! f i) \<in> term_poly_list_rel \<times>\<^sub>r int_rel\<close> for i
      using list_all2_nthD[of _ p y
         \<open>f i\<close>, OF py[unfolded list_rel_def mem_Collect_eq prod.case]]
         mset_eq_length[OF px] f
      by (auto simp: list_rel_def list_all2_conv_all_nth bij_betw_def)
    then have \<open>(x, ?y) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
      xy: \<open>length x = length y\<close>
      using py list_all2_nthD[of \<open>rel2p (term_poly_list_rel \<times>\<^sub>r int_rel)\<close> p y
         \<open>f i\<close> for i, simplified] mset_eq_length[OF px]
      by (auto simp: list_rel_def list_all2_conv_all_nth)
    moreover {
      have f: \<open>mset_set {0..<length x} = f `# mset_set {0..<length x}\<close>
        using f mset_eq_length[OF px]
        by (auto simp: bij_betw_def lessThan_atLeast0 image_mset_mset_set)
      have \<open>mset y = {#y ! f x. x \<in># mset_set {0..<length x}#}\<close>
        by (subst drop_0[symmetric], subst mset_drop_upto, subst xy[symmetric], subst f)
          auto
      then have \<open>(?y, p') \<in> list_mset_rel\<close>
        by (auto simp: list_mset_rel_def br_def p'_y)
    }
    ultimately show ?thesis
      by (auto intro!: relcompI[of _ ?y])
  qed
  show ?thesis
    using zero
    unfolding sort_poly_spec_def poly_list_rel_def sorted_repeat_poly_list_rel_wrt_def
    by refine_rcg (auto intro: H)
qed


subsection \<open>Multiplication\<close>

fun mult_monoms :: \<open>term_poly_list \<Rightarrow> term_poly_list \<Rightarrow> term_poly_list\<close> where
  \<open>mult_monoms p [] = p\<close> |
  \<open>mult_monoms [] p = p\<close> |
  \<open>mult_monoms (x # p) (y # q) =
    (if x = y then x # mult_monoms p q
     else if (x, y) \<in> var_order_rel then x # mult_monoms p (y # q)
      else y # mult_monoms (x # p) q)\<close>

lemma term_poly_list_rel_empty_iff[simp]:
  \<open>([], q') \<in> term_poly_list_rel \<longleftrightarrow> q' = {#}\<close>
  by (auto simp: term_poly_list_rel_def)

lemma mset_eqD_set_mset: \<open>mset xs = A \<Longrightarrow> set xs = set_mset A\<close>
  by auto

lemma term_poly_list_rel_Cons_iff:
  \<open>(y # p, p') \<in> term_poly_list_rel \<longleftrightarrow>
    (p, remove1_mset y p') \<in> term_poly_list_rel \<and>
    y \<in># p' \<and> y \<notin> set p \<and> y \<notin># remove1_mset y p' \<and>
  (\<forall>x\<in>#mset p. (y, x) \<in> var_order_rel)\<close>
  by (auto simp: term_poly_list_rel_def rel2p_def dest!: multi_member_split mset_eqD_set_mset)

lemma var_order_rel_antisym[simp]:
  \<open>(y, y) \<notin> var_order_rel\<close>
  by (simp add: less_than_char_def lexord_irreflexive var_order_rel_def)

lemma term_poly_list_rel_remdups_mset:
  \<open>(p, p') \<in> term_poly_list_rel \<Longrightarrow>
    (p, remdups_mset p') \<in> term_poly_list_rel\<close>
  by (auto simp: term_poly_list_rel_def distinct_mset_remdups_mset_id simp flip: distinct_mset_mset_distinct)

lemma var_notin_notin_mult_monomsD:
  \<open>y \<in> set (mult_monoms p q) \<Longrightarrow> y \<in> set p \<or> y \<in> set q\<close>
  by (induction p q arbitrary: p' q' rule: mult_monoms.induct) (auto split: if_splits)

lemma term_poly_list_rel_set_mset:
  \<open>(p, q) \<in> term_poly_list_rel \<Longrightarrow> set p = set_mset q\<close>
  by (auto simp: term_poly_list_rel_def)


lemma mult_monoms_spec:
  \<open>(mult_monoms, (\<lambda>a b. remdups_mset (a + b))) \<in> term_poly_list_rel \<rightarrow> term_poly_list_rel \<rightarrow> term_poly_list_rel\<close>
proof -
  have [dest]: \<open>remdups_mset (A + Aa) = add_mset y Ab \<Longrightarrow> y \<notin># A \<Longrightarrow>
       y \<notin># Aa \<Longrightarrow>
       False\<close> for Aa Ab y A
    by (metis set_mset_remdups_mset union_iff union_single_eq_member)
  show ?thesis
  apply (intro fun_relI)
  apply (rename_tac p p' q q')
  subgoal for p p' q q'
    apply (induction p q arbitrary: p' q' rule: mult_monoms.induct)
    subgoal by (auto simp: term_poly_list_rel_Cons_iff rel2p_def term_poly_list_rel_remdups_mset)
    subgoal for x p p' q'
      by (auto simp: term_poly_list_rel_Cons_iff rel2p_def term_poly_list_rel_remdups_mset
      dest!: multi_member_split[of _ q'])
    subgoal premises p for x p y q p' q'
      apply (cases \<open>x = y\<close>)
      subgoal
        using p(1)[of \<open>remove1_mset y p'\<close> \<open>remove1_mset y q'\<close>] p(4-)
        by (auto simp: term_poly_list_rel_Cons_iff rel2p_def
          dest!: var_notin_notin_mult_monomsD
          dest!: multi_member_split)
     apply (cases \<open>(x, y) \<in> var_order_rel\<close>)
     subgoal
        using p(2)[of \<open>remove1_mset x p'\<close> \<open>q'\<close>] p(4-)
        apply (auto simp: term_poly_list_rel_Cons_iff
            term_poly_list_rel_set_mset rel2p_def var_order_rel_def
          dest!: multi_member_split[of _ p'] multi_member_split[of _ q']
            var_notin_notin_mult_monomsD
          split: if_splits)
       apply (meson lexord_cons_cons list.inject total_on_lexord_less_than_char_linear)
       apply (meson lexord_cons_cons list.inject total_on_lexord_less_than_char_linear)
       apply (meson lexord_cons_cons list.inject total_on_lexord_less_than_char_linear)
       using lexord_trans trans_less_than_char var_order_rel_antisym
       unfolding var_order_rel_def apply blast+
       done
     subgoal
        using p(3)[of \<open>p'\<close> \<open>remove1_mset y q'\<close>] p(4-)
        apply (auto simp: term_poly_list_rel_Cons_iff rel2p_def
            term_poly_list_rel_set_mset rel2p_def var_order_rel_antisym
          dest!: multi_member_split[of _ p'] multi_member_split[of _ q']
            var_notin_notin_mult_monomsD
          split: if_splits)
       using lexord_trans trans_less_than_char var_order_rel_antisym
       unfolding var_order_rel_def apply blast
       apply (meson lexord_cons_cons list.inject total_on_lexord_less_than_char_linear)
       by (meson less_than_char_linear lexord_linear lexord_trans trans_less_than_char)
       done
    done
  done
qed

definition mult_monomials :: \<open>term_poly_list \<times> int \<Rightarrow> term_poly_list \<times> int \<Rightarrow> term_poly_list \<times> int\<close> where
  \<open>mult_monomials = (\<lambda>(x, a) (y, b). (mult_monoms x y, a * b))\<close>

definition mult_poly_raw :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> llist_polynomial\<close> where
  \<open>mult_poly_raw p q = foldl (\<lambda>b x. map (mult_monomials x) q @ b) [] p\<close>


fun map_append where
  \<open>map_append f b [] = b\<close> |
  \<open>map_append f b (x # xs) = f x # map_append f b xs\<close>

lemma map_append_alt_def:
  \<open>map_append f b xs = map f xs @ b\<close>
  by (induction f b xs rule: map_append.induct)
   auto

lemma foldl_append_empty:
  \<open>NO_MATCH [] xs \<Longrightarrow> foldl (\<lambda>b x. f x @ b) xs p = foldl (\<lambda>b x. f x @ b) [] p @ xs\<close>
  apply (induction p arbitrary: xs)
   apply simp
  by (metis (mono_tags, lifting) NO_MATCH_def append.assoc append_self_conv foldl_Cons)


lemma poly_list_rel_empty_iff[simp]:
  \<open>([], r) \<in> poly_list_rel R \<longleftrightarrow> r = {#}\<close>
  by (auto simp: poly_list_rel_def list_mset_rel_def br_def)

lemma mult_poly_raw_simp[simp]:
  \<open>mult_poly_raw [] q = []\<close>
  \<open>mult_poly_raw (x # p) q = mult_poly_raw p q @ map (mult_monomials x) q\<close>
  subgoal by (auto simp: mult_poly_raw_def)
  subgoal by (induction p) (auto simp: mult_poly_raw_def foldl_append_empty)
  done

lemma sorted_poly_list_relD:
  \<open>(q, q') \<in> sorted_poly_list_rel R \<Longrightarrow> q' = (\<lambda>(a, b). (mset a, b)) `# mset q\<close>
  apply (induction q arbitrary: q')
  apply (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
    list_rel_split_right_iff)
  apply (subst (asm)(2) term_poly_list_rel_def)
  apply (simp add: relcomp.relcompI)
  done

lemma list_all2_in_set_ExD:
  \<open>list_all2 R p q \<Longrightarrow> x \<in> set p \<Longrightarrow> \<exists>y \<in> set q. R x y\<close>
  by (induction p q rule: list_all2_induct)
    auto

inductive_cases mult_poly_p_elim: \<open>mult_poly_p q (A, r) (B, r')\<close>

lemma mult_poly_p_add_mset_same:
  \<open>(mult_poly_p q')\<^sup>*\<^sup>* (A, r) (B, r') \<Longrightarrow> (mult_poly_p q')\<^sup>*\<^sup>* (add_mset x A, r) (add_mset x B, r')\<close>
  apply (induction rule: rtranclp_induct[of \<open>mult_poly_p q'\<close> \<open>(_, r)\<close> \<open>(p', q'')\<close> for p' q'', split_format(complete)])
  subgoal by simp
  apply (rule rtranclp.rtrancl_into_rtrancl)
   apply assumption
  by (auto elim!: mult_poly_p_elim intro: mult_poly_p.intros
      intro: rtranclp.rtrancl_into_rtrancl simp: add_mset_commute[of x])

lemma mult_poly_raw_mult_poly_p:
  assumes \<open>(p, p') \<in> sorted_poly_rel\<close> and \<open>(q, q') \<in> sorted_poly_rel\<close>
  shows \<open>\<exists>r. (mult_poly_raw p q, r) \<in> unsorted_poly_rel \<and> (mult_poly_p q')\<^sup>*\<^sup>* (p', {#}) ({#}, r)\<close>
proof -
  have H: \<open>(q, q') \<in> sorted_poly_list_rel term_order \<Longrightarrow> n < length q \<Longrightarrow>
    distinct aa \<Longrightarrow> sorted_wrt var_order aa \<Longrightarrow>
    (mult_monoms aa (fst (q ! n)),
           mset (mult_monoms aa (fst (q ! n))))
          \<in> term_poly_list_rel\<close> for aa n
    using mult_monoms_spec[unfolded fun_rel_def, simplified] apply -
    apply (drule bspec[of _ _ \<open>(aa, (mset aa))\<close>])
     apply (auto simp: term_poly_list_rel_def)[]
    unfolding prod.case sorted_poly_list_rel_wrt_def
    apply clarsimp
    subgoal for y
      apply (drule bspec[of _ _ \<open>(fst (q ! n), mset (fst (q ! n)))\<close>])
      apply (cases \<open>q ! n\<close>; cases \<open>y ! n\<close>)
      using param_nth[of n y n q \<open>term_poly_list_rel \<times>\<^sub>r int_rel\<close>]
      by (auto simp: list_rel_imp_same_length term_poly_list_rel_def)
    done

  have H': \<open>(q, q') \<in> sorted_poly_list_rel term_order \<Longrightarrow>
    distinct aa \<Longrightarrow> sorted_wrt var_order aa \<Longrightarrow>
     (ab, ba) \<in> set q \<Longrightarrow>
       remdups_mset (mset aa + mset ab) = mset (mult_monoms aa ab)\<close> for aa n ab ba
    using mult_monoms_spec[unfolded fun_rel_def, simplified] apply -
    apply (drule bspec[of _ _ \<open>(aa, (mset aa))\<close>])
    apply (auto simp: term_poly_list_rel_def)[]
    unfolding prod.case sorted_poly_list_rel_wrt_def
    apply clarsimp
    subgoal for y
      apply (drule bspec[of _ _ \<open>(ab, mset ab)\<close>])
      apply (auto simp: list_rel_imp_same_length term_poly_list_rel_def list_rel_def
        dest: list_all2_in_set_ExD)
    done
    done

  have  H: \<open>(q, q') \<in> sorted_poly_list_rel term_order \<Longrightarrow>
       a = (aa, b) \<Longrightarrow>
       (pq, r) \<in> unsorted_poly_rel \<Longrightarrow>
       p' = add_mset (mset aa, b) A \<Longrightarrow>
       \<forall>x\<in>set p. term_order aa (fst x) \<Longrightarrow>
       sorted_wrt var_order aa \<Longrightarrow>
       distinct aa \<Longrightarrow> b\<noteq> 0 \<Longrightarrow>
       (\<And>aaa. (aaa, 0) \<notin># q') \<Longrightarrow>
       (pq @
        map (mult_monomials (aa, b)) q,
        {#case x of (ys, n) \<Rightarrow> (remdups_mset (mset aa + ys), n * b)
        . x \<in># q'#} +
        r)
       \<in> unsorted_poly_rel\<close> for a p p' pq aa b r
   apply (auto simp: poly_list_rel_def)
   apply (rule_tac b = \<open>y @ map (\<lambda>(a,b). (mset a, b)) (map (mult_monomials (aa, b)) q)\<close> in relcompI)
   apply (auto simp: list_rel_def list_all2_append list_all2_lengthD H
     list_mset_rel_def br_def mult_monomials_def case_prod_beta intro!: list_all2_all_nthI
     simp: sorted_poly_list_relD)
     apply (subst sorted_poly_list_relD[of q q' term_order])
     apply (auto simp: case_prod_beta H' intro!: image_mset_cong)
   done

  show ?thesis
    using assms
    apply (induction p arbitrary: p')
    subgoal
      by auto
    subgoal premises p for a p p'
      using p(1)[of \<open>remove1_mset (mset (fst a), snd a) p'\<close>] p(2-)
      apply (cases a)
      apply (auto simp: sorted_poly_list_rel_Cons_iff
        dest!: multi_member_split)
      apply (rule_tac x = \<open>(\<lambda>(ys, n). (remdups_mset (mset (fst a) + ys), n * snd a)) `# q' + r\<close> in exI)
      apply (auto 5 3 intro: mult_poly_p.intros simp: intro!: H
        dest: sorted_poly_list_rel_nonzeroD nonzero_coeffsD)
      apply (rule rtranclp_trans)
      apply (rule mult_poly_p_add_mset_same)
      apply assumption
      apply (rule converse_rtranclp_into_rtranclp)
      apply (auto intro!: mult_poly_p.intros simp: ac_simps)
      done
    done
qed

fun merge_coeffs :: \<open>llist_polynomial \<Rightarrow> llist_polynomial\<close> where
  \<open>merge_coeffs [] = []\<close> |
  \<open>merge_coeffs [(xs, n)] = [(xs, n)]\<close> |
  \<open>merge_coeffs ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then if n + m \<noteq> 0 then merge_coeffs ((xs, n + m) # p) else merge_coeffs p
    else (xs, n) # merge_coeffs ((ys, m) # p))\<close>

abbreviation  (in -)mononoms :: \<open>llist_polynomial \<Rightarrow> term_poly_list set\<close> where
  \<open>mononoms p \<equiv> fst `set p\<close>


lemma fst_normalize_polynomial_subset:
  \<open>mononoms (merge_coeffs p) \<subseteq> mononoms p\<close>
  by (induction p rule: merge_coeffs.induct)  auto


lemma fst_normalize_polynomial_subsetD:
  \<open>(a, b) \<in> set (merge_coeffs p) \<Longrightarrow> a \<in> mononoms p\<close>
  apply (induction p rule: merge_coeffs.induct)
  subgoal
    by auto
  subgoal
    by auto
  subgoal
    by (auto split: if_splits)
  done

lemma distinct_merge_coeffs:
  assumes \<open>sorted_wrt R (map fst xs)\<close> and \<open>transp R\<close> \<open>antisymp R\<close>
  shows \<open>distinct (map fst (merge_coeffs xs))\<close>
  using assms
  by (induction xs rule: merge_coeffs.induct)
    (auto 5 4 dest: antisympD dest!: fst_normalize_polynomial_subsetD)

lemma in_set_merge_coeffsD:
  \<open>(a, b) \<in> set (merge_coeffs p) \<Longrightarrow>\<exists>b. (a, b) \<in> set p\<close>
  by  (auto dest!: fst_normalize_polynomial_subsetD)

lemma rtranclp_normalize_poly_add_mset:
  \<open>normalize_poly_p\<^sup>*\<^sup>* A r \<Longrightarrow> normalize_poly_p\<^sup>*\<^sup>* (add_mset x A) (add_mset x r)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest: normalize_poly_p.keep_coeff[of _ _ x])

lemma nonzero_coeffs_diff:
  \<open>nonzero_coeffs A \<Longrightarrow> nonzero_coeffs (A - B)\<close>
  by (auto simp: nonzero_coeffs_def dest: in_diffD)


lemma merge_coeffs_is_normalize_poly_p:
  \<open>(xs, ys) \<in> sorted_repeat_poly_rel \<Longrightarrow> \<exists>r. (merge_coeffs xs, r) \<in> sorted_poly_rel \<and> normalize_poly_p\<^sup>*\<^sup>* ys r\<close>
  apply (induction xs arbitrary: ys rule: merge_coeffs.induct)
  subgoal by (auto simp: sorted_repeat_poly_list_rel_wrt_def sorted_poly_list_rel_wrt_def)
  subgoal
    by (auto simp: sorted_repeat_poly_list_rel_wrt_def sorted_poly_list_rel_wrt_def)
  subgoal premises p for xs n ys m p ysa
    apply (cases \<open>xs = ys\<close>, cases \<open>m+n \<noteq> 0\<close>)
    subgoal
      using p(1)[of \<open>add_mset (mset ys, m+n) ysa - {#(mset ys, m), (mset ys, n)#}\<close>] p(4-)
      apply (auto simp: sorted_poly_list_rel_Cons_iff ac_simps add_mset_commute
        remove1_mset_add_mset_If nonzero_coeffs_diff sorted_repeat_poly_list_rel_Cons_iff)
      apply (rule_tac x = \<open>r\<close> in exI)
      using normalize_poly_p.merge_dup_coeff[of \<open>ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>mset ys\<close> m n]
      by (auto dest!: multi_member_split simp del: normalize_poly_p.merge_dup_coeff
        simp: add_mset_commute
        intro: converse_rtranclp_into_rtranclp)
   subgoal
      using p(2)[of \<open>ysa - {#(mset ys, m), (mset ys, n)#}\<close>] p(4-)
      apply (auto simp: sorted_poly_list_rel_Cons_iff ac_simps add_mset_commute
        remove1_mset_add_mset_If nonzero_coeffs_diff sorted_repeat_poly_list_rel_Cons_iff)
      apply (rule_tac x = \<open>r\<close> in exI)
      using normalize_poly_p.rem_0_coeff[of \<open>add_mset (mset ys, m +n) ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>add_mset (mset ys, m +n) ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>mset ys\<close>]
      using normalize_poly_p.merge_dup_coeff[of \<open>ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>mset ys\<close> m n]
      by (force intro: add_mset_commute[of \<open>(mset ys, n)\<close> \<open>(mset ys, -n)\<close>]
          converse_rtranclp_into_rtranclp
        dest!: multi_member_split
        simp del: normalize_poly_p.rem_0_coeff
        simp: add_eq_0_iff2
        intro: normalize_poly_p.rem_0_coeff)
   subgoal
      using p(3)[of \<open>add_mset (mset ys, m) ysa - {#(mset xs, n), (mset ys, m)#}\<close>] p(4-)
    apply (auto simp: sorted_poly_list_rel_Cons_iff ac_simps add_mset_commute
      remove1_mset_add_mset_If sorted_repeat_poly_list_rel_Cons_iff)
    apply (rule_tac x = \<open>add_mset (mset xs, n) r\<close> in exI)
    apply (auto dest!: in_set_merge_coeffsD)
    apply (auto intro: normalize_poly_p.intros rtranclp_normalize_poly_add_mset
      simp: rel2p_def var_order_rel_def
      dest!: multi_member_split
      dest: sorted_poly_list_rel_nonzeroD)
     using total_on_lexord_less_than_char_linear apply fastforce
     using total_on_lexord_less_than_char_linear apply fastforce
    done
  done
done


subsection \<open>Normalisation\<close>

definition normalize_poly where
  \<open>normalize_poly p = do {
     p \<leftarrow> sort_poly_spec p;
     RETURN (merge_coeffs p)
}\<close>
definition sort_coeff :: \<open>string list \<Rightarrow> string list nres\<close> where
\<open>sort_coeff ys = SPEC(\<lambda>xs. mset xs = mset ys \<and> sorted_wrt (rel2p (Id \<union> var_order_rel)) xs)\<close>

lemma distinct_var_order_Id_var_order:
  \<open>distinct a \<Longrightarrow> sorted_wrt (rel2p (Id \<union> var_order_rel)) a \<Longrightarrow>
          sorted_wrt var_order a\<close>
  by (induction a) (auto simp: rel2p_def)

definition sort_all_coeffs :: \<open>llist_polynomial \<Rightarrow> llist_polynomial nres\<close> where
\<open>sort_all_coeffs xs = monadic_nfoldli xs (\<lambda>_. RETURN True) (\<lambda>(a, n) b. do {a \<leftarrow> sort_coeff a; RETURN ((a, n) # b)}) []\<close>

lemma sort_all_coeffs_gen:
  assumes \<open>(\<forall>xs \<in> mononoms xs'. sorted_wrt (rel2p (var_order_rel)) xs)\<close> and
    \<open>\<forall>x \<in> mononoms (xs @ xs'). distinct x\<close>
  shows \<open>monadic_nfoldli xs (\<lambda>_. RETURN True) (\<lambda>(a, n) b. do {a \<leftarrow> sort_coeff a; RETURN ((a, n) # b)}) xs' \<le>
     \<Down>Id (SPEC(\<lambda>ys. map (\<lambda>(a,b). (mset a, b)) (rev xs @ xs') = map (\<lambda>(a,b). (mset a, b)) (ys) \<and>
     (\<forall>xs \<in> mononoms ys. sorted_wrt (rel2p (var_order_rel)) xs)))\<close>
proof -
  have H: \<open>
       \<forall>x\<in>set xs'. sorted_wrt var_order (fst x) \<Longrightarrow>
       sorted_wrt (rel2p (Id \<union> var_order_rel)) x \<Longrightarrow>
       (aaa, ba) \<in> set xs' \<Longrightarrow>
       sorted_wrt (rel2p (Id \<union> var_order_rel)) aaa\<close> for xs  xs' ba aa b x aaa
    by (metis UnCI fst_eqD rel2p_def sorted_wrt_mono_rel)
  show ?thesis
    using assms
    unfolding sort_all_coeffs_def sort_coeff_def
    apply (induction xs arbitrary: xs')
    subgoal
      using assms
      by auto
    subgoal premises p for a xs
      using p(2-)
      apply (cases a, simp only: monadic_nfoldli_simp bind_to_let_conv Let_def if_True Refine_Basic.nres_monad3
        intro_spec_refine_iff prod.case)
      by (auto 5 3 simp: intro_spec_refine_iff image_Un
        dest: same_mset_distinct_iff
        intro!: p(1)[THEN order_trans] distinct_var_order_Id_var_order
        simp: H)
    done
qed

definition shuffle_coefficients where
  \<open>shuffle_coefficients xs = (SPEC(\<lambda>ys. map (\<lambda>(a,b). (mset a, b)) (rev xs) = map (\<lambda>(a,b). (mset a, b)) ys \<and>
     (\<forall>xs \<in> mononoms ys. sorted_wrt (rel2p (var_order_rel)) xs)))\<close>

lemma sort_all_coeffs:
  \<open>\<forall>x \<in> mononoms xs. distinct x \<Longrightarrow>
  sort_all_coeffs xs \<le> \<Down> Id (shuffle_coefficients xs)\<close>
  unfolding sort_all_coeffs_def shuffle_coefficients_def
  by (rule sort_all_coeffs_gen[THEN order_trans])
   auto

lemma unsorted_term_poly_list_rel_mset:
  \<open>(ys, aa) \<in> unsorted_term_poly_list_rel \<Longrightarrow> mset ys = aa\<close>
  by (auto simp: unsorted_term_poly_list_rel_def)

lemma RETURN_map_alt_def:
  \<open>RETURN o (map f) =
    REC\<^sub>T (\<lambda>g xs.
      case xs of
        [] \<Rightarrow> RETURN []
      | x # xs \<Rightarrow> do {xs \<leftarrow> g xs; RETURN (f x # xs)})\<close>
  unfolding comp_def
  apply (subst eq_commute)
  apply (intro ext)
  apply (induct_tac x)
  subgoal
    apply (subst RECT_unfold)
    apply refine_mono
    apply auto
    done
  subgoal
    apply (subst RECT_unfold)
    apply refine_mono
    apply auto
    done
  done


lemma fully_unsorted_poly_rel_Cons_iff:
  \<open>((ys, n) # p, a) \<in> fully_unsorted_poly_rel \<longleftrightarrow>
    (p, remove1_mset (mset ys, n) a) \<in> fully_unsorted_poly_rel \<and>
    (mset ys, n) \<in># a \<and> distinct ys\<close>
  apply (auto simp: poly_list_rel_def list_rel_split_right_iff list_mset_rel_def br_def
     unsorted_term_poly_list_rel_def
     nonzero_coeffs_def fully_unsorted_poly_list_rel_def dest!: multi_member_split)
  apply blast
  apply (rule_tac b = \<open>(mset ys, n) # y\<close> in relcompI)
  apply auto
  done

lemma map_mset_unsorted_term_poly_list_rel:
  \<open>(\<And>a. a \<in> mononoms s \<Longrightarrow> distinct a) \<Longrightarrow> \<forall>x \<in> mononoms s. distinct x \<Longrightarrow>
    (\<forall>xs \<in> mononoms s. sorted_wrt (rel2p (Id \<union> var_order_rel)) xs) \<Longrightarrow>
    (s, map (\<lambda>(a, y). (mset a, y)) s)
          \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close>
  by (induction s) (auto simp: term_poly_list_rel_def
    distinct_var_order_Id_var_order)

lemma list_rel_unsorted_term_poly_list_relD:
  \<open>(p, y) \<in> \<langle>unsorted_term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
   mset y = (\<lambda>(a, y). (mset a, y)) `# mset p \<and> (\<forall>x \<in> mononoms p. distinct x)\<close>
  by (induction p arbitrary: y)
   (auto simp: list_rel_split_right_iff
    unsorted_term_poly_list_rel_def)

lemma shuffle_terms_distinct_iff:
  assumes \<open>map (\<lambda>(a, y). (mset a, y)) p = map (\<lambda>(a, y). (mset a, y)) s\<close>
  shows \<open>(\<forall>x\<in>set p. distinct (fst x)) \<longleftrightarrow> (\<forall>x\<in>set s. distinct (fst x))\<close>
proof -
  have  \<open>\<forall>x\<in>set s. distinct (fst x)\<close>
    if m:  \<open>map (\<lambda>(a, y). (mset a, y)) p = map (\<lambda>(a, y). (mset a, y)) s\<close> and
      dist: \<open>\<forall>x\<in>set p. distinct (fst x)\<close>
    for s p
  proof standard+
    fix x
    assume x: \<open>x \<in> set s\<close>
    obtain v n where [simp]: \<open>x = (v, n)\<close> by (cases x)
    then have \<open>(mset v, n) \<in> set (map (\<lambda>(a, y). (mset a, y)) p)\<close>
      using x unfolding m by auto
    then obtain v' where
      \<open>(v', n) \<in> set p\<close> and
      \<open>mset v' = mset v\<close>
      by (auto simp: image_iff)
    then show \<open>distinct (fst x)\<close>
      using dist by (metis \<open>x = (v, n)\<close> distinct_mset_mset_distinct fst_conv)
  qed
  from this[of p s] this[of s p]
  show \<open>?thesis\<close>
    unfolding assms
    by blast
qed

lemma
  \<open>(p, y) \<in> \<langle>unsorted_term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
       (a, b) \<in> set p \<Longrightarrow>  distinct a\<close>
   using list_rel_unsorted_term_poly_list_relD by fastforce

lemma sort_all_coeffs_unsorted_poly_rel_with0:
  assumes \<open>(p, p') \<in> fully_unsorted_poly_rel\<close>
  shows \<open>sort_all_coeffs p \<le> \<Down> (unsorted_poly_rel_with0) (RETURN p')\<close>
proof -
  have H: \<open>(map (\<lambda>(a, y). (mset a, y)) (rev p)) =
          map (\<lambda>(a, y). (mset a, y)) s \<longleftrightarrow>
          (map (\<lambda>(a, y). (mset a, y)) p) =
          map (\<lambda>(a, y). (mset a, y)) (rev s)\<close> for s
    by (auto simp flip: rev_map simp: eq_commute[of \<open>rev (map _ _)\<close> \<open>map _ _\<close>])
  have 1: \<open>\<And>s y. (p, y) \<in> \<langle>unsorted_term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
           p' = mset y \<Longrightarrow>
           map (\<lambda>(a, y). (mset a, y)) (rev p) = map (\<lambda>(a, y). (mset a, y)) s \<Longrightarrow>
           \<forall>x\<in>set s. sorted_wrt var_order (fst x) \<Longrightarrow>
           (s, map (\<lambda>(a, y). (mset a, y)) s)
           \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close>
    by (auto 4 4 simp: rel2p_def
        dest!: list_rel_unsorted_term_poly_list_relD
        dest: shuffle_terms_distinct_iff["THEN" iffD1]
        intro!: map_mset_unsorted_term_poly_list_rel
        sorted_wrt_mono_rel[of _ \<open>rel2p (var_order_rel)\<close> \<open>rel2p (Id \<union> var_order_rel)\<close>])
  have 2: \<open>\<And>s y. (p, y) \<in> \<langle>unsorted_term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
           p' = mset y \<Longrightarrow>
           map (\<lambda>(a, y). (mset a, y)) (rev p) = map (\<lambda>(a, y). (mset a, y)) s \<Longrightarrow>
           \<forall>x\<in>set s. sorted_wrt var_order (fst x) \<Longrightarrow>
           mset y = {#case x of (a, x) \<Rightarrow> (mset a, x). x \<in># mset s#}\<close>
    by (metis (no_types, lifting) list_rel_unsorted_term_poly_list_relD mset_map mset_rev)
  show ?thesis
    apply (rule sort_all_coeffs[THEN order_trans])
    using assms
    by (auto simp: shuffle_coefficients_def poly_list_rel_def
        RETURN_def fully_unsorted_poly_list_rel_def list_mset_rel_def
        br_def dest: list_rel_unsorted_term_poly_list_relD
        intro!: RES_refine relcompI[of _  \<open>map (\<lambda>(a, y). (mset a, y)) (rev p)\<close>]
        1 2)
qed

lemma sort_poly_spec_id':
  assumes \<open>(p, p') \<in> unsorted_poly_rel_with0\<close>
  shows \<open>sort_poly_spec p \<le> \<Down> (sorted_repeat_poly_rel_with0) (RETURN p')\<close>
proof -
  obtain y where
    py: \<open>(p, y) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
    p'_y: \<open>p' = mset y\<close>
    using assms
    unfolding fully_unsorted_poly_list_rel_def poly_list_rel_def sorted_poly_list_rel_wrt_def
    by (auto simp: list_mset_rel_def br_def)
  then have [simp]: \<open>length y = length p\<close>
    by (auto simp: list_rel_def list_all2_conv_all_nth)
  have H: \<open>(x, p')
        \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel O list_mset_rel\<close>
     if px: \<open>mset p = mset x\<close> and \<open>sorted_wrt (rel2p (Id \<union> lexord var_order_rel)) (map fst x)\<close>
     for x :: \<open>llist_polynomial\<close>
  proof -
    obtain f where
      f: \<open>bij_betw f {..<length x} {..<length p}\<close> and
      [simp]: \<open>\<And>i. i<length x \<Longrightarrow> x ! i = p ! (f i)\<close>
      using px apply - apply (subst (asm)(2) eq_commute)  unfolding mset_eq_perm
      by (auto dest!: permutation_Ex_bij)
    let ?y = \<open>map (\<lambda>i. y ! f i) [0 ..< length x]\<close>
    have \<open>i < length y \<Longrightarrow> (p ! f i, y ! f i) \<in> term_poly_list_rel \<times>\<^sub>r int_rel\<close> for i
      using list_all2_nthD[of _ p y
         \<open>f i\<close>, OF py[unfolded list_rel_def mem_Collect_eq prod.case]]
         mset_eq_length[OF px] f
      by (auto simp: list_rel_def list_all2_conv_all_nth bij_betw_def)
    then have \<open>(x, ?y) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel\<close> and
      xy: \<open>length x = length y\<close>
      using py list_all2_nthD[of \<open>rel2p (term_poly_list_rel \<times>\<^sub>r int_rel)\<close> p y
         \<open>f i\<close> for i, simplified] mset_eq_length[OF px]
      by (auto simp: list_rel_def list_all2_conv_all_nth)
    moreover {
      have f: \<open>mset_set {0..<length x} = f `# mset_set {0..<length x}\<close>
        using f mset_eq_length[OF px]
        by (auto simp: bij_betw_def lessThan_atLeast0 image_mset_mset_set)
      have \<open>mset y = {#y ! f x. x \<in># mset_set {0..<length x}#}\<close>
        by (subst drop_0[symmetric], subst mset_drop_upto, subst xy[symmetric], subst f)
          auto
      then have \<open>(?y, p') \<in> list_mset_rel\<close>
        by (auto simp: list_mset_rel_def br_def p'_y)
    }
    ultimately show ?thesis
      by (auto intro!: relcompI[of _ ?y])
  qed
  show ?thesis
    unfolding sort_poly_spec_def poly_list_rel_def sorted_repeat_poly_list_rel_with0_wrt_def
    by refine_rcg (auto intro: H)
qed


fun merge_coeffs0 :: \<open>llist_polynomial \<Rightarrow> llist_polynomial\<close> where
  \<open>merge_coeffs0 [] = []\<close> |
  \<open>merge_coeffs0 [(xs, n)] = (if n = 0 then [] else [(xs, n)])\<close> |
  \<open>merge_coeffs0 ((xs, n) # (ys, m) # p) =
    (if xs = ys
    then if n + m \<noteq> 0 then merge_coeffs0 ((xs, n + m) # p) else merge_coeffs0 p
    else if n = 0 then merge_coeffs0 ((ys, m) # p)
      else(xs, n) # merge_coeffs0 ((ys, m) # p))\<close>


lemma sorted_repeat_poly_list_rel_with0_wrt_ConsD:
  \<open>((ys, n) # p, a) \<in> sorted_repeat_poly_list_rel_with0_wrt S term_poly_list_rel \<Longrightarrow>
     (p, remove1_mset (mset ys, n) a) \<in> sorted_repeat_poly_list_rel_with0_wrt S term_poly_list_rel \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p var_order_rel) ys \<and>
    distinct ys\<close>
  unfolding sorted_repeat_poly_list_rel_with0_wrt_def prod.case mem_Collect_eq
    list_rel_def
  apply (clarsimp)
  apply (subst (asm) list.rel_sel)
  apply (intro conjI)
  apply (rule_tac b = \<open>tl y\<close> in relcompI)
  apply (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def)
  apply (case_tac \<open>lead_coeff y\<close>; case_tac y)
  apply (auto simp: term_poly_list_rel_def)
  apply (case_tac \<open>lead_coeff y\<close>; case_tac y)
  apply (auto simp: term_poly_list_rel_def)
  apply (case_tac \<open>lead_coeff y\<close>; case_tac y)
  apply (auto simp: term_poly_list_rel_def)
  apply (case_tac \<open>lead_coeff y\<close>; case_tac y)
  apply (auto simp: term_poly_list_rel_def)
  done

lemma sorted_repeat_poly_list_rel_with0_wrtl_Cons_iff:
  \<open>((ys, n) # p, a) \<in> sorted_repeat_poly_list_rel_with0_wrt S term_poly_list_rel \<longleftrightarrow>
    (p, remove1_mset (mset ys, n) a) \<in> sorted_repeat_poly_list_rel_with0_wrt S term_poly_list_rel \<and>
    (mset ys, n) \<in># a \<and> (\<forall>x \<in> set p. S ys (fst x)) \<and> sorted_wrt (rel2p var_order_rel) ys \<and>
    distinct ys\<close>
  apply (rule iffI)
  subgoal
    by (auto dest!: sorted_repeat_poly_list_rel_with0_wrt_ConsD)
  subgoal
    unfolding sorted_poly_list_rel_wrt_def prod.case mem_Collect_eq
      list_rel_def sorted_repeat_poly_list_rel_with0_wrt_def
    apply (clarsimp)
    apply (rule_tac b = \<open>(mset ys, n) # y\<close> in relcompI)
    by (auto simp: sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
        term_poly_list_rel_def add_mset_eq_add_mset eq_commute[of _ \<open>mset _\<close>]
        nonzero_coeffs_def
      dest!: multi_member_split)
    done

lemma fst_normalize0_polynomial_subsetD:
  \<open>(a, b) \<in> set (merge_coeffs0 p) \<Longrightarrow> a \<in> mononoms p\<close>
  apply (induction p rule: merge_coeffs0.induct)
  subgoal
    by auto
  subgoal
    by (auto split: if_splits)
  subgoal
    by (auto split: if_splits)
  done

lemma in_set_merge_coeffs0D:
  \<open>(a, b) \<in> set (merge_coeffs0 p) \<Longrightarrow>\<exists>b. (a, b) \<in> set p\<close>
  by  (auto dest!: fst_normalize0_polynomial_subsetD)


lemma merge_coeffs0_is_normalize_poly_p:
  \<open>(xs, ys) \<in> sorted_repeat_poly_rel_with0 \<Longrightarrow> \<exists>r. (merge_coeffs0 xs, r) \<in> sorted_poly_rel \<and> normalize_poly_p\<^sup>*\<^sup>* ys r\<close>
  apply (induction xs arbitrary: ys rule: merge_coeffs0.induct)
  subgoal by (auto simp: sorted_repeat_poly_list_rel_wrt_def sorted_poly_list_rel_wrt_def
    sorted_repeat_poly_list_rel_with0_wrt_def list_mset_rel_def br_def)
  subgoal for xs n ys
    by (force simp: sorted_repeat_poly_list_rel_wrt_def sorted_poly_list_rel_wrt_def
      sorted_repeat_poly_list_rel_with0_wrt_def list_mset_rel_def br_def
      list_rel_split_right_iff)
  subgoal premises p for xs n ys m p ysa
    apply (cases \<open>xs = ys\<close>, cases \<open>m+n \<noteq> 0\<close>)
    subgoal
      using p(1)[of \<open>add_mset (mset ys, m+n) ysa - {#(mset ys, m), (mset ys, n)#}\<close>] p(5-)
      apply (auto simp: sorted_repeat_poly_list_rel_with0_wrtl_Cons_iff ac_simps add_mset_commute
        remove1_mset_add_mset_If nonzero_coeffs_diff sorted_repeat_poly_list_rel_Cons_iff)
      apply (auto intro: normalize_poly_p.intros add_mset_commute add_mset_commute
         converse_rtranclp_into_rtranclp dest!: multi_member_split
        simp del: normalize_poly_p.merge_dup_coeff)
      apply (rule_tac x = \<open>r\<close> in exI)
      using normalize_poly_p.merge_dup_coeff[of \<open>ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>mset ys\<close> m n]
      by (auto intro: normalize_poly_p.intros 
         converse_rtranclp_into_rtranclp dest!: multi_member_split
         simp: add_mset_commute[of \<open>(mset ys, n)\<close> \<open>(mset ys, m)\<close>]
         simp del: normalize_poly_p.merge_dup_coeff)
   subgoal
      using p(2)[of \<open>ysa - {#(mset ys, m), (mset ys, n)#}\<close>] p(5-)
      apply (auto simp: sorted_repeat_poly_list_rel_with0_wrtl_Cons_iff ac_simps add_mset_commute
        remove1_mset_add_mset_If nonzero_coeffs_diff sorted_repeat_poly_list_rel_Cons_iff)
      apply (rule_tac x = \<open>r\<close> in exI)
      using normalize_poly_p.rem_0_coeff[of \<open>add_mset (mset ys, m +n) ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>add_mset (mset ys, m +n) ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>mset ys\<close>]
      using normalize_poly_p.merge_dup_coeff[of \<open>ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>ysa -  {#(mset ys, m), (mset ys, n)#}\<close> \<open>mset ys\<close> m n]
      by (force intro: normalize_poly_p.intros converse_rtranclp_into_rtranclp
          dest!: multi_member_split
        simp del: normalize_poly_p.rem_0_coeff
         simp: add_mset_commute[of \<open>(mset ys, n)\<close> \<open>(mset ys, m)\<close>])
   apply (cases \<open>n = 0\<close>)
   subgoal
      using p(3)[of \<open>add_mset (mset ys, m) ysa - {#(mset xs, n), (mset ys, m)#}\<close>] p(4-)
    apply (auto simp: sorted_repeat_poly_list_rel_with0_wrtl_Cons_iff ac_simps add_mset_commute
      remove1_mset_add_mset_If sorted_repeat_poly_list_rel_Cons_iff)
    apply (rule_tac x = \<open>r\<close> in exI)
    apply (auto dest!: in_set_merge_coeffsD)
    by (force intro: rtranclp_normalize_poly_add_mset converse_rtranclp_into_rtranclp
      simp: rel2p_def var_order_rel_def sorted_poly_list_rel_Cons_iff
      dest!: multi_member_split
      dest: sorted_poly_list_rel_nonzeroD)
   subgoal
      using p(4)[of \<open>add_mset (mset ys, m) ysa - {#(mset xs, n), (mset ys, m)#}\<close>] p(5-)
    apply (auto simp: sorted_repeat_poly_list_rel_with0_wrtl_Cons_iff ac_simps add_mset_commute
      remove1_mset_add_mset_If sorted_repeat_poly_list_rel_Cons_iff)
    apply (rule_tac x = \<open>add_mset (mset xs, n) r\<close> in exI)
    apply (auto dest!: in_set_merge_coeffs0D)
    apply (auto intro: normalize_poly_p.intros rtranclp_normalize_poly_add_mset
      simp: rel2p_def var_order_rel_def sorted_poly_list_rel_Cons_iff
      dest!: multi_member_split
      dest: sorted_poly_list_rel_nonzeroD)
      using in_set_merge_coeffs0D total_on_lexord_less_than_char_linear apply fastforce
      using in_set_merge_coeffs0D total_on_lexord_less_than_char_linear apply fastforce
      done
    done
  done

definition full_normalize_poly where
  \<open>full_normalize_poly p = do {
     p \<leftarrow> sort_all_coeffs p;
     p \<leftarrow> sort_poly_spec p;
     RETURN (merge_coeffs0 p)
  }\<close>

fun sorted_remdups where
  \<open>sorted_remdups (x # y # zs) =
    (if x = y then sorted_remdups (y # zs) else x # sorted_remdups (y # zs))\<close> |
  \<open>sorted_remdups zs = zs\<close>

lemma set_sorted_remdups[simp]:
  \<open>set (sorted_remdups xs) = set xs\<close>
  by (induction xs rule: sorted_remdups.induct)
   auto

lemma distinct_sorted_remdups:
  \<open>sorted_wrt R xs \<Longrightarrow> transp R \<Longrightarrow> Restricted_Predicates.total_on R UNIV \<Longrightarrow>
    antisymp R \<Longrightarrow> distinct (sorted_remdups xs)\<close>
  by (induction xs rule: sorted_remdups.induct)
    (auto dest: antisympD)

lemma full_normalize_poly_normalize_poly_p:
  assumes \<open>(p, p') \<in> fully_unsorted_poly_rel\<close>
  shows \<open>full_normalize_poly p \<le> \<Down> (sorted_poly_rel) (SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r))\<close>
  (is \<open>?A \<le> \<Down> ?R ?B\<close>)
proof -
  have 1: \<open>?B = do {
     p' \<leftarrow> RETURN p';
     p' \<leftarrow> RETURN p';
     SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r)
    }\<close>
    by auto
  have [refine0]: \<open>sort_all_coeffs p \<le> SPEC(\<lambda>p. (p, p') \<in> unsorted_poly_rel_with0)\<close>
    by (rule sort_all_coeffs_unsorted_poly_rel_with0[OF assms, THEN order_trans])
      (auto simp: conc_fun_RES RETURN_def)
  have [refine0]: \<open>sort_poly_spec p \<le> SPEC (\<lambda>c. (c, p') \<in> sorted_repeat_poly_rel_with0)\<close>
    if \<open>(p, p') \<in> unsorted_poly_rel_with0\<close>
    for p p'
    by (rule sort_poly_spec_id'[THEN order_trans, OF that])
      (auto simp: conc_fun_RES RETURN_def)
  show ?thesis
    apply (subst 1)
    unfolding full_normalize_poly_def
    by (refine_rcg)
     (auto intro!: RES_refine
        dest!: merge_coeffs0_is_normalize_poly_p
        simp: RETURN_def)
qed

definition mult_poly_full :: \<open>_\<close> where
\<open>mult_poly_full p q = do {
  let pq = mult_poly_raw p q;
  normalize_poly pq
}\<close>

lemma normalize_poly_normalize_poly_p:
  assumes \<open>(p, p') \<in> unsorted_poly_rel\<close>
  shows \<open>normalize_poly p \<le> \<Down> (sorted_poly_rel) (SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r))\<close>
proof -
  have 1: \<open>SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r) = do {
      p' \<leftarrow> RETURN p';
      SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p' r)
   }\<close>
   by auto
  show ?thesis
    unfolding normalize_poly_def
    apply (subst 1)
    apply (refine_rcg sort_poly_spec_id[OF assms]
      merge_coeffs_is_normalize_poly_p)
    subgoal
      by (drule merge_coeffs_is_normalize_poly_p)
        (auto intro!: RES_refine simp: RETURN_def)
    done
qed


subsection \<open>Multiplication and normalisation\<close>

definition mult_poly_p' :: \<open>_\<close> where
\<open>mult_poly_p' p' q' = do {
  pq \<leftarrow> SPEC(\<lambda>r. (mult_poly_p q')\<^sup>*\<^sup>* (p', {#}) ({#}, r));
  SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* pq r)
}\<close>

lemma unsorted_poly_rel_fully_unsorted_poly_rel:
  \<open>unsorted_poly_rel \<subseteq> fully_unsorted_poly_rel\<close>
proof -
  have \<open>term_poly_list_rel  \<times>\<^sub>r int_rel \<subseteq> unsorted_term_poly_list_rel \<times>\<^sub>r int_rel\<close>
    by (auto simp: unsorted_term_poly_list_rel_def term_poly_list_rel_def)
  from list_rel_mono[OF this]
  show ?thesis
    unfolding poly_list_rel_def fully_unsorted_poly_list_rel_def
    by (auto simp:)
qed

lemma mult_poly_full_mult_poly_p':
  assumes \<open>(p, p') \<in> sorted_poly_rel\<close> \<open>(q, q') \<in> sorted_poly_rel\<close>
  shows \<open>mult_poly_full p q \<le> \<Down> (sorted_poly_rel) (mult_poly_p' p' q')\<close>
  unfolding mult_poly_full_def mult_poly_p'_def
  apply (refine_rcg full_normalize_poly_normalize_poly_p
    normalize_poly_normalize_poly_p)
  apply (subst RETURN_RES_refine_iff)
  apply (subst Bex_def)
  apply (subst mem_Collect_eq)
  apply (subst conj_commute)
  apply (rule mult_poly_raw_mult_poly_p[OF assms(1,2)])
  subgoal
    by blast
  done

definition add_poly_spec :: \<open>_\<close> where
\<open>add_poly_spec p q = SPEC (\<lambda>r. p + q - r \<in> ideal polynomial_bool)\<close>

definition add_poly_p' :: \<open>_\<close> where
\<open>add_poly_p' p q = SPEC(\<lambda>r. add_poly_p\<^sup>*\<^sup>* (p, q, {#}) ({#}, {#}, r))\<close>

lemma add_poly_l_add_poly_p':
  assumes \<open>(p, p') \<in> sorted_poly_rel\<close> \<open>(q, q') \<in> sorted_poly_rel\<close>
  shows \<open>add_poly_l (p, q) \<le> \<Down> (sorted_poly_rel) (add_poly_p' p' q')\<close>
  unfolding add_poly_p'_def
  apply (refine_rcg add_poly_l_spec[THEN fref_to_Down_curry_right, THEN order_trans, of _ p' q'])
  subgoal by auto
  subgoal using assms by auto
  subgoal
    by auto
  done


subsection \<open>Correctness\<close>

context poly_embed
begin

definition mset_poly_rel where
  \<open>mset_poly_rel = {(a, b). b = polynomial_of_mset a}\<close>

definition var_rel where
  \<open>var_rel = br \<phi> (\<lambda>_. True)\<close>

lemma normalize_poly_p_normalize_poly_spec:
  \<open>(p, p') \<in> mset_poly_rel \<Longrightarrow>
    SPEC (\<lambda>r. normalize_poly_p\<^sup>*\<^sup>* p r) \<le> \<Down>mset_poly_rel (normalize_poly_spec p')\<close>
  by (auto simp: mset_poly_rel_def rtranclp_normalize_poly_p_poly_of_mset ideal.span_zero
    normalize_poly_spec_def intro!: RES_refine)


lemma mult_poly_p'_mult_poly_spec:
  \<open>(p, p') \<in> mset_poly_rel \<Longrightarrow> (q, q') \<in> mset_poly_rel \<Longrightarrow>
  mult_poly_p' p q \<le> \<Down>mset_poly_rel (mult_poly_spec p' q')\<close>
  unfolding mult_poly_p'_def mult_poly_spec_def
  apply refine_rcg
  apply (auto simp: mset_poly_rel_def dest!: rtranclp_mult_poly_p_mult_ideal_final)
  apply (intro RES_refine)
  using ideal.span_add_eq2 ideal.span_zero
  by (fastforce dest!: rtranclp_normalize_poly_p_poly_of_mset intro: ideal.span_add_eq2)


lemma add_poly_p'_add_poly_spec:
  \<open>(p, p') \<in> mset_poly_rel \<Longrightarrow> (q, q') \<in> mset_poly_rel \<Longrightarrow>
  add_poly_p' p q \<le> \<Down>mset_poly_rel (add_poly_spec p' q')\<close>
  unfolding add_poly_p'_def add_poly_spec_def
  apply (auto simp: mset_poly_rel_def dest!: rtranclp_add_poly_p_polynomial_of_mset_full)
  apply (intro RES_refine)
  apply (auto simp: rtranclp_add_poly_p_polynomial_of_mset_full ideal.span_zero)
  done

end


definition weak_equality_l :: \<open>llist_polynomial \<Rightarrow> llist_polynomial \<Rightarrow> bool nres\<close> where
  \<open>weak_equality_l p q = RETURN (p = q)\<close>

definition weak_equality :: \<open>int mpoly \<Rightarrow> int mpoly \<Rightarrow> bool nres\<close> where
  \<open>weak_equality p q = SPEC (\<lambda>r. r \<longrightarrow> p = q)\<close>

definition weak_equality_spec :: \<open>mset_polynomial \<Rightarrow> mset_polynomial \<Rightarrow> bool nres\<close> where
  \<open>weak_equality_spec p q = SPEC (\<lambda>r. r \<longrightarrow> p = q)\<close>

lemma term_poly_list_rel_same_rightD:
  \<open>(a, aa) \<in> term_poly_list_rel \<Longrightarrow> (a, ab) \<in> term_poly_list_rel \<Longrightarrow> aa = ab\<close>
    by (auto simp: term_poly_list_rel_def)

lemma list_rel_term_poly_list_rel_same_rightD:
  \<open>(xa, y) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
   (xa, ya) \<in> \<langle>term_poly_list_rel \<times>\<^sub>r int_rel\<rangle>list_rel \<Longrightarrow>
    y = ya\<close>
  by (induction xa arbitrary: y ya)
    (auto simp: list_rel_split_right_iff
      dest: term_poly_list_rel_same_rightD)

lemma weak_equality_l_weak_equality_spec:
  \<open>(uncurry weak_equality_l, uncurry weak_equality_spec) \<in>
    sorted_poly_rel \<times>\<^sub>r sorted_poly_rel \<rightarrow>\<^sub>f \<langle>bool_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
   (auto simp: weak_equality_l_def weak_equality_spec_def
      sorted_poly_list_rel_wrt_def list_mset_rel_def br_def
    dest: list_rel_term_poly_list_rel_same_rightD)

end

