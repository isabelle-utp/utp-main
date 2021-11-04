(*
  File:         PAC_Checker_Init.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Init
  imports  PAC_Checker WB_Sort PAC_Checker_Relation
begin

section \<open>Initial Normalisation of Polynomials\<close>

subsection \<open>Sorting\<close>

text \<open>Adapted from the theory \<^text>\<open>HOL-ex.MergeSort\<close> by Tobias Nipkow. We did not change much, but
   we refine it to executable code and try to improve efficiency.
\<close>

fun merge :: "_ \<Rightarrow>  'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "merge f (x#xs) (y#ys) =
         (if f x y then x # merge f xs (y#ys) else y # merge f (x#xs) ys)"
| "merge f xs [] = xs"
| "merge f [] ys = ys"

lemma mset_merge [simp]:
  "mset (merge f xs ys) = mset xs + mset ys"
  by (induct f xs ys rule: merge.induct) (simp_all add: ac_simps)

lemma set_merge [simp]:
  "set (merge f xs ys) = set xs \<union> set ys"
  by (induct f xs ys rule: merge.induct) auto

lemma sorted_merge:
  "transp f \<Longrightarrow> (\<And>x y. f x y \<or> f y x) \<Longrightarrow>
   sorted_wrt f (merge f xs ys) \<longleftrightarrow> sorted_wrt f xs \<and> sorted_wrt f ys"
  apply (induct f xs ys rule: merge.induct)
  apply (auto simp add: ball_Un not_le less_le dest: transpD)
  apply blast
  apply (blast dest: transpD)
  done

fun msort :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "msort f [] = []"
| "msort f [x] = [x]"
| "msort f xs = merge f
                      (msort f (take (size xs div 2) xs))
                      (msort f (drop (size xs div 2) xs))"

fun swap_ternary :: \<open>_\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow> ('a \<times> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a \<times> 'a)\<close> where
  \<open>swap_ternary f m n  =
    (if (m = 0 \<and> n = 1)
    then (\<lambda>(a, b, c). if f a b then (a, b, c)
      else (b,a,c))
    else if (m = 0 \<and> n = 2)
    then (\<lambda>(a, b, c). if f a c then (a, b, c)
      else (c,b,a))
    else if (m = 1 \<and> n = 2)
    then (\<lambda>(a, b, c). if f b c then (a, b, c)
      else (a,c,b))
    else (\<lambda>(a, b, c). (a,b,c)))\<close>

fun msort2 :: "_ \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "msort2 f [] = []"
| "msort2 f [x] = [x]"
| "msort2 f [x,y] = (if f x y then [x,y] else [y,x])"
| "msort2 f xs = merge f
                      (msort f (take (size xs div 2) xs))
                      (msort f (drop (size xs div 2) xs))"

lemmas [code del] =
  msort2.simps

declare msort2.simps[simp del]
lemmas [code] =
  msort2.simps[unfolded swap_ternary.simps, simplified]

declare msort2.simps[simp]

lemma msort_msort2:
  fixes xs :: \<open>'a :: linorder list\<close>
  shows \<open>msort (\<le>) xs = msort2 (\<le>) xs\<close>
  apply (induction  \<open>(\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> xs rule: msort2.induct)
  apply (auto dest: transpD)
  done

lemma sorted_msort:
  "transp f \<Longrightarrow> (\<And>x y. f x y \<or> f y x) \<Longrightarrow>
   sorted_wrt f (msort f xs)"
  by (induct f xs rule: msort.induct) (simp_all add: sorted_merge)

lemma mset_msort[simp]:
  "mset (msort f xs) = mset xs"
  by (induction f xs rule: msort.induct)
    (simp_all add: union_code)


subsection \<open>Sorting applied to monomials\<close>

lemma merge_coeffs_alt_def:
  \<open>(RETURN o merge_coeffs) p =
   REC\<^sub>T(\<lambda>f p.
     (case p of
       [] \<Rightarrow> RETURN []
     | [_] => RETURN p
     | ((xs, n) # (ys, m) # p) \<Rightarrow>
      (if xs = ys
       then if n + m \<noteq> 0 then f ((xs, n + m) # p) else f p
       else do {p \<leftarrow> f ((ys, m) # p); RETURN ((xs, n) # p)})))
    p\<close>
  apply (induction p rule: merge_coeffs.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal for x p y q
    by (subst RECT_unfold, refine_mono)
     (smt case_prod_conv list.simps(5) merge_coeffs.simps(3) nres_monad1
      push_in_let_conv(2))
  done

lemma hn_invalid_recover:
  \<open>is_pure R \<Longrightarrow> hn_invalid R = (\<lambda>x y. R x y * true)\<close>
  \<open>is_pure R \<Longrightarrow> invalid_assn R = (\<lambda>x y. R x y * true)\<close>
  by (auto simp: is_pure_conv invalid_pure_recover hn_ctxt_def intro!: ext)

lemma safe_poly_vars:
  shows
    [safe_constraint_rules]:
      "is_pure (poly_assn)" and
    [safe_constraint_rules]:
      "is_pure (monom_assn)" and
    [safe_constraint_rules]:
      "is_pure (monomial_assn)" and
    [safe_constraint_rules]:
      "is_pure string_assn"
  by (auto intro!: pure_prod list_assn_pure simp: prod_assn_pure_conv)

lemma invalid_assn_distrib:
  \<open>invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn = invalid_assn (monom_assn \<times>\<^sub>a int_assn)\<close>
    apply (simp add: invalid_pure_recover hn_invalid_recover
      safe_constraint_rules)
    apply (subst hn_invalid_recover)
    apply (rule safe_poly_vars(2))
    apply (subst hn_invalid_recover)
    apply (rule safe_poly_vars)
    apply (auto intro!: ext)
    done

lemma WTF_RF_recover:
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xb
        x'a \<or>\<^sub>A
       hn_ctxt monomial_assn xb x'a \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xb x'a\<close>
  by (smt assn_aci(5) hn_ctxt_def invalid_assn_distrib invalid_pure_recover is_pure_conv
    merge_thms(4) merge_true_star reorder_enttI safe_poly_vars(3) star_aci(2) star_aci(3))

lemma WTF_RF:
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xb x'a *
       (hn_invalid poly_assn la l'a * hn_invalid int_assn a2' a2 *
        hn_invalid monom_assn a1' a1 *
        hn_invalid poly_assn l l' *
        hn_invalid monomial_assn xa x' *
        hn_invalid poly_assn ax px) \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xb x'a *
       hn_ctxt poly_assn
        la l'a *
       hn_ctxt poly_assn l l' *
       (hn_invalid int_assn a2' a2 *
        hn_invalid monom_assn a1' a1 *
        hn_invalid monomial_assn xa x' *
        hn_invalid poly_assn ax px)\<close>
  \<open>hn_ctxt (invalid_assn monom_assn \<times>\<^sub>a invalid_assn int_assn) xa x' *
       (hn_ctxt poly_assn l l' * hn_invalid poly_assn ax px) \<Longrightarrow>\<^sub>t
       hn_ctxt (monomial_assn) xa x' *
       hn_ctxt poly_assn l l' *
       hn_ctxt poly_assn ax px *
       emp\<close>
  by sepref_dbg_trans_step+

text \<open>The refinement frameword is completely lost here when synthesizing the constants -- it does
  not understant what is pure (actually everything) and what must be destroyed.\<close>
sepref_definition merge_coeffs_impl
  is \<open>RETURN o merge_coeffs\<close>
  :: \<open>poly_assn\<^sup>d \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding merge_coeffs_alt_def
    HOL_list.fold_custom_empty poly_assn_alt_def
  apply (rewrite in \<open>_\<close> annotate_assn[where A=\<open>poly_assn\<close>])
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply (rule WTF_RF | sepref_dbg_trans_step)+
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done

definition full_quicksort_poly where
  \<open>full_quicksort_poly = full_quicksort_ref (\<lambda>x y. x = y \<or> (x, y) \<in> term_order_rel) fst\<close>

lemma down_eq_id_list_rel: \<open>\<Down>(\<langle>Id\<rangle>list_rel) x = x\<close>
  by auto

definition quicksort_poly:: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynomial \<Rightarrow> (llist_polynomial) nres\<close> where
  \<open>quicksort_poly x y  z = quicksort_ref (\<le>) fst (x, y, z)\<close>

term partition_between_ref

definition partition_between_poly :: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynomial \<Rightarrow> (llist_polynomial \<times> nat) nres\<close> where
  \<open>partition_between_poly = partition_between_ref (\<le>) fst\<close>

definition partition_main_poly :: \<open>nat \<Rightarrow> nat \<Rightarrow> llist_polynomial \<Rightarrow> (llist_polynomial \<times> nat) nres\<close> where
  \<open>partition_main_poly = partition_main (\<le>)  fst\<close>

lemma string_list_trans:
  \<open>(xa ::char list list, ya) \<in> lexord (lexord {(x, y). x < y}) \<Longrightarrow>
  (ya, z) \<in> lexord (lexord {(x, y). x < y}) \<Longrightarrow>
    (xa, z) \<in> lexord (lexord {(x, y). x < y})\<close>
  by (smt less_char_def char.less_trans less_than_char_def lexord_partial_trans p2rel_def)

lemma full_quicksort_sort_poly_spec:
  \<open>(full_quicksort_poly, sort_poly_spec) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
proof -
  have xs: \<open>(xs, xs) \<in> \<langle>Id\<rangle>list_rel\<close> and \<open>\<Down>(\<langle>Id\<rangle>list_rel) x = x\<close> for x xs
    by auto
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding full_quicksort_poly_def
    apply (rule full_quicksort_ref_full_quicksort[THEN fref_to_Down_curry, THEN order_trans])
    subgoal
      by (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def
        dest: string_list_trans)
    subgoal
      using total_on_lexord_less_than_char_linear[unfolded var_order_rel_def]
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def less_char_def)
      done
    subgoal by fast
    apply (rule xs)
    apply (subst down_eq_id_list_rel)
    unfolding sorted_wrt_map sort_poly_spec_def
    apply (rule full_quicksort_correct_sorted[where R = \<open>(\<lambda>x y. x = y \<or> (x, y) \<in> term_order_rel)\<close> and h = \<open>fst\<close>,
       THEN order_trans])
    subgoal
      by (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def dest: string_list_trans)
    subgoal for x y
      using total_on_lexord_less_than_char_linear[unfolded var_order_rel_def]
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def
        less_char_def)
      done
   subgoal
    by (auto simp: rel2p_def p2rel_def)
   done
qed


subsection \<open>Lifting to polynomials\<close>

definition merge_sort_poly :: \<open>_\<close> where
\<open>merge_sort_poly = msort (\<lambda>a b. fst a \<le> fst b)\<close>

definition merge_monoms_poly :: \<open>_\<close> where
\<open>merge_monoms_poly = msort (\<le>)\<close>

definition merge_poly :: \<open>_\<close> where
\<open>merge_poly = merge (\<lambda>a b. fst a \<le> fst b)\<close>

definition merge_monoms :: \<open>_\<close> where
\<open>merge_monoms = merge (\<le>)\<close>

definition msort_poly_impl :: \<open>(String.literal list \<times> int) list \<Rightarrow> _\<close> where
\<open>msort_poly_impl = msort (\<lambda>a b. fst a \<le> fst b)\<close>

definition msort_monoms_impl :: \<open>(String.literal list) \<Rightarrow> _\<close> where
\<open>msort_monoms_impl = msort (\<le>)\<close>

lemma msort_poly_impl_alt_def:
  \<open>msort_poly_impl xs =
    (case xs of
      [] \<Rightarrow> []
     | [a] \<Rightarrow> [a]
     | [a,b] \<Rightarrow> if fst a \<le> fst b then [a,b]else [b,a]
     | xs \<Rightarrow> merge_poly
                      (msort_poly_impl (take ((length xs) div 2) xs))
                      (msort_poly_impl (drop ((length xs) div 2) xs)))\<close>
   unfolding msort_poly_impl_def
  apply (auto split: list.splits simp: merge_poly_def)
  done

lemma le_term_order_rel':
  \<open>(\<le>) = (\<lambda>x y. x = y \<or>  term_order_rel' x y)\<close>
  apply (intro ext)
  apply (auto simp add: less_list_def less_eq_list_def
    lexordp_eq_conv_lexord lexordp_def)
  using term_order_rel'_alt_def_lexord term_order_rel'_def apply blast
  using term_order_rel'_alt_def_lexord term_order_rel'_def apply blast
  done

fun lexord_eq where
  \<open>lexord_eq [] _ = True\<close> |
  \<open>lexord_eq (x # xs) (y # ys) = (x < y \<or> (x = y \<and> lexord_eq xs ys))\<close> |
  \<open>lexord_eq _ _ = False\<close>

lemma [simp]:
  \<open>lexord_eq [] [] = True\<close>
  \<open>lexord_eq (a # b)[] = False\<close>
  \<open>lexord_eq [] (a # b) = True\<close>
  apply auto
  done

lemma var_order_rel':
  \<open>(\<le>) = (\<lambda>x y. x = y \<or> (x,y) \<in> var_order_rel)\<close>
  by (intro ext)
   (auto simp add: less_list_def less_eq_list_def
    lexordp_eq_conv_lexord lexordp_def var_order_rel_def
    lexordp_conv_lexord p2rel_def)


lemma var_order_rel'':
  \<open>(x,y) \<in> var_order_rel \<longleftrightarrow> x < y\<close>
  by (metis leD less_than_char_linear lexord_linear neq_iff var_order_rel' var_order_rel_antisym
      var_order_rel_def)

lemma lexord_eq_alt_def1:
  \<open>a \<le> b = lexord_eq a b\<close> for a b :: \<open>String.literal list\<close>
  unfolding le_term_order_rel'
  apply (induction a b rule: lexord_eq.induct)
  apply (auto simp: var_order_rel'' less_eq_list_def)
  done

lemma lexord_eq_alt_def2:
  \<open>(RETURN oo lexord_eq) xs ys =
     REC\<^sub>T (\<lambda>f (xs, ys).
        case (xs, ys) of
           ([], _) \<Rightarrow> RETURN True
         | (x # xs, y # ys) \<Rightarrow>
            if x < y then RETURN True
            else if x = y then f (xs, ys) else RETURN False
        | _ \<Rightarrow> RETURN False)
        (xs, ys)\<close>
  apply (subst eq_commute)
  apply (induction xs ys rule: lexord_eq.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) auto
  done


definition var_order' where
  [simp]: \<open>var_order' = var_order\<close>

lemma var_order_rel[def_pat_rules]:
  \<open>(\<in>)$(x,y)$var_order_rel \<equiv> var_order'$x$y\<close>
  by (auto simp: p2rel_def rel2p_def)

lemma var_order_rel_alt_def:
  \<open>var_order_rel = p2rel char.lexordp\<close>
  apply (auto simp: p2rel_def char.lexordp_conv_lexord var_order_rel_def)
  using char.lexordp_conv_lexord apply auto
  done

lemma var_order_rel_var_order:
  \<open>(x, y) \<in> var_order_rel \<longleftrightarrow> var_order x y\<close>
  by (auto simp: rel2p_def)

lemma var_order_string_le[sepref_import_param]:
  \<open>((<), var_order') \<in> string_rel \<rightarrow> string_rel \<rightarrow> bool_rel\<close>
  apply (auto intro!: frefI simp: string_rel_def String.less_literal_def
     rel2p_def linorder.lexordp_conv_lexord[OF char.linorder_axioms,
      unfolded less_eq_char_def] var_order_rel_def
      p2rel_def
      simp flip: PAC_Polynomials_Term.less_char_def)
  using char.lexordp_conv_lexord apply auto
  done

lemma [sepref_import_param]:
  \<open>( (\<le>), (\<le>)) \<in> monom_rel \<rightarrow> monom_rel \<rightarrow>bool_rel\<close>
  apply (intro fun_relI)
  using list_rel_list_rel_order_iff by fastforce

lemma [sepref_import_param]:
  \<open>( (<), (<)) \<in> string_rel \<rightarrow> string_rel \<rightarrow>bool_rel\<close>
proof -
  have [iff]: \<open>ord.lexordp (<) (literal.explode a) (literal.explode aa) \<longleftrightarrow>
       List.lexordp (<) (literal.explode a) (literal.explode aa)\<close> for a aa
    apply (rule iffI)
     apply (metis PAC_Checker_Relation.less_char_def char.lexordp_conv_lexord less_list_def
        p2rel_def var_order_rel'' var_order_rel_def)
    apply (metis PAC_Checker_Relation.less_char_def char.lexordp_conv_lexord less_list_def
        p2rel_def var_order_rel'' var_order_rel_def)
    done
  show ?thesis
    unfolding string_rel_def less_literal.rep_eq less_than_char_def
      less_eq_list_def PAC_Polynomials_Term.less_char_def[symmetric]
    by (intro fun_relI)
     (auto simp: string_rel_def less_literal.rep_eq
        less_list_def char.lexordp_conv_lexord lexordp_eq_refl
        lexordp_eq_conv_lexord)
qed


lemma lexordp_char_char: \<open>ord_class.lexordp = char.lexordp\<close>
  unfolding char.lexordp_def ord_class.lexordp_def
  by (rule arg_cong[of _ _ lfp])
    (auto intro!: ext)

lemma [sepref_import_param]:
  \<open>( (\<le>), (\<le>)) \<in> string_rel \<rightarrow> string_rel \<rightarrow>bool_rel\<close>
  unfolding string_rel_def less_eq_literal.rep_eq less_than_char_def
    less_eq_list_def PAC_Polynomials_Term.less_char_def[symmetric]
  by (intro fun_relI)
   (auto simp: string_rel_def less_eq_literal.rep_eq less_than_char_def
    less_eq_list_def char.lexordp_eq_conv_lexord lexordp_eq_refl
    lexordp_eq_conv_lexord lexordp_char_char
    simp flip: less_char_def[abs_def])

sepref_register lexord_eq
sepref_definition lexord_eq_term
  is \<open>uncurry (RETURN oo lexord_eq)\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply[[goals_limit=1]]
  unfolding lexord_eq_alt_def2
  by sepref

declare lexord_eq_term.refine[sepref_fr_rules]


lemmas [code del] = msort_poly_impl_def msort_monoms_impl_def
lemmas [code] =
  msort_poly_impl_def[unfolded lexord_eq_alt_def1[abs_def]]
  msort_monoms_impl_def[unfolded msort_msort2]

lemma term_order_rel_trans:
  \<open>(a, aa) \<in> term_order_rel \<Longrightarrow>
       (aa, ab) \<in> term_order_rel \<Longrightarrow> (a, ab) \<in> term_order_rel\<close>
  by (metis PAC_Checker_Relation.less_char_def p2rel_def string_list_trans var_order_rel_def)

lemma merge_sort_poly_sort_poly_spec:
  \<open>(RETURN o merge_sort_poly, sort_poly_spec) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding sort_poly_spec_def merge_sort_poly_def
  apply (intro frefI nres_relI)
  using total_on_lexord_less_than_char_linear var_order_rel_def
  by (auto intro!: sorted_msort simp: sorted_wrt_map rel2p_def
    le_term_order_rel' transp_def dest: term_order_rel_trans)

lemma msort_alt_def:
  \<open>RETURN o (msort f) =
     REC\<^sub>T (\<lambda>g xs.
        case xs of
          [] \<Rightarrow> RETURN []
        | [x] \<Rightarrow> RETURN [x]
        | _ \<Rightarrow> do {
           a \<leftarrow> g (take (size xs div 2) xs);
           b \<leftarrow> g (drop (size xs div 2) xs);
           RETURN (merge f a b)})\<close>
  apply (intro ext)
  unfolding comp_def
  apply (induct_tac f x rule: msort.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal
    by (subst RECT_unfold, refine_mono)
     (smt let_to_bind_conv list.simps(5) msort.simps(3))
  done

lemma monomial_rel_order_map:
  \<open>(x, a, b) \<in> monomial_rel \<Longrightarrow>
       (y, aa, bb) \<in> monomial_rel \<Longrightarrow>
       fst x \<le> fst y \<longleftrightarrow> a \<le> aa\<close>
  apply (cases x; cases y)
  apply auto
  using list_rel_list_rel_order_iff by fastforce+


lemma step_rewrite_pure:
  fixes K :: \<open>('olbl \<times> 'lbl) set\<close>
  shows
    \<open>pure (p2rel (\<langle>K, V, R\<rangle>pac_step_rel_raw)) = pac_step_rel_assn (pure K) (pure V) (pure R)\<close>
    \<open>monomial_assn = pure (monom_rel \<times>\<^sub>r int_rel)\<close> and
  poly_assn_list:
    \<open>poly_assn = pure (\<langle>monom_rel \<times>\<^sub>r int_rel\<rangle>list_rel)\<close>
  subgoal
    apply (intro ext)
    apply (case_tac x; case_tac xa)
    apply (auto simp: relAPP_def p2rel_def pure_def)
    done
  subgoal H
    apply (intro ext)
    apply (case_tac x; case_tac xa)
    by (simp add: list_assn_pure_conv)
  subgoal
    unfolding H
    by (simp add: list_assn_pure_conv relAPP_def)
  done

lemma safe_pac_step_rel_assn[safe_constraint_rules]:
  "is_pure K \<Longrightarrow> is_pure V \<Longrightarrow> is_pure R \<Longrightarrow> is_pure (pac_step_rel_assn K V R)"
  by (auto simp: step_rewrite_pure(1)[symmetric] is_pure_conv)


lemma merge_poly_merge_poly:
  \<open>(merge_poly, merge_poly)
   \<in> poly_rel \<rightarrow> poly_rel \<rightarrow> poly_rel\<close>
   unfolding merge_poly_def
  apply (intro fun_relI)
  subgoal for a a' aa a'a
    apply (induction \<open>(\<lambda>(a :: String.literal list \<times> int)
      (b :: String.literal list \<times> int). fst a \<le> fst b)\<close> a aa
      arbitrary: a' a'a
      rule: merge.induct)
    subgoal
      by (auto elim!: list_relE3 list_relE4 list_relE list_relE2
        simp: monomial_rel_order_map)
    subgoal
      by (auto elim!: list_relE3 list_relE)
    subgoal
      by (auto elim!: list_relE3 list_relE4 list_relE list_relE2)
    done
  done

lemmas [fcomp_norm_unfold] =
  poly_assn_list[symmetric]
  step_rewrite_pure(1)

lemma merge_poly_merge_poly2:
  \<open>(a, b) \<in> poly_rel \<Longrightarrow> (a', b') \<in> poly_rel \<Longrightarrow>
    (merge_poly a a', merge_poly b b') \<in> poly_rel\<close>
  using merge_poly_merge_poly
  unfolding fun_rel_def
  by auto

lemma list_rel_takeD:
  \<open>(a, b) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (n, n')\<in> Id \<Longrightarrow> (take n a, take n' b) \<in> \<langle>R\<rangle>list_rel\<close>
  by (simp add: list_rel_eq_listrel listrel_iff_nth relAPP_def)

lemma list_rel_dropD:
  \<open>(a, b) \<in> \<langle>R\<rangle>list_rel \<Longrightarrow> (n, n')\<in> Id \<Longrightarrow> (drop n a, drop n' b) \<in> \<langle>R\<rangle>list_rel\<close>
  by (simp add: list_rel_eq_listrel listrel_iff_nth relAPP_def)

lemma merge_sort_poly[sepref_import_param]:
  \<open>(msort_poly_impl, merge_sort_poly)
   \<in> poly_rel \<rightarrow> poly_rel\<close>
   unfolding merge_sort_poly_def msort_poly_impl_def
  apply (intro fun_relI)
  subgoal for a a'
    apply (induction \<open>(\<lambda>(a :: String.literal list \<times> int)
      (b :: String.literal list \<times> int). fst a \<le> fst b)\<close> a
      arbitrary: a'
      rule: msort.induct)
    subgoal
      by auto
    subgoal
      by (auto elim!: list_relE3 list_relE)
    subgoal premises p
      using p
      by (auto elim!: list_relE3 list_relE4 list_relE list_relE2
        simp: merge_poly_def[symmetric]
        intro!: list_rel_takeD list_rel_dropD
        intro!: merge_poly_merge_poly2 p(1)[simplified] p(2)[simplified],
        auto simp: list_rel_imp_same_length)
    done
  done



lemmas [sepref_fr_rules] = merge_sort_poly[FCOMP merge_sort_poly_sort_poly_spec]

sepref_definition partition_main_poly_impl
  is \<open>uncurry2 partition_main_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn poly_assn nat_assn \<close>
  unfolding partition_main_poly_def partition_main_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    le_term_order_rel'
  by sepref

declare partition_main_poly_impl.refine[sepref_fr_rules]

sepref_definition partition_between_poly_impl
  is \<open>uncurry2 partition_between_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn poly_assn nat_assn \<close>
  unfolding partition_between_poly_def partition_between_ref_def
    partition_main_poly_def[symmetric]
  unfolding choose_pivot3_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def choose_pivot_def
    lexord_eq_alt_def1
  by sepref

declare partition_between_poly_impl.refine[sepref_fr_rules]

sepref_definition quicksort_poly_impl
  is \<open>uncurry2 quicksort_poly\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding partition_main_poly_def quicksort_ref_def quicksort_poly_def
    partition_between_poly_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] = quicksort_poly_impl.refine

sepref_register quicksort_poly
sepref_definition full_quicksort_poly_impl
  is \<open>full_quicksort_poly\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding full_quicksort_poly_def full_quicksort_ref_def
    quicksort_poly_def[symmetric]
    le_term_order_rel'[symmetric]
    term_order_rel'_def[symmetric]
    List.null_def
  by sepref


lemmas sort_poly_spec_hnr =
  full_quicksort_poly_impl.refine[FCOMP full_quicksort_sort_poly_spec]

declare merge_coeffs_impl.refine[sepref_fr_rules]

sepref_definition normalize_poly_impl
  is \<open>normalize_poly\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding normalize_poly_def
  by sepref

declare normalize_poly_impl.refine[sepref_fr_rules]


definition full_quicksort_vars where
  \<open>full_quicksort_vars = full_quicksort_ref (\<lambda>x y. x = y \<or> (x, y) \<in> var_order_rel) id\<close>


definition quicksort_vars:: \<open>nat \<Rightarrow> nat \<Rightarrow> string list \<Rightarrow> (string list) nres\<close> where
  \<open>quicksort_vars x y  z = quicksort_ref (\<le>) id (x, y, z)\<close>


definition partition_between_vars :: \<open>nat \<Rightarrow> nat \<Rightarrow> string list \<Rightarrow> (string list \<times> nat) nres\<close> where
  \<open>partition_between_vars = partition_between_ref (\<le>) id\<close>

definition partition_main_vars :: \<open>nat \<Rightarrow> nat \<Rightarrow> string list \<Rightarrow> (string list \<times> nat) nres\<close> where
  \<open>partition_main_vars = partition_main (\<le>) id\<close>

lemma total_on_lexord_less_than_char_linear2:
  \<open>xs \<noteq> ys \<Longrightarrow> (xs, ys) \<notin> lexord (less_than_char) \<longleftrightarrow>
       (ys, xs) \<in> lexord less_than_char\<close>
   using lexord_linear[of \<open>less_than_char\<close> xs ys]
   using lexord_linear[of \<open>less_than_char\<close>] less_than_char_linear
   apply (auto simp: Relation.total_on_def)
   using lexord_irrefl[OF irrefl_less_than_char]
     antisym_lexord[OF antisym_less_than_char irrefl_less_than_char]
   apply (auto simp: antisym_def)
   done

lemma string_trans:
  \<open>(xa, ya) \<in> lexord {(x::char, y::char). x < y} \<Longrightarrow>
  (ya, z) \<in> lexord {(x::char, y::char). x < y} \<Longrightarrow>
  (xa, z) \<in> lexord {(x::char, y::char). x < y}\<close>
  by (smt less_char_def char.less_trans less_than_char_def lexord_partial_trans p2rel_def)

lemma full_quicksort_sort_vars_spec:
  \<open>(full_quicksort_vars, sort_coeff) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
proof -
  have xs: \<open>(xs, xs) \<in> \<langle>Id\<rangle>list_rel\<close> and \<open>\<Down>(\<langle>Id\<rangle>list_rel) x = x\<close> for x xs
    by auto
  show ?thesis
    apply (intro frefI nres_relI)
    unfolding full_quicksort_vars_def
    apply (rule full_quicksort_ref_full_quicksort[THEN fref_to_Down_curry, THEN order_trans])
    subgoal
      by (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def
        dest: string_trans)
    subgoal
      using total_on_lexord_less_than_char_linear2[unfolded var_order_rel_def]
      apply (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def less_char_def)
      done
    subgoal by fast
    apply (rule xs)
    apply (subst down_eq_id_list_rel)
    unfolding sorted_wrt_map sort_coeff_def
    apply (rule full_quicksort_correct_sorted[where R = \<open>(\<lambda>x y. x = y \<or> (x, y) \<in> var_order_rel)\<close> and h = \<open>id\<close>,
       THEN order_trans])
    subgoal
      by (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def dest: string_trans)
    subgoal for x y
      using total_on_lexord_less_than_char_linear2[unfolded var_order_rel_def]
      by (auto simp: rel2p_def var_order_rel_def p2rel_def Relation.total_on_def
        less_char_def)
   subgoal
    by (auto simp: rel2p_def p2rel_def rel2p_def[abs_def])
   done
qed


sepref_definition partition_main_vars_impl
  is \<open>uncurry2 partition_main_vars\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a (monom_assn)\<^sup>k \<rightarrow>\<^sub>a prod_assn (monom_assn) nat_assn\<close>
  unfolding partition_main_vars_def partition_main_def
    var_order_rel_var_order
    var_order'_def[symmetric]
    term_order_rel'_alt_def
    le_term_order_rel'
    id_apply
    by sepref

declare partition_main_vars_impl.refine[sepref_fr_rules]

sepref_definition partition_between_vars_impl
  is \<open>uncurry2 partition_between_vars\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a prod_assn monom_assn nat_assn \<close>
  unfolding partition_between_vars_def partition_between_ref_def
    partition_main_vars_def[symmetric]
  unfolding choose_pivot3_def
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def choose_pivot_def
    le_term_order_rel' id_apply
  by sepref

declare partition_between_vars_impl.refine[sepref_fr_rules]

sepref_definition quicksort_vars_impl
  is \<open>uncurry2 quicksort_vars\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a monom_assn\<^sup>k \<rightarrow>\<^sub>a monom_assn\<close>
  unfolding partition_main_vars_def quicksort_ref_def quicksort_vars_def
    partition_between_vars_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] = quicksort_vars_impl.refine

sepref_register quicksort_vars


lemma le_var_order_rel:
  \<open>(\<le>) = (\<lambda>x y. x = y \<or> (x, y) \<in> var_order_rel)\<close>
  by (intro ext)
   (auto simp add: less_list_def less_eq_list_def rel2p_def
      p2rel_def lexordp_conv_lexord p2rel_def var_order_rel_def
    lexordp_eq_conv_lexord lexordp_def)

sepref_definition full_quicksort_vars_impl
  is \<open>full_quicksort_vars\<close>
  :: \<open>monom_assn\<^sup>k \<rightarrow>\<^sub>a monom_assn\<close>
  unfolding full_quicksort_vars_def full_quicksort_ref_def
    quicksort_vars_def[symmetric]
    le_var_order_rel[symmetric]
    term_order_rel'_def[symmetric]
    List.null_def
  by sepref


lemmas sort_vars_spec_hnr =
  full_quicksort_vars_impl.refine[FCOMP full_quicksort_sort_vars_spec]

lemma string_rel_order_map:
  \<open>(x, a) \<in> string_rel \<Longrightarrow>
       (y, aa) \<in> string_rel \<Longrightarrow>
       x \<le> y \<longleftrightarrow> a \<le> aa\<close>
  unfolding string_rel_def less_eq_literal.rep_eq less_than_char_def
    less_eq_list_def PAC_Polynomials_Term.less_char_def[symmetric]
  by (auto simp: string_rel_def less_eq_literal.rep_eq less_than_char_def
    less_eq_list_def char.lexordp_eq_conv_lexord lexordp_eq_refl
    lexordp_char_char lexordp_eq_conv_lexord
    simp flip: less_char_def[abs_def])

lemma merge_monoms_merge_monoms:
  \<open>(merge_monoms, merge_monoms) \<in> monom_rel \<rightarrow> monom_rel \<rightarrow> monom_rel\<close>
   unfolding merge_monoms_def
  apply (intro fun_relI)
  subgoal for a a' aa a'a
    apply (induction \<open>(\<lambda>(a :: String.literal)
      (b :: String.literal). a \<le> b)\<close> a aa
      arbitrary: a' a'a
      rule: merge.induct)
    subgoal
      by (auto elim!: list_relE3 list_relE4 list_relE list_relE2
        simp: string_rel_order_map)
    subgoal
      by (auto elim!: list_relE3 list_relE)
    subgoal
      by (auto elim!: list_relE3 list_relE4 list_relE list_relE2)
    done
  done

lemma merge_monoms_merge_monoms2:
  \<open>(a, b) \<in> monom_rel \<Longrightarrow> (a', b') \<in> monom_rel \<Longrightarrow>
    (merge_monoms a a', merge_monoms b b') \<in> monom_rel\<close>
  using merge_monoms_merge_monoms
  unfolding fun_rel_def merge_monoms_def
  by auto


lemma msort_monoms_impl:
  \<open>(msort_monoms_impl, merge_monoms_poly)
   \<in> monom_rel \<rightarrow> monom_rel\<close>
   unfolding msort_monoms_impl_def merge_monoms_poly_def
  apply (intro fun_relI)
  subgoal for a a'
    apply (induction \<open>(\<lambda>(a :: String.literal)
      (b :: String.literal). a \<le> b)\<close> a
      arbitrary: a'
      rule: msort.induct)
    subgoal
      by auto
    subgoal
      by (auto elim!: list_relE3 list_relE)
    subgoal premises p
      using p
      by (auto elim!: list_relE3 list_relE4 list_relE list_relE2
        simp: merge_monoms_def[symmetric] intro!: list_rel_takeD list_rel_dropD
        intro!: merge_monoms_merge_monoms2 p(1)[simplified] p(2)[simplified])
        (simp_all add: list_rel_imp_same_length)
    done
  done

lemma merge_sort_monoms_sort_monoms_spec:
  \<open>(RETURN o merge_monoms_poly, sort_coeff) \<in> \<langle>Id\<rangle>list_rel \<rightarrow>\<^sub>f \<langle>\<langle>Id\<rangle>list_rel\<rangle>nres_rel\<close>
  unfolding merge_monoms_poly_def sort_coeff_def
  by (intro frefI nres_relI)
    (auto intro!: sorted_msort simp: sorted_wrt_map rel2p_def
     le_term_order_rel' transp_def rel2p_def[abs_def]
     simp flip: le_var_order_rel)

sepref_register sort_coeff
lemma  [sepref_fr_rules]:
  \<open>(return o msort_monoms_impl, sort_coeff) \<in> monom_assn\<^sup>k \<rightarrow>\<^sub>a monom_assn\<close>
  using msort_monoms_impl[sepref_param, FCOMP merge_sort_monoms_sort_monoms_spec]
  by auto

sepref_definition sort_all_coeffs_impl
  is \<open>sort_all_coeffs\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding sort_all_coeffs_def
    HOL_list.fold_custom_empty
  by sepref

declare sort_all_coeffs_impl.refine[sepref_fr_rules]

lemma merge_coeffs0_alt_def:
  \<open>(RETURN o merge_coeffs0) p =
   REC\<^sub>T(\<lambda>f p.
     (case p of
       [] \<Rightarrow> RETURN []
     | [p] => if snd p = 0 then RETURN [] else RETURN [p]
     | ((xs, n) # (ys, m) # p) \<Rightarrow>
      (if xs = ys
       then if n + m \<noteq> 0 then f ((xs, n + m) # p) else f p
       else if n = 0 then
          do {p \<leftarrow> f ((ys, m) # p);
            RETURN p}
       else do {p \<leftarrow> f ((ys, m) # p);
            RETURN ((xs, n) # p)})))
    p\<close>
  apply (subst eq_commute)
  apply (induction p rule: merge_coeffs0.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) (auto simp: let_to_bind_conv)
  done

text \<open>Again, Sepref does not understand what is going here.\<close>
sepref_definition merge_coeffs0_impl
  is \<open>RETURN o merge_coeffs0\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding merge_coeffs0_alt_def
    HOL_list.fold_custom_empty
  apply sepref_dbg_preproc
  apply sepref_dbg_cons_init
  apply sepref_dbg_id
  apply sepref_dbg_monadify
  apply sepref_dbg_opt_init
  apply (rule WTF_RF | sepref_dbg_trans_step)+
  apply sepref_dbg_opt
  apply sepref_dbg_cons_solve
  apply sepref_dbg_cons_solve
  apply sepref_dbg_constraints
  done


declare merge_coeffs0_impl.refine[sepref_fr_rules]

sepref_definition fully_normalize_poly_impl
  is \<open>full_normalize_poly\<close>
  :: \<open>poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding full_normalize_poly_def
  by sepref

declare fully_normalize_poly_impl.refine[sepref_fr_rules]


end