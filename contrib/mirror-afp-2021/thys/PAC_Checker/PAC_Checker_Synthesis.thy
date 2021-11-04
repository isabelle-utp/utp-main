(*
  File:         PAC_Checker_Synthesis.thy
  Author:       Mathias Fleury, Daniela Kaufmann, JKU
  Maintainer:   Mathias Fleury, JKU
*)
theory PAC_Checker_Synthesis
  imports PAC_Checker WB_Sort PAC_Checker_Relation
    PAC_Checker_Init More_Loops PAC_Version
begin

section \<open>Code Synthesis of the Complete Checker\<close>

text \<open>We here combine refine the full checker, using the initialisation provided in another file and
adding more efficient data structures (mostly replacing the set of variables by a more efficient
hash map).\<close>

abbreviation vars_assn where
  \<open>vars_assn \<equiv> hs.assn string_assn\<close>

fun vars_of_monom_in where
  \<open>vars_of_monom_in [] _ = True\<close> |
  \<open>vars_of_monom_in (x # xs) \<V> \<longleftrightarrow> x \<in> \<V> \<and> vars_of_monom_in xs \<V>\<close>

fun vars_of_poly_in where
  \<open>vars_of_poly_in [] _ = True\<close> |
  \<open>vars_of_poly_in ((x, _) # xs) \<V> \<longleftrightarrow> vars_of_monom_in x \<V> \<and> vars_of_poly_in xs \<V>\<close>

lemma vars_of_monom_in_alt_def:
  \<open>vars_of_monom_in xs \<V> \<longleftrightarrow> set xs \<subseteq> \<V>\<close>
  by (induction xs)
   auto

lemma vars_llist_alt_def:
  \<open>vars_llist xs \<subseteq> \<V> \<longleftrightarrow> vars_of_poly_in xs \<V>\<close>
  by (induction xs)
   (auto simp: vars_llist_def vars_of_monom_in_alt_def)

lemma vars_of_monom_in_alt_def2:
  \<open>vars_of_monom_in xs \<V> \<longleftrightarrow> fold (\<lambda>x b. b \<and> x \<in> \<V>) xs True\<close>
  apply (subst foldr_fold[symmetric])
  subgoal by auto
  subgoal by (induction xs) auto
  done

sepref_definition vars_of_monom_in_impl
  is \<open>uncurry (RETURN oo vars_of_monom_in)\<close>
  :: \<open>(list_assn string_assn)\<^sup>k *\<^sub>a vars_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding vars_of_monom_in_alt_def2
  by sepref

declare vars_of_monom_in_impl.refine[sepref_fr_rules]

lemma vars_of_poly_in_alt_def2:
  \<open>vars_of_poly_in xs \<V> \<longleftrightarrow> fold (\<lambda>(x, _) b. b \<and> vars_of_monom_in x \<V>) xs True\<close>
  apply (subst foldr_fold[symmetric])
  subgoal by auto
  subgoal by (induction xs) auto
  done


sepref_definition vars_of_poly_in_impl
  is \<open>uncurry (RETURN oo vars_of_poly_in)\<close>
  :: \<open>(poly_assn)\<^sup>k *\<^sub>a vars_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  unfolding vars_of_poly_in_alt_def2
  by sepref

declare vars_of_poly_in_impl.refine[sepref_fr_rules]


definition union_vars_monom :: \<open>string list \<Rightarrow> string set \<Rightarrow> string set\<close> where
\<open>union_vars_monom xs \<V> = fold insert xs \<V>\<close>

definition union_vars_poly :: \<open>llist_polynomial \<Rightarrow> string set \<Rightarrow> string set\<close> where
\<open>union_vars_poly xs \<V> = fold (\<lambda>(xs, _) \<V>. union_vars_monom xs \<V>) xs \<V>\<close>

lemma union_vars_monom_alt_def:
  \<open>union_vars_monom xs \<V> = \<V> \<union> set xs\<close>
  unfolding union_vars_monom_def
  apply (subst foldr_fold[symmetric])
  subgoal for x y
    by (cases x; cases y) auto
  subgoal
    by (induction xs) auto
  done

lemma union_vars_poly_alt_def:
  \<open>union_vars_poly xs \<V> = \<V> \<union> vars_llist xs\<close>
  unfolding union_vars_poly_def
  apply (subst foldr_fold[symmetric])
  subgoal for x y
    by (cases x; cases y)
      (auto simp: union_vars_monom_alt_def)
  subgoal
    by (induction xs)
     (auto simp: vars_llist_def union_vars_monom_alt_def)
   done

sepref_definition union_vars_monom_impl
  is \<open>uncurry (RETURN oo union_vars_monom)\<close>
  :: \<open>monom_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_monom_def
  by sepref

declare union_vars_monom_impl.refine[sepref_fr_rules]

sepref_definition union_vars_poly_impl
  is \<open>uncurry (RETURN oo union_vars_poly)\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding union_vars_poly_def
  by sepref

declare union_vars_poly_impl.refine[sepref_fr_rules]


hide_const (open) Autoref_Fix_Rel.CONSTRAINT

fun status_assn where
  \<open>status_assn _ CSUCCESS CSUCCESS = emp\<close> |
  \<open>status_assn _ CFOUND CFOUND = emp\<close> |
  \<open>status_assn R (CFAILED a) (CFAILED b) = R a b\<close> |
  \<open>status_assn _ _ _ = false\<close>

lemma SUCCESS_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return CSUCCESS), uncurry0 (RETURN CSUCCESS)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  by (sepref_to_hoare)
    sep_auto

lemma FOUND_hnr[sepref_fr_rules]:
  \<open>(uncurry0 (return CFOUND), uncurry0 (RETURN CFOUND)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  by (sepref_to_hoare)
    sep_auto

lemma is_success_hnr[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  ((return o is_cfound), (RETURN o is_cfound)) \<in> (status_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply (sepref_to_hoare)
  apply (rename_tac xi x; case_tac xi; case_tac x)
  apply sep_auto+
  done

lemma is_cfailed_hnr[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  ((return o is_cfailed), (RETURN o is_cfailed)) \<in> (status_assn R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  apply (sepref_to_hoare)
  apply (rename_tac xi x; case_tac xi; case_tac x)
  apply  sep_auto+
  done

lemma merge_cstatus_hnr[sepref_fr_rules]:
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  (uncurry (return oo merge_cstatus), uncurry (RETURN oo merge_cstatus)) \<in>
    (status_assn R)\<^sup>k *\<^sub>a  (status_assn R)\<^sup>k \<rightarrow>\<^sub>a status_assn R\<close>
  apply (sepref_to_hoare)
  by (case_tac b; case_tac bi; case_tac a; case_tac ai; sep_auto simp: is_pure_conv pure_app_eq)

sepref_definition add_poly_impl
  is \<open>add_poly_l\<close>
  :: \<open>(poly_assn \<times>\<^sub>a poly_assn)\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding add_poly_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref


declare add_poly_impl.refine[sepref_fr_rules]


sepref_register mult_monomials
lemma mult_monoms_alt_def:
  \<open>(RETURN oo mult_monoms) x y = REC\<^sub>T
    (\<lambda>f (p, q).
      case (p, q) of
        ([], _) \<Rightarrow> RETURN q
       | (_, []) \<Rightarrow> RETURN p
       | (x # p, y # q) \<Rightarrow>
        (if x = y then do {
          pq \<leftarrow> f (p, q);
           RETURN (x # pq)}
        else if (x, y) \<in> var_order_rel
        then do {
          pq \<leftarrow> f (p, y # q);
          RETURN (x # pq)}
        else do {
          pq \<leftarrow>  f (x # p, q);
          RETURN (y # pq)}))
     (x, y)\<close>
  apply (subst eq_commute)
  apply (induction x y rule: mult_monoms.induct)
  subgoal for p
    by (subst RECT_unfold, refine_mono) (auto split: list.splits)
  subgoal for p
    by (subst RECT_unfold, refine_mono) (auto split: list.splits)
  subgoal for x p y q
    by (subst RECT_unfold, refine_mono) (auto split: list.splits simp: let_to_bind_conv)
  done


sepref_definition mult_monoms_impl
  is \<open>uncurry (RETURN oo mult_monoms)\<close>
  :: \<open>(monom_assn)\<^sup>k *\<^sub>a (monom_assn)\<^sup>k \<rightarrow>\<^sub>a (monom_assn)\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_raw_def
    HOL_list.fold_custom_empty
    var_order'_def[symmetric]
    term_order_rel'_alt_def
    mult_monoms_alt_def
    var_order_rel_var_order
  by sepref

declare mult_monoms_impl.refine[sepref_fr_rules]

sepref_definition mult_monomials_impl
  is \<open>uncurry (RETURN oo mult_monomials)\<close>
  :: \<open>(monomial_assn)\<^sup>k *\<^sub>a (monomial_assn)\<^sup>k \<rightarrow>\<^sub>a (monomial_assn)\<close>
  supply [[goals_limit=1]]
  unfolding mult_monomials_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref


lemma map_append_alt_def2:
  \<open>(RETURN o (map_append f b)) xs = REC\<^sub>T
    (\<lambda>g xs. case xs of [] \<Rightarrow> RETURN b
      | x # xs \<Rightarrow> do {
           y \<leftarrow> g xs;
           RETURN (f x # y)
     }) xs\<close>
   apply (subst eq_commute)
  apply (induction f b xs rule: map_append.induct)
  subgoal by (subst RECT_unfold, refine_mono) auto
  subgoal by (subst RECT_unfold, refine_mono) auto
  done


definition map_append_poly_mult where
  \<open>map_append_poly_mult x = map_append (mult_monomials x)\<close>

declare mult_monomials_impl.refine[sepref_fr_rules]

sepref_definition map_append_poly_mult_impl
  is \<open>uncurry2 (RETURN ooo map_append_poly_mult)\<close>
  :: \<open>monomial_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  unfolding map_append_poly_mult_def
    map_append_alt_def2
  by sepref

declare map_append_poly_mult_impl.refine[sepref_fr_rules]

text \<open>TODO @{thm map_by_foldl} is the worst possible implementation of map!\<close>
sepref_definition mult_poly_raw_impl
  is \<open>uncurry (RETURN oo mult_poly_raw)\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  supply [[eta_contract = false, show_abbrevs=false]]
  unfolding mult_poly_raw_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    foldl_conv_fold
    fold_eq_nfoldli
    map_append_poly_mult_def[symmetric]
    map_append_alt_def[symmetric]
  by sepref

declare mult_poly_raw_impl.refine[sepref_fr_rules]


sepref_definition mult_poly_impl
  is \<open>uncurry mult_poly_full\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a poly_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
  by sepref

declare mult_poly_impl.refine[sepref_fr_rules]

lemma inverse_monomial:
  \<open>monom_rel\<inverse> \<times>\<^sub>r int_rel = (monom_rel \<times>\<^sub>r int_rel)\<inverse>\<close>
  by (auto)

lemma eq_poly_rel_eq[sepref_import_param]:
  \<open>((=), (=)) \<in> poly_rel \<rightarrow> poly_rel \<rightarrow> bool_rel\<close>
  using list_rel_sv[of \<open>monomial_rel\<close>, OF single_valued_monomial_rel]
  using list_rel_sv[OF single_valued_monomial_rel'[unfolded IS_LEFT_UNIQUE_def inv_list_rel_eq]]
  unfolding inv_list_rel_eq[symmetric]
  by (auto intro!: frefI simp:
      rel2p_def single_valued_def p2rel_def
    simp del: inv_list_rel_eq)

sepref_definition weak_equality_l_impl
  is \<open>uncurry weak_equality_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  supply [[goals_limit=1]]
  unfolding weak_equality_l_def
  by sepref

declare weak_equality_l_impl.refine[sepref_fr_rules]
sepref_register add_poly_l mult_poly_full

abbreviation raw_string_assn :: \<open>string \<Rightarrow> string \<Rightarrow> assn\<close> where
  \<open>raw_string_assn \<equiv> list_assn id_assn\<close>

definition show_nat :: \<open>nat \<Rightarrow> string\<close> where
  \<open>show_nat i = show i\<close>

lemma [sepref_import_param]:
  \<open>(show_nat, show_nat) \<in> nat_rel \<rightarrow> \<langle>Id\<rangle>list_rel\<close>
  by (auto intro: fun_relI)

lemma status_assn_pure_conv:
  \<open>status_assn (id_assn) a b = id_assn a b\<close>
  by (cases a; cases b)
    (auto simp: pure_def)


lemma [sepref_fr_rules]:
  \<open>(uncurry3 (\<lambda>x y. return oo (error_msg_not_equal_dom x y)), uncurry3 check_not_equal_dom_err) \<in>
  poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  unfolding show_nat_def[symmetric] list_assn_pure_conv
    prod_assn_pure_conv check_not_equal_dom_err_def
  by (sepref_to_hoare; sep_auto simp: error_msg_not_equal_dom_def)



lemma [sepref_fr_rules]:
  \<open>(return o (error_msg_notin_dom o nat_of_uint64), RETURN o error_msg_notin_dom)
   \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  \<open>(return o (error_msg_reused_dom o nat_of_uint64), RETURN o error_msg_reused_dom)
    \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
  \<open>(uncurry (return oo (\<lambda>i. error_msg (nat_of_uint64 i))), uncurry (RETURN oo error_msg))
    \<in> uint64_nat_assn\<^sup>k *\<^sub>a raw_string_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  \<open>(uncurry (return oo  error_msg), uncurry (RETURN oo error_msg))
   \<in> nat_assn\<^sup>k *\<^sub>a raw_string_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  unfolding error_msg_notin_dom_def list_assn_pure_conv list_rel_id_simp
  unfolding status_assn_pure_conv
  unfolding show_nat_def[symmetric]
  by (sepref_to_hoare; sep_auto simp: uint64_nat_rel_def br_def; fail)+

sepref_definition check_addition_l_impl
  is \<open>uncurry6 check_addition_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a
        uint64_nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding mult_poly_full_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    check_addition_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
  by sepref

declare check_addition_l_impl.refine[sepref_fr_rules]

sepref_register check_mult_l_dom_err

definition check_mult_l_dom_err_impl where
  \<open>check_mult_l_dom_err_impl pd p ia i =
    (if pd then ''The polynomial with id '' @ show (nat_of_uint64 p) @ '' was not found'' else '''') @
    (if ia then ''The id of the resulting id '' @ show (nat_of_uint64 i) @ '' was already given'' else '''')\<close>

definition check_mult_l_mult_err_impl where
  \<open>check_mult_l_mult_err_impl p q pq r =
    ''Multiplying '' @ show p @ '' by '' @ show q @ '' gives '' @ show pq @ '' and not '' @ show r\<close>

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_mult_l_dom_err_impl x y))),
   uncurry3 (check_mult_l_dom_err)) \<in> bool_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a bool_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_mult_l_dom_err_def check_mult_l_dom_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

lemma [sepref_fr_rules]:
  \<open>(uncurry3 ((\<lambda>x y. return oo (check_mult_l_mult_err_impl x y))),
   uncurry3 (check_mult_l_mult_err)) \<in> poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_mult_l_mult_err_def check_mult_l_mult_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

sepref_definition check_mult_l_impl
  is \<open>uncurry6 check_mult_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k  \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_mult_l_def
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
  by sepref

declare check_mult_l_impl.refine[sepref_fr_rules]

definition check_ext_l_dom_err_impl :: \<open>uint64 \<Rightarrow> _\<close>  where
  \<open>check_ext_l_dom_err_impl p =
    ''There is already a polynomial with index '' @ show (nat_of_uint64 p)\<close>

lemma [sepref_fr_rules]:
  \<open>(((return o (check_ext_l_dom_err_impl))),
    (check_extension_l_dom_err)) \<in> uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_dom_err_def check_ext_l_dom_err_impl_def list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done


definition check_extension_l_no_new_var_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_no_new_var_err_impl p =
    ''No new variable could be found in polynomial '' @ show p\<close>

lemma [sepref_fr_rules]:
  \<open>(((return o (check_extension_l_no_new_var_err_impl))),
    (check_extension_l_no_new_var_err)) \<in> poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_no_new_var_err_impl_def check_extension_l_no_new_var_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_side_cond_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_side_cond_err_impl v p r s =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    '' polynomial is '' @ show p @ ''side condition p*p - p = '' @ show s @ '' and should be 0''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry3 (\<lambda>x y. return oo (check_extension_l_side_cond_err_impl x y))),
    uncurry3 (check_extension_l_side_cond_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_side_cond_err_impl_def check_extension_l_side_cond_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done

definition check_extension_l_new_var_multiple_err_impl :: \<open>_ \<Rightarrow> _\<close>  where
  \<open>check_extension_l_new_var_multiple_err_impl v p =
    ''Error while checking side conditions of extensions polynow, var is '' @ show v @
    '' but it either appears at least once in the polynomial or another new variable is created '' @
    show p @ '' but should not.''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry (return oo (check_extension_l_new_var_multiple_err_impl))),
    uncurry (check_extension_l_new_var_multiple_err)) \<in> string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding check_extension_l_new_var_multiple_err_impl_def
     check_extension_l_new_var_multiple_err_def
     list_assn_pure_conv
   apply sepref_to_hoare
   apply sep_auto
   done


sepref_register check_extension_l_dom_err fmlookup'
  check_extension_l_side_cond_err check_extension_l_no_new_var_err
  check_extension_l_new_var_multiple_err

definition uminus_poly :: \<open>llist_polynomial \<Rightarrow> llist_polynomial\<close> where
  \<open>uminus_poly p' = map (\<lambda>(a, b). (a, - b)) p'\<close>

sepref_register uminus_poly
lemma [sepref_import_param]:
  \<open>(map (\<lambda>(a, b). (a, - b)), uminus_poly) \<in> poly_rel \<rightarrow> poly_rel\<close>
  unfolding uminus_poly_def
  apply (intro fun_relI)
  subgoal for p p'
    by (induction p p' rule: list_rel_induct)
     auto
  done

sepref_register vars_of_poly_in
  weak_equality_l

lemma [safe_constraint_rules]:
  \<open>Sepref_Constraints.CONSTRAINT single_valued (the_pure monomial_assn)\<close> and
  single_valued_the_monomial_assn:
    \<open>single_valued (the_pure monomial_assn)\<close>
    \<open>single_valued ((the_pure monomial_assn)\<inverse>)\<close>
  unfolding IS_LEFT_UNIQUE_def[symmetric]
  by (auto simp: step_rewrite_pure single_valued_monomial_rel single_valued_monomial_rel' Sepref_Constraints.CONSTRAINT_def)

sepref_definition check_extension_l_impl
  is \<open>uncurry5 check_extension_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a vars_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k *\<^sub>a string_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k \<rightarrow>\<^sub>a
     status_assn raw_string_assn\<close>
  supply option.splits[split] single_valued_the_monomial_assn[simp]
  supply [[goals_limit=1]]
  unfolding
    HOL_list.fold_custom_empty
    term_order_rel'_def[symmetric]
    term_order_rel'_alt_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    vars_llist_alt_def
    check_extension_l_def
    not_not
    option.case_eq_if
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
  by sepref


declare check_extension_l_impl.refine[sepref_fr_rules]

sepref_definition check_del_l_impl
  is \<open>uncurry2 check_del_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn\<^sup>k *\<^sub>a uint64_nat_assn\<^sup>k \<rightarrow>\<^sub>a status_assn raw_string_assn\<close>
  supply [[goals_limit=1]]
  unfolding check_del_l_def
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
  by sepref

lemmas [sepref_fr_rules] = check_del_l_impl.refine

abbreviation pac_step_rel where
  \<open>pac_step_rel \<equiv> p2rel (\<langle>Id, \<langle>monomial_rel\<rangle>list_rel, Id\<rangle> pac_step_rel_raw)\<close>

sepref_register PAC_Polynomials_Operations.normalize_poly
  pac_src1 pac_src2 new_id pac_mult case_pac_step check_mult_l
  check_addition_l check_del_l check_extension_l

lemma pac_step_rel_assn_alt_def2:
  \<open>hn_ctxt (pac_step_rel_assn nat_assn poly_assn id_assn) b bi =
       hn_val
        (p2rel
          (\<langle>nat_rel, poly_rel, Id :: (string \<times> _) set\<rangle>pac_step_rel_raw)) b bi\<close>
  unfolding poly_assn_list hn_ctxt_def
  by (induction nat_assn poly_assn \<open>id_assn :: string \<Rightarrow> _\<close> b bi rule: pac_step_rel_assn.induct)
   (auto simp: p2rel_def hn_val_unfold pac_step_rel_raw.simps relAPP_def
    pure_app_eq)


lemma is_AddD_import[sepref_fr_rules]:
  assumes \<open>CONSTRAINT is_pure K\<close>  \<open>CONSTRAINT is_pure V\<close>
  shows
    \<open>(return o pac_res, RETURN o pac_res) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Extension x]\<^sub>a
       (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> V\<close>
    \<open>(return o pac_src1, RETURN o pac_src1) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Del x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o new_id, RETURN o new_id) \<in> [\<lambda>x. is_Add x \<or> is_Mult x \<or> is_Extension x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
    \<open>(return o is_Add, RETURN o is_Add) \<in>  (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o is_Mult, RETURN o is_Mult) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o is_Del, RETURN o is_Del) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
    \<open>(return o is_Extension, RETURN o is_Extension) \<in> (pac_step_rel_assn K V R)\<^sup>k \<rightarrow>\<^sub>a bool_assn\<close>
  using assms
  by (sepref_to_hoare; sep_auto simp: pac_step_rel_assn_alt_def is_pure_conv ent_true_drop pure_app_eq
      split: pac_step.splits; fail)+

lemma [sepref_fr_rules]:
  \<open>CONSTRAINT is_pure K \<Longrightarrow>
  (return o pac_src2, RETURN o pac_src2) \<in> [\<lambda>x. is_Add x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> K\<close>
  \<open>CONSTRAINT is_pure V \<Longrightarrow>
  (return o pac_mult, RETURN o pac_mult) \<in> [\<lambda>x. is_Mult x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> V\<close>
  \<open>CONSTRAINT is_pure R \<Longrightarrow>
  (return o new_var, RETURN o new_var) \<in> [\<lambda>x. is_Extension x]\<^sub>a (pac_step_rel_assn K V R)\<^sup>k \<rightarrow> R\<close>
  by (sepref_to_hoare; sep_auto simp: pac_step_rel_assn_alt_def is_pure_conv ent_true_drop pure_app_eq
      split: pac_step.splits; fail)+

lemma is_Mult_lastI:
  \<open>\<not> is_Add b \<Longrightarrow> \<not>is_Mult b \<Longrightarrow> \<not>is_Extension b \<Longrightarrow> is_Del b\<close>
  by (cases b) auto

sepref_register is_cfailed is_Del

definition PAC_checker_l_step' ::  _ where
  \<open>PAC_checker_l_step' a b c d = PAC_checker_l_step a (b, c, d)\<close>

lemma PAC_checker_l_step_alt_def:
  \<open>PAC_checker_l_step a bcd e = (let (b,c,d) = bcd in PAC_checker_l_step' a b c d e)\<close>
  unfolding PAC_checker_l_step'_def by auto

sepref_decl_intf ('k) acode_status is "('k) code_status"
sepref_decl_intf ('k, 'b, 'lbl) apac_step is "('k, 'b, 'lbl) pac_step"

sepref_register merge_cstatus full_normalize_poly new_var is_Add

lemma poly_rel_the_pure:
  \<open>poly_rel = the_pure poly_assn\<close> and
  nat_rel_the_pure:
  \<open>nat_rel = the_pure nat_assn\<close> and
 WTF_RF: \<open>pure (the_pure nat_assn) = nat_assn\<close>
  unfolding poly_assn_list
  by auto

lemma [safe_constraint_rules]:
    \<open>CONSTRAINT IS_LEFT_UNIQUE uint64_nat_rel\<close> and
  single_valued_uint64_nat_rel[safe_constraint_rules]:
    \<open>CONSTRAINT single_valued uint64_nat_rel\<close>
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def uint64_nat_rel_def br_def)

sepref_definition check_step_impl
  is \<open>uncurry4 PAC_checker_l_step'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (pac_step_rel_assn (uint64_nat_assn) poly_assn (string_assn :: string \<Rightarrow> _))\<^sup>d \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro] single_valued_uint64_nat_rel[simp]
  unfolding PAC_checker_l_step_def PAC_checker_l_step'_def
    pac_step.case_eq_if Let_def
     is_success_alt_def[symmetric]
    uminus_poly_def[symmetric]
    HOL_list.fold_custom_empty
  by sepref


declare check_step_impl.refine[sepref_fr_rules]

sepref_register PAC_checker_l_step PAC_checker_l_step' fully_normalize_poly_impl

definition PAC_checker_l' where
  \<open>PAC_checker_l' p \<V> A status steps = PAC_checker_l p (\<V>, A) status steps\<close>

lemma PAC_checker_l_alt_def:
  \<open>PAC_checker_l p \<V>A status steps =
    (let (\<V>, A) = \<V>A in PAC_checker_l' p \<V> A status steps)\<close>
  unfolding PAC_checker_l'_def by auto

sepref_definition PAC_checker_l_impl
  is \<open>uncurry4 PAC_checker_l'\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn\<^sup>d *\<^sub>a (status_assn raw_string_assn)\<^sup>d *\<^sub>a
       (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
     status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding PAC_checker_l_def is_success_alt_def[symmetric] PAC_checker_l_step_alt_def
    nres_bind_let_law[symmetric] PAC_checker_l'_def
  apply (subst nres_bind_let_law)
  by sepref

declare PAC_checker_l_impl.refine[sepref_fr_rules]

abbreviation polys_assn_input where
  \<open>polys_assn_input \<equiv> iam_fmap_assn nat_assn poly_assn\<close>

definition remap_polys_l_dom_err_impl :: \<open>_\<close>  where
  \<open>remap_polys_l_dom_err_impl =
    ''Error during initialisation. Too many polynomials where provided. If this happens,'' @
    ''please report the example to the authors, because something went wrong during '' @
    ''code generation (code generation to arrays is likely to be broken).''\<close>

lemma [sepref_fr_rules]:
  \<open>((uncurry0 (return (remap_polys_l_dom_err_impl))),
    uncurry0 (remap_polys_l_dom_err)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a raw_string_assn\<close>
   unfolding remap_polys_l_dom_err_def
     remap_polys_l_dom_err_def
     list_assn_pure_conv
   by sepref_to_hoare sep_auto

text \<open>MLton is not able to optimise the calls to pow.\<close>
lemma pow_2_64: \<open>(2::nat) ^ 64 = 18446744073709551616\<close>
  by auto

sepref_register upper_bound_on_dom op_fmap_empty

sepref_definition remap_polys_l_impl
  is \<open>uncurry2 remap_polys_l2\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro] indom_mI[dest]
  unfolding remap_polys_l2_def op_fmap_empty_def[symmetric] while_eq_nfoldli[symmetric]
    while_upt_while_direct pow_2_64
    in_dom_m_lookup_iff
    fmlookup'_def[symmetric]
    union_vars_poly_alt_def[symmetric]
  apply (rewrite at \<open>fmupd \<hole>\<close> uint64_of_nat_conv_def[symmetric])
  apply (subst while_upt_while_direct)
  apply simp
  apply (rewrite at \<open>op_fmap_empty\<close> annotate_assn[where A=\<open>polys_assn\<close>])
  by sepref

lemma remap_polys_l2_remap_polys_l:
  \<open>(uncurry2 remap_polys_l2, uncurry2 remap_polys_l) \<in> (Id \<times>\<^sub>r \<langle>Id\<rangle>set_rel) \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel\<close>
  apply (intro frefI fun_relI nres_relI)
  using remap_polys_l2_remap_polys_l by auto

lemma [sepref_fr_rules]:
   \<open>(uncurry2 remap_polys_l_impl,
     uncurry2 remap_polys_l) \<in> poly_assn\<^sup>k *\<^sub>a vars_assn\<^sup>d *\<^sub>a polys_assn_input\<^sup>d \<rightarrow>\<^sub>a
       status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
   using hfcomp_tcomp_pre[OF remap_polys_l2_remap_polys_l remap_polys_l_impl.refine]
   by (auto simp: hrp_comp_def hfprod_def)

sepref_register remap_polys_l

sepref_definition full_checker_l_impl
  is \<open>uncurry2 full_checker_l\<close>
  :: \<open>poly_assn\<^sup>k *\<^sub>a polys_assn_input\<^sup>d *\<^sub>a (list_assn (pac_step_rel_assn (uint64_nat_assn) poly_assn string_assn))\<^sup>k \<rightarrow>\<^sub>a
    status_assn raw_string_assn \<times>\<^sub>a vars_assn \<times>\<^sub>a polys_assn\<close>
  supply [[goals_limit=1]] is_Mult_lastI[intro]
  unfolding full_checker_l_def hs.fold_custom_empty
    union_vars_poly_alt_def[symmetric]
    PAC_checker_l_alt_def
  by sepref

sepref_definition PAC_update_impl
  is \<open>uncurry2 (RETURN ooo fmupd)\<close>
  :: \<open>nat_assn\<^sup>k *\<^sub>a poly_assn\<^sup>k *\<^sub>a (polys_assn_input)\<^sup>d \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding comp_def
  by sepref

sepref_definition PAC_empty_impl
  is \<open>uncurry0 (RETURN fmempty)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a polys_assn_input\<close>
  unfolding op_iam_fmap_empty_def[symmetric] pat_fmap_empty
  by sepref

sepref_definition empty_vars_impl
  is \<open>uncurry0 (RETURN {})\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vars_assn\<close>
  unfolding hs.fold_custom_empty
  by sepref

text \<open>This is a hack for performance. There is no need to recheck that that a char is valid when
  working on chars coming from strings... It is not that important in most cases, but in our case
  the preformance difference is really large.\<close>


definition unsafe_asciis_of_literal :: \<open>_\<close> where
  \<open>unsafe_asciis_of_literal xs = String.asciis_of_literal xs\<close>

definition unsafe_asciis_of_literal' :: \<open>_\<close> where
  [simp, symmetric, code]: \<open>unsafe_asciis_of_literal' = unsafe_asciis_of_literal\<close>

code_printing
  constant unsafe_asciis_of_literal' \<rightharpoonup>
    (SML) "!(List.map (fn c => let val k = Char.ord c in IntInf.fromInt k end) /o String.explode)"

text \<open>
  Now comes the big and ugly and unsafe hack.

  Basically, we try to avoid the conversion to IntInf when calculating the hash. The performance
  gain is roughly 40\%, which is a LOT and definitively something we need to do. We are aware that the
  SML semantic encourages compilers to optimise conversions, but this does not happen here,
  corroborating our early observation on the verified SAT solver IsaSAT.x
\<close>
definition raw_explode where
  [simp]: \<open>raw_explode = String.explode\<close>
code_printing
  constant raw_explode \<rightharpoonup>
    (SML) "String.explode"

definition \<open>hashcode_literal' s \<equiv>
    foldl (\<lambda>h x. h * 33 + uint32_of_int (of_char x)) 5381
     (raw_explode s)\<close>

lemmas [code] =
  hashcode_literal_def[unfolded String.explode_code
    unsafe_asciis_of_literal_def[symmetric]]

definition uint32_of_char where
  [symmetric, code_unfold]: \<open>uint32_of_char x = uint32_of_int (int_of_char x)\<close>


code_printing
  constant uint32_of_char \<rightharpoonup>
    (SML) "!(Word32.fromInt /o (Char.ord))"

lemma [code]: \<open>hashcode s = hashcode_literal' s\<close>
  unfolding hashcode_literal_def hashcode_list_def
  apply (auto simp: unsafe_asciis_of_literal_def hashcode_list_def
     String.asciis_of_literal_def hashcode_literal_def hashcode_literal'_def)
  done

text \<open>We compile Pastèque in \<^file>\<open>PAC_Checker_MLton.thy\<close>.\<close>
export_code PAC_checker_l_impl PAC_update_impl PAC_empty_impl the_error is_cfailed is_cfound
  int_of_integer Del Add Mult nat_of_integer String.implode remap_polys_l_impl
  fully_normalize_poly_impl union_vars_poly_impl empty_vars_impl
  full_checker_l_impl check_step_impl CSUCCESS
  Extension hashcode_literal' version
  in SML_imp module_name PAC_Checker


section \<open>Correctness theorem\<close>

context poly_embed
begin

definition full_poly_assn where
  \<open>full_poly_assn = hr_comp poly_assn (fully_unsorted_poly_rel O mset_poly_rel)\<close>

definition full_poly_input_assn where
  \<open>full_poly_input_assn = hr_comp
        (hr_comp polys_assn_input
          (\<langle>nat_rel, fully_unsorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
        polys_rel\<close>

definition fully_pac_assn where
  \<open>fully_pac_assn = (list_assn
        (hr_comp (pac_step_rel_assn uint64_nat_assn poly_assn string_assn)
          (p2rel
            (\<langle>nat_rel,
             fully_unsorted_poly_rel O
             mset_poly_rel, var_rel\<rangle>pac_step_rel_raw))))\<close>

definition code_status_assn where
  \<open>code_status_assn = hr_comp (status_assn raw_string_assn)
                            code_status_status_rel\<close>

definition full_vars_assn where
  \<open>full_vars_assn = hr_comp (hs.assn string_assn)
                              (\<langle>var_rel\<rangle>set_rel)\<close>

lemma polys_rel_full_polys_rel:
  \<open>polys_rel_full = Id \<times>\<^sub>r polys_rel\<close>
  by (auto simp: polys_rel_full_def)

definition full_polys_assn :: \<open>_\<close> where
\<open>full_polys_assn = hr_comp (hr_comp polys_assn
                              (\<langle>nat_rel,
                               sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
                            polys_rel\<close>

text \<open>

Below is the full correctness theorems. It basically states that:

  \<^enum> assuming that the input polynomials have no duplicate variables


Then:

\<^enum> if the checker returns \<^term>\<open>CFOUND\<close>, the spec is in the ideal
  and the PAC file is correct

\<^enum> if the checker returns \<^term>\<open>CSUCCESS\<close>, the PAC file is correct (but
there is no information on the spec, aka checking failed)

\<^enum> if the checker return \<^term>\<open>CFAILED err\<close>, then checking failed (and
\<^term>\<open>err\<close> \<^emph>\<open>might\<close> give you an indication of the error, but the correctness
theorem does not say anything about that).


The input parameters are:

\<^enum> the specification polynomial represented as a list

\<^enum> the input polynomials as hash map (as an array of option polynomial)

\<^enum> a represention of the PAC proofs.

\<close>

lemma PAC_full_correctness: (* \htmllink{PAC-full-correctness} *)
  \<open>(uncurry2 full_checker_l_impl,
     uncurry2 (\<lambda>spec A _. PAC_checker_specification spec A))
    \<in> (full_poly_assn)\<^sup>k *\<^sub>a (full_poly_input_assn)\<^sup>d *\<^sub>a (fully_pac_assn)\<^sup>k \<rightarrow>\<^sub>a hr_comp
      (code_status_assn \<times>\<^sub>a full_vars_assn \<times>\<^sub>a hr_comp polys_assn
                              (\<langle>nat_rel, sorted_poly_rel O mset_poly_rel\<rangle>fmap_rel))
                            {((st, G), st', G').
                             st = st' \<and> (st \<noteq> FAILED \<longrightarrow> (G, G') \<in> Id \<times>\<^sub>r polys_rel)}\<close>
  using
    full_checker_l_impl.refine[FCOMP full_checker_l_full_checker',
      FCOMP full_checker_spec',
      unfolded full_poly_assn_def[symmetric]
        full_poly_input_assn_def[symmetric]
        fully_pac_assn_def[symmetric]
        code_status_assn_def[symmetric]
        full_vars_assn_def[symmetric]
        polys_rel_full_polys_rel
        hr_comp_prod_conv
        full_polys_assn_def[symmetric]]
      hr_comp_Id2
   by auto

text \<open>

It would be more efficient to move the parsing to Isabelle, as this
would be more memory efficient (and also reduce the TCB). But now
comes the fun part: It cannot work. A stream (of a file) is consumed
by side effects. Assume that this would work. The code could look like:

\<^term>\<open>
  let next_token = read_file file
  in f (next_token)
\<close>

This code is equal to (in the HOL sense of equality):
\<^term>\<open>
  let _ = read_file file;
      next_token = read_file file
  in f (next_token)
\<close>

However, as an hypothetical \<^term>\<open>read_file\<close> changes the underlying stream, we would get the next
token. Remark that this is already a weird point of ML compilers. Anyway, I see currently two
solutions to this problem:

\<^enum> The meta-argument: use it only in the Refinement Framework in a setup where copies are
disallowed. Basically, this works because we can express the non-duplication constraints on the type
level. However, we cannot forbid people from expressing things directly at the HOL level.

\<^enum> On the target language side, model the stream as the stream and the position. Reading takes two
arguments. First, the position to read. Second, the stream (and the current position) to read. If
the position to read does not match the current position, return an error. This would fit the
correctness theorem of the code generation (roughly ``if it terminates without exception, the answer
is the same''), but it is still unsatisfactory.
\<close>

end

definition \<phi> :: \<open>string \<Rightarrow> nat\<close> where
  \<open>\<phi> = (SOME \<phi>. bij \<phi>)\<close>

lemma bij_\<phi>: \<open>bij \<phi>\<close>
  using someI[of \<open>\<lambda>\<phi> :: string \<Rightarrow> nat. bij \<phi>\<close>]
  unfolding \<phi>_def[symmetric]
  using poly_embed_EX
  by auto

global_interpretation PAC: poly_embed where
  \<phi> = \<phi>
  apply standard
  apply (use bij_\<phi> in \<open>auto simp: bij_def\<close>)
  done


text \<open>The full correctness theorem is @{thm PAC.PAC_full_correctness}.\<close>

end
