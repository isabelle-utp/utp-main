section "Equality VS Proofs"
subsection "Linear Case"
theory LinearCase
  imports VSAlgos
begin




theorem var_not_in_linear : 
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c" 
  shows "freeIn var (Atom (linear_substitution var b c A))"
proof(cases A)
  case (Less p) define d where "d = MPoly_Type.degree p var"
  then show ?thesis using Less apply simp unfolding d_def[symmetric]
    apply simp using not_in_sum
    using not_in_isovarspar assms  not_in_mult not_in_neg not_in_pow not_in_add
    by (metis (no_types, lifting))
next
  case (Eq p)
  define d where "d = MPoly_Type.degree p var"
  then show ?thesis using Eq apply simp unfolding d_def[symmetric]
    apply simp using not_in_sum
    using not_in_isovarspar assms  not_in_mult not_in_neg not_in_pow not_in_add
    by (metis (no_types, lifting))
next
  case (Leq p)
  define d where "d = MPoly_Type.degree p var"
  then show ?thesis using Leq apply simp unfolding d_def[symmetric]
    apply simp using not_in_sum
    using not_in_isovarspar assms  not_in_mult not_in_neg not_in_pow not_in_add
    by (metis (no_types, lifting))
next
  case (Neq p)
  define d where "d = MPoly_Type.degree p var"
  then show ?thesis using Neq apply simp unfolding d_def[symmetric]
    apply simp using not_in_sum
    using not_in_isovarspar assms  not_in_mult not_in_neg not_in_pow not_in_add
    by (metis (no_types, lifting))
qed

(* ----------------------------------------------------------------------------------------------- *)
lemma linear_eq :
  assumes lLength : "length L > var"
  assumes nonzero : "C \<noteq> 0"
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c"
  assumes hb :  "insertion (nth_default 0 (list_update L var( B/C))) b = (B::real)"
  assumes hc : "insertion (nth_default 0 (list_update L var (B/C))) c = (C::real)"
  shows "aEval (Eq(p)) (list_update L var (B/C)) = (aEval (linear_substitution var b c (Eq(p))) (list_update L var v))"
proof -
  define d where "d = MPoly_Type.degree p var"
  define f where "f i = (insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B) ^ i::real)" for i
  have h : "((\<Sum>i = 0..<d+1. f i / C ^ i) = 0) =((\<Sum>i = 0..<d+1. (f i) * C ^ (d - i)) = 0)"
    using normalize_summation nonzero by(auto)
  have "aEval (linear_substitution var b c (Eq(p))) (list_update L var (B/C)) =
    aEval (Eq(\<Sum>i = 0..<d+1. isolate_variable_sparse p var i * (b) ^ i * c ^ (d - i))) (list_update L var (B/C))"
    by (metis (no_types, lifting) d_def linear_substitution.simps(1) sum.cong)
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B) ^ i * C ^ (d - i)) = 0)"
    using assms by(simp add: insertion_sum insertion_mult insertion_add insertion_pow insertion_neg lLength)
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B) ^ i/ (C ^ i)) = 0)"
    using h by(simp add: f_def)
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * ((B/C) ^ i)) = 0)"
    by (metis (no_types, lifting) power_divide sum.cong times_divide_eq_right)
  also have "... = aEval (Eq(p :: real mpoly)) (list_update L var (B/C))"
    using sum_over_degree_insertion d_def lLength by auto
  finally show ?thesis using assms plugInLinear var_not_in_linear var_not_in_eval
    by (meson var_not_in_aEval)
qed





(* -------------------------------------------------------------------------------------------- *)


lemma linear_less :
  assumes lLength : "length L > var"
  assumes nonzero : "C \<noteq> 0"
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) b = (B::real)"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) c = (C::real)"
  shows "aEval (Less(p)) (list_update L var (B/C)) = (aEval (linear_substitution var b c (Less(p))) (list_update L var v))"
proof-
  define d where "d = MPoly_Type.degree p var"
  define f where "f i = (insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B) ^ i::real)" for i
  have h : "(\<Sum>i = 0..<(d+1). (f i) * C ^ (d - i)) * C ^ (d mod 2) < 0  \<longleftrightarrow> (\<Sum>i = 0..<((d::nat)+1). (f i::real) / (C ^ i)) < 0"
    using nonzero normalize_summation_less by auto
  have "aEval (linear_substitution var b c (Less(p))) (list_update L var (B/C))=aEval (Less((\<Sum>i\<in>{0..<(d+1)}. isolate_variable_sparse p var i * (b^i) * (c^(d-i))) * (c ^ (d mod 2)))) (list_update L var (B/C))"
    by (metis (no_types, lifting) d_def linear_substitution.simps(2) sum.cong)
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B) ^ i * C ^ (d - i)) * C ^ (d mod 2) < 0)"
    using assms by(simp add: insertion_sum insertion_mult insertion_add insertion_pow insertion_neg lLength)
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (((B) ^ i) / (C ^ i))) < 0)"
    using f_def h by auto
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B/C)^i) < 0)"
    by (metis (no_types, lifting) power_divide sum.cong)
  also have "... = aEval (Less(p)) (list_update L var (B/C))"
    using d_def sum_over_degree_insertion lLength by auto
  finally show ?thesis using assms plugInLinear var_not_in_linear var_not_in_eval
    by (meson var_not_in_aEval)
qed



(* -------------------------------------------------------------------------------------------- *)

lemma linear_leq :
  assumes lLength : "length L > var"
  assumes nonzero : "C \<noteq> 0"
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) b = (B::real)"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) c = (C::real)"
  shows "aEval (Leq(p)) (list_update L var (B/C)) = (aEval (linear_substitution var b c (Leq(p))) (list_update L var v))"
proof -
  define d where "d = MPoly_Type.degree p var"
  define f where "f i = (insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B) ^ i::real)" for i
  have h1a : "((\<Sum>i = 0..<(d+1). (f i) * C ^ (d - i)) * C ^ (d mod 2) < 0 ) = ((\<Sum>i = 0..<((d::nat)+1). (f i::real) / (C ^ i)) < 0)"
    using nonzero normalize_summation_less by auto
  have "((\<Sum>i = 0..<d+1. f i / C ^ i) = 0) =((\<Sum>i = 0..<d+1. (f i) * C ^ (d - i)) = 0)"
    using normalize_summation nonzero by(auto)
  also have "... =((\<Sum>i = 0..<d+1. (f i) * C ^ (d - i))* C ^ (d mod 2) = 0)"
    using mult_eq_0_iff nonzero power_not_zero by blast
  finally have h1 : "((\<Sum>i = 0..<(d+1). (f i) * C ^ (d - i)) * C ^ (d mod 2) \<le> 0 ) = ((\<Sum>i = 0..<((d::nat)+1). (f i::real) / (C ^ i)) \<le> 0)"
    using h1a by smt 
  have "aEval (linear_substitution var b c (Leq(p))) (list_update L var (B/C))=aEval (Leq((\<Sum>i\<in>{0..<(d+1)}. isolate_variable_sparse p var i * (b^i) * (c^(d-i))) * (c ^ (d mod 2)))) (list_update L var (B/C))"
    by (metis (no_types, lifting) d_def linear_substitution.simps(3) sum.cong)
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B) ^ i * C ^ (d - i)) * C ^ (d mod 2) \<le> 0)"
    using assms by(simp add: insertion_sum insertion_mult insertion_add insertion_pow insertion_neg lLength)
  also have"...= ((\<Sum>i = 0..<(d+1). (insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B) ^ i) / (C ^ i)) \<le> 0)"
    using h1 f_def by auto
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (((B) ^ i) / (C ^ i))) \<le> 0)"
    by auto
  also have "... = ((\<Sum>i = 0..<(d+1). insertion (nth_default 0 (list_update L var (B/C))) (isolate_variable_sparse p var i) * (B/C)^i) \<le> 0)"
    by (metis (no_types, lifting) power_divide sum.cong)
  also have  "... = aEval (Leq(p)) (list_update L var (B/C))"
    using d_def sum_over_degree_insertion lLength by auto
  finally show ?thesis using assms plugInLinear var_not_in_eval var_not_in_linear
    by (meson var_not_in_aEval) 
qed
  (* ----------------------------------------------------------------------------------------------- *)


lemma linear_neq :
  assumes lLength : "length L > var"
  assumes nonzero : "C \<noteq> 0"
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) b = (B::real)"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) c = (C::real)"
  shows "aEval (Neq(p)) (list_update L var (B/C)) = (aEval (linear_substitution var b c (Neq(p))) (list_update L var v))"
proof -
  define d where "d = MPoly_Type.degree p var"
  have "aEval (Eq(p)) (list_update L var (B/C)) = (\<forall>v. aEval (linear_substitution var b c (Eq(p))) (list_update L var v))"
    using linear_eq assms by auto
  also have "... = (\<forall>v. eval (Atom (Eq ((\<Sum>i = 0..<d+1. isolate_variable_sparse p var i * (b) ^ i * c ^ (d - i))))) (list_update L var v))"
    by (metis (no_types, lifting) d_def eval.simps(1) linear_substitution.simps(1) sum.cong)
  also have "... = (\<not>(\<forall>v. eval (Atom (Neq ((\<Sum>i = 0..<d+1. isolate_variable_sparse p var i * (b) ^ i * c ^ (d - i))))) (list_update L var v)))"
    by (metis (no_types, lifting) aEval.simps(1) aEval.simps(4) eval.simps(1) assms(3) assms(4) not_contains_insertion not_in_isovarspar not_in_mult not_in_pow not_in_sum)
  also have "... = (\<not>(\<forall>v. aEval (linear_substitution var b c (Neq(p))) (list_update L var v)))"
    by (metis (full_types) d_def eval.simps(1) linear_substitution.simps(4))
  finally have "... = (\<not>(aEval (Neq(p)) (list_update L var (B/C))))" by simp
  then show ?thesis
    using assms(3) assms(4) var_not_in_aEval var_not_in_linear by blast
qed

(* -------------------------------------------------------------------------------------------- *)



theorem linear :
  assumes lLength : "length L > var"
  assumes "C \<noteq> 0"
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) b = (B::real)"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) c = (C::real)"
  shows "aEval A (list_update L var (B/C))  = (aEval (linear_substitution var b c A) (list_update L var v))"
  apply(cases A) using linear_less[OF assms(1-6)] linear_eq[OF assms(1-6)] linear_leq[OF assms(1-6)] linear_neq[OF assms(1-6)] by auto




lemma var_not_in_linear_fm_helper : 
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c" 
  shows "freeIn (var+z) (linear_substitution_fm_helper var b c F z)"
proof(induction F arbitrary: z)
  case TrueF
  then show ?case by(simp)
next
  case FalseF
  then show ?case by simp
next
  case (Atom x)
  show ?case unfolding linear_substitution_fm_helper.simps liftmap.simps
    using var_not_in_linear[OF not_in_lift[OF assms(1)] not_in_lift[OF assms(2)], of z] by blast
next
  case (And F1 F2)
  then show ?case by simp
next
  case (Or F1 F2)
  then show ?case by simp
next
  case (Neg F)
  then show ?case by simp
next
  case (ExQ F)
  show ?case using ExQ[of "z+1"] by simp
next
  case (AllQ F)
  show ?case using AllQ[of "z+1"] by simp
next
  case (ExN x1 \<phi>)
  then show ?case
    by (metis (no_types, lifting) freeIn.simps(13) group_cancel.add1 liftmap.simps(10) linear_substitution_fm_helper.simps)
next
  case (AllN x1 \<phi>)
  then show ?case
    by (metis (no_types, lifting) freeIn.simps(12) group_cancel.add1 liftmap.simps(9) linear_substitution_fm_helper.simps)
qed

theorem var_not_in_linear_fm : 
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c" 
  shows "freeIn var (linear_substitution_fm var b c F)"
  using var_not_in_linear_fm_helper[OF assms, of 0] by auto

lemma linear_fm_helper :
  assumes "C \<noteq> 0"
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c"
  assumes "insertion (nth_default 0 (list_update (drop z L) var (B/C))) b = (B::real)"
  assumes "insertion (nth_default 0 (list_update (drop z L) var (B/C))) c = (C::real)"
  assumes lLength : "length L > var+z"
  shows "eval F (list_update L (var+z) (B/C))  = (eval (linear_substitution_fm_helper var b c F z) (list_update L (var+z) v))"
  using assms proof(induction F arbitrary:z L)
  case TrueF
  then show ?case by auto
next
  case FalseF
  then show ?case by auto
next
  case (Atom x)
  define L1 where "L1 = drop z L"
  define L2 where "L2 = take z L"
  have L_def : "L = L2 @ L1" using L1_def L2_def by auto
  have h1a : "insertion (nth_default 0 L1) b = B"
    using not_contains_insertion[OF Atom(2), of L1 "B/C" B] Atom(4) unfolding L1_def nth_default_def
    by (metis list_update_id)
  have lengthl2 : "length L2 = z" using L2_def
    using Atom.prems(6) min.absorb2 by auto 
  have "(\<forall>I amount.
         length I = amount \<longrightarrow>
         (\<forall>xs. eval (fm.Atom (Eq (b - Const B))) ([] @ xs) =
               eval (liftFm 0 amount (fm.Atom (Eq (b - Const B)))) ([] @ I @ xs)))"
    by (metis eval_liftFm_helper list.size(3))
  then have "eval (Atom(Eq (b-Const B))) ([] @ L1) = eval (liftFm 0 z (Atom(Eq (b- Const B)))) ([] @ L2 @ L1)"
    using lengthl2 by auto 
  then have "(insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z (b - Const B)) = 0)"
    apply(simp add: insertion_sub insertion_const) using h1a by auto
  then have "insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z b) = B"
    using lift_minus by blast
  then have h1 : "insertion (nth_default 0 (L[var + z := B/C])) (liftPoly 0 z b) = B"
    using not_in_lift[OF Atom(2), of z] L_def
    by (metis list_update_id not_contains_insertion) 
  have h2a : "insertion (nth_default 0 L1) c = C"
    using not_contains_insertion[OF Atom(3), of L1 "B/C" C] Atom(5) unfolding L1_def
    by (metis list_update_id)
  have "(\<forall>I amount.
         length I = amount \<longrightarrow>
         (\<forall>xs. eval (fm.Atom (Eq (c - Const C))) ([] @ xs) =
               eval (liftFm 0 amount (fm.Atom (Eq (c - Const C)))) ([] @ I @ xs)))"
    by (metis eval_liftFm_helper list.size(3))
  then have "eval (Atom(Eq (c-Const C))) ([] @ L1) = eval (liftFm 0 z (Atom(Eq (c- Const C)))) ([] @ L2 @ L1)"
    using lengthl2 by auto 
  then have "(insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z (c - Const C)) = 0)"
    apply(simp add: insertion_sub insertion_const) using h2a by auto
  then have "insertion (nth_default 0 (L2 @ L1)) (liftPoly 0 z c) = C"
    using lift_minus by blast
  then have h2 : "insertion (nth_default 0 (L[var + z := B/C])) (liftPoly 0 z c) = C"
    using not_in_lift[OF Atom(3), of z] L_def
    by (metis list_update_id not_contains_insertion)
  show ?case using linear[OF Atom(6) Atom(1) not_in_lift[OF Atom(2)] not_in_lift[OF Atom(3)], of B, of x, OF h1 h2] unfolding linear_substitution_fm_helper.simps liftmap.simps eval.simps
    .
next
  case (And F1 F2)
  then show ?case by auto
next
  case (Or F1 F2)  
  then show ?case using var_not_in_linear_fm_helper var_not_in_eval unfolding linear_substitution_fm_helper.simps liftmap.simps eval.simps
    by blast
next
  case (Neg F)
  then show ?case using var_not_in_linear_fm_helper var_not_in_eval  unfolding linear_substitution_fm_helper.simps liftmap.simps eval.simps
    by blast
next
  case (ExQ F)
  have droph : "(drop (z + 1) (x#L)) = (drop z L)" for x by auto
  have l : "x # L[var + z := v] = ((x#L)[var+(z+1):=v])" for x v
    by auto
  have "eval (ExQ F) (L[var + z := B/C]) =
        (\<exists>x. eval F ((x # L)[var + (z + 1) := B/C])) "
    apply(simp) unfolding l done

  also have "... = (\<exists>x. eval
              (liftmap (\<lambda>x. \<lambda>a. Atom(linear_substitution (var + x) (liftPoly 0 x b) (liftPoly 0 x c) a)) F (z + 1))
              ((x # L)[var + (z + 1) := v]))"
    apply(rule ex_cong1)
    using ExQ(1)[of "z+1", OF assms(1) assms(2) assms(3)] droph
    unfolding linear_substitution_fm_helper.simps liftmap.simps
    by (metis (mono_tags, lifting) ExQ.prems(4) ExQ.prems(5) ExQ.prems(6) One_nat_def Suc_eq_plus1 Suc_less_eq add_Suc_right list.size(4))
  also have "... = (eval (linear_substitution_fm_helper var b c (ExQ F) z) (L[var + z := v]))"
    unfolding linear_substitution_fm_helper.simps liftmap.simps eval.simps l by simp
  finally show ?case by simp
next
  case (AllQ F)
  have droph : "(drop (z + 1) (x#L)) = (drop z L)" for x by auto
  have l : "x # L[var + z := v] = ((x#L)[var+(z+1):=v])" for x v
    by auto
  have "eval (AllQ F) (L[var + z := B/C]) =
        (\<forall>x. eval F ((x # L)[var + (z + 1) := B/C])) "
    apply(simp) unfolding l done
  also have "... = (\<forall>x. eval
             (liftmap (\<lambda>x.\<lambda>a. Atom(linear_substitution (var + x) (liftPoly 0 x b) (liftPoly 0 x c) a)) F (z + 1))
              ((x # L)[var + (z + 1) := v]))"
    apply(rule all_cong1)
    using AllQ(1)[of "z+1", OF assms(1) assms(2) assms(3)]
      var_not_in_linear_fm_helper[OF assms(2) assms(3)] var_not_in_eval droph
    unfolding linear_substitution_fm_helper.simps liftmap.simps
    by (metis (mono_tags, lifting) AllQ(7) AllQ.prems(4) AllQ.prems(5) One_nat_def Suc_eq_plus1 Suc_less_eq add_Suc_right list.size(4))
  also have "... = (eval (linear_substitution_fm_helper var b c (AllQ F) z) (L[var + z := v]))"
    unfolding linear_substitution_fm_helper.simps liftmap.simps eval.simps l by auto
  finally show ?case by simp
next
  case (ExN x1 \<phi>)
  have list : "\<And>l. length l=x1 \<Longrightarrow> ((drop (z + x1) l @ drop (z + x1 - length l) L)[var := B / C]) = ((drop z L)[var := B / C])"
    by auto
  have map : "\<And> z L. eval (liftmap (\<lambda>x A. fm.Atom (linear_substitution (var + x) (liftPoly 0 x b) (liftPoly 0 x c) A)) \<phi> (z + x1))
      L = eval (liftmap (\<lambda>x A. fm.Atom (linear_substitution (var + x1 + x) (liftPoly 0 (x+x1) b) (liftPoly 0 (x+x1) c) A)) \<phi> z)
      L"
    apply(induction \<phi>) apply(simp_all add:add.commute add.left_commute)
    apply force
    apply force
    by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1))+
  show ?case
    apply simp apply(rule ex_cong1)
    subgoal for l
      using map[of z] ExN(1)[OF ExN(2-4), of "z+x1" "l@L"] ExN(5-7) list
      apply simp
      by (smt (z3) add.commute add.left_commute add_diff_cancel_left' add_mono_thms_linordered_field(4) list list_update_append not_add_less1 order_refl)
    done
next
  case (AllN x1 \<phi>)
  have list : "\<And>l. length l=x1 \<Longrightarrow> ((drop (z + x1) l @ drop (z + x1 - length l) L)[var := B / C]) = ((drop z L)[var := B / C])"
    by auto
  have map : "\<And> z L. eval (liftmap (\<lambda>x A. fm.Atom (linear_substitution (var + x) (liftPoly 0 x b) (liftPoly 0 x c) A)) \<phi> (z + x1))
      L = eval (liftmap (\<lambda>x A. fm.Atom (linear_substitution (var + x1 + x) (liftPoly 0 (x+x1) b) (liftPoly 0 (x+x1) c) A)) \<phi> z)
      L"
    apply(induction \<phi>) apply(simp_all add:add.commute add.left_commute)
    apply force
    apply force
    by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1))+
  show ?case
    apply simp apply(rule all_cong1)
    subgoal for l
      using map[of z] AllN(1)[OF AllN(2-4), of "z+x1" "l@L"] AllN(5-7) list
      apply simp
      by (smt (z3) add.commute add.left_commute add_diff_cancel_left' add_mono_thms_linordered_field(4) list list_update_append not_add_less1 order_refl)
    done
qed

theorem linear_fm :
  assumes lLength : "length L > var"
  assumes "C \<noteq> 0"
  assumes "var \<notin> vars b"
  assumes "var \<notin> vars c"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) b = (B::real)"
  assumes "insertion (nth_default 0 (list_update L var (B/C))) c = (C::real)"
  shows "eval F (list_update L var (B/C))  = (\<forall>v. eval (linear_substitution_fm var b c F) (list_update L var v))"
  unfolding linear_substitution_fm.simps using linear_fm_helper[OF assms(2) assms(3) assms(4), of 0 L B] assms(1) assms(5) assms(6)
  by (simp add: lLength)
end