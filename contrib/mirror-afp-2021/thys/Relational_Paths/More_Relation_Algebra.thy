(* Title:      (More) Relation Algebra
   Author:     Walter Guttmann, Peter Hoefner
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
               Peter Hoefner <peter at hoefner-online.de>
*)

section \<open>(More) Relation Algebra\<close>

text \<open>
This theory presents fundamental properties of relation algebras, which are not present in the AFP entry on relation algebras but could be integrated there \cite{ArmstrongFosterStruthWeber2014}.
Many theorems concern vectors and points.
\<close>

theory More_Relation_Algebra

imports Relation_Algebra.Relation_Algebra_RTC Relation_Algebra.Relation_Algebra_Functions

begin

no_notation
  trancl ("(_\<^sup>+)" [1000] 999)

context relation_algebra
begin

notation
  converse ("(_\<^sup>T)" [102] 101)

abbreviation bijective
  where "bijective x \<equiv> is_inj x \<and> is_sur x"

abbreviation reflexive
  where "reflexive R \<equiv> 1' \<le> R"

abbreviation symmetric
  where "symmetric R \<equiv> R = R\<^sup>T"

abbreviation transitive
  where "transitive R \<equiv> R;R \<le> R"

text \<open>General theorems\<close>

lemma x_leq_triple_x:
  "x \<le> x;x\<^sup>T;x"
proof -
  have "x = x;1' \<cdot> 1"
    by simp
  also have "... \<le> (x \<cdot> 1;1'\<^sup>T);(1' \<cdot> x\<^sup>T;1)"
    by (rule dedekind)
  also have "... = x;(x\<^sup>T;1 \<cdot> 1')"
    by (simp add: inf.commute)
  also have "... \<le> x;(x\<^sup>T \<cdot> 1';1\<^sup>T);(1 \<cdot> (x\<^sup>T)\<^sup>T;1')"
    by (metis comp_assoc dedekind mult_isol)
  also have "... \<le> x;x\<^sup>T;x"
    by simp
  finally show ?thesis .
qed

lemma inj_triple:
  assumes "is_inj x"
    shows "x = x;x\<^sup>T;x"
by (metis assms eq_iff inf_absorb2 is_inj_def mult_1_left mult_subdistr x_leq_triple_x)

lemma p_fun_triple:
  assumes "is_p_fun x"
    shows "x = x;x\<^sup>T;x"
by (metis assms comp_assoc eq_iff is_p_fun_def mult_isol mult_oner x_leq_triple_x)

lemma loop_backward_forward:
  "x\<^sup>T \<le> -(1') + x"
by (metis conv_e conv_times inf.cobounded2 test_dom test_domain test_eq_conv galois_2 inf.commute
           sup.commute)

lemma inj_sur_semi_swap:
  assumes "is_sur z"
      and "is_inj x"
    shows "z \<le> y;x \<Longrightarrow> x \<le> y\<^sup>T;z"
proof -
  assume "z \<le> y;x"
  hence "z;x\<^sup>T \<le> y;(x;x\<^sup>T)"
    by (metis mult_isor mult_assoc)
  hence "z;x\<^sup>T \<le> y"
    using \<open>is_inj x\<close> unfolding is_inj_def
    by (metis mult_isol order.trans mult_1_right)
  hence "(z\<^sup>T;z);x\<^sup>T \<le> z\<^sup>T;y"
    by (metis mult_isol mult_assoc)
  hence "x\<^sup>T \<le> z\<^sup>T;y"
    using \<open>is_sur z\<close> unfolding is_sur_def
    by (metis mult_isor order.trans mult_1_left)
  thus ?thesis
    using conv_iso by fastforce
qed

lemma inj_sur_semi_swap_short:
  assumes "is_sur z"
      and "is_inj x"
    shows "z \<le> y\<^sup>T;x \<Longrightarrow> x \<le> y;z"
proof -
  assume as: "z \<le> y\<^sup>T;x"
  hence "z;x\<^sup>T \<le> y\<^sup>T"
    using \<open>z \<le> y\<^sup>T;x\<close> \<open>is_inj x\<close> unfolding is_inj_def
    by (metis assms(2) conv_invol inf.orderI inf_absorb1 inj_p_fun ss_422iii)
  hence "x\<^sup>T \<le> z\<^sup>T;y\<^sup>T"
    using \<open>is_sur z\<close> unfolding is_sur_def
    by (metis as assms inj_sur_semi_swap conv_contrav conv_invol conv_iso)
  thus "x \<le> y;z"
    using conv_iso by fastforce
qed

lemma bij_swap:
  assumes "bijective z"
      and "bijective x"
    shows "z \<le> y\<^sup>T;x \<longleftrightarrow> x \<le> y;z"
by (metis assms inj_sur_semi_swap conv_invol)

text \<open>The following result is \cite[Proposition 4.2.2(iv)]{SchmidtStroehlein1993}.\<close>

lemma ss422iv:
  assumes "is_p_fun y"
      and "x \<le> y"
      and "y;1 \<le> x;1"
    shows "x = y"
proof -
  have "y \<le> (x;1)\<cdot>y"
    using assms(3) le_infI maddux_20 order_trans by blast
  also have "... \<le> x;x\<^sup>T;y"
    by (metis inf_top_left modular_1_var comp_assoc)
  also have "... \<le> x;y\<^sup>T;y"
    using assms(2) conv_iso mult_double_iso by blast
  also have "... \<le> x"
    using assms(1) comp_assoc is_p_fun_def mult_isol mult_1_right
    by fastforce
  finally show ?thesis
    by (simp add: assms(2) antisym)
qed

text \<open>The following results are variants of \cite[Proposition 4.2.3]{SchmidtStroehlein1993}.\<close>

lemma ss423conv:
  assumes "bijective x"
    shows "x ; y \<le> z \<longleftrightarrow> y \<le> x\<^sup>T ; z"
by (metis assms conv_contrav conv_iso inj_p_fun is_map_def ss423 sur_total)

lemma ss423bij:
  assumes "bijective x"
    shows "y ; x\<^sup>T \<le> z \<longleftrightarrow> y \<le> z ; x"
by (simp add: assms is_map_def p_fun_inj ss423 total_sur)

lemma inj_distr:
  assumes "is_inj z"
    shows "(x\<cdot>y);z = (x;z)\<cdot>(y;z)"
apply (rule antisym)
 using mult_subdistr_var apply blast
using assms conv_iso inj_p_fun p_fun_distl by fastforce

lemma test_converse:
  "x \<cdot> 1' = x\<^sup>T \<cdot> 1'"
by (metis conv_e conv_times inf_le2 is_test_def test_eq_conv)

lemma injective_down_closed:
  assumes "is_inj x"
      and "y \<le> x"
    shows "is_inj y"
by (meson assms conv_iso dual_order.trans is_inj_def mult_isol_var)

lemma injective_sup:
  assumes "is_inj t"
      and "e;t\<^sup>T \<le> 1'"
      and "is_inj e"
    shows "is_inj (t + e)"
proof -
  have 1: "t;e\<^sup>T \<le> 1'"
    using assms(2) conv_contrav conv_e conv_invol conv_iso by fastforce
  have "(t + e);(t + e)\<^sup>T = t;t\<^sup>T + t;e\<^sup>T + e;t\<^sup>T + e;e\<^sup>T"
    by (metis conv_add distrib_left distrib_right' sup_assoc)
  also have "... \<le> 1'"
    using 1 assms by (simp add: is_inj_def le_supI)
  finally show ?thesis
    unfolding is_inj_def .
qed

text \<open>Some (more) results about vectors\<close>

lemma vector_meet_comp:
  assumes "is_vector v"
      and "is_vector w"
    shows "v;w\<^sup>T = v\<cdot>w\<^sup>T"
by (metis assms conv_contrav conv_one inf_top_right is_vector_def vector_1)

lemma vector_meet_comp':
  assumes "is_vector v"
    shows "v;v\<^sup>T = v\<cdot>v\<^sup>T"
using assms vector_meet_comp by blast

lemma vector_meet_comp_x:
  "x;1;x\<^sup>T = x;1\<cdot>1;x\<^sup>T"
by (metis comp_assoc inf_top.right_neutral is_vector_def one_idem_mult vector_1)

lemma vector_meet_comp_x':
  "x;1;x = x;1\<cdot>1;x"
by (metis inf_commute inf_top.right_neutral ra_1)

lemma vector_prop1:
  assumes "is_vector v"
    shows "-v\<^sup>T;v = 0"
by (metis assms compl_inf_bot inf_top.right_neutral one_compl one_idem_mult vector_2)

text \<open>The following results and a number of others in this theory are from \cite{Guttmann2017a}.\<close>

lemma ee:
  assumes "is_vector v"
      and "e \<le> v;-v\<^sup>T"
    shows "e;e = 0"
proof -
  have "e;v \<le> 0"
    by (metis assms annir mult_isor vector_prop1 comp_assoc)
  thus ?thesis
    by (metis assms(2) annil antisym bot_least comp_assoc mult_isol)
qed

lemma et:
  assumes "is_vector v"
      and "e \<le> v;-v\<^sup>T"
      and "t \<le> v;v\<^sup>T"
    shows "e;t = 0"
      and "e;t\<^sup>T = 0"
proof -
  have "e;t \<le> v;-v\<^sup>T;v;v\<^sup>T"
    by (metis assms(2-3) mult_isol_var comp_assoc)
  thus "e;t = 0"
    by (simp add: assms(1) comp_assoc le_bot vector_prop1)
next
  have "t\<^sup>T \<le> v;v\<^sup>T"
    using assms(3) conv_iso by fastforce
  hence "e;t\<^sup>T \<le> v;-v\<^sup>T;v;v\<^sup>T"
    by (metis assms(2) mult_isol_var comp_assoc)
  thus "e;t\<^sup>T = 0"
    by (simp add: assms(1) comp_assoc le_bot vector_prop1)
qed

text \<open>Some (more) results about points\<close>

definition point
  where "point x \<equiv> is_vector x \<and> bijective x"

lemma point_swap:
  assumes "point p"
      and "point q"
    shows "p \<le> x;q \<longleftrightarrow> q \<le> x\<^sup>T;p"
by (metis assms conv_invol inj_sur_semi_swap point_def)

text \<open>Some (more) results about singletons\<close>

abbreviation singleton
  where "singleton x \<equiv> bijective (x;1) \<and> bijective (x\<^sup>T;1)"

lemma singleton_injective:
  assumes "singleton x"
    shows "is_inj x"
using assms injective_down_closed maddux_20 by blast

lemma injective_inv:
  assumes "is_vector v"
      and "singleton e"
      and "e \<le> v;-v\<^sup>T"
      and "t \<le> v;v\<^sup>T"
      and "is_inj t"
    shows "is_inj (t + e)"
by (metis assms singleton_injective injective_sup bot_least et(2))

lemma singleton_is_point:
  assumes "singleton p"
    shows "point (p;1)"
by (simp add: assms comp_assoc is_vector_def point_def)

lemma singleton_transp:
  assumes "singleton p"
    shows "singleton (p\<^sup>T)"
by (simp add: assms)

lemma point_to_singleton:
  assumes "singleton p"
    shows "singleton (1'\<cdot>p;p\<^sup>T)"
using assms dom_def_aux_var dom_one is_vector_def point_def by fastforce

lemma singleton_singletonT:
  assumes "singleton p"
    shows "p;p\<^sup>T \<le> 1'"
using assms singleton_injective is_inj_def by blast

text \<open>Minimality\<close>

abbreviation minimum
  where "minimum x v \<equiv> v \<cdot> -(x\<^sup>T;v)"

text \<open>Regressively finite\<close>

abbreviation regressively_finite
  where "regressively_finite x \<equiv> \<forall>v . is_vector v \<and> v \<le> x\<^sup>T;v \<longrightarrow> v = 0"

lemma regressively_finite_minimum:
  "regressively_finite R \<Longrightarrow> is_vector v \<Longrightarrow> v \<noteq> 0 \<Longrightarrow> minimum R v \<noteq> 0"
using galois_aux2 by blast

lemma regressively_finite_irreflexive:
  assumes "regressively_finite x"
    shows "x \<le> -1'"
proof -
  have 1: "is_vector ((x\<^sup>T \<cdot> 1');1)"
    by (simp add: is_vector_def mult_assoc)
  have "(x\<^sup>T \<cdot> 1');1 = (x\<^sup>T \<cdot> 1');(x\<^sup>T \<cdot> 1');1"
    by (simp add: is_test_def test_comp_eq_mult)
  with 1 have "(x\<^sup>T \<cdot> 1');1 = 0"
    by (metis assms comp_assoc mult_subdistr)
  thus ?thesis
    by (metis conv_e conv_invol conv_times conv_zero galois_aux ss_p18)
qed

end (* relation_algebra *)

subsection \<open>Relation algebras satisfying the Tarski rule\<close>

class relation_algebra_tarski = relation_algebra +
  assumes tarski: "x \<noteq> 0 \<longleftrightarrow> 1;x;1 = 1"
begin

text \<open>Some (more) results about points\<close>

lemma point_equations:
  assumes "is_point p"
  shows "p;1=p"
    and "1;p=1"
    and "p\<^sup>T;1=1"
    and "1;p\<^sup>T=p\<^sup>T"
   apply (metis assms is_point_def is_vector_def)
  using assms is_point_def is_vector_def tarski vector_comp apply fastforce
 apply (metis assms conv_contrav conv_one conv_zero is_point_def is_vector_def tarski)
by (metis assms conv_contrav conv_one is_point_def is_vector_def)

text \<open>The following result is \cite[Proposition 2.4.5(i)]{SchmidtStroehlein1993}.\<close>

lemma point_singleton:
  assumes "is_point p"
      and "is_vector v"
      and "v \<noteq> 0"
      and "v \<le> p"
    shows "v = p"
proof -
  have "1;v = 1"
    using assms(2,3) comp_assoc is_vector_def tarski by fastforce
  hence "p = 1;v \<cdot> p"
    by simp
  also have "... \<le> (1 \<cdot> p;v\<^sup>T);(v \<cdot> 1\<^sup>T;p)"
    using dedekind by blast
  also have "... \<le> p;v\<^sup>T;v"
    by (simp add: mult_subdistl)
  also have "... \<le> p;p\<^sup>T;v"
    using assms(4) conv_iso mult_double_iso by blast
  also have "... \<le> v"
    by (metis assms(1) is_inj_def is_point_def mult_isor mult_onel)
  finally show ?thesis
    using assms(4) by simp
qed

lemma point_not_equal_aux:
  assumes "is_point p"
      and "is_point q"
    shows "p\<noteq>q \<longleftrightarrow> p \<cdot> -q \<noteq> 0"
proof
  show "p \<noteq> q \<Longrightarrow> p \<cdot> - q \<noteq> 0"
  proof (rule contrapos_nn)
    assume "p \<cdot> -q = 0"
    thus "p = q"
     using assms galois_aux2 is_point_def point_singleton by fastforce
  qed
next
  show "p \<cdot> - q \<noteq> 0 \<Longrightarrow> p \<noteq> q"
    using inf_compl_bot by blast
qed

text \<open>The following result is part of \cite[Proposition 2.4.5(ii)]{SchmidtStroehlein1993}.\<close>

lemma point_not_equal:
  assumes "is_point p"
      and "is_point q"
    shows "p\<noteq>q \<longleftrightarrow> p\<le>-q"
      and "p\<le>-q \<longleftrightarrow> p;q\<^sup>T \<le> -1'"
      and "p;q\<^sup>T \<le> -1' \<longleftrightarrow> p\<^sup>T;q \<le> 0"
proof -
  have "p \<noteq> q \<Longrightarrow> p \<le> - q"
    by (metis assms point_not_equal_aux is_point_def vector_compl vector_mult point_singleton
              inf.orderI inf.cobounded1)
  thus "p\<noteq>q \<longleftrightarrow> p\<le>-q"
    by (metis assms(1) galois_aux inf.orderE is_point_def order.refl)
next
  show "(p \<le> - q) = (p ; q\<^sup>T \<le> - 1')"
    by (simp add: conv_galois_2)
next
  show "(p ; q\<^sup>T \<le> - 1') = (p\<^sup>T ; q \<le> 0)"
    by (metis assms(2) compl_bot_eq conv_galois_2 galois_aux maddux_141 mult_1_right
              point_equations(4))
qed

lemma point_is_point:
  "point x \<longleftrightarrow> is_point x"
apply (rule iffI)
 apply (simp add: is_point_def point_def surj_one tarski)
using is_point_def is_vector_def mult_assoc point_def sur_def_var1 tarski by fastforce

lemma point_in_vector_or_complement:
  assumes "point p"
      and "is_vector v"
    shows "p \<le> v \<or> p \<le> -v"
proof (cases "p \<le> -v")
  assume "p \<le> -v"
  thus ?thesis
    by simp
next
  assume "\<not>(p \<le> -v)"
  hence "p\<cdot>v \<noteq> 0"
    by (simp add: galois_aux)
  hence "1;(p\<cdot>v) = 1"
    using assms comp_assoc is_vector_def point_def tarski vector_mult by fastforce
  hence "p \<le> p;(p\<cdot>v)\<^sup>T;(p\<cdot>v)"
    by (metis inf_top.left_neutral modular_2_var)
  also have "... \<le> p;p\<^sup>T;v"
    by (simp add: mult_isol_var)
  also have "... \<le> v"
    using assms(1) comp_assoc point_def ss423conv by fastforce
  finally show ?thesis ..
qed

lemma point_in_vector_or_complement_iff:
  assumes "point p"
      and "is_vector v"
    shows "p \<le> v \<longleftrightarrow> \<not>(p \<le> -v)"
by (metis assms annir compl_top_eq galois_aux inf.orderE one_compl point_def ss423conv tarski
          top_greatest point_in_vector_or_complement)

lemma different_points_consequences:
  assumes "point p"
      and "point q"
      and "p\<noteq>q"
    shows "p\<^sup>T;-q=1"
      and "-q\<^sup>T;p=1"
      and "-(p\<^sup>T;-q)=0"
      and "-(-q\<^sup>T;p)=0"
proof -
  have "p \<le> -q"
    by (metis assms compl_le_swap1 inf.absorb1 inf.absorb2 point_def point_in_vector_or_complement)
  thus 1: "p\<^sup>T;-q=1"
    using assms(1) by (metis is_vector_def point_def ss423conv top_le)
  thus 2: "-q\<^sup>T;p=1"
    using conv_compl conv_one by force
  from 1 show "-(p\<^sup>T;-q)=0"
    by simp
  from 2 show "-(-q\<^sup>T;p)=0"
    by simp
qed

text \<open>Some (more) results about singletons\<close>

lemma singleton_pq:
  assumes "point p"
      and "point q"
    shows "singleton (p;q\<^sup>T)"
using assms comp_assoc point_def point_equations(1,3) point_is_point by fastforce

lemma singleton_equal_aux:
  assumes "singleton p"
      and "singleton q"
      and "q\<le>p"
    shows "p \<le> q;1"
proof -
  have pLp: "p;1;p\<^sup>T \<le>1'"
    by (simp add: assms(1) maddux_21 ss423conv)

  have "p = 1;(q\<^sup>T;q;1) \<cdot> p"
    using tarski
    by (metis assms(2) annir singleton_injective inf.commute inf_top.right_neutral inj_triple
              mult_assoc surj_one)
  also have "... \<le> (1 \<cdot> p;(q\<^sup>T;q;1)\<^sup>T);(q\<^sup>T;q;1 \<cdot> 1;p)"
    using dedekind by (metis conv_one)
  also have "... \<le> p;1;q\<^sup>T;q;q\<^sup>T;q;1"
    by (simp add: comp_assoc mult_isol)
  also have "... \<le> p;1;p\<^sup>T;q;q\<^sup>T;q;1"
    using assms(3) by (metis comp_assoc conv_iso mult_double_iso)
  also have "... \<le> 1';q;q\<^sup>T;q;1"
    using pLp using mult_isor by blast
  also have "... \<le> q;1"
    using assms(2) singleton_singletonT by (simp add: comp_assoc mult_isol)
  finally show ?thesis .
qed

lemma singleton_equal:
 assumes "singleton p"
     and "singleton q"
     and "q\<le>p"
   shows "q=p"
proof -
  have p1: "p \<le> q;1"
    using assms by (rule singleton_equal_aux)
  have "p\<^sup>T \<le> q\<^sup>T;1"
    using assms singleton_equal_aux singleton_transp conv_iso by fastforce
  hence p2: "p \<le> 1;q"
    using conv_iso by force

  have "p \<le> q;1 \<cdot> 1;q"
    using p1 p2 inf.boundedI by blast
  also have "... \<le> (q \<cdot> 1;q;1);(1 \<cdot> q\<^sup>T;1;q)"
    using dedekind by (metis comp_assoc conv_one)
  also have "... \<le> q;q\<^sup>T;1;q"
    by (simp add: mult_isor comp_assoc)
  also have "... \<le> q;1'"
    by (metis assms(2) conv_contrav conv_invol conv_one is_inj_def mult_assoc mult_isol
              one_idem_mult)
  also have "... \<le> q"
    by simp
  finally have "p \<le> q" .
  thus "q=p"
  using assms(3) by simp
qed

lemma singleton_nonsplit:
  assumes "singleton p"
      and "x\<le>p"
    shows "x=0 \<or> x=p"
proof (cases "x=0")
  assume "x=0"
  thus ?thesis ..
next
  assume 1: "x\<noteq>0"
  have "singleton x"
  proof (safe)
    show "is_inj (x;1)"
      using assms injective_down_closed mult_isor by blast
    show "is_inj (x\<^sup>T;1)"
      using assms conv_iso injective_down_closed mult_isol_var by blast
    show "is_sur (x;1)"
      using 1 comp_assoc sur_def_var1 tarski by fastforce
    thus "is_sur (x\<^sup>T;1)"
      by (metis conv_contrav conv_one mult.semigroup_axioms sur_def_var1 semigroup.assoc)
  qed
  thus ?thesis
    using assms singleton_equal by blast
qed

lemma singleton_nonzero:
  assumes "singleton p"
    shows "p\<noteq>0"
proof
  assume "p = 0"
  hence "point 0"
    using assms singleton_is_point by fastforce
  thus False
    by (simp add: is_point_def point_is_point)
qed

lemma singleton_sum:
  assumes "singleton p"
    shows "p \<le> x+y \<longleftrightarrow> (p\<le>x \<or> p\<le>y)"
proof
  show "p \<le> x + y \<Longrightarrow> p \<le> x \<or> p \<le> y"
  proof -
    assume as: "p \<le> x + y"
    show "p \<le> x \<or> p \<le> y"
    proof (cases "p\<le>x")
      assume "p\<le>x"
      thus ?thesis ..
    next
      assume a:"\<not>(p\<le>x)"
      hence "p\<cdot>x \<noteq> p"
        using a inf.orderI by fastforce
      hence "p \<le> -x"
        using assms singleton_nonsplit galois_aux inf_le1 by blast
      hence "p\<le>y"
        using as by (metis galois_1 inf.orderE)
      thus ?thesis
        by simp
    qed
  qed
next
  show "p \<le> x \<or> p \<le> y \<Longrightarrow> p \<le> x + y"
    using sup.coboundedI1 sup.coboundedI2 by blast
qed

lemma singleton_iff:
 "singleton x \<longleftrightarrow> x \<noteq> 0 \<and> x\<^sup>T;1;x + x;1;x\<^sup>T \<le> 1'"
by (smt comp_assoc conv_contrav conv_invol conv_one is_inj_def le_sup_iff one_idem_mult
        sur_def_var1 tarski)

lemma singleton_not_atom_in_relation_algebra_tarski:
 assumes "p\<noteq>0"
     and "\<forall>x . x\<le>p \<longrightarrow> x=0 \<or> x=p"
   shows "singleton p"
nitpick [expect=genuine] oops

end (* relation_algebra_tarski *)

subsection \<open>Relation algebras satisfying the point axiom\<close>

class relation_algebra_point = relation_algebra +
  assumes point_axiom: "x \<noteq> 0 \<longrightarrow> (\<exists>y z . point y \<and> point z \<and> y;z\<^sup>T \<le> x)"
begin

text \<open>Some (more) results about points\<close>

lemma point_exists:
  "\<exists>x . point x"
by (metis (full_types) eq_iff is_inj_def is_sur_def is_vector_def point_axiom point_def)

lemma point_below_vector:
  assumes "is_vector v"
      and "v \<noteq> 0"
    shows "\<exists>x . point x \<and> x \<le> v"
proof -
  from assms(2) obtain y and z where 1: "point y \<and> point z \<and> y;z\<^sup>T \<le> v"
    using point_axiom by blast
  have "z\<^sup>T;1 = (1;z)\<^sup>T"
    using conv_contrav conv_one by simp
  hence "y;(1;z)\<^sup>T \<le> v"
    using 1 by (metis assms(1) comp_assoc is_vector_def mult_isor)
  thus ?thesis
    using 1 by (metis conv_one is_vector_def point_def sur_def_var1)
qed

end (* relation_algebra_point *)

class relation_algebra_tarski_point = relation_algebra_tarski + relation_algebra_point
begin

lemma atom_is_singleton:
  assumes "p\<noteq>0"
      and "\<forall>x . x\<le>p \<longrightarrow> x=0 \<or> x=p"
    shows "singleton p"
by (metis assms singleton_nonzero singleton_pq point_axiom)

lemma singleton_iff_atom:
  "singleton p \<longleftrightarrow> p\<noteq>0 \<and> (\<forall>x . x\<le>p \<longrightarrow> x=0 \<or> x=p)"
using singleton_nonsplit singleton_nonzero atom_is_singleton by blast

lemma maddux_tarski:
  assumes "x\<noteq>0"
  shows "\<exists>y . y\<noteq>0 \<and> y\<le>x \<and> is_p_fun y"
proof -
  obtain p q where 1: "point p \<and> point q \<and> p;q\<^sup>T \<le> x"
    using assms point_axiom by blast
  hence 2: "p;q\<^sup>T\<noteq>0"
    by (simp add: singleton_nonzero singleton_pq)
  have "is_p_fun (p;q\<^sup>T)"
    using 1 by (meson singleton_singletonT singleton_pq singleton_transp is_inj_def p_fun_inj)
  thus ?thesis
    using 1 2 by force
qed

text \<open>Intermediate Point Theorem \cite[Proposition 2.4.8]{SchmidtStroehlein1993}\<close>

lemma intermediate_point_theorem:
  assumes "point p"
      and "point r"
    shows "p \<le> x;y;r \<longleftrightarrow> (\<exists>q . point q \<and> p \<le> x;q \<and> q \<le> y;r)"
proof
  assume 1: "p \<le> x;y;r"
  let ?v = "x\<^sup>T;p \<cdot> y;r"
  have 2: "is_vector ?v"
    using assms comp_assoc is_vector_def point_def vector_mult by fastforce
  have "?v \<noteq> 0"
    using 1 by (metis assms(1) inf.absorb2 is_point_def maddux_141 point_is_point mult.assoc)
  hence "\<exists>q . point q \<and> q \<le> ?v"
    using 2 point_below_vector by blast
  thus "\<exists>q . point q \<and> p \<le> x;q \<and> q \<le> y;r"
    using assms(1) point_swap by auto
next
  assume "\<exists>q . point q \<and> p \<le> x;q \<and> q \<le> y;r"
  thus "p \<le> x;y;r"
    using comp_assoc mult_isol order_trans by fastforce
qed

end (* relation_algebra_tarski_point *)

(*
The following shows that rtc can be defined with only 2 axioms.
This should eventually go into AFP/Relation_Algebra_RTC.relation_algebra_rtc.
There the class definition should be replaced with:

class relation_algebra_rtc = relation_algebra + star_op +
  assumes rtc_unfoldl: "1' + x ; x\<^sup>\<star> \<le> x\<^sup>\<star>"
      and rtc_inductl: "z + x ; y \<le> y \<longrightarrow> x\<^sup>\<star> ; z \<le> y"

and the following lemmas:
*)

context relation_algebra
begin

lemma unfoldl_inductl_implies_unfoldr:
  assumes "\<And>x. 1' + x;(rtc x) \<le> rtc x"
      and "\<And>x y z. x+y;z \<le> z \<Longrightarrow> rtc(y);x \<le> z"
    shows "1' + rtc(x);x \<le> rtc x"
by (metis assms le_sup_iff mult_oner order.trans subdistl_eq sup_absorb2 sup_ge1)

lemma star_transpose_swap:
  assumes "\<And>x. 1' + x;(rtc x) \<le> rtc x"
      and "\<And>x y z. x+y;z \<le> z \<Longrightarrow> rtc(y);x \<le> z"
    shows "rtc(x\<^sup>T) = (rtc x)\<^sup>T"
apply(simp only: eq_iff; rule conjI)
  apply (metis assms conv_add conv_contrav conv_e conv_iso mult_1_right
             unfoldl_inductl_implies_unfoldr )
by (metis assms conv_add conv_contrav conv_e conv_invol conv_iso mult_1_right
          unfoldl_inductl_implies_unfoldr)

lemma unfoldl_inductl_implies_inductr:
  assumes "\<And>x. 1' + x;(rtc x) \<le> rtc x"
      and "\<And>x y z. x+y;z \<le> z \<Longrightarrow> rtc(y);x \<le> z"
    shows "x+z;y \<le> z \<Longrightarrow> x;rtc(y) \<le> z"
by (metis assms conv_add conv_contrav conv_iso star_transpose_swap)

end (* relation_algebra *)

context relation_algebra_rtc
begin

abbreviation tc ("(_\<^sup>+)" [101] 100) where "tc x \<equiv> x;x\<^sup>\<star>"

abbreviation is_acyclic
  where "is_acyclic x \<equiv> x\<^sup>+ \<le> -1'"

text \<open>General theorems\<close>

lemma star_denest_10:
  assumes "x;y=0"
    shows "(x+y)\<^sup>\<star> = y;y\<^sup>\<star>;x\<^sup>\<star>+x\<^sup>\<star>"
using assms bubble_sort sup.commute by auto

lemma star_star_plus:
  "x\<^sup>\<star> + y\<^sup>\<star> = x\<^sup>+ + y\<^sup>\<star>"
by (metis (full_types) sup.left_commute star_plus_one star_unfoldl_eq sup.commute)

text \<open>The following two lemmas are from \cite{Guttmann2018b}.\<close>

lemma cancel_separate:
  assumes "x ; y \<le> 1'"
  shows "x\<^sup>\<star> ; y\<^sup>\<star> \<le> x\<^sup>\<star> + y\<^sup>\<star>"
proof -
  have "x ; y\<^sup>\<star> = x + x ; y ; y\<^sup>\<star>"
    by (metis comp_assoc conway.dagger_unfoldl_distr distrib_left mult_oner)
  also have "... \<le> x + y\<^sup>\<star>"
    by (metis assms join_isol star_invol star_plus_one star_subdist_var_2 sup.absorb2 sup.assoc)
  also have "... \<le> x\<^sup>\<star> + y\<^sup>\<star>"
    using join_iso by fastforce
  finally have "x ; (x\<^sup>\<star> + y\<^sup>\<star>) \<le> x\<^sup>\<star> + y\<^sup>\<star>"
    by (simp add: distrib_left le_supI1)
  thus ?thesis
    by (simp add: rtc_inductl)
qed

lemma cancel_separate_inj_converse:
  assumes "is_inj x"
    shows "x\<^sup>\<star> ; x\<^sup>T\<^sup>\<star> = x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
 apply (rule antisym)
  using assms cancel_separate is_inj_def apply blast
by (metis conway.dagger_unfoldl_distr le_supI mult_1_right mult_isol sup.cobounded1)

lemma cancel_separate_p_fun_converse:
  assumes "is_p_fun x"
    shows "x\<^sup>T\<^sup>\<star> ; x\<^sup>\<star> = x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
using sup_commute assms cancel_separate_inj_converse p_fun_inj by fastforce

lemma cancel_separate_converse_idempotent:
  assumes "is_inj x"
      and "is_p_fun x"
    shows "(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>);(x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>) = x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
by (metis assms cancel_separate cancel_separate_p_fun_converse church_rosser_equiv is_inj_def
          star_denest_var_6)

lemma triple_star:
  assumes "is_inj x"
      and "is_p_fun x"
    shows "x\<^sup>\<star>;x\<^sup>T\<^sup>\<star>;x\<^sup>\<star> = x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
by (simp add: assms cancel_separate_inj_converse cancel_separate_p_fun_converse)

lemma inj_xxts:
  assumes "is_inj x"
    shows "x;x\<^sup>T\<^sup>\<star> \<le> x\<^sup>\<star> + x\<^sup>T\<^sup>\<star>"
by (metis assms cancel_separate_inj_converse distrib_right less_eq_def star_ext)

lemma plus_top:
  "x\<^sup>+;1 = x;1"
by (metis comp_assoc conway.dagger_unfoldr_distr sup_top_left)

lemma top_plus:
  "1;x\<^sup>+ = 1;x"
by (metis comp_assoc conway.dagger_unfoldr_distr star_denest_var_2 star_ext star_slide_var
           sup_top_left top_unique)

lemma plus_conv:
  "(x\<^sup>+)\<^sup>T = x\<^sup>T\<^sup>+"
by (simp add: star_conv star_slide_var)

lemma inj_implies_step_forwards_backwards:
  assumes "is_inj x"
    shows "x\<^sup>\<star>;(x\<^sup>+\<cdot>1');1 \<le> x\<^sup>T;1"
proof -
  have "(x\<^sup>+\<cdot>1');1 \<le> (x\<^sup>\<star>\<cdot>x\<^sup>T);(x\<cdot>(x\<^sup>\<star>)\<^sup>T);1"
    by (metis conv_contrav conv_e dedekind mult_1_right mult_isor star_slide_var)
  also have "... \<le> (x\<^sup>\<star>\<cdot>x\<^sup>T);1"
    by (simp add: comp_assoc mult_isol)
  finally have 1: "(x\<^sup>+\<cdot>1');1 \<le> (x\<^sup>\<star>\<cdot>x\<^sup>T);1" .

  have "x;(x\<^sup>\<star>\<cdot>x\<^sup>T);1 \<le> (x\<^sup>+\<cdot>x;x\<^sup>T);1"
    by (metis inf_idem meet_interchange mult_isor)
  also have "... \<le> (x\<^sup>+\<cdot>1');1"
    using assms is_inj_def meet_isor mult_isor by fastforce
  finally have "x;(x\<^sup>\<star>\<cdot>x\<^sup>T);1 \<le> (x\<^sup>\<star>\<cdot>x\<^sup>T);1"
    using 1 by fastforce
  hence "x\<^sup>\<star>;(x\<^sup>+\<cdot>1');1 \<le> (x\<^sup>\<star>\<cdot>x\<^sup>T);1"
    using 1 by (simp add: comp_assoc rtc_inductl)
  thus "x\<^sup>\<star>;(x\<^sup>+\<cdot>1');1 \<le> x\<^sup>T;1"
    using inf.cobounded2 mult_isor order_trans by blast
qed

text \<open>Acyclic relations\<close>

text \<open>The following result is from \cite{Guttmann2017c}.\<close>

lemma acyclic_inv:
  assumes "is_acyclic t"
      and "is_vector v"
      and "e \<le> v;-v\<^sup>T"
      and "t \<le> v;v\<^sup>T"
    shows "is_acyclic (t + e)"
proof -
  have "t\<^sup>+;e \<le> t\<^sup>+;v;-v\<^sup>T"
    by (simp add: assms(3) mult_assoc mult_isol)
  also have "... \<le> v;v\<^sup>T;t\<^sup>\<star>;v;-v\<^sup>T"
    by (simp add: assms(4) mult_isor)
  also have "... \<le> v;-v\<^sup>T"
    by (metis assms(2) mult_double_iso top_greatest is_vector_def mult_assoc)
  also have "... \<le> -1'"
    by (simp add: conv_galois_1)
  finally have 1: "t\<^sup>+;e \<le> -1'" .
  have "e \<le> v;-v\<^sup>T"
    using assms(3) by simp
  also have "... \<le> -1'"
    by (simp add: conv_galois_1)
  finally have 2: "t\<^sup>+;e + e \<le> -1'"
    using 1 by simp
  have 3: "e;t\<^sup>\<star> = e"
    by (metis assms(2-4) et(1) independence2)
  have 4: "e\<^sup>\<star> = 1' + e"
    using assms(2-3) ee boffa_var bot_least by blast
  have "(t + e)\<^sup>+ = (t + e);t\<^sup>\<star>;(e;t\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: comp_assoc)
  also have "... = (t + e);t\<^sup>\<star>;(1' + e)"
    using 3 4 by simp
  also have "... = t\<^sup>+;(1' + e) + e;t\<^sup>\<star>;(1' + e)"
    by simp
  also have "... = t\<^sup>+;(1' + e) + e;(1' + e)"
    using 3 by simp
  also have "... = t\<^sup>+;(1' + e) + e"
    using 4 assms(2-3) ee independence2 by fastforce
  also have "... = t\<^sup>+ + t\<^sup>+;e + e"
    by (simp add: distrib_left)
  also have "... \<le> -1'"
    using assms(1) 2 by simp
  finally show ?thesis .
qed

lemma acyclic_single_step:
  assumes "is_acyclic x"
    shows "x \<le> -1'"
by (metis assms dual_order.trans mult_isol mult_oner star_ref)

lemma acyclic_reachable_points:
  assumes "is_point p"
      and "is_point q"
      and "p \<le> x;q"
      and "is_acyclic x"
    shows "p\<noteq>q"
proof
  assume "p=q"
  hence "p \<le> x;q \<cdot> q"
    by (simp add: assms(3) eq_iff inf.absorb2)
  also have "... = (x \<cdot> 1');q"
    using assms(2) inj_distr is_point_def by simp
  also have "... \<le> (-1' \<cdot> 1');q"
    using acyclic_single_step assms(4) by (metis abel_semigroup.commute inf.abel_semigroup_axioms
          meet_isor mult_isor)
 also have "... = 0"
  by simp
 finally have "p \<le> 0" .
 thus False
  using assms(1) bot_unique is_point_def by blast
qed

lemma acyclic_trans:
 assumes "is_acyclic x"
   shows "x \<le> -(x\<^sup>T\<^sup>+)"
proof -
 have "\<exists>c\<ge>x. c \<le> - (x\<^sup>+)\<^sup>T"
  by (metis assms compl_mono conv_galois_2 conv_iso double_compl mult_onel star_1l)
 thus ?thesis
  by (metis dual_order.trans plus_conv)
qed

lemma acyclic_trans':
 assumes "is_acyclic x"
   shows "x\<^sup>\<star> \<le> -(x\<^sup>T\<^sup>+)"
proof -
 have "x\<^sup>\<star> \<le> - (- (- (x\<^sup>T ; - (- 1'))) ; (x\<^sup>\<star>)\<^sup>T)"
  by (metis assms conv_galois_1 conv_galois_2 order_trans star_trans)
 then show ?thesis
  by (simp add: star_conv)
qed

text \<open>Regressively finite\<close>

lemma regressively_finite_acyclic:
  assumes "regressively_finite x"
    shows "is_acyclic x"
proof -
  have 1: "is_vector ((x\<^sup>+ \<cdot> 1');1)"
    by (simp add: is_vector_def mult_assoc)
  have "(x\<^sup>+ \<cdot> 1');1 = (x\<^sup>T\<^sup>+ \<cdot> 1');1"
    by (metis plus_conv test_converse)
  also have "... \<le> x\<^sup>T;(1';x\<^sup>T\<^sup>\<star> \<cdot> x);1"
    by (metis conv_invol modular_1_var mult_isor mult_oner mult_onel)
  also have "... \<le> x\<^sup>T;(1' \<cdot> x\<^sup>+);x\<^sup>T\<^sup>\<star>;1"
    by (metis comp_assoc conv_invol modular_2_var mult_isol mult_isor star_conv)
  also have "... = x\<^sup>T;(x\<^sup>+ \<cdot> 1');1"
    by (metis comp_assoc conway.dagger_unfoldr_distr inf.commute sup.cobounded1 top_le)
  finally have "(x\<^sup>+ \<cdot> 1');1 = 0"
    using 1 assms by (simp add: comp_assoc)
  thus ?thesis
    by (simp add: galois_aux ss_p18)
qed

notation power (infixr "\<up>" 80)

lemma power_suc_below_plus:
  "x \<up> Suc n \<le> x\<^sup>+"
  apply (induct n)
 using mult_isol star_ref apply fastforce
by (simp add: mult_isol_var order_trans)

end (* relation_algebra_rtc *)

class relation_algebra_rtc_tarski = relation_algebra_rtc + relation_algebra_tarski
begin

lemma point_loop_not_acyclic:
  assumes "is_point p"
      and "p \<le> x \<up> Suc n ; p"
    shows "\<not> is_acyclic x"
proof -
  have "p \<le> x\<^sup>+ ; p"
    by (meson assms dual_order.trans point_def point_is_point ss423bij power_suc_below_plus)
  hence "p ; p\<^sup>T \<le> x\<^sup>+"
    using assms(1) point_def point_is_point ss423bij by blast
  thus ?thesis
    using assms(1) order.trans point_not_equal(1) point_not_equal(2) by blast
qed

end

class relation_algebra_rtc_point = relation_algebra_rtc + relation_algebra_point

class relation_algebra_rtc_tarski_point = relation_algebra_rtc_tarski + relation_algebra_rtc_point +
                                          relation_algebra_tarski_point

text \<open>
Finite graphs: the axiom says the algebra has finitely many elements.
This means the relations have a finite base set.
\<close>

class relation_algebra_rtc_tarski_point_finite = relation_algebra_rtc_tarski_point + finite
begin

text \<open>For a finite acyclic relation, the powers eventually vanish.\<close>

lemma acyclic_power_vanishes:
  assumes "is_acyclic x"
    shows "\<exists>n . x \<up> Suc n = 0"
proof -
  let ?n = "card { p . is_point p }"
  let ?p = "x \<up> ?n"
  have "?p = 0"
  proof (rule ccontr)
    assume "?p \<noteq> 0"
    from this obtain p q where 1: "point p \<and> point q \<and> p;q\<^sup>T \<le> ?p"
      using point_axiom by blast
    hence 2: "p \<le> ?p;q"
      using point_def ss423bij by blast
    have "\<forall>n\<le>?n . (\<exists>f. \<forall>i\<le>n . is_point (f i) \<and> (\<forall>j\<le>i . p \<le> x\<up>(?n-i) ; f i \<and> f i \<le> x\<up>(i-j) ; f j))"
    proof
      fix n
      show "n\<le>?n \<longrightarrow> (\<exists>f. \<forall>i\<le>n . is_point (f i) \<and> (\<forall>j\<le>i . p \<le> x\<up>(?n-i) ; f i \<and> f i \<le> x\<up>(i-j) ; f j))"
      proof (induct n)
        case 0
        thus ?case
          using 1 2 point_is_point by fastforce
      next
        case (Suc n)
        fix n
        assume 3: "n\<le>?n \<longrightarrow> (\<exists>f . \<forall>i\<le>n . is_point (f i) \<and> (\<forall>j\<le>i . p \<le> x \<up> (?n-i) ; f i \<and> f i \<le> x \<up> (i-j) ; f j))"
        show "Suc n\<le>?n \<longrightarrow> (\<exists>f . \<forall>i\<le>Suc n . is_point (f i) \<and> (\<forall>j\<le>i . p \<le> x \<up> (?n-i) ; f i \<and> f i \<le> x \<up> (i-j) ; f j))"
        proof
          assume 4: "Suc n\<le>?n"
          from this obtain f where 5: "\<forall>i\<le>n . is_point (f i) \<and> (\<forall>j\<le>i . p \<le> x \<up> (?n-i) ; f i \<and> f i \<le> x \<up> (i-j) ; f j)"
            using 3 by auto
          have "p \<le> x \<up> (?n-n) ; f n"
            using 5 by blast
          also have "... = x \<up> (?n-n-one_class.one) ; x ; f n"
            using 4 by (metis (no_types) Suc_diff_le diff_Suc_1 diff_Suc_Suc power_Suc2)
          finally obtain r where 6: "point r \<and> p \<le> x \<up> (?n-Suc n) ; r \<and> r \<le> x ; f n"
            using 1 5 intermediate_point_theorem point_is_point by fastforce
          let ?g = "\<lambda>m . if m = Suc n then r else f m"
          have "\<forall>i\<le>Suc n . is_point (?g i) \<and> (\<forall>j\<le>i . p \<le> x \<up> (?n-i) ; ?g i \<and> ?g i \<le> x \<up> (i-j) ; ?g j)"
          proof
            fix i
            show "i\<le>Suc n \<longrightarrow> is_point (?g i) \<and> (\<forall>j\<le>i . p \<le> x \<up> (?n-i) ; ?g i \<and> ?g i \<le> x \<up> (i-j) ; ?g j)"
            proof (cases "i\<le>n")
              case True
              thus ?thesis
                using 5 by simp
            next
              case False
              have "is_point (?g (Suc n)) \<and> (\<forall>j\<le>Suc n . p \<le> x \<up> (?n-Suc n) ; ?g (Suc n) \<and> ?g (Suc n) \<le> x \<up> (Suc n-j) ; ?g j)"
              proof
                show "is_point (?g (Suc n))"
                  using 6 point_is_point by fastforce
              next
                show "\<forall>j\<le>Suc n . p \<le> x \<up> (?n-Suc n) ; ?g (Suc n) \<and> ?g (Suc n) \<le> x \<up> (Suc n-j) ; ?g j"
                proof
                  fix j
                  show "j\<le>Suc n \<longrightarrow> p \<le> x \<up> (?n-Suc n) ; ?g (Suc n) \<and> ?g (Suc n) \<le> x \<up> (Suc n-j) ; ?g j"
                  proof
                    assume 7: "j\<le>Suc n"
                    show "p \<le> x \<up> (?n-Suc n) ; ?g (Suc n) \<and> ?g (Suc n) \<le> x \<up> (Suc n-j) ; ?g j"
                    proof
                      show "p \<le> x \<up> (?n-Suc n) ; ?g (Suc n)"
                        using 6 by simp
                    next
                      show "?g (Suc n) \<le> x \<up> (Suc n-j) ; ?g j"
                      proof (cases "j = Suc n")
                        case True
                        thus ?thesis
                          by simp
                      next
                        case False
                        hence "f n \<le> x \<up> (n-j) ; f j"
                          using 5 7 by fastforce
                        hence "x ; f n \<le> x \<up> (Suc n-j) ; f j"
                          using 7 False Suc_diff_le comp_assoc mult_isol by fastforce
                        thus ?thesis
                          using 6 False by fastforce
                      qed
                    qed
                  qed
                qed
              qed
              thus ?thesis
                by (simp add: False le_Suc_eq)
            qed
          qed
          thus "\<exists>f . \<forall>i\<le>Suc n . is_point (f i) \<and> (\<forall>j\<le>i . p \<le> x \<up> (?n-i) ; f i \<and> f i \<le> x \<up> (i-j) ; f j)"
            by auto
        qed
      qed
    qed
    from this obtain f where 8: "\<forall>i\<le>?n . is_point (f i) \<and> (\<forall>j\<le>i . p \<le> x \<up> (?n-i) ; f i \<and> f i \<le> x \<up> (i-j) ; f j)"
      by fastforce
    let ?A = "{ k . k\<le>?n }"
    have "f ` ?A \<subseteq> { p . is_point p }"
      using 8 by blast
    hence "card (f ` ?A) \<le> ?n"
      by (simp add: card_mono)
    hence "\<not> inj_on f ?A"
      by (simp add: pigeonhole)
    from this obtain i j where 9: "i \<le> ?n \<and> j \<le> ?n \<and> i \<noteq> j \<and> f i = f j"
      by (metis (no_types, lifting) inj_on_def mem_Collect_eq)
    show False
      apply (cases "i < j")
     using 8 9 apply (metis Suc_diff_le Suc_leI assms diff_Suc_Suc order_less_imp_le
                            point_loop_not_acyclic)
    using 8 9 by (metis assms neqE point_loop_not_acyclic Suc_diff_le Suc_leI assms diff_Suc_Suc
                        order_less_imp_le)
    qed
    thus ?thesis
      by (metis annir power.simps(2))
qed

text \<open>Hence finite acyclic relations are regressively finite.\<close>

lemma acyclic_regressively_finite:
  assumes "is_acyclic x"
    shows "regressively_finite x"
proof
  have "is_acyclic (x\<^sup>T)"
    using assms acyclic_trans' compl_le_swap1 order_trans star_ref by blast
  from this obtain n where 1: "x\<^sup>T \<up> Suc n = 0"
    using acyclic_power_vanishes by fastforce
  fix v
  show "is_vector v \<and> v \<le> x\<^sup>T;v \<longrightarrow> v = 0"
  proof
    assume 2: "is_vector v \<and> v \<le> x\<^sup>T;v"
    have "v \<le> x\<^sup>T \<up> Suc n ; v"
    proof (induct n)
      case 0
      thus ?case
        using 2 by simp
    next
      case (Suc n)
      hence "x\<^sup>T ; v \<le> x\<^sup>T \<up> Suc (Suc n) ; v"
        by (simp add: comp_assoc mult_isol)
      thus ?case
        using 2 dual_order.trans by blast
    qed
    thus "v = 0"
      using 1 by (simp add: le_bot)
  qed
 qed

lemma acyclic_is_regressively_finite:
  "is_acyclic x \<longleftrightarrow> regressively_finite x"
using acyclic_regressively_finite regressively_finite_acyclic by blast

end (* end relation_algebra_rtc_tarski_point_finite *)

end
