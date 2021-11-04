(*  Title:      Schutz_Spacetime/TemporalOrderOnPath.thy
    Authors:    Richard Schmoetten, Jake Palmer and Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)
theory TemporalOrderOnPath
imports Main Minkowski TernaryOrdering
begin

text \<open>
  In Schutz \cite[pp.~18-30]{schutz1997}, this is ``Chapter 3: Temporal order on a path''.
  All theorems are from Schutz, all lemmas are either parts of the Schutz proofs extracted, or
  additional lemmas which needed to be added, with the exception of the three transitivity lemmas
  leading to Theorem 9, which are given by Schutz as well.
  Much of what we'd like to prove about chains with respect to injectivity, surjectivity,
  bijectivity, is proved in \<open>TernaryOrdering.thy\<close>.
  Some more things are proved in interlude sections.
\<close>

text \<open>Disable list syntax.\<close>
no_translations
  "[x, xs]" == "x#[xs]"
  "[x]" == "x#[]"
no_syntax
  \<comment> \<open>list Enumeration\<close>
  "_list" :: "args => 'a list" ("[(_)]")
no_notation Cons (infixr "#" 65)
no_notation Nil ("[]")


section "Preliminary Results for Primitives"
text \<open>
  First some proofs that belong in this section but aren't proved in the book or are covered but
  in a different form or off-handed remark.
\<close>

context MinkowskiPrimitive begin

lemma three_in_set3:
  assumes "card X \<ge> 3"
  obtains x y z where "x\<in>X" and "y\<in>X" and "z\<in>X" and "x\<noteq>y" and "x\<noteq>z" and "y\<noteq>z"
  using assms by (auto simp add: card_le_Suc_iff numeral_3_eq_3)

lemma paths_cross_once:
  assumes path_Q: "Q \<in> \<P>"
      and path_R: "R \<in> \<P>"
      and Q_neq_R: "Q \<noteq> R"
      and QR_nonempty: "Q\<inter>R \<noteq> {}"
  shows "\<exists>!a\<in>\<E>. Q\<inter>R = {a}"
proof -
  have ab_inQR: "\<exists>a\<in>\<E>. a\<in>Q\<inter>R" using QR_nonempty in_path_event path_Q by auto
  then obtain a where a_event: "a \<in> \<E>" and a_inQR: "a \<in> Q\<inter>R" by auto
  have "Q\<inter>R = {a}"
  proof (rule ccontr)
    assume "Q\<inter>R \<noteq> {a}"
    then have "\<exists>b\<in>Q\<inter>R. b \<noteq> a" using a_inQR by blast
    then have "Q = R" using eq_paths a_inQR path_Q path_R by auto
    thus False using Q_neq_R by simp
  qed
  thus ?thesis using a_event by blast
qed

lemma cross_once_notin:
  assumes "Q \<in> \<P>"
      and "R \<in> \<P>"
      and "a \<in> Q"
      and "b \<in> Q"
      and "b \<in> R"
      and "a \<noteq> b"
      and "Q \<noteq> R"
  shows "a \<notin> R"
using assms paths_cross_once eq_paths by meson

lemma paths_cross_at:
  assumes path_Q: "Q \<in> \<P>" and path_R: "R \<in> \<P>"
      and Q_neq_R: "Q \<noteq> R"
      and QR_nonempty: "Q \<inter> R \<noteq> {}"
      and x_inQ: "x \<in> Q" and x_inR: "x \<in> R"
  shows "Q \<inter> R = {x}"
proof (rule equalityI)
  show "Q \<inter> R \<subseteq> {x}"
  proof (rule subsetI, rule ccontr)
    fix y
    assume y_in_QR: "y \<in> Q \<inter> R"
       and y_not_in_just_x: "y \<notin> {x}"
    then have y_neq_x: "y \<noteq> x" by simp
    then have "\<not> (\<exists>z. Q \<inter> R = {z})"
        by (meson Q_neq_R path_Q path_R x_inQ x_inR y_in_QR cross_once_notin IntD1 IntD2)
    thus False using paths_cross_once by (meson QR_nonempty Q_neq_R path_Q path_R)
  qed
  show "{x} \<subseteq> Q \<inter> R" using x_inQ x_inR by simp
qed

lemma events_distinct_paths:
  assumes a_event: "a \<in> \<E>"
      and b_event: "b \<in> \<E>"
      and a_neq_b: "a \<noteq> b"
  shows "\<exists>R\<in>\<P>. \<exists>S\<in>\<P>. a \<in> R \<and> b \<in> S \<and> (R \<noteq> S \<longrightarrow> (\<exists>!c\<in>\<E>. R \<inter> S = {c}))"
  by (metis events_paths assms paths_cross_once)

end (* context MinkowskiPrimitive *)
context MinkowskiBetweenness begin

lemma assumes "[[a b c]]" shows "\<exists>f. long_ch_by_ord f {a,b,c}"
  using abc_abc_neq ord_ordered long_ch_by_ord_def assms
  by (smt insertI1 insert_commute)

lemma between_chain: "[[a b c]] \<Longrightarrow> ch {a,b,c}"
proof -
  assume "[[a b c]]"
  hence "\<exists>f. ordering f betw {a,b,c}"
    by (simp add: abc_abc_neq ord_ordered)
  hence "\<exists>f. long_ch_by_ord f {a,b,c}"
    using \<open>[[a b c]]\<close> abc_abc_neq long_ch_by_ord_def by auto
  thus ?thesis
    by (simp add: ch_by_ord_def ch_def)
qed

lemma overlap_chain: "\<lbrakk>[[a b c]]; [[b c d]]\<rbrakk> \<Longrightarrow> ch {a,b,c,d}"
proof -
  assume "[[a b c]]" and "[[b c d]]"
  have "\<exists>f. ordering f betw {a,b,c,d}"
    proof -
      have f1: "[[a b d]]"
        using \<open>[[a b c]]\<close> \<open>[[b c d]]\<close> by blast
      have "[[a c d]]"
        using \<open>[[a b c]]\<close> \<open>[[b c d]]\<close> abc_bcd_acd by blast
      then show ?thesis
        using f1 by (metis (no_types) \<open>[[a b c]]\<close> \<open>[[b c d]]\<close> abc_abc_neq overlap_ordering)
    qed
    hence "\<exists>f. long_ch_by_ord f {a,b,c,d}"
      using \<open>[[a b c]]\<close> abc_abc_neq long_ch_by_ord_def by auto
    thus ?thesis
      by (simp add: ch_by_ord_def ch_def)
  qed

end (* context MinkowskiBetweenness *)


section "3.1 Order on a finite chain"
context MinkowskiBetweenness begin

subsection \<open>Theorem 1\<close>
text \<open>
  See \<open>Minkowski.abc_only_cba\<close>.
  Proving it again here to show it can be done following the prose in Schutz.
\<close>
theorem theorem1 [no_atp]:
  assumes abc: "[[a b c]]"
  shows "[[c b a]] \<and> \<not> [[b c a]] \<and> \<not> [[c a b]]" 
proof -
  (* (i) *)
  have part_i: "[[c b a]]" using abc abc_sym by simp
  (* (ii) *)
  have part_ii: "\<not> [[b c a]]"
  proof (rule notI)
    assume "[[b c a]]"
    then have "[[a b a]]" using abc abc_bcd_abd by blast
    thus False using abc_ac_neq by blast
  qed
  (* (iii) *)
  have part_iii: "\<not> [[c a b]]"
  proof (rule notI)
    assume "[[c a b]]"
    then have "[[c a c]]" using abc abc_bcd_abd by blast
    thus False using abc_ac_neq by blast
  qed
  thus ?thesis using part_i part_ii part_iii by auto
qed

subsection \<open>Theorem 2\<close>
text \<open>
  The lemma \<open>abc_bcd_acd\<close>, equal to the start of Schutz's proof, is given in \<open>Minkowski\<close> in order
  to prove some equivalences.
  Splitting it up into the proof of:
    ``there is a betweenness relation for each ordered triple", and
    ``all events of a chain are distinct"
  The first part is obvious with total chains (using \<open>ordering\<close>), and will be proved using the
  local definition as well (\<open>ordering2\<close>), following Schutz' proof.
  The second part is proved as injectivity of the indexing function (see \<open>index_injective\<close>).
\<close>

text \<open>
  For the case of two-element chains: the elements are distinct by definition,
  and the statement on ordering is void (respectively, \<open>False \<Longrightarrow> P\<close> for any \<open>P\<close>).
\<close>

(* Theorem 2 for total chains *)
theorem order_finite_chain:
  assumes chX: "long_ch_by_ord f X"
      and finiteX: "finite X"
      and ordered_nats: "0 \<le> (i::nat) \<and> i < j \<and> j < l \<and> l < card X"
  shows "[[(f i) (f j) (f l)]]"
  by (metis chX long_ch_by_ord_def ordered_nats ordering_ord_ijk)

(* Theorem 2 (with helper lemmas for induction) for local chains *)
lemma thm2_ind1:
  assumes chX: "long_ch_by_ord2 f X"
      and finiteX: "finite X"
    shows "\<forall>j i. ((i::nat) < j \<and> j < card X - 1) \<longrightarrow> [[(f i) (f j) (f (j + 1))]]"
proof (rule allI)+
  let ?P = "\<lambda> i j. [[(f i) (f j) (f (j+1))]]"
  fix i j
  show "(i<j \<and> j<card X -1) \<longrightarrow> ?P i j"
  proof (induct j)
    case 0 (* this assumption is False, so easy *)
    show ?case by blast
  next
    case (Suc j)
    show ?case
    proof (clarify)
      assume asm: "i<Suc j" "Suc j<card X -1"
      have pj: "?P j (Suc j)" (* needs Suc Suc j < card X *)
        using asm(2) chX less_diff_conv long_ch_by_ord2_def ordering2_def
        by (metis Suc_eq_plus1)
      have "i<j \<or> i=j" using asm(1)
        by linarith
      thus "?P i (Suc j)"
      proof
        assume "i=j"
        hence "Suc i = Suc j \<and> Suc (Suc j) = Suc (Suc j)"
          by simp
        thus "?P i (Suc j)"
          using pj by auto
      next
        assume "i<j"
        have "j < card X - 1"
          using asm(2) by linarith
        thus "?P i (Suc j)"
          using \<open>i<j\<close> Suc.hyps asm(1) asm(2) chX finiteX Suc_eq_plus1 abc_bcd_acd pj
          by presburger 
      qed
    qed
  qed
qed

lemma thm2_ind2:
  assumes chX: "long_ch_by_ord2 f X"
      and finiteX: "finite X"
    shows "\<forall>m l. (0<(l-m) \<and> (l-m) < l \<and> l < card X) \<longrightarrow> [[(f ((l-m)-1)) (f (l-m)) (f l)]]"
proof (rule allI)+
  fix l m
  let ?P = "\<lambda> k l. [[(f (k-1)) (f k) (f l)]]"
  let ?n = "card X"
  let ?k = "(l::nat)-m"
  show "0 < ?k \<and> ?k < l \<and> l < ?n \<longrightarrow> ?P ?k l"
  proof (induct m)
    case 0 (* yet again, this assumption is False, so easy *)
    show ?case by simp
  next
    case (Suc m)
    show ?case
    proof (clarify)
      assume asm: "0 < l - Suc m" "l - Suc m < l" "l < ?n"
      have "Suc m = 1 \<or> Suc m > 1" by linarith
      thus "[[(f (l - Suc m - 1)) (f (l - Suc m)) (f l)]]" (is ?goal)
      proof
        assume "Suc m = 1"
        show ?goal
        proof -
          have "l - Suc m < card X"
            using asm(2) asm(3) less_trans by blast
          then show ?thesis
            using \<open>Suc m = 1\<close> asm finiteX thm2_ind1 chX
            using Suc_eq_plus1 add_diff_inverse_nat diff_Suc_less
                  gr_implies_not_zero less_one plus_1_eq_Suc
            by (smt long_ch_by_ord2_def ordering2_ord_ijk)
        qed
      next
        assume "Suc m > 1"
        show ?goal
          apply (rule_tac a="f l" and c="f(l - Suc m - 1)" in abc_sym)
          apply (rule_tac a="f l" and c="f(l-Suc m)" and d="f(l-Suc m-1)" and b="f(l-m)" in abc_bcd_acd)
        proof -
          have "[[(f(l-m-1)) (f(l-m)) (f l)]]"
            using Suc.hyps \<open>1 < Suc m\<close> asm(1,3) by force
          thus "[[(f l) (f(l - m)) (f(l - Suc m))]]"
            using abc_sym One_nat_def diff_zero minus_nat.simps(2)
            by metis
          have "Suc(l - Suc m - 1) = l - Suc m" "Suc(l - Suc m) = l-m"
            using Suc_pred asm(1) by presburger+
          hence "[[(f(l - Suc m - 1)) (f(l - Suc m)) (f(l - m))]]"
            using chX unfolding long_ch_by_ord2_def ordering2_def
            by (meson asm(3) less_imp_diff_less)
          thus "[[(f(l - m)) (f(l - Suc m)) (f(l - Suc m - 1))]]"
            using abc_sym by blast
        qed
      qed
    qed
  qed
qed

lemma thm2_ind2b:
  assumes chX: "long_ch_by_ord2 f X"
      and finiteX: "finite X"
      and ordered_nats: "0<k \<and> k<l \<and> l < card X"
    shows "[[(f (k-1)) (f k) (f l)]]"
  using thm2_ind2 finiteX chX ordered_nats
  by (metis diff_diff_cancel less_imp_le)


text \<open>
  This is Theorem 2 properly speaking, except for the "chain elements are distinct" part
  (which is proved as injectivity of the index later). Follows Schutz fairly well!
  The statement Schutz proves under (i) is given in \<open>MinkowskiBetweenness.abc_bcd_acd\<close> instead.
\<close>
theorem (*2*) order_finite_chain2:
  assumes chX: "long_ch_by_ord2 f X"
      and finiteX: "finite X"
      and ordered_nats: "0 \<le> (i::nat) \<and> i < j \<and> j < l \<and> l < card X"
    shows "[[(f i) (f j) (f l)]]"
proof -
  let ?n = "card X - 1"
  have ord1: "0\<le>i \<and> i<j \<and> j<?n"
    using ordered_nats by linarith
  have e2: "[[(f i) (f j) (f (j+1))]]" using thm2_ind1
    using Suc_eq_plus1 chX finiteX ord1
    by presburger
  have e3: "\<forall>k. 0<k \<and> k<l \<longrightarrow> [[(f (k-1)) (f k) (f l)]]"
    using thm2_ind2b chX finiteX ordered_nats
    by blast
  have "j<l-1 \<or> j=l-1"
    using ordered_nats by linarith
  thus ?thesis
  proof
    assume "j<l-1"
    have  "[[(f j) (f (j+1)) (f l)]]"
      using e3 abc_abc_neq ordered_nats
      using \<open>j < l - 1\<close> less_diff_conv by auto
    thus ?thesis
      using e2 abc_bcd_abd
      by blast
  next
    assume "j=l-1"
    thus ?thesis using e2
      using ordered_nats by auto
  qed
qed


lemma three_in_long_chain2:
  assumes "long_ch_by_ord2 f X"
  obtains x y z where "x\<in>X" and "y\<in>X" and "z\<in>X" and "x\<noteq>y" and "x\<noteq>z" and "y\<noteq>z"
  using assms(1) long_ch_by_ord2_def by auto


lemma short_ch_card_2:
  assumes "ch_by_ord f X"
  shows "short_ch X \<longleftrightarrow> card X = 2"
  by (metis assms card_2_iff' ch_by_ord_def long_ch_by_ord_def short_ch_def)


lemma long_chain2_card_geq:
  assumes "long_ch_by_ord2 f X" and fin: "finite X"
  shows "card X \<ge> 3"
proof -
  obtain x y z where xyz: "x\<in>X" "y\<in>X" "z\<in>X" and neq: "x\<noteq>y" "x\<noteq>z" "y\<noteq>z"
    using three_in_long_chain2 assms(1) by blast
  let ?S = "{x,y,z}"
  have "?S \<subseteq> X"
    by (simp add: xyz)
  moreover have "card ?S \<ge> 3"
    using antisym \<open>x \<noteq> y\<close> \<open>x \<noteq> z\<close> \<open>y \<noteq> z\<close> by auto
  ultimately show ?thesis
    by (meson neq fin three_subset)
qed


lemma fin_chain_card_geq_2:
  assumes "[f[a..b]X]"
  shows "card X \<ge> 2"
  using fin_chain_def apply (cases "short_ch X")
  using short_ch_card_2
  apply (metis card_2_iff' dual_order.eq_iff short_ch_def)
  using assms fin_long_chain_def not_less by fastforce


(*TODO: make index_neq_ results use this, much simpler!?*)
theorem (*2ii*) index_injective:
  fixes i::nat and j::nat
  assumes chX: "long_ch_by_ord2 f X"
      and finiteX: "finite X"
      and indices: "i<j" "j<card X"
    shows "f i \<noteq> f j"
proof (cases)
  assume "Suc i < j"
  then have "[[(f i) (f (Suc(i))) (f j)]]"
    using order_finite_chain2 chX finiteX indices(2) by blast
  then show ?thesis
    using abc_abc_neq by blast
next
  assume "\<not>Suc i < j"
  hence "Suc i = j"
    using Suc_lessI indices(1) by blast
  show ?thesis
  proof (cases)
    assume "Suc j = card X"
    then have "0<i"
    proof -
      have "Suc(Suc i) = card X"
        by (simp add: \<open>Suc i = j\<close> \<open>Suc j = card X\<close>)
      have "card X \<ge> 3"
        using assms(1) finiteX long_chain2_card_geq by blast
      thus ?thesis
        using \<open>Suc i = j\<close> \<open>Suc j = card X\<close> by linarith
    qed
    then have "[[(f 0) (f i) (f j)]]"
      using assms order_finite_chain2 by blast
    thus ?thesis
      using abc_abc_neq by blast
  next
    assume "\<not>Suc j = card X"
    then have "Suc j < card X"
      using Suc_lessI indices(2) by blast
    then have "[[(f i) (f j) (f(Suc j))]]"
      using chX finiteX indices(1) order_finite_chain2 by blast
    thus ?thesis
      using abc_abc_neq by blast
  qed
qed

end (* context MinkowskiBetweenness *)


section \<open>Finite chain equivalence: local \<open>\<leftrightarrow>\<close> global\<close>
context MinkowskiBetweenness begin


lemma ch_equiv1:
  assumes "long_ch_by_ord f X" "finite X"
  shows "long_ch_by_ord2 f X"
  using assms
  unfolding long_ch_by_ord_def long_ch_by_ord2_def ordering_def ordering2_def
  by (metis lessI)


lemma ch_equiv2:
  assumes "long_ch_by_ord2 f X" "finite X"
  shows "long_ch_by_ord f X"
  using order_finite_chain2 assms
  unfolding long_ch_by_ord_def long_ch_by_ord2_def ordering_def ordering2_def
  apply safe by blast


lemma ch_equiv:
  assumes "finite X"
  shows "long_ch_by_ord f X \<longleftrightarrow> long_ch_by_ord2 f X"
  using ch_equiv1 ch_equiv2 assms by blast


end (*context MinkowskiBetweenness*)


section "Preliminary Results for Kinematic Triangles and Paths/Betweenness"

text \<open>
  Theorem 3 (collinearity)
  First we prove some lemmas that will be very helpful.
\<close>


context MinkowskiPrimitive begin

lemma triangle_permutes [no_atp]:
  assumes "\<triangle> a b c" 
  shows "\<triangle> a c b" "\<triangle> b a c" "\<triangle> b c a" "\<triangle> c a b" "\<triangle> c b a"
  using assms by (auto simp add: kinematic_triangle_def)+

lemma triangle_paths [no_atp]:
  assumes tri_abc: "\<triangle> a b c"
  shows "path_ex a b" "path_ex a c" "path_ex b c"
using tri_abc by (auto simp add: kinematic_triangle_def)+


lemma triangle_paths_unique:
  assumes tri_abc: "\<triangle> a b c"
  shows "\<exists>!ab. path ab a b"      
  using path_unique tri_abc triangle_paths(1) by auto

text \<open>
  The definition of the kinematic triangle says that there exist paths that $a$ and $b$ pass through,
  and $a$ and $c$ pass through etc that are not equal. But we can show there is a \emph{unique} $ab$ that $a$
  and $b$ pass through, and assuming there is a path $abc$  that $a, b, c$ pass through, it must be
  unique. Therefore \<open>ab = abc\<close> and \<open>ac = abc\<close>, but \<open>ab \<noteq> ac\<close>, therefore \<open>False\<close>.
  Lemma \<open>tri_three_paths\<close> is not in the books but might simplify some path obtaining.
\<close>

lemma triangle_diff_paths:
  assumes tri_abc: "\<triangle> a b c"
  shows "\<not> (\<exists>Q\<in>\<P>. a \<in> Q \<and> b \<in> Q \<and> c \<in> Q)"
proof (rule notI)
  assume not_thesis: "\<exists>Q\<in>\<P>. a \<in> Q \<and> b \<in> Q \<and> c \<in> Q"
  (* First show [abc] or similar so I can show the path through abc is unique. *)
  then obtain abc where path_abc: "abc \<in> \<P> \<and> a \<in> abc \<and> b \<in> abc \<and> c \<in> abc" by auto
  have abc_neq: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c" using tri_abc kinematic_triangle_def by simp
  (* Now extract some information from \<triangle> a b c. *)
  have "\<exists>ab\<in>\<P>. \<exists>ac\<in>\<P>. ab \<noteq> ac \<and> a \<in> ab \<and> b \<in> ab \<and> a \<in> ac \<and> c \<in> ac"
    using tri_abc kinematic_triangle_def by metis
  then obtain ab ac where ab_ac_relate: "ab \<in> \<P> \<and> ac \<in> \<P> \<and> ab \<noteq> ac \<and> {a,b} \<subseteq> ab \<and> {a,c} \<subseteq> ac"
    by blast
  have "\<exists>!ab\<in>\<P>. a \<in> ab \<and> b \<in> ab" using tri_abc triangle_paths_unique by blast
  then have ab_eq_abc: "ab = abc" using path_abc ab_ac_relate by auto
  have "\<exists>!ac\<in>\<P>. a \<in> ac \<and> b \<in> ac" using tri_abc triangle_paths_unique by blast
  then have ac_eq_abc: "ac = abc" using path_abc ab_ac_relate eq_paths abc_neq by auto
  have "ab = ac" using ab_eq_abc ac_eq_abc by simp
  thus False using ab_ac_relate by simp
qed

lemma tri_three_paths [elim]:
  assumes tri_abc: "\<triangle> a b c"
  shows "\<exists>ab bc ca. path ab a b \<and> path bc b c \<and> path ca c a \<and> ab \<noteq> bc \<and> ab \<noteq> ca \<and> bc \<noteq> ca"
using tri_abc triangle_diff_paths triangle_paths(2,3) triangle_paths_unique
by fastforce

lemma triangle_paths_neq:
  assumes tri_abc: "\<triangle> a b c"
      and path_ab: "path ab a b"
      and path_ac: "path ac a c"
  shows "ab \<noteq> ac"
using assms triangle_diff_paths by blast

end (*context MinkowskiPrimitive*)
context MinkowskiBetweenness begin

lemma abc_ex_path_unique:
  assumes abc: "[[a b c]]"
  shows "\<exists>!Q\<in>\<P>. a \<in> Q \<and> b \<in> Q \<and> c \<in> Q"
proof -
  have a_neq_c: "a \<noteq> c" using abc_ac_neq abc by simp
  have "\<exists>Q\<in>\<P>. a \<in> Q \<and> b \<in> Q \<and> c \<in> Q" using abc_ex_path abc by simp
  then obtain P Q where path_P: "P \<in> \<P>" and abc_inP: "a \<in> P \<and> b \<in> P \<and> c \<in> P"
                    and path_Q: "Q \<in> \<P>" and abc_in_Q: "a \<in> Q \<and> b \<in> Q \<and> c \<in> Q" by auto
  then have "P = Q" using a_neq_c eq_paths by blast
  thus ?thesis using eq_paths a_neq_c using abc_inP path_P by auto
qed

lemma betw_c_in_path:
  assumes abc: "[[a b c]]"
      and path_ab: "path ab a b"
  shows "c \<in> ab"
(* By abc_ex_path, there is a path through a b c. By eq_paths there can be only one, which must be ab. *)
using eq_paths abc_ex_path assms by blast

lemma betw_b_in_path:
  assumes abc: "[[a b c]]"
      and path_ab: "path ac a c"
  shows "b \<in> ac"
using assms abc_ex_path_unique path_unique by blast

lemma betw_a_in_path:
  assumes abc: "[[a b c]]"
      and path_ab: "path bc b c"
  shows "a \<in> bc"
using assms abc_ex_path_unique path_unique by blast

lemma triangle_not_betw_abc:
  assumes tri_abc: "\<triangle> a b c"
  shows "\<not> [[a b c]]"
using tri_abc abc_ex_path triangle_diff_paths by blast

lemma triangle_not_betw_acb:
  assumes tri_abc: "\<triangle> a b c"
  shows "\<not> [[a c b]]"
by (simp add: tri_abc triangle_not_betw_abc triangle_permutes(1))

lemma triangle_not_betw_bac:
  assumes tri_abc: "\<triangle> a b c"
  shows "\<not> [[b a c]]"
by (simp add: tri_abc triangle_not_betw_abc triangle_permutes(2))

lemma triangle_not_betw_any:
  assumes tri_abc: "\<triangle> a b c"
  shows "\<not> (\<exists>d\<in>{a,b,c}. \<exists>e\<in>{a,b,c}. \<exists>f\<in>{a,b,c}. [[d e f]])"
  by (metis abc_ex_path abc_abc_neq empty_iff insertE tri_abc triangle_diff_paths)

end (*context MinkowskiBetweenness*)


section "3.2 First collinearity theorem"

theorem (*3*) (in MinkowskiChain) collinearity_alt2:
  assumes tri_abc: "\<triangle> a b c"
      and path_de: "path de d e"
      (* This follows immediately from tri_abc without it as an assumption, but we need ab in scope
         to refer to it in the conclusion. *)
      and path_ab: "path ab a b"
      and bcd: "[[b c d]]"
      and cea: "[[c e a]]"
  shows "\<exists>f\<in>de\<inter>ab. [[a f b]]"
proof -
  have "\<exists>f\<in>ab \<inter> de. \<exists>X. [[a..f..b]X]"
  proof -
    have "path_ex a c" using tri_abc triangle_paths(2) by auto
    then obtain ac where path_ac: "path ac a c" by auto
    have "path_ex b c" using tri_abc triangle_paths(3) by auto
    then obtain bc where path_bc: "path bc b c" by auto
    have ab_neq_ac: "ab \<noteq> ac" using triangle_paths_neq path_ab path_ac tri_abc by fastforce
    have ab_neq_bc: "ab \<noteq> bc" using eq_paths ab_neq_ac path_ab path_ac path_bc by blast
    have ac_neq_bc: "ac \<noteq> bc" using eq_paths ab_neq_bc path_ab path_ac path_bc by blast
    have d_in_bc: "d \<in> bc" using bcd betw_c_in_path path_bc by blast
    have e_in_ac: "e \<in> ac" using betw_b_in_path cea path_ac by blast 
    show ?thesis
      using O6 [where Q = ab and R = ac and S = bc and T = de and a = a and b = b and c = c] 
            ab_neq_ac ab_neq_bc ac_neq_bc path_ab path_bc path_ac path_de bcd cea d_in_bc e_in_ac
      by auto
  qed
  thus ?thesis using finite_chain3_betw by blast
qed


theorem (*3*) (in MinkowskiChain) collinearity_alt:
  assumes tri_abc: "\<triangle> a b c"
      and path_de: "path de d e"
      and bcd: "[[b c d]]"
      and cea: "[[c e a]]"
  shows "\<exists>ab. path ab a b \<and> (\<exists>f\<in>de\<inter>ab. [[a f b]])"
proof -
  have ex_path_ab: "path_ex a b"
    using tri_abc triangle_paths_unique by blast
  then obtain ab where path_ab: "path ab a b"
    by blast
  have "\<exists>f\<in>ab \<inter> de. \<exists>X. [[a..f..b]X]"
  proof -
    have "path_ex a c" using tri_abc triangle_paths(2) by auto
    then obtain ac where path_ac: "path ac a c" by auto
    have "path_ex b c" using tri_abc triangle_paths(3) by auto
    then obtain bc where path_bc: "path bc b c" by auto
    have ab_neq_ac: "ab \<noteq> ac" using triangle_paths_neq path_ab path_ac tri_abc by fastforce
    have ab_neq_bc: "ab \<noteq> bc" using eq_paths ab_neq_ac path_ab path_ac path_bc by blast
    have ac_neq_bc: "ac \<noteq> bc" using eq_paths ab_neq_bc path_ab path_ac path_bc by blast
    have d_in_bc: "d \<in> bc" using bcd betw_c_in_path path_bc by blast
    have e_in_ac: "e \<in> ac" using betw_b_in_path cea path_ac by blast 
    show ?thesis
      using O6 [where Q = ab and R = ac and S = bc and T = de and a = a and b = b and c = c] 
            ab_neq_ac ab_neq_bc ac_neq_bc path_ab path_bc path_ac path_de bcd cea d_in_bc e_in_ac
      by auto
  qed
  thus ?thesis using finite_chain3_betw path_ab by fastforce
qed


theorem (*3*) (in MinkowskiChain) collinearity:
  assumes tri_abc: "\<triangle> a b c"
      and path_de: "path de d e"
      and bcd: "[[b c d]]"
      and cea: "[[c e a]]"
    shows "(\<exists>f\<in>de\<inter>(path_of a b). [[a f b]])"
proof - 
  let ?ab = "path_of a b"
  have path_ab: "path ?ab a b"
    using tri_abc theI' [OF triangle_paths_unique] by blast
  have "\<exists>f\<in>?ab \<inter> de. \<exists>X. [[a..f..b]X]"
  proof -
    have "path_ex a c" using tri_abc triangle_paths(2) by auto
    then obtain ac where path_ac: "path ac a c" by auto
    have "path_ex b c" using tri_abc triangle_paths(3) by auto
    then obtain bc where path_bc: "path bc b c" by auto
    have ab_neq_ac: "?ab \<noteq> ac" using triangle_paths_neq path_ab path_ac tri_abc by fastforce
    have ab_neq_bc: "?ab \<noteq> bc" using eq_paths ab_neq_ac path_ab path_ac path_bc by blast
    have ac_neq_bc: "ac \<noteq> bc" using eq_paths ab_neq_bc path_ab path_ac path_bc by blast
    have d_in_bc: "d \<in> bc" using bcd betw_c_in_path path_bc by blast
    have e_in_ac: "e \<in> ac" using betw_b_in_path cea path_ac by blast 
    show ?thesis
      using O6 [where Q = ?ab and R = ac and S = bc and T = de and a = a and b = b and c = c] 
            ab_neq_ac ab_neq_bc ac_neq_bc path_ab path_bc path_ac path_de bcd cea d_in_bc e_in_ac
            IntI Int_commute
      by (metis (no_types, lifting))
  qed
  thus ?thesis using finite_chain3_betw by blast
qed


section "Additional results for Paths and Unreachables"

context MinkowskiPrimitive begin

text \<open>The degenerate case.\<close>
lemma big_bang:
  assumes no_paths: "\<P> = {}"
  shows "\<exists>a. \<E> = {a}"
proof -
  have "\<exists>a. a \<in> \<E>" using nonempty_events by blast
  then obtain a where a_event: "a \<in> \<E>" by auto
  have "\<not> (\<exists>b\<in>\<E>. b \<noteq> a)"
  proof (rule notI)
    assume "\<exists>b\<in>\<E>. b \<noteq> a"
    then have "\<exists>Q. Q \<in> \<P>" using events_paths a_event by auto
    thus False using no_paths by simp
  qed
  then have "\<forall>b\<in>\<E>. b = a" by simp
  thus ?thesis using a_event by auto
qed

lemma two_events_then_path:
  assumes two_events: "\<exists>a\<in>\<E>. \<exists>b\<in>\<E>. a \<noteq> b"
  shows "\<exists>Q. Q \<in> \<P>"
proof -
  have "(\<forall>a. \<E> \<noteq> {a}) \<longrightarrow> \<P> \<noteq> {}" using big_bang by blast
  then have "\<P> \<noteq> {}" using two_events by blast
  thus ?thesis by blast
qed

lemma paths_are_events: "\<forall>Q\<in>\<P>. \<forall>a\<in>Q. a \<in> \<E>"
  by simp

lemma same_empty_unreach:
  "\<lbrakk>Q \<in> \<P>; a \<in> Q\<rbrakk> \<Longrightarrow> \<emptyset> Q a = {}"
apply (unfold unreachable_subset_def)
by simp

lemma same_path_reachable:
  "\<lbrakk>Q \<in> \<P>; a \<in> Q; b \<in> Q\<rbrakk> \<Longrightarrow> a \<in> Q - \<emptyset> Q b"
by (simp add: same_empty_unreach)

text \<open>
  If we have two paths crossing and $a$ is on the crossing point, and $b$ is on one of the paths,
  then $a$ is in the reachable part of the path $b$ is on.
\<close>

lemma same_path_reachable2:
  "\<lbrakk>Q \<in> \<P>; R \<in> \<P>; a \<in> Q; a \<in> R; b \<in> Q\<rbrakk> \<Longrightarrow> a \<in> R - \<emptyset> R b"
  unfolding unreachable_subset_def by blast

(* This will never be used without R \<in> \<P> but we might as well leave it off as the proof doesn't
   need it. *)
lemma cross_in_reachable:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
      and b_inQ: "b \<in> Q"
      and b_inR: "b \<in> R"
  shows "b \<in> R - \<emptyset> R a"
unfolding unreachable_subset_def using a_inQ b_inQ b_inR path_Q by auto

lemma reachable_path:
  assumes path_Q: "Q \<in> \<P>"
      and b_event: "b \<in> \<E>"
      and a_reachable: "a \<in> Q - \<emptyset> Q b"
  shows "\<exists>R\<in>\<P>. a \<in> R \<and> b \<in> R"
proof -
  have a_inQ: "a \<in> Q" using a_reachable by simp
  have "Q \<notin> \<P> \<or> b \<notin> \<E> \<or> b \<in> Q \<or> (\<exists>R\<in>\<P>. b \<in> R \<and> a \<in> R)"
      using a_reachable unreachable_subset_def by auto
  then have "b \<in> Q \<or> (\<exists>R\<in>\<P>. b \<in> R \<and> a \<in> R)" using path_Q b_event by simp
  thus ?thesis
  proof (rule disjE)
    assume "b \<in> Q"
    thus ?thesis using a_inQ path_Q by auto
  next
    assume "\<exists>R\<in>\<P>. b \<in> R \<and> a \<in> R"
    thus ?thesis using conj_commute by simp
  qed
qed

end (* context MinkowskiPrimitive *)
context MinkowskiUnreachable begin

text \<open>
  First some basic facts about the primitive notions, which seem to belong here.
  I don't think any/all of these are explicitly proved in Schutz.
\<close>

lemma no_empty_paths [simp]:
  assumes "Q\<in>\<P>"
  shows "Q\<noteq>{}"
proof -
  obtain a where "a\<in>\<E>" using nonempty_events by blast
  have "a\<in>Q \<or> a\<notin>Q" by auto
  thus ?thesis
  proof
    assume "a\<in>Q"
    thus ?thesis by blast
  next
    assume "a\<notin>Q"
    then obtain b where "b\<in>\<emptyset> Q a"
      using two_in_unreach \<open>a \<in> \<E>\<close> assms
      by blast
    thus ?thesis
      using unreachable_subset_def by auto
  qed
qed

lemma events_ex_path:
  assumes ge1_path: "\<P> \<noteq> {}"
  shows "\<forall>x\<in>\<E>. \<exists>Q\<in>\<P>. x \<in> Q"
proof
  fix x
  assume x_event: "x \<in> \<E>"
  have "\<exists>Q. Q \<in> \<P>" using ge1_path using ex_in_conv by blast
  then obtain Q where path_Q: "Q \<in> \<P>" by auto
  then have "\<exists>y. y \<in> Q" using no_empty_paths by blast
  then obtain y where y_inQ: "y \<in> Q" by auto
  then have y_event: "y \<in> \<E>" using in_path_event path_Q by simp
  have "\<exists>P\<in>\<P>. x \<in> P"
  proof cases
    assume "x = y"
    thus ?thesis using y_inQ path_Q by auto
  next
    assume "x \<noteq> y"
    thus ?thesis using events_paths x_event y_event by auto
  qed
  thus "\<exists>Q\<in>\<P>. x \<in> Q" by simp
qed

lemma unreach_ge2_then_ge2:
  assumes "\<exists>x\<in>\<emptyset> Q b. \<exists>y\<in>\<emptyset> Q b. x \<noteq> y"
  shows "\<exists>x\<in>Q. \<exists>y\<in>Q. x \<noteq> y"
using assms unreachable_subset_def by auto

text \<open>
  This lemma just proves that the chain obtained to bound the unreachable set of a path
  is indeed on that path. Extends I6; requires Theorem 2; used in Theorem 13.
  Seems to be assumed in Schutz' chain notation in I6.
\<close>

lemma chain_on_path_I6:
  assumes path_Q: "Q\<in>\<P>"
      and event_b: "b\<notin>Q" "b\<in>\<E>"
      and unreach: "Q\<^sub>x \<in> \<emptyset> Q b" "Q\<^sub>z \<in> \<emptyset> Q b" "Q\<^sub>x \<noteq> Q\<^sub>z"
      and X_def: "ch_by_ord f X" "f 0 = Q\<^sub>x" "f (card X - 1) = Q\<^sub>z"
          "(\<forall>i\<in>{1 .. card X - 1}. (f i) \<in> \<emptyset> Q b \<and> (\<forall>Q\<^sub>y\<in>\<E>. [[(f(i-1)) Q\<^sub>y (f i)]] \<longrightarrow> Q\<^sub>y \<in> \<emptyset> Q b))"
          "(short_ch X \<longrightarrow> Q\<^sub>x\<in>X \<and> Q\<^sub>z\<in>X \<and> (\<forall>Q\<^sub>y\<in>\<E>. [[Q\<^sub>x Q\<^sub>y Q\<^sub>z]] \<longrightarrow> Q\<^sub>y \<in> \<emptyset> Q b))"
  shows "X\<subseteq>Q"
  (* by (smt X_def(1) chain_on_path eq_paths in_Q in_X path_Q subset_eq unreach(3)) *)
  (* smt has a really easy time of this, but no other method does (legacy code from thm13) *)
proof -
  have in_Q: "Q\<^sub>x\<in>Q \<and> Q\<^sub>z\<in>Q"
    using unreachable_subset_def unreach(1,2) by blast
  have fin_X: "finite X"
    using unreach(3) not_less X_def by fastforce
  {
    assume "short_ch X"
    hence ?thesis
      by (metis X_def(5) in_Q short_ch_def subsetI unreach(3))
  } moreover {
    assume asm: "long_ch_by_ord f X"
    have ?thesis
      proof
        fix x assume "x\<in>X"
        then obtain i where "f i = x" "i < card X"
          using asm unfolding ch_by_ord_def long_ch_by_ord_def ordering_def
          using fin_X by auto
        show "x\<in>Q"
        proof (cases)
          assume "x=Q\<^sub>x \<or> x=Q\<^sub>z"
          thus ?thesis
            using in_Q by blast
        next
          assume "\<not>(x=Q\<^sub>x \<or> x=Q\<^sub>z)"
          hence "x\<noteq>Q\<^sub>x" "x\<noteq>Q\<^sub>z" by linarith+
          have "i>0"
            using X_def(2) `x\<noteq>Q\<^sub>x` \<open>f i = x\<close> gr_zeroI by force
          have "i<card X - 1"
            using X_def(3) \<open>f i = x\<close> \<open>i < card X\<close> \<open>x \<noteq> Q\<^sub>z\<close> less_imp_diff_less less_SucE
            by (metis Suc_pred' cancel_comm_monoid_add_class.diff_cancel)
          have "[[Q\<^sub>x (f i) Q\<^sub>z]]"
            using X_def(2,3) \<open>0 < i\<close> \<open>i < card X - 1\<close> asm fin_X order_finite_chain
            by auto
          thus ?thesis
            by (simp add: \<open>f i = x\<close> betw_b_in_path in_Q path_Q unreach(3))
        qed
      qed
    }
  ultimately show ?thesis
    using X_def(1) ch_by_ord_def by blast
qed

end (* context MinkowskiUnreachable *)


section "Results about Paths as Sets"

text \<open>
  Note several of the following don't need MinkowskiPrimitive, they are just Set lemmas;
  nevertheless I'm naming them and writing them this way for clarity.
\<close>

context MinkowskiPrimitive begin

lemma distinct_paths:
  assumes "Q \<in> \<P>"
      and "R \<in> \<P>"
      and "d \<notin> Q"
      and "d \<in> R"
  shows "R \<noteq> Q"
using assms by auto

lemma distinct_paths2:
  assumes "Q \<in> \<P>"
      and "R \<in> \<P>"
      and "\<exists>d. d \<notin> Q \<and> d \<in> R"
  shows "R \<noteq> Q"
using assms by auto

lemma external_events_neq:
  "\<lbrakk>Q \<in> \<P>; a \<in> Q; b \<in> \<E>; b \<notin> Q\<rbrakk> \<Longrightarrow> a \<noteq> b"
by auto

lemma notin_cross_events_neq:
  "\<lbrakk>Q \<in> \<P>; R \<in> \<P>; Q \<noteq> R; a \<in> Q; b \<in> R; a \<notin> R\<inter>Q\<rbrakk> \<Longrightarrow> a \<noteq> b"
by blast

lemma nocross_events_neq:
  "\<lbrakk>Q \<in> \<P>; R \<in> \<P>; a \<in> Q; b \<in> R; R\<inter>Q = {}\<rbrakk> \<Longrightarrow> a \<noteq> b"
by auto

text \<open>
  Given a nonempty path $Q$, and an external point $d$, we can find another path
  $R$ passing through $d$ (by I2 aka \<open>events_paths\<close>). This path is distinct
  from $Q$, as it passes through a point external to it.
\<close>
lemma external_path:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
      and d_notinQ: "d \<notin> Q"
      and d_event: "d \<in> \<E>"
  shows "\<exists>R\<in>\<P>. d \<in> R"
proof -
  have a_neq_d: "a \<noteq> d" using a_inQ d_notinQ by auto
  thus "\<exists>R\<in>\<P>. d \<in> R" using events_paths by (meson a_inQ d_event in_path_event path_Q)
qed

lemma distinct_path:
  assumes "Q \<in> \<P>"
      and "a \<in> Q"
      and "d \<notin> Q"
      and "d \<in> \<E>"
  shows "\<exists>R\<in>\<P>. R \<noteq> Q"
using assms external_path by metis

lemma external_distinct_path:
  assumes "Q \<in> \<P>"
      and "a \<in> Q"
      and "d \<notin> Q"
      and "d \<in> \<E>"
  shows "\<exists>R\<in>\<P>. R \<noteq> Q \<and> d \<in> R"
  using assms external_path by fastforce

end (* context MinkowskiPrimitive *)


section "3.3 Boundedness of the unreachable set"

subsection \<open>Theorem 4 (boundedness of the unreachable set)\<close>
text \<open>
  The same assumptions as I7, different conclusion.
  This doesn't just give us boundedness, it gives us another event outside of the unreachable
  set, as long as we have one already.
  I7 conclusion:  \<open>\<exists>X Q0 Qm Qn. [[Q0 .. Qm .. Qn]X] \<and> Q0 = ?Qx \<and> Qm = ?Qy \<and> Qn \<in> ?Q - \<emptyset> ?Q ?b\<close>
\<close>

theorem (*4*) (in MinkowskiUnreachable) unreachable_set_bounded:
  assumes path_Q: "Q \<in> \<P>"
      and b_nin_Q: "b \<notin> Q"
      and b_event: "b \<in> \<E>"
      and Qx_reachable: "Qx \<in> Q - \<emptyset> Q b"
      and Qy_unreachable: "Qy \<in> \<emptyset> Q b"
  shows "\<exists>Qz\<in>Q - \<emptyset> Q b. [[Qx Qy Qz]] \<and> Qx \<noteq> Qz"
  using assms I7 order_finite_chain fin_long_chain_def
  by (metis fin_ch_betw)

subsection \<open>Theorem 5 (first existence theorem)\<close>
text \<open>
  The lemma below is used in the contradiction in \<open>external_event\<close>,
  which is the essential part to Theorem 5(i).
\<close>
lemma (in MinkowskiUnreachable) only_one_path:
  assumes path_Q: "Q \<in> \<P>"
      and all_inQ: "\<forall>a\<in>\<E>. a \<in> Q"
      and path_R: "R \<in> \<P>"
  shows "R = Q"
proof (rule ccontr)
  assume "\<not> R = Q"
  then have R_neq_Q: "R \<noteq> Q" by simp
  have "\<E> = Q"
    by (simp add: all_inQ antisym path_Q path_sub_events subsetI)
  hence "R\<subset>Q"
    using R_neq_Q path_R path_sub_events by auto
  obtain c where "c\<notin>R" "c\<in>Q"
    using \<open>R \<subset> Q\<close> by blast
  then obtain a b where "path R a b"
    using \<open>\<E> = Q\<close> path_R two_in_unreach unreach_ge2_then_ge2 by blast
  have "a\<in>Q" "b\<in>Q"
    using \<open>\<E> = Q\<close> \<open>path R a b\<close> in_path_event by blast+
  thus False using eq_paths
    using R_neq_Q \<open>path R a b\<close> path_Q by blast
qed

context MinkowskiSpacetime begin

text \<open>Unfortunately, we cannot assume that a path exists without the axiom of dimension.\<close>
lemma external_event:
  assumes path_Q: "Q \<in> \<P>"
  shows "\<exists>d\<in>\<E>. d \<notin> Q"
proof (rule ccontr)
  assume "\<not> (\<exists>d\<in>\<E>. d \<notin> Q)"
  then have all_inQ: "\<forall>d\<in>\<E>. d \<in> Q" by simp
  then have only_one_path: "\<forall>P\<in>\<P>. P = Q" by (simp add: only_one_path path_Q) 
  thus False using ex_3SPRAY three_SPRAY_ge4 four_paths by auto
qed

text \<open>
  Now we can prove the first part of the theorem's conjunction.
  This follows pretty much exactly the same pattern as the book, except it relies on more
  intermediate lemmas.
\<close>
theorem (*5i*) ge2_events:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
  shows "\<exists>b\<in>Q. b \<noteq> a"
proof -
  have d_notinQ: "\<exists>d\<in>\<E>. d \<notin> Q" using path_Q external_event by blast 
  then obtain d where "d \<in> \<E>" and "d \<notin> Q" by auto
  thus ?thesis using two_in_unreach [where Q = Q and b = d] path_Q unreach_ge2_then_ge2 by metis
qed

text \<open>
  Simple corollary which is easier to use when we don't have one event on a path yet.
  Anything which uses this implicitly used \<open>no_empty_paths\<close> on top of \<open>ge2_events\<close>.
\<close>
lemma ge2_events_lax:
  assumes path_Q: "Q \<in> \<P>"
  shows "\<exists>a\<in>Q. \<exists>b\<in>Q. a \<noteq> b"
proof -
  have "\<exists>a\<in>\<E>. a \<in> Q" using path_Q no_empty_paths by (meson ex_in_conv in_path_event)
  thus ?thesis using path_Q ge2_events by blast
qed

lemma ex_crossing_path:
  assumes path_Q: "Q \<in> \<P>"
  shows "\<exists>R\<in>\<P>. R \<noteq> Q \<and> (\<exists>c. c \<in> R \<and> c \<in> Q)"
proof -
  obtain a where a_inQ: "a \<in> Q" using ge2_events_lax path_Q by blast
  obtain d where d_event: "d \<in> \<E>"
             and d_notinQ: "d \<notin> Q" using external_event path_Q by auto
  then have "a \<noteq> d" using a_inQ by auto
  then have ex_through_d: "\<exists>R\<in>\<P>. \<exists>S\<in>\<P>. a \<in> R \<and> d \<in> S \<and> R \<inter> S \<noteq> {}"
      using events_paths [where a = a and b = d]
            path_Q a_inQ in_path_event d_event by simp
  then obtain R S where path_R: "R \<in> \<P>"
                    and path_S: "S \<in> \<P>"
                    and a_inR: "a \<in> R"
                    and d_inS: "d \<in> S"
                    and R_crosses_S: "R \<inter> S \<noteq> {}" by auto
  have S_neq_Q: "S \<noteq> Q" using d_notinQ d_inS by auto
  show ?thesis
  proof cases
    assume "R = Q"
    then have "Q \<inter> S \<noteq> {}" using R_crosses_S by simp
    thus ?thesis using S_neq_Q path_S by blast
  next
    assume "R \<noteq> Q"
    thus ?thesis using a_inQ a_inR path_R by blast
  qed
qed

text \<open>
  If we have two paths $Q$ and $R$ with $a$ on $Q$ and $b$ at the intersection of $Q$ and $R$, then by
  \<open>two_in_unreach\<close> (I5) and Theorem 4 (boundedness of the unreachable set), there is an unreachable
  set from $a$ on one side of $b$ on $R$, and on the other side of that there is an event which is
  reachable from $a$ by some path, which is the path we want.
\<close>

lemma path_past_unreach:
  assumes path_Q: "Q \<in> \<P>"
      and path_R: "R \<in> \<P>"
      and a_inQ: "a \<in> Q"
      and b_inQ: "b \<in> Q"
      and b_inR: "b \<in> R"
      and Q_neq_R: "Q \<noteq> R"
      and a_neq_b: "a \<noteq> b"
  shows "\<exists>S\<in>\<P>. S \<noteq> Q \<and> a \<in> S \<and> (\<exists>c. c \<in> S \<and> c \<in> R)"
proof -
  obtain d where d_event: "d \<in> \<E>"
             and d_notinR: "d \<notin> R" using external_event path_R by blast
  have b_reachable: "b \<in> R - \<emptyset> R a" using cross_in_reachable path_R a_inQ b_inQ b_inR path_Q by simp
  have a_notinR: "a \<notin> R" using cross_once_notin
                               Q_neq_R a_inQ a_neq_b b_inQ b_inR path_Q path_R by blast
  then obtain u where "u \<in> \<emptyset> R a"
      using two_in_unreach a_inQ in_path_event path_Q path_R by blast
  then obtain c where c_reachable: "c \<in> R - \<emptyset> R a"
                  and c_neq_b: "b \<noteq> c" using unreachable_set_bounded
                                        [where Q = R and Qx = b and b = a and Qy = u]
                                        path_R d_event d_notinR
      using a_inQ a_notinR b_reachable in_path_event path_Q by blast
  then obtain S where S_facts: "S \<in> \<P> \<and> a \<in> S \<and> (c \<in> S \<and> c \<in> R)" using reachable_path
      by (metis Diff_iff a_inQ in_path_event path_Q path_R)
  then have "S \<noteq> Q" using Q_neq_R b_inQ b_inR c_neq_b eq_paths path_R by blast
  thus ?thesis using S_facts by auto
qed

theorem (*5ii*) ex_crossing_at:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
  shows "\<exists>ac\<in>\<P>. ac \<noteq> Q \<and> (\<exists>c. c \<notin> Q \<and> a \<in> ac \<and> c \<in> ac)"
proof -
  obtain b where b_inQ: "b \<in> Q"
             and a_neq_b: "a \<noteq> b" using a_inQ ge2_events path_Q by blast
  have "\<exists>R\<in>\<P>. R \<noteq> Q \<and> (\<exists>e. e \<in> R \<and> e \<in> Q)" by (simp add: ex_crossing_path path_Q)
  then obtain R e where path_R: "R \<in> \<P>"
                    and R_neq_Q: "R \<noteq> Q"
                    and e_inR: "e \<in> R"
                    and e_inQ: "e \<in> Q" by auto
  thus ?thesis
  proof cases
    assume e_eq_a: "e = a"
    then have "\<exists>c. c \<in> \<emptyset> R b" using R_neq_Q a_inQ a_neq_b b_inQ e_inR path_Q path_R
                                    two_in_unreach path_unique in_path_event by metis
    thus ?thesis using R_neq_Q e_eq_a e_inR path_Q path_R
                       eq_paths ge2_events_lax by metis
  next
    assume e_neq_a: "e \<noteq> a"
    (* We know the whole of R isn't unreachable from a because e is on R and both a and e are on Q.
       We also know there is some point after e, and after the unreachable set, which is reachable
       from a (because there are at least two events in the unreachable set, and it is bounded). *)
    (* This does follow Schutz, if you unfold the proof for path_past_unreach here, though it's a
       little trickier than Schutz made it seem. *)
    then have "\<exists>S\<in>\<P>. S \<noteq> Q \<and> a \<in> S \<and> (\<exists>c. c \<in> S \<and> c \<in> R)"
        using path_past_unreach
              R_neq_Q a_inQ e_inQ e_inR path_Q path_R by auto
    thus ?thesis by (metis R_neq_Q e_inR e_neq_a eq_paths path_Q path_R) 
  qed
qed

(* Alternative formulation using the path function *)
lemma (*5ii_alt*) ex_crossing_at_alt:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
    shows "\<exists>ac. \<exists>c. path ac a c \<and> ac \<noteq> Q \<and> c \<notin> Q"
  using ex_crossing_at assms by fastforce

end (* context MinkowskiSpacetime *)


section "3.4 Prolongation"
context MinkowskiSpacetime begin

lemma (in MinkowskiPrimitive) unreach_on_path:
  "a \<in> \<emptyset> Q b \<Longrightarrow> a \<in> Q"
using unreachable_subset_def by simp

lemma (in MinkowskiUnreachable) unreach_equiv:
  "\<lbrakk>Q \<in> \<P>; R \<in> \<P>; a \<in> Q; b \<in> R; a \<in> \<emptyset> Q b\<rbrakk> \<Longrightarrow> b \<in> \<emptyset> R a"
  unfolding unreachable_subset_def by auto

theorem (*6i*) prolong_betw:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
      and b_inQ: "b \<in> Q"
      and ab_neq: "a \<noteq> b"
  shows "\<exists>c\<in>\<E>. [[a b c]]"
proof -
  obtain e ae where e_event: "e \<in> \<E>"
                and e_notinQ: "e \<notin> Q"
                and path_ae: "path ae a e"
    using ex_crossing_at a_inQ path_Q in_path_event by blast
  have "b \<notin> ae" using a_inQ ab_neq b_inQ e_notinQ eq_paths path_Q path_ae by blast
  then obtain f where f_unreachable: "f \<in> \<emptyset> ae b"
    using two_in_unreach b_inQ in_path_event path_Q path_ae by blast
  then have b_unreachable: "b \<in> \<emptyset> Q f" using unreach_equiv
      by (metis (mono_tags, lifting) CollectD b_inQ path_Q unreachable_subset_def)
  have a_reachable: "a \<in> Q - \<emptyset> Q f"
      using same_path_reachable2 [where Q = ae and R = Q and a = a and b = f]
            path_ae a_inQ path_Q f_unreachable unreach_on_path by blast
  thus ?thesis
      using unreachable_set_bounded [where Qy = b and Q = Q and b = f and Qx = a]
            b_unreachable unreachable_subset_def by auto
qed

lemma (in MinkowskiSpacetime) prolong_betw2:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
      and b_inQ: "b \<in> Q"
      and ab_neq: "a \<noteq> b"
  shows "\<exists>c\<in>Q. [[a b c]]"
  by (metis assms betw_c_in_path prolong_betw)

lemma (in MinkowskiSpacetime) prolong_betw3:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
      and b_inQ: "b \<in> Q"
      and ab_neq: "a \<noteq> b"
  shows "\<exists>c\<in>Q. \<exists>d\<in>Q. [[a b c]] \<and> [[a b d]] \<and> c\<noteq>d"
  by (metis (full_types) abc_abc_neq abc_bcd_abd a_inQ ab_neq b_inQ path_Q prolong_betw2)

lemma finite_path_has_ends:
  assumes "Q \<in> \<P>"
      and "X \<subseteq> Q"
      and "finite X"
      and "card X \<ge> 3"
    shows "\<exists>a\<in>X. \<exists>b\<in>X. a \<noteq> b \<and> (\<forall>c\<in>X. a \<noteq> c \<and> b \<noteq> c \<longrightarrow> [[a c b]])"
using assms
proof (induct "card X - 3" arbitrary: X)
  case 0
  then have "card X = 3"
    by linarith
  then obtain a b c where X_eq: "X = {a, b, c}"
    by (metis card_Suc_eq numeral_3_eq_3)
  then have abc_neq: "a \<noteq> b" "a \<noteq> c" "b \<noteq> c"
    by (metis \<open>card X = 3\<close> empty_iff insert_iff order_refl three_in_set3)+
  then consider "[[a b c]]" | "[[b c a]]" | "[[c a b]]"
    using some_betw [of Q a b c] "0.prems"(1) "0.prems"(2) X_eq by auto
  thus ?case
  proof (cases)
    assume "[[a b c]]"
    thus ?thesis \<comment> \<open>All d not equal to a or c is just d = b, so it immediately follows.\<close>
      using X_eq abc_neq(2) by blast
  next
    assume "[[b c a]]"
    thus ?thesis
      by (simp add: X_eq abc_neq(1))
  next
    assume "[[c a b]]"
    thus ?thesis (* jep: sledgehammer had trouble with this case without explicitly telling it what
      assumptions to use, for some reason, and even then only one prover figured out "by auto". *)
      using X_eq abc_neq(3) by blast
  qed
next
  case IH: (Suc n)
  obtain Y x where X_eq: "X = insert x Y" and "x \<notin> Y"
    by (meson IH.prems(4) Set.set_insert three_in_set3)
  then have "card Y - 3 = n" "card Y \<ge> 3"
    using IH.hyps(2) IH.prems(3) X_eq \<open>x \<notin> Y\<close> by auto
  then obtain a b where ab_Y: "a \<in> Y" "b \<in> Y" "a \<noteq> b"
                    and Y_ends: "\<forall>c\<in>Y. (a \<noteq> c \<and> b \<noteq> c) \<longrightarrow> [[a c b]]"
    using IH(1) [of Y] IH.prems(1-3) X_eq by auto
  consider "[[a x b]]" | "[[x b a]]" | "[[b a x]]"
    using some_betw [of Q a x b] ab_Y IH.prems(1,2) X_eq \<open>x \<notin> Y\<close> by auto
  thus ?case
  proof (cases)
    assume "[[a x b]]"
    thus ?thesis
      using Y_ends X_eq ab_Y by auto
  next
    assume "[[x b a]]"
    { fix c
      assume "c \<in> X" "x \<noteq> c" "a \<noteq> c"
      then have "[[x c a]]"
        by (smt IH.prems(2) X_eq Y_ends \<open>[[x b a]]\<close> ab_Y(1) abc_abc_neq abc_bcd_abd abc_only_cba(3) abc_sym \<open>Q \<in> \<P>\<close> betw_b_in_path insert_iff some_betw subsetD)
    }
    thus ?thesis
      using X_eq \<open>[[x b a]]\<close> ab_Y(1) abc_abc_neq insert_iff by force
  next
    assume "[[b a x]]"
    { fix c
      assume "c \<in> X" "b \<noteq> c" "x \<noteq> c"
      then have "[[b c x]]"
        by (smt IH.prems(2) X_eq Y_ends \<open>[[b a x]]\<close> ab_Y(1) abc_abc_neq abc_bcd_acd abc_only_cba(1)
            abc_sym \<open>Q \<in> \<P>\<close> betw_a_in_path insert_iff some_betw subsetD)
    }
    thus ?thesis
      using X_eq \<open>x \<notin> Y\<close> ab_Y(2) by fastforce
  qed
qed


lemma obtain_fin_path_ends:
  assumes path_X: "X\<in>\<P>"
      and fin_Q: "finite Q"
      and card_Q: "card Q \<ge> 3"
      and events_Q: "Q\<subseteq>X"
  obtains a b where "a\<noteq>b" and "a\<in>Q" and "b\<in>Q" and "\<forall>c\<in>Q. (a\<noteq>c \<and> b\<noteq>c) \<longrightarrow> [[a c b]]"
proof -
  obtain n where "n\<ge>0" and "card Q = n+3"
    using card_Q nat_le_iff_add
    by auto
  then obtain a b where "a\<noteq>b" and "a\<in>Q" and "b\<in>Q" and "\<forall>c\<in>Q. (a\<noteq>c \<and> b\<noteq>c) \<longrightarrow> [[a c b]]"
    using finite_path_has_ends assms \<open>n\<ge>0\<close>
    by metis
  thus ?thesis
    using that by auto
qed


lemma path_card_nil:
  assumes "Q\<in>\<P>"
  shows "card Q = 0"
proof (rule ccontr)
  assume "card Q \<noteq> 0"
  obtain n where "n = card Q"
    by auto
  hence "n\<ge>1"
    using \<open>card Q \<noteq> 0\<close> by linarith
  then consider (n1) "n=1" | (n2) "n=2" | (n3) "n\<ge>3"
    by linarith
  thus False
  proof (cases)
    case n1
    thus ?thesis
      using One_nat_def card_Suc_eq ge2_events_lax singletonD assms(1)
      by (metis \<open>n = card Q\<close>)
  next
    case n2
    then obtain a b where "a\<noteq>b" and "a\<in>Q" and "b\<in>Q"
      using ge2_events_lax assms(1) by blast
    then obtain c where "c\<in>Q" and "c\<noteq>a" and "c\<noteq>b"
      using prolong_betw2 by (metis abc_abc_neq assms(1))
    hence "card Q \<noteq> 2"
      by (metis \<open>a \<in> Q\<close> \<open>a \<noteq> b\<close> \<open>b \<in> Q\<close> card_2_iff')
    thus False
      using \<open>n = card Q\<close> \<open>n = 2\<close> by blast
  next
    case n3
    have fin_Q: "finite Q"
    proof -
      have "(0::nat) \<noteq> 1"
        by simp
      then show ?thesis
        by (meson \<open>card Q \<noteq> 0\<close> card.infinite)
    qed
    have card_Q: "card Q \<ge> 3"
      using \<open>n = card Q\<close> n3 by blast
    have "Q\<subseteq>Q" by simp 
    then obtain a b where "a\<in>Q" and "b\<in>Q" and "a\<noteq>b"
        and acb: "\<forall>c\<in>Q. (c\<noteq>a \<and> c\<noteq>b) \<longrightarrow> [[a c b]]"
      using obtain_fin_path_ends card_Q fin_Q assms(1)
      by metis
    then obtain x where "[[a b x]]" and "x\<in>Q"
      using prolong_betw2 assms(1) by blast
    thus False
      by (metis acb abc_abc_neq abc_only_cba(2))
  qed
qed


theorem (*6ii*) infinite_paths:
  assumes "P\<in>\<P>"
  shows "infinite P"
proof
  assume fin_P: "finite P"
  have "P\<noteq>{}"
    by (simp add: assms)
  hence "card P \<noteq> 0"
    by (simp add: fin_P)
  moreover have "\<not>(card P \<ge> 1)"
    using path_card_nil
    by (simp add: assms)
  ultimately show False
    by simp
qed


end (* contex MinkowskiSpacetime *)


section "3.5 Second collinearity theorem"


text \<open>We start with a useful betweenness lemma.\<close>
lemma (in MinkowskiBetweenness) some_betw2:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
      and b_inQ: "b \<in> Q"
      and c_inQ: "c \<in> Q"
  shows "a = b \<or> a = c \<or> b = c \<or> [[a b c]] \<or> [[b c a]] \<or> [[c a b]]"
  using a_inQ b_inQ c_inQ path_Q some_betw by blast

lemma (in MinkowskiPrimitive) paths_tri:
  assumes path_ab: "path ab a b"
      and path_bc: "path bc b c"
      and path_ca: "path ca c a"
      and a_notin_bc: "a \<notin> bc"
  shows "\<triangle> a b c"
proof -
  have abc_events: "a \<in> \<E> \<and> b \<in> \<E> \<and> c \<in> \<E>"
    using path_ab path_bc path_ca in_path_event by auto
  have abc_neq: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c"
    using path_ab path_bc path_ca by auto
  have paths_neq: "ab \<noteq> bc \<and> ab \<noteq> ca \<and> bc \<noteq> ca"
    using a_notin_bc cross_once_notin path_ab path_bc path_ca by blast
  show ?thesis
    unfolding kinematic_triangle_def
    using abc_events abc_neq paths_neq path_ab path_bc path_ca
    by auto
qed

lemma (in MinkowskiPrimitive) paths_tri2:
  assumes path_ab: "path ab a b"
      and path_bc: "path bc b c"
      and path_ca: "path ca c a"
      and ab_neq_bc: "ab \<noteq> bc"
  shows "\<triangle> a b c"
by (meson ab_neq_bc cross_once_notin path_ab path_bc path_ca paths_tri)

text \<open>
  Schutz states it more like
   \<open>\<lbrakk>tri_abc; bcd; cea\<rbrakk> \<Longrightarrow> (path de d e \<longrightarrow> \<exists>f\<in>de. [[a f b]]\<and>[[d e f]])\<close>.
  Equivalent up to usage of \<open>impI\<close>.
\<close>

theorem (*7*) (in MinkowskiChain) collinearity2:
  assumes tri_abc: "\<triangle> a b c"
      and bcd: "[[b c d]]"
      and cea: "[[c e a]]"
      and path_de: "path de d e"
  shows "\<exists>f\<in>de. [[a f b]] \<and> [[d e f]]"
proof -
  obtain ab where path_ab: "path ab a b" using tri_abc triangle_paths_unique by blast
  then obtain f where afb: "[[a f b]]"
                  and f_in_de: "f \<in> de" using collinearity tri_abc path_de path_ab bcd cea by blast
  (* af will be used a few times, so obtain it here. *)
  obtain af where path_af: "path af a f" using abc_abc_neq afb betw_b_in_path path_ab by blast
  have "[[d e f]]"
  proof -
    have def_in_de: "d \<in> de \<and> e \<in> de \<and> f \<in> de" using path_de f_in_de by simp
    then have five_poss:"f = d \<or> f = e \<or> [[e f d]] \<or> [[f d e]] \<or> [[d e f]]"
        using path_de some_betw2 by blast
    have "f = d \<or> f = e \<longrightarrow> (\<exists>Q\<in>\<P>. a \<in> Q \<and> b \<in> Q \<and> c \<in> Q)"
        by (metis abc_abc_neq afb bcd betw_a_in_path betw_b_in_path cea path_ab)
    then have f_neq_d_e: "f \<noteq> d \<and> f \<noteq> e" using tri_abc
        using triangle_diff_paths by simp
    then consider "[[e f d]]" | "[[f d e]]" | "[[d e f]]" using five_poss by linarith
    thus ?thesis
    proof (cases)
      assume efd: "[[e f d]]"
      obtain dc where path_dc: "path dc d c" using abc_abc_neq abc_ex_path bcd by blast
      obtain ce where path_ce: "path ce c e" using abc_abc_neq abc_ex_path cea by blast
      have "dc\<noteq>ce"
        using bcd betw_a_in_path betw_c_in_path cea path_ce path_dc tri_abc triangle_diff_paths
        by blast
      hence "\<triangle> d c e"
        using paths_tri2 path_ce path_dc path_de by blast
      then obtain x where x_in_af: "x \<in> af"
                      and dxc: "[[d x c]]"
          using collinearity
                [where a = d and b = c and c = e and d = a and e = f and de = af]
                cea efd path_dc path_af by blast
      then have x_in_dc: "x \<in> dc" using betw_b_in_path path_dc by blast
      then have "x = b" using eq_paths by (metis path_af path_dc afb bcd tri_abc x_in_af
                                            betw_a_in_path betw_c_in_path triangle_diff_paths)
      then have "[[d b c]]" using dxc by simp
      then have "False" using bcd abc_only_cba [where a = b and b = c and c = d] by simp
      thus ?thesis by simp
    next
      assume fde: "[[f d e]]"
      obtain bd where path_bd: "path bd b d" using abc_abc_neq abc_ex_path bcd by blast
      obtain ea where path_ea: "path ea e a" using abc_abc_neq abc_ex_path_unique cea by blast
      obtain fe where path_fe: "path fe f e" using f_in_de f_neq_d_e path_de by blast
      have "fe\<noteq>ea"
        using tri_abc afb cea path_ea path_fe
        by (metis abc_abc_neq betw_a_in_path betw_c_in_path triangle_paths_neq)
      hence "\<triangle> e a f"
        by (metis path_unique path_af path_ea path_fe paths_tri2)
      then obtain y where y_in_bd: "y \<in> bd"
                      and eya: "[[e y a]]" thm collinearity
          using collinearity
                [where a = e and b = a and c = f and d = b and e = d and de = bd]
                afb fde path_bd path_ea by blast
      then have "y = c" by (metis (mono_tags, lifting)
                                  afb bcd cea path_bd tri_abc
                                  abc_ac_neq betw_b_in_path path_unique triangle_paths(2)
                                    triangle_paths_neq)
      then have "[[e c a]]" using eya by simp
      then have "False" using cea abc_only_cba [where a = c and b = e and c = a] by simp
      thus ?thesis by simp
    next
      assume "[[d e f]]"
      thus ?thesis by assumption
    qed
  qed
  thus ?thesis using afb f_in_de by blast
qed



section "3.6 Order on a path - Theorems 8 and 9"
context MinkowskiSpacetime begin

subsection \<open>Theorem 8 (as in Veblen (1911) Theorem 6)\<close>
text \<open>
  Note \<open>a'b'c'\<close> don't necessarily form a triangle, as there still needs to be paths between them.
\<close>


theorem (*8*) (in MinkowskiChain) tri_betw_no_path:
  assumes tri_abc: "\<triangle> a b c"
      and ab'c: "[[a b' c]]"
      and bc'a: "[[b c' a]]"
      and ca'b: "[[c a' b]]"
  shows "\<not> (\<exists>Q\<in>\<P>. a' \<in> Q \<and> b' \<in> Q \<and> c' \<in> Q)"
proof -
  have abc_a'b'c'_neq: "a \<noteq> a' \<and> a \<noteq> b' \<and> a \<noteq> c'
                      \<and> b \<noteq> a' \<and> b \<noteq> b' \<and> b \<noteq> c'
                      \<and> c \<noteq> a' \<and> c \<noteq> b' \<and> c \<noteq> c'"
      using abc_ac_neq
      by (metis ab'c abc_abc_neq bc'a ca'b tri_abc triangle_not_betw_abc triangle_permutes(4))
  show ?thesis
  proof (rule notI)
    assume path_a'b'c': "\<exists>Q\<in>\<P>. a' \<in> Q \<and> b' \<in> Q \<and> c' \<in> Q"
    consider "[[a' b' c']]" | "[[b' c' a']]" | "[[c' a' b']]" using some_betw
        by (smt abc_a'b'c'_neq path_a'b'c' bc'a ca'b ab'c tri_abc
                abc_ex_path cross_once_notin triangle_diff_paths)
    thus False
    proof (cases)
      assume a'b'c': "[[a' b' c']]"
      then have c'b'a': "[[c' b' a']]" using abc_sym by simp
      have nopath_a'c'b: "\<not> (\<exists>Q\<in>\<P>. a' \<in> Q \<and> c' \<in> Q \<and> b \<in> Q)"
      proof (rule notI)
        assume "\<exists>Q\<in>\<P>. a' \<in> Q \<and> c' \<in> Q \<and> b \<in> Q"
        then obtain Q where path_Q: "Q \<in> \<P>"
                        and a'_inQ: "a' \<in> Q"
                        and c'_inQ: "c' \<in> Q"
                        and b_inQ: "b \<in> Q" by blast
        then have ac_inQ: "a \<in> Q \<and> c \<in> Q" using eq_paths
            by (metis abc_a'b'c'_neq ca'b bc'a betw_a_in_path betw_c_in_path)
        thus False using b_inQ path_Q tri_abc triangle_diff_paths by blast
      qed
      then have tri_a'bc': "\<triangle> a' b c'"
          by (smt bc'a ca'b path_a'b'c' paths_tri abc_ex_path_unique)
      obtain ab' where path_ab': "path ab' a b'" using ab'c abc_a'b'c'_neq abc_ex_path by blast
      obtain a'b where path_a'b: "path a'b a' b" using tri_a'bc' triangle_paths(1) by blast
      then have "\<exists>x\<in>a'b. [[a' x b]] \<and> [[a b' x]]"
          using collinearity2 [where a = a' and b = b and c = c' and e = b' and d = a and de = ab']
                bc'a betw_b_in_path c'b'a' path_ab' tri_a'bc' by blast
      then obtain x where x_in_a'b: "x \<in> a'b"
                      and a'xb: "[[a' x b]]"
                      and ab'x: "[[a b' x]]" by blast
      (* ab' \<inter> a'b = {c} doesn't follow as immediately as in Schutz. *)
      have c_in_ab': "c \<in> ab'" using ab'c betw_c_in_path path_ab' by auto
      have c_in_a'b: "c \<in> a'b" using ca'b betw_a_in_path path_a'b by auto 
      have ab'_a'b_distinct: "ab' \<noteq> a'b"
          using c_in_a'b path_a'b path_ab' tri_abc triangle_diff_paths by blast
      have "ab' \<inter> a'b = {c}"
          using paths_cross_at ab'_a'b_distinct c_in_a'b c_in_ab' path_a'b path_ab' by auto
      then have "x = c" using ab'x path_ab' x_in_a'b betw_c_in_path by auto
      then have "[[a' c b]]" using a'xb by auto
      thus False using ca'b abc_only_cba by blast
    next
      assume b'c'a': "[[b' c' a']]"
      then have a'c'b': "[[a' c' b']]" using abc_sym by simp
      have nopath_a'cb': "\<not> (\<exists>Q\<in>\<P>. a' \<in> Q \<and> c \<in> Q \<and> b' \<in> Q)"
      proof (rule notI)
        assume "\<exists>Q\<in>\<P>. a' \<in> Q \<and> c \<in> Q \<and> b' \<in> Q"
        then obtain Q where path_Q: "Q \<in> \<P>"
                        and a'_inQ: "a' \<in> Q"
                        and c_inQ: "c \<in> Q"
                        and b'_inQ: "b' \<in> Q" by blast
        then have ab_inQ: "a \<in> Q \<and> b \<in> Q"
            using eq_paths
            by (metis ab'c abc_a'b'c'_neq betw_a_in_path betw_c_in_path ca'b)
        thus False using c_inQ path_Q tri_abc triangle_diff_paths by blast
      qed
      then have tri_a'cb': "\<triangle> a' c b'"
          by (smt ab'c abc_ex_path_unique b'c'a' ca'b paths_tri)
      obtain bc' where path_bc': "path bc' b c'"
          using abc_a'b'c'_neq abc_ex_path_unique bc'a
          by blast
      obtain b'c where path_b'c: "path b'c b' c" using tri_a'cb' triangle_paths(3) by blast
      then have "\<exists>x\<in>b'c. [[b' x c]] \<and> [[b c' x]]"
          using collinearity2 [where a = b' and b = c and c = a'
                                 and e = c' and d = b and de = bc']
                bc'a betw_b_in_path a'c'b' path_bc' tri_a'cb'
          by (meson ca'b triangle_permutes(5))
      then obtain x where x_in_b'c: "x \<in> b'c"
                      and b'xc: "[[b' x c]]"
                      and bc'x: "[[b c' x]]" by blast
      have a_in_bc': "a \<in> bc'" using bc'a betw_c_in_path path_bc' by blast
      have a_in_b'c: "a \<in> b'c" using ab'c betw_a_in_path path_b'c by blast
      have bc'_b'c_distinct: "bc' \<noteq> b'c"
          using a_in_bc' path_b'c path_bc' tri_abc triangle_diff_paths by blast
      have "bc' \<inter> b'c = {a}"
          using paths_cross_at bc'_b'c_distinct a_in_b'c a_in_bc' path_b'c path_bc' by auto
      then have "x = a" using bc'x betw_c_in_path path_bc' x_in_b'c by auto
      then have "[[b' a c]]" using b'xc by auto
      thus False using ab'c abc_only_cba by blast
    next
      assume c'a'b': "[[c' a' b']]"
      then have b'a'c': "[[b' a' c']]" using abc_sym by simp
      have nopath_c'ab': "\<not> (\<exists>Q\<in>\<P>. c' \<in> Q \<and> a \<in> Q \<and> b' \<in> Q)"
      proof (rule notI)
        assume "\<exists>Q\<in>\<P>. c' \<in> Q \<and> a \<in> Q \<and> b' \<in> Q"
        then obtain Q where path_Q: "Q \<in> \<P>"
                        and c'_inQ: "c' \<in> Q"
                        and a_inQ: "a \<in> Q"
                        and b'_inQ: "b' \<in> Q" by blast
        then have bc_inQ: "b \<in> Q \<and> c \<in> Q"
            using eq_paths ab'c abc_a'b'c'_neq bc'a betw_a_in_path betw_c_in_path by blast
        thus False using a_inQ path_Q tri_abc triangle_diff_paths by blast
      qed
      then have tri_a'cb': "\<triangle> b' a c'"
          by (smt bc'a abc_ex_path_unique c'a'b' ab'c paths_tri)
      obtain ca' where path_ca': "path ca' c a'"
          using abc_a'b'c'_neq abc_ex_path_unique ca'b
          by blast
      obtain c'a where path_c'a: "path c'a c' a" using tri_a'cb' triangle_paths(3) by blast
      then have "\<exists>x\<in>c'a. [[c' x a]] \<and> [[c a' x]]"
          using collinearity2 [where a = c' and b = a and c = b'
                                 and e = a' and d = c and de = ca']
                ab'c b'a'c' betw_b_in_path path_ca' tri_a'cb' triangle_permutes(5) by blast
      then obtain x where x_in_c'a: "x \<in> c'a"
                      and c'xa: "[[c' x a]]"
                      and ca'x: "[[c a' x]]" by blast
      have b_in_ca': "b \<in> ca'" using betw_c_in_path ca'b path_ca' by blast
      have b_in_c'a: "b \<in> c'a" using bc'a betw_a_in_path path_c'a by auto
      have ca'_c'a_distinct: "ca' \<noteq> c'a"
          using b_in_c'a path_c'a path_ca' tri_abc triangle_diff_paths by blast
      have "ca' \<inter> c'a = {b}"
          using b_in_c'a b_in_ca' ca'_c'a_distinct path_c'a path_ca' paths_cross_at by auto
      then have "x = b" using betw_c_in_path ca'x path_ca' x_in_c'a by auto
      then have "[[c' b a]]" using c'xa by auto
      thus False using abc_only_cba bc'a by blast
    qed
  qed
qed

subsection \<open>Theorem 9\<close>
text \<open>
  We now begin working on the transitivity lemmas needed to prove Theorem 9.
  Multiple lemmas below obtain primed variables (e.g. \<open>d'\<close>). These are starred in Schutz (e.g. \<open>d*\<close>),
  but that notation is already reserved in Isabelle.
\<close>

lemma unreachable_bounded_path_only:
  assumes d'_def: "d'\<notin> \<emptyset> ab e" "d'\<in>ab" "d'\<noteq>e"
      and e_event: "e \<in> \<E>"
      and path_ab: "ab \<in> \<P>"
      and e_notin_S: "e \<notin> ab"
  shows "\<exists>d'e. path d'e d' e"
proof (rule ccontr)
  assume "\<not>(\<exists>d'e. path d'e d' e)"
  hence "\<not>(\<exists>R\<in>\<P>. d'\<in>R \<and> e\<in>R \<and> d'\<noteq>e)"
    by blast
  hence "\<not>(\<exists>R\<in>\<P>.  e\<in>R \<and> d'\<in>R)"
    using d'_def(3) by blast
  moreover have "ab\<in>\<P> \<and> e\<in>\<E> \<and> e\<notin>ab"
    by (simp add: e_event e_notin_S path_ab)
  ultimately have "d'\<in> \<emptyset> ab e"
    unfolding unreachable_subset_def using d'_def(2)
    by blast
  thus False
    using d'_def(1) by auto
qed

lemma unreachable_bounded_path:
  assumes S_neq_ab: "S \<noteq> ab"
      and a_inS: "a \<in> S"
      and e_inS: "e \<in> S"
      and e_neq_a: "e \<noteq> a"
      and path_S: "S \<in> \<P>"
      and path_ab: "path ab a b"
      and path_be: "path be b e"
      and no_de: "\<not>(\<exists>de. path de d e)"
      and abd:"[[a b d]]"
    obtains d' d'e where "d'\<in>ab \<and> path d'e d' e \<and> [[b d d']]"
proof -
  have e_event: "e\<in>\<E>"
    using e_inS path_S by auto
  have "e\<notin>ab"
    using S_neq_ab a_inS e_inS e_neq_a eq_paths path_S path_ab by auto
  have "ab\<in>\<P> \<and> e\<notin>ab"
    using S_neq_ab a_inS e_inS e_neq_a eq_paths path_S path_ab
    by auto
  have "b \<in> ab - \<emptyset> ab e"
    using cross_in_reachable path_ab path_be
    by blast
  have "d \<in> \<emptyset> ab e"
    using no_de abd path_ab e_event \<open>e\<notin>ab\<close>
      betw_c_in_path unreachable_bounded_path_only
    by blast
  have  "\<exists>d' d'e. d'\<in>ab \<and> path d'e d' e \<and> [[b d d']]"
  proof -
    obtain d' where "[[b d d']]" "d'\<in>ab" "d'\<notin> \<emptyset> ab e" "b\<noteq>d'" "e\<noteq>d'"
      using unreachable_set_bounded \<open>b \<in> ab - \<emptyset> ab e\<close> \<open>d \<in> \<emptyset> ab e\<close> e_event \<open>e\<notin>ab\<close> path_ab
      by (metis DiffE)
    then obtain d'e where "path d'e d' e"
      using unreachable_bounded_path_only e_event \<open>e\<notin>ab\<close> path_ab
      by blast
    thus ?thesis
      using \<open>[[b d d']]\<close> \<open>d' \<in> ab\<close>
      by blast
  qed
  thus ?thesis
    using that by blast
qed

text \<open>
  This lemma collects the first three paragraphs of Schutz' proof of Theorem 9 - Lemma 1.
  Several case splits need to be considered, but have no further importance outside of this lemma:
  thus we parcel them away from the main proof.\<close>
lemma exist_c'd'_alt:
  assumes abc: "[[a b c]]"
      and abd: "[[a b d]]"
      and dbc: "[[d b c]]" (* the assumption that makes this False for ccontr! *)
      and c_neq_d: "c \<noteq> d"
      and path_ab: "path ab a b"
      and path_S: "S \<in> \<P>"
      and a_inS: "a \<in> S"
      and e_inS: "e \<in> S"
      and e_neq_a: "e \<noteq> a"
      and S_neq_ab: "S \<noteq> ab"
      and path_be: "path be b e"
  shows "\<exists>c' d'. \<exists>d'e c'e. c'\<in>ab \<and> d'\<in>ab
                        \<and> [[a b d']] \<and> [[c' b a]] \<and> [[c' b d']]
                        \<and> path d'e d' e \<and> path c'e c' e"
proof (cases)
  assume "\<exists>de. path de d e"
  then obtain de where "path de d e"
    by blast
  hence "[[a b d]] \<and> d\<in>ab"
    using abd betw_c_in_path path_ab by blast
  thus ?thesis
  proof (cases)
    assume "\<exists>ce. path ce c e"
    then obtain ce where "path ce c e" by blast
    have "c \<in> ab"
      using abc betw_c_in_path path_ab by blast
    thus ?thesis
      using \<open>[[a b d]] \<and> d \<in> ab\<close> \<open>\<exists>ce. path ce c e\<close> \<open>c \<in> ab\<close> \<open>path de d e\<close> abc abc_sym dbc
      by blast
  next
    assume "\<not>(\<exists>ce. path ce c e)"
    obtain c' c'e where "c'\<in>ab \<and> path c'e c' e \<and> [[b c c']]"
      using unreachable_bounded_path [where ab=ab and e=e and b=b and d=c and a=a and S=S and be=be]
        S_neq_ab \<open>\<not>(\<exists>ce. path ce c e)\<close> a_inS abc e_inS e_neq_a path_S path_ab path_be
    by (metis (mono_tags, lifting))
    hence "[[a b c']] \<and> [[d b c']]"
      using abc dbc by blast
    hence "[[c' b a]] \<and> [[c' b d]]"
      using theorem1 by blast
    thus ?thesis
      using \<open>[[a b d]] \<and> d \<in> ab\<close> \<open>c' \<in> ab \<and> path c'e c' e \<and> [[b c c']]\<close> \<open>path de d e\<close>
      by blast
  qed
next
  assume "\<not> (\<exists>de. path de d e)"
  obtain d' d'e where d'_in_ab: "d' \<in> ab"
                   and bdd': "[[b d d']]"
                   and "path d'e d' e"
    using unreachable_bounded_path [where ab=ab and e=e and b=b and d=d and a=a and S=S and be=be]
      S_neq_ab \<open>\<nexists>de. path de d e\<close> a_inS abd e_inS e_neq_a path_S path_ab path_be
    by (metis (mono_tags, lifting))
  hence "[[a b d']]" using abd by blast
  thus ?thesis
  proof (cases)
    assume "\<exists>ce. path ce c e"
    then obtain ce where "path ce c e" by blast
    have "c \<in> ab"
      using abc betw_c_in_path path_ab by blast
    thus ?thesis
      using \<open>[[a b d']]\<close> \<open>d' \<in> ab\<close> \<open>path ce c e\<close> \<open>c \<in> ab\<close> \<open>path d'e d' e\<close> abc abc_sym dbc
      by (meson abc_bcd_acd bdd')
  next
    assume "\<not>(\<exists>ce. path ce c e)"
    obtain c' c'e where "c'\<in>ab \<and> path c'e c' e \<and> [[b c c']]"
      using unreachable_bounded_path [where ab=ab and e=e and b=b and d=c and a=a and S=S and be=be]
        S_neq_ab \<open>\<not>(\<exists>ce. path ce c e)\<close> a_inS abc e_inS e_neq_a path_S path_ab path_be
    by (metis (mono_tags, lifting))
    hence "[[a b c']] \<and> [[d b c']]"
      using abc dbc by blast
    hence "[[c' b a]] \<and> [[c' b d]]"
      using theorem1 by blast
    thus ?thesis
      using \<open>[[a b d']]\<close> \<open>c' \<in> ab \<and> path c'e c' e \<and> [[b c c']]\<close> \<open>path d'e d' e\<close> bdd' d'_in_ab
      by blast
  qed
qed

lemma exist_c'd':
  assumes abc: "[[a b c]]"
      and abd: "[[a b d]]"
      and dbc: "[[d b c]]" (* the assumption that makes this False for ccontr! *)
      and path_S: "path S a e"
      and path_be: "path be b e"
      and S_neq_ab: "S \<noteq> path_of a b"
    shows "\<exists>c' d'. [[a b d']] \<and> [[c' b a]] \<and> [[c' b d']] \<and>
                   path_ex d' e \<and> path_ex c' e"
proof (cases "path_ex d e")
  let ?ab = "path_of a b"
  have "path_ex a b"
    using abc abc_abc_neq abc_ex_path by blast
  hence path_ab: "path ?ab a b" using path_of_ex by simp
  have "c\<noteq>d" using abc_ac_neq dbc by blast
  {
    case True
    then obtain de where "path de d e"
      by blast
    hence "[[a b d]] \<and> d\<in>?ab"
      using abd betw_c_in_path path_ab by blast
    thus ?thesis
    proof (cases "path_ex c e")
      case True
      then obtain ce where "path ce c e" by blast
      have "c \<in> ?ab"
        using abc betw_c_in_path path_ab by blast
      thus ?thesis
        using \<open>[[a b d]] \<and> d \<in> ?ab\<close> \<open>\<exists>ce. path ce c e\<close> \<open>c \<in> ?ab\<close> \<open>path de d e\<close> abc abc_sym dbc
        by blast
    next
      case False
      obtain c' c'e where "c'\<in>?ab \<and> path c'e c' e \<and> [[b c c']]"
        using unreachable_bounded_path [where ab="?ab" and e=e and b=b and d=c and a=a and S=S and be=be]
          S_neq_ab \<open>\<not>(\<exists>ce. path ce c e)\<close> abc path_S path_ab path_be
      by (metis (mono_tags, lifting))
      hence "[[a b c']] \<and> [[d b c']]"
        using abc dbc by blast
      hence "[[c' b a]] \<and> [[c' b d]]"
        using theorem1 by blast
      thus ?thesis
        using \<open>[[a b d]] \<and> d \<in> ?ab\<close> \<open>c' \<in> ?ab \<and> path c'e c' e \<and> [[b c c']]\<close> \<open>path de d e\<close>
        by blast
    qed
  } {
    case False
    obtain d' d'e where d'_in_ab: "d' \<in> ?ab"
                     and bdd': "[[b d d']]"
                     and "path d'e d' e"
      using unreachable_bounded_path [where ab="?ab" and e=e and b=b and d=d and a=a and S=S and be=be]
        S_neq_ab \<open>\<not>path_ex d e\<close> abd path_S path_ab path_be
      by (metis (mono_tags, lifting))
    hence "[[a b d']]" using abd by blast
    thus ?thesis
    proof (cases "path_ex c e")
      case True
      then obtain ce where "path ce c e" by blast
      have "c \<in> ?ab"
        using abc betw_c_in_path path_ab by blast
      thus ?thesis
        using \<open>[[a b d']]\<close> \<open>d' \<in> ?ab\<close> \<open>path ce c e\<close> \<open>c \<in> ?ab\<close> \<open>path d'e d' e\<close> abc abc_sym dbc
        by (meson abc_bcd_acd bdd')
    next
      case False
      obtain c' c'e where "c'\<in>?ab \<and> path c'e c' e \<and> [[b c c']]"
        using unreachable_bounded_path [where ab="?ab" and e=e and b=b and d=c and a=a and S=S and be=be]
          S_neq_ab \<open>\<not>(path_ex c e)\<close> abc path_S path_ab path_be
      by (metis (mono_tags, lifting))
      hence "[[a b c']] \<and> [[d b c']]"
        using abc dbc by blast
      hence "[[c' b a]] \<and> [[c' b d]]"
        using theorem1 by blast
      thus ?thesis
        using \<open>[[a b d']]\<close> \<open>c' \<in> ?ab \<and> path c'e c' e \<and> [[b c c']]\<close> \<open>path d'e d' e\<close> bdd' d'_in_ab
        by blast
    qed
  }
qed


lemma exist_f'_alt:
  assumes path_ab: "path ab a b"
      and path_S: "S \<in> \<P>"
      and a_inS: "a \<in> S"
      and e_inS: "e \<in> S"
      and e_neq_a: "e \<noteq> a"
      and f_def: "[[e c' f]]" "f\<in>c'e"
      and S_neq_ab: "S \<noteq> ab"
      and c'd'_def: "c'\<in>ab \<and> d'\<in>ab
            \<and> [[a b d']] \<and> [[c' b a]] \<and> [[c' b d']]
            \<and> path d'e d' e \<and> path c'e c' e"
    shows "\<exists>f'. \<exists>f'b. [[e c' f']] \<and> path f'b f' b"
proof (cases)
  assume "\<exists>bf. path bf b f"
  thus ?thesis
    using \<open>[[e c' f]]\<close> by blast
next
  assume "\<not>(\<exists>bf. path bf b f)"
  hence "f \<in> \<emptyset> c'e b"
    using assms(1-5,7-9) abc_abc_neq betw_events eq_paths unreachable_bounded_path_only
    by metis
  moreover have "c' \<in> c'e - \<emptyset> c'e b"
    using c'd'_def cross_in_reachable path_ab by blast
  moreover have "b\<in>\<E> \<and> b\<notin>c'e"
    using \<open>f \<in> \<emptyset> c'e b\<close> betw_events c'd'_def same_empty_unreach by auto
  ultimately obtain f' where f'_def: "[[c' f f']]" "f'\<in>c'e" "f'\<notin> \<emptyset> c'e b" "c'\<noteq>f'" "b\<noteq>f'"
    using unreachable_set_bounded c'd'_def
    by (metis DiffE)
  hence "[[e c' f']]"
    using \<open>[[e c' f]]\<close> by blast
  moreover obtain f'b where "path f'b f' b"
    using \<open>b \<in> \<E> \<and> b \<notin> c'e\<close> c'd'_def f'_def(2,3) unreachable_bounded_path_only
    by blast
  ultimately show ?thesis by blast
qed

lemma exist_f':
  assumes path_ab: "path ab a b"
      and path_S: "path S a e"
      and f_def: "[[e c' f]]"
      and S_neq_ab: "S \<noteq> ab"
      and c'd'_def: "[[a b d']]" "[[c' b a]]" "[[c' b d']]"
            "path d'e d' e" "path c'e c' e"
    shows "\<exists>f'. [[e c' f']] \<and> path_ex f' b"
proof (cases)
  assume "path_ex b f"
  thus ?thesis
    using f_def by blast
next
  assume no_path: "\<not>(path_ex b f)"
  have path_S_2: "S \<in> \<P>" "a \<in> S" "e \<in> S" "e \<noteq> a"
    using path_S by auto
  have "f\<in>c'e"
    using betw_c_in_path f_def c'd'_def(5) by blast
  have "c'\<in> ab" "d'\<in> ab"
    using betw_a_in_path betw_c_in_path c'd'_def(1,2) path_ab by blast+
  have "f \<in> \<emptyset> c'e b"
    using no_path assms(1,4-9) path_S_2 \<open>f\<in>c'e\<close> \<open>c'\<in>ab\<close> \<open>d'\<in>ab\<close>
      abc_abc_neq betw_events eq_paths unreachable_bounded_path_only
    by metis
  moreover have "c' \<in> c'e - \<emptyset> c'e b"
    using c'd'_def cross_in_reachable path_ab \<open>c' \<in> ab\<close> by blast
  moreover have "b\<in>\<E> \<and> b\<notin>c'e"
    using \<open>f \<in> \<emptyset> c'e b\<close> betw_events c'd'_def same_empty_unreach by auto
  ultimately obtain f' where f'_def: "[[c' f f']]" "f'\<in>c'e" "f'\<notin> \<emptyset> c'e b" "c'\<noteq>f'" "b\<noteq>f'"
    using unreachable_set_bounded c'd'_def
    by (metis DiffE)
  hence "[[e c' f']]"
    using \<open>[[e c' f]]\<close> by blast
  moreover obtain f'b where "path f'b f' b"
    using \<open>b \<in> \<E> \<and> b \<notin> c'e\<close> c'd'_def f'_def(2,3) unreachable_bounded_path_only
    by blast
  ultimately show ?thesis by blast
qed


lemma abc_abd_bcdbdc:
  assumes abc: "[[a b c]]"
      and abd: "[[a b d]]"
      and c_neq_d: "c \<noteq> d"
  shows "[[b c d]] \<or> [[b d c]]"
proof -
  have "\<not> [[d b c]]"
  proof (rule notI)
    assume dbc: "[[d b c]]"
    obtain ab where path_ab: "path ab a b"
      using abc_abc_neq abc_ex_path_unique abc by blast
    obtain S where path_S: "S \<in> \<P>" 
               and S_neq_ab: "S \<noteq> ab"
               and a_inS: "a \<in> S"
      using ex_crossing_at path_ab
      by auto
    (* This is not as immediate as Schutz presents it. *)
    have "\<exists>e\<in>S. e \<noteq> a \<and> (\<exists>be\<in>\<P>. path be b e)"
    proof -
      have b_notinS: "b \<notin> S" using S_neq_ab a_inS path_S path_ab path_unique by blast
      then obtain x y z where x_in_unreach: "x \<in> \<emptyset> S b"
                        and y_in_unreach: "y \<in> \<emptyset> S b"
                        and x_neq_y: "x \<noteq> y"
                        and z_in_reach: "z \<in> S - \<emptyset> S b"
        using two_in_unreach [where Q = S and b = b]
          in_path_event path_S path_ab a_inS cross_in_reachable
        by blast
      then obtain w where w_in_reach: "w \<in> S - \<emptyset> S b"
                      and w_neq_z: "w \<noteq> z"
          using unreachable_set_bounded [where Q = S and b = b and Qx = z and Qy = x]
                b_notinS in_path_event path_S path_ab by blast
      thus ?thesis by (metis DiffD1 b_notinS in_path_event path_S path_ab reachable_path z_in_reach)
    qed
    then obtain e be where e_inS: "e \<in> S"
                       and e_neq_a: "e \<noteq> a"
                       and path_be: "path be b e"
      by blast
    have path_ae: "path S a e"
      using a_inS e_inS e_neq_a path_S by auto
    have S_neq_ab_2: "S \<noteq> path_of a b"
      using S_neq_ab cross_once_notin path_ab path_of_ex by blast

    (* Obtain c' and d' as in Schutz (there called c* and d* ) *)
    have "\<exists>c' d'.
              c'\<in>ab \<and> d'\<in>ab
            \<and> [[a b d']] \<and> [[c' b a]] \<and> [[c' b d']]
            \<and> path_ex d' e \<and> path_ex c' e"
      using exist_c'd' [where a=a and b=b and c=c and d=d and e=e and be=be and S=S]
      using assms(1-2) dbc e_neq_a path_ae path_be S_neq_ab_2
      using abc_sym betw_a_in_path path_ab by blast
    then obtain c' d' d'e c'e
      where c'd'_def: "c'\<in>ab \<and> d'\<in>ab
            \<and> [[a b d']] \<and> [[c' b a]] \<and> [[c' b d']]
            \<and> path d'e d' e \<and> path c'e c' e"
      by blast

    (* Now obtain f' (called f* in Schutz) *)
    obtain f where f_def: "f\<in>c'e" "[[e c' f]]"
      using c'd'_def prolong_betw2 by blast
    then obtain f' f'b where f'_def: "[[e c' f']] \<and> path f'b f' b"
      using exist_f'
        [where e=e and c'=c' and b=b and f=f and S=S and ab=ab and d'=d' and a=a and c'e=c'e]
      using path_ab path_S a_inS e_inS e_neq_a f_def S_neq_ab c'd'_def
      by blast

    (* Now we follow Schutz, who follows Veblen. *)
    obtain ae where path_ae: "path ae a e" using a_inS e_inS e_neq_a path_S by blast
    have tri_aec: "\<triangle> a e c'"
        by (smt cross_once_notin S_neq_ab a_inS abc abc_abc_neq abc_ex_path
                e_inS e_neq_a path_S path_ab c'd'_def paths_tri)
    (* The second collinearity theorem doesn't explicitly capture the fact that it meets at
       ae, so Schutz misspoke, but maybe that's an issue with the statement of the theorem. *)
    then obtain h where h_in_f'b: "h \<in> f'b"
                    and ahe: "[[a h e]]"
                    and f'bh: "[[f' b h]]"
        using collinearity2 [where a = a and b = e and c = c' and d = f' and e = b and de = f'b]
              f'_def c'd'_def f'_def by blast
    have tri_dec: "\<triangle> d' e c'"
        using cross_once_notin S_neq_ab a_inS abc abc_abc_neq abc_ex_path
                e_inS e_neq_a path_S path_ab c'd'_def paths_tri by smt
    then obtain g where g_in_f'b: "g \<in> f'b"
                    and d'ge: "[[d' g e]]"
                    and f'bg: "[[f' b g]]"
        using collinearity2 [where a = d' and b = e and c = c' and d = f' and e = b and de = f'b]
              f'_def c'd'_def by blast
    have "\<triangle> e a d'" by (smt betw_c_in_path paths_tri2 S_neq_ab a_inS abc_ac_neq
                           abd e_inS e_neq_a c'd'_def path_S path_ab)
    thus False
      using tri_betw_no_path [where a = e and b = a and c = d' and b' = g and a' = b and c' = h]
        f'_def c'd'_def h_in_f'b g_in_f'b abd d'ge ahe abc_sym
      by blast
  qed
  thus ?thesis
    by (smt abc abc_abc_neq abc_ex_path abc_sym abd c_neq_d cross_once_notin some_betw)
qed


(* Lemma 2-3.6. *)
lemma abc_abd_acdadc:
  assumes abc: "[[a b c]]"
      and abd: "[[a b d]]"
      and c_neq_d: "c \<noteq> d"
  shows "[[a c d]] \<or> [[a d c]]"
proof -
  have cba: "[[c b a]]" using abc_sym abc by simp
  have dba: "[[d b a]]" using abc_sym abd by simp
  (* This goes through so easily because the overlapping betweenness axiom is an intro rule.
     Adding it here to more closely match Schutz. *)
  have dcb_over_cba: "[[d c b]] \<and> [[c b a]] \<Longrightarrow> [[d c a]]" by auto
  have cdb_over_dba: "[[c d b]] \<and> [[d b a]] \<Longrightarrow> [[c d a]]" by auto

  have bcdbdc: "[[b c d]] \<or> [[b d c]]" using abc abc_abd_bcdbdc abd c_neq_d by auto
  then have dcb_or_cdb: "[[d c b]] \<or> [[c d b]]" using abc_sym by blast
  then have "[[d c a]] \<or> [[c d a]]" using abc_only_cba dcb_over_cba cdb_over_dba cba dba by blast
  thus ?thesis using abc_sym by auto
qed

(* Lemma 3-3.6. *)
lemma abc_acd_bcd:
  assumes abc: "[[a b c]]"
      and acd: "[[a c d]]"
  shows "[[b c d]]"
proof -
  have path_abc: "\<exists>Q\<in>\<P>. a \<in> Q \<and> b \<in> Q \<and> c \<in> Q" using abc by (simp add: abc_ex_path)
  have path_acd: "\<exists>Q\<in>\<P>. a \<in> Q \<and> c \<in> Q \<and> d \<in> Q" using acd by (simp add: abc_ex_path)
  then have "\<exists>Q\<in>\<P>. b \<in> Q \<and> c \<in> Q \<and> d \<in> Q" using path_abc abc_abc_neq acd cross_once_notin by metis 
  (* Schutz implicitly assumes this. *)
  then have bcd3: "[[b c d]] \<or> [[b d c]] \<or> [[c b d]]" by (metis abc abc_only_cba(1,2) acd some_betw2)
  show ?thesis
  proof (rule ccontr)
    assume "\<not> [[b c d]]"
    then have "[[b d c]] \<or> [[c b d]]" using bcd3 by simp
    thus False
    proof (rule disjE)
      assume "[[b d c]]"
      then have "[[c d b]]" using abc_sym by simp
      then have "[[a c b]]" using acd abc_bcd_abd by blast
      thus False using abc abc_only_cba by blast
    next
      assume cbd: "[[c b d]]"
      have cba: "[[c b a]]" using abc abc_sym by blast
      have a_neq_d: "a \<noteq> d" using abc_ac_neq acd by auto
      then have "[[c a d]] \<or> [[c d a]]" using abc_abd_acdadc cbd cba by simp
      thus False using abc_only_cba acd by blast
    qed
  qed
qed

text \<open>
  A few lemmas that don't seem to be proved by Schutz, but can be proven now, after Lemma 3.
  These sometimes avoid us having to construct a chain explicitly.
\<close>
lemma abd_bcd_abc:
  assumes abd: "[[a b d]]"
      and bcd: "[[b c d]]"
  shows "[[a b c]]"
proof -
  have dcb: "[[d c b]]" using abc_sym bcd by simp
  have dba: "[[d b a]]" using abc_sym abd by simp
  have "[[c b a]]" using abc_acd_bcd dcb dba by blast
  thus ?thesis using abc_sym by simp
qed

lemma abc_acd_abd:
  assumes abc: "[[a b c]]"
      and acd: "[[a c d]]"
    shows "[[a b d]]"
  using abc abc_acd_bcd acd by blast

lemma abd_acd_abcacb:
  assumes abd: "[[a b d]]"
      and acd: "[[a c d]]"
      and bc: "b\<noteq>c"
    shows "[[a b c]] \<or> [[a c b]]"
proof -
  obtain P where P_def: "P\<in>\<P>" "a\<in>P" "b\<in>P" "d\<in>P"
    using abd abc_ex_path by blast
  hence "c\<in>P"
    using acd abc_abc_neq betw_b_in_path by blast
  have "\<not>[[b a c]]"
    using abc_only_cba abd acd by blast
  thus ?thesis
    by (metis P_def(1-3) \<open>c \<in> P\<close> abc_abc_neq abc_sym abd acd bc some_betw)
qed

lemma abe_ade_bcd_ace:
  assumes abe: "[[a b e]]"
      and ade: "[[a d e]]"
      and bcd: "[[b c d]]"
    shows "[[a c e]]"
proof -
  have abdadb: "[[a b d]] \<or> [[a d b]]"
    using abc_ac_neq abd_acd_abcacb abe ade bcd by auto
  thus ?thesis
  proof
    assume "[[a b d]]" thus ?thesis
      by (meson abc_acd_abd abc_sym ade bcd)
  next assume "[[a d b]]" thus ?thesis
      by (meson abc_acd_abd abc_sym abe bcd)
  qed
qed

text \<open>Now we start on Theorem 9. Based on Veblen (1904) Lemma 2 p357.\<close>

lemma (in MinkowskiBetweenness) chain3:
  assumes path_Q: "Q \<in> \<P>"
      and a_inQ: "a \<in> Q"
      and b_inQ: "b \<in> Q"
      and c_inQ: "c \<in> Q"
      and abc_neq: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c"
  shows "ch {a,b,c}"
proof -
  have abc_betw: "[[a b c]] \<or> [[a c b]] \<or> [[b a c]]"
    using assms by (meson in_path_event abc_sym some_betw insert_subset)
  have ch1: "[[a b c]] \<longrightarrow> ch {a,b,c}"
    using abc_abc_neq ch_by_ord_def ch_def ord_ordered between_chain by auto
  have ch2: "[[a c b]] \<longrightarrow> ch {a,c,b}"
    using abc_abc_neq ch_by_ord_def ch_def ord_ordered between_chain by auto
  have ch3: "[[b a c]] \<longrightarrow> ch {b,a,c}"
    using abc_abc_neq ch_by_ord_def ch_def ord_ordered between_chain by auto
  show ?thesis
    using abc_betw ch1 ch2 ch3 by (metis insert_commute)
qed

text \<open>
  The book introduces Theorem 9 before the above three lemmas but can only complete the proof
  once they are proven.
  This doesn't exactly say it the same way as the book, as the book gives the ordering (abcd)
  explicitly (for arbitrarly named events), but is equivalent.
\<close>

theorem (*9*) chain4:
  assumes path_Q: "Q \<in> \<P>"
      and inQ: "a \<in> Q" "b \<in> Q" "c \<in> Q" "d \<in> Q"
      and abcd_neq: "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d"
    shows "ch {a,b,c,d}"
proof -
  obtain a' b' c' where a'_pick: "a' \<in> {a,b,c,d}"
                    and b'_pick: "b' \<in> {a,b,c,d}"
                    and c'_pick: "c' \<in> {a,b,c,d}"
                    and a'b'c': "[[a' b' c']]"
      using some_betw by (metis inQ(1,2,4) abcd_neq insert_iff path_Q)
  then obtain d' where d'_neq: "d' \<noteq> a' \<and> d' \<noteq> b' \<and> d' \<noteq> c'"
                   and d'_pick: "d' \<in> {a,b,c,d}"
    using insert_iff abcd_neq by metis
  have all_picked_on_path: "a'\<in>Q" "b'\<in>Q" "c'\<in>Q" "d'\<in>Q"
    using a'_pick b'_pick c'_pick d'_pick inQ by blast+
  consider "[[d' a' b']]" | "[[a' d' b']]" | "[[a' b' d']]"
    using some_betw abc_only_cba all_picked_on_path(1,2,4)
    by (metis a'b'c' d'_neq path_Q)
  then have picked_chain: "ch {a',b',c',d'}"
  proof (cases)
    assume "[[d' a' b']]"
    thus ?thesis using a'b'c' overlap_chain by (metis (full_types) insert_commute)
  next
    assume a'd'b': "[[a' d' b']]"
    then have "[[d' b' c']]" using abc_acd_bcd a'b'c' by blast
    thus ?thesis using a'd'b' overlap_chain by (metis (full_types) insert_commute)
  next
    assume a'b'd': "[[a' b' d']]"
    then have two_cases: "[[b' c' d']] \<or> [[b' d' c']]" using abc_abd_bcdbdc a'b'c' d'_neq by blast
    (* Doing it this way avoids SMT. *)
    have case1: "[[b' c' d']] \<Longrightarrow> ?thesis" using a'b'c' overlap_chain by blast
    have case2: "[[b' d' c']] \<Longrightarrow> ?thesis"
        using abc_only_cba abc_acd_bcd a'b'd' overlap_chain
        by (metis (full_types) insert_commute)
    show ?thesis using two_cases case1 case2 by blast
  qed
  have "{a',b',c',d'} = {a,b,c,d}"
  proof (rule Set.set_eqI, rule iffI)
    fix x
    assume "x \<in> {a',b',c',d'}"
    thus "x \<in> {a,b,c,d}" using a'_pick b'_pick c'_pick d'_pick by auto
  next
    fix x
    assume x_pick: "x \<in> {a,b,c,d}"
    have "a' \<noteq> b' \<and> a' \<noteq> c' \<and> a' \<noteq> d' \<and> b' \<noteq> c' \<and> c' \<noteq> d'"
        using a'b'c' abc_abc_neq d'_neq by blast
    thus "x \<in> {a',b',c',d'}"
        using a'_pick b'_pick c'_pick d'_pick x_pick d'_neq by auto
  qed
  thus ?thesis using picked_chain by simp
qed


end (* context MinkowskiSpacetime *)


section "Interlude - Chains and Equivalences"
text \<open>
  This section is meant for our alternative definitions of chains, and proofs of equivalence.
  If we want to regain full independence of our axioms, we probably need to shuffle a few
  things around. Some of this may be redundant, but is kept for compatibility with legacy proofs.

  Three definitions are given (cf `Betweenness: Chains` in Minkowski.thy):
   - one relying on explicit betweenness conditions
   - one relying on a total ordering and explicit indexing
   - one equivalent to the above except for use of the weaker, local-only ordering2
\<close>

context MinkowskiChain begin

subsection "Proofs for totally ordered index-chains"

subsubsection "General results"

lemma inf_chain_is_long:
  assumes "semifin_chain f x X"
  shows "long_ch_by_ord f X \<and> f 0 = x \<and> infinite X"
proof - 
  have "infinite X \<longrightarrow> card X \<noteq> 2" using card.infinite by simp
  hence "semifin_chain f x X \<longrightarrow> long_ch_by_ord f X"
    using long_ch_by_ord_def semifin_chain_def short_ch_def
    by simp
  thus ?thesis using assms semifin_chain_def by blast
qed

text \<open>A reassurance that the starting point $x$ is implied.\<close>
lemma long_inf_chain_is_semifin:
  assumes "long_ch_by_ord f X \<and> infinite X"
  shows "\<exists> x. [f[x..]X]"
  by (simp add: assms semifin_chain_def)

lemma endpoint_in_semifin:
  assumes "semifin_chain f x X"
    shows "x\<in>X"
  using assms semifin_chain_def zero_into_ordering inf_chain_is_long long_ch_by_ord_def
  by (metis finite.emptyI)

lemma three_in_long_chain:
  assumes "long_ch_by_ord f X" and fin: "finite X"
  obtains x y z where "x\<in>X" and "y\<in>X" and "z\<in>X" and "x\<noteq>y" and "x\<noteq>z" and "y\<noteq>z"
    using assms(1) long_ch_by_ord_def by auto

subsubsection "Index-chains lie on paths"

lemma all_aligned_on_semifin_chain:
  assumes "[f[x..]X]"
  and a: "y\<in>X" and b:"z\<in>X" and xy: "x\<noteq>y" and xz: "x\<noteq>z" and yz: "y\<noteq>z" 
  shows "[[x y z]] \<or> [[x z y]]"
proof -
    obtain n\<^sub>y n\<^sub>z where "f n\<^sub>y = y" and "f n\<^sub>z = z"
      by (metis TernaryOrdering.ordering_def a assms(1) b inf_chain_is_long long_ch_by_ord_def)
    have "(0<n\<^sub>y \<and> n\<^sub>y<n\<^sub>z) \<or> (0<n\<^sub>z \<and> n\<^sub>z<n\<^sub>y)"
      using \<open>f n\<^sub>y = y\<close> \<open>f n\<^sub>z = z\<close> assms less_linear semifin_chain_def xy xz yz  by auto
    hence "[[(f 0) (f n\<^sub>y) (f n\<^sub>z)]] \<or> [[(f 0) (f n\<^sub>z) (f n\<^sub>y)]]"
      using ordering_def assms(1) long_ch_by_ord_def semifin_chain_def
      by (metis long_ch_by_ord_def)
    thus "[[x y z]] \<or> [[x z y]]"
      using \<open>f n\<^sub>y = y\<close> \<open>f n\<^sub>z = z\<close> assms semifin_chain_def by auto
  qed


lemma semifin_chain_on_path:
  assumes "[f[x..]X]"
  shows "\<exists>P\<in>\<P>. X\<subseteq>P"
proof -
  obtain y where "y\<in>X" and "y\<noteq>x"
    using assms inf_chain_is_long
    by (metis Diff_iff all_not_in_conv finite_Diff2 finite_insert infinite_imp_nonempty insert_iff)
  have path_exists: "\<exists>P\<in>\<P>. path P x y"
  proof -
    obtain e where "e\<in>X" and "e\<noteq>x" and "e\<noteq>y" and "[[x y e]] \<or> [[x e y]]"
      using all_aligned_on_semifin_chain inf_chain_is_long long_ch_by_ord_def assms
            ordering_def lessI \<open>y \<in> X\<close> \<open>y \<noteq> x\<close> finite.emptyI finite_insert
            finite_subset insert_iff subsetI
      by smt
    obtain P where "path P x y"
      using \<open>[[x y e]] \<or> [[x e y]]\<close> abc_abc_neq abc_ex_path
      by blast
    show ?thesis
      using \<open>path P x y\<close>
      by blast
  qed
  obtain P where "path P x y"
    using path_exists
    by blast
  have "X\<subseteq>P"
  proof
    fix e
    assume "e\<in>X"
    show "e\<in>P"
    proof -
      have "e=x \<or> e=y \<or> (e\<noteq>x \<and> e\<noteq>y)" by auto
      moreover { assume "e\<noteq>x \<and> e\<noteq>y"
        have "[[x y e]] \<or> [[x e y]]"
          using all_aligned_on_semifin_chain assms
                \<open>e \<in> X\<close> \<open>e \<noteq> x \<and> e \<noteq> y\<close> \<open>y \<in> X\<close> \<open>y \<noteq> x\<close>
          by blast
        hence ?thesis
          using \<open>path P x y\<close> abc_ex_path path_unique
          by blast
      } moreover { assume "e=x"
        have ?thesis
          by (simp add: \<open>e = x\<close> \<open>path P x y\<close>)
      } moreover { assume "e=y"
        have "e\<in>P"
          by (simp add: \<open>e = y\<close> \<open>path P x y\<close>)
      }
      ultimately show ?thesis by blast
    qed
  qed
  thus ?thesis
    using \<open>path P x y\<close>
    by blast
qed


lemma card2_either_elt1_or_elt2:
  assumes "card X = 2" and "x\<in>X" and "y\<in>X" and "x\<noteq>y"
    and "z\<in>X" and "z\<noteq>x"
  shows "z=y"
by (metis assms card_2_iff')

lemma short_chain_on_path:
  assumes "short_ch X"
  shows "\<exists>P\<in>\<P>. X\<subseteq>P"
proof -
  obtain x y where "x\<noteq>y" and "x\<in>X" and "y\<in>X"
    using assms short_ch_def by auto
  obtain P where "path P x y"
    using \<open>x \<in> X\<close> \<open>x \<noteq> y\<close> \<open>y \<in> X\<close> assms short_ch_def
    by metis
  have "X\<subseteq>P"
  proof
    fix z
    assume "z\<in>X"
    show "z\<in>P"
    proof cases
      assume "z=x"
      show "z\<in>P" using \<open>path P x y\<close> by (simp add: \<open>z=x\<close>)
    next
      assume "z\<noteq>x"
      have "z=y"
        using \<open>x\<in>X\<close> \<open>y\<in>X\<close> \<open>z\<noteq>x\<close> \<open>z\<in>X\<close> \<open>x\<noteq>y\<close> assms short_ch_def
        by metis
      thus "z\<in>P" using \<open>path P x y\<close> by (simp add: \<open>z=y\<close>)
    qed
  qed
  thus ?thesis
    using \<open>path P x y\<close> by blast
qed


lemma all_aligned_on_long_chain:
  assumes "long_ch_by_ord f X" and "finite X"
  and a: "x\<in>X" and b: "y\<in>X" and c:"z\<in>X" and xy: "x\<noteq>y" and xz: "x\<noteq>z" and yz: "y\<noteq>z" 
shows "[[x y z]] \<or> [[x z y]] \<or> [[z x y]]"
proof -
  obtain n\<^sub>x n\<^sub>y n\<^sub>z where fx: "f n\<^sub>x = x" and fy: "f n\<^sub>y = y" and fz: "f n\<^sub>z = z"
                    and xx: "n\<^sub>x < card X" and yy: "n\<^sub>y < card X" and zz: "n\<^sub>z < card X"
  proof -
    assume a1: "\<And>n\<^sub>x n\<^sub>y n\<^sub>z. \<lbrakk>f n\<^sub>x = x; f n\<^sub>y = y; f n\<^sub>z = z; n\<^sub>x < card X; n\<^sub>y < card X; n\<^sub>z < card X\<rbrakk> \<Longrightarrow> thesis"
    obtain nn :: "'a set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> nat" where
      "\<And>a A f p pa. (a \<notin> A \<or> \<not> ordering f p A \<or> f (nn A f a) = a)
                  \<and> (infinite A \<or> a \<notin> A \<or> \<not> ordering f pa A \<or> nn A f a < card A)"
      by (metis (no_types) ordering_def)
    then show ?thesis
      using a1 by (metis a assms(1) assms(2) b c long_ch_by_ord_def)
  qed
  have less_or: "(n\<^sub>x<n\<^sub>y \<and> n\<^sub>y<n\<^sub>z) \<or> (n\<^sub>x<n\<^sub>z \<and> n\<^sub>z<n\<^sub>y) \<or> (n\<^sub>z<n\<^sub>x \<and> n\<^sub>x<n\<^sub>y) \<or>
        (n\<^sub>z<n\<^sub>y \<and> n\<^sub>y<n\<^sub>x) \<or> (n\<^sub>y<n\<^sub>z \<and> n\<^sub>z<n\<^sub>x) \<or> (n\<^sub>y<n\<^sub>x \<and> n\<^sub>x<n\<^sub>z)"
    using fx fy fz assms less_linear
    by metis
  have int_imp_1: "(n\<^sub>x<n\<^sub>y \<and> n\<^sub>y<n\<^sub>z) \<and> long_ch_by_ord f X \<and> n\<^sub>z < card X \<longrightarrow> [[(f n\<^sub>x) (f n\<^sub>y) (f n\<^sub>z)]]"
    using assms long_ch_by_ord_def ordering_def
    by metis
  hence "[[(f n\<^sub>x) (f n\<^sub>y) (f n\<^sub>z)]] \<or> [[(f n\<^sub>x) (f n\<^sub>z) (f n\<^sub>y)]] \<or> [[(f n\<^sub>z) (f n\<^sub>x) (f n\<^sub>y)]] \<or>
         [[(f n\<^sub>z) (f n\<^sub>y) (f n\<^sub>x)]] \<or> [[(f n\<^sub>y) (f n\<^sub>z) (f n\<^sub>x)]] \<or> [[(f n\<^sub>y) (f n\<^sub>x) (f n\<^sub>z)]]"
  proof -
    have f1: "\<And>n na nb. \<not> n < na \<or> \<not> nb < n \<or> \<not> na < card X \<or> [[(f nb) (f n) (f na)]]"
      by (metis (no_types) ordering_def \<open>long_ch_by_ord f X\<close> long_ch_by_ord_def)
    then have f2: "\<not> n\<^sub>z < n\<^sub>y \<or> \<not> n\<^sub>x < n\<^sub>z \<or> [[x z y]]"
      using fx fy fz yy
      by blast
    have "\<not> n\<^sub>x < n\<^sub>y \<or> \<not> n\<^sub>z < n\<^sub>x \<or> [[z x y]]"
      using f1 fx fy fz yy by blast
    then show ?thesis
      using f2 f1 fx fy fz less_or xx zz by auto
  qed
  hence "[[x y z]] \<or> [[x z y]] \<or> [[z x y]] \<or>
         [[z y x]] \<or> [[y z x]] \<or> [[y x z]]"
    using fx fy fz assms semifin_chain_def long_ch_by_ord_def
    by metis
  thus ?thesis
    using abc_sym
    by blast
qed


lemma long_chain_on_path:
  assumes "long_ch_by_ord f X" and "finite X"
  shows "\<exists>P\<in>\<P>. X\<subseteq>P"
proof -
  obtain x y where "x\<in>X" and "y\<in>X" and "y\<noteq>x"
    using long_ch_by_ord_def assms
    by (metis (mono_tags, hide_lams))
  obtain z where "z\<in>X" and "x\<noteq>z" and "y\<noteq>z"
    using long_ch_by_ord_def assms
    by metis
  have "[[x y z]] \<or> [[x z y]] \<or> [[z x y]]"
    using all_aligned_on_long_chain assms
    using \<open>x \<in> X\<close> \<open>x \<noteq> z\<close> \<open>y \<in> X\<close> \<open>y \<noteq> x\<close> \<open>y \<noteq> z\<close> \<open>z \<in> X\<close>
    by auto
  then have path_exists: "\<exists>P\<in>\<P>. path P x y"
    using all_aligned_on_long_chain abc_ex_path
    by (metis \<open>y \<noteq> x\<close>)
  obtain P where "path P x y"
    using path_exists
    by blast
  have "X\<subseteq>P"
  proof
    fix e
    assume "e\<in>X"
    show "e\<in>P"
    proof -
      have "e=x \<or> e=y \<or> (e\<noteq>x \<and> e\<noteq>y)" by auto
      moreover {
        assume "e\<noteq>x \<and> e\<noteq>y"
        have "[[x y e]] \<or> [[x e y]] \<or> [[e x y]]"
          using all_aligned_on_long_chain all_aligned_on_long_chain assms
                \<open>e \<in> X\<close> \<open>e \<noteq> x \<and> e \<noteq> y\<close> \<open>y \<in> X\<close> \<open>y \<noteq> x\<close> \<open>x\<in>X\<close>
          by metis
        hence ?thesis
          using \<open>path P x y\<close> abc_ex_path path_unique
          by blast
      }
      moreover {
        assume "e=x"
        have ?thesis
          by (simp add: \<open>e = x\<close> \<open>path P x y\<close>)
      }
      moreover {
        assume "e=y"
        have "e\<in>P"
          by (simp add: \<open>e = y\<close> \<open>path P x y\<close>)
      }
      ultimately show ?thesis by blast
    qed
  qed
  thus ?thesis
    using \<open>path P x y\<close>
    by blast
qed

text \<open>
  Notice that this whole proof would be unnecessary if including path-belongingness in the
  definition, as Schutz does. This would also keep path-belongingness independent of axiom O1 and O4,
  thus enabling an independent statement of axiom O6, which perhaps we now lose. In exchange,
  our definition is slightly weaker (for \<open>card X \<ge> 3\<close> and \<open>infinite X\<close>).
\<close>

lemma chain_on_path:
  assumes "ch_by_ord f X"
  shows "\<exists>P\<in>\<P>. X\<subseteq>P"
  using assms ch_by_ord_def
  using semifin_chain_on_path long_chain_on_path short_chain_on_path long_inf_chain_is_semifin
  by meson

subsubsection "More general results"

(* In fact, it is xor. *)
lemma ch_some_betw: "\<lbrakk>x \<in> X; y \<in> X; z \<in> X; x \<noteq> y; x \<noteq> z; y \<noteq> z; ch X\<rbrakk>
        \<Longrightarrow> [[x y z]] \<or> [[y x z]] \<or> [[y z x]]"
proof -
  assume asm: "x \<in> X" "y \<in> X" "z \<in> X" "x \<noteq> y" "x \<noteq> z" "y \<noteq> z" "ch X"
  {
    fix f assume f_def: "long_ch_by_ord f X"
    assume evts: "x \<in> X" "y \<in> X" "z \<in> X" "x \<noteq> y" "x \<noteq> z" "y \<noteq> z"
    assume ords: "\<not> [[x y z]]" "\<not> [[y z x]]"
    obtain P where "X\<subseteq>P" "P\<in>\<P>"
      using chain_on_path f_def ch_by_ord_def
      by meson
    have "[[y x z]]"
    proof -
      have f1: "\<forall>A Aa a. \<not> A \<subseteq> Aa \<or> (a::'a) \<notin> A \<or> a \<in> Aa"
        by blast
      have f2: "y \<in> P"
        using \<open>X \<subseteq> P\<close> evts(2) by blast
      have f3: "x \<in> P"
        using f1 by (metis \<open>X \<subseteq> P\<close> evts(1))
      have "z \<in> P"
        using \<open>X \<subseteq> P\<close> evts(3) by blast
      then show ?thesis
        using f3 f2 by (metis some_betw_xor \<open>P \<in> \<P>\<close> abc_sym evts(4,5,6) ords)
    qed
  }
  thus ?thesis
    unfolding ch_def long_ch_by_ord_def ch_by_ord_def ordering_def short_ch_def
    using asm ch_by_ord_def ch_def short_ch_def
    by (metis \<open>\<And>f. \<lbrakk>long_ch_by_ord f X; x \<in> X; y \<in> X; z \<in> X; x \<noteq> y; x \<noteq> z; y \<noteq> z;
      \<not> [[x y z]]; \<not> [[y z x]]\<rbrakk> \<Longrightarrow> [[y x z]]\<close>)
qed


lemma ch_all_betw_f:
  assumes "[f[x..yy..z]X]" and "y\<in>X" and "y\<noteq>x" and "y\<noteq>z"
  shows "[[x y z]]"
proof (rule ccontr)
  assume asm: "\<not> [[x y z]]"
  obtain Q where "Q\<in>\<P>" and "x\<in>Q \<and> y\<in>Q \<and> z\<in>Q"
    using chain_on_path assms ch_by_ord_def asm fin_ch_betw fin_long_chain_def
    by auto
  hence "[[x y z]] \<or> [[y x z]] \<or> [[y z x]]"
    using some_betw assms
    by (metis abc_sym fin_long_chain_def)
  hence "[[y x z]] \<or> [[x z y]]"
    using asm abc_sym
    by blast
  thus False
    using fin_long_chain_def long_ch_by_ord_def asm assms fin_ch_betw
    by (metis (no_types, hide_lams))
qed

(* potential misnomer: Schutz defines bounds only for infinite chains *)
lemma get_fin_long_ch_bounds:
  assumes "long_ch_by_ord f X"
      and "finite X"
    shows "\<exists>x\<in>X. \<exists>y\<in>X. \<exists>z\<in>X. [f[x..y..z]X]"
proof -
  obtain x where "x = f 0" by simp
  obtain z where "z = f (card X - 1)" by simp
  obtain y where y_def: "y\<noteq>x \<and> y\<noteq>z \<and> y\<in>X"
    by (metis assms(1) long_ch_by_ord_def)
  have "x\<in>X"
    using ordering_def \<open>x = f 0\<close> assms(1) long_ch_by_ord_def
    by (metis card_gt_0_iff equals0D)
  have "z\<in>X"
    using ordering_def \<open>z = f (card X - 1)\<close> assms(1) long_ch_by_ord_def
    by (metis card_gt_0_iff equals0D Suc_diff_1 lessI)
  obtain n where "n<card X" and "f n = y"
    using ordering_def y_def long_ch_by_ord_def assms
    by metis
  have "n>0"
    using y_def \<open>f n = y\<close> \<open>x = f 0\<close>
    using neq0_conv by blast
  moreover have "n<card X - 1"
    using y_def \<open>f n = y\<close> \<open>n < card X\<close> \<open>z = f (card X - 1)\<close> assms(2)
    by (metis card.remove card_Diff_singleton less_SucE)
  ultimately have "[f[x..y..z]X]"
    using long_ch_by_ord_def y_def \<open>x = f 0\<close> \<open>z = f (card X - 1)\<close> abc_abc_neq assms ordering_ord_ijk
    unfolding fin_long_chain_def
    by (metis (no_types, lifting) card_gt_0_iff diff_less equals0D zero_less_one)
  thus ?thesis
    using points_in_chain
    by blast
qed

lemma get_fin_long_ch_bounds2:
  assumes "long_ch_by_ord f X"
      and "finite X"
    obtains x y z n\<^sub>x n\<^sub>y n\<^sub>z
    where "x\<in>X \<and> y\<in>X \<and> z\<in>X \<and> [f[x..y..z]X] \<and> f n\<^sub>x = x \<and> f n\<^sub>y = y \<and> f n\<^sub>z = z"
  by (meson assms(1) assms(2) fin_long_chain_def get_fin_long_ch_bounds index_middle_element)

lemma long_ch_card_ge3:
  assumes "ch_by_ord f X" "finite X"
  shows "long_ch_by_ord f X \<longleftrightarrow> card X \<ge> 3"
proof
  assume "long_ch_by_ord f X"
  then obtain a b c where "[f[a..b..c]X]"
    using get_fin_long_ch_bounds assms(2) by blast
  thus "3 \<le> card X"
    by (metis (no_types, hide_lams) One_nat_def card_eq_0_iff diff_Suc_1 empty_iff
        fin_long_chain_def index_middle_element leI less_3_cases less_one)
next
  assume "3 \<le> card X"
  hence "\<not>short_ch X"
    using assms(1) short_ch_card_2 by auto
  thus "long_ch_by_ord f X"
    using assms(1) ch_by_ord_def by auto
qed

lemma chain_bounds_unique:
  assumes "[f[a..b..c]X]" "[g[x..y..z]X]"
  shows "(a=x \<and> c=z) \<or> (a=z \<and> c=x)"
proof -
  have "\<forall>p\<in>X. (a = p \<or> p = c) \<or> [[a p c]]"
    using assms(1) ch_all_betw_f by force
  then show ?thesis
    by (metis (full_types) abc_abc_neq abc_bcd_abd abc_sym assms(1,2) ch_all_betw_f points_in_chain)
qed

lemma chain_bounds_unique2:
  assumes "[f[a..c]X]" "[g[x..z]X]" "card X \<ge> 3"
  shows "(a=x \<and> c=z) \<or> (a=z \<and> c=x)"
  using chain_bounds_unique
  by (metis abc_ac_neq assms(1,2) ch_all_betw_f fin_chain_def points_in_chain short_ch_def)

subsection "Chain Equivalences"

subsubsection "Betweenness-chains and strong index-chains"

lemma equiv_chain_1a:
  assumes "[[..a..b..c..]X]"
  shows "\<exists>f. ch_by_ord f X \<and> a\<in>X \<and> b\<in>X \<and> c\<in>X \<and> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
proof -
  have in_X: "a\<in>X \<and> b\<in>X \<and> c\<in>X"
    using assms chain_with_def by auto
  have all_neq: "a\<noteq>c \<and> a\<noteq>b \<and> b\<noteq>c"
    using abc_abc_neq assms chain_with_def by auto
  obtain f where "ordering f betw X"
    using assms chain_with_def by auto
  hence "long_ch_by_ord f X"
    using in_X all_neq long_ch_by_ord_def by blast
  hence "ch_by_ord f X"
    by (simp add: ch_by_ord_def)
  thus ?thesis
    using all_neq in_X by blast
qed


lemma equiv_chain_1b:
  assumes "ch_by_ord f X \<and> a\<in>X \<and> b\<in>X \<and> c\<in>X \<and> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<and> [[a b c]]"
  shows "[[..a..b..c..]X]"
  using assms chain_with_def ch_by_ord_def
  by (metis long_ch_by_ord_def short_ch_def)


lemma equiv_chain_1:
  "[[..a..b..c..]X] \<longleftrightarrow> (\<exists>f. ch_by_ord f X \<and> a\<in>X \<and> b\<in>X \<and> c\<in>X \<and> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<and> [[a b c]])"
  using equiv_chain_1a equiv_chain_1b long_chain_betw
  by meson


lemma index_order:
  assumes "chain_with x y z X"
      and "ch_by_ord f X" and "f a = x" and "f b = y" and "f c = z"
      and "finite X \<longrightarrow> a<card X" and "finite X \<longrightarrow> b<card X" and "finite X \<longrightarrow> c<card X"
    shows "(a<b \<and> b<c) \<or> (c<b \<and> b<a)"
proof (rule ccontr)
  assume a1: "\<not> (a < b \<and> b < c \<or> c < b \<and> b < a)"
  hence "(a\<ge>b \<or> b\<ge>c) \<and> (c\<ge>b \<or> b\<ge>a)"
    by auto
  have all_neq: "x\<noteq>y \<and> x\<noteq>z \<and> y\<noteq>z"
    using assms(1) equiv_chain_1 by blast
  hence is_long: "long_ch_by_ord f X"
    by (metis assms(1) assms(2) ch_by_ord_def equiv_chain_1 short_ch_def)
  have "a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
    using assms(3) assms(4) assms(5) all_neq by blast
  hence "(a>b \<or> b>c) \<and> (c>b \<or> b>a)"
    using a1 linorder_neqE_nat by blast
  hence "(a>b \<and> c>b) \<or> (b>c \<and> b>a)"
    using not_less_iff_gr_or_eq by blast
  have "a>c \<or> c>a"
    using \<open>a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c\<close> by auto
  hence "(a>c \<and> c>b) \<or> (a>c \<and> b>a) \<or> (a>b \<and> c>a) \<or> (b>c \<and> c>a)"
    using \<open>(b < a \<or> c < b) \<and> (b < c \<or> a < b)\<close> by blast
  hence o1: "(b<c \<and> c<a) \<or> (c<a \<and> a<b) \<or> (b<a \<and> a<c) \<or> (a<c \<and> c<b)"
    by blast
  have "(b<c \<and> c<a) \<longrightarrow> [[y z x]]"
    using assms ordering_ord_ijk long_ch_by_ord_def is_long
    by metis 
  moreover have "(c<a \<and> a<b) \<longrightarrow> [[z x y]]"
    using  assms ordering_ord_ijk long_ch_by_ord_def is_long
    by metis
  moreover have "(b<a \<and> a<c) \<longrightarrow> [[y x z]]"
    using assms ordering_ord_ijk long_ch_by_ord_def is_long
    by metis
  moreover have "(a<c \<and> c<b) \<longrightarrow> [[x z y]]"
    using assms ordering_ord_ijk long_ch_by_ord_def is_long
    by metis
  ultimately have "[[y z x]] \<or> [[z x y]] \<or> [[y x z]] \<or> [[x z y]]"
    using assms long_ch_by_ord_def is_long o1
    by metis
  thus False
    by (meson abc_only_cba assms(1) chain_with_def)
qed


lemma old_fin_chain_finite:
  assumes "finite_chain_with3 x y z X"
  shows "finite X"
proof (rule ccontr)
  assume "infinite X"
  have "x\<in>X"
    using assms finite_chain_with3_def chain_with_def by simp
  have "y\<in>X"
    using assms finite_chain_with3_def chain_with_def by simp
  have "z\<in>X"
    using assms finite_chain_with3_def chain_with_def by simp
  obtain f where "ch_by_ord f X"
    using assms equiv_chain_1 finite_chain_with3_def
    by auto
  obtain a where "f a = x"
    using equiv_chain_1 ordering_def \<open>ch_by_ord f X\<close> assms
    by (metis ch_by_ord_def finite_chain_with3_def long_ch_by_ord_def short_ch_def)
  obtain c where "f c = z" and "a\<noteq>c"
    using equiv_chain_1 ordering_def \<open>ch_by_ord f X\<close> \<open>f a = x\<close> assms
    using ch_by_ord_def finite_chain_with3_def long_ch_by_ord_def short_ch_def
    by metis
  obtain b where "f b = y" and "a\<noteq>b" and "b\<noteq>c"
    using equiv_chain_1 ordering_def \<open>ch_by_ord f X\<close> \<open>f a = x\<close> \<open>f c = z\<close> assms
    using ch_by_ord_def finite_chain_with3_def long_ch_by_ord_def short_ch_def
    by metis
  obtain n where "a<n" and "c<n"
    using \<open>ch_by_ord f X\<close> \<open>f a = x\<close> \<open>f c = z\<close> assms equiv_chain_1 \<open>infinite X\<close>
    using  ch_by_ord_def finite_chain_with3_def long_ch_by_ord_def short_ch_def
    by (metis less_Suc_eq_le not_le not_less_iff_gr_or_eq)
  have "[[x y z]]"
    using assms chain_with_def finite_chain_with3_def by auto
  hence "(a<b \<and> b<c) \<or> (c<b \<and> b<a)"
    using \<open>f a = x\<close> \<open>f b = y\<close> \<open>f c = z\<close> \<open>ch_by_ord f X\<close> \<open>x\<in>X\<close> \<open>y\<in>X\<close> \<open>z\<in>X\<close> index_order
    using \<open>infinite X\<close> assms finite_chain_with3_def
    by blast
  hence "(a<b \<and> b<c \<and> c<n) \<or> (c<b \<and> b<a \<and> a<n)"
    using \<open>a\<noteq>c\<close> \<open>a\<noteq>b\<close> \<open>b\<noteq>c\<close> \<open>a<n\<close> \<open>c<n\<close> less_linear
    by blast
  hence acn_can: "(b<c \<and> c<n) \<or> (b<a \<and> a<n)"
    by blast
  have "f n \<in> X"
    by (metis ordering_def \<open>ch_by_ord f X\<close> \<open>infinite X\<close> assms ch_by_ord_def equiv_chain_1 finite_chain_with3_def long_ch_by_ord_def short_ch_def)
  hence outside: "[[y z (f n)]] \<or> [[(f n) x y]]"
    using acn_can \<open>ch_by_ord f X\<close> \<open>f a = x\<close> \<open>f c = z\<close> \<open>infinite X\<close> assms equiv_chain_1 abc_sym
    using ch_by_ord_def finite_chain_with3_def long_ch_by_ord_def ordering_ord_ijk short_ch_def
    by (metis \<open>f b = y\<close>)
  thus False
    using \<open>f n \<in> X\<close> assms finite_chain_with3_def
    by blast
qed


lemma index_from_with3:
  assumes "finite_chain_with3 a b c X"
  shows "\<exists>f. (f 0 = a \<or> f 0 = c) \<and> ch_by_ord f X"
proof -
  obtain f where "ch_by_ord f X"
    using assms equiv_chain_1 finite_chain_with3_def
    by auto
  have no_elt: "\<not>(\<exists>w\<in>X. [[w a b]] \<or> [[b c w]])"
    using assms finite_chain_with3_def
    by blast
  obtain n\<^sub>a n\<^sub>b where "f n\<^sub>a = a" and "n\<^sub>a < card X"
      and "f n\<^sub>b = b" and "n\<^sub>b < card X"
    using assms old_fin_chain_finite ch_by_ord_def ordering_def
    using \<open>ch_by_ord f X\<close> equiv_chain_1 finite_chain_with3_def long_ch_by_ord_def short_ch_def
    by metis
  obtain n\<^sub>c where "f n\<^sub>c = c" and "n\<^sub>c < card X"
    using assms old_fin_chain_finite ch_by_ord_def ordering_def
    using \<open>ch_by_ord f X\<close> equiv_chain_1 finite_chain_with3_def long_ch_by_ord_def short_ch_def
    by metis
  have "a\<noteq>b \<and> b\<noteq>c \<and> a\<noteq>c"
    using assms equiv_chain_1 finite_chain_with3_def by auto
  have "a\<noteq>b \<longrightarrow> n\<^sub>a\<noteq>n\<^sub>b \<and> b\<noteq>c \<longrightarrow> n\<^sub>a\<noteq>n\<^sub>c \<and> a\<noteq>c \<longrightarrow> n\<^sub>b\<noteq>n\<^sub>c"
    using \<open>f n\<^sub>a = a\<close> \<open>f n\<^sub>b = b\<close> \<open>f n\<^sub>c = c\<close> by blast
  hence "n\<^sub>a\<noteq>n\<^sub>b \<and> n\<^sub>a\<noteq>n\<^sub>c \<and> n\<^sub>b\<noteq>n\<^sub>c"
    using \<open>a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c\<close> \<open>f n\<^sub>a = a\<close> \<open>f n\<^sub>b = b\<close> \<open>f n\<^sub>c = c\<close>
    by auto
  have "n\<^sub>a = 0 \<or> n\<^sub>c = 0"
    proof (rule ccontr)
      assume "\<not> (n\<^sub>a = 0 \<or> n\<^sub>c = 0)"
      hence not_0: "n\<^sub>a \<noteq> 0 \<and> n\<^sub>c \<noteq> 0"
        by linarith
      then obtain p where "f 0 = p"
        by simp
      hence "p\<in>X"
        using \<open>ch_by_ord f X\<close> \<open>n\<^sub>a < card X\<close> assms card_0_eq ch_by_ord_def zero_into_ordering
        using equiv_chain_1 finite_chain_with3_def inf.strict_coboundedI2 inf.strict_order_iff less_one long_ch_by_ord_def old_fin_chain_finite short_ch_def
        by metis
      have "n\<^sub>a<n\<^sub>c \<or> n\<^sub>c<n\<^sub>a"
        using \<open>n\<^sub>a \<noteq> n\<^sub>b \<and> n\<^sub>a \<noteq> n\<^sub>c \<and> n\<^sub>b \<noteq> n\<^sub>c\<close> less_linear by blast
      {
        assume "n\<^sub>a < n\<^sub>c"
        hence "n\<^sub>a < n\<^sub>b"
          using index_order \<open>ch_by_ord f X\<close> \<open>f n\<^sub>a = a\<close> \<open>f n\<^sub>b = b\<close> \<open>f n\<^sub>c = c\<close> \<open>n\<^sub>c < card X\<close>
          using finite_chain_with3_def assms
          by fastforce
        have "0<n\<^sub>a \<and> n\<^sub>a<n\<^sub>b"
          using index_order \<open>n\<^sub>a < n\<^sub>b\<close> not_0
          by blast
        hence "[[p a b]]"
          using \<open>ch_by_ord f X\<close> \<open>f 0=p\<close> \<open>f n\<^sub>a=a\<close> \<open>f n\<^sub>b=b\<close> \<open>n\<^sub>b<card X\<close> assms equiv_chain_1 short_ch_def
          by (metis ch_by_ord_def finite_chain_with3_def long_ch_by_ord_def ordering_ord_ijk)
        hence False
          using finite_chain_with3_def \<open>p\<in>X\<close>
          by (metis no_elt)
      }
      moreover {
        assume "n\<^sub>c < n\<^sub>a"
        hence "n\<^sub>c < n\<^sub>b"
          using index_order \<open>ch_by_ord f X\<close> \<open>f n\<^sub>a = a\<close> \<open>f n\<^sub>b = b\<close> \<open>f n\<^sub>c = c\<close> \<open>n\<^sub>a < card X\<close>
          using finite_chain_with3_def assms
          by fastforce
        have "0<n\<^sub>c \<and> n\<^sub>c<n\<^sub>b"
          using index_order \<open>n\<^sub>c < n\<^sub>b\<close> not_0
          by blast
        hence "[[p c b]]"
          using \<open>ch_by_ord f X\<close> \<open>f 0=p\<close> \<open>f n\<^sub>c=c\<close> \<open>f n\<^sub>b=b\<close> \<open>n\<^sub>b<card X\<close> assms equiv_chain_1 short_ch_def
          using ch_by_ord_def finite_chain_with3_def long_ch_by_ord_def ordering_ord_ijk
          by metis
        hence "[[b c p]]"
          by (simp add: abc_sym)
        hence False
          using finite_chain_with3_def \<open>p\<in>X\<close>
          by (metis no_elt)
      }
      ultimately show False
        using \<open>n\<^sub>a < n\<^sub>c \<or> n\<^sub>c < n\<^sub>a\<close> by blast
    qed
  thus ?thesis
    using \<open>ch_by_ord f X\<close> \<open>f n\<^sub>a = a\<close> \<open>f n\<^sub>c = c\<close>
    by blast
qed


lemma (in MinkowskiSpacetime) with3_and_index_is_fin_chain:
  assumes "f 0 = a" and "ch_by_ord f X" and "finite_chain_with3 a b c X"
  shows "[f[a..b..c]X]"
proof -
  have "finite X"
    using ordering_def assms old_fin_chain_finite
    by auto
  moreover have "long_ch_by_ord f X"
    using  assms(2) assms(3) ch_by_ord_def equiv_chain_1 finite_chain_with3_def short_ch_def
    by metis
  moreover have "a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<and> f 0 = a \<and> b\<in>X"
    using assms(1) assms(3) equiv_chain_1 finite_chain_with3_def
    by auto
  moreover have "f (card X - 1) = c"
    proof -
      obtain n where "f n = c" and "n < card X"
        using ordering_def equiv_chain_1 finite_chain_with3_def long_ch_by_ord_def
        by (metis assms(3) calculation(1,2))
      {
        assume "n < card X - 1"
        then obtain m where "n<m" and "m<card X" by simp
        hence "[[a c (f m)]] \<and> (f m)\<in>X"
          proof -
            have f1: "TernaryOrdering.ordering f betw X"
              using \<open>long_ch_by_ord f X\<close> long_ch_by_ord_def by blast
            have f2: "\<forall>f A p na. ((p (f na::'a) (f n) (f m) \<or> \<not> m < card A) \<or> \<not> ordering f p A)
                                      \<or> \<not> na < n"
              by (metis ordering_def \<open>n < m\<close>)
            have "f m \<in> X"
              using f1 by (simp add: ordering_def \<open>m < card X\<close>)
            then show ?thesis
              using f2 f1 \<open>a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<and> f 0 = a \<and> b\<in>X\<close> \<open>f n = c\<close> \<open>m < card X\<close>
              using gr_implies_not0 linorder_neqE_nat
              by (metis (no_types))
          qed
        hence "[[b c (f m)]]" using abc_acd_bcd
          by (meson assms(3) chain_with_def finite_chain_with3_def)
        hence False
          using assms(3) \<open>[[a c (f m)]] \<and> f m \<in> X\<close>
          by (metis finite_chain_with3_def)
      }
      hence "n = card X - 1"
        using \<open>n < card X\<close> by fastforce
      thus ?thesis
        using \<open>f n = c\<close> by blast
    qed
  ultimately show ?thesis
    by (simp add: fin_long_chain_def)
qed


lemma (in MinkowskiSpacetime) g_from_with3:
  assumes "finite_chain_with3 a b c X"
  obtains g where "[g[a..b..c]X] \<or> [g[c..b..a]X]"
proof -
  have old_chain_sym: "finite_chain_with3 c b a X"
    by (metis abc_sym assms chain_with_def finite_chain_with3_def)
  obtain f where f_def: "(f 0 = a \<or> f 0 = c) \<and> ch_by_ord f X"
    using index_from_with3 assms
    by blast
  hence "f 0 = a \<longrightarrow> [f[a..b..c]X]"
    using with3_and_index_is_fin_chain f_def assms
    by simp
  moreover have "f 0 = c \<longrightarrow> [f[c..b..a]X]"
    using with3_and_index_is_fin_chain f_def assms old_chain_sym
    by simp
  ultimately show ?thesis
    using f_def that
    by auto
qed


lemma (in MinkowskiSpacetime) equiv_chain_2a:
  assumes "finite_chain_with3 a b c X"
  obtains f where "[f[a..b..c]X]"
proof -
  obtain g where "[g[a..b..c]X] \<or> [g[c..b..a]X]"
    using assms g_from_with3 by blast
  thus ?thesis
  proof (* in two cases *)
    assume "[g[a..b..c]X]"
    show ?thesis
      using \<open>[g[a .. b .. c]X]\<close> that
      by blast
  next
    assume "[g[c..b..a]X]"
    show ?thesis
      using \<open>[g[c .. b .. a]X]\<close> chain_sym that
      by blast
  qed
qed


lemma equiv_chain_2b:
  assumes "[f[a..b..c]X]"
  shows "finite_chain_with3 a b c X"
proof -
  have aligned: "[[a b c]]"
    using assms fin_ch_betw
    by auto
  hence some_chain: "[[..a..b..c..]X]"
    using assms ch_by_ord_def equiv_chain_1b fin_long_chain_def points_in_chain
    by metis
  have "\<not>(\<exists>w\<in>X. [[w a b]] \<or> [[b c w]])"
  proof (safe)
    fix w assume "w\<in>X"
    {
      assume case1: "[[w a b]]"
      then obtain n where "f n = w" and "n<card X"
        using \<open>w\<in>X\<close> abc_bcd_abd abc_only_cba aligned assms fin_ch_betw fin_long_chain_def
        by (metis (no_types, hide_lams))
      have "f 0 = a"
        using assms fin_long_chain_def
        by blast
      hence "n < 0"
        proof -
          have f1: "f (card X - 1) = c"
            by (meson MinkowskiBetweenness.fin_long_chain_def MinkowskiBetweenness_axioms assms)
          have "\<not> [[a w c]]"
            by (meson abc_bcd_abd abc_only_cba assms case1 fin_ch_betw)
          thus ?thesis
            using f1 fin_long_chain_def \<open>w \<in> X\<close> abc_only_cba assms case1 fin_ch_betw
            by (metis (no_types))
        qed
      thus False
        by simp
    }
    moreover {
        assume case2: "[[b c w]]"
      then obtain n where "f n = w" and "n<card X"
        using \<open>w\<in>X\<close> ordering_def abc_bcd_abd abc_only_cba aligned assms fin_ch_betw
        using fin_long_chain_def long_ch_by_ord_def
        by metis
      have "f (card X - 1) = c"
        using assms fin_long_chain_def
        by blast
      have "\<not> [[a w c]]"
        using abc_bcd_abd abc_only_cba assms case2 fin_ch_betw abc_bcd_acd
        by meson
      hence "n > card X - 1"
        using \<open>\<not> [[a w c]]\<close> \<open>w \<in> X\<close> abc_only_cba assms case2 fin_ch_betw
        unfolding fin_long_chain_def
        by (metis (no_types))
      thus False
        using \<open>n < card X\<close>
        by linarith
    }
  qed
  thus ?thesis
    by (simp add: finite_chain_with3_def some_chain)
qed


lemma (in MinkowskiSpacetime) equiv_chain_2:
  "\<exists>f. [f[a..b..c]X] \<longleftrightarrow> [[a..b..c]X]"
  using equiv_chain_2a equiv_chain_2b
  by meson

end (* context MinkowskiChain *)

section "Results for segments, rays and chains"

context MinkowskiChain begin

lemma inside_not_bound:
  assumes "[f[a..b..c]X]"
      and "j<card X"
    shows "j>0 \<Longrightarrow> f j \<noteq> a" "j<card X - 1 \<Longrightarrow> f j \<noteq> c"
proof -
  have bound_indices: "f 0 = a \<and> f (card X - 1) = c"
    using assms(1) fin_long_chain_def by auto
  show "f j \<noteq> a" if "j>0"
  proof (cases)
    assume "f j = c"
    then have "[[(f 0) (f j) b]] \<or> [[(f 0) b (f j)]]"
      using assms(1) fin_ch_betw fin_long_chain_def
      by metis
    thus ?thesis using abc_abc_neq bound_indices by blast
  next
    assume "f j \<noteq> c"
    then have "[[(f 0) (f j) c]] \<or> [[(f 0) c (f j)]]"
      using assms fin_ch_betw
      unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
      by (metis abc_abc_neq assms that ch_all_betw_f nat_neq_iff)
    thus ?thesis
      using abc_abc_neq bound_indices by blast
  qed
  show "f j \<noteq> c" if "j<card X - 1"
  proof (cases)
    assume "f j = a"
    show ?thesis
      using \<open>f j = a\<close> assms(1) fin_long_chain_def
      by blast
  next
    assume "f j \<noteq> a"
    have "0 < card X"
      using assms(2) by linarith
    hence "[[a (f j) (f (card X - 1))]] \<or> [[(f j) a (f (card X - 1))]]"
      using  assms fin_ch_betw fin_long_chain_def order_finite_chain
      by (metis \<open>f j \<noteq> a\<close> diff_less le_numeral_extra(1-3) neq0_conv that)
  thus "f j \<noteq> c"
    using abc_abc_neq bound_indices by auto
  qed
qed


lemma some_betw2:
  assumes "[f[a..b..c]X]"
      and "j<card X" "j>0" "f j \<noteq> b"
    shows "[[a b (f j)]] \<or> [[a (f j) b]]"
proof -
  obtain ab where ab_def: "path ab a b" "X\<subseteq>ab"
    by (metis fin_long_chain_def long_chain_on_path assms(1) points_in_chain subsetD)
  have bound_indices: "f 0 = a \<and> f (card X - 1) = c"
    using assms(1) fin_long_chain_def by auto
  have "f j \<noteq> a"
    using inside_not_bound(1) assms(1) assms(2) assms(3)
    by blast
  have "\<not>[[(f j) a b]]"
    using abc_bcd_abd abc_only_cba assms(1,2) fin_ch_betw fin_long_chain_def
    by (metis ordering_def ch_all_betw_f long_ch_by_ord_def)
  thus " [[a b (f j)]] \<or> [[a (f j) b]]"
    using some_betw [where Q=ab and a=a and b=b and c="f j"]
    using ab_def assms(4) \<open>f j \<noteq> a\<close>
    by (metis ordering_def abc_sym assms(1,2) fin_long_chain_def long_ch_by_ord_def subsetD)
qed

lemma i_le_j_events_neq1:
  assumes "[f[a..b..c]X]"
      and "i<j" "j<card X" "f j \<noteq> b" (* this just means you need to pick b well *)
    shows "f i \<noteq> f j"
proof -
  have in_X: "f i \<in> X \<and> f j \<in> X"
    by (metis ordering_def assms(1,2,3) fin_long_chain_def less_trans long_ch_by_ord_def)
  have bound_indices: "f 0 = a \<and> f (card X - 1) = c"
    using assms(1) fin_long_chain_def by auto
  obtain ab where ab_def: "path ab a b" "X\<subseteq>ab"
    by (metis fin_long_chain_def long_chain_on_path assms(1) points_in_chain subsetD)
  show ?thesis
  proof (cases)
    assume "f i = a"
    hence "[[a (f j) b]] \<or> [[a b (f j)]]"
      using some_betw2 assms by blast
    thus ?thesis
      using \<open>f i = a\<close> abc_abc_neq by blast
  next assume "f i \<noteq> a"
    hence "[[a (f i) (f j)]]"
      using assms(1,2,3) ch_equiv fin_long_chain_def order_finite_chain2
      by (metis gr_implies_not_zero le_numeral_extra(3) less_linear)
    thus ?thesis
      using abc_abc_neq by blast
  qed
qed

lemma i_le_j_events_neq:
  assumes "[f[a..b..c]X]"
      and "i<j" "j<card X"
    shows "f i \<noteq> f j"
proof -
  have in_X: "f i \<in> X \<and> f j \<in> X"
    by (metis ordering_def assms(1,2,3) fin_long_chain_def less_trans long_ch_by_ord_def)
  have bound_indices: "f 0 = a \<and> f (card X - 1) = c"
    using assms(1) fin_long_chain_def by auto
  obtain ab where ab_def: "path ab a b" "X\<subseteq>ab"
    by (metis fin_long_chain_def long_chain_on_path assms(1) points_in_chain subsetD)
  show ?thesis
  proof (cases)
    assume "f i = a"
    show ?thesis
    proof (cases)
    assume "(f j) = b"
      thus ?thesis
        by (simp add: \<open>(f i) = a\<close> ab_def(1))
    next assume "(f j) \<noteq> b"
      have "[[a (f j) b]] \<or> [[a b (f j)]]"
        using some_betw2 assms \<open>(f j) \<noteq> b\<close> by blast
      thus ?thesis
        using \<open>(f i) = a\<close> abc_abc_neq by blast
    qed
  next assume "(f i) \<noteq> a"
    hence "[[a (f i) (f j)]]"
      using assms(1,2,3) ch_equiv fin_long_chain_def order_finite_chain2
      by (metis gr_implies_not_zero le_numeral_extra(3) less_linear)
    thus ?thesis
      using abc_abc_neq by blast
  qed
qed

lemma indices_neq_imp_events_neq:
  assumes "[f[a..b..c]X]"
      and "i\<noteq>j" "j<card X" "i<card X"
    shows "f i \<noteq> f j"
  by (metis assms i_le_j_events_neq less_linear)


lemma index_order2:
  assumes "[f[x..y..z]X]" and "f a = x" and "f b = y" and "f c = z"
      and "finite X \<longrightarrow> a < card X" and "finite X \<longrightarrow> b < card X" and "finite X \<longrightarrow> c < card X"
    shows "(a<b \<and> b<c) \<or> (c<b \<and> b<a)"
  using index_order [where x=x and y=y and z=z and a=a and b=b and c=c and f=f and X=X]
  by (metis assms ch_by_ord_def equiv_chain_2b fin_long_chain_def finite_chain_with3_def)

lemma index_order3:
  assumes "[[x y z]]" and "f a = x" and "f b = y" and "f c = z" and "long_ch_by_ord f X"
      and "finite X \<longrightarrow> a < card X" and "finite X \<longrightarrow> b < card X" and "finite X \<longrightarrow> c < card X"
    shows "(a<b \<and> b<c) \<or> (c<b \<and> b<a)"
  using index_order2 [where x=x and y=y and z=z and a=a and b=b and c=c and f=f and X=X]
  using assms long_ch_by_ord_def ordering_ord_ijk
  by (smt abc_abc_neq abc_only_cba(1-3) linorder_neqE_nat)

end (* context MinkowskiChain *)

context MinkowskiSpacetime begin

lemma bound_on_path:
  assumes "Q\<in>\<P>" "[f[(f 0)..]X]" "X\<subseteq>Q" "is_bound_f b X f"
  shows "b\<in>Q"
proof -
  obtain a c where "a\<in>X" "c\<in>X" "[[a c b]]"
    using assms(4)
    by (metis ordering_def inf_chain_is_long is_bound_f_def long_ch_by_ord_def zero_less_one)
  thus ?thesis
    using abc_abc_neq assms(1) assms(3) betw_c_in_path by blast
qed

lemma pro_basis_change:
  assumes "[[a b c]]"
  shows "prolongation a c = prolongation b c" (is "?ac=?bc")
proof
  show "?ac \<subseteq> ?bc"
  proof
    fix x assume "x\<in>?ac"
    hence "[[a c x]]"
      by (simp add: pro_betw)
    hence "[[b c x]]"
      using assms abc_acd_bcd by blast
    thus "x\<in>?bc"
      using abc_abc_neq pro_betw by blast
  qed
  show "?bc \<subseteq> ?ac"
  proof
    fix x assume "x\<in>?bc"
    hence "[[b c x]]"
      by (simp add: pro_betw)
    hence "[[a c x]]"
      using assms abc_bcd_acd by blast
    thus "x\<in>?ac"
      using abc_abc_neq pro_betw by blast
  qed
qed

lemma adjoining_segs_exclusive:
  assumes "[[a b c]]"
  shows "segment a b \<inter> segment b c = {}"
proof (cases)
  assume "segment a b = {}" thus ?thesis by blast
next
  assume "segment a b \<noteq> {}"
  have "x\<in>segment a b \<longrightarrow> x\<notin>segment b c" for x
  proof
    fix x assume "x\<in>segment a b"
    hence "[[a x b]]" by (simp add: seg_betw)
    have "\<not>[[a b x]]" by (meson `[[a x b]]` abc_only_cba)
    have "\<not>[[b x c]]"
      using \<open>\<not> [[a b x]]\<close> abd_bcd_abc assms by blast
    thus "x\<notin>segment b c"
      by (simp add: seg_betw)
  qed
  thus ?thesis by blast
qed

end (* context MinkowskiSpacetime *)

section "3.6 Order on a path - Theorems 10 and 11"

context MinkowskiSpacetime begin

subsection \<open>Theorem 10 (based on Veblen (1904) theorem 10).\<close>

lemma (in MinkowskiBetweenness) two_event_chain:
  assumes finiteX: "finite X"
      and path_Q: "Q \<in> \<P>"
      and events_X: "X \<subseteq> Q"
      and card_X: "card X = 2"
    shows "ch X"
proof -
  obtain a b where X_is: "X={a,b}"
    using card_le_Suc_iff numeral_2_eq_2
    by (meson card_2_iff card_X)
  have no_c: "\<not>(\<exists>c\<in>{a,b}. c\<noteq>a \<and> c\<noteq>b)"
    by blast
  have "a\<noteq>b \<and> a\<in>Q & b\<in>Q"
    using X_is card_X events_X by force
  hence "short_ch {a,b}"
    using path_Q short_ch_def no_c by blast
  thus ?thesis
    by (simp add: X_is ch_by_ord_def ch_def)
qed

lemma (in MinkowskiBetweenness) three_event_chain:
  assumes finiteX: "finite X"
      and path_Q: "Q \<in> \<P>"
      and events_X: "X \<subseteq> Q"
      and card_X: "card X = 3"
    shows "ch X"
proof -
  obtain a b c where X_is: "X={a,b,c}"
    using numeral_3_eq_3 card_X by (metis card_Suc_eq)
  then have all_neq: "a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
    using card_X numeral_2_eq_2 numeral_3_eq_3
    by (metis Suc_n_not_le_n insert_absorb2 insert_commute set_le_two)
  have in_path: "a\<in>Q \<and> b\<in>Q \<and> c\<in>Q"
    using X_is events_X by blast
  hence "[[a b c]] \<or> [[b c a]] \<or> [[c a b]]"
    using some_betw all_neq path_Q by auto
  thus "ch X"
    using between_chain X_is all_neq chain3 in_path path_Q by auto
qed

text \<open>This is case (i) of the induction in Theorem 10.\<close>

lemma (*for 10*) chain_append_at_left_edge:
  assumes long_ch_Y: "[f[a\<^sub>1..a..a\<^sub>n]Y]"
      and bY: "[[b a\<^sub>1 a\<^sub>n]]"
    fixes g defines g_def: "g \<equiv> (\<lambda>j::nat. if j\<ge>1 then f (j-1) else b)"
    shows "[g[b .. a\<^sub>1 .. a\<^sub>n](insert b Y)]"
proof -
  let ?X = "insert b Y"
  have "b\<notin>Y"
    by (metis abc_ac_neq abc_only_cba(1) bY ch_all_betw_f long_ch_Y)
  have bound_indices: "f 0 = a\<^sub>1 \<and> f (card Y - 1) = a\<^sub>n"
    using long_ch_Y by (simp add: fin_long_chain_def)
  have fin_Y: "card Y \<ge> 3"
    using  fin_long_chain_def long_ch_Y numeral_2_eq_2
    by (metis ch_by_ord_def long_ch_card_ge3)
  hence num_ord: "0 \<le> (0::nat) \<and> 0<(1::nat) \<and> 1 < card Y - 1 \<and> card Y - 1 < card Y"
    by linarith
  hence "[[a\<^sub>1 (f 1) a\<^sub>n]]"
    using order_finite_chain fin_long_chain_def long_ch_Y
    by auto
  text \<open>Schutz has a step here that says \<open>[b a\<^sub>1 a\<^sub>2 a\<^sub>n]\<close> is a chain (using Theorem 9).
    We have no easy way of denoting an ordered 4-element chain, so we skip this step
    using an ordering lemma from our script for 3.6, which Schutz doesn't list.\<close>
  hence "[[b a\<^sub>1 (f 1)]]"
    using bY abd_bcd_abc by blast
  have "ordering2 g betw ?X"
  proof -
    {
      fix n assume "finite ?X \<longrightarrow> n<card ?X"
      have "g n \<in> ?X"
        apply (cases "n\<ge>1")
         prefer 2 apply (simp add: g_def)
      proof
        assume "1\<le>n" "g n \<notin> Y"
        hence "g n = f(n-1)" unfolding g_def by auto
        hence "g n \<in> Y"
        proof (cases "n = card ?X - 1")
          case True
          thus ?thesis
            using \<open>b\<notin>Y\<close> card.insert diff_Suc_1 fin_long_chain_def long_ch_Y points_in_chain
            by (metis \<open>g n = f (n - 1)\<close>)
        next
          case False
          hence "n < card Y"
            using points_in_chain \<open>finite ?X \<longrightarrow> n < card ?X\<close> \<open>g n = f (n - 1)\<close> \<open>g n \<notin> Y\<close> \<open>b\<notin>Y\<close>
            by (metis card.insert fin_long_chain_def finite_insert long_ch_Y not_less_simps(1))
          hence "n-1 < card Y - 1"
            using \<open>1 \<le> n\<close> diff_less_mono by blast
          hence "f(n-1)\<in>Y"
            using long_ch_Y unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
            by (meson less_trans num_ord)
          thus ?thesis
            using \<open>g n = f (n - 1)\<close> by presburger
        qed
        hence False using \<open>g n \<notin> Y\<close> by auto
        thus "g n = b" by simp
      qed
    } moreover {
      fix n n' n'' assume "(finite ?X \<longrightarrow> n'' < card ?X)" "Suc n = n' \<and> Suc n' = n''"
      hence "[[(g n) (g n') (g n'')]]"
        using \<open>b\<notin>Y\<close> \<open>[[b a\<^sub>1 (f 1)]]\<close> g_def long_ch_Y ordering_ord_ijk
        by (smt (verit, ccfv_threshold) fin_long_chain_def long_ch_by_ord_def
            One_nat_def card.insert diff_Suc_Suc diff_diff_cancel diff_is_0_eq
            finite_insert nat_less_le not_less not_less_eq_eq)
    } moreover {
      fix x assume "x\<in>?X" "x=b"
      have "(finite ?X \<longrightarrow> 0 < card ?X) \<and> g 0 = x"
        by (simp add: \<open>b\<notin>Y\<close> \<open>x = b\<close> g_def)
    } moreover {
      fix x assume "x\<in>?X" "x\<noteq>b"
      hence "\<exists>n. (finite ?X \<longrightarrow> n < card ?X) \<and> g n = x"
      proof -
        obtain n where "f n = x" "n < card Y"
          using \<open>x\<in>?X\<close> \<open>x\<noteq>b\<close>
          by (metis ordering_def fin_long_chain_def insert_iff long_ch_Y long_ch_by_ord_def)
        have "(finite ?X \<longrightarrow> n+1 < card ?X)" "g(n+1) = x"
          apply (simp add: \<open>b\<notin>Y\<close> \<open>n < card Y\<close>)
          by (simp add: \<open>f n = x\<close> g_def)
        thus ?thesis by auto
      qed
    }
    ultimately show ?thesis
      unfolding ordering2_def
      by smt (* sledgehammer proposes both meson and auto, neither of which work... *)
  qed
  hence "long_ch_by_ord2 g ?X"
    unfolding long_ch_by_ord2_def
    using points_in_chain fin_long_chain_def \<open>b\<notin>Y\<close>
    by (metis abc_abc_neq bY insert_iff long_ch_Y points_in_chain)
  hence "long_ch_by_ord g ?X"
    using ch_equiv fin_Y
    by (meson fin_long_chain_def finite_insert long_ch_Y)
  thus ?thesis
    unfolding fin_long_chain_def
    using bound_indices \<open>b\<notin>Y\<close> g_def num_ord points_in_chain long_ch_Y fin_long_chain_def
    by (metis card.insert diff_Suc_1 finite_insert insert_iff less_trans nat_less_le)
qed

text \<open>
  This is case (iii) of the induction in Theorem 10.
  Schutz says merely ``The proof for this case is similar to that for Case (i).''
  Thus I feel free to use a result on symmetry, rather than going through
  the pain of Case (i) (\<open>chain_append_at_left_edge\<close>) again.
\<close>
lemma (*for 10*) chain_append_at_right_edge:
  assumes long_ch_Y: "[f[a\<^sub>1..a..a\<^sub>n]Y]"
      and Yb: "[[a\<^sub>1 a\<^sub>n b]]"
    fixes g defines g_def: "g \<equiv> (\<lambda>j::nat. if j \<le> (card Y - 1) then f j else b)"
    shows "[g[a\<^sub>1 .. a\<^sub>n .. b](insert b Y)]"
proof -
  let ?X = "insert b Y"
  have "b\<notin>Y"
    by (metis Yb abc_abc_neq abc_only_cba(2) ch_all_betw_f long_ch_Y)
  have fin_X: "finite ?X"
    using fin_long_chain_def long_ch_Y by blast
  have fin_Y: "card Y \<ge> 3"
    by (meson ch_by_ord_def fin_long_chain_def long_ch_Y long_ch_card_ge3)
  have "a\<^sub>1\<in>Y \<and> a\<^sub>n\<in>Y \<and> a\<in>Y"
    using long_ch_Y points_in_chain by blast
  have "a\<^sub>1\<noteq>a \<and> a\<noteq> a\<^sub>n \<and> a\<^sub>1\<noteq>a\<^sub>n"
    using fin_long_chain_def long_ch_Y by auto
  have "Suc (card Y) = card ?X"
    using \<open>b\<notin>Y\<close> fin_X fin_long_chain_def long_ch_Y by auto
  obtain f2 where f2_def: "[f2[a\<^sub>n..a..a\<^sub>1]Y]" "f2=(\<lambda>n. f (card Y - 1 - n))"
    using chain_sym long_ch_Y by blast
  obtain g2 where g2_def: "g2 = (\<lambda>j::nat. if j\<ge>1 then f2 (j-1) else b)"
    by simp
  have "[[b a\<^sub>n a\<^sub>1]]"
    using abc_sym Yb by blast
  hence g2_ord_X: "[g2[b .. a\<^sub>n .. a\<^sub>1]?X]"
    using chain_append_at_left_edge [where a\<^sub>1="a\<^sub>n" and a\<^sub>n="a\<^sub>1" and f="f2"]
      fin_X \<open>b\<notin>Y\<close> f2_def g2_def
    by blast
  then obtain g1 where g1_def: "[g1[a\<^sub>1..a\<^sub>n..b]?X]" "g1=(\<lambda>n. g2 (card ?X - 1 - n))"
    using chain_sym by blast
  have sYX: "(card Y) = (card ?X) - 1"
    using assms(2,3) fin_long_chain_def long_ch_Y \<open>Suc (card Y) = card ?X\<close> by linarith
  have "g1=g"
    unfolding g1_def g2_def f2_def g_def
  proof
    fix n
    show "(
            if 1 \<le> card ?X - 1 - n then
              f (card Y - 1 - (card ?X - 1 - n - 1))
            else b
          ) = (
            if n \<le> card Y - 1 then
              f n
            else b
          )" (is "?lhs=?rhs")
    proof (cases)
      assume "n \<le> card ?X - 2"
      show "?lhs=?rhs"
        using \<open>n \<le> card ?X - 2\<close> fin_long_chain_def long_ch_Y sYX
        by (metis Suc_1 Suc_diff_1 Suc_diff_le card_gt_0_iff diff_Suc_eq_diff_pred diff_commute
            diff_diff_cancel equals0D less_one nat.simps(3) not_less)
    next
      assume "\<not> n \<le> card ?X - 2"
      thus "?lhs=?rhs"
        by (metis \<open>Suc (card Y) = card ?X\<close> Suc_1 diff_Suc_1 diff_Suc_eq_diff_pred diff_diff_cancel
            diff_is_0_eq' nat_le_linear not_less_eq_eq)
    qed
  qed
  thus ?thesis
    using g1_def(1) by blast
qed


lemma S_is_dense:
  assumes long_ch_Y: "[f[a\<^sub>1..a..a\<^sub>n]Y]"
      and S_def: "S = {k::nat. [[a\<^sub>1 (f k) b]] \<and> k < card Y}"
      and k_def: "S\<noteq>{}" "k = Max S"
      and k'_def: "k'>0" "k'<k"
  shows "k' \<in> S"
proof -
  have "k\<in>S" using k_def Max_in S_def
    by (metis finite_Collect_conjI finite_Collect_less_nat)
  show "k' \<in> S"
  proof (rule ccontr)
    assume "\<not>k'\<in>S"
    hence "[[a\<^sub>1 b (f k')]]"
      using order_finite_chain S_def abc_acd_bcd abc_bcd_acd abc_sym long_ch_Y
      by (smt fin_long_chain_def \<open>0 < k'\<close> \<open>k \<in> S\<close> \<open>k' < k\<close> le_numeral_extra(3)
          less_trans mem_Collect_eq)
    have "[[a\<^sub>1 (f k) b]]"
      using S_def \<open>k \<in> S\<close> by blast
    have "[[(f k) b (f k')]]"
      using abc_acd_bcd \<open>[[a\<^sub>1 b (f k')]]\<close> \<open>[[a\<^sub>1 (f k) b]]\<close> by blast
    have "k' < card Y"
      using S_def \<open>k \<in> S\<close> \<open>k' < k\<close> less_trans by blast
    thus False
      using abc_bcd_abd order_finite_chain S_def abc_only_cba(2) long_ch_Y
        \<open>0 < k'\<close> \<open>[[(f k) b (f k')]]\<close> \<open>k \<in> S\<close> \<open>k' < k\<close>
      unfolding fin_long_chain_def
      by (metis (mono_tags, lifting) le_numeral_extra(3) mem_Collect_eq)
  qed
qed


lemma (*for 10*) smallest_k_ex:
  assumes long_ch_Y: "[f[a\<^sub>1..a..a\<^sub>n]Y]"
      and Y_def: "b\<notin>Y"
      and Yb: "[[a\<^sub>1 b a\<^sub>n]]"
    shows "\<exists>k>0. [[a\<^sub>1 b (f k)]] \<and> k < card Y \<and> \<not>(\<exists>k'<k. [[a\<^sub>1 b (f k')]])"
proof -
(* the usual suspects first, they'll come in useful I'm sure *)
  have bound_indices: "f 0 = a\<^sub>1 \<and> f (card Y - 1) = a\<^sub>n"
    using fin_long_chain_def long_ch_Y by auto
  have fin_Y: "finite Y"
    using fin_long_chain_def long_ch_Y by blast
  have card_Y: "card Y \<ge> 3"
    using fin_long_chain_def long_ch_Y points_in_chain
    by (metis (no_types, lifting) One_nat_def antisym card2_either_elt1_or_elt2 diff_is_0_eq'
        not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3)

  text \<open>We consider all indices of chain elements between \<open>a\<^sub>1\<close> and \<open>b\<close>, and find the maximal one.\<close>
  let ?S = "{k::nat. [[a\<^sub>1 (f k) b]] \<and> k < card Y}"
  obtain S where S_def: "S=?S"
    by simp (* just to check this Isabelle-exists *)
  have "S\<subseteq>{0..card Y}"
    using S_def by auto
  hence "finite S"
    using finite_subset by blast

  show ?thesis
  proof (cases)
    assume "S={}"
    show ?thesis
    proof
      show "(0::nat)<1 \<and> [[a\<^sub>1 b (f 1)]] \<and> 1 < card Y \<and> \<not> (\<exists>k'::nat. k' < 1 \<and> [[a\<^sub>1 b (f k')]])"
      proof (intro conjI)
        show "(0::nat)<1" by simp
        show "1 < card Y"
          using Yb abc_ac_neq bound_indices not_le by fastforce
          (* using card_Y by linarith *)
        show "\<not> (\<exists>k'::nat. k' < 1 \<and> [[a\<^sub>1 b (f k')]])"
          using abc_abc_neq bound_indices
          by blast
        show "[[a\<^sub>1 b (f 1)]]"
        proof -
          have "f 1 \<in> Y"
            by (metis ordering_def diff_0_eq_0 fin_long_chain_def less_one long_ch_Y long_ch_by_ord_def nat_neq_iff)
          (* have "[[a\<^sub>1 b f 1]] \<or> [[a\<^sub>1 f 1 b]]" *)
          hence "[[a\<^sub>1 (f 1) a\<^sub>n]]"
            using bound_indices long_ch_Y
            unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
            by (smt One_nat_def card.remove card_Diff1_less card_Diff_singleton diff_is_0_eq'
                le_eq_less_or_eq less_SucE neq0_conv zero_less_diff zero_less_one)
          hence "[[a\<^sub>1 b (f 1)]] \<or> [[a\<^sub>1 (f 1) b]] \<or> [[b a\<^sub>1 (f 1)]]"
            using abc_ex_path_unique some_betw abc_sym
            by (smt Y_def Yb \<open>f 1 \<in> Y\<close> abc_abc_neq cross_once_notin)
          thus "[[a\<^sub>1 b (f 1)]]"
            (* by (smt S_def Yb \<open>S = {}\<close> \<open>[[a\<^sub>1 f 1 a\<^sub>n]]\<close> abc_bcd_abd abc_sym abd_bcd_abc bound_indices
                diff_is_0_eq' empty_iff mem_Collect_eq nat_le_linear nat_less_le) *)
          proof -
            have "\<forall>n. \<not> ([[a\<^sub>1 (f n) b]] \<and> n < card Y)"
              using S_def \<open>S = {}\<close>
              by blast
            then have "[[a\<^sub>1 b (f 1)]] \<or> \<not> [[a\<^sub>n (f 1) b]] \<and> \<not> [[a\<^sub>1 (f 1) b]]"
              using bound_indices abc_sym abd_bcd_abc Yb
              by (metis (no_types) diff_is_0_eq' nat_le_linear nat_less_le)
            then show ?thesis
              using abc_bcd_abd abc_sym
              by (meson \<open>[[a\<^sub>1 b (f 1)]] \<or> [[a\<^sub>1 (f 1) b]] \<or> [[b a\<^sub>1 (f 1)]]\<close> \<open>[[a\<^sub>1 (f 1) a\<^sub>n]]\<close>)
          qed
        qed
      qed
    qed
  next assume "\<not>S={}"
    obtain k where "k = Max S"
      by simp
    hence  "k \<in> S" using Max_in
      by (simp add: \<open>S \<noteq> {}\<close> \<open>finite S\<close>)
    have "k\<ge>1"
    proof (rule ccontr)
      assume "\<not> 1 \<le> k"
      hence "k=0" by simp
      have "[[a\<^sub>1 (f k) b]]"
        using \<open>k\<in>S\<close> S_def
        by blast
      thus False
        using bound_indices \<open>k = 0\<close> abc_abc_neq
        by blast
    qed

    show ?thesis
    proof
      let ?k = "k+1"
      show "0<?k \<and> [[a\<^sub>1 b (f ?k)]] \<and> ?k < card Y \<and> \<not> (\<exists>k'::nat. k' < ?k \<and> [[a\<^sub>1 b (f k')]])"
      proof (intro conjI)
        show "(0::nat)<?k" by simp
        show "?k < card Y"
          by (metis (no_types, lifting) S_def Yb \<open>k \<in> S\<close> abc_only_cba(2) add.commute
              add_diff_cancel_right' bound_indices less_SucE mem_Collect_eq nat_add_left_cancel_less
              plus_1_eq_Suc)
        show "[[a\<^sub>1 b (f ?k)]]"
        proof -
          have "f ?k \<in> Y"
            using \<open>k + 1 < card Y\<close>
            by (metis ordering_def fin_long_chain_def long_ch_Y long_ch_by_ord_def)
          have "[[a\<^sub>1 (f ?k) a\<^sub>n]] \<or> f ?k = a\<^sub>n"
            using bound_indices long_ch_Y \<open>k + 1 < card Y\<close>
            unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
            by (metis (no_types, lifting) Suc_lessI add.commute add_gr_0 card_Diff1_less
                card_Diff_singleton less_diff_conv plus_1_eq_Suc zero_less_one)
          thus  "[[a\<^sub>1 b (f ?k)]]"
          proof (rule disjE)
            assume "[[a\<^sub>1 (f ?k) a\<^sub>n]]"
            hence "f ?k \<noteq> a\<^sub>n"
              by (simp add: abc_abc_neq)
            hence "[[a\<^sub>1 b (f ?k)]] \<or> [[a\<^sub>1 (f ?k) b]] \<or> [[b a\<^sub>1 (f ?k)]]"
              using abc_ex_path_unique some_betw abc_sym \<open>[[a\<^sub>1 (f ?k) a\<^sub>n]]\<close>
                \<open>f ?k \<in> Y\<close> Yb abc_abc_neq assms(3) cross_once_notin
              by (smt Y_def)
            moreover have "\<not> [[a\<^sub>1 (f ?k) b]]"
            proof
              assume "[[a\<^sub>1 (f ?k) b]]"
              hence "?k \<in> S"
                using S_def \<open>[[a\<^sub>1 (f ?k) b]]\<close> \<open>k + 1 < card Y\<close> by blast
              hence "?k \<le> k"
                by (simp add: \<open>finite S\<close> \<open>k = Max S\<close>)
              thus False
                by linarith
            qed
            moreover have "\<not> [[b a\<^sub>1 (f ?k)]]"
              using Yb \<open>[[a\<^sub>1 (f ?k) a\<^sub>n]]\<close> abc_only_cba
              by blast
            ultimately show "[[a\<^sub>1 b (f ?k)]]"
              by blast
          next assume "f ?k = a\<^sub>n"
            show ?thesis
              using Yb \<open>f (k + 1) = a\<^sub>n\<close> by blast
          qed
        qed
        show "\<not>(\<exists>k'::nat. k' < k + 1 \<and> [[a\<^sub>1 b (f k')]])"
        proof
          assume "\<exists>k'::nat. k' < k + 1 \<and> [[a\<^sub>1 b (f k')]]"
          then obtain k' where k'_def: "k'>0" "k' < k + 1" "[[a\<^sub>1 b (f k')]]"
            using abc_ac_neq bound_indices neq0_conv
            by blast
          hence "k'<k"
            using S_def \<open>k \<in> S\<close> abc_only_cba(2) less_SucE by fastforce
          hence "k'\<in>S"
            using S_is_dense long_ch_Y S_def \<open>\<not>S={}\<close> \<open>k = Max S\<close> \<open>k'>0\<close>
            by blast
          thus False
            using S_def abc_only_cba(2) k'_def(3) by blast
        qed
      qed
    qed
  qed
qed


(* TODO: there's definitely a way of doing this using chain_sym and smallest_k_ex. *)
lemma greatest_k_ex:
  assumes long_ch_Y: "[f[a\<^sub>1..a..a\<^sub>n]Y]"
      and Y_def: "b\<notin>Y"
      and Yb: "[[a\<^sub>1 b a\<^sub>n]]"
    shows "\<exists>k. [[(f k) b a\<^sub>n]] \<and> k < card Y - 1 \<and> \<not>(\<exists>k'<card Y. k'>k \<and> [[(f k') b a\<^sub>n]])"
proof -
(* the usual suspects first, they'll come in useful I'm sure *)
  have bound_indices: "f 0 = a\<^sub>1 \<and> f (card Y - 1) = a\<^sub>n"
    using fin_long_chain_def long_ch_Y by auto
  have fin_Y: "finite Y"
    using fin_long_chain_def long_ch_Y by blast
  have card_Y: "card Y \<ge> 3"
    using fin_long_chain_def long_ch_Y points_in_chain
    by (metis (no_types, lifting) One_nat_def antisym card2_either_elt1_or_elt2 diff_is_0_eq'
        not_less_eq_eq numeral_2_eq_2 numeral_3_eq_3)

  text \<open>Again we consider all indices of chain elements between \<open>a\<^sub>1\<close> and \<open>b\<close>.\<close>
  let ?S = "{k::nat. [[a\<^sub>n (f k) b]] \<and> k < card Y}"
  obtain S where S_def: "S=?S"
    by simp (* just to check this Isabelle-exists *)
  have "S\<subseteq>{0..card Y}"
    using S_def by auto
  hence "finite S"
    using finite_subset by blast

  show ?thesis
  proof (cases)
    assume "S={}"
    show ?thesis
    proof
      let ?n = "card Y - 2"
      show "[[(f ?n) b a\<^sub>n]] \<and> ?n < card Y - 1 \<and> \<not>(\<exists>k'<card Y. k'>?n \<and> [[(f k') b a\<^sub>n]])"
      proof (intro conjI)
        show "?n < card Y - 1"
          using Yb abc_ac_neq bound_indices not_le by fastforce
      next show "\<not>(\<exists>k'<card Y. k'>?n \<and> [[(f k') b a\<^sub>n]])"
          using abc_abc_neq bound_indices
          by (metis One_nat_def Suc_diff_le Suc_leD Suc_lessI card_Y diff_Suc_1 diff_Suc_Suc
              not_less_eq numeral_2_eq_2 numeral_3_eq_3)
      next show "[[(f ?n) b a\<^sub>n]]"
        proof -
          have "f ?n \<in> Y"
            by (metis ordering_def diff_less fin_long_chain_def gr_implies_not0 long_ch_Y
                long_ch_by_ord_def neq0_conv not_less_eq numeral_2_eq_2)
          hence "[[a\<^sub>1 (f ?n) a\<^sub>n]]"
            using bound_indices long_ch_Y
            unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
            using card_Y by force
          hence "[[a\<^sub>n b (f ?n)]] \<or> [[a\<^sub>n (f ?n) b]] \<or> [[b a\<^sub>n (f ?n)]]"
            using abc_ex_path_unique some_betw abc_sym
            by (smt Y_def Yb \<open>f ?n \<in> Y\<close> abc_abc_neq cross_once_notin)
          thus "[[(f ?n) b a\<^sub>n]]"
          proof -
            have "\<forall>n. \<not> ([[a\<^sub>n (f n) b]] \<and> n < card Y)"
              using S_def \<open>S = {}\<close>
              by blast
            then have "[[a\<^sub>n b (f ?n)]] \<or> \<not> [[a\<^sub>1 (f ?n) b]] \<and> \<not> [[a\<^sub>n (f ?n) b]]"
              using bound_indices abc_sym abd_bcd_abc Yb
              by (metis (no_types, lifting) \<open>f (card Y - 2) \<in> Y\<close> card_gt_0_iff diff_less empty_iff fin_Y zero_less_numeral)
            then show ?thesis
              using abc_bcd_abd abc_sym
              by (meson \<open>[[a\<^sub>n b (f ?n)]] \<or> [[a\<^sub>n (f ?n) b]] \<or> [[b a\<^sub>n (f ?n)]]\<close> \<open>[[a\<^sub>1 (f ?n) a\<^sub>n]]\<close>)
          qed
        qed
      qed
    qed
  next assume "\<not>S={}"
    obtain k where "k = Min S"
      by simp
    hence  "k \<in> S" using Max_in
      by (simp add: \<open>S \<noteq> {}\<close> \<open>finite S\<close>)

    show ?thesis
    proof
      let ?k = "k-1"
      show "[[(f ?k) b a\<^sub>n]] \<and> ?k < card Y - 1 \<and> \<not> (\<exists>k'<card Y. ?k < k' \<and> [[(f k') b a\<^sub>n]])"
      proof (intro conjI)
        show "?k < card Y - 1"
          using S_def \<open>k \<in> S\<close> less_imp_diff_less card_Y
          by (metis (no_types, lifting) One_nat_def diff_is_0_eq' diff_less_mono lessI less_le_trans
              mem_Collect_eq nat_le_linear numeral_3_eq_3 zero_less_diff)
        show "[[(f ?k) b a\<^sub>n]]"
        proof -
          have "f ?k \<in> Y"
            using \<open>k - 1 < card Y - 1\<close> long_ch_Y long_ch_by_ord_def ordering_def
            by (metis diff_less fin_long_chain_def less_trans neq0_conv zero_less_one)
          have "[[a\<^sub>1 (f ?k) a\<^sub>n]] \<or> f ?k = a\<^sub>1"
            using bound_indices long_ch_Y \<open>k - 1 < card Y - 1\<close>
            unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
            by (smt S_def \<open>k \<in> S\<close> add_diff_inverse_nat card_Diff1_less card_Diff_singleton
                less_numeral_extra(4) less_trans mem_Collect_eq nat_add_left_cancel_less
                neq0_conv zero_less_diff)
          thus  "[[(f ?k) b a\<^sub>n]]"
          proof (rule disjE)
            assume "[[a\<^sub>1 (f ?k) a\<^sub>n]]"
            hence "f ?k \<noteq> a\<^sub>1"
              using abc_abc_neq by blast
            hence "[[a\<^sub>n b (f ?k)]] \<or> [[a\<^sub>n (f ?k) b]] \<or> [[b a\<^sub>n (f ?k)]]"
              using abc_ex_path_unique some_betw abc_sym \<open>[[a\<^sub>1 (f ?k) a\<^sub>n]]\<close>
                \<open>f ?k \<in> Y\<close> Yb abc_abc_neq assms(3) cross_once_notin
              by (smt Y_def)
            moreover have "\<not> [[a\<^sub>n (f ?k) b]]"
            proof
              assume "[[a\<^sub>n (f ?k) b]]"
              hence "?k \<in> S"
                using S_def \<open>[[a\<^sub>n (f ?k) b]]\<close> \<open>k - 1 < card Y - 1\<close>
                by simp
              hence "?k \<ge> k"
                by (simp add: \<open>finite S\<close> \<open>k = Min S\<close>)
              thus False
                using \<open>f (k - 1) \<noteq> a\<^sub>1\<close> fin_long_chain_def long_ch_Y
                by auto
            qed
            moreover have "\<not> [[b a\<^sub>n (f ?k)]]"
              using Yb \<open>[[a\<^sub>1 (f ?k) a\<^sub>n]]\<close> abc_only_cba(2) abc_bcd_acd
              by blast
            ultimately show "[[(f ?k) b a\<^sub>n]]"
              using abc_sym by auto
          next assume "f ?k = a\<^sub>1"
            show ?thesis
              using Yb \<open>f (k - 1) = a\<^sub>1\<close> by blast
          qed
        qed
        show "\<not>(\<exists>k'<card Y. k-1 < k' \<and> [[(f k') b a\<^sub>n]])"
        proof
          assume "\<exists>k'<card Y. k-1 < k' \<and> [[(f k') b a\<^sub>n]]"
          then obtain k' where k'_def: "k'<card Y -1" "k' > k - 1" "[[a\<^sub>n b (f k')]]"
            using abc_ac_neq bound_indices neq0_conv
            by (metis Suc_diff_1 abc_sym gr_implies_not0 less_SucE)
          hence "k'>k"
            using S_def \<open>k \<in> S\<close> abc_only_cba(2) less_SucE
            by (metis (no_types, lifting) add_diff_inverse_nat less_one mem_Collect_eq
                not_less_eq plus_1_eq_Suc)
          hence "k'\<in>S"
            using S_is_dense long_ch_Y S_def \<open>\<not>S={}\<close> \<open>k = Min S\<close> \<open>k'<card Y - 1\<close>
            by (smt Yb \<open>k \<in> S\<close> abc_acd_bcd abc_only_cba(3) card_Diff1_less card_Diff_singleton
                fin_long_chain_def k'_def(3) less_le mem_Collect_eq neq0_conv order_finite_chain)
          thus False
            using S_def abc_only_cba(2) k'_def(3)
            by blast
        qed
      qed
    qed
  qed
qed


lemma get_closest_chain_events:
  assumes long_ch_Y: "[f[a\<^sub>0..a..a\<^sub>n]Y]"
      and x_def: "x\<notin>Y" "[[a\<^sub>0 x a\<^sub>n]]"
    obtains n\<^sub>b n\<^sub>c b c
      where "b=f n\<^sub>b" "c=f n\<^sub>c" "[[b x c]]" "b\<in>Y" "c\<in>Y" "n\<^sub>b = n\<^sub>c - 1" "n\<^sub>c<card Y" "n\<^sub>c>0"
            "\<not>(\<exists>k < card Y. [[(f k) x a\<^sub>n]] \<and> k>n\<^sub>b)" "\<not>(\<exists>k<n\<^sub>c. [[a\<^sub>0 x (f k)]])"
proof -
  have "\<exists> n\<^sub>b n\<^sub>c b c. b=f n\<^sub>b \<and> c=f n\<^sub>c \<and> [[b x c]] \<and> b\<in>Y \<and> c\<in>Y \<and> n\<^sub>b = n\<^sub>c - 1 \<and> n\<^sub>c<card Y \<and> n\<^sub>c>0
    \<and> \<not>(\<exists>k < card Y. [[(f k) x a\<^sub>n]] \<and> k>n\<^sub>b) \<and> \<not>(\<exists>k < n\<^sub>c. [[a\<^sub>0 x (f k)]])"
  proof -
    have bound_indices: "f 0 = a\<^sub>0 \<and> f (card Y - 1) = a\<^sub>n"
      using fin_long_chain_def long_ch_Y by auto
    have "finite Y"
      using fin_long_chain_def long_ch_Y by blast
    obtain P where P_def: "P\<in>\<P>" "Y\<subseteq>P"
      using chain_on_path long_ch_Y
      unfolding fin_long_chain_def ch_by_ord_def
      by blast
    hence "x\<in>P"
      using betw_b_in_path x_def(2) long_ch_Y points_in_chain
      by (metis abc_abc_neq in_mono)
    obtain n\<^sub>c where nc_def: "\<not>(\<exists>k. [[a\<^sub>0 x (f k)]] \<and> k<n\<^sub>c)" "[[a\<^sub>0 x (f n\<^sub>c)]]" "n\<^sub>c<card Y" "n\<^sub>c>0"
      using smallest_k_ex [where a\<^sub>1=a\<^sub>0 and a=a and a\<^sub>n=a\<^sub>n and b=x and f=f and Y=Y]
        long_ch_Y x_def
      by blast
    then obtain c where c_def: "c=f n\<^sub>c" "c\<in>Y"
      using long_ch_Y long_ch_by_ord_def fin_long_chain_def
      by (metis ordering_def)
    have c_goal: "c=f n\<^sub>c \<and> c\<in>Y \<and> n\<^sub>c<card Y \<and> n\<^sub>c>0 \<and> \<not>(\<exists>k < card Y. [[a\<^sub>0 x (f k)]] \<and> k<n\<^sub>c)"
      using c_def nc_def(1,3,4) by blast
    obtain n\<^sub>b where nb_def: "\<not>(\<exists>k < card Y. [[(f k) x a\<^sub>n]] \<and> k>n\<^sub>b)" "[[(f n\<^sub>b) x a\<^sub>n]]" "n\<^sub>b<card Y-1"
      using greatest_k_ex [where a\<^sub>1=a\<^sub>0 and a=a and a\<^sub>n=a\<^sub>n and b=x and f=f and Y=Y]
        long_ch_Y x_def
      by blast
    hence "n\<^sub>b<card Y"
      by linarith
    then obtain b where b_def: "b=f n\<^sub>b" "b\<in>Y"
      using nb_def long_ch_Y long_ch_by_ord_def fin_long_chain_def ordering_def
      by metis
    have "[[b x c]]"
    proof -
      have "[[b x a\<^sub>n]]"
        using b_def(1) nb_def(2) by blast
      have "[[a\<^sub>0 x c]]"
        using c_def(1) nc_def(2) by blast
      moreover have "\<forall>a. [[a x b]] \<or> \<not> [[a a\<^sub>n x]]"
        using \<open>[[b x a\<^sub>n]]\<close> abc_bcd_acd
        by (metis (full_types) abc_sym)
      moreover have "\<forall>a. [[a x b]] \<or> \<not> [[a\<^sub>n a x]]"
        using \<open>[[b x a\<^sub>n]]\<close> by (meson abc_acd_bcd abc_sym)
      moreover have "a\<^sub>n = c \<longrightarrow> [[b x c]]"
        using \<open>[[b x a\<^sub>n]]\<close> by meson
      ultimately show ?thesis
        using abc_abd_bcdbdc abc_sym x_def(2)
        by meson
    qed
    have "n\<^sub>b<n\<^sub>c"
      using \<open>[[b x c]]\<close> \<open>n\<^sub>c<card Y\<close> \<open>n\<^sub>b<card Y\<close> \<open>c = f n\<^sub>c\<close> \<open>b = f n\<^sub>b\<close>
      by (smt (* TODO *)
          \<open>\<And>thesis. (\<And>n\<^sub>b. \<lbrakk>\<not> (\<exists>k<card Y. [[(f k) x a\<^sub>n]] \<and> n\<^sub>b < k); [[(f n\<^sub>b) x a\<^sub>n]]; n\<^sub>b < card Y - 1\<rbrakk>
          \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> abc_abd_acdadc abc_ac_neq abc_only_cba diff_less
          fin_long_chain_def le_antisym le_trans less_imp_le_nat less_numeral_extra(1)
          linorder_neqE_nat long_ch_Y nb_def(2) nc_def(4) order_finite_chain)
    have "n\<^sub>b = n\<^sub>c - 1"
    proof (rule ccontr)
      assume "n\<^sub>b \<noteq> n\<^sub>c - 1"
      have "n\<^sub>b<n\<^sub>c-1"
        using \<open>n\<^sub>b \<noteq> n\<^sub>c - 1\<close> \<open>n\<^sub>b<n\<^sub>c\<close> by linarith
      hence "[[(f n\<^sub>b) (f(n\<^sub>c-1)) (f n\<^sub>c)]]"
        using \<open>n\<^sub>b \<noteq> n\<^sub>c - 1\<close> fin_long_chain_def long_ch_Y nc_def(3) order_finite_chain
        by auto
      have "\<not>[[a\<^sub>0 x (f(n\<^sub>c-1))]]"
        using nc_def(1,4) diff_less less_numeral_extra(1)
        by blast
      have "n\<^sub>c-1\<noteq>0"
        using \<open>n\<^sub>b < n\<^sub>c\<close> \<open>n\<^sub>b \<noteq> n\<^sub>c - 1\<close> by linarith
      hence "f(n\<^sub>c-1)\<noteq>a\<^sub>0 \<and> a\<^sub>0\<noteq>x"
        using bound_indices
        by (metis \<open>[[(f n\<^sub>b) (f (n\<^sub>c - 1)) (f n\<^sub>c)]]\<close> abc_abc_neq abd_bcd_abc b_def(1,2) ch_all_betw_f
            long_ch_Y nb_def(2) nc_def(2))
      have "x\<noteq>f(n\<^sub>c-1)"
        using x_def(1) nc_def(3) long_ch_Y
        unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
        by (metis less_imp_diff_less)
      hence "[[a\<^sub>0 (f (n\<^sub>c-1)) x]]"
        using some_betw P_def(1,2) abc_abc_neq abc_acd_bcd abc_bcd_acd abc_sym b_def(1,2)
              c_def(1,2) ch_all_betw_f in_mono long_ch_Y nc_def(2) betw_b_in_path
        by (smt \<open>[[(f n\<^sub>b) (f (n\<^sub>c-1)) (f n\<^sub>c)]]\<close> \<open>\<not> [[a\<^sub>0 x (f (n\<^sub>c-1))]]\<close> \<open>x \<in> P\<close> \<open>f(n\<^sub>c-1)\<noteq>a\<^sub>0 \<and> a\<^sub>0\<noteq>x\<close>)
      hence "[[(f(n\<^sub>c-1)) x a\<^sub>n]]"
        using abc_acd_bcd x_def(2) by blast
      thus False using nb_def(1)
        using \<open>n\<^sub>b < n\<^sub>c - 1\<close> less_imp_diff_less nc_def(3)
        by blast
    qed
    have b_goal: "b=f n\<^sub>b \<and> b\<in>Y \<and> n\<^sub>b=n\<^sub>c-1 \<and> \<not>(\<exists>k < card Y. [[(f k) x a\<^sub>n]] \<and> k>n\<^sub>b)"
      using b_def nb_def(1) nb_def(3) \<open>n\<^sub>b=n\<^sub>c-1\<close> by blast
    thus ?thesis
      using \<open>[[b x c]]\<close> c_goal
      using \<open>n\<^sub>b < card Y\<close> nc_def(1) by auto
  qed
  thus ?thesis
    using that by auto
qed


text \<open>This is case (ii) of the induction in Theorem 10.\<close>
lemma (*for 10*) chain_append_inside:
  assumes long_ch_Y: "[f[a\<^sub>1..a..a\<^sub>n]Y]"
      and Y_def: "b\<notin>Y"
      and Yb: "[[a\<^sub>1 b a\<^sub>n]]"
      and k_def: "[[a\<^sub>1 b (f k)]]" "k < card Y" "\<not>(\<exists>k'. (0::nat)<k' \<and> k'<k \<and> [[a\<^sub>1 b (f k')]])"
    fixes g
  defines g_def: "g \<equiv> (\<lambda>j::nat. if (j\<le>k-1) then f j else (if (j=k) then b else f (j-1)))"
    shows "[g[a\<^sub>1 .. b .. a\<^sub>n]insert b Y]"
proof -
  let ?X = "insert b Y"
  have fin_X: "finite ?X"
    by (meson fin_long_chain_def finite.insertI long_ch_Y)
  have bound_indices: "f 0 = a\<^sub>1 \<and> f (card Y - 1) = a\<^sub>n"
    using fin_long_chain_def long_ch_Y
    by auto
  have fin_Y: "finite Y"
    using fin_long_chain_def long_ch_Y by blast
  have f_def: "long_ch_by_ord f Y"
    using fin_long_chain_def long_ch_Y by blast
  have  \<open>a\<^sub>1 \<noteq> a\<^sub>n \<and> a\<^sub>1 \<noteq> b \<and> b \<noteq> a\<^sub>n\<close>
    using Yb abc_abc_neq by blast
  have "k \<noteq> 0"
    using abc_abc_neq bound_indices k_def
    by metis

  have b_middle: "[[(f (k-1)) b (f k)]]"
  proof (cases)
    assume "k=1" show "[[(f (k-1)) b (f k)]]"
      using \<open>[[a\<^sub>1 b (f k)]]\<close> \<open>k = 1\<close> bound_indices by auto
  next assume "k\<noteq>1" show "[[(f (k-1)) b (f k)]]"
    proof -
      have "[[a\<^sub>1 (f (k-1)) (f k)]]" using bound_indices
        using \<open>k < card Y\<close> \<open>k \<noteq> 0\<close> \<open>k \<noteq> 1\<close> long_ch_Y fin_Y order_finite_chain
        unfolding fin_long_chain_def
        by auto
      text \<open>In fact, the comprehension below gives the order of elements too.
         Our notation and Theorem 9 are too weak to say that just now.\<close>
      have ch_with_b: "ch {a\<^sub>1, (f (k-1)), b, (f k)}" using chain4
        using k_def(1) abc_ex_path_unique between_chain cross_once_notin
        by (smt \<open>[[a\<^sub>1 (f (k - 1)) (f k)]]\<close> abc_abc_neq insert_absorb2)
(*TODO: the proof below needs extra assumptions, but we should still try to get rid of smt above. *)
      (* proof -
        have "a\<^sub>1\<in>Q \<and> a\<^sub>n\<in>Q \<and> b\<in>Q"
          using Y_def long_ch_Y events_X points_in_chain by auto
        have f1: "a\<^sub>1 \<noteq> b \<and> a\<^sub>1 \<noteq> f k \<and> b \<noteq> f k"
          using abc_abc_neq k_def(1) by presburger
        then have f2: "f k \<in> Q"
          using betw_c_in_path k_def(1) path_Q
            \<open>a\<^sub>1 \<in> Q \<and> a\<^sub>n \<in> Q \<and> b \<in> Q\<close>
          by blast
        then have "f (k - 1) \<in> Q"
          using betw_b_in_path path_Q
            f1 \<open>[[a\<^sub>1 f (k - 1) f k]]\<close> \<open>a\<^sub>1 \<in> Q \<and> a\<^sub>n \<in> Q \<and> b \<in> Q\<close>
          by presburger
        then show ?thesis
          using abc_abc_neq between_chain chain4 k_def(1) path_Q
          by (metis (no_types) f2 \<open>[[a\<^sub>1 f (k - 1) f k]]\<close> \<open>a\<^sub>1 \<in> Q \<and> a\<^sub>n \<in> Q \<and> b \<in> Q\<close>
              insertI1 insert_absorb)
      qed *)
      have "f (k-1) \<noteq> b \<and> (f k) \<noteq> (f (k-1)) \<and> b \<noteq> (f k)"
        using abc_abc_neq f_def k_def(2) Y_def
        by (metis ordering_def \<open>[[a\<^sub>1 (f (k - 1)) (f k)]]\<close> less_imp_diff_less long_ch_by_ord_def)
      hence some_ord_bk: "[[(f (k-1)) b (f k)]] \<or> [[b (f (k-1)) (f k)]] \<or> [[(f (k-1)) (f k) b]]"
        using chain_on_path ch_with_b some_betw Y_def unfolding ch_def
        by (metis abc_sym insert_subset)
      thus "[[(f (k-1)) b (f k)]]"
      proof -
        have "\<not> [[a\<^sub>1 (f k) b]]"
          by (simp add: \<open>[[a\<^sub>1 b (f k)]]\<close> abc_only_cba(2))
        thus ?thesis
          using some_ord_bk k_def abc_bcd_acd abd_bcd_abc bound_indices
          by (metis diff_is_0_eq' diff_less less_imp_diff_less less_irrefl_nat not_less
              zero_less_diff zero_less_one \<open>[[a\<^sub>1 b (f k)]]\<close> \<open>[[a\<^sub>1 (f (k - 1)) (f k)]]\<close>)
      qed
    qed
  qed
  (* not xor but it works anyway *)
  let "?case1 \<or> ?case2" = "k-2 \<ge> 0 \<or> k+1 \<le> card Y -1"

  have b_right: "[[(f (k-2)) (f (k-1)) b]]" if "k \<ge> 2"
  proof -
    have "k-1 < (k::nat)"
      using \<open>k \<noteq> 0\<close> diff_less zero_less_one by blast
    hence "k-2 < k-1"
      using \<open>2 \<le> k\<close> by linarith
    have "[[(f (k-2)) (f (k-1)) (f k)]]"
      using f_def k_def(2) \<open>k-2 < k-1\<close> \<open>k-1 < k\<close> unfolding long_ch_by_ord_def ordering_def
      by blast
    thus "[[(f (k-2)) (f (k-1)) b]]"
      using \<open>[[(f (k - 1)) b (f k)]]\<close> abd_bcd_abc
      by blast
  qed

  have b_left: "[[b (f k) (f (k+1))]]" if "k+1 \<le> card Y -1"
  proof -
    have "[[(f (k-1)) (f k) (f (k+1))]]"
      using \<open>k \<noteq> 0\<close> f_def fin_Y order_finite_chain that
      by auto
    thus "[[b (f k) (f (k+1))]]"
      using \<open>[[(f (k - 1)) b (f k)]]\<close> abc_acd_bcd
      by blast
  qed

  have "ordering2 g betw ?X"
  proof -
    have "\<forall>n. (finite ?X \<longrightarrow> n < card ?X) \<longrightarrow> g n \<in> ?X"
    proof (clarify)
      fix n assume "finite ?X \<longrightarrow> n < card ?X" "g n \<notin> Y"
      consider "n\<le>k-1" | "n\<ge>k+1" | "n=k"
        by linarith
      thus "g n = b"
      proof (cases)
        assume "n \<le> k - 1"
        thus "g n = b"
          using  f_def k_def(2) Y_def(1) long_ch_by_ord_def ordering_def g_def
          by (metis \<open>g n \<notin> Y\<close> \<open>k \<noteq> 0\<close> diff_less le_less less_one less_trans not_le)
      next
        assume "k + 1 \<le> n"
        show "g n = b"
        proof -
          (* assume asm: "Suc k \<le> n" "?X = insert b Y" "b \<notin> Y" "g n \<notin> Y" *)
          have "f n \<in> Y \<or> \<not>(n < card Y)" for n
            by (metis ordering_def f_def long_ch_by_ord_def)
          then show "g n = b"
            using \<open>finite ?X \<longrightarrow> n < card ?X\<close> fin_Y g_def Y_def \<open>g n \<notin> Y\<close> \<open>k + 1 \<le> n\<close>
              not_less not_less_simps(1) not_one_le_zero
            by fastforce
        qed
      next
        assume "n=k"
        thus "g n = b"
          using Y_def \<open>k \<noteq> 0\<close> g_def
          by auto
      qed
    qed
    moreover have "\<forall>x\<in>?X. \<exists>n. (finite ?X \<longrightarrow> n < card ?X) \<and> g n = x"
    proof
      fix x assume "x\<in>?X"
      show "\<exists>n. (finite ?X \<longrightarrow> n < card ?X) \<and> g n = x"
      proof (cases)
        assume "x\<in>Y"
        show ?thesis
        proof -
          obtain ix where "f ix = x" "ix < card Y"
            using  \<open>x \<in> Y\<close> f_def fin_Y
            unfolding long_ch_by_ord_def ordering_def
            by auto
          have "ix\<le>k-1 \<or> ix\<ge>k"
            by linarith
          thus ?thesis
          proof
            assume "ix\<le>k-1"
            hence "g ix = x"
              using \<open>f ix = x\<close> g_def by auto
            moreover have "finite ?X \<longrightarrow> ix < card ?X"
              using Y_def \<open>ix < card Y\<close> by auto
            ultimately show ?thesis by metis
          next assume "ix\<ge>k"
            hence "g (ix+1) = x"
              using \<open>f ix = x\<close> g_def by auto
            moreover have "finite ?X \<longrightarrow> ix+1 < card ?X"
              using Y_def \<open>ix < card Y\<close> by auto
            ultimately show ?thesis by metis
          qed
        qed
      next assume "x\<notin>Y"
        hence "x=b"
          using Y_def \<open>x \<in> ?X\<close> by blast
        thus ?thesis
          using Y_def \<open>k \<noteq> 0\<close> k_def(2) ordered_cancel_comm_monoid_diff_class.le_diff_conv2 g_def
          by auto
      qed
    qed
    moreover have "\<forall>n n' n''. (finite ?X \<longrightarrow> n'' < card ?X) \<and> Suc n = n' \<and> Suc n' = n''
          \<longrightarrow> [[(g n) (g (Suc n)) (g (Suc (Suc n)))]]"
    proof (clarify)
      fix n n' n'' assume  a: "(finite ?X \<longrightarrow> (Suc (Suc n)) < card ?X)"
      
      text \<open>Introduce the two-case splits used later.\<close>
      have  cases_sn: "Suc n\<le>k-1 \<or> Suc n=k" if "n\<le>k-1"
        using \<open>k \<noteq> 0\<close> that by linarith
      have cases_ssn: "Suc(Suc n)\<le>k-1 \<or> Suc(Suc n)=k" if "n\<le>k-1" "Suc n\<le>k-1"
        using that(2) by linarith

      consider "n\<le>k-1" | "n\<ge>k+1" | "n=k"
        by linarith
      then show "[[(g n) (g (Suc n)) (g (Suc (Suc n)))]]"
      proof (cases)
        assume "n\<le>k-1" show ?thesis
          using cases_sn
        proof (rule disjE)
          assume "Suc n \<le> k - 1"
          show ?thesis using cases_ssn
          proof (rule disjE)
            show  "n \<le> k - 1" using \<open>n \<le> k - 1\<close> by blast
            show \<open>Suc n \<le> k - 1\<close> using \<open>Suc n \<le> k - 1\<close> by blast
          next
            assume "Suc (Suc n) \<le> k - 1"
            thus ?thesis
              using  \<open>Suc n \<le> k - 1\<close> \<open>k \<noteq> 0\<close> \<open>n \<le> k - 1\<close> ordering_ord_ijk f_def g_def k_def(2)
              by (metis (no_types, lifting) add_diff_inverse_nat lessI less_Suc_eq_le
                  less_imp_le_nat less_le_trans less_one long_ch_by_ord_def plus_1_eq_Suc)
          next
            assume "Suc (Suc n) = k"
            thus ?thesis
              using b_right g_def by force
          qed
        next
          assume "Suc n = k"
          show ?thesis
            using b_middle \<open>Suc n = k\<close> \<open>n \<le> k - 1\<close> g_def
            by auto
        next show "n \<le> k-1" using \<open>n \<le> k - 1\<close> by blast
        qed
      next assume "n\<ge>k+1" show ?thesis
        proof -
          have "g n = f (n-1)"
            using \<open>k + 1 \<le> n\<close> less_imp_diff_less g_def
            by auto
          moreover have "g (Suc n) = f (n)"
            using \<open>k + 1 \<le> n\<close> g_def by auto
          moreover have "g (Suc (Suc n)) = f (Suc n)"
            using \<open>k + 1 \<le> n\<close> g_def by auto
          moreover have "n-1<n \<and> n<Suc n"
            using \<open>k + 1 \<le> n\<close> by auto
          moreover have "finite Y \<longrightarrow> Suc n < card Y"
            using Y_def a by auto
          ultimately show ?thesis
            using f_def unfolding long_ch_by_ord_def ordering_def
            by auto
        qed
      next assume "n=k"
        show ?thesis
          using \<open>k \<noteq> 0\<close> \<open>n = k\<close> b_left g_def Y_def(1) a assms(3) fin_Y
          by auto
      qed
    qed
    ultimately show "ordering2 g betw ?X"
      unfolding ordering2_def
      by presburger
  qed
  hence "long_ch_by_ord2 g ?X"
    using Y_def f_def long_ch_by_ord2_def long_ch_by_ord_def
    by auto
  thus "[g[a\<^sub>1..b..a\<^sub>n]?X]"
      unfolding fin_long_chain_def
      using ch_equiv fin_X \<open>a\<^sub>1 \<noteq> a\<^sub>n \<and> a\<^sub>1 \<noteq> b \<and> b \<noteq> a\<^sub>n\<close> bound_indices k_def(2) Y_def g_def
      by simp
qed

(* jep *)
lemma card4_eq:
  assumes "card X = 4"
  shows "\<exists>a b c d. a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d \<and> X = {a, b, c, d}"
proof -
  obtain a X' where "X = insert a X'" and "a \<notin> X'"
    by (metis Suc_eq_numeral assms card_Suc_eq)
  then have "card X' = 3"
    by (metis add_2_eq_Suc' assms card_eq_0_iff card_insert_if diff_Suc_1 finite_insert numeral_3_eq_3 numeral_Bit0 plus_nat.add_0 zero_neq_numeral)
  then obtain b X'' where "X' = insert b X''" and "b \<notin> X''"
    by (metis card_Suc_eq numeral_3_eq_3)
  then have "card X'' = 2"
    by (metis Suc_eq_numeral \<open>card X' = 3\<close> card.infinite card_insert_if finite_insert pred_numeral_simps(3) zero_neq_numeral)
  then have "\<exists>c d. c \<noteq> d \<and> X'' = {c, d}"
    by (meson card_2_iff)
  thus ?thesis
    using \<open>X = insert a X'\<close> \<open>X' = insert b X''\<close> \<open>a \<notin> X'\<close> \<open>b \<notin> X''\<close> by blast
qed

(* jep *)
theorem (*10*) path_finsubset_chain:
  assumes "Q \<in> \<P>"
      and "X \<subseteq> Q"
      and "card X \<ge> 2"
  shows "ch X"
proof -
  have "finite X"
    using assms(3) not_numeral_le_zero by fastforce
  consider "card X = 2" | "card X = 3" | "card X \<ge> 4"
    using \<open>card X \<ge> 2\<close> by linarith
  thus ?thesis
  proof (cases)
    assume "card X = 2"
    thus ?thesis
      using \<open>finite X\<close> assms two_event_chain by blast
  next
    assume "card X = 3"
    thus ?thesis
      using \<open>finite X\<close> assms three_event_chain by blast
  next
    assume "card X \<ge> 4"
    thus ?thesis
      using assms(1,2) \<open>finite X\<close>
    proof (induct "card X - 4" arbitrary: X)
      case 0
      then have "card X = 4"
        by auto
      then have "\<exists>a b c d. a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d \<and> X = {a, b, c, d}"
        using card4_eq by fastforce
      thus ?case
        using "0.prems"(3) assms(1) chain4 by auto
    next
      case IH: (Suc n)

      then obtain Y b where X_eq: "X = insert b Y" and "b \<notin> Y"
        by (metis Diff_iff card_eq_0_iff finite.cases insertI1 insert_Diff_single not_numeral_le_zero)
      have "card Y \<ge> 4" "n = card Y - 4"
        using IH.hyps(2) IH.prems(4) X_eq \<open>b \<notin> Y\<close> by auto
      then have "ch Y"
        using IH(1) [of Y] IH.prems(3,4) X_eq assms(1) by auto

      then obtain f where f_ords: "long_ch_by_ord f Y"
        using ch_long_if_card_ge3 \<open>4 \<le> card Y\<close> by fastforce
      then obtain a\<^sub>1 a a\<^sub>n where long_ch_Y: "[f[a\<^sub>1..a..a\<^sub>n]Y]"
        using \<open>4 \<le> card Y\<close> get_fin_long_ch_bounds by fastforce
      hence bound_indices: "f 0 = a\<^sub>1 \<and> f (card Y - 1) = a\<^sub>n"
        by (simp add: fin_long_chain_def)
      have "a\<^sub>1 \<noteq> a\<^sub>n \<and> a\<^sub>1 \<noteq> b \<and> b \<noteq> a\<^sub>n"
        using \<open>b \<notin> Y\<close> abc_abc_neq fin_ch_betw long_ch_Y points_in_chain by blast
      moreover have "a\<^sub>1 \<in> Q \<and> a\<^sub>n \<in> Q \<and> b \<in> Q"
        using IH.prems(3) X_eq long_ch_Y points_in_chain by auto
      ultimately consider "[[b a\<^sub>1 a\<^sub>n]]" | "[[a\<^sub>1 a\<^sub>n b]]" | "[[a\<^sub>n b a\<^sub>1]]"
        using some_betw [of Q b a\<^sub>1 a\<^sub>n] \<open>Q \<in> \<P>\<close> by blast
      thus "ch X"
      proof (cases)
        (* case (i) *)
        assume "[[b a\<^sub>1 a\<^sub>n]]"
        have X_eq': "X = Y \<union> {b}"
          using X_eq by auto
        let ?g = "\<lambda>j. if j \<ge> 1 then f (j - 1) else b"
        have "[?g[b..a\<^sub>1..a\<^sub>n]X]"
          using chain_append_at_left_edge IH.prems(4) X_eq' \<open>[[b a\<^sub>1 a\<^sub>n]]\<close> \<open>b \<notin> Y\<close> long_ch_Y X_eq
          by presburger
        thus "ch X"
          using ch_by_ord_def ch_def fin_long_chain_def by auto
      next
        (* case (ii) *)
        assume "[[a\<^sub>1 a\<^sub>n b]]"
        let ?g = "\<lambda>j. if j \<le> (card X - 2) then f j else b"
        have "[?g[a\<^sub>1..a\<^sub>n..b]X]"
          using chain_append_at_right_edge IH.prems(4) X_eq \<open>[[a\<^sub>1 a\<^sub>n b]]\<close> \<open>b \<notin> Y\<close> long_ch_Y
          by auto
        thus "ch X"
          unfolding ch_def ch_by_ord_def using fin_long_chain_def by auto
      next
        (* case (iii) *)
        assume "[[a\<^sub>n b a\<^sub>1]]" (* jep: I have it this way so it matches some_betw, then switching it so it matches your old proof -- messy but easy to rectify, I'm just too tired to think too hard! *)
        then have "[[a\<^sub>1 b a\<^sub>n]]"
          by (simp add: abc_sym)
        obtain k where
            k_def: "[[a\<^sub>1 b (f k)]]" "k < card Y" "\<not> (\<exists>k'. 0 < k' \<and> k' < k \<and> [[a\<^sub>1 b (f k')]])"
          using \<open>[[a\<^sub>1 b a\<^sub>n]]\<close> \<open>b \<notin> Y\<close> long_ch_Y smallest_k_ex by blast
        obtain g where "g = (\<lambda>j::nat. if j \<le> k - 1
                                        then f j
                                        else if j = k
                                          then b else f (j - 1))"
          by simp
        hence "[g[a\<^sub>1..b..a\<^sub>n]X]"
          using chain_append_inside [of f a\<^sub>1 a a\<^sub>n Y b k] IH.prems(4) X_eq
            \<open>[[a\<^sub>1 b a\<^sub>n]]\<close> \<open>b \<notin> Y\<close> k_def long_ch_Y
          by auto
        thus "ch X"
          using ch_by_ord_def ch_def fin_long_chain_def by auto
      qed
    qed
  qed
qed


lemma path_finsubset_chain2:
  assumes "Q \<in> \<P>" and "X \<subseteq> Q" and "card X \<ge> 2"
  obtains f a b where "[f[a..b]X]"
proof -
  have finX: "finite X"
    by (metis assms(3) card.infinite rel_simps(28))
  have ch_X: "ch X"
    using path_finsubset_chain[OF assms] by blast
  obtain f a b where f_def: "[f[a..b]X]" "a\<in>X \<and> b\<in>X"
    using assms finX ch_X ch_some_betw get_fin_long_ch_bounds ch_long_if_card_ge3
    by (metis ch_by_ord_def ch_def fin_chain_def short_ch_def)
  thus ?thesis
    using that by auto
qed


subsection \<open>Theorem 11\<close>


text \<open>
  Notice this case is so simple, it doesn't even require the path density larger sets of segments
  rely on for fixing their cardinality.
\<close>

lemma (*for 11*) segmentation_ex_N2:
  assumes path_P: "P\<in>\<P>"
      and Q_def: "finite (Q::'a set)" "card Q = N" "Q\<subseteq>P" "N=2"
      and f_def: "[f[a..b]Q]"
      and S_def: "S = {segment a b}"
      and P1_def: "P1 = prolongation b a"
      and P2_def: "P2 = prolongation a b"
    shows "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q) \<and>
           card S = (N-1) \<and> (\<forall>x\<in>S. is_segment x) \<and>
           P1\<inter>P2={} \<and> (\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})))"
proof -
  have "a\<in>Q \<and> b\<in>Q \<and> a\<noteq>b"
    by (metis f_def fin_chain_def fin_long_chain_def points_in_chain)
  hence "Q={a,b}"
    using assms(3,5)
    by (smt card_2_iff insert_absorb insert_commute insert_iff singleton_insert_inj_eq)
  have "a\<in>P \<and> b\<in>P"
    using \<open>Q={a,b}\<close> assms(4) by auto
  have "a\<noteq>b" using \<open>Q={a,b}\<close>
    using \<open>N = 2\<close> assms(3) by force
  obtain s where s_def: "s = segment a b" by simp
  let ?S = "{s}"
  have "P = ((\<Union>{s}) \<union> P1 \<union> P2 \<union> Q) \<and>
          card {s} = (N-1) \<and> (\<forall>x\<in>{s}. is_segment x) \<and>
          P1\<inter>P2={} \<and> (\<forall>x\<in>{s}. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>{s}. x\<noteq>y \<longrightarrow> x\<inter>y={})))"
  proof (rule conjI)
    { fix x assume "x\<in>P"
      have "[[a x b]] \<or> [[b a x]] \<or> [[a b x]] \<or> x=a \<or> x=b"
        using \<open>a\<in>P \<and> b\<in>P\<close> some_betw path_P \<open>a\<noteq>b\<close>
        by (meson \<open>x \<in> P\<close> abc_sym)
      then have "x\<in>s \<or> x\<in>P1 \<or> x\<in>P2 \<or> x=a \<or> x=b"
        using pro_betw seg_betw P1_def P2_def s_def \<open>Q = {a, b}\<close>
        by auto
      hence "x \<in> (\<Union>{s}) \<union> P1 \<union> P2 \<union> Q"
        using \<open>Q = {a, b}\<close> by auto
    } moreover {
      fix x assume "x \<in> (\<Union>{s}) \<union> P1 \<union> P2 \<union> Q"
      hence "x\<in>s \<or> x\<in>P1 \<or> x\<in>P2 \<or> x=a \<or> x=b"
        using \<open>Q = {a, b}\<close> by blast
      hence "[[a x b]] \<or> [[b a x]] \<or> [[a b x]] \<or> x=a \<or> x=b"
        using s_def P1_def P2_def
        unfolding segment_def prolongation_def
        by auto
      hence "x\<in>P"
        using \<open>a \<in> P \<and> b \<in> P\<close> \<open>a \<noteq> b\<close> betw_b_in_path betw_c_in_path path_P
        by blast
    }
    ultimately show union_P: "P = ((\<Union>{s}) \<union> P1 \<union> P2 \<union> Q)"
      by blast
    show "card {s} = (N-1) \<and> (\<forall>x\<in>{s}. is_segment x) \<and> P1\<inter>P2={} \<and>
          (\<forall>x\<in>{s}. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>{s}. x\<noteq>y \<longrightarrow> x\<inter>y={})))"
    proof (safe)
      show "card {s} = N - 1"
        using \<open>Q = {a, b}\<close> \<open>a \<noteq> b\<close> assms(3) by auto
      show "is_segment s"
        using s_def by blast
      {
        fix x assume "x\<in>P1" "x\<in>P2"
        show "x\<in>{}"
          using P1_def P2_def \<open>x \<in> P1\<close> \<open>x \<in> P2\<close> abc_only_cba pro_betw
          by metis
      } {
        fix x assume "x\<in>s" "x\<in>P1"
        show "x\<in>{}"
          using abc_only_cba seg_betw pro_betw  P1_def \<open>x \<in> P1\<close> \<open>x \<in> s\<close> s_def
          by (metis)
      } {
        fix x assume "x\<in>s" "x\<in>P2"
        show "x\<in>{}"
          using abc_only_cba seg_betw pro_betw
          by (metis P2_def \<open>x \<in> P2\<close> \<open>x \<in> s\<close> s_def)
      }
    qed
  qed
  thus ?thesis
    by (simp add: S_def s_def)
qed



lemma int_split_to_segs:
  assumes f_def: "[f[a..b..c]Q]"
  fixes S defines S_def: "S \<equiv> {segment (f i) (f(i+1)) | i. i<card Q-1}"
  shows "interval a c = (\<Union>S) \<union> Q"
proof
  let ?N = "card Q"
  have f_def_2: "a\<in>Q \<and> b\<in>Q \<and> c\<in>Q"
    using f_def points_in_chain by blast
  hence "?N \<ge> 3"
    by (meson ch_by_ord_def f_def fin_long_chain_def long_ch_card_ge3)
  have bound_indices: "f 0 = a \<and> f (card Q - 1) = c"
    using f_def fin_long_chain_def by auto
  let "?i = ?u" = "interval a c = (\<Union>S) \<union> Q"
  show "?i\<subseteq>?u"
  proof
    fix p assume "p \<in> ?i"
    show "p\<in>?u"
    proof (cases)
      assume "p\<in>Q" thus ?thesis by blast
    next assume "p\<notin>Q"
      hence "p\<noteq>a \<and> p\<noteq>c"
        using f_def f_def_2 by blast
      hence "[[a p c]]"
        using seg_betw \<open>p \<in> interval a c\<close> interval_def
        by auto
      then obtain n\<^sub>y n\<^sub>z y z
        where yz_def: "y=f n\<^sub>y" "z=f n\<^sub>z" "[[y p z]]" "y\<in>Q" "z\<in>Q" "n\<^sub>y=n\<^sub>z-1" "n\<^sub>z<card Q"
          "\<not>(\<exists>k < card Q. [[(f k) p c]] \<and> k>n\<^sub>y)" "\<not>(\<exists>k<n\<^sub>z. [[a p (f k)]])"
        using get_closest_chain_events [where f=f and x=p and Y=Q and a\<^sub>n=c and a\<^sub>0=a and a=b]
          f_def \<open>p\<notin>Q\<close>
        by metis
      have "n\<^sub>y<card Q-1"
        using yz_def(6,7) f_def index_middle_element
        by fastforce
      let ?s = "segment (f n\<^sub>y) (f n\<^sub>z)"
      have "p\<in>?s"
        using \<open>[[y p z]]\<close> abc_abc_neq seg_betw yz_def(1,2)
        by blast
      have "n\<^sub>z = n\<^sub>y + 1"
        using yz_def(6)
        by (metis abc_abc_neq add.commute add_diff_inverse_nat less_one yz_def(1,2,3) zero_diff)
      hence "?s\<in>S"
        using S_def \<open>n\<^sub>y<card Q-1\<close> assms(2)
        by blast
      hence "p\<in>\<Union>S"
        using \<open>p \<in> ?s\<close> by blast
      thus ?thesis by blast
    qed
  qed
  show "?u\<subseteq>?i"
  proof
    fix p assume "p \<in> ?u"
    hence "p\<in>\<Union>S \<or> p\<in>Q" by blast
    thus "p\<in>?i"
    proof
      assume "p\<in>Q"
      then consider "p=a"|"p=c"|"[[a p c]]"
        using ch_all_betw_f f_def by blast
      thus ?thesis
      proof (cases)
        assume "p=a"
        thus ?thesis by (simp add: interval_def)
      next assume "p=c"
        thus ?thesis by (simp add: interval_def)
      next assume "[[a p c]]"
        thus ?thesis using interval_def seg_betw by auto
      qed
    next assume "p\<in>\<Union>S"
      then obtain s where "p\<in>s" "s\<in>S"
        by blast
      then obtain y where "s = segment (f y) (f (y+1))" "y<?N-1"
        using S_def by blast
      hence "y+1<?N" by (simp add: assms(2))
      hence fy_in_Q: "(f y)\<in>Q \<and> f (y+1) \<in> Q"
        using f_def unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
        by (meson add_lessD1)
      have "[[a (f y) c]] \<or> y=0"
        using \<open>y <?N - 1\<close> assms(2) f_def fin_long_chain_def order_finite_chain by auto
      moreover have "[[a (f (y+1)) c]] \<or> y = ?N-2"
        using \<open>y + 1 < card Q\<close> assms(2) f_def fin_long_chain_def order_finite_chain
        by (smt One_nat_def Suc_diff_1 Suc_eq_plus1 diff_Suc_eq_diff_pred gr_implies_not0
            lessI less_Suc_eq_le linorder_neqE_nat not_le numeral_2_eq_2)
      ultimately consider "y=0"|"y=?N-2"|"([[a (f y) c]] \<and> [[a (f (y+1)) c]])"
        by linarith
      hence "[[a p c]]"
      proof (cases)
        assume "y=0"
        hence "f y = a"
          by (simp add: bound_indices)
        hence "[[a p (f(y+1))]]"
          using \<open>p \<in> s\<close> \<open>s = segment (f y) (f (y + 1))\<close> seg_betw
          by auto
        moreover have "[[a (f(y+1)) c]]"
          using \<open>[[a (f(y+1)) c]] \<or> y = ?N - 2\<close> \<open>y = 0\<close> \<open>?N\<ge>3\<close>
          by linarith
        ultimately show "[[a p c]]"
          using abc_acd_abd by blast
      next
        assume "y=?N-2"
        hence "f (y+1) = c"
          using bound_indices \<open>?N\<ge>3\<close> numeral_2_eq_2 numeral_3_eq_3
          by (metis One_nat_def Suc_diff_le add.commute add_leD2 diff_Suc_Suc plus_1_eq_Suc)
        hence "[[(f y) p c]]"
          using \<open>p \<in> s\<close> \<open>s = segment (f y) (f (y + 1))\<close> seg_betw
          by auto
        moreover have "[[a (f y) c]]"
          using \<open>[[a (f y) c]] \<or> y = 0\<close> \<open>y = ?N - 2\<close> `?N\<ge>3`
          by linarith
        ultimately show "[[a p c]]"
          by (meson abc_acd_abd abc_sym)
      next
        assume "[[a (f y) c]] \<and> [[a (f(y+1)) c]]"
        thus "[[a p c]]"
          using abe_ade_bcd_ace [where a=a and b="f y" and d="f (y+1)" and e=c and c=p]
          using \<open>p \<in> s\<close> \<open>s = segment (f y) (f(y+1))\<close> seg_betw
          by auto
      qed
      thus ?thesis
        using interval_def seg_betw by auto
    qed
  qed
qed


lemma (*for 11*) path_is_union:
  assumes path_P: "P\<in>\<P>"
      and Q_def: "finite (Q::'a set)" "card Q = N" "Q\<subseteq>P" "N\<ge>3"
      and f_def: "a\<in>Q \<and> b\<in>Q \<and> c\<in>Q" "[f[a..b..c]Q]"
      and S_def: "S = {s. \<exists>i<(N-1). s = segment (f i) (f (i+1))}"
      and P1_def: "P1 = prolongation b a"
      and P2_def: "P2 = prolongation b c"
    shows "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)"
proof -
  (* For future use, as always *)
  have in_P: "a\<in>P \<and> b\<in>P \<and> c\<in>P"
    using assms(4) f_def by blast
  have bound_indices: "f 0 = a \<and> f (card Q - 1) = c"
    using f_def fin_long_chain_def by auto
  have points_neq: "a\<noteq>b \<and> b\<noteq>c \<and> a\<noteq>c"
    using f_def fin_long_chain_def by auto

  text \<open>The proof in two parts: subset inclusion one way, then the other.\<close>
  { fix x assume "x\<in>P"
    have "[[a x c]] \<or> [[b a x]] \<or> [[b c x]] \<or> x=a \<or> x=c"
      using in_P some_betw path_P points_neq \<open>x \<in> P\<close> abc_sym
      by (metis (full_types) abc_acd_bcd ch_all_betw_f f_def)
    then have "(\<exists>s\<in>S. x\<in>s) \<or> x\<in>P1 \<or> x\<in>P2 \<or> x\<in>Q"
    proof (cases)
      assume "[[a x c]]"
      hence only_axc: "\<not>([[b a x]] \<or> [[b c x]] \<or> x=a \<or> x=c)"
        using abc_only_cba
        by (meson abc_bcd_abd abc_sym f_def fin_ch_betw)
      have "x \<in> interval a c"
        using \<open>[[a x c]]\<close> interval_def seg_betw by auto
      hence "x\<in>Q \<or> x\<in>\<Union>S"
        using int_split_to_segs S_def assms(2,3,5) f_def
        by blast
      thus ?thesis by blast
    next assume "\<not>[[a x c]]"
      hence "[[b a x]] \<or> [[b c x]] \<or> x=a \<or> x=c"
        using \<open>[[a x c]] \<or> [[b a x]] \<or> [[b c x]] \<or> x = a \<or> x = c\<close> by blast
      hence " x\<in>P1 \<or> x\<in>P2 \<or> x\<in>Q"
        using P1_def P2_def f_def pro_betw by auto
      thus ?thesis by blast
    qed
    hence "x \<in> (\<Union>S) \<union> P1 \<union> P2 \<union> Q" by blast
  } moreover {
    fix x assume "x \<in> (\<Union>S) \<union> P1 \<union> P2 \<union> Q"
    hence "(\<exists>s\<in>S. x\<in>s) \<or> x\<in>P1 \<or> x\<in>P2 \<or> x\<in>Q"
      by blast
    hence "x\<in>\<Union>S \<or> [[b a x]] \<or> [[b c x]] \<or> x\<in>Q"
      using S_def P1_def P2_def
      unfolding segment_def prolongation_def
      by auto
    hence "x\<in>P"
    proof (cases)
      assume "x\<in>\<Union>S"
      have "S = {segment (f i) (f(i+1)) | i. i<N-1}"
        using S_def by blast
      hence "x\<in>interval a c"
        using int_split_to_segs [OF f_def(2)] assms `x\<in>\<Union>S`
        by (simp add: UnCI)
      hence "[[a x c]] \<or> x=a \<or> x=c"
        using interval_def seg_betw by auto
      thus ?thesis
      proof (rule disjE)
        assume "x=a \<or> x=c"
        thus ?thesis
          using in_P by blast
      next
        assume "[[a x c]]"
        thus ?thesis
          using betw_b_in_path in_P path_P points_neq by blast
      qed
     next assume "x\<notin>\<Union>S"
      hence "[[b a x]] \<or> [[b c x]] \<or> x\<in>Q"
        using \<open>x \<in> \<Union> S \<or> [[b a x]] \<or> [[b c x]] \<or> x \<in> Q\<close>
        by blast
      thus ?thesis
        using assms(4) betw_c_in_path in_P path_P points_neq
        by blast
    qed
  }
  ultimately show "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)"
    by blast
qed


lemma (*for 11*) inseg_axc:
  assumes path_P: "P\<in>\<P>"
      and Q_def: "finite (Q::'a set)" "card Q = N" "Q\<subseteq>P" "N\<ge>3"
      and f_def: "a\<in>Q \<and> b\<in>Q \<and> c\<in>Q" "[f[a..b..c]Q]"
      and S_def: "S = {s. \<exists>i<(N-1). s = segment (f i) (f (i+1))}"
      and x_def: "x\<in>s" "s\<in>S"
    shows "[[a x c]]"
proof -
  have inseg_neq_ac: "x\<noteq>a \<and> x\<noteq>c" if "x\<in>s" "s\<in>S" for x s
  proof
    show "x\<noteq>a"
    proof (rule notI)
      assume "x=a"
      obtain n where s_def: "s = segment (f n) (f (n+1))" "n<N-1"
        using S_def \<open>s \<in> S\<close> by blast
      have "f n \<in> Q"
        using f_def \<open>n < N - 1\<close> fin_long_chain_def long_ch_by_ord_def ordering_def
        by (metis assms(3) diff_diff_cancel less_imp_diff_less less_irrefl_nat not_less)
      hence "[[a (f n) c]]"
        using f_def fin_long_chain_def assms(3) order_finite_chain seg_betw that(1)
        using \<open>n < N - 1\<close> \<open>s = segment (f n) (f (n + 1))\<close> \<open>x = a\<close>
        by (metis abc_abc_neq add_lessD1 ch_all_betw_f inside_not_bound(2) less_diff_conv)
      moreover have "[[(f(n)) x (f(n+1))]]"
        using \<open>x\<in>s\<close> seg_betw s_def(1) by simp
      ultimately show False
        using \<open>x=a\<close> abc_only_cba(1) assms(3) f_def fin_long_chain_def s_def(2) order_finite_chain
        by (metis le_numeral_extra(3) less_add_one less_diff_conv neq0_conv)
    qed

    show "x\<noteq>c"
    proof (rule notI)
      assume "x=c"
      obtain n where s_def: "s = segment (f n) (f (n+1))" "n<N-1"
        using S_def \<open>s \<in> S\<close> by blast
      hence "n+1<N" by simp
      have "[[(f(n)) x (f(n+1))]]"
        using \<open>x\<in>s\<close> seg_betw s_def(1) by simp
      have "f (n) \<in> Q"
        using f_def \<open>n+1 < N\<close> fin_long_chain_def long_ch_by_ord_def ordering_def
        by (metis add_lessD1 assms(3))
      have "f (n+1) \<in> Q"
        using f_def \<open>n+1 < N\<close> fin_long_chain_def long_ch_by_ord_def ordering_def
        by (metis assms(3))
      have "f(n+1) \<noteq> c"
        using \<open>x=c\<close> \<open>[[(f(n)) x (f(n+1))]]\<close> abc_abc_neq
        by blast
      hence "[[a (f(n+1)) c]]"
        using f_def fin_long_chain_def assms(3) order_finite_chain seg_betw that(1)
          abc_abc_neq abc_only_cba ch_all_betw_f
        by (metis \<open>[[(f n) x (f (n + 1))]]\<close> \<open>f (n + 1) \<in> Q\<close> \<open>f n \<in> Q\<close> \<open>x = c\<close>)
      thus False
        using \<open>x=c\<close> \<open>[[(f(n)) x (f(n+1))]]\<close> assms(3) f_def s_def(2)
          abc_only_cba(1) fin_long_chain_def order_finite_chain
        by (metis \<open>f n \<in> Q\<close> abc_bcd_acd abc_only_cba(1,2) ch_all_betw_f)
    qed
  qed

  show "[[a x c]]"
  proof -
    have "x\<in>interval a c"
      using int_split_to_segs [OF f_def(2)] S_def assms(2,3,5) x_def
      by blast
    have "x\<noteq>a \<and> x\<noteq>c" using inseg_neq_ac
      using x_def by auto
    thus ?thesis
      using seg_betw \<open>x \<in> interval a c\<close> interval_def
      by auto
  qed
qed


lemma disjoint_segmentation:
  assumes path_P: "P\<in>\<P>"
      and Q_def: "finite (Q::'a set)" "card Q = N" "Q\<subseteq>P" "N\<ge>3"
      and f_def: "a\<in>Q \<and> b\<in>Q \<and> c\<in>Q" "[f[a..b..c]Q]"
      and S_def: "S = {s. \<exists>i<(N-1). s = segment (f i) (f (i+1))}"
      and P1_def: "P1 = prolongation b a"
      and P2_def: "P2 = prolongation b c"
    shows "P1\<inter>P2={} \<and> (\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})))"
proof (rule conjI)
  show "P1 \<inter> P2 = {}"
  proof (safe)
    fix x assume "x\<in>P1" "x\<in>P2"
    show "x\<in>{}"
      using abc_only_cba pro_betw P1_def P2_def
      by (metis \<open>x \<in> P1\<close> \<open>x \<in> P2\<close> abc_bcd_abd f_def(2) fin_ch_betw)
  qed

  show "\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={}))"
  proof (rule ballI)
    fix s assume "s\<in>S"
    show "s \<inter> P1 = {} \<and> s \<inter> P2 = {} \<and> (\<forall>y\<in>S. s \<noteq> y \<longrightarrow> s \<inter> y = {})"
    proof (intro conjI ballI impI)
      show "s\<inter>P1={}"
      proof (safe)
        fix x assume "x\<in>s" "x\<in>P1"
        hence "[[a x c]]"
          using inseg_axc \<open>s \<in> S\<close> assms by blast
        thus "x\<in>{}"
          by (metis P1_def \<open>x \<in> P1\<close> abc_bcd_abd abc_only_cba(1) f_def(2) fin_ch_betw pro_betw)
      qed
      show "s\<inter>P2={}"
      proof (safe)
        fix x assume "x\<in>s" "x\<in>P2"
        hence "[[a x c]]"
          using inseg_axc \<open>s \<in> S\<close> assms by blast
        thus "x\<in>{}"
          by (metis P2_def \<open>x \<in> P2\<close> abc_bcd_acd abc_only_cba(2) f_def(2) fin_ch_betw pro_betw)
      qed
      fix r assume "r\<in>S" "s\<noteq>r"
      show "s\<inter>r={}"
      proof (safe)
        fix y assume "y \<in> r" "y \<in> s"
        obtain n m where rs_def: "r = segment (f n) (f(n+1))" "s = segment (f m) (f(m+1))"
                                 "n\<noteq>m" "n<N-1" "m<N-1"
          using S_def \<open>r \<in> S\<close> \<open>s \<noteq> r\<close> \<open>s \<in> S\<close> by blast
        have y_betw: "[[(f n) y (f(n+1))]] \<and> [[(f m) y (f(m+1))]]"
          using seg_betw \<open>y\<in>r\<close> \<open>y\<in>s\<close> rs_def(1,2) by simp
        have False
        proof (cases)
          assume "n<m"
          have "[[(f n) (f m) (f(m+1))]]"
            using \<open>n < m\<close> assms(3) f_def fin_long_chain_def order_finite_chain rs_def(5) by auto
          have "n+1<m" (* NOTICE: this is astounding. in principle, r and s could be adjacent? must be the False in the assumptions. *)
            using \<open>[[(f n) (f m) (f(m + 1))]]\<close> \<open>n < m\<close> abc_only_cba(2) abd_bcd_abc y_betw
            by (metis Suc_eq_plus1 Suc_leI le_eq_less_or_eq)
          hence "[[(f n) (f(n+1)) (f m)]]"
            using f_def assms(3) rs_def(5)
            unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
            by (metis add_lessD1 less_add_one less_diff_conv)
          hence "[[(f n) (f(n+1)) y]]"
            using \<open>[[(f n) (f m) (f(m + 1))]]\<close> abc_acd_abd abd_bcd_abc y_betw
            by blast
          thus ?thesis
            using abc_only_cba y_betw by blast
        next
          assume "\<not>n<m"
          hence "n>m" using nat_neq_iff rs_def(3) by blast
          have "[[(f m) (f n) (f(n+1))]]"
            using \<open>n > m\<close> assms(3) f_def fin_long_chain_def order_finite_chain rs_def(4) by auto
          hence "m+1<n"
            using  \<open>n > m\<close> abc_only_cba(2) abd_bcd_abc y_betw
            by (metis Suc_eq_plus1 Suc_leI le_eq_less_or_eq)
          hence "[[(f m) (f(m+1)) (f n)]]"
            using f_def assms(3) rs_def(4)
            unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
            by (metis add_lessD1 less_add_one less_diff_conv)
          hence "[[(f m) (f(m+1)) y]]"
            using \<open>[[(f m) (f n) (f(n + 1))]]\<close> abc_acd_abd abd_bcd_abc y_betw
            by blast
          thus ?thesis
            using abc_only_cba y_betw by blast
        qed
        thus "y\<in>{}" by blast
      qed
    qed
  qed
qed


lemma (*for 11*) segmentation_ex_Nge3:
  assumes path_P: "P\<in>\<P>"
      and Q_def: "finite (Q::'a set)" "card Q = N" "Q\<subseteq>P" "N\<ge>3"
      and f_def: "a\<in>Q \<and> b\<in>Q \<and> c\<in>Q" "[f[a..b..c]Q]"
      and S_def: "S = {s. \<exists>i<(N-1). s = segment (f i) (f (i+1))}"
      and P1_def: "P1 = prolongation b a"
      and P2_def: "P2 = prolongation b c"
    shows "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q) \<and>
           (\<forall>x\<in>S. is_segment x) \<and>
           P1\<inter>P2={} \<and> (\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})))"
proof -
  have "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q) \<and>
          (\<forall>x\<in>S. is_segment x) \<and> P1\<inter>P2={} \<and>
          (\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})))"
  proof (intro disjoint_segmentation conjI)
    show "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)"
      using path_is_union assms
      by blast
    show "\<forall>x\<in>S. is_segment x"
    proof
      fix s assume "s\<in>S"
      thus "is_segment s" using S_def by auto
    qed
  qed (use assms disjoint_segmentation in auto)
  then show ?thesis by auto
qed

text \<open>
  We define \<open>disjoint\<close> to be the same as in HOL-Library.DisjointSets.
  This saves importing a lot of baggage we don't need.
  The two lemmas below are just for safety.
\<close>

abbreviation disjoint
  where "disjoint A \<equiv> (\<forall>a\<in>A. \<forall>b\<in>A. a \<noteq> b \<longrightarrow> a \<inter> b = {})"

lemma
  fixes S:: "('a set) set" and P1:: "'a set" and P2:: "'a set"
  assumes "\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={}))" "P1\<inter>P2={}"
  shows "disjoint (S\<union>{P1,P2})"
proof (rule ballI)
  let ?U = "S\<union>{P1,P2}"
  fix a assume "a\<in>?U"
  then consider (aS)"a\<in>S"|(a1)"a=P1"|(a2)"a=P2"
    by fastforce
  thus "\<forall>b\<in>?U. a \<noteq> b \<longrightarrow> a \<inter> b = {}"
  proof cases
    case aS
    { fix b assume "b\<in>?U" "a\<noteq>b"
      then consider "b\<in>S"|"b=P1"|"b=P2"
        by fastforce
      hence "a\<inter>b={}"
        apply cases
        apply (simp add: \<open>a \<in> S\<close> \<open>a \<noteq> b\<close> assms)
        apply (meson \<open>a \<in> S\<close> assms)
        by (simp add: \<open>a \<in> S\<close> assms)
    }
    thus ?thesis
      by meson
  next
    case a1
    { fix b assume "b\<in>?U" "a\<noteq>b"
      then consider "b\<in>S"|"b=P2"
        using a1 by fastforce
      hence "a\<inter>b={}"
        apply cases
        apply (metis a1 assms(1) inf_commute)
        by (simp add: a1 assms(2))
    }
    thus ?thesis
      by meson
  next
    case a2
    { fix b assume "b\<in>?U" "a\<noteq>b"
      then consider "b\<in>S"|"b=P1"
        using a2 by fastforce
      hence "a\<inter>b={}"
        apply cases
        apply (metis a2 assms(1) inf_commute)
        by (simp add: a2 assms(2) inf_commute)
    }
    thus ?thesis
      by meson
  qed
qed
lemma
  fixes S:: "('a set) set" and P1:: "'a set" and P2:: "'a set"
  assumes "disjoint (S\<union>{P1,P2})" "P1\<notin>S" "P2\<notin>S" "P1\<noteq>P2"
  shows "\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={}))" "P1\<inter>P2={}"
proof (rule ballI)
  show "P1\<inter>P2={}"
    using assms(1,4) by simp
  fix x assume "x\<in>S"
  show "x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})"
  proof (rule conjI, rule_tac[2] conjI, rule_tac[3] ballI, rule_tac[3] impI)
    show "x\<inter>P1={}"
      using \<open>x \<in> S\<close> assms(1,2) by fastforce
    show "x\<inter>P2={}"
      using \<open>x \<in> S\<close> assms(1,3) by fastforce
    fix y assume "y\<in>S" "x\<noteq>y"
    thus "x\<inter>y={}"
      by (simp add: \<open>x \<in> S\<close> assms(1))
  qed
qed


text \<open>
  Schutz says "As in the proof of the previous theorem [...]" - does he mean to imply that this
  should really be proved as induction? I can see that quite easily, induct on $N$, and add a segment
  by either splitting up a segment or taking a piece out of a prolongation.
  But I think that might be too much trouble.
\<close>

theorem (*11*) show_segmentation:  
  assumes path_P: "P\<in>\<P>"
      and Q_def: "Q\<subseteq>P"
      and f_def: "[f[a..b]Q]"
    fixes P1 defines P1_def: "P1 \<equiv> prolongation b a"
    fixes P2 defines P2_def: "P2 \<equiv> prolongation a b"
    fixes S  defines S_def: "S \<equiv> if card Q=2 then {segment a b}
                                 else {segment (f i) (f (i+1)) | i. i<card Q-1}"
    shows "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)" "(\<forall>x\<in>S. is_segment x)"
          "disjoint (S\<union>{P1,P2})" "P1\<noteq>P2" "P1\<notin>S" "P2\<notin>S"
proof -
  have card_Q: "card Q \<ge> 2"
    using fin_chain_card_geq_2 f_def by blast
  have "finite Q"
    by (metis card.infinite card_Q rel_simps(28))
(* Hooray for theorem 10! Without it, we couldn't so brazenly go from a set of events
   to an ordered chain of events. The line below doesn't need f_def (which is needed for S_def)! *)
  have ch_Q: "ch Q"
    using Q_def card_Q path_P path_finsubset_chain [where X=Q and Q=P]
    by blast
  have f_def_2: "a\<in>Q \<and> b\<in>Q"
    using f_def points_in_chain fin_chain_def by auto
  have "a\<noteq>b"
    using f_def fin_chain_def fin_long_chain_def by auto
  {
    assume "card Q = 2"
    hence "S={segment a b}"
      by (simp add: S_def)
    have "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)" "(\<forall>x\<in>S. is_segment x)" "P1\<inter>P2={}"
         "(\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})))"
      using assms ch_Q \<open>finite Q\<close> segmentation_ex_N2
        [where P=P and Q=Q and N="card Q"]
      by (metis (no_types, lifting) \<open>card Q = 2\<close>)+
  } moreover {
    assume "card Q \<noteq> 2"
    hence "card Q \<ge> 3"
      using card_Q by auto
    then obtain c where c_def: "[f[a..c..b]Q]"
      using assms(3,5) \<open>a\<noteq>b\<close>
      by (metis f_def fin_chain_def short_ch_def three_in_set3)
    have pro_equiv: "P1 = prolongation c a \<and> P2 = prolongation c b"
      using pro_basis_change
      using P1_def P2_def abc_sym c_def fin_ch_betw by auto
    have S_def2: "S = {s. \<exists>i<(card Q-1). s = segment (f i) (f (i+1))}"
      using S_def \<open>card Q \<ge> 3\<close> by auto
    have "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)" "(\<forall>x\<in>S. is_segment x)" "P1\<inter>P2={}"
         "(\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})))"
      using f_def_2 assms ch_Q \<open>card Q \<ge> 3\<close> c_def pro_equiv
        segmentation_ex_Nge3 [where P=P and Q=Q and N="card Q" and S=S and a=a and b=c and c=b and f=f]
      using points_in_chain \<open>finite Q\<close> S_def2 by presburger+
  }
  ultimately have old_thesis: "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)" "(\<forall>x\<in>S. is_segment x)" "P1\<inter>P2={}"
                  "(\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})))" by meson+
  thus "disjoint (S\<union>{P1,P2})" "P1\<noteq>P2" "P1\<notin>S" "P2\<notin>S"
       "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)" "(\<forall>x\<in>S. is_segment x)"
         apply (simp add: Int_commute)
        apply (metis P2_def Un_iff old_thesis(1,3) \<open>a \<noteq> b\<close> disjoint_iff f_def_2 path_P pro_betw prolong_betw2)
       apply (metis P1_def Un_iff old_thesis(1,4) \<open>a \<noteq> b\<close> disjoint_iff f_def_2 path_P pro_betw prolong_betw3)
      apply (metis P2_def Un_iff old_thesis(1,4) \<open>a \<noteq> b\<close> disjoint_iff f_def_2 path_P pro_betw prolong_betw)
    using old_thesis(1,2) by linarith+
qed


theorem (*11*) segmentation:
  assumes path_P: "P\<in>\<P>"
      and Q_def: "card Q\<ge>2" "Q\<subseteq>P"
    shows "\<exists>S P1 P2. P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q) \<and>
                     disjoint (S\<union>{P1,P2}) \<and> P1\<noteq>P2 \<and> P1\<notin>S \<and> P2\<notin>S \<and>
                     (\<forall>x\<in>S. is_segment x) \<and> is_prolongation P1 \<and> is_prolongation P2"
proof -
  let ?N = "card Q"
  obtain f a b where f_def: "[f[a..b]Q]"
    using path_finsubset_chain2[OF path_P Q_def(2,1)]
    by metis
  let ?S = "if ?N=2 then {segment a b} else {segment (f i) (f (i+1)) | i. i<card Q-1}"
  let ?P1 = "prolongation b a"
  let ?P2 = "prolongation a b"
  have from_seg: "P = ((\<Union>?S) \<union> ?P1 \<union> ?P2 \<union> Q)" "(\<forall>x\<in>?S. is_segment x)"
          "disjoint (?S\<union>{?P1,?P2})" "?P1\<noteq>?P2" "?P1\<notin>?S" "?P2\<notin>?S"
    using show_segmentation[OF path_P Q_def(2) `[f[a..b]Q]`]
    by force+
  thus ?thesis
    by blast
qed


  
end (* context MinkowskiSpacetime *)


section "Chains are unique up to reversal"

lemma (in MinkowskiSpacetime) chain_remove_at_right_edge:
  assumes "[f[a..c]X]" "f (card X - 2) = p" "3 \<le> card X" "X = insert c Y" "c\<notin>Y"
  shows "[f[a..p]Y]"
proof -

  have lch_X: "long_ch_by_ord f X"
    using assms(1,3) fin_chain_def fin_long_chain_def ch_by_ord_def short_ch_card_2
    by fastforce
  have "p\<in>X"
    by (metis ordering_def assms(2,3) card.empty card_gt_0_iff diff_less lch_X
        long_ch_by_ord_def not_numeral_le_zero zero_less_numeral)
  have bound_ind: "f 0 = a \<and> f (card X - 1) = c"
    using lch_X assms(1,3) unfolding fin_chain_def fin_long_chain_def
    by (metis (no_types, hide_lams) One_nat_def Suc_1 ch_by_ord_def diff_Suc_Suc
        less_Suc_eq_le neq0_conv numeral_3_eq_3 short_ch_card_2 zero_less_diff)
  
  have "[[a p c]]"
  proof -
    have "card X - 2 < card X - 1"
      using \<open>3 \<le> card X\<close> by auto
    moreover have "card X - 2 > 0"
      using \<open>3 \<le> card X\<close> by linarith
    ultimately show ?thesis
      using assms(2) lch_X bound_ind \<open>3 \<le> card X\<close> unfolding long_ch_by_ord_def ordering_def
      by (metis One_nat_def diff_Suc_less less_le_trans zero_less_numeral)
  qed
  hence "p\<noteq>c"
    using abc_abc_neq by blast
  hence "p\<in>Y"
    using \<open>p \<in> X\<close> assms(4) by blast

  show ?thesis
  proof (cases)
    assume "3 = card X"
    hence "2 = card Y"
      by (metis assms(4,5) card.insert card.infinite diff_Suc_1 finite_insert nat.simps(3)
          numeral_2_eq_2 numeral_3_eq_3)
    have "a\<noteq>p"
      using \<open>[[a p c]]\<close> abc_abc_neq by auto
    moreover have "a\<in>Y \<and> p\<in>Y"
      using \<open>[[a p c]]\<close> \<open>p \<in> Y\<close> abc_abc_neq assms(1,4) fin_chain_def points_in_chain
      by fastforce
    moreover have "short_ch Y"
    proof -
      obtain ap where "path ap a p"
        using \<open>[[a p c]]\<close> abc_ex_path_unique calculation(1) by blast
      hence "\<exists>Q. path Q a p"
        by blast
      moreover have "\<not> (\<exists>z\<in>Y. z \<noteq> a \<and> z \<noteq> p)"
        using \<open>2 = card Y\<close> \<open>a \<in> Y \<and> p \<in> Y\<close> \<open>a \<noteq> p\<close>
        by (metis card_2_iff')
      ultimately show ?thesis
        unfolding short_ch_def using \<open>a \<in> Y \<and> p \<in> Y\<close>
        by blast
    qed
    ultimately show ?thesis unfolding fin_chain_def by blast
  next
    assume "3 \<noteq> card X"
    hence "4 \<le> card X"
      using assms(3) by auto
  
    obtain b where "b = f 1" by simp
    have "\<exists>b. [f[a..b..p]Y]"
    proof
      have "[[a b p]]"
        using bound_ind \<open>b = f 1\<close> \<open>3 \<noteq> card X\<close> assms(2,3) lch_X order_finite_chain
        by fastforce
      hence all_neq: "b\<noteq>a \<and> b\<noteq>p \<and> a\<noteq>p"
        using abc_abc_neq by blast
      have "b\<in>X"
        using \<open>b = f 1\<close> lch_X assms(3) unfolding long_ch_by_ord_def ordering_def
        by force
      hence "b\<in>Y"
        using \<open>[[a b p]]\<close> \<open>[[a p c]]\<close> abc_only_cba(2) assms(4) by blast
  
      have "ordering f betw Y"
        unfolding ordering_def
      proof (safe)
        show "\<And>n. infinite Y \<Longrightarrow> f n \<in> Y"
          using assms(3) assms(4) by auto
        show "\<And>n. n < card Y \<Longrightarrow> f n \<in> Y"
          using assms(3,4,5) bound_ind lch_X
          unfolding long_ch_by_ord_def ordering_def
          using get_fin_long_ch_bounds indices_neq_imp_events_neq
          by (smt Suc_less_eq add_leD1 cancel_comm_monoid_add_class.diff_cancel card_Diff1_less
              card_Diff_singleton card_eq_0_iff card_insert_disjoint gr_implies_not0 insert_iff lch_X
              le_add_diff_inverse less_SucI numeral_3_eq_3 plus_1_eq_Suc zero_less_diff)
        { 
          fix x assume "x\<in>Y"
          hence "x\<in>X"
            using assms(4) by blast
          then obtain n where "n < card X" "f n = x"
            using lch_X unfolding long_ch_by_ord_def ordering_def
            using assms(3) by auto
          show "\<exists>n. (finite Y \<longrightarrow> n < card Y) \<and> f n = x"
          proof
            show "(finite Y \<longrightarrow> n < card Y) \<and> f n = x"
              using \<open>f n = x\<close> \<open>n < card X\<close> \<open>x \<in> Y\<close> assms(4,5) bound_ind
              by (metis Diff_insert_absorb card.remove card_Diff_singleton
                  finite.insertI insertI1 less_SucE)
          qed
        }
        fix n n' n''
        assume "(n::nat)<n'" "n'<n''"
        {
          assume "infinite Y"
          show "[[(f n) (f n') (f n'')]]"
            using \<open>\<And>n. infinite Y \<Longrightarrow> f n \<in> Y\<close> \<open>infinite Y\<close> assms(5) bound_ind by blast
        } {
          assume "n'' < card Y"
          show "[[(f n) (f n') (f n'')]]"
            using \<open>n < n'\<close> \<open>n' < n''\<close> \<open>n'' < card Y\<close> assms(4,5) lch_X order_finite_chain
            using \<open>infinite Y \<Longrightarrow> [[(f n) (f n') (f n'')]]\<close> by fastforce
        }
      qed
      hence lch_Y: "long_ch_by_ord f Y"
        using \<open>[[a p c]]\<close> \<open>b \<in> Y\<close> \<open>p \<in> X\<close> abc_abc_neq all_neq assms(4) bound_ind
          long_ch_by_ord_def zero_into_ordering
        by fastforce
  
      show "[f[a..b..p]Y]"
        using all_neq lch_Y bound_ind \<open>b\<in>Y\<close> assms(2,3,4,5) unfolding fin_long_chain_def
        by (metis Diff_insert_absorb One_nat_def add_leD1 card.infinite finite_insert plus_1_eq_Suc
            diff_diff_left card_Diff_singleton not_one_le_zero insertI1 numeral_2_eq_2 numeral_3_eq_3)
    qed
  
    thus ?thesis unfolding fin_chain_def
      using points_in_chain by blast
  qed
qed


lemma (in MinkowskiChain) fin_long_ch_imp_fin_ch:
  assumes "[f[a..b..c]X]"
  shows "[f[a..c]X]"
  using assms fin_chain_def points_in_chain by auto


text \<open>
  If we ever want to have chains less strongly identified by endpoints,
  this result should generalise - $a,c,x,z$ are only used to identify reversal/no-reversal cases.
\<close>
lemma (in MinkowskiSpacetime) chain_unique_induction_ax:
  assumes "card X \<ge> 3"
      and "i < card X"
      and "[f[a..c]X]"
      and "[g[x..z]X]"
      and "a = x \<or> c = z"
    shows "f i = g i"
using assms
proof (induct "card X - 3" arbitrary: X a c x z)
  case Nil: 0
  have "card X = 3"
    using Nil.hyps Nil.prems(1) by auto

  obtain b where f_ch: "[f[a..b..c]X]"
    by (metis Nil.prems(1,3) fin_chain_def short_ch_def three_in_set3)
  obtain y where g_ch: "[g[x..y..z]X]"
    using Nil.prems fin_chain_def short_ch_card_2
    by (metis Suc_n_not_le_n ch_by_ord_def numeral_2_eq_2 numeral_3_eq_3)

  have "i=1 \<or> i=0 \<or> i=2"
    using \<open>card X = 3\<close> Nil.prems(2) by linarith
  thus ?case
  proof (rule disjE)
    assume "i=1"
    hence "f i = b \<and> g i = y"
      using index_middle_element f_ch g_ch \<open>card X = 3\<close> numeral_3_eq_3
      by (metis One_nat_def add_diff_cancel_left' less_SucE not_less_eq plus_1_eq_Suc)
    have "f i = g i"
    proof (rule ccontr)
      assume "f i \<noteq> g i"
      hence "g i \<noteq> b"
        by (simp add: \<open>f i = b \<and> g i = y\<close>)
      have "g i \<in> X"
        using \<open>f i = b \<and> g i = y\<close>  g_ch points_in_chain by blast
      hence "(g i = a \<or> g i = c)"
        using \<open>g i \<noteq> b\<close> \<open>card X = 3\<close> points_in_chain
        by (smt  f_ch card2_either_elt1_or_elt2 card_Diff_singleton diff_Suc_1
            fin_long_chain_def insert_Diff insert_iff numeral_2_eq_2 numeral_3_eq_3)
      hence "\<not> [[a (g i) c]]"
        using abc_abc_neq by blast
      hence "g i \<notin> X"
        using \<open>f i=b \<and> g i=y\<close> \<open>g i=a \<or> g i=c\<close>  f_ch g_ch chain_bounds_unique fin_long_chain_def
        by blast
      thus False
        by (simp add: \<open>g i \<in> X\<close>)
    qed
    thus ?thesis
      by (simp add: \<open>card X = 3\<close> \<open>i = 1\<close>)
  next
    assume "i = 0 \<or> i = 2"
    show ?thesis
      using Nil.prems(5) \<open>card X = 3\<close> \<open>i = 0 \<or> i = 2\<close> chain_bounds_unique f_ch g_ch
      by (metis diff_Suc_1 fin_long_chain_def numeral_2_eq_2 numeral_3_eq_3)
  qed
next
  case IH: (Suc n)
  have lch_fX: "long_ch_by_ord f X"
    using ch_by_ord_def fin_chain_def fin_long_chain_def long_ch_card_ge3 IH(3,5)
    by fastforce
  have lch_gX: "long_ch_by_ord g X"
    using IH(3,6) ch_by_ord_def fin_chain_def fin_long_chain_def long_ch_card_ge3
    by fastforce
  have fin_X: "finite X"
    using IH(4) le_0_eq by fastforce

  have "ch_by_ord f X"
    using lch_fX unfolding ch_by_ord_def by blast
  have "card X \<ge> 4"
    using IH.hyps(2) by linarith

  obtain b where f_ch: "[f[a..b..c]X]"
    using \<open>ch_by_ord f X\<close> IH(3,5) fin_chain_def short_ch_card_2
    by auto
  obtain y where g_ch: "[g[x..y..z]X]"
    using \<open>ch_by_ord f X\<close> IH.prems(1,4) fin_chain_def short_ch_card_2
    by auto

  obtain p where p_def: "p = f (card X - 2)" by simp
  have "[[a p c]]"
  proof -
    have "card X - 2 < card X - 1"
      using \<open>4 \<le> card X\<close> by auto
    moreover have "card X - 2 > 0"
      using \<open>3 \<le> card X\<close> by linarith
    ultimately show ?thesis
      using f_ch p_def unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
      by (metis card_Diff1_less card_Diff_singleton)
  qed
  hence "p\<noteq>c \<and> p\<noteq>a"
    using abc_abc_neq by blast

  obtain Y where Y_def: "X = insert c Y" "c\<notin>Y"
    using f_ch points_in_chain
    by (meson mk_disjoint_insert)
  hence fin_Y: "finite Y"
    using f_ch fin_long_chain_def by auto
  hence "n = card Y - 3"
    using \<open>Suc n = card X - 3\<close> \<open>X = insert c Y\<close> \<open>c\<notin>Y\<close> card_insert_if
    by auto
  hence card_Y: "card Y = n + 3"
    using Y_def(1) Y_def(2) fin_Y IH.hyps(2) by fastforce 
  have "card Y = card X - 1"
    using Y_def(1,2) fin_X by auto
  have "p\<in>Y"
    using \<open>X = insert c Y\<close> \<open>[[a p c]]\<close> abc_abc_neq lch_fX p_def IH.prems(1,3) Y_def(2)
    by (metis chain_remove_at_right_edge fin_chain_def points_in_chain)
  have "[f[a..p]Y]"
    using chain_remove_at_right_edge [where f=f and a=a and c=c and X=X and p=p and Y=Y]
    using fin_long_ch_imp_fin_ch  [where f=f and a=a and c=c and b=b and X=X]
    using f_ch p_def \<open>card X \<ge> 3\<close> Y_def
    by blast
  hence ch_fY: "long_ch_by_ord f Y"
    unfolding fin_chain_def
    using card_Y ch_by_ord_def fin_Y fin_long_chain_def long_ch_card_ge3
    by force

  have p_closest: "\<not> (\<exists>q\<in>X. [[p q c]])"
  proof
    assume "(\<exists>q\<in>X. [[p q c]])"
    then obtain q where "q\<in>X" "[[p q c]]" by blast
    then obtain j where "j < card X" "f j = q"
      using lch_fX lch_gX fin_X points_in_chain \<open>p\<noteq>c \<and> p\<noteq>a\<close>
      by (metis ordering_def long_ch_by_ord_def)
    have "j > card X - 2 \<and> j < card X - 1"
    proof -
      have "j > card X - 2 \<and> j < card X - 1 \<or> j < card X - 2 \<and> j > card X - 1"
        using index_order3 [where b=j and a="card X - 2" and c="card X - 1"]
        using \<open>[[p q c]]\<close> \<open>f j = q\<close> \<open>j < card X\<close> f_ch p_def
        by (metis (no_types, lifting) One_nat_def card_gt_0_iff diff_less empty_iff
            fin_long_chain_def lessI zero_less_numeral)
      thus ?thesis by linarith
    qed
    thus False by linarith
  qed

  have "g (card X - 2) = p"
  proof (rule ccontr)
    assume asm_false: "g (card X - 2) \<noteq> p"
    obtain j where "g j = p" "j < card X - 1" "j>0"
      using \<open>X = insert c Y\<close> \<open>p\<in>Y\<close>  points_in_chain \<open>p\<noteq>c \<and> p\<noteq>a\<close>
      by (metis (no_types, hide_lams) chain_bounds_unique f_ch
          fin_long_chain_def g_ch index_middle_element insert_iff)
    hence "j < card X - 2"
      using asm_false le_eq_less_or_eq by fastforce
    hence "j < card Y - 1"
      by (simp add: Y_def(1,2) fin_Y)
    obtain d where "d = g (card X - 2)" by simp
    have "[[p d z]]"
    proof -
      have "card X - 1 > card X - 2"
        using \<open>j < card X - 1\<close> by linarith
      thus ?thesis
        using lch_gX \<open>j < card Y - 1\<close> \<open>card Y = card X - 1\<close> \<open>d = g (card X - 2)\<close> \<open>g j = p\<close>
        unfolding long_ch_by_ord_def ordering_def
        by (metis (mono_tags, lifting) One_nat_def card_Diff1_less card_Diff_singleton
            diff_diff_left fin_long_chain_def g_ch numeral_2_eq_2 plus_1_eq_Suc)
    qed
    moreover have "d\<in>X"
      using lch_gX \<open>d = g (card X - 2)\<close> unfolding long_ch_by_ord_def ordering_def
      by auto
    ultimately show False
      using p_closest abc_sym IH.prems(5) chain_bounds_unique f_ch g_ch
      by blast
  qed

  hence ch_gY: "long_ch_by_ord g Y"
    using IH.prems(1,4,5) g_ch f_ch ch_fY card_Y ch_by_ord_def chain_remove_at_right_edge fin_Y
    by (metis Y_def chain_bounds_unique fin_chain_def fin_long_chain_def long_ch_card_ge3)
  
  have "f i \<in> Y \<or> f i = c"
    by (metis ordering_def \<open>X = insert c Y\<close> \<open>i < card X\<close> lch_fX insert_iff long_ch_by_ord_def)
  thus "f i = g i"
  proof (rule disjE)
    assume "f i \<in> Y"
    hence "f i \<noteq> c"
      using \<open>c \<notin> Y\<close> by blast
    hence "i < card Y"
      using \<open>X = insert c Y\<close> \<open>c\<notin>Y\<close> IH(3,4) f_ch fin_Y fin_long_chain_def not_less_less_Suc_eq
      by fastforce
    hence "3 \<le> card Y"
      using card_Y le_add2 by presburger
    show "f i = g i"
      using IH(1) [of Y]
      using \<open>n = card Y - 3\<close> \<open>3 \<le> card Y\<close> \<open>i < card Y\<close>
      using Y_def card_Y chain_remove_at_right_edge le_add2
      by (metis IH.prems(1,3,4,5) chain_bounds_unique2)
  next
    assume "f i = c"
    show ?thesis
      using IH.prems(2,5) \<open>f i = c\<close> chain_bounds_unique f_ch g_ch indices_neq_imp_events_neq
      by (metis \<open>card Y = card X - 1\<close> Y_def card_insert_disjoint fin_Y fin_long_chain_def lessI)
  qed
qed

text \<open>I'm really impressed \<open>sledgehammer\<close>/\<open>smt\<close> can solve this if I just tell them "Use symmetry!".\<close>

lemma (in MinkowskiSpacetime) chain_unique_induction_cx:
  assumes "card X \<ge> 3"
      and "i < card X"
      and "[f[a..c]X]"
      and "[g[x..z]X]"
      and "c = x \<or> a = z"
    shows "f i = g (card X - i - 1)"
  using chain_sym chain_unique_induction_ax
  by (smt (verit, best) assms diff_right_commute fin_chain_def fin_long_ch_imp_fin_ch)



text \<open>
  This lemma has to exclude two-element chains again, because no order exists within them.
  Alternatively, the result is trivial: any function that assigns one element to index 0 and
  the other to 1 can be replaced with the (unique) other assignment, without destroying any
  (trivial, since ternary) "ordering" of the chain.
  This could be made generic over the ordering similar to \<open>chain_sym\<close> relying on \<open>ordering_sym\<close>.
\<close>

lemma (in MinkowskiSpacetime) chain_unique_upto_rev_cases:
  assumes ch_f: "[f[a..c]X]"
      and ch_g: "[g[x..z]X]"
      and card_X: "card X \<ge> 3"
      and valid_index: "i < card X"
  shows "((a=x \<or> c=z) \<longrightarrow> (f i = g i))" "((a=z \<or> c=x) \<longrightarrow> (f i = g (card X - i - 1)))"
proof -
  obtain n where n_def: "n = card X - 3"
    by blast
  hence valid_index_2: "i < n + 3"
    by (simp add: card_X valid_index)

  show "((a=x \<or> c=z) \<longrightarrow> (f i = g i))"
    using card_X ch_f ch_g chain_unique_induction_ax valid_index by blast
  show "((a=z \<or> c=x) \<longrightarrow> (f i = g (card X - i - 1)))"
    using assms(3) ch_f ch_g chain_unique_induction_cx valid_index by blast
qed

lemma (in MinkowskiSpacetime) chain_unique_upto_rev:
  assumes "[f[a..c]X]" "[g[x..z]X]" "card X \<ge> 3" "i < card X"
  shows "f i = g i \<or> f i = g (card X - i - 1)" "a=x\<and>c=z \<or> c=x\<and>a=z"
proof -
  have "(a=x \<or> c=z) \<or> (a=z \<or> c=x)"
    using chain_bounds_unique
    by (metis assms(1,2) fin_chain_def points_in_chain short_ch_def)
  thus "f i = g i \<or> f i = g (card X - i - 1)"
    using assms(3) \<open>i < card X\<close> assms chain_unique_upto_rev_cases by blast
  thus "(a=x\<and>c=z) \<or> (c=x\<and>a=z)"
    by (meson assms(1-3) chain_bounds_unique2)
qed



section "Subchains"
context MinkowskiSpacetime begin


lemma f_img_is_subset:
  assumes "[f[(f 0) ..]X]" "i\<ge>0" "j>i" "Y=f`{i..j}"
  shows "Y\<subseteq>X"
proof
  fix x assume "x\<in>Y"
  then obtain n where "n\<in>{i..j}" "f n = x"
    using assms(4) by blast
  hence "f n \<in> X"
    by (metis ordering_def assms(1) inf_chain_is_long long_ch_by_ord_def)
  thus "x\<in>X"
    using \<open>f n = x\<close> by blast
qed


lemma f_inj_on_index_subset:
  assumes "[f[(f 0) ..]X]" "i\<ge>0" "j>i" "Y=f`{i..j}"
  shows "inj_on f {i..j}"
  unfolding inj_on_def
proof (safe)
  fix x y assume "x\<in>{i..j}" "y\<in>{i..j}" "f x = f y"
  show "x=y"
  proof (rule ccontr)
    assume "x\<noteq>y"
    let ?P = "\<lambda>r s. f r \<noteq> f s"
    {
      assume "x\<le>y"
      hence "x<y"
        using \<open>x \<noteq> y\<close> le_imp_less_or_eq by blast
      obtain n where "n>y" by blast
      hence "[[(f x)(f y)(f n)]]"
        using assms(1) \<open>x<y\<close> inf_chain_is_long long_ch_by_ord_def ordering_ord_ijk by fastforce
      hence "?P x y"
        using abc_abc_neq by blast
    } moreover { (* TODO: use a wlog theorem for sets instead? *)
      assume "x>y"
      obtain n where "n>x" by blast
      hence "[[(f y)(f x)(f n)]]"
        using assms(1) \<open>x>y\<close> inf_chain_is_long long_ch_by_ord_def ordering_ord_ijk by fastforce
      hence "?P y x"
        using abc_abc_neq by blast
    }
    ultimately show False
      using not_le_imp_less \<open>f x = f y\<close> by auto
  qed
qed


lemma f_bij_on_index_subset:
  assumes "[f[(f 0) ..]X]" "i\<ge>0" "j>i" "Y=f`{i..j}"
  shows "bij_betw f {i..j} Y"
  using f_inj_on_index_subset
  by (metis assms inj_on_imp_bij_betw)


lemma only_one_index:
  assumes "[f[(f 0) ..]X]" "i\<ge>0" "j>i" "Y=f`{i..j}" "f n \<in> Y"
  shows "n\<in>{i..j}"
proof -
  obtain m where "m\<in>{i..j}" "f m = f n"
    using assms(4) assms(5) by auto
  have "inj_on f {i..j}"
    using assms(1,3) f_inj_on_index_subset by blast
  have "m = n"
  proof (rule ccontr)
    assume "m\<noteq>n"
    obtain l where "f l \<in> X" "l\<noteq>m" "l\<noteq>n"
      using assms(1) inf_chain_is_long
      by (metis ordering_def le_eq_less_or_eq lessI long_ch_by_ord_def not_less_eq_eq)
    hence "[[(f l)(f m)(f n)]] \<or> [[(f m)(f l)(f n)]] \<or> [[(f l)(f n)(f m)]]"
      using \<open>f m = f n\<close> \<open>m\<noteq>n\<close> 
      using abc_abc_neq assms(1) inf_chain_is_long inf_ordering_inj' long_ch_by_ord_def
      by blast
    thus False
      using \<open>f m = f n\<close> abc_abc_neq by auto
  qed
  thus ?thesis
    using \<open>m \<in> {i..j}\<close> by blast
qed


lemma f_one_to_one_on_index_subset:
  assumes "[f[(f 0) ..]X]" "i\<ge>0" "j>i" "Y=f`{i..j}" "y\<in>Y"
  shows "\<exists>!k\<in>{i..j}. f k = y" "f k = y \<longrightarrow> k\<in>{i..j}"
  using f_inj_on_index_subset only_one_index assms image_iff inj_on_eq_iff apply metis
  using assms(1,3,4,5) only_one_index by blast


lemma card_of_subchain:
  assumes "[f[(f 0) ..]X]" "i\<ge>0" "j>i" "Y=f`{i..j}"
  shows "card Y = card {i..j}" "card Y = j-i+1"
proof -
  show "card Y = card {i..j}"
    by (metis assms bij_betw_same_card f_bij_on_index_subset)
  thus "card Y = j-i+1"
    using card_Collect_nat
    by (simp add: assms(3))
qed


lemma fin_long_subchain_of_semifin:
  assumes "[f[(f 0) ..]X]" "i\<ge>0" "j>i+1" "Y=f`{i..j}"
    "g = (\<lambda>n. f(n+i))"
  shows "[g[(f i)..(f j)]Y]" (* "j=i+1 \<longrightarrow> short_ch Y" "j>i+1 \<longrightarrow> fin_long_ch_by_ord g Y" *)
proof -
  obtain k where "k=i+1" by simp
  hence ind_ord: "i<k \<and> k<j" using assms(3) by simp
  have "[g[(f i) .. (f k) .. (f j)]Y]"
  proof -
    have "f i \<noteq> f k \<and> f i \<noteq> f j \<and> f k \<noteq> f j"
    proof -
      have "[[(f i) (f k) (f j)]]"
        using assms(1) ind_ord long_ch_by_ord_def ordering_ord_ijk semifin_chain_def
        by fastforce
      thus ?thesis
        using abc_abc_neq by blast
    qed
    moreover have "finite Y"
    proof -
      have "inj f"
        using inf_ordering_inj [where ord="betw"] abc_abc_neq
        using assms(1) long_ch_by_ord_def semifin_chain_def by auto
      hence "card Y \<le> card {i..j}"
        using assms(4) inf_ordering_inj
        using card_image_le by blast
      have "finite {i..j}"
        by simp
      thus "finite Y"
        by (simp add: assms(4)) 
    qed
    moreover have "long_ch_by_ord g Y"
    proof -
      obtain x y z where "x=f i" "y=f k" "z=f j"
        by auto
      have "x\<in>Y \<and> y\<in>Y \<and> z\<in>Y \<and> x \<noteq> y \<and> y \<noteq> z \<and> x \<noteq> z"
        using \<open>x = f i\<close> \<open>y = f k\<close> \<open>z = f j\<close> assms(4) calculation(1) ind_ord by auto
      moreover have "ordering g betw Y"
        unfolding ordering_def
      proof (intro conjI)
        show "\<forall>n. (finite Y \<longrightarrow> n < card Y) \<longrightarrow> g n \<in> Y"
          apply (safe) apply (auto simp add: \<open>finite Y\<close>)
        proof -
          fix n assume "n<card Y"
          then obtain n' where "n+i = n'" "n'\<in>{i..j}"
          proof -
            assume asm: "\<And>n'. \<lbrakk>n + i = n'; n' \<in> {i..j}\<rbrakk> \<Longrightarrow> thesis"
            have "n < card {i..j}"
              by (metis \<open>n < card Y\<close> assms(4) card_image_le finite_atLeastAtMost less_le_trans)
            thus ?thesis
              using asm by simp
          qed
          show "g n \<in> Y"
            using \<open>n + i = n'\<close> \<open>n' \<in> {i..j}\<close> assms(4,5) by blast
        qed
        show "\<forall>x\<in>Y. \<exists>n. (finite Y \<longrightarrow> n < card Y) \<and> g n = x"
        proof (rule ballI)
          fix x assume "x\<in>Y"
          hence "x\<in>X"
            using f_img_is_subset assms(1,4)
            by (metis ordering_def imageE inf_chain_is_long long_ch_by_ord_def)
          then obtain n where "f n = x"
            using \<open>x \<in> Y\<close> assms(4) by blast
          have "n\<in>{i..j}" using only_one_index
            by (metis \<open>f n = x\<close> \<open>x \<in> Y\<close> assms(1,2,4) ind_ord less_trans)
          show "\<exists>n. (finite Y \<longrightarrow> n < card Y) \<and> g n = x"
          proof (rule exI, rule conjI)
            have "n-i\<ge>0"
              by blast
            have "g (n-i) = f (n-i+i)"
              using assms(5) by blast
            show "g (n-i) = x"
            proof (cases)
              assume "n-i>0"
              thus ?thesis
                by (simp add: \<open>f n = x\<close> \<open>g (n - i) = f (n - i + i)\<close>)
            next assume "\<not>n-i>0"
              hence "n-i=0" by blast
              thus ?thesis
                using \<open>n\<in>{i..j}\<close> \<open>f n = x\<close> \<open>g (n - i) = f (n - i + i)\<close> by auto
            qed
            show "finite Y \<longrightarrow> (n-i) < card Y"
            proof
              assume "finite Y"
              show "n-i<card Y"
                using card_of_subchain
                using \<open>n \<in> {i..j}\<close> assms(1,4) ind_ord by auto
            qed
          qed
        qed
        show "\<forall>n n' n''. (finite Y \<longrightarrow> n'' < card Y) \<and> n<n' \<and> n'<n'' \<longrightarrow> [[(g n)(g n')(g n'')]]"
          apply (safe) using \<open>finite Y\<close> apply blast
        proof -
          fix l m n
          assume "l<m" "m<n" "n<card Y"
          hence "l+i<m+i" "m+i<n+i"
            apply simp by (simp add: \<open>m < n\<close>)
          hence "[[(f(l+i))(f(m+i))(f(n+i))]]"
            using assms(1) inf_chain_is_long long_ch_by_ord_def ordering_ord_ijk by fastforce
          thus "[[(g l)(g m)(g n)]]"
            using assms(5) by blast
        qed
      qed
      ultimately show ?thesis
        using long_ch_by_ord_def by auto
    qed
    moreover have "g 0 = f i \<and> f k \<in> Y \<and> g (card Y - 1) = f j"
      using card_of_subchain assms(1,4,5) ind_ord less_imp_le_nat 
      by force
    ultimately show ?thesis
      using fin_long_chain_def by blast
  qed
  thus ?thesis
    using fin_long_ch_imp_fin_ch by blast
qed

end (*Context MinkowskiSpacetime*)



section "Extensions of results to infinite chains"
context MinkowskiSpacetime begin

lemma i_neq_j_imp_events_neq_inf:
  assumes "[f[(f 0)..]X]" "i\<noteq>j"
  shows "f i \<noteq> f j"
proof -
  let ?P = "\<lambda> i j. i\<noteq>j \<longrightarrow> f i \<noteq> f j"
  {
    fix i j assume "(i::nat)\<le>j"
    have "?P i j"
    proof (cases)
      assume "i<j"
      then obtain k where "k>j" by blast
      hence "[[(f i)(f j)(f k)]]"
        using \<open>i < j\<close> assms(1) inf_chain_is_long long_ch_by_ord_def ordering_ord_ijk by fastforce
      thus "?P i j"
        using abc_abc_neq by blast
    next
      assume "\<not>i<j" hence "i=j" using \<open>i \<le> j\<close> by auto
      show "?P i j" by (simp add: \<open>i = j\<close>)
    qed
  } moreover {
    fix i j assume "?P j i"
    hence "?P i j" by auto
  }
  ultimately show ?thesis
    by (metis assms(2) leI less_imp_le_nat)
qed


lemma i_neq_j_imp_events_neq:
  assumes "long_ch_by_ord f X" "i\<noteq>j" "finite X \<longrightarrow> (i<card X \<and> j<card X)"
  shows "f i \<noteq> f j"
  using i_neq_j_imp_events_neq_inf indices_neq_imp_events_neq
  by (meson assms get_fin_long_ch_bounds semifin_chain_def)


lemma inf_chain_origin_unique:
  assumes "[f[f 0..]X]" "[g[g 0..]X]"
  shows "f 0 = g 0"
proof (rule ccontr)
  assume "f 0 \<noteq> g 0"
  obtain P where "P\<in>\<P>" "X\<subseteq>P"
    using assms(1) semifin_chain_on_path by blast
  obtain x where "x = g 1" by simp
  hence "x\<noteq>g 0"
    using assms(2) i_neq_j_imp_events_neq_inf zero_neq_one by blast
  have "x\<in>X"
    by (metis ordering_def \<open>x = g 1\<close> assms(2) inf_chain_is_long long_ch_by_ord_def)
  have "x=f 0 \<or> x\<noteq>f 0" by auto
  thus False
  proof (rule disjE)
    assume "x=f 0"
    hence "[[(g 0)(f 0)(g 2)]]"
      using \<open>x=g 1\<close> \<open>x=f 0\<close> assms(2) inf_chain_is_long long_ch_by_ord_def ordering_ord_ijk
      by fastforce
    then obtain m n where "f m = g 0" "f n = g 2"
      by (metis ordering_def assms(1) assms(2) inf_chain_is_long long_ch_by_ord_def)
    hence "[[(f m)(f 0)(f n)]]"
      by (simp add: \<open>[[(g 0)(f 0)(g 2)]]\<close>)
    hence "m\<noteq>n"
      using abc_abc_neq by blast
    have "m>0 \<and> n>0"
      using \<open>[[(f m)(f 0)(f n)]]\<close> abc_abc_neq neq0_conv by blast
    hence "(0<m \<and> m<n) \<or> (0<n \<and> n<m)"
      using \<open>m \<noteq> n\<close> by auto
    thus False
      using `[[(f m)(f 0)(f n)]]` assms(1) index_order3 inf_chain_is_long by blast
  next
    assume "x\<noteq>f 0"

    (*Help for Sledgehammer*)
    have fn: "\<forall>n. f n \<in> X"
      by (metis (no_types) ordering_def assms(1) inf_chain_is_long long_ch_by_ord_def)
    have gn: "\<forall>n. g n \<in> X"
      by (metis ordering_def assms(2) inf_chain_is_long long_ch_by_ord_def)

    have "[[(g 0)x(f 0)]]"
    proof -
      have "[[(f 0)(g 0)x]] \<or> [[(g 0)(f 0)x]] \<or> [[(g 0)x(f 0)]]"
        using \<open>f 0 \<noteq> g 0\<close> \<open>x \<noteq> f 0\<close> \<open>x \<noteq> g 0\<close> all_aligned_on_semifin_chain
        by (metis ordering_def \<open>x \<in> X\<close> assms inf_chain_is_long long_ch_by_ord_def)
      moreover have "\<not>[[(f 0)(g 0)x]]"
        using abc_only_cba(1,3) all_aligned_on_semifin_chain assms(2) fn
        by (metis \<open>x\<in>X\<close> \<open>x\<noteq>f 0\<close> \<open>x\<noteq>g 0\<close>)
      moreover have "\<not>[[(g 0)(f 0)x]]"
        using fn gn \<open>x \<in> X\<close> \<open>x \<noteq> g 0\<close>
        by (metis (no_types) abc_only_cba(1,2,4) all_aligned_on_semifin_chain assms(1))
      ultimately show ?thesis by blast
    qed

    obtain m m' where "g m' = f 0" "m = Suc m'"
      using ordering_def assms inf_chain_is_long long_ch_by_ord_def by metis
    hence "[[(g 0)(f 0)(g m)]]"
      by (metis Suc_le_eq \<open>f 0 \<noteq> g 0\<close> assms(2) inf_chain_is_long lessI linorder_neqE_nat
          long_ch_by_ord_def not_le ordering_ord_ijk zero_less_Suc)
    then obtain n p where "f n = g 0" "f p = g m"
      by (metis abc_abc_neq abc_only_cba(1,4) all_aligned_on_semifin_chain assms(1) gn)
    hence "m<0 \<or> n<0"
      using all_aligned_on_semifin_chain assms(1) \<open>[[(g 0)(f 0)(g m)]]\<close>
      by (metis abc_abc_neq abc_only_cba(1,4) fn)
    thus False by simp
  qed
qed


lemma inf_chain_unique:
  assumes "[f[f 0..]X]" "[g[g 0..]X]"
  shows "\<forall>i::nat. f i = g i"
proof -
  {
    assume asm: "[f[f 0..]X]" "[g[f 0..]X]"
    have "\<forall>i::nat. f i = g i"
    proof
      fix i::nat
      show "f i = g i"
      proof (induct i)
        show "f 0 = g 0"
          using asm(2) inf_chain_is_long by fastforce
        fix i assume "f i = g i"
        show "f (Suc i) = g (Suc i)"
        proof (rule ccontr)
          assume "f (Suc i) \<noteq> g (Suc i)"
          let ?i = "Suc i"
          have "f 0\<in>X \<and> g?i\<in>X \<and> f?i\<in>X"
            by (metis ordering_def assms(1) assms(2) inf_chain_is_long long_ch_by_ord_def)
          hence "[[(f 0)(f ?i)(g ?i)]] \<or> [[(f 0)(g ?i)(f ?i)]] \<or> [[(f ?i)(f 0)(g ?i)]]"
            using all_aligned_on_semifin_chain assms(1,2) i_neq_j_imp_events_neq_inf
            by (metis \<open>f?i \<noteq>g?i\<close> \<open>f 0 = g 0\<close>)
          hence "[[(f 0)(f ?i)(g ?i)]] \<or> [[(f 0)(g ?i)(f ?i)]]"
            using all_aligned_on_semifin_chain asm(2)
            by (metis \<open>f 0 \<in> X \<and> g (Suc i) \<in> X \<and> f (Suc i) \<in> X\<close> abc_abc_neq)
          have "([[(f 0)(f i)(f ?i)]] \<and> [[(f 0)(g i)(g ?i)]]) \<or> i=0"
            using long_ch_by_ord_def ordering_ord_ijk asm(1,2)
            by (metis Suc_inject Suc_lessI Suc_less_eq inf_chain_is_long lessI zero_less_Suc)
          thus False
          proof (rule disjE)
            assume "i=0"
            have "[[(g 0)(f 1)(g 1)]]"
            proof -
              obtain x where "x = g 1" by simp
              hence "x\<in>X"
                using \<open>f 0 \<in> X \<and> g (Suc i) \<in> X \<and> f (Suc i) \<in> X\<close> \<open>i = 0\<close> by force
              then obtain m where "f m = x"
                by (metis ordering_def assms(1) inf_chain_is_long long_ch_by_ord_def)
              hence "f m = g 1"
                using \<open>x = g 1\<close> by blast
              have "m>1"
                using assms(2) i_neq_j_imp_events_neq_inf \<open>f?i \<noteq> g?i\<close>
                by (metis One_nat_def Suc_lessI \<open>f 0 = g 0\<close> \<open>f m = x\<close> \<open>i = 0\<close> \<open>x = g 1\<close> neq0_conv)
              thus "[[(g 0)(f 1)(g 1)]]"
                using \<open>[[(f 0)(f?i)(g?i)]] \<or> [[(f 0)(g?i)(f?i)]]\<close> \<open>f 0 = g 0\<close> \<open>f m = x\<close> \<open>i=0\<close> \<open>x = g 1\<close>
                by (metis One_nat_def assms(1) gr_implies_not_zero index_order3 inf_chain_is_long order.asym)
            qed
            have "f 1 \<in> X"
              using \<open>f 0 \<in> X \<and> g (Suc i) \<in> X \<and> f (Suc i) \<in> X\<close> \<open>i = 0\<close> by auto
            then obtain m' where "g m' = f 1"
              by (metis ordering_def assms(2) inf_chain_is_long long_ch_by_ord_def)
            hence "[[(g 0)(g m')(g 1)]]"
              using \<open>[[(g 0)(f 1)(g 1)]]\<close> by auto
            have "[[(g 0)(g 1)(g m')]]"
            proof -
              have "m' \<noteq> 1 \<and> m' \<noteq> 0"
                using `[[(g 0)(g m')(g 1)]]` by (meson abc_abc_neq)
              hence "m'>1" by auto
              thus "[[(g 0)(g 1)(g m')]]"
                using \<open>[[(g 0)(g m')(g 1)]]\<close> assms(2) index_order3 inf_chain_is_long by blast
            qed
            thus False
              using `[[(g 0)(g m')(g 1)]]` abc_only_cba(2) by blast
          next
            assume "[[(f 0)(f i)(f ?i)]] \<and> [[(f 0)(g i)(g ?i)]]"
            have "[[(g 0)(f ?i)(g ?i)]]"
            proof -
              obtain x where "x = g ?i" by simp
              hence "x\<in>X"
                by (simp add: \<open>f 0 \<in> X \<and> g (Suc i) \<in> X \<and> f (Suc i) \<in> X\<close>)
              then obtain m where "f m = x"
                by (metis ordering_def assms(1) inf_chain_is_long long_ch_by_ord_def)
              hence "f m = g ?i"
                using \<open>x = g ?i\<close> by blast
              have "m>?i"
                using assms(2) i_neq_j_imp_events_neq_inf \<open>f?i \<noteq> g?i\<close>
                by (metis Suc_lessI \<open>[[(f 0)(f i)(f ?i)]] \<and> [[(f 0)(g i)(g ?i)]]\<close> \<open>f i = g i\<close> \<open>f m = x\<close>
                    \<open>x = g (Suc i)\<close> assms(1) index_order3 less_nat_zero_code semifin_chain_def)
              thus "[[(g 0)(f ?i)(g ?i)]]"
                using \<open>[[(f 0)(f?i)(g?i)]] \<or> [[(f 0)(g?i)(f?i)]]\<close> \<open>f 0 = g 0\<close> \<open>f m = x\<close> \<open>x = g ?i\<close>
                by (metis assms(1) gr_implies_not_zero index_order3 inf_chain_is_long order.asym)
            qed
            obtain m where "g m = f ?i"
              using \<open>(f 0)\<in>X \<and> g?i\<in>X \<and> f?i\<in>X\<close> assms(2)
              by (metis ordering_def inf_chain_is_long long_ch_by_ord_def)
            hence "[[(g i)(g m)(g ?i)]]"
              using abc_acd_bcd \<open>[[(f 0)(f i)(f?i)]] \<and> [[(f 0)(g i)(g ?i)]]\<close> \<open>[[(g 0)(f ?i)(g ?i)]]\<close>
              by (metis \<open>f 0 = g 0\<close> \<open>f i = g i\<close>)
            have "[[(g i)(g ?i)(g m)]]"
            proof -
              have "m>?i"
                using \<open>[[(g i)(g m)(g ?i)]]\<close> assms(2) index_order3 inf_chain_is_long by fastforce
              thus ?thesis
                using assms(2) inf_chain_is_long long_ch_by_ord_def ordering_ord_ijk by fastforce
            qed
            thus False
              using \<open>[[(g i)(g m)(g ?i)]]\<close> abc_only_cba by blast
          qed
        qed
      qed
    qed
  }
  moreover have "f 0 = g 0" using inf_chain_origin_unique assms by blast
  ultimately show ?thesis using assms by auto
qed

end (*context MinkowskiSpacetime*)



section "Interlude: betw4 and WLOG"

subsection "betw4 - strict and non-strict, basic lemmas"
context MinkowskiBetweenness begin

text \<open>Define additional notation for non-strict ordering - cf Schutz' monograph \cite[ p.~27]{schutz1997}.\<close>

abbreviation nonstrict_betw_right :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("[[_ _ _\<rbrakk>") where
  "nonstrict_betw_right a b c \<equiv> [[a b c]] \<or> b = c"

abbreviation nonstrict_betw_left :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrakk>_ _ _]]") where
  "nonstrict_betw_left a b c \<equiv> [[a b c]] \<or> b = a"

abbreviation nonstrict_betw_both :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* ("[(_ _ _)]") *) where
  "nonstrict_betw_both a b c \<equiv> nonstrict_betw_left a b c \<or> nonstrict_betw_right a b c"

abbreviation betw4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("[[_ _ _ _]]") where
  "betw4 a b c d \<equiv> [[a b c]] \<and> [[b c d]]"

abbreviation nonstrict_betw_right4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("[[_ _ _ _\<rbrakk>") where
  "nonstrict_betw_right4 a b c d \<equiv> betw4 a b c d \<or> c = d"

abbreviation nonstrict_betw_left4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("\<lbrakk>_ _ _ _]]") where
  "nonstrict_betw_left4 a b c d \<equiv> betw4 a b c d \<or> a = b"

abbreviation nonstrict_betw_both4 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* ("[(_ _ _ _)]") *) where
  "nonstrict_betw_both4 a b c d \<equiv> nonstrict_betw_left4 a b c d \<or> nonstrict_betw_right4 a b c d"

lemma betw4_strong:
  assumes "betw4 a b c d"
  shows "[[a b d]] \<and> [[a c d]]"
  using abc_bcd_acd assms by blast

lemma betw4_imp_neq:
  assumes "betw4 a b c d"
  shows "a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d"
  using abc_only_cba assms by blast


end (* context MinkowskiBetweenness *)
context MinkowskiSpacetime begin


lemma betw4_weak:
  fixes a b c d :: 'a
  assumes "[[a b c]] \<and> [[a c d]]
          \<or> [[a b c]] \<and> [[b c d]]
          \<or> [[a b d]] \<and> [[b c d]]
          \<or> [[a b d]] \<and> [[b c d]]"
  shows "betw4 a b c d"
  using abc_acd_bcd abd_bcd_abc assms by blast

lemma betw4_sym:
  fixes a::'a and b::'a and c::'a and d::'a
  shows "betw4 a b c d \<longleftrightarrow> betw4 d c b a"
  using abc_sym by blast

lemma abcd_dcba_only:
  fixes a::'a and b::'a and c::'a and d::'a
  assumes "betw4 a b c d"
  shows "\<not>betw4 a b d c" "\<not>betw4 a c b d" "\<not>betw4 a c d b" "\<not>betw4 a d b c" "\<not>betw4 a d c b"
        "\<not>betw4 b a c d" "\<not>betw4 b a d c" "\<not>betw4 b c a d" "\<not>betw4 b c d a" "\<not>betw4 b d c a" "\<not>betw4 b d a c"
        "\<not>betw4 c a b d" "\<not>betw4 c a d b" "\<not>betw4 c b a d" "\<not>betw4 c b d a" "\<not>betw4 c d a b" "\<not>betw4 c d b a"
        "\<not>betw4 d a b c" "\<not>betw4 d a c b" "\<not>betw4 d b a c" "\<not>betw4 d b c a" "\<not>betw4 d c a b"
  using abc_only_cba assms by blast+ 

lemma some_betw4a:
  fixes a::'a and b::'a and c::'a and d::'a and P
  assumes "P\<in>\<P>" "a\<in>P" "b\<in>P" "c\<in>P" "d\<in>P" "a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d"
      and "\<not>(betw4 a b c d \<or> betw4 a b d c \<or> betw4 a c b d \<or> betw4 a c d b \<or> betw4 a d b c \<or> betw4 a d c b)"
    shows "betw4 b a c d \<or> betw4 b a d c \<or> betw4 b c a d \<or> betw4 b d a c \<or> betw4 c a b d \<or> betw4 c b a d"
  by (smt abc_bcd_acd abc_sym abd_bcd_abc assms some_betw_xor)

lemma some_betw4b:
  fixes a::'a and b::'a and c::'a and d::'a and P
  assumes "P\<in>\<P>" "a\<in>P" "b\<in>P" "c\<in>P" "d\<in>P" "a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d"
      and "\<not>(betw4 b a c d \<or> betw4 b a d c \<or> betw4 b c a d \<or> betw4 b d a c \<or> betw4 c a b d \<or> betw4 c b a d)"
    shows "betw4 a b c d \<or> betw4 a b d c \<or> betw4 a c b d \<or> betw4 a c d b \<or> betw4 a d b c \<or> betw4 a d c b"
  by (smt abc_bcd_acd abc_sym abd_bcd_abc assms some_betw_xor)


lemma abd_acd_abcdacbd:
  fixes a::'a and b::'a and c::'a and d::'a
  assumes abd: "[[a b d]]" and acd: "[[a c d]]" and "b\<noteq>c"
  shows "betw4 a b c d \<or> betw4 a c b d"
proof -
  obtain P where "P\<in>\<P>" "a\<in>P" "b\<in>P" "d\<in>P"
    using abc_ex_path abd by blast
  have "c\<in>P"
    using \<open>P \<in> \<P>\<close> \<open>a \<in> P\<close> \<open>d \<in> P\<close> abc_abc_neq acd betw_b_in_path by blast
  have "\<not>[[b d c]]"
    using abc_sym abcd_dcba_only(5) abd acd by blast
  hence "[[b c d]] \<or> [[c b d]]"
    using abc_abc_neq abc_sym abd acd assms(3) some_betw
    by (metis \<open>P \<in> \<P>\<close> \<open>b \<in> P\<close> \<open>c \<in> P\<close> \<open>d \<in> P\<close>)
  thus ?thesis
    using abd acd betw4_weak by blast
qed

end (*context MinkowskiSpacetime*)

subsection "WLOG for two general symmetric relations of two elements on a single path"
context MinkowskiBetweenness begin

text \<open>
  This first one is really just trying to get a hang of how to write these things.
  If you have a relation that does not care which way round the ``endpoints'' (if $Q$ is the
  interval-relation) go, then anything you want to prove about both undistinguished endpoints,
  follows from a proof involving a single endpoint.
\<close>

lemma wlog_sym_element:
  assumes symmetric_rel: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and one_endpoint: "\<And>a b x I. \<lbrakk>Q I a b; x=a\<rbrakk> \<Longrightarrow> P x I"
    shows other_endpoint: "\<And>a b x I. \<lbrakk>Q I a b; x=b\<rbrakk> \<Longrightarrow> P x I"
  using assms by fastforce

text \<open>
  This one gives the most pertinent case split: a proof involving e.g. an element of an interval
  must consider the edge case and the inside case.
\<close>
lemma wlog_element:
  assumes symmetric_rel: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and one_endpoint: "\<And>a b x I. \<lbrakk>Q I a b; x=a\<rbrakk> \<Longrightarrow> P x I"
      and neither_endpoint: "\<And>a b x I. \<lbrakk>Q I a b; x\<in>I; (x\<noteq>a \<and> x\<noteq>b)\<rbrakk> \<Longrightarrow> P x I"
    shows any_element: "\<And>x I. \<lbrakk>x\<in>I; (\<exists>a b. Q I a b)\<rbrakk> \<Longrightarrow> P x I"
  by (metis assms)

text \<open>
  Summary of the two above. Use for early case splitting in proofs.
  Doesn't need $P$ to be symmetric - the context in the conclusion is explicitly symmetric.
\<close>

lemma wlog_two_sets_element:
  assumes symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and case_split: "\<And>a b c d x I J. \<lbrakk>Q I a b; Q J c d\<rbrakk> \<Longrightarrow>
              (x=a \<or> x=c \<longrightarrow> P x I J) \<and> (\<not>(x=a \<or> x=b \<or> x=c \<or> x=d) \<longrightarrow> P x I J)"
    shows "\<And>x I J. \<lbrakk>\<exists>a b. Q I a b; \<exists>a b. Q J a b\<rbrakk> \<Longrightarrow> P x I J"
  by (smt case_split symmetric_Q)

text \<open>
  Now we start on the actual result of interest. First we assume the events are all distinct,
  and we deal with the degenerate possibilities after.
\<close>

lemma wlog_endpoints_distinct1:
  assumes symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; betw4 a b c d\<rbrakk> \<Longrightarrow> P I J"
    shows "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d;
              betw4 b a c d \<or> betw4 a b d c \<or> betw4 b a d c \<or> betw4 d c b a\<rbrakk> \<Longrightarrow> P I J"
  by (meson abc_sym assms(2) symmetric_Q)

lemma wlog_endpoints_distinct2:
  assumes symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; betw4 a c b d\<rbrakk> \<Longrightarrow> P I J"
    shows "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d;
              betw4 b c a d \<or> betw4 a d b c \<or> betw4 b d a c \<or> betw4 d b c a\<rbrakk> \<Longrightarrow> P I J"
  by (meson abc_sym assms(2) symmetric_Q)

lemma wlog_endpoints_distinct3:
  assumes symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and symmetric_P: "\<And>I J. \<lbrakk>\<exists>a b. Q I a b; \<exists>a b. Q J a b; P I J\<rbrakk> \<Longrightarrow> P J I"
      and "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; betw4 a c d b\<rbrakk> \<Longrightarrow> P I J"
    shows "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d;
              betw4 a d c b \<or> betw4 b c d a \<or> betw4 b d c a \<or> betw4 c a b d\<rbrakk> \<Longrightarrow> P I J"
  by (meson assms)

lemma (in MinkowskiSpacetime) wlog_endpoints_distinct4:
    fixes Q:: "('a set) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (* cf `I = interval a b` *)
      and P:: "('a set) \<Rightarrow> ('a set) \<Rightarrow> bool"
      and A:: "('a set)" (* the path that takes the role of the real line *)
  assumes path_A: "A\<in>\<P>"
      and symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and Q_implies_path: "\<And>a b I. \<lbrakk>I\<subseteq>A; Q I a b\<rbrakk> \<Longrightarrow> b\<in>A \<and> a\<in>A"
      and symmetric_P: "\<And>I J. \<lbrakk>\<exists>a b. Q I a b; \<exists>a b. Q J a b; P I J\<rbrakk> \<Longrightarrow> P J I"
      and "\<And>I J a b c d.
          \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A; betw4 a b c d \<or> betw4 a c b d \<or> betw4 a c d b\<rbrakk> \<Longrightarrow> P I J"
    shows "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A;
                a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d\<rbrakk> \<Longrightarrow> P I J"
proof -
  fix I J a b c d
  assume asm: "Q I a b" "Q J c d" "I \<subseteq> A" "J \<subseteq> A"
              "a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d"
  have endpoints_on_path: "a\<in>A" "b\<in>A" "c\<in>A" "d\<in>A"
    using Q_implies_path asm by blast+
  show "P I J"
  proof (cases) (* have to split like this, because the full some_betw4 is too large for Isabelle *)
    assume "betw4 b a c d \<or> betw4 b a d c \<or> betw4 b c a d \<or>
            betw4 b d a c \<or> betw4 c a b d \<or> betw4 c b a d"
    then consider "betw4 b a c d"|"betw4 b a d c"|"betw4 b c a d"|
                  "betw4 b d a c"|"betw4 c a b d"|"betw4 c b a d"
      by linarith
    thus "P I J"
      apply (cases)
           apply (metis(mono_tags) asm(1-4) assms(5) symmetric_Q)+
       apply (metis asm(1-4) assms(4,5))
      by (metis asm(1-4) assms(2,4,5) symmetric_Q)
  next
    assume "\<not>(betw4 b a c d \<or> betw4 b a d c \<or> betw4 b c a d \<or>
              betw4 b d a c \<or> betw4 c a b d \<or> betw4 c b a d)"
    hence "betw4 a b c d \<or> betw4 a b d c \<or> betw4 a c b d \<or>
           betw4 a c d b \<or> betw4 a d b c \<or> betw4 a d c b"
      using some_betw4b [where P=A and a=a and b=b and c=c and d=d]
      using endpoints_on_path asm path_A by simp
    then consider "betw4 a b c d"|"betw4 a b d c"|"betw4 a c b d"|
                  "betw4 a c d b"|"betw4 a d b c"|"betw4 a d c b"
      by linarith
    thus "P I J"
      apply (cases)
      by (metis asm(1-4) assms(5) symmetric_Q)+
  qed
qed


lemma (in MinkowskiSpacetime) wlog_endpoints_distinct':
  assumes "A \<in> \<P>"
      and "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and "\<And>a b I. \<lbrakk>I \<subseteq> A; Q I a b\<rbrakk> \<Longrightarrow> a \<in> A"
      and "\<And>I J. \<lbrakk>\<exists>a b. Q I a b; \<exists>a b. Q J a b; P I J\<rbrakk> \<Longrightarrow> P J I"
      and "\<And>I J a b c d.
          \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A; betw4 a b c d \<or> betw4 a c b d \<or> betw4 a c d b\<rbrakk> \<Longrightarrow> P I J"
      and "Q I a b" (* Is it better style to have these assumptions first, or last like this? *)
      and "Q J c d"
      and "I \<subseteq> A"
      and "J \<subseteq> A"
      and "a \<noteq> b" "a \<noteq> c" "a \<noteq> d" "b \<noteq> c" "b \<noteq> d" "c \<noteq> d"
  shows "P I J"
proof -
  { 
    let ?R = "(\<lambda>I. (\<exists>a b. Q I a b))"
    have "\<And>I J. \<lbrakk>?R I; ?R J; P I J\<rbrakk> \<Longrightarrow> P J I"
      using assms(4) by blast
  }
  thus ?thesis
    using wlog_endpoints_distinct4
      [where P=P and Q=Q and A=A and I=I and J=J and a=a and b=b and c=c and d=d]
    by (smt assms(1-3,5-))
qed

lemma (in MinkowskiSpacetime) wlog_endpoints_distinct:
  assumes path_A: "A\<in>\<P>"
      and symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and Q_implies_path: "\<And>a b I. \<lbrakk>I\<subseteq>A; Q I a b\<rbrakk> \<Longrightarrow> b\<in>A \<and> a\<in>A"
      and symmetric_P: "\<And>I J. \<lbrakk>\<exists>a b. Q I a b; \<exists>a b. Q J a b; P I J\<rbrakk> \<Longrightarrow> P J I"
      and "\<And>I J a b c d.
          \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A; betw4 a b c d \<or> betw4 a c b d \<or> betw4 a c d b\<rbrakk> \<Longrightarrow> P I J"
  shows "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A;
              a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d\<rbrakk> \<Longrightarrow> P I J"
  by (smt (verit, ccfv_SIG) assms some_betw4b)


lemma wlog_endpoints_degenerate1:
  assumes symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and symmetric_P: "\<And>I J. \<lbrakk>\<exists>a b. Q I a b; \<exists>a b. Q I a b; P I J\<rbrakk> \<Longrightarrow> P J I"
          (* two singleton intervals *)
      and two: "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d;
                  (a=b \<and> b=c \<and> c=d) \<or> (a=b \<and> b\<noteq>c \<and> c=d)\<rbrakk> \<Longrightarrow> P I J"
          (* one singleton interval *)
      and one: "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d;
                  (a=b \<and> b=c \<and> c\<noteq>d) \<or> (a=b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d)\<rbrakk> \<Longrightarrow> P I J"
          (* no singleton interval - the all-distinct case is a separate theorem *)
      and no: "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d;
                  (a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a=d) \<or> (a\<noteq>b \<and> b=c \<and> c\<noteq>d \<and> a=d)\<rbrakk> \<Longrightarrow> P I J"
    shows "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; \<not>(a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d \<and> a\<noteq>c \<and> b\<noteq>d)\<rbrakk> \<Longrightarrow> P I J"
  by (metis assms)

lemma wlog_endpoints_degenerate2:
  assumes symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and Q_implies_path: "\<And>a b I A. \<lbrakk>I\<subseteq>A; A\<in>\<P>; Q I a b\<rbrakk> \<Longrightarrow> b\<in>A \<and> a\<in>A"
      and symmetric_P: "\<And>I J. \<lbrakk>\<exists>a b. Q I a b; \<exists>a b. Q J a b; P I J\<rbrakk> \<Longrightarrow> P J I"
      and "\<And>I J a b c d A. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A; A\<in>\<P>;
              [[a b c]] \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
      and "\<And>I J a b c d A. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A; A\<in>\<P>;
              [[b a c]] \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
    shows "\<And>I J a b c d A. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A; A\<in>\<P>;
              a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
proof -
  have last_case: "\<And>I J a b c d A. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A; A\<in>\<P>;
              [[b c a]] \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
    using assms(1,3-5) by (metis abc_sym)
  thus "\<And>I J a b c d A. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A; A\<in>\<P>;
              a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
    by (smt (z3) abc_sym assms(2,4,5) some_betw)
qed


lemma wlog_endpoints_degenerate:
  assumes path_A: "A\<in>\<P>"
      and symmetric_Q: "\<And>a b I. Q I a b \<Longrightarrow> Q I b a"
      and Q_implies_path: "\<And>a b I. \<lbrakk>I\<subseteq>A; Q I a b\<rbrakk> \<Longrightarrow> b\<in>A \<and> a\<in>A"
      and symmetric_P: "\<And>I J. \<lbrakk>\<exists>a b. Q I a b; \<exists>a b. Q J a b; P I J\<rbrakk> \<Longrightarrow> P J I"
      and "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A\<rbrakk>
            \<Longrightarrow> ((a=b \<and> b=c \<and> c=d) \<longrightarrow> P I J) \<and> ((a=b \<and> b\<noteq>c \<and> c=d) \<longrightarrow> P I J)
              \<and> ((a=b \<and> b=c \<and> c\<noteq>d) \<longrightarrow> P I J) \<and> ((a=b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d) \<longrightarrow> P I J)
              \<and> ((a\<noteq>b \<and> b=c \<and> c\<noteq>d \<and> a=d) \<longrightarrow> P I J)
              \<and> (([[a b c]] \<and> a=d) \<longrightarrow> P I J) \<and> (([[b a c]] \<and> a=d) \<longrightarrow> P I J)"
    shows "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A;
            \<not>(a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d \<and> a\<noteq>c \<and> b\<noteq>d)\<rbrakk> \<Longrightarrow> P I J"
proof -

  text \<open>We first extract some of the assumptions of this lemma into the form
  of other WLOG lemmas' assumptions.\<close>
  have ord1: "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A;
              [[a b c]] \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
    using assms(5) by auto
  have ord2: "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A;
              [[b a c]] \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
    using assms(5) by auto
  have last_case: "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A;
              a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
    using ord1 ord2 wlog_endpoints_degenerate2 symmetric_P symmetric_Q Q_implies_path path_A
    by (metis abc_sym some_betw)
  show "\<And>I J a b c d. \<lbrakk>Q I a b; Q J c d; I\<subseteq>A; J\<subseteq>A;
            \<not>(a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d \<and> a\<noteq>c \<and> b\<noteq>d)\<rbrakk> \<Longrightarrow> P I J"
  proof -

    text \<open>Fix the sets on the path, and obtain the assumptions of \<open>wlog_endpoints_degenerate1\<close>.\<close>
    fix I J
    assume asm1: "I\<subseteq>A" "J\<subseteq>A"
    have two: "\<And>a b c d. \<lbrakk>Q I a b; Q J c d; a=b \<and> b=c \<and> c=d\<rbrakk> \<Longrightarrow> P I J"
            "\<And>a b c d. \<lbrakk>Q I a b; Q J c d; a=b \<and> b\<noteq>c \<and> c=d\<rbrakk> \<Longrightarrow> P I J"
      using \<open>J \<subseteq> A\<close> \<open>I \<subseteq> A\<close> path_A assms(5) by blast+ 
    have one: "\<And> a b c d. \<lbrakk>Q I a b; Q J c d; a=b \<and> b=c \<and> c\<noteq>d\<rbrakk> \<Longrightarrow> P I J"
          "\<And> a b c d. \<lbrakk>Q I a b; Q J c d; a=b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d\<rbrakk> \<Longrightarrow> P I J"
      using \<open>I \<subseteq> A\<close> \<open>J \<subseteq> A\<close> path_A assms(5) by blast+ 
    have no: "\<And> a b c d. \<lbrakk>Q I a b; Q J c d; a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
          "\<And> a b c d. \<lbrakk>Q I a b; Q J c d; a\<noteq>b \<and> b=c \<and> c\<noteq>d \<and> a=d\<rbrakk> \<Longrightarrow> P I J"
      using \<open>I \<subseteq> A\<close> \<open>J \<subseteq> A\<close> path_A last_case apply blast
      using \<open>I \<subseteq> A\<close> \<open>J \<subseteq> A\<close> path_A assms(5) by auto

    text \<open>Now unwrap the remaining object logic and finish the proof.\<close>
    fix a b c d
    assume asm2: "Q I a b" "Q J c d" "\<not>(a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d \<and> a\<noteq>c \<and> b\<noteq>d)"
    show "P I J"
      using two [where a=a and b=b and c=c and d=d]
      using one [where a=a and b=b and c=c and d=d]
      using no [where a=a and b=b and c=c and d=d]
      using wlog_endpoints_degenerate1
        [where I=I and J=J and a=a and b=b and c=c and d=d and P=P and Q=Q]
      using asm1 asm2 symmetric_P last_case assms(5) symmetric_Q
      (* by metis *) (* metis is proposed by solver "e", but is slow :-( *)
      by smt
  qed
qed


end (*context MinkowskiSpacetime*)


subsection "WLOG for two intervals"
context MinkowskiBetweenness begin

text \<open>
  This section just specifies the results for a generic relation $Q$
  in the previous section to the interval relation.
\<close>

lemma wlog_two_interval_element:
  assumes "\<And>x I J. \<lbrakk>is_interval I; is_interval J; P x J I\<rbrakk> \<Longrightarrow> P x I J"
      and "\<And>a b c d x I J. \<lbrakk>I = interval a b; J = interval c d\<rbrakk> \<Longrightarrow>
              (x=a \<or> x=c \<longrightarrow> P x I J) \<and> (\<not>(x=a \<or> x=b \<or> x=c \<or> x=d) \<longrightarrow> P x I J)"
    shows "\<And>x I J. \<lbrakk>is_interval I; is_interval J\<rbrakk> \<Longrightarrow> P x I J"
  by (metis assms(2) int_sym)


lemma (in MinkowskiSpacetime) wlog_interval_endpoints_distinct:
  assumes "\<And>I J. \<lbrakk>is_interval I; is_interval J; P I J\<rbrakk> \<Longrightarrow> P J I" (*P does not distinguish between intervals*)
          "\<And>I J a b c d. \<lbrakk>I = interval a b; J = interval c d\<rbrakk>
          \<Longrightarrow> (betw4 a b c d \<longrightarrow> P I J) \<and> (betw4 a c b d \<longrightarrow> P I J) \<and> (betw4 a c d b \<longrightarrow> P I J)"
  shows "\<And>I J Q a b c d. \<lbrakk>I = interval a b; J = interval c d; I\<subseteq>Q; J\<subseteq>Q; Q\<in>\<P>;
              a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d\<rbrakk> \<Longrightarrow> P I J"
proof -
  let ?Q = "\<lambda> I a b. I = interval a b"

  fix I J A a b c d
  assume asm: "?Q I a b" "?Q J c d" "I\<subseteq>A" "J\<subseteq>A" "A\<in>\<P>" "a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d"
  show "P I J"
  proof (rule wlog_endpoints_distinct)
    show "\<And>a b I. ?Q I a b \<Longrightarrow> ?Q I b a"
      by (simp add: int_sym)
    show "\<And>a b I. I \<subseteq> A \<Longrightarrow> ?Q I a b \<Longrightarrow> b \<in> A \<and> a \<in> A"
      by (simp add: ends_in_int subset_iff)
    show "\<And>I J. is_interval I \<Longrightarrow> is_interval J \<Longrightarrow> P I J \<Longrightarrow> P J I"
      using assms(1) by blast
    show "\<And>I J a b c d. \<lbrakk>?Q I a b; ?Q J c d; betw4 a b c d \<or> betw4 a c b d \<or> betw4 a c d b\<rbrakk>
        \<Longrightarrow> P I J"
      by (meson assms(2))
    show "I = interval a b" "J = interval c d" "I\<subseteq>A" "J\<subseteq>A" "A\<in>\<P>"
        "a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d"
      using asm by simp+
  qed
qed


lemma wlog_interval_endpoints_degenerate:
  assumes symmetry: "\<And>I J. \<lbrakk>is_interval I; is_interval J; P I J\<rbrakk> \<Longrightarrow> P J I"
      and "\<And>I J a b c d Q. \<lbrakk>I = interval a b; J = interval c d; I\<subseteq>Q; J\<subseteq>Q; Q\<in>\<P>\<rbrakk>
            \<Longrightarrow> ((a=b \<and> b=c \<and> c=d) \<longrightarrow> P I J) \<and> ((a=b \<and> b\<noteq>c \<and> c=d) \<longrightarrow> P I J)
              \<and> ((a=b \<and> b=c \<and> c\<noteq>d) \<longrightarrow> P I J) \<and> ((a=b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d) \<longrightarrow> P I J)
              \<and> ((a\<noteq>b \<and> b=c \<and> c\<noteq>d \<and> a=d) \<longrightarrow> P I J)
              \<and> (([[a b c]] \<and> a=d) \<longrightarrow> P I J) \<and> (([[b a c]] \<and> a=d) \<longrightarrow> P I J)"
    shows "\<And>I J a b c d Q. \<lbrakk>I = interval a b; J = interval c d; I\<subseteq>Q; J\<subseteq>Q; Q\<in>\<P>;
            \<not>(a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d \<and> a\<noteq>c \<and> b\<noteq>d)\<rbrakk> \<Longrightarrow> P I J"
proof -
  let ?Q = "\<lambda> I a b. I = interval a b"

  fix I J a b c d A
  assume asm: "?Q I a b" "?Q J c d" "I\<subseteq>A" "J\<subseteq>A" "A\<in>\<P>" "\<not>(a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d \<and> a\<noteq>c \<and> b\<noteq>d)"
  show "P I J"
  proof (rule wlog_endpoints_degenerate)
    show "\<And>a b I. ?Q I a b \<Longrightarrow> ?Q I b a"
      by (simp add: int_sym)
    show "\<And>a b I. I \<subseteq> A \<Longrightarrow> ?Q I a b \<Longrightarrow> b \<in> A \<and> a \<in> A"
      by (simp add: ends_in_int subset_iff)
    show "\<And>I J. is_interval I \<Longrightarrow> is_interval J \<Longrightarrow> P I J \<Longrightarrow> P J I"
      using symmetry by blast
    show "I = interval a b" "J = interval c d" "I\<subseteq>A" "J\<subseteq>A" "A\<in>\<P>"
      "\<not> (a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d \<and> a\<noteq>c \<and> b\<noteq>d)"
      using asm by auto+ 
    show "\<And>I J a b c d. \<lbrakk>?Q I a b; ?Q J c d; I \<subseteq> A; J \<subseteq> A\<rbrakk> \<Longrightarrow>
        (a = b \<and> b = c \<and> c = d \<longrightarrow> P I J) \<and>
        (a = b \<and> b \<noteq> c \<and> c = d \<longrightarrow> P I J) \<and>
        (a = b \<and> b = c \<and> c \<noteq> d \<longrightarrow> P I J) \<and>
        (a = b \<and> b \<noteq> c \<and> c \<noteq> d \<and> a \<noteq> d \<longrightarrow> P I J) \<and>
        (a \<noteq> b \<and> b = c \<and> c \<noteq> d \<and> a = d \<longrightarrow> P I J) \<and>
        ([[a b c]] \<and> a = d \<longrightarrow> P I J) \<and> ([[b a c]] \<and> a = d \<longrightarrow> P I J)"
      using assms(2) \<open>A\<in>\<P>\<close> by auto
  qed
qed

end (* context MinkowskiBetweenness *)


section "Interlude: Intervals, Segments, Connectedness"
context MinkowskiSpacetime begin

text \<open>
  In this secion, we apply the WLOG lemmas from the previous section in order to reduce the
  number of cases we need to consider when thinking about two arbitrary intervals on a path.
  This is used to prove that the (countable) intersection of intervals is an interval.
  These results cannot be found in Schutz, but he does use them (without justification)
  in his proof of Theorem 12 (even for uncountable intersections).
\<close>

lemma int_of_ints_is_interval_neq: (* Proof using WLOG *)
  assumes  "I1 = interval a b" "I2 = interval c d" "I1\<subseteq>P" "I2\<subseteq>P" "P\<in>\<P>" "I1\<inter>I2 \<noteq> {}"
      and events_neq: "a\<noteq>b" "a\<noteq>c" "a\<noteq>d" "b\<noteq>c" "b\<noteq>d" "c\<noteq>d"
    shows "is_interval (I1 \<inter> I2)"
proof -
  have on_path: "a\<in>P \<and> b\<in>P \<and> c\<in>P \<and> d\<in>P"
    using assms(1-4) interval_def by auto

  let ?prop = "\<lambda> I J. is_interval (I\<inter>J) \<or> (I\<inter>J) = {}" (* The empty intersection is excluded in assms. *)

  have symmetry: "(\<And>I J. is_interval I \<Longrightarrow> is_interval J \<Longrightarrow> ?prop I J \<Longrightarrow> ?prop J I)"
    by (simp add: Int_commute)

  {
    fix I J a b c d
    assume "I = interval a b" "J = interval c d" (* "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d" *)
    have "(betw4 a b c d \<longrightarrow> ?prop I J)"
         "(betw4 a c b d \<longrightarrow> ?prop I J)"
         "(betw4 a c d b \<longrightarrow> ?prop I J)"
    proof (rule_tac [!] impI)
      assume "betw4 a b c d"
      have "I\<inter>J = {}"
      proof (rule ccontr)
        assume "I\<inter>J\<noteq>{}"
        then obtain x where "x\<in>I\<inter>J"
          by blast
        show False
        proof (cases)
          assume "x\<noteq>a \<and> x\<noteq>b \<and> x\<noteq>c \<and> x\<noteq>d"
          hence "[[a x b]]" "[[c x d]]"
            using \<open>I=interval a b\<close> \<open>x\<in>I\<inter>J\<close> \<open>J=interval c d\<close> \<open>x\<in>I\<inter>J\<close>
            by (simp add: interval_def seg_betw)+
          thus False
            by (meson \<open>betw4 a b c d\<close> abc_only_cba(3) abc_sym abd_bcd_abc)
        next
          assume "\<not>(x\<noteq>a \<and> x\<noteq>b \<and> x\<noteq>c \<and> x\<noteq>d)"
          thus False
            using interval_def seg_betw \<open>I = interval a b\<close> \<open>J = interval c d\<close> abcd_dcba_only(21)
                 \<open>x \<in> I \<inter> J\<close> \<open>betw4 a b c d\<close> abc_bcd_abd abc_bcd_acd abc_only_cba(1,2)
            by (metis (full_types) insert_iff Int_iff)
        qed
      qed 
      thus "?prop I J" by simp
    next
      assume "betw4 a c b d"
      then have "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d"
        using betw4_imp_neq by blast
      have "I\<inter>J = interval c b"
      proof (safe)
        fix x
        assume "x \<in> interval c b"
        {
          assume "x=b \<or> x=c"
          hence "x\<in>I"
            using \<open>betw4 a c b d\<close> \<open>I = interval a b\<close> interval_def seg_betw by auto
          have "x\<in>J"
            using \<open>x=b \<or> x=c\<close>
            using \<open>betw4 a c b d\<close> \<open>J = interval c d\<close> interval_def seg_betw by auto 
          hence "x\<in>I \<and> x\<in>J" using \<open>x \<in> I\<close> by blast
        } moreover {
          assume  "\<not>(x=b \<or> x=c)"
          hence "[[c x b]]"
            using `x\<in>interval c b` unfolding interval_def segment_def by simp
          hence "[[a x b]]"
            by (meson \<open>betw4 a c b d\<close> abc_acd_abd abc_sym)
          have "[[c x d]]"
            using \<open>betw4 a c b d\<close> \<open>[[c x b]]\<close> abc_acd_abd by blast
          have "x\<in>I" "x\<in>J"
            using \<open>I = interval a b\<close> `[[a x b]]` \<open>J = interval c d\<close> \<open>[[c x d]]\<close> 
                  interval_def seg_betw by auto
        }
        ultimately show "x\<in>I" "x\<in>J" by blast+
      next
        fix x
        assume "x\<in>I" "x\<in>J"
        show "x \<in> interval c b"
        proof (cases)
          assume not_eq: "x\<noteq>a \<and> x\<noteq>b \<and> x\<noteq>c \<and> x\<noteq>d"
          have "[[a x b]]" "[[c x d]]"
            using `x\<in>I` \<open>I = interval a b\<close>  `x\<in>J` \<open>J = interval c d\<close> 
                  not_eq unfolding interval_def segment_def by blast+
          hence "[[c x b]]"
            by (meson \<open>betw4 a c b d\<close> abc_bcd_acd betw4_weak)
          thus ?thesis
            unfolding interval_def segment_def using seg_betw segment_def by auto
        next
          assume not_not_eq: "\<not>(x\<noteq>a \<and> x\<noteq>b \<and> x\<noteq>c \<and> x\<noteq>d)"
          {
            assume "x=a"
            have "\<not>[[d a c]]"
              using \<open>betw4 a c b d\<close> abcd_dcba_only(9) by blast
            hence "a \<notin> interval c d" unfolding interval_def segment_def
              using abc_sym \<open>a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d\<close> by blast
            hence "False" using `x\<in>J` \<open>J = interval c d\<close> `x=a` by blast
          } moreover {
            assume "x=d"
            have "\<not>[[a d b]]" using \<open>betw4 a c b d\<close> abc_sym abcd_dcba_only(9) by blast
            hence "d\<notin>interval a b" unfolding interval_def segment_def
              using \<open>a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d\<close> by blast
            hence "False" using `x\<in>I` `x=d` \<open>I = interval a b\<close> by blast
          }
          ultimately show ?thesis
            using interval_def not_not_eq by auto
        qed
      qed
      thus "?prop I J" by auto
    next
      assume "betw4 a c d b"
      have "I\<inter>J = interval c d"
      proof (safe)
        fix x
        assume "x \<in> interval c d"
        {
          assume "x\<noteq>c \<and> x\<noteq>d"
          have "x \<in> J"
            by (simp add: \<open>J = interval c d\<close> \<open>x \<in> interval c d\<close>)
          have "[[c x d]]"
            using \<open>x \<in> interval c d\<close> \<open>x \<noteq> c \<and> x \<noteq> d\<close> interval_def seg_betw by auto
          have "[[a x b]]"
            by (meson \<open>betw4 a c d b\<close> \<open>[[c x d]]\<close> abc_bcd_abd abc_sym abe_ade_bcd_ace)
          have "x \<in> I"
            using \<open>I = interval a b\<close> \<open>[[a x b]]\<close> interval_def seg_betw by auto
          hence "x\<in>I \<and> x\<in>J" by (simp add: \<open>x \<in> J\<close>)
        } moreover {
          assume "\<not> (x\<noteq>c \<and> x\<noteq>d)"
          hence "x\<in>I \<and> x\<in>J"
            by (metis \<open>I = interval a b\<close> \<open>J = interval c d\<close> \<open>betw4 a c d b\<close> \<open>x \<in> interval c d\<close>
                abc_bcd_abd abc_bcd_acd insertI2 interval_def seg_betw)
        }
        ultimately show "x\<in>I" "x\<in>J" by blast+
      next
        fix x
        assume "x\<in>I" "x\<in>J"
        show "x \<in> interval c d"
          using \<open>J = interval c d\<close> \<open>x \<in> J\<close> by auto
      qed
      thus "?prop I J" by auto
    qed
  }
    
  then show "is_interval (I1\<inter>I2)"
    using wlog_interval_endpoints_distinct
      [where P="?prop" and I=I1 and J=I2 and Q=P and a=a and b=b and c=c and d=d]
    using symmetry assms by simp
qed


lemma int_of_ints_is_interval_deg: (* Proof using WLOG *)
  assumes  "I = interval a b" "J = interval c d" "I\<inter>J \<noteq> {}" "I\<subseteq>P" "J\<subseteq>P" "P\<in>\<P>"
      and events_deg: "\<not>(a\<noteq>b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d \<and> a\<noteq>c \<and> b\<noteq>d)"
    shows "is_interval (I \<inter> J)"
proof -

  let ?p = "\<lambda> I J. (is_interval (I \<inter> J) \<or> I\<inter>J = {})"

  have symmetry: "\<And>I J. \<lbrakk>is_interval I; is_interval J; ?p I J\<rbrakk> \<Longrightarrow> ?p J I"
    by (simp add: inf_commute)

  have degen_cases: "\<And>I J a b c d Q. \<lbrakk>I = interval a b; J = interval c d; I\<subseteq>Q; J\<subseteq>Q; Q\<in>\<P>\<rbrakk>
            \<Longrightarrow> ((a=b \<and> b=c \<and> c=d) \<longrightarrow> ?p I J) \<and> ((a=b \<and> b\<noteq>c \<and> c=d) \<longrightarrow> ?p I J)
              \<and> ((a=b \<and> b=c \<and> c\<noteq>d) \<longrightarrow> ?p I J) \<and> ((a=b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d) \<longrightarrow> ?p I J)
              \<and> ((a\<noteq>b \<and> b=c \<and> c\<noteq>d \<and> a=d) \<longrightarrow> ?p I J)
              \<and> (([[a b c]] \<and> a=d) \<longrightarrow> ?p I J) \<and> (([[b a c]] \<and> a=d) \<longrightarrow> ?p I J)"
  proof -
    fix I J a b c d Q
    assume "I = interval a b" "J = interval c d" "I\<subseteq>Q" "J\<subseteq>Q" "Q\<in>\<P>"
    show "((a=b \<and> b=c \<and> c=d) \<longrightarrow> ?p I J) \<and> ((a=b \<and> b\<noteq>c \<and> c=d) \<longrightarrow> ?p I J)
              \<and> ((a=b \<and> b=c \<and> c\<noteq>d) \<longrightarrow> ?p I J) \<and> ((a=b \<and> b\<noteq>c \<and> c\<noteq>d \<and> a\<noteq>d) \<longrightarrow> ?p I J)
              \<and> ((a\<noteq>b \<and> b=c \<and> c\<noteq>d \<and> a=d) \<longrightarrow> ?p I J)
              \<and> (([[a b c]] \<and> a=d) \<longrightarrow> ?p I J) \<and> (([[b a c]] \<and> a=d) \<longrightarrow> ?p I J)"
    proof (intro conjI impI)
      assume "a = b \<and> b = c \<and> c = d" thus "?p I J"
        using \<open>I = interval a b\<close> \<open>J = interval c d\<close> by auto
    next
      assume "a = b \<and> b \<noteq> c \<and> c = d" thus "?p I J"
        using \<open>J = interval c d\<close> empty_segment interval_def by auto
    next
      assume "a = b \<and> b = c \<and> c \<noteq> d" thus "?p I J"
        using \<open>I = interval a b\<close> empty_segment interval_def by auto
    next
      assume "a = b \<and> b \<noteq> c \<and> c \<noteq> d \<and> a \<noteq> d" thus "?p I J"
        using \<open>I = interval a b\<close> empty_segment interval_def by auto
    next
      assume "a \<noteq> b \<and> b = c \<and> c \<noteq> d \<and> a = d" thus "?p I J"
        using \<open>I = interval a b\<close> \<open>J = interval c d\<close> int_sym by auto
    next
      assume "[[a b c]] \<and> a = d" show "?p I J"
      proof (cases)
        assume "I\<inter>J = {}" thus ?thesis by simp
      next
        assume "I\<inter>J \<noteq> {}"
        have "I\<inter>J = interval a b"
        proof (safe)
          fix x assume "x\<in>I" "x\<in>J"
          thus "x\<in>interval a b"
            using \<open>I = interval a b\<close> by blast
        next
          fix x assume "x\<in>interval a b"
          show "x\<in>I"
            by (simp add: \<open>I = interval a b\<close> \<open>x \<in> interval a b\<close>)
          have "[[d b c]]"
            using \<open>[[a b c]] \<and> a = d\<close> by blast
          have "[[a x b]] \<or> x=a \<or> x=b"
            using \<open>I = interval a b\<close> \<open>x \<in> I\<close> interval_def seg_betw by auto
          consider "[[d x c]]"|"x=a \<or> x=b"
            using \<open>[[a b c]] \<and> a = d\<close> \<open>[[a x b]] \<or> x = a \<or> x = b\<close> abc_acd_abd by blast
          thus "x\<in>J" 
          proof (cases)
            case 1
            then show ?thesis 
              by (simp add: \<open>J = interval c d\<close> abc_abc_neq abc_sym interval_def seg_betw)
          next
            case 2
            then have "x \<in> interval c d"
              using  \<open>[[a b c]] \<and> a = d\<close> int_sym interval_def seg_betw 
              by force 
            then show ?thesis
              using \<open>J = interval c d\<close> by blast  
          qed
        qed
        thus "?p I J" by blast
      qed
    next
      assume "[[b a c]] \<and> a = d" show "?p I J"
      proof (cases)
        assume "I\<inter>J = {}" thus ?thesis by simp
      next
        assume "I\<inter>J \<noteq> {}"
        have "I\<inter>J = {a}"
        proof (safe)
          fix x assume "x\<in>I" "x\<in>J" "x\<notin>{}"
          have cxd: "[[c x d]] \<or> x=c \<or> x=d"
            using \<open>J = interval c d\<close> \<open>x \<in> J\<close> interval_def seg_betw by auto
          consider "[[a x b]]"|"x=a"|"x=b"
            using \<open>I = interval a b\<close> \<open>x \<in> I\<close> interval_def seg_betw by auto
          then show "x=a"
          proof (cases)
            assume "[[a x b]]"
            hence "betw4 b x d c"
              using \<open>[[b a c]] \<and> a = d\<close> abc_acd_bcd abc_sym by meson
            hence False
              using cxd abc_abc_neq by blast
            thus ?thesis by simp
          next
            assume "x=b"
            hence "[[b d c]]"
              using \<open>[[b a c]] \<and> a = d\<close> by blast
            hence False
              using cxd \<open>x = b\<close> abc_abc_neq by blast
            thus ?thesis
              by simp
          next
            assume "x=a" thus "x=a" by simp
          qed
        next
          show "a\<in>I"
            by (simp add: \<open>I = interval a b\<close> ends_in_int)
          show "a\<in>J"
            by (simp add: \<open>J = interval c d\<close> \<open>[[b a c]] \<and> a = d\<close> ends_in_int)
        qed
        thus "?p I J"
          by (simp add: empty_segment interval_def)
      qed
    qed
  qed

  have "?p I J"
    using wlog_interval_endpoints_degenerate
      [where P="?p" and I=I and J=J and a=a and b=b and c=c and d=d and Q=P]
    using degen_cases
    using symmetry assms
    by smt

  thus ?thesis
    using assms(3) by blast
qed


lemma int_of_ints_is_interval:
  assumes "is_interval I" "is_interval J" "I\<subseteq>P" "J\<subseteq>P" "P\<in>\<P>" "I\<inter>J \<noteq> {}"
  shows "is_interval (I \<inter> J)"
  using int_of_ints_is_interval_neq int_of_ints_is_interval_deg
  by (meson assms)


lemma int_of_ints_is_interval2:
  assumes "\<forall>x\<in>S. (is_interval x \<and> x\<subseteq>P)" "P\<in>\<P>" "\<Inter>S \<noteq> {}" "finite S" "S\<noteq>{}"
  shows "is_interval (\<Inter>S)"
proof -
  obtain n where "n = card S"
    by simp
  consider "n=0"|"n=1"|"n\<ge>2"
    by linarith
  thus ?thesis
  proof (cases)
    assume "n=0"
    then have False
      using \<open>n = card S\<close> assms(4,5) by simp
    thus ?thesis
      by simp
  next
    assume "n=1"
    then obtain I where "S = {I}"
      using \<open>n = card S\<close> card_1_singletonE by auto
    then have "\<Inter>S = I"
      by simp
    moreover have "is_interval I"
      by (simp add: \<open>S = {I}\<close> assms(1))
    ultimately show ?thesis
      by blast
  next
    assume "2\<le>n"
    obtain m where "m+2=n"
      using \<open>2 \<le> n\<close> le_add_diff_inverse2 by blast
    have ind: "\<And>S. \<lbrakk>\<forall>x\<in>S. (is_interval x \<and> x\<subseteq>P); P\<in>\<P>; \<Inter>S \<noteq> {}; finite S; S\<noteq>{}; m+2=card S\<rbrakk>
      \<Longrightarrow>  is_interval (\<Inter>S)"
    proof (induct m)
      case 0
      then have "card S = 2"
        by auto
      then obtain I J where "S={I,J}" "I\<noteq>J"
        by (meson card_2_iff)
      then have "I\<in>S" "J\<in>S"
        by blast+
      then have "is_interval I" "is_interval J" "I\<subseteq>P" "J\<subseteq>P"
           by (simp add: "0.prems"(1))+ 
      also have "I\<inter>J \<noteq> {}"
        using \<open>S={I,J}\<close> "0.prems"(3) by force
      then have "is_interval(I\<inter>J)"
        using assms(2) calculation int_of_ints_is_interval[where I=I and J=J and P=P]
        by fastforce
      then show ?case
        by (simp add: \<open>S = {I, J}\<close>)
    next
      case (Suc m)
      obtain S' I where "I\<in>S" "S = insert I S'" "I\<notin>S'"
        using Suc.prems(4,5) by (metis Set.set_insert finite.simps insertI1)
      then have "is_interval (\<Inter>S')"
      proof -
        have "m+2 = card S'"
          using Suc.prems(4,6) `S = insert I S'` `I\<notin>S'` by auto
        moreover have "\<forall>x\<in>S'. is_interval x \<and> x \<subseteq> P"
          by (simp add: Suc.prems(1) \<open>S = insert I S'\<close>)
        moreover have "\<Inter> S' \<noteq> {}"
          using Suc.prems(3) \<open>S = insert I S'\<close> by auto
        moreover have "finite S'"
          using Suc.prems(4) \<open>S = insert I S'\<close> by auto
        ultimately show ?thesis
          using assms(2) Suc(1) [where S=S'] by fastforce
      qed
      then have "is_interval ((\<Inter>S')\<inter>I)"
      proof (rule int_of_ints_is_interval)
        show "is_interval I"
          by (simp add: Suc.prems(1) \<open>I \<in> S\<close>)
        show "\<Inter>S' \<subseteq> P"
          using \<open>I \<notin> S'\<close> \<open>S = insert I S'\<close> Suc.prems(1,4,6) Inter_subset
          by (metis Suc_n_not_le_n card.empty card_insert_disjoint finite_insert
              le_add2 numeral_2_eq_2 subset_eq subset_insertI)
        show "I \<subseteq> P"
          by (simp add: Suc.prems(1) \<open>I \<in> S\<close>)
        show "P \<in> \<P>"
          using assms(2) by auto
        show "\<Inter>S' \<inter> I \<noteq> {}"
          using Suc.prems(3) \<open>S = insert I S'\<close> by auto
      qed
      thus ?case
        using \<open>S = insert I S'\<close> by (simp add: inf.commute)
    qed
    then show ?thesis
      using \<open>m + 2 = n\<close> \<open>n = card S\<close> assms by blast
  qed
qed


end (*context MinkowskiSpacetime*)



section "3.7 Continuity and the monotonic sequence property"
context MinkowskiSpacetime begin

text \<open>
  This section only includes a proof of the first part of Theorem 12, as well as some results
  that would be useful in proving part (ii).
\<close>

theorem (*12(i)*) two_rays:
  assumes path_Q: "Q\<in>\<P>"
      and event_a: "a\<in>Q"
    shows "\<exists>R L. (is_ray_on R Q \<and> is_ray_on L Q
                \<and> Q-{a} \<subseteq> (R \<union> L)               \<^cancel>\<open>events of Q excl. a belong to two rays\<close>
                \<and> (\<forall>r\<in>R. \<forall>l\<in>L. [[l a r]])       \<^cancel>\<open>a is betw any 'a of one ray and any 'a of the other\<close>
                \<and> (\<forall>x\<in>R. \<forall>y\<in>R. \<not> [[x a y]])     \<^cancel>\<open>but a is not betw any two events \<dots>\<close>
                \<and> (\<forall>x\<in>L. \<forall>y\<in>L. \<not> [[x a y]]))"   \<^cancel>\<open>\<dots> of the same ray\<close>
proof -
  text \<open>Schutz here uses Theorem 6, but we don't need it.\<close>
  obtain b where "b\<in>\<E>" and "b\<in>Q" and "b\<noteq>a"
    using event_a ge2_events in_path_event path_Q by blast
  let ?L = "{x. [[x a b]]}"
  let ?R = "{y. [[a y b]] \<or> [[a b y\<rbrakk>}"
  have "Q = ?L \<union> {a} \<union> ?R"
  proof -
    have inQ: "\<forall>x\<in>Q. [[x a b]] \<or> x=a \<or> [[a x b]] \<or> [[a b x\<rbrakk>"
      by (meson \<open>b \<in> Q\<close> \<open>b \<noteq> a\<close> abc_sym event_a path_Q some_betw)
    show ?thesis
    proof (safe)
      fix x
      assume "x \<in> Q" "x \<noteq> a" "\<not> [[x a b]]" "\<not> [[a x b]]" "b \<noteq> x" 
      then show "[[a b x]]"
        using inQ by blast
    next
      fix x  
      assume "[[x a b]]" 
      then show "x \<in> Q"
        by (simp add: \<open>b \<in> Q\<close> abc_abc_neq betw_a_in_path event_a path_Q)
    next
      show "a \<in> Q"
        by (simp add: event_a)
    next
      fix x
      assume "[[a x b]]"
      then show  "x \<in> Q"
        by (simp add: \<open>b \<in> Q\<close> abc_abc_neq betw_b_in_path event_a path_Q)
    next
      fix x
      assume "[[a b x]]"
      then show  "x \<in> Q"
        by (simp add: \<open>b \<in> Q\<close> abc_abc_neq betw_c_in_path event_a path_Q)
    next
      show "b \<in> Q" using \<open>b \<in> Q\<close> .
    qed
  qed
  have disjointLR: "?L \<inter> ?R = {}"
    using abc_abc_neq abc_only_cba by blast

  have wxyz_ord: "nonstrict_betw_right4 x a y b \<or> nonstrict_betw_right4 x a b y
      \<and> (([[w x a]] \<and> [[x a y]]) \<or> ([[x w a]] \<and> [[w a y]]))
      \<and> (([[x a y]] \<and> [[a y z]]) \<or> ([[x a z]] \<and> [[a z y]]))"
    if "x\<in>?L" "w\<in>?L" "y\<in>?R" "z\<in>?R" "w\<noteq>x" "y\<noteq>z" for x w y z
    using path_finsubset_chain order_finite_chain2 (* Schutz says: implied by thm 10 & 2 *)
    by (smt abc_abd_bcdbdc abc_bcd_abd abc_sym abd_bcd_abc mem_Collect_eq that) (* impressive! *)

  obtain x y where "x\<in>?L" "y\<in>?R"
    by (metis (mono_tags) \<open>b \<in> Q\<close> \<open>b \<noteq> a\<close> abc_sym event_a mem_Collect_eq path_Q prolong_betw2)
  obtain w where "w\<in>?L" "w\<noteq>x"
    by (metis \<open>b \<in> Q\<close> \<open>b \<noteq> a\<close> abc_sym event_a mem_Collect_eq path_Q prolong_betw3) 
  obtain z where "z\<in>?R" "y\<noteq>z"
    by (metis (mono_tags) \<open>b \<in> Q\<close> \<open>b \<noteq> a\<close> event_a mem_Collect_eq path_Q prolong_betw3)

  have "is_ray_on ?R Q \<and>
          is_ray_on ?L Q \<and>
          Q - {a} \<subseteq> ?R \<union> ?L \<and>
          (\<forall>r\<in>?R. \<forall>l\<in>?L. [[l a r]]) \<and>
          (\<forall>x\<in>?R. \<forall>y\<in>?R. \<not> [[x a y]]) \<and>
          (\<forall>x\<in>?L. \<forall>y\<in>?L. \<not> [[x a y]])"
  proof (intro conjI)
    show "is_ray_on ?L Q"
    proof (unfold is_ray_on_def, safe)
      show "Q \<in> \<P>" 
        by (simp add: path_Q)
    next
      fix x 
      assume "[[x a b]]" 
      then show "x \<in> Q"
        using \<open>b \<in> Q\<close> \<open>b \<noteq> a\<close> betw_a_in_path event_a path_Q by blast
    next
      show "is_ray {x. [[x a b]]}"
    proof -
      have "[[x a b]]"
        using \<open>x\<in>?L\<close> by simp
      have "?L = ray a x"
      proof
        show "ray a x \<subseteq> ?L"
        proof
          fix e assume "e\<in>ray a x"
          show "e\<in>?L"
            using wxyz_ord ray_cases abc_bcd_abd abd_bcd_abc abc_sym
            by (metis \<open>[[x a b]]\<close> \<open>e \<in> ray a x\<close> mem_Collect_eq)
        qed
        show "?L \<subseteq> ray a x"
        proof
          fix e assume "e\<in>?L"
          hence "[[e a b]]"
            by simp
          show "e\<in>ray a x"
          proof (cases)
            assume "e=x"
            thus ?thesis
              by (simp add: ray_def)
          next
            assume "e\<noteq>x"
            hence "[[e x a]] \<or> [[x e a]]" using wxyz_ord
              by (meson \<open>[[e a b]]\<close> \<open>[[x a b]]\<close> abc_abd_bcdbdc abc_sym)
            thus "e\<in>ray a x"
              by (metis Un_iff abc_sym insertCI pro_betw ray_def seg_betw)
          qed
        qed
      qed
      thus "is_ray ?L" by auto
    qed
  qed
(*
 1. Q \<in> \<P>
 2. \<And>x. [[a x b]] \<Longrightarrow> x \<in> Q
 3. \<And>x. [[a b x]] \<Longrightarrow> x \<in> Q
 4. \<And>x. b \<in> Q
 5. is_ray {y. [[a y b]] \<or> [[a b y\<rbrakk>}
*)
  show "is_ray_on ?R Q"
  proof (unfold is_ray_on_def, safe)
    show "Q \<in> \<P>" 
      by (simp add: path_Q)
  next 
    fix x 
    assume "[[a x b]]" 
    then show "x \<in> Q"
      by (simp add: \<open>b \<in> Q\<close> abc_abc_neq betw_b_in_path event_a path_Q)
  next
    fix x
    assume "[[a b x]]" 
    then show "x \<in> Q"
      by (simp add: \<open>b \<in> Q\<close> abc_abc_neq betw_c_in_path event_a path_Q)
  next
    show "b \<in> Q" using \<open>b \<in> Q\<close> .
  next
    show "is_ray {y. [[a y b]] \<or> [[a b y\<rbrakk>}"
    proof -
      have "[[a y b]] \<or> [[a b y]] \<or> y=b"
        using \<open>y\<in>?R\<close> by blast
      have "?R = ray a y"
      proof
        show "ray a y \<subseteq> ?R"
        proof
          fix e assume "e\<in>ray a y"
          hence "[[a e y]] \<or> [[a y e]] \<or> y=e"
            using ray_cases by auto
          show "e\<in>?R"
          proof -
            { assume "e \<noteq> b"
              have "(e \<noteq> y \<and> e \<noteq> b) \<and> [[w a y]] \<or> [[a e b]] \<or> [[a b e\<rbrakk>"
                using \<open>[[a y b]] \<or> [[a b y]] \<or> y = b\<close> \<open>w \<in> {x. [[x a b]]}\<close> abd_bcd_abc by blast
              hence "[[a e b]] \<or> [[a b e\<rbrakk>"
                using abc_abd_bcdbdc abc_bcd_abd abd_bcd_abc
                by (metis \<open>[[a e y]] \<or> [[a y e\<rbrakk>\<close> \<open>w \<in> ?L\<close> mem_Collect_eq)
            }
            thus ?thesis
              by blast
          qed
        qed
        show "?R \<subseteq> ray a y"
        proof
          fix e assume "e\<in>?R"
          hence aeb_cases: "[[a e b]] \<or> [[a b e]] \<or> e=b"
            by blast
          hence aey_cases: "[[a e y]] \<or> [[a y e]] \<or> e=y"
            using abc_abd_bcdbdc abc_bcd_abd abd_bcd_abc
            by (metis \<open>[[a y b]] \<or> [[a b y]] \<or> y = b\<close> \<open>x \<in> {x. [[x a b]]}\<close> mem_Collect_eq)
          show "e\<in>ray a y"
          proof -
            {
              assume "e=b"
              hence ?thesis
                using \<open>[[a y b]] \<or> [[a b y]] \<or> y = b\<close> \<open>b \<noteq> a\<close> pro_betw ray_def seg_betw by auto
            } moreover {
              assume "[[a e b]] \<or> [[a b e]]"
              assume "y\<noteq>e"
              hence "[[a e y]] \<or> [[a y e]]"
                using aey_cases by auto
              hence "e\<in>ray a y"
                unfolding ray_def using abc_abc_neq pro_betw seg_betw by auto
            } moreover {
              assume "[[a e b]] \<or> [[a b e]]"
              assume "y=e"
              have "e\<in>ray a y"
                unfolding ray_def by (simp add: \<open>y = e\<close>)
            }
            ultimately show ?thesis
              using aeb_cases by blast 
          qed
        qed
      qed
      thus "is_ray ?R" by auto
    qed
  qed
    show "(\<forall>r\<in>?R. \<forall>l\<in>?L. [[l a r]])"
      using abd_bcd_abc by blast
    show "\<forall>x\<in>?R. \<forall>y\<in>?R. \<not> [[x a y]]"
      by (smt abc_ac_neq abc_bcd_abd abd_bcd_abc mem_Collect_eq)
    show "\<forall>x\<in>?L. \<forall>y\<in>?L. \<not> [[x a y]]"
      using abc_abc_neq abc_abd_bcdbdc abc_only_cba by blast
    show "Q-{a} \<subseteq> ?R \<union> ?L"
      using \<open>Q = {x. [[x a b]]} \<union> {a} \<union> {y. [[a y b]] \<or> [[a b y\<rbrakk>}\<close> by blast
  qed
  thus ?thesis
    by (metis (mono_tags, lifting))
qed

text \<open>
  The definition \<open>closest_to\<close> in prose:
  Pick any $r \in R$. The closest event $c$ is such that there is no closer event in $L$,
  i.e. all other events of $L$ are further away from $r$.
  Thus in $L$, $c$ is the element closest to $R$.
\<close>
definition closest_to :: "('a set) \<Rightarrow> 'a \<Rightarrow> ('a set) \<Rightarrow> bool"
  where "closest_to L c R \<equiv> c\<in>L \<and> (\<forall>r\<in>R. \<forall>l\<in>L-{c}. [[l c r]])"


lemma int_on_path:
  assumes "l\<in>L" "r\<in>R" "Q\<in>\<P>"
      and partition: "L\<subseteq>Q" "L\<noteq>{}" "R\<subseteq>Q" "R\<noteq>{}" "L\<union>R=Q" (*disjoint?*)
    shows "interval l r \<subseteq> Q"
proof
  fix x assume "x\<in>interval l r"
  thus "x\<in>Q"
    unfolding interval_def segment_def
    using betw_b_in_path partition(5) \<open>Q\<in>\<P>\<close> seg_betw \<open>l \<in> L\<close> \<open>r \<in> R\<close>
    by blast
qed


lemma ray_of_bounds1:
  assumes "Q\<in>\<P>" "[f[(f 0)..]X]" "X\<subseteq>Q" "closest_bound c X" "is_bound_f b X f" "b\<noteq>c"
  assumes "is_bound_f x X f"
  shows "x=b \<or> x=c \<or> [[c x b]] \<or> [[c b x]]"
proof -
  have "x\<in>Q"
    using bound_on_path assms(1,3,7) unfolding all_bounds_def is_bound_def is_bound_f_def
    by auto
  {
    assume "x=b"
    hence ?thesis by blast
  } moreover {
    assume "x=c"
    hence ?thesis by blast
  } moreover {
    assume "x\<noteq>b" "x\<noteq>c"
    hence ?thesis
      by (meson abc_abd_bcdbdc assms(4,5,6,7) closest_bound_def is_bound_def)
  }
  ultimately show ?thesis by blast
qed


lemma ray_of_bounds2:
  assumes "Q\<in>\<P>" "[f[(f 0)..]X]" "X\<subseteq>Q" "closest_bound_f c X f" "is_bound_f b X f" "b\<noteq>c"
  assumes "x=b \<or> x=c \<or> [[c x b]] \<or> [[c b x]]"
  shows "is_bound_f x X f"
proof -
  have "x\<in>Q"
    using assms(1,3,4,5,6,7) betw_b_in_path betw_c_in_path bound_on_path
    using closest_bound_f_def is_bound_f_def by metis
  {
    assume "x=b"
    hence ?thesis
      by (simp add: assms(5))
  } moreover {
    assume "x=c"
    hence ?thesis using assms(4)
      by (simp add: closest_bound_f_def)
  } moreover {
    assume "[[c x b]]"
    hence ?thesis unfolding is_bound_f_def
    proof (safe)
      fix i j::nat
      show "[f[f 0..]X]"
        by (simp add: assms(2))
      assume "i<j"
      hence "[[(f i)(f j)b]]"
        using assms(5) is_bound_f_def by blast
      hence "[[(f j) b c]] \<or> [[(f j) c b]]"
        using \<open>i < j\<close> abc_abd_bcdbdc assms(4,6) closest_bound_f_def is_bound_f_def by auto
      thus "[[(f i)(f j)(x)]]"
        by (meson \<open>[[c x b]]\<close> \<open>[[(f i)(f j)b]]\<close> abc_bcd_acd abc_sym abd_bcd_abc)
    qed
  } moreover {
    assume "[[c b x]]"
    hence ?thesis unfolding is_bound_f_def
    proof (safe)
      fix i j::nat
      show "[f[f 0..]X]"
        by (simp add: assms(2))
      assume "i<j"
      hence "[[(f i)(f j)b]]"
        using assms(5) is_bound_f_def by blast
      hence "[[(f j) b c]] \<or> [[(f j) c b]]"
        using \<open>i < j\<close> abc_abd_bcdbdc assms(4,6) closest_bound_f_def is_bound_f_def by auto
      thus "[[(f i)(f j)(x)]]"
      proof -
        have "(c = b) \<or> [[(f 0) c b]]"
          using assms(4,5) closest_bound_f_def is_bound_def by auto
        hence "[[(f j) b c]] \<longrightarrow> [[x(f j)(f i)]]"
          by (metis abc_bcd_acd abc_only_cba(2) assms(5) is_bound_f_def neq0_conv)
        thus ?thesis
          using \<open>[[c b x]]\<close> \<open>[[(f i)(f j)b]]\<close> \<open>[[(f j) b c]] \<or> [[(f j) c b]]\<close> abc_bcd_acd abc_sym
          by blast
      qed
    qed
  }
  ultimately show ?thesis using assms(7) by blast
qed


lemma ray_of_bounds3:
  assumes "Q\<in>\<P>" "[f[(f 0)..]X]" "X\<subseteq>Q" "closest_bound_f c X f" "is_bound_f b X f" "b\<noteq>c"
  shows "all_bounds X = insert c (ray c b)"
proof
  let ?B = "all_bounds X"
  let ?C = "insert c (ray c b)"
  show "?B \<subseteq> ?C"
  proof
    fix x assume "x\<in>?B"
    hence "is_bound x X"
      by (simp add: all_bounds_def)
    hence "x=b \<or> x=c \<or> [[c x b]] \<or> [[c b x]]"
      using ray_of_bounds1 abc_abd_bcdbdc assms(4,5,6)
      by (meson closest_bound_f_def is_bound_def)
    thus "x\<in>?C"
      using pro_betw ray_def seg_betw by auto
  qed
  show "?C \<subseteq> ?B"
  proof
    fix x assume "x\<in>?C"
    hence "x=b \<or> x=c \<or> [[c x b]] \<or> [[c b x]]"
      using pro_betw ray_def seg_betw by auto
    hence "is_bound x X"
      unfolding is_bound_def using ray_of_bounds2 assms
      by blast
    thus "x\<in>?B"
      by (simp add: all_bounds_def)
  qed
qed


lemma ray_of_bounds:
  assumes "[f[(f 0)..]X]" "closest_bound_f c X f" "is_bound_f b X f" "b\<noteq>c"
  shows "all_bounds X = insert c (ray c b)"
  using ray_of_bounds3 assms semifin_chain_on_path by blast


lemma int_in_closed_ray:
  assumes "path ab a b"
  shows "interval a b \<subset> insert a (ray a b)"
proof
  let ?i = "interval a b"
  show "interval a b \<noteq> insert a (ray a b)"
  proof -
    obtain c where "[[a b c]]" using prolong_betw2
      using assms by blast
    hence "c\<in>ray a b"
      using abc_abc_neq pro_betw ray_def by auto
    have "c\<notin>interval a b"
      using \<open>[[a b c]]\<close> abc_abc_neq abc_only_cba(2) interval_def seg_betw by auto
    thus ?thesis
      using \<open>c \<in> ray a b\<close> by blast
  qed
  show "interval a b \<subseteq> insert a (ray a b)"
    using interval_def ray_def by auto
qed


lemma bound_any_f:
  assumes "Q\<in>\<P>" "[f[(f 0)..]X]" "X\<subseteq>Q" "is_bound c X"
  shows "is_bound_f c X f"
proof -
  obtain g where "is_bound_f c X g" "[g[g 0..]X]"
    using assms(4) is_bound_def is_bound_f_def by blast
  show ?thesis
    unfolding is_bound_f_def
  proof (safe)
    fix i j::nat
    show "[f[f 0 ..]X]" by (simp add: assms(2))
    assume "i<j"
    have "[[(g i)(g j)c]]"
      using \<open>i < j\<close> \<open>is_bound_f c X g\<close> is_bound_f_def by blast
    thus "[[(f i)(f j)c]]"
      using inf_chain_unique \<open>[g[g 0 ..]X]\<close> assms(2) by force
  qed
qed


lemma closest_bound_any_f:
  assumes "Q\<in>\<P>" "[f[(f 0)..]X]" "X\<subseteq>Q" "closest_bound c X"
  shows "closest_bound_f c X f"
proof (unfold closest_bound_f_def, safe)
  show "is_bound_f c X f"
  using bound_any_f assms closest_bound_def is_bound_def by blast
next
  fix Q\<^sub>b'
  assume "is_bound Q\<^sub>b' X" "Q\<^sub>b' \<noteq> c" 
  then show "[[(f 0) c Q\<^sub>b']]"
  by (metis (full_types) assms(2,4) closest_bound_def inf_chain_unique is_bound_f_def)
qed

end (* context MinkowskiSpacetime *)


section "3.8 Connectedness of the unreachable set"
context MinkowskiSpacetime begin

subsection \<open>Theorem 13 (Connectedness of the Unreachable Set)\<close>

theorem (*13*) unreach_connected:
  assumes path_Q: "Q\<in>\<P>"
      and event_b: "b\<notin>Q" "b\<in>\<E>"
      and unreach: "Q\<^sub>x \<in> \<emptyset> Q b" "Q\<^sub>z \<in> \<emptyset> Q b" "Q\<^sub>x \<noteq> Q\<^sub>z"
      and xyz: "[[Q\<^sub>x Q\<^sub>y Q\<^sub>z]]"
    shows "Q\<^sub>y \<in> \<emptyset> Q b"
proof -

  text \<open>First we obtain the chain from I6.\<close>
  have in_Q: "Q\<^sub>x\<in>Q \<and> Q\<^sub>y\<in>Q \<and> Q\<^sub>z\<in>Q"
    using betw_b_in_path path_Q unreach(1,2,3) unreach_on_path xyz by blast
  hence event_y: "Q\<^sub>y\<in>\<E>"
    using in_path_event path_Q by blast
  obtain X f where X_def: "ch_by_ord f X" "f 0 = Q\<^sub>x" "f (card X - 1) = Q\<^sub>z"
      "(\<forall>i\<in>{1 .. card X - 1}. (f i) \<in> \<emptyset> Q b \<and> (\<forall>Qy\<in>\<E>. [[(f (i - 1)) Qy (f i)]] \<longrightarrow> Qy \<in> \<emptyset> Q b))"
      "short_ch X \<longrightarrow> Q\<^sub>x \<in> X \<and> Q\<^sub>z \<in> X \<and> (\<forall>Q\<^sub>y\<in>\<E>. [[Q\<^sub>x Q\<^sub>y Q\<^sub>z]] \<longrightarrow> Q\<^sub>y \<in> \<emptyset> Q b)"
    using I6 [OF assms(1-6)] by blast
  hence fin_X: "finite X"
    using unreach(3) not_less by fastforce
  obtain N where "N=card X" "N\<ge>2"
    using X_def(2,3) unreach(3) by fastforce

  text \<open>
  Then we have to manually show the bounds, defined via indices only, are in the obtained chain.
  This step made me add the two-element-chain-case to I6 in \<open>Minkowski.thy\<close>;
  this case is referenced here as \<open>X_def(5)\<close>.
\<close>
  let ?a = "f 0"
  let ?d = "f (card X - 1)"
  {
    assume "card X = 2"
    hence "short_ch X" "?a \<in> X \<and> ?d \<in> X" "?a \<noteq> ?d"
      using X_def \<open>card X = 2\<close> short_ch_card_2  unreach(3) by blast+
  }
  hence "[f[Q\<^sub>x..Q\<^sub>z]X]"
    unfolding fin_chain_def
    by (metis X_def(1-3,5) ch_by_ord_def fin_X fin_long_chain_def get_fin_long_ch_bounds unreach(3))

  text \<open>
  Further on, we split the proof into two cases, namely the split Schutz absorbs into his
  non-strict ordering. Just below is the statement we use \<open>disjE\<close> with.\<close>
  have y_cases: "Q\<^sub>y\<in>X \<or> Q\<^sub>y\<notin>X" by blast
  have y_int: "Q\<^sub>y\<in>interval Q\<^sub>x Q\<^sub>z"
    using interval_def seg_betw xyz by auto
  have X_in_Q: "X\<subseteq>Q"
    using chain_on_path_I6 [where Q=Q and X=X] X_def event_b path_Q unreach
    by blast

  show ?thesis
  proof (cases)
    text \<open>As usual, we treat short chains separately, and they have their own clause in I6.\<close>
    assume "N=2"
    thus ?thesis
      using X_def(1,5) xyz \<open>N = card X\<close> event_y short_ch_card_2 by auto
  next
    text \<open>
  This is where Schutz obtains the chain from Theorem 11. We instead use the chain we already have
  with only a part of Theorem 11, namely \<open>int_split_to_segs\<close>. \<open>?S\<close> is defined like in \<open>segmentation\<close>.\<close>
    assume "N\<noteq>2"
    hence "N\<ge>3" using \<open>2 \<le> N\<close> by auto
    have "2\<le>card X" using \<open>2 \<le> N\<close> \<open>N = card X\<close> by blast
    show ?thesis using y_cases
    proof (rule disjE)
      assume "Q\<^sub>y\<in>X"
      then obtain i where i_def: "i<card X" "Q\<^sub>y = f i"
        using X_def(1)
        unfolding ch_by_ord_def long_ch_by_ord_def ordering_def
        by (metis X_def(5) abc_abc_neq fin_X short_ch_def xyz)
      have "i\<noteq>0 \<and> i\<noteq>card X - 1"
        using X_def(2,3)
        by (metis abc_abc_neq i_def(2) xyz)
      hence "i\<in>{1..card X -1}"
        using i_def(1) by fastforce
      thus ?thesis using X_def(4) i_def(2) by metis
    next
      assume "Q\<^sub>y\<notin>X"

      let ?S = "if card X = 2 then {segment ?a ?d} else {segment (f i) (f(i+1)) | i. i<card X - 1}"

      have "Q\<^sub>y\<in>\<Union>?S"
      proof -
        obtain c where "[f[Q\<^sub>x..c..Q\<^sub>z]X]"
          using X_def(1) \<open>N = card X\<close> \<open>N\<noteq>2\<close> \<open>[f[Q\<^sub>x..Q\<^sub>z]X]\<close> fin_chain_def short_ch_card_2 by auto
        have "interval Q\<^sub>x Q\<^sub>z = \<Union>?S \<union> X"
          using int_split_to_segs [OF `[f[Q\<^sub>x..c..Q\<^sub>z]X]`] by auto
        thus ?thesis
          using \<open>Q\<^sub>y\<notin>X\<close> y_int by blast
      qed
      then obtain s where "s\<in>?S" "Q\<^sub>y\<in>s" by blast

      have "\<exists>i. i\<in>{1..(card X)-1} \<and> [[(f(i-1)) Q\<^sub>y (f i)]]"
      proof -
        obtain i' where i'_def: "i' < N-1" "s = segment (f i') (f (i' + 1))"
          using \<open>Q\<^sub>y\<in>s\<close> \<open>s\<in>?S\<close> \<open>N=card X\<close>
          by (smt \<open>2 \<le> N\<close> \<open>N \<noteq> 2\<close> le_antisym mem_Collect_eq not_less)
        show ?thesis
        proof (rule exI, rule conjI)
          show "(i'+1) \<in> {1..card X - 1}"
            using i'_def(1)
            by (simp add: \<open>N = card X\<close>)
          show "[[(f((i'+1) - 1)) Q\<^sub>y (f(i'+1))]]"
            using i'_def(2) \<open>Q\<^sub>y\<in>s\<close> seg_betw by simp
        qed
      qed
      then obtain i where i_def: "i\<in>{1..(card X)-1}" "[[(f(i-1)) Q\<^sub>y (f i)]]"
        by blast

      show ?thesis
        by (meson X_def(4) i_def event_y)
    qed
  qed
qed

subsection \<open>Theorem 14 (Second Existence Theorem)\<close>

lemma (*for 14i*) union_of_bounded_sets_is_bounded:
  assumes "\<forall>x\<in>A. [[a x b]]" "\<forall>x\<in>B. [[c x d]]" "A\<subseteq>Q" "B\<subseteq>Q" "Q\<in>\<P>"
    "card A > 1 \<or> infinite A" "card B > 1 \<or> infinite B"
  shows "\<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>A\<union>B. [[l x u]]"
proof -
  let ?P = "\<lambda> A B. \<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>A\<union>B. [[l x u]]"
  let ?I = "\<lambda> A a b. (card A > 1 \<or> infinite A) \<and> (\<forall>x\<in>A. [[a x b]])"
  let ?R = "\<lambda>A. \<exists>a b. ?I A a b"

  have on_path: "\<And>a b A. A \<subseteq> Q \<Longrightarrow> ?I A a b \<Longrightarrow> b \<in> Q \<and> a \<in> Q"
  proof -
    fix a b A assume "A\<subseteq>Q" "?I A a b"
    show "b\<in>Q\<and>a\<in>Q"
    proof (cases)
      assume "card A \<le> 1 \<and> finite A"
      thus ?thesis
        using \<open>?I A a b\<close> by auto
    next
      assume "\<not> (card A \<le> 1 \<and> finite A)"
      hence asmA: "card A > 1 \<or> infinite A"
        by linarith
      then obtain x y where "x\<in>A" "y\<in>A" "x\<noteq>y"
      proof 
        assume "1 < card A" "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; x \<noteq> y\<rbrakk> \<Longrightarrow> thesis"
        then show ?thesis 
          by (metis One_nat_def Suc_le_eq card_le_Suc_iff insert_iff)
      next
        assume "infinite A" "\<And>x y. \<lbrakk>x \<in> A; y \<in> A; x \<noteq> y\<rbrakk> \<Longrightarrow> thesis"
        then show ?thesis 
        using infinite_imp_nonempty by (metis finite_insert finite_subset singletonI subsetI)
    qed
      have "x\<in>Q" "y\<in>Q"
        using \<open>A \<subseteq> Q\<close> \<open>x \<in> A\<close> \<open>y \<in> A\<close> by auto
      have "[[a x b]]" "[[a y b]]"
        by (simp add: \<open>(1 < card A \<or> infinite A) \<and> (\<forall>x\<in>A. [[a x b]])\<close> \<open>x \<in> A\<close> \<open>y \<in> A\<close>)+ 
      hence "betw4 a x y b \<or> betw4 a y x b"
        using \<open>x \<noteq> y\<close> abd_acd_abcdacbd by blast
      hence "a\<in>Q \<and> b\<in>Q"
        using \<open>Q\<in>\<P>\<close> \<open>x\<in>Q\<close> \<open>x\<noteq>y\<close> \<open>x\<in>Q\<close> \<open>y\<in>Q\<close> betw_a_in_path betw_c_in_path by blast
      thus ?thesis by simp
    qed
  qed

  show ?thesis
  proof (cases)
    assume "a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d"
    show "?P A B"
    proof (rule_tac P="?P" and A=Q in wlog_endpoints_distinct)

      text \<open>First, some technicalities: the relations $P, I, R$ have the symmetry required.\<close>
      show "\<And>a b I. ?I I a b \<Longrightarrow> ?I I b a" using abc_sym by blast
      show "\<And>a b A. A \<subseteq> Q \<Longrightarrow> ?I A a b \<Longrightarrow> b \<in> Q \<and> a \<in> Q" using on_path assms(5) by blast
      show "\<And>I J. ?R I \<Longrightarrow> ?R J \<Longrightarrow> ?P I J \<Longrightarrow> ?P J I" by (simp add: Un_commute)

      text \<open>Next, the lemma/case assumptions have to be repeated for Isabelle.\<close>
      show "?I A a b" "?I B c d" "A\<subseteq>Q" "B\<subseteq>Q" "Q\<in>\<P>"
        using assms by simp+ 
      show "a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d"
        using \<open>a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d\<close> by simp

      text \<open>Finally, the important bit: proofs for the necessary cases of betweenness.\<close>
      show "?P I J"
        if "?I I a b" "?I J c d"  "I\<subseteq>Q" "J\<subseteq>Q"
          and "betw4 a b c d \<or> betw4 a c b d \<or> betw4 a c d b"
        for I J a b c d
      proof -
        consider "betw4 a b c d"|"betw4 a c b d"|"betw4 a c d b"
          using \<open>betw4 a b c d \<or> betw4 a c b d \<or> betw4 a c d b\<close> by fastforce
        thus ?thesis
        proof (cases)
          assume asm: "betw4 a b c d" show "?P I J"
          proof -
            have "\<forall>x\<in> I\<union>J. [[a x d]]"
              by (metis Un_iff asm betw4_strong betw4_weak that(1) that(2))
            moreover have "a\<in>Q" "d\<in>Q"
              using assms(5) on_path that(1-4) by blast+ 
            ultimately show ?thesis by blast
          qed
        next
          assume "betw4 a c b d" show "?P I J"
          proof -
            have "\<forall>x\<in> I\<union>J. [[a x d]]"
              by (metis Un_iff \<open>betw4 a c b d\<close> abc_bcd_abd abc_bcd_acd betw4_weak that(1,2))
            moreover have "a\<in>Q" "d\<in>Q"
              using assms(5) on_path that(1-4) by blast+ 
            ultimately show ?thesis by blast
          qed
        next
          assume "betw4 a c d b" show "?P I J"
          proof -
            have "\<forall>x\<in> I\<union>J. [[a x b]]"
              using \<open>betw4 a c d b\<close> abc_bcd_abd abc_bcd_acd abe_ade_bcd_ace
              by (meson UnE that(1,2))
            moreover have "a\<in>Q" "b\<in>Q"
              using assms(5) on_path that(1-4) by blast+
            ultimately show ?thesis by blast
          qed
        qed
      qed
    qed
  next
    assume "\<not>(a\<noteq>b \<and> a\<noteq>c \<and> a\<noteq>d \<and> b\<noteq>c \<and> b\<noteq>d \<and> c\<noteq>d)"
  
    show "?P A B"
    proof (rule_tac P="?P" and A=Q in wlog_endpoints_degenerate)

      text \<open>
        This case follows the same pattern as above: the next five \<open>show\<close> statements
        are effectively bookkeeping.\<close>
      show "\<And>a b I. ?I I a b \<Longrightarrow> ?I I b a" using abc_sym by blast
      show "\<And>a b A. A \<subseteq> Q \<Longrightarrow> ?I A a b \<Longrightarrow> b \<in> Q \<and> a \<in> Q" using on_path \<open>Q\<in>\<P>\<close> by blast
      show "\<And>I J. ?R I \<Longrightarrow> ?R J \<Longrightarrow> ?P I J \<Longrightarrow> ?P J I" by (simp add: Un_commute)

      show "?I A a b" "?I B c d" "A\<subseteq>Q" "B\<subseteq>Q" "Q\<in>\<P>"
        using assms by simp+
      show "\<not> (a \<noteq> b \<and> b \<noteq> c \<and> c \<noteq> d \<and> a \<noteq> d \<and> a \<noteq> c \<and> b \<noteq> d)"
        using \<open>\<not> (a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d)\<close> by blast

      text \<open>Again, this is the important bit: proofs for the necessary cases of degeneracy.\<close>
      show "(a = b \<and> b = c \<and> c = d \<longrightarrow> ?P I J) \<and> (a = b \<and> b \<noteq> c \<and> c = d \<longrightarrow> ?P I J) \<and>
          (a = b \<and> b = c \<and> c \<noteq> d \<longrightarrow> ?P I J) \<and> (a = b \<and> b \<noteq> c \<and> c \<noteq> d \<and> a \<noteq> d \<longrightarrow> ?P I J) \<and>
          (a \<noteq> b \<and> b = c \<and> c \<noteq> d \<and> a = d \<longrightarrow> ?P I J) \<and>
          ([[a b c]] \<and> a = d \<longrightarrow> ?P I J) \<and> ([[b a c]] \<and> a = d \<longrightarrow> ?P I J)"
      if "?I I a b" "?I J c d" "I \<subseteq> Q" "J \<subseteq> Q"
      for I J a b c d
      proof (intro conjI impI)
        assume "a = b \<and> b = c \<and> c = d"
        show "\<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>I \<union> J. [[l x u]]"
          using \<open>a = b \<and> b = c \<and> c = d\<close> abc_ac_neq assms(5) ex_crossing_path that(1,2)
          by fastforce
      next
        assume "a = b \<and> b \<noteq> c \<and> c = d"
        show "\<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>I \<union> J. [[l x u]]"
          using \<open>a = b \<and> b \<noteq> c \<and> c = d\<close> abc_ac_neq assms(5) ex_crossing_path that(1,2)
          by (metis Un_iff)
      next
        assume "a = b \<and> b = c \<and> c \<noteq> d"
        hence "\<forall>x\<in> I\<union>J. [[c x d]]"
          using abc_abc_neq that(1,2) by fastforce
        moreover have "c\<in>Q" "d\<in>Q"
          using on_path \<open>a = b \<and> b = c \<and> c \<noteq> d\<close> that(1,3) abc_abc_neq by metis+ 
        ultimately show "\<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>I \<union> J. [[l x u]]" by blast
      next
        assume "a = b \<and> b \<noteq> c \<and> c \<noteq> d \<and> a \<noteq> d"
        hence "\<forall>x\<in> I\<union>J. [[c x d]]"
          using abc_abc_neq that(1,2) by fastforce
        moreover have "c\<in>Q" "d\<in>Q"
          using on_path \<open>a = b \<and> b \<noteq> c \<and> c \<noteq> d \<and> a \<noteq> d\<close> that(1,3) abc_abc_neq by metis+ 
        ultimately show "\<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>I \<union> J. [[l x u]]" by blast
      next
        assume "a \<noteq> b \<and> b = c \<and> c \<noteq> d \<and> a = d"
        hence "\<forall>x\<in> I\<union>J. [[c x d]]"
          using abc_sym that(1,2) by auto
        moreover have "c\<in>Q" "d\<in>Q"
          using on_path \<open>a \<noteq> b \<and> b = c \<and> c \<noteq> d \<and> a = d\<close> that(1,3) abc_abc_neq by metis+ 
        ultimately show "\<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>I \<union> J. [[l x u]]" by blast
      next
        assume "[[a b c]] \<and> a = d"
        hence "\<forall>x\<in> I\<union>J. [[c x d]]"
          by (metis UnE abc_acd_abd abc_sym that(1,2))
        moreover have "c\<in>Q" "d\<in>Q"
          using on_path that(2,4) by blast+ 
        ultimately show "\<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>I \<union> J. [[l x u]]" by blast
      next
        assume "[[b a c]] \<and> a = d"
        hence "\<forall>x\<in> I\<union>J. [[c x b]]"
          using  abc_sym abd_bcd_abc betw4_strong that(1,2) by (metis Un_iff)
        moreover have "c\<in>Q" "b\<in>Q"
          using on_path that by blast+ 
        ultimately show "\<exists>l\<in>Q. \<exists>u\<in>Q. \<forall>x\<in>I \<union> J. [[l x u]]" by blast
      qed
    qed
  qed
qed


lemma (*for 14i*) union_of_bounded_sets_is_bounded2:
  assumes "\<forall>x\<in>A. [[a x b]]" "\<forall>x\<in>B. [[c x d]]" "A\<subseteq>Q" "B\<subseteq>Q" "Q\<in>\<P>"
      "1<card A \<or> infinite A" "1<card B \<or> infinite B"
    shows "\<exists>l\<in>Q-(A\<union>B). \<exists>u\<in>Q-(A\<union>B). \<forall>x\<in>A\<union>B. [[l x u]]"
  using assms union_of_bounded_sets_is_bounded
    [where A=A and a=a and b=b and B=B and c=c and d=d and Q=Q]
  by (metis Diff_iff abc_abc_neq)

text \<open>
  Schutz proves a mildly stronger version of this theorem than he states. Namely, he gives an
  additional condition that has to be fulfilled by the bounds $y,z$ in the proof (\<open>y,z\<notin>\<emptyset> Q ab\<close>).
  This condition is trivial given \<open>abc_abc_neq\<close>. His stating it in the proof makes me wonder
  whether his (strictly speaking) undefined notion of bounded set is somehow weaker than the
  version using strict betweenness in his theorem statement and used here in Isabelle.
  This would make sense, given the obvious analogy with sets on the real line.
\<close>

theorem (*14i*) second_existence_thm_1:
  assumes path_Q: "Q\<in>\<P>"
      and events: "a\<notin>Q" "b\<notin>Q"
      and reachable: "path_ex a q1" "path_ex b q2" "q1\<in>Q" "q2\<in>Q" (* "\<exists>P\<in>\<P>. \<exists>q\<in>Q. path P a q" *)(*  "\<exists>P\<in>\<P>. \<exists>q\<in>Q. path P b q" *)
    shows "\<exists>y\<in>Q. \<exists>z\<in>Q. (\<forall>x\<in>\<emptyset> Q a. [[y x z]]) \<and> (\<forall>x\<in>\<emptyset> Q b. [[y x z]])"
proof -
  text \<open>Slightly annoying: Schutz implicitly extends \<open>bounded\<close> to sets, so his statements are neater.\<close>

(* alternative way of saying reachable *)
  have "\<exists>q\<in>Q. q\<notin>(\<emptyset> Q a)" "\<exists>q\<in>Q. q\<notin>(\<emptyset> Q b)"
    using cross_in_reachable reachable by blast+

  text \<open>This is a helper statement for obtaining bounds in both directions of both unreachable sets.
  Notice this needs Theorem 13 right now, Schutz claims only Theorem 4. I think this is necessary?\<close>
  have get_bds: "\<exists>la\<in>Q. \<exists>ua\<in>Q. la\<notin>\<emptyset> Q a \<and> ua\<notin>\<emptyset> Q a \<and> (\<forall>x\<in>\<emptyset> Q a. [[la x ua]])"
    if asm: "a\<notin>Q" "path_ex a q" "q\<in>Q"
    for a q
  proof -
    obtain Qy where "Qy\<in>\<emptyset> Q a"
      using asm(2) \<open>a \<notin> Q\<close> in_path_event path_Q two_in_unreach by blast
    then obtain la where "la \<in> Q - \<emptyset> Q a"
      using asm(2,3) cross_in_reachable by blast
    then obtain ua where "ua \<in> Q - \<emptyset> Q a" "[[la Qy ua]]" "la \<noteq> ua"
      using unreachable_set_bounded [where Q=Q and b=a and Qx=la and Qy=Qy]
      using \<open>Qy \<in> \<emptyset> Q a\<close> asm in_path_event path_Q by blast
    have "la \<notin> \<emptyset> Q a \<and> ua \<notin> \<emptyset> Q a \<and> (\<forall>x\<in>\<emptyset> Q a. (x\<noteq>la \<and> x\<noteq>ua) \<longrightarrow> [[la x ua]])"
    proof (intro conjI)
      show "la \<notin> \<emptyset> Q a"
        using \<open>la \<in> Q - \<emptyset> Q a\<close> by force
    next
      show "ua \<notin> \<emptyset> Q a"
        using \<open>ua \<in> Q - \<emptyset> Q a\<close> by force
    next show "\<forall>x\<in>\<emptyset> Q a. x \<noteq> la \<and> x \<noteq> ua \<longrightarrow> [[la x ua]]"
    proof (safe)
      fix x assume "x\<in>\<emptyset> Q a" "x\<noteq>la" "x\<noteq>ua"
      {
        assume "x=Qy" hence "[[la x ua]]" by (simp add: \<open>[[la Qy ua]]\<close>)
      } moreover {
        assume "x\<noteq>Qy"
        have "[[Qy x la]] \<or> [[la Qy x]]"
        proof -
          { assume "[[x la Qy]]"
            hence "la\<in>\<emptyset> Q a"
              using unreach_connected \<open>Qy\<in>\<emptyset> Q a\<close>\<open>x\<in>\<emptyset> Q a\<close>\<open>x\<noteq>Qy\<close> in_path_event path_Q that by blast
            hence False
              using \<open>la \<in> Q - \<emptyset> Q a\<close> by blast }
          thus "[[Qy x la]] \<or> [[la Qy x]]"
            using some_betw [where Q=Q and a=x and b=la and c=Qy] path_Q unreach_on_path
            using \<open>Qy \<in> \<emptyset> Q a\<close> \<open>la \<in> Q - \<emptyset> Q a\<close> \<open>x \<in> \<emptyset> Q a\<close> \<open>x \<noteq> Qy\<close> \<open>x \<noteq> la\<close> by force
        qed
        hence "[[la x ua]]"
          (* by (smt DiffD1 DiffD2 \<open>Qy \<in> \<emptyset> Q a\<close> \<open>[[la Qy ua]]\<close> \<open>ua \<in> Q - \<emptyset> Q a\<close> \<open>x \<in> \<emptyset> Q a\<close> \<open>x \<noteq> la\<close> abc_abd_acdadc abc_acd_abd abc_only_cba abc_sym in_path_event path_Q some_betw that(1) that(2) unreach_connected unreach_on_path) *)
        proof
          assume "[[Qy x la]]"
          thus ?thesis using \<open>[[la Qy ua]]\<close> abc_acd_abd abc_sym by blast
        next
          assume "[[la Qy x]]"
          hence "[[la x ua]] \<or> [[la ua x]]"
            using \<open>[[la Qy ua]]\<close> \<open>x \<noteq> ua\<close> abc_abd_acdadc by auto
          have "\<not>[[la ua x]]"
            using unreach_connected that abc_abc_neq abc_acd_bcd in_path_event path_Q
            by (metis DiffD2 \<open>Qy \<in> \<emptyset> Q a\<close> \<open>[[la Qy ua]]\<close> \<open>ua \<in> Q - \<emptyset> Q a\<close> \<open>x \<in> \<emptyset> Q a\<close>)
          show ?thesis
            using \<open>[[la x ua]] \<or> [[la ua x]]\<close> \<open>\<not> [[la ua x]]\<close> by linarith
        qed
      }
      ultimately show "[[la x ua]]" by blast
    qed
  qed
    thus ?thesis using \<open>la \<in> Q - \<emptyset> Q a\<close> \<open>ua \<in> Q - \<emptyset> Q a\<close> by force
  qed

  have "\<exists>y\<in>Q. \<exists>z\<in>Q. (\<forall>x\<in>(\<emptyset> Q a)\<union>(\<emptyset> Q b). [[y x z]])"
  proof -
    obtain la ua where "\<forall>x\<in>\<emptyset> Q a. [[la x ua]]"
      using events(1) get_bds reachable(1,3) by blast
    obtain lb ub where "\<forall>x\<in>\<emptyset> Q b. [[lb x ub]]"
      using events(2) get_bds reachable(2,4) by blast
    have "\<emptyset> Q a \<subseteq> Q" "\<emptyset> Q b \<subseteq> Q"
      by (simp add: subsetI unreach_on_path)+
    moreover have "1 < card (\<emptyset> Q a) \<or> infinite (\<emptyset> Q a)"
      using two_in_unreach events(1) in_path_event path_Q reachable(1)
      by (metis One_nat_def card_le_Suc0_iff_eq not_less)
    moreover have "1 < card (\<emptyset> Q b) \<or> infinite (\<emptyset> Q b)"
      using two_in_unreach events(2) in_path_event path_Q reachable(2)
      by (metis One_nat_def card_le_Suc0_iff_eq not_less)
    ultimately show ?thesis
      using union_of_bounded_sets_is_bounded [where Q=Q and A="\<emptyset> Q a" and B="\<emptyset> Q b"]
      using get_bds assms `\<forall>x\<in>\<emptyset> Q a. [[la x ua]]` `\<forall>x\<in>\<emptyset> Q b. [[lb x ub]]`
      by blast
  qed

  then obtain y z where "y\<in>Q" "z\<in>Q" "(\<forall>x\<in>(\<emptyset> Q a)\<union>(\<emptyset> Q b). [[y x z]])"
    by blast
  show ?thesis
  proof (rule bexI)+
    show "y\<in>Q" by (simp add: \<open>y \<in> Q\<close>)
    show "z\<in>Q" by (simp add: \<open>z \<in> Q\<close>)
    show "(\<forall>x\<in>\<emptyset> Q a. [[z x y]]) \<and> (\<forall>x\<in>\<emptyset> Q b. [[z x y]])"
      by (simp add: \<open>\<forall>x\<in>\<emptyset> Q a \<union> \<emptyset> Q b. [[y x z]]\<close> abc_sym)
  qed
qed


theorem (*14*) second_existence_thm_2:
  assumes path_Q: "Q\<in>\<P>"
      and events: "a\<notin>Q" "b\<notin>Q" "c\<in>Q" "d\<in>Q" "c\<noteq>d"
      and reachable: "\<exists>P\<in>\<P>. \<exists>q\<in>Q. path P a q" "\<exists>P\<in>\<P>. \<exists>q\<in>Q. path P b q"
    shows "\<exists>e\<in>Q. \<exists>ae\<in>\<P>. \<exists>be\<in>\<P>. path ae a e \<and> path be b e \<and> [[c d e]]"
proof -
  obtain y z where bounds_yz: "(\<forall>x\<in>\<emptyset> Q a. [[z x y]]) \<and> (\<forall>x\<in>\<emptyset> Q b. [[z x y]])"
               and yz_inQ: "y\<in>Q" "z\<in>Q"
    using second_existence_thm_1 [where Q=Q and a=a and b=b]
    using path_Q events(1,2) reachable by blast
  have "y\<notin>(\<emptyset> Q a)\<union>(\<emptyset> Q b)" "z\<notin>(\<emptyset> Q a)\<union>(\<emptyset> Q b)"
    by (meson Un_iff \<open>(\<forall>x\<in>\<emptyset> Q a. [[z x y]]) \<and> (\<forall>x\<in>\<emptyset> Q b. [[z x y]])\<close> abc_abc_neq)+ 
  let ?P = "\<lambda>e ae be. (e\<in>Q \<and> path ae a e \<and> path be b e \<and> [[c d e]])"

  have exist_ay: "\<exists>ay. path ay a y"
    if "a\<notin>Q" "\<exists>P\<in>\<P>. \<exists>q\<in>Q. path P a q" "y\<notin>(\<emptyset> Q a)" "y\<in>Q"
    for a y
    using in_path_event path_Q that unreachable_bounded_path_only
    by blast

  have "[[c d y]] \<or> \<lbrakk>y c d]] \<or> [[c y d\<rbrakk>"
    by (meson \<open>y \<in> Q\<close> abc_sym events(3-5) path_Q some_betw)
  moreover have "[[c d z]] \<or> \<lbrakk>z c d]] \<or> [[c z d\<rbrakk>"
    by (meson \<open>z \<in> Q\<close> abc_sym events(3-5) path_Q some_betw)
  ultimately consider "[[c d y]]" | "[[c d z]]" |
                      "((\<lbrakk>y c d]] \<or> [[c y d\<rbrakk>) \<and> (\<lbrakk>z c d]] \<or> [[c z d\<rbrakk>))"
    by auto
  thus ?thesis
  proof (cases)
    assume "[[c d y]]"
    have "y\<notin>(\<emptyset> Q a)" "y\<notin>(\<emptyset> Q b)"
      using \<open>y \<notin> \<emptyset> Q a \<union> \<emptyset> Q b\<close> by blast+
    then obtain ay yb where "path ay a y" "path yb b y"
      using `y\<in>Q` exist_ay events(1,2) reachable(1,2) by blast
    have "?P y ay yb"
      using \<open>[[c d y]]\<close> \<open>path ay a y\<close> \<open>path yb b y\<close> \<open>y \<in> Q\<close> by blast
    thus ?thesis by blast
  next
    assume "[[c d z]]"
    have "z\<notin>(\<emptyset> Q a)" "z\<notin>(\<emptyset> Q b)"
      using \<open>z \<notin> \<emptyset> Q a \<union> \<emptyset> Q b\<close> by blast+ 
    then obtain az bz where "path az a z" "path bz b z"
      using `z\<in>Q` exist_ay events(1,2) reachable(1,2) by blast
    have "?P z az bz"
      using \<open>[[c d z]]\<close> \<open>path az a z\<close> \<open>path bz b z\<close> \<open>z \<in> Q\<close> by blast
    thus ?thesis by blast
  next
    assume "(\<lbrakk>y c d]] \<or> [[c y d\<rbrakk>) \<and> (\<lbrakk>z c d]] \<or> [[c z d\<rbrakk>)"
    have "\<exists>e. [[c d e]]"
      using prolong_betw (* works as Schutz says! *)
      using events(3-5) path_Q by blast
    then obtain e where "[[c d e]]" by auto
    have "\<not>[[y e z]]"
    proof (rule notI)
      text \<open>Notice Theorem 10 is not needed for this proof, and does not seem to help \<open>sledgehammer\<close>.
        I think this is because it cannot be easily/automatically reconciled with non-strict
        notation.\<close>
      assume "[[y e z]]"
      moreover consider "(\<lbrakk>y c d]] \<and> \<lbrakk>z c d]])" | "(\<lbrakk>y c d]] \<and> [[c z d\<rbrakk>)" |
               "([[c y d\<rbrakk> \<and> \<lbrakk>z c d]])" | "([[c y d\<rbrakk> \<and> [[c z d\<rbrakk>)"
        using \<open>(\<lbrakk>y c d]] \<or> [[c y d\<rbrakk>) \<and> (\<lbrakk>z c d]] \<or> [[c z d\<rbrakk>)\<close> by linarith
      ultimately show False
        by (smt \<open>[[c d e]]\<close> abc_ac_neq betw4_strong betw4_weak)
    qed
    have "e\<in>Q"
      using \<open>[[c d e]]\<close> betw_c_in_path events(3-5) path_Q by blast
    have "e\<notin> \<emptyset> Q a" "e\<notin> \<emptyset> Q b"
      using bounds_yz \<open>\<not> [[y e z]]\<close> abc_sym by blast+ 
    hence ex_aebe: "\<exists>ae be. path ae a e \<and> path be b e"
      using \<open>e \<in> Q\<close> events(1,2) in_path_event path_Q reachable(1,2) unreachable_bounded_path_only
      by metis
    thus ?thesis
      using \<open>[[c d e]]\<close> \<open>e \<in> Q\<close> by blast
  qed
qed

text \<open>
  The assumption \<open>Q\<noteq>R\<close> in Theorem 14(iii) is somewhat implicit in Schutz.
  If \<open>Q=R\<close>, \<open>\<emptyset> Q a\<close> is empty, so the third conjunct of the conclusion is meaningless.
\<close>

theorem (*14*) second_existence_thm_3:
  assumes paths: "Q\<in>\<P>" "R\<in>\<P>" "Q\<noteq>R"
      and events: "x\<in>Q" "x\<in>R" "a\<in>R" "a\<noteq>x" "b\<notin>Q"
      and reachable: "\<exists>P\<in>\<P>. \<exists>q\<in>Q. path P b q"
    shows "\<exists>e\<in>\<E>. \<exists>ae\<in>\<P>. \<exists>be\<in>\<P>. path ae a e \<and> path be b e \<and> (\<forall>y\<in>\<emptyset> Q a. [[x y e]])"
proof -
  have "a\<notin>Q"
    using events(1-4) paths eq_paths by blast
  hence "\<emptyset> Q a \<noteq> {}"
    by (metis events(3) ex_in_conv in_path_event paths(1,2) two_in_unreach)

  then obtain d where "d\<in> \<emptyset> Q a" (*as in Schutz*)
    by blast
  have "x\<noteq>d"
    using \<open>d \<in> \<emptyset> Q a\<close> cross_in_reachable events(1) events(2) events(3) paths(2) by auto
  have "d\<in>Q"
    using \<open>d \<in> \<emptyset> Q a\<close> unreach_on_path by blast

  have "\<exists>e\<in>Q. \<exists>ae be. [[x d e]] \<and> path ae a e \<and> path be b e"
    using second_existence_thm_2 [where c=x and Q=Q and a=a and b=b and d=d] (*as in Schutz*)
    using \<open>a \<notin> Q\<close> \<open>d \<in> Q\<close> \<open>x \<noteq> d\<close> events(1-3,5) paths(1,2) reachable by blast
  then obtain e ae be where conds: "[[x d e]] \<and> path ae a e \<and> path be b e" by blast
  have "\<forall>y\<in>(\<emptyset> Q a). [[x y e]]"
  proof
    fix y assume "y\<in>(\<emptyset> Q a)"
    hence "y\<in>Q"
      using unreach_on_path by blast
    show "[[x y e]]"
    proof (rule ccontr)
      assume "\<not>[[x y e]]"
      then consider "y=x" | "y=e" | "[[y x e]]" | "[[x e y]]"
        by (metis \<open>d\<in>Q\<close> \<open>y\<in>Q\<close> abc_abc_neq abc_sym betw_c_in_path conds events(1) paths(1) some_betw)
      thus False
      proof (cases)
        assume "y=x" thus False
          using \<open>y \<in> \<emptyset> Q a\<close> events(2,3) paths(1,2) same_empty_unreach unreach_equiv unreach_on_path
          by blast
      next
        assume "y=e" thus False
          by (metis \<open>y\<in>Q\<close> assms(1) conds empty_iff same_empty_unreach unreach_equiv \<open>y \<in> \<emptyset> Q a\<close>)
      next
        assume "[[y x e]]"
        hence "[[y x d]]"
          using abd_bcd_abc conds by blast
        hence "x\<in>(\<emptyset> Q a)"
          using unreach_connected [where Q=Q and Q\<^sub>x=y and Q\<^sub>y=x and Q\<^sub>z=d and b=a]
          using \<open>\<not>[[x y e]]\<close> \<open>a\<notin>Q\<close> \<open>d\<in>\<emptyset> Q a\<close> \<open>y\<in>\<emptyset> Q a\<close> conds in_path_event paths(1) by blast
        thus False
          using empty_iff events(2,3) paths(1,2) same_empty_unreach unreach_equiv unreach_on_path
          by metis
      next
        assume "[[x e y]]"
        hence "[[d e y]]"
          using abc_acd_bcd conds by blast
        hence "e\<in>(\<emptyset> Q a)"
          using unreach_connected [where Q=Q and Q\<^sub>x=y and Q\<^sub>y=e and Q\<^sub>z=d and b=a]
          using \<open>a \<notin> Q\<close> \<open>d \<in> \<emptyset> Q a\<close> \<open>y \<in> \<emptyset> Q a\<close>
            abc_abc_neq abc_sym events(3) in_path_event paths(1,2)
          by blast
        thus False
          by (metis conds empty_iff paths(1) same_empty_unreach unreach_equiv unreach_on_path)
      qed
    qed
  qed
  thus ?thesis
    using conds in_path_event by blast 
qed


end (* context MinkowskiSpacetime *)

section "Theorem 11 - with path density assumed"
locale MinkowskiDense = MinkowskiSpacetime +
  assumes path_dense: "path ab a b \<Longrightarrow> \<exists>x. [[a x b]]"
begin

text \<open>
  Path density: if $a$ and $b$ are connected by a path, then the segment between them is nonempty.
  Since Schutz insists on the number of segments in his segmentation (Theorem 11), we prove it here,
  showcasing where his missing assumption of path density fits in
  (it is used three times in \<open>number_of_segments\<close>, once in each separate meaningful ordering case).
\<close>

lemma segment_nonempty:
  assumes "path ab a b"
  obtains x where "x \<in> segment a b"
  using path_dense by (metis seg_betw assms)


lemma (*for 11*) number_of_segments:
  assumes path_P: "P\<in>\<P>"
      and Q_def: "Q\<subseteq>P"
      and f_def: "[f[a..b..c]Q]"
    shows "card {segment (f i) (f (i+1)) | i. i<(card Q-1)} = card Q - 1"
proof -
  let ?S = "{segment (f i) (f (i+1)) | i. i<(card Q-1)}"
  let ?N = "card Q"
  let ?g = "\<lambda> i. segment (f i) (f (i+1))"
  have "?N \<ge> 3"
    by (meson ch_by_ord_def f_def fin_long_chain_def long_ch_card_ge3)
  have "?g ` {0..?N-2} = ?S"
  proof (safe)
    fix i assume "i\<in>{(0::nat)..?N-2}"
    show "\<exists>ia. segment (f i) (f (i+1)) = segment (f ia) (f (ia+1)) \<and> ia<card Q - 1"
    proof
      have "i<?N-1"
        using assms \<open>i\<in>{(0::nat)..?N-2}\<close> `?N\<ge>3`
        by (metis One_nat_def Suc_diff_Suc atLeastAtMost_iff le_less_trans lessI less_le_trans
            less_trans numeral_2_eq_2 numeral_3_eq_3)
      then show "segment (f i) (f (i + 1)) = segment (f i) (f (i + 1)) \<and> i<?N-1"
        by blast
    qed
  next
    fix x i assume "i < card Q - 1"
    let ?s = "segment (f i) (f (i + 1))"
    show "?s \<in> ?g ` {0..?N - 2}"
    proof -
      have "i\<in>{0..?N-2}"
        using \<open>i < card Q - 1\<close> by force
      thus ?thesis by blast
    qed
  qed
  moreover have "inj_on ?g {0..?N-2}"
  proof
    fix i j assume asm: "i\<in>{0..?N-2}" "j\<in>{0..?N-2}" "?g i = ?g j"
    show "i=j"
    proof (rule ccontr)
      assume "i\<noteq>j"
      hence "f i \<noteq> f j"
        using asm(1,2) f_def assms(3) indices_neq_imp_events_neq
          [where X=Q and f=f and a=a and b=b and c=c and i=i and j=j]
        by auto
      show False
      proof (cases)
        assume "j=i+1"
        hence "[[(f i) (f j) (f (j+1))]]"
          using asm(2) assms fin_long_chain_def order_finite_chain `?N\<ge>3`
          by (metis (no_types, lifting) One_nat_def Suc_diff_Suc Suc_less_eq add.commute
              add_leD2 atLeastAtMost_iff card.remove card_Diff_singleton less_Suc_eq_le
              less_add_one numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc)
        obtain e where "e\<in>?g j" using segment_nonempty abc_ex_path asm(3)
          by (metis \<open>[[(f i) (f j) (f (j + 1))]]\<close> \<open>f i \<noteq> f j\<close> \<open>j = i + 1\<close>)
        hence "e\<in>?g i"
          using asm(3) by blast
        have "[[(f i) (f j) e]]"
          using abd_bcd_abc \<open>[[(f i) (f j) (f (j + 1))]]\<close>
          by (meson \<open>e \<in> segment (f j) (f (j + 1))\<close> seg_betw) 
        thus False
          using \<open>e \<in> segment (f i) (f (i + 1))\<close> \<open>j = i + 1\<close> abc_only_cba(2) seg_betw
          by auto
      next assume "j\<noteq>i+1"
        have "i < card Q \<and> j < card Q \<and> (i+1) < card Q"
          using add_mono_thms_linordered_field(3) asm(1,2) assms `?N\<ge>3` by auto
        hence "f i \<in> Q \<and> f j \<in> Q \<and> f (i+1) \<in> Q"
          using f_def unfolding fin_long_chain_def long_ch_by_ord_def ordering_def
          by blast
        hence "f i \<in> P \<and> f j \<in> P \<and> f (i+1) \<in> P"
          using path_is_union assms
          by (simp add: subset_iff)
        then consider "[[(f i) (f(i+1)) (f j)]]" | "[[(f i) (f j) (f(i+1))]]" |
                      "[[(f(i+1)) (f i) (f j)]]"
          using some_betw path_P f_def indices_neq_imp_events_neq
            \<open>f i \<noteq> f j\<close> \<open>i < card Q \<and> j < card Q \<and> i + 1 < card Q\<close> \<open>j \<noteq> i + 1\<close>
          by (metis abc_sym less_add_one less_irrefl_nat)
        thus False
        proof (cases)
          assume "[[(f(i+1)) (f i) (f j)]]"
          then obtain e where "e\<in>?g i" using segment_nonempty
            by (metis \<open>f i \<in> P \<and> f j \<in> P \<and> f (i + 1) \<in> P\<close> abc_abc_neq path_P)
          hence "[[e (f j) (f(j+1))]]"
            using \<open>[[(f(i+1)) (f i) (f j)]]\<close>
            by (smt abc_acd_abd abc_acd_bcd abc_only_cba abc_sym asm(3) seg_betw)
          moreover have "e\<in>?g j"
            using \<open>e \<in> ?g i\<close> asm(3) by blast
          ultimately show False
            by (simp add: abc_only_cba(1) seg_betw)
        next
          assume "[[(f i) (f j) (f(i+1))]]"
          thus False
            using abc_abc_neq [where b="f j" and a="f i" and c="f(i+1)"] asm(3) seg_betw [where x="f j"]
            using ends_notin_segment by blast
        next
          assume "[[(f i) (f(i+1)) (f j)]]"
          then obtain e where "e\<in>?g i" using segment_nonempty
            by (metis \<open>f i \<in> P \<and> f j \<in> P \<and> f (i + 1) \<in> P\<close> abc_abc_neq path_P)
          hence "[[e (f j) (f(j+1))]]"
          proof -
            have "f (i+1) \<noteq> f j"
              using \<open>[[(f i) (f(i+1)) (f j)]]\<close> abc_abc_neq by presburger
            then show ?thesis
              using \<open>e \<in> segment (f i) (f (i+1))\<close> \<open>[[(f i) (f(i+1)) (f j)]]\<close> asm(3) seg_betw
              by (metis (no_types) abc_abc_neq abc_acd_abd abc_acd_bcd abc_sym)
          qed
          moreover have "e\<in>?g j"
            using \<open>e \<in> ?g i\<close> asm(3) by blast
          ultimately show False
            by (simp add: abc_only_cba(1) seg_betw)
        qed
      qed
    qed
  qed
  ultimately have "bij_betw ?g {0..?N-2} ?S"
    using inj_on_imp_bij_betw by fastforce
  thus ?thesis
    using assms(2) bij_betw_same_card numeral_2_eq_2 numeral_3_eq_3 `?N\<ge>3`
    by (metis (no_types, lifting) One_nat_def Suc_diff_Suc card_atLeastAtMost le_less_trans
        less_Suc_eq_le minus_nat.diff_0 not_less not_numeral_le_zero)
qed

theorem (*11*) segmentation_card:
  assumes path_P: "P\<in>\<P>"
      and Q_def: "Q\<subseteq>P"
      and f_def: "[f[a..b]Q]" (* This always exists given card Q > 2 *)
    fixes P1 defines P1_def: "P1 \<equiv> prolongation b a"
    fixes P2 defines  P2_def: "P2 \<equiv> prolongation a b"
    fixes S defines S_def: "S \<equiv> (if card Q=2 then {segment a b} else {segment (f i) (f (i+1)) | i. i<card Q-1})"
    shows "P = ((\<Union>S) \<union> P1 \<union> P2 \<union> Q)"
        (* The union of these segments and prolongations with the separating points is the path. *)
          "card S = (card Q-1) \<and> (\<forall>x\<in>S. is_segment x)"
        (* There are N-1 segments. *)
        (* There are two prolongations. *)
            (* "P1\<inter>P2={} \<and> (\<forall>x\<in>S. (x\<inter>P1={} \<and> x\<inter>P2={} \<and> (\<forall>y\<in>S. x\<noteq>y \<longrightarrow> x\<inter>y={})))" *)
          "disjoint (S\<union>{P1,P2})" "P1\<noteq>P2" "P1\<notin>S" "P2\<notin>S"
        (* The prolongations and all the segments are disjoint. *)
proof -
  let ?N = "card Q"
  have "2 \<le> card Q"
    using f_def fin_chain_card_geq_2 by blast
  have seg_facts: "P = (\<Union>S \<union> P1 \<union> P2 \<union> Q)" "(\<forall>x\<in>S. is_segment x)"
    "disjoint (S\<union>{P1,P2})" "P1\<noteq>P2" "P1\<notin>S" "P2\<notin>S"
    using show_segmentation [OF path_P Q_def f_def]
    using P1_def P2_def S_def by fastforce+
  show "P = \<Union>S \<union> P1 \<union> P2 \<union> Q" by (simp add: seg_facts(1))
  show "disjoint (S\<union>{P1,P2})" "P1\<noteq>P2" "P1\<notin>S" "P2\<notin>S"
    using seg_facts(3-6) by blast+
  have "card S = (?N-1)"
  proof (cases)
    assume "?N=2"
    hence "card S = 1"
      by (simp add: S_def)
    thus ?thesis
      by (simp add: \<open>?N = 2\<close>)
  next
    assume "?N\<noteq>2"
    hence "?N\<ge>3"
      using \<open>2 \<le> card Q\<close> by linarith
    then obtain c where "[f[a..c..b]Q]"
      using assms ch_by_ord_def fin_chain_def short_ch_card_2 \<open>2 \<le> card Q\<close> \<open>card Q \<noteq> 2\<close>
      by force
    show ?thesis
      using number_of_segments [OF assms(1,2) `[f[a..c..b]Q]`]
      using S_def \<open>card Q \<noteq> 2\<close> by presburger
  qed
  thus "card S = card Q - 1 \<and> Ball S is_segment"
    using seg_facts(2) by blast
qed


end (* context MinkowskiDense *)

end