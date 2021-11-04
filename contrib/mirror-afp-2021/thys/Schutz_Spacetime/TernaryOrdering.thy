(*  Title:      Schutz_Spacetime/TernaryOrdering.thy
    Authors:    Richard Schmoetten, Jake Palmer and Jacques D. Fleuriot
                University of Edinburgh, 2021          
*)
theory TernaryOrdering
  imports Util

begin

text \<open>
  Definition of chains using an ordering on sets of events
  based on natural numbers, plus some proofs.
\<close>

section \<open>Totally ordered chains\<close>

text \<open>
  Based on page 110 of Phil Scott's thesis and the following HOL Light definition:
  \begin{verbatim}
  let ORDERING = new_definition
    `ORDERING f X <=> (!n. (FINITE X ==> n < CARD X) ==> f n IN X)
                    /\ (!x. x IN X ==> ?n. (FINITE X ==> n < CARD X)
                        /\ f n = x)                   
                    /\ !n n' n''. (FINITE X ==> n'' < CARD X)
                          /\ n < n' /\ n' < n'' 
                          ==> between (f n) (f n') (f n'')`;;
  \end{verbatim}
  I've made it strict for simplicity, and because that's how Schutz's ordering is. It could be
  made more generic by taking in the function corresponding to $<$ as a paramater.
  Main difference to Schutz: he has local order, not total (cf Theorem 2 and \<open>ordering2\<close>).
\<close>

definition ordering :: "(nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "ordering f ord X \<equiv> (\<forall>n. (finite X \<longrightarrow> n < card X) \<longrightarrow> f n \<in> X)
                     \<and> (\<forall>x\<in>X. (\<exists>n. (finite X \<longrightarrow> n < card X) \<and> f n = x))
                     \<and> (\<forall>n n' n''. (finite X \<longrightarrow> n'' < card X) \<and> n < n' \<and> n' < n''
                                   \<longrightarrow> ord (f n) (f n') (f n''))"

lemma ordering_ord_ijk:
  assumes "ordering f ord X"
      and "i < j \<and> j < k \<and> (finite X \<longrightarrow> k < card X)"
  shows "ord (f i) (f j) (f k)"
by (metis ordering_def assms)

lemma empty_ordering [simp]: "\<exists>f. ordering f ord {}"
by (simp add: ordering_def)

lemma singleton_ordering [simp]: "\<exists>f. ordering f ord {a}"
apply (rule_tac x = "\<lambda>n. a" in exI)
by (simp add: ordering_def)

lemma two_ordering [simp]: "\<exists>f. ordering f ord {a, b}"
proof cases
  assume "a = b"
  thus ?thesis using singleton_ordering by simp
next
  assume a_neq_b: "a \<noteq> b"
  let ?f = "\<lambda>n. if n = 0 then a else b"
  have ordering1: "(\<forall>n. (finite {a,b} \<longrightarrow> n < card {a,b}) \<longrightarrow> ?f n \<in> {a,b})" by simp
  have ordering2: "(\<forall>x\<in>{a,b}. \<exists>n. (finite {a,b} \<longrightarrow> n < card {a,b}) \<and> ?f n = x)"
    using a_neq_b all_not_in_conv card_Suc_eq card_0_eq card_gt_0_iff insert_iff lessI by auto
  have ordering3: "(\<forall>n n' n''. (finite {a,b} \<longrightarrow> n'' < card {a,b}) \<and> n < n' \<and> n' < n''
                                \<longrightarrow> ord (?f n) (?f n') (?f n''))" using a_neq_b by auto
  have "ordering ?f ord {a, b}" using ordering_def ordering1 ordering2 ordering3 by blast
  thus ?thesis by auto
qed

lemma card_le2_ordering:
  assumes finiteX: "finite X"
      and card_le2: "card X \<le> 2"
  shows "\<exists>f. ordering f ord X"
proof -
  have card012: "card X = 0 \<or> card X = 1 \<or> card X = 2" using card_le2 by auto
  have card0: "card X = 0 \<longrightarrow> ?thesis" using finiteX by simp
  have card1: "card X = 1 \<longrightarrow> ?thesis" using card_eq_SucD by fastforce
  have card2: "card X = 2 \<longrightarrow> ?thesis" by (metis two_ordering card_eq_SucD numeral_2_eq_2)
  thus ?thesis using card012 card0 card1 card2 by auto
qed

lemma ord_ordered:
  assumes abc: "ord a b c"
      and abc_neq: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c"
  shows "\<exists>f. ordering f ord {a,b,c}"
apply (rule_tac x = "\<lambda>n. if n = 0 then a else if n = 1 then b else c" in exI)
apply (unfold ordering_def)
using abc abc_neq by auto

lemma overlap_ordering:
  assumes abc: "ord a b c"
      and bcd: "ord b c d"
      and abd: "ord a b d"
      and acd: "ord a c d"
      and abc_neq: "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d"
  shows "\<exists>f. ordering f ord {a,b,c,d}"
proof -
  let ?X = "{a,b,c,d}"
  let ?f = "\<lambda>n. if n = 0 then a else if n = 1 then b else if n = 2 then c else d"
  have card4: "card ?X = 4" using abc bcd abd abc_neq by simp
  have ordering1: "\<forall>n. (finite ?X \<longrightarrow> n < card ?X) \<longrightarrow> ?f n \<in> ?X" by simp
  have ordering2: "\<forall>x\<in>?X. \<exists>n. (finite ?X \<longrightarrow> n < card ?X) \<and> ?f n = x"
    by (metis card4 One_nat_def Suc_1 Suc_lessI empty_iff insertE numeral_3_eq_3 numeral_eq_iff
              numeral_eq_one_iff rel_simps(51) semiring_norm(85) semiring_norm(86) semiring_norm(87)
              semiring_norm(89) zero_neq_numeral)
  have ordering3: "(\<forall>n n' n''. (finite ?X \<longrightarrow> n'' < card ?X) \<and> n < n' \<and> n' < n''
                                 \<longrightarrow> ord (?f n) (?f n') (?f n''))"
    using card4 abc bcd abd acd card_0_eq card_insert_if finite.emptyI finite_insert less_antisym
          less_one less_trans_Suc not_less_eq not_one_less_zero numeral_2_eq_2 by auto
  have "ordering ?f ord ?X" using ordering1 ordering2 ordering3 ordering_def by blast
  thus ?thesis by auto
qed

lemma overlap_ordering_alt1:
  assumes abc: "ord a b c"
      and bcd: "ord b c d"
      and abc_bcd_abd: "\<forall> a b c d. ord a b c \<and> ord b c d \<longrightarrow> ord a b d"
      and abc_bcd_acd: "\<forall> a b c d. ord a b c \<and> ord b c d \<longrightarrow> ord a c d"
      and ord_distinct: "\<forall>a b c. (ord a b c \<longrightarrow> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)"
  shows "\<exists>f. ordering f ord {a,b,c,d}"
by (metis (full_types) assms overlap_ordering)

lemma overlap_ordering_alt2:
  assumes abc: "ord a b c"
      and bcd: "ord b c d"
      and abd: "ord a b d"
      and acd: "ord a c d"
      and ord_distinct: "\<forall>a b c. (ord a b c \<longrightarrow> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)"
  shows "\<exists>f. ordering f ord {a,b,c,d}"
by (metis assms overlap_ordering)

lemma overlap_ordering_alt:
  assumes abc: "ord a b c"
      and bcd: "ord b c d"
      and abc_bcd_abd: "\<forall> a b c d. ord a b c \<and> ord b c d \<longrightarrow> ord a b d"
      and abc_bcd_acd: "\<forall> a b c d. ord a b c \<and> ord b c d \<longrightarrow> ord a c d"
      and abc_neq: "a \<noteq> b \<and> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<and> c \<noteq> d"
  shows "\<exists>f. ordering f ord {a,b,c,d}"
by (meson assms overlap_ordering)

text \<open>
  The lemmas below are easy to prove for \<open>X = {}\<close>, and if I included that case then I would have
  to write a conditional definition in place of \<open>{0..|X| - 1}\<close>.
\<close>

lemma finite_ordering_img: "\<lbrakk>X \<noteq> {}; finite X; ordering f ord X\<rbrakk> \<Longrightarrow> f ` {0..card X - 1} = X"
by (force simp add: ordering_def image_def)

lemma inf_ordering_img: "\<lbrakk>infinite X; ordering f ord X\<rbrakk> \<Longrightarrow> f ` {0..} = X"
by (auto simp add: ordering_def image_def)

lemma finite_ordering_inv_img: "\<lbrakk>X \<noteq> {}; finite X; ordering f ord X\<rbrakk> \<Longrightarrow> f -` X = {0..card X - 1}"
apply (auto simp add: ordering_def)
oops

lemma inf_ordering_inv_img: "\<lbrakk>infinite X; ordering f ord X\<rbrakk> \<Longrightarrow> f -` X = {0..}"
by (auto simp add: ordering_def image_def)

lemma inf_ordering_img_inv_img: "\<lbrakk>infinite X; ordering f ord X\<rbrakk> \<Longrightarrow> f ` f -` X = X"
using inf_ordering_img by auto

lemma finite_ordering_inj_on: "\<lbrakk>finite X; ordering f ord X\<rbrakk> \<Longrightarrow> inj_on f {0..card X - 1}"
by (metis finite_ordering_img Suc_diff_1 atLeastAtMost_iff card_atLeastAtMost card_eq_0_iff
          diff_0_eq_0 diff_zero eq_card_imp_inj_on gr0I inj_onI le_0_eq)

lemma finite_ordering_bij:
  assumes orderingX: "ordering f ord X"
      and finiteX: "finite X"
      and non_empty: "X \<noteq> {}"
  shows "bij_betw f {0..card X - 1} X"
proof -
  have f_image: "f ` {0..card X - 1} = X" by (metis orderingX finiteX finite_ordering_img non_empty)
  thus ?thesis by (metis inj_on_imp_bij_betw orderingX finiteX finite_ordering_inj_on)  
qed

(* I think there might be a way of proving this without ord_distinct (?) *)
lemma inf_ordering_inj':
  assumes infX: "infinite X"
      and f_ord: "ordering f ord X"
      and ord_distinct: "\<forall>a b c. (ord a b c \<longrightarrow> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)"
      and f_eq: "f m = f n"
  shows "m = n"
(* If m \<noteq> n and f m = f n then it wouldn't be an ordering, and this part:
   \<forall>n n' n''. n < n' \<and> n' < n'' \<longrightarrow> [[f n f n' f n'']]
   would fail because two of f n f n' f n'' would be equal, and that violates ord_distinct. *)
proof (rule ccontr)
  assume m_not_n: "m \<noteq> n"
  have betw_3n: "\<forall>n n' n''. n < n' \<and> n' < n'' \<longrightarrow> ord (f n) (f n') (f n'')"
       using f_ord by (simp add: ordering_def infX)
  thus False
  proof cases
    assume m_less_n: "m < n"
    then obtain k where "n < k" by auto
    then have "ord (f m) (f n) (f k)" using m_less_n betw_3n by simp
    then have "f m \<noteq> f n" using ord_distinct by simp
    thus ?thesis using f_eq by simp
  next
    assume "\<not> m < n"
    then have n_less_m: "n < m" using m_not_n by simp
    then obtain k where "m < k" by auto
    then have "ord (f n) (f m) (f k)" using n_less_m betw_3n by simp
    then have "f n \<noteq> f m" using ord_distinct by simp
    thus ?thesis using f_eq by simp
  qed
qed

(* f is actually injective when X is infinite. *)
lemma inf_ordering_inj:
  assumes "infinite X"
      and "ordering f ord X"
      and "\<forall>a b c. (ord a b c \<longrightarrow> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)"
  shows "inj f"
using inf_ordering_inj' assms by (metis injI) 

text \<open>
  The finite case is a little more difficult as I can't just choose some other natural number
  to form the third part of the betweenness relation and the initial simplification isn't as nice.
  Note that I cannot prove \<open>inj f\<close> (over the whole type that \<open>f\<close> is defined on, i.e. natural numbers),
  because I need to capture the \<open>m\<close> and \<open>n\<close> that obey specific requirements for the finite case.
  In order to prove \<open>inj f\<close>, I would have to extend the definition for ordering to include \<open>m\<close> and \<open>n\<close>
  beyond \<open>card X\<close>, such that it is still injective. That would probably not be very useful.
\<close>

lemma finite_ordering_inj:
  assumes finiteX: "finite X"
      and f_ord: "ordering f ord X"
      and ord_distinct: "\<forall>a b c. (ord a b c \<longrightarrow> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)"
      and m_less_card: "m < card X"
      and n_less_card: "n < card X"
      and f_eq: "f m = f n"
  shows "m = n"
proof (rule ccontr)
  assume m_not_n: "m \<noteq> n"
  have surj_f: "\<forall>x\<in>X. \<exists>n<card X. f n = x"
               using f_ord by (simp add: ordering_def finiteX)
  have betw_3n: "\<forall>n n' n''. n'' < card X \<and> n < n' \<and> n' < n'' \<longrightarrow> ord (f n) (f n') (f n'')"
                using f_ord by (simp add: ordering_def)
  show False
  proof cases
    assume card_le2: "card X \<le> 2"
    have card0: "card X = 0 \<longrightarrow> False" using m_less_card by simp
    have card1: "card X = 1 \<longrightarrow> False" using m_less_card n_less_card m_not_n by simp
    have card2: "card X = 2 \<longrightarrow> False"
    proof (rule impI)
      assume card_is_2: "card X = 2"
      then have mn01: "m = 0 \<and> n = 1 \<or> n = 0 \<and> m = 1" using m_less_card n_less_card m_not_n by auto
      then have "f m \<noteq> f n" using card_is_2 surj_f One_nat_def card_eq_SucD insertCI
                                  less_2_cases numeral_2_eq_2 by (metis (no_types, lifting))
      thus False using f_eq by simp
    qed
    show False using card0 card1 card2 card_le2 by simp
  next
    assume "\<not> card X \<le> 2"
    then have card_ge3: "card X \<ge> 3" by simp
    thus False
    proof cases
      assume m_less_n: "m < n"
      then obtain k where k_pos: "k < m \<or> (m < k \<and> k < n) \<or> (n < k \<and> k < card X)"
          using is_free_nat m_less_n n_less_card card_ge3 by blast
      have k1: "k < m \<longrightarrow>ord (f k) (f m) (f n)" using m_less_n n_less_card betw_3n by simp
      have k2: "m < k \<and> k < n \<longrightarrow> ord (f m) (f k) (f n)" using m_less_n n_less_card betw_3n by simp
      have k3: "n < k \<and> k < card X \<longrightarrow> ord (f m) (f n) (f k)" using m_less_n betw_3n by simp
      have "f m \<noteq> f n" using k1 k2 k3 k_pos ord_distinct by auto
      thus False using f_eq by simp
    next (* Should work on making these two cases into one; this is quite boilerplatery. *)
      assume "\<not> m < n"
      then have n_less_m: "n < m" using m_not_n by simp
      then obtain k where k_pos: "k < n \<or> (n < k \<and> k < m) \<or> (m < k \<and> k < card X)"
          using is_free_nat n_less_m m_less_card card_ge3 by blast
      have k1: "k < n \<longrightarrow>ord (f k) (f n) (f m)" using n_less_m m_less_card betw_3n by simp
      have k2: "n < k \<and> k < m \<longrightarrow> ord (f n) (f k) (f m)" using n_less_m m_less_card betw_3n by simp
      have k3: "m < k \<and> k < card X \<longrightarrow> ord (f n) (f m) (f k)" using n_less_m betw_3n by simp
      have "f n \<noteq> f m" using k1 k2 k3 k_pos ord_distinct by auto
      thus False using f_eq by simp
    qed
  qed
qed

lemma ordering_inj:
  assumes "ordering f ord X"
      and "\<forall>a b c. (ord a b c \<longrightarrow> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)"
      and "finite X \<longrightarrow> m < card X"
      and "finite X \<longrightarrow> n < card X"
      and "f m = f n"
  shows "m = n"
  using inf_ordering_inj' finite_ordering_inj assms by blast

lemma ordering_sym:
  assumes ord_sym: "\<And>a b c. ord a b c \<Longrightarrow> ord c b a"
      and "finite X"
      and "ordering f ord X"
  shows "ordering (\<lambda>n. f (card X - 1 - n)) ord X"
unfolding ordering_def using assms(2)
  apply auto
  apply (metis ordering_def assms(3) card_0_eq card_gt_0_iff diff_Suc_less gr_implies_not0)
proof -
  fix x
  assume "finite X"
  assume "x \<in> X"
  obtain n where "finite X \<longrightarrow> n < card X" and "f n = x"
    by (metis ordering_def \<open>x \<in> X\<close> assms(3))
  have "f (card X - ((card X - 1 - n) + 1)) = x"
    by (simp add: Suc_leI \<open>f n = x\<close> \<open>finite X \<longrightarrow> n < card X\<close> assms(2))
  thus "\<exists>n<card X. f (card X - Suc n) = x"
    by (metis \<open>x \<in> X\<close> add.commute assms(2) card_Diff_singleton card_Suc_Diff1 diff_less_Suc plus_1_eq_Suc)
next
  fix n n' n''
  assume "finite X"
  assume "n'' < card X" "n < n'" "n' < n''"
  have "ord (f (card X - Suc n'')) (f (card X - Suc n')) (f (card X - Suc n))"
    using assms(3) unfolding ordering_def
    using \<open>n < n'\<close> \<open>n' < n''\<close> \<open>n'' < card X\<close> diff_less_mono2 by auto 
  thus " ord (f (card X - Suc n)) (f (card X - Suc n')) (f (card X - Suc n''))"
    using ord_sym by blast
qed

lemma  zero_into_ordering:
  assumes "ordering f betw X"
  and "X \<noteq> {}"
  shows "(f 0) \<in> X"
    using ordering_def
    by (metis assms card_eq_0_iff gr_implies_not0 linorder_neqE_nat)


section "Locally ordered chains"
text \<open>Definitions for Schutz-like chains, with local order only.\<close>

definition ordering2 :: "(nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "ordering2 f ord X \<equiv> (\<forall>n. (finite X \<longrightarrow> n < card X) \<longrightarrow> f n \<in> X)
                     \<and> (\<forall>x\<in>X. (\<exists>n. (finite X \<longrightarrow> n < card X) \<and> f n = x))
                     \<and> (\<forall>n n' n''. (finite X \<longrightarrow> n'' < card X) \<and> Suc n = n' \<and> Suc n' = n''
                                   \<longrightarrow> ord (f n) (f n') (f n''))"


text \<open>Analogue to \<open>ordering_ord_ijk\<close>, which is quicker to use in sledgehammer than the definition.\<close>

lemma ordering2_ord_ijk:
  assumes "ordering2 f ord X"
      and "Suc i = j \<and> Suc j = k \<and> (finite X \<longrightarrow> k < card X)"
  shows "ord (f i) (f j) (f k)"
  by (metis ordering2_def assms)


end