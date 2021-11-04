section \<open>Set Cover\<close>

theory Approx_SC_Hoare
imports
  "HOL-Hoare.Hoare_Logic"
  Complex_Main (* "HOL-Analysis.Harmonic_Numbers" *)
begin

text \<open>This is a formalization of the set cover algorithm and proof
in the book by Kleinberg and Tardos \cite{KleinbergT06}.\<close>

definition harm :: "nat \<Rightarrow> 'a :: real_normed_field" where
  "harm n = (\<Sum>k=1..n. inverse (of_nat k))"
(* For simplicity defined locally instead of importing HOL-Analysis.Harmonic_Numbers.
   Only the definition, no theorems are needed.
*)

locale Set_Cover = (* Set Cover *)
  fixes w :: "nat \<Rightarrow> real"
    and m :: nat
    and S :: "nat \<Rightarrow> 'a set"
  assumes S_finite: "\<forall>i \<in> {1..m}. finite (S i)"
      and w_nonneg: "\<forall>i. 0 \<le> w i"
begin

definition U :: "'a set" where
  "U = (\<Union>i \<in> {1..m}. S i)"

lemma S_subset: "\<forall>i \<in> {1..m}. S i \<subseteq> U"
  using U_def by blast

lemma U_finite: "finite U"
  unfolding U_def using S_finite by blast

lemma empty_cover: "m = 0 \<Longrightarrow> U = {}"
  using U_def by simp

definition sc :: "nat set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "sc C X \<longleftrightarrow> C \<subseteq> {1..m} \<and> (\<Union>i \<in> C. S i) = X"

definition cost :: "'a set \<Rightarrow> nat \<Rightarrow> real" where
  "cost R i = w i / card (S i \<inter> R)"

lemma cost_nonneg: "0 \<le> cost R i"
  using w_nonneg by (simp add: cost_def)

text \<open>\<open>cost R i = 0\<close> if \<open>card (S i \<inter> R) = 0\<close>! Needs to be accounted for separately in \<open>min_arg\<close>.\<close>
fun min_arg :: "'a set \<Rightarrow> nat \<Rightarrow> nat" where
  "min_arg R 0 = 1"
| "min_arg R (Suc x) =
   (let j = min_arg R x
    in if S j \<inter> R = {} \<or> (S (Suc x) \<inter> R \<noteq> {} \<and> cost R (Suc x) < cost R j) then (Suc x) else j)"

lemma min_in_range: "k > 0 \<Longrightarrow> min_arg R k \<in> {1..k}"
  by (induction k) (force simp: Let_def)+

lemma min_empty: "S (min_arg R k) \<inter> R = {} \<Longrightarrow> \<forall>i \<in> {1..k}. S i \<inter> R = {}"
proof (induction k)
  case (Suc k)
  from Suc.prems have prem: "S (min_arg R k) \<inter> R = {}" by (auto simp: Let_def split: if_splits)
  with Suc.IH have IH: "\<forall>i \<in> {1..k}. S i \<inter> R = {}" .
  show ?case proof fix i assume "i \<in> {1..Suc k}" show "S i \<inter> R = {}"
    proof (cases \<open>i = Suc k\<close>)
      case True with Suc.prems prem show ?thesis by simp
    next
      case False with IH \<open>i \<in> {1..Suc k}\<close> show ?thesis by simp
    qed
  qed
qed simp

lemma min_correct: "\<lbrakk> i \<in> {1..k}; S i \<inter> R \<noteq> {} \<rbrakk> \<Longrightarrow> cost R (min_arg R k) \<le> cost R i"
proof (induction k)
  case (Suc k)
  show ?case proof (cases \<open>i = Suc k\<close>)
    case True with Suc.prems show ?thesis by (auto simp: Let_def)
  next
    case False with Suc.prems Suc.IH have IH: "cost R (min_arg R k) \<le> cost R i" by simp
    from Suc.prems False min_empty[of R k] have "S (min_arg R k) \<inter> R \<noteq> {}" by force
    with IH show ?thesis by (auto simp: Let_def)
  qed
qed simp

text \<open>Correctness holds quite trivially for both m = 0 and m > 0
      (assuming a set cover can be found at all, otherwise algorithm would not terminate).\<close>
lemma set_cover_correct:
"VARS (R :: 'a set) (C :: nat set) (i :: nat)
  {True}
  R := U; C := {};
  WHILE R \<noteq> {} INV {R \<subseteq> U \<and> sc C (U - R)} DO
  i := min_arg R m;
  R := R - S i;
  C := C \<union> {i}
  OD
  {sc C U}"
proof (vcg, goal_cases)
  case 2 show ?case proof (cases m)
    case 0
    from empty_cover[OF this] 2 show ?thesis by (auto simp: sc_def)
  next
    case Suc then have "m > 0" by simp
    from min_in_range[OF this] 2 show ?thesis using S_subset by (auto simp: sc_def)
  qed
qed (auto simp: sc_def)

definition c_exists :: "nat set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "c_exists C R = (\<exists>c. sum w C = sum c (U - R) \<and> (\<forall>i. 0 \<le> c i)
                \<and> (\<forall>k \<in> {1..m}. sum c (S k \<inter> (U - R))
                   \<le> (\<Sum>j = card (S k \<inter> R) + 1..card (S k). inverse j) * w k))"

definition inv :: "nat set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "inv C R \<longleftrightarrow> sc C (U - R) \<and> R \<subseteq> U \<and> c_exists C R"

lemma invI:
  assumes "sc C (U - R)" "R \<subseteq> U"
          "\<exists>c. sum w C = sum c (U - R) \<and> (\<forall>i. 0 \<le> c i)
        \<and> (\<forall>k \<in> {1..m}. sum c (S k \<inter> (U - R))
                      \<le> (\<Sum>j = card (S k \<inter> R) + 1..card (S k). inverse j) * w k)"
    shows "inv C R" using assms by (auto simp: inv_def c_exists_def)

lemma invD:
  assumes "inv C R"
  shows "sc C (U - R)" "R \<subseteq> U"
        "\<exists>c. sum w C = sum c (U - R) \<and> (\<forall>i. 0 \<le> c i)
      \<and> (\<forall>k \<in> {1..m}. sum c (S k \<inter> (U - R))
                    \<le> (\<Sum>j = card (S k \<inter> R) + 1..card (S k). inverse j) * w k)"
  using assms by (auto simp: inv_def c_exists_def)

lemma inv_init: "inv {} U"
proof (rule invI, goal_cases)
  case 3
  let ?c = "(\<lambda>_. 0) :: 'a \<Rightarrow> real"
  have "sum w {} = sum ?c (U - U)" by simp
  moreover {
    have "\<forall>k \<in> {1..m}. 0 \<le> (\<Sum>j = card (S k \<inter> U) + 1..card (S k). inverse j) * w k"
      by (simp add: sum_nonneg w_nonneg)
    then have "(\<forall>k\<in>{1..m}. sum ?c (S k \<inter> (U - U))
             \<le> (\<Sum>j = card (S k \<inter> U) + 1..card (S k). inverse j) * w k)" by simp
  }
  ultimately show ?case by blast
qed (simp_all add: sc_def)

lemma inv_step:
  assumes "inv C R" "R \<noteq> {}"
  defines [simp]: "i \<equiv> min_arg R m"
  shows "inv (C \<union> {i}) (R - (S i))"
proof (cases m)
  case 0
  from empty_cover[OF this] invD(2)[OF assms(1)] have "R = {}" by blast
  then show ?thesis using assms(2) by simp
next
  case Suc then have "0 < m" by simp
  note hyp = invD[OF assms(1)]
  show ?thesis proof (rule invI, goal_cases)
      \<comment> \<open>Correctness\<close>
    case 1 have "i \<in> {1..m}" using min_in_range[OF \<open>0 < m\<close>] by simp
    with hyp(1) S_subset show ?case by (auto simp: sc_def)
  next
    case 2 from hyp(2) show ?case by auto
  next
    case 3
      \<comment> \<open>Set Cover grows\<close>
    have "\<exists>i \<in> {1..m}. S i \<inter> R \<noteq> {}"
      using assms(2) U_def hyp(2) by blast
    then have "S i \<inter> R \<noteq> {}" using min_empty by auto
    then have "0 < card (S i \<inter> R)"
      using S_finite min_in_range[OF \<open>0 < m\<close>] by auto

      \<comment> \<open>Proving properties of cost function\<close>
    from hyp(3) obtain c where "sum w C = sum c (U - R)" "\<forall>i. 0 \<le> c i" and
      SUM: "\<forall>k\<in>{1..m}. sum c (S k \<inter> (U - R))
        \<le> (\<Sum>j = card (S k \<inter> R) + 1..card (S k). inverse j) * w k" by blast
    let ?c = "(\<lambda>x. if x \<in> S i \<inter> R then cost R i else c x)"

      \<comment> \<open>Proof of Lemma 11.9\<close>
    have "finite (U - R)" "finite (S i \<inter> R)" "(U - R) \<inter> (S i \<inter> R) = {}"
      using U_finite S_finite min_in_range[OF \<open>0 < m\<close>] by auto
    then have "sum ?c (U - R \<union> (S i \<inter> R)) = sum ?c (U - R) + sum ?c (S i \<inter> R)"
      by (rule sum.union_disjoint)
    moreover have U_split: "U - (R - S i) = U - R \<union> (S i \<inter> R)" using hyp(2) by blast
    moreover {
      have "sum ?c (S i \<inter> R) = card (S i \<inter> R) * cost R i" by simp
      also have "... = w i" unfolding cost_def using \<open>0 < card (S i \<inter> R)\<close> by simp
      finally have "sum ?c (S i \<inter> R) = w i" .
    }
    ultimately have "sum ?c (U - (R - S i)) = sum ?c (U - R) + w i" by simp
    moreover {
      have "C \<inter> {i} = {}" using hyp(1) \<open>S i \<inter> R \<noteq> {}\<close> by (auto simp: sc_def)
      from sum.union_disjoint[OF _ _ this] have "sum w (C \<union> {i}) = sum w C + w i"
        using hyp(1) by (auto simp: sc_def intro: finite_subset)
    }
    ultimately have 1: "sum w (C \<union> {i}) = sum ?c (U - (R - S i))" \<comment> \<open>Lemma 11.9\<close>
      using \<open>sum w C = sum c (U - R)\<close> by simp

    have 2: "\<forall>i. 0 \<le> ?c i" using \<open>\<forall>i. 0 \<le> c i\<close> cost_nonneg by simp

      \<comment> \<open>Proof of Lemma 11.10\<close>
    have 3: "\<forall>k\<in>{1..m}. sum ?c (S k \<inter> (U - (R - S i)))
          \<le> (\<Sum>j = card (S k \<inter> (R - S i)) + 1..card (S k). inverse j) * w k"
    proof
      fix k assume "k \<in> {1..m}"
      let ?rem = "S k \<inter> R" \<comment> \<open>Remaining elements to be covered\<close>
      let ?add = "S k \<inter> S i \<inter> R" \<comment> \<open>Elements that will be covered in this step\<close>
      let ?cov = "S k \<inter> (U - R)" \<comment> \<open>Covered elements\<close>

      \<comment> \<open>Transforming left and right sides\<close>
      have "sum ?c (S k \<inter> (U - (R - S i))) = sum ?c (S k \<inter> (U - R \<union> (S i \<inter> R)))"
        unfolding U_split ..
      also have "... = sum ?c (?cov \<union> ?add)"
        by (simp add: Int_Un_distrib Int_assoc)
      also have "... = sum ?c ?cov + sum ?c ?add"
        by (rule sum.union_disjoint) (insert S_finite \<open>k \<in> _\<close>, auto)
      finally have lhs:
        "sum ?c (S k \<inter> (U - (R - S i))) = sum ?c ?cov + sum ?c ?add" .
      have "S k \<inter> (R - S i) = ?rem - ?add" by blast
      then have "card (S k \<inter> (R - S i)) = card (?rem - ?add)" by simp
      also have "... = card ?rem - card ?add"
        using S_finite \<open>k \<in> _\<close> by (auto intro: card_Diff_subset)
      finally have rhs:
        "card (S k \<inter> (R - S i)) + 1 = card ?rem - card ?add + 1" by simp
      
      \<comment> \<open>The apparent complexity of the remaining proof is deceiving. Much of this is just about
          convincing Isabelle that these sum transformations are allowed.\<close>
      have "sum ?c ?add = card ?add * cost R i" by simp
      also have "... \<le> card ?add * cost R k"
        proof (cases "?rem = {}")
          case True
          then have "card ?add = 0" by (auto simp: card_eq_0_iff)
          then show ?thesis by simp
        next
          case False
          from min_correct[OF \<open>k \<in> _\<close> this] have "cost R i \<le> cost R k" by simp
          then show ?thesis by (simp add: mult_left_mono)
        qed
      also have "... = card ?add * inverse (card ?rem) * w k"
        by (simp add: cost_def divide_inverse_commute)
      also have "... = (\<Sum>j \<in> {card ?rem - card ?add + 1 .. card ?rem}. inverse (card ?rem)) * w k"
        proof -
          have "card ?add \<le> card ?rem"
            using S_finite \<open>k \<in> _\<close> by (blast intro: card_mono)
          then show ?thesis by (simp add: sum_distrib_left)
        qed
      also have "... \<le> (\<Sum>j \<in> {card ?rem - card ?add + 1 .. card ?rem}. inverse j) * w k"
        proof -
          have "\<forall>j \<in> {card ?rem - card ?add + 1 .. card ?rem}. inverse (card ?rem) \<le> inverse j"
            by force
          then have "(\<Sum>j \<in> {card ?rem - card ?add + 1 .. card ?rem}. inverse (card ?rem))
                   \<le> (\<Sum>j \<in> {card ?rem - card ?add + 1 .. card ?rem}. inverse j)"
            by (blast intro: sum_mono)
          with w_nonneg show ?thesis by (blast intro: mult_right_mono)
        qed
      finally have "sum ?c ?add
                 \<le> (\<Sum>j \<in> {card ?rem - card ?add + 1 .. card ?rem}. inverse j) * w k" .
      moreover from SUM have "sum ?c ?cov 
                           \<le> (\<Sum>j \<in> {card ?rem + 1 .. card (S k)}. inverse j) * w k"
        using \<open>k \<in> {1..m}\<close> by simp
      ultimately have "sum ?c (S k \<inter> (U - (R - S i)))
                    \<le> ((\<Sum>j \<in> {card ?rem - card ?add + 1 .. card ?rem}. inverse j) +
                        (\<Sum>j \<in> {card ?rem + 1 .. card (S k)}. inverse j)) * w k"
        unfolding lhs by argo
      also have "... = (\<Sum>j \<in> {card ?rem - card ?add + 1 .. card (S k)}. inverse j) * w k"
        proof -
          have sum_split: "b \<in> {a .. c} \<Longrightarrow> sum f {a .. c} = sum f {a .. b} + sum f {Suc b .. c}"
            for f :: "nat \<Rightarrow> real" and a b c :: nat
          proof -
            assume "b \<in> {a .. c}"
            then have "{a .. b} \<union> {Suc b .. c} = {a .. c}" by force
            moreover have "{a .. b} \<inter> {Suc b .. c} = {}"
              using \<open>b \<in> {a .. c}\<close> by auto
            ultimately show ?thesis by (metis finite_atLeastAtMost sum.union_disjoint)
          qed

          have "(\<Sum>j \<in> {card ?rem - card ?add + 1 .. card (S k)}. inverse j)
              = (\<Sum>j \<in> {card ?rem - card ?add + 1 .. card ?rem}. inverse j)
              + (\<Sum>j \<in> {card ?rem + 1 .. card (S k)}. inverse j)"
            proof (cases \<open>?add = {}\<close>)
              case False
              then have "0 < card ?add" "0 < card ?rem"
                using S_finite \<open>k \<in> _\<close> by fastforce+
              then have "Suc (card ?rem - card ?add) \<le> card ?rem" by simp
              moreover have "card ?rem \<le> card (S k)"
                using S_finite \<open>k \<in> _\<close> by (simp add: card_mono)
              ultimately show ?thesis by (auto intro: sum_split)
            qed simp
          then show ?thesis by algebra
        qed
      finally show "sum ?c (S k \<inter> (U - (R - S i)))
                 \<le> (\<Sum>j \<in> {card (S k \<inter> (R - S i)) + 1 .. card (S k)}. inverse j) * w k"
        unfolding rhs .
    qed

    from 1 2 3 show ?case by blast
  qed
qed

lemma cover_sum:
  fixes c :: "'a \<Rightarrow> real"
  assumes "sc C V" "\<forall>i. 0 \<le> c i"
  shows "sum c V \<le> (\<Sum>i \<in> C. sum c (S i))"
proof -
  from assms(1) have "finite C" by (auto simp: sc_def finite_subset)
  then show ?thesis using assms(1)
  proof (induction C arbitrary: V rule: finite_induct)
    case (insert i C)
    have V_split: "(\<Union> (S ` insert i C)) = (\<Union> (S ` C)) \<union> S i" by auto
    have finite: "finite (\<Union> (S ` C))" "finite (S i)"
      using insert S_finite by (auto simp: sc_def)

    have "sum c (S i) - sum c (\<Union> (S ` C) \<inter> S i) \<le> sum c (S i)"
      using assms(2) by (simp add: sum_nonneg)
    then have "sum c (\<Union> (S ` insert i C)) \<le> sum c (\<Union> (S ` C)) + sum c (S i)"
      unfolding V_split using sum_Un[OF finite, of c] by linarith
    moreover have "(\<Sum>i\<in>insert i C. sum c (S i)) = (\<Sum>i \<in> C. sum c (S i)) + sum c (S i)"
      by (simp add: insert.hyps)
    ultimately show ?case using insert by (fastforce simp: sc_def)
  qed (simp add: sc_def)
qed

abbreviation H :: "nat \<Rightarrow> real" where "H \<equiv> harm"

definition d_star :: nat ("d\<^sup>*") where "d\<^sup>* \<equiv> Max (card ` (S ` {1..m}))"

lemma set_cover_bound:
  assumes "inv C {}" "sc C' U"
  shows "sum w C \<le> H d\<^sup>* * sum w C'"
proof -
  from invD(3)[OF assms(1)] obtain c where
    "sum w C = sum c U" "\<forall>i. 0 \<le> c i" and H_bound:
    "\<forall>k \<in> {1..m}. sum c (S k) \<le> H (card (S k)) * w k" \<comment> \<open>Lemma 11.10\<close>
    by (auto simp: harm_def Int_absorb2 S_subset)

  have "\<forall>k \<in> {1..m}. card (S k) \<le> d\<^sup>*" by (auto simp: d_star_def)
  then have "\<forall>k \<in> {1..m}. H (card (S k)) \<le> H d\<^sup>*" by (auto simp: harm_def intro!: sum_mono2)
  with H_bound have "\<forall>k \<in> {1..m}. sum c (S k) \<le> H d\<^sup>* * w k"
    by (metis atLeastAtMost_iff atLeastatMost_empty_iff empty_iff mult_right_mono w_nonneg)
  moreover have "C' \<subseteq> {1..m}" using assms(2) by (simp add: sc_def)
  ultimately have "\<forall>i \<in> C'. sum c (S i) \<le> H d\<^sup>* * w i" by blast
  then have "(\<Sum>i \<in> C'. sum c (S i)) \<le> H d\<^sup>* * sum w C'"
    by (auto simp: sum_distrib_left intro: sum_mono)

  have "sum w C = sum c U" by fact \<comment> \<open>Lemma 11.9\<close>
  also have "... \<le> (\<Sum>i \<in> C'. sum c (S i))" by (rule cover_sum[OF assms(2)]) fact
  also have "... \<le> H d\<^sup>* * sum w C'" by fact
  finally show ?thesis .
qed

theorem set_cover_approx:
"VARS (R :: 'a set) (C :: nat set) (i :: nat)
  {True}
  R := U; C := {};
  WHILE R \<noteq> {} INV {inv C R} DO
  i := min_arg R m;
  R := R - S i;
  C := C \<union> {i}
  OD
  {sc C U \<and> (\<forall>C'. sc C' U \<longrightarrow> sum w C \<le> H d\<^sup>* * sum w C')}"
proof (vcg, goal_cases)
  case 1 show ?case by (rule inv_init)
next
  case 2 thus ?case using inv_step ..
next
  case (3 R C i)
  then have "sc C U" unfolding inv_def by auto
  with 3 show ?case by (auto intro: set_cover_bound)
qed

end (* Set Cover *)

end (* Theory *)
