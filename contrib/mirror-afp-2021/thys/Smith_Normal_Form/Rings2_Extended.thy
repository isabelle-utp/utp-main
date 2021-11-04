(*
    Author:      Jose Divasón
    Email:       jose.divason@unirioja.es
*)

section \<open>Some theorems about rings and ideals\<close>

theory Rings2_Extended
  imports
    Echelon_Form.Rings2
    "HOL-Types_To_Sets.Types_To_Sets"
begin

subsection \<open>Missing properties on ideals\<close>

lemma ideal_generated_subset2:
  assumes  "\<forall>b\<in>B. b \<in> ideal_generated A"
  shows "ideal_generated B \<subseteq> ideal_generated A"
  by (metis (mono_tags, lifting) InterE assms ideal_generated_def
ideal_ideal_generated mem_Collect_eq subsetI)

context comm_ring_1
begin

lemma ideal_explicit: "ideal_generated S
      = {y. \<exists>f U. finite U \<and> U \<subseteq> S \<and> (\<Sum>i\<in>U. f i * i) = y}"
  by (simp add: ideal_generated_eq_left_ideal left_ideal_explicit)
end

lemma ideal_generated_minus:
  assumes a: "a \<in> ideal_generated (S-{a})"
  shows "ideal_generated S = ideal_generated (S-{a})"
proof (cases "a \<in> S")
  case True note a_in_S = True
  show ?thesis
  proof
    show "ideal_generated S \<subseteq> ideal_generated (S - {a})"
    proof (rule ideal_generated_subset2, auto)
      fix b assume b: "b \<in> S" show "b \<in> ideal_generated (S - {a})"
      proof (cases "b = a")
        case True
        then show ?thesis using a by auto
      next
        case False
        then show ?thesis using b
          by (simp add: ideal_generated_in)
      qed
    qed
    show "ideal_generated (S - {a}) \<subseteq> ideal_generated S"
      by (rule ideal_generated_subset, auto)
  qed
next
  case False
  then show ?thesis by simp
qed

lemma ideal_generated_dvd_eq:
  assumes a_dvd_b: "a dvd b"
  and a: "a \<in> S"
  and a_not_b: "a \<noteq> b"
  shows "ideal_generated S = ideal_generated (S - {b})"
proof
  show "ideal_generated S \<subseteq> ideal_generated (S - {b})"
  proof (rule ideal_generated_subset2, auto)
    fix x assume x: "x \<in> S"
    show "x \<in> ideal_generated (S - {b})"
    proof (cases "x = b")
      case True
      obtain k where b_ak: "b = a * k" using a_dvd_b unfolding dvd_def by blast
      let ?f = "\<lambda>c. k"
      have "(\<Sum>i\<in>{a}. i * ?f i) = x" using True b_ak by auto
      moreover have "{a} \<subseteq> S - {b}" using a_not_b a by auto
      moreover have "finite {a}" by auto
      ultimately show ?thesis
        unfolding ideal_def
        by (metis True b_ak ideal_def ideal_generated_in ideal_ideal_generated insert_subset right_ideal_def)
    next
      case False
      then show ?thesis by (simp add: ideal_generated_in x)
    qed
  qed
  show "ideal_generated (S - {b}) \<subseteq> ideal_generated S" by (rule ideal_generated_subset, auto)
qed

lemma ideal_generated_dvd_eq_diff_set:
  assumes i_in_I: "i\<in>I" and i_in_J: "i \<notin> J" and i_dvd_j: "\<forall>j\<in>J. i dvd j"
  and f: "finite J"
  shows "ideal_generated I = ideal_generated (I - J)"
  using f i_in_J i_dvd_j i_in_I
  proof (induct J arbitrary: I)
  case empty
    then show ?case by auto
  next
    case (insert x J)
    have "ideal_generated I = ideal_generated (I-{x})"
      by (rule ideal_generated_dvd_eq[of i], insert insert.prems , auto)
    also have "... = ideal_generated ((I-{x}) - J)"
      by (rule insert.hyps, insert insert.prems insert.hyps, auto)
    also have "... = ideal_generated (I - insert x J)"
      using Diff_insert2[of I x J] by auto
    finally show ?case .
  qed


context comm_ring_1
begin

lemma ideal_generated_singleton_subset:
  assumes d: "d \<in> ideal_generated S" and fin_S: "finite S"
  shows "ideal_generated {d} \<subseteq> ideal_generated S"
proof
  fix x assume x: "x \<in> ideal_generated {d}"
  obtain k where x_kd: "x = k*d " using x using obtain_sum_ideal_generated[OF x]
    by (metis finite.emptyI finite.insertI sum_singleton)
  show "x \<in> ideal_generated S"
    using d ideal_eq_right_ideal ideal_ideal_generated right_ideal_def mult_commute x_kd by auto
qed

lemma ideal_generated_singleton_dvd:
  assumes i: "ideal_generated S = ideal_generated {d}" and x: "x \<in> S"
  shows "d dvd x"
  by (metis i x finite.intros dvd_ideal_generated_singleton
      ideal_generated_in ideal_generated_singleton_subset)

lemma ideal_generated_UNIV_insert:
  assumes "ideal_generated S = UNIV"
  shows "ideal_generated (insert a S) = UNIV" using assms
  using local.ideal_generated_subset by blast

lemma ideal_generated_UNIV_union:
  assumes "ideal_generated S = UNIV"
  shows "ideal_generated (A \<union> S) = UNIV"
  using assms local.ideal_generated_subset
  by (metis UNIV_I Un_subset_iff equalityI subsetI)

lemma ideal_explicit2:
  assumes "finite S"
  shows "ideal_generated S = {y. \<exists>f. (\<Sum>i\<in>S. f i * i) = y}"
  by (smt Collect_cong assms ideal_explicit obtain_sum_ideal_generated mem_Collect_eq subsetI)

lemma ideal_generated_unit:
  assumes u: "u dvd 1"
  shows "ideal_generated {u} = UNIV"
proof -
  have "x \<in> ideal_generated {u}" for x
  proof -
    obtain inv_u where inv_u: "inv_u * u = 1" using u unfolding dvd_def
      using local.mult_ac(2) by blast
    have "x = x * inv_u * u" using inv_u by (simp add: local.mult_ac(1))
    also have "... \<in> {k * u |k. k \<in> UNIV}" by auto
    also have "... = ideal_generated {u}" unfolding ideal_generated_singleton by simp
    finally show ?thesis .
  qed
  thus ?thesis by auto
qed


lemma ideal_generated_dvd_subset:
  assumes x: "\<forall>x \<in> S. d dvd x" and S: "finite S"
  shows "ideal_generated S \<subseteq> ideal_generated {d}"
proof
  fix x assume "x\<in> ideal_generated S"
  from this obtain f where f: "(\<Sum>i\<in>S. f i * i) = x" using ideal_explicit2[OF S] by auto
  have "d dvd (\<Sum>i\<in>S. f i * i)" by (rule dvd_sum, insert x, auto)
  thus "x \<in> ideal_generated {d}"
    using f dvd_ideal_generated_singleton' ideal_generated_in singletonI by blast
qed


lemma ideal_generated_mult_unit:
  assumes f: "finite S" and u: "u dvd 1"
  shows "ideal_generated ((\<lambda>x. u*x)` S) = ideal_generated S"
  using f
proof (induct S)
  case empty
  then show ?case by auto
next
  case (insert x S)
  obtain inv_u where inv_u: "inv_u * u = 1" using u unfolding dvd_def
    using mult_ac by blast
  have f: "finite (insert (u*x) ((\<lambda>x. u*x)` S))" using insert.hyps by auto
  have f2: "finite (insert x S)" by (simp add: insert(1))
  have f3: "finite S" by (simp add: insert)
  have f4: "finite ((*) u ` S)" by (simp add: insert)
  have inj_ux: "inj_on (\<lambda>x. u*x) S" unfolding inj_on_def
    by (auto, metis inv_u local.mult_1_left local.semiring_normalization_rules(18))
  have "ideal_generated ((\<lambda>x. u*x)` (insert x S)) = ideal_generated (insert (u*x) ((\<lambda>x. u*x)` S))"
    by auto
  also have "... = {y. \<exists>f. (\<Sum>i\<in>insert (u*x) ((\<lambda>x. u*x)` S). f i * i) = y}"
    using ideal_explicit2[OF f] by auto
  also have "... = {y. \<exists>f. (\<Sum>i\<in>(insert x S). f i * i) = y}" (is "?L = ?R")
  proof -
    have "a \<in> ?L"  if a: "a \<in> ?R" for a
    proof -
      obtain f where sum_rw: "(\<Sum>i\<in>(insert x S). f i * i) = a" using a by auto
      define b where "b=(\<Sum>i\<in>S. f i * i)"
      have "b \<in> ideal_generated S" unfolding b_def ideal_explicit2[OF f3] by auto
      hence "b \<in> ideal_generated ((*) u ` S)" using insert.hyps(3) by auto
      from this obtain g where "(\<Sum>i\<in>((*) u ` S). g i * i) = b"
        unfolding ideal_explicit2[OF f4] by auto
      hence sum_rw2: "(\<Sum>i\<in>S. f i * i) = (\<Sum>i\<in>((*) u ` S). g i * i)" unfolding b_def by auto
      let ?g = "\<lambda>i. if i = u*x then f x * inv_u else g i"
       have sum_rw3: "sum ((\<lambda>i. g i * i) \<circ> (\<lambda>x. u*x)) S = sum ((\<lambda>i. ?g i * i) \<circ> (\<lambda>x. u*x)) S"
        by (rule sum.cong, auto, metis inv_u local.insert(2) local.mult_1_right
              local.mult_ac(2) local.semiring_normalization_rules(18))
      have sum_rw4: "(\<Sum>i\<in>(\<lambda>x. u*x)` S. g i * i) = sum ((\<lambda>i. g i * i) \<circ> (\<lambda>x. u*x)) S"
        by (rule sum.reindex[OF inj_ux])
      have "a = f x * x + (\<Sum>i\<in>S. f i * i)"
        using sum_rw local.insert(1) local.insert(2) by auto
      also have "... = f x * x + (\<Sum>i\<in>(\<lambda>x. u*x)` S. g i * i)" using sum_rw2 by auto
      also have "... = ?g (u * x) * (u * x) + (\<Sum>i\<in>(\<lambda>x. u*x)` S. g i * i)"
        using inv_u by (smt local.mult_1_right local.mult_ac(1))
      also have "... =  ?g (u * x) * (u * x) + sum ((\<lambda>i. g i * i) \<circ> (\<lambda>x. u*x)) S"
        using sum_rw4 by auto
      also have "... = ((\<lambda>i. ?g i * i) \<circ> (\<lambda>x. u*x)) x + sum ((\<lambda>i. g i * i) \<circ> (\<lambda>x. u*x)) S" by auto
      also have "... = ((\<lambda>i. ?g i * i) \<circ> (\<lambda>x. u*x)) x + sum ((\<lambda>i. ?g i * i) \<circ> (\<lambda>x. u*x)) S"
        using sum_rw3 by auto
      also have "... = sum ((\<lambda>i. ?g i * i) \<circ> (\<lambda>x. u*x)) (insert x S)"
        by (rule sum.insert[symmetric], auto simp add: insert)
      also have "... = (\<Sum>i\<in>insert (u * x) ((\<lambda>x. u*x)` S). ?g i * i)"
        by (smt abel_semigroup.commute f2 image_insert inv_u mult.abel_semigroup_axioms mult_1_right
            semiring_normalization_rules(18) sum.reindex_nontrivial)
      also have "... = (\<Sum>i\<in>(\<lambda>x. u*x)` (insert x S). ?g i * i)" by auto
      finally show ?thesis by auto
    qed
    moreover have "a \<in> ?R" if a: "a \<in> ?L" for a
    proof -
      obtain f where sum_rw: "(\<Sum>i\<in>(insert (u * x) ((*) u ` S)). f i * i) = a" using a by auto
      have ux_notin: "u*x \<notin> ((*) u ` S)"
        by (metis UNIV_I inj_on_image_mem_iff inj_on_inverseI inv_u local.insert(2) local.mult_1_left
            local.semiring_normalization_rules(18) subsetI)
      let ?f = "(\<lambda>x. f x * x)"
      have "sum ?f ((*) u ` S) \<in> ideal_generated ((*) u ` S)"
        unfolding ideal_explicit2[OF f4] by auto
      from this obtain g where sum_rw1: "sum (\<lambda>i. g i * i) S = sum ?f (((*) u ` S))"
        using insert.hyps(3) unfolding ideal_explicit2[OF f3] by blast
      let ?g = "(\<lambda>i. if i = x  then (f (u*x) *u) * x else g i * i)"
      let ?g' = "\<lambda>i. if i = x  then f (u*x) * u else g i"
      have sum_rw2: "sum (\<lambda>i. g i * i) S = sum ?g S" by (rule sum.cong, insert inj_ux ux_notin, auto)
      have "a = (\<Sum>i\<in>(insert (u * x) ((*) u ` S)). f i * i)" using sum_rw by simp
      also have "... = ?f (u*x) +  sum ?f (((*) u ` S))"
        by (rule sum.insert[OF f4], insert inj_ux) (metis UNIV_I inj_on_image_mem_iff inj_on_inverseI
            inv_u local.insert(2) local.mult_1_left local.semiring_normalization_rules(18) subsetI)
      also have "... = ?f (u*x) + sum (\<lambda>i. g i * i) S" unfolding sum_rw1 by auto
      also have "... = ?g x + sum ?g S" unfolding sum_rw2 using mult.assoc by auto
      also have "... = sum ?g (insert x S)" by (rule sum.insert[symmetric, OF f3 insert.hyps(2)])
      also have "... = sum (\<lambda>i. ?g' i * i) (insert x S)" by (rule sum.cong, auto)
      finally show ?thesis by fast
    qed
    ultimately show ?thesis by blast
  qed
  also have "... = ideal_generated (insert x S)" using ideal_explicit2[OF f2] by auto
  finally show ?case by auto
qed

corollary ideal_generated_mult_unit2:
  assumes u: "u dvd 1"
  shows "ideal_generated {u*a,u*b} = ideal_generated {a,b}"
proof -
  let ?S = "{a,b}"
  have "ideal_generated {u*a,u*b} = ideal_generated ((\<lambda>x. u*x)` {a,b})" by auto
  also have "... = ideal_generated {a,b}" by (rule ideal_generated_mult_unit[OF _ u], simp)
  finally show ?thesis .
qed

lemma ideal_generated_1[simp]: "ideal_generated {1} = UNIV"
  by (metis ideal_generated_unit dvd_ideal_generated_singleton order_refl)

lemma ideal_generated_pair: "ideal_generated {a,b} = {p*a+q*b | p q. True}"
proof -
  have i: "ideal_generated {a,b} = {y. \<exists>f. (\<Sum>i\<in>{a,b}. f i * i) = y}" using ideal_explicit2 by auto
  show ?thesis
  proof (cases "a=b")
    case True
    show ?thesis using True i
      by (auto, metis mult_ac(2) semiring_normalization_rules)
      (metis (no_types, hide_lams) add_minus_cancel mult_ac ring_distribs semiring_normalization_rules)
  next
    case False
    have 1: "\<exists>p q. (\<Sum>i\<in>{a, b}. f i * i) = p * a + q * b" for f
      by (rule exI[of _ "f a"], rule exI[of _ "f b"], rule sum_two_elements[OF False])
    moreover have "\<exists>f. (\<Sum>i\<in>{a, b}. f i * i) = p * a + q * b" for p q
      by (rule exI[of _ "\<lambda>i. if i=a then p else q"],
          unfold sum_two_elements[OF False], insert False, auto)
    ultimately show ?thesis using i by auto
  qed
qed

lemma ideal_generated_pair_exists_pq1:
  assumes i: "ideal_generated {a,b} = (UNIV::'a set)"
  shows "\<exists>p q. p*a + q*b = 1"
  using i unfolding ideal_generated_pair
  by (smt iso_tuple_UNIV_I mem_Collect_eq)

lemma ideal_generated_pair_UNIV:
  assumes sa_tb_u: "s*a+t*b = u" and u: "u dvd 1"
  shows "ideal_generated {a,b} = UNIV"
proof -
  have f: "finite {a,b}" by simp
  obtain inv_u where inv_u: "inv_u * u = 1" using u unfolding dvd_def
    by (metis mult.commute)
  have "x \<in> ideal_generated {a,b}" for x
  proof (cases "a = b")
    case True
    then show ?thesis
      by (metis UNIV_I dvd_def dvd_ideal_generated_singleton' ideal_generated_unit insert_absorb2
          mult.commute sa_tb_u semiring_normalization_rules(34) subsetI subset_antisym u)
  next
    case False note a_not_b = False
    let ?f = "\<lambda>y. if y = a then inv_u * x * s else inv_u * x * t"
    have "(\<Sum>i\<in>{a,b}. ?f i * i) = ?f a * a + ?f b * b" by (rule sum_two_elements[OF a_not_b])
    also have "... = x" using a_not_b sa_tb_u inv_u
      by (auto, metis mult_ac(1) mult_ac(2) ring_distribs(1) semiring_normalization_rules(12))
    finally show ?thesis unfolding ideal_explicit2[OF f] by auto
  qed
  thus ?thesis by auto
qed


lemma ideal_generated_pair_exists:
  assumes l: "(ideal_generated {a,b} = ideal_generated {d})"
  shows "(\<exists> p q. p*a+q*b = d)"
proof -
  have d: "d \<in> ideal_generated {d}" by (simp add: ideal_generated_in)
  hence "d \<in> ideal_generated {a,b}" using l by auto
  from this obtain p q where "d = p*a+q*b" using ideal_generated_pair[of a b] by auto
  thus ?thesis by auto
qed


lemma obtain_ideal_generated_pair:
  assumes "c \<in> ideal_generated {a,b}"
  obtains p q where "p*a+q*b=c"
proof -
  have "c \<in> {p * a + q * b |p q. True}" using assms ideal_generated_pair by auto
  thus ?thesis using that by auto
qed

lemma ideal_generated_pair_exists_UNIV:
  shows "(ideal_generated {a,b} = ideal_generated {1}) = (\<exists>p q. p*a+q*b = 1)" (is "?lhs = ?rhs")
proof
  assume r: ?rhs
  have "x \<in> ideal_generated {a,b}" for x
  proof (cases "a=b")
    case True
    then show ?thesis
      by (metis UNIV_I r dvd_ideal_generated_singleton finite.intros ideal_generated_1
          ideal_generated_pair_UNIV ideal_generated_singleton_subset)
  next
    case False
    have f: "finite {a,b}" by simp
    have 1: "1 \<in> ideal_generated {a,b}"
      using ideal_generated_pair_UNIV local.one_dvd r by blast
    hence i: "ideal_generated {a,b} = {y. \<exists>f. (\<Sum>i\<in>{a,b}. f i * i) = y}"
      using ideal_explicit2[of "{a,b}"] by auto
    from this obtain f where f: "f a * a + f b * b = 1" using sum_two_elements 1 False by auto
    let ?f = "\<lambda>y. if y = a then x * f a else x * f b"
    have "(\<Sum>i\<in>{a,b}. ?f i * i) = x" unfolding sum_two_elements[OF False] using f False
      using mult_ac(1) ring_distribs(1) semiring_normalization_rules(12) by force
    thus ?thesis unfolding i by auto
  qed
  thus ?lhs by auto
next
  assume ?lhs thus ?rhs using ideal_generated_pair_exists[of a b 1] by auto
qed

corollary ideal_generated_UNIV_obtain_pair:
  assumes "ideal_generated {a,b} = ideal_generated {1}"
  shows " (\<exists>p q. p*a+q*b = d)"
proof -
  obtain x y where "x*a+y*b = 1" using ideal_generated_pair_exists_UNIV assms by auto
  hence "d*x*a+d*y*b=d"
    using local.mult_ac(1) local.ring_distribs(1) local.semiring_normalization_rules(12) by force
  thus ?thesis by auto
qed



lemma sum_three_elements:
  shows "\<exists>x y z::'a. (\<Sum>i\<in>{a,b,c}. f i * i) = x * a + y * b + z * c"
proof (cases "a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c")
  case True
  then show ?thesis by (auto, metis add.assoc)
next
  case False
  have 1: "\<exists>x y z. f c * c = x * c + y * c + z * c"
    by (rule exI[of _ 0],rule exI[of _ 0], rule exI[of _ "f c"], auto)
  have 2: "\<exists>x y z. f b * b + f c * c = x * b + y * b + z * c"
    by (rule exI[of _ 0],rule exI[of _ "f b"], rule exI[of _ "f c"], auto)
  have 3: "\<exists>x y z. f a * a + f c * c = x * a + y * c + z * c"
    by (rule exI[of _ "f a"],rule exI[of _ 0], rule exI[of _ "f c"], auto)
  have 4: "\<exists>x y z. (\<Sum>i\<in>{c, b, c}. f i * i) = x * c + y * b + z * c" if a: "a = c" and b: "b \<noteq> c"
    by (rule exI[of _ 0],rule exI[of _ "f b"], rule exI[of _ "f c"], insert a b,
        auto simp add: insert_commute)
  show ?thesis using False
    by (cases "b=c", cases "a=c", auto simp add: 1 2 3 4)
qed

lemma sum_three_elements':
  shows "\<exists>f::'a\<Rightarrow>'a. (\<Sum>i\<in>{a,b,c}. f i * i) = x * a + y * b + z * c"
proof (cases "a \<noteq> b \<and> b \<noteq> c \<and> a \<noteq> c")
  case True
  let ?f = "\<lambda>i. if i = a then x else if i = b then y else if i = c then z else 0"
  show ?thesis by (rule exI[of _ "?f"], insert True mult.assoc, auto simp add: local.add_ac)
next
  case False
  have 1: "\<exists>f. f c * c = x * c + y * c + z * c"
    by (rule exI[of _ "\<lambda>i. if i = c then x+y+z else 0"], auto simp add: local.ring_distribs)
  have 2: "\<exists>f. f a * a + f c * c = x * a + y * c + z * c" if bc: " b = c" and ac: "a \<noteq> c"
    by (rule exI[of _ "\<lambda>i. if i = a then x else y+z"], insert ac bc add_ac ring_distribs, auto)
  have 3: "\<exists>f. f b * b + f c * c = x * b + y * b + z * c" if bc: " b \<noteq> c" and ac: "a = b"
    by (rule exI[of _ "\<lambda>i. if i = a then x+y else z"], insert ac bc add_ac ring_distribs, auto)
  have 4: "\<exists>f. (\<Sum>i\<in>{c, b, c}. f i * i) = x * c + y * b + z * c" if a: "a = c" and b: "b \<noteq> c"
    by (rule exI[of _ "\<lambda>i. if i = c then x+z else y"], insert a b add_ac ring_distribs,
        auto simp add: insert_commute)
  show ?thesis using False
    by (cases "b=c", cases "a=c", auto simp add: 1 2 3 4)
qed


(*This is generalizable to arbitrary sets.*)
lemma ideal_generated_triple_pair_rewrite:
  assumes i1: "ideal_generated {a, b, c} = ideal_generated {d}"
    and i2: "ideal_generated {a, b} = ideal_generated {d'}"
  shows "ideal_generated{d',c} = ideal_generated {d}"
proof
  have d': "d' \<in> ideal_generated {a,b}" using i2 by (simp add: ideal_generated_in)
  show "ideal_generated {d', c} \<subseteq> ideal_generated {d}"
  proof
    fix x assume x: "x \<in> ideal_generated {d', c}"
    obtain f1 f2 where f: "f1*d' + f2*c = x" using obtain_ideal_generated_pair[OF x] by auto
    obtain g1 g2 where g: "g1*a + g2*b = d'" using obtain_ideal_generated_pair[OF d'] by blast
    have 1: "f1*g1*a + f1*g2*b + f2*c = x"
      using f g local.ring_distribs(1) local.semiring_normalization_rules(18) by auto
    have "x \<in> ideal_generated {a, b, c}"
    proof -
      obtain f where "(\<Sum>i\<in>{a,b,c}. f i * i) = f1*g1*a + f1*g2*b + f2*c"
        using sum_three_elements' 1 by blast
      moreover have "ideal_generated {a,b,c} = {y. \<exists>f. (\<Sum>i\<in>{a,b,c}. f i * i) = y}"
        using ideal_explicit2[of "{a,b,c}"] by simp
      ultimately show ?thesis using 1 by auto
    qed
    thus "x \<in> ideal_generated {d}" using i1 by auto
  qed
  show "ideal_generated {d} \<subseteq> ideal_generated {d', c}"
  proof (rule ideal_generated_singleton_subset)
    obtain f1 f2 f3 where f: "f1*a + f2*b + f3*c = d"
    proof -
      have "d \<in> ideal_generated {a,b,c}" using i1  by (simp add: ideal_generated_in)
      from this obtain f where d: "(\<Sum>i\<in>{a,b,c}. f i * i) = d"
        using ideal_explicit2[of "{a,b,c}"] by auto
      obtain x y z where "(\<Sum>i\<in>{a,b,c}. f i * i) = x * a + y * b + z * c"
        using sum_three_elements by blast
      thus ?thesis using d that by auto
    qed
    obtain k where k: "f1*a + f2*b = k*d'"
    proof -
      have "f1*a + f2*b \<in> ideal_generated{a,b}" using ideal_generated_pair by blast
      also have "... = ideal_generated {d'}" using i2 by simp
      also have "... = {k*d' |k. k\<in>UNIV}" using ideal_generated_singleton by auto
      finally show ?thesis using that by auto
    qed
    have "k*d'+f3*c=d" using f k by auto
    thus "d \<in> ideal_generated {d', c}"
      using ideal_generated_pair by blast
  qed (simp)
qed

lemma ideal_generated_dvd:
  assumes i: "ideal_generated {a,b::'a} = ideal_generated{d} "
  and a: "d' dvd a" and b: "d' dvd b"
shows "d' dvd d"
proof -
  obtain p q where "p*a+q*b = d"
    using i ideal_generated_pair_exists by blast
  thus ?thesis using a b by auto
qed

lemma ideal_generated_dvd2:
  assumes i: "ideal_generated S = ideal_generated{d::'a} "
  and "finite S"
  and x: "\<forall>x\<in>S. d' dvd x"
shows "d' dvd d"
  by (metis assms dvd_ideal_generated_singleton ideal_generated_dvd_subset)

end


subsection \<open>An equivalent characterization of B\'ezout rings\<close>

text \<open>The goal of this subsection is to prove that a ring is B\'ezout ring if and only if every
  finitely generated ideal is principal.\<close>

definition "finitely_generated_ideal I = (ideal I \<and> (\<exists>S. finite S \<and> ideal_generated S = I))"

context
  assumes "SORT_CONSTRAINT('a::comm_ring_1)"
begin


lemma sum_two_elements':
  fixes d::'a
  assumes s: "(\<Sum>i\<in>{a,b}. f i * i) = d"
  obtains p and q where "d = p * a + q * b"
proof (cases "a=b")
  case True
  then show ?thesis
    by (metis (no_types, lifting) add_diff_cancel_left' emptyE finite.emptyI insert_absorb2
        left_diff_distrib' s sum.insert sum_singleton that)
next
  case False
  show ?thesis using s unfolding sum_two_elements[OF False]
    using that by auto
qed

text \<open>This proof follows Theorem 6-3 in "First Course in Rings and Ideals" by Burton\<close>

lemma all_fin_gen_ideals_are_principal_imp_bezout:
  assumes all: "\<forall>I::'a set. finitely_generated_ideal I \<longrightarrow> principal_ideal I"
  shows "OFCLASS ('a, bezout_ring_class)"
proof (intro_classes)
  fix a b::'a
  obtain d where ideal_d: "ideal_generated {a,b} = ideal_generated {d}"
    using all unfolding finitely_generated_ideal_def
    by (metis finite.emptyI finite_insert ideal_ideal_generated principal_ideal_def)
  have a_in_d: "a \<in> ideal_generated {d}"
    using ideal_d ideal_generated_subset_generator by blast
  have b_in_d: "b \<in> ideal_generated {d}"
    using ideal_d ideal_generated_subset_generator by blast
  have d_in_ab: "d \<in> ideal_generated {a,b}"
    using ideal_d ideal_generated_subset_generator by auto
  obtain f where "(\<Sum>i\<in>{a,b}. f i * i) = d" using obtain_sum_ideal_generated[OF d_in_ab] by auto
  from this obtain p q where d_eq: "d = p*a + q*b" using sum_two_elements' by blast
  moreover have d_dvd_a: "d dvd a"
    by (metis dvd_ideal_generated_singleton ideal_d ideal_generated_subset insert_commute
        subset_insertI)
  moreover have "d dvd b"
    by (metis dvd_ideal_generated_singleton ideal_d ideal_generated_subset subset_insertI)
  moreover have "d' dvd d" if d'_dvd: "d' dvd a \<and> d' dvd b" for d'
  proof -
    obtain s1 s2 where s1_dvd: "a = s1*d'" and s2_dvd: "b = s2*d'"
      using mult.commute d'_dvd unfolding dvd_def by auto
    have "d = p*a + q*b" using d_eq .
    also have "...= p * s1 * d' + q * s2 *d'" unfolding s1_dvd s2_dvd by auto
    also have "... = (p * s1 + q * s2) * d'" by (simp add: ring_class.ring_distribs(2))
    finally show "d' dvd d" using mult.commute unfolding dvd_def by auto
  qed
  ultimately show "\<exists>p q d. p * a + q * b = d \<and> d dvd a \<and> d dvd b
  \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d)" by auto
qed
end


context bezout_ring
begin

lemma exists_bezout_extended:
  assumes S: "finite S" and ne: "S \<noteq> {}"
  shows "\<exists>f d. (\<Sum>a\<in>S. f a * a) = d \<and> (\<forall>a\<in>S. d dvd a) \<and> (\<forall>d'. (\<forall>a\<in>S. d' dvd a) \<longrightarrow> d' dvd d)"
  using S ne
proof (induct S)
  case empty
  then show ?case by auto
next
  case (insert x S)
  show ?case
  proof (cases  "S={}")
    case True
    let ?f = "\<lambda>x. 1"
    show ?thesis by (rule exI[of _ ?f], insert True, auto)
  next
    case False note ne = False
    note x_notin_S = insert.hyps(2)
    obtain f d where sum_eq_d: "(\<Sum>a\<in>S. f a * a) = d"
      and d_dvd_each_a: "(\<forall>a\<in>S. d dvd a)"
      and d_is_gcd: "(\<forall>d'. (\<forall>a\<in>S. d' dvd a) \<longrightarrow> d' dvd d)"
      using insert.hyps(3)[OF ne] by auto
    have "\<exists>p q d'. p * d + q * x = d' \<and> d' dvd d \<and> d' dvd x \<and> (\<forall>c. c dvd d \<and> c dvd x \<longrightarrow> c dvd d')"
      using exists_bezout by auto
    from this obtain p q d' where pd_qx_d': "p*d + q*x = d'"
      and d'_dvd_d: "d' dvd d" and d'_dvd_x: "d' dvd x"
      and d'_dvd: "\<forall>c. (c dvd d \<and> c dvd x) \<longrightarrow> c dvd d'" by blast
    let ?f = "\<lambda>a. if a = x then q else p * f a"
    have "(\<Sum>a\<in>insert x S. ?f a * a) = d'"
    proof -
      have "(\<Sum>a\<in>insert x S. ?f a * a) = (\<Sum>a\<in>S. ?f a * a) + ?f x * x"
        by (simp add: add_commute insert.hyps(1) insert.hyps(2))
      also have "... = p * (\<Sum>a\<in>S. f a * a) + q * x"
        unfolding sum_distrib_left
        by (auto, rule sum.cong, insert x_notin_S,
            auto simp add: mult.semigroup_axioms semigroup.assoc)
      finally show ?thesis using pd_qx_d' sum_eq_d by auto
    qed
    moreover have "(\<forall>a\<in>insert x S. d' dvd a)"
      by (metis d'_dvd_d d'_dvd_x d_dvd_each_a insert_iff local.dvdE local.dvd_mult_left)
    moreover have " (\<forall>c. (\<forall>a\<in>insert x S. c dvd a) \<longrightarrow> c dvd d')"
      by (simp add: d'_dvd d_is_gcd)
    ultimately show ?thesis by auto
  qed
qed

end

lemma ideal_generated_empty: "ideal_generated {} = {0}"
  unfolding ideal_generated_def using ideal_generated_0
  by (metis empty_subsetI ideal_generated_def ideal_generated_subset ideal_ideal_generated
      ideal_not_empty subset_singletonD)


lemma bezout_imp_all_fin_gen_ideals_are_principal:
  fixes I::"'a :: bezout_ring set"
  assumes fin: "finitely_generated_ideal I"
  shows "principal_ideal I"
proof -
  obtain S where fin_S: "finite S" and ideal_gen_S: "ideal_generated S = I"
    using fin unfolding finitely_generated_ideal_def by auto
  show ?thesis
  proof (cases "S = {}")
    case True
    then show ?thesis
      using ideal_gen_S unfolding True
      using ideal_generated_empty ideal_generated_0 principal_ideal_def by fastforce
  next
    case False note ne = False
    obtain d f where sum_S_d: "(\<Sum>i\<in>S. f i * i) = d"
    and d_dvd_a: "(\<forall>a\<in>S. d dvd a)" and d_is_gcd: "(\<forall>d'. (\<forall>a\<in>S. d' dvd a) \<longrightarrow> d' dvd d)"
      using exists_bezout_extended[OF fin_S ne] by auto
    have d_in_S: "d \<in> ideal_generated S"
      by (metis fin_S ideal_def ideal_generated_subset_generator
          ideal_ideal_generated sum_S_d sum_left_ideal)
    have "ideal_generated {d} \<subseteq> ideal_generated S"
      by (rule ideal_generated_singleton_subset[OF d_in_S fin_S])
    moreover have "ideal_generated S \<subseteq> ideal_generated {d}"
    proof
      fix x assume x_in_S: "x \<in> ideal_generated S"
      obtain f where sum_S_x: "(\<Sum>a\<in>S. f a * a) = x"
        using fin_S obtain_sum_ideal_generated x_in_S by blast
      have d_dvd_each_a: "\<exists>k. a = k * d" if "a \<in> S" for a
        by (metis d_dvd_a dvdE mult.commute that)
      let ?g = "\<lambda>a. SOME k. a = k*d"
      have "x = (\<Sum>a\<in>S. f a * a)" using sum_S_x by simp
      also have "... = (\<Sum>a\<in>S. f a * (?g a * d))"
      proof (rule sum.cong)
        fix a assume a_in_S: "a \<in> S"
        obtain k where a_kd: "a = k * d" using d_dvd_each_a a_in_S by auto
        have "a = ((SOME k. a = k * d) * d)" by (rule someI_ex, auto simp add: a_kd)
        thus "f a * a = f a * ((SOME k. a = k * d) * d)" by auto
      qed (simp)
      also have "... = (\<Sum>a\<in>S. f a * ?g a * d)" by (rule sum.cong, auto)
      also have "... = (\<Sum>a\<in>S. f a * ?g a)*d" using sum_distrib_right[of _ S d] by auto
      finally show "x \<in> ideal_generated {d}"
        by (meson contra_subsetD dvd_ideal_generated_singleton' dvd_triv_right
            ideal_generated_in singletonI)
    qed
    ultimately show ?thesis unfolding principal_ideal_def using ideal_gen_S by auto
  qed
qed

text \<open>Now we have the required lemmas to prove the theorem that states that
  a ring is B\'ezout ring if and only if every
  finitely generated ideal is principal. They are the following ones.

\begin{itemize}
\item @{text "all_fin_gen_ideals_are_principal_imp_bezout"}
\item @{text "bezout_imp_all_fin_gen_ideals_are_principal"}
\end{itemize}

However, in order to prove the final lemma, we need the lemmas with no type restrictions.
For instance, we need a version of theorem @{text "bezout_imp_all_fin_gen_ideals_are_principal"}
as

@{text "OFCLASS('a,bezout_ring) \<Longrightarrow>"} the theorem with generic types
  (i.e., @{text "'a"} with no type restrictions)


or as

@{text "class.bezout_ring _ _ _ _ \<Longrightarrow>"} the theorem with generic
  types (i.e., @{text "'a"} with no type restrictions)
\<close>

(*A possible workaround is to adapt the proof*)
(*
lemma bezout_imp_all_fin_gen_ideals_are_principal_unsatisfactory:
  assumes a1: "class.bezout_ring ( * ) (1::'a::comm_ring_1) (+) 0 (-) uminus" (*Me da igual esto que OFCLASS*)
  shows "\<forall>I::'a set. finitely_generated_ideal I \<longrightarrow> principal_ideal I"
proof (rule allI, rule impI)
  fix I::"'a set" assume fin: "finitely_generated_ideal I"
  interpret a: bezout_ring "( * )" "(1::'a)" "(+)" 0 "(-)" uminus using a1 .
  interpret dvd "( * )::'a\<Rightarrow>'a\<Rightarrow>'a" .
  interpret b: comm_monoid_add "(+)" "(0::'a)" using a1 by intro_locales
  have c: " class.comm_monoid_add (+) (0::'a)"  using a1 by intro_locales
  have [simp]: "(dvd.dvd ( * ) d a) = (d dvd a)" for d a::'a
    by (auto simp add: dvd.dvd_def dvd_def)
  have [simp]: "comm_monoid_add.sum (+) 0 (\<lambda>a. f a * a) S = sum (\<lambda>a. f a * a) S"
    for f and S::"'a set"
    unfolding sum_def unfolding comm_monoid_add.sum_def[OF c] ..
  obtain S where fin_S: "finite S" and ideal_gen_S: "ideal_generated S = I"
    using fin unfolding finitely_generated_ideal_def by auto
  show "principal_ideal I"
  proof (cases "S = {}")
    case True
    then show ?thesis
      using ideal_gen_S unfolding True
      using ideal_generated_empty ideal_generated_0 principal_ideal_def by fastforce
  next
    case False note ne = False
    obtain d f where sum_S_d: "(\<Sum>i\<in>S. f i * i) = d"
    and d_dvd_a: "(\<forall>a\<in>S. d dvd a)" and d_is_gcd: "(\<forall>d'. (\<forall>a\<in>S. d' dvd a) \<longrightarrow> d' dvd d)"
      using a.exists_bezout_extended[OF fin_S ne] by auto
    have d_in_S: "d \<in> ideal_generated S"
      by (metis fin_S ideal_def ideal_generated_subset_generator
          ideal_ideal_generated sum_S_d sum_left_ideal)
    have "ideal_generated {d} \<subseteq> ideal_generated S"
      by (rule ideal_generated_singleton_subset[OF d_in_S fin_S])
    moreover have "ideal_generated S \<subseteq> ideal_generated {d}"
    proof
      fix x assume x_in_S: "x \<in> ideal_generated S"
      obtain f where sum_S_x: "(\<Sum>a\<in>S. f a * a) = x"
        using fin_S obtain_sum_ideal_generated x_in_S by blast
      have d_dvd_each_a: "\<exists>k. a = k * d" if "a \<in> S" for a
        by (metis d_dvd_a dvdE mult.commute that)
      let ?g = "\<lambda>a. SOME k. a = k*d"
      have "x = (\<Sum>a\<in>S. f a * a)" using sum_S_x by simp
      also have "... = (\<Sum>a\<in>S. f a * (?g a * d))"
      proof (rule sum.cong)
        fix a assume a_in_S: "a \<in> S"
        obtain k where a_kd: "a = k * d" using d_dvd_each_a a_in_S by auto
        have "a = ((SOME k. a = k * d) * d)" by (rule someI_ex, auto simp add: a_kd)
        thus "f a * a = f a * ((SOME k. a = k * d) * d)" by auto
      qed (simp)
      also have "... = (\<Sum>a\<in>S. f a * ?g a * d)" by (rule sum.cong, auto)
      also have "... = (\<Sum>a\<in>S. f a * ?g a)*d" using sum_distrib_right[of _ S d] by auto
      finally show "x \<in> ideal_generated {d}"
        by (meson contra_subsetD dvd_ideal_generated_singleton' dvd_triv_right
            ideal_generated_in singletonI)
    qed
    ultimately show ?thesis unfolding principal_ideal_def using ideal_gen_S by auto
  qed
qed
*)

text \<open>Thanks to local type definitions, we can obtain it automatically by means
  of @{text "internalize-sort"}.\<close>

lemma bezout_imp_all_fin_gen_ideals_are_principal_unsatisfactory:
  assumes a1: "class.bezout_ring (*) (1::'b::comm_ring_1) (+) 0 (-) uminus" (*It is algo possible to prove it using OFCLASS*)
  shows "\<forall>I::'b set. finitely_generated_ideal I \<longrightarrow> principal_ideal I"
  using bezout_imp_all_fin_gen_ideals_are_principal[internalize_sort "'a::bezout_ring"]
  using a1 by auto


text \<open>The standard library does not connect @{text "OFCLASS"} and @{text "class.bezout_ring"}
in both directions. Here we show that @{text "OFCLASS \<Longrightarrow> class.bezout_ring"}. \<close>

lemma OFCLASS_bezout_ring_imp_class_bezout_ring:
  assumes "OFCLASS('a::comm_ring_1,bezout_ring_class)"
  shows "class.bezout_ring ((*)::'a\<Rightarrow>'a\<Rightarrow>'a) 1 (+) 0 (-) uminus"
  using assms
  unfolding bezout_ring_class_def class.bezout_ring_def
  using conjunctionD2[of "OFCLASS('a, comm_ring_1_class)"
                         "class.bezout_ring_axioms ((*)::'a\<Rightarrow>'a\<Rightarrow>'a) (+)"]
  by (auto, intro_locales)

text \<open>The other implication can be obtained
  by thm @{text "Rings2.class.Rings2.bezout_ring.of_class.intro"} \<close>
thm Rings2.class.Rings2.bezout_ring.of_class.intro


(*OFCLASS is a proposition (Prop), and then the following statement is not valid.*)

(*
lemma
  shows "(\<forall>I::'a::comm_ring_1 set. finitely_generated_ideal I \<longrightarrow> principal_ideal I)
    = OFCLASS('a, bezout_ring_class)"
*)

(*Thus, we use the meta-equality and the meta universal quantifier.*)
text \<open>Final theorem (with OFCLASS)\<close>
lemma bezout_ring_iff_fin_gen_principal_ideal:
    "(\<And>I::'a::comm_ring_1 set. finitely_generated_ideal I \<Longrightarrow> principal_ideal I)
    \<equiv> OFCLASS('a, bezout_ring_class)"
proof
  show "(\<And>I::'a::comm_ring_1 set. finitely_generated_ideal I \<Longrightarrow> principal_ideal I)
    \<Longrightarrow> OFCLASS('a, bezout_ring_class)"
    using all_fin_gen_ideals_are_principal_imp_bezout [where ?'a='a] by auto
  show "\<And>I::'a::comm_ring_1 set. OFCLASS('a, bezout_ring_class)
    \<Longrightarrow> finitely_generated_ideal I \<Longrightarrow> principal_ideal I"
    using bezout_imp_all_fin_gen_ideals_are_principal_unsatisfactory[where ?'b='a]
    using OFCLASS_bezout_ring_imp_class_bezout_ring[where ?'a='a] by auto
qed

text \<open>Final theorem (with @{text "class.bezout_ring"})\<close>

lemma bezout_ring_iff_fin_gen_principal_ideal2:
    "(\<forall>I::'a::comm_ring_1 set. finitely_generated_ideal I \<longrightarrow> principal_ideal I)
    = (class.bezout_ring ((*)::'a\<Rightarrow>'a\<Rightarrow>'a) 1 (+) 0 (-) uminus)"
proof
  show "\<forall>I::'a::comm_ring_1 set. finitely_generated_ideal I \<longrightarrow> principal_ideal I
      \<Longrightarrow> class.bezout_ring (*) 1 (+) (0::'a) (-) uminus"
    using all_fin_gen_ideals_are_principal_imp_bezout[where ?'a='a]
    using OFCLASS_bezout_ring_imp_class_bezout_ring[where ?'a='a]
    by auto
  show "class.bezout_ring (*) 1 (+) (0::'a) (-) uminus \<Longrightarrow> \<forall>I::'a set.
    finitely_generated_ideal I \<longrightarrow> principal_ideal I"
    using bezout_imp_all_fin_gen_ideals_are_principal_unsatisfactory by auto
qed

end
